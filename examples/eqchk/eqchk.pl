#!/usr/bin/perl

use strict;

my $bin = "./two-funcs";
die "Usage: synth-one.pl \n1. <fuzzball-feature-to-test, e.g. implied-value-conc> \n2. <on or off> \n3. <fnum> \n4. <seed> \n5. <recompile $bin=1, use $bin as-is=0> \n6. <verbose=1, non-verbose=0, extra-verbose=2 (is logging-heavy, be warned)>"
  unless @ARGV == 6;
my($opt_to_eqchk, $opt_control, $fnum, $rand_seed, $recompile, $verbose) = @ARGV;

my $fnargs = 6;
my $region_limit = 936;
srand($rand_seed);

my $fuzzball="fuzzball";
if (exists $ENV{FUZZBALL_LOC}) {
    $fuzzball = $ENV{FUZZBALL_LOC};
}
my $stp="stp";
if (exists $ENV{STP_LOC}) {
    $stp = $ENV{STP_LOC};
}

my $pwd = $ENV{PWD};

my $f1_completed_count = 0;
my $iteration_count = 0;

if ($recompile == 1) {
    print "compiling binary: ";
    my $unused = `gcc -static two-funcs.c -g -o two-funcs `;
    my $gcc_ec = $?;
    die "failed to compile $bin" unless $gcc_ec == 0;
}

# Try to figure out the code and data addresses we need based on
# matching the output of "nm" and "objdump". Not the most robust
# possible approach.

my $fuzz_start_addr = "0x" . substr(`nm $bin | fgrep " T fuzz_start"`, 0, 16);

my $f1_call_addr =
  "0x" . substr(`objdump -dr $bin | grep 'call.*<f1>'`, 2, 6);

my $f2_call_addr =
  "0x" . substr(`objdump -dr $bin | grep 'call.*<wrap_f2>'`, 2, 6);

my $post_f1_call = sprintf("0x%x",hex($f1_call_addr)+0x5);
my $post_f2_call = sprintf("0x%x",hex($f2_call_addr)+0x5);

my @arg_addr;
for my $i (0 .. 5) {
    $arg_addr[$i] =
      "0x" . substr(`nm $bin | fgrep " B global_arg$i"`, 0, 16);
}

my $match_jne_addr =
  "0x" . substr(`objdump -dr $bin | grep 'jne.*compare+'`, 2, 6);

print "$fuzzball\n";
print "$stp\n";
print "fuzz-start-addr:\t$fuzz_start_addr\n";
print "f1-call-addr:\t$f1_call_addr\n";
print "f2-call-addr:\t$f2_call_addr\n";
for my $i (0 .. 5) {
    print "arg$i: $arg_addr[$i]\n";
}
print "branch: $match_jne_addr\n";

my @solver_opts = ("-solver", "smtlib-batch", "-solver-path", $stp
		   # , "-save-solver-files"
		   #, "-solver-timeout",5,"-timeout-as-unsat"
    );

my @verbose_1_opts = (
    "-trace-conditions",
    "-trace-decisions",
    "-trace-sym-addr-details",
    "-trace-sym-addrs",
    "-trace-syscalls",
    "-trace-temps",
    "-trace-tables",
    "-trace-binary-paths-bracketed",
    "-trace-solver",
    "-trace-regions");

my @verbose_2_opts = (@verbose_1_opts,
		      "-trace-offset-limit",
		      "-trace-basic",
		      "-trace-eip",
		      "-trace-registers",
		      "-trace-stmts",
		      "-trace-insns",
		      "-trace-loads",
		      "-trace-stores");
my @verbose_opts = ($verbose == 1) ? @verbose_1_opts : (($verbose == 2) ? @verbose_2_opts : ());

my @common_opts = (
    "-no-fail-on-huer",
    #"-return-zero-missing-x64-syscalls",
    #"-region-limit", $region_limit,
    "-trace-iterations", "-trace-assigns", "-solve-final-pc",
    "-trace-stopping",
    "-table-limit","12",
    "-omit-pf-af",
    #"-match-syscalls-in-addr-range", before using this option, fix the null f2_call_addr 
    #$f1_call_addr.":".$post_f1_call.":".$f2_call_addr.":".$post_f2_call,
    "-random-seed", int(rand(10000000)),
    #"-turn-opt-". $opt_control . "-range", $opt_to_eqchk.":".$f1_call_addr.":".$post_f1_call
    );

# Given the specification of a FuzzBALL option, execute it with symbolic
# inputs and look for a "mismatch" between when the option is turned off and turned on
sub run_test_harness {
    my @args = ($fuzzball, "-linux-syscalls", "-arch", "x64",
		$bin,
		@solver_opts, "-fuzz-start-addr", $fuzz_start_addr,
		"-symbolic-long", "$arg_addr[0]=a",
		"-symbolic-long", "$arg_addr[1]=b",
		"-symbolic-long", "$arg_addr[2]=c",
		"-symbolic-long", "$arg_addr[3]=d",
		"-symbolic-long", "$arg_addr[4]=e",
		"-symbolic-long", "$arg_addr[5]=f",
		"-trace-regions", #useful for the "Address ... is region ..." line matching below
		#"-trace-loopsum",
		@verbose_opts,
		"-branch-preference", "$match_jne_addr:0",
		"-use-loopsum",
		#"-trace-loopsum",
		@common_opts,
		"--", $bin, $fnum);
    my @printable;
    for my $a (@args) {
	if ($a =~ /[\s|<>]/) {
	    push @printable, "'$a'";
	} else {
	    push @printable, $a;
	}
    }
    if ($verbose != 0) { print "@printable\n"; }
    open(LOG, "-|", @args);
    my($matches, $fails) = (0, 0);
    my(@ce, $this_ce);
    $this_ce = 0;
    my $f1_completed = 0;
    $f1_completed_count = 0;
    $iteration_count = 0;
    my @extra_ce_info = ();
    while (<LOG>) {
	if ($_ eq "Match\n" ) {
	    $matches++;
	} elsif (/^Iteration (.*):$/) {
	    $f1_completed = 0;
	    $iteration_count++;
	} elsif ($_ eq "Completed f1\n") {
	    $f1_completed = 1;
	    $f1_completed_count++;
	} elsif (($_ eq "Mismatch\n") or 
		 (/^Stopping at null deref at (0x[0-9a-f]+)$/ and $f1_completed == 1) or
		 (/^Stopping at access to unsupported address at (0x[0-9a-f]+)$/ and $f1_completed == 1) or
		 (/^Stopping on disqualified path at (0x[0-9a-f]+)$/ and $f1_completed == 1) or 
		 (/^Disqualified path at (0x[0-9a-f]+)$/ and $f1_completed == 1)) {
	    $fails++;
	    $this_ce = 1;
	} elsif (/^Input vars: (.*)$/ and $this_ce) {
	    my $vars = $1;
	    $this_ce = 0;
	    @ce = (0) x $fnargs;
	    for my $v (split(/ /, $vars)) {
		if ($v =~ /^([a-f])=(0x[0-9a-f]+)$/) {
		    my $index = ord($1) - ord("a");
		    $ce[$index] = hex $2;
		}
	    }
	    if ($verbose != 0) { print "  $_"; }
	    last;
	} elsif (/Address [a-f]:reg64_t is region ([0-9]+)/) {
	    my $add_line = $_;
	    my $add_var = -1;
	    for my $v (split(/ /, $add_line)) {
		if ($v =~ /^[a-f]:reg64_t$/) { # matches argument name
		    $add_var = ord($v) - ord('a');
		    if ($add_var < $fnargs and $add_var >= 0) {
			push @extra_ce_info, 
			(sprintf "symbolic input $v corresponds to a symbolic region\n"); 
		    }
		}
	    }
	}
 
	if ($verbose != 0) { print "  $_"; }
    }
    close LOG;
    if ($matches == 0 and $fails == 0) {
	print "CounterExample search failed";
	die "Missing results from check run";
    }
    if ($fails == 0) {
	return 1;
    } else {
	return (0, [@ce], [@extra_ce_info]);
    }
}

my $start_time = time();
my $diff;
print "Checking $opt_to_eqchk using function $fnum:\n";
my ($res, $cer, $extra_ce_info) = run_test_harness();
$diff = time() - $start_time;
print "elapsed time = $diff\n";
if ($res) {
    print "Success!\n";
    my $verified="partially";
    if ($f1_completed_count == $iteration_count) {
	$verified="completely";
    }
    print "Option $opt_to_eqchk was $verified equivalent using function $fnum\n";
} else {
    print "Failure!\n";
    my $ce_s = join(", ", @$cer);
    my $extra_ce_info_s = join(", ", @$extra_ce_info);
    print "Mismatch on input $ce_s";
    if (scalar($extra_ce_info) != 0) {
	print ", extra ce info = $extra_ce_info_s";
    }
    print "\n";
}
