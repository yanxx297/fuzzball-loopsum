# FuzzBALL with Loop Summarization
Implement loop summarization <sup>[1](#footnote1)</sup> on FuzzBALL, a symbolic execution tool for X86 binary code.

## FuzzBALL
FuzzBALL is a symbolic execution tool for x86 (and a little ARM)
binary code, based on the BitBlaze Vine library. (The name comes from
the phrase "FUZZing Binaries with A Little Language", where "fuzzing"
is a common application of symbolic execution to bug-finding, and the
"little language" refers to the Vine intermediate language that
FuzzBALL uses for execution.  Also "fuzzball" is a common nickname for
a small kitten, and FuzzBALL was intended to be simpler and
lighter-weight than some other symbolic execution tools.)

At a high level, there are two kinds of code you can run FuzzBALL
on. First, there is any code that can execute stand-alone, without the
services of an OS or special hardware devices; this can include a
subset of code from a larger program that does need those
things. Second, there are single-threaded Linux programs, which
FuzzBALL can run by passing their system calls onto your real OS.

FuzzBALL is free software distributed under the GNU GPL: see the files
LICENSE and COPYING for details.

Compilation instructions are in the file INSTALL.

The README file includes some more detailed description of FuzzBALL
and some tutorial-style examples.

FuzzBALL's page on the Berkeley web site, at

http://bitblaze.cs.berkeley.edu/fuzzball.html

has links to some papers that build on FuzzBALL.

We are interested in your comments, questions, and feedback about
FuzzBALL via the bitblaze-users mailing list (hosted by Google Groups):

http://groups.google.com/group/bitblaze-users

## Loop Summarization

### Bytecode Compilation
Currently we cannot compile bytecode FuzzBALL because recent change in OCaml break it.
As a workaround, we turn off warning errors.
Note that for now we still need to rerun the last command with additional option added.
See commit [3bbe3a5](https://github.com/yanxx297/fuzzball-loopsum/commit/3bbe3a5c06b16663bbfe099a2adb5a932616a28e) for more details.

### Test Loop Summarization
```bash
../../exec_utils/fuzzball -use-loopsum -trace-loop -trace-decisions -trace-iterations \
-trace-conditions -trace-loopsum -fuzz-start-addr 0x8048553 -fuzz-end-addr 0x5006f63a \
-solver smtlib -solver-path ../../../lib/z3/build/z3 \
-linux-syscalls -skip-call-ret-symbol 0x8048598=n -trace-stopping \
input-dependent -- ./input-dependent 0
# -fuzz-start-addr          the first instruction of main()
# -fuzz-end-addr            the 2nd instruction after returning from main(), we
#                           identify this instruction by tracing instruction in
#                           FuzzBALL (-trace-insns)
# -skip-call-ret-symbol     The eip of an atoi that transform string format input
#                           to an integer.
```
### Decision Tree Visualization
FuzzBALL writes the decision tree in dot format when it stops.
The dot file is stored at /tmp/bdt_graph by default.
You can convert the file to pdf by running the command bellow.
```bash
dot -Tpdf /tmp/bdt_graph -o /tmp/bdt.pdf
```

## Known Bugs
* -check-for-ret-addr-overwrite doesn't work in example/loopsum/ret-addr-overwrite

## Reference
<a name="footnote1">[1]</a>
Patrice Godefroid and Daniel Luchaup. Automatic partial loop summarization in
dynamic test generation. In Proceedings of the 2011 International Symposium on
Software Testing and Analysis, ISSTA ’11, pages 23–33, New York, NY, USA, 2011.
ACM.
