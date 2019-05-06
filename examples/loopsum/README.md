# Test Examples for Loop Summarization

### input-dependent
The 1st toy example used to test the basic function of loop summarization.
```bash
../../exec_utils/fuzzball -use-loopsum -trace-loop -trace-loopsum \
-fuzz-start-addr 0x8048561 -fuzz-end-addr 0x5006f63a -skip-call-ret-symbol 0x80485a6=n \
-solver smtlib -trace-iterations -trace-conditions \
-solver-path /path/to/z3/build/z3 -linux-syscalls \
-trace-stopping input-dependent -- ./input-dependent 0
```
### multi-occurence
Another basic example to test whether context-aware summarization works.

### ret-addr-overwrite
A running example that can demonstrate the benefit using loopsum in bug finding.

To simplify this test, compile this example with ``-fno-stack-protector``
```bash
gcc -m32 -fno-stack-protector ret-addr-overwrite.c -g -o ret-addr-overwrite
```

Pure symbolic execution
```bash
../../exec_utils/fuzzball -use-loopsum -trace-loopsum \
-fuzz-start-addr 0x0804840d -symbolic-short 0x0804a01c=n \
-trace-conditions -trace-iterations -solver smtlib \
-solver-path /path/to/z3/build/z3 -linux-syscalls -trace-stopping \
ret-addr-overwrite -- ./ret-addr-overwrite 0
# End with Strange term exception; not 100% sure whether that's the right result
```

"2-path" experiment
```bash
# Create a file with value int 0x27
perl -e 'print "\x27\0\0\0"' > /tmp/input

# with -concolic-cstring-file, we can use 0x27 to direct concolic execution.
# You can add -tracepoint 0x8048405:'R_EAX:reg32_t' to check whether variable `c`
# is symbolic after applying loopsum
../../exec_utils/fuzzball -use-loopsum -trace-loopsum -fuzz-start-addr 0x0804840d \
-concolic-cstring-file 0x0804a01c=/tmp/input -concolic-prob 1.0 -num-paths 2 \
-trace-temps -trace-conditions -trace-iterations \
-solver smtlib -solver-path /path/to/z3/build/z3 -linux-syscalls \
-trace-stopping ret-addr-overwrite -- ./ret-addr-overwrite 0
```
