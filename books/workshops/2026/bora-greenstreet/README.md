# Erlang in ACL2: A CPS Evaluator

## Erlang in ACL2

Some names from the paper are different at the moment:
- `estate` is `erl-state`
- `eval-cont-list` is `apply-k`
- `cont-binop` and `cont-expr` are `kont-binop` and `kont-expr`

## Certify with:
```bash
ACL2_DIR/books/build/cert.pl --acl2 ACL2 *.lisp
```
where `ACL2_DIR` denotes your ACL2 sources directory and `ACL2` denotes a recent ACL2 executable.

## Important files:

### The Translator
erl-to-acl2.erl : translator for Erlang modules and expressions. (It is not fully automated).

### The AST Evaluator:
- eval/erl-ast : the ACL2 representation of Erlang ASTs
- evaluator/erl-kont : the continuations.
- evaluator/erl-eval : the CPS evaluator
- evaluator/erl-state : program states

### The Scheduler:
- scheduler/proc : process states
- scheduler/network : map from pid to process
- scheduler/abstract : the abstract scheduler
- scheduler/erl-in-acl2 : run the entire pipeline here.

### Examples:
- evaluator/examples : test cases for the CPS evaluator.
- scheduler/examples : test cases for concurrent execution.
- examples/ : the examples from the paper
+ erl-arithmetic/sum_of_nats : closed form of sum.
+ reduce-v2 : work in progress reduce proof.
