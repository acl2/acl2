# A Formal Specification of the EVM (Ethereum Virtual Machine) in ACL2

This directory contains an initial, in-progress formal specification
of the Ethereum Virtual Machine (EVM).  It needs to be fleshed out by
adding missing instructions and updating it to cover the latest
Ethereum/EVM version.

## Related work (other formalizations/implementations/specifications of the EVM):

### Python Executable Specifications

https://github.com/ethereum/execution-specs

As of October, 2025 this appears to be up-to-date, covering versions
through Prague.

### Ethereum Yellow Paper

https://github.com/ethereum/yellowpaper

A LaTex document describing the EVM, etc.  As of October, 2025, the
Yellow Paper is out-of-date, only covering versions through Shanghai.

### KEVM

https://github.com/runtimeverification/evm-semantics

https://jellopaper.org/

A formalization of the EVM in the K framework.  As of October, 2025,
it appears to be actively maintained and to have support for versions
through Prague.

### Dafny-EVM

https://github.com/ConsenSys/evm-dafny

https://franck44.github.io/publications/papers/dafnyevm-fm-23.pdf

### revm: an implementation in Rust

https://github.com/bluealloy/revm

### LEVM (Lambda EVM), implemented in Rust

https://github.com/lambdaclass/ethrex/tree/main/crates/vm/levm

As of October, 2025 this appears to be up-to-date as it supports Prague.

### Geth (Go Ethereum)

https://github.com/ethereum/go-ethereum/tree/master

### A formalization in LEM

https://github.com/pirapira/eth-isabelle

A formalization in LEM, which can be translated to Isabelle/HOL and
other systems.  As of October, 2025, it appears out-of-date, having
not been changed since 2018.

### A formalization in F*

https://secpriv.wien/ethsemantics/

https://secpriv.wien/downloads/ethsemantics/post2018-tr.pdf

### EVM tests:

https://github.com/ethereum/tests