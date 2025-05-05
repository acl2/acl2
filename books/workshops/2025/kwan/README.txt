SUMMARY
A simulator for the RISC-V 32-bit base instructions set
architecture (RV32I), written in the operational semantics style.

PROJECT STRUCTURE
  - decode.lisp   : decoding / disassembly functions for RV32I instructions
  - demo.lsp      : a simple example of how to use the simulator
  - rv32i.lisp    : RV32I step function & instruction correctness theorems
  - rv-state.lisp : RV32 state object & state access / update theorems
  - instructions/ : directory for all RV32I semantic & assembly functions / theorems
  - extensions/   : directory for RV32 extensions (WIP)

  Miscellaneous / mostly boiler-plate events:
    - constants.lisp
    - init.lisp
    - misc-events.lisp
    - operations.lisp

CERTIFY INSTRUCTION:

    <cert.pl command> --acl2 <path to acl2 executable> *.lisp
