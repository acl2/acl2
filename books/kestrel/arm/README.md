This directory contains an in-progress formal model of ARM32.

Reference: ARM Architecture Reference Manual ARMv7-A and ARMv7-R edition,
available from https://developer.arm.com/documentation/ddi0406/latest/

Contents:

* package.lsp: The ARM package.

* portcullis.lisp: dummy book for portcullis (see :doc working-with-packages).

* encodings.lisp: Bit encodings of the instructions.

* decoder.lisp: Generation of a decoder from the encodings.

* decoder-tests.lisp: Tests of the generated decoder.

* state.lisp: Model of the ARM32 state (memory, registers, flags, etc.).

* memory32.lisp: Supporting machinery for the 32-bit memory.

* memory.lisp: Functions for manipulating memory.

* pseudocode.lisp: Helper functions that appear in the pseudo-code representing instructions.  These are called by our semantic functions.

* def-inst.lisp: The def-inst tool for defining instructions.

* instructions.lisp: Semantic functions of the instructions.

* step.lisp: Function to step the ARM32 CPU (fetch, decode, and execute an instruction).

* top.lisp: Top-level file for the model.

* doc.lisp: Documentation for the model.
