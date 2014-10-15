; ihs-doc-topic.lisp -- root of the IHS libraries
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.


; [Jared]: I split this out of ihs-init.lisp into its own book so that
; basic-definitions.lisp doesn't need to include ihs-init.lisp

(in-package "ACL2")

(defdoc ihs
  ":Doc-Section ihs
The Integer Hardware Specification (IHS) library is a collection of
arithmetic books, mainly geared toward bit-vector arithmetic.~/

This is a classic ACL2 arithmetic library wherein bit-vectors are represented
as ordinary ACL2 integers, which has some nice efficiency properties.

Despite the underlying integer-based representation, the library allows you to
easily treat integers akin to lsb-first lists of bits, with the functions
~ilc[logcar] and ~ilc[logcdr] acting as analogues for ~ilc[car] and ~ilc[cdr].

To help you make use of this view, the library introduces alternate,
list-style, recursive definitions for operations like ~ilc[logand].  Once you
understand how to induct in the right way to use these definitions, it becomes
an extremely useful way to prove theorems about these bit functions.

The IHS library is found in:
~bv[]
books/ihs/*.lisp
~ev[]~/~/")
