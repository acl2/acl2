; ihs-doc-topic.lisp -- root of the IHS libraries
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.


; [Jared]: I split this out of ihs-init.lisp into its own book so that
; basic-definitions.lisp doesn't need to include ihs-init.lisp

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(defxdoc ihs
  :parents (bit-vectors)
  :short "The Integer Hardware Specification (IHS) library is a collection of
arithmetic books, mainly geared toward bit-vector arithmetic."

  :long "<p>This is a classic ACL2 arithmetic library wherein bit-vectors are
represented as ordinary ACL2 integers, which has some nice efficiency
properties.</p>

<p>Despite the underlying integer-based representation, the library allows you
to easily treat integers akin to lsb-first lists of bits, with the functions
@(see logcar) and @(see logcdr) acting as analogues for @(see car) and @(see
cdr).</p>

<p>To help you make use of this view, the library introduces alternate,
list-style, recursive definitions for operations like @(see logand).  Once you
understand how to induct in the right way to use these definitions, it becomes
an extremely useful way to prove theorems about these bit functions.</p>

<p>The IHS library is found in: @('books/ihs/*.lisp').</p>")
