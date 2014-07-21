; ihs-doc-topic.lisp -- root of the IHS libraries
; Copyright (C) 1997  Computational Logic, Inc.

; This book is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This book is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this book; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.


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
