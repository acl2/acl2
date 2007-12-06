; ihs-theories.lisp -- subtheories of ACL2 boot-strap theory
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

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    ihs-theories.lisp
;;;
;;;    Definitions of useful theories that are subtheories of the Acl2
;;;    BOOT-STRAP theories.  This book is separate from "ihs-init" because we
;;;    need certain theory functions defined in "ihs-init" to be compiled. 
;;;
;;;    Bishop Brock
;;;    Computational Logic, Inc.
;;;    1717 West Sixth Street, Suite 290
;;;    Austin, Texas 78703
;;;    (512) 322-9951
;;;    brock@cli.com
;;;    
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "ACL2")

(include-book "ihs-init")

(deflabel ihs-theories
  :doc ":doc-section ihs-theories
  Subtheories of the Acl2 initialization theory.~/

  The following theories are available: ~/

  The conventional way to initiate the definition of a book in the IHS
  library hierarchy is to 1) Include all necessary books, 2) DISABLE the
  world with (IN-THEORY NIL), and 3) Construct the theory needed to certify
  the present book from theory expressions supplied by the included books.
  This book includes the most basic theories, i.e., theories of the Acl2
  functions avaiable at this label: 'IHS-THEORIES, which is exactly the
  extension of the Acl2 initialization theory made by \"ihs-init\".  Every
  IHS book will normally begin by ENABLEing one of these theories.  Some of
  the theories may also be useful, for example, to specify very restricted
  local theories for specialized apllications.~/")

(deftheory built-ins
  (defun-theory
    '(IFF NOT IMPLIES EQ ATOM EQL = /= NULL ENDP
          ZEROP SYNP PLUSP MINUSP
	  LISTP PROG2$ FORCE CASE-SPLIT))
  :doc ":doc-section ihs-theories
  Functions whose definitions are \"built in\" to Acl2.~/~/

  If you execute (IN-THEORY NIL), Acl2 prints a warning that the empty theory
  does not contain the :DEFINITION rules for certain functions whose
  definitions are built into Acl2 at various places.  This theory contains
  the DEFUN-THEORY (see :DOC DEFUN-THEORY) of exactly those functions named
  in that message.~/" )

(deftheory measures
  (defun-theory
    '(O< O-P NATP POSP O-FINP ACL2-COUNT CONSP CAR CDR RATIONALP 
         INTEGERP < STRINGP INTEGER-ABS NUMERATOR DENOMINATOR
         FIX RFIX IFIX NFIX ZIP ZP))
  :doc ":doc-section ihs-theories
  Functions used to prove admissibility.~/~/

  This theory contains the DEFUN-THEORY (see :DOC DEFUN-THEORY) of all
  functions (except those in (THEORY BUILT-INS)) that are necessary to prove
  the admissibility of recursive functions in most cases.  Note that this
  theory is probably useless without the theory BUILT-INS and some simple
  theory of arithmetic (such as the theory ALGEBRA from the book
  \"math-lemmas\".

  For functions that recur on the length of a string you may have to ENABLE
  LENGTH and LEN, as we steadfastly refuse to allow ANY globally enabled
  recursive functions.~/")

(deftheory basic-boot-strap
  (union-theories
   (rewrite-free-theory
    (definition-free-theory
      (universal-theory 'ihs-theories)))
   (union-theories
    (theory 'built-ins)
    (union-theories
     (theory 'measures)
     '(car-cons cdr-cons car-cdr-elim))))
  :doc  ":doc-section ihs-theories
  A controlled boot-strap theory.
  ~/~/

  We begin with the theory at 'IHS-THEORIES (see :DOC IHS-THEORIES), and
  remove all of the :DEFINITION and :REWRITE rules.  To this theory we add
  back in the theories BUILT-INS, MEASURES, and the following 3 names:
  CAR-CONS, CDR-CONS, and CAR-CDR-ELIM.  This theory provides a controlled
  base for devloping books.  Note that this theory is of limited use without
  some simple theory of arithmetic such as the theory ALGEBRA from the book
  \"math-lemmas\".

  The key point of BASIC-BOOT-STRAP is to eliminate recursive definitions,
  and all of the random :REWRITE rules contained in the Acl2 boot-strap
  theory, while maintaining :EXECUTABLE-COUNTERPART and :TYPE-PRESCRIPTION
  rules.  Of course, many useful non-recursive definitions and useful lemmas
  have also been disabled, but other theories should take care of ENABLEing
  those as the need arises.~/")

