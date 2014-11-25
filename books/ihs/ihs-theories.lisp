; ihs-theories.lisp -- subtheories of ACL2 boot-strap theory
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

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
;;;    Modified October 2014 by Jared Davis <jared@centtech.com>
;;;    Ported documentation to XDOC
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "ACL2")

(include-book "ihs-init")

(deflabel ihs-theories)

(defxdoc ihs-theories
  :parents (ihs)
  :short "Subtheories of the ACL2 initialization theory."

  :long "<box><p>Note: Jared recommends against following the advice below.  In
particular, using @('(in-theory nil)') is probably not a good idea most of the
time.</p></box>

<p>The conventional way to initiate the definition of a book in the IHS library
hierarchy is to</p>

<ul>
<li>Include all necessary books</li>
<li>DISABLE the world with (IN-THEORY NIL), and</li>
<li>Construct the theory needed to certify
  the present book from theory expressions supplied by the included books.</li>
</ul>

<p>The @('ihs-theories') book includes the most basic theories, i.e., theories
of the ACL2 functions available at this label: 'IHS-THEORIES, which is exactly
the extension of the ACL2 initialization theory made by \"ihs-init\".  Every
IHS book will normally begin by ENABLEing one of these theories.  Some of the
theories may also be useful, for example, to specify very restricted local
theories for specialized apllications.</p>")

(defsection built-ins
  :parents (ihs-theories)
  :short "Functions whose definitions are \"built in\" to ACL2."
  :long "<p>If you execute (IN-THEORY NIL), ACL2 prints a warning that the
empty theory does not contain the :DEFINITION rules for certain functions whose
definitions are built into ACL2 at various places.  This theory contains the
DEFUN-THEORY (see :DOC DEFUN-THEORY) of exactly those functions named in that
message.</p>"

  (deftheory built-ins
    (defun-theory
      '(IFF NOT IMPLIES EQ ATOM EQL = /= NULL ENDP
            ZEROP SYNP PLUSP MINUSP
            LISTP
            ;; Changed by Matt K. after v4-1, from PROG2$ to:
            RETURN-LAST
            FORCE CASE-SPLIT))))

(defsection measures
  :parents (ihs-theories)
  :short "Functions used to prove admissibility."
  :long "<p>This theory contains the DEFUN-THEORY (see :DOC DEFUN-THEORY) of
all functions (except those in (THEORY BUILT-INS)) that are necessary to prove
the admissibility of recursive functions in most cases.  Note that this theory
is probably useless without the theory BUILT-INS and some simple theory of
arithmetic (such as the theory ALGEBRA from the book \"math-lemmas\".</p>

<p>For functions that recur on the length of a string you may have to ENABLE
LENGTH and LEN, as we steadfastly refuse to allow ANY globally enabled
recursive functions.</p>"

  (deftheory measures
    (defun-theory
      '(O< O-P NATP POSP O-FINP ACL2-COUNT CONSP CAR CDR RATIONALP
           INTEGERP < STRINGP INTEGER-ABS NUMERATOR DENOMINATOR
           FIX RFIX IFIX NFIX ZIP ZP))))


(defsection basic-boot-strap
  :parents (ihs-theories)
  :short "A controlled boot-strap theory."

  :long "<p>We begin with the theory at 'IHS-THEORIES (see :DOC IHS-THEORIES),
and remove all of the :DEFINITION and :REWRITE rules.  To this theory we add
back in the theories BUILT-INS, MEASURES, and the following 3 names: CAR-CONS,
CDR-CONS, and CAR-CDR-ELIM.  This theory provides a controlled base for
devloping books.  Note that this theory is of limited use without some simple
theory of arithmetic such as the theory ALGEBRA from the book
\"math-lemmas\".</p>

<p>The key point of BASIC-BOOT-STRAP is to eliminate recursive definitions, and
all of the random :REWRITE rules contained in the ACL2 boot-strap theory, while
maintaining :EXECUTABLE-COUNTERPART and :TYPE-PRESCRIPTION rules.  Of course,
many useful non-recursive definitions and useful lemmas have also been
disabled, but other theories should take care of ENABLEing those as the need
arises.</p>"

  (deftheory basic-boot-strap
    (union-theories
     (rewrite-free-theory
      (definition-free-theory
        (universal-theory 'ihs-theories)))
     (union-theories
      (theory 'built-ins)
      (union-theories
       (theory 'measures)
       '(car-cons cdr-cons car-cdr-elim))))))
