; ihs-lemmas.lisp  --  a top-level book INCLUDEing the IHS lemmas
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    ihs-lemmas.lisp
;;;
;;;    The top-level book of lemmas in the IHS (Integer Hardware
;;;    Specification) library.
;;;
;;;    Bishop Brock
;;;    Computational Logic, Inc.
;;;    1717 West 6th Street, Suite 290
;;;    Austin, Texas 78703
;;;    brock@cli.com
;;;
;;;    Modified for ACL2 Version_2.7 by:
;;;    Matt Kaufmann, kaufmann@cs.utexas.edu
;;;
;;;    Modified October 2014 by Jared Davis <jared@centtech.com>
;;;    Ported documentation to XDOC
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "ACL2")

(include-book "math-lemmas")
(include-book "quotient-remainder-lemmas")
(include-book "logops-lemmas")

(defxdoc ihs-lemmas
  :parents (ihs)
  :short "A simple interface to the books of lemmas in the IHS libaray."
  :long "<p>Including the @('ihs-lemmas') book includes all of the books of
lemmas in the IHS library.  This book is typically included after the
@('ihs-definitions') book, e.g.,</p>

@({
  (include-book \"ihs-definitions\")
  (local (include-book \"ihs-lemmas\"))
})

<p>The above sequence extends the theory that existed before the inclusion of
the books with those definitions and lemmas provided be the included books.</p>

<p>To continue in a minimal theory that contains only the IHS libraries, you
may wish to see @(see minimal-ihs-theory).</p>")

(defsection minimal-ihs-theory
  :parents (ihs-lemmas)
  :short "Set up a minimal theory based on the @(see ihs) library."

  :long "<box><p>Note: Jared recommends against using @('minimal-ihs-theory').
In particular, it invokes @('(in-theory nil)'), which is probably not a good
idea most of the time.</p></box>

<p>Executing the macro call</p>

@({
    (local (minimal-ihs-theory))
})

<p>will set up a minimal theory based on the theories exported by the books in
the IHS libraries.  This is Bishop's preferred way to use the IHS library.</p>

@(def minimal-ihs-theory)"

  (defmacro minimal-ihs-theory ()
    '(PROGN
      (IN-THEORY NIL)
      (IN-THEORY
       (ENABLE
        BASIC-BOOT-STRAP                 ; From "ihs-theories"
        IHS-MATH                         ; From "math-lemmas"
        QUOTIENT-REMAINDER-RULES         ; From "quotient-remainder-lemmas"
        LOGOPS-LEMMAS-THEORY             ; From "logops-lemmas"
        INTEGER-RANGE-P                  ; new for Version_2.7; added by Matt
                                         ; Kaufmann, as suggested by Matt Wilding
        )))))
