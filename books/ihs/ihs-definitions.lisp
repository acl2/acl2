; ihs-definitions.lisp  --  a top-level book INCLUDEing the IHS definitions
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
;;;
;;;    ihs-definitions.lisp
;;;
;;;    The top-level book of definitions in the IHS (Integer Hardware
;;;    Specification) library.
;;;
;;;    Bishop Brock
;;;    Computational Logic, Inc.
;;;    1717 West 6th Street, Suite 290
;;;    Austin, Texas 78703
;;;    brock@cli.com
;;;
;;;    Modified October 2014 by Jared Davis <jared@centtech.com>
;;;    Ported documentation to XDOC
;;;
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "ACL2")

(include-book "ihs-init")
(include-book "ihs-theories")
(include-book "logops-definitions")

(defxdoc ihs-definitions
  :parents (ihs)
  :short "The @('ihs-definitions') book is a simple interface to the books of
definitions in the @(see ihs) library."

  :long "<p>Including the \"ihs-definitions\" book includes all of the books of
definitions in the IHS library.  Thus, for :PROGRAM mode specification,
simply</p>

@({
    (include-book \"ihs-definitions\")
})

<p>at the beginning of a specification book.  If you want to do proofs, then
also include the book \"ihs-lemmas\", e.g.,</p>

@({
    (local (include-book \"ihs-lemmas\"))
})

<p>which will include all of ihs lemma books; see @(see ihs-lemmas).</p>")
