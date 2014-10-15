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
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "ACL2")

(include-book "ihs-init")
(include-book "ihs-theories")
(include-book "logops-definitions")

(deflabel ihs-definitions
  :doc ":doc-section ihs
  A simple interface to the books of definitions in the IHS library.
  ~/~/

  Including the \"ihs-definitions\" book includes all of the books of
  definitions in the IHS library.  Thus, for :PROGRAM mode specification,
  simply
  ~bv[]
  (INCLUDE-BOOK
   \"ihs-definitions\")
  ~ev[]
  at the beginning of a specification book.  If you want to do proofs, then
  also include the book \"ihs-lemmas\", e.g.,
  ~bv[]
  (LOCAL (INCLUDE-BOOK
          \"ihs-lemmas\")).
  ~ev[]
  which will INCLUDE all of IHS lemma books.  See :DOC IHS-LEMMAS for more
  details.~/")

