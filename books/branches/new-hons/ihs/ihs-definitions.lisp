; ihs-definitions.lisp  --  a top-level book INCLUDEing the IHS definitions
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
  :doc ":doc-section ihs-definitions
  A simple interface to the books of definitions in the IHS library.
  ~/~/

  Including the \"ihs-definitions\" book includes all of the books of
  definitions in the IHS library.  Thus, for :RED mode specification, simply

  (INCLUDE-BOOK
   \"ihs-definitions\")

  at the beginning of a specification book.  For :BLUE or :GOLD mode, follow
  the above by including the book \"ihs-lemmas\", e.g.,

  (LOCAL (INCLUDE-BOOK
          \"ihs-lemmas\")).

  which will INCLUDE all of IHS lemma books.  See :DOC IHS-LEMMAS for more
  details.~/")

