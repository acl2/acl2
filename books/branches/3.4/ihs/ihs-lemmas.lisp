; ihs-lemmas.lisp  --  a top-level book INCLUDEing the IHS lemmas
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
;;;~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

(in-package "ACL2")

(include-book "math-lemmas")
(include-book "quotient-remainder-lemmas")
(include-book "logops-lemmas")

(deflabel ihs-lemmas
  :doc ":doc-section ihs-lemmas
  A simple interface to the books of lemmas in the IHS libaray.
  ~/~/

  Including the \"ihs-lemmas\" book includes all of the books of lemmas in
  the IHS library.  This book must always be included after the
  \"ihs-definitions\" book, e.g.,

  (INCLUDE-BOOK
   \"ihs-definitions\")
  (LOCAL (INCLUDE-BOOK
          \"ihs-lemmas\"))

  The above sequence extends the theory that existed before the inclusion of
  the books with those definitions and lemmas provided be the included books.
  To continue in a minimal theory that contains only the IHS libraries,
  invoke the macro MINIMAL-IHS-THEORY, e.g.,

  (LOCAL (MINIMAL-IHS-THEORY))~/")

(defmacro minimal-ihs-theory ()
  ":doc-section ihs-lemmas
  Set up a minimal theory based on the IHS library.
  ~/~/

  Executing the macro call

  (MINIMAL-IHS-THEORY)

  will set up a minimal theory based on the theories exported by the books in
  the IHS libraries.  This is the preferred way to use the IHS library.~/"

  `(PROGN
    (IN-THEORY NIL)
    (IN-THEORY
     (ENABLE
      BASIC-BOOT-STRAP                 ; From "ihs-theories"
      IHS-MATH                         ; From "math-lemmas"
      QUOTIENT-REMAINDER-RULES         ; From "quotient-remainder-lemmas"
      LOGOPS-LEMMAS-THEORY             ; From "logops-lemmas"
      INTEGER-RANGE-P                  ; new for Version_2.7; added by Matt
                                       ; Kaufmann, as suggested by Matt Wilding
      ))))

