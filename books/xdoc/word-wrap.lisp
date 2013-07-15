; XDOC Documentation System for ACL2
; Copyright (C) 2009-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "XDOC")
(include-book "tools/bstar" :dir :system)
(include-book "str/cat" :dir :system)
(program)


; NORMALIZE-WHITESPACE canonicalizes whitespace so that any adjacent whitespace
; characters are merged into a single space.

(defun normalize-whitespace-aux (x n xl acc)
  (b* (((when (>= n xl))
        acc)
       (char-n (char x n))
       ((when (member char-n '(#\Space #\Tab #\Page #\Newline)))
        (normalize-whitespace-aux
         x (+ n 1) xl
         (if (and (< (+ n 1) xl)
                  (member (char x (+ n 1)) '(#\Space #\Tab #\Page #\Newline)))
             acc
           (cons #\Space acc)))))
    (normalize-whitespace-aux x (+ n 1) xl (cons char-n acc))))

(defun normalize-whitespace (x)
  (declare (type string x))
  (str::rchars-to-string (normalize-whitespace-aux x 0 (length x) nil)))


; (WORD-WRAP-PARAGRAPH X INDENT WRAP-COL) reformats the string X, trying to
; word wrap to WRAP-COL and indenting each subsequent line to INDENT.  We
; assume that indent-many characters have already been printed, so the first
; line is not indented.

(defun add-word-to-paragraph (x n xl col acc)
  "Returns (MV N COL ACC)"
  (b* (((when (>= n xl))
        (mv n col acc))
       (char-n (char x n))
       ((when (eql char-n #\Space))
        (mv n col acc)))
    (add-word-to-paragraph x (+ n 1) xl (+ 1 col) (cons char-n acc))))

(defun remove-spaces-from-front (x)
  (if (atom x)
      x
    (if (eql (car x) #\Space)
        (remove-spaces-from-front (cdr x))
      x)))

(defun word-wrap-paragraph-aux (x n xl col wrap-col indent acc)
  (b* (((when (>= n xl))
        acc)
       (char-n (char x n))
       ((when (eql char-n #\Space))
        (word-wrap-paragraph-aux x (+ n 1) xl (+ col 1)
                                 wrap-col indent (cons char-n acc)))
       ((mv spec-n spec-col spec-acc)
        (add-word-to-paragraph x n xl col acc))
       ((when (or (< spec-col wrap-col)
                  (= col indent)))
        ;; Either (1) it fits, or (2) we can't get any more space by moving to
        ;; the next line anyway, so accept this speculative addition.
        (word-wrap-paragraph-aux x spec-n xl spec-col wrap-col indent spec-acc))
       ;; Else, try again, starting on the next line.
       (acc (remove-spaces-from-front acc)) ;; deletes trailing spaces on this line
       (acc (cons #\Newline acc))
       (acc (append (make-list indent :initial-element #\Space) acc)))
    (word-wrap-paragraph-aux x n xl indent wrap-col indent acc)))

(defun word-wrap-paragraph (x indent wrap-col)
  (let* ((acc (word-wrap-paragraph-aux x 0 (length x) 0 wrap-col indent nil))
         (acc (remove-spaces-from-front acc))
         (acc (reverse acc))
         (acc (remove-spaces-from-front acc)))
    (coerce acc 'string)))
