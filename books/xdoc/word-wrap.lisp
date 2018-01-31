; XDOC Documentation System for ACL2
; Copyright (C) 2009-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "XDOC")
(include-book "std/util/bstar" :dir :system)
(include-book "std/strings/defs-program" :dir :system)
(program)


; NORMALIZE-WHITESPACE canonicalizes whitespace so that any adjacent
; whitespace characters are merged into a single space unless they
; occur at the end of a sentence, in which case they are merged into
; two spaces.

(defun normalize-whitespace-aux (x n xl acc)
  (b* (((when (>= n xl))
        acc)
       (char-n (char x n))
       (whitespace '(#\Space #\Tab #\Newline #\Page #\Return))
       (sentence-ends '(#\. #\! #\?))
       (closers '(#\" #\' #\` #\) #\] #\} #\>))
       (acc (cond
             ;; Keep all non-whitespace characters.
             ((not (member char-n whitespace))
              (cons char-n acc))
             ;; Keep a whitespace character (but convert it
             ;; specifically to a #\Space character) if:
             ;; - There's no whitespace immediately after it; or
             ;; - There is whitespace after it but a sentence ended
             ;;   right before it.
             ((or (>= (+ n 1) xl)
                  (not (member (char x (+ n 1)) whitespace))
                  (and (>= n 1)
                       (or (member (char x (- n 1)) sentence-ends)
                           (and (>= n 2)
                                (member (char x (- n 1)) closers)
                                (member (char x (- n 2)) sentence-ends)))))
              (cons #\Space acc))
             ;; Otherwise, merge it into the subsequent whitespace.
             (t acc))))
    (normalize-whitespace-aux x (+ n 1) xl acc)))

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
    (str::implode acc)))
