; Originally part of...
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

; In 2022, moved from books/xdoc/full-escape-symbol.lisp
; and from XDOC to ACL2 package, and fixed escaping of backslash.
; Eric McCarthy (mccarthy@kestrel.edu).

(in-package "ACL2")

(defun bar-escape-chars (x)
  (declare (xargs :guard (character-listp x)))
  (cond ((atom x)
         nil)
        ((eql (car x) #\|)
         (list* #\\ #\| (bar-escape-chars (cdr x))))
        ((eql (car x) #\\)
         (list* #\\ #\\ (bar-escape-chars (cdr x))))
        (t
         (cons (car x) (bar-escape-chars (cdr x))))))

(local
 (defthm character-listp-of-bar-escape-chars
   (implies (character-listp x)
            (character-listp (bar-escape-chars x)))))

(defun bar-escape-string (x)
  (declare (type string x))
  ;; Dumb optimization: don't need to escape anything unless there's a #\| or #\\
  ;; somewhere.
  (if (or (position #\| x) (position #\\ x))
      (coerce (bar-escape-chars (coerce x 'list)) 'string)
    x))

(defun bar-escape-name (x)
  (declare (type string x))
  (concatenate 'string "|" (bar-escape-string x) "|"))

(defun full-escape-symbol (x)
  (declare (type symbol x))
  (concatenate 'string
               (bar-escape-name (symbol-package-name x))
               "::"
               (bar-escape-name (symbol-name x))))
