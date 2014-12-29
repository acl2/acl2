; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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


(in-package "ACL2")

(include-book "syntaxp")
(include-book "misc/total-order" :dir :system)

(defun subterm-rec (x y)
  (declare (type t x y))
  (if (consp y)
      (let ((term (car y)))
	(or (equal x term)
	    (and (consp term)
		 (subterm-rec x (cdr term)))
	    (subterm-rec x (cdr y))))
    nil))

(defun subterm-p (x y)
  (declare (type t x y))
  (and (consp y)
       (subterm-rec x (cdr y))))

;; We rewrite larger symbols into smaller symbols and smaller (non
;; constant) terms into larger terms.

;; What about (equiv ram (goo ram)) ?  - presumably we would want to
;; eliminate (goo ram) ?  Which is to say, if one is a subterm of the
;; other, prehaps we should collapse the larger term into the smaller
;; term ?

(defun good-rewrite-order (x y)
  (declare (xargs :mode :program))
  (if (and (symbolp x)
	   (symbolp y))
      (smaller-term y x)
    (if (quotep x)
	(and (quotep y)
	     (<< (cadr y) (cadr x)))
      (or (quotep y)
	  (and (smaller-term x y)
	       (not (subterm-p x y)))
	  (subterm-p y x)))))