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

(in-package "SYMBOL-FNS")
(include-book "../symbol-fns/symbol-fns")

(defun collect-variables-rec (fn term res)
  (declare (type t fn term res))
  (if (consp term)
      (if (consp (car term))
	  (let ((res (collect-variables-rec t (car term) res)))
	    (collect-variables-rec nil (cdr term) res))
	(if fn (collect-variables-rec nil (cdr term) res)
	  (let ((res (append (if (symbolp (car term)) (list (car term)) nil)
			     res)))
	    (collect-variables-rec nil (cdr term) res))))
    res))

(defthm symbol-listp-collect-variables-rec
  (implies
   (symbol-listp res)
   (symbol-listp (collect-variables-rec fn term res)))
  :rule-classes (:type-prescription :rewrite))

(defthm true-listp-collect-variables-rec
  (implies
   (true-listp res)
   (true-listp (collect-variables-rec fn term res)))
  :rule-classes (:type-prescription :rewrite))

(defmacro collect-variables (term)
  `(remove-duplicates-equal (collect-variables-rec t ,term nil)))

(defun join-lists (list1 list2)
  (declare (type t list1 list2))
  (if (and (consp list1)
	   (consp list2))
      (cons (list (car list1) (car list2))
	    (join-lists (cdr list1) (cdr list2)))
    nil))