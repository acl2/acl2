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

(include-book "gensym")

(include-book "coi/lists/disjoint" :dir :system)
(include-book "coi/bags/basic" :dir :system)

;;
;; Given a list of bases, construct a new set of symbols
;;
(defun non-nil-symbol-listp (list)
  (if (atom list) (null list)
    (and (non-nil-symbolp (car list))
         (non-nil-symbol-listp (cdr list)))))

(defthm non-nil-symbol-listp-implies-symbol-listp
  (implies
   (non-nil-symbol-listp list)
   (and (true-listp list)
        (symbol-listp list)))
  :rule-classes (:forward-chaining))

(defthm non-nil-symbol-list-member
  (implies
   (and
    (list::memberp a list)
    (non-nil-symbol-listp list))
   (non-nil-symbolp a))
  :rule-classes :forward-chaining)

(defun gensym::gensym-list (list omit)
  (declare (type (satisfies true-listp) omit))
  (if (consp list)
      (let ((a (gensym::gensym (car list) omit)))
	(cons a (gensym::gensym-list (cdr list) (cons a omit))))
    nil))

(defthm gensym::len-gensym-list
  (equal (len (gensym::gensym-list list omit))
	 (len list)))

(defthm gensym::memberp-gensym-list-forward-1
  (implies
   (list::memberp a omit)
   (not (list::memberp a (gensym::gensym-list list omit))))
  :rule-classes (:rewrite
		 (:forward-chaining
		  :trigger-terms ((gensym::gensym-list list omit)))))

(defthm gensym::memberp-gensym-list-forward-2
  (implies
   (list::memberp a (gensym::gensym-list list omit))
   (not (list::memberp a omit)))
  :rule-classes (:rewrite :forward-chaining))

(defthm gensym::unique-gensym-list
  (bag::unique (gensym::gensym-list list omit))
  :rule-classes (:rewrite
		 (:forward-chaining
		  :trigger-terms ((gensym::gensym-list list omit)))))

(defthm gensym::disjoint-gensym-list
  (bag::disjoint (gensym::gensym-list list omit) omit)
  :rule-classes (:rewrite
		 (:forward-chaining
		  :trigger-terms ((gensym::gensym-list list omit)))))

(defthm gensym::non-nil-symbol-listp-gensym-list
  (non-nil-symbol-listp (gensym::gensym-list list omit))
  :rule-classes (:rewrite
		 (:forward-chaining
		  :trigger-terms ((gensym::gensym-list list omit)))))

;;
;; Given a base and a count, construct n new symbols from base.
;;

(defun gensym::gensym-n (n base omit)
  (declare (type (integer 0 *) n)
	   (type (satisfies true-listp) omit))
  (if (zp n) nil
    (let ((a (gensym::gensym base omit)))
      (cons a (gensym::gensym-n (1- n) base (cons a omit))))))


(defthm gensym::memberp-gensym-n-forward-1
  (implies
   (list::memberp a omit)
   (not (list::memberp a (gensym::gensym-n n base omit))))
  :rule-classes (:rewrite
		 (:forward-chaining
		  :trigger-terms ((gensym::gensym-n n base omit)))))

(defthm gensym::memberp-gensym-n-forward-2
  (implies
   (list::memberp a (gensym::gensym-n n base omit))
   (not (list::memberp a omit)))
  :rule-classes (:rewrite :forward-chaining))

(defthm gensym::len-gensym-n
  (equal (len (gensym::gensym-n n base omit))
	 (nfix n)))

(defthm gensym::unique-gensym-n
  (bag::unique (gensym::gensym-n n base omit))
  :rule-classes (:rewrite
		 (:forward-chaining
		  :trigger-terms ((gensym::gensym-n n base omit)))))

(defthm gensym::disjoint-gensym-n
  (bag::disjoint (gensym::gensym-n n base omit) omit)
  :rule-classes (:rewrite
		 (:forward-chaining
		  :trigger-terms ((gensym::gensym-n n base omit)))))

(defthm gensym::symbol-listp-gensym-n
  (non-nil-symbol-listp (gensym::gensym-n n base omit))
  :rule-classes (:rewrite
		 (:forward-chaining
		  :trigger-terms ((gensym::gensym-n n base omit)))))
