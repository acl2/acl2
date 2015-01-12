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

(in-package "LIST")

;; This should be multiple files, one per function

(include-book "remove")

;; Rules that otherwise eliminate removes

(in-theory (disable subset-remove-reduction-2))
(in-theory (disable subset-remove-reduction-1))
(in-theory (disable remove-list-remove-reduction-2))
(in-theory (disable remove-list-remove-reduction-1-alt))
(in-theory (disable remove-list-remove-reduction-1))

(defun remove-induction-1 (x)
  (declare (xargs :measure (len x)))
  (if (consp x)
      (remove-induction-1 (remove (car x) x))
    x))

(defun remove-induction-2 (x y)
  (declare (xargs :measure (len x)))
  (if (consp x)
      (remove-induction-2 (remove (car x) x) (remove (car x) y))
    (list x y)))

(defun remove-induction-3 (x y z)
  (declare (xargs :measure (len x)))
  (if (consp x)
      (remove-induction-3 (remove (car x) x) (remove (car x) y) (remove (car x) z))
    (list x y z)))

(defthm memberp-from-consp-fwd
  (implies
   (consp x)
   (memberp (car x) x))
  :rule-classes (:forward-chaining))

(defthmd open-memberp-on-memberp
  (implies
   (memberp a list)
   (equal (memberp b list)
	  (if (equal b a) t
	    (memberp b (remove a list))))))

(defthm memberp-remove-definition
  (equal (memberp a x)
	 (if (consp x)
	     (or (equal a (car x))
		 (memberp a (remove (car x) x)))
	   nil))
  :hints (("Goal" :in-theory (enable open-memberp-on-memberp)))
  :rule-classes (:definition))


(defthm open-subsetp-on-memberp
  (implies
   (memberp a x)
   (equal (subsetp x y)
	  (and (memberp a y)
	       (subsetp (remove a x) (remove a y))))))

; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced subsetp by subsetp-equal).]
(defthm subsetp-remove-definition
  (equal (subsetp-equal x y)
	 (if (consp x)
	     (and (memberp (car x) y)
		  (subsetp-equal (remove (car x) x) (remove (car x) y)))
	   t))
  :hints (("Goal" :in-theory (disable SUBSET-BY-MULTIPLICITY)))
  :rule-classes (:definition))

(defthm open-remove-list-on-memberp
  (implies
   (memberp a x)
   (equal (remove-list x y)
	  (remove-list (remove a x) (remove a y))))
  :hints (("Goal" :in-theory `(remove-list-remove-reduction-1-ALT
			       REMOVE-LIST-REMOVE-REDUCTION-2
			       MEMBERP-REMOVE
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;			       (:TYPE-PRESCRIPTION MEMBERP)
;			       (:TYPE-PRESCRIPTION REMOVE)
			       ))))

(in-theory (enable remove-list-remove-definition))