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

(include-book "../symbol-fns/symbol-fns")

(defmacro def::fix (fix equiv &key (in-theory 'nil))

  (let ((equiv-implies-equal-fix-1 (symbol-fns::suffix equiv '_implies_equal fix '_1))
	(fix-fixes                 (symbol-fns::suffix fix '_fixes))
	(equal-fix-implies-equiv   (symbol-fns::prefix 'equal_ fix '_implies_ equiv))
	(equiv-fix-reduction       (symbol-fns::suffix equiv '_ fix '_reduction))
	(fixed-p                   (symbol-fns::suffix fix 'ed-p))
	(fixed-p-fix               (symbol-fns::suffix fix 'ed-p_ fix))
	(equal-fix-to-equiv        (symbol-fns::prefix 'equal_ fix '_to_ equiv)))

  `(encapsulate
       ()

     ,@(and in-theory `((local (in-theory ,in-theory))))

     (defchoose ,fix x (y)
       (,equiv x y)
       :strengthen t)

     (encapsulate
	 ()

       (defthm ,equiv-implies-equal-fix-1
	 (implies (,equiv y y1)
		  (equal (,fix y) (,fix y1)))
	 :hints (("Goal" :use ,fix))
	 :rule-classes (:congruence))

       (defthm ,fix-fixes
	 (,equiv (,fix x) x)
	 :hints (("Goal" :use ((:instance ,fix (y x))))))

       ;; anything that fixes to this point is equiv

       (local
	(defthm any-fix-is-equiv
	  (implies (equal y (,fix x))
		   (,equiv y x))
	  :rule-classes nil)
	)

       (local
	(defthmd ,equal-fix-implies-equiv
	  (implies (equal (,fix y) (,fix x))
		   (equal (,equiv y x) t))
	  :hints (("Goal" :use (:instance any-fix-is-equiv (y (,fix y))))))
	)

       (defthmd ,equiv-fix-reduction
	 (equal (,equiv x y)
		(equal (,fix x) (,fix y)))
	 :hints (("Goal" :in-theory (enable ,equal-fix-implies-equiv))))

       (defund ,fixed-p (x)
	 (equal x (,fix x)))

       (in-theory (disable (,fixed-p)))

       (defthm ,fixed-p-fix
	 (,fixed-p (,fix x))
	 :rule-classes (:rewrite
			(:forward-chaining :trigger-terms ((,fix x))))
	 :hints (("Goal" :in-theory (enable ,fixed-p))))

       (defthm setfixed-p-setfix-reduction
	 (implies
	  (,fixed-p x)
	  (equal (,fix x) x))
	 :hints (("Goal" :in-theory (enable ,fixed-p))))

       (defthm ,equal-fix-to-equiv
	 (equal (equal (,fix x) y)
		(and (,fixed-p y)
		     (,equiv x y)))
	 :hints (("Goal" :in-theory (enable ,fixed-p ,equiv-fix-reduction))))

       (theory-invariant (incompatible (:rewrite ,equal-fix-to-equiv)
				       (:rewrite ,equiv-fix-reduction)))

       ))))

(local
 (encapsulate
     ()

   (defun myeq (x y)
     (equal x y))

   (defequiv myeq)

   (in-theory (disable myeq))

   (def::fix myfix myeq :in-theory '(myeq-is-an-equivalence))

   ))