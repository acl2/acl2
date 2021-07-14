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
; cert_param: (non-acl2r)
(include-book "ordinals/lexicographic-ordering" :dir :system)

(defun o1-test (o1)
  (declare (type t o1))
  (and (consp o1)
       (o-p (car o1))
       (or (equal (cdr o1) 3)
	   (equal (cdr o1) 2)
	   (equal (cdr o1) 1))))

(defun o2-test (o2)
  (declare (type t o2))
  (and (consp o2)
       (o-p (car o2))
       (equal (cdr o2) 1)))

(defun oconsp (x)
  (declare (type t x))
  (and (o-p x)
       (consp x)
       (let ((o1 (car x)))
	 (and (o1-test o1)
	      (if (equal (cdr o1) 3)
		  (equal (cdr x) 0)
		(and (consp (cdr x))
		     (let ((o2 (cadr x)))
		       (o2-test o2))
		     (equal (cddr x) 0)))))))

(defun ocons (x y)
  (declare (type (satisfies o-p) x y))
  (if (o< x y)
      `((,(o+ y 1) . 2) (,(o+ x 1) . 1) . 0)
    (if (o< y x)
	`((,(o+ x 1) . 1) (,(o+ y 1) . 1) . 0)
      `((,(o+ x 1) . 3) . 0))))

(defun polarity (x)
  (declare (type (satisfies oconsp) x))
  (cdar x))

(defun ocar (x)
  (declare (type (satisfies oconsp) x))
  (let ((p (polarity x)))
    (cond
     ((= p 3)
      (caar x))
     ((= p 2)
      (caadr x))
     (t
      (caar x)))))

(defun ocdr (x)
  (declare (type (satisfies oconsp) x))
  (let ((p (polarity x)))
    (cond
     ((= p 3)
      (caar x))
     ((= p 2)
      (caar x))
     (t
      (caadr x)))))

(defthm ocdr-ocons
  (implies
   (and
    (o-p x)
    (o-p y))
   (equal (ocdr (ocons x y))
	  (o+ y 1))))

(defthm ocar-ocons
  (implies
   (and
    (o-p x)
    (o-p y))
   (equal (ocar (ocons x y))
	  (o+ x 1))))

(encapsulate
 ()

 (local (in-theory (enable o-p O-FINP O-RST O-FIRST-COEFF O-FIRST-EXPT)))

 (defthm oconsp-ocons
   (implies
    (and
     (o-p x)
     (o-p y))
    (oconsp (ocons x y))))

 (defthm op-ocons
   (implies
    (and
     (o-p x)
     (o-p y))
    (o-p (ocons x y))))

 (defthm oconsp-equal
   (implies
    (and
     (oconsp x)
     (oconsp y))
    (equal (equal x y)
	   (and (equal (ocar x) (ocar y))
		(equal (ocdr x) (ocdr y))))))

 )

;; We can now use the ordinals to encode structure.  The
;; rest is a simple matter of programming :)

(in-theory (disable ocons ocar ocdr oconsp))

;;

(defun len-len-induction (x y)
  (declare (xargs :measure (+ (len x) (len y))))
  (if (and (consp x) (consp y))
      (len-len-induction (cdr x) (cdr y))
    (if (consp x)
	(len-len-induction (cdr x) y)
      (if (consp y)
	  (len-len-induction x (cdr y))
	(list x y)))))

(defthmd ordinal-double-containment-expensive
  (implies
   (and
    (o-p x)
    (o-p y))
   (equal (equal x y)
	  (and (not (o< x y))
	       (not (o< y x))))))

(defun chartoo (x)
  (declare (type character x))
  (char-code x))

(defthm op-chartoo
  (o-p (chartoo x)))

(encapsulate
 ()

 (local
  (encapsulate
   ()

   (DEFthm CODE-CHAR-CHAR-CODE-IS-IDENTITY-weaker
     (IMPLIES (CHARACTERP C)
	      (EQUAL (CODE-CHAR (CHAR-CODE C)) C)))

   (in-theory (disable CODE-CHAR-CHAR-CODE-IS-IDENTITY))

   (defthm characterp-reduction
     (equal (characterp x)
	    (equal x (code-char (char-code x)))))

   ))

 (defthm equal-chartoo-reduction
   (implies
    (and
     (characterp x)
     (characterp y))
    (equal (equal (chartoo x) (chartoo y))
	   (equal x y))))

 )

(in-theory (disable chartoo))

(defun char-listoo (x)
  (declare (type (satisfies character-listp) x))
  (if (consp x)
      (ocons (chartoo (car x))
	     (char-listoo (cdr x)))
    0))

(defthm op-char-listoo
  (o-p (char-listoo x)))

(defthm equal-char-listoo-reduction
  (implies
   (and
    (character-listp x)
    (character-listp y))
   (equal (equal (char-listoo x) (char-listoo y))
	  (equal x y)))
  :hints (("Goal" :induct (len-len-induction x y))
	  (and stable-under-simplificationp
	       '(:in-theory (e/d (ordinal-double-containment-expensive)
				 (|0 < a  =  ~(a = 0)|))))))

(defun stringtoo (x)
  (declare (type string x))
  (char-listoo (coerce x 'list)))

(defthm op-stringtoo
  (o-p (stringtoo x)))

(defthm equal-coerce-reduction
  (implies
   (and
    (stringp x)
    (stringp y))
   (equal (equal (coerce x 'list) (coerce y 'list))
	  (equal x y)))
  :hints (("Goal" :in-theory (disable COERCE-INVERSE-2)
	   :cases ((equal x (coerce (coerce x 'list) 'string))))
	  ("Subgoal 2" :in-theory (enable COERCE-INVERSE-2))
	  ("Subgoal 1" :in-theory (disable COERCE-INVERSE-2)
	   :cases ((equal y (coerce (coerce y 'list) 'string))))
	  ("Subgoal 1.2" :in-theory (enable COERCE-INVERSE-2))))

(defthm equal-stringtoo-reduction
  (implies
   (and
    (stringp x)
    (stringp y))
   (equal (equal (stringtoo x) (stringtoo y))
	  (equal x y))))

(in-theory (disable stringtoo))

(defun symboltoo (x)
  (declare (type symbol x))
  (ocons (stringtoo (symbol-package-name x))
	 (stringtoo (symbol-name x))))

(defthm op-symboltoo
  (implies
   (symbolp x)
   (o-p (symboltoo x)))
  :hints (("Goal" :in-theory (enable symboltoo))))

(defthm equal-0+-1-reduction
  (implies
   (and
    (o-p x)
    (o-p y))
   (equal (equal (o+ x 1)
		 (o+ y 1))
	  (equal x y)))
  :hints (("Goal" :in-theory (e/d (ordinal-double-containment-expensive)
				  (|0 < a  =  ~(a = 0)|)))))

(defthmd equal-string-double-containment-expensive
  (implies
   (and
    (stringp x)
    (stringp y))
   (equal (equal x y)
	  (and (not (string< x y))
	       (not (string< y x)))))
  :hints (("Goal" :in-theory (enable string<))))

(defthmd equal-symbol-double-containment-expensive
  (implies
   (and
    (symbolp x)
    (symbolp y))
   (equal (equal x y)
	  (and (not (symbol< x y))
	       (not (symbol< y x))))))


(defthm equal-symboltoo-reduction
  (implies
   (and
    (symbolp x)
    (symbolp y))
   (equal (equal (symboltoo x) (symboltoo y))
	  (equal x y)))
  :hints (("goal" :in-theory (enable
			      equal-string-double-containment-expensive
			      ))
	  ("Subgoal 5" :in-theory (e/d
				   (symbol< equal-symbol-double-containment-expensive)
				   (SYMBOL<-TRICHOTOMY)))))

(in-theory (disable symboltoo))

(defun intoo (x)
  (declare (type integer x))
  (if (< x 0) (ocons 0 (- x))
    (ocons 1 x)))

(defthm equal-intoo-reduction
  (implies
   (and
    (integerp x)
    (integerp y))
   (equal (equal (intoo x) (intoo y))
	  (equal x y))))

(defthm op-intoo
  (implies
   (integerp x)
   (o-p (intoo x))))

(in-theory (disable intoo))

(defun rationaltoo (x)
  (declare (type rational x))
  (let ((n (numerator x))
	(d (denominator x)))
    (ocons (intoo n)
	   (intoo d))))

(defthm op-rationaltoo
  (implies
   (rationalp x)
   (o-p (rationaltoo x))))

(defthmd equal-rational-reduction
  (implies
   (and
    (syntaxp (and (symbolp x) (symbolp y)))
    (rationalp x)
    (rationalp y))
   (equal (equal x y)
	  (equal (* (/ (DENOMINATOR X)) (NUMERATOR X))
		 (* (/ (DENOMINATOR y)) (NUMERATOR y))))))


(defthm equal-rationaltoo-reduction
  (implies
   (and
    (rationalp x)
    (rationalp y))
   (equal (equal (rationaltoo x) (rationaltoo y))
	  (equal x y)))
  :hints (("Goal" :in-theory (e/d (equal-rational-reduction)
				  (EQUAL-*-/-1 RATIONAL-IMPLIES2)))
	  (and stable-under-simplificationp
	       '(:in-theory (current-theory :here)))))

(in-theory (disable rationaltoo))

(defun complextoo (x)
  (declare (type complex x))
  (let ((r (realpart x))
	(i (imagpart x)))
    (ocons (rationaltoo r)
	   (rationaltoo i))))

(defthm op-complextoo
  (implies
   (complex-rationalp x)
   (o-p (complextoo x))))

(defthm equal-complextoo-reduction
  (implies
   (and
    (complex-rationalp x)
    (complex-rationalp y))
   (equal (equal (complextoo x) (complextoo y))
	  (equal x y))))

(in-theory (disable complextoo))

(defun numtoo (x)
  (declare (type (satisfies acl2-numberp) x))
  (if (COMPLEX-RATIONALP x)
      (ocons 0 (complextoo x))
    (ocons 1 (rationaltoo x))))

(defthm op-numtoo
  (implies
   (acl2-numberp x)
   (o-p (numtoo x))))

(defthm equal-numtoo-reduction
  (implies
   (and
    (acl2-numberp x)
    (acl2-numberp y))
   (equal (equal (numtoo x) (numtoo y))
	  (equal x y))))

(in-theory (disable numtoo))

(defun atomtoo (x)
  (declare (type (satisfies atom) x))
  (cond
   ((acl2-numberp x)
    (ocons 0 (numtoo x)))
   ((symbolp x)
    (ocons 1 (symboltoo x)))
   ((characterp x)
    (ocons 2 (chartoo x)))
   ((stringp x)
    (ocons 3 (stringtoo x)))
   (t
    (ocons 4 0))))

(defun good-atom (x)
  (declare (type t x))
  (or (acl2-numberp x)
      (symbolp x)
      (characterp x)
      (stringp x)))

(defthm equal-atomtoo-reduction
  (implies
   (and
    (good-atom x)
    (good-atom y))
   (equal (equal (atomtoo x) (atomtoo y))
	  (equal x y))))

(defthm op-atomtoo
  (o-p (atomtoo x)))

(in-theory (disable atomtoo))
(in-theory (disable good-atom))

(defun good-term (x)
  (declare (type t x))
  (if (consp x)
      (and (good-term (car x))
	   (good-term (cdr x)))
    (good-atom x)))

(defun *too (x)
  (declare (type t x)
	   (xargs :verify-guards nil))
  (if (consp x)
      (ocons 0 (ocons (*too (car x))
		      (*too (cdr x))))
    (ocons 1 (atomtoo x))))

(defthm op-*too
  (o-p (*too x)))

(verify-guards *too)

(defun *too-induction (x y)
  (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
  (if (consp x)
      (if (consp y)
	  (cons (*too-induction (car x) (car y))
		(*too-induction (cdr x) (cdr y)))
	(cons (*too-induction (car x) y)
	      (*too-induction (cdr x) y)))
    (if (consp y)
	(cons (*too-induction x (car y))
	      (*too-induction x (cdr y)))
      (list x y))))

(defthmd equal-*too-reduction
  (implies
   (and
    (good-term x)
    (good-term y))
   (equal (equal x y)
	  (equal (*too x) (*too y))))
  :hints (("Goal" :induct (*too-induction x y))))

(defun o<< (x y)
  (declare (type t x y))
  (o< (*too x) (*too y)))

(in-theory (disable *too))
(in-theory (disable good-term))

(defthmd ordinal-order-property
  (implies
   (and (good-term x)
	(good-term y))
   (equal (equal x y)
	  (and (not (o<< x y))
	       (not (o<< y x)))))
  :hints (("Goal" :in-theory (enable equal-*too-reduction
				     ordinal-double-containment-expensive))))

(defthm o<<-is-well-founded
  (and (o-p (*too x))
       (implies (o<< x y)
		(o< (*too x) (*too y))))
  :rule-classes (:well-founded-relation))

(in-theory (disable o<<))
