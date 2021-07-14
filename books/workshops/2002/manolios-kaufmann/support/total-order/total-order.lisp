; Copyright (C) 2001  Georgia Institute of Technology

; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by: Panagiotis Manolios who can be reached as follows.

; Email: manolios@cc.gatech.edu

; Postal Mail:
; College of Computing
; CERCS Lab
; Georgia Institute of Technology
; 801 Atlantic Drive
; Atlanta, Georgia 30332-0280 U.S.A.

; Certify with ACL2 version 2.5

(in-package "ACL2")

(defun bad-atom (x)
  (not (or (consp x)
           (acl2-numberp x)
           (symbolp x)
           (characterp x)
           (stringp x))))

(defstub bad-atom<= (* *) => *)

(defmacro boolp (x)
  `(or (equal ,x t)
       (equal ,x nil)))

(defaxiom boolp-bad-atom<=
  (boolp (bad-atom<= x y))
  :rule-classes :type-prescription)

(defaxiom bad-atom<=-anti-symmetric
  (implies (and (bad-atom x)
                (bad-atom y)
                (bad-atom<= x y)
                (bad-atom<= y x))
           (equal x y))
  :rule-classes nil)

(defaxiom bad-atom<=-transitive
  (implies (and (bad-atom<= x y)
                (bad-atom<= y z)
                (bad-atom x)
                (bad-atom y)
                (bad-atom z))
           (bad-atom<= x z)))

(defaxiom bad-atom<=-total
  (implies (and (bad-atom x)
                (bad-atom y))
           (or (bad-atom<= x y)
               (bad-atom<= y x)))
  :rule-classes nil)

(defun atom-order (x y)
  (cond ((rationalp x)
	 (if (rationalp y)
	     (<= x y)
	   t))
	((rationalp y) nil)
	((complex-rationalp x)
	 (if (complex-rationalp y)
	     (or (< (realpart x) (realpart y))
		 (and (= (realpart x) (realpart y))
		      (<= (imagpart x) (imagpart y))))
	   t))
	((complex-rationalp y)
	 nil)
	((characterp x)
	 (if (characterp y)
	     (<= (char-code x)
		 (char-code y))
	   t))
	((characterp y) nil)
	((stringp x)
	 (if (stringp y)
	     (and (string<= x y) t)
	   t))
	((stringp y) nil)
	((symbolp x)
	 (if (symbolp y)
	     (not (symbol< y x))
	   t))
	((symbolp y) nil)
	(t (bad-atom<= x y))))

(local
 (defthm bad-atom<=-reflexive
   (implies (bad-atom x)
            (bad-atom<= x x))
   :hints (("Goal"
            :by (:instance bad-atom<=-total (y x))))))

(local
 (defthm bad-atom<=-total-rewrite
   (implies (and (not (bad-atom<= y x))
                 (bad-atom x)
                 (bad-atom y))
            (bad-atom<= x y))
   :hints (("Goal"
            :by (:instance bad-atom<=-total)))
   :rule-classes :forward-chaining))

(local
 (defthm equal-coerce
   (implies (and (stringp x)
		 (stringp y))
	    (equal (equal (coerce x 'list)
			  (coerce y 'list))
                   (equal x y)))
   :hints (("Goal" :use
	    ((:instance coerce-inverse-2 (x x))
	     (:instance coerce-inverse-2 (x y)))
	    :in-theory (disable coerce-inverse-2)))))

(local
 (defthm boolp-atom-order
   (boolp (atom-order x y))
   :rule-classes :type-prescription))

(local
 (defthm atom-order-reflexive
   (implies (atom x)
            (atom-order x x))))

(local
 (defthm string<=-l-transitive-at-0
   (implies (and (not (string<-l y x 0))
                 (not (string<-l z y 0))
                 (character-listp x)
                 (character-listp y)
                 (character-listp z))
            (not (string<-l z x 0)))
   :hints
   (("Goal" :use (:instance string<-l-transitive
                            (i 0) (j 0) (k 0))))))

(local
 (defthm atom-order-transitive
   (implies (and (atom-order x y)
                 (atom-order y z)
                 (atom x)
                 (atom y)
                 (atom z))
            (atom-order x z))
   :hints (("Goal"
            :in-theory (enable string< symbol<)))))

(local
 (defthm atom-order-anti-symmetric
   (implies (and (atom x)
                 (atom y)
                 (atom-order x y)
                 (atom-order y x))
            (equal x y))
   :hints (("Goal"
            :in-theory (union-theories
                        '(string< symbol<)
                        (disable code-char-char-code-is-identity))
            :use ((:instance symbol-equality (s1 x) (s2 y))
                  (:instance bad-atom<=-anti-symmetric)
                  (:instance code-char-char-code-is-identity (c y))
                  (:instance code-char-char-code-is-identity (c x)))))
   :rule-classes
   ((:forward-chaining :corollary
                       (implies (and (atom-order x y)
                                     (not (consp x))
                                     (not (consp y)))
                                (iff (atom-order y x)
                                     (equal x y)))
                       :hints (("Goal" :in-theory
                                (disable atom-order)))))))

(local
 (defthm atom-order-total
   (implies (and (atom x)
                 (atom y))
            (or (atom-order x y)
		(atom-order y x)))
   :hints (("Goal" :use (:instance bad-atom<=-total)
            :in-theory (enable string< symbol<)))
   :rule-classes
   ((:forward-chaining :corollary
                       (implies (and (not (atom-order x y))
                                     (not (consp x))
                                     (not (consp y)))
                                (atom-order y x))))))

(in-theory (disable atom-order))

(defun total-order (x y)
  (cond ((atom x)
         (cond ((atom y)
                (atom-order x y))
               (t t)))
        ((atom y) nil)
        ((equal (car x) (car y))
         (total-order (cdr x) (cdr y)))
        (t (total-order (car x) (car y)))))

(defthm boolp-total-order
  (boolp (total-order x y))
  :rule-classes :type-prescription)

(defthm total-order-reflexive
  (total-order x x))

(defthm total-order-anti-symmetric
  (implies (and (total-order x y)
		(total-order y x))
	   (equal x y))
  :rule-classes :forward-chaining)

(defthm total-order-transitive
  (implies (and (total-order x y)
		(total-order y z))
	   (total-order x z)))

(defthm total-order-total
  (or (total-order x y)
      (total-order y x))
  :rule-classes nil)
