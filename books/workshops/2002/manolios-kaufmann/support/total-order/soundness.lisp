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

(defun good-atom (x)
  (and (atom x)
       (or (acl2-numberp x)
	   (symbolp x)
	   (characterp x)
	   (stringp x))))

(defthm good-atom-compound-recognizer
  (iff (good-atom x)
       (and (atom x)
	    (or (acl2-numberp x)
		(symbolp x)
		(characterp x)
		(stringp x))))
  :rule-classes :compound-recognizer)

(in-theory (disable good-atom))

(defun good-atom-order (x y)
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
	(t t)))

(defmacro boolp (x)
  `(or (equal ,x t)
       (equal ,x nil)))

(defthm boolp-good-atom-order
  (boolp (good-atom-order x y))
  :rule-classes :type-prescription)

(defthm good-atom-order-reflexive
  (implies (atom x)
	   (good-atom-order x x)))

(defthm equal-coerce
  (implies (and (stringp x)
		(stringp y))
	   (equal (equal (coerce x 'list)
			 (coerce y 'list))
		  (equal x y)))
  :hints (("Goal" :use
	   ((:instance coerce-inverse-2 (x x))
	    (:instance coerce-inverse-2 (x y)))
	   :in-theory (disable coerce-inverse-2))))

(defthm string<=-l-transitive-at-0
  (implies (and (not (string<-l y x 0))
		(not (string<-l z y 0))
		(character-listp x)
		(character-listp y)
		(character-listp z))
	   (not (string<-l z x 0)))
  :hints
  (("Goal" :use (:instance string<-l-transitive
			   (i 0) (j 0) (k 0)))))

(defthm good-atom-order-transitive
  (implies (and (good-atom-order x y)
		(good-atom-order y z)
		(atom x)
		(atom y)
		(atom z))
	   (good-atom-order x z))
  :hints (("Goal"
	   :in-theory (enable string< symbol<))))

(defthm good-atom-order-anti-symmetric
  (implies (and (good-atom x)
		(good-atom-order x y)
		(good-atom-order y x))
	   (equal x y))
  :hints (("Goal"
	   :in-theory (union-theories
		       '(string< symbol<)
		       (disable code-char-char-code-is-identity))
	   :use ((:instance symbol-equality (s1 x) (s2 y))
		 (:instance code-char-char-code-is-identity (c y))
		 (:instance code-char-char-code-is-identity (c x)))))
  :rule-classes
   ((:forward-chaining :corollary
                       (implies (and (good-atom-order x y)
				     (good-atom x)
                                     (not (consp x))
                                     (not (consp y)))
                                (iff (good-atom-order y x)
                                     (equal x y)))
                       :hints (("Goal" :in-theory
                                (disable good-atom-order))))))

(defthm good-atom-order-total
  (implies (and (atom x)
		(atom y))
	   (or (good-atom-order x y)
	       (good-atom-order y x)))
  :hints (("Goal"
	   :in-theory (enable string< symbol<)))
  :rule-classes
  ((:forward-chaining :corollary
		      (implies (and (not (good-atom-order x y))
				    (not (consp x))
				    (not (consp y)))
			       (good-atom-order y x)))))

(in-theory (disable good-atom-order))

(defun good-object (x)
  (if (consp x)
      (and (good-object (car x))
	   (good-object (cdr x)))
    (good-atom x)))

(defun good-object-order (x y)
  (cond ((atom x)
         (cond ((atom y)
                (good-atom-order x y))
               (t t)))
        ((atom y) nil)
        ((equal (car x) (car y))
         (good-object-order (cdr x) (cdr y)))
        (t (good-object-order (car x) (car y)))))

(defthm boolp-good-object-order
  (boolp (good-object-order x y))
  :rule-classes :type-prescription)

(defthm good-object-order-reflexive
  (good-object-order x x))

(defthm good-object-order-anti-symmetric
  (implies (and (good-object-order x y)
		(good-object-order y x)
		(good-object x)
		(good-object y))
	   (equal x y))
  :rule-classes :forward-chaining)

(defthm good-object-order-transitive
  (implies (and (good-object x)
		(good-object-order x y)
		(good-object-order y z))
	   (good-object-order x z)))

(defthm good-object-order-total
  (or (good-object-order x y)
      (good-object-order y x))
  :rule-classes nil)
