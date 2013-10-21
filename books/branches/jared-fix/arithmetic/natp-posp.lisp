; Copyright (C) 2002  Georgia Institute of Technology

; This file is free software; you can redistribute it and/or
; modify it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or (at your
; option) any later version.

; This file is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with ACL2; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by: Panagiotis Manolios and Daron Vroon who can be reached as follows.

; Email: manolios@cc.gatech.edu, vroon@cc.gatech.edu

; Postal Mail:
; College of Computing
; CERCS Lab
; Georgia Institute of Technology
; 801 Atlantic Drive
; Atlanta, Georgia 30332-0280 U.S.A.

(in-package "ACL2")

(include-book "inequalities")

; theorems about natp, posp

; Note: Compound-recognizer rules natp-cr and posp-cr were originally proved
; here for predicates natp and posp.  However, such rules are in the ACL2
; sources starting with ACL2 Version 2.9.2, under the names
; natp-compound-recognizer and posp-compound-recognizer).

(defthm natp-fc-1
  (implies (natp x)
	   (<= 0 x))
  :rule-classes :forward-chaining)

(defthm natp-fc-2
  (implies (natp x)
	   (integerp x))
  :rule-classes :forward-chaining)

(defthm posp-fc-1
  (implies (posp x)
	   (< 0 x))
  :rule-classes :forward-chaining)

(defthm posp-fc-2
  (implies (posp x)
	   (integerp x))
  :rule-classes :forward-chaining)

(defthm natp-rw
  (implies (and (integerp x)
		(<= 0 x))
	   (natp x)))

(defthm posp-rw
  (implies (and (integerp x)
		(< 0 x))
	   (posp x)))

(defthm |(natp a)  <=>  (posp a+1)|
  (implies (integerp a)
	   (equal (posp (+ 1 a))
		  (natp a))))

; The lemma posp-natp is needed for the proof of o^-alt-def-l2 in
; books/ordinals/ordinal-exponentiation.lisp.
(encapsulate
 ()
 (local
  (defthm posp-natp-l1
    (implies (posp (+ -1 x))
	     (natp (+ -1 (+ -1 x))))))

 (defthm posp-natp
   (implies (posp (+ -1 x))
	    (natp (+ -2 x)))
   :hints (("goal" :use posp-natp-l1))))

(defthm natp-*
  (implies (and (natp a)
		(natp b))
	   (natp (* a b))))

(defthm natp-posp
 (implies (and (natp a)
	       (not (equal a 0)))
	  (posp a)))

(defthm natp-posp--1
  (equal (natp (+ -1 q))
         (posp q))
  :hints (("goal"
           :in-theory (enable posp natp))))

(defthm |x < y  =>  0 < -x+y|
  (implies (and (integerp x) (integerp y) (< x y))
	   (posp (+ (- x) y)))
 :rule-classes

; An earlier version of this rule included the rule class
; (:forward-chaining :trigger-terms ((+ (- x) y))).
; However, we believe that in the presence of the corresponding
; :type-prescription rule, that :forward-chaining rule would never do anything
; other than waste time, because the resulting conclusion would be typed to T.

; By the way, this rule is needed for certification of
; books/workshops/2003/sustik/support/dickson,lisp, in particular, map-lemma-4.

 ((:type-prescription)))

(defthm |x < y  =>  0 < y-x|

; We add this rule in analogy to the one before it, since either x or y could
; be larger in term-order and unary minus is "invisible" for binary-+
; (see :DOC invisible-fns-table).

  (implies (and (integerp x) (integerp y) (< x y))
	   (posp (+ y (- x))))
 :rule-classes ((:type-prescription)))

#|
; The following rule is completely analogous to the one just above it.  Should
; we add it?  How about analogous rules for rationals rather than just
; integers?

(defthm |x < y  =>  0 <= -x+y|
  (implies (and (integerp x) (integerp y) (<= x y))
	   (and (natp (+ (- x) y))
                (natp (+ y (- x)))))
 :rule-classes
 ((:type-prescription)))
|#

(in-theory (disable natp posp))
