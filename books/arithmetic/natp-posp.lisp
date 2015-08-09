;; Note: The license below is based on the template at:
;; http://opensource.org/licenses/BSD-3-Clause

;; Copyright (C) 2013  Northeastern University
;; All rights reserved.

;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions are
;; met:

;; o Redistributions of source code must retain the above copyright
;;   notice, this list of conditions and the following disclaimer.

;; o Redistributions in binary form must reproduce the above copyright
;;   notice, this list of conditions and the following disclaimer in the
;;   documentation and/or other materials provided with the distribution.

;; o Neither the name of Northeastern University nor the names of
;;   its contributors may be used to endorse or promote products derived
;;   from this software without specific prior written permission.

;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
;; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
;; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
;; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
;; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
;; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
;; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
;; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;; Written by: Panagiotis Manolios and Daron Vroon who can be
;; reached as follows.

;; Email: pete@ccs.neu.edu, pmanolios@gmail.com, daron.vroon@gmail.com

;; Postal Mail:
;; Pete Manolios
;; College of Computer and Information Science
;; Northeastern University
;; 360 Huntington Avenue
;; Boston, Massachusetts 02115 U.S.A.

;; Modified by Jared Davis in January 2014 to add XDOC documentation

(in-package "ACL2")

(include-book "inequalities")

; theorems about natp, posp

; Note: Compound-recognizer rules natp-cr and posp-cr were originally proved
; here for predicates natp and posp.  However, such rules are in the ACL2
; sources starting with ACL2 Version 2.9.2, under the names
; natp-compound-recognizer and posp-compound-recognizer).

(defsection arithmetic/natp-posp
  :parents (arithmetic-1)
  :short "Lemmas for reasoning about when the basic arithmetic operators
produce natural and positive integer results."

  :long "<p>This is a good, lightweight book for working with @(see natp) and
@(see posp).</p>

<p>For a somewhat heavier and more comprehensive alternative, you may also wish
to see the @(see arith-equivs) book, which introduces, @(see equivalence) relations
like @(see int-equiv) and @(see nat-equiv), and many useful @(see congruence) rules
about these equivalences.</p>"

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
; books/workshops/2003/sustik/support/dickson.lisp, in particular, map-lemma-4.

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

)
