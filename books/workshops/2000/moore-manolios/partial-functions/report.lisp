;  Copyright (C) 2000 Panagiotis Manolios and J Strother Moore

;  This program is free software; you can redistribute it and/or modify
;  it under the terms of the GNU General Public License as published by
;  the Free Software Foundation; either version 2 of the License, or
;  (at your option) any later version.

;  This program is distributed in the hope that it will be useful,
;  but WITHOUT ANY WARRANTY; without even the implied warranty of
;  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;  GNU General Public License for more details.

;  You should have received a copy of the GNU General Public License
;  along with this program; if not, write to the Free Software
;  Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;  Written by Panagiotis Manolios who can be reached as follows.

;  Email: pete@cs.utexas.edu, moore@cs.utexas.edu

;  Postal Mail:
;  Department of Computer Science
;  The University of Texas at Austin
;  Austin, TX 78701 USA

; (certify-book "report")

(in-package "ACL2")
(include-book "defpun")
(include-book "../../../../ihs/quotient-remainder-lemmas")
(include-book "../../../../arithmetic/top-with-meta")
(include-book "mod-1-property")

; Section: Example Results

(defpun offset (n)
  (declare (xargs :witness fix))
  (if (equal n 0)
      0
    (+ 1 (offset (- n 1)))))

(defun quotm (i j)
  (let ((temp (floor (/ i j) 1)))
    (if (< temp 0)
        0
      (+ 1 temp))))

(in-theory (disable floor))

; The next two events illustrate a little trick.  To prove that the
; domain in quot, below, is closed, i.e., to do the guard proof for
; quot, I need to know that the-quot ``always'' returns a rational.
; But we have implemented no means of providing hints to be inserted
; between the admission of the automatically generated the-quot and
; its guard verification.  So I define the-quot now and prove what I
; need.  Then I do the defpun which will REDUNDANTLY define it.  Cool.

(defun the-quot (i j)
  (declare (xargs :guard (and (rationalp i)
                              (rationalp j)
                              (< 0 j))

; Modified by Matt K. after Version 3.0.1: This measure was formerly
; (quotm i j), but it needed to change so that the introduction of
; the-quote in the defpun below would be redundant, after the fix for
; the soundness bug in the redundancy criterion for defun.

                  :measure (if (and (rationalp i)
                                    (rationalp j)
                                    (< 0 j))
                               (quotm i j)
                             0)
                  :verify-guards nil))
  (if (and (rationalp i)
           (rationalp j)
           (< 0 j))
      (if (<= i 0) 0 (+ 1 (the-quot (- i j) j)))
    'undef))

(defthm rationalp-the-quot
  (implies (and (rationalp i)
                (rationalp j)
                (< 0 j))
           (rationalp (the-quot i j)))
  :rule-classes :type-prescription)

(defpun quot (i j)
  (declare (xargs :gdomain (and (rationalp i)
                                (rationalp j)
                                (< 0 j))
                  :measure (quotm i j)))
  (if (<= i 0) 0 (+ 1 (quot (- i j) j))))

(defpun 3n+1 (n)
  (if (<= n 1)
      n
    (3n+1 (if (evenp n)
              (/ n 2)
            (+ (* 3 n) 1)))))


(defstub haltedp (s) t)
(defstub step1 (s) t)

(defpun stepw (s)
  (if (haltedp s)
      s
    (stepw (step1 s))))

; Section: Consistency

(defun natural-induction (n)
  (if (zp n)
      t
    (natural-induction (- n 1))))

(defmacro show-g-inconsistent nil
  '(ld '((defstub g (n) t)

         (defaxiom g-axiom
           (equal (g n)
                  (if (equal n 0)
                      nil
                    (cons nil (g (- n 1)))))
           :rule-classes :definition)

         (defthm g-induction
           t
           :rule-classes ((:induction
                           :pattern (g n)
                           :scheme (natural-induction n))))

         (defthm len-of-g
           (implies (natp n)
                    (equal (len (g n)) n)))

         (defun bad-lemma-hint (k n)
           (if (zp k)
               (list k n)
             (bad-lemma-hint (- k 1) (- n 1))))

         (defthm bad-lemma
           (implies (and (natpp k)
                         (integerp n)
                         (< n 0))
                    (< k (len (g n))))
           :hints (("Goal" :induct (bad-lemma-hint k n))
                   ("Subgoal *1/1" :use g-axiom)))

         (defthm bad-theorem
           nil
           :rule-classes nil
           :hints (("Goal" :use (:instance bad-lemma
                                           (k (len (g -1)))
                                           (n -1)))))
         (ubt! 'g))
       :ld-pre-eval-print t))

(defpun undef (x)
  (declare (xargs :witness car))
  (undef x)
  :rule-classes nil)

; Section:  Witnessing Equations

(defpun h (n)
  (declare (xargs :witness fix))
  (if (equal n 0) 0 (+ 1 (h (- n 1)))))

(defthm h-induction
  t
  :rule-classes ((:induction
                  :pattern (h n)
                  :scheme (natural-induction n))))

(defthm h-is-id-on-naturals
  (implies (natp n)
           (equal (h n) n)))

(defun h22/7 (n)
  (if (natp n)
      n
    (+ 22/7 n)))

(defthm h22/7-satisfies-h-def
  (equal (h22/7 n)
         (if (equal n 0) 0 (+ 1 (h22/7 (- n 1)))))
  :rule-classes nil)

(defthm h-prop-0
  (acl2-numberp (h n))
  :rule-classes :type-prescription
  :hints (("Goal" :use h-def)))

(encapsulate
 nil
 (local
  (defthm lemma1
    (implies (natp n)
             (equal (h n) n))
    :rule-classes nil
    :hints (("Goal" :induct (natural-induction n)))))

 (local
  (defthm lemma2
    (implies (and (integerp n)
                  (< 0 n))
             (equal (h (- n)) (+ (- (h -1) -1) (- n))))
    :rule-classes nil
    :hints (("Goal" :induct (natural-induction n)))))

 (defun hconst () (+ 1 (h -1) ))

 (defthm acl2-numberp-hconst
   (acl2-numberp (hconst)))

 (in-theory (disable (:executable-counterpart hconst)))

 (defthm h-prop-1
   (implies (integerp n)
            (equal (h n)
                   (if (<= 0 n)
                       n
                     (+ n (hconst)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance lemma1)
                         (:instance lemma2 (n (- n))))))))

(encapsulate
 nil
 (local
  (defthm lemma1
    (implies (and (acl2-numberp x)
                  (not (integerp x))
                  (natp n))
             (equal (h (+ n x))
                    (+ n (h x))))
    :rule-classes nil
    :hints (("Goal" :induct (natural-induction n)))))

 (local
  (defthm lemma2
    (implies (and (acl2-numberp x)
                  (not (integerp x))
                  (integerp n)
                  (< 0 n))
             (equal (h (+ (- n) x))
                    (+ (- n) (h x))))
    :rule-classes nil
    :hints (("Goal" :induct (natural-induction n)))))

 (local
  (defthm lemma3
    (implies (and (acl2-numberp x)
                  (not (integerp x))
                  (integerp n))
             (equal (h (+ n x))
                    (+ n (h x))))
    :rule-classes nil
    :hints (("Goal" :use ((:instance lemma1)
                          (:instance lemma2 (n (- n))))))))

; Consider any rational x.  It can be represented by an integer n plus some
; epsilon between 0 and 1.  H-prop-5 tells us that (h x) is n+(h epsilon).

 (defthm h-prop-2
   (implies (and (rationalp x)
                 (not (integerp x)))
            (equal (h x)
                   (+ (floor x 1) (h (mod x 1)))))
   :rule-classes nil
   :hints (("Goal" :use (:instance lemma3
                                   (x (mod x 1))
                                   (n (floor x 1))))))

 )

; Here is a witness for h that demonstrates that it is not just a linear
; offset.

(encapsulate ((arbitrary-constant (x) t))
             (local (defun arbitrary-constant (x) (fix x)))
             (defthm acl2-numberp-arbitrary-constant
               (acl2-numberp (arbitrary-constant x))
               :rule-classes :type-prescription))

(defun hv (x)
  (if (integerp x)
      x
    (if (rationalp x)
        (+ (floor x 1) (arbitrary-constant (mod x 1)))
      (fix x))))

(defthm hv-satisfies-h-def
  (equal (hv n)
         (if (equal n 0) 0 (+ 1 (hv (- n 1)))))
  :hints (("Goal" :in-theory (disable floor)))
  :rule-classes nil)

; We can make this general observation very concrete by letting the
; arbitrary-constant be a particular function.

(defun concrete-arbitrary-constant (x)
  (case x
    (1/2 100)
    (1/3 -273)
    (1/4 57)
    (1/5 123)
    (otherwise (* x x))))

(defun concrete-hv (x)
  (if (integerp x)
      x
    (if (rationalp x)
        (+ (floor x 1) (concrete-arbitrary-constant (mod x 1)))
      (fix x))))

(defthm concrete-hv-satisfies-h-def
  (equal (concrete-hv n)
         (if (equal n 0) 0 (+ 1 (concrete-hv (- n 1)))))
  :hints (("Goal" :in-theory (disable floor concrete-arbitrary-constant)))
  :rule-classes nil)

(set-ignore-ok t)
(set-irrelevant-formals-ok t)

(defpun z (x)
  (declare (xargs :witness (lambda (x) 0)))
  (if (zip x)
      0
    (* (z (- x 1))
       (z (+ x 1)))))

(defun integer-induction (i)
  (if (integerp i)
      (if (equal i 0)
          t
        (if (< i 0)
            (integer-induction (+ i 1))
          (integer-induction (- i 1))))
    t))

(defthm z-induction
  t
  :rule-classes ((:induction
                  :pattern (z i)
                  :scheme (integer-induction i))))

(defthm z-is-0
  (equal (z x) 0))

(defpun three (x)
  (declare (xargs :witness (lambda (x) 1)))
  (if (equal x nil)
      (let ((i (three x)))
        (if (and (integerp i) (<= 1 i) (<= i 3))
            i
          1))
    1)
  :rule-classes nil)

(defun three1 (x) (if (equal x nil) 1 1))
(defun three2 (x) (if (equal x nil) 2 1))
(defun three3 (x) (if (equal x nil) 3 1))

(defthm three-and-only-three
  (and (equal (three1 x)
              (if (equal x nil)
                  (let ((i (three1 x)))
                    (if (and (<= 1 i) (<= i 3))
                        i
                      1))
                1))
       (equal (three2 x)
              (if (equal x nil)
                  (let ((i (three2 x)))
                    (if (and (<= 1 i) (<= i 3))
                        i
                      1))
                1))
       (equal (three3 x)
              (if (equal x nil)
                  (let ((i (three3 x)))
                    (if (and (<= 1 i) (<= i 3))
                        i
                      1))
                1))
       (or (equal (three x) (three1 x))
           (equal (three x) (three2 x))
           (equal (three x) (three3 x))))
  :hints (("Goal" :use three-def))
  :rule-classes nil)

; Section:  Domains

(defpun gnat (n)
  (declare (xargs :domain (natp n) :measure n))
  (if (equal n 0)
      nil
    (cons nil (gnat (- n 1)))))


(defpun gsev (n)
  (declare (xargs :domain (and (integerp n) (<= -7 n)) :measure (+ 8 n)))
  (if (equal n 0)
      nil
    (cons nil (gsev (- n 1)))))

; Tail Recursion

(defpun trfact (n a)
  (if (equal n 0)
      a
     (trfact (- n 1) (* n a))))

(defun fact (n) (if (zp n) 1 (* n (fact (- n 1)))))

(defun fact1 (n a) (if (zp n) a (fact1 (- n 1) (* n a))))
(defthm trfact-induction
  t
  :rule-classes ((:induction
                  :pattern (trfact n a)
                  :scheme (fact1 n a))))

(defthm trfact-is-fact-on-nats
  (implies (and (natp n)
                (acl2-numberp a))
           (equal (trfact n a) (* a (fact n)))))


; It would be nice if we could switch packages now from "ACL2" to "TJVM"
; and prove some theorems about the tjvm using its partial function semantics.
; But it is not permitted by Common Lisp to switch packages in the middle of a
; file.  So we proved the results we wanted in tjvm-examples.lisp.

(include-book "tjvm-examples")

; We recommend that you visit that file to see the tjvm results cited
; in the paper.

