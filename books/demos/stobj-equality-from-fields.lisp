; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Ben Selfridge was looking for a way to prove two stobjs equal, after having
; proved that their respective fields are equal.  Here, each of those stobjs is
; the result of applying different functions to the same stobj as well as other
; parameters.  Here we illustrate an approach for completing such a proof.

; See also list-equality-from-nth.lisp for a way to prove equality of two stobj
; array fields.

; NOTE: All lemmas in this file before the last one (main) should probably be
; local if we are to use this book in other work.

(in-package "ACL2")

(defstobj st fld1 fld2 fld3)

(defstub fa (x st) t)
(defstub fb (x st) t)

; Assume we've proved the following three theorems (stated here as axioms).

(defaxiom fa-is-fb-fields
  (implies (stp st)
           (let ((sta (fa x st))
                 (stb (fb x st)))
             (and (equal (fld1 sta) (fld1 stb)) ; FLD1s are equal
                  (equal (fld2 sta) (fld2 stb)) ; FLD2s are equal
                  (equal (fld3 sta) (fld3 stb)) ; FLD3s are equal
                  )))
  :rule-classes nil)

(defaxiom stp-fa
  (implies (stp st)
           (stp (fa x st)))
  :rule-classes nil)

(defaxiom stp-fb
  (implies (stp st)
           (stp (fb x st)))
  :rule-classes nil)

; The key idea is to reduce equality of two lists to equality of their
; respective fields:

(defthm equal-lists-reduction
  (implies (consp x)
           (equal (equal x y)
                  (and (consp y)
                       (equal (car x) (car y))
                       (equal (cdr x) (cdr y))))))

; We know that our stobjs have a certain length (3, in this case), so the lemma
; just above will apply repeatedly if we can open up equality of the length to
; a constant.  The next lemma does that for a positive constant, while the one
; after that does so for 0.

(defthm equal-len-open
  (implies (posp n)
           (equal (equal (len x) n)
                  (and (consp x)
                       (equal (len (cdr x))
                              (1- n))))))

(defthm equal-len-0
  (equal (equal (len x) 0)
         (not (consp x))))

; Since the accessors are defined in terms of nth but equal-lists-reduction is
; about cons, we eliminate calls of nth with the following lemma.

(defthm nth-opener
  (implies (posp n)
           (equal (nth n x)
                  (nth (1- n) (cdr x)))))

; Now our main lemma proves automatically, when the axioms are given in a :use
; hint.

(defthm main
  (implies (stp st)
           (equal (fa x st)
                  (fb x st)))
  :hints (("Goal" :use (stp-fa
                        stp-fb
                        fa-is-fb-fields))))
