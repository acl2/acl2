; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Formalization in ACL2 of the template functions, theorems, and proofs
; in the design notes, for n = m = 1.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Uninterpreted constituents of the function.

(defstub a (*) => *) ; exit test

(defstub b (*) => *) ; base value

(defstub c (* *) => *) ; combination of argument and recursive call

(defstub d (*) => *) ; update of argument in recursive call

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Possibly non-terminating function.

(defun f (x)
  (declare (xargs :mode :program))
  (if (a x)
      (b x)
    (c x (f (d x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Iterated application of D.

(defund d* (k x)
  (declare (xargs
            ;; the following measure and hints should work in any situation
            ;; (i.e. no matter what the current theory is):
            :measure (acl2-count k)
            :hints (("Goal" :in-theory nil))))
  (if (zp k)
      x
    (d* (1- k) (d x))))

; Lemma used to prove NU-END below.

(defthm d*-lemma
  (implies (and (a (d* k x))
                (not (natp k)))
           (a (d* 0 x)))
  :hints (("Goal" :in-theory '(d* natp zp)))
  :rule-classes nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Termination test (note that T is disallowed as function name).

(defun-sk tt (x)
  (exists k
          (a (d* k x))))

(in-theory (disable tt tt-suff))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Measure, defined recursively.

(defund nu (x k)
  (declare
   (xargs
    :measure (nfix (- (tt-witness x) (nfix k)))
    :hints (("Goal" :in-theory '(o-p o-finp o< nfix natp)))))
  (let ((k (nfix k)))
    (if (or (a (d* k x))
            (>= k (nfix (tt-witness x))))
        k
      (nu x (1+ k)))))

(defund mu (x)
  (nu x 0))

; The measure is a natural number.

(defthmd nu-natp
  (natp (nu x k))
  :hints (("Goal"
           :in-theory '((:type-prescription nu)
                        (:compound-recognizer natp-compound-recognizer)))))

(defthmd mu-natp
  (natp (mu x))
  :hints (("Goal" :in-theory '(mu nu-natp))))

; For a terminating argument,
; updating it for the number of times indicated by the measure,
; yields a value satisfying the exit test.

(defthmd nu-end
  (implies (and (tt x)
                (natp k)
                (<= k (nfix (tt-witness x))))
           (a (d* (nu x k) x)))
  :hints (("Goal"
           :in-theory '(nu tt natp nfix)
           :induct (nu x k))
          '(:use (:instance d*-lemma (k (tt-witness x))))))

(defthmd mu-end
  (implies (tt x)
           (a (d* (mu x) x)))
  :hints (("Goal" :in-theory '(mu nu-end natp nfix))))

; For a terminating argument,
; the measure is minimal among
; the numbers of times that updating the argument
; yields a value satisfying the exit test.

(defthmd nu-min
  (implies (and (natp l)
                (natp k)
                (>= l k)
                (a (d* l x)))
           (>= l (nu x k)))
  :hints (("Goal"
           :in-theory '(nu natp nfix)
           :induct (nu x k))))

(defthmd mu-min
  (implies (and (natp l)
                (a (d* l x)))
           (>= l (mu x)))
  :hints (("Goal" :in-theory '(mu nu-min natp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Always-terminating version of F.
; This is not executable because TT is not executable,
; but if it can be proved that TT holds on every argument,
; then the TT test can be transformed away
; (e.g. with APT's SIMPLIFY transformation)
; to generate an equivalent executable function.
; If TT holds only on some arguments,
; the function can be first restricted to those arguments
; (e.g. with APT's RESTRICT transformation)
; and then the TT test can be transformed away.

(defun f^ (x)
  (declare
   (xargs
    :measure (mu x)
    :hints (("Goal"
             :in-theory '(o-p o-finp natp o< zp d*)
             :use (mu-natp
                   (:instance mu-natp (x (d x)))
                   mu-end
                   (:instance mu-min (l (1- (mu x))) (x (d x))))))))
  (if (tt x)
      (if (a x)
          (b x)
        (c x (f^ (d x))))
    :nonterminating))
