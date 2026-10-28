; ACL2-2026 Workshop Paper on DEFINDUCTIVE
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/definductive" :dir :system)

(local (include-book "std/basic/inductions" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains details of the EVEN-AND-ODD example in Sections 4 and 5.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Define even and odd natural numbers.

(definductive even-and-odd
  :preds ((even n) (odd n))
  :irules ((zero ()
                 (even 0))
           (from-even ((even n))
                      (odd (1+ n)))
           (from-odd ((odd n))
                     (even (1+ n))))
  :verify-guards nil)

; The predicates just defined only hold on natural numbers.

(defthm-even-proof-validp-clique-flag
  (defthmd natp-when-even-proof-validp
    (implies (even-proof-validp proof _n)
             (natp _n))
    :flag even-proof-validp)
  (defthmd natp-when-odd-proof-validp
    (implies (odd-proof-validp proof _n)
             (natp _n))
    :flag odd-proof-validp)
  :hints (("Goal" :in-theory (enable even-proof-validp
                                     odd-proof-validp
                                     even-zero-validp
                                     even-from-odd-validp
                                     odd-from-even-validp))))

(defruled natp-when-even/odd
  (implies (or (even n)
               (odd n))
           (natp n))
  :enable (even
           odd
           natp-when-even-proof-validp
           natp-when-odd-proof-validp))

; The same fact, proved by rule induction instead of proof tree induction.
; (We disable tau, otherwise it's just proved from the previous theorem.)

(defthm-even-induction
  (defthmd natp-when-even
    (implies (even n)
             (natp n))
    :flag even-induct)
  (defthmd natp-when-odd
    (implies (odd n)
             (natp n))
    :flag odd-induct)
  :hints (("Goal"
           :expand ((even-proof-validp (even-proof n) n)
                    (odd-proof-validp (odd-proof n) n))
           :in-theory (e/d (even
                            odd
                            even-zero-validp
                            even-from-odd-validp
                            odd-from-even-validp
                            even-when-proof-validp
                            odd-when-proof-validp)
                           ((:e tau-system))))))

; Some arithmetic facts used below.

(defruled integerp-when-natp
  (implies (natp x)
           (integerp x)))

(defruled acl2-numberp-when-natp
  (implies (natp x)
           (acl2-numberp x)))

(defruled arith-lemma1
  (implies (and (integerp x)
                (not (integerp (* 1/2 x))))
           (integerp (+ 1/2 (* 1/2 x))))
  :prep-books ((include-book "arithmetic-3/top" :dir :system)))

(defruled arith-lemma2
  (implies (and (integerp x)
                (not (integerp (* 1/2 x))))
           (integerp (+ -1/2 (* 1/2 x))))
  :prep-books ((include-book "arithmetic-3/top" :dir :system)))

; The inductively defined EVEN and ODD implies ACL2's EVENP and ODDP.

(defthm-even-proof-validp-clique-flag
  (defthmd evenp-when-even-proof-validp
    (implies (even-proof-validp proof _n)
             (evenp _n))
    :flag even-proof-validp)
  (defthmd oddp-when-odd-proof-validp
    (implies (odd-proof-validp proof _n)
             (oddp _n))
    :flag odd-proof-validp)
  :hints (("Goal" :in-theory (enable even-proof-validp
                                     odd-proof-validp
                                     even-zero-validp
                                     even-from-odd-validp
                                     odd-from-even-validp
                                     natp-when-odd-proof-validp
                                     arith-lemma1
                                     integerp-when-natp))))

(defruled evenp-when-even
  (implies (even n)
           (evenp n))
  :enable (even evenp-when-even-proof-validp)
  :disable evenp)

(defruled oddp-when-odd
  (implies (odd n)
           (oddp n))
  :enable (odd oddp-when-odd-proof-validp)
  :disable oddp)

; For natural numbers, ACL2's EVENP and ODDP
; imply the inductively defined EVEN and ODD.
; This is shown by defining
; the construction of a proof tree for each natural number,
; and by showing each proof tree proves
; the evenness or oddity of the natural number.

(defines proof-for-even/odd
  (define proof-for-even ((n natp)) ; proof tree that n is even
    :guard (evenp n)
    :returns (proof even-proofp)
    (b* (((when (zp n)) (even-proof-zero))
         (odd-proof (proof-for-odd (1- n))))
      (make-even-proof-from-odd :n (1- n) :premise1-proof odd-proof)))
  (define proof-for-odd ((n natp)) ; proof tree that n is odd
    :guard (oddp n)
    :returns (proof odd-proofp)
    (b* (((when (zp n))
          (prog2$ (impossible)
                  (make-odd-proof-from-even
                   :n n :premise1-proof (even-proof-zero))))
         (even-proof (proof-for-even (1- n))))
      (make-odd-proof-from-even :n (1- n) :premise1-proof even-proof)))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable arith-lemma2)))
  :flag-local nil)

(defthm-proof-for-even/odd-flag
  (defthmd even-proof-validp-of-proof-for-even
    (implies (and (natp n)
                  (evenp n))
             (even-proof-validp (proof-for-even n) n))
    :flag proof-for-even)
  (defthmd odd-proof-validp-of-proof-for-odd
    (implies (and (natp n)
                  (oddp n))
             (odd-proof-validp (proof-for-odd n) n))
    :flag proof-for-odd)
  :hints (("Goal"
           :in-theory (enable proof-for-even
                              proof-for-odd
                              even-proof-validp
                              odd-proof-validp
                              even-zero-validp
                              even-from-odd-validp
                              odd-from-even-validp
                              arith-lemma2))))

(defruled even-when-evenp
  (implies (and (natp n)
                (evenp n))
           (even n))
  :use (:instance even-when-proof-validp
                  (proof (proof-for-even n))
                  (_n n))
  :enable even-proof-validp-of-proof-for-even)

(defruled odd-when-oddp
  (implies (and (natp n)
                (oddp n))
           (odd n))
  :use (:instance odd-when-proof-validp
                  (proof (proof-for-odd n))
                  (_n n))
  :enable odd-proof-validp-of-proof-for-odd)

; Thus, the inductively defined EVEN and ODD are equivalent to
; ACL2's EVENP and ODDP, on natural numbers.

(defruled even-is-evenp
  (implies (natp n)
           (equal (even n)
                  (evenp n)))
  :use (evenp-when-even even-when-evenp))

(defruled odd-is-oddp
  (implies (natp n)
           (equal (odd n)
                  (oddp n)))
  :use (oddp-when-odd odd-when-oddp))

; A derived inference rule, proved by combining two defining inference rules.

(defruled even-add-2
  (implies (even n)
           (even (+ 2 n)))
  :enable odd-from-even
  :use (:instance even-from-odd (n (1+ n))))

; A derived inference rule,
; proved by combining m-1 instances of the preceding rule.
; The proof is by induction on M (not on proof trees).

(defruled even-add-double
  (implies (and (natp m)
                (even n))
           (even (+ (* 2 m) n)))
  :induct (dec-induct m)
  :hints ('(:use (:instance even-add-2 (n (+ (* 2 (1- m)) n))))))

; A derived inference rule,
; proved by constructing a proof tree for the conclusion
; from a proof tree for the premise.

(defruled even-of-pred-when-odd
  (implies (odd n)
           (even (1- n)))
  :use (:instance even-when-proof-validp
                  (proof (odd-proof-from-even->premise1-proof (odd-proof n)))
                  (_n (1- n)))
  :expand (odd-proof-validp (odd-proof n) n)
  :enable (odd
           odd-proof-validp
           odd-from-even-validp
           natp-when-even-proof-validp
           acl2-numberp-when-natp))

; The theorem natp-when-even/odd can be also proved
; using the minimality of the predicates, via function instantiation.

(defruled natp-when-even/odd-via-functional-instantiation
  (implies (or (even n)
               (odd n))
           (natp n))
  :disable ((:e tau-system))
  :use ((:functional-instance even-alt-when-even (even-alt natp) (odd-alt natp))
        (:functional-instance odd-alt-when-odd (even-alt natp) (odd-alt natp))))
