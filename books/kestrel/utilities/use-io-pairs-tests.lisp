; Copyright (C) 2020, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book tests the use-io-pairs utility.

(in-package "ACL2")

; These are in the .acl2 file.
; (include-book "kestrel/crypto/primes/top" :dir :system)
; (include-book "kestrel/crypto/primes/baby-jubjub-subgroup-prime" :dir :system)

(include-book "use-io-pairs")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Using memoize directly
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This section illustrates what is really going on when we teach ACL2 how to
; execute a function efficiently by using results from previously-proved
; theorems.

(defun primep-exec-1 (n)
  (declare (xargs :guard t))
  (if (member n '(#.primes::*secp256k1-field-prime*
                  #.primes::*baby-jubjub-subgroup-prime*
                  #.primes::*bn-254-group-prime*))
      t
    (rtl::primep n)))

(defthm primep-is-primep-exec-1
  (equal (rtl::primep n)
         (primep-exec-1 n))
  :rule-classes nil)

(memoize 'rtl::primep :invoke 'primep-exec-1)

(local (in-theory (disable
                   primes::primep-of-baby-jubjub-subgroup-prime-constant
                   primes::primep-of-bn-254-group-prime-constant
                   primes::primep-of-secp256k1-field-prime-constant)))

(thm (rtl::primep #.primes::*bn-254-group-prime*)
     :hints (("Goal" :in-theory '((:e rtl::primep)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Using primep
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Restore slow execution for now.

; Add io-pair for bn-254-group-prime.

(use-io-pair
 'rtl::primep #.primes::*bn-254-group-prime* t
 :test 'eql
 :hints '(("Goal"
           :in-theory
           (enable primes::primep-of-bn-254-group-prime-constant))))

(thm (rtl::primep #.primes::*bn-254-group-prime*)
     :hints (("Goal" :in-theory '((:e rtl::primep)))))

; Add io-pair for each of the other two primes under consideration.

(use-io-pairs
 'rtl::primep
 '((#.primes::*secp256k1-field-prime* . t)
   (#.primes::*bn-254-group-prime* . t)
   (#.primes::*baby-jubjub-subgroup-prime* . t))
 :debug t
 :hints '(("Goal"
           :in-theory
           (enable primes::primep-of-baby-jubjub-subgroup-prime-constant
                   primes::primep-of-bn-254-group-prime-constant
                   primes::primep-of-secp256k1-field-prime-constant))))

(thm (rtl::primep #.primes::*secp256k1-field-prime*)
     :hints (("Goal" :in-theory '((:e rtl::primep)))))

(thm (rtl::primep #.primes::*bn-254-group-prime*)
     :hints (("Goal" :in-theory '((:e rtl::primep)))))

(thm (rtl::primep #.primes::*baby-jubjub-subgroup-prime*)
     :hints (("Goal" :in-theory '((:e rtl::primep)))))

; Trivial, without debug printing since the original rtl::primep is run:
(thm (rtl::primep 7)
     :hints (("Goal" :in-theory '((:e rtl::primep)))))
