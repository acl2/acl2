; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "ACL2")

(include-book "rtl")
(local (include-book "stick-proofs"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))
;(set-inhibit-warnings) ; restore theory warnings (optional)


(defthm top-thm-1-original
  (implies (and (natp n)
                (natp k)
                (< k n)
                (integerp a) ;(bvecp a n)
                (integerp b) ;(bvecp b n)
                )
           (equal (equal (bits (+ a b 1) k 0)
                         0)
		  (equal (bits (lnot (lxor0 a b n) n) k 0)
                         0)))
  :rule-classes ())

(defund sigm-0 (a b c n)
  (if (= c 0)
      (lnot (lxor0 a b n) n)
    (lxor0 a b n)))

(defund kap-0 (a b c n)
  (if (= c 0)
      (* 2 (lior0 a b n))
    (* 2 (land0 a b n))))

(defund tau-0 (a b c n)
  (lnot (lxor0 (sigm-0 a b c n) (kap-0 a b c n) (1+ n)) (1+ n)))

(defthm bvecp-sigm-0
  (bvecp (sigm-0 a b c n) n)
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((sigm-0 a b c n)))))

(defthm bvecp-kap-0
  (implies (and (integerp n) (<= 0 n))
           (bvecp (kap-0 a b c n) (1+ n)))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((kap-0 a b c n)))))

(defthm bvecp-tau-0
  (bvecp (tau-0 a b c n) (1+ n))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((tau-0 a b c n)))))

(defthm top-thm-2-old
  (implies (and (natp n)
                (integerp a) ;(bvecp a n)
                (integerp b) ;(bvecp b n)
                (natp k)
                (< k n)
                (or (equal c 0) (equal c 1)))
           (equal (equal (bits (+ a b c) k 0) 0)
		  (equal (bits (tau-0 a b c n) k 0) 0)))
  :rule-classes ())
