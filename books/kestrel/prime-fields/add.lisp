; Prime fields library: Addition
;
; Copyright (C) 2019-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

(include-book "fep")
(include-book "kestrel/utilities/pos-fix" :dir :system)
(include-book "../utilities/smaller-termp")
(local (include-book "../arithmetic-light/mod"))

;; Compute the sum of x and y modulo the prime.
(defund add (x y p)
  (declare (xargs :guard (and (integerp p)
                              (fep x p)
                              (fep y p))))
  (mbe :exec (mod (+ x y) p)
       :logic (mod (+ (ifix x) (ifix y)) (pos-fix p))))

(defthm natp-of-add
  (natp (add x y p))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable fep add))))

(defthm fep-of-add
  (implies (posp p)
           (fep (add x y p) p))
  :hints (("Goal" :in-theory (enable add fep))))

(defthm add-of-0-arg1
  (implies (and (fep x p)
                (integerp p))
           (equal (add 0 x p)
                  x))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-of-0-arg2
  (implies (and (fep x p)
                (integerp p))
           (equal (add x 0 p)
                  x))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-of-0-arg1-gen
  (equal (add 0 x p)
         (mod (ifix x) (pos-fix p)))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-of-0-arg2-gen
  (equal (add x 0 p)
         (mod (ifix x) (pos-fix p)))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-of-1-arg3
  (equal (add x y 1)
         0)
  :hints (("Goal" :in-theory (enable add))))

(defthm add-associative
  (equal (add (add x y p) z p)
         (add x (add y z p) p))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-when-not-integerp-arg1-cheap
  (implies (not (integerp x))
           (equal (add x y p)
                  ;; could further simplify:
                  (add 0 y p)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-when-not-integerp-arg2-cheap
  (implies (not (integerp y))
           (equal (add x y p)
                  ;; could further simplify:
                  (add 0 x p)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable add))))

(defun strip-neg (x)
  (declare (xargs :guard (pseudo-termp x)))
  (if (and (consp x)
           (eq 'neg (ffn-symb x)))
      (cadr x)
    x))

(defun strip-constant-mul (x)
  (declare (xargs :guard (pseudo-termp x)))
  (if (and (consp x)
           (eq 'mul (ffn-symb x))
           (quotep (cadr x)))
      (caddr x)
    x))

;; compare terms ignoring calls to inv and constant factors (so that terms that
;; can be combined are brought together)
(defun smaller-add-termp (x y)
  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y))))
  (smaller-termp (strip-constant-mul (strip-neg x))
                 (strip-constant-mul (strip-neg y))))

(defthm add-commutative
  (implies (syntaxp (smaller-add-termp y x))
           (equal (add x y p)
                  (add y x p)))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-commutative-2
  (implies (syntaxp (smaller-add-termp y x))
           (equal (add x (add y z p) p)
                  (add y (add x z p) p)))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-combine-constants
  (implies (and (syntaxp (and (quotep x)
                              (quotep y)))
                (integerp p))
           (equal (add x (add y z p) p)
                  (add (add x y p) z p)))
  :hints (("Goal" :in-theory (enable add))))

(defthm equal-of-add-cancel-1
  (implies (and (fep x p)
                (fep y p)
                (integerp p))
           (equal (equal x (add x y p))
                  (equal 0 y)))
  :hints (("Goal" :in-theory (enable add acl2::mod-sum-cases))))

;; For use when x and y are constants but p is not.
(defthm add-of-constants
  (implies (syntaxp (and (quotep y) ;checked first since more likely to fail
                         (quotep x)))
           (equal (add x y p)
                  (mod (+ (ifix x) (ifix y)) (pos-fix p))))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-of-mod-arg1
  (equal (add (mod x p) y p)
         (add x y p))
  :hints (("Goal" :in-theory (enable add))))

(defthm add-of-mod-arg2
  (equal (add x (mod y p) p)
         (add x y p))
  :hints (("Goal" :in-theory (enable add))))

;; basic cancellation rule sufficient to prove the bind-free rules in other files
(defthmd equal-of-add-and-add-cancel
   (implies (posp p)
            (equal (equal (add x y p) (add x z p))
                   (equal (mod (ifix y) p) (mod (ifix z) p))))
   :hints (("Goal" ;:do-not '(preprocess)
            :in-theory (enable add))))
