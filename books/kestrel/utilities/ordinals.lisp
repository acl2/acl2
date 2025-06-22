; A lightweight book about the built-in ordinal functions
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; See also books/ordinals

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable o-p
                    o-finp
                    o-first-expt
                    o-first-coeff
                    o-rst
                    make-ord
                    o<))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm o-finp-compound-recognizer
  (equal (o-finp x)
         (not (consp x)))
  :rule-classes :compound-recognizer
  :hints (("Goal" :in-theory (enable o-finp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm o-p-compound-recognizer
  (if (o-p x)
      (or (natp x)
          (consp x))
    (not (natp x)))
  :rule-classes :compound-recognizer
  :hints (("Goal" :in-theory (enable o-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd o-first-expt-when-o-finp
  (implies (o-finp x)
           (equal (o-first-expt x)
                  0))
  :hints (("Goal" :in-theory (enable o-first-expt))))

(defthm o-first-expt-when-o-finp-cheap
  (implies (o-finp x)
           (equal (o-first-expt x)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :by o-first-expt-when-o-finp)))

;;;;;;;;;;;;;;;;;;;;

(defthm o-p-of-o-first-expt-when-o-p
  (implies (o-p x)
           (o-p (o-first-expt x)))
  :hints (("Goal" :in-theory (enable o-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd o-first-coeff-when-o-finp
  (implies (o-finp x)
           (equal (o-first-coeff x)
                  x))
  :hints (("Goal" :in-theory (enable o-first-coeff))))

(defthm o-first-coeff-when-o-finp-cheap
  (implies (o-finp x)
           (equal (o-first-coeff x)
                  x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :by o-first-coeff-when-o-finp)))

;;;;;;;;;;;;;;;;;;;;

(defthm natp-of-o-first-coeff
  (implies (o-p x)
           (natp (o-first-coeff x)))
  :hints (("Goal" :in-theory (enable o-p))))

(defthm posp-of-o-first-coeff
  (implies (o-p x)
           (equal (posp (o-first-coeff x))
                  (not (equal 0 x))))
  :hints (("Goal" :in-theory (enable o-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd o-rst-when-o-finp
  (implies (o-finp x)
           (equal (o-rst x)
                  nil))
  :hints (("Goal" :in-theory (enable o-rst o-finp))))

(defthm o-rst-when-o-finp-cheap
  (implies (o-finp x)
           (equal (o-rst x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :by o-rst-when-o-finp)))

;;;;;;;;;;;;;;;;;;;;

(defthm o-p-of-o-rst-when-o-p
  (implies (o-p x)
           (equal (o-p (o-rst x))
                  (not (o-finp x))))
  :hints (("Goal" :in-theory (enable o-p o-rst))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm o-first-expt-of-make-ord
  (equal (o-first-expt (make-ord fe fco rst))
         fe)
  :hints (("Goal" :in-theory (enable o-first-expt make-ord))))

(defthm o-first-coeff-of-make-ord
  (equal (o-first-coeff (make-ord fe fco rst))
         fco)
  :hints (("Goal" :in-theory (enable o-first-coeff make-ord))))

(defthm o-rst-of-make-ord
  (equal (o-rst (make-ord fe fco rst))
         rst)
  :hints (("Goal" :in-theory (enable o-rst make-ord))))

;;;;;;;;;;;;;;;;;;;;

(defthm make-ord-elim
  (implies (and (o-p x)
                (not (o-finp x)))
           (equal (make-ord (o-first-expt x) (o-first-coeff x) (o-rst x))
                  x))
  :rule-classes (:rewrite :elim)
  :hints (("Goal" :in-theory (enable make-ord
                                     o-first-expt
                                     o-first-coeff
                                     o-rst
                                     o-p))))

;;;;;;;;;;;;;;;;;;;;

(defthm o-p-of-make-ord
  (equal (o-p (make-ord fe fco rst))
         (and (o-p fe)
              (not (equal 0 fe))
              (posp fco)
              (o-p rst)
              (o< (o-first-expt rst) fe)))
  :hints (("Goal" :in-theory (enable o-p
                                     make-ord
                                     o-first-expt
                                     o-first-coeff
                                     o-rst))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd o<-when-o-finp
  (implies (and (o-finp x)
                (o-finp y))
           (equal (o< x y)
                  (< x y)))
  :hints (("Goal" :in-theory (enable o<))))

;; These hypotheses are often known immediately by type reasoning.
(defthm o<-when-o-finp-cheap
  (implies (and (o-finp x)
                (o-finp y))
           (equal (o< x y)
                  (< x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :hints (("Goal" :by o<-when-o-finp)))
