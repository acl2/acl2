; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

(include-book "bits-mul-field")
(include-book "boolean-check")
(include-book "pow2sum")
(include-book "babbage-multiplication")

(local (include-book "../library-extensions/arithmetic"))
(local (include-book "../library-extensions/r1cses"))

(local (include-book "kestrel/arithmetic-light/evenp" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Binary version of little-endian Babbage multiplication,
; more convenient in :use hints for theorems involving lebits=>nat,
; because this obviates the need to open lebits=>nat.
; This belongs to a more general place than this file.

(define babbage-mul-lebits ((x-bits bit-listp) (y-bits bit-listp) (n natp))
  :guard (and (equal (len y-bits) (len x-bits))
              (< n (len x-bits)))
  :returns (product natp)
  (b* ((n (nfix n))
       (x0 (lebits=>nat (take n x-bits)))
       (y0 (lebits=>nat (take n y-bits)))
       (x1 (lebits=>nat (nthcdr n x-bits)))
       (y1 (lebits=>nat (nthcdr n y-bits)))
       (z0 (* x0 y0))
       (z1 (+ (* x1 y0)
              (* x0 y1)))
       (z2 (* x1 y1)))
    (+ z0
       (* z1 (expt 2 n))
       (* z2 (expt 2 (* 2 n)))))
  :hooks (:fix)
  ///

  (defruled babbage-mul-lebits-correct
    (implies (and (equal (len y-bits) (len x-bits))
                  (natp n)
                  (< n (len x-bits)))
             (equal (babbage-mul-lebits x-bits y-bits n)
                    (* (lebits=>nat x-bits)
                       (lebits=>nat y-bits))))
    :do-not-induct t
    :enable (babbage-mul-lendian
             lebits=>nat)
    :use (:instance babbage-mul-lendian-correct
                    (base 2)
                    (n n)
                    (x-digits x-bits)
                    (y-digits y-bits))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This gadget performs an unsigned multiplication with carry,
; according to the function mul_with_carry() in snarkVM.
; As explained in the comments of that function,
; the carry bits are not quite the ones whose value is the carry
; (i.e. the portion of the product that does not fit in n bits,
; where n is the number of bits of the operands xs and ys);
; instead, they are the concatenation of the carry bits
; from sub-multiplications of the multiplication.
; These sub-multiplications are according to Babbage's method;
; see ../babbage-multiplication.lisp.

; This gadget works as follows.
; The operands xs and ys are split into low and high halves.
; The Babbage sub-multiplications are put into field elements
; low-low, high-low, low-high, and high-high.
; Boolean variables for the lists zs, zs-carry-low, and zs-carry-high
; are introduced.
; The result of the partial multiplication of xs and ys
; is put into zs and zs-carry-low:
; here 'partial' means that it excludes the high-high part,
; i.e. it only has (low-low + 2^(n/2) * (high-low + low-high)).
; The missing part is (2^n * high-high),
; but note that this part does not affect zs,
; so the bits of zs are correct also with the partial multiplication.
; We put the bits that form high-high into zs-carry-high.
; In order to get the actual bits of the carry,
; we would have to add zs-carry-low and zs-carry-high;
; instead, the gadget returns zs-carry-low and zs-carry-high as they are
; (in the snarkVM code, these are concatenated and returned).
; This gadget is used in larger gadgets that
; just check that there is no carry,
; without needing the actual value of the carry;
; for that purpose,
; it is enough to check that zs-carry-low and zs-carry-high are 0,
; without having the calculate the actual carry bits,
; which would cost extra constraints.

; The 'medium' part of the name of this gadget refers to the fact that
; the operands are not small enough so that their product fits in the field
; (for that case, see the unsigned-small-mul-carry gadget),
; but still small enough that their Babbage sub-multiplications
; fit in the field.
; One could imagine a third gadget variant for 'large' operands,
; but currently snarkVM only generates the 'small' and 'medium' variants.

; This gadget uses Babbage multiplication.
; Using Karatsuba multiplication, we should be able to save constraints.
; That is, instead of calculating high-low and low-high separately
; (as two multiplications), we could use a constraint
;   (xs-high + xs-low) (ys-high + ys-low)
;   = (high-low+low-high + high-high + low-low)
; i.e. doing just one multiplication
; and replacing high-low and low-high
; with a variable high-low+low-high for their sum.

; Another possible optimization is
; to avoid introducing and calculating zs-carry-high,
; since the only purpose is to check that they are 0.
; It suffices to check that high-high (i.e. z2) is 0.

(define unsigned-medium-mul-carry-gadget ((xs symbol-listp)
                                          (ys symbol-listp)
                                          (low-low symbolp)
                                          (high-low symbolp)
                                          (low-high symbolp)
                                          (high-high symbolp)
                                          (zs symbol-listp)
                                          (zs-carry-low symbol-listp)
                                          (zs-carry-high symbol-listp)
                                          (p primep))
  :guard (and (< 0 (len xs))
              (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (equal (len zs-carry-low) (1+ (floor (len xs) 2)))
              (equal (len zs-carry-high) (len xs))
              (< (len (append zs zs-carry-low)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (b* ((n/2 (floor (len xs) 2))
       (xs-low (take n/2 xs))
       (xs-high (nthcdr n/2 xs))
       (ys-low (take n/2 ys))
       (ys-high (nthcdr n/2 ys)))
    (append
     (bits-mul-field-gadget xs-low ys-low low-low p)
     (bits-mul-field-gadget xs-high ys-low high-low p)
     (bits-mul-field-gadget xs-low ys-high low-high p)
     (boolean-check-gadget-list zs p)
     (boolean-check-gadget-list zs-carry-low p)
     (list
      (r1cs::make-r1cs-constraint
       :a (list (list 1 low-low)
                (list (expt 2 n/2) high-low)
                (list (expt 2 n/2) low-high))
       :b (list (list 1 1))
       :c (pow2sum-vector (append zs zs-carry-low) 0)))
     (bits-mul-field-gadget xs-high ys-high high-high p)
     (boolean-check-gadget-list zs-carry-high p)
     (pow2sum-gadget high-high zs-carry-high))))

; The proof has some similarities to unsigned-small-mul-wrapped,
; which also uses Babbage multiplication,
; but there are significant differences.

; Since all the callers of this gadget check that the carry bits are 0,
; we simplify the task of proving the soundness of this gadget
; by including preconditions saying that the carry bits are 0
; (see the formulation of the soundness theorem at the end of this file).

; In the soundness proof below,
; we enable the correctness theorem for bits-mul-field,
; which results in (mod X p) terms, which can be simplified to just X
; because of the bounds on the numbers of bits.
; The following two lemmas help with that.
; The first one simplifies a term that arises in the proof.
; The second one lets us conclude a bound from a stronger bound.

(defruledl lemma1
  (implies (and (integerp x)
                (evenp x))
           (equal (+ (floor x 2)
                     (floor x 2))
                  x))
  :enable evenp)

(defruledl lemma2
  (implies (and (natp x)
                (natp y)
                (< (+ x y) (integer-length p)))
           (< x (integer-length p))))

; This theorem says that the value of the zs result bits fits,
; so the (mod ... p) can be eliminated for that too.

(defruledl zs-fits
  (implies (and (posp p)
                (bit-listp zs)
                (< (len zs) (integer-length p)))
           (< (lebits=>nat zs)
              p))
  :rule-classes :linear
  :do-not-induct t
  :disable acl2::<-of-expt-and-expt-same-base
  :use ((:instance expt2-mono
                   (a (len zs))
                   (b (1- (integer-length p)))))
  :enable positive->=-expt2-of-integer-length-minus-1)

; The following encapsulate is quite analogous to
; the one in the unsigned-small-mul-wrapped,
; but a little simpler.
; In the soundness proof,
; because of the aforementioned preconditions (enforced by callers)
; that the carry bits are 0,
; the proof naturally splits into either xs-high = 0 or ys-high = 0,
; each of which forces low-high or high-low to be 0.
; Thus, instead of dealing with
;   x0 + (x1 * y0) * 2^m + (x0 * y1) * 2^m
; here we deal with
;   x0 + (x1 * y0) * 2^m
; in one case and with
;   x0 + (x0 * y1) * 2^m
; in the other case.

; The bound this time is 2^(3m).
; Consider the first one (the second one is symmetric):
;   x0 * y0 + 2^m * (x1 * y0)
;   <= (2^m - 1)^2 + 2^m (2^m - 1)^2
;   = (2^m - 1)^2 * (2^m + 1)
;   = (2^m - 1) * (2^m - 1) * (2^m + 1)
;   = (2^m - 1) * (2^n - 1)
;   = 2^(n+m) -2^m -2^n + 1
;   <= 2^(n+m) -2^m
;   < 2^(3m)

(encapsulate ()

  (local (include-book "arithmetic-3/top" :dir :system))

  (defruledl times-left-mono
    (implies (and (natp x)
                  (natp y)
                  (natp a)
                  (<= x y))
             (<= (* a x) (* a y))))

  (defruledl times-mono
    (implies (and (natp x)
                  (natp y)
                  (natp a)
                  (natp b)
                  (<= x a)
                  (<= y b))
             (<= (* x y) (* a b)))
    :use ((:instance times-left-mono (a x) (x y) (y b))
          (:instance times-left-mono (a b) (x x) (y a))))

  (defruledl product-bound
    (implies (and (natp m)
                  (natp x)
                  (natp y)
                  (< x (expt 2 m))
                  (< y (expt 2 m)))
             (<= (* x y)
                 (* (1- (expt 2 m))
                    (1- (expt 2 m)))))
    :use (:instance times-mono (a (1- (expt 2 m))) (b (1- (expt 2 m)))))

  (defruledl product-expt-bound
    (implies (and (natp m)
                  (natp x)
                  (natp y)
                  (< x (expt 2 m))
                  (< y (expt 2 m)))
             (<= (* x y (expt 2 m))
                 (* (1- (expt 2 m))
                    (1- (expt 2 m))
                    (expt 2 m))))
    :use product-bound)

  (defruledl lte-add2
    (implies (and (<= x a)
                  (<= y b))
             (<= (+ x y)
                 (+ a b))))

  (defruledl total-bound
    (implies (and (natp m)
                  (natp x0)
                  (natp x1)
                  (natp y0)
                  (< x0 (expt 2 m))
                  (< x1 (expt 2 m))
                  (< y0 (expt 2 m)))
             (<= (+ (* x0 y0)
                    (* x1 y0 (expt 2 m)))
                 (+ (* (1- (expt 2 m))
                       (1- (expt 2 m)))
                    (* (1- (expt 2 m))
                       (1- (expt 2 m))
                       (expt 2 m)))))
    :use ((:instance product-bound (x x0) (y y0))
          (:instance product-expt-bound (x x1) (y y0))
          (:instance lte-add2
                     (x (* x0 y0))
                     (y (* x1 y0 (expt 2 m)))
                     (a (* (1- (expt 2 m))
                           (1- (expt 2 m))))
                     (b (* (1- (expt 2 m))
                           (1- (expt 2 m))
                           (expt 2 m))))))

  (defruledl bound-of-bound
    (implies (natp m)
             (< (+ (* (1- (expt 2 m))
                      (1- (expt 2 m)))
                   (* (1- (expt 2 m))
                      (1- (expt 2 m))
                      (expt 2 m)))
                (expt 2 (* 3 m))))
    :prep-books ((acl2::scatter-exponents)))

  (defruled product-fits-lemma
    (implies (and (natp m)
                  (natp x0)
                  (natp x1)
                  (natp y0)
                  (< x0 (expt 2 m))
                  (< x1 (expt 2 m))
                  (< y0 (expt 2 m)))
             (< (+ (* x0 y0)
                   (* x1 y0 (expt 2 m)))
                (expt 2 (* 3 m))))
    :use (total-bound bound-of-bound)))

; The following two theorems cover the two cases,
; with hl = high-low and lh = low-high.

(defruledl ll+hl-fits
  (implies (and (posp p)
                (bit-listp xs)
                (bit-listp ys)
                (evenp (len xs))
                (equal (len ys) (len xs))
                (< (+ 1 (len xs) (floor (len xs) 2))
                   (integer-length p)))
           (b* ((x0 (lebits=>nat (take (floor (len xs) 2) xs)))
                (x1 (lebits=>nat (nthcdr (floor (len xs) 2) xs)))
                (y0 (lebits=>nat (take (floor (len ys) 2) ys))))
             (< (+ (* x0 y0)
                   (* x1 y0 (expt 2 (floor (len xs) 2))))
                p)))
  :do-not-induct t
  :enable evenp
  :use (:instance lemma
                  (xs-low (take (floor (len xs) 2) xs))
                  (xs-high (nthcdr (floor (len xs) 2) xs))
                  (ys-low (take (floor (len xs) 2) ys))
                  (m (floor (len xs) 2)))
  :prep-lemmas
  ((defruled lemma
     (implies (and (posp p)
                   (bit-listp xs-low)
                   (bit-listp xs-high)
                   (bit-listp ys-low)
                   (equal (len xs-low) m)
                   (equal (len xs-high) m)
                   (equal (len ys-low) m)
                   (< (* 3 m) (integer-length p)))
              (b* ((x0 (lebits=>nat xs-low))
                   (x1 (lebits=>nat xs-high))
                   (y0 (lebits=>nat ys-low)))
                (< (+ (* x0 y0)
                      (* x1 y0 (expt 2 m)))
                   p)))
     :do-not-induct t
     :use ((:instance product-fits-lemma
                      (x0 (lebits=>nat xs-low))
                      (x1 (lebits=>nat xs-high))
                      (y0 (lebits=>nat ys-low)))
           (:instance expt2-mono
                      (a (* 3 m))
                      (b (1- (integer-length p)))))
     :disable acl2::<-of-expt-and-expt-same-base
     :enable positive->=-expt2-of-integer-length-minus-1)))

(defruledl ll+lh-fits
  (implies (and (posp p)
                (bit-listp xs)
                (bit-listp ys)
                (evenp (len xs))
                (equal (len ys) (len xs))
                (< (+ 1 (len xs) (floor (len xs) 2))
                   (integer-length p)))
           (b* ((x0 (lebits=>nat (take (floor (len xs) 2) xs)))
                (y0 (lebits=>nat (take (floor (len ys) 2) ys)))
                (y1 (lebits=>nat (nthcdr (floor (len ys) 2) ys))))
             (< (+ (* x0 y0)
                   (* x0 y1 (expt 2 (floor (len xs) 2))))
                p)))
  :do-not-induct t
  :enable evenp
  :use (:instance lemma
                  (xs-low (take (floor (len xs) 2) xs))
                  (ys-low (take (floor (len xs) 2) ys))
                  (ys-high (nthcdr (floor (len xs) 2) ys))
                  (m (floor (len xs) 2)))
  :prep-lemmas
  ((defruled lemma
     (implies (and (posp p)
                   (bit-listp xs-low)
                   (bit-listp ys-low)
                   (bit-listp ys-high)
                   (equal (len xs-low) m)
                   (equal (len ys-low) m)
                   (equal (len ys-high) m)
                   (< (* 3 m) (integer-length p)))
              (b* ((x0 (lebits=>nat xs-low))
                   (y0 (lebits=>nat ys-low))
                   (y1 (lebits=>nat ys-high)))
                (< (+ (* x0 y0)
                      (* x0 y1 (expt 2 m)))
                   p)))
     :do-not-induct t
     :use ((:instance product-fits-lemma
                      (x0 (lebits=>nat ys-low))
                      (y0 (lebits=>nat xs-low))
                      (x1 (lebits=>nat ys-high)))
           (:instance expt2-mono
                      (a (* 3 m))
                      (b (1- (integer-length p)))))
     :disable acl2::<-of-expt-and-expt-same-base
     :enable positive->=-expt2-of-integer-length-minus-1)))

; Finally we prove soundness.
; Note that we use the binary version of Babbage multiplcation,
; so that we don't have to enable lebits=>nat,
; which would prevent certain rules we use from firing.

(defruled unsigned-medium-mul-carry-gadget-soundness
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbolp low-low)
                (symbolp high-low)
                (symbolp low-high)
                (symbolp high-high)
                (symbol-listp zs)
                (symbol-listp zs-carry-low)
                (symbol-listp zs-carry-high)
                (< 0 (len xs))
                (evenp (len xs))
                (equal (len ys) (len xs))
                (equal (len zs) (len xs))
                (equal (len zs-carry-low) (1+ (floor (len xs) 2)))
                (equal (len zs-carry-high) (len xs))
                (< (len (append zs zs-carry-low)) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg low-low)
                (r1cs::valuation-bindsp asg high-low)
                (r1cs::valuation-bindsp asg low-high)
                (r1cs::valuation-bindsp asg high-high)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg zs-carry-low)
                (r1cs::valuation-binds-allp asg zs-carry-high))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg))
                (zs-carry-low$ (lookup-equal-list zs-carry-low asg))
                (zs-carry-high$ (lookup-equal-list zs-carry-high asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$)
                           (equal zs-carry-low$
                                  (repeat (len zs-carry-low) 0))
                           (equal zs-carry-high$
                                  (repeat (len zs-carry-high) 0)))
                      (implies
                       (r1cs::r1cs-constraints-holdp
                        (unsigned-medium-mul-carry-gadget xs
                                                          ys
                                                          low-low
                                                          high-low
                                                          low-high
                                                          high-high
                                                          zs
                                                          zs-carry-low
                                                          zs-carry-high
                                                          p)
                        asg
                        p)
                       (and (bit-listp zs$)
                            (equal (lebits=>nat zs$)
                                   (* (lebits=>nat xs$)
                                      (lebits=>nat ys$))))))))
  :do-not-induct t
  :use ((:instance ll+hl-fits
                   (xs (lookup-equal-list xs asg))
                   (ys (lookup-equal-list ys asg)))
        (:instance ll+lh-fits
                   (xs (lookup-equal-list xs asg))
                   (ys (lookup-equal-list ys asg)))
        (:instance babbage-mul-lebits-correct
                   (x-bits (lookup-equal-list xs asg))
                   (y-bits (lookup-equal-list ys asg))
                   (n (floor (len xs) 2))))
  :enable (unsigned-medium-mul-carry-gadget
           bits-mul-field-gadget-to-equal-of-mul
           boolean-check-gadget-list-to-bit-listp
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pow2sum-vector-to-mod-of-lebits=>nat
           pow2sum-gadget-to-equal-of-mod-of-lebits=>nat
           lookup-equal-list-of-append
           lookup-equal-list-of-take
           lookup-equal-list-of-nthcdr
           pfield::add
           pfield::mul
           acl2::lebits=>nat-of-append
           lemma1
           lemma2
           zs-fits
           babbage-mul-lebits))
