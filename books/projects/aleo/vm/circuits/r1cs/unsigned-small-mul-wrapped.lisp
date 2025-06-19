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

; This gadget uses Karatsuba-style (Babbage, in fact) multiplication
; on the bit lists that are used for integers.  (Unsigned integers, for now.)

; Starting with N variables for the bits of x,
; and N variables for the bits of y,
; it takes the lists one half at a time, so we have low-xs, high-xs,
; low-ys, and high-ys lists of bits.  (They are in little-endian order.)
; Note that each bit is in a separate variable, so the R1CS
; doesn't actually split any list in half; this is just how
; we would like to think about the bit variables.
; Each (half) list is turned into a number using a weighted sum.
; We designate the weighted sum of the low bits of x `low-x`
; and the weighted sum of the high bits of x `high-x`,
; so, e.g., x equals low-x + (2^(N/2) * high-x).
;
; Then the product of x and y is
;   (low-x * low-y)
;   + (2^(N/2) * high-x * low-y)
;   + (2^(N/2) * low-x * high-y)
;   + (2^N * high-x * high-y)
; restricted to the low N bits (throwing away all the carry bits).

; The last term does not affect the low N bits, so
; the gadget ignores the last term.
; For the remaining three terms, a field variable is set
; to each term (exclusive of the scaling factor), like:
;   lowlow = low-x * low-y
;   highlow = high-x * low-y
;   lowhigh = low-x * high-y
; and then these are added in a term
;   lowlow + (2^(N/2) * highlow) + (2^(N/2) * lowhigh) = low-and-medium-z
; where low-and-medium-z is a weighted sum of (N/2 + N + 1) bits.
; That is because that is how many bits you need to represent the maximum
; sum of those three terms.
;
; Note, the return value is just the N bits of zs.
; The carry bits im zs-high are ignored --- that is the meaning
; of "wrapped".

; Note that "small" for the mul-wrapped gadget means something different
; than "small" for mul-checked.
; Mul-wrapped requires looking at (N/2 + N + 1) bits.
; For safety and generality, we say
;   (N/2 + N + 1) < (integer-length p)
; *however*, in some cases, including when using the scalar field of BLS12-377
; (aka the base field of the edwards-bls12 curve),
; the maximum value of the low (N/2 + N + 1) bits of the product is less than p.
; So for this particular p that has 253 bits, it would still be possible
; to multiply 168-bit operands.  A consequence is that if the largest supported
; integer type is 128 bits for a prime of 153 bits then no
; "large-mul-wrapped-gadget" will be needed.

(define unsigned-small-mul-wrapped-gadget ((xs symbol-listp)
                                           (ys symbol-listp)
                                           (lowlow symbolp)
                                           (highlow symbolp)
                                           (lowhigh symbolp)
                                           (zs symbol-listp)
                                           (zs-high symbol-listp)
                                           (p primep))
  :guard (and (< 0 (len xs))
              (evenp (len xs))
              (equal (len ys) (len xs))
              (equal (len zs) (len xs))
              (equal (len zs-high) (1+ (floor (len xs) 2)))
              (< (len (append zs zs-high)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (b* ((n/2 (floor (len xs) 2))
       (low-xs (take n/2 xs))
       (high-xs (nthcdr n/2 xs))
       (low-ys (take n/2 ys))
       (high-ys (nthcdr n/2 ys)))
    (append (bits-mul-field-gadget low-xs
                                   low-ys
                                   lowlow
                                   p)
            (bits-mul-field-gadget high-xs
                                   low-ys
                                   highlow
                                   p)
            (bits-mul-field-gadget low-xs
                                   high-ys
                                   lowhigh
                                   p)
            (boolean-check-gadget-list zs p)
            (boolean-check-gadget-list zs-high p)
            (list
             ;; (lowlow + 2^(n/2).highlow + 2^(n/2).lowhigh)
             ;; *
             ;; (1)
             ;; =
             ;; (zs(0) + 2.zs(1) + ... + 2^(n-1).zs(n-1) +
             ;;  2^n.zs-high(0) + ... + 2^(n+n/2).zs-high(n/2)):
             (r1cs::make-r1cs-constraint
              :a (list (list 1 lowlow)
                       (list (expt 2 n/2) highlow)
                       (list (expt 2 n/2) lowhigh))
              :b (list (list 1 1))
              :c (pow2sum-vector (append zs zs-high) 0))))))

; The soundness proof of this gadget takes a little bit of work.
; The soundness theorem is at the end of this file,
; preceded by lemmas used in that proof.
; The proof of the main theorem uses proof builder instructions,
; because the key proof steps do not seem to be readily amenable
; to the kind of rewriting strategies that ACL2 uses;
; it may be possible to make the proof more concise,
; but at least currently it is understandable and hopefully easy to maintain.

; The first :claim instruction in that theorem
; opens the gadget definition,
; uses correctness theorems for the subgadgets and linear combinations,
; expands the explicit R1CS constraint,
; and expands the field addition and multiplication operations,
; to obtain a fact that involves + and * and acl2::lendian=>bits.
; The expansion of field addition and multiplication
; naturally leads to the presence of mod p.
; However, these can be all eliminated
; (in fact, the claim has no trace of mod p).

; First, the calculation of the linear combination of zs and zs-high
; fits in the field, because the total length is
; below the integer length of the prime.
; This is expressed by the following theorem,
; which could be a more general rule.
; (We use ws for what will be the concatenation of zs and zs-high;
; see main theorem.)

(defruledl z-fits
  (implies (and (primep p)
                (bit-listp ws)
                (< (len ws) (integer-length p)))
           (< (lebits=>nat ws)
              p))
  :do-not-induct t
  :disable acl2::<-of-expt-and-expt-same-base
  :use ((:instance expt2-mono
                   (a (len ws))
                   (b (1- (integer-length p)))))
  :enable positive->=-expt2-of-integer-length-minus-1)

; We also need to show that the calculation involving x and y,
; namely sum = lowlow + highlow * 2^m + lowhigh * 2^m, where m = n/2,
; fits in the field; the reason is the following.
; Each of x0, x1, y0, y1 (using the Babbage terminology) is <= 2^m - 1,
; and therefore each of lowlow, highlow, lowhigh is <= (2^m - 1)^2.
; Thus we have sum <= (2^m - 1)^2 + 2 * (2^m - 1)^2 * 2^m.
; Our hypothesis on the gadget is that
; the length of zs with zs-high is < the length of the prime,
; where the length of zs is 2m and the length of zs-high is m + 1;
; thus our hypothesis is 3m + 1 < integer length of p.
; Thus, if we can show that sum is < 2^(3m+1),
; the sum fits in the field and we can remove the mod p.
; So we need to show that
;   (2^m - 1)^2 + 2 * (2^m - 1)^2 * 2^m < 2^(3m+1)
; i.e., refactoring the left side, that
;   (2^m - 1)^2 * (1 + 2^(m+1)) < 2^(3m+1)
; i.e., expanding the square, that
;   (2^(2m) - 2^(m+1) + 1) (1 + 2^(m+1)) < 2^(3m+1)
; i.e., distributing multiplications over additions, that
;   2^(2m) - 2^(m+1) + 1 + 2^(3m+1) - 2^(2*m+2) + 2^(m+1) < 2^(3m+1)
; i.e., simplifying away terms of opposite sign on the left, that
;   2^(2m) + 1 + 2^(3m+1) - 2^(2m+2) < 2^(3m+1)
; i.e., simplifying away equal terms on the left and right, that
;   2^(2m) + 1 - 2^(2m+2) < 0
; i.e., refactoring the left side, that
;   1 - 3 * 2^(2m) < 0,
; which holds for every m >= 0.
; We prove this key lemma below, with the help of arithmetic-5.

(local
 (encapsulate ()

   (local (include-book "arithmetic-5/top" :dir :system))

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

   (defruledl lte-add3
     (implies (and (<= x a)
                   (<= y b)
                   (<= z c))
              (<= (+ x y z)
                  (+ a b c))))

   (defruledl total-bound
     (implies (and (natp m)
                   (natp x0)
                   (natp x1)
                   (natp y0)
                   (natp y1)
                   (< x0 (expt 2 m))
                   (< x1 (expt 2 m))
                   (< y0 (expt 2 m))
                   (< y1 (expt 2 m)))
              (<= (+ (* x0 y0)
                     (* x0 y1 (expt 2 m))
                     (* x1 y0 (expt 2 m)))
                  (+ (* (1- (expt 2 m))
                        (1- (expt 2 m)))
                     (* (1- (expt 2 m))
                        (1- (expt 2 m))
                        (expt 2 m))
                     (* (1- (expt 2 m))
                        (1- (expt 2 m))
                        (expt 2 m)))))
     :use ((:instance product-bound (x x0) (y y0))
           (:instance product-expt-bound (x x0) (y y1))
           (:instance product-expt-bound (x x1) (y y0))
           (:instance lte-add3
                      (x (* x0 y0))
                      (y (* x0 y1 (expt 2 m)))
                      (z (* x1 y0 (expt 2 m)))
                      (a (* (1- (expt 2 m))
                            (1- (expt 2 m))))
                      (b (* (1- (expt 2 m))
                            (1- (expt 2 m))
                            (expt 2 m)))
                      (c (* (1- (expt 2 m))
                            (1- (expt 2 m))
                            (expt 2 m))))))

   (defruledl bound-of-bound
     (implies (natp m)
              (< (+ (* (1- (expt 2 m))
                       (1- (expt 2 m)))
                    (* (1- (expt 2 m))
                       (1- (expt 2 m))
                       (expt 2 m))
                    (* (1- (expt 2 m))
                       (1- (expt 2 m))
                       (expt 2 m)))
                 (expt 2 (1+ (* 3 m)))))
     :prep-books ((acl2::scatter-exponents)))

   (defruled xy-fits-lemma
     (implies (and (natp m)
                   (natp x0)
                   (natp x1)
                   (natp y0)
                   (natp y1)
                   (< x0 (expt 2 m))
                   (< x1 (expt 2 m))
                   (< y0 (expt 2 m))
                   (< y1 (expt 2 m)))
              (< (+ (* x0 y0)
                    (* x1 y0 (expt 2 m))
                    (* x0 y1 (expt 2 m)))
                 (expt 2 (1+ (* 3 m)))))
     :use (total-bound bound-of-bound))))

; We use the lemma just proved above to show that
; the calculation on xs and ys fits in the field.

(defruledl xy-fits
  (implies (and (primep p)
                (bit-listp xs)
                (bit-listp ys)
                (evenp (len xs))
                (equal (len ys) (len xs))
                (< (+ 1 (len xs) (floor (len xs) 2))
                   (integer-length p)))
           (b* ((x0 (lebits=>nat (take (floor (len xs) 2) xs)))
                (x1 (lebits=>nat (nthcdr (floor (len xs) 2) xs)))
                (y0 (lebits=>nat (take (floor (len ys) 2) ys)))
                (y1 (lebits=>nat (nthcdr (floor (len ys) 2) ys))))
             (< (+ (* x0 y0)
                   (* x1 y0 (expt 2 (floor (len xs) 2)))
                   (* x0 y1 (expt 2 (floor (len xs) 2))))
                p)))
  :do-not-induct t
  :enable evenp
  :use (:instance lemma
                  (xs-low (take (floor (len xs) 2) xs))
                  (xs-high (nthcdr (floor (len xs) 2) xs))
                  (ys-low (take (floor (len xs) 2) ys))
                  (ys-high (nthcdr (floor (len xs) 2) ys))
                  (m (floor (len xs) 2)))
  :prep-lemmas
  ((defruled lemma
     (implies (and (primep p)
                   (bit-listp xs-low)
                   (bit-listp xs-high)
                   (bit-listp ys-low)
                   (bit-listp ys-high)
                   (equal (len xs-low) m)
                   (equal (len xs-high) m)
                   (equal (len ys-low) m)
                   (equal (len ys-high) m)
                   (< (1+ (* 3 m)) (integer-length p)))
              (b* ((x0 (lebits=>nat xs-low))
                   (x1 (lebits=>nat xs-high))
                   (y0 (lebits=>nat ys-low))
                   (y1 (lebits=>nat ys-high)))
                (< (+ (* x0 y0)
                      (* x1 y0 (expt 2 m))
                      (* x0 y1 (expt 2 m)))
                   p)))
     :do-not-induct t
     :use ((:instance xy-fits-lemma
                      (x0 (lebits=>nat xs-low))
                      (x1 (lebits=>nat xs-high))
                      (y0 (lebits=>nat ys-low))
                      (y1 (lebits=>nat ys-high)))
           (:instance expt2-mono
                      (a (1+ (* 3 m)))
                      (b (1- (integer-length p)))))
     :disable acl2::<-of-expt-and-expt-same-base
     :enable positive->=-expt2-of-integer-length-minus-1)))

; Another key property concerns Babbage multiplication.
; If we calculate Babbage multiplication modulo 2^n
; (where n is the number of low digits),
; we can ignore the z2 addend.
; This serves to justify the fact that the gadget
; does not calculate z2 at all;
; this avoids an extra multiplication,
; and thus in this case Babbage is as efficient as Karatsuba
; in terms of number of multiplications.

(defruledl babbage-mod-lemma
  (implies (and (acl2::dab-basep base)
                (equal (len y-digits) (len x-digits))
                (natp n)
                (< n (len x-digits)))
           (equal (mod (babbage-mul-lendian base x-digits y-digits n)
                       (expt base (* 2 n)))
                  (b* ((x0 (acl2::lendian=>nat base (take n x-digits)))
                       (y0 (acl2::lendian=>nat base (take n y-digits)))
                       (x1 (acl2::lendian=>nat base (nthcdr n x-digits)))
                       (y1 (acl2::lendian=>nat base (nthcdr n y-digits)))
                       (z0 (* x0 y0))
                       (z1 (+ (* x1 y0)
                              (* x0 y1))))
                    (mod (+ z0 (* z1 (expt base n)))
                         (expt base (* 2 n))))))
  :enable babbage-mul-lendian)

; Finally we need a simple arithmetic lemma.

(defruledl arith-lemma
  (implies (and (posp k)
                (natp a)
                (< a k)
                (natp b))
           (equal (mod (+ a (* b k)) k)
                  a)))

; Below is the main theorem, i.e. the soundness proof of the gadget.
; As mentioned earlier, we use proof builder instructions,
; since the proof does not seem readily amenable to
; the typical kind of "normalizing" rewrites that ACL2 employs.
; The steps are commented below.

(defruled unsigned-small-mul-wrapped-gadget-soundness
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbolp lowlow)
                (symbolp highlow)
                (symbolp lowhigh)
                (symbol-listp zs)
                (symbol-listp zs-high)
                (< 0 (len xs))
                (evenp (len xs))
                (equal (len ys) (len xs))
                (equal (len zs) (len xs))
                (equal (len zs-high) (1+ (floor (len xs) 2)))
                (< (len (append zs zs-high)) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-bindsp asg lowlow)
                (r1cs::valuation-bindsp asg highlow)
                (r1cs::valuation-bindsp asg lowhigh)
                (r1cs::valuation-binds-allp asg zs)
                (r1cs::valuation-binds-allp asg zs-high))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$))
                      (implies (r1cs::r1cs-constraints-holdp
                                (unsigned-small-mul-wrapped-gadget
                                 xs ys lowlow highlow lowhigh zs zs-high p)
                                asg
                                p)
                               (and (bit-listp zs$)
                                    (equal (lebits=>nat zs$)
                                           (mod (* (lebits=>nat xs$)
                                                   (lebits=>nat ys$))
                                                (expt 2 (len xs)))))))))

  :instructions

  (;; We normalize the structure of the proof,
   ;; promoting the antecedents,
   ;; expanding the b*,
   ;; and splitting into two subgoals.
   (:bash)

   ;; The first subgoal is the bit-listp conjunct, which is easy:
   ;; it follows from the correctness of the bit check gadgets.
   (:prove ; bit-listp conjunct
    :hints
    (("Goal" :in-theory (enable unsigned-small-mul-wrapped-gadget
                                boolean-check-gadget-list-to-bit-listp))))

   ;; The second subgoal is proved in a few step.
   ;; The first one has been mentioned earlier:
   ;; we expand the subgadgets and we eliminate mod p.
   ;; Note the use of the z-fits and xy-fits lemmas.
   ;; This claim is actually the conjunction of several claims.
   (:claim
    (and (equal (lookup-equal lowlow asg)
                (* (lebits=>nat (take (floor (len xs) 2)
                                            (lookup-equal-list xs asg)))
                   (lebits=>nat (take (floor (len xs) 2)
                                            (lookup-equal-list ys asg)))))
         (equal (lookup-equal highlow asg)
                (* (lebits=>nat (nthcdr (floor (len xs) 2)
                                              (lookup-equal-list xs asg)))
                   (lebits=>nat (take (floor (len xs) 2)
                                            (lookup-equal-list ys asg)))))
         (equal (lookup-equal lowhigh asg)
                (* (lebits=>nat (nthcdr (floor (len xs) 2)
                                              (lookup-equal-list ys asg)))
                   (lebits=>nat (take (floor (len xs) 2)
                                            (lookup-equal-list xs asg)))))
         (bit-listp (lookup-equal-list zs asg))
         (bit-listp (lookup-equal-list zs-high asg))
         (equal (+ (lookup-equal lowlow asg)
                   (* (expt 2 (floor (len xs) 2))
                      (lookup-equal highlow asg))
                   (* (expt 2 (floor (len xs) 2))
                      (lookup-equal lowhigh asg)))
                (+ (lebits=>nat (lookup-equal-list zs asg))
                   (* (expt 2 (len xs))
                      (lebits=>nat (lookup-equal-list zs-high asg))))))
    :hints (("Goal"
             :do-not-induct t
             :use ((:instance z-fits
                              (ws (lookup-equal-list (append zs zs-high) asg)))
                   (:instance xy-fits
                              (xs (lookup-equal-list xs asg))
                              (ys (lookup-equal-list ys asg))))
             :in-theory (enable unsigned-small-mul-wrapped-gadget
                                bits-mul-field-gadget-to-equal-of-mul
                                boolean-check-gadget-list-to-bit-listp
                                r1cs::r1cs-constraint-holdsp
                                r1cs::dot-product
                                pow2sum-vector-to-mod-of-lebits=>nat
                                acl2::lebits=>nat-of-append
                                lookup-equal-list-of-append
                                lookup-equal-list-of-take
                                lookup-equal-list-of-nthcdr
                                pfield::add
                                pfield::mul))))

   ;; Now we apply mod 2^n to both sides of the last claim conjunct above,
   ;; and eliminate it from the right side thanks to the arithmetic lemma.
   (:claim
    (equal (mod (+ (lookup-equal lowlow asg)
                   (* (expt 2 (floor (len xs) 2))
                      (lookup-equal highlow asg))
                   (* (expt 2 (floor (len xs) 2))
                      (lookup-equal lowhigh asg)))
                (expt 2 (len xs)))
           (lebits=>nat (lookup-equal-list zs asg)))
    :hints (("Goal"
             :use (:instance
                   arith-lemma
                   (k (expt 2 (len xs)))
                   (a (lebits=>nat (lookup-equal-list zs asg)))
                   (b (lebits=>nat (lookup-equal-list zs-high asg)))))))

   ;; Now we replace the sum of three addends above
   ;; with Babbage multiplication, using the lemma proved above.
   (:claim
    (equal (mod (babbage-mul-lendian 2
                                     (lookup-equal-list xs asg)
                                     (lookup-equal-list ys asg)
                                     (floor (len xs) 2))
                (expt 2 (len xs)))
           (lebits=>nat (lookup-equal-list zs asg)))
    :hints (("Goal"
             :use (:instance babbage-mod-lemma
                             (base 2)
                             (x-digits (lookup-equal-list xs asg))
                             (y-digits (lookup-equal-list ys asg))
                             (n (floor (len xs) 2)))
             :in-theory (enable lebits=>nat))))

   ;; Finally we conclude the subgoal,
   ;; using the correctnes theorem of Babbage multiplication,
   ;; which says that it does calculate multiplication (i.e. *).
   ;; That is, the value of zs is the modular multiplication of xs and ys.
   (:prove
    :hints (("Goal"
             :use (:instance babbage-mul-lendian-correct
                             (base 2)
                             (x-digits (lookup-equal-list xs asg))
                             (y-digits (lookup-equal-list ys asg))
                             (n (floor (len xs) 2)))
             :in-theory (enable lebits=>nat))))))
