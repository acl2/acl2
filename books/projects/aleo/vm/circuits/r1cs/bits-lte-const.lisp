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

(include-book "boolean-and")
(include-book "boolean-or")

(include-book "kestrel/utilities/bits-as-digits" :dir :system)

(local (include-book "../library-extensions/digits"))
(local (include-book "../library-extensions/r1cses"))

(local (include-book "projects/pfcs/r1cs-lib-ext" :dir :system))
(local (include-book "std/lists/last" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is a bitwise less-than-or-equal-to comparison gadget,
; between a variable value and a known constant value.
; Given boolean variables x(0) x(1) ... x(n-1)
; and given boolean values c(0) c(1) ... c(n-1),
; in equal number n,
; this gadget checks whether x <= c,
; where x = x(0) + 2*x(1) + ... + 2^(n-1)*x(n-1)
; and c = c(0) + 2*c(1) + ... + 2^(n-1)*c(n-1).
; Note that x and c are not confined to be below the prime:
; they can be any value, even consist of millions of bits;
; this gadget operates on bits, it does not calculate any weighted sums.
; The values x and c are not calculated by the gadget,
; which only manipulates these two values via their bits.
; All the gadget operations are on bits.

; The exact constraints depend on the bits c(0) c(1) ..., as follows.
; It is easier to explain a more uniform construction first,
; and then how it is optimized to obtain the actual gadget.

; The unoptimized construction
; calculates result bits r(-1) r(0) r(1) .. r(n-1) as follows:
;   r(-1) = 0
;   r(i) = x(i) OR r(i-1), if c(i) = 0
;   r(i) = x(i) AND r(i-1), if c(i) = 1
; We use r(-1) to start off things, and then each r(i), with 0 <= i < n,
; is calculated uniformly.

; This is an illustration of the bits:
;         c(0) c(1) ... c(n-1)
;         x(0) x(1) ... x(n-1)
;   r(-1) r(0) r(1) ... r(n-1)

; It is the case that r(i) = 0
; iff x(0) + 2*x(1) + ... + 2^i*x(i) <= c(0) + 2*c(1) + ... + 2^i*c(i).
; At the beginning, r(-1) = 0, because 0 <= 0.
; By induction, we see that
; if the above fact holds for i, it also holds for i+1:
; - If c(i+1) = 0, the only way for <= to hold is that
;   both x(i+1) = 0 and also r(i) = 0.
;   So OR is the appropriate operation, as it is 0 iff both operands are 0.
; - If c(i+1) = 1, there are two cases:
;   - If x(i+1) = 0, then <= holds, regardless of r(i).
;   - If x(i+1) = 1, then we must have r(i) = 0 for <= to hold.
;   So AND is the appropriate operation, as it is 0 iff any operand is 0.

; Now let us see how this is optimized for the actual gadget.
; In general, there will be a k such that
; c(0) = ... = c(k-1) = 1 and c(k) = 0,
; i.e. k is the position of the least significant bit that is 0.
; It may well be k = 0, i.e. the least significant of c could be 0.
; If there is no 0 at all in the bits of c, it means that c = 2^n-1,
; and thus x <= c always holds; so this is not an interesting case,
; which can be dealt with separately
; (this gadget is used to check whether something
; is less than or equal to the prime minus 1,
; in which case c is not all 1s).
; We can also assume that k /= n-1,
; i.e. there must be more significant bits after position k;
; this is because presumably the most significant bit of c is 1,
; otherwise we would pick a smaller n
; (separately checking that the bits in x above n are all 0).
; In any case, the situation in which k = n-1 can be dealt with separately.
; So the bits of c are 1 ... 1 0 ... (from least to most significant),
; i.e. there are zero or more 1s, then a 0, and then more bits.

; Let us rewrite the constraints, highlighting the ones for k:
;   r(-1) = 0
;   r(0) = x(0) AND r(-1) = x(0) AND 0 = 0
;   r(1) = x(1) AND r(0) = x(1) AND 0 = 0
;   ...
;   r(k-1) = x(k-1) AND r(k-2) = x(k-1) AND 0 = 0
;   r(k) = x(k) OR r(k-1) = x(k) OR 0 = x(k)
;   r(k+1) = x(k+1) AND/OR r(k) = x(k+1) AND/OR x(k)
;   r(k+2) = x(k+2) AND/OR r(k+1)
;   ...
;   r(n-1) = x(n-1) AND/OR r(n-1)
; We have used AND/OR to denote either AND or OR, depending on the bit of c.
; Note that r(-1) through r(k-1) are all constant 0,
; so there is no need to introduce them as variables,
; and to have any constraint about them.
; We also do not need a variable for r(k), because it is the same as x(k).
; We need variables for r(k+1) through r(n-1),
; and they are all defined uniformly
; by combining the x bit with the previous r bit,
; except that r(k+1) is defined by combigninf the x bit with the previous x bit.
; So the first constraint is a little different from the subsequent ones.
; This is the case also if k = 0: we have r(1) = x(1) AND/OR x(0).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; As explained above, the number of r variables depends on c.
; Since our generic gadget takes the r variables as input,
; we need to know their number before we define the generic gadget.
; We do so via the following auxiliary function,
; which goes through the c bits (assumed in little endian order),
; until it finds a 0 bit,
; at which point it returns the length of the rest of the c bits after the 0
; as the number of r bits (see explanation given above).
; We require that there is at least a 0 bit,
; and also that the highest bit is 1;
; the rationale for this is explained earlier.

(define bits-lte-const-rlen ((cs bit-listp))
  :guard (and (member-equal 0 cs)
              (equal (car (last cs)) 1))
  :returns (len natp)
  (cond ((endp cs) 0)
        ((equal (car cs) 0) (len (cdr cs)))
        (t (bits-lte-const-rlen (cdr cs))))
  ///

  (more-returns
   (len posp
        :hyp (and (member-equal 0 cs)
                  (equal (car (last cs)) 1))
        :rule-classes :type-prescription
        :hints (("Goal" :in-theory (enable last)))))

  (defret bits-lte-const-rlen-lower-bound
    (> len 0)
    :hyp (and (member-equal 0 cs)
              (equal (car (last cs)) 1))
    :rule-classes :linear)

  (defret bits-lte-const-rlen-upper-bound
    (< len (len cs))
    :hyp (and (member-equal 0 cs)
              (equal (car (last cs)) 1))
    :rule-classes :linear))

; We build the gadget as follows.
; Here xs and cs are equal-length lists of variables and bits,
; in little endian order,
; while rs is the list of r variables, also in little endian order,
; whose length is calculated by the function above.
; We skip over all the c bits that are 1:
; see the nthcdr applied to cs below, which keeps the last rlen bits of cs.
; We also skip over almost as many xs variables as cs bits,
; more precisely we keep the last rlen + 1 variables of xs:
; see the nthcdr applied to xs below
; In reference to the explanation given earlier,
; where k is the position of the first 0 bit in cs,
; we keep
;        c(k+1) c(k+2) ... c(n-1)
;   x(k) x(k+1) x(k+2) ... x(n-1)
; with all the rs variables being
;        r(k+1) r(k+2) ... r(n-1)
; which let us write the optimize constraints discussed above.
; These constraints are more naturally generated in big endian order,
; using the auxiliary function below.
; We pass the reversed lists to the auxiliary function,
; and then we reverse the resulting constraints
; so that they appear in the order given earlier.

(define bits-lte-const-gadget ((xs symbol-listp)
                               (cs bit-listp)
                               (rs symbol-listp)
                               (p primep))
  :guard (and (member-equal 0 cs)
              (equal (car (last cs)) 1)
              (equal (len xs) (len cs))
              (equal (len rs) (bits-lte-const-rlen cs)))
  :returns (constrs r1cs::r1cs-constraint-listp
                    :hyp :guard
                    :hints
                    (("Goal" :in-theory (enable bits-lte-const-rlen))))
  (b* ((rlen (bits-lte-const-rlen cs))
       (trimmed-xs (nthcdr (- (len xs) (1+ rlen)) xs))
       (trimmed-cs (nthcdr (- (len cs) rlen) cs)))
    (rev (bits-lte-const-gadget-aux (rev trimmed-xs)
                                    (rev trimmed-cs)
                                    (rev rs)
                                    p)))

  :prepwork
  ((define bits-lte-const-gadget-aux ((xs symbol-listp)
                                      (cs bit-listp)
                                      (rs symbol-listp)
                                      (p primep))
     :guard (and (equal (len xs) (1+ (len cs)))
                 (equal (len rs) (len cs))
                 (consp cs))
     :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
     (cond ((endp (cdr cs))
            (if (equal (car cs) 0)
                (boolean-or-gadget (car xs) (cadr xs) (car rs) p)
              (boolean-and-gadget (car xs) (cadr xs) (car rs))))
           (t (append (if (equal (car cs) 0)
                          (boolean-or-gadget (car xs) (cadr rs) (car rs) p)
                        (boolean-and-gadget (car xs) (cadr rs) (car rs)))
                      (bits-lte-const-gadget-aux (cdr xs)
                                                 (cdr cs)
                                                 (cdr rs)
                                                 p)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; In order to verify this gadget, it is convenient to define a function
; that expresses the recursive definition of rs described above:
; it calculates rs from (the trimmed and reversed) xs and cs.
; This corresponds to the constraints given above.
; Note that there is one more bit in xs than in cs, and that cs is not empty.

(local
 (define calc-rs ((xs bit-listp) (cs bit-listp))
   :guard (and (equal (len xs) (1+ (len cs)))
               (consp cs))
   :returns (rs bit-listp)
   (cond ((endp cs) nil)
         ((endp (cdr cs))
          (list (if (equal (car cs) 0)
                    (bitor (car xs) (cadr xs))
                  (bitand (car xs) (cadr xs)))))
         (t (b* ((cdr-rs (calc-rs (cdr xs) (cdr cs)))
                 (car-rs (if (equal (car cs) 0)
                             (bitor (car xs) (car cdr-rs))
                           (bitand (car xs) (car cdr-rs)))))
              (cons car-rs cdr-rs))))
   :verify-guards nil ; done below
   ///

   (more-returns
    (rs bit-listp
        :name bit-listp-of-calc-rs-forward
        :rule-classes
        ((:forward-chaining :trigger-terms ((calc-rs xs cs))))))

   (in-theory (disable bit-listp-of-calc-rs-forward))

   (defruled bitp-of-car-of-calc-rs-forward
     (implies (consp cs)
              (bitp (car (calc-rs xs cs))))
     :rule-classes ((:forward-chaining :trigger-terms ((car (calc-rs xs cs))))))

   (defret len-of-calc-rs
     (equal (len rs) (len cs)))

   (defret consp-of-calc-rs
     (equal (consp rs) (consp cs)))

   (verify-guards calc-rs)))

; We show that this calculation of rs is indeed consistent with the constraints.
; For this, we consider the auxiliary function that defines the gadget,
; i.e. the one that takes the trimmed (and reversed) xs and cs.
; We use a custom induction schema ind;
; attempting to use the bits-lte-const-gadget-aux induction fails.
; If bitp is not disabled, the proof fails.
; The disabling of cons-equal is just for speed, to avoid some case splits.
; Note also the use of the forward chaining rule for calc-rs,
; needed to provide that fact,
; which otherwise seems harder to get by rewriting.
; Note also that we use the correctness theorems of
; the boolean 'and' and 'or' gadgets.

(defruledl bits-lte-gadget-aux-implies-calc-rs
  (implies (and (symbol-listp xs)
                (bit-listp cs)
                (symbol-listp rs)
                (equal (len xs) (1+ (len cs)))
                (equal (len rs) (len cs))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg rs))
           (b* ((xs$ (lookup-equal-list xs asg))
                (rs$ (lookup-equal-list rs asg)))
             (implies (bit-listp xs$)
                      (implies
                       (r1cs::r1cs-constraints-holdp
                        (bits-lte-const-gadget-aux xs cs rs p) asg p)
                       (equal rs$ (calc-rs xs$ cs))))))
  :induct (ind xs cs rs)
  :enable (bits-lte-const-gadget-aux
           boolean-or-gadget-to-bitor
           boolean-and-gadget-to-bitand
           calc-rs
           lookup-equal-list
           bit-listp-of-calc-rs-forward)
  :disable (bitp cons-equal)
  :prep-books ((include-book "arithmetic/top" :dir :system))
  :prep-lemmas
  ((defun ind (xs cs rs)
     (cond ((or (endp xs) (endp (cdr xs)) (endp (cddr xs))
                (endp cs) (endp (cdr cs))
                (endp rs) (endp (cdr rs)))
            nil)
           (t (ind (cdr xs) (cdr cs) (cdr rs)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Now we prove the core of the soundness argument for the constraints,
; namely that if the definition of rs expressed by calc-rs holds,
; then saying that the value of xs is less than or equal to the value of cs
; is equivalent to saying that the high bit of rs is 0.

; Since the bits are in big endian order,
; we prove the theorem, by induction,
; in terms of the big-endian value, so the high bit of rs is the car.
; Note that we add the 0 back to cs, so that xs and cs have the same length,
; for the purpose of calculating the big-endian values.
; We use a custom induction schema ind.
; The key property here is acl2::bebits=>nat-of-cons;
; we use a lemma for a version of the induction step with cons,
; then another one for car and cdr
; (which is how the induction step manifests in the proof by induction),
; and those suffice to prove the main claim here.

(defruledl calc-rs-implies-bendian-lte-iff-bit0
  (implies (and (bit-listp xs)
                (bit-listp cs)
                (equal (len xs) (1+ (len cs)))
                (consp cs))
           (b* ((rs (calc-rs xs cs)))
             (iff (<= (bebits=>nat xs)
                      (bebits=>nat (append cs (list 0))))
                  (equal (car rs) 0))))
  :induct (ind xs cs)
  :enable (acl2::bebits=>nat-of-cons
           calc-rs
           bitor
           bitand
           induction-step)
  :prep-books ((include-book "arithmetic/top" :dir :system))

  :prep-lemmas

  ((defun ind (xs cs)
     (cond ((or (endp xs) (endp (cdr xs)) (endp (cddr xs))
                (endp cs) (endp (cdr cs)))
            nil)
           (t (ind (cdr xs) (cdr cs)))))

   (defruled induction-step-with-cons
     (implies (and (bit-listp xs)
                   (bitp x)
                   (bit-listp cs)
                   (bitp c)
                   (equal (len xs) (1+ (len cs)))
                   (b* ((rs (calc-rs xs cs)))
                     (iff (<= (bebits=>nat xs)
                              (bebits=>nat (append cs (list 0))))
                          (equal (car rs) 0))))
              (b* ((rs-cons (calc-rs (cons x xs) (cons c cs))))
                (iff (<= (bebits=>nat (cons x xs))
                         (bebits=>nat (append (cons c cs) (list 0))))
                     (equal (car rs-cons) 0))))
     :do-not-induct t
     :enable (calc-rs
              acl2::bebits=>nat-of-cons
              bitor
              bitand
              bitp-of-car-of-calc-rs-forward)
     :prep-books ((include-book "arithmetic/top" :dir :system)))

   (defruled induction-step
     (implies (and (bit-listp xs)
                   (bit-listp cs)
                   (equal (len xs) (1+ (len cs)))
                   (consp cs)
                   (consp (cdr cs))
                   (b* ((cdr-rs (calc-rs (cdr xs) (cdr cs))))
                     (iff (<= (bebits=>nat (cdr xs))
                              (bebits=>nat (append (cdr cs) (list 0))))
                          (equal (car cdr-rs) 0))))
              (b* ((rs (calc-rs xs cs)))
                (iff (<= (bebits=>nat xs)
                         (bebits=>nat (append cs (list 0))))
                     (equal (car rs) 0))))
     :use (:instance induction-step-with-cons
                     (xs (cdr xs))
                     (x (car xs))
                     (cs (cdr cs))
                     (c (car cs))))))

; We turn that into a little-endian formulation, just by reversing things.
; Since the original (not auxiliary) gadget is in little endian order,
; ultimately we want things expressed in little endian order,
; and thus we will use the following theorem going forward.
; However, the big endian version was the one to prove by induction,
; given that the definition of calc-rs is in big endian order.
; Note that the 0 bit added to cs is now in front.

(defruledl calc-rs-implies-lendian-lte-iff-bit0
  (implies (and (bit-listp xs)
                (bit-listp cs)
                (equal (len xs) (1+ (len cs)))
                (consp cs))
           (b* ((rs (rev (calc-rs (rev xs) (rev cs)))))
             (iff (<= (lebits=>nat xs)
                      (lebits=>nat (cons 0 cs)))
                  (equal (car (last rs)) 0))))
  :enable acl2::lebits=>nat-as-bebits=>nat
  :use ((:instance calc-rs-implies-bendian-lte-iff-bit0
                   (xs (rev xs))
                   (cs (rev cs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; In the theorem proved just above, the little-endian values refer
; to the trimmed xs and cs (with the 0 added to cs).
; But that is not the value of the original (i.e. non-trimmed) xs and cs:
; we have eliminated the low 1 bits of cs, and the same number of bits in xs.
; However, we can "transfer" the inequality from the trimmed to the full bits.

; Consider two sequences of bits xs and ys or equal length.
; Suppose that their big-endian values x and y satisfy x <= y.
; Now we want to add more bits to both xs and ys:
; we add arbitrary bits to xs, but all 1 bits to ys:
;     ...   x(0) x(1) ... x(m-1)
;   1 ... 1 y(0) y(1) ... y(m-1)
; Since the 1s always form a number >= any choice of the extra x bits,
; these two extended numbers satisfy <= iff the original ones do.
; We prove this equivalence below, by proving the two directions.

; The first direction is to add the bits.
; We use an intermediate lemma in which we simply multiply
; the original number by the power of 2
; whose exponent is the number of added bits.
; That is, we "scale" the inequality,
; and since the added x bits are <= the all 1 bits,
; the extended inequality follows.
; A key property used here is bebits=>nat-of-repeat-of-1.

(defruledl bendian-equiv-direction1
  (implies (and (bit-listp xs)
                (bit-listp ys)
                (bit-listp xs2))
           (implies (<= (bebits=>nat xs)
                        (bebits=>nat ys))
                    (<= (bebits=>nat (append xs xs2))
                        (bebits=>nat (append ys (repeat (len xs2) 1))))))
  :enable (acl2::bebits=>nat-of-append
           bebits=>nat-of-repeat-of-1)
  :use (lemma
        (:instance acl2::bebits=>nat-upper-bound (digits xs2)))
  :disable acl2::bebits=>nat-upper-bound
  :prep-books ((include-book "kestrel/arithmetic-light/expt" :dir :system))
  :prep-lemmas
  ((defruled lemma
     (implies (and (bit-listp xs)
                   (bit-listp ys)
                   (bit-listp xs2))
              (implies (<= (bebits=>nat xs)
                           (bebits=>nat ys))
                       (<= (* (bebits=>nat xs)
                              (expt 2 (len xs2)))
                           (* (bebits=>nat ys)
                              (expt 2 (len xs2))))))
     :prep-books ((include-book "arithmetic/top" :dir :system)))))

; The other direction takes a little more work.
; We use a simple lemma saying that the
; we can divide a (strict) inequality by a positive number;
; somehow this did not just come out automatically, in the course of the proofs,
; after trying different arithmetic libraries;
; so we just added this as a simple lemma.
; The second lemma is more interesting,
; showing that, given the scaled and extended inequality,
; we can derive the unscaled inequality.
; This requires a few algebraic manipulations
; that are actually fairly well described by the proof builder command
; that prove them
; If a is xs, b is xs2, c is ys, and 2^n-1 are the extra 1 bits,
; we have this chain of inequalities
;   a * 2^n <= a * 2^n + b <= c * 2^n + 2^n - 1 < c * 2^n + 2^n = (c+1) * 2^n
; where this   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  is the premise,
; from which we derive the strict inequality (at the extremes)
;   a * 2^n < (c+1) * 2^n
; from which we obtain (by dividing by 2^n)
;   a < c+1
; which reduces to
;   a <= c
; since we are dealing with integers.

(defruledl bendian-equiv-direction2
  (implies (and (bit-listp xs)
                (bit-listp ys)
                (bit-listp xs2))
           (implies (<= (bebits=>nat (append xs xs2))
                        (bebits=>nat (append ys (repeat (len xs2) 1))))
                    (<= (bebits=>nat xs)
                        (bebits=>nat ys))))
  :do-not-induct t
  :enable (acl2::bebits=>nat-of-append
           bebits=>nat-of-repeat-of-1)
  :use (:instance lemma2
                  (a (bebits=>nat xs))
                  (b (bebits=>nat xs2))
                  (c (bebits=>nat ys))
                  (p (expt 2 (len xs2))))
  :prep-books ((include-book "kestrel/arithmetic-light/expt" :dir :system))

  :prep-lemmas

  ((defruled lemma1
     (implies (and (natp a)
                   (natp b)
                   (posp p)
                   (< (* a p) (* b p)))
              (< a b))
     :prep-books ((include-book "arithmetic/top" :dir :system)))

   (defruled lemma2
     (implies (and (natp a)
                   (natp b)
                   (natp c)
                   (posp p)
                   (<= (+ (* a p) b)
                       (+ (* c p) (1- p))))
              (<= a c))
     :instructions
     (:pro
      (:claim (<= (* a p) (+ (* a p) b)))
      (:claim (< (+ (* c p) (1- p)) (* (1+ c) p)))
      (:claim (< (* a p) (* (1+ c) p)))
      (:claim (< a (1+ c)) :hints (("Goal" :in-theory (enable lemma1))))
      :prove))))

; Given the two directions above, the equivalence is immediate.

(defruledl bendian-equiv
  (implies (and (bit-listp xs)
                (bit-listp ys)
                (bit-listp xs2))
           (equal (<= (bebits=>nat xs)
                      (bebits=>nat ys))
                  (<= (bebits=>nat (append xs xs2))
                      (bebits=>nat (append ys (repeat (len xs2) 1))))))
  :in-theory nil
  :use (bendian-equiv-direction1 bendian-equiv-direction2))

; We actually need the above theorem for little endian.
; This is easily achieved, by reversing things.

(defruledl lendian-equiv
  (implies (and (bit-listp xs)
                (bit-listp ys)
                (bit-listp xs2))
           (equal (<= (lebits=>nat xs)
                      (lebits=>nat ys))
                  (<= (lebits=>nat (append xs2 xs))
                      (lebits=>nat (append (repeat (len xs2) 1) ys)))))
  :do-not-induct t
  :use (:instance bendian-equiv (xs (rev xs)) (xs2 (rev xs2)) (ys (rev ys)))
  :enable acl2::lebits=>nat-as-bebits=>nat)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We have now most of the theorems necessary to verify the gadget:
; we have that the auxiliary function that defines the gadget
; implies the calculation performed by calc-rs;
; we have that calc-rs implies the equivalence between
; the inequality (trimmed) x <= c and the high r bit being 0;
; and we have that the trimmed inequality can be extended.
; But we need the fact that the extension of c is correct,
; i.e. that the trimming operated by the gadget
; is consistent with the properties of cs used in the theorems proved above.
; The trimming is defined by bits-lte-const-rlen,
; so the following theorems are about it.

; First, the last cs bit before the trimming is 0.

(defruledl nth-for-bits-lte-const-rlen
  (implies (and (bit-listp cs)
                (member-equal 0 cs))
           (b* ((rlen (bits-lte-const-rlen cs))
                (i (- (len cs) (1+ rlen))))
             (equal (nth i cs)
                    0)))
  :enable (bits-lte-const-rlen))

; The skipped-over bits of cs, excluding the 0 bit, are all 1s.

(defruledl take-for-bits-lte-const-rlen
  (implies (and (bit-listp cs)
                (member-equal 0 cs))
           (b* ((rlen (bits-lte-const-rlen cs))
                (i (- (len cs) (1+ rlen))))
             (equal (take i cs)
                    (repeat i 1))))
  :enable (bits-lte-const-rlen repeat))

; The index of the 0 bit is in the range of the length.

(defruledl index-for-bits-lte-const-rlen
  (implies (and (bit-listp cs)
                (member-equal 0 cs))
           (b* ((rlen (bits-lte-const-rlen cs))
                (i (- (len cs) (1+ rlen))))
             (and (natp i)
                  (< i (len cs)))))
  :enable bits-lte-const-rlen)

; This is a variant of a library theorem that says that
; a list can be decomposed into take and nthcdr.
; Our variant decomposed the list into take, nth, and nthcdr;
; this is because the nth will be for the 0 bit in cs.

(defruledl append-of-take-and-nth-and-nthcdr
  (implies (and (true-listp l)
                (natp i)
                (< i (len l)))
           (equal (append (take i l)
                          (list (nth i l))
                          (nthcdr (1+ i) l))
                  l))
  :enable (take nth nthcdr))

; Here we specialize the lemma above to hold under the assumptions on cs.

(defruledl append-of-take-and-nth-and-nthcdr-for-cs
  (implies (and (bit-listp cs)
                (member-equal 0 cs))
           (b* ((rlen (bits-lte-const-rlen cs))
                (i (- (len cs) (1+ rlen))))
             (equal (append (take i cs)
                            (list (nth i cs))
                            (nthcdr (1+ i) cs))
                    cs)))
  :do-not-induct t
  :use (index-for-bits-lte-const-rlen
        (:instance append-of-take-and-nth-and-nthcdr
                   (l cs)
                   (i (- (len cs) (1+ (bits-lte-const-rlen cs)))))))

; This is the final decomposition theorem of cs,
; specialized to the initial bits being 1 and the next bit being 0.

(defruledl cs-decomposition
  (implies (and (bit-listp cs)
                (member-equal 0 cs))
           (b* ((rlen (bits-lte-const-rlen cs))
                (i (- (len cs) (1+ rlen))))
             (equal (append (repeat i 1)
                            (list 0)
                            (nthcdr (1+ i) cs))
                    cs)))
  :use (nth-for-bits-lte-const-rlen
        take-for-bits-lte-const-rlen
        append-of-take-and-nth-and-nthcdr-for-cs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Now we finally putting everything together.
; While conceptually this is not difficult,
; there are a few key steps that are best highlighted as separate theorems;
; putting them all together also makes the proof more fragile.

; As a first step, we show that the (full) gadget
; implies that the relevant bits are related according to calc-rs.
; We expand bits-lte-const-gadget, exposing bits-lte-const-gadget-aux,
; and we use the theorem that it implies calc-rs;
; note that we have the rev applications.

(defruledl soundness-lemma1
  (implies
   (and (symbol-listp xs)
        (bit-listp cs)
        (symbol-listp rs)
        (equal (len xs) (len cs))
        (equal (len rs) (bits-lte-const-rlen cs))
        (primep p)
        (member-equal 0 cs)
        (equal (car (last cs)) 1)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-binds-allp asg xs)
        (r1cs::valuation-binds-allp asg rs))
   (b* ((xs$ (lookup-equal-list xs asg))
        (rs$ (lookup-equal-list rs asg)))
     (implies (bit-listp xs$)
              (implies
               (r1cs::r1cs-constraints-holdp
                (bits-lte-const-gadget xs cs rs p) asg p)
               (equal rs$
                      (rev
                       (calc-rs
                        (lookup-equal-list
                         (rev
                          (nthcdr (- (len cs) (1+ (bits-lte-const-rlen cs)))
                                  xs))
                         asg)
                        (rev
                         (nthcdr (- (len cs) (bits-lte-const-rlen cs))
                                 cs)))))))))
  :do-not-induct t
  :enable (bits-lte-const-gadget
           lookup-equal-list-of-rev
           lookup-equal-list-of-nthcdr)
  :use (:instance
        bits-lte-gadget-aux-implies-calc-rs
        (xs (rev (nthcdr (- (len xs) (1+ (bits-lte-const-rlen cs))) xs)))
        (cs (rev (nthcdr (- (len cs) (bits-lte-const-rlen cs)) cs)))
        (rs (rev rs))))

; As a second step, given the same bits-lte-const-gadget premise,
; we use the previous lemma to obtain its conclusion right away,
; and then we instantiate calc-rs-implies-lendian-lte-iff-bit0
; with the suitably trimmed bit sequences,
; to obtain the equivalence about the inequality,
; but for the trimmed bits for now.

(defruledl soundness-lemma2
  (implies
   (and (symbol-listp xs)
        (bit-listp cs)
        (symbol-listp rs)
        (equal (len xs) (len cs))
        (equal (len rs) (bits-lte-const-rlen cs))
        (primep p)
        (member-equal 0 cs)
        (equal (car (last cs)) 1)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-binds-allp asg xs)
        (r1cs::valuation-binds-allp asg rs))
   (b* ((xs$ (lookup-equal-list xs asg))
        (rs$ (lookup-equal-list rs asg)))
     (implies (bit-listp xs$)
              (implies
               (r1cs::r1cs-constraints-holdp
                (bits-lte-const-gadget xs cs rs p) asg p)
               (iff (<= (lebits=>nat
                         (nthcdr (- (len cs) (1+ (bits-lte-const-rlen cs)))
                                 xs$))
                        (lebits=>nat
                         (cons 0
                               (nthcdr (- (len cs) (bits-lte-const-rlen cs))
                                       cs))))
                    (equal (car (last rs$)) 0))))))
  :do-not-induct t
  :enable (lookup-equal-list-of-nthcdr
           lookup-equal-list-of-rev)
  :use (soundness-lemma1
        (:instance
         calc-rs-implies-lendian-lte-iff-bit0
         (xs (lookup-equal-list
              (nthcdr (- (len cs) (1+ (bits-lte-const-rlen cs)))
                      xs)
              asg))
         (cs (nthcdr (- (len cs) (bits-lte-const-rlen cs))
                     cs)))))

; We conclude things, again starting from the same premise,
; using the previous lemma to obtain the equivalence about the inequality,
; and then we use the little endian "scaling" equivalence
; to effectively replace the inequality on the trimmed bits
; with the inequality on all the bits, which is what we want.
; We need to use cs-decomposition to show that cs
; is the same as the extension of its trimmed version.
; The disabling of the library rule acl2::equal-of-append-repeat
; is necessary, otherwise it sabotages the decomposition of cs.

(defruled bits-lte-const-soundness
  (implies
   (and (symbol-listp xs)
        (bit-listp cs)
        (symbol-listp rs)
        (equal (len xs) (len cs))
        (equal (len rs) (bits-lte-const-rlen cs))
        (primep p)
        (member-equal 0 cs)
        (equal (car (last cs)) 1)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-binds-allp asg xs)
        (r1cs::valuation-binds-allp asg rs))
   (b* ((xs$ (lookup-equal-list xs asg))
        (rs$ (lookup-equal-list rs asg)))
     (implies (bit-listp xs$)
              (implies
               (r1cs::r1cs-constraints-holdp
                (bits-lte-const-gadget xs cs rs p) asg p)
               (iff (<= (lebits=>nat xs$)
                        (lebits=>nat cs))
                    (equal (car (last rs$)) 0))))))
  :do-not-induct t
  :enable (lookup-equal-list-of-nthcdr
           lookup-equal-list-of-take)
  :disable acl2::equal-of-append-repeat
  :use (soundness-lemma2
        (:instance lendian-equiv
                   (xs (lookup-equal-list
                        (nthcdr (- (len cs) (1+ (bits-lte-const-rlen cs)))
                                xs)
                        asg))
                   (xs2 (lookup-equal-list
                         (take (- (len cs) (1+ (bits-lte-const-rlen cs)))
                               xs)
                         asg))
                   (ys (cons 0
                             (nthcdr (- (len cs) (bits-lte-const-rlen cs))
                                     cs))))
        cs-decomposition))
