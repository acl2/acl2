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

(include-book "bits-lte-const")
(include-book "zero")

(local (include-book "../library-extensions/digits"))
(local (include-book "../library-extensions/r1cses"))

(local (include-book "arithmetic/top" :dir :system))
(local (include-book "std/lists/last" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is a bitwise less-than-or-equal-to comparison gadget,
; between a variable value and a known constant value.
; It generalizes bit-lte-const (see that gadget)
; by not requiring the cs bits to include a 0.
; However, while bit-lte-const calculates the result of the comparison,
; this gadget enforces the comparison,
; i.e. the gadget is satisfied iff the comparison holds.
; We should also add a gadget that is similar to this one
; but instead returns the result of the comparison at some point.

; In this gadget, we only assume that the high bit of cs is 1.
; This is straightforward to satisfy,
; as cs typically derives from decomposing a natural number into bits:
; one can simply pick the minimal-length bits.
; As a degenerate case, we also allow cs to be empty:
; this happens when the natural number is 0 and we pick the minimal bits.
; In this case the gadget reduces to checking that every xs bit is 0, see below.

; The gadget works as follows.
; First, if cs has strictly more bits than xs,
; the comparison must hold, and no constraints are generated;
; the reason is that the high bit is 1 by assumption,
; and so the value of xs has to be less than the value of cs.

; Otherwise, xs may or may not have more bits than cs.
; In order for the comparison to hold, any excess bit must be 0:
; thus, we add one zero gadget for each excess bits (possibly none),
; forcing the excess bits to be 0.
; Note that if cs has no bits then the zero gadgets apply to all bits of xs,
; i.e. we check that the value of xs is 0, the only value that is <= 0 in fact.

; Whether there are excess bits or not,
; the zero gadgets mentioned above
; reduce the comparison to the lower bits of cs,
; equal in number to the bits of cs.
; If all the bits of cs are 1, i.e. there is no 0,
; then we know that the comparison holds,
; and no further constraint is needed.
; If instead cs has at least one 0 bits,
; in which case cs is not empty, and thus its high bit is 1,
; the preconditions of the bits-lte-const gadget are satisfied,
; and we use it to calculate the comparison, in the last bit of rs,
; which we constrain to be 0 via the zero gadget.

(define bits-lte-const-check-rlen ((cs bit-listp))
  :guard (or (endp cs)
             (equal (car (last cs)) 1))
  :returns (rlen natp)
  (if (member-equal 0 cs)
      (bits-lte-const-rlen cs)
    0))

(define bits-lte-const-check-gadget ((xs symbol-listp)
                                     (cs bit-listp)
                                     (rs symbol-listp)
                                     (p primep))
  :guard (and (or (endp cs)
                  (equal (car (last cs)) 1))
              (equal (len rs)
                     (bits-lte-const-check-rlen cs)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (if (< (len xs) (len cs))
      nil
    (append (zero-gadget-list (nthcdr (len cs) xs))
            (if (member-equal 0 cs)
                (append
                 (bits-lte-const-gadget (take (len cs) xs) cs rs p)
                 (zero-gadget (car (last rs))))
              nil)))
  :prepwork ((local (in-theory (enable bits-lte-const-check-rlen)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We prove soundess for the case in which cs has more bits than xs.
; This means that cs cannot be empty, and since we assume its high bit to be 1,
; the value of cs is ... + 2^n, where n is the length of cs minus 1.
; We know that the value of xs is less than 2^m, where m is the length of xs.
; Since there are more bits in cs than xs, n >= m,
; and thus 2^n >= 2^m, and therefore the comparison holds.

; First, we explicate the decomposition of cs into
; the low bits (all but the last) and the high bit (the last).
; This is actually a general list theorem, which could go into the list library.

(defruledl cs-decompsition
  (implies (and (true-listp cs)
                (consp cs))
           (equal (append (butlast cs 1)
                          (last cs))
                  cs)))

; The length of all the bits except the last is one less than total length.
; This is actually a general list theorem, which could go into the list library.

(defruledl len-of-butlast-1
  (implies (and (true-listp cs)
                (consp cs))
           (equal (len (butlast cs 1))
                  (1- (len cs)))))

; We decompose the value of cs to explicate the 2^n mentioned above,
; using the above three theorems.

(defruledl cs-value-decomposition
  (implies (and (bit-listp cs)
                (consp cs)
                (equal (car (last cs)) 1))
           (equal (lebits=>nat cs)
                  (+ (lebits=>nat (butlast cs 1))
                     (expt 2 (1- (len cs))))))
  :enable (cs-decompsition
           lebits=>nat-of-last
           len-of-butlast-1)
  :use (:instance acl2::lebits=>nat-of-append
                  (lodigits (butlast cs 1))
                  (hidigits (last cs)))
  :disable (last butlast))

; Using the decomposition of the cs value,
; we can show that the inequality holds.
; We need a lemma about the monotonicity of expt,
; and we need to disable an arithmetic rule that interferes with that.
; (Attempting to prove the following theorem without the lemma fails.)

(defruledl inequality
  (implies (and (bit-listp cs)
                (consp cs)
                (equal (car (last cs)) 1)
                (< (len xs) (len cs)))
           (<= (lebits=>nat xs)
               (lebits=>nat cs)))
  :use (cs-value-decomposition
        monotonicity)
  :disable acl2::expt-is-weakly-increasing-for-base>1
  :prep-lemmas
  ((defruled monotonicity
     (implies (and (consp cs)
                   (< (len xs) (len cs)))
              (<= (expt 2 (len xs))
                  (expt 2 (1- (len cs))))))))

; The inequality above lets us prove soundness
; for this case of cs having more bits than xs.

(defruledl soundness-case1
  (implies
   (< (len xs) (len cs))
   (implies
    (and (bit-listp cs)
         (or (endp cs)
             (equal (car (last cs)) 1)))
    (b* ((xs$ (lookup-equal-list xs asg)))
      (implies (bit-listp xs$)
               (<= (lebits=>nat xs$)
                   (lebits=>nat cs))))))
  :enable inequality)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Now we switch to the case in which xs has at least as many bits as cs,
; i.e. the negation of the case proved just above.
; This splits into two sub-cases, but there is some commonality.
; In particular, because the zero gadgets force the excess bits of xs to be 0,
; we have that the value of xs is the value of its low bits,
; in number that equals the number of bits of cs.

; The following theorem captures this in a more general form,
; where, in later theorems, xs will be in fact the low bits of xs,
; and where the repeated 0s will be the excess bits of xs.

(defruledl remove-high-zeros
  (implies (bit-listp xs)
           (equal (lebits=>nat (append xs (repeat l 0)))
                  (lebits=>nat xs)))
  :use (:instance acl2::lebits=>nat-of-append
                  (lodigits xs)
                  (hidigits (repeat l 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Now we consider the (sub-)case in which cs has no 0 bits,
; i.e. it has all 1 bits, including the case of no bits at all,
; which still falls under this case.

; If cs has no 0 bits, we can reformulate as a repetition of 1.

(defruledl cs-reformulation
  (implies (and (bit-listp cs)
                (not (member-equal 0 cs)))
           (equal (repeat (len cs) 1)
                  cs))
  :enable repeat)

; Because of the above reformulation, its value is 2^n-1,
; where n is its length.

(defruledl value-of-cs
  (implies (and (bit-listp cs)
                (not (member-equal 0 cs)))
           (equal (lebits=>nat cs)
                  (1- (expt 2 (len cs)))))
  :use cs-reformulation
  :enable lebits=>nat-of-repeat-of-1)

; Using the fact just proved,
; and the fact that the high 0 bits of xs have value 0 proved earlier,
; and decomposing xs into the non-excess and excess bits
; via the library theorem acl2::append-of-take-and-nthcdr,
; we prove soundness for this case.
; One key rule, which fires automatically,
; is that lebits=>nat is less than 2^n,
; where n is the length of cs here,
; which is also the length of the non-excess bits of xs.

(defruledl soundness-case2
  (implies
   (and (>= (len xs) (len cs))
        (not (member-equal 0 cs)))
   (implies
    (and (symbol-listp xs)
         (bit-listp cs)
         (or (endp cs)
             (equal (car (last cs)) 1))
         (primep p)
         (r1cs::r1cs-valuationp asg p)
         (r1cs::valuation-binds-allp asg xs))
    (b* ((xs$ (lookup-equal-list xs asg)))
      (implies (bit-listp xs$)
               (implies
                (r1cs::r1cs-constraints-holdp
                 (bits-lte-const-check-gadget xs cs rs p) asg p)
                (<= (lebits=>nat xs$)
                    (lebits=>nat cs)))))))
  :do-not-induct t
  :enable (bits-lte-const-check-gadget
           zero-gadget-list-to-all-equal-0
           lookup-equal-list-of-nthcdr
           value-of-cs
           remove-high-zeros)
  :disable acl2::append-of-take-and-nthcdr
  :use ((:instance acl2::append-of-take-and-nthcdr
                   (x (lookup-equal-list xs asg))
                   (n (len cs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Finally, we consider the (sub-)case in which cs has at least one 0 bit.
; Here we use the soundness theorem of bits-lte-const,
; as well as the remove-high-zeros theorem from earlier
; (which is still needed to remove the excess bits of xs from consideration).
; Note that enable zero-gadget-to-equal-0 to enforce that
; the last rs bit is 0, i.e. that the comparison succeeds.

(defruledl soundness-case3
  (implies
   (and (>= (len xs) (len cs))
        (member-equal 0 cs))
   (implies
    (and (symbol-listp xs)
         (bit-listp cs)
         (or (endp cs)
             (equal (car (last cs)) 1))
         (symbol-listp rs)
         (equal (len rs) (bits-lte-const-rlen cs))
         (primep p)
         (r1cs::r1cs-valuationp asg p)
         (r1cs::valuation-binds-allp asg xs)
         (r1cs::valuation-binds-allp asg rs))
    (b* ((xs$ (lookup-equal-list xs asg)))
      (implies (bit-listp xs$)
               (implies
                (r1cs::r1cs-constraints-holdp
                 (bits-lte-const-check-gadget xs cs rs p) asg p)
                (<= (lebits=>nat xs$)
                    (lebits=>nat cs)))))))
  :do-not-induct t
  :enable (bits-lte-const-check-gadget
           zero-gadget-list-to-all-equal-0
           zero-gadget-to-equal-0
           lookup-equal-list-of-nthcdr
           remove-high-zeros
           last-of-lookup-equal-list
           car-of-lookup-equal-list)
  :use ((:instance acl2::append-of-take-and-nthcdr
                   (x (lookup-equal-list xs asg))
                   (n (len cs)))
        (:instance bits-lte-const-soundness
                   (xs (take (len cs) xs)))
        (:instance lookup-equal-list-of-take
                   (i (len cs))
                   (keys xs)
                   (alist asg)))
  :disable acl2::append-of-take-and-nthcdr
  :cases ((consp rs)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The soundness theorem for the gadget
; is proved from the ones for the cases above.

(defruled bits-lte-const-check-soundness
  (implies
   (and (symbol-listp xs)
        (bit-listp cs)
        (or (endp cs)
            (equal (car (last cs)) 1))
        (symbol-listp rs)
        (equal (len rs)
               (bits-lte-const-check-rlen cs))
        (primep p)
        (r1cs::r1cs-valuationp asg p)
        (r1cs::valuation-binds-allp asg xs)
        (r1cs::valuation-binds-allp asg rs))
   (b* ((xs$ (lookup-equal-list xs asg)))
     (implies (bit-listp xs$)
              (implies
               (r1cs::r1cs-constraints-holdp
                (bits-lte-const-check-gadget xs cs rs p) asg p)
               (<= (lebits=>nat xs$)
                   (lebits=>nat cs))))))
  :use (bits-lte-const-check-rlen
        soundness-case1
        soundness-case2
        soundness-case3))
