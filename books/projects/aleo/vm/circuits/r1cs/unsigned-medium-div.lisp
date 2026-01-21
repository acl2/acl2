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

(include-book "boolean-check")
(include-book "unsigned-medium-mul-checked")
(include-book "unsigned-small-add-checked")
(include-book "unsigned-small-lt")
(include-book "zero")

(local (include-book "../library-extensions/arithmetic"))

(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (in-theory (disable integer-length)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is a 'medium' version of the unsigned-small-div gadget.
; It declaratively constrains quotient and reminder
; to satisfy the Euclidean property.

(define unsigned-medium-div-gadget ((xs symbol-listp)
                                    (ys symbol-listp)
                                    (qs symbol-listp)
                                    (rs symbol-listp)
                                    (low-low symbolp)
                                    (high-low symbolp)
                                    (low-high symbolp)
                                    (high-high symbolp)
                                    (ms symbol-listp)
                                    (ms-carry-low symbol-listp)
                                    (ms-carry-high symbol-listp)
                                    (ls symbol-listp)
                                    (l symbolp)
                                    (ds symbol-listp)
                                    (d symbolp)
                                    (one symbolp)
                                    (p primep))
  :guard (and (< 0 (len xs))
              (equal (len ys) (len xs))
              (equal (len qs) (len xs))
              (equal (len rs) (len xs))
              (equal (len ms) (len xs))
              (equal (len ms-carry-low) (1+ (floor (len xs) 2)))
              (equal (len ms-carry-high) (len xs))
              (equal (len ls) (len xs))
              (equal (len ds) (len xs))
              (< (len (append ms ms-carry-low)) (integer-length p)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (append
   (boolean-check-gadget-list qs p)
   (boolean-check-gadget-list rs p)
   (unsigned-medium-mul-checked-gadget
    qs ys low-low high-low low-high high-high ms ms-carry-low ms-carry-high p)
   (unsigned-small-add-checked-gadget ms rs ls l p)
   (list (r1cs::make-r1cs-constraint
          :a (pow2sum-vector xs 0)
          :b (list (list 1 1))
          :c (pow2sum-vector ls 0)))
   (unsigned-small-lt-gadget rs ys ds d p)
   (zero-unit-gadget d one p)))

; We need this lemma to get rid of a (mod ... p) in the theorem below
; about Euclidean division for this gadget.
; This probably belongs to a more general library.

(defruledl pow2sum-fits
  (implies (and (posp p)
                (bit-listp bits)
                (< (len bits) (integer-length p)))
           (< (lebits=>nat bits)
              p))
  :rule-classes :linear
  :do-not-induct t
  :use ((:instance expt2-mono
                   (a (len bits))
                   (b (1- (integer-length p)))))
  :enable positive->=-expt2-of-integer-length-minus-1)

; We first prove that the gadget satisfies the Euclidean property.

(defruled unsigned-medium-div-gadget-euclidian
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp qs)
                (symbol-listp rs)
                (symbolp low-low)
                (symbolp high-low)
                (symbolp low-high)
                (symbolp high-high)
                (symbol-listp ms)
                (symbol-listp ms-carry-low)
                (symbol-listp ms-carry-high)
                (symbol-listp ls)
                (symbolp l)
                (symbol-listp ds)
                (symbolp d)
                (symbolp one)
                (< 0 (len xs))
                (evenp (len xs))
                (equal (len ys) (len xs))
                (equal (len qs) (len xs))
                (equal (len rs) (len xs))
                (equal (len ms) (len xs))
                (equal (len ms-carry-low) (1+ (floor (len xs) 2)))
                (equal (len ms-carry-high) (len xs))
                (equal (len ls) (len xs))
                (equal (len ds) (len xs))
                (< (len (append ms ms-carry-low)) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg qs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg low-low)
                (r1cs::valuation-bindsp asg high-low)
                (r1cs::valuation-bindsp asg low-high)
                (r1cs::valuation-bindsp asg high-high)
                (r1cs::valuation-binds-allp asg ms)
                (r1cs::valuation-binds-allp asg ms-carry-low)
                (r1cs::valuation-binds-allp asg ms-carry-high)
                (r1cs::valuation-binds-allp asg ls)
                (r1cs::valuation-bindsp asg l)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-bindsp asg d)
                (r1cs::valuation-bindsp asg one))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (qs$ (lookup-equal-list qs asg))
                (rs$ (lookup-equal-list rs asg))
                (one$ (lookup-equal one asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$)
                           (equal one$ 1))
                      (implies (r1cs::r1cs-constraints-holdp
                                (unsigned-medium-div-gadget
                                 xs ys qs rs
                                 low-low high-low low-high high-high
                                 ms ms-carry-low ms-carry-high
                                 ls l ds d one p)
                                asg
                                p)
                               (and (bit-listp qs$)
                                    (bit-listp rs$)
                                    (not (equal (lebits=>nat ys$) 0))
                                    (equal (lebits=>nat xs$)
                                           (+ (* (lebits=>nat qs$)
                                                 (lebits=>nat ys$))
                                              (lebits=>nat rs$)))
                                    (< (lebits=>nat rs$)
                                       (lebits=>nat ys$)))))))
  :do-not-induct t
  :enable (unsigned-medium-div-gadget
           boolean-check-gadget-list-to-bit-listp
           unsigned-small-add-checked-gadget-correct
           zero-unit-gadget-to-equal-0
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product
           pow2sum-vector-to-mod-of-lebits=>nat
           pow2sum-fits)
  :disable evenp
  :use ((:instance unsigned-medium-mul-checked-gadget-soundness
                   (xs qs)
                   (zs ms)
                   (zs-carry-low ms-carry-low)
                   (zs-carry-high ms-carry-high))
        (:instance unsigned-small-lt-gadget-soundness
                   (xs rs) (ys ys) (zs ds) (z d))))

; Then we use the Euclidean property to show that
; quotient and reminder are indeed quotient and reminder.

(defruled unsigned-medium-div-opt-gadget-soundness
  (implies (and (primep p)
                (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp qs)
                (symbol-listp rs)
                (symbolp low-low)
                (symbolp high-low)
                (symbolp low-high)
                (symbolp high-high)
                (symbol-listp ms)
                (symbol-listp ms-carry-low)
                (symbol-listp ms-carry-high)
                (symbol-listp ls)
                (symbolp l)
                (symbol-listp ds)
                (symbolp d)
                (symbolp one)
                (< 0 (len xs))
                (evenp (len xs))
                (equal (len ys) (len xs))
                (equal (len qs) (len xs))
                (equal (len rs) (len xs))
                (equal (len ms) (len xs))
                (equal (len ms-carry-low) (1+ (floor (len xs) 2)))
                (equal (len ms-carry-high) (len xs))
                (equal (len ls) (len xs))
                (equal (len ds) (len xs))
                (< (len (append ms ms-carry-low)) (integer-length p))
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg qs)
                (r1cs::valuation-binds-allp asg rs)
                (r1cs::valuation-bindsp asg low-low)
                (r1cs::valuation-bindsp asg high-low)
                (r1cs::valuation-bindsp asg low-high)
                (r1cs::valuation-bindsp asg high-high)
                (r1cs::valuation-binds-allp asg ms)
                (r1cs::valuation-binds-allp asg ms-carry-low)
                (r1cs::valuation-binds-allp asg ms-carry-high)
                (r1cs::valuation-binds-allp asg ls)
                (r1cs::valuation-bindsp asg l)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-bindsp asg d)
                (r1cs::valuation-bindsp asg one))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (qs$ (lookup-equal-list qs asg))
                (rs$ (lookup-equal-list rs asg))
                (one$ (lookup-equal one asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$)
                           (equal one$ 1))
                      (implies (r1cs::r1cs-constraints-holdp
                                (unsigned-medium-div-gadget
                                 xs ys qs rs
                                 low-low high-low low-high high-high
                                 ms ms-carry-low ms-carry-high
                                 ls l ds d one p)
                                asg
                                p)
                               (and
                                (equal (lebits=>nat qs$)
                                       (truncate (lebits=>nat xs$)
                                                 (lebits=>nat ys$)))
                                (equal (lebits=>nat rs$)
                                       (rem (lebits=>nat xs$)
                                            (lebits=>nat ys$))))))))
  :do-not-induct t
  :use (unsigned-medium-div-gadget-euclidian
        (:instance truncate-when-euclidian
                   (x (lebits=>nat (lookup-equal-list xs asg)))
                   (y (lebits=>nat (lookup-equal-list ys asg)))
                   (q (lebits=>nat (lookup-equal-list qs asg)))
                   (r (lebits=>nat (lookup-equal-list rs asg))))
        (:instance rem-when-euclidian
                   (x (lebits=>nat (lookup-equal-list xs asg)))
                   (y (lebits=>nat (lookup-equal-list ys asg)))
                   (q (lebits=>nat (lookup-equal-list qs asg)))
                   (r (lebits=>nat (lookup-equal-list rs asg)))))
  :disable (truncate rem))
