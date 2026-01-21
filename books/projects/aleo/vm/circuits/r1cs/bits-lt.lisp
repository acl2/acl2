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

(include-book "boolean-xor")
(include-book "if")

(include-book "../library-extensions/digits")

(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "projects/pfcs/r1cs-lib-ext" :dir :system))
(local (include-book "std/lists/last" :dir :system))
(local (include-book "std/lists/len" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is a bitwise less-than comparison gadget.
; Given lists of (boolean) values xs and ys, in equal number,
; the gadget checks whether x < y,
; where x = x0 + 2x1 + 4x2 + ...
; and y = y0 + 2y1 + 4y2 + ...
; That is, xs and ys are assumed to be the bits of two numbers x and y,
; which are not at all constrained to be below the prime:
; they could even consist of many more bits than the prime,
; and still this gadget correctly checks whether x < y or not.
; Note that the gadget only involves operations on booleans;
; it does not involve any powers-of-two weighted sums in the constraints,
; i.e. x and y are not variables in the gadget,
; just x0, x1, ... and y0, y1, ... are.

; The gadget calculates the ds values as follows:
;   di = xi XOR yi
; Then it calculates the rs values recursively as follows:
;   r0 = IF d0 THEN y0 ELSE 0
;   ri = IF di THEN yi ELSE ri-1
; The constraints for the di's and ri's are interleaved:
; - constraint for d0
; - constraint for r0
; - constraint for d1
; - constraint for r1
; - etc.
; The constraints for the di's are exclusive disjunction gadgets.
; The constraint for r0 is the specialized conditional gadget;
; the constraints for r1, r2, etc. are conditional gadgets.

; The variables in xs and ys (and ds and rs)
; are organized in little-endian order,
; i.e. from least to most significant.
; Since the recursive construction
; is more naturally expressed in big-endian order,
; we use an auxiilary recursive function.
; The list of constraints that results from the auxiliary recursive function is:
; - constraint for rn-1
; - constraint for dn-1
; ...
; - constraint for r0
; - constraint for d0
; So we reverse that list to obtain the right order, given earlier above.

(define bits-lt-gadget ((xs symbol-listp)
                        (ys symbol-listp)
                        (ds symbol-listp)
                        (rs symbol-listp)
                        (p primep))
  :guard (and (equal (len xs) (len ys))
              (equal (len ys) (len ds))
              (equal (len ds) (len rs)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (rev (bits-lt-gadget-aux (rev xs) (rev ys) (rev ds) (rev rs) p))
  :prepwork
  ((define bits-lt-gadget-aux ((xs symbol-listp)
                               (ys symbol-listp)
                               (ds symbol-listp)
                               (rs symbol-listp)
                               (p primep))
     :guard (and (equal (len xs) (len ys))
                 (equal (len ys) (len ds))
                 (equal (len ds) (len rs)))
     :returns (constr r1cs::r1cs-constraint-listp :hyp :guard)
     (cond
      ((endp xs) nil)
      ((endp (cdr xs)) (append
                        (if0-gadget (car ds) (car ys) (car rs))
                        (boolean-xor-gadget (car xs) (car ys) (car ds) p)))
      (t (append (if-gadget-variant (car ds) (car ys) (cadr rs) (car rs) p)
                 (boolean-xor-gadget (car xs) (car ys) (car ds) p)
                 (bits-lt-gadget-aux (cdr xs)
                                     (cdr ys)
                                     (cdr ds)
                                     (cdr rs)
                                     p)))))))

; In order to prove the correctness of the gadget,
; it is convenient to introduce a function that expresses
; the recursive definition of rs sketched above.
; This recursive definition is in big-endian order,
; i.e. it corresponds to the auxiliary recursive function
; used in the definition of the gadget above.

(local
 (define bits-lt-r ((ds bit-listp) (ys bit-listp))
   :guard (equal (len ys) (len ds))
   :returns rs ; type proved below
   (cond ((endp ds) nil)
         ((endp (cdr ds)) (list (if (equal (car ds) 1)
                                    (car ys)
                                  0)))
         (t (b* ((cdr-rs (bits-lt-r (cdr ds) (cdr ys))))
              (cons (if (equal (car ds) 1)
                        (car ys)
                      (car cdr-rs))
                    cdr-rs))))
   ///
   (defret len-of-bits-lt-r
     (equal (len rs) (len ds)))
   (defret consp-of-bits-lt-r
     (equal (consp rs)
            (consp ds)))
   (more-returns
    (rs bit-listp
        :hyp (and (bit-listp ys)
                  (equal (len ys) (len ds)))))))

; First, we relate the big-endian version of the gadget
; to a shallowly embedded characterization
; that is in terms of BITXOR-LIST and BITS-LT-R.

(defruledl bits-lt-gadget-aux-to-bitxor+bitslt
  (implies (and (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp ds)
                (symbol-listp rs)
                (equal (len xs) (len ys))
                (equal (len ys) (len ds))
                (equal (len ds) (len rs))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-binds-allp asg rs))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (ds$ (lookup-equal-list ds asg))
                (rs$ (lookup-equal-list rs asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$))
                      (implies (r1cs::r1cs-constraints-holdp
                                (bits-lt-gadget-aux xs ys ds rs p) asg p)
                               (and (equal ds$ (bitxor-list xs$ ys$))
                                    (equal rs$ (bits-lt-r ds$ ys$)))))))
  :induct (ind xs ys ds rs)
  :enable (bits-lt-gadget-aux
           boolean-xor-gadget-to-bitxor
           if0-gadget-to-if0
           if-gadget-variant-to-if
           bits-lt-r
           bitxor-list
           if0
           lookup-equal-list)
  :disable (;; for speed:
            bitp
            default-car
            default-cdr
            acl2::len-when-atom
            acl2::len-when-not-consp-cheap
            acl2::consp-when-len-equal-constant
            append
            acl2::append-when-not-consp
            acl2::bitp-when-member-equal-of-bit-listp
            default-+-2
            default-+-1
            acl2::bit-listp-when-subsetp-equal
            acl2::consp-when-len-greater
            acl2::subsetp-when-atom-right
            acl2::subsetp-when-atom-left
            acl2::bit-listp-when-not-consp
            acl2::subsetp-member
            acl2::lookup-equal-when-not-consp-cheap
            acl2::consp-of-cdr-when-len-known
            default-<-1
            default-<-2
            acl2::lookup-equal-when-not-consp-cheap
            acl2::lookup-equal-when-not-assoc-equal-cheap
            acl2::subsetp-trans
            acl2::subsetp-trans2
            acl2::subsetp-of-cons
            acl2::not-primep-when-divides
            acl2::member-of-car
            (:t boolean-xor-gadget)
            (:t if-gadget-variant)
            cons-equal)
  :prep-lemmas
  ((defun ind (xs ys ds rs)
     (cond ((or (endp xs)
                (endp ys)
                (endp ds)
                (endp rs))
            nil)
           ((or (endp (cdr xs))
                (endp (cdr ys))
                (endp (cdr ds))
                (endp (cdr rs)))
            nil)
           (t (ind (cdr xs) (cdr ys) (cdr ds) (cdr rs)))))))

; The core reason why the gadget works is proved now,
; using BITXOR-LIST and BITS-LT-R, i.e. the shallow embedding of the gadget.
; It is the case that
;   (x0 + 2x1 + ... + (2^i)xi) < (y0 + 2y1 + ... + (2^i)yi)
;     <==>
;   ri = 1
; which can be proved by induction.
; Thus, x < y <==> rn-1 = 1.

; For this proof by induction on lists,
; it is more convenient to reverse the bits.
; Thus, in the theorem below, xs and ys are in big-endian order,
; and ds and rs follow the same order.
; This way, the most significant bit is the CAR,
; and the remaining bits, for which we have the inductive hypothesis,
; are the CDR.

(defruledl bitxor+bitslt-to-<-bendian-iff-bit1
  (implies (and (bit-listp xs)
                (bit-listp ys)
                (equal (len xs) (len ys))
                (consp xs))
           (b* ((ds (bitxor-list xs ys))
                (rs (bits-lt-r ds ys)))
             (iff (< (bebits=>nat xs)
                     (bebits=>nat ys))
                  (equal (car rs) 1))))
  :induct (ind xs ys)
  :enable (len-lemma
           induction-step)

  :prep-lemmas

  ((defun ind (xs ys)
     (cond ((or (endp xs) (endp ys)) nil)
           ((or (endp (cdr xs)) (endp (cdr ys))) nil)
           (t (ind (cdr xs) (cdr ys)))))

   (defruled induction-step-with-cons
     (implies (and (bit-listp xs)
                   (bit-listp ys)
                   (equal (len xs) (len ys))
                   (consp xs)
                   (consp ys)
                   (bitp a)
                   (bitp b)
                   (b* ((ds (bitxor-list xs ys))
                        (rs (bits-lt-r ds ys)))
                     (iff (< (bebits=>nat xs)
                             (bebits=>nat ys))
                          (equal (car rs) 1))))
              (b* ((ds-cons (bitxor-list (cons a xs) (cons b ys)))
                   (rs-cons (bits-lt-r ds-cons (cons b ys))))
                (iff (< (bebits=>nat (cons a xs))
                        (bebits=>nat (cons b ys)))
                     (equal (car rs-cons) 1))))
     :enable (bitxor-list
              bits-lt-r
              acl2::bebits=>nat-of-cons))

   (defruled induction-step
     (implies (and (bit-listp xs)
                   (bit-listp ys)
                   (equal (len xs) (len ys))
                   (consp xs)
                   (consp ys)
                   (consp (cdr xs))
                   (consp (cdr ys))
                   (b* ((cdr-ds (bitxor-list (cdr xs) (cdr ys)))
                        (cdr-rs (bits-lt-r cdr-ds (cdr ys))))
                     (iff (< (bebits=>nat (cdr xs))
                             (bebits=>nat (cdr ys)))
                          (equal (car cdr-rs) 1))))
              (b* ((ds (bitxor-list xs ys))
                   (rs (bits-lt-r ds ys)))
                (iff (< (bebits=>nat xs)
                        (bebits=>nat ys))
                     (equal (car rs) 1))))
     :use (:instance induction-step-with-cons
                     (xs (cdr xs))
                     (ys (cdr ys))
                     (a (car xs))
                     (b (car ys))))

   (defruled len-lemma
     (equal (equal (len l) 1)
            (and (consp l)
                 (not (consp (cdr l))))))))

; As explained earlier, the gadget has the bits in little-endian order.
; Thus, we use the core theorem proved just above
; to prove a similar one for little-endian order.
; The theorem below uses LEBITS=>NAT instead of BEBITS=>NAT,
; applies BITS-LT-R to the reversed lists and reverses its result,
; and pick the last bit instead of the first one.
; As it should be clear from the :USE hints below,
; this is proved from the previous one just by reversing everything.
; The reason why REV only appears around BITS-LT-R is that
; all the other uses are essentialy "invariant" under reversal,
; i.e. BIT-LISTP holds on a list iff it holds on the reverse,
; BITXOR-LIST maps reversed inputs to reversed outputs,
; and so on.
; But BITS-LT-R is not like that,
; and so we need REV on both inputs and outputs.

(defruledl bitxor+bitslt-to-<-lendian-iff-bit1
  (implies (and (bit-listp xs)
                (bit-listp ys)
                (equal (len xs) (len ys))
                (consp xs))
           (b* ((ds (bitxor-list xs ys))
                (rs (rev (bits-lt-r (rev ds) (rev ys)))))
             (iff (< (lebits=>nat xs)
                     (lebits=>nat ys))
                  (equal (car (last rs)) 1))))
  :use (:instance bitxor+bitslt-to-<-bendian-iff-bit1
                  (xs (rev xs))
                  (ys (rev ys)))
  :enable (bitxor-list-of-rev
           acl2::bebits=>nat-of-rev))

; Finally we put things together to obtain
; the main soundness theorem for the gadget.
; By expanding BITS-LT-GADGET,
; we obtain BITS-LT-GADGET-AUX on the REVs of the lists of variables.
; We use BITS-LT-GADGET-AUX-TO-BITXOR+BITSLT
; to derive a characterization in terms of BITXOR-LIST and BITS-LT-R.
; We use BITXOR+BITSLT-TO-<-LENDIAN-IFF-BIT1 just above
; to derive the desired main property,
; i.e. that the inequality is equivalent to the last RS bit being 1.

; The local lemma below serves to discharge a subgoal
; whose essence is the lemma itself.
; It is actually conceptually very easy to prove:
; since (REV (LOOKUP-EQUAL-LST RS ASG)) = (BITS-LT-R ...),
; which returns BIT-LISTP under suitable assumptions (given in the lemma),
; it's enough to "move" the REV from the left to the right
; in the equality stated just above,
; obtaining (LOOKUP-EQUAL-LST RS ASG) = (REV (BITS-LT-R ...)),
; from which BIT-LISTP follows easily.
; However, ACL2's heuristics resist that,
; even with some targeted rewrite rules;
; we resorted to proof builder commands to get this proof.
; Perhaps there is a less verbose way,
; but this is nonetheless clear and efficient.

(defruled bits-lt-gadget-to-<-lendian-iff-bit1
  (implies (and (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp ds)
                (symbol-listp rs)
                (equal (len xs) (len ys))
                (equal (len ys) (len ds))
                (equal (len ds) (len rs))
                (consp xs)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg ds)
                (r1cs::valuation-binds-allp asg rs))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (ds$ (lookup-equal-list ds asg))
                (rs$ (lookup-equal-list rs asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$))
                      (implies (r1cs::r1cs-constraints-holdp
                                (bits-lt-gadget xs ys ds rs p) asg p)
                               (and (bit-listp ds$)
                                    (bit-listp rs$)
                                    (iff (< (lebits=>nat xs$)
                                            (lebits=>nat ys$))
                                         (equal (car (last rs$)) 1)))))))
  :do-not-induct t
  :enable (bits-lt-gadget
           lookup-equal-list-of-rev
           len-of-lookup-equal-list
           r1cs::valuation-binds-allp-of-rev
           bitxor-list-of-rev)
  :use ((:instance bits-lt-gadget-aux-to-bitxor+bitslt
                   (xs (rev xs)) (ys (rev ys)) (ds (rev ds)) (rs (rev rs)))
        (:instance bitxor+bitslt-to-<-lendian-iff-bit1
                   (xs (lookup-equal-list xs asg))
                   (ys (lookup-equal-list ys asg))))
  :prep-lemmas
  ((defrule lemma
     (implies (and (bit-listp (lookup-equal-list ys asg))
                   (equal (len ds) (len ys))
                   (equal (rev (lookup-equal-list rs asg))
                          (bits-lt-r (rev (lookup-equal-list ds asg))
                                     (rev (lookup-equal-list ys asg)))))
              (bit-listp (lookup-equal-list rs asg)))
     :instructions
     ((pro)
      (claim (equal (lookup-equal-list rs asg)
                    (rev (bits-lt-r (rev (lookup-equal-list ds asg))
                                    (rev (lookup-equal-list ys asg))))))
      (dive 1)
      (=)
      (up)
      (drop 3 4)
      (prove)))))
