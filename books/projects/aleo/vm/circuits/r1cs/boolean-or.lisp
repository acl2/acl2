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

(include-book "zero")
(include-book "equal")

(include-book "../library-extensions/lookup-equal-list")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "kestrel/utilities/typed-lists/bit-listp" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "../library-extensions/r1cses"))

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))
(local (include-book "projects/pfcs/r1cs-lib-ext" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specification

; We define a function for the inclusive disjunction of two bits,
; even though perhaps we could just use the built-in LOGOR.

(define bitor ((x bitp) (y bitp))
  :returns (z bitp)
  (if (or (= x 1) (= y 1)) 1 0))

(defruled bitor-commute
  (equal (bitor x y) (bitor y x))
  :hints (("Goal" :in-theory (enable bitor))))

; We introduce a function that lifts BITOR to lists.

(define bitor-list ((xs bit-listp) (ys bit-listp))
  :guard (equal (len xs) (len ys))
  :returns (zs bit-listp)
  (cond ((endp xs) nil)
        (t (cons (bitor (car xs) (car ys))
                 (bitor-list (cdr xs) (cdr ys)))))

  ///

  (defret len-of-bitor-list
    (equal (len zs) (len xs)))

  (defruled bitor-list-of-append
    (implies (equal (len xs1) (len ys1))
             (equal (bitor-list (append xs1 xs2)
                                (append ys1 ys2))
                    (append (bitor-list xs1 ys1)
                            (bitor-list xs2 ys2)))))

  (defruled bitor-list-of-rev
    (implies (equal (len xs) (len ys))
             (equal (bitor-list (rev xs) (rev ys))
                    (rev (bitor-list xs ys))))
    :enable bitor-list-of-append))

; N-ary bitor

(define bitor* ((xs bit-listp))
  :returns (z bitp)
  (cond ((endp xs) 0)
        (t (bitor (car xs) (bitor* (cdr xs))))))

(defruled bitor*-1arg-means-identity
  (implies (and (bit-listp xs)
                (equal (len xs) 1))
           (equal (bitor* xs)
                  (car xs)))
  :enable bitor*)

(defruled bitor*-0args-means-0
  (implies (and (bit-listp xs)
                (equal (len xs) 0))
           (equal (bitor* xs)
                  0))
  :enable bitor*)

; An interesting thing about bitor* is that if the result is zero
; then all the arguments are zero.

(defruled bitor*=0-means-all-zero
  (implies (bit-listp xs)
           (equal (equal (bitor* xs) 0)
                  (equal xs (repeat (len xs) 0))))
  :enable (bitor* bitor repeat))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is boolean inclusive disjunction.
; It assumes that x and y are booleans,
; and constraint z to be their inclusive disjunction,
; i.e. 0 iff both are 0.
; The gadget consists of a single constraint
;   ((p-1)x + 1) ((p-1)y + 1) = ((p-1)z + 1)

(define boolean-or-gadget ((x symbolp) (y symbolp) (z symbolp) (p primep))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (list (r1cs::make-r1cs-constraint
         :a (list (list (1- p) x)
                  (list 1 1))
         :b (list (list (1- p) y)
                  (list 1 1))
         :c (list (list (1- p) z)
                  (list 1 1)))))

; The gadget is equivalent to its specification,
; i.e. that z is the inclusive disjunction of x and y
; assuming x and y are booleans.

(defruled boolean-or-gadget-to-bitor
  (implies (and (symbolp x)
                (symbolp y)
                (symbolp z)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-bindsp asg x)
                (r1cs::valuation-bindsp asg y)
                (r1cs::valuation-bindsp asg z))
           (b* ((x$ (lookup-equal x asg))
                (y$ (lookup-equal y asg))
                (z$ (lookup-equal z asg)))
             (implies (and (bitp x$)
                           (bitp y$))
                      (equal (r1cs::r1cs-constraints-holdp
                              (boolean-or-gadget x y z p) asg p)
                             (equal z$ (bitor x$ y$))))))
  :cases ((equal p 2))
  :enable (boolean-or-gadget
           r1cs::r1cs-constraint-holdsp
           r1cs::dot-product))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A list of inclusive disjunction gadgets.

(define boolean-or-gadget-list ((xs symbol-listp)
                                (ys symbol-listp)
                                (zs symbol-listp)
                                (p primep))
  :guard (and (equal (len xs) (len ys))
              (equal (len ys) (len zs)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (cond ((endp xs) nil)
        (t (append (boolean-or-gadget (car xs) (car ys) (car zs) p)
                   (boolean-or-gadget-list (cdr xs) (cdr ys) (cdr zs) p)))))

; A list of exclusive disjunction gadgets is equivalent to its specification,
; which is in terms of BITOR-LIST.

(defruled boolean-or-gadget-list-to-bitor-list
  (implies (and (symbol-listp xs)
                (symbol-listp ys)
                (symbol-listp zs)
                (equal (len xs) (len ys))
                (equal (len ys) (len zs))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ys)
                (r1cs::valuation-binds-allp asg zs))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ys$ (lookup-equal-list ys asg))
                (zs$ (lookup-equal-list zs asg)))
             (implies (and (bit-listp xs$)
                           (bit-listp ys$))
                      (equal (r1cs::r1cs-constraints-holdp
                              (boolean-or-gadget-list xs ys zs p) asg p)
                             (equal zs$ (bitor-list xs$ ys$))))))
  :induct (ind xs ys zs)
  :enable (boolean-or-gadget-list
           boolean-or-gadget-to-bitor
           bitor-list
           lookup-equal-list)
  :disable bitp
  :prep-lemmas
  ((defun ind (x y z)
     (cond ((or (atom x) (atom y) (atom z)) nil)
           (t (ind (cdr x) (cdr y) (cdr z)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; N-ary boolean 'or', such as from
;   let r = bits.iter().fold(Boolean::constant(false), |a, b| a | b);
;
; The way this looks in constraints is:
;   bit0 | bit1 = w0
;   w0 | bit2 = w1
;   w1 | bit3 = w2
;   ...
; The last wN is the return value ('r' in the let statement above)

; This is actually a family of gadgets, since the length of the 'bits' list can
; be anything:
; * If it is empty, the gadget sets r to false.
; * If 'bits' has only one element, the gadget sets r to that bit.
; * If 'bits" has two elements, the gadget is equivalent to boolean-or-gadget.
; * If 'bits' has three or more elements, the first constraint is a
;   boolean-or-gadget applied to the first two elements,
;   and then each additional constraint ORs the result of the previous constraint
;   with one additional element of 'bits' to yield a new result bit.

#||
; Here is the first formulation of the gadget.
; This assumes 'bits' and 'resultvars' are in the natural order they occur
; in the constraints, and the recursive case creates constraints in the
; R1CS order as well (shown above).

; However, it is easier to do the inductive proofs of correctness if the
; recursive call takes 'bits' and 'resultvars' in the reverse order
; and assembles the constraints in the reverse order,
; so we leave these definitions in the comment.
; (We could take them out of the comment and prove equivalence later.)

(define boolean-n-ary-or-gadget-recur ((bits symbol-listp)
                                       (resultvars symbol-listp)
                                       (p primep))
  ;; The first resultvar was set in the previous constraint.
  :guard (= (+ (len bits) 1) (len resultvars))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (if (or (endp bits) (endp resultvars) (endp (cdr resultvars)))
      nil
    (append (boolean-or-gadget (first resultvars)
                               (first bits)
                               (second resultvars)
                               p)
            (boolean-n-ary-or-gadget-recur (cdr bits)
                                           (cdr resultvars)
                                           p))))

(define boolean-n-ary-or-gadget ((bits symbol-listp) (resultvars symbol-listp) (p primep))
  :guard (or (and (< 1 (len bits)) (equal (len resultvars) (- (len bits) 1)))
             (and (< (len bits) 2) (equal (len resultvars) 1)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (if (endp bits)
      (zero-gadget (car resultvars))
    (if (= (len bits) 1)
        (equal-gadget (car bits) (car resultvars))
      (append (boolean-or-gadget (first bits) (second bits) (first resultvars) p)
              (boolean-n-ary-or-gadget-recur (cddr bits)
                                             resultvars
                                             p)))))
||#

; We calculate the constraints recursively with boolean-n-ary-or-gadget-recur
; but in the reverse order of above, and then boolean-n-ary-or-gadget reverses
; them to get the order above.
;
; To facilitate recursively calculating the constraints in the reverse order,
; and to facilitate proofs about the computation,
; the variables in the lists 'xs' and 'ws' are in reverse
; of their occurrence in the constraints in the comments above.

(define boolean-n-ary-or-gadget ((xs symbol-listp) (ws symbol-listp) (p primep))
  :guard (or (and (< 1 (len xs)) (equal (len ws) (- (len xs) 1)))
             (and (< (len xs) 2) (equal (len ws) 1)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  (if (endp xs)
      (zero-gadget (car ws))
    (if (= (len xs) 1)
        (equal-gadget (car xs) (car ws))
      (rev (boolean-n-ary-or-gadget-recur xs
                                          ws
                                          p))))
  :prepwork
  ((define boolean-n-ary-or-gadget-recur ((xs symbol-listp)
                                          (ws symbol-listp)
                                          (p primep))
     :guard (and (< 1 (len xs))
                 (equal (len ws) (- (len xs) 1)))
     :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
     (if (not (mbt (consp (cdr xs))))
         nil
       (if (endp (cddr xs))
           (boolean-or-gadget (second xs) (first xs) (first ws) p)
         (append (boolean-or-gadget (second ws)
                                    (first xs)
                                    (first ws)
                                    p)
                 (boolean-n-ary-or-gadget-recur (cdr xs)
                                                (cdr ws)
                                                p)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We introduce a function that describes
; the recursive computation of the result values ($ws) from the bits (xs$).

(local
 (define wss ((xs$ bit-listp))
   :guard (and (consp xs$) (consp (cdr xs$)))
   :returns (ws$ bit-listp)
   :measure (len xs$)
   (cond ((not (mbt (consp (cdr xs$)))) nil)
         ((endp (cddr xs$))
          (list (bitor (cadr xs$) (car xs$))))
         (t (let ((cdr-ors (wss (cdr xs$))))
              (cons (bitor (car cdr-ors) (car xs$))
                    cdr-ors))))
   ///
   (defret len-of-wss
     (equal (len ws$)
            (1- (len xs$)))
     :hyp (consp xs$))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We prove that the gadget's satisfaction implies that
; its inputs and outputs are related according to the wss function.
; In order to prove this, we actually need to strenghten the claim
; to also say that the ws are bits:
; this is because boolean-or-gadget-to-bitor has hyps saying that
; the operands are bits, but during the proof of the following theorem
; these operands may be from ws, so we need the fact that they are bits.

; Attempting to prove both base case and induction step in one shot
; causes the proof to keep expanding wss,
; even though it should only be expanded once per case.
; It's not immediately clear why that happens;
; it seems just easier to prove base case and induction step separately.

; We use a custom induction scheme,
; because the base case must cover all the cases of xs and ws
; in which the gadget does not recur.

; We introduce an abbreviation p for the property to prove,
; and we use it in the base case and induction steps,
; to reduce repetitions.

(defruledl boolean-n-ary-or-gadget-recur-to-wss
  (implies (and (symbol-listp xs)
                (consp xs)
                (consp (cdr xs))
                (symbol-listp ws)
                (equal (len ws) (1- (len xs)))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ws))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ws$ (lookup-equal-list ws asg)))
             (implies (bit-listp xs$)
                      (implies (r1cs::r1cs-constraints-holdp
                                (boolean-n-ary-or-gadget-recur xs ws p)
                                asg p)
                               (and (bit-listp ws$)
                                    (let ((ws1$ (wss xs$)))
                                      (equal ws$ ws1$)))))))
  :induct (ind xs ws)
  :hints ('(:use (base-case induction-step)))

  :prep-lemmas

  ((defun ind (xs ws)
     (cond ((or (endp xs) (endp (cdr xs)) (endp (cddr xs))
                (endp ws) (endp (cdr ws))) t)
           (t (ind (cdr xs) (cdr ws)))))

   (defun p (xs ws asg p)
     (implies (and (symbol-listp xs)
                   (consp xs)
                   (consp (cdr xs))
                   (symbol-listp ws)
                   (equal (len ws) (1- (len xs)))
                   (primep p)
                   (r1cs::r1cs-valuationp asg p)
                   (r1cs::valuation-binds-allp asg xs)
                   (r1cs::valuation-binds-allp asg ws))
              (b* ((xs$ (lookup-equal-list xs asg))
                   (ws$ (lookup-equal-list ws asg)))
                (implies (bit-listp xs$)
                         (implies (r1cs::r1cs-constraints-holdp
                                   (boolean-n-ary-or-gadget-recur xs ws p)
                                   asg p)
                                  (and (bit-listp ws$)
                                       (let ((ws1$ (wss xs$)))
                                         (equal ws$ ws1$))))))))

   (defruled base-case
     (implies (or (endp xs) (endp (cdr xs)) (endp (cddr xs))
                  (endp ws) (endp (cdr ws)))
              (p xs ws asg p))
     :do-not-induct t
     :enable (boolean-n-ary-or-gadget-recur
              wss
              lookup-equal-list
              boolean-or-gadget-to-bitor))

   (defruled induction-step
     (implies (and (not (or (endp xs) (endp (cdr xs)) (endp (cddr xs))
                            (endp ws) (endp (cdr ws))))
                   (p (cdr xs) (cdr ws) asg p))
              (p xs ws asg p))
     :do-not-induct t
     :expand (wss (list* (lookup-equal (car xs) asg)
                         (lookup-equal (cadr xs) asg)
                         (lookup-equal-list (cddr xs) asg)))
     :enable (boolean-n-ary-or-gadget-recur
              lookup-equal-list
              boolean-or-gadget-to-bitor
              car-of-lookup-equal-list)
     :disable bitp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Prove that the function wss is correct according to the spec bitor*.

(defruledl wss-correctness
  (implies (and (bit-listp xs$)
                (consp xs$) (consp (cdr xs$)))
           (let ((ors (wss xs$)))
             (equal (car ors)
                    (bitor* xs$))))

  :induct (ind xs$)
  :hints ('(:use (base-case induction-step)))

  :prep-lemmas

  ((defun ind (xs$)
     (cond ((or (endp xs$) (endp (cdr xs$)) (endp (cddr xs$)))
            t)
           (t (ind (cdr xs$)))))

   ;; We copy the exact form of the body of wss-correctness
   (defun p (xs$)
     (implies (and (bit-listp xs$)
                   (consp xs$) (consp (cdr xs$)))
              (let ((ors (wss xs$)))
                (equal (car ors)
                       (bitor* xs$)))))

   (defruled base-case
     (implies (or (endp xs$) (endp (cdr xs$)) (endp (cddr xs$)))
              (p xs$))
     :do-not-induct t
     :enable (wss bitor*))

   (defruled induction-step
     (implies (and (not (or (endp xs$) (endp (cdr xs$)) (endp (cddr xs$))))
                   (p (cdr xs$)))
              (p xs$))
     :do-not-induct t
     :expand (wss xs$)
     :enable (bitor* bitor-commute)
   )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Prove soundness of the boolean-n-ary-or-gadget
; by splitting into 3 cases.

;;;;;;;;;;;;;;;;;;;;

; Prove soundness of the boolean-n-ary-or-gadget when there are two or more
; input variables in xs.

; soundness of the `-recur` function (for the case of 2 or more elements of ws)
(defruledl boolean-n-ary-or-recur-soundness
  (implies (and (symbol-listp xs)
                (symbol-listp ws)
                (< 1 (len xs))
                (equal (len ws) (1- (len xs)))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ws))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ws$ (lookup-equal-list ws asg)))
             (implies (bit-listp xs$)
                      (implies (r1cs::r1cs-constraints-holdp
                                (boolean-n-ary-or-gadget-recur xs ws p) asg p)
                               (and (bit-listp ws$)
                                    (equal (car ws$) (bitor* xs$)))))))
  :enable (boolean-n-ary-or-gadget-recur)
  :use (boolean-n-ary-or-gadget-recur-to-wss
        (:instance wss-correctness
                   (xs$ (lookup-equal-list xs asg)))))

(defruledl boolean-n-ary-or-2-soundness
  (implies (and (symbol-listp xs)
                (symbol-listp ws)
                (< 1 (len xs))
                (equal (len ws) (1- (len xs)))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ws))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ws$ (lookup-equal-list ws asg)))
             (implies (and (bit-listp xs$))
                      (implies (r1cs::r1cs-constraints-holdp
                                (boolean-n-ary-or-gadget xs ws p)
                                asg p)
                               (and (bit-listp ws$)
                                    (equal (car ws$) (bitor* xs$)))))))
  :enable (boolean-n-ary-or-gadget
           boolean-n-ary-or-recur-soundness))

;;;;;;;;;;;;;;;;;;;;

; Prove soundness of the boolean-n-ary-or-gadget when there is one
; input variable in xs.

(defruledl boolean-n-ary-or-=1-soundness
  (implies (and (symbol-listp xs)
                (symbol-listp ws)
                (equal (len xs) 1)
                (equal (len ws) 1)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ws))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ws$ (lookup-equal-list ws asg)))
             (implies (bit-listp xs$)
                      (implies (r1cs::r1cs-constraints-holdp
                                (boolean-n-ary-or-gadget xs ws p)
                                asg p)
                               (and (bit-listp ws$)
                                    (equal (car ws$) (bitor* xs$)))))))
  :enable (lookup-equal-list
           boolean-n-ary-or-gadget
           equal-gadget-to-equal))

;;;;;;;;;;;;;;;;;;;;

; Prove soundness of the boolean-n-ary-or-gadget when there are no
; input variable in xs.

(defruledl boolean-n-ary-or-=0-soundness
  (implies (and (symbol-listp xs)
                (symbol-listp ws)
                (equal (len xs) 0)
                (equal (len ws) 1)
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ws))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ws$ (lookup-equal-list ws asg)))
             (implies (bit-listp xs$)
                      (implies (r1cs::r1cs-constraints-holdp
                                (boolean-n-ary-or-gadget xs ws p)
                                asg p)
                               (and (bit-listp ws$)
                                    (equal (car ws$) (bitor* xs$)))))))
  :enable (boolean-n-ary-or-gadget
           lookup-equal-list
           zero-gadget-to-equal-0))

;;;;;;;;;;;;;;;;;;;;

; Combine the three cases to prove soundness of the boolean-n-ary-or-gadget
; for any number of inputs that satisfy the guard.

(defruled boolean-n-ary-or-soundness
  (implies (and (symbol-listp xs)
                (symbol-listp ws)
                (or (and (< 1 (len xs)) (equal (len ws) (- (len xs) 1)))
                    (and (< (len xs) 2) (equal (len ws) 1)))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ws))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ws$ (lookup-equal-list ws asg)))
             (implies (bit-listp xs$)
                      (implies (r1cs::r1cs-constraints-holdp
                                (boolean-n-ary-or-gadget xs ws p)
                                asg p)
                               (and (bit-listp ws$)
                                    (equal (car ws$) (bitor* xs$)))))))
  :do-not-induct t
  :cases ((and (equal (len xs) 0)
               (equal (len ws) 1))
          (and (equal (len xs) 1)
               (equal (len ws) 1))
          (and (< 1 (len xs))
               (equal (len ws) (1- (len xs)))))
  :use ((:instance boolean-n-ary-or-=0-soundness
                   (xs xs)
                   (ws ws)))
  :enable (len-of-lookup-equal-list
           boolean-n-ary-or-2-soundness
           boolean-n-ary-or-=1-soundness
          ;boolean-n-ary-or-=0-soundness
          ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The combination of the N-ary or gadget and a zero gadget,
; as in
;     let overflow = carry.iter().fold(Boolean::constant(false), |a, b| a | b);
;       E::assert_eq(overflow, E::zero());;
; Given that the variables are already constrained to be bits, the gadget
; is equivalent to stating that all the input variables are zero.

; Note, for now we restrict this to (< 1 (len xs))

(define boolean-n-ary-or-all-zero-gadget ((xs symbol-listp)
                                          (ws symbol-listp)
                                          (p primep))
  :guard ; (or
  (and (< 1 (len xs)) (equal (len ws) (- (len xs) 1)))
         ;(and (< (len xs) 2) (equal (len ws) 1)))
  :returns (constrs r1cs::r1cs-constraint-listp :hyp :guard)
  ; Note, xs and ws are the reverse of the natural (snarkVM) order,
  ; but the constraints returned are in the natural order.
  (append (boolean-n-ary-or-gadget xs ws p)
          (zero-gadget (first ws))))

; We show that if the xs are bits they must all be zero.
(defruled boolean-n-ary-or-all-zero-gadget-soundness
  (implies (and (symbol-listp xs)
                (symbol-listp ws)
                (and (< 1 (len xs)) (equal (len ws) (- (len xs) 1)))
                (primep p)
                (r1cs::r1cs-valuationp asg p)
                (r1cs::valuation-binds-allp asg xs)
                (r1cs::valuation-binds-allp asg ws))
           (b* ((xs$ (lookup-equal-list xs asg))
                (ws$ (lookup-equal-list ws asg)))
             (implies (bit-listp xs$)
                      (implies (r1cs::r1cs-constraints-holdp
                                (boolean-n-ary-or-all-zero-gadget xs ws p)
                                asg p)
                               (and (bit-listp ws$)
                                    (equal xs$ (repeat (len xs$) 0)))))))
  :use ((:instance boolean-n-ary-or-soundness
                   (xs xs)
                   (ws ws)))
  :enable (zero-gadget-to-equal-0
           car-of-lookup-equal-list
           boolean-n-ary-or-all-zero-gadget
           bitor*=0-means-all-zero))
