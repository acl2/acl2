; The Axe equivalence checker
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "axe-types")
;(include-book "evaluator") ; todo
(include-book "evaluator-basic")
(include-book "misc/random" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(include-book "kestrel/utilities/acons-fast" :dir :system)
(local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))

(local (in-theory (disable randp symbol-alistp)))

;move
(defthm integerp-of-mv-nth-0-of-genrandom
  (implies (integerp max) ; gen?
           (integerp (mv-nth 0 (genrandom max rand))))
  :hints (("Goal" :in-theory (enable genrandom))))

(defthm <=-of-0-and-mv-nth-0-of-genrandom
  (implies (natp max) ; gen?
           (<= 0 (mv-nth 0 (genrandom max rand))))
  :hints (("Goal" :in-theory (enable genrandom))))

(defthm natp-of-mv-nth-0-of-genrandom
  (implies (natp max) ; gen?
           (natp (mv-nth 0 (genrandom max rand))))
  :hints (("Goal" :in-theory (enable genrandom))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv val rand).
;since genrandom doesn't work for a BV of more than 31 bits, we have to generate it in chunks
;; TODO: Not quite uniform?
(defund gen-random-bv (size rand)
  (declare (xargs :guard (posp size)
                  :stobjs rand
                  :measure (nfix size)
                  :guard-hints (("Goal" :in-theory (enable genrandom)))
                  :verify-guards nil ;done below
                  ))
  (if (or (not (mbt (natp size)))
          (< size 32))
      (genrandom (expt 2 size) rand)
    (mv-let (first-chunk rand)
      (genrandom 2147483648 ; (expt 2 31)
                 rand)
      (mv-let (rest-chunk rand)
        (gen-random-bv (- size 31) rand)
        (mv (bvcat 31 first-chunk (- size 31) rest-chunk)
            rand)))))

(defthm integerp-of-mv-nth-0-of-gen-random-bv
  (integerp (mv-nth 0 (gen-random-bv size rand)))
  :hints (("Goal" :in-theory (enable gen-random-bv
                                     genrandom ;todo
                                     ))))

(verify-guards gen-random-bv)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Generate a random integer in the range [0, limit-1].
;; TODO: Not quite uniform
;; Handles larger integers than genrandom.
(defund gen-random-integer (limit rand)
  (declare (xargs :guard (posp limit)
                  :stobjs rand))
  (if (= 1 limit) ; special case (BV size of 0)
      (mv 0 rand)
    (mv-let (bv rand)
      (gen-random-bv (ceiling-of-lg limit) rand)
      (mv (mod bv limit) rand))))

(defthm integerp-of-mv-nth-0-of-gen-random-integer
  (implies (posp limit)
           (integerp (mv-nth 0 (gen-random-integer limit rand))))
  :hints (("Goal" :in-theory (enable gen-random-integer))))

(defthm acl2-numberp-of-mv-nth-0-of-gen-random-integer
  (acl2-numberp (mv-nth 0 (gen-random-integer limit rand)))
  :hints (("Goal" :in-theory (enable gen-random-integer))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;returns an integer in the range [low, high-1].
(defund gen-random-integer-in-range (low high rand)
  (declare (xargs :guard (and (integerp low)
                              (integerp high)
                              (< low high))
                  :stobjs rand))
  (mv-let (value rand)
    (gen-random-integer (- high low) rand)
    (mv (+ low value) rand)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund test-case-typep (type)
  (declare (xargs :guard t
                  :hints (("Goal" :in-theory (enable list-type-len-type
                                                     list-type-element-type
                                                     list-typep)))))
  (or (myquotep type)
      (symbolp type) ; look up a previous val
      (bv-typep type)
      (and (list-typep type)
           (test-case-typep (list-type-element-type type))
           ;; todo: must be a scalar type:
           (test-case-typep (list-type-len-type type)))
      (and (consp type)
           (eq :range (ffn-symb type))
           (consp (fargs type))
           (consp (cdr (fargs type)))
           (integerp (farg1 type))
           (integerp (farg2 type))
           (< (farg1 type) (farg2 type)) ; low < high
           )
      (and (consp type)
           (eq :eval (ffn-symb type))
           (consp (fargs type))
           (pseudo-termp (farg1 type)))
      (and (consp type)
           (eq :element (ffn-symb type))
           (true-listp (cdr type)) ; or make the elements the cadr?
           (consp (cdr type)) ; must be at least one element
           )))

;; Recognize an alist from vars to their "test types"
(defund test-case-type-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (null alist)
    (let ((entry (first alist)))
      (and (consp entry)
           (let ((var (car entry))
                 (type (cdr entry)))
             (and (symbolp var)
                  (test-case-typep type)
                  (test-case-type-alistp (rest alist))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;returns (mv erp value rand)
;should we allow tuples?
(mutual-recursion
 (defund gen-random-value (type rand var-value-alist)
   (declare (xargs :guard (and (test-case-typep type)
                               (symbol-alistp var-value-alist))
                   :stobjs rand
                   :measure (make-ord 1 (+ 1 (acl2-count type)) 0)
                   :hints (("Goal" :expand (axe-typep type)
                            :in-theory (e/d (list-type-element-type
                                             list-type-len-type
                                             bv-typep
                                             list-typep
                                             axe-typep)
                                            (natp))))
                   :guard-hints (("Goal"
                                  :in-theory (e/d (list-typep BV-TYPEP test-case-typep)
                                                  (natp))))))
   (cond ((quotep type) ;; a quoted constant represents a singleton type (just unquote the constant):
          (mv (erp-nil) (unquote type) rand))
         ((symbolp type) ;; a symbol means lookup a previously generated value (i guess this is a 'dependent type'?) ; todo: just use :eval for this?
          (mv (erp-nil)
              (lookup-eq-safe type var-value-alist) ; todo
              rand))
         ((bv-typep type) ;a bit-vector of the indicated width - should we allow this width to be random?
          ;; if it's a bit-vector
          ;; look up the variable's width and generate a random value of that width
          (let* ((width (bv-type-width type))
                 ;;(max (expt 2 width)) ;bozo precompute this on small values?
                 )
            (if (equal width 0)
                (mv (erp-nil) 0 rand)
              (b* (((mv value rand) (gen-random-bv width rand)))
                (mv (erp-nil) value rand)))))
         ;; a value in the given range: should we allow the bounds to be random? ;fixme are the args of this good types? if we allow random endpoints, what if the range is empty?  maybe :range should take a start value and am interval length?
         ((eq :range (car type)) ;here the bounds are both inclusive
          (let ((low (second type))
                (high (third type)))
            (b* (((mv value rand) (gen-random-integer-in-range low (+ 1 high) rand)))
              (mv (erp-nil) value rand))))
         ;;           ((eq :len (car type)) ;the length of something (probably a previously generated var - this is also a dependent type - more general facility for this?):
         ;;            (mv-let (value rand)
         ;;                    (gen-random-value (second type) rand var-value-alist) ;just lookup the value?
         ;;                    (mv (len value) rand)))
         ;; ((eq :choice (car type)) ;fixme add support for probabilities other than 50/50
         ;;  (mv-let (val rand)
         ;;    (genrandom 2 rand)
         ;;    (if (eql 0 val)
         ;;        (gen-random-value (second type) rand var-value-alist)
         ;;      (gen-random-value (third type) rand var-value-alist))))
         ((eq :eval (car type))
          (b* (((mv erp value) (eval-axe-evaluator-basic var-value-alist
                                                         (second type)
                                                         nil ;fixme?
                                                         1000000000))
               ((when erp) (mv erp nil rand)))
            (mv (erp-nil) value rand)))
         ;;a random element of the given set:
         ((eq :element (car type)) ;should the elements be allowed to be random?
          (let ((set (cdr type)))  ;or use cadr?
            (mv-let (index rand)
              (genrandom (len set) rand)
              (mv (erp-nil) (nth index set) rand))))
         ;;a list, of the given element type and length - can the length be random? yes.?
         ((list-typep type)
          ;;            (or (eq :list (car type))
          ;;                ;;(eq 'array (car type)) ;i think the args to an array type aren't currently good types
          ;;                ) ;bozo why both? get rid of the 'array option? hmmm. it's used in translating...
          (b* ((element-type (list-type-element-type type))
               (len-type (list-type-len-type type))
               ((mv erp len rand)
                ;;if the len-type is a quoted constant, this just unquotes it:
                (gen-random-value len-type rand var-value-alist))
               ((when erp) (mv erp nil rand)))
            (if (not (natp len)) ; todo: drop check if we restrict what the len-type of a list-type can be
                (prog2$ (er hard? 'gen-random-value "List length not a natp.")
                        (mv (erp-t) nil rand))
              (prog2$ (cw "List length: ~x0.~%" len)
                      (gen-random-values len element-type rand var-value-alist)))))
         (t (mv (erp-t)
                (er hard? 'gen-random-value "Unknown type: ~x0" type)
                rand))))

 ;;returns (mv erp values rand)
 (defund gen-random-values (n type rand var-value-alist)
   (declare (xargs :guard (and (natp n)
                               (test-case-typep type)
                               (symbol-alistp var-value-alist))
                   :stobjs rand
                   :measure (make-ord 1 (+ 1 (acl2-count type)) (+ 1 (nfix n)))))
   (if (zp n)
       (mv (erp-nil) nil rand)
     (b* (((mv erp value rand) (gen-random-value type rand var-value-alist))
          ((when erp) (mv erp nil rand))
          ((mv erp values rand) (gen-random-values (+ -1 n) type rand var-value-alist))
          ((when erp) (mv erp nil rand)))
       (mv (erp-nil) (cons value values) rand)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognize a test case, an alist from variables to their values.
(defund test-casep (test-case)
  (declare (xargs :guard t))
  (symbol-alistp test-case))

(defthm test-casep-of-cons-of-cons
  (equal (test-casep (cons (cons var val) test-case))
         (and (symbolp var)
              (test-casep test-case)))
  :hints (("Goal" :in-theory (enable test-casep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognize a true list of test cases.
(defund test-casesp (test-cases)
  (declare (xargs :guard t))
  (if (atom test-cases)
      (null test-cases)
    (and (test-casep (first test-cases))
         (test-casesp (rest test-cases)))))

(defthm test-casesp-of-cons
  (equal (test-casesp (cons case cases))
         (and (test-casep case)
              (test-casesp cases)))
  :hints (("Goal" :in-theory (enable test-casesp))))

(defthm test-casesp-of-reverse-list
  (implies (test-casesp acc)
           (test-casesp (reverse-list acc)))
  :hints (("Goal" :in-theory (enable reverse-list test-casep))))

(defthm test-casesp-of-car
  (implies (test-casesp l)
           (test-casep (car l)))
  :hints (("Goal" :in-theory (enable test-casesp))))

(defthm test-casesp-forward-to-true-listp
  (implies (test-casesp cases)
           (true-listp cases))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable test-casesp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp test-case rand).
(defund make-test-case (test-case-type-alist acc rand)
  (declare (xargs :guard (and (test-case-type-alistp test-case-type-alist)
                              (test-casep acc))
                  :stobjs rand
                  :guard-hints (("Goal" :in-theory (enable test-case-type-alistp)))))
  (if (endp test-case-type-alist)
      (mv (erp-nil) acc rand)
    (let* ((entry (first test-case-type-alist))
           (var (car entry))
           (type (cdr entry)))
      (b* (((mv erp value rand) (gen-random-value type rand acc))
           ((when erp) (mv erp nil rand)))
        (make-test-case (rest test-case-type-alist) (acons-fast var value acc) rand)))))

(defthm test-casep-of-mv-nth-1-of-make-test-case
  (implies (and (test-case-type-alistp test-case-type-alist)
                (test-casep acc))
           (test-casep (mv-nth 1 (make-test-case test-case-type-alist acc rand))))
  :hints (("Goal" :in-theory (enable test-casep make-test-case TEST-CASE-TYPE-ALISTP))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: might we need to pass in interpreted-functions?
;; Returns (mv erp res).
(defund test-case-satisfies-assumptionsp (test-case assumptions)
  (declare (xargs :guard (and (test-casep test-case)
                              (pseudo-term-listp assumptions))))
  (if (endp assumptions)
      (mv (erp-nil) t)
    (b* ((assumption (first assumptions))
         ((mv erp value) (eval-axe-evaluator-basic test-case assumption
                                                   nil ;interpreted-function-alist
                                                   1000000000))
         ((when erp) (mv erp value)))
      (if (equal t value)
          (test-case-satisfies-assumptionsp test-case (rest assumptions))
        (mv (erp-nil) nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;returns (mv erp test-cases rand), where each test case is an alist from vars to values
;should we give them numbers?
(defund make-test-cases-aux (test-cases-left test-case-number test-case-type-alist assumptions print acc rand)
  (declare (xargs :guard (and (natp test-cases-left)
                              (natp test-case-number)
                              (test-case-type-alistp test-case-type-alist)
                              (pseudo-term-listp assumptions)
                              (test-casesp acc))
                  :stobjs rand))
  (if (zp test-cases-left)
      (mv (erp-nil)
          (reverse-list acc)
          rand)
    (b* ((- (and print (cw "(Test case ~x0: " test-case-number)))
         ((mv erp test-case rand) (make-test-case test-case-type-alist nil rand))
         ((when erp) (mv erp nil rand))
         (- (and print (cw ")~%")))
         ((mv erp satp)
          (test-case-satisfies-assumptionsp test-case assumptions))
         ((when erp) (mv erp nil rand)))
      (if satp
          (make-test-cases-aux (+ -1 test-cases-left)
                               (+ 1 test-case-number)
                               test-case-type-alist
                               assumptions
                               print
                               (cons test-case acc)
                               rand)
        (prog2$ (cw "!! WARNING test case ~x0 does not satisfy assumptions. Dropping it. !!~%" test-case-number)
                (make-test-cases-aux (+ -1 test-cases-left) ;perhaps don't decrement the counter?
                                     (+ 1 test-case-number)
                                     test-case-type-alist
                                     assumptions
                                     print
                                     acc ;don't cons it on
                                     rand))))))

(defthm test-casesp-of-mv-nth-1-of-make-test-cases-aux
  (implies (and (test-case-type-alistp test-case-type-alist)
                (test-casesp acc))
           (test-casesp (mv-nth 1 (make-test-cases-aux test-cases-left test-case-number test-case-type-alist assumptions print acc rand))))
  :hints (("Goal" :in-theory (enable make-test-cases-aux))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp test-cases rand), where each test case is an alist from vars to values.
;; TODO: Consider passing in interpreted-functions?
(defund make-test-cases (test-case-count test-case-type-alist assumptions rand)
  (declare (xargs :guard (and (natp test-case-count)
                              (test-case-type-alistp test-case-type-alist)
                              (pseudo-term-listp assumptions))
                  :stobjs rand))
  (prog2$ (cw "(Making ~x0 test cases:~%" test-case-count)
          (mv-let (erp test-cases rand)
                  (make-test-cases-aux test-case-count 0 test-case-type-alist assumptions nil nil rand)
                  (prog2$ (cw ")~%")
                          (mv erp test-cases rand)))))

(defthm test-casesp-of-mv-nth-1-of-make-test-cases
  (implies (and (test-case-type-alistp test-case-type-alist)
                (test-casesp acc))
           (test-casesp (mv-nth 1 (make-test-cases test-case-count test-case-type-alist assumptions rand))))
  :hints (("Goal" :in-theory (enable make-test-cases))))
