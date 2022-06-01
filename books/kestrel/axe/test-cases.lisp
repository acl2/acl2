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
(include-book "evaluator") ; todo
(include-book "misc/random" :dir :system)
(local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;move
(defthm integerp-of-mv-nth-0-of-genrandom
  (implies (integerp max) ; gen?
           (integerp (mv-nth 0 (genrandom max rand))))
  :hints (("Goal" :in-theory (enable genrandom))))

;;returns an integer in the range [low, high)
;fffixme doesn't work if the range is too big?
(defun gen-random-integer-in-range (low high rand)
  (declare (xargs :stobjs (rand)
                  :guard-hints (("Goal" :in-theory (enable genrandom)))
                  :guard (and (integerp low) (> low 0) (integerp high) (< low high))))
  (mv-let (value rand)
          (genrandom (- high low) rand)
          (mv (+ low value) rand)))

;returns (val rand)
;since genrandom doesn't work for a BV of more than 31 bits, we have to generate it in chunks
(defund gen-random-bv (size rand)
  (declare (xargs :stobjs (rand)
                  :measure (nfix size)
                  :guard (and (posp size))
                  :guard-hints (("Goal" :in-theory (enable genrandom)))
                  :verify-guards nil ;done below
                  ))
  (if (or (not (natp size))
          (< size 32))
      (genrandom (expt 2 size) rand)
    (mv-let (first-chunk rand)
      (genrandom (expt 2 31) ;compute
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

;fixme where do we document the format of var-type-alist (see axe-types.lisp, but that is incomplete?)?  a naked integer is a bv, a quoted integer is that constant
;returns (mv value rand)
;should we allow tuples?
(mutual-recursion
 (defun gen-random-value (type rand var-value-alist)
   (declare (xargs :guard (and (axe-typep type)
                               (symbol-alistp var-value-alist))
                   :stobjs (rand)
                   :measure (make-ord 1 (+ 1 (acl2-count type)) 0)
                   :verify-guards nil ; todo
                   :hints (("Goal" :expand (axe-typep type)
                            :in-theory (enable list-type-element-type list-type-len-type bv-typep list-typep
                                                      axe-typep)))))
   (cond ((quotep type) ;; a quoted constant represents a singleton type (just unquote the constant):
          (mv (unquote type) rand))
         ((symbolp type) ;; a symbol means lookup a previously generated value (i guess this is a 'dependent type'?) ; todo: just use :eval for this?
          (mv (lookup-eq-safe type var-value-alist)
              rand))
         ((bv-typep type) ;a bit-vector of the indicated width - should we allow this width to be random?
          ;; if it's a bit-vector
          ;; look up the variable's width and generate a random value of that width
          (let* ((width (bv-type-width type))
                 ;;(max (expt 2 width)) ;bozo precompute this on small values?
                 )
            (gen-random-bv width rand)))
         ;; a value in the given range: should we allow the bounds to be random? ;fixme are the args of this good types? if we allow random endpoints, what if the range is empty?  maybe :range should take a start value and am interval length?
         ((eq :range (car type)) ;here the bounds are both inclusive
          (let ((low (second type))
                (high (third type)))
            (gen-random-integer-in-range low (+ 1 high) rand)))
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
          (mv (eval-axe-evaluator var-value-alist
                                  (second type)
                                  nil ;fixme?
                                  0)
              rand))
         ;;a random element of the given set:
         ((eq :element (car type)) ;should the elements be allowed to be random?
          (let ((set (cdr type)))  ;or use cadr?
            (mv-let (index rand)
              (genrandom (len set) rand)
              (mv (nth index set) rand))))
         ;;a list, of the given element type and length - can the length be random? yes.?
         ((list-typep type)
          ;;            (or (eq :list (car type))
          ;;                ;;(eq 'array (car type)) ;i think the args to an array type aren't currently good types
          ;;                ) ;bozo why both? get rid of the 'array option? hmmm. it's used in translating...
          (let ((element-type (list-type-element-type type))
                (len-type (list-type-len-type type)))
            (mv-let (len rand)
              ;;if the len-type is a quoted constant, this just unquotes it:
              (gen-random-value len-type rand var-value-alist)
              (prog2$ (cw "List length: ~x0.~%" len)
                      (gen-random-values len element-type rand var-value-alist)))))
         (t (mv (er hard? 'gen-random-value "Unknown type: ~x0" type)
                rand))))

 ;;returns (mv values rand)
 (defun gen-random-values (n type rand var-value-alist)
   (declare (xargs :guard (and (natp n)
                               (axe-typep type)
                               (symbol-alistp var-value-alist))
                   :stobjs (rand)
                   :measure (make-ord 1 (+ 1 (acl2-count type)) (+ 1 (nfix n)))))
   (if (zp n)
       (mv nil rand)
     (mv-let (value rand)
       (gen-random-value type rand var-value-alist)
       (mv-let (values rand)
         (gen-random-values (+ -1 n) type rand var-value-alist)
         (mv (cons value values)
             rand))))))

(skip-proofs (verify-guards gen-random-value))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognize a test case.
(defund test-casep (test-case)
  (declare (xargs :guard t))
  (symbol-alistp test-case))

;; Recognize a true list of test cases.
(defund test-casesp (test-cases)
  (declare (xargs :guard t))
  (if (atom test-cases)
      (null test-cases)
    (and (test-casep (first test-cases))
         (test-casesp (rest test-cases)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;returns (mv alist rand)
(defund make-test-case (var-type-alist acc rand)
  (declare (xargs :guard (and (symbol-alistp var-type-alist)
                              (symbol-alistp acc))
                  :stobjs rand
                  :verify-guards nil ; todo
                  ))
  (if (endp var-type-alist)
      (mv acc rand)
    (let* ((entry (first var-type-alist))
           (var (car entry))
           (type (cdr entry)))
      (mv-let (value rand)
              (gen-random-value type rand acc)
              (make-test-case (rest var-type-alist) (acons-fast var value acc) rand)))))

(skip-proofs (verify-guards make-test-case))

(defthm test-casep-of-mv-nth-0-of-make-test-case
  (implies (and (symbol-alistp var-type-alist)
                (test-casep acc))
           (test-casep (mv-nth 0 (make-test-case var-type-alist acc rand))))
  :hints (("Goal" :in-theory (enable test-casep make-test-case))))

;;ffixme might we need to pass in interpreted-functions
(defun test-case-satisfies-assumptionsp (test-case assumptions)
  (if (endp assumptions)
      t
    (let ((assumption (first assumptions)))
      (and (equal t (eval-axe-evaluator test-case assumption nil ;interpreted-function-alist
                                           0))
           (test-case-satisfies-assumptionsp test-case (rest assumptions))
           ))))

(skip-proofs (verify-guards test-case-satisfies-assumptionsp))

;returns (mv test-cases rand), where each test case is an alist from vars to values
;should we give them numbers?
(defun make-test-cases-aux (test-cases-left test-case-number var-type-alist assumptions print acc rand)
  (declare (xargs :stobjs rand
                  :verify-guards nil))
  (if (zp test-cases-left)
      (mv (reverse acc)
          rand)
    (prog2$
     (and print (cw "(Test case ~x0: " test-case-number))
     (mv-let (test-case rand)
             (make-test-case var-type-alist nil rand)
             (prog2$ (and print (cw ")~%"))
                     (if (test-case-satisfies-assumptionsp test-case assumptions)
                         (make-test-cases-aux (+ -1 test-cases-left)
                                              (+ 1 test-case-number)
                                              var-type-alist
                                              assumptions
                                              print
                                              (cons test-case acc)
                                              rand)
                       (prog2$ (cw "!! WARNING test case ~x0 does not satisfy assumptions. Dropping it. !!~%" test-case-number)
                               (make-test-cases-aux (+ -1 test-cases-left) ;perhaps don't decrement the counter?
                                                    (+ 1 test-case-number)
                                                    var-type-alist
                                                    assumptions
                                                    print
                                                    acc ;don't cons it on
                                                    rand))))))))

(skip-proofs (verify-guards make-test-cases-aux))

;returns (mv test-cases rand), where each test case is an alist from vars to values
(defun make-test-cases (test-case-count var-type-alist assumptions rand)
  (declare (xargs :stobjs rand
                  :verify-guards nil))
  (prog2$ (cw "(Making ~x0 test cases:~%" test-case-count)
          (mv-let (test-cases rand)
                  (make-test-cases-aux test-case-count 0 var-type-alist assumptions nil nil rand)
                  (prog2$ (cw ")~%")
                          (mv test-cases rand)))))

(skip-proofs (verify-guards make-test-cases))
