
; Multiplier verification

; Copyright (C) 2023 Intel Corporation
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Mertcan Temel <mert.temel@intel.com>

(in-package "RP")

(include-book "fnc-defs")

(include-book "find-adders/top")

(local
 (include-book "projects/rp-rewriter/proofs/proof-function-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(rp::def-rp-rule 4vec-p-of-int-vector-adder
  (sv::4vec-p (int-vector-adder x y)))

(rp::def-rp-rule 4vec-p-of-int-vector-adder-lst
  (sv::4vec-p (int-vector-adder-lst x)))

;;:i-am-here
(local
 (create-regular-eval-lemma rp 2 find-adders-in-svex-formula-checks))

(local
 (create-regular-eval-lemma INT-VECTOR-ADDER 2 find-adders-in-svex-formula-checks))

(local
 (create-regular-eval-lemma INT-VECTOR-ADDER-LST 1 find-adders-in-svex-formula-checks))

(local
 (create-regular-eval-lemma apply$ 2 find-adders-in-svex-formula-checks))

(local
 (create-regular-eval-lemma svl::4veclist-fix-wog 1 find-adders-in-svex-formula-checks))

(local
 (create-regular-eval-lemma svl::light-4vec-fix 1 find-adders-in-svex-formula-checks))

(local
 (create-regular-eval-lemma cons 2 find-adders-in-svex-formula-checks))

(local
 (defthm integerp-of-sum-of-integers
   (implies (and (integerp x)
                 (integerp y))
            (integerp (+ x y)))))

(local
 (defthm ifix-and-4vev-fix-when-integerp
   (implies (integerp x)
            (and (equal (ifix x) x)
                 (equal (sv::4vec-fix x) x)))
   :hints (("Goal"
            :in-theory (e/d (sv::4vec-fix) ())))))

(local
 (defthm rp-evlt-lst-of-append
   (equal (rp-evlt-lst (append x y) a)
          (append (rp-evlt-lst x a)
                  (rp-evlt-lst y a)))))

(local
 (defthm int-vector-adder-lst-of-append
   (equal (int-vector-adder-lst (append x y))
          (int-vector-adder (int-vector-adder-lst x)
                            (int-vector-adder-lst y)))
   :hints (("goal"
            :in-theory (e/d (int-vector-adder-lst int-vector-adder) ())))))

(define collect-int-vector-adder-meta-aux (term dont-rw)
  :returns (mv (res-terms rp-term-listp
                          :hyp (rp-termp term)
                          :hints (("Goal"
                                   :in-theory (e/d () (rp-termp)))))
               (res-dont-rw))
  :verify-guards nil
  :prepwork ((create-case-match-macro
              apply-of-int-vector-pattern
              ('apply$ ''int-vector-adder ('svl::4veclist-fix-wog ('cons x ('cons y ''nil))))))

  (case-match term
    (('int-vector-adder x y)
     (b* (((mv xs x-dont-rws)
           (collect-int-vector-adder-meta-aux x (dont-rw-car (dont-rw-cdr dont-rw))))
          ((mv ys y-dont-rws)
           (collect-int-vector-adder-meta-aux y (dont-rw-car (dont-rw-cdr (dont-rw-cdr dont-rw))))))
       (mv (append xs ys)
           (append x-dont-rws y-dont-rws))))
    (('rp & x)
     (collect-int-vector-adder-meta-aux x (dont-rw-car (dont-rw-cdr (dont-rw-cdr dont-rw)))))
    (&
     (b* (((mv k dont-rw)
           (case-match term
             (('svl::light-4vec-fix k)
              (mv k (dont-rw-car (dont-rw-cdr dont-rw))))
             (& (mv term dont-rw)))))
       (cond ((apply-of-int-vector-pattern-p k)
              (apply-of-int-vector-pattern-body
               k
               (b* ((dont-rw (dont-rw-car (dont-rw-cdr (dont-rw-cdr dont-rw))))
                    (dont-rw (dont-rw-car (dont-rw-cdr dont-rw)))
                    (x-dont-rw (dont-rw-car (dont-rw-cdr dont-rw)))
                    (dont-rw (dont-rw-car (dont-rw-cdr (dont-rw-cdr dont-rw))))
                    (y-dont-rw (dont-rw-car (dont-rw-cdr dont-rw)))
                    ((mv xs x-dont-rws)
                     (collect-int-vector-adder-meta-aux x x-dont-rw))
                    ((mv ys y-dont-rws)
                     (collect-int-vector-adder-meta-aux y y-dont-rw)))
                 (mv (append xs ys)
                     (append x-dont-rws y-dont-rws)))
               ))
             (t
              (mv (list term) (list dont-rw)))))))
  ///
  (defret true-listp-of-<fn>
    (and (true-listp res-terms)
         (true-listp res-dont-rw))
    :hints (("Goal"
             :in-theory (e/d () (rp-term-listp
                                 ;; RP-TERM-LISTP-OF-COLLECT-INT-VECTOR-ADDER-META-AUX
                                 RP-TERMP-CADR
                                 ACL2::SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP
                                 RP-TERMP
                                 RP-TERM-LISTP-IS-TRUE-LISTP)))))

  (verify-guards collect-int-vector-adder-meta-aux)

  (defret <fn>-correct
    (implies (and (find-adders-in-svex-formula-checks state)
                  (apply$-warrant-int-vector-adder)
                  (rp-evl-meta-extract-global-facts))
             (equal (int-vector-adder-lst (rp-evlt-lst res-terms a))
                    (int-vector-adder (rp-evlt term a) 0)))
    :hints (("Goal"
             :do-not-induct t
             :induct (collect-int-vector-adder-meta-aux term dont-rw)
             :in-theory (e/d* (INT-VECTOR-ADDER
                               sum
                               INT-VECTOR-ADDER-LST
                               REGULAR-EVAL-LEMMAS)
                              (RP-EVL-OF-APPLY$-WARRANT-INT-VECTOR-ADDER-WHEN-FIND-ADDERS-IN-SVEX-FORMULA-CHECKS-SMALL
                               SVL::HAS-INTEGERP-RP-IS-CORRECT
                               valid-sc
                               VALID-SC-CADR
                               rp-trans ifix)))))

  (defret <fn>-valid-sc
    (implies (valid-sc term a)
             (valid-sc-subterms res-terms a))
    :hints (("goal"
             :do-not-induct t
             :induct (collect-int-vector-adder-meta-aux term dont-rw)
             :in-theory (e/d* (valid-sc-single-step
                               is-rp is-if is-equals
                               apply-of-int-vector-pattern-p)
                              (ifix))))))

(define collect-int-vector-adder-meta (term dont-rw (context true-listp))
  :prepwork ((local
              (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))
             (local
              (defthm rp-termp-of-trans-list
                (implies (rp-term-listp lst)
                         (rp::rp-termp (rp::trans-list lst))))))
  :returns (mv (res-term rp-termp :hyp (rp-termp term))
               (res-dont-rw))
  (b* (((Unless (case-match term
                  (('int-vector-adder & &) t)
                  (('apply$ ''int-vector-adder &) t)
                  ))
        (mv term dont-rw))
       (warrant '(apply$-warrant-int-vector-adder))
       ((unless (member-equal warrant context))
        (mv term (raise "A necessary warrant is not found in the context: ~p0 ~%" warrant)))
       ((mv terms dont-rws)
        (collect-int-vector-adder-meta-aux term dont-rw))

       ;;(- (cw "Terms size: ~p0 ~%" (len terms)))
       ;;(- (cwe "Input term: ~p0 ~%" term))
       )
    (mv `(int-vector-adder-lst ;;(list . ,terms)
          ,(trans-list terms)
          )
        `(nil ;;(list . ,dont-rws)
          ,(trans-list dont-rws)
          )))
  ///

  (local
   (defthm member-equal-and-eval-and-all
     (implies (and (eval-and-all context a)
                   (member-equal x context))
              (and (rp-evlt x a)
                   (implies (force (not (include-fnc x 'list)))
                            (rp-evl x a))))
     :rule-classes (:rewrite)))

  (Local
   (defthm rp-evlt-of-list
     (equal (rp-evlt (cons 'list rest) a)
            (rp-evlt-lst rest a))))

  (defret <fn>-correct
    (implies (and (find-adders-in-svex-formula-checks state)
                  (eval-and-all context a)
                  (rp-evl-meta-extract-global-facts))
             (equal (rp-evlt res-term a)
                    (rp-evlt term a)))
    :hints (("Goal"
             :use
             ((:instance COLLECT-INT-VECTOR-ADDER-META-AUX-CORRECT)
              (:instance
               RP-EVL-OF-APPLY$-WARRANT-INT-VECTOR-ADDER-WHEN-FIND-ADDERS-IN-SVEX-FORMULA-CHECKS-SMALL
               (cmr::env a)))
             :do-not-induct t
             :in-theory (e/d* (int-vector-adder
                               sum
                               int-vector-adder-lst
                               regular-eval-lemmas)
                              (RP-EVL-OF-APPLY$-WARRANT-INT-VECTOR-ADDER-WHEN-FIND-ADDERS-IN-SVEX-FORMULA-CHECKS-SMALL
                               COLLECT-INT-VECTOR-ADDER-META-AUX-CORRECT
                               eval-and-all ifix rp-trans)))))

  (defret <fn>-valid-sc
    (implies (valid-sc term a)
             (valid-sc res-term a))
    :hints (("goal"
             :do-not-induct t
             :in-theory (e/d* (is-rp is-if is-equals)
                              ())))))
(rp::add-meta-rule
 :meta-fnc collect-int-vector-adder-meta
 :trig-fnc int-vector-adder
 :valid-syntaxp t
 :formula-checks find-adders-in-svex-formula-checks
 :returns (mv term dont-rw)
 :rw-direction :outside-in
 :hints (("Goal"
          :do-not-induct t
          :use ((:instance collect-int-vector-adder-meta-correct))
          :in-theory (e/d () ()))))

(rp::add-meta-rule
 :meta-fnc collect-int-vector-adder-meta
 :trig-fnc apply$
 :valid-syntaxp t
 :formula-checks find-adders-in-svex-formula-checks
 :returns (mv term dont-rw)
 :rw-direction :outside-in
 :hints (("Goal"
          :do-not-induct t
          :use ((:instance collect-int-vector-adder-meta-correct))
          :in-theory (e/d () ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; now unto summations.

(define int-vector-adder-lst-meta-aux (args)
  :returns (mv (s-args rp-termp :hyp (rp-term-listp args))
               s-args-dont-rw
               (r-args rp-term-listp :hyp (rp-term-listp args))
               r-args-dont-rw
               shiftable)
  (if (atom args)
      (mv ''nil nil
          nil nil nil)
    (b* (((mv s-args s-args-dont-rw r-args r-args-dont-rw shiftable)
          (int-vector-adder-lst-meta-aux (cdr args)))
         (arg (car args))

         (s-arg `(sv::4vec-part-select '0 '1 ,arg))
         (s-arg-dont-rw `(nil t t t))
         (r-arg `(sv::4vec-rsh '1 ,arg))
         (r-arg-dont-rw `(nil t t))

         ;; if at  least one  of the  arg is not  easily shiftable,  then don't
         ;; bother  because   it  will  cause  indefinite   expansion  of  this
         ;; function. The  hope here is  that there  is a partselect  out there
         ;; somewhere that will make the "unshifted" portion irrelevant.
         (shiftable (or*-exec shiftable
                              (and*-exec (consp arg)
                                         (equal (car arg) 'svl::4vec-concat$))
                              (binary-fnc-p arg)
                              (has-bitp-rp arg)
                              (and*-exec (consp arg)
                                         (equal (car arg) 'svl::bits)))))
      (mv `(cons ,s-arg ,s-args)
          `(cons ,s-arg-dont-rw ,s-args-dont-rw)
          (cons r-arg r-args)
          (cons r-arg-dont-rw r-args-dont-rw)
          shiftable)))

  ///

  )

(defthm rp-term-listp-of-remove-equal
  (implies (rp-term-listp lst)
           (rp-term-listp (remove-equal rm lst))))

(define int-vector-adder-lst-meta ((term rp-termp))
  :returns (mv (res-term rp-termp :hyp (rp-termp term))
               dont-rw)
  ;; !!!!! When deciding to  verify this meta function make sure  to change the
  ;; !!!!! collect-int-vector-adder-meta function to return a list object instead
  ;; !!!!! of a cons object.
  (case-match term
    (('int-vector-adder-lst ('list . lst))
     (b* ((lst (remove-equal ''0 lst))
          ((unless lst) (mv `(int-vector-adder-lst 'nil) `(nil t)))
          ((mv s-args s-args-dont-rw r-args r-args-dont-rw shiftable)
           (int-vector-adder-lst-meta-aux lst))

          ((Unless shiftable) (mv term nil))

          ;;(- (cw "int-vector-adder-lst in int-vector-adder-lst-meta generated ~p0 nodes~%" (cons-count
          )
       (mv `(svl::4vec-concat$
             '1
             (s-spec ,s-args)
             (int-vector-adder-lst-w/carry (list . ,r-args)
                                           (c-spec ,s-args)))
           `(svl::4vec-concat$
             t
             (s-spec ,s-args-dont-rw)
             (int-vector-adder-lst-w/carry (list . ,r-args-dont-rw)
                                           (c-spec ,s-args-dont-rw))))))
    (('int-vector-adder-lst-w/carry ('list . lst) carry)
     (b* ((lst (remove-equal ''0 lst))
          ((unless lst) (mv `(int-vector-adder-lst-w/carry 'nil ,carry) `(nil t t)))
          ((mv s-args s-args-dont-rw r-args r-args-dont-rw shiftable)
           (int-vector-adder-lst-meta-aux lst))
          ((Unless shiftable) (mv term nil)))
       (mv `(svl::4vec-concat$
             '1
             (s-spec (cons ,carry ,s-args))
             (int-vector-adder-lst-w/carry (list . ,r-args)
                                           (c-spec (cons ,carry ,s-args))))
           `(svl::4vec-concat$
             t
             (s-spec (cons t ,s-args-dont-rw))
             (int-vector-adder-lst-w/carry (list . ,r-args-dont-rw)
                                           (c-spec (cons t ,s-args-dont-rw)))))))
    (& (mv term nil))))

(progn
  (defun was-full-adder (x)
    (declare (ignorable x))
    t)
  (defthm was-full-adder-thm
    (was-full-adder (full-adder x y z)))

  (defun was-half-adder (x)
    (declare (ignorable x))
    t)

  (defthm was-half-adder-thm
    (was-half-adder (half-adder x y))))

(progn
  ;; Rw rules to open
  (def-rp-rule int-vector-adder-lst-w/carry-no-lst
    (implies (integerp carry)
             (equal (int-vector-adder-lst-w/carry nil carry)
                    carry))
    :hints (("Goal"
             :in-theory (e/d (int-vector-adder-lst-w/carry
                              int-vector-adder)
                             ()))))

  (def-rp-rule int-vector-adder-lst-opener
    (and (equal (int-vector-adder-lst (cons x rest))
                (+ (ifix (sv::4vec-fix x))
                   (int-vector-adder-lst rest)))
         )
    :hints (("goal"
             :in-theory (e/d (int-vector-adder-lst
                              int-vector-adder) ()))))

  (def-rp-rule int-vector-adder-lst-opener-3-elements
    (and (equal (int-vector-adder-lst (list x y z))
                (+ (ifix (sv::4vec-fix x))
                   (ifix (sv::4vec-fix y))
                   (ifix (sv::4vec-fix z))))
         )
    :rw-direction :both
    :hints (("goal"
             :in-theory (e/d (int-vector-adder-lst
                              int-vector-adder) ()))))

  (def-rp-rule int-vector-adder-lst-opener-3-bitp
    (implies (and (bitp x) (bitp y) (bitp z))
             (equal (int-vector-adder-lst (list x y z))
                    (full-adder x y z)
                    ))
    :rw-direction :both
    :hints (("Goal"
             :in-theory (e/d (bitp) ()))))
  (rp-attach-sc int-vector-adder-lst-opener-3-bitp
                was-full-adder-thm)

  (def-rp-rule int-vector-adder-lst-opener-4-bitp
    (implies (and (bitp x1) (bitp x2) (bitp x3) (bitp x4))
             (equal (int-vector-adder-lst (list x1 x2 x3 x4))
                    (b* ((res (full-adder x1 x2 x3)))
                      (2vec-adder res x4 0 3))
                    ))
    :rw-direction :both
    :hints (("Goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule int-vector-adder-lst-opener-5-bitp
    (implies (and (bitp x1) (bitp x2) (bitp x3) (bitp x4) (bitp x5))
             (equal (int-vector-adder-lst (list x1 x2 x3 x4 x5))
                    (b* ((res1 (full-adder x1 x2 x3)))
                      (2vec-adder res1 x4 x5 3))
                    ))
    :rw-direction :both
    :hints (("Goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule int-vector-adder-lst-opener-6-bitp
    (implies (and (bitp x1) (bitp x2) (bitp x3) (bitp x4) (bitp x5) (bitp x6))
             (equal (int-vector-adder-lst (list x1 x2 x3 x4 x5 x6))
                    (b* ((res1 (full-adder x1 x2 x3))
                         (res2 (full-adder x4 x5 x6)))
                      (2vec-adder res1 res2 0 3))
                    ))
    :rw-direction :both
    :hints (("Goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule int-vector-adder-lst-opener-7-bitp
    (implies (and (bitp x1) (bitp x2) (bitp x3) (bitp x4) (bitp x5) (bitp x6) (bitp x7))
             (equal (int-vector-adder-lst (list x1 x2 x3 x4 x5 x6 x7))
                    (b* ((res1 (full-adder x1 x2 x3))
                         (res2 (full-adder x4 x5 x6)))
                      (2vec-adder res1 res2 x7 3))
                    ))
    :rw-direction :both
    :hints (("Goal"
             :in-theory (e/d (bitp) ()))))


  (def-rp-rule int-vector-adder-lst-half-1
    (implies (and (bitp x)
                  (bitp y))
             (equal (svl::bits (+ x y) start size)
                    (svl::bits (half-adder x y)
                               start size)))

    :hints (("Goal"
             :in-theory (e/d (bitp) ()))))
  (rp-attach-sc int-vector-adder-lst-half-1
                was-half-adder-thm)

  (def-rp-rule int-vector-adder-lst-half-2
    (implies (and (bitp x)
                  (bitp y))
             (equal (sv::4vec-rsh size (+ x y))
                    (sv::4vec-rsh size (half-adder x y))))

    :hints (("Goal"
             :in-theory (e/d (bitp) ()))))
  (rp-attach-sc int-vector-adder-lst-half-2
                was-half-adder-thm)

  (def-rp-rule int-vector-adder-lst-half-3
    (implies (and (bitp x)
                  (bitp y))
             (equal (SV::4VEC-XDET (+ x y))
                    (SV::4VEC-XDET (half-adder x y))))

    :hints (("Goal"
             :in-theory (e/d (bitp) ()))))

  (rp-attach-sc int-vector-adder-lst-half-3
                was-half-adder-thm)

  (def-rp-rule int-vector-adder-lst-carry-opener
    (and (equal (int-vector-adder-lst-w/carry lst carry)
                (+ (ifix (sv::4vec-fix carry))
                   (int-vector-adder-lst lst)))
         )
    :hints (("goal"
             :in-theory (e/d (int-vector-adder-lst-w/carry
                              int-vector-adder) ())))))

;; !!!!! When  deciding   to  prove  the   below,  make  sure  to   change  the
;; !!!!! collect-int-vector-adder-meta function to return a list object instead
;; !!!!! of a cons object.

;; #!RP
;; (skip-proofs
;;  (progn

;;    (rp::add-meta-rule
;;     :meta-fnc int-vector-adder-lst-meta
;;     :trig-fnc int-vector-adder-lst-w/carry
;;     :valid-syntaxp t
;;     :formula-checks find-adders-in-svex-formula-checks
;;     :returns (mv term dont-rw)
;;     )

;;    (rp::add-meta-rule
;;     :meta-fnc int-vector-adder-lst-meta
;;     :trig-fnc int-vector-adder-lst
;;     :valid-syntaxp t
;;     :formula-checks find-adders-in-svex-formula-checks
;;     :returns (mv term dont-rw)
;;     )

;;    ))

;; These rules might be necessary.........
;; #!rp
;; (skip-proofs
;;  (def-rp-rule bits-0-1-of-s-c-res
;;    (equal (svl::bits (s-c-res x y z) 0 1)
;;           (s-spec (list (s-c-res x y z))))))

;; #!rp
;; (skip-proofs
;;  (def-rp-rule bits-posp-start-size=1--of-s-c-res
;;    (implies (posp start)
;;             (equal (svl::bits (s-c-res x y z) start 1)
;;                    (svl::bits (cc (s-c-res x y z)) (1- start) 1)))))

;; (rp::attach-meta-fncs svl-mult-rules2)
