; Use Rp-rewriter, then FGL as clause-processors (and some other things in between)
;
; Copyright (C) 2021 Centaur Technology
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
; Original author: Mertcan Temel <mert@centtech.com>

(in-package "RP")

(include-book "fnc-defs")

;;(include-book "svl-top")

(local
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

(local
 (include-book "lemmas"))

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

(encapsulate
  nil

  (local
   (in-theory (e/d (fix)
                   (+-IS-SUM
                    ACL2::BINARY-LOGAND
                    FLOOR2-IF-F2
                    S-SPEC-IS-M2
                    ;;EQUAL-SIDES-TO-S
                    SUM-LIST-IS-SUM
                    C-IS-F2
                    s-is-m2))))

  (local
   (defthm fix-of-number
     (implies (force (acl2-numberp x))
              (equal (fix x) x))))

  (with-output
    :off :all
    :gag-mode nil

    (def-formula-checks
      make-sc-fgl-ready-meta-formula-checks
      (binary-append
       ifix
       acl2::logcar$inline
       acl2::logcdr$inline
       acl2::logbit

       --
       sum-list
       binary-and
       and-list

       bit-of
       ;; svl::bits
       ;; svl::4vec-bitand
       ;; svl::4vec-bitor
       ;; svl::4vec-?
       ;; svl::4vec-?*
       ;; sv::4vec-bitxor
       ;; svl::4vec-bitnot
       ;; svl::4vec-bitnot$

       binary-?
       binary-xor
       binary-or
       binary-not
       bit-fix
       s-c-res
       c

       s
       pp
       binary-sum
       ;;sv::3vec-fix
       bit-concat
       ;;svl::4vec-concat
       ;;svl::4vec-concat$
       logapp
       ;;sv::4vec-fix
       ))))

;; (define has-integerp-rp (term)
;;   :measure (cons-count term)
;;   :hints
;;   (("goal" :in-theory (e/d (is-rp
;;                             measure-lemmas)
;;                            nil)))
;;   :guard-hints
;;   (("goal" :in-theory (e/d (is-rp) nil)))
;;   (if (is-rp term)
;;       (or (equal (cadr term) ''integerp)
;;           (has-integerp-rp (caddr term)))
;;     nil))

(define sc-integer-termp ((term rp-termp))
  (b* ((?orig term)
       (term (ex-from-rp term)))
    (or (case-match term
          (('s & & &) t)
          (('ACL2::LOGCAR$INLINE & ) t)
          (('ACL2::LOGCdR$INLINE & ) t)
          (('c & & & &) t)
          (('binary-sum & &) t)
          (('and-list & &) t)
          (('logapp & & &) t)
          (('quote term) (integerp term)))
        ;;(has-integerp-rp orig)
        (binary-fnc-p term))))

(acl2::defines
 make-sc-fgl-ready-meta
 :hints (("Goal"
          :in-theory (e/d ()
                          (ex-from-rp))))
 :prepwork ((local
             (in-theory (e/d (measure-lemmas)
                             (FALIST-CONSISTENT))))
            (local
             (defthm dummy-lemma0
               (IMPLIES (AND
                         (CONSP (EX-FROM-RP TERM)))
                        (O< 1 (CONS-COUNT TERM)))
               :hints (("Goal"
                        :do-not-induct t
                        :induct (EX-FROM-RP TERM)
                        :expand ((CONS-COUNT TERM))
                        :in-theory (e/d (ex-from-rp
                                         cons-count)
                                        (+-IS-SUM))))))
            (local
             (defthm dummy-lemma1
               (and (implies (and
                              (not (consp (ex-from-rp term)))
                              (rp-termp term))
                             (symbolp (ex-from-rp term)))
                    (implies (and
                              (rp-termp term))
                             (ex-from-rp term)))
               :hints (("Goal"
                        :in-theory (e/d (rp-termp ex-from-rp)
                                        ())))))

            (local
             (defthm rp-termp-of-trans-list
               (implies (rp-term-listp lst)
                        (rp-termp (trans-list lst)))
               :hints (("Goal"
                        :do-not-induct t
                        :induct (trans-list lst)
                        :in-theory (e/d () ())))))

            )

 :returns-hints (("Goal"
                  :do-not-induct t
                  :expand ((:free (x y)
                                  (rp-termp (cons x y))))
                  :in-theory (e/d () (rp-termp
                                      ex-from-rp)
                                  )))

 :flag-defthm-macro defthm-make-sc-fgl-ready-meta
 :flag-local nil

 (define make-sc-fgl-ready-meta ((term rp-termp))
   :returns (res rp-termp :hyp (rp-termp term))
   :measure (cons-count term)
   :verify-guards nil
   (b* ((term (ex-from-rp$ term)))
     (case-match term
       (('s & pp c)
        `(acl2::logcar$inline (binary-sum (sum-list ,(make-sc-fgl-ready-meta pp))
                                          (sum-list ,(make-sc-fgl-ready-meta c)))))
       (('c & s pp c)
        `(acl2::logcdr$inline (binary-sum
                               (sum-list ,(make-sc-fgl-ready-meta s))
                               (binary-sum (sum-list ,(make-sc-fgl-ready-meta pp))
                                           (sum-list ,(make-sc-fgl-ready-meta c))))))
       (('bit-of x index)
        `(acl2::logbit$inline ,index ,(make-sc-fgl-ready-meta x)))

       (('quote . &)
        term)
       (('falist . &)
        term)
       (('list . lst)
        (trans-list (make-sc-fgl-ready-meta-lst lst)))
       (('if a b c) ;; just to make proofs a little bit easier.
        `(if ,(make-sc-fgl-ready-meta a)
             ,(make-sc-fgl-ready-meta b)
           ,(make-sc-fgl-ready-meta c)))
       ((fnc . args)
        `(,fnc . ,(make-sc-fgl-ready-meta-lst args)))
       (& term))))
 (define make-sc-fgl-ready-meta-lst ((lst rp-term-listp))
   :returns (res-lst rp-term-listp :hyp (rp-term-listp lst))
   :measure (cons-count lst)
   (if (atom lst)
       nil
     (cons-with-hint (make-sc-fgl-ready-meta (car lst))
                     (make-sc-fgl-ready-meta-lst (cdr lst))
                     lst)))
 ///
 (verify-guards make-sc-fgl-ready-meta-lst))

(define make-sc-fgl-ready-meta-main ((term rp-termp))
  :returns (mv (res rp-termp :hyp (rp-termp term))
               (dont-rw))
  (mv (make-sc-fgl-ready-meta term) t))

;;;

(local
 (progn
   (defthmd RP-EVLt-OF-FNCALL-ARGS
     (implies (and (Not (equal fn 'quote))
                   (Not (equal fn 'list))
                   (Not (equal fn 'falist)))
              (equal (rp-evlt (cons fn args) a)
                     (RP-EVL (CONS FN (KWOTE-LST (RP-EVLT-LST ARGS A)))
                             NIL)))
     :hints (("Goal"
              :expand ((:free (args)
                              (rp-trans (cons fn args))))
              :in-theory (e/d (RP-EVL-OF-FNCALL-ARGS
                               rp-trans)
                              ()))))

   (defthmd RP-EVL-OF-FNCALL-ARGS2
     (implies (and (Not (equal fn 'quote))
                   )
              (equal (rp-evl (cons fn args) a)
                     (RP-EVL (CONS FN (KWOTE-LST (RP-EVL-LST ARGS A)))
                             NIL)))
     :hints (("Goal"
              :expand ((:free (args)
                              (rp-trans (cons fn args))))
              :in-theory (e/d (RP-EVL-OF-FNCALL-ARGS
                               rp-trans)
                              ()))))

   (in-theory (e/d (rp-trans)
                   (bitp
                    LOGBITP
                    acl2::logcar
                    acl2::logcdr
                    logbit
                    logapp
                    )))

   (create-regular-eval-lemma acl2::logbit$inline 2 make-sc-fgl-ready-meta-formula-checks)
   (create-regular-eval-lemma acl2::logcar$inline 1 make-sc-fgl-ready-meta-formula-checks)
   (create-regular-eval-lemma acl2::logcdr$inline 1 make-sc-fgl-ready-meta-formula-checks)
   ;; (create-regular-eval-lemma svl::4vec-concat$ 3
   ;;                            make-sc-fgl-ready-meta-formula-checks)
   ;; (create-regular-eval-lemma svl::4vec-concat 3
   ;;                            make-sc-fgl-ready-meta-formula-checks)
   (create-regular-eval-lemma logapp 3 make-sc-fgl-ready-meta-formula-checks)

   (defthm
     bit-of-is-logbit
     (implies t
              (equal (rp::bit-of x index)
                     (logbit index x)))
     :hints (("Goal"                             ;
              :in-theory (e/d (rp::bit-of) ()))) ;
     )

   (defthm s-is-logcar
     (implies t
              (equal (s hash pp c)
                     (acl2::logcar (sum (sum-list pp) (sum-list c)))))
     :hints (("Goal"
              :in-theory (e/d (s
                               acl2::logcar)
                              ()))))

   (defthm c-is-logcdr
     (implies t
              (equal (c hash s pp c)
                     (acl2::logcdr (sum (sum-list s)
                                        (sum-list pp)
                                        (sum-list c)))))
     :hints (("Goal"
              :in-theory (e/d (c
                               f2
                               acl2::logcdr)
                              ()))))

   #|(defthm 4vec-concat$-is-logapp
     (implies (and (natp a)
                   (integerp x)
                   (integerp y))
              (equal (svl::4vec-concat$ a x y)
                     (logapp a x y)))
     :hints (("Goal"
              :in-theory (e/d (SVL::LOGAPP-TO-4VEC-CONCAT
                               svl::4vec-concat$)
                              (logapp)))))||#

   (defthmd rp-evlt-of-ex-from-rp-reverse
     (and (implies (syntaxp (atom term))
                   (equal (rp-evl (rp-trans term) a)
                          (rp-evl (rp-trans (ex-from-rp term)) a)))
          ))

   (defthmd valid-sc-of-ex-from-rp-reverse
     (implies (syntaxp (atom term))
              (equal (valid-sc term a)
                     (and (EVAL-AND-ALL (CONTEXT-FROM-RP TERM NIL)
                                        A)
                          (valid-sc (ex-from-rp term) a))))
     :hints (("Goal"
              :expand ((VALID-SC TERM A)
                       (CONTEXT-FROM-RP TERM NIL))
              :do-not-induct t
              :in-theory (e/d (valid-sc
                               is-if
                               is-rp)
                              (;;EVAL-AND-ALL
                               ;;context-from-rp
                               )))))

   (create-regular-eval-lemma binary-sum 2 make-sc-fgl-ready-meta-formula-checks)
   (create-regular-eval-lemma c 4 make-sc-fgl-ready-meta-formula-checks)
   (create-regular-eval-lemma s 3 make-sc-fgl-ready-meta-formula-checks)
   (create-regular-eval-lemma BINARY-? 3 make-sc-fgl-ready-meta-formula-checks)
   (create-regular-eval-lemma BINARY-xor 2 make-sc-fgl-ready-meta-formula-checks)
   (create-regular-eval-lemma BINARY-and 2 make-sc-fgl-ready-meta-formula-checks)
   (create-regular-eval-lemma BINARY-or 2 make-sc-fgl-ready-meta-formula-checks)
   (create-regular-eval-lemma BINARY-not 1 make-sc-fgl-ready-meta-formula-checks)
   (create-regular-eval-lemma and-list 2 make-sc-fgl-ready-meta-formula-checks)

   (defthm sc-integer-termp-is-correct
     (implies (and (rp-evl-meta-extract-global-facts :state state)
                   (make-sc-fgl-ready-meta-formula-checks state)
                   (sc-integer-termp term)
                   )
              (integerp (rp-evlt term a)))
     :hints (("goal"
              :in-theory (e/d* (sc-integer-termp
                                binary-fnc-p
                                rp-evlt-of-ex-from-rp-reverse
                                regular-eval-lemmas
                                regular-eval-lemmas-with-ex-from-rp)
                               (rp-trans
                                evl-of-extract-from-rp
                                rp-evlt-of-ex-from-rp)))))

   (defthm dummy-integerp-chain
     (implies (and (equal (rp-evlt (MAKE-SC-FGL-READY-META x) a)
                          (rp-evlt x a))
                   (rp-evl-meta-extract-global-facts :state state)
                   (make-sc-fgl-ready-meta-formula-checks state)
                   (SC-INTEGER-TERMP (MAKE-SC-FGL-READY-META x)))
              (integerp (rp-evlt x a)))
     :hints (("Goal"
              :use ((:instance SC-INTEGER-TERMP-is-correct
                               (term x)))
              :in-theory (e/d () ()))))

   (defret-mutual make-sc-fgl-ready-meta-correct
     (defret make-sc-fgl-ready-meta-correct
       (implies (and (rp-evl-meta-extract-global-facts :state state)
                     (make-sc-fgl-ready-meta-formula-checks state)
                     ;;(valid-sc term a)
                     )
                (and (equal (rp-evlt res a)
                            (rp-evlt term a))
                     ;;(valid-sc res a)
                     ))
       :fn make-sc-fgl-ready-meta)

     (defret make-sc-fgl-ready-meta-lst-correct
       (implies (and (rp-evl-meta-extract-global-facts :state state)
                     (make-sc-fgl-ready-meta-formula-checks state)
                     ;;(valid-sc-subterms lst a)
                     )
                (and (equal (rp-evlt-lst res-lst a)
                            (rp-evlt-lst lst a))
                     ;; (valid-sc-subterms res-lst a)
                     ))
       :fn make-sc-fgl-ready-meta-lst)

     :hints (("Goal"
              :do-not-induct t

              :in-theory (e/d* (make-sc-fgl-ready-meta
                                make-sc-fgl-ready-meta-lst
                                RP-EVLt-OF-FNCALL-ARGS
                                RP-EVL-OF-FNCALL-ARGS
                                rp-evlt-of-ex-from-rp-reverse
                                regular-eval-lemmas
                                regular-eval-lemmas-with-ex-from-rp
                                )
                               (rp-evlt-of-ex-from-rp
                                (:DEFINITION EX-FROM-RP)
                                (:REWRITE NOT-INCLUDE-RP)
                                (:DEFINITION INCLUDE-FNC)
                                (:REWRITE DEFAULT-CDR)
                                (:DEFINITION INCLUDE-FNC-SUBTERMS)
                                (:REWRITE RP-EVL-OF-RP-EQUAL2)
                                (:REWRITE RP-TERMP-OF-RP-TRANS)
                                (:REWRITE
                                 RETURN-TYPE-OF-MAKE-SC-FGL-READY-META.RES)
                                (:DEFINITION RP-TERM-LISTP)
                                (:REWRITE IS-IF-RP-TERMP)
                                (:DEFINITION RP-TERMP)
                                rp-trans-is-term-when-list-is-absent)))))

   (defret make-sc-fgl-ready-metawhen-quoted
     (implies (and (case-match term (('QUOTE . &) t)))
              (equal res term))
     :fn make-sc-fgl-ready-meta
     :hints (("Goal"
              :in-theory (e/d (make-sc-fgl-ready-meta) ()))))

   (defret make-sc-fgl-ready-metawhen-consp
     (implies (consp lst)
              (equal res-lst (cons (make-sc-fgl-ready-meta (car lst))
                                   (make-sc-fgl-ready-meta-lst (cdr lst))
                                   )))
     :fn make-sc-fgl-ready-meta-lst
     :hints (("Goal"
              :in-theory (e/d (make-sc-fgl-ready-meta-lst) ()))))

   (defret-mutual make-sc-fgl-ready-meta-valid-sc
     (defret make-sc-fgl-ready-meta-valid-sc
       (implies (and (rp-evl-meta-extract-global-facts :state state)
                     (make-sc-fgl-ready-meta-formula-checks state)
                     (valid-sc term a)
                     (rp-termp term)
                     )
                (valid-sc res a))
       :fn make-sc-fgl-ready-meta)

     (defret make-sc-fgl-ready-meta-lst-valid-sc
       (implies (and (rp-evl-meta-extract-global-facts :state state)
                     (make-sc-fgl-ready-meta-formula-checks state)
                     (rp-term-listp lst)
                     (valid-sc-subterms lst a))
                (valid-sc-subterms res-lst a))
       :fn make-sc-fgl-ready-meta-lst)

     :hints (("Goal"
              :do-not-induct t
              :expand ((:free (x y)
                              (valid-sc (cons x y) a))
                       ;;(MAKE-SC-FGL-READY-META-LST (CDDR (EX-FROM-RP TERM)))
                       ;;(MAKE-SC-FGL-READY-META-LST (CDR (EX-FROM-RP TERM)))
                       ;;(MAKE-SC-FGL-READY-META TERM)
                       (VALID-SC (EX-FROM-RP TERM) A))
              :in-theory (e/d* (make-sc-fgl-ready-meta
                                make-sc-fgl-ready-meta-lst
                                RP-EVLt-OF-FNCALL-ARGS
                                RP-EVL-OF-FNCALL-ARGS
                                rp-evlt-of-ex-from-rp-reverse
                                regular-eval-lemmas
                                is-if
                                is-rp
                                regular-eval-lemmas-with-ex-from-rp
                                valid-sc-of-ex-from-rp-reverse
                                )
                               (rp-evlt-of-ex-from-rp
                                VALID-SC-OF-EX-FROM-RP
                                VALID-SC-EX-FROM-RP-2
                                (:DEFINITION EVAL-AND-ALL)
                                (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                                (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                                (:DEFINITION ACL2::APPLY$-BADGEP)
                                (:DEFINITION RP-TRANS)
                                (:DEFINITION EX-FROM-RP)
                                (:REWRITE NOT-INCLUDE-RP)
                                (:DEFINITION INCLUDE-FNC)
                                (:REWRITE DEFAULT-CDR)
                                (:DEFINITION INCLUDE-FNC-SUBTERMS)
                                (:REWRITE RP-EVL-OF-RP-EQUAL2)
                                (:REWRITE RP-TERMP-OF-RP-TRANS)
                                (:REWRITE DEFAULT-CAR)
                                (:REWRITE
                                 RETURN-TYPE-OF-MAKE-SC-FGL-READY-META.RES)
                                ;;(:DEFINITION RP-TERM-LISTP)
                                (:REWRITE IS-IF-RP-TERMP)
                                (:DEFINITION RP-TERMP)
                                rp-trans-is-term-when-list-is-absent)))))))

(memoize 'make-sc-fgl-ready-meta)

(add-postprocessor
 :processor-fnc make-sc-fgl-ready-meta
 :valid-syntaxp t
 :disabledp t
 :formula-checks make-sc-fgl-ready-meta-formula-checks
 :hints (("Goal"
          :in-theory (e/d (make-sc-fgl-ready-meta-main) ()))))
