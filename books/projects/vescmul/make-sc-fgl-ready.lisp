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
 (include-book "lemmas-2"))

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
                    logcons
                    expt
                    s-is-m2

                    rw-dir1
                    rw-dir2))))

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
       acl2::logbit$inline
       return-last
       --
       sum-list
       binary-and
       and-list

       acl2::logcons$inline

       logbit
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

       binary-xor
       binary-and
       binary-or
       binary-?
       binary-not
       and-list

       acl2::logbit$inline
       
       
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

(local
   (in-theory (e/d () (rw-dir1 rw-dir2))))

(defsection sum-list-optimized-meta

  

  (define sum-list-optimized-meta-aux (lst)
    :returns (mv (sum rp-term-listp :hyp (rp-term-listp lst))
                 (carry rp-term-listp :hyp (rp-term-listp lst)))
    (if (and (consp lst)
             (consp (cdr lst))
             (consp (cddr lst)))
        (b* ((sum `(binary-+ ,(car lst)
                            (binary-+ ,(cadr lst)
                                      ,(caddr lst))))
             (s `(acl2::logbit$inline '0 ,sum))
             (c `(acl2::logbit$inline '1 ,sum))
             ((mv rest-sum rest-carry)
              (sum-list-optimized-meta-aux (cdr (cddr lst)))))
          (mv (cons s rest-sum)
              (cons c rest-carry)))
      (mv lst nil)))

  (local
   (defret sum-list-optimized-meta-aux-measure-lemma
     (implies (and ;;(consp sum)
               ;;(consp (cdr sum))
               (consp (cddr sum)))
              (and (< (len sum)
                      (len lst))))
     :fn SUM-LIST-OPTIMIZED-META-AUX
     :hints (("Goal"
              :in-theory (e/d (SUM-LIST-OPTIMIZED-META-AUX
                               len)
                              (rw-dir1 rw-dir2 +-IS-SUM))))))

  (local
   (defret sum-list-optimized-meta-aux-measure-lemma2
     (implies (consp sum)
              (and (< (len carry)
                      (len lst))))
     :fn sum-list-optimized-meta-aux
     :hints (("goal"
              :expand ((sum-list-optimized-meta-aux (cdddr lst)))
              :in-theory (e/d (sum-list-optimized-meta-aux
                               len)
                              (rw-dir1 rw-dir2 +-is-sum))))))

  (defthm rp-termp-of-car-when-rp-term-listp
    (implies (and (consp lst)
                  (rp-term-listp lst))
             (and (rp-termp (car lst))
                  (implies (consp (cdr lst))
                           (rp-termp (cadr lst))))))

  (local
   (defthm --of-sum
     (equal (-- (sum x y))
            (sum (-- x) (-- y)))
     :hints (("Goal"
              :in-theory (e/d (sum --)
                              (+-IS-SUM))))))

  (local
   (defret <fn>-correct
     (implies (and (rp-evl-meta-extract-global-facts :state state)
                   (make-sc-fgl-ready-meta-formula-checks state)
                   (bit-listp (rp-evlt-lst lst a)))
              (and (equal (sum-list (rp-evlt-lst sum a))
                          (sum (sum-list (rp-evlt-lst lst a))
                               (-- (sum-list (rp-evlt-lst carry a)))
                               (-- (sum-list (rp-evlt-lst carry a)))))
                   (bit-listp (rp-evlt-lst carry a))
                   (bit-listp (rp-evlt-lst sum a))))
     :fn sum-list-optimized-meta-aux
     :hints (("Goal"
              :expand ((:free (x other)
                              (sum (cons 0 x) other)))
              :in-theory (e/d (BIT-LISTP
                               sum-list-optimized-meta-aux)
                              ())))))

  (local
   (defret <fn>-bit-listp
     (implies (and (rp-evl-meta-extract-global-facts :state state)
                   (make-sc-fgl-ready-meta-formula-checks state)
                   (bit-listp (rp-evlt-lst lst a)))
              (and (bit-listp (rp-evlt-lst carry a))
                   (bit-listp (rp-evlt-lst sum a))))
     :fn sum-list-optimized-meta-aux
     :hints (("Goal"
              :expand ((:free (x other)
                              (sum (cons 0 x) other)))
              :in-theory (e/d (BIT-LISTP
                               sum-list-optimized-meta-aux)
                              ())))))

  (local
   (defret <fn>-valid-sc
     (implies (valid-sc-subterms lst a)
              (and (valid-sc-subterms sum a)
                   (valid-sc-subterms carry a)))
     :fn sum-list-optimized-meta-aux
     :hints (("Goal"
              :expand ((:free (x) (valid-sc (cons 'binary-or x) a))
                       (:free (x) (valid-sc (cons 'LOGBIT$INLINE x) a))
                       (:free (x) (valid-sc (cons 'BINARY-+ x) a))
                       (:free (x) (valid-sc (cons 'binary-xor x) a))
                       (:free (x) (valid-sc (cons 'binary-and x) a)))
              :in-theory (e/d (sum-list-optimized-meta-aux
                               is-rp
                               is-if is-equals)
                              (valid-sc))))))

  (local
   (defret true-listp-of-<fn>
     (and (true-listp carry))
     :fn sum-list-optimized-meta-aux
     :hints (("Goal"
              :in-theory (e/d (sum-list-optimized-meta-aux) ())))))

  (define sum-list-optimized-meta-aux2 (lst)
    :returns (mv (sum rp-termp :hyp (rp-term-listp lst))
                 (carry rp-term-listp :hyp (rp-term-listp lst)))
    :measure (len lst)
    :hints (("Goal"
             :in-theory (e/d () (RW->-TO-GT
                                 RW-<-TO-LTE
                                 LT-TO-GT
                                 len +-IS-SUM))))
    :prepwork ()

    (b* (((mv lst carry-lst)
          (sum-list-optimized-meta-aux lst))
         ((when (atom lst))
          (mv ''0 carry-lst))
         ((when (and* (consp lst) (atom (cdr lst))))
          (mv (car lst) carry-lst))
         ((when (and* (consp lst) (consp (cdr lst)) (atom (cddr lst))))
          (mv `(binary-xor ,(car lst) ,(cadr lst))
              (cons `(binary-and ,(car lst) ,(cadr lst))
                    carry-lst)))
         ((mv sum carry-lst2)
          (sum-list-optimized-meta-aux2 lst)))
      (mv sum (acl2::append-without-guard carry-lst carry-lst2))))

  #|(local
  (defret <fn>-measure-lemma2
  (implies (consp carry)
  (and (< (len carry)
  (len lst))))
  :fn sum-list-optimized-meta-aux2
  :hints (("goal"
  :in-theory (e/d (sum-list-optimized-meta-aux2
  SUM-LIST-OPTIMIZED-META-AUX
  len)
  (
  rw-dir1 rw-dir2 +-is-sum))
  :use ((:instance sum-list-optimized-meta-aux-measure-lemma)
  (:instance sum-list-optimized-meta-aux-measure-lemma2))))))|#

  (local
   (defthm rp-evlt-lst-of-append
     (equal (rp-evlt-lst (append x y) a)
            (append (rp-evlt-lst x a)
                    (rp-evlt-lst y a)))))

  (local
   (defret bitp-of-car-of-<fn>
     (implies (and (rp-evl-meta-extract-global-facts :state state)
                   (make-sc-fgl-ready-meta-formula-checks state)
                   (bit-listp (rp-evlt-lst lst a)))
              (and (implies (consp sum)
                            (bitp (rp-evlt (car sum) a)))
                   (implies (and (consp sum)
                                 (consp (cdr sum)))
                            (bitp (rp-evlt (cadr sum) a)))
                   (implies (and (consp sum)
                                 (consp (cdr sum))
                                 (consp (cddr sum)))
                            (bitp (rp-evlt (caddr sum) a)))))
     :fn sum-list-optimized-meta-aux
     :hints (("Goal"
              :use ((:instance <fn>-correct))
              :in-theory (e/d (BIT-LISTP)
                              (bitp <fn>-correct))))))

  (local
   (defthm dummy-sum-lemma
     (and (equal (equal (sum x1 x2 x3 a b) (sum y1 y2 y3 a b))
                 (equal (sum x1 x2 x3) (sum y1 y2 y3)))
          (equal (equal (sum x1 x2 x3 x4 a b) (sum y1 y2 y3 a b))
                 (equal (sum x1 x2 x3 x4) (sum y1 y2 y3))))))

  (local
   (defthm rw-binary-xor
     (implies (and (bitp x)
                   (bitp y))
              (equal (binary-xor x y)
                     (sum x y
                          (-- (and$ x y))
                          (-- (and$ x y)))))))

  (local
   (defthm ifix-when-bitp
     (implies (bitp x)
              (equal (ifix x) x))))

  (local
   (defret <fn>-correct
     (implies (and (rp-evl-meta-extract-global-facts :state state)
                   (make-sc-fgl-ready-meta-formula-checks state)
                   (bit-listp (rp-evlt-lst lst a)))
              (equal (rp-evlt sum a)
                     (sum (sum-list (rp-evlt-lst lst a))
                          (-- (sum-list (rp-evlt-lst carry a)))
                          (-- (sum-list (rp-evlt-lst carry a))))))
     :fn sum-list-optimized-meta-aux2
     :hints (("Goal"
              :do-not-induct t
              :induct (<fn> lst)
              :expand ((:free (x other)
                              (sum (cons 0 x) other)))
              :in-theory (e/d (BIT-LISTP
                               sum-list-optimized-meta-aux2)
                              (sum-list-optimized-meta-aux-correct
                               )))
             (and stable-under-simplificationp
                  '(:use ((:instance sum-list-optimized-meta-aux-correct
                                     )
                          (:instance bitp-of-car-of-sum-list-optimized-meta-aux
                                     )))))))

  (local
   (defret <fn>-valid-sc
     (implies (valid-sc-subterms lst a)
              (and (valid-sc sum a)
                   (valid-sc-subterms carry a)))
     :fn sum-list-optimized-meta-aux2
     :hints (("goal"
              :expand ((:free (x) (valid-sc (cons 'binary-or x) a))
                       (:free (x) (valid-sc (cons 'binary-xor x) a))
                       (:free (x) (valid-sc (cons 'binary-and x) a)))
              :in-theory (e/d (sum-list-optimized-meta-aux2
                               is-rp
                               is-if is-equals)
                              (valid-sc
                               sum-list-optimized-meta-aux-valid-sc)))
             (and stable-under-simplificationp
                  '(:use ((:instance
                           sum-list-optimized-meta-aux-valid-sc)))))))

  (local
   (defthm bit-listp-of-append
     (implies t
              (equal (bit-listp (append x y))
                     (and (bit-listp (true-list-fix x))
                          (bit-listp y))))
     :hints (("Goal"
              :in-theory (e/d (bit-listp) ())))))

  (local
   (defthm true-listp-of-rp-evlt-lst
     (implies (true-listp lst)
              (true-listp (rp-evlt-lst lst a)))))

  (local
   (defret bit-listp-of-<fn>
     (implies (and (rp-evl-meta-extract-global-facts :state state)
                   (make-sc-fgl-ready-meta-formula-checks state)
                   (bit-listp (rp-evlt-lst lst a)))
              (and (bitp (rp-evlt sum a))
                   (bit-listp (rp-evlt-lst carry a))))
     :fn sum-list-optimized-meta-aux2
     :hints (("Goal"
              :in-theory (e/d (BIT-LISTP
                               sum-list-optimized-meta-aux2)
                              (sum-list-optimized-meta-aux-correct
                               sum-list-optimized-meta-aux2-correct
                               bitp
                               RW-BINARY-XOR)))
             (and stable-under-simplificationp
                  '(:use ((:instance sum-list-optimized-meta-aux-bit-listp)))))))

  (define sum-list-optimized-meta (lst
                                   &optional
                                   ((limit natp) '(expt 2 20)))
    :measure (nfix limit)

    :hints (("Goal"
             :in-theory (e/d ()
                             (rw-dir1 rw-dir2 len
                                      +-IS-SUM))))
    :returns (res-term rp-termp :hyp (rp-term-listp lst))
    (b* (((when (zp limit)) `(sum-list ,(trans-list lst)))
         ((when (atom lst)) ''0)
         ((mv sum carry-lst)
          (sum-list-optimized-meta-aux2 lst)))
      `(acl2::logcons$inline ,sum
                             ,(sum-list-optimized-meta carry-lst (1- limit)))))


  (local
   (defthm logcons-rw
     (implies (bitp x)
              (equal (logcons x y)
                     (sum x y y)))
     :hints (("Goal"
              :in-theory (e/d (BIT-FIX sum)
                              (+-IS-SUM))))))
  
  (defret <fn>-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (make-sc-fgl-ready-meta-formula-checks state)
                  (bit-listp (rp-evlt-lst lst a)))
             (equal (rp-evlt res-term a)
                    (sum-list (rp-evlt-lst lst a))))
    :fn sum-list-optimized-meta
    :hints (("Goal"
             :in-theory (e/d (sum-list-optimized-meta)
                             (bitp logcons bit-listp)))
            (and stable-under-simplificationp
                 '(:use ((:instance
                          bit-listp-of-sum-list-optimized-meta-aux2))))))

  (defret <fn>-valid-sc
    (implies (valid-sc-subterms lst a)
             (valid-sc res-term a))
    :fn sum-list-optimized-meta
    :hints (("Goal"
             :in-theory (e/d (IS-EQUALS
                              is-rp is-if
                              sum-list-optimized-meta)
                             ()))))

  )

;; (sum-list-optimized-meta '(x1 x2 x3 x4 x5 x6))



(define bit-listp-of-pp-terms (lst)
  :progn t
  :returns res
  (if (atom lst)
      (equal lst nil)
    (and (or ;;(has-bitp-rp (car lst))
             (binary-fnc-p (car lst))
             (and-list-p (car lst))
             (single-s-p (car lst)))
         (bit-listp-of-pp-terms (cdr lst))))
  ///

  (local
   (defthm has-bitp-rp-implies
     (implies (and (has-bitp-rp x)
                   (valid-sc x a))
              (bitp (rp-evlt x a)))
     :hints (("goal"
              :do-not-induct t
              :induct (has-bitp-rp x)
              :in-theory (e/d (valid-sc-single-step is-rp is-if is-equals
                                has-bitp-rp)
                              (bitp valid-sc))))))
  
  (local
   (defret <fn>-implies-bit-lisp
     (implies (and res
                   ;;(valid-sc-subterms lst a)
                   (rp-evl-meta-extract-global-facts :state state)
                   (make-sc-fgl-ready-meta-formula-checks state))
              (bit-listp (rp-evlt-lst lst a)))
     :hints (("goal"
              :in-theory (e/d (binary-and-p
                               binary-not-p
                               binary-xor-p
                               binary-?-p
                               and-list-p
                               single-s-p
                               binary-or-p
                               binary-fnc-p
                               bit-listp)
                              (bitp))))))
  )



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
         `(acl2::logcar$inline
           (binary-sum ,(if (and nil ;; DISABLE IT 
                                 (bit-listp-of-pp-terms (list-to-lst pp)))
                            (sum-list-optimized-meta (list-to-lst pp)) 
                          `(sum-list ,(make-sc-fgl-ready-meta pp)))
                       (sum-list ,(make-sc-fgl-ready-meta c)))))
        (('c & s pp c)
         `(acl2::logcdr$inline
           (binary-sum
            (sum-list ,(make-sc-fgl-ready-meta s))
            (binary-sum ,(if (and nil ;; DISABLE IT 
                                  (bit-listp-of-pp-terms (list-to-lst pp)))
                             (sum-list-optimized-meta (list-to-lst pp)) 
                           `(sum-list ,(make-sc-fgl-ready-meta pp)))
                        (sum-list ,(make-sc-fgl-ready-meta c))))))
        (('logbit$inline index x)
         `(logbit$inline ,index ,(make-sc-fgl-ready-meta x)))

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
         (if (is-equals term)
             (make-sc-fgl-ready-meta (cadr term))
           `(,fnc . ,(make-sc-fgl-ready-meta-lst args))))
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

#|(define make-sc-fgl-ready-meta-main ((term rp-termp)
(rp-state))
:returns (res rp-termp :hyp (and (rp-termp term)
(rp-statep rp-state)))
`(return-last 'progn
,(orig-conjecture rp-state)
,(make-sc-fgl-ready-meta term)))|#

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

   #||#

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

   #||#))


(local
 (defthm is-equals-of-same-car-and-length
   (implies (and (not (is-equals term))
                 (true-listp term)
                 (equal (len (cdr term))
                        (len args)))
            (not (is-equals (cons (car term)
                                  args))))
   :hints (("Goal"
            :expand ((len (cdddr term))
                     (len (cddr term))
                     (len (cdr term))
                     (len term))
            :in-theory (e/d (is-equals)
                            (+-IS-SUM))))))

(Local
 (defthm len-of-adder-mux-meta-aux-lst
   (implies t
            (equal (len (make-sc-fgl-ready-meta-lst lst))
                   (len lst)))
   :hints (("Goal"
            :induct (len lst)
            :do-not-induct t
            :in-theory (e/d (MAKE-SC-FGL-READY-META-LST len)
                            (+-IS-SUM))))))


(local
 (defthm sum-list-of-list-to-lst
   (implies (and (rp-evl-meta-extract-global-facts :state state)
                 (make-sc-fgl-ready-meta-formula-checks state))
            (equal (SUM-LIST (RP-EVLT-LST (LIST-TO-LST x) A))
                   (sum-list (rp-evlt x a))))
   :hints (("Goal"
            :in-theory (e/d (LIST-TO-LST) ())))))

(defret-mutual make-sc-fgl-ready-meta-correct
  (defret make-sc-fgl-ready-meta-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (make-sc-fgl-ready-meta-formula-checks state)
                  
                  )
             (and (equal (rp-evlt res a)
                         (rp-evlt term a))
                  
                  ))
    :fn make-sc-fgl-ready-meta)

  (defret make-sc-fgl-ready-meta-lst-correct
    (implies (and (rp-evl-meta-extract-global-facts :state state)
                  (make-sc-fgl-ready-meta-formula-checks state)
                 
                  )
             (and (equal (rp-evlt-lst res-lst a)
                         (rp-evlt-lst lst a))
                  
                  ))
    :fn make-sc-fgl-ready-meta-lst)

  :hints (("Goal"
           :do-not-induct t

           :expand ((VALID-SC-SUBTERMS NIL A)) 
           :in-theory (e/d* (make-sc-fgl-ready-meta
                             make-sc-fgl-ready-meta-lst
                             RP-EVLt-OF-FNCALL-ARGS
                             RP-EVL-OF-FNCALL-ARGS
                             rp-evlt-of-ex-from-rp-reverse
                             regular-eval-lemmas
                             regular-eval-lemmas-with-ex-from-rp
                             is-equals
                             )
                            (EVAL-AND-ALL
                             CONTEXT-FROM-RP
                             VALID-SC-OF-EX-FROM-RP
                             VALID-SC-EX-FROM-RP-2
                             
                             rp-evlt-of-ex-from-rp
                             (:DEFINITION EX-FROM-RP)
                             (:REWRITE NOT-INCLUDE-RP)
                             (:DEFINITION INCLUDE-FNC-fn)
                             (:REWRITE DEFAULT-CDR)
                             (:DEFINITION INCLUDE-FNC-SUBTERMS-fn)
                             (:REWRITE RP-EVL-OF-RP-EQUAL2)
                             (:REWRITE RP-TERMP-OF-RP-TRANS)
                             (:REWRITE
                              RETURN-TYPE-OF-MAKE-SC-FGL-READY-META.RES)
                             (:DEFINITION RP-TERM-LISTP)
                             (:REWRITE IS-IF-RP-TERMP)
                             (:DEFINITION RP-TERMP)
                             rp-trans-is-term-when-list-is-absent)))))


(local
 (defthm VALID-SC-SUBTERMS-LIST-TO-LST
   (implies (valid-sc x a)
            (valid-sc-subterms (list-to-lst x)
                               a))
   :hints (("Goal"
            :in-theory (e/d (is-rp is-equals is-if list-to-lst)
                            ())))))


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
                    (:free (args) (is-equals (cons 'if args)))
                    (:free (args) (is-equals (cons 'logbit$inline args)))
                    (:free (args) (is-equals (cons 'c args)))
                    (:free (args) (is-equals (cons 's args)))
                    (:free (args) (is-equals (cons 'acl2::logcdr$inline args)))
                    (:free (args) (is-equals (cons 'binary-sum args)))
                    (:free (args) (is-equals (cons 'sum-list args)))
                    (:free (args) (is-equals (cons 'acl2::logcar$inline args)))
                    (VALID-SC (EX-FROM-RP TERM) A))
           :in-theory (e/d* (make-sc-fgl-ready-meta
                             make-sc-fgl-ready-meta-lst
                             RP-EVLt-OF-FNCALL-ARGS
                             RP-EVL-OF-FNCALL-ARGS
                             rp-evlt-of-ex-from-rp-reverse
                             ;;regular-eval-lemmas
                             is-if
                             is-rp ;;is-equals
                             ;;regular-eval-lemmas-with-ex-from-rp
                             valid-sc-of-ex-from-rp-reverse
                             )
                            (EVAL-AND-ALL
                             CONTEXT-FROM-RP
                             
                             (:rewrite make-sc-fgl-ready-metawhen-quoted)
                             rp-evlt-of-ex-from-rp
                             VALID-SC-OF-EX-FROM-RP
                             VALID-SC-EX-FROM-RP-2
                             (:DEFINITION EVAL-AND-ALL)
                             (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                             (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                             (:DEFINITION ACL2::APPLY$-BADGEP)
                             (:DEFINITION RP-TRANS)
                             (:DEFINITION EX-FROM-RP)
                             (:REWRITE NOT-INCLUDE-RP)

                             (:REWRITE DEFAULT-CDR)
                             (:DEFINITION INCLUDE-FNC-SUBTERMS-fn)
                             (:REWRITE RP-EVL-OF-RP-EQUAL2)
                             (:REWRITE RP-TERMP-OF-RP-TRANS)
                             (:REWRITE DEFAULT-CAR)
                             (:REWRITE
                              RETURN-TYPE-OF-MAKE-SC-FGL-READY-META.RES)
                             ;;(:DEFINITION RP-TERM-LISTP)
                             (:REWRITE IS-IF-RP-TERMP)
                             (:DEFINITION RP-TERMP)
                             rp-trans-is-term-when-list-is-absent)))))



(memoize 'make-sc-fgl-ready-meta)
(memoize 'sum-list-optimized-meta)
