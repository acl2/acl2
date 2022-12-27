; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2021 Centaur Technology
; Copyright (C) 2022 Intel Corporation
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

(in-package "SVL")

(include-book "centaur/sv/svex/eval" :dir :system)

(include-book "projects/rp-rewriter/top" :dir :system)

(include-book "../fnc-defs")

(include-book "svex-reduce-apply")

(local
 (include-book "../4vec-lemmas"))

(local
 (include-book "../bits-sbits"))

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/ihs-extensions" :dir :system)
  use-ihs-extensions
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "ihs/logops-lemmas" :dir :system)
  use-ihs-logops-lemmas
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "ihs/quotient-remainder-lemmas" :dir :system)
  use-qr-lemmas
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/equal-by-logbitp" :dir :system)
  use-equal-by-logbitp
  :disabled t))

(local
 (defthm svex-p-of-consed
   (implies (and (not (equal fn ':var))
                 (not (integerp fn)))
            (equal (svex-p (cons fn args))
                   (and (FNSYM-P fn)
                        (SVEXLIST-P args))))
   :hints (("Goal"
            :in-theory (e/d (svex-p) ())))))

(acl2::defsection bitand/bitor-cancel-repeated
  (define bitand/bitor-collect-leaves ((svex)
                                       (fn))
    :Returns (leaves sv::Svexlist-p :hyp (and (sv::Svex-p svex)
                                              (not (equal fn ':var)))
                     :hints (("Goal"
                              :in-theory (e/d (svex-p
                                               4vec-p)
                                              ()))))
    (case-match svex
      ((this-fn x y)
       (if (equal this-fn fn)
           (cons svex (append (bitand/bitor-collect-leaves x fn)
                              (bitand/bitor-collect-leaves y fn)))
         (list svex)))
      (& (list svex)))
    ///
    (defret true-listp-of-<fn>
      (true-listp leaves)))

  (define bitand/or/xor-simple-constant-simplify (fn arg1 arg2 &optional 1masked)
    ;; for easier theorem proving,
    :returns (simplified-svex sv::Svex-p :hyp (and (sv::fnsym-p fn)
                                                   (not (equal fn ':var))
                                                   (sv::Svex-p arg1)
                                                   (sv::Svex-p arg2)))
    (cond ((equal fn 'sv::bitor)
           (b* (((when (and 1masked
                            (or (equal arg1 1)
                                (equal arg2 1))))
                 1)
                ((when (and (not 1masked)
                            (or (equal arg1 -1)
                                (equal arg2 -1))))
                 -1)
                ((when (equal arg1 0))
                 (svex-reduce-w/-env-apply 'sv::unfloat (hons-list arg2)))
                ((when (equal arg2 0))
                 (svex-reduce-w/-env-apply 'sv::unfloat (hons-list arg1))))
             (svex-reduce-w/-env-apply 'sv::bitor (hons-list arg1 arg2))))
          ((equal fn 'sv::bitxor)
           (b* (((when (equal arg1 0))
                 (svex-reduce-w/-env-apply 'sv::unfloat (hons-list arg2)))
                ((when (equal arg2 0))
                 (svex-reduce-w/-env-apply 'sv::unfloat (hons-list arg1))))
             (svex-reduce-w/-env-apply 'sv::bitxor (hons-list arg1 arg2))))
          ((equal fn 'sv::bitand)
           (b*  (((when (or (equal arg1 0)
                            (equal arg2 0)))
                  0)
                 ((when (or (equal arg1 -1)
                            (and 1masked (equal arg1 1))))
                  (svex-reduce-w/-env-apply 'sv::unfloat (hons-list arg2)))
                 ((when (or (equal arg2 -1)
                            (and 1masked (equal arg2 1))))
                  (svex-reduce-w/-env-apply 'sv::unfloat (hons-list arg1))))
             (svex-reduce-w/-env-apply 'sv::bitand (hons-list arg1 arg2))))
          (t (svex-reduce-w/-env-apply fn (hons-list arg1 arg2)))))

  (define member-hons-equal (x lst)
    (if (atom lst)
        nil
      (or (hons-equal x (car lst))
          (member-hons-equal x (cdr lst))))
    ///
    (defthm member-hons-equal-is-member-equal
      (iff (member-hons-equal x lst)
           (member-equal x lst))))

  (define bitand/bitor-cancel-repeated-aux ((svex)
                                            (leaves true-listp)
                                            (new-val integerp)
                                            &optional
                                            ((limit natp) ''10))
    :returns (mv (simplified-svex sv::Svex-p :hyp (and (sv::svex-p svex)
                                                       (sv::Svex-p new-val)))
                 changed)
    (cond
     ((zp limit)
      (mv svex nil))
     ((member-hons-equal svex leaves)
      (mv new-val t))
     ;; this is to prevent diving into and simplifying shared nodes.
     #|((member-hons-equal svex all-nodes)
     (mv svex nil))|#
     (t
      (case-match svex
        (('sv::bitor x y)
         (b* (((mv x changed-x) (bitand/bitor-cancel-repeated-aux x leaves new-val (1- limit)))
              ((mv y changed-y) (bitand/bitor-cancel-repeated-aux y leaves new-val (1- limit))))
           (if (or changed-x
                   changed-y)
               (mv (bitand/or/xor-simple-constant-simplify 'sv::bitor x y) t)
             (mv svex nil))))
        (('sv::bitand x y)
         (b* (((mv x changed-x) (bitand/bitor-cancel-repeated-aux x leaves new-val (1- limit)))
              ((mv y changed-y) (bitand/bitor-cancel-repeated-aux y leaves new-val (1- limit))))
           (if (or changed-x
                   changed-y)
               (mv (bitand/or/xor-simple-constant-simplify 'sv::bitand x y) t)
             (mv svex nil))))
        ;; (('sv::bitxor x  1) ;; bitxor simplification requires this to be an
        ;; integer apparently...
        (& (mv svex nil))))))

  (define bitand/bitor-cancel-repeated (fn x y)
    :returns (simplified-svex sv::Svex-p :hyp (and (sv::fnsym-p fn)
                                                   (Not (equal fn :var))
                                                   (svex-p x)
                                                   (svex-p y)))
    (case fn
      (sv::bitor
       (b* (;;(orig-y y)
            ;;(orig-x x)
            (l1
             (bitand/bitor-collect-leaves x 'sv::bitor))
            ((mv y changed-y) (bitand/bitor-cancel-repeated-aux y l1  0))
            #|(- (and changed-y
            (rp::cwe "bitor-change: full-svex: ~p0 y:~p1~%" (list fn orig-x orig-y) y)))|#
            (l2
             (bitand/bitor-collect-leaves y 'sv::bitor))
            ((mv x changed-x) (bitand/bitor-cancel-repeated-aux x l2  0))
            #|(- (and changed-x
            (rp::cwe "bitor-change: full-svex: ~p0 x:~p1~%" (list fn orig-x orig-y) x)))|#)
         (if (or changed-x changed-y)
             (bitand/or/xor-simple-constant-simplify 'sv::bitor x y nil)
           (svex-reduce-w/-env-apply fn (hons-list x y)))))
      (sv::bitand
       (b* (;;(orig-y y)
            ;;(orig-x x)
            (l1
             (bitand/bitor-collect-leaves x 'sv::bitand))
            ((mv y changed-y) (bitand/bitor-cancel-repeated-aux y l1  -1))
            #|(- (and changed-y
            (rp::cwe "bitand-change: full-svex: ~p0 y:~p1~%" (list fn orig-x orig-y) y)))|#
            (l2
             (bitand/bitor-collect-leaves y 'sv::bitand))
            ((mv x changed-x) (bitand/bitor-cancel-repeated-aux x l2  -1))
            #|(- (and changed-x
            (rp::cwe "bitand-change: full-svex: ~p0 x:~p1~%" (list fn orig-x orig-y) x)))|#)
         (if (or changed-x changed-y)
             (bitand/or/xor-simple-constant-simplify 'sv::bitand x y nil)
           (svex-reduce-w/-env-apply fn (hons-list x y)))))
      #|(('sv::bitxor x y)
      (bitand/or/xor-simple-constant-simplify 'sv::bitxor x y nil) ;
      )|#
      (otherwise
       (svex-reduce-w/-env-apply fn (hons-list x y)))))

  ;; (bitand/bitor-cancel-repeated '(sv::Bitand (sv::Bitand a b)
  ;;                                            (sv::bitand (sv::bitor a x) y)))
  ;; returns:
  ;; (BITAND (BITAND A B) Y)

  ;; (bitand/bitor-cancel-repeated '(sv::Bitor (sv::Bitor a b)
  ;;                                           (sv::bitand (sv::bitor a x) y)))
  ;; returns:
  ;; (SV::BITOR (SV::BITOR A B) (BITAND X Y))

  ;; (bitand/bitor-cancel-repeated '(sv::Bitor a (sv::bitxor 1 a)))
  ;; returns:
  ;; 1
  )

(local
 (defthm svex-eval-opener-when-call
   (implies (and (syntaxp (and (consp fn)
                               (quotep fn)))
                 (fnsym-p fn))
            (equal (svex-eval (cons fn args) env)
                   (SV::SVEX-APPLY fn
                                   (SVEXLIST-EVAL args env))))
   :hints (("Goal"
            :expand (svex-eval (cons fn args) env)
            :in-theory (e/d (SVEX-CALL->FN
                             SVEX-VAR->NAME
                             SVEX-KIND
                             SVEX-CALL->ARGS)
                            ())))))

(local
 (defthm 4VEC-BITOR-of-1
   (equal (4VEC-BITOR -1 then)
          -1)
   :hints (("Goal"
            :expand (4VEC-BITOR -1 then)
            :in-theory (e/d (SV::3VEC-BITOR) ())))))



(Local
 (acl2::defsection single-bit-part-select-case-splitter

   (defun single-bit-4vec-p-ored (x)
     (or (equal x 1)
         (equal x 0)
         (equal x '(1 . 0))
         (equal x '(0 . 1))))

   (local
    (defthm  single-bit-4vec-p-ored-of-4vec-part-select-0-1
      (let* ((x (4vec-part-select 0 1 x)))
        (and (single-bit-4vec-p-ored x)))
      :rule-classes (:rewrite :type-prescription)
      :hints (("goal"
               :in-theory (e/d* (bitops::ihsext-inductions
                                 bitops::ihsext-recursive-redefs
                                 4vec-part-select
                                 4vec-concat)
                                (loghead
                                 floor
                                 equal-of-4vec-concat-with-size=1))))))

   (define single-bit-part-select-case-splitter-aux (term lst-flg)
     (cond ((or (atom term)
                (quotep term))
            nil)
           (lst-flg
            (acl2::append-without-guard
             (single-bit-part-select-case-splitter-aux (car term) nil)
             (single-bit-part-select-case-splitter-aux (cdr term) t)))
           (t (case-match term
                (('sv::4vec-part-select ''0 ''1 x)
                 (list x))
                (('sv::4vec-part-select '0 '1 x)
                 (list x))
                (&
                 (single-bit-part-select-case-splitter-aux (cdr term) t))))))

   (define single-bit-part-select-case-splitter-aux-2 (terms)
     (if (atom terms)
         nil
       (cons `(not (single-bit-4vec-p-ored (4vec-part-select '0 '1 ,(car terms))))
             (single-bit-part-select-case-splitter-aux-2 (cdr terms)))))

   (defun single-bit-part-select-case-splitter (cl)
     (b* ((terms (single-bit-part-select-case-splitter-aux cl t))
          (extra-hyps (single-bit-part-select-case-splitter-aux-2 terms))
          ((when (atom extra-hyps))
           (list cl)))
       (list (append cl extra-hyps))))

   (defevaluator evl0 evl0-lst
     ((if x y z)
      (not x)
      (single-bit-4vec-p-ored x)
      (sv::4vec-part-select x y z))
     :namedp t)

   (defthm ACL2::DISJOIN-of-append
     (iff (evl0 (ACL2::DISJOIN (append x y)) a)
          (or (evl0 (ACL2::DISJOIN x) a)
              (evl0 (ACL2::DISJOIN y) a)))
     :hints (("Goal"
              :in-theory (e/d (ACL2::DISJOIN
                               ACL2::DISJOIN2)
                              ()))))

   (local
    (defthm correctness-lemma-1
      (implies t
               (not (EVL0 (ACL2::DISJOIN (SINGLE-BIT-PART-SELECT-CASE-SPLITTER-AUX-2 terms))
                          A)))
      :hints (("Goal"
               :in-theory (e/d (ACL2::DISJOIN
                                ACL2::DISJOIN2
                                single-bit-part-select-case-splitter-aux-2)
                               ())))))

   (defthmd correctness-of-single-bit-part-select-case-splitter-aux
     (implies (and (evl0 (acl2::conjoin-clauses
                          (single-bit-part-select-case-splitter cl))
                         a))
              (evl0 (acl2::disjoin cl) a))
     :hints (("Goal"
              :expand ((:free (x y)
                              (ACL2::DISJOIN (cons x y))))
              :in-theory (e/d (
                               single-bit-part-select-case-splitter
                               )
                              ())))
     :rule-classes :clause-processor)

   ))

(defsection bitand/bitor-cancel-repeated-correct

  (defun single-bit-4vec-p (x)
    (equal (4vec-part-select 0 1 x)
           x))

  (local
   (defun eval-bitand-lst (lst env)
     (if (atom lst)
         -1
       (4vec-bitand (svex-eval (car lst) env)
                    (eval-bitand-lst (cdr lst) env)))))

  (local
   (defun eval-bitor-lst (lst env)
     (if (atom lst)
         0
       (4vec-bitor (svex-eval (car lst) env)
                   (eval-bitor-lst (cdr lst) env)))))

  (local
   (defthm 3VEC-P-of-EVAL-BITOR-LST
     (sv::3vec-p (EVAL-BITOR-LST lst env))))

  (local
   (defthm 3VEC-P-of-EVAL-BITand-LST
     (sv::3vec-p (EVAL-BITand-LST lst env))))

  (local
   (defthm 4VEC-P-of-EVAL-BITOR-LST
     (sv::4vec-p (EVAL-BITOR-LST lst env))))

  (local
   (defthm 4VEC-P-of-EVAL-BITand-LST
     (sv::4vec-p (EVAL-BITand-LST lst env))))

  

  (local
   (defthm when-eval-bitor-lst-evals-to-zero
     (implies (and (equal (4vec-part-select 0 1 (eval-bitor-lst leaves env))
                          0)
                   (member-equal svex leaves))
              (equal (4vec-part-select 0 1 (svex-eval svex env))
                     0))
     :otf-flg t
     :hints (("goal"
              :do-not-induct t
              :induct (eval-bitor-lst leaves env)
              :in-theory (e/d (eval-bitor-lst
                               4vec-part-select-of-4vec-bitor-better
                               member-equal)
                              ()))
             (and stable-under-simplificationp
                  '(:use ((:instance when-4vec-bitor-is-zero
                                     (x (4VEC-PART-SELECT 0 1 (EVAL-BITOR-LST (CDR LEAVES) ENV)))
                                     (y (4VEC-PART-SELECT 0 1 (SVEX-EVAL (CAR
                                                                          LEAVES) ENV))))))))))

  (local
   (defthm when-eval-bitand-lst-evals-to-one
     (implies (and (equal (4vec-part-select 0 1 (eval-bitand-lst leaves env))
                          1)
                   (member-equal svex leaves))
              (equal (4vec-part-select 0 1 (svex-eval svex env))
                     1))
     :otf-flg t
     :hints (("goal"
              :do-not-induct t
              :induct (eval-bitand-lst leaves env)
              :in-theory (e/d (eval-bitand-lst
                               4vec-part-select-of-4vec-bitand-better
                               member-equal)
                              ()))
             (and stable-under-simplificationp
                  '(:use ((:instance WHEN-4VEC-BITAND-IS-ONE-WITH-ONE-BIT-MASK
                                     (x (4VEC-PART-SELECT 0 1 (EVAL-BITand-LST (CDR LEAVES) ENV)))
                                     (y (4VEC-PART-SELECT 0 1 (SVEX-EVAL (CAR LEAVES) ENV))))))))))

  (local
   (defthm when-eval-bitor-lst-evals-to-nonzero
     (implies (and (equal (4vec-part-select 0 1 (svex-eval svex env))
                          1)
                   (member-equal svex leaves))
              (equal (4vec-part-select 0 1 (eval-bitor-lst leaves env))
                     1))
     :otf-flg t
     :hints (("goal"
              :do-not-induct t
              :induct (eval-bitor-lst leaves env)
              :in-theory (e/d (eval-bitor-lst
                               4vec-part-select-of-4vec-bitor-better
                               member-equal
                               PUSH-3VEC-FIX-INTO-4VEC-PART-SELECT)
                              (4VEC-PART-SELECT-OF-3VEC-FIX
                               ;;
                               )))
             #|(and stable-under-simplificationp
             '(:use ((:instance when-4vec-bitor-is-zero ; ; ;
             (x (4VEC-PART-SELECT 0 1 (EVAL-BITOR-LST (CDR LEAVES) ENV))) ; ; ;
             (y (4VEC-PART-SELECT 0 1 (SVEX-EVAL (CAR ; ; ;
             LEAVES) ENV)))))))|#)))

  (local
   (defthm when-eval-bitand-lst-evals-to-0
     (implies (and (equal (4vec-part-select 0 1 (svex-eval svex env))
                          0)
                   (member-equal svex leaves))
              (equal (4vec-part-select 0 1 (eval-bitand-lst leaves env))
                     0))
     :otf-flg t
     :hints (("goal"
              :do-not-induct t
              :induct (eval-bitand-lst leaves env)
              :in-theory (e/d (eval-bitand-lst
                               4vec-part-select-of-4vec-bitand-better
                               member-equal
                               PUSH-3VEC-FIX-INTO-4VEC-PART-SELECT)
                              (4VEC-PART-SELECT-OF-3VEC-FIX
                               ;;
                               )))
             #|(and stable-under-simplificationp
             '(:use ((:instance when-4vec-bitor-is-zero ; ; ;
             (x (4VEC-PART-SELECT 0 1 (EVAL-BITOR-LST (CDR LEAVES) ENV))) ; ; ;
             (y (4VEC-PART-SELECT 0 1 (SVEX-EVAL (CAR LEAVES) ENV)))))))|#)))

  (local
   (defthm svex-eval-when-fnc-is-bitand
     (implies (and  (EQUAL (CAR SVEX) 'BITAND)
                    (CONSP (CDR SVEX))
                    (CONSP (CDDR SVEX))
                    (NOT (CDDDR SVEX)))
              (equal (svex-eval svex env)
                     (4vec-bitand (svex-eval (cadr svex) env)
                                  (svex-eval (caddr svex) env))))
     :hints (("Goal"
              :expand ((svex-eval svex env))
              :in-theory (e/d (svex-kind
                               SVEX-APPLY
                               SVEX-CALL->ARGS
                               SVEX-CALL->FN )
                              ())))))

  (local
   (defthm svex-eval-when-fnc-is-bitor
     (implies (and  (EQUAL (CAR SVEX) 'sv::BITor)
                    (CONSP (CDR SVEX))
                    (CONSP (CDDR SVEX))
                    (NOT (CDDDR SVEX)))
              (equal (svex-eval svex env)
                     (4vec-bitor (svex-eval (cadr svex) env)
                                 (svex-eval (caddr svex) env))))
     :hints (("Goal"
              :expand ((svex-eval svex env))
              :in-theory (e/d (svex-kind
                               SVEX-APPLY
                               SVEX-CALL->ARGS
                               SVEX-CALL->FN )
                              ())))))

  (local
   (defthm svex-eval-when-fnc-is-bitxor
     (implies (and  (EQUAL (CAR SVEX) 'sv::BITxor)
                    (CONSP (CDR SVEX))
                    (CONSP (CDDR SVEX))
                    (NOT (CDDDR SVEX)))
              (equal (svex-eval svex env)
                     (sv::4vec-bitxor (svex-eval (cadr svex) env)
                                      (svex-eval (caddr svex) env))))
     :hints (("Goal"
              :expand ((svex-eval svex env))
              :in-theory (e/d (svex-kind
                               SVEX-APPLY
                               SVEX-CALL->ARGS
                               SVEX-CALL->FN )
                              ())))))

  (defthm bitand/or/xor-simple-constant-simplify-correct-1
    (implies (and (or (equal fn 'sv::bitor)
                      (equal fn 'sv::bitxor)
                      (equal fn 'sv::bitand)
                      ))
             (equal (svex-eval (bitand/or/xor-simple-constant-simplify fn arg1 arg2 nil)
                               env)
                    (svex-eval `(,fn ,arg1 ,arg2) env)))
    :hints (("goal"
             :in-theory (e/d (svex-apply
                              bitand/or/xor-simple-constant-simplify) ;
                             ()))))

  (defthm bitand/or/xor-simple-constant-simplify-correct-2
    (implies (and (or (equal fn 'sv::bitor)
                      (equal fn 'sv::bitxor)
                      (equal fn 'sv::bitand)
                      )
                  (force (single-bit-4vec-p (svex-eval arg1 env)))
                  (force (single-bit-4vec-p (svex-eval arg2 env))))
             (equal (svex-eval (bitand/or/xor-simple-constant-simplify fn arg1 arg2 t)
                               env)
                    (svex-eval `(,fn ,arg1 ,arg2) env)))
    :otf-flg t
    :hints (("goal"
             :in-theory (e/d (svex-apply

                              bitand/or/xor-simple-constant-simplify) ;
                             ()))
            (and stable-under-simplificationp
                 '(:clause-processor
                   (single-bit-part-select-case-splitter clause)))))

  (local
   (defthm EVAL-BITOR-LST-ored-with-a-member
     (implies (MEMBER-EQUAL SVEX LEAVES)
              (equal (4VEC-BITOR (EVAL-BITOR-LST LEAVES ENV)
                                 (SVEX-EVAL SVEX ENV))
                     (EVAL-BITOR-LST LEAVES ENV)))
     :hints (("Goal"
              :in-theory (e/d (EVAL-BITOR-LST) ())))))

  (local
   (defthm EVAL-BITAND-LST-anded-with-a-member
     (implies (MEMBER-EQUAL SVEX LEAVES)
              (equal (4VEC-BITAND (EVAL-BITAND-LST LEAVES ENV)
                                  (SVEX-EVAL SVEX ENV))
                     (EVAL-BITAND-LST LEAVES ENV)))
     :hints (("Goal"
              :in-theory (e/d (EVAL-BITAND-LST) ())))))

  (Local
   (defret bitand/bitor-cancel-repeated-aux-correct-1
     (implies (equal new-val 0)
              (equal
               (4vec-bitor (eval-bitor-lst leaves env)
                           (svex-eval simplified-svex env))
               (4vec-bitor (eval-bitor-lst leaves env)
                           (svex-eval svex env))))
     :fn bitand/bitor-cancel-repeated-aux
     ;;:otf-flg t
     :hints (("Goal"
              :induct (bitand/bitor-cancel-repeated-aux svex leaves  new-val limit)
              :do-not-induct t
              :expand (;;(SVEX-EVAL SVEX ENV)
                       (:free (x)
                              (SVEX-APPLY 'sv::bitxor x))
                       (:free (x)
                              (SVEX-APPLY 'sv::unfloat x))
                       (:free (x)
                              (SVEX-APPLY 'sv::bitand x))
                       (:free (x)
                              (SVEX-APPLY 'sv::bitor x)))

              :in-theory (e/d (SVEXLIST-EVAL
                               4vec-bitor-of-4vec-bitand
                               4VEC-PART-SELECT-OF-4VEC-BITOR-BETTER
                               4VEC-PART-SELECT-OF-4VEC-BITXOR-BETTER
                               4VEC-PART-SELECT-OF-4VEC-BITAND-BETTER
                               ;;SVEX-EVAL
                               SVEX-KIND
                               SVEX-CALL->FN
                               SVEX-CALL->ARGS
                               bitand/bitor-cancel-repeated-aux
                               )
                              (PUSH-3VEC-FIX-INTO-4VEC-PART-SELECT

                               ;;4VEC-PART-SELECT-OF-3VEC-FIX
                               member-equal
                               ;;SVEX-EVAL-WHEN-4VEC-P
                               DEFAULT-CAR
                               SV::SVEX-EVAL-WHEN-QUOTE
                               SV::SVEX-EVAL-WHEN-FNCALL
                               SV::4VEC-P-WHEN-MAYBE-4VEC-P
                               (:REWRITE-QUOTED-CONSTANT  SV::SVEX-FIX-UNDER-SVEX-EQUIV)
                               (:definition true-list-listp)
                               (:rewrite
                                acl2::member-equal-newvar-components-1)
                               ;;single-bit-4vec-p-ored-of-4vec-part-select-0-1
                               )))
             (and stable-under-simplificationp
                  '(:clause-processor
                    (single-bit-part-select-case-splitter clause)))
             )))

  (Local
   (defret bitand/bitor-cancel-repeated-aux-correct-2
     (implies (equal new-val -1)
              (equal
               (4vec-bitand (eval-bitand-lst leaves env)
                            (svex-eval simplified-svex env))
               (4vec-bitand (eval-bitand-lst leaves env)
                            (svex-eval svex env))))
     :fn bitand/bitor-cancel-repeated-aux
     ;;:otf-flg t
     :hints (("Goal"
              :induct (bitand/bitor-cancel-repeated-aux svex leaves  new-val limit)
              :do-not-induct t
              :expand (;;(SVEX-EVAL SVEX ENV)
                       (:free (x)
                              (SVEX-APPLY 'sv::bitxor x))
                       (:free (x)
                              (SVEX-APPLY 'sv::unfloat x))
                       (:free (x)
                              (SVEX-APPLY 'sv::bitand x))
                       (:free (x)
                              (SVEX-APPLY 'sv::bitor x)))

              :in-theory (e/d (SVEXLIST-EVAL
                               4vec-bitand-of-4vec-bitor
                               4VEC-PART-SELECT-OF-4VEC-BITOR-BETTER
                               4VEC-PART-SELECT-OF-4VEC-BITXOR-BETTER
                               4VEC-PART-SELECT-OF-4VEC-BITAND-BETTER
                               ;;SVEX-EVAL
                               SVEX-KIND
                               SVEX-CALL->FN
                               SVEX-CALL->ARGS
                               bitand/bitor-cancel-repeated-aux
                               )
                              (push-3vec-fix-into-4vec-part-select
                               member-equal
                               ;;SVEX-EVAL-WHEN-4VEC-P
                               DEFAULT-CAR
                               SV::SVEX-EVAL-WHEN-QUOTE
                               SV::SVEX-EVAL-WHEN-FNCALL
                               SV::4VEC-P-WHEN-MAYBE-4VEC-P
                               (:REWRITE-QUOTED-CONSTANT  SV::SVEX-FIX-UNDER-SVEX-EQUIV)
                               (:definition true-list-listp)
                               (:rewrite
                                acl2::member-equal-newvar-components-1)
                               ;;single-bit-4vec-p-ored-of-4vec-part-select-0-1
                               )))
             (and stable-under-simplificationp
                  '(:clause-processor
                    (single-bit-part-select-case-splitter clause)))
             )))

  (local
   (defthm eval-bitor/bitand-lst-of-append
     (and (equal (eval-bitor-lst (append x y) env)
                 (4vec-bitor (eval-bitor-lst x env)
                             (eval-bitor-lst y env)))
          (equal (eval-bitand-lst (append x y) env)
                 (4vec-bitand (eval-bitand-lst x env)
                              (eval-bitand-lst y env))))
     :otf-flg t
     :hints (("goal"
              :induct (eval-bitor-lst x env)
              :do-not-induct t
              :expand ((eval-bitor-lst y env)
                       (eval-bitand-lst y env))
              :in-theory (e/d (eval-bitor-lst
                               eval-bitand-lst) ())))))

  (local
   (defthm eval-bitor-lst-of-bitand/bitor-collect-leaves
     (and
      (equal
       (sv::3vec-fix (eval-bitor-lst (bitand/bitor-collect-leaves svex 'sv::bitor) env))
       (sv::3vec-fix (svex-eval svex env))))
     :hints (("goal"
              :in-theory (e/d (eval-bitor-lst
                               eval-bitand-lst
                               bitand/bitor-collect-leaves

                               )
                              ())))))

  (local
   (defthm eval-bitand-lst-of-bitand/bitor-collect-leaves
     (equal
      (sv::3vec-fix (eval-bitand-lst (bitand/bitor-collect-leaves svex 'sv::bitand) env))
      (sv::3vec-fix (svex-eval svex env)))
     :hints (("goal"
              :in-theory (e/d (eval-bitor-lst
                               eval-bitand-lst
                               bitand/bitor-collect-leaves)
                              ())))))
  (local
   (defthm eval-bitor-lst-of-bitand/bitor-collect-leaves-2
     (and (equal
           (sv::4vec-bitor other
                           (eval-bitor-lst (bitand/bitor-collect-leaves svex 'sv::bitor) env)
                           )
           (sv::4vec-bitor (svex-eval svex env)
                           other))
          (equal
           (sv::4vec-bitor (eval-bitor-lst (bitand/bitor-collect-leaves svex 'sv::bitor) env)
                           other)
           (sv::4vec-bitor (svex-eval svex env)
                           other)))
     :hints (("goal"
              :use ((:instance eval-bitor-lst-of-bitand/bitor-collect-leaves))
              :in-theory (e/d ()
                              (eval-bitor-lst-of-bitand/bitor-collect-leaves))))))

  (local
   (defthm eval-bitand-lst-of-bitand/bitor-collect-leaves-2
     (and (equal
           (sv::4vec-bitand other
                            (eval-bitand-lst (bitand/bitor-collect-leaves svex 'sv::bitand) env)
                            )
           (sv::4vec-bitand (svex-eval svex env)
                            other))
          (equal
           (sv::4vec-bitand (eval-bitand-lst (bitand/bitor-collect-leaves svex 'sv::bitand) env)
                            other)
           (sv::4vec-bitand (svex-eval svex env)
                            other)))
     :hints (("goal"
              :use ((:instance eval-bitand-lst-of-bitand/bitor-collect-leaves))
              :in-theory (e/d ()
                              (eval-bitand-lst-of-bitand/bitor-collect-leaves))))))

  (local
   (defthm 4vec-p-of-EVAL-BITOR/and-LST
     (and (sv::4vec-p (EVAL-BITOR-LST lst env))
          (sv::4vec-p (EVAL-BITand-LST lst env)))))

  (defret bitand/bitor-cancel-repeated-correct
    (implies (and (FNSYM-P FN))
             (equal
              (svex-eval simplified-svex env)
              (svex-eval `(,fn ,x ,y) env)))
    :fn bitand/bitor-cancel-repeated
    :otf-flg t
    :hints (("goal"
             :do-not-induct t
             :use ( (:instance bitand/bitor-cancel-repeated-aux-correct-1
                               (svex y)
                               (leaves (bitand/bitor-collect-leaves x 'bitor))

                               (new-val 0)
                               (limit 10))
                    (:instance bitand/bitor-cancel-repeated-aux-correct-1
                               (svex x)
                               (leaves (bitand/bitor-collect-leaves
                                        (MV-NTH 0
                                                (bitand/bitor-cancel-repeated-aux
                                                 y
                                                 (bitand/bitor-collect-leaves x
                                                                              'bitor)
                                                 0))
                                        'bitor))
                               (new-val 0)
                               (limit 10))
                    (:instance bitand/bitor-cancel-repeated-aux-correct-2
                               (svex y)
                               (leaves (bitand/bitor-collect-leaves x
                                                                    'bitand))

                               (new-val -1)
                               (limit 10))
                    (:instance bitand/bitor-cancel-repeated-aux-correct-2
                               (svex x)
                               (leaves (bitand/bitor-collect-leaves
                                        (MV-NTH 0
                                                (bitand/bitor-cancel-repeated-aux
                                                 y
                                                 (bitand/bitor-collect-leaves x
                                                                              'bitand)
                                                 -1))
                                        'bitand))

                               (new-val -1)
                               (limit 10))
                    )
             :in-theory (e/d (bitand/bitor-cancel-repeated
                              4vec-part-select-of-4vec-bitor-better
                              4vec-part-select-of-4vec-bitand-better)
                             (eval-bitor-lst-of-bitand/bitor-collect-leaves
                              bitand/bitor-cancel-repeated-aux-correct-1
                              bitand/bitor-cancel-repeated-aux-correct-2
                              )))))

  )
