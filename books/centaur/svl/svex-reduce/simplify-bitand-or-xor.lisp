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

(include-book "base")

(include-book "projects/rp-rewriter/top" :dir :system)

(include-book "../fnc-defs")

(include-book "svex-reduce-apply")
(include-book "integerp-of-svex")
(include-book "width-of-svex")

(local
 (include-book "../4vec-lemmas"))

(local
 (include-book "../bits-sbits"))

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/ihs-extensions" :dir :system)
  use-ihs-extensions
  ))

(local
 (rp::fetch-new-events
  (include-book "ihs/logops-lemmas" :dir :system)
  use-ihs-logops-lemmas
  ))

(local
 (rp::fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "ihs/quotient-remainder-lemmas" :dir :system)
  use-qr-lemmas
  ))

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

(local
 (defthm svex-p-of-4vec-p
   (implies (4vec-p x)
            (svex-p x))
   :rule-classes :rewrite
   :hints (("Goal"
            :in-theory (e/d (svex-p 4vec-p) ())))))

#|(skip-proofs
(defines bitand-xor-bad-pattern
:prepwork ((rp::create-case-match-macro bad-pattern
('sv::bitxor 1 ('sv::bitxor 1 k))))
(define bitand-xor-bad-pattern ((x svex-p))
:measure (sv::Svex-count x)
(sv::Svex-case
x
:var nil
:quote nil
:call (or (and (bad-pattern-p x)
(not (rp::cwe "bad pattern: ~p0 ~%" x)))
(bitand-xor-bad-pattern-list x.args))))
(define bitand-xor-bad-pattern-list ((lst svexlist-p))
:measure (sv::Svex-count lst)
(and (consp lst)
(or (bitand-xor-bad-pattern (car lst))
(bitand-xor-bad-pattern-list (cdr lst)))))
///
(memoize 'bitand-xor-bad-pattern
:condition '(eq (sv::svex-kind x) :call))))|#

(define bitand/or/xor-simple-constant-simplify (fn (arg1 svex-p)
                                                   (arg2 svex-p)
                                                   &key
                                                   (1masked 'nil)
                                                   ((config svex-reduce-config-p)
                                                    'config))
  ;; for easier theorem proving,
  :returns (simplified-svex sv::Svex-p :hyp (and (sv::fnsym-p fn)
                                                 (not (equal fn ':var))
                                                 (sv::Svex-p arg1)
                                                 (sv::Svex-p arg2)))
  (cond ((equal fn 'sv::bitor)
         (b* (((when (and* (4vec-p arg1)
                           (4vec-p arg2)))
               (4vec-bitor arg1 arg2))
              ((when (and 1masked
                          (or (equal arg1 1)
                              (equal arg2 1))))
               1)
              ((when (and (not 1masked) ;; not necessarry
                          (or (equal arg1 -1)
                              (equal arg2 -1))))
               -1)

              ((when (and (not 1masked) ;; not necessary
                          (or (and (equal arg1 1)
                                   (let* ((arg2-width (width-of-svex arg2)))
                                     (and arg2-width
                                          (equal arg2-width 1))))
                              (and (equal arg2 1)
                                   (let* ((arg1-width (width-of-svex arg1)))
                                     (and arg1-width
                                          (equal arg1-width 1)))))))
               1)

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
                          (and (equal arg1 1)
                               (or 1masked
                                   (let* ((arg2-width (width-of-svex arg2)))
                                     (and arg2-width
                                          (equal arg2-width 1)))))))
                (svex-reduce-w/-env-apply 'sv::unfloat (hons-list arg2)))
               ((when (or (equal arg2 -1)
                          (and (equal arg2 1)
                               (or 1masked
                                   (let* ((arg1-width (width-of-svex arg1)))
                                     (and arg1-width
                                          (equal arg1-width 1)))))))
                (svex-reduce-w/-env-apply 'sv::unfloat (hons-list arg1))))
           (svex-reduce-w/-env-apply 'sv::bitand (hons-list arg1 arg2))))
        (t (svex-reduce-w/-env-apply fn (hons-list arg1 arg2)))))

(defsection clear-1s-from-bitxor
  ;; A quick  way to  clear repeated  1's from bitxors.  These are  expected to
  ;; appear in bitand/bitor-cancel-repeated

  (define bitxor-has-1 (x)
    :returns (res)
    (case-match x
      (('sv::bitxor a b)
       (or (equal a 1)
           (equal b 1)
           (bitxor-has-1 a)
           (bitxor-has-1 b)))
      (& (equal x 1))))

  (define remove-1-from-xor ((x svex-p)
                             &key
                             ((config svex-reduce-config-p)
                              'config))
    :returns (res svex-p :hyp (svex-p x))

    (case-match x
      (('sv::bitxor a b)
       (cond ((equal a 1)
              (svex-reduce-w/-env-apply 'sv::unfloat (hons-list b)))
             ((equal b 1)
              (svex-reduce-w/-env-apply 'sv::unfloat (hons-list a)))
             ((bitxor-has-1 a)
              (bitand/or/xor-simple-constant-simplify 'sv::bitxor
                                                      (remove-1-from-xor a) b))
             ((bitxor-has-1 b)
              (bitand/or/xor-simple-constant-simplify 'sv::bitxor
                                                      a
                                                      (remove-1-from-xor b)))
             (t x)
             ))
      (& (if (equal x 1) 0 x))))

  (define clear-1s-from-bitxor ((x svex-p)
                                &key
                                ((config svex-reduce-config-p)
                                 'config))
    :returns (res svex-p :hyp (svex-p x))
    (case-match x
      (('sv::bitxor a b)
       (b* (((unless (and (bitxor-has-1 a)
                          (bitxor-has-1 b)))
             x)
            (a (remove-1-from-xor a))
            (b (remove-1-from-xor b)))
         (bitand/or/xor-simple-constant-simplify 'sv::bitxor a b)))
      (& x)))

  ;;(clear-1s-from-bitxor `(bitxor (bitxor 1 x) (bitxor (bitxor 1 y) z)))
  ;; returns:
  ;; (BITXOR X (BITXOR Y Z))
  )

(define bitand/or/xor-collect-leaves ((svex)
                                      (fn)
                                      &key
                                      ((limit integerp) 'leave-depth))
  :Returns (leaves sv::Svexlist-p :hyp (and (sv::Svex-p svex)
                                            (not (equal fn ':var)))
                   :hints (("Goal"
                            :in-theory (e/d (svex-p
                                             4vec-p)
                                            ()))))
  :prepwork
  (
   ;; TODO: (partial) memoization can help here  to increase the limit. This may
   ;; require having a very large limit though, which might be bad again.
   (defconst *bitand/or/xor-collect-leaves-limit*
     4))
  (case-match svex
    ((this-fn x y)
     (if (and (> limit 0)
              (equal this-fn fn))
         (cons svex (append (bitand/or/xor-collect-leaves x fn :limit (1- limit))
                            (bitand/or/xor-collect-leaves y fn :limit (1- limit))))
       (list svex)))
    #|(('id x)
    (list svex x))|#
    (& (list svex)))
  ///
  (defret true-listp-of-<fn>
    (true-listp leaves)))

(define member-hons-equal (x lst)
  (if (atom lst)
      nil
    (or (hons-equal x (car lst))
        (member-hons-equal x (cdr lst))))
  ///
  (defthm member-hons-equal-is-member-equal
    (iff (member-hons-equal x lst)
         (member-equal x lst))))

(define member-hons-equal-of-negated (x lst)
  (if (atom lst)
      nil
    (or (b* ((cur (car lst)))
          (case-match cur
            (('sv::bitxor 1 n)
             (hons-equal x n))
            (('sv::bitxor n 1)
             (hons-equal x n))))
        (member-hons-equal-of-negated x (cdr lst))))
  )

(define bitand/bitor-cancel-repeated-aux ((svex sv::svex-p)
                                          (leaves svexlist-p)
                                          (new-val integerp)
                                          &key
                                          (under-xor 'under-xor)
                                          ((limit natp) '*bitand/bitor-cancel-repeated-aux-limit*)
                                          ;;((require-integerp booleanp) 'require-integerp)
                                          ((env) 'env)
                                          ((context rp::rp-term-listp) 'context)
                                          ((config svex-reduce-config-p) 'config))
  :verify-guards nil
  :prepwork
  (
   ;; TODO: (partial) memoization can help here  to increase the limit. This may
   ;; require having a very large limit though, which might be bad again.
   (defconst *bitand/bitor-cancel-repeated-aux-limit*
     6))

  :returns (mv (simplified-svex sv::svex-p
                                :hyp (and (sv::svex-p svex)
                                          (sv::Svex-p new-val))
                                :hints (("Goal"
                                         :in-theory (e/d (sv::Svex-p) ()))))
               changed)
  (cond
   ((zp limit)
    (mv svex nil))
   ((member-hons-equal svex leaves)
    (b* (((Unless (and under-xor
                       (not (equal new-val 0))))
          (mv new-val t))
         (width (width-of-svex svex))
         ((Unless width)
          (mv new-val t)))
      (mv (4vec-part-select 0 width new-val) t)))
   ((mbe :exec (and (member-hons-equal-of-negated svex leaves)
                    (equal (width-of-svex svex) 1)
                    (integerp-of-svex svex))
         ;; I should find a better way than this mbe stuff..
         :logic (and* (member-hons-equal-of-negated svex leaves)
                      (equal (width-of-svex svex) 1)
                      (integerp-of-svex svex)))
    (mv (4vec-part-select 0 1 (lognot new-val)) t))
   ((and (consp svex)
         (equal (car svex) 'sv::bitor)
         (equal-len (cdr svex) 2))
    (b* ((x (first (cdr svex))) (y (second (cdr svex)))
         ((mv x changed-x) (bitand/bitor-cancel-repeated-aux x leaves new-val :limit (1- limit)))
         ((mv y changed-y) (bitand/bitor-cancel-repeated-aux y leaves new-val :limit (1- limit))))
      (if (or changed-x
              changed-y)
          (mv (bitand/or/xor-simple-constant-simplify 'sv::bitor x y) t)
        (mv svex nil))))
   ((and (consp svex)
         (equal (car svex) 'sv::bitand)
         (equal-len (cdr svex) 2))
    (b* ((x (first (cdr svex))) (y (second (cdr svex)))
         ((mv x changed-x) (bitand/bitor-cancel-repeated-aux x leaves new-val :limit (1- limit)))
         ((mv y changed-y) (bitand/bitor-cancel-repeated-aux y leaves new-val :limit (1- limit))))
      (if (or changed-x
              changed-y)
          (mv (bitand/or/xor-simple-constant-simplify 'sv::bitand x y) t)
        (mv svex nil))))
   ((and (consp svex)
         (equal (car svex) 'sv::bitxor)
         (equal-len (cdr svex) 2))
    (b* ((x (first (cdr svex))) (y (second (cdr svex)))
         ((mv new-x changed-x) (bitand/bitor-cancel-repeated-aux x leaves new-val :limit (+ limit -1) :under-xor t))
         ((mv new-y changed-y) (bitand/bitor-cancel-repeated-aux y leaves new-val :limit (+ limit -1) :under-xor t))
         ((Unless (and (or changed-x changed-y) ;; this is and not and* becasue
                       ;; don't want to run integer-listp-of-svexlist if first
                       ;; test fails.
                       (or (integer-listp-of-svexlist leaves)
                           (rp::cwe "integer-listp-of-svexlist check has failed for ~p0~%" leaves))))
          (mv svex nil))
         (res (bitand/or/xor-simple-constant-simplify 'sv::bitxor new-x new-y))
         (res (clear-1s-from-bitxor res)))
      (mv res t)))
   #|((and (consp svex)
   (equal (car svex) 'sv::id)
   (equal-len (cdr svex) 1))
   (b* (((mv res changed)
   (bitand/bitor-cancel-repeated-aux (cadr svex) leaves new-val :limit (1- limit))))
   (if changed
   (mv (sv::svex-call 'id (hons-list res)) t)
   (mv svex nil))))|#
   (t (mv svex nil)))

  ///

  (verify-guards bitand/bitor-cancel-repeated-aux-fn
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (SVEX-P) ())))))

(defsection bitxor-cancel-repeated-aux-functions
  ;; TODO: Maybe a limit should be imposed for cancelling repeated in bitxor...

  (defconst *bitxor-cancel-repeated-limit*
    5)

  (define bitxor-collect-repeated (svex
                                   leaves
                                   (limit natp)
                                   &key
                                   (collect-4vecs 'collect-4vecs))
    :Returns (commons sv::Svexlist-p :hyp (and (sv::Svex-p svex))
                      :hints (("Goal"
                               :in-theory (e/d (svex-p
                                                4vec-p)
                                               ()))))
    ;; Using the leaves from the other arg of bitxor, find the commons.
    (cond
     ((zp limit)
      nil)
     ((member-hons-equal svex leaves)
      (and (or collect-4vecs (not (4vec-p svex))) ;; don't clear constants as they likely come from bitnot.
           (list svex)))
     (t
      (case-match svex
        (('bitxor x y)
         (append (bitxor-collect-repeated x leaves (1- limit))
                 (bitxor-collect-repeated y leaves (1- limit))))))))

  (define bitxor-remove-node ((svex svex-p)
                              (node-to-remove)
                              (limit natp)
                              &key
                              ((config svex-reduce-config-p) 'config))
    :returns (mv (res-svex svex-p :hyp (svex-p svex))
                 success)
    ;; try to remove a node from an svex.
    :verify-guards :after-returns
    (cond
     ((zp limit)
      (mv svex nil))
     ((hons-equal svex node-to-remove)
      (mv 0 t))
     (t
      (case-match svex
        (('bitxor x y)
         (b* (((mv new-x success-x)
               (bitxor-remove-node x node-to-remove (1- limit)))
              ((when success-x) ;; allowed to be replaced only once.
               (mv (bitand/or/xor-simple-constant-simplify 'sv::bitxor new-x y) t))
              ((mv new-y success-y)
               (bitxor-remove-node y node-to-remove (1- limit))))
           (if success-y
               (mv (bitand/or/xor-simple-constant-simplify 'sv::bitxor x new-y) t)
             (mv svex nil))))
        (& (mv svex nil))))))

  (define bitxor-remove-nodes-from-both ((svex1 svex-p)
                                         (svex2 svex-p)
                                         (nodes-to-remove svexlist-p)
                                         &key
                                         ((env) 'env)
                                         ((context rp::rp-term-listp) 'context)
                                         ((config svex-reduce-config-p) 'config))
    :returns (mv (res-svex1 svex-p :hyp (svex-p svex1))
                 (res-svex2 svex-p :hyp (svex-p svex2)))
    ;; Try removing from both svexes at the same time.
    (if (atom nodes-to-remove)
        (mv svex1 svex2)
      (b* ((limit *bitxor-cancel-repeated-limit*)
           ((mv new-svex1 success-1)
            (bitxor-remove-node svex1 (car nodes-to-remove) limit))
           ((Unless success-1) ;; expected to never happen
            (bitxor-remove-nodes-from-both svex1 svex2 (cdr nodes-to-remove)))
           ((mv new-svex2 success-2)
            (bitxor-remove-node svex2 (car nodes-to-remove) limit))
           ((Unless success-2) ;; expected to never happen
            (bitxor-remove-nodes-from-both svex1 svex2 (cdr nodes-to-remove)))
           ((unless (integerp-of-svex (car nodes-to-remove)))
            (progn$ (rp::cwe "integerp-of-svex check has failed for ~p0~%" (car nodes-to-remove))
                    (bitxor-remove-nodes-from-both svex1 svex2 (cdr nodes-to-remove)))))

        (bitxor-remove-nodes-from-both new-svex1 new-svex2 (cdr nodes-to-remove))))))

(define extract-from-unfloat (x)
  :Returns (res svex-p :hyp (svex-p x))
  (case-match x
    (('sv::unfloat y)
     (extract-from-unfloat y))
    (& x)))

(define bitand/or/xor-cancel-repeated ((fn)
                                       (x sv::svex-p)
                                       (y sv::svex-p)
                                       &key
                                       ((leave-depth integerp)
                                        '*bitand/bitor-cancel-repeated-aux-limit*)
                                       ((env) 'env)
                                       ((context rp::rp-term-listp) 'context)
                                       ((config svex-reduce-config-p) 'config))

  :returns (simplified-svex sv::Svex-p :hyp (and (sv::fnsym-p fn)
                                                 (Not (equal fn :var))
                                                 (svex-p x)
                                                 (svex-p y)))
  (b* (((Unless (or (equal fn 'sv::bitxor)
                    (equal fn 'sv::bitand)
                    (equal fn 'sv::bitor)))
        (svex-reduce-w/-env-apply fn (hons-list x y)))
       (x (extract-from-unfloat x))
       (y (extract-from-unfloat y))
       ((svex-reduce-config config))
       ((when config.skip-bitor/and/xor-repeated)
        (bitand/or/xor-simple-constant-simplify fn x y)))
    (case fn
      (sv::bitor
       (b* ((under-xor nil)
            (l1 (bitand/or/xor-collect-leaves x 'sv::bitor))
            ((mv y changed-y) (bitand/bitor-cancel-repeated-aux y l1 0))
            (l2 (bitand/or/xor-collect-leaves y 'sv::bitor))
            ((mv x changed-x) (bitand/bitor-cancel-repeated-aux x l2  0)))
         (if (or changed-x changed-y)
             (bitand/or/xor-simple-constant-simplify 'sv::bitor x y)
           (svex-reduce-w/-env-apply fn (hons-list x y)))))
      (sv::bitand
       (b* ((under-xor nil)
            (l1 (bitand/or/xor-collect-leaves x 'sv::bitand))
            ((mv y changed-y) (bitand/bitor-cancel-repeated-aux y l1  -1))
            (l2 (bitand/or/xor-collect-leaves y 'sv::bitand))
            ((mv x changed-x) (bitand/bitor-cancel-repeated-aux x l2  -1))
            (result
             (if (or changed-x changed-y)
                 (bitand/or/xor-simple-constant-simplify 'sv::bitand x y)
               (svex-reduce-w/-env-apply fn (hons-list x y))))
            #|(- (and (bitand-xor-bad-pattern result)
            (acl2::raise "Found bitand-xor-bad-pattern. Input fn: ~p0, x:~p1, y:~p2. Result: ~p3~%" ; ;
            fn x y result)))|#)
         result))
      (sv::bitxor
       (b* ((collect-4vecs (or* (integerp x) (integerp y)))
            (limit *bitxor-cancel-repeated-limit*)
            (leaves (bitand/or/xor-collect-leaves x 'sv::bitxor))
            (commons (bitxor-collect-repeated y leaves limit))
            #|(- (and commons
            (rp::cwe "Some commons in botxor are found: ~p0 in x:~p1 and y:~p2~%" commons x y)))|#
            ((mv x y) (bitxor-remove-nodes-from-both x y commons))
            (result (bitand/or/xor-simple-constant-simplify fn x y)))
         result
         ))
      (otherwise
       (svex-reduce-w/-env-apply fn (hons-list x y))))))

;; (bitand/or/xor-cancel-repeated '(sv::Bitand (sv::Bitand a b)
;;                                            (sv::bitand (sv::bitor a x) y)))
;; returns:
;; (BITAND (BITAND A B) Y)

;; (bitand/or/xor-cancel-repeated '(sv::Bitor (sv::Bitor a b)
;;                                           (sv::bitand (sv::bitor a x) y)))
;; returns:
;; (SV::BITOR (SV::BITOR A B) (BITAND X Y))

;; (bitand/or/xor-cancel-repeated '(sv::Bitor a (sv::bitxor 1 a)))
;; returns:
;; 1

;; (bitand/or/xor-cancel-repeated 'sv::bitand `x `(sv::bitxor x y)
;;                               :env (make-fast-alist `((x . x) (y . y)))
;;                               :context `((integerp x) (Integerp y)))
;; returns
;; (BITAND X (BITXOR -1 Y))
;;)

;; (bitand/or/xor-cancel-repeated 'sv::bitxor
;;                                `(sv::bitxor (sv::bitxor x y) z) `(bitxor a (sv::bitxor x y))
;;                                :env (make-fast-alist `((x . x) (y . y)))
;;                                :context `((integerp x) (Integerp y)))
;; returns
;; (BITXOR Z A)

(defines svex-simplify-bitand/or/xor
  :verify-guards nil
  :flag-local nil
  (define svex-simplify-bitand/or/xor ((x svex-p)
                                       &key
                                       ((env) 'env)
                                       ((context rp::rp-term-listp) 'context)
                                       ((config svex-reduce-config-p) 'config))
    :measure (sv::svex-count x)
    :returns (res svex-p :hyp (svex-p x))
    (sv::svex-case
     x
     :var x
     :quote x
     :call
     (cond ((and (equal-len x.args 2)
                 (or (equal x.fn 'sv::bitxor)
                     (equal x.fn 'sv::bitor)
                     (equal x.fn 'sv::bitand)))
            (bitand/or/xor-cancel-repeated
             x.fn
             (svex-simplify-bitand/or/xor (first x.args))
             (svex-simplify-bitand/or/xor (second x.args))))
           (t (sv::svex-call x.fn
                             (svexlist-simplify-bitand/or/xor x.args))))))
  (define svexlist-simplify-bitand/or/xor ((lst svexlist-p)
                                           &key
                                           ((env) 'env)
                                           ((context rp::rp-term-listp) 'context)
                                           ((config svex-reduce-config-p) 'config))
    :measure (sv::svexlist-count lst)
    :returns (res svexlist-p :hyp (svexlist-p lst))
    (if (atom lst)
        nil
      (hons (svex-simplify-bitand/or/xor (car lst))
            (svexlist-simplify-bitand/or/xor (cdr lst)))))
  ///
  (verify-guards svex-simplify-bitand/or/xor-fn)
  (memoize 'svex-simplify-bitand/or/xor
           :condition '(equal (svex-kind x) :call)
           ))

(define svex-alist-simplify-bitand/or/xor ((alist sv::svex-alist-p)
                                           &key
                                           ((env) 'env)
                                           ((context rp::rp-term-listp) 'context)
                                           ((config svex-reduce-config-p) 'config))
  :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p alist))
  (if (atom alist)
      nil
    (acons (caar alist)
           (svex-simplify-bitand/or/xor (cdar alist))
           (svex-alist-simplify-bitand/or/xor (cdr alist)))))

(defines svex-simplify-bitand/or/xor-outside-in
  :verify-guards nil
  :flag-local nil
  (define svex-simplify-bitand/or/xor-outside-in ((x svex-p)
                                                  &key
                                                  ((env) 'env)
                                                  ((context rp::rp-term-listp) 'context)
                                                  ((config svex-reduce-config-p) 'config)
                                                  (skip 'nil)
                                                  ((limit natp) 'limit))
    :measure (nfix limit)
    :returns (res svex-p :hyp (svex-p x))
    :no-function t
    (if (zp limit)
        x
      (let ((limit (1- limit)))
        (sv::svex-case
         x
         :var x
         :quote x
         :call
         (cond ((and (equal-len x.args 2)
                     (or (equal x.fn 'sv::bitxor)
                         (equal x.fn 'sv::bitor)
                         (equal x.fn 'sv::bitand)))
                (b* ((res (if skip
                              x
                            (bitand/or/xor-cancel-repeated x.fn (first x.args) (second x.args))))
                     ((unless (equal res x))
                      (svex-simplify-bitand/or/xor-outside-in res :skip t)))
                  (bitand/or/xor-simple-constant-simplify
                   x.fn
                   (svex-simplify-bitand/or/xor-outside-in (first x.args))
                   (svex-simplify-bitand/or/xor-outside-in (second x.args)))))
               (t (sv::svex-call x.fn
                                 (svexlist-simplify-bitand/or/xor-outside-in x.args))))))))
  (define svexlist-simplify-bitand/or/xor-outside-in ((lst svexlist-p)
                                                      &key
                                                      ((env) 'env)
                                                      ((context rp::rp-term-listp) 'context)
                                                      ((config svex-reduce-config-p) 'config)
                                                      ((limit natp) 'limit))
    :measure (nfix limit)
    :returns (res svexlist-p :hyp (svexlist-p lst))
    :no-function t
    (if (zp limit)
        lst
      (let ((limit (1- limit)))
        (if (atom lst)
            nil
          (hons (svex-simplify-bitand/or/xor-outside-in (car lst))
                (svexlist-simplify-bitand/or/xor-outside-in (cdr lst)))))))
  ///
  (verify-guards svex-simplify-bitand/or/xor-outside-in-fn)

  (acl2::memoize-partial
   ((svex-simplify-bitand/or/xor-outside-in*-fn svex-simplify-bitand/or/xor-outside-in-fn
                                                :condition '(and (equal (svex-kind x) :call)
                                                                 (not skip)))
    (svexlist-simplify-bitand/or/xor-outside-in*-fn svexlist-simplify-bitand/or/xor-outside-in-fn
                                                    :condition nil)))

  (defmacro svex-simplify-bitand/or/xor-outside-in* (x
                                                     &key
                                                     (env 'env)
                                                     (context 'context)
                                                     (config 'config))
    `(svex-simplify-bitand/or/xor-outside-in*-fn ,x ,env ,context ,config nil)))

(define svex-alist-simplify-bitand/or/xor-outside-in ((alist sv::svex-alist-p)
                                                      &key
                                                      ((env) 'env)
                                                      ((context rp::rp-term-listp) 'context)
                                                      ((config svex-reduce-config-p) 'config))
  :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p alist))
  (if (atom alist)
      nil
    (acons (caar alist)
           (svex-simplify-bitand/or/xor-outside-in* (cdar alist))
           (svex-alist-simplify-bitand/or/xor-outside-in (cdr alist)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proofs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (svex-eval-lemma-tmpl
  (defthm svex-eval-opener-when-call
    (implies (and (syntaxp (and (consp fn)
                                (quotep fn)))
                  (fnsym-p fn))
             (equal (svex-eval (cons fn args) env)
                    (SV::SVEX-APPLY fn
                                    (svexlist-eval args env))))
    :hints (("Goal"
             :expand (svex-eval (cons fn args) env)
             :in-theory (e/d (SVEX-CALL->FN
                              SVEX-VAR->NAME
                              SVEX-KIND
                              SVEX-CALL->ARGS)
                             ()))))))

(local
 (defthm 4vec-bitor-of-1
   (equal (4vec-bitor -1 then)
          -1)
   :hints (("goal"
            :expand (4vec-bitor -1 then)
            :in-theory (e/d (sv::3vec-bitor) ())))))

(local
 (defsection single-bit-part-select-case-splitter

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

(defun single-bit-4vec-p (x)
  (equal (4vec-part-select 0 1 x)
         x))

(svex-eval-lemma-tmpl
 (progn
   (defun svex-eval-bitand-lst (lst env)
     (if (atom lst)
         -1
       (4vec-bitand (svex-eval (car lst) env)
                    (svex-eval-bitand-lst (cdr lst) env))))

   (defun svex-eval-bitxor-lst (lst env)
     (if (atom lst)
         0
       (sv::4vec-bitxor (svex-eval (car lst) env)
                        (svex-eval-bitxor-lst (cdr lst) env))))

   (defun svex-eval-bitor-lst (lst env)
     (if (atom lst)
         0
       (4vec-bitor (svex-eval (car lst) env)
                   (svex-eval-bitor-lst (cdr lst) env))))))

(local
 (svex-eval-lemma-tmpl
  (progn
    (defthm 3vec-p-of-svex-eval-bitor-lst
      (sv::3vec-p (svex-eval-bitor-lst lst env)))

    (defthm 3vec-p-of-svex-eval-bitxor-lst
      (sv::3vec-p (svex-eval-bitxor-lst lst env)))

    (defthm 3vec-p-of-svex-eval-bitand-lst
      (sv::3vec-p (svex-eval-bitand-lst lst env)))

    (defthm 4vec-p-of-svex-eval-bitor-lst
      (sv::4vec-p (svex-eval-bitor-lst lst env)))

    (defthm 4vec-p-of-svex-eval-bitxor-lst
      (sv::4vec-p (svex-eval-bitxor-lst lst env)))

    (defthm 4vec-p-of-svex-eval-bitand-lst
      (sv::4vec-p (svex-eval-bitand-lst lst env))))))

(local
 (svex-eval-lemma-tmpl
  (defthm when-svex-eval-bitor-lst-evals-to-zero
    (implies (and (equal (4vec-part-select 0 1 (svex-eval-bitor-lst leaves env))
                         0)
                  (member-equal svex leaves))
             (equal (4vec-part-select 0 1 (svex-eval svex env))
                    0))
    :otf-flg t
    :hints (("goal"
             :do-not-induct t
             :induct (svex-eval-bitor-lst leaves env)
             :in-theory (e/d (svex-eval-bitor-lst
                              4vec-part-select-of-4vec-bitor-better
                              member-equal)
                             ()))
            (and stable-under-simplificationp
                 '(:use ((:instance when-4vec-bitor-is-zero
                                    (x (4VEC-PART-SELECT 0 1 (SVEX-EVAL-BITOR-LST (CDR LEAVES) ENV)))
                                    (y (4VEC-PART-SELECT 0 1 (SVEX-EVAL (CAR
                                                                         LEAVES) ENV)))))))))))

(local
 (svex-eval-lemma-tmpl
  (defthm when-svex-eval-bitand-lst-evals-to-one
    (implies (and (equal (4vec-part-select 0 1 (svex-eval-bitand-lst leaves env))
                         1)
                  (member-equal svex leaves))
             (equal (4vec-part-select 0 1 (svex-eval svex env))
                    1))
    :otf-flg t
    :hints (("goal"
             :do-not-induct t
             :induct (svex-eval-bitand-lst leaves env)
             :in-theory (e/d (svex-eval-bitand-lst
                              4vec-part-select-of-4vec-bitand-better
                              member-equal)
                             ()))
            (and stable-under-simplificationp
                 '(:use ((:instance WHEN-4VEC-BITAND-IS-ONE-WITH-ONE-BIT-MASK
                                    (x (4VEC-PART-SELECT 0 1 (Svex-Eval-Bitand-Lst (CDR LEAVES) ENV)))
                                    (y (4VEC-PART-SELECT 0 1 (SVEX-EVAL (CAR LEAVES) ENV)))))))))))

(local
 (svex-eval-lemma-tmpl
  (defthm when-svex-eval-bitor-lst-evals-to-nonzero
    (implies (and (equal (4vec-part-select 0 1 (svex-eval svex env))
                         1)
                  (member-equal svex leaves))
             (equal (4vec-part-select 0 1 (svex-eval-bitor-lst leaves env))
                    1))
    :otf-flg t
    :hints (("goal"
             :do-not-induct t
             :induct (svex-eval-bitor-lst leaves env)
             :in-theory (e/d (svex-eval-bitor-lst
                              4vec-part-select-of-4vec-bitor-better
                              member-equal
                              PUSH-3VEC-FIX-INTO-4VEC-PART-SELECT)
                             (4VEC-PART-SELECT-OF-3VEC-FIX
                              ;;
                              )))))))

(local
 (svex-eval-lemma-tmpl
  (defthm when-svex-eval-bitand-lst-evals-to-0
    (implies (and (equal (4vec-part-select 0 1 (svex-eval svex env))
                         0)
                  (member-equal svex leaves))
             (equal (4vec-part-select 0 1 (svex-eval-bitand-lst leaves env))
                    0))
    :otf-flg t
    :hints (("goal"
             :do-not-induct t
             :induct (svex-eval-bitand-lst leaves env)
             :in-theory (e/d (svex-eval-bitand-lst
                              4vec-part-select-of-4vec-bitand-better
                              member-equal
                              push-3vec-fix-into-4vec-part-select)
                             (4vec-part-select-of-3vec-fix
                              ;;
                              )))))))

(local
 (svex-eval-lemma-tmpl
  (defthm svex-eval-when-fnc-is-bitand
    (implies (and  (equal (car svex) 'bitand)
                   (consp (cdr svex))
                   (consp (cddr svex))
                   (not (cdddr svex)))
             (equal (svex-eval svex env)
                    (4vec-bitand (svex-eval (cadr svex) env)
                                 (svex-eval (caddr svex) env))))
    :hints (("goal"
             :expand ((svex-eval svex env))
             :in-theory (e/d (svex-kind
                              svex-apply
                              svex-call->args
                              svex-call->fn )
                             ()))))))

(local
 (svex-eval-lemma-tmpl
  (defthm svex-eval-when-fnc-is-bitor
    (implies (and  (equal (car svex) 'sv::bitor)
                   (consp (cdr svex))
                   (consp (cddr svex))
                   (not (cdddr svex)))
             (equal (svex-eval svex env)
                    (4vec-bitor (svex-eval (cadr svex) env)
                                (svex-eval (caddr svex) env))))
    :hints (("goal"
             :expand ((svex-eval svex env))
             :in-theory (e/d (svex-kind
                              svex-apply
                              svex-call->args
                              svex-call->fn )
                             ()))))))

(local
 (svex-eval-lemma-tmpl
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
                             ()))))))

(local
 (svex-eval-lemma-tmpl
  (defthmd svex-eval-of-4vec-p
    (implies (4vec-p x)
             (equal (svex-eval x env)
                    x))
    :rule-classes :rewrite
    :hints (("Goal"
             :in-theory (e/d (svex-eval svex-kind SV::SVEX-QUOTE->VAL svex-p 4vec-p) ()))))))

(local
 (defthmd 4vec-rsh-1-of-single-bit
   (implies (equal (4vec-part-select 0 1 x) x)
            (equal (4vec-rsh 1 x) 0))))

(local
 (in-theory (disable sv::svex-apply$-is-svex-apply)))

(svex-eval-lemma-tmpl
 (defthm svex-eval-of-bitand/or/xor-simple-constant-simplify-correct-1
   (implies (and (fnsym-p fn)
                 (svex-p arg1)
                 (svex-p arg2)

                 (:@ :dollar-eval
                     (width-of-svex-extn-correct<$>-lst
                      (svex-reduce-config->width-extns config)))
                 (:@ :normal-eval
                     (equal (svex-reduce-config->width-extns config) nil))
                 )
            (equal (svex-eval (bitand/or/xor-simple-constant-simplify fn arg1 arg2)
                              env)
                   (svex-eval `(,fn ,arg1 ,arg2) env)))
   :hints (("goal"
            :in-theory (e/d (svex-apply
                             4vec-rsh-1-of-single-bit
                             svex-eval-of-4vec-p
                             bitand/or/xor-simple-constant-simplify) ;
                            ())))))

(svex-eval-lemma-tmpl
 (defthm svex-eval-of-bitand/or/xor-simple-constant-simplify-correct-2
   (implies (and (fnsym-p fn)
                 (single-bit-4vec-p (svex-eval arg1 env))
                 (single-bit-4vec-p (svex-eval arg2 env)))
            (equal (svex-eval (bitand/or/xor-simple-constant-simplify fn arg1
                                                                      arg2 :1masked t)
                              env)
                   (svex-eval `(,fn ,arg1 ,arg2) env)))
   :otf-flg t
   :hints (("goal"
            :in-theory (e/d (svex-apply
                             svex-eval-of-4vec-p
                             and*
                             bitand/or/xor-simple-constant-simplify) ;
                            ()))
           (and stable-under-simplificationp
                '(:clause-processor
                  (single-bit-part-select-case-splitter clause))))))

(local
 (defthm 4vec-bitand-of-same-2
   (equal (4vec-bitand x (4vec-bitand x a))
          (4vec-bitand x a))))

(local
 (svex-eval-lemma-tmpl
  (progn
    (defthm svex-eval-bitor-lst-ored-with-a-member
      (implies (member-equal svex leaves)
               (equal (4vec-bitor (svex-eval-bitor-lst leaves env)
                                  (svex-eval svex env))
                      (svex-eval-bitor-lst leaves env)))
      :hints (("goal"
               :in-theory (e/d (svex-eval-bitor-lst) ()))))

    (defthm svex-eval-bitand-lst-anded-with-a-member
      (implies (member-equal svex leaves)
               (equal (4vec-bitand (svex-eval-bitand-lst leaves env)
                                   (svex-eval svex env))
                      (svex-eval-bitand-lst leaves env)))
      :hints (("goal"
               :in-theory (e/d (svex-eval-bitand-lst) ())))))))

(local
 (svex-eval-lemma-tmpl
  (progn
    (defthm integerp-of-svex-eval-bitor-lst
      (implies (and
                (sv::svexlist-p lst)
                (rp::rp-term-listp context)
                (integer-listp-of-svexlist lst)
                (rp::valid-sc env-term a)
                (rp::eval-and-all context a)
                (sub-alistp env big-env)
                (rp::falist-consistent-aux big-env env-term)
                (:@ :dollar-eval
                    (integerp-of-svex-extn-correct<$>-lst
                     (svex-reduce-config->integerp-extns config)))
                (:@ :normal-eval
                    (equal (svex-reduce-config->integerp-extns config) nil))
                (or* (svex-reduce-config->keep-missing-env-vars config)
                     (equal big-env env)))
               (integerp (svex-eval-bitor-lst lst (rp-evlt env-term a))))
      :hints (("Goal"
               :induct (len lst)
               :do-not-induct t
               :in-theory (e/d (svex-eval-bitor-lst
                                integer-listp-of-svexlist)
                               (sub-alistp
                                rp::falist-consistent-aux
                                rp::eval-and-all
                                rp-trans)))))

    (defthm integerp-of-svex-eval-bitor-lst-env=nil
      (implies (and
                (sv::svexlist-p lst)
                (integer-listp-of-svexlist lst :env nil)
                (:@ :dollar-eval
                    (integerp-of-svex-extn-correct<$>-lst
                     (svex-reduce-config->integerp-extns config)))
                (:@ :normal-eval
                    (equal (svex-reduce-config->integerp-extns config) nil))
                (svex-reduce-config->keep-missing-env-vars config))
               (integerp (svex-eval-bitor-lst lst svex-env)))
      :hints (("Goal"
               :induct (len lst)
               :do-not-induct t
               :in-theory (e/d (svex-eval-bitor-lst
                                integer-listp-of-svexlist)
                               (sub-alistp
                                rp::falist-consistent-aux
                                rp::eval-and-all
                                rp-trans)))))

    (defthm integerp-of-svex-eval-bitand-lst
      (implies (and
                (sv::svexlist-p lst)
                (rp::rp-term-listp context)
                (integer-listp-of-svexlist lst )
                (rp::valid-sc env-term a)
                (rp::eval-and-all context a)
                (sub-alistp env big-env)
                (rp::falist-consistent-aux big-env env-term)
                (:@ :dollar-eval
                    (integerp-of-svex-extn-correct<$>-lst
                     (svex-reduce-config->integerp-extns config)))
                (:@ :normal-eval
                    (equal (svex-reduce-config->integerp-extns config) nil))
                (or* (svex-reduce-config->keep-missing-env-vars config)
                     (equal big-env env)))
               (integerp (svex-eval-bitand-lst lst (rp-evlt env-term a))))
      :hints (("Goal"
               :induct (len lst)
               :do-not-induct t
               :in-theory (e/d (svex-eval-bitand-lst
                                INTEGER-LISTP-OF-SVEXLIST)
                               (rp::falist-consistent-aux
                                rp::eval-and-all
                                rp-trans)))))

    (defthm integerp-of-svex-eval-bitand-lst-env=nil
      (implies (and
                (sv::svexlist-p lst)
                (integer-listp-of-svexlist lst :env nil)
                (:@ :dollar-eval
                    (integerp-of-svex-extn-correct<$>-lst
                     (svex-reduce-config->integerp-extns config)))
                (:@ :normal-eval
                    (equal (svex-reduce-config->integerp-extns config) nil))
                (svex-reduce-config->keep-missing-env-vars config))
               (integerp (svex-eval-bitand-lst lst svex-env)))
      :hints (("Goal"
               :induct (len lst)
               :do-not-induct t
               :in-theory (e/d (svex-eval-bitand-lst
                                INTEGER-LISTP-OF-SVEXLIST)
                               (rp::falist-consistent-aux
                                rp::eval-and-all
                                rp-trans))))))))

(local
 (svex-eval-lemma-tmpl
  (defthmd svex-eval-of-4vec
    (implies (4vec-p x)
             (equal (svex-eval x a)
                    x))
    :hints (("Goal"
             :in-theory (e/d (svex-eval
                              4vec-p
                              SV::SVEX-QUOTE->VAL
                              svex-kind)
                             ()))))))

(progn
  (local
   (defthm 4vec-bitxor-of-two-ones
     (equal (SV::4VEC-BITXOR x (SV::4VEC-BITXOR 1 1))
            (sv::3vec-fix x))
     :hints (("Goal"
              :in-theory (e/d ()
                              (4vec)))
             )))

  (local
   (defthm 4vec-bitxor-of-two-ones-2
     (equal (SV::4VEC-BITXOR 1 (SV::4VEC-BITXOR 1 x))
            (sv::3vec-fix x))
     :hints (("Goal"
              :use ((:instance 4vec-bitxor-of-two-ones))
              :in-theory (e/d ()
                              (4vec-bitxor-of-two-ones
                               (:e sv::4vec-bitxor)
                               4vec)))
             )))

  (local
   (svex-eval-lemma-tmpl
    (defthm svex-eval-of-clear-1s-from-bitxor-correct-lemma
      (implies (and (bitxor-has-1 x)
                    (svex-p x)
                    (:@ :dollar-eval
                        (width-of-svex-extn-correct<$>-lst
                         (svex-reduce-config->width-extns config)))
                    (:@ :normal-eval
                        (equal (svex-reduce-config->width-extns config) nil)))
               (equal (svex-eval (remove-1-from-xor x) env)

                      (sv::4vec-bitxor 1
                                       (svex-eval x env))))
      :hints (("goal"
               :in-theory (e/d (bitxor-has-1
                                svex-apply
                                remove-1-from-xor)
                               ()))))))

  (local
   (svex-eval-lemma-tmpl
    (defret svex-eval-of-clear-1s-from-bitxor-correct
      (implies (and (svex-p x)
                    (:@ :dollar-eval
                        (width-of-svex-extn-correct<$>-lst
                         (svex-reduce-config->width-extns config)))
                    (:@ :normal-eval
                        (equal (svex-reduce-config->width-extns config) nil)))
               (equal (svex-eval res env)
                      (svex-eval x env)))
      :fn clear-1s-from-bitxor
      :hints (("goal"
               :in-theory (e/d (clear-1s-from-bitxor) ())))))))

(local
 (in-theory (disable rp::falist-consistent-aux
                     rp::eval-and-all)))

#|(skip-proofs
(svex-eval-lemma-tmpl
(local
(defthm when-width-of-svex-is-1-its-rsh-is-0
(implies (EQUAL (WIDTH-OF-SVEX SVEX) 1)
(EQUAL (4VEC-RSH 1
(SV::3VEC-FIX (SVEX-EVAL SVEX SVEX-ENV)))
0))))))|#

(local
 (svex-eval-lemma-tmpl
  (defthm svex-eval-member-hons-equal-of-negated-lemma-1
    (implies (and (member-hons-equal-of-negated svex leaves)
                  (integerp (svex-eval svex svex-env))
                  (equal (4vec-part-select 0 1 (svex-eval svex svex-env))
                         0))
             (equal (4vec-part-select 0 1 (svex-eval-bitor-lst leaves svex-env))
                    1))
    :hints (("Goal"
             :induct (MEMBER-HONS-EQUAL-OF-NEGATED SVEX LEAVES)
             :do-not-induct t
             :Expand ((SVEX-EVAL-BITOR-LST LEAVES SVEX-ENV))
             :in-theory (e/d (4vec-rsh-of-3vec-fix
                              MEMBER-HONS-EQUAL-OF-NEGATED
                              4VEC-PART-SELECT-OF-4VEC-BITOR-BETTER
                              4VEC-PART-SELECT-OF-4VEC-BITXOR-BETTER)
                             ()))))))

(local
 (svex-eval-lemma-tmpl
  (defthm dummy-integerp-of-svex-lemma-for-svex-eval
    (implies (integerp (SVEX-EVAL SVEX SVEX-ENV))
             (and (not (EQUAL (SVEX-EVAL SVEX SVEX-ENV)
                              '(1 . 0)))
                  (not (EQUAL (SVEX-EVAL SVEX SVEX-ENV)
                              '(0 . 1))))))))

(local
 (svex-eval-lemma-tmpl
  (defret svex-eval-of-bitand/bitor-cancel-repeated-aux-correct-1
    (and (implies (and (equal new-val 0)

                       (svexlist-p leaves)
                       (sv::svex-p svex)
                       (rp::rp-term-listp context)
                       (rp::valid-sc env-term a)
                       (rp::eval-and-all context a)
                       (sub-alistp env big-env)
                       (rp::falist-consistent-aux big-env env-term)

                       (:@ :dollar-eval
                           (width-of-svex-extn-correct<$>-lst
                            (svex-reduce-config->width-extns config))
                           (integerp-of-svex-extn-correct<$>-lst
                            (svex-reduce-config->integerp-extns config)))
                       (:@ :normal-eval
                           (equal (svex-reduce-config->width-extns config) nil)
                           (equal (svex-reduce-config->integerp-extns config) nil))
                       (or* (svex-reduce-config->keep-missing-env-vars config)
                            (equal big-env env))

                       )
                  (EQUAL
                   (4vec-bitor (svex-eval-bitor-lst leaves (rp-evlt env-term a))
                               (svex-eval simplified-svex (rp-evlt env-term a)))
                   (4vec-bitor (svex-eval-bitor-lst leaves (rp-evlt env-term a))
                               (svex-eval svex (rp-evlt env-term a)))))
         (implies (and (equal new-val 0)
                       (svexlist-p leaves)
                       (sv::svex-p svex)
                       (equal env nil)

                       (:@ :dollar-eval
                           (width-of-svex-extn-correct<$>-lst
                            (svex-reduce-config->width-extns config))
                           (integerp-of-svex-extn-correct<$>-lst
                            (svex-reduce-config->integerp-extns config)))
                       (:@ :normal-eval
                           (equal (svex-reduce-config->width-extns config) nil)
                           (equal (svex-reduce-config->integerp-extns config) nil))
                       (svex-reduce-config->keep-missing-env-vars config))
                  (equal
                   (4vec-bitor (svex-eval-bitor-lst leaves svex-env)
                               (svex-eval simplified-svex svex-env))
                   (4vec-bitor (svex-eval-bitor-lst leaves svex-env)
                               (svex-eval svex svex-env)))))
    :fn bitand/bitor-cancel-repeated-aux
    ;;:otf-flg t
    :hints (("Goal"
             :induct (bitand/bitor-cancel-repeated-aux svex leaves  new-val :limit limit)
             :do-not-induct t
             :expand ((:free (x)
                             (svex-apply 'sv::bitxor x))
                      (:free (x)
                             (svex-apply 'sv::unfloat x))
                      (:free (x)
                             (svex-apply 'sv::bitand x))
                      (:free (x)
                             (svex-apply 'sv::bitor x)))

             :in-theory (e/d (;;all-xor/and/or-nodes-are-masked-p
                              sv::svex-p
                              svexlist-eval
                              4vec-bitor-of-4vec-bitand
                              4vec-part-select-of-4vec-bitor-better
                              4vec-part-select-of-4vec-bitxor-better
                              4vec-part-select-of-4vec-bitand-better
                              ;;svex-eval
                              svex-kind
                              svex-call->fn
                              svex-call->args
                              bitand/bitor-cancel-repeated-aux
                              )
                             (push-3vec-fix-into-4vec-part-select
                              single-bit-4vec-p
                              member-equal
                              default-car
                              sv::svex-eval-when-quote
                              sv::svex-eval-when-fncall
                              sv::4vec-p-when-maybe-4vec-p
                              (:rewrite-quoted-constant  sv::svex-fix-under-svex-equiv)
                              (:definition true-list-listp)
                              (:rewrite acl2::member-equal-newvar-components-1)
                              svex-eval-width-of-svex-is-correct
                              ;;svex-eval-of-integerp-of-svex-is-correct-env=nil
                              )))
            (and stable-under-simplificationp
                 '(:use ((:instance svex-eval-width-of-svex-is-correct
                                    (free-var-width 1)
                                    (x svex)
                                    (env (rp-evlt env-term a))
                                    ;;(x `(unfloat ,svex))
                                    )
                         (:instance svex-eval-width-of-svex-is-correct
                                    (free-var-width 1)
                                    (x svex)
                                    (env svex-env)
                                    ;;(x `(unfloat ,svex))
                                    ))))

            (and stable-under-simplificationp
                 '(:clause-processor
                   (single-bit-part-select-case-splitter clause)))
            ))))

(encapsulate
  nil
  (local
   (use-equal-by-logbitp t))

  (local
   (in-theory (enable acl2::b-and
                      acl2::b-ior)))

  (local
   (defthmd logand-of-single-loghead-2
     (and (equal (logand x (loghead size y))
                 (loghead size (logand x y)))
          (equal (logand (loghead size y) x)
                 (loghead size (logand x y))))
     :hints (("goal"
              :use ((:instance logand-of-single-loghead))
              :in-theory (e/d* (bitops::ihsext-recursive-redefs
                                bitops::ihsext-inductions)
                               ()) ))))

  (defthmd pull-out-part-select-from-4vec-bitand
    (implies (natp width)
             (equal (4vec-bitand x
                                 (4vec-part-select 0 width y))
                    (4vec-part-select 0 width
                                      (4vec-bitand x y))))
    :hints (("goal"
             :in-theory (e/d (4vec-bitand
                              3vec-bitand
                              4vec-part-select
                              4vec-concat
                              4vec
                              sv::3vec-fix)
                             (4vec
                              logapp logand loghead
                              )))
            (bitops::logbitp-reasoning)
            ))

  (defthmd move-over-part-select-from-4vec-bitand
    (implies (natp width)
             (equal (4vec-bitand x
                                 (4vec-part-select 0 width y))
                    (4vec-bitand y
                                 (4vec-part-select 0 width x))))
    :hints (("goal"
             :in-theory (e/d (4vec-bitand
                              3vec-bitand
                              4vec-part-select
                              4vec-concat
                              4vec
                              sv::3vec-fix)
                             (4vec
                              logapp logand loghead
                              )))
            (bitops::logbitp-reasoning)
            ))

  (svex-eval-lemma-tmpl
   (defthm width-of-svex-eval-bitand-lst-lemma
     (implies (and (member-equal svex leaves)
                   (natp width)
                   (equal (4vec-part-select 0 width (svex-eval svex env))
                          (svex-eval svex env)))
              (equal (4vec-part-select 0 width (svex-eval-bitand-lst leaves env))
                     (svex-eval-bitand-lst leaves env)))
     :hints (("goal"
              :in-theory (e/d (move-over-part-select-from-4vec-bitand
                               member-equal
                               svex-eval-bitand-lst
                               4vec-part-select-of-4vec-bitand-better)
                              ()))))))

(local
 (defthm dummy-lemma-when-bitand-of-2-is-zero-with-other-is-also-zero
   (implies (equal (4vec-bitand x y) 0)
            (equal (4vec-bitand x (4vec-bitand a y)) 0))))

(local
 (defthm 4vec-bitand-of-negated-same
   (implies (and (4vec-correct-width-p 1 x)
                 (integerp x))
            (equal (4vec-bitand x (sv::4vec-bitxor 1 x))
                   0))
   :hints (("Goal"
            :in-theory (e/d (4VEC-CORRECT-WIDTH-P
                             SV::4VEC-BITXOR
                             4VEC-BITAND
                             4VEC
                             3VEC-BITAND
                             4VEC-PART-SELECT
                             4VEC-RSH
                             4VEC-SHIFT-CORE
                             4VEC-CONCAT)
                            (EQUAL-OF-4VEC-CONCAT-WITH-SIZE=1))))))

(local
 (svex-eval-lemma-tmpl
  (defthm svex-eval-member-hons-equal-of-negated-lemma-for-bitand
    (implies (and (member-hons-equal-of-negated svex leaves)
                  (4vec-correct-width-p 1 (svex-eval svex env))
                  (integerp (svex-eval svex env)))
             (equal
              (4vec-bitand (svex-eval svex env)
                           (svex-eval-bitand-lst leaves env))
              0))
    :hints (("Goal"
             :do-not-induct t
             :expand ((SVEX-EVAL-BITAND-LST LEAVES ENV))
             :induct (member-hons-equal-of-negated svex leaves)
             :in-theory (e/d (member-hons-equal-of-negated)
                             ()))))))

(local
 (svex-eval-lemma-tmpl
  (defret svex-eval-of-bitand/bitor-cancel-repeated-aux-correct-2
    (and (implies (and (equal new-val -1)
                       (svexlist-p leaves)
                       (sv::svex-p svex)
                       (rp::rp-term-listp context)
                       (rp::valid-sc env-term a)
                       (rp::eval-and-all context a)
                       (sub-alistp env big-env)
                       (rp::falist-consistent-aux big-env env-term)
                       (:@ :dollar-eval
                           (width-of-svex-extn-correct<$>-lst
                            (svex-reduce-config->width-extns config))
                           (integerp-of-svex-extn-correct<$>-lst
                            (svex-reduce-config->integerp-extns config)))
                       (:@ :normal-eval
                           (equal (svex-reduce-config->width-extns config) nil)
                           (equal (svex-reduce-config->integerp-extns config) nil))
                       (or* (svex-reduce-config->keep-missing-env-vars config)
                            (equal big-env env)))
                  (equal
                   (4vec-bitand (svex-eval-bitand-lst leaves (rp-evlt env-term a))
                                (svex-eval simplified-svex (rp-evlt env-term a)))
                   (4vec-bitand (svex-eval-bitand-lst leaves (rp-evlt env-term a))
                                (svex-eval svex (rp-evlt env-term a)))))
         (implies (and (equal new-val -1)
                       (svexlist-p leaves)
                       (sv::svex-p svex)
                       (equal env nil)
                       (:@ :dollar-eval
                           (width-of-svex-extn-correct<$>-lst
                            (svex-reduce-config->width-extns config))
                           (integerp-of-svex-extn-correct<$>-lst
                            (svex-reduce-config->integerp-extns config)))
                       (:@ :normal-eval
                           (equal (svex-reduce-config->width-extns config) nil)
                           (equal (svex-reduce-config->integerp-extns config) nil))
                       (svex-reduce-config->keep-missing-env-vars config))
                  (equal
                   (4vec-bitand (svex-eval-bitand-lst leaves svex-env)
                                (svex-eval simplified-svex svex-env))
                   (4vec-bitand (svex-eval-bitand-lst leaves svex-env)
                                (svex-eval svex svex-env)))))
    :fn bitand/bitor-cancel-repeated-aux
    :otf-flg t
    :hints (("goal"
             :induct (bitand/bitor-cancel-repeated-aux svex leaves  new-val :limit limit)
             :do-not-induct t
             :expand (;;(svex-eval svex env)
                      (:free (x)
                             (svex-apply 'sv::bitxor x))
                      (:free (x)
                             (svex-apply 'sv::unfloat x))
                      (:free (x)
                             (svex-apply 'sv::bitand x))
                      (:free (x)
                             (svex-apply 'sv::bitor x)))

             :in-theory (e/d (move-over-part-select-from-4vec-bitand
                              sv::svex-p
                              svexlist-eval
                              svex-eval-of-4vec
                              4vec-bitand-of-4vec-bitor
                              4vec-part-select-of-4vec-bitor-better
                              4vec-part-select-of-4vec-bitxor-better
                              4vec-part-select-of-4vec-bitand-better
                              svex-kind
                              svex-call->fn
                              svex-call->args
                              bitand/bitor-cancel-repeated-aux
                              )
                             (push-3vec-fix-into-4vec-part-select
                              member-equal
                              default-car
                              sv::svex-eval-when-quote
                              sv::svex-eval-when-fncall
                              sv::4vec-p-when-maybe-4vec-p
                              (:rewrite-quoted-constant  sv::svex-fix-under-svex-equiv)
                              (:definition true-list-listp)
                              ;;svex-eval-width-of-svex-is-correct
                              acl2::member-equal-newvar-components-1)))))))

(svex-eval-lemma-tmpl
 (defthm svex-eval-bitor/bitand/bitxor-lst-of-append
   (and (equal (svex-eval-bitor-lst (append x y) env)
               (4vec-bitor (svex-eval-bitor-lst x env)
                           (svex-eval-bitor-lst y env)))
        (equal (svex-eval-bitand-lst (append x y) env)
               (4vec-bitand (svex-eval-bitand-lst x env)
                            (svex-eval-bitand-lst y env)))
        (equal (svex-eval-bitxor-lst (append x y) env)
               (sv::4vec-bitxor (svex-eval-bitxor-lst x env)
                                (svex-eval-bitxor-lst y env))))
   :otf-flg t
   :hints (("goal"
            :induct (svex-eval-bitor-lst x env)
            :do-not-induct t
            :expand ((svex-eval-bitor-lst y env)
                     (svex-eval-bitand-lst y env)
                     (svex-eval-bitxor-lst y env))
            :in-theory (e/d (svex-eval-bitxor-lst
                             svex-eval-bitor-lst
                             svex-eval-bitand-lst)
                            ())))))

(local
 (svex-eval-lemma-tmpl
  (progn
    (defthm svex-eval-bitor-lst-of-bitand/or/xor-collect-leaves
      (and
       (equal
        (sv::3vec-fix (svex-eval-bitor-lst (bitand/or/xor-collect-leaves svex 'sv::bitor :limit limit) env))
        (sv::3vec-fix (svex-eval svex env))))
      :hints (("goal"
               :in-theory (e/d (svex-eval-bitor-lst
                                svex-eval-bitand-lst
                                bitand/or/xor-collect-leaves

                                )
                               ()))))

    (defthm svex-eval-bitand-lst-of-bitand/or/xor-collect-leaves
      (equal
       (sv::3vec-fix (svex-eval-bitand-lst (bitand/or/xor-collect-leaves svex 'sv::bitand :limit limit) env))
       (sv::3vec-fix (svex-eval svex env)))
      :hints (("goal"
               :in-theory (e/d (svex-eval-bitor-lst
                                svex-eval-bitand-lst
                                bitand/or/xor-collect-leaves)
                               ()))))

    (defthm svex-eval-bitor-lst-of-bitand/or/xor-collect-leaves-2
      (and (equal
            (sv::4vec-bitor other
                            (svex-eval-bitor-lst (bitand/or/xor-collect-leaves svex 'sv::bitor :limit limit) env)
                            )
            (sv::4vec-bitor (svex-eval svex env)
                            other))
           (equal
            (sv::4vec-bitor (svex-eval-bitor-lst (bitand/or/xor-collect-leaves svex 'sv::bitor :limit limit) env)
                            other)
            (sv::4vec-bitor (svex-eval svex env)
                            other)))
      :hints (("goal"
               :use ((:instance svex-eval-bitor-lst-of-bitand/or/xor-collect-leaves))
               :in-theory (e/d ()
                               (svex-eval-bitor-lst-of-bitand/or/xor-collect-leaves)))))

    (defthm svex-eval-bitand-lst-of-bitand/or/xor-collect-leaves-2
      (and (equal
            (sv::4vec-bitand other
                             (svex-eval-bitand-lst (bitand/or/xor-collect-leaves svex 'sv::bitand :limit limit) env)
                             )
            (sv::4vec-bitand (svex-eval svex env)
                             other))
           (equal
            (sv::4vec-bitand (svex-eval-bitand-lst (bitand/or/xor-collect-leaves svex 'sv::bitand :limit limit) env)
                             other)
            (sv::4vec-bitand (svex-eval svex env)
                             other)))
      :hints (("goal"
               :use ((:instance svex-eval-bitand-lst-of-bitand/or/xor-collect-leaves))
               :in-theory (e/d ()
                               (svex-eval-bitand-lst-of-bitand/or/xor-collect-leaves))))))))

(local
 (svex-eval-lemma-tmpl
  (defthm 4vec-p-of-svex-eval-bitor/and-lst
    (and (sv::4vec-p (svex-eval-bitor-lst lst env))
         (sv::4vec-p (svex-eval-bitand-lst lst env))))))

(local
 (svex-eval-lemma-tmpl
  (defret svex-eval-of-bitxor-remove-node-correct
    (implies (and (svex-p svex)
                  (integerp (svex-eval node-to-remove env))
                  success
                  (:@ :dollar-eval
                      (width-of-svex-extn-correct<$>-lst
                       (svex-reduce-config->width-extns config))
                      (integerp-of-svex-extn-correct<$>-lst
                       (svex-reduce-config->integerp-extns config)))
                  (:@ :normal-eval
                      (equal (svex-reduce-config->width-extns config) nil)
                      (equal (svex-reduce-config->integerp-extns config) nil))
                  )
             (equal (svex-eval res-svex env)
                    (sv::4vec-bitxor (svex-eval node-to-remove env)
                                     (svex-eval svex env))))
    :fn bitxor-remove-node
    :hints (("Goal"
             :in-theory (e/d (SVEX-P
                              bitxor-remove-node) ()))))))

(local
 (svex-eval-lemma-tmpl
  (defret svex-eval-bitxor-remove-nodes-from-both-correct-1
    (implies (and (svex-p svex1)
                  (svex-p svex2)
                  (svexlist-p nodes-to-remove)

                  (equal env nil)

                  (:@ :dollar-eval
                      (width-of-svex-extn-correct<$>-lst
                       (svex-reduce-config->width-extns config))
                      (integerp-of-svex-extn-correct<$>-lst
                       (svex-reduce-config->integerp-extns config)))
                  (:@ :normal-eval
                      (equal (svex-reduce-config->width-extns config) nil)
                      (equal (svex-reduce-config->integerp-extns config) nil))

                  (svex-reduce-config->keep-missing-env-vars config)
                  )
             (equal (sv::4vec-bitxor (svex-eval res-svex1 svex-env)
                                     (svex-eval res-svex2 svex-env))
                    (sv::4vec-bitxor (svex-eval svex1 svex-env)
                                     (svex-eval svex2 svex-env))))
    :fn bitxor-remove-nodes-from-both
    :hints (("Goal"
             :in-theory (e/d (svex-p
                              bitxor-remove-nodes-from-both)
                             ()))))))

(local
 (svex-eval-lemma-tmpl
  (defret svex-eval-bitxor-remove-nodes-from-both-correct-2
    (implies (and (rp::falist-consistent-aux big-env env-term)
                  (sub-alistp env big-env)
                  (svex-p svex1)
                  (svex-p svex2)
                  (svexlist-p nodes-to-remove)

                  (rp::rp-term-listp context)
                  (rp::valid-sc env-term a)
                  (rp::eval-and-all context a)

                  (:@ :dollar-eval
                      (width-of-svex-extn-correct<$>-lst
                       (svex-reduce-config->width-extns config))
                      (integerp-of-svex-extn-correct<$>-lst
                       (svex-reduce-config->integerp-extns config)))
                  (:@ :normal-eval
                      (equal (svex-reduce-config->width-extns config) nil)
                      (equal (svex-reduce-config->integerp-extns config) nil))

                  (or* (svex-reduce-config->keep-missing-env-vars config)
                       (equal big-env env))
                  )
             (equal (sv::4vec-bitxor (svex-eval res-svex1 (rp-evlt env-term a))
                                     (svex-eval res-svex2 (rp-evlt env-term a)))
                    (sv::4vec-bitxor (svex-eval svex1 (rp-evlt env-term a))
                                     (svex-eval svex2 (rp-evlt env-term a)))))
    :fn bitxor-remove-nodes-from-both
    :hints (("Goal"
             :in-theory (e/d (svex-p
                              bitxor-remove-nodes-from-both)
                             ()))))))

(svex-eval-lemma-tmpl
 (defret svex-eval-of-extract-from-unfloat-correct
   (and (equal (sv::4vec-bitxor (svex-eval res env) other)
               (sv::4vec-bitxor (svex-eval x env) other))
        (equal (sv::4vec-bitxor other (svex-eval res env))
               (sv::4vec-bitxor (svex-eval x env) other))
        (equal (sv::4vec-bitand (svex-eval res env) other)
               (sv::4vec-bitand (svex-eval x env) other))
        (equal (sv::4vec-bitand other (svex-eval res env))
               (sv::4vec-bitand (svex-eval x env) other))
        (equal (sv::4vec-bitor (svex-eval res env) other)
               (sv::4vec-bitor (svex-eval x env) other))
        (equal (sv::4vec-bitor other (svex-eval res env))
               (sv::4vec-bitor (svex-eval x env) other)))
   :fn extract-from-unfloat
   :hints (("Goal"
            :expand ((:free (args) (svex-apply 'sv::unfloat args)))
            :in-theory (e/d (svex-eval
                             svex-kind
                             SVEX-CALL->FN
                             SVEX-CALL->ARGS
                             SVEXLIST-EVAL
                             extract-from-unfloat)
                            ())))))

(svex-eval-lemma-tmpl
 (defret svex-eval-of-bitand/or/xor-cancel-repeated-correct
   (and (implies (and (rp::falist-consistent-aux big-env env-term)
                      (sub-alistp env big-env)
                      (fnsym-p fn)
                      (sv::svex-p x)
                      (sv::svex-p y)
                      (rp::rp-term-listp context)
                      (rp::valid-sc env-term a)
                      (rp::eval-and-all context a)
                      (:@ :dollar-eval
                          (width-of-svex-extn-correct<$>-lst
                           (svex-reduce-config->width-extns config))
                          (integerp-of-svex-extn-correct<$>-lst
                           (svex-reduce-config->integerp-extns config)))
                      (:@ :normal-eval
                          (equal (svex-reduce-config->width-extns config) nil)
                          (equal (svex-reduce-config->integerp-extns config) nil))
                      (or* (svex-reduce-config->keep-missing-env-vars config)
                           (equal big-env env)))
                 (equal
                  (svex-eval simplified-svex (rp-evlt env-term a))
                  (svex-eval `(,fn ,x ,y) (rp-evlt env-term a))))

        )
   :fn bitand/or/xor-cancel-repeated
   ;;:otf-flg t
   :hints (("goal"
            :do-not-induct t

            :use ( (:instance svex-eval-of-bitand/bitor-cancel-repeated-aux-correct-1
                              (svex (extract-from-unfloat y))
                              (leaves (bitand/or/xor-collect-leaves (extract-from-unfloat x) 'bitor))

                              (new-val 0)
                              (under-xor nil)
                              (limit *bitand/bitor-cancel-repeated-aux-limit*))
                   (:instance svex-eval-of-bitand/bitor-cancel-repeated-aux-correct-1
                              (svex (extract-from-unfloat x))
                              (leaves (bitand/or/xor-collect-leaves
                                       (mv-nth 0
                                               (bitand/bitor-cancel-repeated-aux
                                                (extract-from-unfloat y)
                                                (bitand/or/xor-collect-leaves (extract-from-unfloat x) 'bitor)
                                                0
                                                :under-xor nil))
                                       'bitor))
                              (new-val 0)
                              (under-xor nil)
                              (limit *bitand/bitor-cancel-repeated-aux-limit*))
                   (:instance svex-eval-of-bitand/bitor-cancel-repeated-aux-correct-2
                              (svex (extract-from-unfloat y))
                              (leaves (bitand/or/xor-collect-leaves (extract-from-unfloat x)
                                                                    'bitand))

                              (new-val -1)
                              (under-xor nil)
                              (limit *bitand/bitor-cancel-repeated-aux-limit*))
                   (:instance svex-eval-of-bitand/bitor-cancel-repeated-aux-correct-2
                              (svex (extract-from-unfloat x))
                              (leaves (bitand/or/xor-collect-leaves
                                       (mv-nth 0
                                               (bitand/bitor-cancel-repeated-aux
                                                (extract-from-unfloat y)
                                                (bitand/or/xor-collect-leaves (extract-from-unfloat x)
                                                                              'bitand)
                                                -1
                                                :under-xor nil))
                                       'bitand))

                              (new-val -1)
                              (under-xor nil)
                              (limit *bitand/bitor-cancel-repeated-aux-limit*))

                   )
            :in-theory (e/d (bitand/or/xor-cancel-repeated
                             4vec-part-select-of-4vec-bitor-better
                             4vec-part-select-of-4vec-bitand-better)
                            (svex-eval-bitor-lst-of-bitand/or/xor-collect-leaves
                             svex-eval-of-bitand/bitor-cancel-repeated-aux-correct-1
                             svex-eval-of-bitand/bitor-cancel-repeated-aux-correct-2
                             ))))))

(svex-eval-lemma-tmpl
 (defret svex-eval-of-bitand/or/xor-cancel-repeated-correct-env=nil
   (implies (and* (fnsym-p fn)
                  (sv::svex-p x)
                  (sv::svex-p y)
                  (equal env nil)
                  (:@ :dollar-eval
                      (width-of-svex-extn-correct<$>-lst
                       (svex-reduce-config->width-extns config))
                      (integerp-of-svex-extn-correct<$>-lst
                       (svex-reduce-config->integerp-extns config)))
                  (:@ :normal-eval
                      (equal (svex-reduce-config->width-extns config) nil)
                      (equal (svex-reduce-config->integerp-extns config) nil))
                  (svex-reduce-config->keep-missing-env-vars config))
            (equal
             (svex-eval simplified-svex svex-env)
             (svex-eval `(,fn ,x ,y) svex-env)))
   :fn bitand/or/xor-cancel-repeated
   ;;:otf-flg t
   :hints (("goal"
            :do-not-induct t

            :use ( (:instance svex-eval-of-bitand/bitor-cancel-repeated-aux-correct-1
                              (svex (extract-from-unfloat y))
                              (leaves (bitand/or/xor-collect-leaves (extract-from-unfloat x) 'bitor))

                              (new-val 0)
                              (under-xor nil)
                              (limit *bitand/bitor-cancel-repeated-aux-limit*))
                   (:instance svex-eval-of-bitand/bitor-cancel-repeated-aux-correct-1
                              (svex (extract-from-unfloat x))
                              (leaves (bitand/or/xor-collect-leaves
                                       (mv-nth 0
                                               (bitand/bitor-cancel-repeated-aux
                                                (extract-from-unfloat y)
                                                (bitand/or/xor-collect-leaves (extract-from-unfloat x) 'bitor)
                                                0
                                                :under-xor nil))
                                       'bitor))
                              (new-val 0)
                              (under-xor nil)
                              (limit *bitand/bitor-cancel-repeated-aux-limit*))
                   (:instance svex-eval-of-bitand/bitor-cancel-repeated-aux-correct-2
                              (svex (extract-from-unfloat y))
                              (leaves (bitand/or/xor-collect-leaves (extract-from-unfloat x)
                                                                    'bitand))

                              (new-val -1)
                              (under-xor nil)
                              (limit *bitand/bitor-cancel-repeated-aux-limit*))
                   (:instance svex-eval-of-bitand/bitor-cancel-repeated-aux-correct-2
                              (svex (extract-from-unfloat x))
                              (leaves (bitand/or/xor-collect-leaves
                                       (mv-nth 0
                                               (bitand/bitor-cancel-repeated-aux
                                                (extract-from-unfloat y)
                                                (bitand/or/xor-collect-leaves (extract-from-unfloat x)
                                                                              'bitand)
                                                -1
                                                :under-xor nil))
                                       'bitand))

                              (new-val -1)
                              (under-xor nil)
                              (limit *bitand/bitor-cancel-repeated-aux-limit*))

                   )
            :in-theory (e/d (bitand/or/xor-cancel-repeated
                             4vec-part-select-of-4vec-bitor-better
                             4vec-part-select-of-4vec-bitand-better)
                            (svex-eval-bitor-lst-of-bitand/or/xor-collect-leaves
                             svex-eval-of-bitand/bitor-cancel-repeated-aux-correct-1
                             svex-eval-of-bitand/bitor-cancel-repeated-aux-correct-2
                             ))))))

(svex-eval-lemma-tmpl
 (defret-mutual svex-eval-of-<fn>
   (defret svex-eval-of-<fn>
     (implies (and (sv::svex-p x)
                   (rp::rp-term-listp context)
                   (rp::valid-sc env-term a)
                   (rp::eval-and-all context a)
                   (sub-alistp env big-env)
                   (rp::falist-consistent-aux big-env env-term)
                   (:@ :dollar-eval
                       (width-of-svex-extn-correct<$>-lst
                        (svex-reduce-config->width-extns config))
                       (integerp-of-svex-extn-correct<$>-lst
                        (svex-reduce-config->integerp-extns config)))
                   (:@ :normal-eval
                       (equal (svex-reduce-config->width-extns config) nil)
                       (equal (svex-reduce-config->integerp-extns config) nil))
                   (or* (svex-reduce-config->keep-missing-env-vars config)
                        (equal big-env env)))
              (equal
               (svex-eval res (rp-evlt env-term a))
               (svex-eval x (rp-evlt env-term a))))
     :fn svex-simplify-bitand/or/xor)
   (defret svexlist-eval-of-<fn>
     (implies (and (sv::svexlist-p lst)
                   (rp::rp-term-listp context)
                   (rp::valid-sc env-term a)
                   (rp::eval-and-all context a)
                   (sub-alistp env big-env)
                   (rp::falist-consistent-aux big-env env-term)
                   (:@ :dollar-eval
                       (width-of-svex-extn-correct<$>-lst
                        (svex-reduce-config->width-extns config))
                       (integerp-of-svex-extn-correct<$>-lst
                        (svex-reduce-config->integerp-extns config)))
                   (:@ :normal-eval
                       (equal (svex-reduce-config->width-extns config) nil)
                       (equal (svex-reduce-config->integerp-extns config) nil))
                   (or* (svex-reduce-config->keep-missing-env-vars config)
                        (equal big-env env)))
              (equal
               (svexlist-eval res (rp-evlt env-term a))
               (svexlist-eval lst (rp-evlt env-term a))))
     :fn svexlist-simplify-bitand/or/xor)
   :mutual-recursion svex-simplify-bitand/or/xor
   :hints (("Goal"
            :expand ((:free (args)
                            (svex-apply 'bitor args))
                     (:free (args)
                            (svex-apply 'bitxor args))
                     (:free (args)
                            (svex-apply 'bitand args)))
            :in-theory (e/d (svexlist-eval
                             svex-simplify-bitand/or/xor
                             svexlist-simplify-bitand/or/xor)
                            ())))))

(svex-eval-lemma-tmpl
 (defret-mutual svex-eval-of-<fn>
   (defret svex-eval-of-<fn>-env=nil
     (implies (and (sv::svex-p x)
                   (equal env nil)
                   (:@ :dollar-eval
                       (width-of-svex-extn-correct<$>-lst
                        (svex-reduce-config->width-extns config))
                       (integerp-of-svex-extn-correct<$>-lst
                        (svex-reduce-config->integerp-extns config)))
                   (:@ :normal-eval
                       (equal (svex-reduce-config->width-extns config) nil)
                       (equal (svex-reduce-config->integerp-extns config) nil))
                   (svex-reduce-config->keep-missing-env-vars config))
              (equal
               (svex-eval res svex-env)
               (svex-eval x svex-env)))
     :fn svex-simplify-bitand/or/xor)
   (defret svexlist-eval-of-<fn>-env=nil
     (implies (and (sv::svexlist-p lst)
                   (equal env nil)
                   (:@ :dollar-eval
                       (width-of-svex-extn-correct<$>-lst
                        (svex-reduce-config->width-extns config))
                       (integerp-of-svex-extn-correct<$>-lst
                        (svex-reduce-config->integerp-extns config)))
                   (:@ :normal-eval
                       (equal (svex-reduce-config->width-extns config) nil)
                       (equal (svex-reduce-config->integerp-extns config) nil))
                   (svex-reduce-config->keep-missing-env-vars config))
              (equal
               (svexlist-eval res svex-env)
               (svexlist-eval lst svex-env)))
     :fn svexlist-simplify-bitand/or/xor)
   :mutual-recursion svex-simplify-bitand/or/xor
   :hints (("Goal"
            :expand ((:free (args)
                            (svex-apply 'bitor args))
                     (:free (args)
                            (svex-apply 'bitxor args))
                     (:free (args)
                            (svex-apply 'bitand args)))
            :in-theory (e/d (svexlist-eval
                             svex-simplify-bitand/or/xor
                             svexlist-simplify-bitand/or/xor)
                            ())))))

(svex-eval-lemma-tmpl
 (defret svex-alist-eval-of-<fn>
   (implies (and (sv::svex-alist-p alist)
                 (rp::rp-term-listp context)
                 (rp::valid-sc env-term a)
                 (rp::eval-and-all context a)

                 (sub-alistp env big-env)
                 (rp::falist-consistent-aux big-env env-term)
                 (:@ :dollar-eval
                     (width-of-svex-extn-correct<$>-lst
                      (svex-reduce-config->width-extns config))
                     (integerp-of-svex-extn-correct<$>-lst
                      (svex-reduce-config->integerp-extns config)))
                 (:@ :normal-eval
                     (equal (svex-reduce-config->width-extns config) nil)
                     (equal (svex-reduce-config->integerp-extns config) nil))
                 (or* (svex-reduce-config->keep-missing-env-vars config)
                      (equal big-env env)))
            (equal
             (svex-alist-eval res (rp-evlt env-term a))
             (svex-alist-eval alist (rp-evlt env-term a))))
   :fn svex-alist-simplify-bitand/or/xor
   :hints (("Goal"
            :in-theory (e/d (SVEX-ALIST-EVAL
                             svex-alist-simplify-bitand/or/xor)
                            ())))))

(svex-eval-lemma-tmpl
 (defret svex-alist-eval-of-<fn>-2
   (implies (and (sv::svex-alist-p alist)
                 (rp::rp-term-listp context)
                 (rp::valid-sc env-term a)
                 (rp::eval-and-all context a)
                 (rp::falist-consistent-aux env env-term)
                 (:@ :dollar-eval
                     (width-of-svex-extn-correct<$>-lst
                      (svex-reduce-config->width-extns config))
                     (integerp-of-svex-extn-correct<$>-lst
                      (svex-reduce-config->integerp-extns config)))
                 (:@ :normal-eval
                     (equal (svex-reduce-config->width-extns config) nil)
                     (equal (svex-reduce-config->integerp-extns config) nil)))
            (equal
             (svex-alist-eval res (rp-evlt env-term a))
             (svex-alist-eval alist (rp-evlt env-term a))))
   :fn svex-alist-simplify-bitand/or/xor
   :hints (("Goal"
            :use ((:instance svex-alist-eval-of-<fn>
                             (big-env env)))
            :in-theory (e/d ()
                            (svex-alist-eval-of-<fn>))))))

(svex-eval-lemma-tmpl
 (defret svex-alist-eval-of-<fn>=env=nil
   (implies (and (sv::svex-alist-p alist)
                 (equal env nil)
                 (:@ :dollar-eval
                     (width-of-svex-extn-correct<$>-lst
                      (svex-reduce-config->width-extns config))
                     (integerp-of-svex-extn-correct<$>-lst
                      (svex-reduce-config->integerp-extns config)))
                 (:@ :normal-eval
                     (equal (svex-reduce-config->width-extns config) nil)
                     (equal (svex-reduce-config->integerp-extns config) nil))
                 (svex-reduce-config->keep-missing-env-vars config))
            (equal
             (svex-alist-eval res svex-env)
             (svex-alist-eval alist svex-env)))
   :fn svex-alist-simplify-bitand/or/xor
   :hints (("Goal"
            :in-theory (e/d (SVEX-ALIST-EVAL
                             svex-alist-simplify-bitand/or/xor)
                            ())))))

;;;;;;;;;;; outside-in version

(svex-eval-lemma-tmpl
 (defret-mutual svex-eval-of-<fn>
   (defret svex-eval-of-<fn>
     (implies (and (sv::svex-p x)
                   (rp::rp-term-listp context)
                   (rp::valid-sc env-term a)
                   (rp::eval-and-all context a)
                   (sub-alistp env big-env)
                   (rp::falist-consistent-aux big-env env-term)
                   (:@ :dollar-eval
                       (width-of-svex-extn-correct<$>-lst
                        (svex-reduce-config->width-extns config))
                       (integerp-of-svex-extn-correct<$>-lst
                        (svex-reduce-config->integerp-extns config)))
                   (:@ :normal-eval
                       (equal (svex-reduce-config->width-extns config) nil)
                       (equal (svex-reduce-config->integerp-extns config) nil))
                   (or* (svex-reduce-config->keep-missing-env-vars config)
                        (equal big-env env)))
              (equal
               (svex-eval res (rp-evlt env-term a))
               (svex-eval x (rp-evlt env-term a))))
     :fn svex-simplify-bitand/or/xor-outside-in)
   (defret svexlist-eval-of-<fn>
     (implies (and (sv::svexlist-p lst)
                   (rp::rp-term-listp context)
                   (rp::valid-sc env-term a)
                   (rp::eval-and-all context a)
                   (sub-alistp env big-env)
                   (rp::falist-consistent-aux big-env env-term)
                   (:@ :dollar-eval
                       (width-of-svex-extn-correct<$>-lst
                        (svex-reduce-config->width-extns config))
                       (integerp-of-svex-extn-correct<$>-lst
                        (svex-reduce-config->integerp-extns config)))
                   (:@ :normal-eval
                       (equal (svex-reduce-config->width-extns config) nil)
                       (equal (svex-reduce-config->integerp-extns config) nil))
                   (or* (svex-reduce-config->keep-missing-env-vars config)
                        (equal big-env env)))
              (equal
               (svexlist-eval res (rp-evlt env-term a))
               (svexlist-eval lst (rp-evlt env-term a))))
     :fn svexlist-simplify-bitand/or/xor-outside-in)
   :mutual-recursion svex-simplify-bitand/or/xor-outside-in
   :hints (("Goal"
            :expand ((:free (args)
                            (svex-apply 'bitor args))
                     (:free (args)
                            (svex-apply 'bitxor args))
                     (:free (args)
                            (svex-apply 'bitand args)))
            :in-theory (e/d (svexlist-eval
                             svex-simplify-bitand/or/xor-outside-in
                             svexlist-simplify-bitand/or/xor-outside-in)
                            ())))))

(svex-eval-lemma-tmpl
 (defret svex-alist-eval-of-<fn>
   (implies (and (sv::svex-alist-p alist)
                 (rp::rp-term-listp context)
                 (rp::valid-sc env-term a)
                 (rp::eval-and-all context a)

                 (sub-alistp env big-env)
                 (rp::falist-consistent-aux big-env env-term)
                 (:@ :dollar-eval
                     (width-of-svex-extn-correct<$>-lst
                      (svex-reduce-config->width-extns config))
                     (integerp-of-svex-extn-correct<$>-lst
                      (svex-reduce-config->integerp-extns config)))
                 (:@ :normal-eval
                     (equal (svex-reduce-config->width-extns config) nil)
                     (equal (svex-reduce-config->integerp-extns config) nil))
                 (or* (svex-reduce-config->keep-missing-env-vars config)
                      (equal big-env env)))
            (equal
             (svex-alist-eval res (rp-evlt env-term a))
             (svex-alist-eval alist (rp-evlt env-term a))))
   :fn svex-alist-simplify-bitand/or/xor-outside-in
   :hints (("Goal"
            :in-theory (e/d (svex-alist-eval
                             svex-alist-simplify-bitand/or/xor-outside-in)
                            ())))))

(svex-eval-lemma-tmpl
 (defret svex-alist-eval-of-<fn>-2
   (implies (and (sv::svex-alist-p alist)
                 (rp::rp-term-listp context)
                 (rp::valid-sc env-term a)
                 (rp::eval-and-all context a)

                 (rp::falist-consistent-aux env env-term)
                 (:@ :dollar-eval
                     (width-of-svex-extn-correct<$>-lst
                      (svex-reduce-config->width-extns config))
                     (integerp-of-svex-extn-correct<$>-lst
                      (svex-reduce-config->integerp-extns config)))
                 (:@ :normal-eval
                     (equal (svex-reduce-config->width-extns config) nil)
                     (equal (svex-reduce-config->integerp-extns config) nil))
                 (or* (svex-reduce-config->keep-missing-env-vars config)
                      (equal big-env env)))
            (equal
             (svex-alist-eval res (rp-evlt env-term a))
             (svex-alist-eval alist (rp-evlt env-term a))))
   :fn svex-alist-simplify-bitand/or/xor-outside-in
   :hints (("Goal"
            :use ((:instance svex-alist-eval-of-<fn>
                             (big-env env)))
            :in-theory (e/d ()
                            (svex-alist-eval-of-<fn>))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; BITXOR/OR/AND-EQUIV
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bitand/or/xor-collect-leaves2 ((svex)
                                       (fn)
                                       (limit natp)) ;
  :returns (mv (leaves sv::svexlist-p :hyp (and (sv::Svex-p svex)
                                                (not (equal fn ':var)))
                       :hints (("Goal"
                                :in-theory (e/d (svex-p
                                                 4vec-p)
                                                ()))))
               (limit-reached-p booleanp))
  :verify-guards nil
  (case-match svex
    ((this-fn x y)
     (b* (((when (zp limit))
           (mv (list svex) t)) ;; want to sent limit-reached-p to t only when there is more to go.
          ((unless (equal this-fn fn))
           (mv (list svex) nil))
          ((mv l1 r1) (bitand/or/xor-collect-leaves2 x fn (1- limit)))
          ((mv l2 r2) (bitand/or/xor-collect-leaves2 y fn (1- limit))))
       (mv (append l1 l2)
           (or r1 r2))))
    #|(('id x)
    (mv (list x svex) nil))|#
    (& (mv (list svex) nil)))
  ///
  (defret true-listp-of-<fn>
    (true-listp leaves))
  (verify-guards bitand/or/xor-collect-leaves2)

  (svex-eval-lemma-tmpl
   (defret svex-eval-of-<fn>-is-correct
     (and (implies (equal fn 'bitand)
                   (equal (svex-eval-bitand-lst leaves env)
                          (sv::3vec-fix (svex-eval svex env))))
          (implies (equal fn 'bitor)
                   (equal (svex-eval-bitor-lst leaves env)
                          (sv::3vec-fix (svex-eval svex env))))
          (implies (equal fn 'bitxor)
                   (equal (svex-eval-bitxor-lst leaves env)
                          (sv::3vec-fix (svex-eval svex env)))))
     :fn bitand/or/xor-collect-leaves2
     :hints (("Goal"
              :in-theory (e/d (bitand/or/xor-collect-leaves2) ()))))))

(define bitxor/or/and-equiv-precheck ((svex)
                                      (fn)
                                      (leaves)
                                      (limit natp)) ;; should be size of leaves (max)
  :Returns (mv (found-cnt natp :hyp (natp limit))
               (traversed-cnt natp :hyp (natp limit)))
  :verify-guards :after-returns
  (if (member-hons-equal svex leaves)
      (mv 1 1)
    (case-match svex
      ((this-fn x y)
       (b* (((unless (equal this-fn fn))
             (mv 0 1))
            ((mv f1 t1) (bitxor/or/and-equiv-precheck x fn leaves limit))
            ((when (>= t1 limit))
             (mv 0 t1))
            ((mv f2 t2) (bitxor/or/and-equiv-precheck y fn leaves limit)))
         (mv (+ f1 f2) (+ t1 t2))))
      (& ;; return limit here as traversed so it stops searching
       (mv 0 limit)))))

;; This is to append l1 and l2 in the same order as given in leaves.
(define bitxor/or/and-equiv-aux-append ((l1 true-listp)
                                        (l2 true-listp)
                                        (leaves true-listp))
  :measure (+ (len leaves) (len l1) (len l2))
  :returns (res true-listp :hyp (and (true-listp l1)
                                     (true-listp l2)))
  (cond
   ((atom l1) l2)
   ((atom l2) l1)
   ((atom leaves) ;; should never come here
    (append l1 l2))
   ((equal (car l1) (car leaves))
    (cons (car l1)
          (bitxor/or/and-equiv-aux-append (cdr l1) l2 leaves)))
   ((equal (car l2) (car leaves))
    (cons (car l2)
          (bitxor/or/and-equiv-aux-append l1 (cdr l2) leaves)))
   (t (bitxor/or/and-equiv-aux-append l1 l2 (cdr leaves))))
  ///
  (svex-eval-lemma-tmpl
   (defret svex-eval-of-<fn>-is-correct
     (and (equal (svex-eval-bitand-lst res env)
                 (4vec-bitand (svex-eval-bitand-lst l1 env)
                              (svex-eval-bitand-lst l2 env)))
          (equal (svex-eval-bitor-lst res env)
                 (4vec-bitor (svex-eval-bitor-lst l1 env)
                             (svex-eval-bitor-lst l2 env)))
          (equal (svex-eval-bitxor-lst res env)
                 (sv::4vec-bitxor (svex-eval-bitxor-lst l1 env)
                                  (svex-eval-bitxor-lst l2 env))))
     :fn bitxor/or/and-equiv-aux-append
     :hints (("goal"
              :expand ((svex-eval-bitand-lst l2 env)
                       (svex-eval-bitxor-lst l1 env)
                       (svex-eval-bitxor-lst l2 env))
              :induct (bitxor/or/and-equiv-aux-append l1 l2 leaves)
              :in-theory (e/d (svex-eval-bitand-lst
                               svex-eval-bitxor-lst)
                              ()))))))

(define remove-equal-once (x l)
  :returns (res true-listp :hyp (true-listp l))
  (cond ((atom l) nil)
        ((equal x (car l))
         (cdr l))
        (t (cons-with-hint (car l)
                           (remove-equal-once x (cdr l))
                           l)))
  ///
  (defret count-of-<fn>
    (implies (member-equal x l)
             (< (acl2-count (remove-equal-once x l))
                (acl2-count l)))
    :rule-classes (:linear :rewrite))

  (svex-eval-lemma-tmpl
   (defthm svex-eval-bitxor-lst-of-remove-pair-equal-lemma
     (implies (member-equal x lst)
              (equal (sv::4vec-bitxor (svex-eval x env)
                                      (svex-eval-bitxor-lst (remove-equal-once x lst) env))
                     (svex-eval-bitxor-lst lst env)))
     :hints (("goal"
              :in-theory (e/d (remove-equal-once) ())))))

  (defret svexlist-p-of-<fn>
    (implies (sv::svexlist-p l)
             (sv::svexlist-p res))
    )
  )

(define remove-pair-equal ((lst true-listp))
  :returns (res sv::Svexlist-p :hyp (sv::Svexlist-p lst))
  :prepwork
  ()
  (cond
   ((atom lst) nil)
   (t
    (b* (((Unless (integerp (car lst)))
          (cons-with-hint (car lst)
                          (remove-pair-equal (cdr lst))
                          lst))
         ((when (member-equal (car lst) (cdr lst)))
          (remove-pair-equal (remove-equal-once (car lst) (cdr lst)))))

      (cons-with-hint (car lst)
                      (remove-pair-equal (cdr lst))
                      lst))))
  ///

  (local
   (svex-eval-lemma-tmpl
    (defthmd svex-eval-when-integerp
      (implies (integerp x)
               (equal (svex-eval x env)
                      x))
      :hints (("Goal"
               :in-theory (e/d (sv::svex-eval
                                sv::svex-kind
                                SV::SVEX-QUOTE->VAL
                                )
                               ()))))))

  (local
   (svex-eval-lemma-tmpl
    (defthm svex-eval-bitxor-lst-of-remove-pair-equal-lemma-2
      (implies (member-equal x lst)
               (equal (svex-eval-bitxor-lst lst env)
                      (sv::4vec-bitxor (svex-eval x env)
                                       (svex-eval-bitxor-lst (remove-equal-once x lst) env))))
      :hints (("goal"
               :in-theory (e/d (remove-equal-once) ()))))))

  (svex-eval-lemma-tmpl
   (defthm svex-eval-bitxor-lst-of-remove-pair-equal
     (equal (svex-eval-bitxor-lst (remove-pair-equal lst) env)
            (svex-eval-bitxor-lst lst env))
     :hints (("Goal"
              :in-theory (e/d (svex-eval-when-integerp
                               remove-pair-equal)
                              (svex-eval-bitxor-lst-of-remove-pair-equal-lemma)))
             ))))

(local
 (svex-eval-lemma-tmpl
  (defthm svex-eval-bitor/and-lst-of-remove-duplicates-equal-lemma
    (implies (member-equal x lst)
             (and (equal (4vec-bitand (svex-eval x env)
                                      (svex-eval-bitand-lst lst env))
                         (svex-eval-bitand-lst lst env))
                  (equal (4vec-bitor (svex-eval x env)
                                     (svex-eval-bitor-lst lst env))
                         (svex-eval-bitor-lst lst env)))))))

(local
 (svex-eval-lemma-tmpl
  (defthm svex-eval-bitor/and-lst-of-remove-duplicates-equal
    (and (equal (svex-eval-bitor-lst (remove-duplicates-equal lst) env)
                (svex-eval-bitor-lst lst env))
         (equal (svex-eval-bitand-lst (remove-duplicates-equal lst) env)
                (svex-eval-bitand-lst lst env)))
    :hints (("Goal"
             :in-theory (e/d (svex-eval-bitor-lst
                              svex-eval-bitand-lst
                              remove-duplicates-equal)
                             ()))))))

(define bitxor/or/and-equiv-aux ((svex)
                                 (fn)
                                 (leaves true-listp))
  :Returns (mv (leaves2 true-listp)
               valid)
  :verify-guards :after-returns

  (if (member-hons-equal svex leaves)
      (mv (list svex) t)
    (case-match svex
      ((this-fn x y)
       (b* (((unless (equal this-fn fn))
             (mv nil nil))
            ((mv l1 valid1) (bitxor/or/and-equiv-aux x fn leaves))
            ((unless valid1)
             (mv nil nil))
            ((mv l2 valid2) (bitxor/or/and-equiv-aux y fn leaves))
            ((unless valid2)
             (mv nil nil)))
         (mv (bitxor/or/and-equiv-aux-append l1 l2 leaves) t)))
      (&
       (mv nil nil))))
  ///
  (svex-eval-lemma-tmpl
   (defret svex-eval-of-<fn>-is-correct
     (and (implies (and (equal fn 'bitand)
                        valid)
                   (and (equal (svex-eval-bitand-lst leaves2 env)
                               (sv::3vec-fix (svex-eval svex env)))
                        (equal (svex-eval-bitand-lst (remove-duplicates-equal leaves2) env)
                               (sv::3vec-fix (svex-eval svex env)))))
          (implies (and (equal fn 'bitor)
                        valid)
                   (and (equal (svex-eval-bitor-lst leaves2 env)
                               (sv::3vec-fix (svex-eval svex env)))
                        (equal (svex-eval-bitor-lst (remove-duplicates-equal leaves2) env)
                               (sv::3vec-fix (svex-eval svex env)))))
          (implies (and (equal fn 'bitxor)
                        valid)
                   (and (equal (svex-eval-bitxor-lst leaves2 env)
                               (sv::3vec-fix (svex-eval svex env)))
                        (equal (svex-eval-bitxor-lst (remove-pair-equal leaves2) env)
                               (sv::3vec-fix (svex-eval svex env))))))
     :fn bitxor/or/and-equiv-aux
     )))

#|(define has-two-ones (x)
(b* ((x (true-list-fix x)))
(and (member-equal 1 x)
(member-equal 1 (cdr (member-equal 1 x))))))|#

(define bitxor/or/and-equiv-iter (fn
                                  arg1 arg2
                                  other-svex
                                  (cnt natp))
  :returns (equiv)
  :guard (<= cnt *bitxor/or/and-equiv-iter-limit*)
  :measure (nfix (- *bitxor/or/and-equiv-iter-limit* cnt))
  :prepwork
  ((defconst *bitxor/or/and-equiv-iter-limit*
     5))

  (if (zp (- *bitxor/or/and-equiv-iter-limit* cnt))
      nil
    (b* (((mv leaves1 limit-reached1)
          (bitand/or/xor-collect-leaves2 arg1 fn cnt))
         ((mv leaves2 limit-reached2)
          (bitand/or/xor-collect-leaves2 arg2 fn cnt))
         (leaves (append leaves1 leaves2))
         (limit-reached (or limit-reached1 limit-reached2)) ;; if t, it means can iter again.

         (leaves (cond ((or (equal fn 'bitor)
                            (equal fn 'bitand))
                        (remove-duplicates-equal leaves))
                       ((equal fn 'bitxor)
                        ;; Removing  pairs from  bitxor requires  the removed
                        ;; ones to be integer. I am only doing it for contants
                        ;; here because I don't want  to add that here because
                        ;; it requires context
                        (remove-pair-equal leaves))
                       (t leaves)))

         (len-leaves (len leaves))
         ((mv found-cnt traversed-cnt)
          (bitxor/or/and-equiv-precheck other-svex fn leaves
                                        (* 2 len-leaves) ;; give some leeway for repated vars
                                        ))
         ((when (or* (> traversed-cnt (* 2 len-leaves))
                     (< found-cnt len-leaves)))
          (and limit-reached
               (bitxor/or/and-equiv-iter fn arg1 arg2 other-svex (1+ cnt))))
         ((mv leaves2 valid)
          (bitxor/or/and-equiv-aux other-svex fn leaves))

         (leaves2 (cond ((or (equal fn 'bitor)
                             (equal fn 'bitand))
                         (remove-duplicates-equal leaves2))
                        ((equal fn 'bitxor)
                         ;; Removing  pairs from  bitxor requires  the removed
                         ;; ones to be integer. I am only doing it for contants
                         ;; here because I don't want  to add that here because
                         ;; it requires context
                         (remove-pair-equal leaves2))
                        (t  leaves2)))

         #|(- (and (equal fn 'bitxor)
         (has-two-ones leaves)
         valid
         (equal leaves2 leaves)
         ;; if the below message appears, I can implement a way to remove pairs of integers from bitxor.
         (rp::cwe "In svl::bitxor/or/and-equiv-iter. Leaves of bitxor have two ones: ~p0. This may mean a fix is necessary... ~%" leaves)))|#
         )
      (and valid
           (equal leaves2 leaves))))
  ///

  (local
   (svex-eval-lemma-tmpl
    (defthm svex-eval-bitor/and-lst-of-remove-duplicates-equal-2
      (implies (syntaxp (and (consp lst)
                             (equal (car lst) 'binary-append)))
               (and (equal (svex-eval-bitor-lst (remove-duplicates-equal lst) env)
                           (svex-eval-bitor-lst lst env))
                    (equal (svex-eval-bitand-lst (remove-duplicates-equal lst) env)
                           (svex-eval-bitand-lst lst env))
                    (equal (svex-eval-bitxor-lst (remove-pair-equal lst) env)
                           (svex-eval-bitxor-lst lst env)))))))

  (local
   (in-theory (disable svex-eval-bitor/and-lst-of-remove-duplicates-equal
                       svex-eval$-bitor/and-lst-of-remove-duplicates-equal
                       svex-eval-bitxor-lst-of-remove-pair-equal
                       svex-eval$-bitxor-lst-of-remove-pair-equal
                       svex-eval-of-bitxor/or/and-equiv-aux-is-correct
                       svex-eval$-of-bitxor/or/and-equiv-aux-is-correct)))

  (svex-eval-lemma-tmpl
   (defret svex-eval-<fn>-is-correct
     (and (implies (and (or (equal fn 'bitand)
                            (equal fn 'bitor)
                            (equal fn 'bitxor))
                        equiv)
                   (equal (svex-eval `(,fn ,arg1 ,arg2) env)
                          (sv::3vec-fix (svex-eval other-svex env))))
          )
     :fn bitxor/or/and-equiv-iter
     :hints ((and stable-under-simplificationp
                  '(:use ((:instance svex-eval-of-bitxor/or/and-equiv-aux-is-correct
                                     (svex other-svex)
                                     (fn 'bitand)
                                     (leaves (remove-duplicates-equal
                                              (append (mv-nth 0
                                                              (bitand/or/xor-collect-leaves2 arg1 'bitand
                                                                                             cnt))
                                                      (mv-nth 0
                                                              (bitand/or/xor-collect-leaves2 arg2 'bitand
                                                                                             cnt))))))
                          (:instance svex-eval-of-bitxor/or/and-equiv-aux-is-correct
                                     (svex other-svex)
                                     (fn 'bitxor)
                                     (leaves (remove-pair-equal
                                              (append (mv-nth 0
                                                              (bitand/or/xor-collect-leaves2 arg1 'bitxor
                                                                                             cnt))
                                                      (mv-nth 0
                                                              (bitand/or/xor-collect-leaves2 arg2 'bitxor
                                                                                             cnt))))))
                          (:instance svex-eval-of-bitxor/or/and-equiv-aux-is-correct
                                     (svex other-svex)
                                     (fn 'bitor)
                                     (leaves (REMOVE-DUPLICATES-EQUAL
                                              (append (mv-nth 0
                                                              (bitand/or/xor-collect-leaves2 arg1 'bitor
                                                                                             cnt))
                                                      (mv-nth 0
                                                              (bitand/or/xor-collect-leaves2 arg2 'bitor
                                                                                             cnt))))))
                          )))))))

(define bitxor/or/and-equiv (fn arg1 arg2 other-svex)
  :returns (equiv)

  (case-match other-svex
    ((fn-2 arg1-2 arg2-2)
     (b* (((Unless (equal fn-2 fn))
           nil)
          ((when ;; quick check first.
               (or (and* (equal arg1 arg1-2)
                         (equal arg2 arg2-2))
                   (and* (equal arg2 arg1-2)
                         (equal arg1 arg2-2))))
           t))
       (bitxor/or/and-equiv-iter fn arg1 arg2 other-svex 1))))
  ///
  (svex-eval-lemma-tmpl
   (defret svex-eval-of-<fn>-is-correct
     (implies (and equiv
                   (or (equal fn 'bitand)
                       (equal fn 'bitor)
                       (equal fn 'bitxor)))
              (equal (svex-eval other-svex env)
                     (svex-eval `(,fn ,arg1 ,arg2) env)))
     :rule-classes (:rewrite))))

;; (bitxor/or/and-equiv 'bitor 'e '(bitor f (bitor d (bitor a (bitor c b))))
;;                      '(bitor (bitor (bitor a b) c) (bitor d (bitor e f))))

;; (bitxor/or/and-equiv 'bitor '(bitor a b) 'c
;;                      '(bitor (bitor a c) b))

;; (bitxor/or/and-equiv 'bitor '(bitor a b) '(bitor a c)
;;                      '(bitor (bitor a (bitor a (bitor a c))) b))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
