
; Multiplier verification

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
; Original author: Mertcan Temel <mert.temel@intel.com>

(in-package "RP")

(include-book "fnc-defs")
(include-book "centaur/svl/top" :dir :system)

(local
 (include-book "centaur/bitops/ihs-extensions" :dir :system))

(local
 (include-book "ihs/logops-lemmas" :dir :system))

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/equal-by-logbitp" :dir :system)
  use-equal-by-logbitp
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5
  :disabled t))

(defsection svex-pattern-matching-lemmas
  (defthm cdr-of-x-is-svexlist-p-when-kind-is-svex-fn-call
    (implies (and (sv::svex-p x)
                  (equal (sv::svex-kind x) :call))
             (sv::svexlist-p (cdr x)))
    :rule-classes (:forward-chaining
                   :type-prescription
                   :rewrite)
    :hints (("goal"
             :in-theory (e/d (sv::svex-kind
                              sv::svex-p) ()))))

  (defthm x-is-svexlist-p-when-kind-is-svex-fn-call-2
    (implies (and (sv::svex-p x)
                  (consp x)
                  (consp (cdr x))
                  (not (equal (car x) :var))
                  (not (integerp (car x)))
                  (force (equal (sv::svex-kind x) :call)))
             (and (sv::svex-p (cadr x))
                  (implies (consp (cddr x))
                           (and (sv::svex-p (caddr x))
                                (implies (consp (cdddr x))
                                         (sv::svex-p (cadddr x)))))))
    :rule-classes (:rewrite)
    :hints (("goal"
             :in-theory '(sv::svex-kind
                          sv::svex-p
                          sv::svexlist-p))))

  (defthm sv::svexlist-p-of-merge-lexorder
    (implies (and (true-listp l1)
                  (true-listp l2)
                  (true-listp acc))
             (equal
              (sv::svexlist-p (acl2::merge-lexorder l1 l2 acc))
              (and (sv::svexlist-p l1)
                   (sv::svexlist-p l2)
                   (sv::svexlist-p acc))))
    :hints (("goal"
             :in-theory (e/d (acl2::merge-lexorder) ()))))

  (defthm sv::svexlist-p-of-evens/odds
    (implies (sv::svexlist-p l1)
             (and (sv::svexlist-p (evens l1))
                  (sv::svexlist-p (odds l1))))
    :hints (("goal"
             :in-theory (e/d (sv::svexlist-p) ()))))

  (defthm sv::svexlist-p-of-merge-sort-lexorder
    (implies (force (sv::svexlist-p lst))
             (sv::svexlist-p (acl2::merge-sort-lexorder lst)))
    :hints (("goal"
             :in-theory (e/d (sv::svexlist-p
                              acl2::merge-sort-lexorder)
                             (acl2::merge-lexorder
                              evens
                              odds)))))

  (defthm svexlist-count-of-append
    (implies t
             (equal (sv::svexlist-count (append x y))
                    (+ -1
                       (sv::svexlist-count x)
                       (sv::svexlist-count y))))
    :rule-classes (:linear :rewrite)
    :hints (("goal"
             :expand ((sv::svexlist-count x)
                      (sv::svexlist-count (cons (car x) (append (cdr x) y))))
             :do-not-induct t
             :induct (append x y)
             :in-theory (e/d () ()))))

  (defthm svexlist-count-of-rev
    (equal (sv::svexlist-count (rev x))
           (sv::svexlist-count x))
    :hints (("goal"
             :induct (rev x)
             :expand ((sv::svexlist-count x)
                      (sv::svexlist-count (list (car x))))
             :in-theory (e/d (rev)
                             ((:e tau-system))))))

  (defthm svexlist-count-of-merge-lexorder
    (equal (sv::svexlist-count (acl2::merge-lexorder l1 l2 acc))
           (+ (sv::svexlist-count l1)
              (sv::svexlist-count l2)
              (sv::svexlist-count acc)
              -2))
    :hints (("goal"
             :in-theory (e/d (sv::svexlist-count)
                             ((:e tau-system))))))

  (defthm sv::svexlist-count-of-evens
    (implies (syntaxp (atom l1))
             (equal (sv::svexlist-count (evens l1))
                    (+ (sv::svexlist-count l1)
                       (- (sv::svexlist-count (evens (cdr l1))))
                       +1)))
    :hints (("goal"
             ;;:do-not-induct t
             ;;:induct (evens l1)
             :in-theory (e/d (sv::svexlist-count)
                             ((:e tau-system))))))

  (defthm svexlist-count-of-merge-sort-lexorder
    (equal (sv::svexlist-count (acl2::merge-sort-lexorder l1))
           (sv::svexlist-count l1))
    :hints (("goal"
             :induct (acl2::merge-sort-lexorder l1)
             :do-not-induct t
             :in-theory (e/d (sv::svexlist-count)
                             ((:e tau-system))))))

  (define acl2::merge-sort-lexorder-2 ((x true-listp))
    :enabled t
    (acl2::merge-sort-lexorder x))

  (defthm svex-p-of-fn-call
    (implies (and (not (equal fn :var))
                  (sv::fnsym-p fn))
             (equal (sv::svex-p (cons fn lst))
                    (sv::svexlist-p lst)))
    :hints (("goal"
             :in-theory (e/d (sv::svex-p
                              sv::svexlist-p)
                             ())))))

(local
 (in-theory (disable acl2::merge-sort-lexorder
                     acl2::merge-lexorder)))

(defsection pattern-fn-call

  (defsection sv::strict-fnsym
    :set-as-default-parent t

    (define sv::strict-fnsym-p (fn)
      (and (sv::fnsym-p fn)
           (not (equal fn :var)))
      ///
      (defthm sv::strict-fnsym-p-compound-recognizer
        (implies (sv::strict-fnsym-p x)
                 (symbolp x))
        :rule-classes (:compound-recognizer))
      (defthm sv::strict-fnsym-p-compound-recognizer-2
        (implies (sv::strict-fnsym-p x)
                 (sv::fnsym-p x))
        :rule-classes (:compound-recognizer
                       :type-prescription
                       :rewrite))
      (defthm sv::strict-fnsym-p-implies
        (implies (sv::strict-fnsym-p fn)
                 (and (sv::fnsym-p fn)
                      (not (equal fn :var))))
        :rule-classes :forward-chaining))

    (define sv::strict-fnsym-fix (x)
      :returns (x sv::strict-fnsym-p)
      (if (sv::strict-fnsym-p x)
          x
        'id)
      ///
      (defthm sv::strict-fnsym-fix-when-strict-fnsym-p
        (implies (sv::strict-fnsym-p x)
                 (equal (sv::strict-fnsym-fix x) x))))

    (fty::deffixtype sv::strict-fnsym
      :pred sv::strict-fnsym-p
      :fix sv::strict-fnsym-fix
      :equiv sv::strict-fnsym-equiv
      :define t
      :forward t
      :equal eq))

  (fty::defprod pattern-fn-call
    ((fn sv::strict-fnsym-p)
     (extra-arg acl2::maybe-natp)
     (args sv::svexlist-p)
     (rule pseudo-termp)
     )
    :layout :fulltree
    ;;:hons t
    )

  (define pattern-call ((x pattern-fn-call-p)
                        &optional args)
    (b* (((pattern-fn-call x)))
      (hons x.fn
            (if x.extra-arg
                (hons x.extra-arg
                      (if args args x.args))
              (if args args x.args)))))

  (defthm pattern-fn-call->fn-is-not-var
    (and (not (equal (pattern-fn-call->fn x) :var))
         (sv::fnsym-p (pattern-fn-call->fn x)))
    :hints (("goal"
             :in-theory (e/d (sv::strict-fnsym-fix
                              pattern-fn-call->fn)
                             ()))))

  (fty::deflist pattern-fn-call-list
    :elt-type pattern-fn-call
    :true-listp t)

  (define pattern-fn-call-provide-good-measure-p ((x sv::Svex-p)
                                                  (pattern-fn-call pattern-fn-call-p))
    :guard-hints (("Goal"
                   :in-theory (e/d () ())))
    (b* (((pattern-fn-call pattern-fn-call)))
      (< (sv::svexlist-count pattern-fn-call.args)
         (sv::svex-count x))))

  (define pattern-fn-call-list-provide-good-measure-p ((x sv::svex-p)
                                                       (lst pattern-fn-call-list-p))
    :enabled t
    (if (atom lst)
        (equal lst nil)
      (and (pattern-fn-call-provide-good-measure-p x (car lst))
           (pattern-fn-call-list-provide-good-measure-p x (cdr lst))))
    ///
    (defthm pattern-fn-call-list-provide-good-measure-p-of-append
      (implies (and (pattern-fn-call-list-provide-good-measure-p x lst1)
                    (pattern-fn-call-list-provide-good-measure-p x lst2))
               (pattern-fn-call-list-provide-good-measure-p x (append lst1 lst2))))

    (defthm pattern-fn-call-list-provide-good-measure-p-and-member
      (implies (and (pattern-fn-call-list-provide-good-measure-p x lst)
                    (member-equal e lst))
               (pattern-fn-call-provide-good-measure-p x e)))

    )

  (define pattern-alist-p (x)
    :enabled t
    :returns (valid)
    (if (atom x)
        (equal x nil)
      (and (consp (car x))
           (sv::svexlist-p (caar x))
           (true-listp (cdar x))
           (pattern-alist-p (cdr x))))
    ///
    (defret <fn>-with-hons-assoc-equal
      (implies (and (pattern-alist-p x)
                    (case-split (hons-assoc-equal key x)))
               (and (consp (hons-assoc-equal key x))
                    (sv::svexlist-p (car (hons-assoc-equal key x)))
                    (true-listp (cdr (hons-assoc-equal key x)))))
      :rule-classes (:rewrite :forward-chaining))

    (defthm <fn>-implies-alistp
      (implies (pattern-alist-p x)
               (alistp x))))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; adder pattern functions...

(local
 (in-theory (e/d (sv::svex-kind)
                 ((:e tau-system)))))

(local
 (defsection 4vec-lemmas

   (defthm 4vec-concat$-to-logapp
     (implies (and (natp size)
                   (integerp x)
                   (integerp y))
              (equal (svl::4vec-concat$ size x y)
                     (logapp size x y)))
     :hints (("Goal"
              :in-theory (e/d (SVL::4VEC-CONCAT$
                               SVL::LOGAPP-TO-4VEC-CONCAT)
                              ()))))

   (defthm sv::4vec-bitops-to-logops
     (and (implies (and (integerp x)
                        (integerp y))
                   (and (equal (sv::4vec-bitxor x y)
                               (logxor x y))
                        (equal (sv::4vec-bitand x y)
                               (logand x y))
                        (equal (sv::4vec-bitor x y)
                               (logior x y))))
          (implies (integerp x)
                   (equal (sv::4vec-bitnot x)
                          (lognot x))))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d* (sv::4vec
                                sv::4vec-bitand
                                SV::3VEC-BITAND
                                SV::3VEC-BITOR
                                sv::4vec-bitor
                                SV::3VEC-BITNOT
                                sv::4vec-bitnot
                                bitops::ihsext-inductions
                                bitops::ihsext-recursive-redefs
                                sv::4vec-bitxor
                                SV::4VEC->LOWER
                                SV::4VEC->UPPER
                                SV::4VEC-RSH
                                sv::4VEC-SHIFT-CORE
                                svl::Bits
                                SV::4VEC-PART-SELECT
                                SV::4VEC-CONCAT)
                               (floor
                                SVL::EQUAL-OF-4VEC-CONCAT-WITH-SIZE=1
                                logand
                                )))))

   ))

(local
 (defthm SV::SVEXLIST-EVAL$-when-consp
   (implies (consp lst)
            (equal (SV::SVEXLIST-EVAL$ lst env)
                   (CONS (SV::SVEX-EVAL$ (CAR lst) env)
                         (SV::SVEXLIST-EVAL$ (CDR lst) env))))))

(defmacro create-look-for-pattern-fnc (&key name
                                            body
                                            warrant-hyps
                                            prepwork
                                            postwork
                                            good-measure-hints
                                            correct-pattern-hints
                                            (Inline 't)
                                            (enable-2 'nil))
  `(progn
     (define ,(intern-in-package-of-symbol (str::cat "LOOK-FOR-" (SYMBOL-NAME name))
                                           name)
       ((svex sv::svex-p))
       :returns (res pattern-fn-call-list-p
                     :hyp (sv::svex-p svex))
       :prepwork ,prepwork
       :inline ,inline
       ,body
       ///
       (defret <fn>-good-measure
         (implies (sv::svex-p svex)
                  (pattern-fn-call-list-provide-good-measure-p svex res))
         :hints (("Goal"
                  :expand ((sv::svex-count svex)
                           (sv::svexlist-count (cdr svex))
                           (sv::svex-count (cadr svex))
                           (sv::svexlist-count (cdr (cadr svex))))
                  :in-theory (e/d (pattern-fn-call
                                   pattern-call
                                   pattern-fn-call->fn
                                   pattern-fn-call->args
                                   pattern-fn-call->extra-arg
                                   sv::svex-count
                                   sv::svex-call->args
                                   sv::svex-kind
                                   sv::svexlist-count
                                   pattern-fn-call-provide-good-measure-p
                                   pattern-fn-call-list-provide-good-measure-p)
                                  (acl2::merge-sort-lexorder)))
                 ,@(and good-measure-hints
                        `((and stable-under-simplificationp
                               ,good-measure-hints)))))
       (defret <fn>-correct-pattern
         (implies (and ,@warrant-hyps
                       (pattern-fn-call->rule pattern)
                       (member-equal pattern res))
                  (equal (sv::svex-eval$ (pattern-call pattern) env)
                         (sv::svex-eval$ svex env)))
         :hints (("goal"
                  :expand ((:free (args)
                                  (sv::svex-eval$ (cons 'fa-c-chain args)
                                                  env))
                           (:free (x y)
                                  (pattern-call (cons x y))))
                  :in-theory (e/d (,@enable-2
                                   svl::insert-4vec-bitand-into-4vec-bitor
                                   ;;pattern-call
                                   pattern-fn-call->fn
                                   pattern-fn-call->args
                                   pattern-fn-call->extra-arg
                                   pattern-fn-call
                                   acl2::merge-sort-lexorder
                                   acl2::merge-lexorder
                                   sv::svex-call->fn
                                   sv::svex-call->args
                                   sv::svex-apply$
                                   sv::svex-apply
                                   sv::svexlist-eval$)
                                  ((:rewrite sv::svex-eval$-when-quote)
                                   acl2::integerp-of-car-when-integer-listp
                                   acl2::symbolp-of-car-when-symbol-listp
                                   acl2::true-list-listp-implies-true-listp-xxx
                                   (:rewrite default-car)
                                   (:rewrite sv::svexlist-fix-when-svexlist-p)
                                   (:rewrite sv::svexlist-p-of-merge-lexorder)
                                   default-cdr
                                   integer-listp)))
                 ,@(and correct-pattern-hints
                        `((and stable-under-simplificationp
                               ,correct-pattern-hints)))))

       ,@postwork)))

;; not used..
(defines svex-has-more-than-one-var-p
  ;; returns nil,t, or the symbol of the only variable.
  ;; nil means no vars are found,
  ;; t means more than 1 one is found,
  ;; otherwise (a symbol) only one var is found.
  (define svex-has-more-than-one-var-p ((x sv::Svex-p))
    :measure (sv::svex-count x)
    (sv::Svex-case
     x
     :quote nil
     :var  x
     :call (svexlist-has-more-than-one-var-p x.args)))
  (define svexlist-has-more-than-one-var-p ((lst sv::svexlist-p))
    :measure (sv::svexlist-count lst)
    (if (atom lst)
        nil
      (b* ((cur (svex-has-more-than-one-var-p (car lst)))
           ((when (equal cur 't))
            cur)
           (rest (svexlist-has-more-than-one-var-p (cdr lst)))
           ((when (equal rest nil))
            cur)
           ((when (equal rest 't))
            rest)
           ((when (equal cur nil))
            rest))
        (if (equal cur rest)
            cur
          t))))
  ///
  (memoize 'svex-has-more-than-one-var-p
           :condition '(eq (sv::svex-kind x) :call)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ADDER PATTERN RECOGNIZERS.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection fa-s-chain

  (define fa-s-chain (x y z)
    :verify-guards nil
    (sv::4vec-bitxor x (sv::4vec-bitxor y z))
    ///
    (defwarrant-rp fa-s-chain)

    (def-rp-rule :disabled-for-acl2 t
      fa-s-chain-s-spec
      (implies (and (integerp x) (integerp y) (integerp z))
               (equal (fa-s-chain x y z)
                      (svl::4vec-concat$
                       1 (s-spec (list (logcar x) (logcar y) (logcar z)))
                       (fa-s-chain (logcdr x) (logcdr y) (logcdr z)))))
      :hints (("Goal"
               :in-theory (e/d* (bitops::ihsext-inductions bitops::ihsext-recursive-redefs)
                                ())))))

  (defconst *fa-s-chain-rule*
    (hons-copy '(member-equal 'fa-c-chain found-patterns)))

  (create-look-for-pattern-fnc :name fa-s-chain-pattern-1
                               :prepwork ((create-case-match-macro fa-s-chain-pattern-1
                                                                   ('sv::bitxor ('sv::bitxor x y) z))
                                          (local
                                           (in-theory (enable fa-s-chain))))
                               :body
                               (and (fa-s-chain-pattern-1-p svex)
                                    (fa-s-chain-pattern-1-body
                                     svex
                                     (b* ((args (acl2::merge-sort-lexorder (list x y z))))
                                       (list (make-pattern-fn-call
                                              :fn 'fa-s-chain
                                              :rule *fa-s-chain-rule*
                                              :args args)))))
                               :warrant-hyps ((apply$-warrant-fa-s-chain)))

  (create-look-for-pattern-fnc :name fa-s-chain-pattern-2
                               :prepwork ((create-case-match-macro fa-s-chain-pattern-2
                                                                   ('sv::bitxor x ('sv::bitxor y z)))
                                          (local
                                           (in-theory (enable fa-s-chain))))
                               :body
                               (and (fa-s-chain-pattern-2-p svex)
                                    (fa-s-chain-pattern-2-body
                                     svex
                                     (b* ((args (acl2::merge-sort-lexorder (list x y z))))
                                       (list (make-pattern-fn-call
                                              :fn 'fa-s-chain
                                              :rule *fa-s-chain-rule*
                                              :args args)))))
                               :warrant-hyps ((apply$-warrant-fa-s-chain)))

  (create-look-for-pattern-fnc :name fa-s-chain-pattern
                               :prepwork ()
                               :body (append (look-for-fa-s-chain-pattern-1 svex)
                                             (look-for-fa-s-chain-pattern-2 svex)
                                             )
                               :warrant-hyps ((apply$-warrant-fa-s-chain))
                               :inline nil))

(defsection fa-c-chain
  (define fa-c-chain (method x y z)
    :verify-guards nil
    ;; !!!!!!!!!!!
    ;; unfortunately, 4vec-bitxor is differently defined than other stuff like 4vec-bitand, so
    ;; arguments cannot be commuted around for the fa-carry pattern that
    ;; involves bitxor. So I have to do this stuff:
    ;; !!!!!!!!!!!
    (cond ((= method 1)
           (sv::4vec-bitor (sv::4vec-bitand y z)
                           (sv::4vec-bitand x
                                            (sv::4vec-bitxor y z))))
          ((= method 2)
           (sv::4vec-bitor (sv::4vec-bitand x z)
                           (sv::4vec-bitand y
                                            (sv::4vec-bitxor x z))))
          ((= method 3)
           (sv::4vec-bitor (sv::4vec-bitand x y)
                           (sv::4vec-bitand z
                                            (sv::4vec-bitxor x y))))

          (t
           (sv::4vec-bitor (sv::4vec-bitand x y)
                           (sv::4vec-bitor (sv::4vec-bitand x z)
                                           (sv::4vec-bitand y z)))))
    ///
    (defwarrant-rp fa-c-chain)

    (local
     (defthm sanity
       (implies (and (bitp x)
                     (bitp y)
                     (bitp z))
                (equal (fa-c-chain method x y z)
                       (c-spec (list x y z))))
       :hints (("Goal"
                :in-theory (e/d (bitp) ())))))

    (def-rp-rule fa-c-chain-c-spec
      (implies (and (integerp x)
                    (integerp y)
                    (integerp z)
                    (not (> method 40)))
               (equal (fa-c-chain method x y z)
                      (svl::4vec-concat$
                       1
                       (c-spec (list (logcar x) (logcar y) (logcar z)))
                       (fa-c-chain method (logcdr x) (logcdr y) (logcdr z)))))
      :hints (("goal"
               :do-not-induct t))))

  (define look-for-fa-c-chain-pattern-aux (&key
                                           (x1 'x1)
                                           (x2 'x2)
                                           (y1 'y1)
                                           (y2 'y2)
                                           (z1 'z1)
                                           (z2 'z2))
    :enabled t
    :returns (mv x y z valid)
    (b* (((mv x y1 z1 valid)
          (cond ((equal x1 x2)
                 (mv x1 y1 z1 t))
                ((equal x1 z1)
                 (mv x1 y1 x2 t))
                ((equal y1 x2)
                 (mv y1 x1 z1 t))
                ((equal y1 z1)
                 (mv y1 x1 x2 t))
                (t
                 (mv 0 0 0 nil))))
         ((unless valid)
          (mv 0 0 0 nil))
         ((mv y z valid)
          (cond ((and (equal y1 y2)
                      (equal z1 z2))
                 (mv y1 z1 t))
                ((and (equal y1 z2)
                      (equal z1 y2))
                 (mv y1 z1 t))
                (t
                 (mv 0 0 nil))))
         ((unless valid)
          (mv 0 0 0 nil)))
      (mv x y z t))
    )

  (defconst *fa-c-chain-rule*
    ;;t
    (hons-copy '(member-equal 'fa-s-chain found-patterns))
    )

  ;; this is  to recollect the  found patterns so  missed fa-s patterns  may be
  ;; found. (sometimes the same fa-s may  appear in different shapes within the
  ;; same svex.  some would be  caught in quick search  and some could  only be
  ;; caught in slow  search. For the latter group, recollecting  the found fa-c
  ;; is necessary.)
  (create-look-for-pattern-fnc :name fa-c-chain-itself-pattern
                               :prepwork ((create-case-match-macro fa-c-chain-itself-pattern
                                                                   ('fa-c-chain m x y z))
                                          (local
                                           (in-theory (e/d (pattern-fn-call->rule)
                                                           (fa-c-chain)))))
                               :body
                               (cond ((fa-c-chain-itself-pattern-p svex)
                                      (fa-c-chain-itself-pattern-body
                                       svex
                                       (and (natp m)
                                            (list (make-pattern-fn-call
                                                   :fn 'fa-c-chain
                                                   :extra-arg m
                                                   :rule nil
                                                   :args
                                                   (acl2::merge-sort-lexorder (list x y z))))))))
                               :warrant-hyps ((apply$-warrant-fa-c-chain)))

  ;; most-common pattern
  (create-look-for-pattern-fnc :name fa-c-chain-pattern-01
                               :prepwork ((create-case-match-macro fa-c-chain-pattern-0
                                                                   ('sv::bitor ('sv::bitor ('sv::bitand x1 y1)
                                                                                           ('sv::bitand x2 z1))
                                                                               ('sv::bitand y2 z2)))
                                          (create-case-match-macro fa-c-chain-pattern-1
                                                                   ('sv::bitor  ('sv::bitand y2 z2)
                                                                                ('sv::bitor ('sv::bitand x1 y1)
                                                                                            ('sv::bitand
                                                                                             x2 z1))))
                                          (local
                                           (in-theory (enable fa-c-chain))))
                               :body
                               (cond ((fa-c-chain-pattern-0-p svex)
                                      (fa-c-chain-pattern-0-body
                                       svex
                                       (b* (((mv x y z valid) (look-for-fa-c-chain-pattern-aux))
                                            ((unless valid) nil)
                                            (args (acl2::merge-sort-lexorder (list x y z))))
                                         (list (make-pattern-fn-call
                                                :fn 'fa-c-chain
                                                :extra-arg 0
                                                :rule *fa-c-chain-rule*
                                                :args args)))))
                                     ((fa-c-chain-pattern-1-p svex)
                                      (fa-c-chain-pattern-1-body
                                       svex
                                       (b* (((mv x y z valid) (look-for-fa-c-chain-pattern-aux))
                                            ((unless valid) nil)
                                            (args (acl2::merge-sort-lexorder (list x y z))))
                                         (list (make-pattern-fn-call
                                                :fn 'fa-c-chain
                                                :extra-arg 0
                                                :rule *fa-c-chain-rule*
                                                :args args))))))
                               :warrant-hyps ((apply$-warrant-fa-c-chain)))

  (create-look-for-pattern-fnc :name fa-c-chain-pattern-2a
                               :prepwork ((create-case-match-macro fa-c-chain-pattern-2a
                                                                   ('sv::bitor  ('sv::bitand y z)
                                                                                ('sv::bitand x yz)))
                                          (local
                                           (in-theory (enable fa-c-chain))))
                               :body
                               (and (fa-c-chain-pattern-2a-p svex)
                                    (fa-c-chain-pattern-2a-body
                                     svex
                                     (b* ((or/xor? (and (consp yz)
                                                        (or  (equal (car yz) 'sv::bitor)
                                                             (equal (car yz) 'sv::bitxor))
                                                        (car yz)))
                                          ((unless or/xor?) nil)
                                          (valid (svl::bitxor/or/and-equiv or/xor? y z yz))
                                          ((unless valid) nil)
                                          (args (acl2::merge-sort-lexorder (list x y z))))
                                       (list (make-pattern-fn-call
                                              :fn 'fa-c-chain
                                              :extra-arg (cond ((equal or/xor? 'sv::bitor)
                                                                0)
                                                               ((equal (car args) x)
                                                                1)
                                                               ((equal (cadr args) x)
                                                                2)
                                                               ((equal (caddr args) x)
                                                                3))
                                              :rule *fa-c-chain-rule*
                                              :args args)))))
                               :warrant-hyps ((apply$-warrant-fa-c-chain)))

  (create-look-for-pattern-fnc :name fa-c-chain-pattern-2b
                               :prepwork ((create-case-match-macro fa-c-chain-pattern-2b
                                                                   ('sv::bitor  ('sv::bitand y z)
                                                                                ('sv::bitand
                                                                                 yz x)))
                                          (local
                                           (in-theory (enable fa-c-chain))))
                               :body
                               (and (fa-c-chain-pattern-2b-p svex)
                                    (fa-c-chain-pattern-2b-body
                                     svex
                                     (b* ((or/xor? (and (consp yz)
                                                        (or  (equal (car yz) 'sv::bitor)
                                                             (equal (car yz) 'sv::bitxor))
                                                        (car yz)))
                                          ((unless or/xor?) nil)
                                          (valid (svl::bitxor/or/and-equiv or/xor? y z yz))
                                          ((unless valid) nil)
                                          (args (acl2::merge-sort-lexorder (list x y z))))
                                       (list (make-pattern-fn-call
                                              :fn 'fa-c-chain
                                              :extra-arg (cond ((equal or/xor? 'sv::bitor)
                                                                0)
                                                               ((equal (car args) x)
                                                                1)
                                                               ((equal (cadr args) x)
                                                                2)
                                                               ((equal (caddr args) x)
                                                                3))
                                              :rule *fa-c-chain-rule*
                                              :args args)))))
                               :warrant-hyps ((apply$-warrant-fa-c-chain)))

  (create-look-for-pattern-fnc :name fa-c-chain-pattern-2c
                               :prepwork ((create-case-match-macro fa-c-chain-pattern-2c
                                                                   ('sv::bitor  ('sv::bitand x yz)
                                                                                ('sv::bitand
                                                                                 y z)))
                                          (local
                                           (in-theory (enable FA-C-CHAIN))))
                               :body
                               (and (fa-c-chain-pattern-2c-p svex)
                                    (fa-c-chain-pattern-2c-body
                                     svex
                                     (b* ((or/xor? (and (consp yz)
                                                        (or  (equal (car yz) 'sv::bitor)
                                                             (equal (car yz) 'sv::bitxor))
                                                        (car yz)))
                                          ((unless or/xor?) nil)
                                          (valid (svl::bitxor/or/and-equiv or/xor? y z yz))
                                          ((unless valid) nil)
                                          (args (acl2::merge-sort-lexorder (list x y z))))
                                       (list (make-pattern-fn-call
                                              :fn 'fa-c-chain
                                              :extra-arg (cond ((equal or/xor? 'sv::bitor)
                                                                0)
                                                               ((equal (car args) x)
                                                                1)
                                                               ((equal (cadr args) x)
                                                                2)
                                                               ((equal (caddr args) x)
                                                                3))
                                              :rule *fa-c-chain-rule*
                                              :args args)))))
                               :warrant-hyps ((apply$-warrant-fa-c-chain)))

  (create-look-for-pattern-fnc :name fa-c-chain-pattern-2d
                               :prepwork ((create-case-match-macro fa-c-chain-pattern-2d
                                                                   ('sv::bitor  ('sv::bitand yz x)
                                                                                ('sv::bitand
                                                                                 y z)))
                                          (local
                                           (in-theory (enable FA-C-CHAIN))))
                               :body
                               (and (fa-c-chain-pattern-2d-p svex)
                                    (fa-c-chain-pattern-2d-body
                                     svex
                                     (b* ((or/xor? (and (consp yz)
                                                        (or  (equal (car yz) 'sv::bitor)
                                                             (equal (car yz) 'sv::bitxor))
                                                        (car yz)))
                                          ((unless or/xor?) nil)
                                          (valid (svl::bitxor/or/and-equiv or/xor? y z yz))
                                          ((unless valid) nil)
                                          (args (acl2::merge-sort-lexorder (list x y z))))
                                       (list (make-pattern-fn-call
                                              :fn 'fa-c-chain
                                              :extra-arg (cond ((equal or/xor? 'sv::bitor)
                                                                0)
                                                               ((equal (car args) x)
                                                                1)
                                                               ((equal (cadr args) x)
                                                                2)
                                                               ((equal (caddr args) x)
                                                                3))
                                              :rule *fa-c-chain-rule*
                                              :args args)))))
                               :warrant-hyps ((apply$-warrant-fa-c-chain)))

  (create-look-for-pattern-fnc :name fa-c-chain-pattern
                               :prepwork ()
                               :body (append (look-for-fa-c-chain-pattern-01 svex)
                                             (look-for-fa-c-chain-pattern-2a svex)
                                             (look-for-fa-c-chain-pattern-2b svex)
                                             (look-for-fa-c-chain-pattern-2c svex)
                                             (look-for-fa-c-chain-pattern-2d svex)
                                             (look-for-fa-c-chain-itself-pattern svex)
                                             )
                               :warrant-hyps ((apply$-warrant-fa-c-chain))
                               :inline nil))

(defsection ha-s-chain

  (define ha-s-chain (x y)
    :verify-guards nil
    (sv::4vec-bitxor x y)
    ///
    (defwarrant-rp ha-s-chain)
    (def-rp-rule :disabled-for-acl2 t
      ha-s-chain-to-s-spec
      (implies (and (integerp x) (integerp y))
               (equal (ha-s-chain x y)
                      (svl::4vec-concat$ 1
                                         (s-spec (list (logcar x) (logcar y)))
                                         (ha-s-chain (logcdr x) (logcdr y)))))
      :hints (("goal"
               :in-theory (e/d* (sv::4vec
                                 bitops::ihsext-recursive-redefs
                                 sv::4vec-bitxor
                                 sv::4vec->lower
                                 sv::4vec->upper
                                 sv::4vec-rsh
                                 sv::4vec-shift-core
                                 svl::bits
                                 sv::4vec-part-select
                                 sv::4vec-concat)
                                (floor
                                 svl::equal-of-4vec-concat-with-size=1
                                 logand
                                 ))))))

  (defconst *ha-s-chain-rule*
    (hons-copy '(member-equal 'ha-c-chain found-patterns)))

  (create-look-for-pattern-fnc :name ha-s-chain-pattern
                               :prepwork ((create-case-match-macro ha-s-chain-pattern
                                                                   ('sv::bitxor x y))
                                          (local (in-theory (enable ha-s-chain))))
                               :body
                               (and (ha-s-chain-pattern-p svex)
                                    (ha-s-chain-pattern-body
                                     svex
                                     (b* ((args (acl2::merge-sort-lexorder (list x y))))
                                       (list (make-pattern-fn-call
                                              :fn 'ha-s-chain
                                              :rule *ha-s-chain-rule*
                                              :args args)))))
                               :warrant-hyps ((apply$-warrant-ha-s-chain))))

(defsection ha-c-chain

  (define ha-c-chain (x y)
    ;;:ignorable (method)
    :verify-guards nil
    (sv::4vec-bitand x y)
    ///
    (defwarrant-rp ha-c-chain)

    (def-rp-rule ha-c-chain-to-c-spec
      (implies (and (integerp x) (integerp y))
               (equal (ha-c-chain x y)
                      (svl::4vec-concat$
                       1 (c-spec (list (logcar x) (logcar y)))
                       (ha-c-chain (logcdr x) (logcdr y)))))
      :hints (("Goal"
               :in-theory (e/d* (bitops::ihsext-recursive-redefs)
                                ())))))

  (defconst *ha-c-chain-rule*
    (hons-copy '(member-equal 'ha-s-chain found-patterns)))

  (create-look-for-pattern-fnc :name ha-c-chain-pattern
                               :prepwork ((create-case-match-macro ha-c-chain-pattern
                                                                   ('sv::bitand x y))
                                          (create-case-match-macro ha-c-chain-pattern-itself
                                                                   ('ha-c-chain x y))
                                          (local (in-theory (enable ha-c-chain))))
                               :body
                               (append (and (ha-c-chain-pattern-p svex)
                                            (ha-c-chain-pattern-body
                                             svex
                                             (list (make-pattern-fn-call
                                                    :fn 'ha-c-chain
                                                    :rule *ha-c-chain-rule*
                                                    :args (acl2::merge-sort-lexorder (list x y))))))
                                       (and (ha-c-chain-pattern-itself-p svex)
                                            (ha-c-chain-pattern-itself-body
                                             svex
                                             (list (make-pattern-fn-call
                                                    :fn 'ha-c-chain
                                                    :rule nil
                                                    :args (acl2::merge-sort-lexorder (list x y)))))))
                               :warrant-hyps ((apply$-warrant-ha-c-chain))))

(defsection ha+1-c-chain
  (define ha+1-c-chain  (x y)
    :verify-guards nil
    (sv::4vec-bitor x y)
    ///
    (defwarrant-rp ha+1-c-chain)

    (def-rp-rule ha+1-c-chain-c-spec
      (implies (and (integerp x)
                    (integerp y))
               (equal (ha+1-c-chain  x y)
                      (svl::4vec-concat$ 1
                                         (c-spec (list (logcar x) (logcar y) 1))
                                         (ha+1-c-chain (logcdr x) (logcdr y)))))
      :hints (("goal"
               :in-theory (e/d* (bitops::ihsext-inductions bitops::ihsext-recursive-redefs)
                                ())))))

  (defconst *ha+1-c-chain-rule*
    (hons-copy '(member-equal 'ha+1-s-chain found-patterns)))

  (create-look-for-pattern-fnc :name ha+1-c-chain-pattern
                               :prepwork ((create-case-match-macro ha+1-c-chain-pattern
                                                                   ('sv::bitor x y))
                                          (local
                                           (in-theory (enable ha+1-c-chain))))
                               :body
                               (cond ((ha+1-c-chain-pattern-p svex)
                                      (ha+1-c-chain-pattern-body
                                       svex
                                       (b* ((args (acl2::merge-sort-lexorder (list x y))))
                                         (list (make-pattern-fn-call
                                                :fn 'ha+1-c-chain
                                                :rule *ha+1-c-chain-rule*
                                                :args args))))))
                               :warrant-hyps ((apply$-warrant-ha+1-c-chain))))

(defsection ha+1-c-chain
  (define ha+1-s-chain (method x y)
    :verify-guards nil
    (cond ((= method 0)
           (sv::4vec-bitnot (sv::4vec-bitxor x y)))
          (t
           (sv::4vec-bitxor 1 (sv::4vec-bitxor x y))))
    ///
    (defwarrant-rp ha+1-s-chain)

    (def-rp-rule :disabled-for-acl2 t
      ha+1-s-chain-to-s-spec
      (implies (and (integerp x)
                    (integerp y))
               (equal (ha+1-s-chain method x y)
                      (if (equal method 0)
                          (svl::4vec-concat$
                           1 (s-spec (list (logcar x) (logcar y) 1))
                           (ha+1-s-chain method (logcdr x) (logcdr y)))
                        (svl::4vec-concat$
                         1
                         (s-spec (list (logcar x) (logcar y) 1))
                         (ha-s-chain (svl::4vec-rsh 1  x)
                                     (svl::4vec-rsh 1  y))))))
      :hints (("Goal"
               :in-theory (e/d* (sv::4vec
                                 ha-s-chain
                                 bitops::ihsext-recursive-redefs
                                 sv::4vec-bitxor
                                 SV::4VEC->LOWER
                                 SV::4VEC->UPPER
                                 SV::4VEC-RSH
                                 sv::4VEC-SHIFT-CORE
                                 svl::Bits
                                 SV::4VEC-PART-SELECT
                                 SV::4VEC-CONCAT)
                                (floor
                                 SVL::EQUAL-OF-4VEC-CONCAT-WITH-SIZE=1
                                 logand
                                 ))))))

  (defconst *ha+1-s-chain-rule*
    (hons-copy '(member-equal 'ha+1-c-chain found-patterns)))

  (create-look-for-pattern-fnc :name ha+1-s-chain-pattern
                               :prepwork ((define look-for-ha+1-s-chain-pattern-aux (x y z)
                                            :returns (mv x y valid)
                                            :enabled t
                                            (cond ((equal x 1)
                                                   (mv y z t))
                                                  ((equal y 1)
                                                   (mv x z t))
                                                  ((equal z 1)
                                                   (mv x y t))
                                                  (t (mv 0 0 nil))))

                                          (create-case-match-macro ha+1-s-chain-pattern-1
                                                                   ('sv::bitnot ('sv::bitxor x y)))
                                          (create-case-match-macro ha+1-s-chain-pattern-2
                                                                   ('sv::bitxor ('sv::bitxor x y) z))
                                          (create-case-match-macro ha+1-s-chain-pattern-3
                                                                   ('sv::bitxor z ('sv::bitxor x y)))

                                          (local
                                           (in-theory (enable ha+1-s-chain))))
                               :body
                               (append (and (ha+1-s-chain-pattern-1-p svex)
                                            (ha+1-s-chain-pattern-1-body
                                             svex
                                             (b* ((args (acl2::merge-sort-lexorder (list x y))))
                                               (list (make-pattern-fn-call
                                                      :fn 'ha+1-s-chain
                                                      :rule *ha+1-s-chain-rule*
                                                      :extra-arg 0
                                                      :args args)))))
                                       (and (ha+1-s-chain-pattern-2-p svex)
                                            (ha+1-s-chain-pattern-2-body
                                             svex
                                             (b* (((mv x y valid) (look-for-ha+1-s-chain-pattern-aux x y z))
                                                  ((unless valid) nil)
                                                  (args (acl2::merge-sort-lexorder (list x y))))
                                               (list (make-pattern-fn-call
                                                      :rule *ha+1-s-chain-rule*
                                                      :fn 'ha+1-s-chain
                                                      :extra-arg 1
                                                      :args args)))))
                                       (and (ha+1-s-chain-pattern-3-p svex)
                                            (ha+1-s-chain-pattern-3-body
                                             svex
                                             (b* (((mv x y valid) (look-for-ha+1-s-chain-pattern-aux x y z))
                                                  ((unless valid) nil)
                                                  (args (acl2::merge-sort-lexorder (list x y))))
                                               (list (make-pattern-fn-call
                                                      :fn 'ha+1-s-chain
                                                      :extra-arg 1
                                                      :rule *ha+1-s-chain-rule*
                                                      :args args))))))

                               :warrant-hyps ((apply$-warrant-ha+1-s-chain))))

(progn
  (defun warrants-for-adder-pattern-match ()
    (and (apply$-warrant-ha-c-chain)
         (apply$-warrant-fa-c-chain)
         (apply$-warrant-ha+1-c-chain)
         (apply$-warrant-ha+1-s-chain)
         (apply$-warrant-ha-s-chain)
         (apply$-warrant-fa-s-chain)))

  (defconst *adder-fncs*
    '(ha-c-chain
      fa-c-chain
      ha+1-c-chain
      ha+1-s-chain
      ha-s-chain
      fa-s-chain))

  (rp::add-rp-rule warrants-for-adder-pattern-match)
  (rp::disable-rules '((:e warrants-for-adder-pattern-match))))

;; this is a better rule, works more quickly...
(def-rp-rule fa/ha-chain-fncs-when-bitp
  (and (implies (and (bitp x)
                     (bitp y)
                     (bitp z))
                (and (equal (fa-c-chain method x y z)
                            (c-spec (list x y z)))
                     (equal (fa-s-chain x y z)
                            (s-spec (list x y z)))))
       (implies (and (bitp x)
                     (bitp y))
                (and (equal (ha-c-chain x y)
                            (c-spec (list x y)))
                     (equal (ha-s-chain x y)
                            (s-spec (list x y)))
                     (equal (ha+1-c-chain x y)
                            (c-spec (list x y 1)))
                     (equal (ha+1-s-chain 1 x y)
                            (s-spec (list x y 1))))))
  :hints (("goal"
           :in-theory (e/d (fa-c-chain
                            ha-c-chain
                            ha+1-c-chain ;
                            bitp)
                           (fa-c-chain-c-spec)))))

(define adder-pattern-match ((svex sv::svex-p)
                             (pass-num natp))
  ;; returns list of matching key/pattern-name pairs
  ;; key is the arguments of the fn symbol to replace
  ;; pattern-name is the target fn symbol
  :returns (res pattern-fn-call-list-p
                :hyp (sv::svex-p svex))
  (cond
   ((equal pass-num 1)
    (append
     (look-for-fa-s-chain-pattern svex)
     (look-for-fa-c-chain-pattern svex)
     ))
   (t
    (append
     (look-for-ha-s-chain-pattern svex)
     (look-for-ha-c-chain-pattern svex)

     (look-for-ha+1-c-chain-pattern svex)
     (look-for-ha+1-s-chain-pattern svex)
     )))
  ///
  (defret <fn>-good-measure
    (implies (sv::Svex-p svex)
             (pattern-fn-call-list-provide-good-measure-p svex res)))
  (defret <fn>-correct-pattern
    (implies (and (force (warrants-for-adder-pattern-match))
                  (pattern-fn-call->rule pattern)
                  (member-equal pattern res))
             (equal (sv::svex-eval$ (pattern-call pattern) env)
                    (sv::svex-eval$ svex env)))
    :hints (("Goal"
             :in-theory (e/d () (pattern-call))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(progn
  (def-formula-checks-default-evl
    rp-evl
    (list* 'apply$ 'badge-userfn 'apply$-userfn
           (strip-cars rp::*small-evl-fncs*)))

  (with-output
    :off :all :on (error comment)
    :gag-mode nil
    (rp::def-formula-checks
      find-adders-in-svex-formula-checks-small
      (binary-or binary-? binary-not binary-xor binary-and s-spec c-spec)
      :warranted-fns
      (ha-c-chain
       ha-s-chain
       fa-c-chain
       fa-s-chain
       ha+1-c-chain
       ha+1-s-chain)))

  (defun find-adders-in-svex-formula-checks (state)
    (declare (xargs :stobjs (state)))
    (and (find-adders-in-svex-formula-checks-small state)
         (svl::svex-ev-wog-formula-checks state) ;; using this here to save
         ;; certification time instead of adding all those svex-eval functions.
         ))
  )

(svl::create-width-of-svex-extn :fn ha-s-chain
                                :formula #!SVL(safe-max (nth '0 widths)
                                                        (nth '1 widths)))

(svl::create-width-of-svex-extn :fn ha-c-chain
                                :formula #!SVL(safe-min (nth '0 widths)
                                                        (nth '1 widths)))

(svl::create-width-of-svex-extn :fn ha+1-c-chain
                                :formula #!SVL(safe-max (nth '0 widths)
                                                        (nth '1 widths)))

(svl::create-width-of-svex-extn :fn fa-s-chain
                                :formula #!SVL(safe-max
                                               (safe-max (nth '0 widths)
                                                         (nth '1 widths))
                                               (nth '2 widths))
                                :prepwork
                                ((local
                                  (in-theory (e/d (svl::4vec-correct-width-p
                                                   svl::4vec-part-select-of-4vec-bitxor-better)
                                                  ())))))

(svl::create-width-of-svex-extn :fn ha+1-s-chain
                                :formula #!SVL(if (equal (nth '0 args) '1)
                                                  (if (equal (nth '1 widths)'1)
                                                      (if (equal (nth '2 widths)'1)
                                                          '1
                                                        'nil)
                                                    'nil)
                                                'nil)
                                :prepwork
                                ((local
                                  (in-theory (e/d (svl::4vec-correct-width-p
                                                   svl::4vec-part-select-of-4vec-bitxor-better)
                                                  ())))))

(svl::create-width-of-svex-extn :fn fa-c-chain
                                ;; This is overconservative but I expect
                                ;; everything to be width=1, so it shouldn't matter.
                                :formula #!SVL(safe-max (nth '3 widths)
                                                        (safe-max (nth '1 widths)
                                                                  (nth '2 widths)))
                                #|(if (equal (nth '0 args) '3)

                                (safe-max
                                (safe-max (nth '1 widths)
                                (nth '2 widths))
                                (safe-max (nth '3 widths)
                                (safe-max (nth '1 widths)
                                (nth '2 widths))))
                                'nil)|#
                                :prepwork
                                ((local
                                  (in-theory (e/d (svl::4vec-correct-width-p
                                                   svl::4vec-part-select-of-4vec-bitand-better
                                                   svl::4vec-part-select-of-4vec-bitor-better
                                                   svl::4vec-part-select-of-4vec-bitxor-better)
                                                  ((:definition sv::svex-kind$inline)
                                                   (:rewrite acl2::symbolp-of-car-when-symbol-listp)
                                                   (:definition symbol-listp)
                                                   (:definition acl2::apply$-badgep)
                                                   (:rewrite acl2::integerp-of-car-when-integer-listp)
                                                   (:definition integer-listp)
                                                   (:rewrite acl2::symbol-listp-of-cdr-when-symbol-listp)
                                                   (:rewrite acl2::natp-of-car-when-nat-listp)
                                                   (:rewrite sv::svex-eval$-when-quote)
                                                   (:definition nat-listp)
                                                   (:rewrite sv::svex-eval$-when-fncall)
                                                   (:rewrite sv::4vec-bitops-to-logops)
                                                   (:rewrite svl::svex-eval$-of-integerp-of-svex-is-correct-env=nil)
                                                   (:rewrite sv::svex-p-of-car-when-svexlist-p)
                                                   (:rewrite sv::svex-eval$-when-fncall)
                                                   (:rewrite svl::integerp-of-4vec-part-selectr)
                                                   (:type-prescription sv::4vec-bitand)
                                                   (:rewrite svl::integerp-4vec-bitand)
                                                   (:rewrite sv::svex-eval$-is-svex-eval)
                                                   (:rewrite acl2::apply$-badgep-properties . 2)
                                                   (:rewrite default-cdr)
                                                   (:rewrite acl2::integer-listp-of-cdr-when-integer-listp)
                                                   ))))))

(svl::create-integerp-of-svex-extn :fn ha-s-chain
                                   :prepwork
                                   ((local
                                     (in-theory (disable
                                                 ha-s-chain-to-s-spec)))))

(svl::create-integerp-of-svex-extn :fn ha-c-chain
                                   :prepwork
                                   ((local
                                     (in-theory (disable
                                                 ha-c-chain-to-c-spec)))))

(svl::create-integerp-of-svex-extn :fn fa-c-chain)

(svl::create-integerp-of-svex-extn :fn fa-s-chain
                                   :prepwork
                                   ((local
                                     (in-theory (disable
                                                 fa-s-chain-s-spec)))))

(svl::create-integerp-of-svex-extn :fn ha+1-c-chain
                                   :prepwork
                                   ((local
                                     (in-theory (disable
                                                 ha+1-c-chain-c-spec)))))

(svl::create-integerp-of-svex-extn :fn ha+1-s-chain
                                   :prepwork
                                   ((local
                                     (in-theory (disable
                                                 ha+1-s-chain-to-s-spec)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; 1. Gather applicable patterns and create a "pattern-alist"

(acl2::defines gather-adder-patterns-in-svex
  :prepwork
  ((define register-found-adder-patterns ((pattern-fn-call-list pattern-fn-call-list-p)
                                          (pattern-alist))
     :returns (res pattern-alist-p :hyp (pattern-alist-p pattern-alist))
     :inline t
     ;; when a matching pattern  is found, it should be saved  in a fast-alist whose
     ;; keys are arguments, and value should be a list of all the pattern names.
     (b* (((when (atom pattern-fn-call-list)) pattern-alist)
          ((pattern-fn-call x) (car pattern-fn-call-list))

          ;;((unless (and key value)) pattern-alist)
          (entry (hons-get x.args pattern-alist))
          (pattern-alist (hons-acons x.args (cons x.fn (cdr entry)) pattern-alist)))
       (register-found-adder-patterns (cdr pattern-fn-call-list)
                                      pattern-alist))
     ///
     (defret alistp-of-<fn>
       (implies (alistp pattern-alist)
                (alistp res)))))

  (define gather-adder-patterns-in-svex ((x sv::svex-p)
                                         (pattern-alist )
                                         (parsed-svexes)
                                         (pass-num natp))
    :measure (sv::svex-count x)
    :returns (mv (res-pattern-alist pattern-alist-p :hyp (pattern-alist-p pattern-alist))
                 res-parsed-svexes)
    (sv::svex-case
     x
     :quote (mv pattern-alist parsed-svexes)
     :var   (mv pattern-alist parsed-svexes)
     :call (b* ((already-parsed (hons-get x parsed-svexes))
                ((when already-parsed) (mv pattern-alist parsed-svexes))
                (parsed-svexes (hons-acons x nil parsed-svexes))
                (matching-pattern-fn-call-list (adder-pattern-match x pass-num))
                (pattern-alist
                 (register-found-adder-patterns matching-pattern-fn-call-list  pattern-alist)))
             (gather-adder-patterns-in-svexlist x.args pattern-alist
                                                parsed-svexes pass-num))))

  (define gather-adder-patterns-in-svexlist ((lst sv::svexlist-p)
                                             (pattern-alist )
                                             (parsed-svexes)
                                             (pass-num natp))
    :returns (mv (res-pattern-alist pattern-alist-p :hyp (pattern-alist-p pattern-alist))
                 res-parsed-svexes)
    :measure (sv::svexlist-count lst)
    (if (atom lst)
        (mv pattern-alist parsed-svexes)
      (b* (((mv pattern-alist parsed-svexes)
            (gather-adder-patterns-in-svex (car lst) pattern-alist
                                           parsed-svexes pass-num))
           ((mv pattern-alist parsed-svexes)
            (gather-adder-patterns-in-svexlist (cdr lst) pattern-alist
                                               parsed-svexes pass-num)))
        (mv pattern-alist parsed-svexes))))
  ///
  (defret-mutual alistp-of-<fn>
    (defret alistp-of-<fn>
      (implies (alistp pattern-alist)
               (alistp res-pattern-alist))
      :fn gather-adder-patterns-in-svex)
    (defret alistp-of-<fn>
      (implies (alistp pattern-alist)
               (alistp res-pattern-alist))
      :fn gather-adder-patterns-in-svexlist)
    :hints (("Goal"
             :expand ((gather-adder-patterns-in-svexlist
                       lst
                       pattern-alist parsed-svexes pass-num)
                      (gather-adder-patterns-in-svex nil
                                                     pattern-alist parsed-svexes pass-num)
                      (gather-adder-patterns-in-svex x
                                                     pattern-alist parsed-svexes pass-num))

             :in-theory (e/d () ())))))

(define gather-adder-patterns-in-svex-alist ((alist sv::svex-alist-p)
                                             (pattern-alist )
                                             (parsed-svexes)
                                             (pass-num natp))
  :returns (mv (res-pattern-alist pattern-alist-p :hyp (pattern-alist-p pattern-alist))
               res-parsed-svexes)
  (if (atom alist)
      (mv pattern-alist parsed-svexes)
    (b* (((mv pattern-alist parsed-svexes)
          (gather-adder-patterns-in-svex (cdar alist) pattern-alist
                                         parsed-svexes
                                         pass-num))
         ((mv pattern-alist parsed-svexes)
          (gather-adder-patterns-in-svex-alist (cdr alist) pattern-alist
                                               parsed-svexes
                                               pass-num)))
      (mv pattern-alist parsed-svexes)))
  ///
  (defret alistp-of-<fn>
    (implies (alistp pattern-alist)
             (alistp res-pattern-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Apply patterns if their rule is satisfied (usually this means their
;; counterpart pattern is found for the same arguments.

(defines run-pattern-rule
  :prepwork
  ((define andlst (lst)
     (if (atom lst)
         t
       (and (car lst)
            (andlst (cdr lst)))))
   (define orlst (lst)
     (if (atom lst)
         nil
       (or (car lst)
           (orlst (cdr lst))))))
  (define run-pattern-rule ((rule pseudo-termp)
                            (found-patterns))
    (cond ((atom rule)
           (cond ((equal rule 'found-patterns)
                  found-patterns)
                 ((booleanp rule)
                  rule)
                 (t
                  (acl2::raise "Unknown atom in rule pattern is given to run-pattern-rule: ~p0. It
                          may need improvement.. ~%" rule))))
          ((and (quotep rule)
                (consp (cdr rule)))
           (unquote rule))
          ((and (equal (car rule) 'member-equal)
                (equal (len (cdr rule)) 2))
           (ec-call
            (member-equal (run-pattern-rule (second rule) found-patterns)
                          (run-pattern-rule (third rule) found-patterns))))
          ((equal (car rule) 'and)
           (andlst (run-pattern-rule-lst (cdr rule) found-patterns)))
          ((equal (car rule) 'or)
           (orlst (run-pattern-rule-lst (cdr rule) found-patterns))))
    )
  (define run-pattern-rule-lst ((lst pseudo-term-listp)
                                (found-patterns))
    (if (atom lst)
        nil
      (cons (run-pattern-rule (car lst) found-patterns)
            (run-pattern-rule-lst (cdr lst) found-patterns)))))

(define pull-the-first-applicable-adder-pattern ((pattern-alist)
                                                 (pattern-fn-call-list pattern-fn-call-list-p))
  :prepwork ((in-theory (e/d ()
                             (assoc-equal
                              (:e tau-system)))))
  :returns (pattern-fn-call (implies pattern-fn-call
                                     (pattern-fn-call-p pattern-fn-call))
                            :hyp (pattern-fn-call-list-p pattern-fn-call-list))
  (if (atom pattern-fn-call-list)
      nil
    (b* (((pattern-fn-call x) (car pattern-fn-call-list))

         (found-patterns (cdr (hons-get x.args pattern-alist)))
         (should-rewrite (and x.rule (run-pattern-rule x.rule found-patterns)))
         ((when should-rewrite)
          (car pattern-fn-call-list)))
      (pull-the-first-applicable-adder-pattern pattern-alist
                                               (cdr pattern-fn-call-list))))
  ///

  (defret <fn>-returns-a-member-of-pattern-fn-call-list
    (implies pattern-fn-call
             (and (member-equal pattern-fn-call pattern-fn-call-list)
                  (pattern-fn-call->rule pattern-fn-call)))))

(local
 (defthm replace-adder-patterns-in-svex-measure-lemma
   (implies
    (and (pull-the-first-applicable-adder-pattern
          pattern-alist
          (adder-pattern-match (sv::svex-fix x) pass-num)))
    (<
     (sv::svexlist-count
      (pattern-fn-call->args (pull-the-first-applicable-adder-pattern
                              pattern-alist
                              (adder-pattern-match (sv::svex-fix x) pass-num))))
     (sv::svex-count x)))
   :hints (("Goal"
            :use ((:instance
                   pattern-fn-call-list-provide-good-measure-p-and-member
                   (x (sv::svex-fix x))
                   (lst (adder-pattern-match (sv::svex-fix x) pass-num))
                   (e (pull-the-first-applicable-adder-pattern
                       pattern-alist
                       (adder-pattern-match (sv::svex-fix x) pass-num))))

                  (:instance adder-pattern-match-good-measure
                             (svex (sv::svex-fix x))))
            :in-theory (e/d (pattern-fn-call-provide-good-measure-p)
                            (pattern-fn-call-list-provide-good-measure-p-and-member
                             adder-pattern-match-good-measure))))))

(acl2::defines replace-adder-patterns-in-svex

  :flag-local nil

  :prepwork ((local
              (in-theory (e/d ()
                              (pattern-fn-call->args)))))

  (define replace-adder-patterns-in-svex ((x sv::Svex-p)
                                          (pattern-alist)
                                          (pass-num natp))
    :measure (sv::svex-count x)
    :returns res
    :verify-guards nil
    (sv::svex-case
     x
     :quote x
     :var   x
     :call
     (b* ((x (sv::svex-fix x))
          (pattern-fn-call-list (adder-pattern-match x pass-num))
          (pattern-fn-call (pull-the-first-applicable-adder-pattern
                            pattern-alist pattern-fn-call-list)))
       (cond
        (pattern-fn-call
         (b* (((pattern-fn-call x) pattern-fn-call))
           (pattern-call x
                         (replace-adder-patterns-in-svexlist x.args
                                                             pattern-alist
                                                             pass-num))))
        (t
         (sv::svex-call x.fn
                        (replace-adder-patterns-in-svexlist x.args
                                                            pattern-alist pass-num)))))))

  (define replace-adder-patterns-in-svexlist ((lst sv::svexlist-p)
                                              (pattern-alist)
                                              ;;(parsed-svexes)
                                              (pass-num natp)
                                              )
    :returns res
    :measure (sv::svexlist-count lst)
    (if (atom lst)
        nil
      (hons (replace-adder-patterns-in-svex (car lst) pattern-alist pass-num)
            (replace-adder-patterns-in-svexlist (cdr lst) pattern-alist pass-num))))

  ///

  (defthm svex-p-pattern-call
    (implies (and (pattern-fn-call-p x)
                  (or (not optional-args)
                      (sv::svexlist-p optional-args)))
             (sv::svex-p (PATTERN-CALL x optional-args)))
    :hints (("Goal"
             :in-theory (e/d (PATTERN-CALL
                              SV::SVEX-P
                              PATTERN-FN-CALL->FN
                              PATTERN-FN-CALL-P)
                             ()))))

  (defret-mutual svex-p-of-<fn>
    (defret svex-p-of-<fn>
      (implies (sv::Svex-p x)
               (sv::Svex-p res))
      :fn replace-adder-patterns-in-svex)
    (defret Svexlist-p-of-<fn>
      (implies (sv::Svexlist-p lst)
               (sv::Svexlist-p res))
      :fn replace-adder-patterns-in-svexlist))

  (verify-guards replace-adder-patterns-in-svex)

  (memoize 'replace-adder-patterns-in-svex :condition '(eq (sv::svex-kind x) :call))

  (defret-mutual replace-adder-patterns-in-svex-is-correct
    (defret <fn>-is-correct
      (implies (and (force (sv::svex-p x))
                    (force (warrants-for-adder-pattern-match)))
               (equal (sv::svex-eval$ res env)
                      (sv::svex-eval$ x env)))
      :fn replace-adder-patterns-in-svex)
    (defret <fn>-is-correct
      (implies (and (force (sv::Svexlist-p lst))
                    (force (warrants-for-adder-pattern-match)))
               (equal (sv::svexlist-eval$ res env)
                      (sv::svexlist-eval$ lst env)))
      :fn replace-adder-patterns-in-svexlist)
    :hints (("Goal"
             :do-not-induct t
             :expand ((REPLACE-ADDER-PATTERNS-IN-SVEX X PATTERN-ALIST pass-num)
                      (REPLACE-ADDER-PATTERNS-IN-SVEXLIST LST PATTERN-ALIST pass-num)
                      (:free (cons x y)
                             (sv::Svex-eval$ (cons x y) env)))
             :in-theory (e/d (SV::SVEX-EVAL$
                              SV::SVEXlist-EVAL$
                              SV::FNSYM-FIX
                              sv::svex-kind
                              SV::SVEX-P
                              PATTERN-CALL
                              SV::SVEX-CALL->ARGS
                              SV::SVEX-CALL->fn
                              )
                             (adder-pattern-match-correct-pattern)))
            (and STABLE-UNDER-SIMPLIFICATIONP
                 '(:use ((:instance
                          adder-pattern-match-correct-pattern
                          (pattern (PULL-THE-FIRST-APPLICABLE-ADDER-PATTERN
                                    PATTERN-ALIST (ADDER-PATTERN-MATCH X pass-num)))
                          (svex x))))
                 ))))

(define replace-adder-patterns-in-svex-alist ((alist sv::svex-alist-p)
                                              (pattern-alist)
                                              (pass-num natp))
  :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p alist))
  (if (atom alist)
      nil
    (acons (caar alist)
           (replace-adder-patterns-in-svex (cdar alist) pattern-alist pass-num)
           (replace-adder-patterns-in-svex-alist (cdr alist) pattern-alist pass-num)))
  ///
  (defret <fn>-is-correct
    (implies (and (force (sv::Svex-alist-p alist))
                  (force (warrants-for-adder-pattern-match)))
             (equal (sv::svex-alist-eval$ res env)
                    (sv::svex-alist-eval$ alist env)))
    :fn replace-adder-patterns-in-svex-alist
    :hints (("Goal"
             :in-theory (e/d (SV::SVEX-ALIST-EVAL$) ())))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Now on to careful search after initial replacements to see if any patterns
;; are missed.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection fix-order-of-fa/ha-s-args
  ;; After replacements,  ordered-ness of  arguments might change,  which might
  ;; prevent patterns  from being found  when looking more carefully.   So This
  ;; function goes around and reorders arguments in fa-s and ha-s arguments.
  (defines fix-order-of-fa/ha-s-args
    :verify-guards nil
    (define fix-order-of-fa/ha-s-args ((x sv::svex-p))
      :measure (sv::svex-count x)
      :returns (res sv::svex-p :hyp (sv::svex-p x))
      (sv::svex-case
       x
       :var x
       :quote x
       :call (case-match x
               (('fa-s-chain & & &)
                (b* ((lst1 (fix-order-of-fa/ha-s-args-list x.args))
                     (lst2 (acl2::merge-sort-lexorder lst1)))
                  (sv::svex-call x.fn lst2)))
               (('ha-s-chain & &)
                (b* ((lst1 (fix-order-of-fa/ha-s-args-list x.args))
                     (lst2 (acl2::merge-sort-lexorder lst1)))
                  (sv::svex-call x.fn lst2)))
               (& (sv::svex-call
                   x.fn
                   (fix-order-of-fa/ha-s-args-list x.args))))))
    (define fix-order-of-fa/ha-s-args-list ((lst sv::svexlist-p))
      :measure (sv::svexlist-count lst)
      :returns (res sv::svexlist-p :hyp (sv::svexlist-p lst))
      (if (atom lst)
          nil
        (hons (fix-order-of-fa/ha-s-args (car lst))
              (fix-order-of-fa/ha-s-args-list (cdr lst)))))

    ///

    (local
     (defthm svexlist-p-implies-true-listp
       (implies (sv::svexlist-p lst)
                (true-listp lst))))

    (verify-guards fix-order-of-fa/ha-s-args)

    (memoize 'fix-order-of-fa/ha-s-args
             :condition '(eq (sv::svex-kind x) :call))

    (defret-mutual <fn>-is-correct
      (defret <fn>-is-correct
        (implies (and (warrants-for-adder-pattern-match)
                      (sv::svex-p x))
                 (equal (sv::svex-eval$ res env)
                        (sv::svex-eval$ x env)))
        :fn fix-order-of-fa/ha-s-args)
      (defret <fn>-is-correct
        (implies (and (warrants-for-adder-pattern-match)
                      (sv::svexlist-p lst))
                 (equal (sv::svexlist-eval$ res env)
                        (sv::svexlist-eval$ lst env)))
        :fn fix-order-of-fa/ha-s-args-list)
      :hints (("Goal"

               :expand ((:free (args)
                               (sv::svex-apply$ 'ha-s-chain args))
                        (:free (args)
                               (sv::svex-apply$ 'fa-s-chain args))
                        (acl2::merge-sort-lexorder (cdr x))
                        (fix-order-of-fa/ha-s-args-list lst)
                        (fix-order-of-fa/ha-s-args x))
               :in-theory (e/d (acl2::merge-lexorder
                                acl2::merge-sort-lexorder
                                ha-s-chain
                                fa-s-chain
                                sv::svex-call->fn
                                sv::svex-call->args)
                               ())))))

  (define fix-order-of-fa/ha-s-args-alist ((alist sv::svex-alist-p))
    :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p alist))
    (if (atom alist)
        nil
      (acons (caar alist)
             (fix-order-of-fa/ha-s-args (cdar alist))
             (fix-order-of-fa/ha-s-args-alist (cdr alist))))
    ///
    (defret <fn>-is-correct
      (implies (and (warrants-for-adder-pattern-match)
                    (sv::svex-alist-p alist))
               (equal (sv::svex-alist-eval$ res env)
                      (sv::svex-alist-eval$ alist env)))
      :fn fix-order-of-fa/ha-s-args-alist
      :hints (("Goal"
               :in-theory (e/d (SV::SVEX-ALIST-EVAL$) ()))))))

(defsection process-fa/ha-c-chain-pattern-args
  ;; Goal here is  to take a pattern-alist, and create  another fast-alist that
  ;; can be  used to find missed  fa-s/ha-s patterns. If  one of the args  of a
  ;; found fa-c/ha-c is  a bitxor, these function also  "explode" that argument
  ;; for a  more comprehensive  search.  Since  xor chains  can be  large, this
  ;; explosion     is    done     with     a    depth     limit    given     in
  ;; *process-fa/ha-c-chain-pattern-args-limit*.

  (define collected-fa/ha-c-chain-pattern-args-p (x)
    :enabled t
    (if (atom x)
        (equal x nil)
      (and (consp (car x))
           (consp (cdar x))
           (sv::svex-p (caar x)) ;; (caar x) has one of the exploded args
           (sv::Svexlist-p (car (cdar x))) ;; list of exploded args
           (sv::Svexlist-p (cdr (cdar x))) ;; list of args as is.
           (collected-fa/ha-c-chain-pattern-args-p (cdr x))))
    ///
    (defthm an-entry-of-collected-fa/ha-c-chain-pattern-args-p
      (implies (and (hons-assoc-equal key alist)
                    (collected-fa/ha-c-chain-pattern-args-p alist))

               (and (consp (hons-assoc-equal key alist))
                    (consp (cdr (hons-assoc-equal key alist)))
                    (sv::svex-p (car (hons-assoc-equal key alist)))
                    ;; (caar x) has one of the exploded args
                    (sv::Svexlist-p (car (cdr (hons-assoc-equal key alist)))) ;; list of exploded args
                    (sv::Svexlist-p (cdr (cdr (hons-assoc-equal key alist)))) ;; list of args as is.
                    )))

    (defthmd an-entry-of-collected-fa/ha-c-chain-pattern-args-p-2
      (implies (and (collected-fa/ha-c-chain-pattern-args-p alist)
                    (force (member-equal entry alist)))
               (and (consp entry)
                    (consp (cdr entry))
                    ;; (caar x) has one of the exploded args
                    (sv::svex-p (car entry))
                    (sv::Svexlist-p (car (cdr entry))) ;; list of exploded args
                    (sv::Svexlist-p (cdr (cdr entry))) ;; list of args as is.
                    ))))

  (define collected-fa/ha-c-chain-pattern-args-inv (x env)
    :verify-guards nil
    (or (atom x)
        (and (equal (svl::svex-eval$-bitxor-lst (car (cdar x)) env)
                    (svl::svex-eval$-bitxor-lst (cdr (cdar x)) env))
             (collected-fa/ha-c-chain-pattern-args-inv (cdr x) env)))
    ///
    (defthm collected-fa/ha-c-chain-pattern-args-inv-hons-assoc-equal
      (implies (and (collected-fa/ha-c-chain-pattern-args-inv collected-args-alist env)
                    (hons-assoc-equal key collected-args-alist))
               (equal (svl::svex-eval$-bitxor-lst (car (cdr (hons-assoc-equal key collected-args-alist))) env)
                      (svl::svex-eval$-bitxor-lst (cdr (cdr (hons-assoc-equal key collected-args-alist))) env)))))

  (defconst *process-fa/ha-c-chain-pattern-args-limit*
    3)

  (define process-fa/ha-c-chain-pattern-args-aux ((args))
    :prepwork
    ((local
      (defret consp-of-<fn>
        (consp svl::leaves)
        :fn svl::bitand/or/xor-collect-leaves2
        :hints (("Goal"
                 :in-theory (e/d (svl::bitand/or/xor-collect-leaves2) ()))))))

    :returns (mv (keys sv::svexlist-p :hyp (sv::Svexlist-p args))
                 (exploded-args sv::svexlist-p :hyp (sv::Svexlist-p args)))
    (if (atom args)
        (mv nil nil)
      (b* (((mv rest-keys exploded-args)
            (process-fa/ha-c-chain-pattern-args-aux (cdr args)))
           ((mv leaves &)
            (svl::bitand/or/xor-collect-leaves2 (car args)
                                                'sv::bitxor
                                                *process-fa/ha-c-chain-pattern-args-limit*)))
        (mv (cons (car leaves) rest-keys)
            (append leaves exploded-args))))
    ///
    (defret <fn>-is-correct
      (equal (svl::svex-eval$-bitxor-lst exploded-args env)
             (svl::svex-eval$-bitxor-lst args env))
      :fn process-fa/ha-c-chain-pattern-args-aux))

  (define process-fa/ha-c-chain-pattern-args-aux2 (keys args exploded-args collected)
    :returns (collected-res collected-fa/ha-c-chain-pattern-args-p
                            :hyp (and (collected-fa/ha-c-chain-pattern-args-p collected)
                                      (sv::svexlist-p keys)
                                      (sv::svexlist-p exploded-args)
                                      (sv::svexlist-p args)))
    (if (atom keys)
        collected
      (process-fa/ha-c-chain-pattern-args-aux2 (cdr keys) args
                                               exploded-args
                                               (hons-acons (car keys)
                                                           (cons exploded-args args)
                                                           collected)))
    ///
    (defret <fn>-is-correct
      (implies (and (collected-fa/ha-c-chain-pattern-args-inv collected env)
                    (equal (svl::svex-eval$-bitxor-lst exploded-args env)
                           (svl::svex-eval$-bitxor-lst args env)))
               (collected-fa/ha-c-chain-pattern-args-inv collected-res env))
      :hints (("Goal"
               :in-theory (e/d (collected-fa/ha-c-chain-pattern-args-inv) ())))))

  (define process-fa/ha-c-chain-pattern-args ((pattern-alist pattern-alist-p)
                                              (collected collected-fa/ha-c-chain-pattern-args-p)
                                              &key
                                              ((adder-type symbolp) 'adder-type))
    :returns (collected-res collected-fa/ha-c-chain-pattern-args-p
                            :hyp (and (collected-fa/ha-c-chain-pattern-args-p collected)
                                      (pattern-alist-p pattern-alist)))
    (if (atom pattern-alist)
        collected
      (b* ((fns (cdar pattern-alist))
           ((unless (equal fns (if (eq adder-type 'ha) '(ha-c-chain) '(fa-c-chain))))
            (process-fa/ha-c-chain-pattern-args (cdr pattern-alist)
                                                collected))
           (args (caar pattern-alist))
           ((mv keys exploded-args)
            (process-fa/ha-c-chain-pattern-args-aux args))
           (collected (process-fa/ha-c-chain-pattern-args-aux2
                       keys args exploded-args collected)))
        (process-fa/ha-c-chain-pattern-args (cdr pattern-alist) collected)))
    ///
    (defret <fn>-is-correct
      (implies (collected-fa/ha-c-chain-pattern-args-inv collected env)
               (collected-fa/ha-c-chain-pattern-args-inv collected-res env))))

  ;; I pull an exploded-arg from each  arg to construct the fast-alist. So same
  ;; entry is  repeated 2  (ha) or 3  (fa) times with  different keys.  I don't
  ;; expect this to be necessarry but this  can help the search to move forward
  ;; a bit more quickly. But maybe not..

  ;; (process-fa/ha-c-chain-pattern-args '((((sv::bitxor x Y)
  ;;                                        z (sv::bitxor m k))
  ;;                                        . (fa-c-chain)))
  ;;                                     nil
  ;;                                     :adder-type 'fa)
  ;; returns:
  ;; ((M (X Y Z M K)
  ;;     (SV::BITXOR X Y)
  ;;     Z (SV::BITXOR M K))
  ;;  (Z (X Y Z M K)
  ;;     (SV::BITXOR X Y)
  ;;     Z (SV::BITXOR M K))
  ;;  (X (X Y Z M K)
  ;;     (SV::BITXOR X Y)
  ;;     Z (SV::BITXOR M K)))
  )

(defsection find-s-from-found-c-in-svex-aux-explore
  ;; These functions perform  a "cheap" search to see if  all the exploded args
  ;; appear as an  argument in the bitxor  chain of an svex. AND  it makes sure
  ;; that  exploded args  are  distributed  into two  branches  of the  topmost
  ;; bitxor, which  indicates that we are  ready to shuffle around  the svex to
  ;; reveal the matching ha-s/fa-s pattern

  (Local
   (defthm member-equal-of-hons-assoc-equal
     (implies (hons-assoc-equal x lst)
              (member-equal (hons-assoc-equal x lst)
                            lst))))

  (local
   (defthm sv::svexlist-p-implies-true-listp
     (implies (sv::svexlist-p lst)
              (true-listp lst))))

  (local
   (in-theory (enable an-entry-of-collected-fa/ha-c-chain-pattern-args-p-2)))

  (define find-s-from-found-c-in-svex-aux-explore-aux ((svex)
                                                       (collected-args-alist)
                                                       (skip true-listp))
    :returns (alist-entry (implies alist-entry
                                   (member-equal alist-entry collected-args-alist)))
    (case-match svex
      (('sv::bitxor x y)
       (or (and (not (member-equal x skip))
                (hons-get x collected-args-alist))
           (and (not (member-equal y skip))
                (hons-get y collected-args-alist))
           (find-s-from-found-c-in-svex-aux-explore-aux x collected-args-alist skip)
           (find-s-from-found-c-in-svex-aux-explore-aux y collected-args-alist skip)))
      (& nil))
    ///
    (defret return-val-of-<fn>
      (implies (and alist-entry
                    (collected-fa/ha-c-chain-pattern-args-p collected-args-alist))

               (and (consp alist-entry)
                    (consp (cdr alist-entry))
                    ;; (caar x) has one of the exploded args
                    (true-listp (car (cdr alist-entry))) ;; list of exploded args
                    (true-listp (cdr (cdr alist-entry))) ;; list of args as is.
                    ))
      :hints (("Goal"
               :in-theory (e/d () (true-listp hons-assoc-equal)))))
    (defret <fn>-is-correct
      (implies (and (collected-fa/ha-c-chain-pattern-args-inv collected-args-alist env)
                    alist-entry)
               (equal (svl::svex-eval$-bitxor-lst (car (cdr alist-entry)) env)
                      (svl::svex-eval$-bitxor-lst (cdr (cdr alist-entry)) env)))))

  (define find-s-from-found-c-in-svex-aux-arg-exists-p ((svex)
                                                        (arg))
    :returns exists
    (or (hons-equal svex arg)
        (case-match svex
          (('sv::bitxor x y)
           (or (find-s-from-found-c-in-svex-aux-arg-exists-p x arg)
               (find-s-from-found-c-in-svex-aux-arg-exists-p y arg)))
          (& nil)))
    )

  ;; When this function returns 3, then it means the exploded-args appear in both
  ;; branches of the svex. It will indicate that rewriting the svex at this point
  ;; is a good idea.
  (define find-s-from-found-c-in-svex-aux-explore2 ((svex)
                                                    (exploded-args))
    :returns (exist-branch (and (acl2::maybe-natp exist-branch)
                                (or (not exist-branch)
                                    (equal exist-branch 0)
                                    (equal exist-branch 1)
                                    (equal exist-branch 2)
                                    (equal exist-branch 3))))
    :guard (ha-s-chain-pattern-p svex)
    (if (atom exploded-args)
        0
      (b* ((rest (find-s-from-found-c-in-svex-aux-explore2 svex (cdr exploded-args)))
           ((Unless rest)
            nil)
           (x (cadr svex))
           (exist-in-x (find-s-from-found-c-in-svex-aux-arg-exists-p x (car exploded-args)))
           ((when exist-in-x)
            (logior 1 rest))
           (y (caddr svex))
           (exist-in-y (find-s-from-found-c-in-svex-aux-arg-exists-p y (car exploded-args)))
           ((when exist-in-y)
            (logior 2 rest)))
        nil))
    ///

    )

  ;; This function should return ARGS and EXPLODED-ARGS  that are ready to be applied the svex
  (define find-s-from-found-c-in-svex-aux-explore ((svex)
                                                   (collected-args-alist collected-fa/ha-c-chain-pattern-args-p)
                                                   (skip true-listp)
                                                   &key
                                                   ;; give a large limit for measure. I don't expect this to go too big.
                                                   ((limit natp) '1000))
    :guard (ha-s-chain-pattern-p svex)
    :returns (mv (args sv::svexlist-p :hyp (force (collected-fa/ha-c-chain-pattern-args-p collected-args-alist)))
                 (exploded-args sv::svexlist-p :hyp (force (collected-fa/ha-c-chain-pattern-args-p collected-args-alist))))
    :measure (nfix limit)
    (if (zp limit)
        (mv nil nil)
      (b* (;; find  the first candidate by  looking up only one key.  It is not
           ;; guaranteed for other args to be present.
           (entry (find-s-from-found-c-in-svex-aux-explore-aux svex collected-args-alist skip))
           ((Unless entry)
            (Mv nil nil))
           (key (car entry))
           (args (cddr entry))
           (exploded-ags (cadr entry))
           ;; See if all the exploded-args  are present in svex. Also determine
           ;; if they are dispersed into two branches of bitxor, or if they all
           ;; appear in  only one of  them. If they appear  in only one  of the
           ;; branches,  it means  the same  pattern  can be  applied down  the
           ;; line.  In order  to preserve  the  SVEX'es structure  as much  as
           ;; possible, we avoid applying such matches when it is too early.
           (exist-branch (find-s-from-found-c-in-svex-aux-explore2 svex exploded-ags))
           ;; 3 means all exploded-args exist, and they are dispersed to the two branches.
           ((when (equal exist-branch 3))
            (mv args exploded-ags)))
        ;; if exist-branch is not 3, then keep searching for other matches.
        (find-s-from-found-c-in-svex-aux-explore svex collected-args-alist
                                                 (cons key skip)
                                                 :limit (1- limit))))
    ///
    (defret <fn>-is-correct
      (implies (and (collected-fa/ha-c-chain-pattern-args-inv collected-args-alist env)
                    args)
               (equal (svl::svex-eval$-bitxor-lst args env)
                      (svl::svex-eval$-bitxor-lst exploded-args env)
                      )))))

; Matt K. mod, 2/20/2023: The use of (logbitp-reasoning) makes ACL2(p) with
; waterfall-parallelism enabled complain that "the form (LOGBITP-REASONING) was
; expected to represent an ordinary value, not an error triple (mv erp val
; state), as would be acceptable in a serial execution of ACL2".  So I'll turn
; off waterfall parallelism here.
(local (set-waterfall-parallelism nil))

;; This is to remove everyting in to-remove-lst
;; When remaining-to-remove is nil, then it means everything in to-remove-lst was removed.
(define find-s-from-found-c-in-svex-aux-remove ((svex)
                                                (to-remove-lst))

  :prepwork
  ((define remove-equal-once (x lst)
     :returns (res true-listp :hyp (true-listp lst))
     (cond ((atom lst)
            nil)
           ((equal x (car lst))
            (cdr lst))
           (t (cons-with-hint (car lst)
                              (remove-equal-once x (cdr lst))
                              lst)))
     ///
     (defret svexlist-p-of-<fn>
       (implies (sv::svexlist-p lst)
                (sv::svexlist-p res))))

   (define svex-apply$-for-bitxor-meta (arg1 arg2)
     :returns (res-svex sv::svex-p :hyp (and (force (sv::svex-p arg1))
                                             (force (sv::svex-p arg2))))
     :inline t
     (cond ((equal arg1 0)
            arg2)
           ((equal arg2 0)
            arg1)
           (t (hons-list 'sv::bitxor arg1 arg2)))
     ///
     (defret <fn>-is-correct
       (and (equal (sv::3vec-fix (sv::svex-eval$ res-svex env))
                   (sv::4vec-bitxor (sv::svex-eval$ arg1 env)
                                    (sv::svex-eval$ arg2 env)))
            (equal (sv::4vec-bitxor (sv::svex-eval$ res-svex env) other)
                   (sv::4vec-bitxor (sv::4vec-bitxor (sv::svex-eval$ arg1 env)
                                                     (sv::svex-eval$ arg2 env))
                                    other))
            (equal (sv::4vec-bitxor other (sv::svex-eval$ res-svex env))
                   (sv::4vec-bitxor (sv::4vec-bitxor (sv::svex-eval$ arg1 env)
                                                     (sv::svex-eval$ arg2 env))
                                    other)))
       :hints (("Goal"
                :expand ((:free (args)
                                (sv::svex-apply 'sv::bitxor args)))
                :in-theory (e/d (sv::svex-call->fn
                                 sv::svex-call->args
                                 SV::SVEXLIST-EVAL$)
                                ()))))

     ))

  :returns (mv (res-svex sv::svex-p :hyp (sv::svex-p svex))
               (remaining-to-remove sv::svexlist-p :hyp (sv::svexlist-p to-remove-lst)))
  :verify-guards :after-returns

  (case-match svex
    (('sv::bitxor x y)
     (b* ((remove-x (svl::member-hons-equal x to-remove-lst))
          ((mv x to-remove-lst)
           (if remove-x
               (mv 0 (remove-equal-once x to-remove-lst))
             (find-s-from-found-c-in-svex-aux-remove x to-remove-lst)))
          (remove-y (svl::member-hons-equal y to-remove-lst))
          ((mv y to-remove-lst)
           (if remove-y
               (mv 0 (remove-equal-once y to-remove-lst))
             (find-s-from-found-c-in-svex-aux-remove y to-remove-lst))))
       (mv
        (svex-apply$-for-bitxor-meta x y)
        to-remove-lst)))
    (& (mv svex to-remove-lst)))
  ///
  (local
   (defthm svex-eval$-when-4vec-p
     (implies (sv::4vec-p x)
              (equal (sv::Svex-eval x env)
                     x))
     :hints (("Goal"
              :in-theory (e/d (sv::svex-quote->val sv::Svex-eval sv::4vec-p) ())))))

  (local
   (defthm svex-eval$-bitxor-lst-of-remove-equal
     (implies (member-equal x lst)
              (and (equal (sv::4vec-bitxor (svl::svex-eval$-bitxor-lst (remove-equal-once x lst) env)
                                           (sv::Svex-eval$ x env))
                          (svl::svex-eval$-bitxor-lst lst env))
                   (equal (sv::4vec-bitxor (sv::Svex-eval$ x env)
                                           (svl::svex-eval$-bitxor-lst (remove-equal-once x lst) env))
                          (svl::svex-eval$-bitxor-lst lst env))))
     :hints (("Goal"
              :induct (remove-equal-once x lst)
              :do-not-induct t
              :in-theory (e/d (remove-equal-once
                               svl::svex-eval$-bitxor-lst)
                              ())))))

  (local
   (defthmd 4vec-bitxor-introduce-new-var
     (implies (equal a b)
              (equal (sv::4vec-bitxor new a)
                     (sv::4vec-bitxor new b)))
     :hints ((bitops::logbitp-reasoning))))

  (local
   (defthm svex-eval$-bitxor-lst-of-remove-equal-2
     (implies (and (equal (sv::4vec-bitxor (svl::svex-eval$-bitxor-lst (remove-equal-once x lst) env)
                                           other)
                          other2)
                   (member-equal x lst))
              (equal (sv::4vec-bitxor (svl::svex-eval$-bitxor-lst lst env)
                                      other)
                     (sv::4vec-bitxor (svl::svex-eval$ x env) other2)))
     :rule-classes :forward-chaining
     :hints (("Goal"
              :use ((:instance svex-eval$-bitxor-lst-of-remove-equal))
              :in-theory (e/d () (svex-eval$-bitxor-lst-of-remove-equal))))))

  (local
   (defthm bitxor-lemma
     (implies (and (equal (sv::4vec-bitxor a b)
                          (sv::4vec-bitxor x y))
                   (equal (sv::4vec-bitxor y 1z)
                          (sv::4vec-bitxor k m)))
              (equal (equal (sv::4vec-bitxor a (sv::4vec-bitxor b 1z))
                            (sv::4vec-bitxor x (sv::4vec-bitxor k m)))
                     t))))

  (local
   (defthm 3/4vec-p-of-SVEX-EVAL$-BITXOR-LST
     (and (sv::3vec-p (SVL::SVEX-EVAL$-BITXOR-LST x env))
          (sv::4vec-p (SVL::SVEX-EVAL$-BITXOR-LST x env)))
     :hints (("Goal"
              :in-theory (e/d (SVL::SVEX-EVAL$-BITXOR-LST) ())))))

  (defret <fn>-is-correct
    (and (equal (sv::4vec-bitxor (sv::svex-eval$ res-svex env)
                                 (svl::svex-eval$-bitxor-lst to-remove-lst env))
                (sv::4vec-bitxor (sv::svex-eval$ svex env)
                                 (svl::svex-eval$-bitxor-lst remaining-to-remove env)))
         (equal (sv::4vec-bitxor (svl::svex-eval$-bitxor-lst to-remove-lst env)
                                 (sv::svex-eval$ res-svex env))
                (sv::4vec-bitxor (sv::svex-eval$ svex env)
                                 (svl::svex-eval$-bitxor-lst remaining-to-remove env))))
    :otf-flg t
    :hints (("Goal"
             :expand ((:free (args)
                             (sv::svex-apply 'sv::bitxor args)))
             :in-theory (e/d (sv::svex-call->fn
                              sv::svex-call->args
                              SV::SVEXLIST-EVAL$)
                             ()))))

  ;; measure lemmas:
  (defret svex-count-of-<fn>
    (implies (and )
             (and (implies (equal remaining-to-remove to-remove-lst)
                           (<= (sv::svex-count res-svex)
                               (sv::svex-count svex)))
                  (implies (not (equal remaining-to-remove to-remove-lst))
                           (< (sv::svex-count res-svex)
                              (sv::svex-count svex)))))
    :rule-classes (:rewrite :linear)
    :hints (("Goal"
             :in-theory (e/d (svex-apply$-for-bitxor-meta
                              SV::SVEX-COUNT
                              SV::SVEX-CALL->ARGS
                              SV::SVEXlist-COUNT
                              sv::Svex-kind)
                             ()))))

  ;; (find-s-from-found-c-in-svex-aux-remove #!SV'(bitxor (bitxor a b) (bitxor c d)) #!SV'(a c))
  ;; ;; returns
  ;; ((SV::BITXOR SV::B SV::D) NIL)
  )

(defines find-s-from-found-c-in-svex-aux
  :verify-guards nil

  :prepwork ((define find-s-from-found-c-in-svex-aux-counter ()
               nil
               ///
               (profile 'find-s-from-found-c-in-svex-aux-counter))

             (define svex-apply$-for-bitxor-meta2 (arg1 arg2)
               :returns (res-svex sv::svex-p :hyp (and (force (sv::svex-p arg1))
                                                       (force (sv::svex-p arg2))))
               :inline t
               (b* ((res
                     (cond ((equal arg1 0)
                            (case-match arg2
                              (('sv::bitxor & &)
                               arg2)
                              (& ;; should never come here.
                               (hons-list 'sv::unfloat  arg2))))
                           ((equal arg2 0)
                            (case-match arg1
                              (('sv::bitxor & &)
                               arg1)
                              (& ;; should never come here.
                               (hons-list 'sv::unfloat  arg1))))
                           (t (hons-list 'sv::bitxor arg1 arg2))))
                    ;; TODO: clean ones in a better way here...
                    ;;(res (case-match res (('sv::bitxor 1 ('sv::bitxor 1 x)) x) (& res)))
                    )
                 res)
               ///
               (defret <fn>-is-correct
                 (equal (sv::svex-eval$ res-svex env)
                        (sv::4vec-bitxor (sv::svex-eval$ arg1 env)
                                         (sv::svex-eval$ arg2 env)))
                 :hints (("Goal"
                          :expand ((:free (args)
                                          (sv::svex-apply 'sv::bitxor args))
                                   (:free (args)
                                          (sv::svex-apply 'sv::unfloat args)))
                          :in-theory (e/d (sv::svex-call->fn
                                           sv::svex-call->args
                                           SV::SVEXLIST-EVAL$)
                                          ()))))

               )

             (define find-s-from-found-c-bitxor-args (args)
               :returns (res sv::svex-p :hyp (force (sv::Svexlist-p args)))
               (cond
                ((atom args)
                 0)
                ((atom (cdr args))
                 (hons-list 'sv::unfloat (car args)))
                ((atom (cddr args))
                 (hons-list 'sv::bitxor
                            (car args)
                            (cadr args)))
                (t
                 (hons-list 'sv::bitxor
                            (find-s-from-found-c-bitxor-args (cdr args))
                            (car args))))
               ///
               (defret <fn>-is-correct
                 (equal (sv::Svex-eval$ res env)
                        (svl::svex-eval$-bitxor-lst args env))
                 :hints (("Goal"
                          :in-theory (e/d (SV::SVEX-CALL->FN
                                           SV::SVEX-CALL->args
                                           SV::SVEX-APPLY)
                                          ())))))

             )

  (define find-s-from-found-c-in-svex-aux ((svex sv::svex-p)
                                           (collected-args-alist collected-fa/ha-c-chain-pattern-args-p)
                                           &key
                                           ((adder-type symbolp) 'adder-type)
                                           ((limit natp) 'limit))
    ;;:measure (sv::Svex-count svex)
    :measure (nfix limit)
    :returns (res sv::Svex-p :hyp (and (sv::Svex-p svex)
                                       (collected-fa/ha-c-chain-pattern-args-p collected-args-alist)))
    :no-function t
    (if (zp limit) ;; proving the measure is not easy so I will use memoize-partial
        svex
      (let ((limit (1- limit)))
        (sv::svex-case
         svex
         :quote svex
         :var   svex
         :call
         (cond ((ha-s-chain-pattern-p svex)
                ;; possible fa-s-chain/ha-s-chain here.
                (b* (;; first see if anything in the xor chain appears as an argument to an orphan fa-c
                     ;; explore1-res will be list of all 3 args. or 2 args if working for ha-c
                     ((mv args exploded-args)
                      (find-s-from-found-c-in-svex-aux-explore svex collected-args-alist nil))

                     ((unless (and args exploded-args))
                      (sv::svex-call svex.fn
                                     (find-s-from-found-c-in-svexlist-aux svex.args
                                                                          collected-args-alist)))

                     ((mv rest-bitxor remaining-exploded-args)
                      (find-s-from-found-c-in-svex-aux-remove svex exploded-args))

                     ((when remaining-exploded-args)
                      ;; this should never happend
                      (sv::svex-call svex.fn
                                     (find-s-from-found-c-in-svexlist-aux svex.args
                                                                          collected-args-alist)))
                     (- (find-s-from-found-c-in-svex-aux-counter))
                     (result
                      (svex-apply$-for-bitxor-meta2
                       (find-s-from-found-c-in-svex-aux rest-bitxor collected-args-alist)
                       (find-s-from-found-c-bitxor-args
                        (find-s-from-found-c-in-svexlist-aux args collected-args-alist)))))
                  result))
               (t (sv::svex-call svex.fn
                                 (find-s-from-found-c-in-svexlist-aux svex.args
                                                                      collected-args-alist))))))))
  (define find-s-from-found-c-in-svexlist-aux ((lst sv::Svexlist-p)
                                               (collected-args-alist collected-fa/ha-c-chain-pattern-args-p)
                                               &key
                                               ((adder-type symbolp) 'adder-type)
                                               ((limit natp) 'limit))
    ;;:measure (sv::svexlist-count lst)
    :measure (nfix limit)
    :returns (res-lst sv::Svexlist-p :hyp (and (sv::Svexlist-p lst)
                                               (collected-fa/ha-c-chain-pattern-args-p collected-args-alist)))
    :no-function t
    (if (zp limit) ;; proving the measure is not easy so I will use memoize-partial
        lst
      (let ((limit (1- limit)))
        (if (atom lst)
            nil
          (hons (find-s-from-found-c-in-svex-aux (car lst) collected-args-alist)
                (find-s-from-found-c-in-svexlist-aux (cdr lst) collected-args-alist))))))
  ///

  (verify-guards find-s-from-found-c-in-svex-aux-fn
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d () ()))))

  ;;(memoize 'find-s-from-found-c-in-svex-aux-fn :condition '(eq (sv::svex-kind svex) :call))

  (acl2::memoize-partial
   ((find-s-from-found-c-in-svex-aux* find-s-from-found-c-in-svex-aux-fn)
    (find-s-from-found-c-in-svexlist-aux* find-s-from-found-c-in-svexlist-aux-fn
                                          :condition nil)))

  (local
   (include-book "std/basic/inductions" :DIR :SYSTEM))

  (local
   (defthm svex-eval$-bitxor-lst-when-svexlist-evals-are-equal
     (implies (and (equal (sv::Svexlist-eval$ lst1 env)
                          (sv::Svexlist-eval$ lst2 env))
                   (syntaxp (not (lexorder lst2 lst1))))
              (equal (svl::svex-eval$-bitxor-lst lst1 env)
                     (svl::svex-eval$-bitxor-lst lst2 env)))
     :hints (("Goal"
              :induct (acl2::cdr-cdr-induct lst1 lst2)
              :do-not-induct t
              :expand ((SV::SVEXLIST-EVAL$ LST2 ENV))
              :in-theory (e/d (sv::Svexlist-eval$
                               svl::svex-eval$-bitxor-lst)
                              ())))))

  (defret-mutual <fn>-correct
    (defret <fn>-is-correct
      (implies (and (force (sv::svex-p svex))
                    (force (warrants-for-adder-pattern-match))
                    (force (collected-fa/ha-c-chain-pattern-args-p collected-args-alist))
                    (force (collected-fa/ha-c-chain-pattern-args-inv collected-args-alist env)))
               (equal (sv::svex-eval$ res env)
                      (sv::svex-eval$ svex env)))
      :fn find-s-from-found-c-in-svex-aux)
    (defret <fn>-is-correct
      (implies (and (force (sv::svexlist-p lst))
                    (force (warrants-for-adder-pattern-match))
                    (force (collected-fa/ha-c-chain-pattern-args-p collected-args-alist))
                    (force (collected-fa/ha-c-chain-pattern-args-inv collected-args-alist env)))
               (equal (sv::svexlist-eval$ res-lst env)
                      (sv::svexlist-eval$ lst env)))
      :fn find-s-from-found-c-in-svexlist-aux)
    :otf-flg t
    :hints (("goal"
             :expand ((:free (x) (sv::svex-apply$ 'fa-s-chain x))
                      (:free (x) (sv::svex-apply$ 'sv::bitxor x))
                      (:free (x) (sv::svex-apply 'sv::bitxor x))
                      (sv::svexlist-eval$ (cdr svex) env)
                      (sv::svexlist-eval$ (cddr svex) env)
                      (find-s-from-found-c-in-svexlist-aux  lst collected-args-alist)
                      (find-s-from-found-c-in-svex-aux  svex collected-args-alist))
             :in-theory (e/d (sv::svex-call->fn
                              sv::svex-call->args
                              sv::svexlist-eval$
                              fa-s-chain)
                             ())))))

(define find-s-from-found-c-in-svex-alist-aux ((alist sv::svex-alist-p)
                                               (collected-args-alist collected-fa/ha-c-chain-pattern-args-p)
                                               &key
                                               ((adder-type symbolp) 'adder-type))
  :returns (res sv::Svex-alist-p :hyp (and (sv::Svex-alist-p alist)
                                           (collected-fa/ha-c-chain-pattern-args-p collected-args-alist)))
  (if (atom alist)
      alist
    (acons (caar alist)
           (find-s-from-found-c-in-svex-aux* (cdar alist) collected-args-alist adder-type)
           (find-s-from-found-c-in-svex-alist-aux (cdr alist) collected-args-alist)))
  ///
  (defret <fn>-is-correct
    (implies (and (force (sv::svex-alist-p alist))
                  (force (warrants-for-adder-pattern-match))
                  (force (collected-fa/ha-c-chain-pattern-args-p collected-args-alist))
                  (force (collected-fa/ha-c-chain-pattern-args-inv collected-args-alist env)))
             (equal (sv::svex-alist-eval$ res env)
                    (sv::svex-alist-eval$ alist env)))
    :hints (("Goal"
             :in-theory (e/d (sv::svex-alist-eval$) ())))))

(defsection alistp-of-of-fast-alist-clean
  (defthm alistp-of-of-fast-alist-fork
    (implies (and (alistp x)
                  (alistp last))
             (alistp (fast-alist-fork x last))))

  (defthm alistp-of-last
    (implies (alistp x)
             (alistp (last x))))

  (defthm alistp-of-cdr
    (implies (alistp x)
             (alistp (cdr x))))

  (defthm alistp-of-of-fast-alist-clean
    (implies (force (alistp x))
             (alistp (fast-alist-clean x)))))

(defsection pattern-alist-p-of-of-fast-alist-clean
  (defthm pattern-alist-p-of-of-fast-alist-fork
    (implies (and (pattern-alist-p x)
                  (pattern-alist-p last))
             (pattern-alist-p (fast-alist-fork x last))))

  (defthm pattern-alist-p-of-last
    (implies (pattern-alist-p x)
             (pattern-alist-p (last x))))

  (defthm pattern-alist-p-of-cdr
    (implies (pattern-alist-p x)
             (pattern-alist-p (cdr x))))

  (defthm pattern-alist-p-of-of-fast-alist-clean
    (implies (force (pattern-alist-p x))
             (pattern-alist-p (fast-alist-clean x)))))

;; (bitand/or/xor-cancel-repeated fn term1 term2)

(defsection simplify-to-find-fa-c-patterns

  ;; Goal is to attempting to simplify  svexes locally until they reveal a fa-c
  ;; pattern. If it does, then simplification  is left and the found pattern is
  ;; wrapped with "ID"  svex-op in order to prevent  other simplifications from
  ;; messing with it.

  (defconst *simplify-to-find-fa-c-patterns-limit*
    8)

  (define simplify-to-find-fa-c-patterns-aux ((x sv::Svex-p)
                                              (limit natp)
                                              &key
                                              (skip 'nil)
                                              (inside-out 'nil)
                                              ((env) 'env)
                                              ((context rp-term-listp) 'context)
                                              ((config svl::svex-reduce-config-p) 'config))
    :returns (mv (res sv::svex-p :hyp (sv::svex-p x))
                 there-is-more)
    :guard (not (svl::svex-reduce-config->skip-bitor/and/xor-repeated config))
    :measure (acl2::nat-list-measure (list limit (if skip 0 1)))
    :verify-guards :after-returns
    (if (zp limit)
        (mv x t)
      (sv::svex-case
       x
       :var (mv x nil)
       :quote (mv x nil)
       :call
       (cond ((and (or (equal x.fn 'sv::bitor)
                       (equal x.fn 'sv::bitand)
                       (equal x.fn 'sv::bitxor))
                   (svl::equal-len x.args 2))
              (b* (((when (and (not skip)
                               (not inside-out)))
                    (let* ((new-x (svl::bitand/or/xor-cancel-repeated
                                   x.fn (first x.args) (second x.args) :config config)))
                      (simplify-to-find-fa-c-patterns-aux new-x limit :skip t :inside-out inside-out)))

                   ((mv arg1 there-is-more1)
                    (simplify-to-find-fa-c-patterns-aux (first x.args) (1- limit) :inside-out inside-out))
                   ((mv arg2 there-is-more2)
                    (simplify-to-find-fa-c-patterns-aux (second x.args) (1- limit) :inside-out inside-out))
                   (new-x (if inside-out
                              (svl::bitand/or/xor-cancel-repeated
                               x.fn arg1 arg2 :config config)
                            (svl::bitand/or/xor-simple-constant-simplify
                             x.fn arg1 arg2 :config config))))
                (mv new-x (or there-is-more1
                              there-is-more2))))
             (t (mv x nil)))))
    ///
    (defret <fn>-is-correct
      (implies (and (sv::svex-p x)
                    (rp::rp-term-listp context)
                    (rp::valid-sc env-term a)
                    (rp::eval-and-all context a)
                    (rp::falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config)))
               (equal
                (sv::svex-eval$ res (rp-evlt env-term a))
                (sv::svex-eval$ x (rp-evlt env-term a))))
      :hints (("Goal"
               :in-theory (e/d (sv::svex-call->args
                                SV::SVEX-CALL->fn)
                               (eval-and-all
                                rp::rp-term-listp
                                falist-consistent-aux))))))

  (define simplify-to-find-fa-c-patterns-iter ((x sv::Svex-p)
                                               (limit natp)
                                               &key
                                               ((env) 'env)
                                               ((context rp-term-listp) 'context)
                                               ((config svl::svex-reduce-config-p) 'config))
    :guard (and (<= limit *simplify-to-find-fa-c-patterns-limit*)
                (not (svl::svex-reduce-config->skip-bitor/and/xor-repeated config)))
    :returns (mv (new-x sv::svex-p :hyp (sv::svex-p x))
                 (found))
    :prepwork ((local
                (use-arithmetic-5 t)))
    (if (zp limit)
        (mv x nil)
      (b* (((mv simplified there-is-more1)
            (simplify-to-find-fa-c-patterns-aux
             x (+ *simplify-to-find-fa-c-patterns-limit* (- limit) 1)
             :inside-out nil))
           ((when (equal simplified x))
            (simplify-to-find-fa-c-patterns-iter x (1- limit)))
           (fa-c-patterns (look-for-fa-c-chain-pattern simplified))

           #|(- (and (case-match x (('sv::bitor
           ('sv::bitand
           ('sv::bitxor 1 ('sv::?* . &))
           ('sv::bitxor ('sv::bitxor . &) &))
           &)
           t))
           (cwe "x: ~p0, simplified: ~p1, fa-c-patterns: ~p2~%"
           x simplified fa-c-patterns)))|#

           ((when fa-c-patterns)
            (mv simplified t))

           ;; Try also simplifying from inside-out
           ((mv simplified there-is-more2)
            (simplify-to-find-fa-c-patterns-aux
             x (+ *simplify-to-find-fa-c-patterns-limit* (- limit) 1)
             :inside-out t))
           (fa-c-patterns (look-for-fa-c-chain-pattern simplified))
           ((when fa-c-patterns)
            (mv simplified t))

           ((unless (or there-is-more1 there-is-more2))
            (mv simplified nil)))
        (simplify-to-find-fa-c-patterns-iter x (1- limit))))
    ///
    (defret <fn>-is-correct
      (implies (and (sv::svex-p x)
                    (rp::rp-term-listp context)
                    (rp::valid-sc env-term a)
                    (rp::eval-and-all context a)
                    (rp::falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config)))
               (equal
                (sv::svex-eval$ new-x (rp-evlt env-term a))
                (sv::svex-eval$ x (rp-evlt env-term a))))
      :fn simplify-to-find-fa-c-patterns-iter
      :hints (("Goal"
               :expand ((simplify-to-find-fa-c-patterns-iter x limit))
               :in-theory (e/d (simplify-to-find-fa-c-patterns-iter)
                               (eval-and-all
                                rp::rp-term-listp
                                falist-consistent-aux))))))

  (defines simplify-to-find-fa-c-patterns
    :verify-guards nil
    (define simplify-to-find-fa-c-patterns ((x sv::Svex-p)
                                            &key
                                            ((env) 'env)
                                            ((context rp-term-listp) 'context)
                                            ((config svl::svex-reduce-config-p) 'config))
      :measure (sv::svex-count x)
      :guard (not (svl::svex-reduce-config->skip-bitor/and/xor-repeated config))
      :returns (res sv::svex-p :hyp (sv::svex-p x))
      (sv::svex-case
       x
       :var x
       :quote x
       :call
       (b* ((x.args (simplify-to-find-fa-c-patterns-list x.args))
            (x (sv::svex-call x.fn x.args))
            ((unless (equal x.fn 'sv::bitor)) ;; no need to look for fa-c patterns if x is not bitor.
             x)
            ((mv new-x found)
             (simplify-to-find-fa-c-patterns-iter x
                                                  *simplify-to-find-fa-c-patterns-limit*))

            (- (and (not found)
                    (case-match x
                      (('sv::bitor ('sv::bitand x ('sv::bitxor 1 ('sv::bitxor x z)))
                                   ('sv::bitand & ('sv::bitxor x z)))
                       (list x z)))
                    (cwe "WARNING!!! A known fa-c pattern is missed. For x: ~p0. New-x: ~p1" x new-x)))

            )
         ;; wrapping with id so that other simplification attempts do not corrupt this found pattern.
         (if found
             (sv::svex-call 'sv::id (hons-list new-x))
           x))))

    (define simplify-to-find-fa-c-patterns-list ((lst sv::Svexlist-p)
                                                 &key
                                                 ((env) 'env)
                                                 ((context rp-term-listp) 'context)
                                                 ((config svl::svex-reduce-config-p) 'config))
      :guard (not (svl::svex-reduce-config->skip-bitor/and/xor-repeated config))
      :measure (sv::svexlist-count lst)
      :returns (res sv::svexlist-p :hyp (sv::svexlist-p lst))
      (if (atom lst)
          nil
        (hons (simplify-to-find-fa-c-patterns (car lst))
              (simplify-to-find-fa-c-patterns-list (cdr lst)))))
    ///
    (verify-guards simplify-to-find-fa-c-patterns-fn)

    (memoize 'simplify-to-find-fa-c-patterns-fn
             :condition '(eq (sv::svex-kind x) :call))

    (local
     (defthm id-of-bitor-lemma
       (equal (sv::svex-apply 'id (list (sv::svex-apply 'sv::bitor args)))
              (sv::svex-apply 'sv::bitor args))
       :hints (("Goal"
                :in-theory (e/d (sv::svex-apply) ())))))

    (defret-mutual svex-eval$-correctness
      (defret <fn>-is-correct
        (implies (and (sv::svex-p x)
                      (rp::rp-term-listp context)
                      (rp::valid-sc env-term a)
                      (rp::eval-and-all context a)
                      (rp::falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config)))
                 (equal
                  (sv::svex-eval$ res (rp-evlt env-term a))
                  (sv::svex-eval$ x (rp-evlt env-term a))))
        :fn simplify-to-find-fa-c-patterns)
      (defret <fn>-is-correct
        (implies (and (sv::svexlist-p lst)
                      (rp::rp-term-listp context)
                      (rp::valid-sc env-term a)
                      (rp::eval-and-all context a)
                      (rp::falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config)))
                 (equal
                  (sv::svexlist-eval$ res (rp-evlt env-term a))
                  (sv::svexlist-eval$ lst (rp-evlt env-term a))))
        :fn simplify-to-find-fa-c-patterns-list)
      :mutual-recursion simplify-to-find-fa-c-patterns
      :hints (("Goal"
               :in-theory (e/d ()
                               (eval-and-all
                                rp::rp-term-listp
                                falist-consistent-aux))))))

  (define simplify-to-find-fa-c-patterns-alist ((alist sv::Svex-alist-p)
                                                &key
                                                ((env) 'env)
                                                ((context rp-term-listp) 'context)
                                                ((config svl::svex-reduce-config-p) 'config))
    :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p alist))
    :guard (not (svl::svex-reduce-config->skip-bitor/and/xor-repeated config))
    (if (atom alist)
        nil
      (acons (caar alist)
             (simplify-to-find-fa-c-patterns (cdar alist))
             (simplify-to-find-fa-c-patterns-alist (cdr alist))))
    ///
    (defret <fn>-is-correct
      (implies (and (sv::svex-alist-p alist)
                    (rp::rp-term-listp context)
                    (rp::valid-sc env-term a)
                    (rp::eval-and-all context a)
                    (rp::falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config)))
               (equal
                (sv::svex-alist-eval$ res (rp-evlt env-term a))
                (sv::svex-alist-eval$ alist (rp-evlt env-term a))))
      :fn simplify-to-find-fa-c-patterns-alist
      :hints (("Goal"
               :in-theory (e/d (sv::svex-alist-eval$)
                               (eval-and-all
                                rp::rp-term-listp
                                falist-consistent-aux)))))))

;; (rp::simplify-to-find-fa-c-patterns #!SV'(bitxor other
;;                                                  (bitor (bitor (bitand x y) (bitor (bitand x y) (bitand y z)))
;;                                                         (bitand x z)))
;;                                     :context nil
;;                                     :env nil
;;                                     :config nil)
;; ;; returns:
;; (BITXOR OTHER
;;         (ID (BITOR (BITOR (BITAND X Y) (BITAND Y Z))
;;                    (BITAND X Z))))

(define pattern-alist-has-complete-full-adder-patterns-p ((pattern-alist alistp)
                                                          &key
                                                          ((adder-type symbolp) 'adder-type))
  (if (atom pattern-alist)
      0
    (+ (if (if (eq adder-type 'ha)
               (subsetp-equal '(ha-c-chain ha-s-chain)
                              (true-list-fix (cdar pattern-alist)))
             (subsetp-equal '(fa-c-chain fa-s-chain)
                            (true-list-fix (cdar pattern-alist))))
           1 0)
       (pattern-alist-has-complete-full-adder-patterns-p (cdr
                                                          pattern-alist)))))

(define find-f/h-adders-in-svex-alist ((svex-alist sv::svex-alist-p)
                                       (limit natp)
                                       &key
                                       ((adder-type symbolp) 'adder-type)
                                       ((env) 'env)
                                       ((context rp-term-listp) 'context)
                                       ((config svl::svex-reduce-config-p) 'config))
  :prepwork
  ((defconst *find-f/h-adders-in-svex-alist-limit*
     12)
   (local
    (in-theory (disable fast-alist-clean))))
  :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p svex-alist))
  :measure (nfix limit)
  (b* ((pass-num (If (eq adder-type 'ha) 2 1))
       (adder-str (If (eq adder-type 'ha) "half-adder" "full-adder"))

       ((when (zp limit))
        (progn$
         (cw "- Iteration limit of ~p0 is reached. Will not parse again for ~s1 patterns. Either there is an unexpected infinite loop, or the iteration limit may need to be increased. ~%" *find-f/h-adders-in-svex-alist-limit* adder-str)
         svex-alist))

       (- (and (equal limit *find-f/h-adders-in-svex-alist-limit*)
               (cw "- Searching for ~s0 patterns now. ~%" adder-str)))
       (- (cw "-- Pass #~p0:~%" (+ 1 (- limit) *find-f/h-adders-in-svex-alist-limit*)))

       ((mv pattern-alist &)
        (gather-adder-patterns-in-svex-alist svex-alist nil nil pass-num))
       (svex-alist (replace-adder-patterns-in-svex-alist svex-alist pattern-alist pass-num))

       (- (clear-memoize-table 'replace-adder-patterns-in-svex))
       (pattern-alist (fast-alist-clean pattern-alist))
       (replaced-pattern-cnt (pattern-alist-has-complete-full-adder-patterns-p pattern-alist))
       (- (cw "- After the quick search, ~p0 ~s1 patterns are found and replaced. Let's see if more patterns are revealed: ~%" replaced-pattern-cnt adder-str))
       (- (fast-alist-free pattern-alist))

       (- (cw "- First another quick search.. ~%"))

       ;; TODO: to prevent  consing, can do some preliminary check  here for if
       ;; there exists xor chains OR maybe fa-* functions under or gates.

       ;; not sure if fix-order-of-fa/ha-s-args-alist should be called
       ;; somewhere else.
       (svex-alist (fix-order-of-fa/ha-s-args-alist svex-alist))

       ;; search again after replacements so args can match when looking for fa-s/ha-s patterns.
       ((mv pattern-alist &)
        (gather-adder-patterns-in-svex-alist svex-alist nil nil pass-num))
       (pattern-alist (fast-alist-clean pattern-alist))

       (new-pattern-cnt (pattern-alist-has-complete-full-adder-patterns-p pattern-alist))
       ((when (> new-pattern-cnt 0))
        (progn$ (cw "- Replacement after the previous quick search revealed ~p0 more ~s1 patterns, which are all replaced. Let's make another pass.~%"
                    new-pattern-cnt adder-str)
                (b* ((svex-alist
                      (replace-adder-patterns-in-svex-alist svex-alist pattern-alist pass-num))
                     (- (fast-alist-free pattern-alist)))
                  (find-f/h-adders-in-svex-alist svex-alist (1- limit)))))

       ;; TODO:  HERE I  can look  for bitxors  with at  least 3  elements to
       ;; decide if any fa-s/ha-s might be mising before consing below..

       (collected-args-alist (process-fa/ha-c-chain-pattern-args pattern-alist nil))
       (- (fast-alist-free pattern-alist))

       (- (cw "- Nothing after the  second quick search.  Now will look  more carefully if we ~
have missed any ~s0-s pattern that  has a found counterpart ~s0-c pattern...~%"
              adder-str))

       (new-svex-alist
        (find-s-from-found-c-in-svex-alist-aux svex-alist collected-args-alist))

       ;; calling fix-order-of-fa/ha-s-args-alist might be unnecessary
       ;; here. not sure.
       (new-svex-alist (fix-order-of-fa/ha-s-args-alist new-svex-alist))

       (- (clear-memoize-table 'find-s-from-found-c-in-svex-aux-for-fa))
       (- (fast-alist-free collected-args-alist))

       ((when (hons-equal new-svex-alist svex-alist))
        (b* ((- (cw "- Could not find any missed ~s0-s. ~%" adder-str))
             ((unless (equal adder-type 'fa)) svex-alist)
             (- (cw "- Let's see if bitxor/or/and simplification can reveal more fa-c patterns... "))
             (config (svl::change-svex-reduce-config ;; make sure config is set right.
                      config :skip-bitor/and/xor-repeated nil))
             (new-svex-alist (simplify-to-find-fa-c-patterns-alist svex-alist))
             ((when (hons-equal new-svex-alist svex-alist))
              (b* ((- (cw "Nothing. This did not reveal any fa-c pattern. Let's perform a global bitxor/and/or simplification before ending the search for full-adders. ~%"))
                   (new-svex-alist (svl::svex-alist-simplify-bitand/or/xor svex-alist :config config)))
                (if (hons-equal new-svex-alist svex-alist)
                    (progn$ (cw "Global bitxor/and/or simplification did not change anything. Ending the search.~%")
                            svex-alist)
                  (find-f/h-adders-in-svex-alist new-svex-alist (1- limit)))))
             (- (cw "Success! some fa-c patterns are revealed. Let's make another pass.~%")))
          (find-f/h-adders-in-svex-alist new-svex-alist (1- limit))))

       (- (cw "- Some missed ~s0-s patterns are found and their shape is ~
       updated. This will reveal more ~s0 patterns during quick search. So will ~
       now do another pass. There might be an overlap in the statistics below. ~%"
              adder-str))

       ;; find-s-from-found-c-in-svex-alist-aux  may  cause  new  simplify-able
       ;; patterns to  occur. but not sure  if something less general  would be
       ;; useful here. TODO: investigate.
       #|(new-svex-alist (svl::svex-alist-simplify-bitand/or/xor  new-svex-alist
       :config config))|#

       )
    (find-f/h-adders-in-svex-alist new-svex-alist (1- limit)))
  ///
  (defret <fn>-is-correct
    (implies (and (sv::svex-alist-p svex-alist)
                  (rp::rp-term-listp context)
                  (rp::valid-sc env-term a)
                  (rp::eval-and-all context a)
                  (rp::falist-consistent-aux env env-term)
                  (svl::width-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->width-extns config))
                  (svl::integerp-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->integerp-extns config))
                  (force (warrants-for-adder-pattern-match)))
             (equal (sv::svex-alist-eval$ res (rp-evlt env-term a))
                    (sv::svex-alist-eval$ svex-alist (rp-evlt env-term a))))
    :hints (("Goal"
             ;;:do-not-induct t
             :expand (;;(find-f/h-adders-in-svex-alist svex-alist limit)
                      (collected-fa/ha-c-chain-pattern-args-inv nil (rp-evlt env-term a)))
             :in-theory (e/d ()
                             (valid-sc
                              valid-sc-subterms
                              rp-trans
                              rp-term-listp
                              rp-trans-lst
                              eval-and-all
                              falist-consistent-aux
                              ex-from-rp)))))

  )

(progn
  (encapsulate
    (((keep-missing-env-vars-in-svex) => *))
    (local
     (defun keep-missing-env-vars-in-svex ()
       nil)))

  (defmacro enable-keep-missing-env-vars-in-svex (enable)
    (if enable
        `(defattach keep-missing-env-vars-in-svex return-t)
      `(defattach keep-missing-env-vars-in-svex return-nil)))

  (enable-keep-missing-env-vars-in-svex nil))

(make-event
 `(define svex-reduce-w/-env-config-1 ()
    :returns (config svl::svex-reduce-config-p)
    (svl::make-svex-reduce-config
     :width-extns ',(strip-cars (table-alist 'svl::width-of-svex-extns (w state)))
     :integerp-extns ',(strip-cars (table-alist 'svl::integerp-of-svex-extns (w state)))
     :keep-missing-env-vars (keep-missing-env-vars-in-svex))
    ///
    (defret <fn>-correct
      (and (implies (warrants-for-adder-pattern-match)
                    (and (svl::width-of-svex-extn-correct$-lst
                          (svl::svex-reduce-config->width-extns config))
                         (svl::integerp-of-svex-extn-correct$-lst
                          (svl::svex-reduce-config->integerp-extns config)))))
      :hints (("Goal"
               :do-not-induct t
               :use (,@(loop$ for x in (strip-cdrs (table-alist 'svl::width-of-svex-extns (w state)))
                              collect
                              `(:instance ,x))
                     ,@(loop$ for x in (strip-cdrs (table-alist 'svl::integerp-of-svex-extns (w state)))
                              collect
                              `(:instance ,x)))
               :in-theory (e/d (svl::width-of-svex-extn-correct$-lst)
                               (svl::integerp-of-svex-extn-correct$
                                svl::width-of-svex-extn-correct$)
                               ))))
    (in-theory (disable (:e svex-reduce-w/-env-config-1)))))

(make-event
 (b* ((w '((apply$-warrant-ha-c-chain)
           (apply$-warrant-fa-c-chain)
           (apply$-warrant-ha+1-c-chain)
           (apply$-warrant-ha+1-s-chain)
           (apply$-warrant-ha-s-chain)
           (apply$-warrant-fa-s-chain))))
   `(define check-context-for-adder-warrants ((context rp-term-listp))
      :returns valid
      (subsetp-equal ',w context)
      ///
      (local
       (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))
      (local
       (defthm member-equal-and-eval-and-all
         (implies (and (eval-and-all context a)
                       (member-equal x context))
                  (and (rp-evlt x a)
                       (implies (force (not (include-fnc x 'list)))
                                (rp-evl x a))))
         :rule-classes (:rewrite)))
      (local
       (in-theory (disable eval-and-all)))
      (defret <fn>-is-correct
        (implies (and (eval-and-all context acl2::unbound-free-env)
                      (rp-evl-meta-extract-global-facts)
                      (find-adders-in-svex-formula-checks state)
                      valid)
                 (and ,@w))
        :hints (("Goal"
                 :do-not-induct t
                 :in-theory (e/d () ())))))))

(define rewrite-adders-in-svex-alist ((term)
                                      (context rp-term-listp))
  :returns (mv res-term res-dont-rw)
  (case-match term
    (('sv::svex-alist-eval ('quote svex-alist) env-orig)
     (b* ((env (rp::ex-from-rp env-orig))
          ((mv falistp env) (case-match env
                              (('falist ('quote x) &) (mv t x))
                              (& (mv nil env))))
          ((unless falistp)
           (if (and (consp env) (equal (car env) 'cons))
               (progn$
                (cw "Note: the environment of svex-eval-alist is not a fast-alist. Making it a fast-alist now.~%")
                (mv `(sv::svex-alist-eval ',svex-alist (make-fast-alist ,env-orig))
                    `(nil t (nil t))))
             (mv term nil)))

          ((Unless (sv::svex-alist-p svex-alist)) ;; for guards
           (mv term (raise "given sv::svex-alist does not have sv::svex-alist: ~p0." svex-alist)))
          ((Unless (sv::svex-alist-no-foreign-op-p svex-alist)) ;; to convert svex-eval to eval$
           (mv term (raise "given sv::svex-alist has foreign operands: ~p0" svex-alist)))
          ((Unless (check-context-for-adder-warrants context)) ;; check for existence of warrants.
           (mv term (raise "Some necessary warrants were not found in the context: ~p0" context)))

          (config (svex-reduce-w/-env-config-1))

          (- (cw "Starting: svl::svex-alist-reduce-w/-env. ~%"))
          (- (time-tracker :rewrite-adders-in-svex :end))
          (- (time-tracker :rewrite-adders-in-svex :init
                           :times '(1 2 3 4 5)
                           :interval 5
                           ))
          (- (time-tracker :rewrite-adders-in-svex :start!))
          (config (svl::change-svex-reduce-config
                   config :skip-bitor/and/xor-repeated t))
          (svex-alist (svl::svexalist-convert-bitnot-to-bitxor svex-alist))
          (svex-alist (svl::svex-alist-reduce-w/-env svex-alist :env env :config config))
          (- (time-tracker :rewrite-adders-in-svex :stop))
          (- (time-tracker :rewrite-adders-in-svex :print?
                           :min-time 0
                           :msg "The total runtime of svl::svex-alist-reduce-w/-env ~
was ~st seconds."))

          (config (svl::change-svex-reduce-config
                   config
                   :skip-bitor/and/xor-repeated nil
                   :keep-missing-env-vars nil))

          (- (cw "Starting: rp::rewrite-adders-in-svex-alist. ~%"))
          (- (time-tracker :rewrite-adders-in-svex :end))
          (- (time-tracker :rewrite-adders-in-svex :init
                           :times '(1 2 3 4 5)
                           :interval 5
                           ))
          (- (time-tracker :rewrite-adders-in-svex :start!))

          (svex-alist (find-f/h-adders-in-svex-alist svex-alist
                                                     *find-f/h-adders-in-svex-alist-limit*
                                                     :adder-type 'fa))

          (- (cwe "resulting svex-alist after full-adders ~p0 ~%" svex-alist))

          (- (time-tracker :rewrite-adders-in-svex :stop))
          (- (time-tracker :rewrite-adders-in-svex :print?
                           :min-time 0
                           :msg "Search for full adder patterns took ~st secs.~%~%"))

          (- (time-tracker :rewrite-adders-in-svex :end))
          (- (time-tracker :rewrite-adders-in-svex :init
                           :times '(1 2 3 4 5)
                           :interval 5
                           ))
          (- (time-tracker :rewrite-adders-in-svex :start!))

          ;; below simplification might be unnecessary but shouldn't harm (probably)
          ;;(svex-alist (svl::svex-alist-simplify-bitand/or/xor svex-alist :config config))
          ;; commented out because find-f/h-adders-in-svex-alist should call it anyway.

          ;;(- (bad-pattern

          (svex-alist (find-f/h-adders-in-svex-alist svex-alist
                                                     *find-f/h-adders-in-svex-alist-limit*
                                                     :adder-type 'ha))
          (- (clear-memoize-table 'replace-adder-patterns-in-svex))

          (- (time-tracker :rewrite-adders-in-svex :stop))
          (- (time-tracker :rewrite-adders-in-svex :print?
                           :min-time 0
                           :msg "Search for other adder patterns took ~st secs.~%~%"))

          (- (cw "Finished: rp::rewrite-adders-in-svex-alist.~%"))

          (- (cwe "resulting svex-alist: ~p0 ~%" svex-alist))

          (- (cw "Starting: svl::svex-alist-to-svexl-alist ~%"))
          (svexl-alist (svl::svex-alist-to-svexl-alist svex-alist))
          (- (let ((x (svl::svexl-alist->node-array svexl-alist))) ;; for guards
               (cw "Finished: svl::svex-alist-to-svexl-alist. Resulting svexl-alist has ~p0 nodes.~%~%" (len x)))))
       (mv `(svl::svexl-alist-eval$ ',svexl-alist ,env-orig)
           `(nil t t))))
    (& (mv term nil)))
  ///

  (local
   (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

  (local
   (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

  (local
   (defthm is-rp-of-others
     (implies (not (equal (car term) 'rp))
              (not (is-rp term)))
     :hints (("Goal"
              :in-theory (e/d (is-rp) ())))))

  (local
   (defthm is-equals-of-others
     (implies (not (equal (car term) 'equals))
              (not (is-equals term )))
     :hints (("Goal"
              :in-theory (e/d (is-equals) ())))))

  (local
   (defthm is-if-of-others
     (implies (not (equal (car term) 'if))
              (not (is-if term)))
     :hints (("Goal"
              :in-theory (e/d (is-if) ())))))

  (local
   (create-regular-eval-lemma sv::svex-alist-eval 2  find-adders-in-svex-formula-checks))

  (local
   (create-regular-eval-lemma svl::SVEXL-ALIST-EVAL$ 2 find-adders-in-svex-formula-checks))

  (local
   (create-regular-eval-lemma MAKE-FAST-ALIST 1 find-adders-in-svex-formula-checks))

  (local
   (defthm rp-evlt-of-quoted
     (equal (rp-evlt (list 'quote x) a)
            x)))

  (local
   (defthmd rp-evlt-of-ex-from-rp-reverse
     (implies (syntaxp (equal term 'term))
              (equal (rp-evlt (caddr term) a)
                     (rp-evlt (ex-from-rp (caddr term)) a)))))

  (local
   (defthm dummy-lemma-
     (implies (consp (ex-from-rp term))
              (consp term))
     :rule-classes :forward-chaining))

  (local
   (defthm dummy-lemma-2
     (implies (equal (car (ex-from-rp term)) 'falist)
              (not (equal (car term) 'quote)))
     :rule-classes :forward-chaining))

  (local
   (defthm dummy-lemma-3
     (implies (and (rp-termp x)
                   (case-match x
                     (('falist ('quote &) &) t)))
              (falist-consistent-aux (cadr (cadr x))
                                     (caddr x)))
     :hints (("goal"
              :expand ((rp-termp x))
              :in-theory (e/d (rp-termp falist-consistent)
                              ())))))

  (local
   (defthm rp-evlt-of-falist
     (implies (and (rp-termp x)
                   (equal (car x) 'falist))
              (equal (rp-evlt x a)
                     (rp-evlt (caddr x) a)))
     :hints (("Goal"
              :expand ((RP-TERMP X))
              :in-theory (e/d (rp-termp falist-consistent)
                              ())))))

  (defret <fn>-is-correct
    (and (implies (and (rp::rp-term-listp context)
                       (rp-termp term)
                       (valid-sc term a)
                       (rp::eval-and-all context a)
                       (rp-evl-meta-extract-global-facts)
                       (find-adders-in-svex-formula-checks state))
                  (and (equal (rp-evlt res-term a)
                              (rp-evlt term a))
                       (valid-sc res-term a)))
         (implies (and (rp::rp-term-listp context)
                       (rp-termp term))
                  (rp-termp res-term)))
    :fn rewrite-adders-in-svex-alist
    :hints (("Goal"
             :expand ((rp-termp term)
                      (:free (fn args)
                             (valid-sc (cons fn args) a))
                      (RP-TERM-LISTP (CDR TERM))
                      (RP-TERM-LISTP (CDDR TERM)))
             :in-theory (e/d* (or*
                               RP-TERM-LISTP
                               rp-evlt-of-ex-from-rp-reverse
                               regular-eval-lemmas-with-ex-from-rp
                               regular-eval-lemmas
                               ;;is-rp
                               ;;FALIST-CONSISTENT
                               ;;is-if
                               svl::svexl-alist-eval$-correct-reverse)
                              (rp-evlt-of-ex-from-rp
                               rp-trans-is-term-when-list-is-absent
                               ex-from-rp
                               is-rp
                               RP-EVL-OF-VARIABLE
                               rp-trans
                               ;;rp::rp-term-listp
                               rp::falist-consistent-aux
                               rp::eval-and-all
                               valid-sc)))))

  )

(rp::add-meta-rule
 :meta-fnc rewrite-adders-in-svex-alist
 :trig-fnc sv::svex-alist-eval
 :formula-checks find-adders-in-svex-formula-checks
 :valid-syntaxp t
 :returns (mv term dont-rw)
 :disabled t
 :hints (("Goal"
          :in-theory (e/d ()
                          ()))))

(defsection apply$-of-adder-fncs-meta
  (define apply$-of-adder-fncs-meta-aux (args-term)
    :returns (mv (res-args rp-term-listp :hyp (rp-termp args-term))
                 all-bitp
                 valid)
    (case-match args-term
      (('cons x rest)
       (b* ((x-has-bitp (or (has-bitp-rp x)
                            (binary-fnc-p x)
                            (and (quotep x)
                                 (consp (cdr x))
                                 (bitp (unquote x)))))
            ((mv rest bitp valid)
             (apply$-of-adder-fncs-meta-aux rest)))
         (mv (cons x rest)
             (and x-has-bitp bitp)
             valid)))
      (('quote (x . rest))
       (b* ((x-has-bitp (bitp x))
            ((mv rest bitp valid)
             (apply$-of-adder-fncs-meta-aux (list 'quote rest))))
         (mv (cons `',x rest)
             (and x-has-bitp bitp)
             valid)))
      (''nil
       (mv nil t t))
      (& (mv nil nil nil)))
    ///
    (defretd <fn>-is-correct
      (implies valid
               (equal (rp-evlt args-term a)
                      (rp-evlt-lst res-args a))))
    (defret <fn>-is-valid-sc
      (implies (and valid
                    (valid-sc args-term a))
               (valid-sc-subterms res-args a))
      :hints (("Goal"
               :in-theory (e/d (is-rp is-if is-equals) ()))))

    (defret true-listp-of-<fn>
      (true-listp res-args))

    (local
     (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

    (local
     (defthm has-bitp-rp-implies
       (implies (and (has-bitp-rp term)
                     (valid-sc term a))
                (and (bitp (rp-evlt term a))))
       :hints (("goal"

                :in-theory (e/d (valid-sc-single-step
                                 has-bitp-rp
                                 is-rp)
                                (bitp))))))
    (local
     (with-output
       :off :all
       :on (error)
       (progn
         (create-regular-eval-lemma binary-or 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma binary-and 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma binary-xor 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma binary-not 1 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma binary-? 3 find-adders-in-svex-formula-checks)
         )))

    (local
     (defthm BINARY-FNC-P-implies
       (implies (and (BINARY-FNC-P term)
                     (rp-evl-meta-extract-global-facts)
                     (find-adders-in-svex-formula-checks state))
                (and (bitp (rp-evlt term a))))
       :hints (("goal"

                :in-theory (e/d* (REGULAR-EVAL-LEMMAS
                                  BINARY-FNC-P)
                                 (bitp))))))

    (defret <fn>-is-all-bitp
      (implies (and all-bitp
                    valid
                    (valid-sc args-term a)
                    (rp-evl-meta-extract-global-facts)
                    (find-adders-in-svex-formula-checks state))
               (and (bit-listp (rp-evlt args-term a))
                    (bit-listp (rp-evlt-lst res-args a))))
      :rule-classes (:rewrite :forward-chaining)
      :hints (("Goal"
               :in-theory (e/d (bit-listp
                                is-rp
                                is-if
                                is-equals)
                               ())))))

  ;; (apply$-of-adder-fncs-meta-aux `(cons (rp 'bitp x) (cons '1 (cons (rp 'bitp y) '(1)))))
  ;; = (((RP 'BITP X) '1 (RP 'BITP Y) '1) T T)

  (define apply$-of-adder-fncs-meta (term
                                     (context true-listp))
    :returns (mv (res rp-termp :hyp (rp-termp term)
                      :hints (("Goal"
                               :expand ((:free (rest) (is-rp (cons 'rp rest))))
                               :use ((:instance rp-term-listp-of-apply$-of-adder-fncs-meta-aux.res-args
                                                (args-term (CADR (CADDR TERM)))))
                               :in-theory (e/d (RP-TERM-LISTP)
                                               (rp-term-listp-of-apply$-of-adder-fncs-meta-aux.res-args)))))
                 dont-rw)
    (case-match term
      (('apply$ ('quote fnc) ('svl::4veclist-fix-wog args))
       (b* (((unless (member-equal fnc *adder-fncs*))
             (mv term nil))
            (warrant `(,(intern-in-package-of-symbol
                         (str::cat "APPLY$-WARRANT-" (symbol-name fnc))
                         fnc)))
            ((unless (member-equal warrant context))
             (mv term (raise "A necessary warrant is not found in the context: ~p0 ~%" warrant)))
            ((mv args-lst all-bitp valid)
             (apply$-of-adder-fncs-meta-aux args))
            ((unless valid)
             (mv term (raise "apply$-of-adder-fncs-meta-aux did not return valid. args: ~p0 ~%" args)))

            ((when (and* all-bitp
                         (or* (eq fnc 'ha-c-chain)
                              (eq fnc 'ha-s-chain))
                         (svl::equal-len args-lst 2)))
             (case fnc
               (ha-s-chain
                (mv `(rp 'bitp (equals (s-spec (cons ,(car args-lst)
                                                     (cons ,(cadr args-lst)
                                                           'nil)))
                                       (binary-xor ,(car args-lst)
                                                   ,(cadr args-lst))))
                    `(rp 'bitp (equals (s-spec (cons t (cons t 'nil)))
                                       (binary-xor t t)))))
               (ha-c-chain
                (mv `(rp 'bitp (equals (c-spec (cons ,(car args-lst)
                                                     (cons ,(cadr args-lst)
                                                           'nil)))
                                       (binary-and ,(car args-lst)
                                                   ,(cadr args-lst))))
                    `(rp 'bitp (equals (c-spec (cons t (cons t 'nil)))
                                       (binary-and t t)))))
               (t (mv term nil)))))
         (cond
          ((and* (eq fnc 'fa-c-chain)
                 (svl::equal-len args-lst 4))
           (mv `(,fnc (svl::4vec-fix-wog ,(first args-lst))
                      ,(second args-lst)
                      ,(third args-lst)
                      ,(fourth args-lst))
               `(nil (nil t) t t t)))
          ((and* (eq fnc 'ha+1-s-chain)
                 (svl::equal-len args-lst 3))
           (mv `(,fnc (svl::4vec-fix-wog ,(first args-lst))
                      ,(second args-lst)
                      ,(third args-lst))
               `(nil (nil t) t t)))
          ((and* (eq fnc 'fa-s-chain)
                 (svl::equal-len args-lst 3))
           (mv `(,fnc ,(first args-lst)
                      ,(second args-lst)
                      ,(third args-lst))
               `(nil t t t)))
          ((and* (svl::equal-len args-lst 2)
                 (or (eq fnc 'ha-c-chain)
                     (eq fnc 'ha+1-c-chain)
                     (eq fnc 'ha-s-chain)))
           (mv `(,fnc ,(first args-lst)
                      ,(second args-lst))
               `(nil t t t)))
          (t (mv term nil)))))
      (& (mv term nil)))

    ///

    (local
     (with-output
       :off :all
       :on (error)
       (progn
         (create-regular-eval-lemma rp 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma c-spec 1 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma bitp 1 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma equals 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma cons 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma s-spec 1 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma ha-s-chain 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma binary-xor 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma binary-and 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma ha+1-s-chain 3 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma fa-s-chain 3 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma ha+1-c-chain 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma fa-c-chain 4 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma ha-c-chain 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma apply$ 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma svl::4veclist-fix-wog 1 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma svl::4vec-fix-wog 1 find-adders-in-svex-formula-checks))))

    (local
     (defthm rp-evlt-of-quoted
       (implies (and (equal (car x) 'quote))
                (equal (rp-evlt x a)
                       (cadr x)))))

    (local
     (defthm 4vec-bitxor-or-dont-care
       (and (equal (sv::4vec-bitxor '(-1 . 0) x)
                   '(-1 . 0))
            (equal (sv::4vec-bitxor x '(-1 . 0))
                   '(-1 . 0)))
       :hints (("Goal"
                :in-theory (e/d (sv::4vec-bitxor) ())))))

    #|(local
    (defthm 4vec-bitand-or-dont-care
    (and (equal (sv::4vec-bitand '(-1 . 0) x)
    '(-1 . 0))
    (equal (sv::4vec-bitand x '(-1 . 0))
    '(-1 . 0)))
    :hints (("Goal"
    :in-theory (e/d (sv::4vec-bitand) ())))))|#

    ;; (local
    ;;  (defthm rp-evlt-lst-of-cdr
    ;;    (equal (rp-evlt-lst (cdr x) a)
    ;;           (cdr (rp-evlt-lst x a)))))

    (local
     (defthm RP-EVLT-LST-when-atom-and-cddr
       (implies (consp (cdr x))
                (equal (car (rp-evlt-lst (cddr x) a))
                       (rp-evlt (caddr x) a)))))

    (local
     (defthm RP-EVLT-LST-when-atom-and-cdr
       (implies (consp x)
                (equal (car (rp-evlt-lst (cdr x) a))
                       (rp-evlt (cadr x) a)))))

    (local
     (defthm consp-of-rp-evlt-lst
       (equal (consp (rp-evlt-lst lst a))
              (consp lst))
       :hints (("Goal"
                :induct (len lst)
                :in-theory (e/d (rp-trans-lst) ())))))

    (local
     (defthm HA+1-C-CHAIN-of-4vec-fix
       (and (equal (HA+1-C-CHAIN (sv::4vec-fix x) y)
                   (HA+1-C-CHAIN x y))
            (equal (HA+1-C-CHAIN x (sv::4vec-fix y))
                   (HA+1-C-CHAIN x y)))
       :hints (("Goal"
                :in-theory (e/d (HA+1-C-CHAIN) ())))))

    (local
     (defthm HA-C-CHAIN-of-4vec-fix
       (and (equal (HA-C-CHAIN (sv::4vec-fix x) y)
                   (HA-C-CHAIN x y))
            (equal (HA-C-CHAIN x (sv::4vec-fix y))
                   (HA-C-CHAIN x y)))
       :hints (("Goal"
                :in-theory (e/d (HA-C-CHAIN) ())))))

    (local
     (defthm FA-C-CHAIN-of-4vec-fix
       (and (equal (fa-c-chain m (sv::4vec-fix x) y z)
                   (fa-c-chain m x y z))
            (equal (fa-c-chain m x (sv::4vec-fix y) z)
                   (fa-c-chain m x y z))
            (equal (fa-c-chain m x y (sv::4vec-fix z))
                   (fa-c-chain m x y z)))
       :hints (("Goal"
                :in-theory (e/d (fa-c-chain) ())))))

    (local
     (defthm FA-s-CHAIN-of-4vec-fix
       (and (equal (fa-s-chain (sv::4vec-fix x) y z)
                   (fa-s-chain x y z))
            (equal (fa-s-chain x (sv::4vec-fix y) z)
                   (fa-s-chain x y z))
            (equal (fa-s-chain x y (sv::4vec-fix z))
                   (fa-s-chain x y z)))
       :hints (("Goal"
                :in-theory (e/d (fa-s-chain) ())))))

    (local
     (defthm ha+1-s-CHAIN-of-4vec-fix
       (and (equal (ha+1-s-chain m (sv::4vec-fix x) y)
                   (ha+1-s-chain m x y))
            (equal (ha+1-s-chain m x (sv::4vec-fix y))
                   (ha+1-s-chain m x y)))
       :hints (("Goal"
                :in-theory (e/d (ha+1-s-chain) ())))))

    (local
     (defthm ha-s-CHAIN-of-4vec-fix
       (and (equal (ha-s-chain (sv::4vec-fix x) y)
                   (ha-s-chain x y))
            (equal (ha-s-chain x (sv::4vec-fix y))
                   (ha-s-chain x y)))
       :hints (("Goal"
                :in-theory (e/d (ha-s-chain) ())))))

    (local
     (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

    (local
     (defthm member-equal-and-eval-and-all
       (implies (and (eval-and-all context a)
                     (member-equal x context))
                (and (rp-evlt x a)
                     (implies (force (not (include-fnc x 'list)))
                              (rp-evl x a))))
       :rule-classes (:rewrite)))

    (local
     (defthm valid-sc-of-car-when-valid-sc-subterms
       (implies (and (consp lst)
                     (valid-sc-subterms lst a))
                (valid-sc (car lst) a))))

    (local
     (defthm VALID-SC-SUBTERMS-of-cdr
       (implies (VALID-SC-SUBTERMS lst a)
                (VALID-SC-SUBTERMS (cdr lst) a))))

    (local
     (defthmd s-spec-when-bit-listp
       (implies (and (svl::equal-len x 2)
                     (bit-listp (rp-evlt-lst x a)))
                (equal (s-spec (list (rp-evlt (car x) a)
                                     (rp-evlt (cadr x) a)))
                       (binary-xor (rp-evlt (car x) a)
                                   (rp-evlt (cadr x) a))))
       :hints (("Goal"
                :do-not-induct t
                :in-theory (e/d (BIT-LISTP bitp) ())))))

    (local
     (defthmd ha-c-chain-when-bit-listp
       (implies (and (svl::equal-len x 2)
                     (bit-listp (rp-evlt-lst x a)))
                (equal (HA-C-CHAIN (rp-evlt (car x) a)
                                   (rp-evlt (cadr x) a))
                       (binary-and (rp-evlt (car x) a)
                                   (rp-evlt (cadr x) a))))
       :hints (("Goal"
                :do-not-induct t
                :in-theory (e/d (BIT-LISTP bitp) ())))))

    (local
     (defthmd ha-s-chain-when-bit-listp
       (implies (and (svl::equal-len x 2)
                     (bit-listp (rp-evlt-lst x a)))
                (equal (HA-s-CHAIN (rp-evlt (car x) a)
                                   (rp-evlt (cadr x) a))
                       (binary-xor (rp-evlt (car x) a)
                                   (rp-evlt (cadr x) a))))
       :hints (("Goal"
                :do-not-induct t
                :in-theory (e/d (BIT-LISTP bitp) ())))))

    (local
     (defthmd c-spec-when-bit-listp
       (implies (and (svl::equal-len x 2)
                     (bit-listp (rp-evlt-lst x a)))
                (equal (c-spec (list (rp-evlt (car x) a)
                                     (rp-evlt (cadr x) a)))
                       (binary-and (rp-evlt (car x) a)
                                   (rp-evlt (cadr x) a))))
       :hints (("Goal"
                :do-not-induct t
                :in-theory (e/d (BIT-LISTP bitp) ())))))

    (defret <fn>-is-valid-sc
      (and (implies (and (rp::rp-term-listp context)
                         (rp-termp term)
                         (valid-sc term a)
                         (rp-evl-meta-extract-global-facts)
                         (find-adders-in-svex-formula-checks state))
                    (valid-sc res a)))
      :fn apply$-of-adder-fncs-meta
      :hints (("Goal"
               :do-not-induct t
               :expand ((:free (x y a)
                               (eval-and-all (cons x y) a))
                        (:free (x y a)
                               (CONTEXT-FROM-RP (cons 'rp y) a))
                        (:free (x y a)
                               (ex-from-rp (cons 'rp y)))
                        (:free (x y a)
                               (ex-from-rp (cons 'equals y)))
                        (:free (x y a)
                               (CONTEXT-FROM-RP (cons 'equals y) a)))
               :in-theory (e/d* (s-spec-when-bit-listp
                                 c-spec-when-bit-listp
                                 apply$-of-adder-fncs-meta-aux-is-all-bitp
                                 ;;CONTEXT-FROM-RP
                                 regular-eval-lemmas
                                 regular-eval-lemmas-with-ex-from-rp
                                 is-rp is-if is-equals)
                                ((:REWRITE DEFAULT-CDR)
                                 (:REWRITE
                                  RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT)
                                 (:REWRITE
                                  ACL2::SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP)
                                 (:REWRITE VALID-SC-CADR)
                                 (:DEFINITION EX-FROM-RP)
                                 (:DEFINITION MEMBER-EQUAL)
                                 (:REWRITE NTH-0-CONS)
                                 (:REWRITE NTH-ADD1)
                                 len
                                 RP-EVLT-LST-OF-CONS
                                 bit-listp
                                 (:rewrite str::coerce-to-list-removal)
                                 (:rewrite str::coerce-to-string-removal)
                                 (:DEFINITION STR::FAST-STRING-APPEND)
                                 ;;(:DEFINITION RP-TRANS-LST)
                                 (:DEFINITION STRING-APPEND)
                                 ;;rp-trans-lst
                                 rp-trans
                                 rp-termp
                                 eval-and-all
                                 svl::4veclist-fix-wog-is-4veclist-fix
                                 rp-trans)))
              (and stable-under-simplificationp
                   '(:use ((:instance apply$-of-adder-fncs-meta-aux-is-all-bitp
                                      (args-term (cadr (caddr term)))
                                      ))))
              ))

    (defret <fn>-is-correct
      (and (implies (and (rp::rp-term-listp context)
                         (rp-termp term)
                         (valid-sc term ACL2::UNBOUND-FREE-ENV)
                         (rp::eval-and-all context ACL2::UNBOUND-FREE-ENV)
                         (rp-evl-meta-extract-global-facts)
                         (find-adders-in-svex-formula-checks state))
                    (and (equal (rp-evlt res ACL2::UNBOUND-FREE-ENV)
                                (rp-evlt term ACL2::UNBOUND-FREE-ENV))
                         #|(valid-sc res a)|#)))
      :fn apply$-of-adder-fncs-meta
      :hints (("Goal"
               :expand ((:free (x y)
                               (svl::4veclist-fix-wog (cons x y)))
                        (:free (a)
                               (svl::4veclist-fix-wog
                                (rp-evlt-lst
                                 (cddr (mv-nth 0
                                               (apply$-of-adder-fncs-meta-aux (cadr (caddr term)))))
                                 a)))
                        (:free (a)(svl::4veclist-fix-wog
                                   (rp-evlt-lst
                                    (cdr (mv-nth 0
                                                 (apply$-of-adder-fncs-meta-aux (cadr (caddr term)))))
                                    a)))
                        (:free (a)(svl::4veclist-fix-wog
                                   (cdr
                                    (rp-evlt-lst
                                     (cddr (mv-nth 0
                                                   (apply$-of-adder-fncs-meta-aux (cadr (caddr term)))))
                                     a))))
                        (:free (a)
                               (svl::4veclist-fix-wog
                                (rp-evlt-lst
                                 (cdddr (mv-nth 0
                                                (apply$-of-adder-fncs-meta-aux (cadr (caddr term)))))
                                 a))))
               :in-theory (e/d* (s-spec-when-bit-listp
                                 c-spec-when-bit-listp
                                 ha-s-chain-when-bit-listp
                                 ha-c-chain-when-bit-listp
                                 apply$-of-adder-fncs-meta-aux-is-correct
                                 ;;FA-S-CHAIN
                                 ;;HA+1-C-CHAIN
                                 ;;fA-c-CHAIN
                                 regular-eval-lemmas
                                 regular-eval-lemmas-with-ex-from-rp)
                                (rp-evlt-lst-of-cons
                                 (:rewrite str::coerce-to-list-removal)
                                 (:rewrite str::coerce-to-string-removal)
                                 (:definition str::fast-string-append)
                                 ;;(:definition rp-trans-lst)
                                 (:definition string-append)
                                 (:definition valid-sc)
                                 (:definition valid-sc-subterms)
                                 ;;rp-trans-lst

                                 rp-termp
                                 eval-and-all
                                 svl::4veclist-fix-wog-is-4veclist-fix
                                 rp-trans)))
              (and stable-under-simplificationp
                   '(:use ((:instance apply$-of-adder-fncs-meta-aux-is-all-bitp
                                      (args-term (cadr (caddr term)))
                                      (a acl2::unbound-free-env)))))))

    (rp::disable-rules '(svl::4veclist-fix-wog
                         sv::4veclist-fix
                         svl::4veclist-fix-wog-is-4veclist-fix))

    )

  (rp::add-meta-rule
   :meta-fnc apply$-of-adder-fncs-meta
   :trig-fnc apply$
   :formula-checks find-adders-in-svex-formula-checks
   :valid-syntaxp t
   :returns (mv term dont-rw)
   :hints (("Goal"
            :in-theory (e/d ()
                            ())))))

#|
(define rewrite-adders-in-svex-alist ((svex-alist sv::Svex-alist-p))
:Returns (res sv::Svex-alist-p :hyp (sv::Svex-alist-p svex-alist))
(b* ((- (cw "Starting: rp::rewrite-adders-in-svex-alist. ~%"))

(- (time-tracker :rewrite-adders-in-svex :end))
(- (time-tracker :rewrite-adders-in-svex :init
:times '(1 2 3 4 5)
:interval 5
))
(- (time-tracker :rewrite-adders-in-svex :start!))

(svex-alist (find-f/h-adders-in-svex-alist svex-alist
*find-f/h-adders-in-svex-alist-limit*
:adder-type 'fa))

;;(svex-alist (find-f/h-adders-in-svex-alist svex-alist (1- *find-f/h-adders-in-svex-alist-limit*)))

(- (cwe "resulting svex-alist after full-adders ~p0 ~%" svex-alist))

(- (time-tracker :rewrite-adders-in-svex :stop))
(- (time-tracker :rewrite-adders-in-svex :print?
:min-time 0
:msg "Search for full adder patterns took ~st secs.~%~%"))

;; ((mv pattern-alist &)
;;  (gather-adder-patterns-in-svex-alist svex-alist nil nil 1))
;; (svex-alist (replace-adder-patterns-in-svex-alist svex-alist pattern-alist 1))

(- (time-tracker :rewrite-adders-in-svex :end))
(- (time-tracker :rewrite-adders-in-svex :init
:times '(1 2 3 4 5)
:interval 5
))
(- (time-tracker :rewrite-adders-in-svex :start!))
;;(- (cw "- Searching for other adders (e.g., half-adder) now.~%"))
;; ((mv pattern-alist &)
;;  (gather-adder-patterns-in-svex-alist svex-alist nil nil 2))
;; (svex-alist (replace-adder-patterns-in-svex-alist svex-alist pattern-alist 2))
(svex-alist (find-f/h-adders-in-svex-alist svex-alist
*find-f/h-adders-in-svex-alist-limit*
:adder-type 'ha))
(- (clear-memoize-table 'replace-adder-patterns-in-svex))
;;(- (fast-alist-free pattern-alist))
(- (time-tracker :rewrite-adders-in-svex :stop))
(- (time-tracker :rewrite-adders-in-svex :print?
:min-time 0
:msg "Search for other adder patterns took ~st secs.~%~%"))

(- (cw "Finished: rp::rewrite-adders-in-svex-alist.~%"))

)
svex-alist)
///
(defret <fn>-is-correct
(implies (and (force (sv::svex-alist-p svex-alist))
(force (warrants-for-adder-pattern-match)))
(equal (sv::svex-alist-eval$ res env)
(sv::svex-alist-eval$ svex-alist env)))
:hints (("Goal"
:in-theory (e/d () ())))))|#

;; (define rewrite-adders-in-svex ((svex sv::Svex-p))
;;   :Returns (res sv::Svex-p :hyp (sv::svex-p svex))
;;   ;; It is easier to manage the simplification algo in one place. So I am using
;;   ;; rewrite-adders-in-svex-alist here as well.
;;   ;; In practice, I don't expect this function to be ever used.
;;   (b* ((svex-alist (acons 'res svex nil))
;;        (svex-alist (rewrite-adders-in-svex-alist svex-alist)))
;;     (if (and (consp svex-alist) (consp (car svex-alist))) ;; for guards
;;         (cdar svex-alist)
;;       svex))
;;   ///
;;   (defret <fn>-is-correct
;;     (implies (and (force (sv::svex-p svex))
;;                   (force (warrants-for-adder-pattern-match)))
;;              (equal (sv::svex-eval$ res env)
;;                     (sv::svex-eval$ svex env)))
;;     :fn rewrite-adders-in-svex
;;     :hints (("Goal"
;;              :Expand ((sv::svex-alist-eval$
;;                        (rewrite-adders-in-svex-alist (list (cons 'res svex)))
;;                        env))
;;              :use ((:instance rewrite-adders-in-svex-alist-is-correct
;;                               (svex-alist (LIST (CONS 'RES SVEX)))))
;;              :in-theory (e/d (sv::svex-alist-eval$
;;                               SV::SVEX-ALIST-EVAL)
;;                              (rewrite-adders-in-svex-alist-is-correct))))))

;; (def-rp-rule trigger-rewrite-adders-in-svex-alist
;;   (implies (and (force (sv::svex-alist-p alist))
;;                 (force (warrants-for-adder-pattern-match))
;;                 (force (sv::svex-alist-no-foreign-op-p alist)))
;;            ;; svex-alist-eval-meta-w/o-svexl should return wrapped with identity
;;            (equal (identity (sv::svex-alist-eval alist env))
;;                   (sv::svex-alist-eval$
;;                    (rewrite-adders-in-svex-alist
;;                     alist)
;;                    env)))
;;   :disabled t ;; should be enabled in the defthmrp-multiplier macro
;;   :hints (("Goal"
;;            ;; :use ((:instance svl::svex-alist-reduce-w/-env-correct
;;            ;;                  (svl::Svex-alist alist)
;;            ;;                  (svl::env nil)
;;            ;;                  (svl::env-term ''nil)))
;;            :in-theory (e/d () ()))))

(defmacro defthmrp-multiplier (&rest args)
  `(make-event
    (b* ((args ',args)
         (then-fgl (cdr (extract-keyword-from-args :then-fgl args)))
         (args (remove-keywords-from-args '(:then-fgl) args)))
      `(encapsulate
         nil

         (local
          (disable-rules '((:meta svl::svex-alist-eval-meta
                                  .
                                  sv::svex-alist-eval))))

         (local
          (enable-rules '(;;(:rewrite trigger-rewrite-adders-in-svex-alist)
                          (:meta rewrite-adders-in-svex-alist
                                 .
                                 sv::svex-alist-eval))))
         (defthm-with-temporary-warrants
           ,@args
           :fns ,*adder-fncs*
           :defthm-macro ,(if then-fgl 'defthmrp-then-fgl 'defthmrp)
           )))))

;;;;;

(defun remove-keywords-from-args (keywords args)
  (if (or (atom args)
          (atom (cdr args)))
      args
    (if (member-equal (car args) keywords)
        (remove-keywords-from-args keywords (cddr args))
      (cons (car args)
            (remove-keywords-from-args keywords (cdr args))))))

(defwarrant str::fast-string-append)

(defthmd car-and-cdr-when-not-consp
  (implies (not (consp x))
           (and (equal (car x) nil)
                (equal (cdr x) nil))))

(progn
  (defun defthm-with-temporary-warrants-fn (thm-name thm-body args
                                                     state)
    (declare (xargs :stobjs state
                    :mode :program))
    (b* ((fns (cdr (extract-keyword-from-args :fns args)))
         (defthm-macro (extract-keyword-from-args :defthm-macro args))
         (defthm-macro (If defthm-macro (cdr defthm-macro) 'defthm))
         (args (remove-keywords-from-args '(:defthm-macro :fns) args))
         (local-thm-name
          (intern-in-package-of-symbol (str::cat (symbol-name thm-name)
                                                 "-LOCAL-WITH-TEMP-WARRANTS")
                                       thm-name))

         (all-badges (cdr (assoc-equal :BADGE-USERFN-STRUCTURE
                                       (table-alist 'acl2::badge-table (w state)))))

         (- (loop$ for x in fns always
                   (or (assoc-equal x all-badges)
                       (hard-error 'warrant-check
                                   "Warrant cannot be found for ~p0. Please call (defwarrant ~p0) (or pass its actual function name, not its macro alias).~%"
                                   (list (cons #\0 x))))))

         (- (loop$ for x in fns
                   always
                   (or (equal (third (caddr (assoc-equal x all-badges)))
                              1)
                       (hard-error 'return-count-check
                                   "Right now, this program only supports functions that return only one value. However, ~p0 violates that.~%"
                                   (list (cons #\0 x))))))

         (my-badge-userfn-body
          (loop$ for x in fns
                 collect
                 `((eq fn ',x)
                   ',(caddr (assoc-equal x all-badges)))))

         ;;(- (cw "my-badge-userfn-body: ~p0~%" my-badge-userfn-body))

         (warrant-hyps (loop$ for x in fns collect
                              `(,(intern-in-package-of-symbol
                                  (str::cat "APPLY$-WARRANT-"
                                            (symbol-name x))
                                  x))))
         (my-apply$-userfn-body
          (loop$ for x in fns
                 collect
                 `((eq fn ',x)
                   (ec-call
                    (,x
                     ,@(loop$ for i
                              from 0 to (1- (second (caddr (assoc-equal x all-badges))))
                              collect
                              `(nth ,i args)))))))

         (warrant-bindings-for-hints
          (loop$ for x in warrant-hyps collect
                 (append x '((lambda () t)))))

         )
      `(encapsulate
         nil
         (local
          (,defthm-macro ,local-thm-name
            (implies (and ,@warrant-hyps)
                     ,thm-body)
            ,@args))

         (with-output :off :all :on (error)
           (local
            (defun my-badge-userfn (fn)
              (declare (xargs :guard t))
              (cond ,@my-badge-userfn-body))))

         (with-output :off :all :on (error)
           (local
            (defun my-apply$-userfn (fn args)
              (declare (xargs :guard (True-listp args)))
              (cond ,@my-apply$-userfn-body))))

         (with-output
           :off :all
           :gag-mode t
           :on (summary error)
           (defthm ,thm-name
             ,thm-body
             :otf-flg t
             :hints (("Goal"
                      :use ((:functional-instance
                             ,local-thm-name
                             (apply$-userfn my-apply$-userfn)
                             (badge-userfn my-badge-userfn)
                             ,@warrant-bindings-for-hints
                             ))

                      :expand ((:free (x y)
                                      (nth x y))
                               (:free (x y)
                                      (take x y)))
                      :in-theory
                      (union-theories
                       (theory 'minimal-theory)
                       '(car-and-cdr-when-not-consp
                         my-apply$-userfn
                         my-badge-userfn
                         not
                         zp
                         (:definition nth)
                         take
                         car-cons
                         cdr-cons
                         (:executable-counterpart acl2::apply$-badgep)
                         (:executable-counterpart car)
                         (:executable-counterpart cdr)
                         (:executable-counterpart equal)
                         (:executable-counterpart my-badge-userfn))))
                     #|(and stable-under-simplificationp
                     '(:in-theory (e/d () ())))|#
                     )))

         )))

  (defmacro defthm-with-temporary-warrants (thm-name thm-body
                                                     &rest args)
    `(make-event
      (defthm-with-temporary-warrants-fn ',thm-name ',thm-body ',args state))
    ))
