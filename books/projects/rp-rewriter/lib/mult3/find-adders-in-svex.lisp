
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

    ))

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

(defmacro create-look-for-pattern-fnc (&key name
                                            body
                                            warrant-hyps
                                            prepwork
                                            postwork
                                            good-measure-hints
                                            correct-pattern-hints
                                            (Inline 't)

                                            )
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
                  :expand ((sv::svexlist-eval$ (cdr (cadr (cadr svex)))
                                               env)
                           (sv::svexlist-eval$ (cdr svex) env)
                           (sv::svexlist-eval$ (cdr (cadr svex))
                                               env)
                           (:free (x y)
                                  (pattern-call (cons x y))))
                  :in-theory (e/d (svl::insert-4vec-bitand-into-4vec-bitor
                                   fa-c-chain
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

(defsection fa-s-chain
  (define fa-s-chain (x y z)
    :verify-guards nil
    (sv::4vec-bitxor x (sv::4vec-bitxor y z))
    ///
    (defwarrant-rp fa-s-chain)

    (def-rp-rule fa-s-chain-s-spec
      (implies (and (integerp x)
                    (integerp y)
                    (integerp z))
               (equal (fa-s-chain x y z)
                      (svl::4vec-concat$
                       1
                       (s-spec (list (logcar x) (logcar y) (logcar z)))
                       (fa-s-chain (logcdr x) (logcdr y) (logcdr z)))))
      :hints (("Goal"
               ;;:do-not-induct t
               :in-theory (e/d* (bitops::ihsext-inductions
                                 bitops::ihsext-recursive-redefs)
                                ())))))

  (defconst *fa-s-chain-rule*
    (hons-copy '(member-equal 'fa-c-chain found-patterns)))

  ;; ;;;;
  (define look-for-fa-s-chain-pattern ((svex sv::svex-p))
    :returns (res pattern-fn-call-list-p
                  :hyp (sv::svex-p svex))

    :prepwork ((create-case-match-macro fa-s-chain-pattern
                                        ('sv::bitxor ('sv::bitxor x y) z))
               (create-case-match-macro fa-s-chain-pattern-2
                                        ('sv::bitxor x ('sv::bitxor y z)))
               )
    (append (and (fa-s-chain-pattern-p svex)
                 (fa-s-chain-pattern-body
                  svex
                  (b* ((args (acl2::merge-sort-lexorder (list x y z))))
                    (list (make-pattern-fn-call
                           :fn 'fa-s-chain
                           :rule *fa-s-chain-rule*
                           :args args)))))
            (and (fa-s-chain-pattern-2-p svex)
                 (fa-s-chain-pattern-2-body
                  svex
                  (b* ((args (acl2::merge-sort-lexorder (list x y z))))
                    (list (make-pattern-fn-call
                           :fn 'fa-s-chain
                           :rule *fa-s-chain-rule*
                           :args args)))))

            )
    ///

    (defret <fn>-good-measure
      (implies (sv::Svex-p svex)
               (pattern-fn-call-list-provide-good-measure-p svex res))
      :hints (("Goal"
               :expand ((SV::SVEX-COUNT SVEX))
               :in-theory (e/d (PATTERN-FN-CALL->ARGS
                                PATTERN-FN-CALL
                                SV::SVEX-COUNT
                                SV::SVEX-CALL->ARGS
                                sv::svex-kind
                                SV::SVEXLIST-COUNT
                                pattern-fn-call-provide-good-measure-p
                                pattern-fn-call-list-provide-good-measure-p)
                               (acl2::merge-sort-lexorder)))))

    (defret <fn>-correct-pattern
      (implies (and (apply$-warrant-fa-s-chain)
                    (member-equal pattern res))
               (equal (sv::svex-eval$ (pattern-call pattern) env)
                      (sv::svex-eval$ svex env)))
      :hints (("Goal"
               :Expand ()
               :in-theory (e/d (pattern-call
                                pattern-fn-call->rule
                                pattern-fn-call->fn
                                pattern-fn-call->args
                                pattern-fn-call->extra-arg
                                fa-s-chain
                                pattern-fn-call
                                acl2::merge-sort-lexorder
                                acl2::merge-lexorder
                                sv::svex-call->fn
                                sv::svex-call->args
                                sv::svex-apply$
                                sv::svex-apply
                                sv::svexlist-eval$)
                               (acl2::merge-sort-lexorder-2
                                ;;ACL2::MERGE-SORT-LEXORDER
                                (:rewrite sv::svex-eval$-when-quote)
                                acl2::integerp-of-car-when-integer-listp
                                acl2::symbolp-of-car-when-symbol-listp
                                integer-listp)))))

    )

  )

(progn
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
                                           (in-theory (disable fa-c-chain))))
                               :body
                               (cond ((fa-c-chain-itself-pattern-p svex)
                                      (fa-c-chain-itself-pattern-body
                                       svex
                                       (and (natp m)
                                            (list (make-pattern-fn-call
                                                   :fn 'fa-c-chain
                                                   :extra-arg m
                                                   :rule nil
                                                   :args (list x y z)))))))
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
                                                                                            ('sv::bitand x2 z1)))))
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
                                                                   ('sv::bitor  ('sv::bitand y2 z2)
                                                                                ('sv::bitand x1
                                                                                             (or/xor? y1 z1)))))
                               :body
                               (and (fa-c-chain-pattern-2a-p svex)
                                    (fa-c-chain-pattern-2a-body
                                     svex
                                     (b* (((unless (or (equal or/xor? 'sv::bitor)
                                                       (equal or/xor? 'sv::bitxor)))
                                           nil)
                                          ((mv x y z valid) (look-for-fa-c-chain-pattern-aux
                                                             :x2 x1))
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
                                                                   ('sv::bitor  ('sv::bitand y2 z2)
                                                                                ('sv::bitand (or/xor? y1 z1)
                                                                                             x1))))
                               :body
                               (and (fa-c-chain-pattern-2b-p svex)
                                    (fa-c-chain-pattern-2b-body
                                     svex
                                     (b* (((unless (or (equal or/xor? 'sv::bitor)
                                                       (equal or/xor? 'sv::bitxor)))
                                           nil)
                                          ((mv x y z valid) (look-for-fa-c-chain-pattern-aux
                                                             :x2 x1))
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

  (create-look-for-pattern-fnc :name fa-c-chain-pattern-3a
                               :prepwork ((create-case-match-macro fa-c-chain-pattern-3a
                                                                   ('sv::bitor  ('sv::bitand x1
                                                                                             (or/xor? y1 z1))
                                                                                ('sv::bitand y2 z2))))
                               :body
                               (and (fa-c-chain-pattern-3a-p svex)
                                    (fa-c-chain-pattern-3a-body
                                     svex
                                     (b* (((unless (or (equal or/xor? 'sv::bitor)
                                                       (equal or/xor? 'sv::bitxor)))
                                           nil)
                                          ((mv x y z valid) (look-for-fa-c-chain-pattern-aux
                                                             :x2 x1))
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

  (create-look-for-pattern-fnc :name fa-c-chain-pattern-3b
                               :prepwork ((create-case-match-macro fa-c-chain-pattern-3b
                                                                   ('sv::bitor  ('sv::bitand (or/xor? y1 z1)
                                                                                             x1)
                                                                                ('sv::bitand y2 z2))))
                               :body
                               (and (fa-c-chain-pattern-3b-p svex)
                                    (fa-c-chain-pattern-3b-body
                                     svex
                                     (b* (((unless (or (equal or/xor? 'sv::bitor)
                                                       (equal or/xor? 'sv::bitxor)))
                                           nil)
                                          ((mv x y z valid) (look-for-fa-c-chain-pattern-aux
                                                             :x2 x1))
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
                                             (look-for-fa-c-chain-pattern-3a svex)
                                             (look-for-fa-c-chain-pattern-3b svex)
                                             (look-for-fa-c-chain-itself-pattern svex)
                                             )
                               :warrant-hyps ((apply$-warrant-fa-c-chain))
                               :inline nil))

(progn
  (define ha-s-chain (x y)
    :verify-guards nil
    (sv::4vec-bitxor x y)
    ///
    (defwarrant-rp ha-s-chain)

    (def-rp-rule ha-s-chain-to-s-spec
      (implies (and (integerp x)
                    (integerp y))
               (equal (ha-s-chain x y)
                      (svl::4vec-concat$
                       1
                       (s-spec (list (logcar x) (logcar y)))
                       (ha-s-chain (logcdr x) (logcdr y)))))
      :hints (("goal"
               :in-theory (e/d* (sv::4vec
                                 ;;bitops::ihsext-inductions
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

  (define look-for-ha-s-chain-pattern ((svex sv::svex-p))
    :returns (res pattern-fn-call-list-p
                  :hyp (sv::svex-p svex))
    :prepwork
    ((create-case-match-macro ha-s-chain-pattern
                              ('sv::bitxor x y)))
    (cond ((and (ha-s-chain-pattern-p svex)
                ;;(equal (svex-has-more-than-one-var-p svex) t)
                )
           (ha-s-chain-pattern-body
            svex
            (b* ((args (acl2::merge-sort-lexorder (list x y))))
              (list (make-pattern-fn-call
                     :fn 'ha-s-chain
                     :rule *ha-s-chain-rule*
                     :args args))))))
    ///
    (defret <fn>-good-measure
      (implies (sv::Svex-p svex)
               (pattern-fn-call-list-provide-good-measure-p svex res))
      :hints (("Goal"
               :expand ((SV::SVEX-COUNT SVEX))
               :in-theory (e/d (SV::SVEX-COUNT
                                PATTERN-FN-CALL
                                PATTERN-FN-CALL->ARGS
                                SV::SVEX-CALL->ARGS
                                sv::svex-kind
                                SV::SVEXLIST-COUNT
                                pattern-fn-call-provide-good-measure-p
                                pattern-fn-call-list-provide-good-measure-p)
                               (acl2::merge-sort-lexorder)))))

    (defret <fn>-correct-pattern
      (implies (and (apply$-warrant-ha-s-chain)
                    (member-equal pattern res))
               (equal (sv::svex-eval$ (pattern-call pattern) env)
                      (sv::svex-eval$ svex env)))
      :hints (("goal"
               :expand ()
               :in-theory (e/d (ha-s-chain
                                PATTERN-CALL
                                PATTERN-FN-CALL->ARGS
                                PATTERN-FN-CALL->EXTRA-ARG
                                PATTERN-FN-CALL->FN
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

                                default-cdr
                                integer-listp)))))

    ))

(progn
  (define ha-c-chain (method x y)
    :verify-guards nil
    (cond
     ((= method 10)
      (sv::4vec-bitand x
                       (sv::4vec-bitxor (sv::4vec-bitxor 1 x)
                                        y)))
     ((= method 11)
      (sv::4vec-bitand y
                       (sv::4vec-bitxor (sv::4vec-bitxor 1 y)
                                        x)))
     (t
      (sv::4vec-bitand x y)))
    ///
    (defwarrant-rp ha-c-chain)

    (def-rp-rule ha-c-chain-to-c-spec
      (implies (and (integerp x)
                    (integerp y)
                    (equal method 0))
               (equal (ha-c-chain method x y)
                      (svl::4vec-concat$
                       1
                       (c-spec (list (logcar x) (logcar y)))
                       (ha-c-chain method (logcdr x) (logcdr y)))))
      :hints (("Goal"
               :in-theory (e/d* (;;bitops::ihsext-inductions
                                 bitops::ihsext-recursive-redefs)
                                ()))))
    )

  (defconst *ha-c-chain-rule*
    (hons-copy '(member-equal 'ha-s-chain found-patterns)))

  (define look-for-ha-c-chain-pattern ((svex sv::svex-p))
    :returns (res pattern-fn-call-list-p
                  :hyp (sv::svex-p svex))
    :prepwork
    ((create-case-match-macro ha-c-chain-pattern
                              ('sv::bitand x y))
     (create-case-match-macro ha-c-chain-pattern-1
                              ('sv::bitand x
                                           ('sv::bitxor 1 ('sv::bitxor x y)))))
    (append
     (and
      (ha-c-chain-pattern-1-p svex)
      (ha-c-chain-pattern-1-body
       svex
       (b* ((args (acl2::merge-sort-lexorder (list x y))))
         (list (make-pattern-fn-call
                :fn 'ha-c-chain
                :rule *ha-c-chain-rule*
                :extra-arg (cond ((equal (car args) x)
                                  10)
                                 ((equal (cadr args) x)
                                  11))
                :args args)))))
     (and
      (ha-c-chain-pattern-p svex)
      (ha-c-chain-pattern-body
       svex
       (b* ((args (acl2::merge-sort-lexorder (list x y))))
         (list (make-pattern-fn-call
                :fn 'ha-c-chain
                :rule *ha-c-chain-rule*
                :extra-arg 0
                :args args))))))
    ///
    (defret <fn>-good-measure
      (implies (sv::Svex-p svex)
               (pattern-fn-call-list-provide-good-measure-p svex res))
      :hints (("Goal"
               :expand ((SV::SVEX-COUNT SVEX))
               :in-theory (e/d (SV::SVEX-COUNT
                                PATTERN-FN-CALL
                                PATTERN-FN-CALL->ARGS
                                SV::SVEX-CALL->ARGS
                                sv::svex-kind
                                SV::SVEXLIST-COUNT
                                pattern-fn-call-provide-good-measure-p
                                pattern-fn-call-list-provide-good-measure-p)
                               (acl2::merge-sort-lexorder)))))

    (defret <fn>-correct-pattern
      (implies (and (apply$-warrant-ha-c-chain)
                    (member-equal pattern res))
               (equal (sv::svex-eval$ (pattern-call pattern) env)
                      (sv::svex-eval$ svex env)))
      :hints (("goal"
               :expand ((:free (x)
                               (NTH 1 x)))
               :in-theory (e/d (SV::SVEXLIST-EVAL$
                                SV::4VECLIST-NTH-SAFE
                                nth
                                ha-c-chain
                                PATTERN-FN-CALL->FN
                                PATTERN-FN-CALL->EXTRA-ARG
                                PATTERN-FN-CALL->ARGS
                                PATTERN-CALL
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

                                default-cdr
                                integer-listp)))))))

(progn
  (define ha+1-c-chain (x y)
    :verify-guards nil
    (sv::4vec-bitor x y)
    ///
    (defwarrant-rp ha+1-c-chain)

    (def-rp-rule ha+1-c-chain-c-spec
      (implies (and (integerp x)
                    (integerp y))
               (equal (ha+1-c-chain x y)
                      (svl::4vec-concat$
                       1
                       (c-spec (list (logcar x) (logcar y) 1))
                       (ha+1-c-chain (logcdr x) (logcdr y)))))
      :hints (("goal"
               ;;:do-not-induct t
               :in-theory (e/d* (bitops::ihsext-inductions
                                 bitops::ihsext-recursive-redefs)
                                ())))))

  (defconst *ha+1-c-chain-rule*
    (hons-copy '(or (member-equal 'ha+1-s-chain found-patterns)
                    (member-equal 'ha+1-s found-patterns))))

  (define look-for-ha+1-c-chain-pattern ((svex sv::svex-p))
    :returns (res pattern-fn-call-list-p
                  :hyp (sv::svex-p svex))

    :prepwork
    ((create-case-match-macro ha+1-c-chain-pattern
                              ('sv::bitor x y))
     )

    (cond ((ha+1-c-chain-pattern-p svex)
           (ha+1-c-chain-pattern-body
            svex
            (b* ((args (acl2::merge-sort-lexorder (list x y))))
              (list (make-pattern-fn-call
                     :fn 'ha+1-c-chain
                     :rule *ha+1-c-chain-rule*
                     :args args)))))
          )
    ///
    (defret <fn>-good-measure
      (implies (sv::svex-p svex)
               (pattern-fn-call-list-provide-good-measure-p svex res))
      :hints (("goal"
               :expand ((sv::svex-count svex)
                        (SV::SVEXLIST-COUNT (CDR SVEX))
                        (SV::SVEX-COUNT (CADR SVEX))
                        (sv::svexlist-count (cdr (cadr svex))))
               :in-theory (e/d (pattern-fn-call
                                PATTERN-FN-CALL->ARGS
                                sv::svex-count
                                sv::svex-call->args
                                sv::svex-kind
                                sv::svexlist-count
                                pattern-fn-call-provide-good-measure-p
                                pattern-fn-call-list-provide-good-measure-p)
                               (acl2::merge-sort-lexorder)))))

    (defret <fn>-correct-pattern
      (implies (and (apply$-warrant-ha+1-c-chain)
                    (member-equal pattern res))
               (equal (sv::svex-eval$ (pattern-call pattern) env)
                      (sv::svex-eval$ svex env)))
      :hints (("goal"
               :expand ((SV::SVEXLIST-EVAL$ (CDR (CADR (CADR SVEX)))
                                            ENV)
                        (SV::SVEXLIST-EVAL$ (CDR SVEX) ENV)
                        (SV::SVEXLIST-EVAL$ (CDR (CADR SVEX))
                                            ENV))
               :in-theory (e/d (svl::insert-4vec-bitand-into-4vec-bitor
                                ha+1-c-chain
                                pattern-fn-call
                                PATTERN-FN-CALL->FN
                                PATTERN-FN-CALL->EXTRA-ARG
                                PATTERN-FN-CALL->ARGS
                                PATTERN-CALL
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

                                default-cdr
                                integer-listp)))))))

(progn
  (define ha+1-s-chain (x y)
    :verify-guards nil
    (sv::4vec-bitnot (sv::4vec-bitxor x y))
    ///
    (defwarrant-rp ha+1-s-chain)

    (def-rp-rule ha+1-s-chain-to-s-spec
      (implies (and (integerp x)
                    (integerp y))
               (equal (ha+1-s-chain x y)
                      (svl::4vec-concat$
                       1
                       (s-spec (list (logcar x) (logcar y) 1))
                       (ha+1-s-chain (logcdr x) (logcdr y)))))
      :hints (("Goal"
               :in-theory (e/d* (sv::4vec
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

  (define ha+1-s (x y)
    :verify-guards nil
    (sv::4vec-bitxor 1 (sv::4vec-bitxor x y))
    ///
    (defwarrant-rp ha+1-s)

    (def-rp-rule ha+1-s-to-s-spec
      (implies (and (integerp x)
                    (integerp y))
               (equal (ha+1-s x y)
                      (svl::4vec-concat$
                       1
                       (s-spec (list (logcar x) (logcar y) 1))
                       (svl::4vec-rsh 1 (sv::4vec-bitxor 0 (sv::4vec-bitxor x y))))))
      :hints (("Goal"
               ;; :do-not-induct t
               :in-theory (e/d* (
                                 HA+1-S-CHAIN
                                 sv::4vec
                                 ha-s-chain
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
                                 HA+1-S-CHAIN-TO-S-SPEC
                                 SVL::EQUAL-OF-4VEC-CONCAT-WITH-SIZE=1
                                 logand
                                 ))))))

  (define look-for-ha+1-s-chain-pattern ((svex sv::svex-p))
    :returns (res pattern-fn-call-list-p
                  :hyp (sv::svex-p svex))
    :prepwork
    ((create-case-match-macro ha+1-s-chain-pattern
                              ('sv::bitnot ('sv::bitxor x y)))
     (create-case-match-macro ha+1-s-chain-pattern-2
                              ('sv::bitxor ('sv::bitxor x y) z))
     (create-case-match-macro ha+1-s-chain-pattern-3
                              ('sv::bitxor z ('sv::bitxor x y)))

     (define look-for-ha+1-s-chain-pattern-aux (x y z)
       :returns (mv x y valid)
       :enabled t
       (cond ((equal x 1)
              (mv y z t))
             ((equal y 1)
              (mv x z t))
             ((equal z 1)
              (mv x y t))
             (t (mv 0 0 nil)))))

    (cond ((and (ha+1-s-chain-pattern-p svex)
                ;;(equal (svex-has-more-than-one-var-p svex) t)
                )
           (ha+1-s-chain-pattern-body
            svex
            (b* ((args (acl2::merge-sort-lexorder (list x y))))
              (list (make-pattern-fn-call
                     :fn 'ha+1-s-chain
                     :rule *ha+1-s-chain-rule*
                     :args args)))))
          (t (append
              (and (ha+1-s-chain-pattern-2-p svex)
                   ;;(equal (svex-has-more-than-one-var-p svex) t)
                   (ha+1-s-chain-pattern-2-body
                    svex
                    (b* (((mv x y valid) (look-for-ha+1-s-chain-pattern-aux x y z))
                         ((unless valid) nil)
                         (args (acl2::merge-sort-lexorder (list x y))))
                      (list (make-pattern-fn-call
                             :rule *ha+1-s-chain-rule*
                             :fn 'ha+1-s
                             :args args)))))
              (and (ha+1-s-chain-pattern-3-p svex)
                   ;;(equal (svex-has-more-than-one-var-p svex) t)
                   (ha+1-s-chain-pattern-3-body
                    svex
                    (b* (((mv x y valid) (look-for-ha+1-s-chain-pattern-aux x y z))
                         ((unless valid) nil)
                         (args (acl2::merge-sort-lexorder (list x y))))
                      (list (make-pattern-fn-call
                             :fn 'ha+1-s
                             :rule *ha+1-s-chain-rule*
                             :args args))))))
             ))
    ///
    (defret <fn>-good-measure
      (implies (sv::Svex-p svex)
               (pattern-fn-call-list-provide-good-measure-p svex res))
      :hints (("Goal"
               :expand ((SV::SVEX-COUNT SVEX))
               :in-theory (e/d (SV::SVEX-COUNT
                                PATTERN-FN-CALL
                                PATTERN-FN-CALL->FN
                                PATTERN-FN-CALL->EXTRA-ARG
                                PATTERN-FN-CALL->ARGS
                                SV::SVEX-CALL->ARGS
                                sv::svex-kind
                                SV::SVEXLIST-COUNT
                                pattern-fn-call-provide-good-measure-p
                                pattern-fn-call-list-provide-good-measure-p)
                               (acl2::merge-sort-lexorder)))))

    (defret <fn>-correct-pattern
      (implies (and (apply$-warrant-ha+1-s-chain)
                    (apply$-warrant-ha+1-s)
                    (member-equal pattern res))
               (equal (sv::svex-eval$ (pattern-call pattern) env)
                      (sv::svex-eval$ svex env)))
      :hints (("goal"
               :expand ()
               :in-theory (e/d (ha+1-s-chain
                                ha+1-s
                                pattern-call
                                pattern-fn-call->fn
                                pattern-fn-call->extra-arg
                                pattern-fn-call->args
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

                                default-cdr
                                integer-listp)))))

    ))

(progn
  (defun warrants-for-adder-pattern-match ()
    (and (apply$-warrant-ha-c-chain)
         (apply$-warrant-fa-c-chain)
         (apply$-warrant-ha+1-c-chain)
         (apply$-warrant-ha+1-s-chain)
         (apply$-warrant-ha+1-s)
         (apply$-warrant-ha-s-chain)
         (apply$-warrant-fa-s-chain)))

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
                (and (equal (ha-c-chain method x y)
                            (c-spec (list x y)))
                     (equal (ha-s-chain x y)
                            (s-spec (list x y)))
                     (equal (ha+1-c-chain x y)
                            (c-spec (list x y 1))))))
  :hints (("goal"
           :in-theory (e/d (fa-c-chain
                            ha-c-chain
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
             :in-theory (e/d ()
                             (pattern-call))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define register-found-adder-patterns ((pattern-fn-call-list pattern-fn-call-list-p)
                                       (pattern-alist))
  :returns (res alistp :hyp (alistp pattern-alist))
  :inline t
  ;; when a matching pattern  is found, it should be saved  in a fast-alist whose
  ;; keys are arguments, and value should be a list of all the pattern names.
  (b* (((when (atom pattern-fn-call-list)) pattern-alist)
       ((pattern-fn-call x) (car pattern-fn-call-list))

       ;;((unless (and key value)) pattern-alist)
       (entry (hons-get x.args pattern-alist))
       (pattern-alist (hons-acons x.args (cons x.fn (cdr entry)) pattern-alist)))
    (register-found-adder-patterns (cdr pattern-fn-call-list)
                                   pattern-alist)))

(acl2::defines gather-adder-patterns-in-svex
  (define gather-adder-patterns-in-svex ((x sv::svex-p)
                                         (pattern-alist )
                                         (parsed-svexes)
                                         (pass-num natp))
    :measure (sv::svex-count x)
    :returns (mv (res-pattern-alist alistp :hyp (alistp pattern-alist))
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
    :returns (mv (res-pattern-alist alistp :hyp (alistp pattern-alist))
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
        (mv pattern-alist parsed-svexes)))))

(define gather-adder-patterns-in-svex-alist ((alist sv::svex-alist-p)
                                             (pattern-alist )
                                             (parsed-svexes)
                                             (pass-num natp))
  :returns (mv (res-pattern-alist alistp :hyp (alistp pattern-alist))
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
      (mv pattern-alist parsed-svexes))))

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

(defsection find-fa-s-for-orphan-fa-c
  (define process-unmatched-fa-c-chains ((pattern-alist alistp)
                                         (collected alistp))
    ;; should return  a fast-alist  whose keys  are an  argument that  appears in
    ;; unmatched fa-c-chain pattern, and values are the remaining two args.
    :returns (unmatched-arg-alist alistp :hyp (alistp collected))
    (if (atom pattern-alist)
        collected
      (b* ((args (caar pattern-alist))
           ((unless (equal (len args) 3))
            (process-unmatched-fa-c-chains (cdr pattern-alist)
                                           collected))
           (fns (cdar pattern-alist))
           ((unless (equal fns '(fa-c-chain))
              ;;(ec-call (member-equal 'fa-c-chain fns))
              )
            ;; maybe this  should be  a member-equal  test that  says fa-c-chain
            ;; exists but fa-s-chain doesn't
            (process-unmatched-fa-c-chains (cdr pattern-alist)
                                           collected))
           (collected (hons-acons(first args) (cdr args) collected))
           (collected (hons-acons
                       (second args) (cons (car args) (cddr args))
                       collected))
           (collected (hons-acons
                       (third args) (list (car args) (cadr args))
                       collected)))
        (process-unmatched-fa-c-chains (cdr pattern-alist) collected))))

  (define find-s-from-found-c-in-svex-aux-explore1 ((svex sv::Svex-p)
                                                    (unmatched-arg-alist))
    :returns alist-entry
    (case-match svex
      (('sv::bitxor x y)
       (or (hons-get x unmatched-arg-alist)
           (hons-get y unmatched-arg-alist)
           (find-s-from-found-c-in-svex-aux-explore1 x unmatched-arg-alist)
           (find-s-from-found-c-in-svex-aux-explore1 y unmatched-arg-alist)))
      (& nil))
    ///
    (defthm car-of-hons-assoc-equal
      (implies (hons-assoc-equal x y)
               (equal (car (hons-assoc-equal x y))
                      x))
      :hints (("Goal"
               :in-theory (e/d (hons-assoc-equal) ()))))

    (defret svex-count-of-<fn>
      (implies alist-entry
               (< (sv::svex-count (car alist-entry))
                  (sv::svex-count svex)))
      :hints (("Goal"
               :Expand ((SV::SVEX-COUNT SVEX))
               :in-theory (e/d (SV::SVEX-CALL->ARGS)
                               ())))
      :rule-classes (:rewrite :linear :forward-chaining))

    (defret svex-p-of-key-from-<fn>
      (implies (and alist-entry
                    (sv::Svex-p svex))
               (sv::Svex-p (car alist-entry)))))

  (define find-s-from-found-c-in-svex-aux-explore2 ((svex sv::Svex-p)
                                                    (arg))
    :returns exists
    (case-match svex
      (('sv::bitxor x y)
       (or (equal x arg)
           (equal y arg)
           (find-s-from-found-c-in-svex-aux-explore2 x arg)
           (find-s-from-found-c-in-svex-aux-explore2 y arg)))
      (& nil))
    ///
    (defret svex-count-of-<fn>
      (implies exists
               (< (sv::svex-count arg)
                  (sv::svex-count svex)))
      :hints (("Goal"
               :expand (SV::SVEX-COUNT SVEX)
               :in-theory (e/d (SV::SVEX-CALL->ARGS) ())))
      :rule-classes (:rewrite :linear :forward-chaining))

    (defret <fn>-implies-explore2
      (implies alist-entry
               (find-s-from-found-c-in-svex-aux-explore2 svex (car alist-entry)))
      :fn find-s-from-found-c-in-svex-aux-explore1
      :hints (("Goal"
               :in-theory (e/d (find-s-from-found-c-in-svex-aux-explore1) ()))))

    (defret svex-p-of-arg-of-<fn>
      (implies (and exists
                    (sv::Svex-p svex))
               (sv::Svex-p arg))
      :rule-classes (:forward-chaining :rewrite))

    )

  (define find-s-from-found-c-in-svex-aux-explore-remove ((svex sv::Svex-p)
                                                          (arg))
    :returns (res sv::Svex-p :hyp (sv::Svex-p svex))
    (case-match svex
      (('sv::bitxor x y)
       (cond ((equal x arg)
              y)
             ((equal y arg)
              x)
             ((find-s-from-found-c-in-svex-aux-explore2 x arg)
              (sv::Svex-call 'sv::bitxor
                             (hons-list
                              (find-s-from-found-c-in-svex-aux-explore-remove x arg)
                              y)))
             ((find-s-from-found-c-in-svex-aux-explore2 y arg)
              (sv::Svex-call 'sv::bitxor
                             (hons-list
                              x
                              (find-s-from-found-c-in-svex-aux-explore-remove y arg))))
             (t ;; should never come here..
              svex)))
      (& ;; should never come here.
       svex
       ))
    ///
    (defret svex-count-of-<fn>
      (implies (find-s-from-found-c-in-svex-aux-explore2 svex arg)
               (< (sv::svex-count res)
                  (sv::svex-count svex)))
      :hints (("goal"
               :expand ((sv::svex-count svex)
                        (:free (x) (sv::svex-count (cons 'sv::bitxor x))))
               :in-theory (e/d (sv::svex-call
                                sv::svexlist-count
                                sv::svex-call->args
                                find-s-from-found-c-in-svex-aux-explore2)
                               ())))
      :rule-classes (:rewrite :linear :forward-chaining))

    (defret <fn>-correct
      (implies (and (sv::svex-p svex)
                    (find-s-from-found-c-in-svex-aux-explore2 svex arg))
               (equal (sv::4vec-bitxor (sv::svex-eval$ arg env)
                                       (sv::svex-eval$ res env))
                      (sv::svex-eval$ svex env)))
      :hints (("Goal"
               :expand ((:free (x)
                               (SV::SVEX-APPLY 'SV::BITXOR x)))
               :in-theory (e/d (SV::SVEX-CALL->ARGS
                                SV::4VECLIST-NTH-SAFE
                                SV::SVEX-CALL->FN
                                find-s-from-found-c-in-svex-aux-explore2)
                               ()))))

    )

  (define find-s-from-found-c-in-svex-aux-counter ()
    nil
    ///
    (profile 'find-s-from-found-c-in-svex-aux-counter))

  (defines find-s-from-found-c-in-svex-aux
    :verify-guards nil

    (define find-s-from-found-c-in-svex-aux ((svex sv::svex-p)
                                             (unmatched-arg-alist alistp))
      :measure (sv::Svex-count svex)
      :returns (res sv::Svex-p :hyp (sv::Svex-p svex))
      (sv::svex-case
       svex
       :quote svex
       :var   svex
       :call
       (cond ((ha-s-chain-pattern-p svex)
              ;; possible fa-s-chain here.
              (b* (;; first see if anything in the xor chain appears as an argument to an orphan fa-c
                   ;; explore1-res will be list of all 3 args
                   (explore1-res (find-s-from-found-c-in-svex-aux-explore1 svex unmatched-arg-alist))

                   ((unless explore1-res)
                    (sv::svex-call svex.fn
                                   (find-s-from-found-c-in-svexlist-aux svex.args
                                                                        unmatched-arg-alist)))

                   ((cons match args) explore1-res)
                   ((Unless (and (consp args) ;; sanity check. Make sure there are exactly two args
                                 (consp (cdr args))
                                 (atom (cddr args))))
                    (sv::svex-call svex.fn
                                   (find-s-from-found-c-in-svexlist-aux svex.args
                                                                        unmatched-arg-alist)))
                   ((mv arg1 arg2) (mv (car args) (cadr args)))

                   ;; if the pattern  can be found within only one  node of the
                   ;; current svex,  don't match  the pattern  here but  in the
                   ;; subterms in order not to move arguments too much within bitxor.
                   ((when (or* (and* (find-s-from-found-c-in-svex-aux-explore2 (cadr svex) match)
                                     (find-s-from-found-c-in-svex-aux-explore2 (cadr svex) arg1)
                                     (find-s-from-found-c-in-svex-aux-explore2 (cadr svex) arg2))
                               (and* (find-s-from-found-c-in-svex-aux-explore2 (caddr svex) match)
                                     (find-s-from-found-c-in-svex-aux-explore2 (caddr svex) arg1)
                                     (find-s-from-found-c-in-svex-aux-explore2 (caddr svex) arg2))))
                    (sv::svex-call svex.fn
                                   (find-s-from-found-c-in-svexlist-aux svex.args unmatched-arg-alist)))

                   ;; look for the other args in the svex
                   (rest-of-bitxor (find-s-from-found-c-in-svex-aux-explore-remove svex match))
                   (found1 (find-s-from-found-c-in-svex-aux-explore2 rest-of-bitxor arg1))
                   ((unless found1)
                    (sv::svex-call svex.fn
                                   (find-s-from-found-c-in-svexlist-aux svex.args unmatched-arg-alist)))

                   (rest-of-bitxor (find-s-from-found-c-in-svex-aux-explore-remove rest-of-bitxor arg1))
                   (found2 (find-s-from-found-c-in-svex-aux-explore2 rest-of-bitxor arg2))
                   ((unless found2)
                    (sv::svex-call svex.fn
                                   (find-s-from-found-c-in-svexlist-aux svex.args unmatched-arg-alist)))
                   (rest-of-bitxor (find-s-from-found-c-in-svex-aux-explore-remove rest-of-bitxor arg2))
                   (- (find-s-from-found-c-in-svex-aux-counter))
                   (result
                    (sv::Svex-call 'sv::bitxor
                                   (hons-list
                                    (find-s-from-found-c-in-svex-aux rest-of-bitxor unmatched-arg-alist)
                                    ;; state the xor pattern so that it can be caught later.
                                    (sv::svex-call 'sv::Bitxor
                                                   (Hons-list
                                                    (sv::Svex-call
                                                     'sv::bitxor
                                                     (hons-list
                                                      (find-s-from-found-c-in-svex-aux match unmatched-arg-alist)
                                                      (find-s-from-found-c-in-svex-aux arg1 unmatched-arg-alist)))
                                                    (find-s-from-found-c-in-svex-aux arg2 unmatched-arg-alist)))
                                    #|(if (or (equal *fa-c-chain-rule* t) ;; depending on the *fa-c-chain-rule* either constract fa-s-chain now,
                                    ;; or state the xor pattern so that it can be caught later.
                                    (equal *fa-c-chain-rule* ''t))
                                    (sv::svex-call 'fa-s-chain
                                    (Hons-list
                                    (find-s-from-found-c-in-svex-aux match unmatched-arg-alist)
                                    (find-s-from-found-c-in-svex-aux arg1 unmatched-arg-alist)
                                    (find-s-from-found-c-in-svex-aux arg2 unmatched-arg-alist)))
                                    (sv::svex-call 'sv::Bitxor
                                    (Hons-list
                                    (sv::Svex-call
                                    'sv::bitxor
                                    (hons-list
                                    (find-s-from-found-c-in-svex-aux match unmatched-arg-alist)
                                    (find-s-from-found-c-in-svex-aux arg1 unmatched-arg-alist)))
                                    (find-s-from-found-c-in-svex-aux arg2 unmatched-arg-alist))))|#)))
                   ;;(- (rp::cwe "in find-s-from-found-c-in-svex-aux: svex:~p0 result: ~p1 ~%" svex result))
                   )
                result))
             (t (sv::svex-call svex.fn
                               (find-s-from-found-c-in-svexlist-aux svex.args
                                                                    unmatched-arg-alist))))))
    (define find-s-from-found-c-in-svexlist-aux ((lst sv::Svexlist-p)
                                                 (unmatched-arg-alist alistp))
      :measure (sv::svexlist-count lst)
      :returns (res-lst sv::Svexlist-p :hyp (sv::Svexlist-p lst))
      (if (atom lst)
          nil
        (hons (find-s-from-found-c-in-svex-aux (car lst) unmatched-arg-alist)
              (find-s-from-found-c-in-svexlist-aux (cdr lst) unmatched-arg-alist))))
    ///

    (verify-guards find-s-from-found-c-in-svex-aux
      :hints (("Goal"
               :do-not-induct t
               :in-theory (e/d () ()))))

    (memoize 'find-s-from-found-c-in-svex-aux :condition '(eq (sv::svex-kind svex) :call))

    (defret-mutual <fn>-correct
      (defret <fn>-is-correct
        (implies (and (force (sv::svex-p svex))
                      (force (warrants-for-adder-pattern-match)))
                 (equal (sv::svex-eval$ res env)
                        (sv::svex-eval$ svex env)))
        :fn find-s-from-found-c-in-svex-aux)
      (defret <fn>-is-correct
        (implies (and (force (sv::svexlist-p lst))
                      (force (warrants-for-adder-pattern-match)))
                 (equal (sv::svexlist-eval$ res-lst env)
                        (sv::svexlist-eval$ lst env)))
        :fn find-s-from-found-c-in-svexlist-aux)
      :hints (("Goal"
               :expand ((:free (x) (sv::svex-apply$ 'fa-s-chain x))
                        (:free (x) (sv::svex-apply$ 'sv::BITXOR x))
                        (:free (x) (sv::svex-apply 'sv::BITXOR x))
                        (FIND-S-FROM-FOUND-C-IN-SVEXLIST-AUX LST UNMATCHED-ARG-ALIST)
                        (find-s-from-found-c-in-svex-aux svex unmatched-arg-alist))
               :in-theory (e/d (FA-S-CHAIN) ()))))
    )

  (define find-s-from-found-c-in-svex-alist-aux ((alist sv::svex-alist-p)
                                                 (unmatched-arg-alist alistp))
    :returns (res sv::Svex-alist-p :hyp (sv::Svex-alist-p alist))
    (if (atom alist)
        alist
      (acons (caar alist)
             (find-s-from-found-c-in-svex-aux (cdar alist) unmatched-arg-alist)
             (find-s-from-found-c-in-svex-alist-aux (cdr alist) unmatched-arg-alist)))
    ///
    (defret <fn>-is-correct
      (implies (and (force (sv::svex-alist-p alist))
                    (force (warrants-for-adder-pattern-match)))
               (equal (sv::svex-alist-eval$ res env)
                      (sv::svex-alist-eval$ alist env)))
      :hints (("Goal"
               :in-theory (e/d (sv::svex-alist-eval$) ())))))

  (defsection alistp-of-of-fast-alist-clean
    (defthm alistp-of-of-FAST-ALIST-FORK
      (implies (and (alistp x)
                    (alistp last))
               (alistp (FAST-ALIST-FORK x last))))

    (defthm alistp-of-last
      (implies (alistp x)
               (alistp (last x))))

    (defthm alistp-of-cdr
      (implies (alistp x)
               (alistp (cdr x))))

    (defthm alistp-of-of-fast-alist-clean
      (implies (alistp x)
               (alistp (fast-alist-clean x)))))

  (defconst *find-full-adders-in-svex-alist-limit*
    6)

  (define pattern-alist-has-complete-full-adder-patterns-p ((pattern-alist alistp))
    (if (atom pattern-alist)
        0
      (+ (if (subsetp-equal '(fa-c-chain fa-s-chain)
                            (true-list-fix (cdar pattern-alist)))
             1 0)
         (pattern-alist-has-complete-full-adder-patterns-p (cdr pattern-alist)))))

  (define find-full-adders-in-svex-alist ((svex-alist sv::svex-alist-p)
                                          (limit natp))
    :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p svex-alist))
    :measure (nfix limit)
    (b* (((when (zp limit))
          (progn$
           (cw "- Iteration limit of ~p0 is reached. Will not parse again for full-adder patterns. ~%" *find-full-adders-in-svex-alist-limit*)
           svex-alist))
         (- (and (equal limit *find-full-adders-in-svex-alist-limit*)
                 (cw "- Searching for full-adder patterns now. ~%")))
         (- (cw "- Pass #~p0:~%" (+ 1 (- limit) *find-full-adders-in-svex-alist-limit*)))

         ;;(- (rp::cwe "in find-full-adders-in-svex-alist. Incoming svex-alist: ~p0 ~%" svex-alist))

         ((mv pattern-alist &)
          (gather-adder-patterns-in-svex-alist svex-alist nil nil 1))
         (svex-alist (replace-adder-patterns-in-svex-alist svex-alist pattern-alist 1))
         (- (clear-memoize-table 'replace-adder-patterns-in-svex))
         (pattern-alist (fast-alist-clean pattern-alist))
         (replaced-pattern-cnt (pattern-alist-has-complete-full-adder-patterns-p pattern-alist))
         (- (cw "- After the quick search, ~p0 full-adder patterns are found and replaced.~%" replaced-pattern-cnt))
         (- (fast-alist-free pattern-alist))

         ;; search again after replacements so args can match when looking for fa-s patterns.
         ((mv pattern-alist &)
          (gather-adder-patterns-in-svex-alist svex-alist nil nil 1))
         (pattern-alist (fast-alist-clean pattern-alist))

         (new-pattern-cnt (pattern-alist-has-complete-full-adder-patterns-p pattern-alist))
         ((when (> new-pattern-cnt 0))
          (progn$ (cw "- Replacement after the previous quick search revealed ~p0 more full-adder patterns, which are all replaced. Let's make another pass.~%"
                      new-pattern-cnt)
                  (b* ((svex-alist (replace-adder-patterns-in-svex-alist svex-alist pattern-alist 1))
                       (- (fast-alist-free pattern-alist)))
                    (find-full-adders-in-svex-alist svex-alist (1- limit)))))

         ;; TODO:  HERE I  can look  for bitxors  with at  least 3  elements to
         ;; decide if any fa-s might be mising before consing below..

         (unmatched-arg-alist (process-unmatched-fa-c-chains pattern-alist nil))
         (- (fast-alist-free pattern-alist))

         (- (cw "Will now look more carefully if we have missed any fa-s pattern that has a counterpart fa-c pattern.~%" ))

         (new-svex-alist (find-s-from-found-c-in-svex-alist-aux svex-alist unmatched-arg-alist))

         (- (clear-memoize-table 'find-s-from-found-c-in-svex-aux))
         (- (fast-alist-free unmatched-arg-alist))

         ((when (hons-equal new-svex-alist svex-alist))
          (progn$ (cw "- Could not find any missed fa-s. ~%")
                  svex-alist))

         (- (cw "- Some missed fa-s patterns are found and their shape is updated. This will reveal more fa patterns during quick search. So will now do another pass. (There might be an overlap in statistics below) ~%"))
         )
      (find-full-adders-in-svex-alist new-svex-alist (1- limit)))
    ///
    (defret <fn>-is-correct
      (implies (and (force (sv::svex-alist-p svex-alist))
                    (force (warrants-for-adder-pattern-match)))
               (equal (sv::svex-alist-eval$ res env)
                      (sv::svex-alist-eval$ svex-alist env)))
      :hints (("Goal"
               :in-theory (e/d () ()))))))

;; (find-full-adders-in-svex-alist #!SV'((first .
;;                                                 (bitor (bitand x y)
;;                                                        (bitor (bitand y z)
;;                                                               (bitand x z))))
;;                                          (second .
;;                                                  (bitxor (bitxor k (bitxor x z))
;;                                                          y)))
;;                                    3)

(define rewrite-adders-in-svex-alist ((svex-alist sv::Svex-alist-p))
  :Returns (res sv::Svex-alist-p :hyp (sv::Svex-alist-p svex-alist))
  (b* ((- (cw "Starting: rp::rewrite-adders-in-svex-alist. ~%"))

       (- (time-tracker :rewrite-adders-in-svex :end))
       (- (time-tracker :rewrite-adders-in-svex :init
                        :times '(1 2 3 4 5)
                        :interval 5
                        ))
       (- (time-tracker :rewrite-adders-in-svex :start!))

       (svex-alist (find-full-adders-in-svex-alist svex-alist *find-full-adders-in-svex-alist-limit*))

       ;;(svex-alist (find-full-adders-in-svex-alist svex-alist (1- *find-full-adders-in-svex-alist-limit*)))

       ;;(- (cwe "resulting svexl-alist ~p0 ~%" (svl::svex-alist-to-svexl-alist svex-alist)))

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
       (- (cw "- Searching for other adders (e.g., half-adder) now.~%"))
       ((mv pattern-alist &)
        (gather-adder-patterns-in-svex-alist svex-alist nil nil 2))
       (svex-alist (replace-adder-patterns-in-svex-alist svex-alist pattern-alist 2))
       (- (clear-memoize-table 'replace-adder-patterns-in-svex))
       (- (fast-alist-free pattern-alist))
       (- (time-tracker :rewrite-adders-in-svex :stop))
       (- (time-tracker :rewrite-adders-in-svex :print?
                        :min-time 0
                        :msg "Search for other adder patterns took ~st secs.~%~%"))

       (- (cw "Finished: rp::rewrite-adders-in-svex-alist.~%")))
    svex-alist)
  ///
  (defret <fn>-is-correct
    (implies (and (force (sv::svex-alist-p svex-alist))
                  (force (warrants-for-adder-pattern-match)))
             (equal (sv::svex-alist-eval$ res env)
                    (sv::svex-alist-eval$ svex-alist env)))
    :hints (("Goal"
             :in-theory (e/d () ())))))

(define rewrite-adders-in-svex ((svex sv::Svex-p))
  :Returns (res sv::Svex-p :hyp (sv::svex-p svex))
  ;; It is easier to manage the simplification algo in one place. So I am using
  ;; rewrite-adders-in-svex-alist here as well.
  ;; In practice, I don't expect this function to be ever used.
  (b* ((svex-alist (acons 'res svex nil))
       (svex-alist (rewrite-adders-in-svex-alist svex-alist)))
    (if (and (consp svex-alist) (consp (car svex-alist))) ;; for guards
        (cdar svex-alist)
      svex))
  ///
  (defret <fn>-is-correct
    (implies (and (force (sv::svex-p svex))
                  (force (warrants-for-adder-pattern-match)))
             (equal (sv::svex-eval$ res env)
                    (sv::svex-eval$ svex env)))
    :fn rewrite-adders-in-svex
    :hints (("Goal"
             :Expand ((sv::svex-alist-eval$
                       (rewrite-adders-in-svex-alist (list (cons 'res svex)))
                       env))
             :use ((:instance rewrite-adders-in-svex-alist-is-correct
                              (svex-alist (LIST (CONS 'RES SVEX)))))
             :in-theory (e/d (sv::svex-alist-eval$
                              SV::SVEX-ALIST-EVAL)
                             (rewrite-adders-in-svex-alist-is-correct))))))

(def-rp-rule trigger-rewrite-adders-in-svex-alist
  (implies (and (force (sv::svex-alist-p alist))
                (force (warrants-for-adder-pattern-match))
                (force (sv::svex-alist-no-foreign-op-p alist)))
           ;; svex-alist-eval-meta-w/o-svexl should return wrapped with identity
           (equal (identity (sv::svex-alist-eval alist env))
                  (sv::svex-alist-eval$
                   (rewrite-adders-in-svex-alist
                    alist)
                   env)))
  :disabled t ;; should be enabled in the defthmrp-multiplier macro
  :hints (("Goal"
           :use ((:instance svl::svex-alist-reduce-w/-env-correct
                            (svl::Svex-alist alist)
                            (svl::env nil)
                            (svl::env-term ''nil)))
           :in-theory (e/d () ()))))

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
          (enable-rules '((:rewrite trigger-rewrite-adders-in-svex-alist)
                          (:meta svl::svex-alist-eval-meta-w/o-svexl
                                 .
                                 sv::svex-alist-eval))))
         (defthm-with-temporary-warrants
           ,@args
           :fns (ha-c-chain
                 fa-c-chain
                 ha+1-c-chain
                 ha+1-s-chain
                 ha+1-s
                 ha-s-chain
                 fa-s-chain)
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
