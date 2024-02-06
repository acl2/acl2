
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

(include-book "../fnc-defs")
(include-book "centaur/svl/top" :dir :system)
(include-book "centaur/sv/svex/lists" :dir :system)

(local
 (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local
 (include-book "ihs/logops-lemmas" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define some lemmas.

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
                             ()))))

  (defthm len-of-MERGE-LEXORDER
    (equal (len (acl2::merge-lexorder l1 l2 acc))
           (+ (len l1)
              (len l2)
              (len acc))))

  (defthm len-of-evens+odds
    (and (equal (+ (len (evens x))
                   (len (odds x)))
                (len x))
         (equal (+ (len (evens x))
                   (len (evens (cdr x))))
                (len x))))

  (defthm len-of-merge-sort-lexorder
    (equal (len (acl2::merge-sort-lexorder l))
           (len l))))

(local
 (defthm svexlist-p-of-remove-duplicates
   (implies (sv::Svexlist-p x)
            (sv::Svexlist-p (remove-duplicates-equal x)))))

(local
 (in-theory (disable acl2::merge-sort-lexorder
                     acl2::merge-lexorder)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define  some  data  structures  to  help with  programming  and  the  tool's
;; verification.

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
     (rule symbol-listp)
     (new-p booleanp :default t)
     (flip booleanp :default nil)
     )
    :layout :fulltree
    ;;:hons t
    )

  (define pattern-call ((x pattern-fn-call-p)
                        &optional args)
    (b* (((pattern-fn-call x))
         (res
          (hons x.fn
                (if x.extra-arg
                    (hons x.extra-arg
                          (if args args x.args))
                  (if args args x.args)))))
      (if x.flip
          (hons-list 'sv::bitxor 1 res)
        res)))

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

  (fty::defalist pattern-alist
                 :key-type sv::svexlist-p
                 :val-type true-listp
                 :true-listp nil)

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

    (defthm pattern-fn-call-list-provide-good-measure-p-of-REMOVE-DUPLICATES-EQUAL
      (implies (pattern-fn-call-list-provide-good-measure-p x lst1)
               (pattern-fn-call-list-provide-good-measure-p x (REMOVE-DUPLICATES-EQUAL lst1))))

    (defthm pattern-fn-call-list-provide-good-measure-p-and-member
      (implies (and (pattern-fn-call-list-provide-good-measure-p x lst)
                    (member-equal e lst))
               (pattern-fn-call-provide-good-measure-p x e)))

    )

  (defthm PATTERN-FN-CALL-LIST-P-of-REMOVE-DUPLICATES-EQUAL
    (implies (PATTERN-FN-CALL-LIST-P x)
             (PATTERN-FN-CALL-LIST-P (REMOVE-DUPLICATES-EQUAL x))))

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

  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; adder pattern functions.

(local
 (in-theory (e/d (sv::svex-kind)
                 ((:e tau-system)))))

(local
 ;; some more lemmas first.
 (defsection 4vec-lemmas

   (defthm 4vec-concat$-to-logapp
     (implies (and (natp size)
                   (integerp x)
                   (integerp y))
              (equal (svl::4vec-concat$ size x y)
                     (logapp size x y)))
     :hints (("goal"
              :in-theory (e/d (svl::4vec-concat$
                               svl::logapp-to-4vec-concat)
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
     :hints (("goal"
              :do-not-induct t
              :in-theory (e/d* (sv::4vec
                                sv::4vec-bitand
                                sv::3vec-bitand
                                sv::3vec-bitor
                                sv::4vec-bitor
                                sv::3vec-bitnot
                                sv::4vec-bitnot
                                bitops::ihsext-inductions
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
                                logand)))))

   (defthm sv::svexlist-eval$-when-consp
     (implies (consp lst)
              (equal (sv::svexlist-eval$ lst env)
                     (cons (sv::svex-eval$ (car lst) env)
                           (sv::svexlist-eval$ (cdr lst) env)))))))

;; Macro to  help create adder search  patterns.  This will help  quickly prove
;; the  correctness of  patterns.  Also  a measure  showing  that applying  the
;; pattern  will  shrink  the  expression.  This measure  lemma  might  now  be
;; redundant.
(defmacro create-look-for-pattern-fnc (&key name
                                            body
                                            warrant-hyps
                                            prepwork
                                            postwork
                                            good-measure-hints
                                            correct-pattern-hints
                                            (extra-svex-reduce-params? 'nil)
                                            (extra-key-args 'nil)
                                            (inline 't)
                                            (enable-2 'nil))
  `(progn
     (define ,(intern-in-package-of-symbol (str::cat "LOOK-FOR-" (SYMBOL-NAME name))
                                           name)
       ((svex sv::svex-p)
        ,@(and (or extra-svex-reduce-params?
                   extra-key-args)
               `(&key ,@extra-key-args
                      ,@(and extra-svex-reduce-params?
                             '(((env) 'env)
                               ((context rp-term-listp) 'context)
                               ((config svl::svex-reduce-config-p) 'config))))))
       ,@(and extra-svex-reduce-params?
              `((declare (ignorable env context config))))
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
                                   pattern-fn-call->flip
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
         ,(if extra-svex-reduce-params?
              `(implies (and ,@warrant-hyps
                             (pattern-fn-call->rule pattern)
                             (member-equal pattern res)
                             (sv::svex-p svex)
                             (rp::rp-term-listp context)
                             (rp::valid-sc env-term a)
                             (rp::eval-and-all context a)
                             (rp::falist-consistent-aux env env-term)
                             (svl::width-of-svex-extn-correct$-lst
                              (svl::svex-reduce-config->width-extns config))
                             (svl::integerp-of-svex-extn-correct$-lst
                              (svl::svex-reduce-config->integerp-extns config)))
                        (equal (sv::svex-eval$ (pattern-call pattern) (rp-evlt env-term a))
                               (sv::svex-eval$ svex (rp-evlt env-term a))))
            `(implies (and ,@warrant-hyps
                           (pattern-fn-call->rule pattern)
                           (member-equal pattern res))
                      (equal (sv::svex-eval$ (pattern-call pattern) env)
                             (sv::svex-eval$ svex env))))

         :hints (("goal"
                  :expand ((:free (args env)
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
                                   pattern-fn-call->flip
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
  (memoize 'svex-has-more-than-one-var-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ADDER PATTERN RECOGNIZERS.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection fa-s-chain

  ;; define the spec for full-adder sum chains.
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
    '(fa-c-chain)
    ;;(hons-copy '(member-equal 'fa-c-chain found-patterns))
    )

  ;; match itself. This is useful in  later iterations to know what patterns we
  ;; have already found and applied.
  (create-case-match-macro fa-s-chain-itself-pattern
                           ('fa-s-chain x y z))

  ;; create the main pattern function for full-adder sum. This calls the other functions defined above.
  (create-look-for-pattern-fnc :name fa-s-chain-pattern
                               :prepwork ((create-case-match-macro fa-s-chain-pattern-2
                                                                   ('sv::bitxor x ('sv::bitxor y z)))
                                          (create-case-match-macro fa-s-chain-pattern-1
                                                                   ('sv::bitxor ('sv::bitxor x y) z))

                                          (local
                                           (in-theory (enable pattern-fn-call->rule
                                                              fa-s-chain))))
                               :body (append (and (fa-s-chain-pattern-1-p svex)
                                                  (fa-s-chain-pattern-1-body
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
                                             (and (fa-s-chain-itself-pattern-p svex)
                                                  (fa-s-chain-itself-pattern-body
                                                   svex
                                                   (b* ((args (acl2::merge-sort-lexorder (list x y z))))
                                                     (list (make-pattern-fn-call
                                                            :fn 'fa-s-chain
                                                            :rule nil
                                                            :args args
                                                            :new-p nil)
                                                           (make-pattern-fn-call
                                                            :fn 'fa-s-chain-self
                                                            :rule nil
                                                            :args args
                                                            :new-p nil))))))
                               :warrant-hyps ((apply$-warrant-fa-s-chain))
                               :inline nil))

(defsection fa-c-chain

  ;; Look for Full-adder carry patterns.

  ;; Define   the   spec   function   that  will   replace   full-adder   carry
  ;; patterns. Unfortunaly, four-valued logic and that arguments can be vectors
  ;; make it  a challange to  define a  simple function. So  different possible
  ;; patterns are separated with another method argument. When we can show that
  ;; the  arguments are  all two-valued  (integer) and  their size/width  is 1,
  ;; these should all be equivalent to each other.
  (define fa-c-chain (method x y z)
    :verify-guards nil
    ;; unfortunately, 4vec-bitxor is defined  differently than other stuff like
    ;; 4vec-bitand, so  arguments cannot  be commuted  around for  the fa-carry
    ;; pattern that involves bitxor. So I have to do this stuff:
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
          ((= method 4)
           (sv::4vec-bitor y z))
          ((= method 5)
           (sv::4vec-bitor (sv::4vec-bitand y z)
                           (sv::4vec-bitxor y z)))

          ((= method 6)
           (sv::4vec-bitxor (sv::4vec-bitand x (sv::4vec-bitxor y z))
                            (sv::4vec-bitand y z)))
          (t
           (sv::4vec-bitor (sv::4vec-bitand x y)
                           (sv::4vec-bitor (sv::4vec-bitand x z)
                                           (sv::4vec-bitand y z)))))
    ///
    (defwarrant-rp fa-c-chain)

    ;; Need an invariance for the arguments of the fa-c-chain pattern:
    (define valid-fa-c-chain-args-p (method x)
      :enabled t
      (and (integerp method) ;; this to reduce svex-eval$ of method cases.
           (if (or (equal method 4)
                   (equal method 5))
               (equal x 1)
             t)))

    (local
     (defthm sanity
       (implies (and (bitp x)
                     (bitp y)
                     (bitp z)
                     (valid-fa-c-chain-args-p method x))
                (equal (fa-c-chain method x y z)
                       (c-spec (list x y z))))
       :hints (("Goal"
                :in-theory (e/d (bitp
                                 valid-fa-c-chain-args-p)
                                ())))))

    ;; rewrite in terms of known functions.
    (def-rp-rule :disabled-for-acl2 t
      fa-c-chain-c-spec
      (implies (and (integerp x)
                    (integerp y)
                    (integerp z)
                    (valid-fa-c-chain-args-p method x))
               (equal (fa-c-chain method x y z)
                      (svl::4vec-concat$
                       1
                       (c-spec (list (logcar x) (logcar y) (logcar z)))
                       (fa-c-chain method (logcdr x) (logcdr y) (logcdr z)))))
      :hints (("goal"

               :do-not-induct t))))

  ;; auxiliary for pattern matching. It helps commutte arguments around without
  ;; having to hardcode all combinations.
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

  ;; application rule
  (defconst *fa-c-chain-rule*
    '(t) ;; t so that found fa-c patterns with this rule can be applied right away
    ;; without ensuring the  existing of a fa-s pattern. This  is kind of risky
    ;; but fa-c  patterns are so  unique that I don't  expect this to  create a
    ;; problem. This can actually help  for example in shifted multiplier cases
    ;; when a counterpart fa-s pattern is missing..

    ;; (hons-copy '(member-equal 'fa-s-chain found-patterns))
    )

  ;; another application rule.
  (defconst *fa-c-chain-rule-convervative*
    ;;t
    '(fa-s-chain)
    ;;(hons-copy '(member-equal 'fa-s-chain found-patterns))
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
                                                   :new-p nil
                                                   :args
                                                   (acl2::merge-sort-lexorder (list x y z))))))))
                               :warrant-hyps ((apply$-warrant-fa-c-chain)))

  ;; Create pattern matching function for the most-common pattern: ab | bc | ac
  (create-look-for-pattern-fnc :name fa-c-chain-pattern-01
                               :prepwork ((create-case-match-macro fa-c-chain-pattern-0
                                                                   ('sv::bitor ('sv::bitor ('sv::bitand x1 y1)
                                                                                           ('sv::bitand x2 z1))
                                                                               ('sv::bitand y2 z2)))
                                          ;; same pattern as above with swapped operator priority.
                                          (create-case-match-macro fa-c-chain-pattern-1
                                                                   ('sv::bitor  ('sv::bitand y2 z2)
                                                                                ('sv::bitor ('sv::bitand x1 y1)
                                                                                            ('sv::bitand x2 z1))))
                                          (local
                                           (in-theory (enable fa-c-chain))))
                               :body
                               (cond ((fa-c-chain-pattern-0-p svex)
                                      (fa-c-chain-pattern-0-body
                                       svex
                                       (b* (;; commute nodes around to see if a valid combination can be found.
                                            ((mv x y z valid) (look-for-fa-c-chain-pattern-aux))
                                            ((unless valid) nil)
                                            ;; sort the arguments so it can be matched with a corresponding fa-s.
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

  ;; another common pattern: "ab | c(a|b)" AND "ab | c(a^b)"
  (create-look-for-pattern-fnc :name fa-c-chain-pattern-2a
                               :prepwork (;; this will be another pattern if yz
                                          ;; variable  can be  shown to  be the
                                          ;; same as y^z or y|z
                                          (create-case-match-macro fa-c-chain-pattern-2a
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
                                          ;; sometimes  a syntactic  comparison
                                          ;; is not enough. So perform a little
                                          ;; bit  more complicated  equivalance
                                          ;; check between y,z  and a suspected
                                          ;; y|z or y^z pattern:
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

  ;; same patterns as fa-c-chain-pattern-2a but arguments are commutted
  (create-look-for-pattern-fnc :name fa-c-chain-pattern-2b
                               :prepwork ((create-case-match-macro fa-c-chain-pattern-2b
                                                                   ('sv::bitor  ('sv::bitand y z)
                                                                                ('sv::bitand yz x)))
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

  ;; same patterns as fa-c-chain-pattern-2a but arguments are commutted
  (create-look-for-pattern-fnc :name fa-c-chain-pattern-2c
                               :prepwork ((create-case-match-macro fa-c-chain-pattern-2c
                                                                   ('sv::bitor  ('sv::bitand x yz)
                                                                                ('sv::bitand y z)))
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

  ;; same patterns as fa-c-chain-pattern-2a but arguments are commutted
  (create-look-for-pattern-fnc :name fa-c-chain-pattern-2d
                               :prepwork ((create-case-match-macro fa-c-chain-pattern-2d
                                                                   ('sv::bitor  ('sv::bitand yz x)
                                                                                ('sv::bitand y z)))
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

  (set-ignore-ok t)

  ;; Patterns for when one arg is 1.  This pattern matching should be redundant
  ;; because svex-reduce  functions should  be able  to handle  these but  I am
  ;; trying not to rely on these  global simplifications because they should be
  ;; applied conservatively  and I  might want  to change  they are  applied or
  ;; defined later. So it is safest to handle this pattern manually here.
  (create-look-for-pattern-fnc :name fa-c-chain-pattern-3-1
                               :prepwork ((create-case-match-macro fa-c-chain-pattern-3a
                                                                   ('sv::bitor ('sv::bitor x2
                                                                                           ('sv::bitand x1 z1))
                                                                               z2))
                                          (create-case-match-macro fa-c-chain-pattern-3b
                                                                   ('sv::bitor ('sv::bitor ('sv::bitand x1 z1)
                                                                                           x2)
                                                                               z2))
                                          (create-case-match-macro fa-c-chain-pattern-3c
                                                                   ('sv::bitor  z2
                                                                                ('sv::bitor x2
                                                                                            ('sv::bitand x1 z1))))

                                          (local
                                           (in-theory (enable  fa-c-chain))))
                               :correct-pattern-hints '(:in-theory (e/d (or*) ()))
                               :body
                               (b* (((mv x y valid)
                                     (cond ((and (fa-c-chain-pattern-3a-p svex)
                                                 (fa-c-chain-pattern-3a-body svex (or* (and* (equal x1 x2)
                                                                                             (equal z1 z2))
                                                                                       (and* (equal z1 x2)
                                                                                             (equal x1 z2)))))
                                            (fa-c-chain-pattern-3a-body svex (mv x1 z1 t)))
                                           ((and (fa-c-chain-pattern-3b-p svex)
                                                 (fa-c-chain-pattern-3b-body svex (or* (and* (equal x1 x2)
                                                                                             (equal z1 z2))
                                                                                       (and* (equal z1 x2)
                                                                                             (equal x1 z2)))))
                                            (fa-c-chain-pattern-3b-body svex (mv x1 z1 t)))
                                           ((and (fa-c-chain-pattern-3c-p svex)
                                                 (fa-c-chain-pattern-3c-body svex (or* (and* (equal x1 x2)
                                                                                             (equal z1 z2))
                                                                                       (and* (equal z1 x2)
                                                                                             (equal x1 z2)))))
                                            (fa-c-chain-pattern-3c-body svex (mv x1 z1 t)))

                                           (t (mv 0 0 nil))))
                                    ((unless valid) nil)
                                    (args (acl2::merge-sort-lexorder (list x y))))
                                 (list (make-pattern-fn-call
                                        :fn 'sv::bitor
                                        :rule '(t)
                                        :args args)))
                               :warrant-hyps ((apply$-warrant-fa-c-chain)))

  ;; same reasoning as fa-c-chain-pattern-3-1
  (create-look-for-pattern-fnc :name fa-c-chain-pattern-3-2
                               :prepwork (
                                          (create-case-match-macro fa-c-chain-pattern-3d
                                                                   ('sv::bitor  z2
                                                                                ('sv::bitor ('sv::bitand x1 z1)
                                                                                            x2)))
                                          (create-case-match-macro fa-c-chain-pattern-3e
                                                                   ('sv::bitor ('sv::bitor x2 z2)
                                                                               ('sv::bitand x1 z1)))
                                          (create-case-match-macro fa-c-chain-pattern-3f
                                                                   ('sv::bitor  ('sv::bitand x1 z1)
                                                                                ('sv::bitor x2 z2)))

                                          (local
                                           (in-theory (enable  fa-c-chain))))
                               :correct-pattern-hints '(:in-theory (e/d (or*) ()))
                               :body
                               (b* (((mv x y valid)
                                     (cond ((and (fa-c-chain-pattern-3d-p svex)
                                                 (fa-c-chain-pattern-3d-body svex (or* (and* (equal x1 x2)
                                                                                             (equal z1 z2))
                                                                                       (and* (equal z1 x2)
                                                                                             (equal x1 z2)))))
                                            (fa-c-chain-pattern-3d-body svex (mv x1 z1 t)))
                                           ((and (fa-c-chain-pattern-3e-p svex)
                                                 (fa-c-chain-pattern-3e-body svex (or* (and* (equal x1 x2)
                                                                                             (equal z1 z2))
                                                                                       (and* (equal z1 x2)
                                                                                             (equal x1 z2)))))
                                            (fa-c-chain-pattern-3e-body svex (mv x1 z1 t)))
                                           ((and (fa-c-chain-pattern-3f-p svex)
                                                 (fa-c-chain-pattern-3f-body svex (or* (and* (equal x1 x2)
                                                                                             (equal z1 z2))
                                                                                       (and* (equal z1 x2)
                                                                                             (equal x1 z2)))))
                                            (fa-c-chain-pattern-3f-body svex (mv x1 z1 t)))
                                           (t (mv 0 0 nil))))
                                    ((unless valid) nil)
                                    (args (acl2::merge-sort-lexorder (list x y))))
                                 (list (make-pattern-fn-call
                                        :fn 'sv::bitor
                                        :rule '(t)
                                        :args args)))
                               :warrant-hyps ((apply$-warrant-fa-c-chain)))

  ;; Common plus 1 case.  Only apply if the args are other functions to prevent
  ;; this  from  flooding  the  alists,  also  this  can  mess  up  with  local
  ;; simpflification search. So this is currently not used. See below.
  (create-look-for-pattern-fnc :name fa-c-chain-pattern-4a
                               :prepwork ((create-case-match-macro fa-c-chain-pattern-4a
                                                                   ('sv::bitor x y))
                                          (local
                                           (in-theory (enable FA-C-CHAIN))))
                               :body
                               (and (fa-c-chain-pattern-4a-p svex)
                                    (fa-c-chain-pattern-4a-body
                                     svex
                                     (b* ((valid (and (consp x)
                                                      (or* (equal (car x) 'fa-c-chain)
                                                           (equal (car x) 'fa-s-chain)
                                                           (equal (car x) 'ha-s-chain)
                                                           (equal (car x) 'ha-c-chain))
                                                      (consp y)
                                                      (or* (equal (car y) 'fa-c-chain)
                                                           (equal (car y) 'fa-s-chain)
                                                           (equal (car y) 'ha-s-chain)
                                                           (equal (car y) 'ha-c-chain))))
                                          ((unless valid)
                                           nil)
                                          (args (cons 1 (acl2::merge-sort-lexorder (list x y)))))
                                       (list (make-pattern-fn-call
                                              :fn 'fa-c-chain
                                              :extra-arg 4
                                              :rule *fa-c-chain-rule-convervative*
                                              :args args)))))
                               :warrant-hyps ((apply$-warrant-fa-c-chain)))

  ;; Strange plus 1 case. This happens when regular fa-c pattern with bitxor is
  ;; reduced when one of the arguments is 1.
  (create-look-for-pattern-fnc :name fa-c-chain-pattern-4b
                               :prepwork ((create-case-match-macro fa-c-chain-pattern-4b1
                                                                   ('sv::bitor ('sv::bitand x1 y1)
                                                                               ('sv::bitxor x2 y2)))
                                          (create-case-match-macro fa-c-chain-pattern-4b2
                                                                   ('sv::bitor ('sv::bitxor x2 y2)
                                                                               ('sv::bitand x1 y1)))
                                          (local
                                           (in-theory (enable FA-C-CHAIN))))
                               :correct-pattern-hints '(:in-theory (e/d (or*) ()))
                               :body
                               (b* (((mv x y valid)
                                     (cond ((and (fa-c-chain-pattern-4b1-p svex)
                                                 (fa-c-chain-pattern-4b1-body svex (or* (and* (equal x1 x2)
                                                                                              (equal y1 y2))
                                                                                        (and* (equal y1 x2)
                                                                                              (equal x1 y2)))))
                                            (fa-c-chain-pattern-4b1-body svex (mv x1 y1 t)))
                                           ((and (fa-c-chain-pattern-4b2-p svex)
                                                 (fa-c-chain-pattern-4b2-body svex (or* (and* (equal x1 x2)
                                                                                              (equal y1 y2))
                                                                                        (and* (equal y1 x2)
                                                                                              (equal x1 y2)))))
                                            (fa-c-chain-pattern-4b2-body svex (mv x1 y1 t)))
                                           (t (mv 0 0 nil))))
                                    ((Unless valid)
                                     nil)
                                    (args (cons 1 (acl2::merge-sort-lexorder (list x y)))))
                                 (list (make-pattern-fn-call
                                        :fn 'fa-c-chain
                                        :extra-arg 5
                                        :rule *fa-c-chain-rule*
                                        :args args)))
                               :warrant-hyps ((apply$-warrant-fa-c-chain)))

  ;; Some odd  and very rare  cases of full-adder  carry.  It looks  like these
  ;; might  be messing  up with  half-adder search,  so will  give these  a low
  ;; priority  and apply  them  only  at half-adder  search  stage.  These  are
  ;; probably here to satisfy some corner  cases, which the program will likely
  ;; encounter very rarely.
  (create-look-for-pattern-fnc :name fa-c-chain-pattern-6
                               :prepwork ((create-case-match-macro fa-c-chain-pattern-6a-f
                                                                   ('sv::bitxor
                                                                    ('sv::bitxor 1
                                                                                 ('sv::bitand x ('sv::bitxor y1 z1)))
                                                                    ('sv::bitand y z)))
                                          (create-case-match-macro fa-c-chain-pattern-6a
                                                                   ('sv::bitxor
                                                                    ('sv::bitand x ('sv::bitxor y1 z1))
                                                                    ('sv::bitand y z)))
                                          (create-case-match-macro fa-c-chain-pattern-6b
                                                                   ('sv::bitxor
                                                                    ('sv::bitand y z)
                                                                    ('sv::bitand x ('sv::bitxor y1 z1))))

                                          (local
                                           (in-theory (enable fa-c-chain))))
                               :correct-pattern-hints '(:in-theory (e/d (or*) ()))
                               :body
                               (b* (((Unless (and*-exec (consp svex) ;; redundant. hopefully will help with speed.
                                                        (equal (car svex) 'sv::bitxor)))
                                     nil)
                                    ((mv x y z flip valid)
                                     (cond ((fa-c-chain-pattern-6a-f-p svex)
                                            (fa-c-chain-pattern-6a-f-body svex
                                                                          (mv x y z t
                                                                              (or* (and* (equal y1 y)
                                                                                         (equal z1 z))
                                                                                   (and* (equal y1 z)
                                                                                         (equal z1 y))))))
                                           ((fa-c-chain-pattern-6a-p svex)
                                            (fa-c-chain-pattern-6a-body svex (mv x y z nil
                                                                                 (or* (and* (equal y1 y)
                                                                                            (equal z1 z))
                                                                                      (and* (equal y1 z)
                                                                                            (equal z1 y))))))
                                           ((fa-c-chain-pattern-6b-p svex)
                                            (fa-c-chain-pattern-6b-body svex (mv x y z nil
                                                                                 (or* (and* (equal y1 y)
                                                                                            (equal z1 z))
                                                                                      (and* (equal y1 z)
                                                                                            (equal z1 y))))))
                                           (t (mv 0 0 0 nil nil))))
                                    ((Unless valid)
                                     nil)
                                    (args (list x y z)))
                                 (list (make-pattern-fn-call
                                        :fn 'fa-c-chain
                                        :extra-arg 6
                                        :flip flip
                                        :rule *fa-c-chain-rule* ;; TODO: make this conservative and apply at fa-c stage.
                                        :args args)))
                               :warrant-hyps ((apply$-warrant-fa-c-chain)))

  ;; gather the above functions to create the main pattern matching function for fa-c
  (create-look-for-pattern-fnc :name fa-c-chain-pattern
                               :prepwork ()
                               :body (append (look-for-fa-c-chain-pattern-01 svex)
                                             (look-for-fa-c-chain-pattern-2a svex)
                                             (look-for-fa-c-chain-pattern-2b svex)
                                             (look-for-fa-c-chain-pattern-2c svex)
                                             (look-for-fa-c-chain-pattern-2d svex)
                                             (look-for-fa-c-chain-pattern-3-1 svex) ;; some csel multiplier seems to need this...
                                             (look-for-fa-c-chain-pattern-3-2 svex) ;; same as above..
                                             ;;(look-for-fa-c-chain-pattern-4a svex)
                                             (look-for-fa-c-chain-pattern-4b svex)

                                             ;;(look-for-fa-c-chain-pattern-6 svex)
                                             (look-for-fa-c-chain-itself-pattern svex)
                                             )
                               :warrant-hyps ((apply$-warrant-fa-c-chain))
                               :inline nil))

(defsection ha-s-chain
  ;; Match half-adder sum patterns.

  (create-case-match-macro partsel-of-atom-pattern
                           ('sv::partsel start size term)
                           :extra-cond (atom term))
  (create-case-match-macro bitxor-pattern
                           ('sv::bitxor x y))

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
    '(ha-c-chain)
    #|(hons-copy '(or
    ;; match only when a counterpart ha-c is found.
    (member-equal 'ha-c-chain found-patterns)

    ))|#)

  (create-look-for-pattern-fnc :name ha-s-chain-pattern
                               :prepwork ((create-case-match-macro ha-s-chain-pattern
                                                                   ('sv::bitxor x y)
                                                                   ;; When two of them are variables, then don't try to create a a half-adder.
                                                                   ;; This is redundant and only here for performance improvements.
                                                                   ;; May cause issues in corner cases.
                                                                   :extra-cond
                                                                   (and (or (not (and (partsel-of-atom-pattern-p x)
                                                                                      (partsel-of-atom-pattern-p y))))
                                                                        ;; when  one of  them is  zero,
                                                                        ;; then   don't  bother.   This
                                                                        ;; should almost never happen.
                                                                        (not (integerp x))
                                                                        (not (integerp y))))
                                          (create-case-match-macro ha-s-chain-self-pattern
                                                                   ('ha-s-chain x y))
                                          (local (in-theory (enable pattern-fn-call->rule
                                                                    ha-s-chain))))
                               :body
                               (cond ((ha-s-chain-pattern-p svex)
                                      (ha-s-chain-pattern-body
                                       svex
                                       (b* ((args (acl2::merge-sort-lexorder (list x y))))
                                         (list (make-pattern-fn-call
                                                :fn 'ha-s-chain
                                                :rule *ha-s-chain-rule*
                                                :args args)))))
                                     ((ha-s-chain-self-pattern-p svex)
                                      (ha-s-chain-self-pattern-body
                                       svex
                                       (b* ((args (acl2::merge-sort-lexorder (list x y))))
                                         (list (make-pattern-fn-call
                                                :fn 'ha-s-chain
                                                :rule nil
                                                :new-p nil
                                                :args args)
                                               (make-pattern-fn-call
                                                :fn 'ha-s-chain-self
                                                :rule nil
                                                :new-p nil
                                                :args args))))))
                               :warrant-hyps ((apply$-warrant-ha-s-chain))))


(defsection ha-c-chain
  ;; match half-adder carry pattern.

  (create-case-match-macro bitand-pattern
                           ('sv::bitand x y))

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
    '(ha-s-chain)
    ;;(hons-copy '(member-equal 'ha-s-chain found-patterns))
    )

  (create-look-for-pattern-fnc :name ha-c-chain-pattern-with-simplify
                               :extra-key-args ((strength integerp))
                               :prepwork ((create-case-match-macro ha-c-chain-pattern
                                                                   ('sv::bitand x y)
                                                                   ;; prevent two partsels to be go intp a half-adder.
                                                                   :Extra-cond
                                                                   (and (or (not (and (partsel-of-atom-pattern-p x)
                                                                                      (partsel-of-atom-pattern-p y)))
                                                                            )
                                                                        (not (integerp x))
                                                                        (not (integerp y))))
                                          (local (in-theory (e/d (ha-c-chain)
                                                                 (svl::svex-eval$-of-bitand/or/xor-cancel-repeated-correct)))))
                               :body (and
                                      (ha-c-chain-pattern-p svex)
                                      (ha-c-chain-pattern-body
                                       svex
                                       (b* ((new-svex1
                                             (svl::bitand/or/xor-cancel-repeated
                                              'sv::bitand x y :leave-depth strength :nodes-to-skip-alist nil))
                                            (p1 (and (and*-exec (not (equal new-svex1 svex))
                                                                (ha-c-chain-pattern-p new-svex1))
                                                     (ha-c-chain-pattern-body
                                                      new-svex1
                                                      (list (make-pattern-fn-call
                                                             :fn 'ha-c-chain
                                                             :rule *ha-c-chain-rule*
                                                             :args (acl2::merge-sort-lexorder (list x y)))))))
                                            (p1 (and (pattern-fn-call-list-provide-good-measure-p svex p1)
                                                     p1)))
                                         p1)))
                               :correct-pattern-hints
                               '(:use ((:instance svl::svex-eval$-of-bitand/or/xor-cancel-repeated-correct
                                                  (svl::big-env env)
                                                  (svl::env-term env-term)
                                                  (svl::a a)
                                                  (svl::fn 'sv::bitand)
                                                  (svl::x (CADR SVEX))
                                                  (svl::y (CADDR SVEX))
                                                  (svl::leave-depth strength)
                                                  (svl::nodes-to-skip-alist nil))))
                               :extra-svex-reduce-params? t
                               :warrant-hyps ((apply$-warrant-ha-c-chain))
                               :postwork ((memoize 'sv::svex-count)))

  
  (with-output
    :off :all
    :gag-mode :goals
    :on (error summary)
    (create-look-for-pattern-fnc :name ha-c-chain-pattern
                                 :inline nil
                                 :prepwork ((create-case-match-macro ha-c-chain-pattern-itself
                                                                     ('ha-c-chain x y))

                                            (create-case-match-macro ha-c-chain-repeated-with-self1
                                                                     ('ha-c-chain x ('ha-c-chain y1 y2))
                                                                     :extra-cond
                                                                     (or (equal y1 x)
                                                                         (equal y2 x)))
                                            (create-case-match-macro ha-c-chain-repeated-with-self2
                                                                     ('ha-c-chain ('ha-c-chain y1 y2) x)
                                                                     :extra-cond
                                                                     (or (equal y1 x)
                                                                         (equal y2 x)))
                                            
                                            (local (in-theory (e/d (ha-c-chain)
                                                                   ()))))
                                 :body
                                 (append ;; (and
                                         ;;  (ha-c-chain-repeated-with-self1-p svex)
                                         ;;  (ha-c-chain-repeated-with-self1-body
                                         ;;   svex
                                         ;;   (declare (ignorable x))
                                         ;;   (list (make-pattern-fn-call
                                         ;;          :fn 'ha-c-chain
                                         ;;          :rule '(t)
                                         ;;          :args (acl2::merge-sort-lexorder (list y1 y2))))))
                                         ;; (and
                                         ;;  (ha-c-chain-repeated-with-self2-p svex)
                                         ;;  (ha-c-chain-repeated-with-self2-body
                                         ;;   svex
                                         ;;   (declare (ignorable x))
                                         ;;   (list (make-pattern-fn-call
                                         ;;          :fn 'ha-c-chain
                                         ;;          :rule '(t)
                                         ;;          :args (acl2::merge-sort-lexorder (list y1 y2))))))

                                         (and
                                          (ha-c-chain-pattern-itself-p svex)
                                          (ha-c-chain-pattern-itself-body
                                           svex
                                           (list (make-pattern-fn-call
                                                  :fn 'ha-c-chain
                                                  :rule nil
                                                  :new-p nil
                                                  :args (acl2::merge-sort-lexorder (list x y))))))
                                         
                                         (and
                                          (ha-c-chain-pattern-p svex)
                                          (ha-c-chain-pattern-body
                                           svex
                                           (b* ((p0 (make-pattern-fn-call
                                                     :fn 'ha-c-chain
                                                     :rule *ha-c-chain-rule*
                                                     :args (acl2::merge-sort-lexorder (list x y))))

                                                (p1 (look-for-ha-c-chain-pattern-with-simplify svex
                                                                                               :strength 0))
                                                (p2 (look-for-ha-c-chain-pattern-with-simplify svex
                                                                                               :strength 1))
                                                (p3 (and nil (look-for-ha-c-chain-pattern-with-simplify svex
                                                                                                        :strength 2)))
                                                (res `(,p0 ,@p1 ,@p2 ,@p3))
                                                (res (remove-duplicates-equal res)))
                                             res)))

                                         ;; Putting this  here because  when this
                                         ;; is applied at fa  search stage, it is
                                         ;; messing  up  with things.  This  way,
                                         ;; this will have a less priority.... TODO: remove this from here!!!
                                         ;;(look-for-fa-c-chain-pattern-6 svex)
                                         )
                                 :extra-svex-reduce-params? t
                                 :warrant-hyps ((apply$-warrant-ha-c-chain)
                                                (apply$-warrant-fa-c-chain))))

  )

(defsection ha+1-c-chain
  ;; ha+1 are cases where two variables  are summed with a constant.  ha+1-c is
  ;; the carry pattern for them.

  (create-case-match-macro bitor-pattern
                           ('sv::bitor x y))

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
    '(ha+1-s-chain)
    ;;(hons-copy '(member-equal 'ha+1-s-chain found-patterns))
    )

  (create-look-for-pattern-fnc :name ha+1-c-chain-pattern-with-simplify
                               :extra-key-args ((strength integerp))
                               :prepwork ((create-case-match-macro ha+1-c-chain-pattern
                                                                   ('sv::bitor x y)
                                                                   ;; prevent two partsels to be go intp a half-adder.
                                                                   :extra-cond
                                                                   (and (not (and (partsel-of-atom-pattern-p x)
                                                                                  (partsel-of-atom-pattern-p y)))
                                                                        (not (integerp x))
                                                                        (not (integerp y))
                                                                        ))
                                          (local (in-theory (e/d (ha+1-c-chain)
                                                                 (svl::svex-eval$-of-bitand/or/xor-cancel-repeated-correct)))))
                               :body (and
                                      (ha+1-c-chain-pattern-p svex)
                                      (ha+1-c-chain-pattern-body
                                       svex
                                       (b* ((new-svex1
                                             (svl::bitand/or/xor-cancel-repeated
                                              'sv::bitor x y :leave-depth strength :nodes-to-skip-alist nil))
                                            (p1 (and (and*-exec (not (equal new-svex1 svex))
                                                                (ha+1-c-chain-pattern-p new-svex1))
                                                     (ha+1-c-chain-pattern-body
                                                      new-svex1
                                                      (list (make-pattern-fn-call
                                                             :fn 'ha+1-c-chain
                                                             :rule *ha+1-c-chain-rule*
                                                             :args (acl2::merge-sort-lexorder (list x y)))))))
                                            (p1 (and (pattern-fn-call-list-provide-good-measure-p svex p1)
                                                     p1)))
                                         p1)))
                               :correct-pattern-hints
                               '(:use ((:instance svl::svex-eval$-of-bitand/or/xor-cancel-repeated-correct
                                                  (svl::big-env env)
                                                  (svl::env-term env-term)
                                                  (svl::a a)
                                                  (svl::fn 'sv::bitor)
                                                  (svl::x (CADR SVEX))
                                                  (svl::y (CADDR SVEX))
                                                  (svl::leave-depth strength)
                                                  (svl::nodes-to-skip-alist nil))))
                               :extra-svex-reduce-params? t
                               :warrant-hyps ((apply$-warrant-ha+1-c-chain))
                               :postwork ((memoize 'sv::svex-count))

                               :inline nil
                               )

  (create-look-for-pattern-fnc :name ha+1-c-chain-pattern
                               :prepwork (
                                          (create-case-match-macro ha+1-c-chain-self-pattern
                                                                   ('ha+1-c-chain x y))
                                          (local
                                           (in-theory (e/d (ha+1-c-chain)
                                                           ()))))
                               :body
                               (cond ((ha+1-c-chain-pattern-p svex)
                                      (b* ((p0 (ha+1-c-chain-pattern-body
                                                svex
                                                (b* (#|(- (and (or (integerp x)
                                                     (integerp y))
                                                     (cwe "ha+1-c-chain-pattern found an integerp: ~p0~%" svex)))|#
                                                     (args (acl2::merge-sort-lexorder (list x y))))
                                                  (make-pattern-fn-call
                                                   :fn 'ha+1-c-chain
                                                   :rule *ha+1-c-chain-rule*
                                                   :args args))))

                                           (p1 (and t (look-for-ha+1-c-chain-pattern-with-simplify svex
                                                                                                   :strength 0)))
                                           (p2 (and t (look-for-ha+1-c-chain-pattern-with-simplify svex
                                                                                                   :strength 1)))
                                           (p3 (and nil (look-for-ha+1-c-chain-pattern-with-simplify svex
                                                                                                     :strength 2)))
                                           (res `(,p0 ,@p1 ,@p2 ,@p3))
                                           (res (remove-duplicates-equal res)))
                                        res))
                                     ((ha+1-c-chain-self-pattern-p svex)
                                      (ha+1-c-chain-self-pattern-body
                                       svex
                                       (b* ((args (acl2::merge-sort-lexorder (list x y))))
                                         (list (make-pattern-fn-call
                                                :fn 'ha+1-c-chain
                                                :rule nil ;; nil so that it will not try to replace anything.
                                                :new-p nil
                                                :args args))))))
                               :extra-svex-reduce-params? t
                               :inline nil
                               :warrant-hyps ((apply$-warrant-ha+1-c-chain))))

(defsection ha+1-s-chain
  ;; sum for x+y+1 case.

  (define ha+1-s-chain (method x y)
    :verify-guards nil
    (cond  ((= method  10) ;;  when double  negation occurs,  they cancel  each
            ;; other. So need to add this case for matching when 1
            ;; is missing in bitxor chain.
            (sv::4vec-bitxor x y))
           ((= method 0) ;; should never happen as  sv::4vec-bitnot is expected
            ;; to be replaced already.
            (sv::4vec-bitnot (sv::4vec-bitxor x y)))
           (t ;; most common case.
            (sv::4vec-bitxor 1 (sv::4vec-bitxor x y))))
    ///
    (defwarrant-rp ha+1-s-chain)

    (def-rp-rule :disabled-for-acl2 t
      ha+1-s-chain-to-s-spec
      (implies (and (integerp x)
                    (integerp y)
                    (not (= method 10)))
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
    '(ha+1-c-chain)
    ;;(hons-copy '(member-equal 'ha+1-c-chain found-patterns))
    )

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
                                                                   ('sv::bitxor ('sv::bitxor x y) z)
                                                                   :extra-cond
                                                                   (and (or (equal x 1)
                                                                            (equal y 1)
                                                                            (equal z 1))
                                                                        (not (equal x 0))
                                                                        (not (equal y 0))
                                                                        (not (equal z 0))))
                                          (create-case-match-macro ha+1-s-chain-pattern-3
                                                                   ('sv::bitxor z ('sv::bitxor x y))
                                                                   :extra-cond
                                                                   (and (or (equal x 1)
                                                                            (equal y 1)
                                                                            (equal z 1))
                                                                        (not (equal x 0))
                                                                        (not (equal y 0))
                                                                        (not (equal z 0))))

                                          (create-case-match-macro ha+1-s-chain-self-pattern
                                                                   ('ha+1-s-chain m x y))

                                          (local
                                           (in-theory (enable pattern-fn-call->rule
                                                              ha+1-s-chain))))
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
                                                      :args args)))))
                                       (and (ha-s-chain-pattern-p svex)
                                            (ha-s-chain-pattern-body
                                             svex
                                             (b* ((args (acl2::merge-sort-lexorder (list x y))))
                                               (list (make-pattern-fn-call
                                                      :fn 'ha+1-s-chain
                                                      :extra-arg 10
                                                      :rule *ha+1-s-chain-rule*
                                                      :args args)))))

                                       (and (ha+1-s-chain-self-pattern-p svex)
                                            (ha+1-s-chain-self-pattern-body
                                             svex
                                             (b* ((args (acl2::merge-sort-lexorder (list x y))))
                                               (and (natp m)
                                                    (list (make-pattern-fn-call
                                                           :fn 'ha+1-s-chain
                                                           :extra-arg m
                                                           :rule nil
                                                           :new-p nil
                                                           :args args)
                                                          (make-pattern-fn-call
                                                           :fn 'ha+1-s-chain-self
                                                           :extra-arg m
                                                           :rule nil
                                                           :new-p nil
                                                           :args args)))))))
                               
                               :warrant-hyps ((apply$-warrant-ha+1-s-chain))))

(defsection self-patterns
  (set-ignore-ok t)
  ;; When clearing ha under gates, need to search for already found instances of half-adders
  (create-look-for-pattern-fnc :name ha-self-pattern
                               :prepwork (
                                          (create-case-match-macro ha-c-chain-self-pattern
                                                                   ('ha-c-chain x y))
                                          (local
                                           (in-theory (enable pattern-fn-call->rule))))
                               :body
                               (cond ((ha-s-chain-self-pattern-p svex)
                                      (ha-s-chain-self-pattern-body
                                       svex
                                       (b* ((args (acl2::merge-sort-lexorder (list x y))))
                                         (list (make-pattern-fn-call
                                                :fn 'ha-s-chain
                                                :rule nil
                                                :new-p nil
                                                :args args)))))
                                     ((ha-c-chain-self-pattern-p svex)
                                      (ha-c-chain-self-pattern-body
                                       svex
                                       (b* ((args (acl2::merge-sort-lexorder (list x y))))
                                         (list (make-pattern-fn-call
                                                :fn 'ha-c-chain
                                                :rule nil
                                                :new-p nil
                                                :args args)))))
                                     ((ha+1-c-chain-self-pattern-p svex)
                                      (ha+1-c-chain-self-pattern-body
                                       svex
                                       (b* ((args (acl2::merge-sort-lexorder (list x y))))
                                         (list (make-pattern-fn-call
                                                :fn 'ha+1-c-chain
                                                :rule nil
                                                :new-p nil
                                                :args args)))))
                                     ((ha+1-s-chain-self-pattern-p svex)
                                      (ha+1-s-chain-self-pattern-body
                                       svex
                                       (b* ((args (acl2::merge-sort-lexorder (list x y))))
                                         (and (natp m)
                                              (list (make-pattern-fn-call
                                                     :fn 'ha+1-s-chain
                                                     :extra-arg m
                                                     :rule nil
                                                     :new-p nil
                                                     :args args)))))))
                               :warrant-hyps ())

  (create-look-for-pattern-fnc :name fa-self-pattern
                               :prepwork ((local
                                           (in-theory (enable pattern-fn-call->rule))))
                               :body
                               (cond ((fa-s-chain-itself-pattern-p svex)
                                      (fa-s-chain-itself-pattern-body
                                       svex
                                       (b* ((args (acl2::merge-sort-lexorder (list x y z))))
                                         (list (make-pattern-fn-call
                                                :fn 'fa-s-chain
                                                :rule nil
                                                :new-p nil
                                                :args args)))))
                                     ((fa-c-chain-itself-pattern-p svex)
                                      (fa-c-chain-itself-pattern-body
                                       svex
                                       (b* ((args (acl2::merge-sort-lexorder (list x y z))))
                                         (list (make-pattern-fn-call
                                                :fn 'fa-c-chain
                                                :rule nil
                                                :extra-arg 0
                                                :new-p nil
                                                :args args))))))
                               :warrant-hyps ()))

;; a complete full-adder spec.
(define full-adder (x y z)
  :verify-guards nil
  (svl::4vec-list (fa-s-chain x y z)
                  (fa-c-chain 0 x y z)
                  0)
  ///
  (defwarrant-rp full-adder))

;; a complete half-adder spec.
(define half-adder (x y)
  :verify-guards nil
  (svl::4vec-list (fa-s-chain x y 0)
                  (fa-c-chain 0 x y 0)
                  0)
  ///
  (defwarrant-rp half-adder))

;; all warrants for second-order logic.
(progn
  (defun warrants-for-adder-pattern-match ()
    (and (apply$-warrant-ha-c-chain)
         (apply$-warrant-fa-c-chain)
         (apply$-warrant-ha+1-c-chain)
         (apply$-warrant-ha+1-s-chain)
         (apply$-warrant-ha-s-chain)
         (apply$-warrant-fa-s-chain)
         (apply$-warrant-full-adder)
         (apply$-warrant-half-adder)
         (apply$-warrant-int-vector-adder)))

  (make-event
   (b* ((body (meta-extract-formula 'warrants-for-adder-pattern-match state)))
     `(defthm warrants-for-adder-pattern-match-fc
        (implies (warrants-for-adder-pattern-match)
                 ,(third body))
        :rule-classes :forward-chaining)))

  (defconst *adder-fncs*
    '(ha-c-chain
      fa-c-chain
      ha+1-c-chain
      ha+1-s-chain
      ha-s-chain
      fa-s-chain
      full-adder
      half-adder
      int-vector-adder))

  (rp::add-rp-rule warrants-for-adder-pattern-match)
  (rp::disable-rules '((:e warrants-for-adder-pattern-match))))

;; Trigger meta functions  for s-c-rewriting.  Some rules  were already defined
;; above but this is a better rule, it works more quickly for bitp cases (which
;; should be almost always).
(progn
  (def-rp-rule fa/ha-chain-fncs-when-bitp
    (and (implies (and (bitp x)
                       (bitp y)
                       (bitp z))
                  (and (equal (fa-c-chain 0 x y z)
                              (c-spec (list x y z)))
                       (implies (valid-fa-c-chain-args-p method x)
                                (equal (fa-c-chain method x y z)
                                       (c-spec (list x y z))))
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
                              (s-spec (list x y 1)))
                       (equal (ha+1-s-chain 10 x y)
                              (binary-not (s-spec (list x y 1)))))))
    :hints (("goal"
             :in-theory (e/d (fa-c-chain
                              ha-c-chain
                              ha+1-c-chain ;
                              bitp)
                             (fa-c-chain-c-spec)))))

  (def-rp-rule full-adder-when-bitp
    (implies (and (bitp x)
                  (bitp y)
                  (bitp z))
             (equal (full-adder x y z)
                    (b* ((res (s-c-spec (list x y z))))
                      (svl::4vec-concat$ 1 (first res)
                                         (second res)))))
    :lambda-opt t
    :hints (("Goal"
             :in-theory (e/d (bitp) ()))))

  (def-rp-rule half-adder-when-bitp
    (implies (and (bitp x)
                  (bitp y))
             (equal (half-adder x y)
                    (b* ((res (s-c-spec (list x y))))
                      (svl::4vec-concat$ 1 (first res)
                                         (second res)))))
    :lambda-opt t
    :hints (("Goal"
             :in-theory (e/d (bitp) ())))))

;; Main function  to call all the  above functions and return  matched patterns
;; based on the given expression.
(define adder-pattern-match ((svex sv::svex-p)
                             (adder-type)
                             &key
                             ((env) 'env)
                             ((context rp-term-listp) 'context)
                             ((config svl::svex-reduce-config-p) 'config))
  ;; returns list of matching key/pattern-name pairs
  ;; key is the arguments of the fn symbol to replace
  ;; pattern-name is the target fn symbol
  :returns (res pattern-fn-call-list-p
                :hyp (sv::svex-p svex))
  (cond
   ((eq adder-type 'fa)
    (append
     (look-for-fa-s-chain-pattern svex)
     (look-for-fa-c-chain-pattern svex)
     ))
   ((eq adder-type 'ha)
    (progn$
     #|(b* ((ha-s (look-for-ha-s-chain-pattern svex))
     (ha-c (look-for-ha-c-chain-pattern svex))
     (x (append ha-s ha-c))
     (y (append ha-c ha-s))
     (- (and (not (equal x y))
     (raise "weird case: ~p0. x:~p1, y:~p2. ha-s:~p3, ha-c:~p4 ~%" svex x y ha-s ha-c))))
     nil)|#

     (append
      ;; as  long as  look-for-ha-c  has (look-for-fa-c-chain-pattern-6  svex),
      ;; ha-s search has to come first to prevent override!!!
      (look-for-ha-s-chain-pattern svex)
      (look-for-ha-c-chain-pattern svex)
      
      (look-for-ha+1-s-chain-pattern svex)
      (look-for-ha+1-c-chain-pattern svex)

      )))
   ((eq adder-type 'ha-self)
    (look-for-ha-self-pattern svex))
   ((eq adder-type 'fa-self)
    (look-for-fa-self-pattern svex))
   (t (raise "Unknown adder-type: ~p0 ~%" adder-type)))
  ///
  (defret <fn>-good-measure
    (implies (sv::Svex-p svex)
             (pattern-fn-call-list-provide-good-measure-p svex res)))
  (defret <fn>-correct-pattern
    (implies (and (pattern-fn-call->rule pattern)
                  (member-equal pattern res)
                  (force (sv::svex-p svex))
                  (force (rp::rp-term-listp context))
                  (force (rp::valid-sc env-term a))
                  (force (rp::eval-and-all context a))
                  (force (rp::falist-consistent-aux env env-term))
                  (force (svl::width-of-svex-extn-correct$-lst
                          (svl::svex-reduce-config->width-extns config)))
                  (force
                   (svl::integerp-of-svex-extn-correct$-lst
                    (svl::svex-reduce-config->integerp-extns config)))
                  (force (warrants-for-adder-pattern-match))
                  )
             (equal (sv::svex-eval$ (pattern-call pattern) (rp-evlt env-term a))
                    (sv::svex-eval$ svex (rp-evlt env-term a))))
    :hints (("Goal"
             :in-theory (e/d () (pattern-call)))))

  (memoize 'adder-pattern-match))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; For  svex  simplifications,  the  program   needs  to  know  the  width  and
;; integerp-ness of  the given  expressions. Since  we define  custom functions
;; such as ha-s-chain, we need to tell how to calculate these attributes.

;; first define widths.
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
                                :formula #!SVL(if (> (nth '0 args) '0)
                                                  (if (if (bitp (nth '1 widths))
                                                          (bitp (nth '2 widths))
                                                        'nil)
                                                      '1
                                                    'nil)
                                                ;; (if (equal (nth '1 widths) '1)
                                                ;;     (if (equal (nth '2 widths)'1)
                                                ;;         '1
                                                ;;       'nil)
                                                ;;   'nil)
                                                'nil)
                                :prepwork
                                ((local
                                  (in-theory (e/d (svl::4vec-correct-width-p
                                                   SV::SVEX-QUOTE->VAL
                                                   SV::4VEC-FIX
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
(svl::create-width-of-svex-extn :fn full-adder
                                :formula '2
                                :prepwork ((local
                                            (in-theory (e/d (svl::4vec-correct-width-p
                                                             svl::4vec-concat$))))))
(svl::create-width-of-svex-extn :fn half-adder
                                :formula '2
                                :prepwork ((local
                                            (in-theory (e/d (svl::4vec-correct-width-p
                                                             svl::4vec-concat$))))))


(local
 (encapsulate nil
   (local
    (include-book "centaur/bitops/signed-byte-p" :dir :system))
   ;;bitops::basic-unsigned-byte-p-of-+
   
   (defthm width-of-+-lemma-
     (implies (and (integerp x)
                   (integerp y)
                   (natp xsize)
                   (natp ysize)
                   (equal (sv::4vec-part-select 0 xsize x) x)
                   (equal (sv::4vec-part-select 0 ysize y) y))
              (and (equal (sv::4vec-part-select 0
                                                (1+ (max xsize ysize))
                                                (+ x y))
                          (+ x y))))
     :hints (("Goal"
              :in-theory (e/d (sv::4vec-part-select
                               SV::4VEC-CONCAT)
                              ()))))))

(local
 (defthm 4vec-part-select-of-ifix-lemma
   (implies (and (natp xsize)
                 (equal (sv::4vec-part-select 0 xsize x) x))
            (equal (sv::4vec-part-select 0 xsize (ifix x)) (ifix x)))
   :hints (("Goal"
            :in-theory (e/d (ifix) ())))))

(svl::create-width-of-svex-extn :fn int-vector-adder
                                :formula #!SVL(+ '1
                                                 (safe-max (nth '0 widths)
                                                           (nth '1 widths)))
                                :prepwork ((local
                                            (in-theory (e/d
                                                        (;;ifix
                                                         svl::4vec-correct-width-p)
                                                        (max int-vector-adder))))))

;; now define integerp-ness
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

(svl::create-integerp-of-svex-extn :fn int-vector-adder
                                   :prepwork
                                   ())


(svl::create-integerp-of-svex-extn :fn half-adder
                                   :prepwork
                                   ((Local (in-theory (enable fa-s-chain
                                                              fa-c-chain
                                                              svl::4vec-concat$
                                                              SV::4VEC-CONCAT)))))

(svl::create-integerp-of-svex-extn :fn full-adder
                                   :prepwork
                                   ((Local (in-theory (enable fa-s-chain
                                                              fa-c-chain
                                                              svl::4vec-concat$
                                                              SV::4VEC-CONCAT)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;; create an unfloat instance. This can help above
(define create-unfloat-for-adder-fnc (arg)
  :returns (res sv::Svex-p :hyp (sv::Svex-p arg))
  (case-match arg
    (('fa-c-chain & & & &)
     arg)
    (('fa-s-chain & & &)
     arg)
    (('ha+1-s-chain & & &)
     arg)
    ((fn & &)
     (if (member-equal fn
                       '(sv::bitxor sv::bitor
                                    ha-c-chain ha-s-chain ha+1-c-chain))
         arg
       (svl::svex-reduce-w/-env-apply 'sv::unfloat (hons-list arg))))
    (&
     (svl::svex-reduce-w/-env-apply 'sv::unfloat (hons-list arg))))
  ///
  (defret <fn>-is-correct
    (implies (warrants-for-adder-pattern-match)
             (equal (sv::svex-eval$ res env)
                    (sv::3vec-fix (sv::svex-eval$ arg env))))
    :hints (("Goal"
             :in-theory (e/d (ha-c-chain
                              ha-s-chain
                              ha+1-s-chain
                              ha+1-c-chain
                              fa-s-chain
                              fa-c-chain
                              sv::svex-apply
                              sv::svex-apply$
                              sv::svex-call->fn
                              sv::svex-call->args)
                             ())))))

(define ex-adder-fnc-from-unfloat ((svex sv::Svex-p))
     :returns (res-svex sv::svex-p :hyp (sv::Svex-p svex))
     (case-match svex
       (('sv::unfloat ('id x))
        (if (and (equal (sv::svex-kind x) :call)
                 (member-equal  (sv::Svex-call->fn  x)
                                '(fa-c-chain fa-s-chain
                                             full-adder half-adder int-vector-adder  ha+1-c-chain ha+1-s-chain
                                             ha-c-chain   ha-s-chain   sv::bitand   sv::bitor
                                             sv::bitxor)))
            (cadr svex)
          svex))
       (('sv::unfloat x)
        (if (and (equal (sv::svex-kind x) :call)
                 (member-equal  (sv::Svex-call->fn  x)
                                '(fa-c-chain fa-s-chain
                                             full-adder half-adder int-vector-adder ha+1-c-chain ha+1-s-chain
                                             ha-c-chain   ha-s-chain   sv::bitand   sv::bitor
                                             sv::bitxor)))
            x svex))
       (& svex))
     ///
     (defret <fn>-correct
       (implies (and (warrants-for-adder-pattern-match))
                (equal (sv::svex-eval$ res-svex env)
                       (sv::svex-eval$ svex env)))
       :hints (("Goal"
                :expand ((sv::svex-call->fn svex)
                         (sv::svex-call->args svex)
                         (sv::svex-call->fn (cadr svex))
                         (sv::svex-call->args (cadr svex))
                         (:free (args) (sv::svex-apply 'id args))
                         (:free (args) (sv::svex-apply 'sv::bitor args))
                         (:free (args) (sv::svex-apply 'sv::bitxor args))
                         (:free (args) (sv::svex-apply 'sv::bitand args))
                         (:free (args) (sv::svex-apply 'sv::unfloat args)))
                :in-theory (e/d (fa-c-chain
                                 fa-s-chain
                                 full-adder half-adder
                                 int-vector-adder
                                 ha-c-chain ha-s-chain
                                 ha+1-s-chain ha+1-c-chain
                                 sv::svex-apply$)
                                (acl2::apply$-badgep))))))
