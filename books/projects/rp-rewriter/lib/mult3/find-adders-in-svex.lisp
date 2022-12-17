
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

;; (progn
;;   (include-book "centaur/sv/top" :dir :system)
;;   (include-book "centaur/vl/loader/top" :dir :system)
;;   (include-book "oslib/ls" :dir :system))

;; (progn
;;   (acl2::defconsts
;;     (*original-mult1-vl-design* state)
;;     (b* (((mv loadresult state)
;;           (vl::vl-load (vl::make-vl-loadconfig
;;                         :start-files '("DT_SB4_RP_128x128_multgen.sv")))))
;;       (mv (vl::vl-loadresult->design loadresult) state)))
;;   (acl2::defconsts
;;     (*original-mult1-sv-design*)
;;     (b* (((mv errmsg sv-design & &)
;;           (vl::vl-design->sv-design "DT_SB4_RP_128x128_spec"
;;                                     *original-mult1-vl-design*
;;                                     (vl::make-vl-simpconfig))))
;;       (and errmsg
;;            (acl2::raise "~@0~%" errmsg))
;;       sv-design))
;;   (sv::defsvtv  mult1-svtv
;;     :mod *original-mult1-sv-design*
;;     :inputs '(("IN1" a)
;;               ("IN2" b))
;;     :outputs
;;     '(("design_res" design_res)
;;       ("design_is_correct" design_is_correct))))

;;;;

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
                          sv::svexlist-p)))))

(progn
  (defthm sv::svexlist-p-of-merge-lexorder
    (implies (and (true-listp l1)
                  (true-listp l2)
                  (true-listp acc))
             (equal
              (sv::svexlist-p (acl2::merge-lexorder l1 l2 acc))
              (and (sv::svexlist-p l1)
                   (sv::svexlist-p l2)
                   (sv::svexlist-p acc))))
    :hints (("Goal"
             :in-theory (e/d (acl2::merge-lexorder) ()))))

  (defthm sv::svexlist-p-of-evens/odds
    (implies (sv::svexlist-p l1)
             (and (sv::svexlist-p (evens l1))
                  (sv::svexlist-p (odds l1))))
    :hints (("Goal"
             :in-theory (e/d (sv::svexlist-p) ()))))

  (defthm sv::svexlist-p-of-merge-sort-lexorder
    (implies (force (sv::svexlist-p lst))
             (sv::svexlist-p (acl2::merge-sort-lexorder lst)))
    :hints (("Goal"
             :in-theory (e/d (sv::svexlist-p
                              acl2::merge-sort-lexorder)
                             (acl2::merge-lexorder
                              evens
                              odds)))))

  (defthm SVEXLIST-COUNT-of-append
    (implies t
             (equal (sv::Svexlist-count (append x y))
                    (+ -1
                       (sv::Svexlist-count x)
                       (sv::Svexlist-count y))))
    :rule-classes (:linear :rewrite)
    :hints (("Goal"
             :expand ((SV::SVEXLIST-COUNT X)
                      (SV::SVEXLIST-COUNT (CONS (CAR X) (APPEND (CDR X) Y))))
             :do-not-induct t
             :induct (append x y)
             :in-theory (e/d () ()))))

  (defthm SVEXLIST-COUNT-of-rev
    (equal (sv::Svexlist-count (rev x))
           (sv::Svexlist-count x))
    :hints (("Goal"
             :induct (rev x)
             :expand ((SV::SVEXLIST-COUNT X)
                      (SV::SVEXLIST-COUNT (LIST (CAR X))))
             :in-theory (e/d (rev)
                             ((:e tau-system))))))

  (defthm SVEXLIST-COUNT-of-merge-lexorder
    (equal (sv::svexlist-count (acl2::merge-lexorder l1 l2 acc))
           (+ (sv::svexlist-count l1)
              (sv::svexlist-count l2)
              (sv::svexlist-count acc)
              -2))
    :hints (("Goal"
             :in-theory (e/d (SV::SVEXLIST-COUNT)
                             ((:e tau-system))))))

  (defthm SV::SVEXLIST-COUNT-of-evens
    (implies (syntaxp (atom l1))
             (equal (SV::SVEXLIST-COUNT (EVENS L1))
                    (+ (SV::SVEXLIST-COUNT L1)
                       (- (SV::SVEXLIST-COUNT (EVENS (CDR L1))))
                       +1)))
    :hints (("Goal"
             ;;:do-not-induct t
             ;;:induct (evens l1)
             :in-theory (e/d (SV::SVEXLIST-COUNT)
                             ((:e tau-system))))))

  (defthm SVEXLIST-COUNT-of-merge-sort-lexorder
    (equal (sv::svexlist-count (acl2::merge-sort-lexorder l1))
           (sv::svexlist-count l1))
    :hints (("Goal"
             :induct (acl2::merge-sort-lexorder l1)
             :do-not-induct t
             :in-theory (e/d (SV::SVEXLIST-COUNT)
                             ((:e tau-system))))))
  )
(local
 (in-theory (disable acl2::merge-sort-lexorder
                     acl2::merge-lexorder)))

(progn

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
                       :rewrite)))

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
      :equal eq)

    )

  (fty::defprod pattern-fn-call
    ((fn sv::strict-fnsym-p)
     (args sv::svexlist-p))
    ;;:ctor-body (Hons fn args)
    :layout :fulltree
    :hons t

    )

  #|(fty::defoption maybe-pattern-fn-call
  pattern-fn-call-p)|#

  (fty::deflist pattern-fn-call-list
    :elt-type pattern-fn-call
    :true-listp t)

  (defthm pattern-fn-call-accessors-to-svex-call-accessors
    (implies (force (equal (sv::svex-kind x) :call))
             (and (equal (pattern-fn-call->fn x)
                         (sv::svex-call->fn x))
                  (equal (pattern-fn-call->args x)
                         (sv::svex-call->args x))))
    :hints (("goal"
             :in-theory (e/d (sv::svex-kind
                              sv::strict-fnsym-fix
                              sv::strict-fnsym-p
                              sv::fnsym-fix
                              std::prod-consp
                              pattern-fn-call->fn
                              pattern-fn-call->args
                              sv::svex-call->fn
                              sv::svex-call->args)
                             ()))))

  (defthm pattern-fn-call-p-implies-svex-kind-is-call
    (implies (pattern-fn-call-p x)
             (equal (sv::Svex-kind x) :call))
    :hints (("Goal"
             :in-theory (e/d (sv::Svex-kind
                              STD::PROD-CONSP
                              pattern-fn-call-p)
                             ()))))

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

(defconst *adder-pattern-necessary-pairs*
  '((ha+1-c-chain ha+1-s-chain)
    (ha+1-s-chain ha+1-c-chain)

    (ha-c-chain ha-s-chain)
    (ha-s-chain ha-c-chain)

    (fa-s-chain fa-c-chain)
    (fa-c-chain fa-s-chain)

    
    ))

(local
 (in-theory (e/d (sv::Svex-kind)
                 ((:e tau-system)))))

(local
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
                              ))))))

(local
 (defthm 4vec-concat$-to-logapp
   (implies (and (natp size)
                 (integerp x)
                 (integerp y))
            (equal (svl::4vec-concat$ size x y)
                   (logapp size x y)))
   :hints (("Goal"
            :in-theory (e/d (SVL::4VEC-CONCAT$
                             SVL::LOGAPP-TO-4VEC-CONCAT)
                            ())))))

(local
 (encapsulate
   nil
   (local
    (in-theory '(SV::4VEC-BITXOR
                 SV::4VEC-BITAND
                 SV::3VEC-BITAND
                 SV::4VEC-BITOR
                 SV::3VEC-BITOR
                 SV::3VEC-FIX
                 (:e SV::4VEC->LOWER)
                 (:e SV::4VEC->UPPER)
                 (:e logxor)
                 ACL2::SIMPLIFY-LOGXOR
                 ACL2::SIMPLIFY-LOGIOR
                 ACL2::SIMPLIFY-LOGAND
                 SV::4VEC->LOWER-OF-4VEC-FIX
                 SV::4VEC->upper-OF-4VEC-FIX
                 SV::4VEC-P-OF-4VEC-FIX
                 (:TYPE-PRESCRIPTION LOGBITP)
                 SV::4VEC->UPPER-OF-4VEC
                 SV::4VEC->lower-OF-4VEC
                 sv::4vec-equal
                 SV::4VEC-P-OF-4VEc
                 ifix
                 (:e zbp)
                 (:e BIT->BOOL)
                 (:e BOOL->BIT)
                 B-XOR
                 B-IOR
                 B-NOT
                 B-AND
                 ;;b-xor-def
                 ACL2::BFIX-OPENER
                 ;;(:TYPE-PRESCRIPTION ACL2::BITP-OF-B-XOR)
                 (:REWRITE ACL2::BFIX-OPENER)
                 (:COMPOUND-RECOGNIZER ACL2::BITP-COMPOUND-RECOGNIZER)
                 ACL2::BITP-OF-B-IOR
                 ACL2::BITP-OF-B-XOR
                 ACL2::BITP-OF-B-NOT
                 ACL2::BITP-OF-B-AND
                 ACL2::BOOL->BIT-OF-BIT->BOOL
                 BITOPS::LOGBIT-TO-LOGBITP
                 BITOPS::LOGBITP-OF-LOGIOR
                 BITOPS::LOGBITP-OF-LOGxOR
                 BITOPS::LOGBITP-OF-LOGand
                 BITOPS::LOGBITP-OF-LOGnot

                 (:type-prescription binary-logior)
                 (:type-prescription binary-logxor)
                 (:type-prescription binary-logand))))
   (defthm 4VEC-BITXOR-assoc-and-comm
     (and (equal (SV::4VEC-BITXOR (SV::4VEC-BITXOR x y) z)
                 (SV::4VEC-BITXOR x (SV::4VEC-BITXOR y z)))
          (equal (SV::4VEC-BITXOR y x)
                 (SV::4VEC-BITXOR x y))
          (equal (SV::4VEC-BITXOR y (SV::4VEC-BITXOR x z))
                 (SV::4VEC-BITXOR x (SV::4VEC-BITXOR y z))))
     :hints ((bitops::logbitp-reasoning)))

   (defthm 4VEC-BITOR-assoc-and-comm
     (and (equal (SV::4VEC-BITOR (SV::4VEC-BITOR x y) z)
                 (SV::4VEC-BITOR x (SV::4VEC-BITOR y z)))
          (equal (SV::4VEC-BITOR y x)
                 (SV::4VEC-BITOR x y))
          (equal (SV::4VEC-BITOR y (SV::4VEC-BITOR x z))
                 (SV::4VEC-BITOR x (SV::4VEC-BITOR y z))))
     :hints ((bitops::logbitp-reasoning)))

   (defthm 4VEC-BITAND-assoc-and-comm
     (and (equal (SV::4VEC-BITAND (SV::4VEC-BITAND x y) z)
                 (SV::4VEC-BITAND x (SV::4VEC-BITAND y z)))
          (equal (SV::4VEC-BITAND y x)
                 (SV::4VEC-BITAND x y))
          (equal (SV::4VEC-BITAND y (SV::4VEC-BITAND x z))
                 (SV::4VEC-BITAND x (SV::4VEC-BITAND y z))))
     :hints ((bitops::logbitp-reasoning)))

   (defthm 4vec-ab+a+b-pattern-lemma
     (equal (SV::4VEC-BITOR x (SV::4VEC-BITOR y (SV::4VEC-BITAND x y)))
            (sv::4vec-bitor x y))
     :hints ((bitops::logbitp-reasoning)))

   (defthmd insert-4vec-bitand-into-4vec-bitor
     (and (equal (sv::4vec-bitand x (sv::4vec-bitor y z))
                 (sv::4vec-bitor (sv::4vec-bitand x y)
                                 (sv::4vec-bitand x z)))
          (equal (sv::4vec-bitand (sv::4vec-bitor y z) x)
                 (sv::4vec-bitor (sv::4vec-bitand x y)
                                 (sv::4vec-bitand x z))))
     :hints ((bitops::logbitp-reasoning)))


   #|(defthm 4vec-bitxor-with-0
     (and (equal (sv::4vec-bitxor 0 x)
                 (sv::4vec-fix x))
          (equal (sv::4vec-bitxor x 0)
                 (sv::4vec-fix x)))
     :hints ((bitops::logbitp-reasoning)))|#
     
   
   ))

(progn
  (define create-case-match-macro-fn (name pattern)
    :mode :program
    (acl2::template-subst
     `(progn
        (define <name>-p (x)
          :ignore-ok t
          :inline t
          (case-match x
            (<pattern> t))
          ///
          (set-ignore-ok t)
          (defthm <name>-p-implies
            (implies (<name>-p x)
                     (case-match x
                       (,pattern t)))
            :rule-classes :forward-chaining))
        (defmacro <name>-body (var &rest body)
          (second (acl2::match-clause var '<pattern> body))))
     :atom-alist `((<pattern> . ,pattern)
                   (<name> . ,name))
     :str-alist `(("<NAME>" . ,(symbol-name name)))
     :pkg-sym name))

  (defmacro create-case-match-macro (name pattern)
    (create-case-match-macro-fn name pattern)))



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




(progn
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
  ;; ;;;;
  (define look-for-fa-s-chain-pattern ((svex sv::svex-p))
    :returns (res pattern-fn-call-list-p
                  :hyp (sv::svex-p svex))

    :prepwork ((create-case-match-macro fa-s-chain-pattern
                                        ('sv::bitxor ('sv::bitxor x y) z))
               (create-case-match-macro fa-s-chain-pattern-2
                                        ('sv::bitxor x ('sv::bitxor y z))))
    (append (and (fa-s-chain-pattern-p svex)
                 (fa-s-chain-pattern-body
                  svex
                  (b* ((args (acl2::merge-sort-lexorder (list x y z))))
                    (list (make-pattern-fn-call
                           :fn 'fa-s-chain
                           :args args)))))
            (and (fa-s-chain-pattern-2-p svex)
                 (fa-s-chain-pattern-2-body
                  svex
                  (b* ((args (acl2::merge-sort-lexorder (list x y z))))
                    (list (make-pattern-fn-call
                           :fn 'fa-s-chain
                           :args args)))))
            )
    ///

    (defret <fn>-good-measure
      (implies (sv::Svex-p svex)
               (pattern-fn-call-list-provide-good-measure-p svex res))
      :hints (("Goal"
               :expand ((SV::SVEX-COUNT SVEX))
               :in-theory (e/d (PATTERN-FN-CALL
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
               (equal (sv::svex-eval$ pattern env)
                      (sv::svex-eval$ svex env)))
      :hints (("Goal"
               :Expand ()
               :in-theory (e/d (fa-s-chain
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
                                integer-listp)))))

    ))



(progn
  (define fa-c-chain (x y z)
    :verify-guards nil
    (sv::4vec-bitor (sv::4vec-bitand x y)
                    (sv::4vec-bitor (sv::4vec-bitand x z)
                                    (sv::4vec-bitand y z)))
    ///
    (defwarrant-rp fa-c-chain)

    (def-rp-rule fa-c-chain-c-spec
      (implies (and (integerp x)
                    (integerp y)
                    (integerp z))
               (equal (fa-c-chain x y z)
                      (svl::4vec-concat$
                       1
                       (c-spec (list (logcar x) (logcar y) (logcar z)))
                       (fa-c-chain (logcdr x) (logcdr y) (logcdr z)))))
      :hints (("goal"
               ;;:do-not-induct t
               :in-theory (e/d* (bitops::ihsext-inductions
                                 bitops::ihsext-recursive-redefs)
                                ())))))

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
    

  (define look-for-fa-c-chain-pattern ((svex sv::svex-p))
    :returns (res pattern-fn-call-list-p
                  :hyp (sv::svex-p svex))

    :prepwork
    ((create-case-match-macro fa-c-chain-pattern
                              ('sv::bitor ('sv::bitor ('sv::bitand x1 y1)
                                                      ('sv::bitand x2 z1))
                                          ('sv::bitand y2 z2)))
     (create-case-match-macro fa-c-chain-pattern-2
                              ('sv::bitor  ('sv::bitand y2 z2)
                                           ('sv::bitor ('sv::bitand x1 y1)
                                                       ('sv::bitand x2 z1))))
     (create-case-match-macro fa-c-chain-pattern-3
                              ('sv::bitor  ('sv::bitand y2 z2)
                                           ('sv::bitand x1
                                                        ('sv::bitor y1 z1))))
     (create-case-match-macro fa-c-chain-pattern-4
                              ('sv::bitor  ('sv::bitand x1
                                                        ('sv::bitor y1 z1))
                                           ('sv::bitand y2 z2)))

     ;; below can be reduced to x+y, the x&y is redundant. 
     (create-case-match-macro ab+a+b-pattern
                              ('sv::bitor ('sv::bitor ('sv::bitand x y) x) y))
     )

    (cond ((fa-c-chain-pattern-p svex)
           (fa-c-chain-pattern-body
            svex
            (b* (((mv x y z valid) (look-for-fa-c-chain-pattern-aux))
                 ((unless valid) nil)
                 (args (acl2::merge-sort-lexorder (list x y z))))
              (list (make-pattern-fn-call
                     :fn 'fa-c-chain
                     :args args)))))
          ((fa-c-chain-pattern-2-p svex)
           (fa-c-chain-pattern-2-body
            svex
            (b* (((mv x y z valid) (look-for-fa-c-chain-pattern-aux))
                 ((unless valid) nil)
                 (args (acl2::merge-sort-lexorder (list x y z))))
              (list (make-pattern-fn-call
                     :fn 'fa-c-chain
                     :args args)))))
          ((fa-c-chain-pattern-3-p svex)
           (fa-c-chain-pattern-3-body
            svex
            (b* (((mv x y z valid) (look-for-fa-c-chain-pattern-aux
                                    :x2 x1))
                 ((unless valid) nil)
                 (args (acl2::merge-sort-lexorder (list x y z))))
              (list (make-pattern-fn-call
                     :fn 'fa-c-chain
                     :args args)))))
          ((fa-c-chain-pattern-4-p svex)
           (fa-c-chain-pattern-4-body
            svex
            (b* (((mv x y z valid) (look-for-fa-c-chain-pattern-aux
                                    :x2 x1))
                 ((unless valid) nil)
                 (args (acl2::merge-sort-lexorder (list x y z))))
              (list (make-pattern-fn-call
                     :fn 'fa-c-chain
                     :args args)))))
          ((ab+a+b-pattern-p svex)
           (ab+a+b-pattern-body
            svex
            (b* ((args (list x y)))
              (list (make-pattern-fn-call
                     :fn 'sv::bitor
                     :args args)))
            )))
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
                                sv::svex-count
                                sv::svex-call->args
                                sv::svex-kind
                                sv::svexlist-count
                                pattern-fn-call-provide-good-measure-p
                                pattern-fn-call-list-provide-good-measure-p)
                               (acl2::merge-sort-lexorder)))))

    (defret <fn>-correct-pattern
      (implies (and (apply$-warrant-fa-c-chain)
                    (member-equal pattern res))
               (equal (sv::svex-eval$ pattern env)
                      (sv::svex-eval$ svex env)))
      :hints (("goal"
               :expand ((SV::SVEXLIST-EVAL$ (CDR (CADR (CADR SVEX)))
                                            ENV)
                        (SV::SVEXLIST-EVAL$ (CDR SVEX) ENV)
                        (SV::SVEXLIST-EVAL$ (CDR (CADR SVEX))
                                            ENV))
               :in-theory (e/d (insert-4vec-bitand-into-4vec-bitor
                                fa-c-chain
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
      :hints (("Goal"
               :in-theory (e/d* (sv::4vec
                                 ;;bitops::ihsext-inductions
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
                     :args args))))))
    ///
    (defret <fn>-good-measure
      (implies (sv::Svex-p svex)
               (pattern-fn-call-list-provide-good-measure-p svex res))
      :hints (("Goal"
               :expand ((SV::SVEX-COUNT SVEX))
               :in-theory (e/d (SV::SVEX-COUNT
                                PATTERN-FN-CALL
                                SV::SVEX-CALL->ARGS
                                sv::svex-kind
                                SV::SVEXLIST-COUNT
                                pattern-fn-call-provide-good-measure-p
                                pattern-fn-call-list-provide-good-measure-p)
                               (acl2::merge-sort-lexorder)))))

    (defret <fn>-correct-pattern
      (implies (and (apply$-warrant-ha-s-chain)
                    (member-equal pattern res))
               (equal (sv::svex-eval$ pattern env)
                      (sv::svex-eval$ svex env)))
      :hints (("goal"
               :expand ()
               :in-theory (e/d (ha-s-chain
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
  (define ha-c-chain (x y)
    :verify-guards nil
    (sv::4vec-bitand x y)
    ///
    (defwarrant-rp ha-c-chain)

    (def-rp-rule ha-c-chain-to-c-spec
      (implies (and (integerp x)
                    (integerp y))
               (equal (ha-c-chain x y)
                      (svl::4vec-concat$
                       1
                       (c-spec (list (logcar x) (logcar y)))
                       (ha-c-chain (logcdr x) (logcdr y)))))
      :hints (("Goal"
               :in-theory (e/d* (;;bitops::ihsext-inductions
                                 bitops::ihsext-recursive-redefs)
                                ()))))
    )

  (define look-for-ha-c-chain-pattern ((svex sv::svex-p))
    :returns (res pattern-fn-call-list-p
                  :hyp (sv::svex-p svex))
    (case-match svex
      (('sv::bitand x y)
       (b* ((args (acl2::merge-sort-lexorder (list x y))))
         (list (make-pattern-fn-call
                :fn 'ha-c-chain
                :args args)))))
    ///
    (defret <fn>-good-measure
      (implies (sv::Svex-p svex)
               (pattern-fn-call-list-provide-good-measure-p svex res))
      :hints (("Goal"
               :expand ((SV::SVEX-COUNT SVEX))
               :in-theory (e/d (SV::SVEX-COUNT
                                PATTERN-FN-CALL
                                SV::SVEX-CALL->ARGS
                                sv::svex-kind
                                SV::SVEXLIST-COUNT
                                pattern-fn-call-provide-good-measure-p
                                pattern-fn-call-list-provide-good-measure-p)
                               (acl2::merge-sort-lexorder)))))

    (defret <fn>-correct-pattern
      (implies (and (apply$-warrant-ha-c-chain)
                    (member-equal pattern res))
               (equal (sv::svex-eval$ pattern env)
                      (sv::svex-eval$ svex env)))
      :hints (("goal"
               :expand ()
               :in-theory (e/d (ha-c-chain
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

;;:i-am-here
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
               (equal (sv::svex-eval$ pattern env)
                      (sv::svex-eval$ svex env)))
      :hints (("goal"
               :expand ((SV::SVEXLIST-EVAL$ (CDR (CADR (CADR SVEX)))
                                            ENV)
                        (SV::SVEXLIST-EVAL$ (CDR SVEX) ENV)
                        (SV::SVEXLIST-EVAL$ (CDR (CADR SVEX))
                                            ENV))
               :in-theory (e/d (insert-4vec-bitand-into-4vec-bitor
                                ha+1-c-chain
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
                                 ;;bitops::ihsext-inductions
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
               (equal (sv::svex-eval$ pattern env)
                      (sv::svex-eval$ svex env)))
      :hints (("goal"
               :expand ()
               :in-theory (e/d (ha+1-s-chain
                                ha+1-s
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
                (and (equal (fa-c-chain x y z)
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
                            (c-spec (list x y 1))))))
  :hints (("Goal"
           :in-theory (e/d (bitp) ()))))

;; (defun cons-if-nonnil (x y)
;;   (declare (xargs :guard t))
;;   (if x (cons x y) y))

;; (defun list-nonnils-fn (acl2::lst)
;;   (declare (xargs :guard t))
;;   (if (consp acl2::lst)
;;       (cons 'cons-if-nonnil
;;             (cons (car acl2::lst)
;;                   (cons (list-nonnils-fn (cdr acl2::lst)) nil)))
;;     nil))

;; (defmacro list-nonnils (&rest args)
;;   (list-nonnils-fn args))

(define adder-pattern-match ((svex sv::svex-p)
                             (pass-num natp))
  ;; returns list of matching key/pattern-name pairs
  ;; key is the arguments of the fn symbol to replace
  ;; pattern-name is the target fn symbol
  :returns (res pattern-fn-call-list-p
                :hyp (sv::svex-p svex))
  (append
   (and (equal pass-num 1)
        (look-for-fa-s-chain-pattern svex))
   (and (equal pass-num 1)
        (look-for-fa-c-chain-pattern svex))

   (and (equal pass-num 2) 
        (look-for-ha-s-chain-pattern svex))
   (and (equal pass-num 2)
        (look-for-ha-c-chain-pattern svex))

   (and (equal pass-num 2) 
        (look-for-ha+1-c-chain-pattern svex))
   (and (equal pass-num 2) 
        (look-for-ha+1-s-chain-pattern svex)))
  ///
  (defret <fn>-good-measure
    (implies (sv::Svex-p svex)
             (pattern-fn-call-list-provide-good-measure-p svex res)))
  (defret <fn>-correct-pattern
    (implies (and (force (warrants-for-adder-pattern-match))
                  (member-equal pattern res))
             (equal (sv::svex-eval$ pattern env)
                    (sv::svex-eval$ svex env)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define register-found-adder-patterns ((pattern-fn-call-list pattern-fn-call-list-p)
                                       (pattern-alist))
  :inline t

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
    :returns (mv pattern-alist res-parsed-svexes)
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
    :returns (mv pattern-alist res-parsed-svexes)
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
  :returns (mv pattern-alist res-parsed-svexes)
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

(define pull-the-first-applicable-adder-pattern ((pattern-alist)
                                                 (pattern-fn-call-list pattern-fn-call-list-p))
  :prepwork ((in-theory (e/d ()
                             (assoc-equal
                              PATTERN-FN-CALL-ACCESSORS-TO-SVEX-CALL-ACCESSORS
                              (:e tau-system)))))
  :returns (pattern-fn-call (implies pattern-fn-call
                                     (pattern-fn-call-p pattern-fn-call))
                            :hyp (pattern-fn-call-list-p pattern-fn-call-list))
  (if (atom pattern-fn-call-list)
      nil
    (b* (((pattern-fn-call x) (car pattern-fn-call-list))
         (necessary-pair
          (assoc-equal x.fn *adder-pattern-necessary-pairs*))
         (matching-pair (cdr (hons-get x.args pattern-alist)))
         (should-rewrite (or (not necessary-pair)
                             (and (ec-call (subsetp-equal necessary-pair matching-pair))
                                  #|(equal (len necessary-pair)
                                         (len matching-pair))|#)))
         #|(- (and (ec-call (subsetp-equal '(sv::bitor HA-S-CHAIN) matching-pair))
         (cwe "should-rewrite: ~p0. matching-pair: ~p1. (car pattern-fn-call-list): ~p2~%"
         should-rewrite matching-pair (car pattern-fn-call-list))))|#
         ((when should-rewrite)
          (car pattern-fn-call-list)))
      (pull-the-first-applicable-adder-pattern pattern-alist
                                               (cdr pattern-fn-call-list))))
  ///

  (defret <fn>-returns-a-member-of-pattern-fn-call-list
    (implies pattern-fn-call
             (member-equal pattern-fn-call pattern-fn-call-list))))

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
            :in-theory (e/d (PATTERN-FN-CALL-PROVIDE-GOOD-MEASURE-P)
                            (pattern-fn-call-list-provide-good-measure-p-and-member
                             adder-pattern-match-good-measure))))))

;; alternatively
(acl2::defines replace-adder-patterns-in-svex

  :flag-local nil

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
           (sv::svex-call x.fn
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
             :expand ((REPLACE-ADDER-PATTERNS-IN-SVEX X PATTERN-ALIST pass-num)
                      (REPLACE-ADDER-PATTERNS-IN-SVEXLIST LST PATTERN-ALIST pass-num)
                      (:free (cons x y)
                             (sv::Svex-eval$ (cons x y) env)))
             :in-theory (e/d (SV::SVEX-EVAL$
                              SV::SVEXlist-EVAL$
                              ;;SV::SVEX-CALL->FN
                              SV::FNSYM-FIX
                              ;;SV::SVEX-CALL->ARGS
                              sv::svex-kind
                              SV::SVEX-P
                              pattern-fn-call-accessors-to-svex-call-accessors
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

(define rewrite-adders-in-svex ((svex sv::Svex-p))
  :Returns (res sv::Svex-p :hyp (sv::svex-p svex))
  (b* ((- (cw "Starting: rp::rewrite-adders-in-svex ~%"))
       (- (time-tracker :rewrite-adders-in-svex :end))
       (- (time-tracker :rewrite-adders-in-svex :init
                        :times '(1 2 3 4 5)
                        :interval 5
                        ))
       (- (time-tracker :rewrite-adders-in-svex :start!))
       ((mv pattern-alist &)
        (gather-adder-patterns-in-svex svex nil nil 1))
       (svex (replace-adder-patterns-in-svex svex pattern-alist 1))

       ((mv pattern-alist &)
        (gather-adder-patterns-in-svex svex nil nil 2))
       (svex (replace-adder-patterns-in-svex svex pattern-alist 2))
       
       (- (time-tracker :rewrite-adders-in-svex :stop))
       (- (time-tracker :rewrite-adders-in-svex :print?
                        :min-time 0
                        :msg "Two passed took ~st seconds."))
       (- (cw "Finished: rp::rewrite-adders-in-svex ~% ")))
    
    svex)
  ///
  (defret <fn>-is-correct
    (implies (and (force (sv::svex-p svex))
                  (force (warrants-for-adder-pattern-match)))
             (equal (sv::svex-eval$ res env)
                    (sv::svex-eval$ svex env)))
    :fn rewrite-adders-in-svex
    :hints (("Goal"
             :in-theory (e/d () ())))))

(define rewrite-adders-in-svex-alist ((svex-alist sv::Svex-alist-p))
  :Returns (res sv::Svex-alist-p :hyp (sv::Svex-alist-p svex-alist))
  (b* ((- (cw "Starting: rp::rewrite-adders-in-svex-alist. ~%"))
       (- (time-tracker :rewrite-adders-in-svex :end))
       (- (time-tracker :rewrite-adders-in-svex :init
                        :times '(1 2 3 4 5)
                        :interval 5
                        ))
       (- (time-tracker :rewrite-adders-in-svex :start!))
       ((mv pattern-alist &)
        (gather-adder-patterns-in-svex-alist svex-alist nil nil 1))
       (svex-alist (replace-adder-patterns-in-svex-alist svex-alist pattern-alist 1))

       (- (time-tracker :rewrite-adders-in-svex :stop))
       (- (time-tracker :rewrite-adders-in-svex :print?
                        :min-time 0
                        :msg "1st pass took ~st secs."))

       (- (time-tracker :rewrite-adders-in-svex :end))
       (- (time-tracker :rewrite-adders-in-svex :init
                        :times '(1 2 3 4 5)
                        :interval 5
                        ))
       (- (time-tracker :rewrite-adders-in-svex :start!))
       ((mv pattern-alist &)
        (gather-adder-patterns-in-svex-alist svex-alist nil nil 2))
       (svex-alist (replace-adder-patterns-in-svex-alist svex-alist pattern-alist 2))

       (- (time-tracker :rewrite-adders-in-svex :stop))
       (- (time-tracker :rewrite-adders-in-svex :print?
                        :min-time 0
                        :msg "2nd pass took ~st secs."))
       
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
  :disabled t
  :hints (("Goal"
           :use ((:instance svl::svex-alist-reduce-w/-env-correct
                            (svl::Svex-alist alist)
                            (svl::env nil)
                            (svl::env-term ''nil)))
           :in-theory (e/d () ()))))


(defmacro defthmrp-multiplier (&rest args)
  `(encapsulate
     nil

     
     (local
      (disable-rules '((:meta svl::svex-alist-eval-meta
                              .
                              sv::svex-alist-eval))))
     
     (local
      (enable-rules '(trigger-rewrite-adders-in-svex-alist
                      (:meta svl::svex-alist-eval-meta-w/o-svexl
                             .
                             sv::svex-alist-eval))))
     (defthmrp ,@args)))


;; :i-am-here

;; (include-book "svtv-top")

;; (defthmrp-multiplier mult-correct-test-with-svtv-
;;   (implies (and (warrants-for-adder-pattern-match)
;;                 (integerp x)
;;                 (integerp y))
;;            (b* (((sv::svassocs design_res)
;;                  (sv::svtv-run (mult1-svtv)
;;                                `((a . ,x)
;;                                  (b . ,y))
;;                                :include '(design_res))))
;;              (equal design_res
;;                     (Loghead 256 (* (logext 128 x)
;;                                     (logext 128 y))))))
;;   :lambda-opt nil)

;; :i-am-here

;; (set-evisc-tuple '(nil 6 7 nil))

;; (time$
;;  (b* ((svex (cdr (assoc-equal 'design_res (sv::svtv->outexprs (mult1-svtv)))))
;;       ;;(svex (svl::hons-list 'sv::partsel 0 3 svex))
;;       (svex (time$ (svl::svex-reduce-w/-env svex nil)))
;;       ((mv pattern-alist &)
;;        (time$ (gather-adder-patterns-in-svex svex nil nil)))
;;       ;;(- (cw "pattern-alist: ~p0" pattern-alist))
;;       (res
;;        (time$ (replace-adder-patterns-in-svex svex pattern-alist)))

;;       (res (time$ (svl::svex-to-svexl res)))

;;       )
;;    (len res)))

;; #|(progn
;; (defwarrant-rp  HA-C-CHAIN)
;; (add-rp-rule APPLY$-FA-C-CHAIN)
;; (add-rp-rule APPLY$-HA-S-CHAIN)
;; (add-rp-rule APPLY$-FA-S-CHAIN)

;; (rp::disable-rules
;; '((:executable-counterpart APPLY$-WARRANT-HA-C-CHAIN)
;; (:executable-counterpart APPLY$-WARRANT-FA-C-CHAIN)
;; (:executable-counterpart APPLY$-WARRANT-HA-S-CHAIN)
;; (:executable-counterpart APPLY$-WARRANT-FA-S-CHAIN))))|#


;; ;;(bump-rule trigger-rewrite-adders-in-svex-alist)



;; (b* ((svex (cdr (assoc-equal 'design_res (sv::svtv->outexprs (mult1-svtv)))))
;;      ;;(svex (svl::hons-list 'sv::partsel 0 3 svex))
;;      (- (cw "entering hons-copy ~%"))
;;      (svex (hons-copy svex))
;;      (- (cw "entering svl::svex-reduce-w/-env ~%"))
;;      (svex (time$ (svl::svex-reduce-w/-env svex nil)))

;;      (- (cw "entering gather-adder-patterns-in-svex ~%"))
;;      ((mv pattern-alist &)
;;       (time$ (gather-adder-patterns-in-svex svex nil nil)))
;;      ;;(- (cw "pattern-alist: ~p0" pattern-alist))

;;      (- (cw "entering replace-adder-patterns-in-svex ~%"))
;;      (res
;;       (time$ (replace-adder-patterns-in-svex svex pattern-alist)))

;;      (- (cw "entering svl::svex-to-svexl ~%"))
;;      (svexl (time$ (svl::svex-to-svexl res)))

;;      )
;;   svexl)
