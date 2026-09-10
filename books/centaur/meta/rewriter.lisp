; Centaur Meta-reasoning Library
; SPDX-FileCopyrightText: Copyright 2025 Arm Limited and/or its affiliates <open-source-office@arm.com>
; SPDX-License-Identifier: BSD-3-Clause
; 
; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holder nor the names of
;   its contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Author: Sol Swords <sol.swords@arm.com>
; (assisted by Codex/GPT5.5)

(in-package "CMR")

(include-book "centaur/meta/parse-rewrite" :dir :system)
(include-book "centaur/meta/unify" :dir :system)
(include-book "centaur/meta/bindinglist" :dir :system)
(include-book "centaur/meta/substitute" :dir :system)
(include-book "centaur/fty/baselists" :dir :system)
(include-book "std/alists/fast-alist-clean" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :System)

(local (include-book "std/alists/alistp" :dir :system))
(local (include-book "std/alists/pairlis" :dir :system))
(local (include-book "std/lists/sets" :dir :system))

(local (in-theory (disable pseudo-termp pseudo-term-listp)))
(local (std::add-default-post-define-hook :fix))
(local (set-induction-depth-limit 1))


(defevaluator crw-ev crw-ev-list
  ((typespec-check ts x)
   (if a b c)
   (equal a b)
   (not a)
   (iff a b)
   (implies a b)
   (return-last x y z)
   (cons x y)
   (binary-+ x y))
  :namedp t)

(acl2::def-ev-pseudo-term-fty-support crw-ev crw-ev-list)
(acl2::def-meta-extract crw-ev crw-ev-list)

(fty::defmap crw-rewrite-rule-alist
  :parents (crw-rewriter)
  :short "Rewrite rules organized by the leading function symbol of their LHS."
  :key-type pseudo-fnsym
  :val-type rewritelist
  :true-listp t)

(define crw-rewrite-rule-lhs-fn ((rule rewrite-p))
  :parents (crw-rewriter)
  :returns (fn pseudo-fnsym-p)
  (b* ((lhs (rewrite->lhs rule)))
    (pseudo-term-case lhs
      :fncall lhs.fn
      :otherwise nil)))

(define crw-add-rewrite-rule-to-alist ((fn pseudo-fnsym-p)
                                         (rule rewrite-p)
                                         (x crw-rewrite-rule-alist-p))
  :parents (crw-rewriter)
  :returns (new-x crw-rewrite-rule-alist-p)
  (b* ((fn (pseudo-fnsym-fix fn))
       (rule (rewrite-fix rule))
       (x (crw-rewrite-rule-alist-fix x))
       (rules (cdr (hons-assoc-equal fn x))))
    (hons-acons fn (cons rule rules) x)))

(define crw-organize-rules-by-lhs-fn-aux ((x rewritelist-p)
                                            (acc crw-rewrite-rule-alist-p))
  :parents (crw-rewriter)
  :returns (rule-alist crw-rewrite-rule-alist-p)
  (if (atom x)
      (crw-rewrite-rule-alist-fix acc)
    (crw-add-rewrite-rule-to-alist
     (crw-rewrite-rule-lhs-fn (car x))
     (car x)
     (crw-organize-rules-by-lhs-fn-aux (cdr x) acc))))

(define crw-organize-rules-by-lhs-fn ((x rewritelist-p))
  :parents (crw-rewriter)
  :returns (rule-alist crw-rewrite-rule-alist-p)
  (fast-alist-free
   (fast-alist-clean (crw-organize-rules-by-lhs-fn-aux x nil))))

(define crw-rewrite-rule-alist-lookup ((fn pseudo-fnsym-p)
                                         (x crw-rewrite-rule-alist-p))
  :parents (crw-rewriter)
  :returns (rules rewritelist-p)
  (cdr (hons-assoc-equal (pseudo-fnsym-fix fn)
                         (crw-rewrite-rule-alist-fix x))))

(defprod crw-rewrite-config
  ((rules rewritelist-p
          "Rules, typically produced by @(see parse-rewrites-from-term).")
   (rules-by-fn crw-rewrite-rule-alist-p
                "Rules organized by the leading function symbol of their LHS.")
   (executable-fns symbol-listp
                   "Function symbols that may be executed on ground arguments.")
   (repeat-limit natp
                 "Fuel consumed by rule applications and hypothesis relief."))
  :layout :list)

(define crw-make-config ((rules rewritelist-p)
                           &key
                           ((executable-fns symbol-listp) 'nil)
                           ((repeat-limit natp) '1000))
  :parents (crw-rewriter)
  :returns (config crw-rewrite-config-p)
  (make-crw-rewrite-config :rules rules
                             :rules-by-fn
                             (crw-organize-rules-by-lhs-fn rules)
                             :executable-fns executable-fns
                             :repeat-limit repeat-limit))



(define crw-not-term ((x pseudo-termp))
  :returns (not-x pseudo-termp)
  (if (pseudo-term-case x :fncall (eq x.fn 'not) :otherwise nil)
      (first (pseudo-term-call->args x))
    (pseudo-term-fncall 'not (list x)))
  ///
  (defthm crw-ev-of-crw-not-term
    (iff (crw-ev (crw-not-term x) env)
         (not (crw-ev x env)))
    :hints(("Goal" :in-theory (enable crw-not-term
                                      crw-ev-of-fncall-args)))))

(define crw-quote-true-p ((x pseudo-termp))
  :returns (truep booleanp :rule-classes :type-prescription)
  (pseudo-term-case x
    :quote (if x.val t nil)
    :otherwise nil)
  ///
  (defthm crw-quote-true-p-correct
    (implies (crw-quote-true-p x)
             (crw-ev x env))
    :hints(("Goal" :in-theory (enable crw-quote-true-p)))))

(define crw-quote-false-p ((x pseudo-termp))
  :returns (falsep booleanp :rule-classes :type-prescription)
  (pseudo-term-case x
    :const (not x.val)
    :otherwise nil)
  ///

  (defthm crw-quote-false-p-correct
    (implies (crw-quote-false-p x)
             (not (crw-ev x env)))
    :hints(("Goal" :in-theory (enable crw-quote-false-p)))))

(defines crw-term-knownp
  :flag-local nil
  (define crw-term-known-true-p ((x pseudo-termp)
                                   (assumptions pseudo-term-listp))
    :measure (pseudo-term-count x)
    :returns (knownp booleanp :rule-classes :type-prescription)
    (or (crw-quote-true-p x)
        (and (member-equal (pseudo-term-fix x)
                           (pseudo-term-list-fix assumptions)) t)
        (pseudo-term-case x
          :fncall (and (eq x.fn 'not)
                       (eql (len x.args) 1)
                       (crw-term-known-false-p (first x.args) assumptions))
          :otherwise nil)))

  (define crw-term-known-false-p ((x pseudo-termp)
                                    (assumptions pseudo-term-listp))
    :measure (pseudo-term-count x)
    :returns (knownp booleanp :rule-classes :type-prescription)
    (or (crw-quote-false-p x)
        (and (member-equal (crw-not-term x) (pseudo-term-list-fix assumptions)) t)
        (pseudo-term-case x
          :fncall (and (eq x.fn 'not)
                       (eql (len x.args) 1)
                       (crw-term-known-true-p (first x.args) assumptions))
          :otherwise nil)))
  ///
  (fty::deffixequiv-mutual crw-term-knownp))

(define crw-iff-fix ((iffp booleanp) x)
  (if iffp (acl2::bool-fix x) x)
  ///
  (defthm crw-iff-fix-of-nil
    (equal (crw-iff-fix nil x) x))

  (defthm crw-iff-fix-of-t
    (equal (crw-iff-fix t x) (acl2::bool-fix x))))

(define crw-simplify-term-by-assumptions ((x pseudo-termp)
                                          (assumptions pseudo-term-listp)
                                          (iffp booleanp))
  :parents (crw-rewriter)
  :short "Simplify a term to a Boolean constant when assumptions imply it."
  :returns (new-x pseudo-termp)
  (b* ((x (pseudo-term-fix x))
       ((unless iffp) x))
    (cond ((crw-term-known-true-p x assumptions) ''t)
          ((crw-term-known-false-p x assumptions) ''nil)
          (t x))))

(local
 (defthm true-listp-of-crw-ev-list
   (true-listp (crw-ev-list x a))
   :hints (("goal" :induct (len x)))
   :rule-classes :type-prescription))

(define crw-ev-bindinglist ((x bindinglist-p) (a alistp))
  :verify-guards nil
  :returns (final-alist alistp)
  (b* (((when (atom x)) (acl2::alist-fix a))
       ((binding x1) (car x))
       (new-bindings (pairlis$ x1.formals (crw-ev-list x1.args a))))
    (crw-ev-bindinglist (cdr x) (append new-bindings a)))
  ///
  (defthm crw-ev-bindinglist-when-atom
    (implies (atom x)
             (equal (crw-ev-bindinglist x a)
                    (acl2::alist-fix a)))
    :hints (("goal" :in-theory (enable crw-ev-bindinglist)))))

(acl2::def-functional-instance crw-ev-of-lambda-nest-to-bindinglist
  lambda-nest-to-bindinglist-correct
  ((base-ev crw-ev)
   (base-ev-list crw-ev-list)
   (base-ev-bindinglist crw-ev-bindinglist))
  :hints (("goal" :in-theory (enable crw-ev-bindinglist
                                      crw-ev-of-fncall-args))))

(acl2::def-functional-instance crw-ev-of-alist-fix
  base-ev-of-alist-fix
  ((base-ev crw-ev)
   (base-ev-list crw-ev-list)))

(acl2::def-functional-instance crw-ev-list-of-alist-fix
  base-ev-list-of-alist-fix
  ((base-ev crw-ev)
   (base-ev-list crw-ev-list)))

(define crw-ev-alist ((x pseudo-term-subst-p) a)
  :verify-guards nil
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (pseudo-var-p (caar x))))
        (cons (cons (caar x) (crw-ev (cdar x) a))
              (crw-ev-alist (cdr x) a))
      (crw-ev-alist (cdr x) a)))
  ///

  (defthm lookup-in-crw-ev-alist-split
    (equal (assoc k (crw-ev-alist x a))
           (and (pseudo-var-p k)
                (let ((look (assoc k x)))
                  (and look
                       (cons k (crw-ev (cdr look) a))))))
    :hints (("goal" :induct (crw-ev-alist x a))))

  (local (in-theory (enable pseudo-term-subst-fix))))

(acl2::def-functional-instance crw-ev-of-term-subst
  base-ev-of-term-subst
  ((base-ev crw-ev)
   (base-ev-list crw-ev-list)
   (base-ev-alist crw-ev-alist))
  :hints(("Goal" :in-theory (enable crw-ev-alist))))

(defthm alistp-of-crw-ev-alist
  (alistp (crw-ev-alist x env))
  :hints (("goal" :in-theory (enable crw-ev-alist))))

(define crw-subst-env ((subst pseudo-term-subst-p) env)
  :verify-guards nil
  (append (crw-ev-alist subst env) (acl2::alist-fix env))
  ///

  (defthm alistp-of-crw-subst-env
    (alistp (crw-subst-env subst env)))

  (defthm crw-subst-env-of-nil
    (equal (crw-subst-env nil env)
           (acl2::alist-fix env))
    :hints (("goal" :in-theory (enable crw-ev-alist))))

  (defthm crw-ev-of-crw-subst-env-of-nil
    (equal (crw-ev x (crw-subst-env nil env))
           (crw-ev x env)))

  (defthm crw-ev-list-of-crw-subst-env-of-nil
    (equal (crw-ev-list x (crw-subst-env nil env))
           (crw-ev-list x env))))

(local
 (defthm crw-alist-fix-of-append
   (equal (acl2::alist-fix (append x y))
          (append (acl2::alist-fix x) (acl2::alist-fix y)))))

;; (local
;;  (defthmd crw-append-alist-fix-to-alist-fix-append
;;    (implies (alistp x)
;;             (equal (append x (acl2::alist-fix y))
;;                    (acl2::alist-fix (append x y))))))

(defthm crw-ev-of-append-alist-fix
  (equal (crw-ev x (append a (acl2::alist-fix env)))
         (crw-ev x (append a env)))
  :hints (("goal" :do-not-induct t
           :use ((:instance crw-ev-of-alist-fix
                  (a (append a env)))
                 (:instance crw-ev-of-alist-fix
                  (a (append a (acl2::alist-fix env)))))
           :in-theory (e/d ()
                           (crw-ev-of-alist-fix)))))

(defthm crw-ev-list-of-append-alist-fix
  (equal (crw-ev-list x (append a (acl2::alist-fix env)))
         (crw-ev-list x (append a env)))
  :hints (("goal" :induct (len x))))

(local
 (defthm crw-assoc-equal-of-alist-fix-when-pseudo-var-p
   (implies (pseudo-var-p k)
            (equal (assoc-equal k (acl2::alist-fix x))
                   (assoc-equal k x)))
   :hints (("goal" :in-theory (enable acl2::alist-fix)))))

(defthm crw-lookup-in-crw-subst-env-split
  (implies (pseudo-var-p k)
           (equal (assoc-equal k (crw-subst-env subst env))
                  (or (and (pseudo-var-p k)
                           (let ((look (assoc-equal k subst)))
                             (and look
                                  (cons k (crw-ev (cdr look) env)))))
                      (assoc-equal k env))))
  :hints (("goal" :in-theory (enable crw-subst-env
                                     crw-ev-alist
                                     lookup-in-crw-ev-alist-split))))

(defthm crw-pseudo-term-subst-p-of-append
  (implies (and (pseudo-term-subst-p x)
                (pseudo-term-subst-p y))
           (pseudo-term-subst-p (append x y))))

(local
 (defthm crw-symbol-listp-when-pseudo-var-list-p
   (implies (pseudo-var-list-p x)
            (symbol-listp x))))

(define crw-extend-subst ((formals pseudo-var-list-p)
                            (args pseudo-term-listp)
                            (subst pseudo-term-subst-p))
  :guard (equal (len formals) (len args))
  :returns (new-subst pseudo-term-subst-p)
  (append (pairlis$ (pseudo-var-list-fix formals)
                    (pseudo-term-list-fix args))
          (pseudo-term-subst-fix subst)))

(defsection crw-rewrite-rules-validp
  (defun-sk crw-rewrite-rules-validp (rules)
    (forall env
            (crw-ev (conjoin (rewritelist-terms rules))
                         env)))

  (in-theory (disable crw-rewrite-rules-validp
                      crw-rewrite-rules-validp-necc))

  (defthm crw-rewrite-rules-validp-of-rewritelist-fix
    (iff (crw-rewrite-rules-validp (rewritelist-fix rules))
         (crw-rewrite-rules-validp rules))
    :hints (("goal" :in-theory (enable crw-rewrite-rules-validp)
             :use ((:instance crw-rewrite-rules-validp-necc
                    (env (crw-rewrite-rules-validp-witness
                          (rewritelist-fix rules))))
                   (:instance crw-rewrite-rules-validp-necc
                    (rules (rewritelist-fix rules))
                    (env (crw-rewrite-rules-validp-witness rules))))))))

(defsection crw-rewrite-rule-validp

  (defun-sk crw-rewrite-rule-validp (rule)
    (forall env
            (crw-ev (rewrite-term rule) env)))

  (in-theory (disable crw-rewrite-rule-validp
                      crw-rewrite-rule-validp-necc))

  (defthm crw-rewrite-rule-validp-of-car
    (implies (and (crw-rewrite-rules-validp rules)
                  (consp rules))
             (crw-rewrite-rule-validp (car rules)))
    :hints (("goal" :in-theory (enable crw-rewrite-rule-validp
                                       rewritelist-terms
                                       crw-ev-conjoin-when-consp)
             :use ((:instance crw-rewrite-rules-validp-necc
                    (env (crw-rewrite-rule-validp-witness
                          (car rules))))))))

  (defthm crw-rewrite-rules-validp-of-cdr
    (implies (crw-rewrite-rules-validp rules)
             (crw-rewrite-rules-validp (cdr rules)))
    :hints (("goal" :in-theory (enable crw-rewrite-rules-validp
                                       rewritelist-terms
                                       crw-ev-conjoin-when-consp)
             :use ((:instance crw-rewrite-rules-validp-necc
                    (env (crw-rewrite-rules-validp-witness
                          (cdr rules))))))))

  (defthm crw-rewrite-rules-validp-of-nil
    (crw-rewrite-rules-validp nil)
    :hints (("goal" :in-theory (enable crw-rewrite-rules-validp
                                       rewritelist-terms))))

  (defthm crw-rewrite-rules-validp-of-cons
    (implies (and (crw-rewrite-rule-validp rule)
                  (crw-rewrite-rules-validp rest))
             (crw-rewrite-rules-validp (cons rule rest)))
    :hints (("goal" :in-theory (enable crw-rewrite-rules-validp
                                       rewritelist-terms
                                       crw-ev-conjoin-when-consp)
             :use ((:instance crw-rewrite-rule-validp-necc
                    (env (crw-rewrite-rules-validp-witness
                          (cons rule rest))))
                   (:instance crw-rewrite-rules-validp-necc
                    (rules rest)
                    (env (crw-rewrite-rules-validp-witness
                          (cons rule rest))))))))

  (defthm crw-rewrite-rule-validp-of-rewrite-fix
    (iff (crw-rewrite-rule-validp (rewrite-fix rule))
         (crw-rewrite-rule-validp rule))
    :hints (("goal" :in-theory (enable crw-rewrite-rule-validp)
             :use ((:instance crw-rewrite-rule-validp-necc
                    (env (crw-rewrite-rule-validp-witness
                          (rewrite-fix rule))))
                   (:instance crw-rewrite-rule-validp-necc
                    (rule (rewrite-fix rule))
                    (env (crw-rewrite-rule-validp-witness rule))))))))

(define crw-rewrite-rule-alist-validp ((x crw-rewrite-rule-alist-p))
  :verify-guards nil
  :returns (validp booleanp :rule-classes :type-prescription)
  (if (atom x)
      t
    (and (or (not (mbt (and (consp (car x))
                            (pseudo-fnsym-p (caar x)))))
             (crw-rewrite-rules-validp (cdar x)))
         (crw-rewrite-rule-alist-validp (cdr x))))
  ///

  (defthm crw-rewrite-rule-alist-validp-of-fix
    (implies (crw-rewrite-rule-alist-validp x)
             (crw-rewrite-rule-alist-validp
              (crw-rewrite-rule-alist-fix x)))
    :hints (("goal" :in-theory (enable crw-rewrite-rule-alist-validp
                                       crw-rewrite-rule-alist-fix))))

  (defthm crw-rewrite-rules-validp-of-hons-assoc-equal
    (implies (crw-rewrite-rule-alist-validp x)
             (crw-rewrite-rules-validp
              (cdr (hons-assoc-equal fn (crw-rewrite-rule-alist-fix x)))))
    :hints (("goal" :in-theory (enable crw-rewrite-rule-alist-validp
                                       crw-rewrite-rule-alist-fix
                                       crw-rewrite-rules-validp-of-nil
                                       hons-assoc-equal))))

  (defthm crw-rewrite-rule-alist-validp-of-add-rule
    (implies (and (crw-rewrite-rule-validp rule)
                  (crw-rewrite-rule-alist-validp x))
             (crw-rewrite-rule-alist-validp
              (crw-add-rewrite-rule-to-alist fn rule x)))
    :hints (("goal" :in-theory (enable crw-add-rewrite-rule-to-alist
                                       crw-rewrite-rule-alist-validp))))

  (defthm crw-rewrite-rule-alist-validp-of-organize-rules-aux
    (implies (and (crw-rewrite-rules-validp rules)
                  (crw-rewrite-rule-alist-validp acc))
             (crw-rewrite-rule-alist-validp
              (crw-organize-rules-by-lhs-fn-aux rules acc)))
    :hints (("goal" :in-theory (enable crw-organize-rules-by-lhs-fn-aux))))

  (local
   (defthm crw-rewrite-rule-alist-validp-of-fast-alist-fork
     (implies (and (crw-rewrite-rule-alist-validp x)
                   (crw-rewrite-rule-alist-validp y))
              (crw-rewrite-rule-alist-validp (fast-alist-fork x y)))
     :hints (("goal" :in-theory (enable fast-alist-fork
                                        crw-rewrite-rule-alist-validp)))))

  (local
   (defthm crw-rewrite-rule-alist-validp-of-cdr-last
     (implies (crw-rewrite-rule-alist-validp x)
              (crw-rewrite-rule-alist-validp (cdr (last x))))
     :hints (("goal" :in-theory (enable crw-rewrite-rule-alist-validp)))))

  (defthm crw-rewrite-rule-alist-validp-of-fast-alist-clean
    (implies (crw-rewrite-rule-alist-validp x)
             (crw-rewrite-rule-alist-validp (fast-alist-clean x)))
    :hints (("goal" :do-not-induct t
             :in-theory (enable fast-alist-clean))))

  (defthm crw-rewrite-rule-alist-validp-of-organize-rules
    (implies (crw-rewrite-rules-validp rules)
             (crw-rewrite-rule-alist-validp
              (crw-organize-rules-by-lhs-fn rules)))
    :hints (("goal" :in-theory (enable crw-organize-rules-by-lhs-fn
                                       crw-rewrite-rule-alist-validp))))

  (defthm crw-rewrite-rules-validp-of-rule-alist-lookup
    (implies (crw-rewrite-rule-alist-validp x)
             (crw-rewrite-rules-validp
              (crw-rewrite-rule-alist-lookup fn x)))
    :hints (("goal" :in-theory (enable crw-rewrite-rule-alist-lookup
                                       crw-rewrite-rule-alist-validp
                                       crw-rewrite-rules-validp-of-nil))))

  (local (in-theory (enable crw-rewrite-rule-alist-fix))))

(define crw-config-okp ((config crw-rewrite-config-p))
  :verify-guards nil
  :returns (okp booleanp :rule-classes :type-prescription)
  (and (crw-rewrite-rules-validp
        (crw-rewrite-config->rules config))
       (crw-rewrite-rule-alist-validp
        (crw-rewrite-config->rules-by-fn config))
       t)
  ///

  (defthm crw-config-okp-forward
    (implies (crw-config-okp config)
             (and (crw-rewrite-rules-validp
                   (crw-rewrite-config->rules config))
                  (crw-rewrite-rule-alist-validp
                   (crw-rewrite-config->rules-by-fn config))))
    :hints (("goal" :in-theory (enable crw-config-okp)))
    :rule-classes :forward-chaining)

  (defthm crw-config-okp-of-crw-make-config
    (implies (and (crw-rewrite-rules-validp rules))
             (crw-config-okp (crw-make-config rules
                                               :executable-fns executable-fns)))
    :hints(("Goal" :in-theory (enable crw-make-config)))))

(local
 (defthm crw-ev-when-member-of-conjoin
   (implies (and (member-equal x
                               (pseudo-term-list-fix assumptions))
                 (not (crw-ev x env)))
            (not (crw-ev (conjoin assumptions) env)))
   :hints(("Goal" :induct (len assumptions)
           :in-theory (enable crw-ev-conjoin-when-consp)))))

(defthm crw-rewrite-rule-validp-implies-equal-nonstrict
  (implies (and (crw-rewrite-rule-validp rule)
                (equal (rewrite->equiv rule) 'equal)
                (crw-ev
                 (conjoin (rewrite->hyps rule))
                 (crw-subst-env subst env)))
           (equal
            (crw-ev
             (rewrite->rhs rule)
             (crw-subst-env subst env))
            (crw-ev
             (rewrite->lhs rule)
             (crw-subst-env subst env))))
  :hints (("goal" :use ((:instance crw-rewrite-rule-validp-necc
                         (env (crw-subst-env subst env))))
           :in-theory (enable rewrite-term
                              crw-ev-of-fncall-args))))

(defthm crw-rewrite-rule-validp-implies-iff-nonstrict
  (implies (and (crw-rewrite-rule-validp rule)
                (equal (rewrite->equiv rule) 'iff)
                (crw-ev
                 (conjoin (rewrite->hyps rule))
                 (crw-subst-env subst env)))
           (iff
            (crw-ev
             (rewrite->rhs rule)
             (crw-subst-env subst env))
            (crw-ev
             (rewrite->lhs rule)
             (crw-subst-env subst env))))
  :hints (("goal" :use ((:instance crw-rewrite-rule-validp-necc
                         (env (crw-subst-env subst env))))
           :in-theory (enable rewrite-term
                              crw-ev-of-fncall-args))))

(local
 (defthm crw-alistp-when-pseudo-term-subst-p
   (implies (pseudo-term-subst-p x)
            (alistp x))
   :rule-classes :forward-chaining))

(local
 (defthm crw-hons-assoc-equal-when-assoc-equal
   (implies (alistp x)
            (equal (hons-assoc-equal k x)
                   (assoc-equal k x)))
   :hints (("goal" :in-theory (enable hons-assoc-equal)))))

(local
 (defthm-term-subst-flag
   (defthm term-subst-when-vars-bound
     (implies (and (pseudo-term-subst-p a)
                   (subsetp (term-vars x) (alist-keys a)))
              (equal (term-subst x a)
                     (term-subst-strict x a)))
     :flag term-subst)
   (defthm termlist-subst-when-vars-bound
     (implies (and (pseudo-term-subst-p a)
                   (subsetp (termlist-vars x) (alist-keys a)))
              (equal (termlist-subst x a)
                     (termlist-subst-strict x a)))
     :flag termlist-subst)
   :hints (("goal" :expand ((term-subst x a)
                             (term-subst-strict x a)
                             (termlist-subst x a)
                             (termlist-subst-strict x a)
                             (term-vars x)
                             (termlist-vars x))
            :in-theory (enable alist-keys)))))

(acl2::def-functional-instance term-unify-reversible-crw-ev
  term-unify-reversible
  ((unify-ev crw-ev)
   (unify-ev-list crw-ev-list)
   (unify-ev-alist crw-ev-alist))
  :hints(("Goal" :in-theory (enable crw-ev-alist
                                    crw-ev-of-fncall-args))))

(defthm crw-ev-of-unify-lhs-under-crw-subst-env
  (implies (mv-nth 0 (term-unify lhs x nil))
           (equal (crw-ev lhs
                               (crw-subst-env
                                (mv-nth 1 (term-unify lhs x nil))
                                env))
                  (crw-ev x env)))
  :hints (("goal"
           :use (;; (:instance term-unify-reversible
                 ;;  (pat lhs) (x x) (alist nil))
                 (:instance term-vars-subsetp-of-term-unify
                  (pat lhs) (x x) (alist nil))
                 (:instance crw-ev-of-term-subst
                  (x lhs)
                  (a (mv-nth 1 (term-unify lhs x nil)))))
           :in-theory (e/d (crw-subst-env)
                           (term-vars-subsetp-of-term-unify
                            crw-ev-of-term-subst)))))

(defthm crw-ev-alist-of-pair-vars
  (equal (crw-ev-alist (pair-vars x y) env)
         (pair-vars x (crw-ev-list y env)))
  :hints (("goal" :in-theory (enable crw-ev-alist pair-vars))))

(defthm crw-ev-alist-of-append
  (implies (pseudo-term-subst-p x)
           (equal (crw-ev-alist (append x y) env)
                  (append (crw-ev-alist x env)
                          (crw-ev-alist y env))))
  :hints (("goal" :in-theory (enable crw-ev-alist))))

(defthm pair-vars-when-pseudo-var-list-p
  (implies (pseudo-var-list-p x)
           (equal (pair-vars x y)
                  (pairlis$ x y)))
  :hints (("goal" :in-theory (enable pair-vars pairlis$))))

(defthm crw-ev-alist-of-pairlis$
  (implies (and (pseudo-var-list-p x)
                (pseudo-term-listp y)
                (equal (len x) (len y)))
           (equal (crw-ev-alist (pairlis$ x y) env)
                  (pairlis$ x (crw-ev-list y env))))
  :hints (("goal" :in-theory (enable crw-ev-alist pairlis$))))

(defthm crw-ev-alist-of-crw-extend-subst
  (implies (and (pseudo-var-list-p formals)
                (equal (len formals) (len args))
                (pseudo-term-listp args)
                (pseudo-term-subst-p subst))
           (equal (crw-ev-alist
                   (crw-extend-subst formals args subst)
                   env)
                  (append (pairlis$ formals (crw-ev-list args env))
                          (crw-ev-alist subst env))))
  :hints (("goal" :in-theory (enable crw-extend-subst
                                     pair-vars-when-pseudo-var-list-p))))

(defthm crw-subst-env-of-crw-extend-subst
  (implies (equal (len formals) (len args))
           (equal (crw-subst-env (crw-extend-subst formals args subst) env)
                  (append (pair-vars (pseudo-var-list-fix formals)
                                     (crw-ev-list args env))
                          (crw-subst-env subst env))))
  :hints (("goal" :in-theory (enable crw-extend-subst
                                     crw-subst-env)
           :induct t)))

(defthm-crw-term-knownp-flag
  (defthm crw-term-known-true-p-correct
    (implies (and (crw-term-known-true-p x assumptions)
                  (crw-ev (conjoin assumptions) env))
             (crw-ev x env))
    :flag crw-term-known-true-p)
  (defthm crw-term-known-false-p-correct
    (implies (and (crw-term-known-false-p x assumptions)
                  (crw-ev (conjoin assumptions) env))
             (not (crw-ev x env)))
    :flag crw-term-known-false-p)
  :hints (("goal" :in-theory (enable crw-term-known-true-p
                                     crw-term-known-false-p
                                     crw-not-term
                                     crw-ev-of-fncall-args))))

(defthm crw-ev-when-pseudo-term-kind-var
  (implies (equal (pseudo-term-kind x) :var)
           (equal (crw-ev x env)
                  (cdr (assoc-equal (pseudo-term-var->name x) env))))
  :hints (("goal" :use ((:instance acl2::pseudo-term-var-of-accessors
                         (x x)))
           :in-theory (enable pseudo-term-var->name))))

(defthm crw-term-known-true-p-var-lookup
  (implies (and (equal (pseudo-term-kind x) :var)
                (crw-term-known-true-p x assumptions)
                (crw-ev (conjoin assumptions) env))
           (cdr (assoc-equal (pseudo-term-var->name x) env)))
  :hints (("goal" :use ((:instance crw-term-known-true-p-correct))
           :in-theory (enable crw-ev-when-pseudo-term-kind-var))))

(defthm crw-term-known-false-p-var-lookup
  (implies (and (equal (pseudo-term-kind x) :var)
                (crw-term-known-false-p x assumptions)
                (crw-ev (conjoin assumptions) env))
           (not (cdr (assoc-equal (pseudo-term-var->name x) env))))
  :hints (("goal" :use ((:instance crw-term-known-false-p-correct))
           :in-theory (enable crw-ev-when-pseudo-term-kind-var))))

(defret crw-simplify-term-by-assumptions-correct
  (implies (crw-ev (conjoin assumptions) env)
           (equal (crw-iff-fix iffp (crw-ev new-x env))
                  (crw-iff-fix iffp (crw-ev x env))))
  :hints (("goal" :in-theory (enable crw-simplify-term-by-assumptions
                                     crw-iff-fix)))
  :fn crw-simplify-term-by-assumptions)

(defret crw-simplify-term-by-assumptions-correct-bool
  (implies (crw-ev (conjoin assumptions) env)
           (equal (acl2::bool-fix (crw-ev new-x env))
                  (acl2::bool-fix (crw-ev x env))))
  :hints (("goal" :use ((:instance
                         crw-simplify-term-by-assumptions-correct))
           :in-theory (e/d (crw-iff-fix)
                           (crw-simplify-term-by-assumptions-correct))))
  :fn crw-simplify-term-by-assumptions)

(defret crw-simplify-term-by-assumptions-correct-equal
  (implies (and (not iffp)
                (crw-ev (conjoin assumptions) env))
           (equal (crw-ev new-x env)
                  (crw-ev x env)))
  :hints (("goal" :in-theory (enable crw-simplify-term-by-assumptions)))
  :fn crw-simplify-term-by-assumptions)

(define crw-pseudo-term-quote-listp ((x pseudo-term-listp))
  :returns (ok booleanp :rule-classes :type-prescription)
  (if (atom x)
      t
    (and (pseudo-term-case (car x) :quote)
         (crw-pseudo-term-quote-listp (cdr x))))
  ///

  (defthm crw-pseudo-term-quote-listp-of-cdr
    (implies (and (crw-pseudo-term-quote-listp x)
                  (consp x))
             (crw-pseudo-term-quote-listp (cdr x))))

  (defthm crw-pseudo-term-kind-of-car-when-quote-listp
    (implies (and (crw-pseudo-term-quote-listp x)
                  (consp x))
             (equal (pseudo-term-kind (car x)) :quote))))

(define crw-pseudo-term-quote-list->vals ((x pseudo-term-listp))
  :guard (crw-pseudo-term-quote-listp x)
  :returns vals
  (if (atom x)
      nil
    (cons (pseudo-term-quote->val (car x))
          (crw-pseudo-term-quote-list->vals (cdr x)))))

(defthm crw-ev-list-when-pseudo-term-quote-listp
  (implies (crw-pseudo-term-quote-listp x)
           (equal (crw-ev-list x env)
                  (crw-pseudo-term-quote-list->vals x)))
  :hints (("goal" :in-theory (enable crw-pseudo-term-quote-listp
                                     crw-pseudo-term-quote-list->vals))))

(define crw-maybe-execute-fncall ((fn pseudo-fnsym-p)
                                  (args pseudo-term-listp)
                                  (config crw-rewrite-config-p)
                                  state)
  :parents (crw-rewriter)
  :short "Execute a configured function call whose arguments are quoted constants."
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (term pseudo-termp))
  (b* ((fn (pseudo-fnsym-fix fn))
       (args (pseudo-term-list-fix args))
       ((unless (and (symbolp fn)
                     (not (eq fn 'quote))
                     (acl2::logicp fn (w state))
                     (member-eq fn (crw-rewrite-config->executable-fns config))
                     (crw-pseudo-term-quote-listp args)))
        (mv nil nil))
       ((mv err val)
        (acl2::magic-ev-fncall
         fn (crw-pseudo-term-quote-list->vals args) state t nil))
       ((when err) (mv nil nil)))
    (mv t (pseudo-term-quote val)))
  ///

  (local (defthm crw-ev-of-pseudo-term-fncall-when-quote-args
           (implies (and (symbolp (pseudo-fnsym-fix fn))
                         (not (eq (pseudo-fnsym-fix fn) 'quote))
                         (crw-pseudo-term-quote-listp args))
                    (equal (crw-ev (pseudo-term-fncall fn args) env)
                           (crw-ev (cons (pseudo-fnsym-fix fn)
                                         (kwote-lst
                                          (crw-pseudo-term-quote-list->vals args)))
                                   nil)))
           :hints (("goal" :in-theory (enable crw-ev-of-fncall-args)))))

  (local (defthm crw-ev-of-cons-when-quote-args
           (implies (and (symbolp fn)
                         (not (eq fn 'quote))
                         (crw-pseudo-term-quote-listp args))
                    (equal (crw-ev (cons fn args) env)
                           (crw-ev (cons fn
                                         (kwote-lst
                                          (crw-pseudo-term-quote-list->vals args)))
                                   nil)))
           :hints (("goal" :in-theory (enable crw-ev-of-fncall-args)))))

  (defret crw-maybe-execute-fncall-correct
    (implies (and successp
                  (crw-ev-meta-extract-global-facts))
             (equal (crw-ev term env)
                    (crw-ev (pseudo-term-fncall fn args) env)))
    :hints (("goal"
             :use ((:instance crw-ev-meta-extract-fncall
                    (fn (pseudo-fnsym-fix fn))
                    (arglist (crw-pseudo-term-quote-list->vals
                              (pseudo-term-list-fix args)))
                    (st state)))
             :in-theory (e/d (crw-maybe-execute-fncall
                              crw-pseudo-term-quote-listp
                              crw-pseudo-term-quote-list->vals)
                             (crw-ev-meta-extract-fncall))))))

(local (defthmd equal-of-len
         (implies (syntaxp (quotep n))
                  (equal (equal (len x) n)
                         (if (zp n)
                             (and (atom x) (eql n 0))
                           (and (consp x)
                                (equal (len (cdr x)) (1- n))))))))

(local (defthm len-of-cons
         (equal (len (cons x y))
                (+ 1 (len y)))))

(local (defthm len-equal-0
         (equal (equal (len x) 0)
                (not (consp x)))))

(local (in-theory (disable len)))

(define crw-simplify-fncall ((fn pseudo-fnsym-p)
                               (args pseudo-term-listp)
                               (iffp booleanp)
                               (assumptions pseudo-term-listp))
  :returns (term pseudo-termp)
  (b* ((fn (pseudo-fnsym-fix fn))
       (args (pseudo-term-list-fix args)))
    (cond
     ((and (eq fn 'not)
           (eql (len args) 1))
      (b* ((arg (first args)))
        (cond ((crw-term-known-true-p arg assumptions) ''nil)
              ((crw-term-known-false-p arg assumptions) ''t)
              ((crw-quote-true-p arg) ''nil)
              ((crw-quote-false-p arg) ''t)
              (t (pseudo-term-fncall fn args)))))
     ((and (eq fn 'equal)
           (eql (len args) 2))
      (b* ((left (first args))
           (right (second args)))
        (cond ((equal left right) ''t)
              ((and (pseudo-term-case left :const)
                    (pseudo-term-case right :const))
               (pseudo-term-quote
                (equal (acl2::pseudo-term-const->val left)
                       (acl2::pseudo-term-const->val right))))
              (t (pseudo-term-fncall fn args)))))
     ((and (eq fn 'if)
           (eql (len args) 3))
      (b* ((test (first args))
           (then (second args))
           (else (third args)))
        (cond ((crw-term-known-true-p test assumptions) then)
              ((crw-term-known-false-p test assumptions) else)
              ((equal then else) then)
              ((and iffp (equal then ''t) (equal else ''nil)) test)
              (t (pseudo-term-fncall fn args)))))
     ((and (eq fn 'implies)
           (eql (len args) 2))
      (b* ((hyp (first args))
           (concl (second args)))
        (cond ((crw-term-known-false-p hyp assumptions) ''t)
              ((and iffp
                    (crw-term-known-true-p hyp assumptions))
               concl)
              ((crw-term-known-true-p concl assumptions) ''t)
              (t (pseudo-term-fncall fn args)))))
     (t (pseudo-term-fncall fn args))))
  ///
  (local (defthm crw-ev-when-pseudo-term-const
           (implies (pseudo-term-case x :const)
                    (equal (crw-ev x a)
                           (acl2::pseudo-term-const->val x)))))
  
  (local (in-theory (disable
                     member-equal
                     acl2::member-of-cons
                     alistp)))
  
  (defthm crw-simplify-fncall-correct
    (implies (crw-ev (conjoin assumptions) env)
             (equal (crw-iff-fix iffp
                                    (crw-ev (crw-simplify-fncall fn args iffp assumptions)
                                                 env))
                    (crw-iff-fix iffp
                                    (crw-ev (pseudo-term-fncall fn args)
                                                 env))))
    :hints (("goal" 
             :in-theory (e/d (crw-iff-fix
                              crw-ev-of-fncall-args
                              equal-of-len)))))
  
  (defthm crw-simplify-fncall-correct-equal
    (implies (and (not iffp)
                  (crw-ev (conjoin assumptions) env))
             (equal (crw-ev
                     (crw-simplify-fncall fn args iffp assumptions)
                     env)
                    (crw-ev (pseudo-term-fncall fn args) env)))
    :hints (("goal" :use ((:instance crw-simplify-fncall-correct))
             :in-theory (e/d (crw-iff-fix equal-of-len)
                             (crw-simplify-fncall-correct)))))

  (defthm crw-simplify-fncall-correct-bool
    (implies (crw-ev (conjoin assumptions) env)
             (equal (acl2::bool-fix
                     (crw-ev
                      (crw-simplify-fncall fn args iffp assumptions)
                      env))
                    (acl2::bool-fix
                     (crw-ev (pseudo-term-fncall fn args) env))))
    :hints (("goal" :use ((:instance crw-simplify-fncall-correct))
             :in-theory (e/d (crw-iff-fix)
                             (crw-simplify-fncall-correct))))))

(define crw-rewrite-candidate-rules ((fn pseudo-fnsym-p)
                                       (config crw-rewrite-config-p))
  :returns (rules rewritelist-p)
  (crw-rewrite-rule-alist-lookup
   fn
   (crw-rewrite-config->rules-by-fn config))
  ///
  (defthm crw-rewrite-rules-validp-of-candidate-rules
    (implies (crw-rewrite-rule-alist-validp
              (crw-rewrite-config->rules-by-fn config))
             (crw-rewrite-rules-validp
              (crw-rewrite-candidate-rules fn config)))
    :hints (("goal" :in-theory (enable crw-rewrite-candidate-rules)))))

(local
 (defthm crw-pseudo-term-list-binding-count-of-first-three
   (implies (and (consp x)
                 (consp (cdr x))
                 (consp (cddr x)))
            (< (+ (pseudo-term-binding-count (car x))
                  (pseudo-term-binding-count (cadr x))
                  (pseudo-term-binding-count (caddr x)))
               (pseudo-term-list-binding-count x)))
   :hints(("Goal" :expand ((pseudo-term-list-binding-count x)
                           (pseudo-term-list-binding-count (cdr x))
                           (pseudo-term-list-binding-count (cddr x)))))
   :rule-classes :linear))

(local (defthm pseudo-term-binding-count-when-fncall
         (implies (pseudo-term-case x :fncall)
                  (<= 2 (pseudo-term-binding-count x)))
         :hints(("Goal" :expand ((pseudo-term-binding-count x))))
         :rule-classes :linear))


(local (include-book "centaur/vl/util/default-hints" :dir :system))
  
(with-output
  :evisc (:gag-mode '(nil 4 7 nil))
  (defines crw-rewrite
    :flag-local nil
    :well-founded-relation acl2::nat-list-<

    (define crw-rewrite-term-under-subst ((x pseudo-termp)
                                          (subst pseudo-term-subst-p)
                                          (assumptions pseudo-term-listp)
                                          (config crw-rewrite-config-p)
                                          (iffp booleanp)
                                          (limit natp)
                                          state)
      :measure (list (nfix limit) (pseudo-term-binding-count x) 11 0)
      :hints (("goal" :in-theory (enable equal-of-len)))
      :ruler-extenders :all
      :verify-guards nil
      :returns (new-x pseudo-termp)
      (pseudo-term-case x
        :const (crw-simplify-term-by-assumptions x assumptions iffp)
        :var (b* ((look (assoc-eq x.name (pseudo-term-subst-fix subst)))
                  (term (if look (cdr look) (pseudo-term-fix x))))
               (crw-simplify-term-by-assumptions term assumptions iffp))
        :fncall (cond
                 ((and (eq x.fn 'if)
                       (eql (len x.args) 3))
                  (crw-rewrite-if-under-subst (first x.args)
                                              (second x.args)
                                              (third x.args)
                                              subst assumptions config iffp limit state))
                 (t
                  (b* ((args (crw-rewrite-termlist-under-subst
                              x.args subst assumptions config limit state))
                       (simp (crw-simplify-fncall x.fn args iffp assumptions)))
                    (crw-rewrite-top simp assumptions config iffp limit state))))
        :lambda (b* (((mv bindings body) (lambda-nest-to-bindinglist x))
                     (new-subst
                      (crw-rewrite-bindinglist bindings subst assumptions config limit state)))
                  (crw-rewrite-term-under-subst
                            body new-subst assumptions config iffp limit state))))

    (define crw-rewrite-termlist-under-subst ((x pseudo-term-listp)
                                              (subst pseudo-term-subst-p)
                                              (assumptions pseudo-term-listp)
                                              (config crw-rewrite-config-p)
                                              (limit natp)
                                              state)
      :measure (list (nfix limit) (pseudo-term-list-binding-count x) 11 0)
      :ruler-extenders :all
      :returns (new-x pseudo-term-listp)
      (if (atom x)
          nil
        (cons (crw-rewrite-term-under-subst (car x) subst assumptions config nil limit state)
              (crw-rewrite-termlist-under-subst
               (cdr x) subst assumptions config limit state))))

    (define crw-rewrite-bindinglist ((x bindinglist-p)
                                     (subst pseudo-term-subst-p)
                                     (assumptions pseudo-term-listp)
                                     (config crw-rewrite-config-p)
                                     (limit natp)
                                     state)
      :measure (list (nfix limit) (bindinglist-count x) 11 0)
      :ruler-extenders :all
      :returns (new-subst pseudo-term-subst-p)
      (b* (((when (atom x))
            (pseudo-term-subst-fix subst))
           ((binding x1) (car x))
           (args (crw-rewrite-termlist-under-subst
                  x1.args subst assumptions config limit state))
           (new-subst (crw-extend-subst x1.formals args subst)))
        (crw-rewrite-bindinglist (cdr x) new-subst assumptions config limit state)))

    (define crw-rewrite-if-under-subst ((test pseudo-termp)
                                        (then pseudo-termp)
                                        (else pseudo-termp)
                                        (subst pseudo-term-subst-p)
                                        (assumptions pseudo-term-listp)
                                        (config crw-rewrite-config-p)
                                        (iffp booleanp)
                                        (limit natp)
                                        state)
      :measure (list (nfix limit)
                     (+ (pseudo-term-binding-count test)
                        (pseudo-term-binding-count then)
                        (pseudo-term-binding-count else))
                     11
                     0)
      :ruler-extenders :all
      :returns (new-x pseudo-termp)
      (b* ((test2 (crw-rewrite-term-under-subst test subst assumptions config t limit state))
           ((when (crw-term-known-true-p
                   test2 assumptions))
            (crw-rewrite-term-under-subst then subst assumptions config iffp limit state))
           ((when (crw-term-known-false-p
                   test2 assumptions))
            (crw-rewrite-term-under-subst else subst assumptions config iffp limit state))
           (then-assums (cons test2 assumptions))
           (else-assums (cons (crw-not-term test2) assumptions))
           (then2 (crw-rewrite-term-under-subst
                   then subst then-assums config iffp limit state))
           (else2 (crw-rewrite-term-under-subst
                   else subst else-assums config iffp limit state)))
        (crw-simplify-fncall 'if (list test2 then2 else2) iffp assumptions)))

    (define crw-rewrite-top ((x pseudo-termp)
                             (assumptions pseudo-term-listp)
                             (config crw-rewrite-config-p)
                             (iffp booleanp)
                             (limit natp)
                             state)
      :measure (list (nfix limit) 0 8 0)
      :ruler-extenders :all
      :returns (new-x pseudo-termp)
      (b* (((unless (posp limit))
            (pseudo-term-fix x)))
        (pseudo-term-case x
          :fncall (b* (((mv exec-ok exec-term)
                        (crw-maybe-execute-fncall x.fn x.args config state))
                       ((when exec-ok) exec-term)
                       ((mv ok rhs) (crw-try-rewrites
                                     x.fn x.args
                                     (crw-rewrite-candidate-rules
                                      x.fn config)
                                     assumptions config iffp limit state))
                       ((unless ok) (pseudo-term-fix x)))
                    rhs)
          :otherwise (pseudo-term-fix x))))

    (define crw-try-rewrites ((fn pseudo-fnsym-p)
                              (args pseudo-term-listp)
                              (rules rewritelist-p)
                              (assumptions pseudo-term-listp)
                              (config crw-rewrite-config-p)
                              (iffp booleanp)
                              (limit natp)
                              state)
      :measure (list (nfix limit) 0 7 (len rules))
      :ruler-extenders :all
      :returns (mv (successp booleanp :rule-classes :type-prescription)
                   (rhs pseudo-termp))
      (b* (((when (atom rules)) (mv nil nil))
           ((mv ok rhs) (crw-try-rewrite
                         fn args (car rules) assumptions config iffp limit state))
           ((when ok) (mv t rhs)))
        (crw-try-rewrites fn args (cdr rules) assumptions config iffp limit state)))

    (define crw-try-rewrite ((fn pseudo-fnsym-p)
                             (args pseudo-term-listp)
                             (rule rewrite-p)
                             (assumptions pseudo-term-listp)
                             (config crw-rewrite-config-p)
                             (iffp booleanp)
                             (limit natp)
                             state)
      :measure (list (nfix limit) 0 6 0)
      :ruler-extenders :all
      :returns (mv (successp booleanp :rule-classes :type-prescription)
                   (rhs pseudo-termp))
      (b* (((rewrite rule) rule)
           (x (pseudo-term-fncall fn args))
           ((unless (posp limit)) (mv nil nil))
           ((unless (or (eq rule.equiv 'equal)
                        (and iffp (eq rule.equiv 'iff))))
            (mv nil nil))
           ((mv ok subst) (term-unify rule.lhs x nil))
           ((unless ok) (mv nil nil))
           ((unless (crw-relieve-hyps-under-subst
                     rule.hyps subst assumptions config limit state))
            (mv nil nil))
           (rhs (crw-rewrite-term-under-subst
                 rule.rhs subst assumptions config iffp (1- limit) state)))
        (mv t rhs)))

    (define crw-relieve-hyps-under-subst ((hyps pseudo-term-listp)
                                          (subst pseudo-term-subst-p)
                                          (assumptions pseudo-term-listp)
                                          (config crw-rewrite-config-p)
                                          (limit natp)
                                          state)
      :measure (list (nfix limit) 0 5 (len hyps))
      :ruler-extenders :all
      :returns (ok booleanp :rule-classes :type-prescription)
      (b* (((when (atom hyps)) t)
           ((unless (posp limit)) nil)
           (hyp (crw-rewrite-term-under-subst
                 (car hyps) subst assumptions config t (1- limit) state))
           ((unless (crw-term-known-true-p
                     hyp
                     assumptions))
            nil))
        (crw-relieve-hyps-under-subst (cdr hyps) subst assumptions config limit state)))

    ///

    (local
     (make-event `(in-theory (disable . ,(fgetprop 'crw-rewrite-term-under-subst
                                                   'acl2::recursivep nil (w state))))))
  
    (std::defret-mutual len-of-crw-rewrite-termlist
      (defret len-of-crw-rewrite-termlist-under-subst
        (equal (len new-x) (len x))
        :hints ('(:expand (<call>)))
        :fn crw-rewrite-termlist-under-subst)
      :skip-others t)

    (local (in-theory (disable crw-ev-of-if-call)))
  
    (std::defret-mutual <fn>-correct
      (defret <fn>-correct
        (implies (and (crw-ev-meta-extract-global-facts)
                      (crw-config-okp config)
                      (crw-ev (conjoin assumptions) env))
                 (equal (crw-iff-fix
                         iffp
                         (crw-ev new-x env))
                        (crw-iff-fix
                         iffp
                         (crw-ev x (crw-subst-env subst env)))))
        :hints ((and stable-under-simplificationp
                     '(:in-theory (e/d (crw-ev-of-fncall-args))))
                (and stable-under-simplificationp
                     '(:in-theory (enable equal-of-len)))
                )
        :fn crw-rewrite-term-under-subst)
      (defret <fn>-correct
        (implies (and (crw-ev-meta-extract-global-facts)
                      (crw-config-okp config)
                      (crw-ev (conjoin assumptions) env))
                 (equal (crw-ev-list
                         new-x
                         env)
                        (crw-ev-list x (crw-subst-env subst env))))
        :fn crw-rewrite-termlist-under-subst)
      (defret <fn>-correct
        (implies (and (crw-ev-meta-extract-global-facts)
                      (crw-config-okp config)
                      (crw-ev (conjoin assumptions) env))
                 (equal (crw-subst-env
                         new-subst
                         env)
                        (crw-ev-bindinglist
                         x (crw-subst-env subst env))))
        :hints ((and stable-under-simplificationp
                     '(:expand ((:free (env) (CRW-EV-BINDINGLIST x env)))))
                (and stable-under-simplificationp
                     '(:in-theory (enable crw-extend-subst
                                          crw-subst-env))))
        :fn crw-rewrite-bindinglist)
      (defret <fn>-correct
        (implies (and (crw-ev-meta-extract-global-facts)
                      (crw-config-okp config)
                      (crw-ev (conjoin assumptions) env))
                 (equal (crw-iff-fix
                         iffp
                         (crw-ev
                          new-x
                          env))
                        (crw-iff-fix
                         iffp
                         (let ((env (crw-subst-env subst env)))
                           (crw-ev (pseudo-term-call 'if (list test then else)) env)))))
        :hints('(:in-theory (enable crw-ev-of-if-call)))
        :fn crw-rewrite-if-under-subst)
      (defret <fn>-correct
        (implies (and (crw-ev-meta-extract-global-facts)
                      (crw-config-okp config)
                      (crw-ev (conjoin assumptions) env))
                 (equal (crw-iff-fix
                         iffp
                         (crw-ev
                          new-x env))
                        (crw-iff-fix iffp (crw-ev x env))))
        :fn crw-rewrite-top)
      (defret <fn>-correct
        (implies (and successp
                      (crw-ev-meta-extract-global-facts)
                      (crw-config-okp config)
                      (crw-ev (conjoin assumptions) env)
                      (crw-rewrite-rules-validp rules))
                 (equal (crw-iff-fix
                         iffp
                         (crw-ev
                          rhs
                          env))
                        (crw-iff-fix
                         iffp
                         (crw-ev (pseudo-term-fncall fn args) env))))
        :fn crw-try-rewrites)
      (defret <fn>-correct
        (implies (and successp
                      (crw-ev-meta-extract-global-facts)
                      (crw-config-okp config)
                      (crw-ev (conjoin assumptions) env)
                      (crw-rewrite-rule-validp rule))
                 (equal (crw-iff-fix
                         iffp
                         (crw-ev
                          rhs
                          env))
                        (crw-iff-fix
                         iffp
                         (crw-ev (pseudo-term-fncall fn args) env))))
        :fn crw-try-rewrite)
      (defret <fn>-correct
        (implies (and (not (crw-ev (conjoin hyps)
                                   (crw-subst-env subst env)))
                      (crw-ev-meta-extract-global-facts)
                      (crw-config-okp config)
                      (crw-ev (conjoin assumptions) env))
                 (not ok))
        :fn crw-relieve-hyps-under-subst)
      :hints ((vl::big-mutrec-default-hint 'crw-rewrite-top id nil world))
      :mutual-recursion crw-rewrite)
  
    (verify-guards crw-rewrite-term-under-subst)
    (fty::deffixequiv-mutual crw-rewrite)
    ))

(define crw-rewrite-term ((x pseudo-termp)
                          (assumptions pseudo-term-listp)
                          (config crw-rewrite-config-p)
                          (iffp booleanp)
                          (limit natp)
                          state)
  :parents (crw-rewriter)
  :short "Rewrite a pseudo-term inside-out."
  :returns (new-x pseudo-termp)
  (crw-rewrite-term-under-subst x nil assumptions config iffp limit state)
  ///
  (defret crw-rewrite-term-correct
    (implies (and (crw-ev-meta-extract-global-facts)
                  (crw-config-okp config)
                  (crw-ev (conjoin assumptions) env))
             (equal (crw-iff-fix iffp (crw-ev new-x env))
                    (crw-iff-fix iffp (crw-ev x env))))
    :hints (("goal" :use ((:instance crw-rewrite-term-under-subst-correct
                           (subst nil)))
             :in-theory (e/d (crw-rewrite-term
                              crw-subst-env-of-nil)
                             (crw-rewrite-term-under-subst-correct))))
    :fn crw-rewrite-term)

  (defret crw-rewrite-term-correct-equal
    (implies (and (crw-ev-meta-extract-global-facts)
                  (crw-config-okp config)
                  (crw-ev (conjoin assumptions) env)
                  (not iffp))
             (equal (crw-ev new-x env)
                    (crw-ev x env)))
    :hints (("goal" :use ((:instance crw-rewrite-term-under-subst-correct
                           (subst nil) (iffp nil)))
             :in-theory (e/d (crw-rewrite-term
                              crw-subst-env-of-nil)
                             (crw-rewrite-term-under-subst-correct))))
    :fn crw-rewrite-term))

(define crw-rewrite-termlist ((x pseudo-term-listp)
                              (assumptions pseudo-term-listp)
                              (config crw-rewrite-config-p)
                              (limit natp)
                              state)
  :parents (crw-rewriter)
  :short "Rewrite a pseudo-term list inside-out."
  :returns (new-x pseudo-term-listp)
  (crw-rewrite-termlist-under-subst x nil assumptions config limit state)
  ///

  (defret len-of-crw-rewrite-termlist
    (equal (len new-x) (len x))
    :hints (("goal" :in-theory (enable crw-rewrite-termlist)))
    :fn crw-rewrite-termlist)

  (defret crw-rewrite-termlist-correct
    (implies (and (crw-ev-meta-extract-global-facts)
                  (crw-config-okp config)
                  (crw-ev (conjoin assumptions) env))
             (equal (crw-ev-list new-x env)
                    (crw-ev-list x env)))
    :hints (("goal" :use ((:instance crw-rewrite-termlist-under-subst-correct
                           (subst nil)))
             :in-theory (e/d (crw-rewrite-termlist
                              crw-subst-env-of-nil)
                             (crw-rewrite-termlist-under-subst-correct))))
    :fn crw-rewrite-termlist))

(define crw-rewrite-under-iff ((x pseudo-termp)
                               (assumptions pseudo-term-listp)
                               (config crw-rewrite-config-p)
                               state)
  :parents (crw-rewriter)
  :short "Rewrite a pseudo-term in a Boolean context."
  :returns (new-x pseudo-termp)
  (crw-rewrite-term x assumptions config t
                    (crw-rewrite-config->repeat-limit config)
                    state)
  ///

  (defret crw-rewrite-under-iff-correct
    (implies (and (crw-ev-meta-extract-global-facts)
                  (crw-config-okp config)
                  (crw-ev (conjoin assumptions) env))
             (iff (crw-ev new-x env)
                  (crw-ev x env)))
    :hints (("goal" :use ((:instance crw-rewrite-term-correct
                           (iffp t)
                           (limit (crw-rewrite-config->repeat-limit config))))
             :in-theory (e/d (crw-rewrite-under-iff
                              crw-iff-fix)
                             (crw-rewrite-term-correct))))
    :fn crw-rewrite-under-iff))

(define crw-rewrite-term-with-rules ((x pseudo-termp)
                                     (rules rewritelist-p)
                                     (assumptions pseudo-term-listp)
                                     state
                                     &key
                                     ((executable-fns symbol-listp) 'nil)
                                     ((repeat-limit natp) '1000))
  :parents (crw-rewriter)
  :short "Convenience wrapper for rewriting a term under rules and assumptions."
  :returns (new-x pseudo-termp)
  (b* ((config (crw-make-config rules
                                :executable-fns executable-fns
                                :repeat-limit repeat-limit)))
    (crw-rewrite-term x assumptions config nil repeat-limit state))
  ///

  (defret crw-rewrite-term-with-rules-correct
    (implies (and (crw-ev-meta-extract-global-facts)
                  (crw-rewrite-rules-validp rules)
                  (crw-ev (conjoin assumptions) env))
             (equal (crw-ev new-x env)
                    (crw-ev x env)))
    :hints (("goal" :use ((:instance
                           crw-rewrite-term-correct
                           (config (crw-make-config rules
                                                    :executable-fns executable-fns
                                                    :repeat-limit repeat-limit))
                           (iffp nil)
                           (limit repeat-limit)))
             :in-theory (e/d (crw-rewrite-term-with-rules
                              crw-make-config
                              crw-config-okp
                              crw-iff-fix)
                             (crw-rewrite-term-correct))))
    :fn crw-rewrite-term-with-rules))

(encapsulate nil
  (set-ignore-ok t)
  (acl2::def-functional-instance crw-ev-of-parse-rewrites-from-term
    parse-rw-ev-of-parse-rewrites-from-term
    ((parse-rw-ev crw-ev)
     (parse-rw-ev-list crw-ev-list))
    :hints(("Goal" :in-theory (enable crw-ev-of-fncall-args)))))

(local (in-theory (disable w)))

(define crw-parse-rewrites-from-theorem ((name symbolp)
                                         (w plist-worldp))
  :parents (crw-rewriter)
  :short "Parse the formula of a named theorem into crw rewrite rules."
  :returns (mv (err acl2::errmsg-type-p :rule-classes :type-prescription)
               (rules rewritelist-p))
  (let* ((name (mbe :logic (acl2::symbol-fix name) :exec name))
         (formula  (acl2::meta-extract-formula-w name w)))
    (if (pseudo-termp formula)
        (parse-rewrites-from-term formula w)
      (mv "Bad formula: not pseudo-termp" nil)))
  ///

  (defret crw-ev-of-<fn>
    (implies (and (crw-ev-meta-extract-global-facts)
                  (equal w (w state)))
             (crw-ev (conjoin (rewritelist-terms rules)) env))
    :hints (("goal" :use ((:instance crw-ev-of-parse-rewrites-from-term
                           (x (acl2::meta-extract-formula-w (acl2::symbol-fix name) w))))
             :in-theory (disable crw-ev-of-parse-rewrites-from-term)))))

(define crw-parse-rewrites-from-theorems ((names symbol-listp)
                                          (w plist-worldp))
  :parents (crw-rewriter)
  :short "Parse the formulas of named theorems into crw rewrite rules."
  :returns (mv (err acl2::errmsg-type-p :rule-classes :type-prescription)
               (rules rewritelist-p))
  (b* (((when (atom names)) (mv nil nil))
       ((mv err1 rules1)
        (crw-parse-rewrites-from-theorem (car names) w))
       ((mv err2 rules2)
        (crw-parse-rewrites-from-theorems (cdr names) w)))
    (mv (or err1 err2) (append rules1 rules2)))
  ///
  (defret crw-ev-of-<fn>
    (implies (and (crw-ev-meta-extract-global-facts)
                  (equal w (w state)))
             (crw-ev (conjoin (rewritelist-terms rules)) env))))

