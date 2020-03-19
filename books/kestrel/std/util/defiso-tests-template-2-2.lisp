; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defiso-templates")
(include-book "defiso-tests-utils")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Template-based tests for n = m = 2.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definputs-guarded-2-2)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Non-guard-verified variants of the generic domains and isomorhisms.

(progn
  (defun doma* (a1 a2) (doma a1 a2))
  (defun domb* (b1 b2) (domb b1 b2))
  (defun alpha* (a1 a2) (alpha a1 a2))
  (defun beta* (b1 b2) (beta b1 b2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Default options.")

 (must-not-be-defiso)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defiso iso doma domb alpha beta)

 (must-be-defiso)

 (must-be-redundant-theorems-nonguard
  :a1...an (a1 a2)
  :b1...bm (b1 b2)
  :aa1...aan (a1$ a2$)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :a1...an (a1 a2)
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With unconditional theorems.")

 (must-not-be-defiso)

 (must-not-be-theorems-default)

 (local (enable-all-uncond))

 (defiso iso doma domb alpha beta :unconditional t)

 (must-be-defiso :unconditional t)

 (must-be-redundant-theorems-nonguard
  :a1...an (a1 a2)
  :b1...bm (b1 b2)
  :aa1...aan (a1$ a2$)
  :bb1...bbm (b1$ b2$)
  :unconditional t)

 (must-be-redundant-theorems-guard
  :a1...an (a1 a2)
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With conditional theorems.")

 (must-not-be-defiso)

 (must-not-be-theorems-default)

 (local (enable-all-uncond))

 (defiso iso doma domb alpha beta :unconditional nil)

 (must-be-defiso)

 (must-be-redundant-theorems-nonguard
  :a1...an (a1 a2)
  :b1...bm (b1 b2)
  :aa1...aan (a1$ a2$)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :a1...an (a1 a2)
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With guard-related theorems.")

 (must-not-be-defiso)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defiso iso doma domb alpha beta :guard-thms t)

 (must-be-defiso)

 (must-be-redundant-theorems-nonguard
  :a1...an (a1 a2)
  :b1...bm (b1 b2)
  :aa1...aan (a1$ a2$)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :a1...an (a1 a2)
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Without guard-related theorems.")

 (must-not-be-defiso)

 (must-not-be-theorems iso.alpha-image
                       iso.beta-image
                       iso.beta-of-alpha
                       iso.alpha-of-beta
                       iso.alpha-injective
                       iso.beta-injective)

 (local (enable-all))

 (defiso iso doma domb alpha beta :guard-thms nil)

 (must-be-defiso :doma-guard nil
                 :domb-guard nil
                 :alpha-guard nil
                 :beta-guard nil)

 (must-be-redundant-theorems-nonguard
  :a1...an (a1 a2)
  :b1...bm (b1 b2)
  :aa1...aan (a1$ a2$)
  :bb1...bbm (b1$ b2$))

 (must-not-be-theorems iso.doma-guard
                       iso.domb-guard
                       iso.alpha-guard
                       iso.beta-guard)

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Without custom theorem names.")

 (must-not-be-defiso)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defiso iso doma domb alpha beta :thm-names nil)

 (must-be-defiso)

 (must-be-redundant-theorems-nonguard
  :a1...an (a1 a2)
  :b1...bm (b1 b2)
  :aa1...aan (a1$ a2$)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :a1...an (a1 a2)
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With some custom theorem names.")

 (must-not-be-defiso)

 (must-not-be-theorems my-alpha-image
                       iso.beta-image
                       iso.alpha-of-beta
                       my-alpha-of-beta
                       iso.alpha-injective
                       iso.beta-injective
                       iso.doma-guard
                       iso.domb-guard
                       my-alpha-guard
                       iso.beta-guard)

 (local (enable-all))

 (defiso iso doma domb alpha beta
   :thm-names (:alpha-image my-alpha-image
               :alpha-of-beta my-alpha-of-beta
               :alpha-guard my-alpha-guard))

 (must-be-defiso :alpha-image my-alpha-image
                 :alpha-of-beta my-alpha-of-beta
                 :alpha-guard my-alpha-guard)

 (must-be-redundant-theorems-nonguard
  :alpha-image my-alpha-image
  :alpha-of-beta my-alpha-of-beta
  :a1...an (a1 a2)
  :b1...bm (b1 b2)
  :aa1...aan (a1$ a2$)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :alpha-guard my-alpha-guard
  :a1...an (a1 a2)
  :b1...bm (b1 b2))

 (must-not-be-theorems iso.alpha-image
                       iso.alpha-of-beta
                       iso.alpha-guard)

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With all custom theorem names.")

 (must-not-be-defiso)

 (must-not-be-theorems my-alpha-image
                       my-beta-image
                       my-beta-of-alpha
                       my-alpha-of-beta
                       my-alpha-injective
                       my-beta-injective
                       my-doma-guard
                       my-domb-guard
                       my-alpha-guard
                       my-beta-guard)

 (local (enable-all))

 (defiso iso doma domb alpha beta
   :thm-names (:alpha-image my-alpha-image
               :beta-image my-beta-image
               :beta-of-alpha my-beta-of-alpha
               :alpha-of-beta my-alpha-of-beta
               :alpha-injective my-alpha-injective
               :beta-injective my-beta-injective
               :doma-guard my-doma-guard
               :domb-guard my-domb-guard
               :alpha-guard my-alpha-guard
               :beta-guard my-beta-guard))

 (must-be-defiso :alpha-image my-alpha-image
                 :beta-image my-beta-image
                 :beta-of-alpha my-beta-of-alpha
                 :alpha-of-beta my-alpha-of-beta
                 :alpha-injective my-alpha-injective
                 :beta-injective my-beta-injective
                 :doma-guard my-doma-guard
                 :domb-guard my-domb-guard
                 :alpha-guard my-alpha-guard
                 :beta-guard my-beta-guard)

 (must-be-redundant-theorems-nonguard
  :alpha-image my-alpha-image
  :beta-image my-beta-image
  :beta-of-alpha my-beta-of-alpha
  :alpha-of-beta my-alpha-of-beta
  :alpha-injective my-alpha-injective
  :beta-injective my-beta-injective
  :a1...an (a1 a2)
  :b1...bm (b1 b2)
  :aa1...aan (a1$ a2$)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :doma-guard my-doma-guard
  :domb-guard my-domb-guard
  :alpha-guard my-alpha-guard
  :beta-guard my-beta-guard
  :a1...an (a1 a2)
  :b1...bm (b1 b2))

 (must-not-be-theorems-default)

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With no applicability condition hints.")

 (must-not-be-defiso)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defiso iso doma domb alpha beta :hints nil)

 (must-be-defiso)

 (must-be-redundant-theorems-nonguard
  :a1...an (a1 a2)
  :b1...bm (b1 b2)
  :aa1...aan (a1$ a2$)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :a1...an (a1 a2)
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With some applicability condition hints.")

 (must-not-be-defiso)

 (must-not-be-theorems-default)

 (local (in-theory (enable alpha-image
                           alpha-of-beta
                           doma-guard
                           alpha-guard
                           beta-guard)))

 (defiso iso doma domb alpha beta
   :hints (:beta-image (("Goal" :by beta-image))
           :beta-of-alpha (("Goal" :use beta-of-alpha))
           :domb-guard (("Goal" :in-theory (enable domb-guard)))))

 (must-be-defiso)

 (must-be-redundant-theorems-nonguard
  :a1...an (a1 a2)
  :b1...bm (b1 b2)
  :aa1...aan (a1$ a2$)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :a1...an (a1 a2)
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With all applicability condition hints.")

 (must-not-be-defiso)

 (must-not-be-theorems-default)

 (defiso iso doma domb alpha beta
   :hints (:alpha-image (("Goal" :use alpha-image))
           :beta-image (("Goal" :use beta-image))
           :beta-of-alpha (("Goal" :use beta-of-alpha))
           :alpha-of-beta (("Goal" :use alpha-of-beta))
           :doma-guard (("Goal" :use doma-guard))
           :domb-guard (("Goal" :use domb-guard))
           :alpha-guard (("Goal" :use alpha-guard))
           :beta-guard (("Goal" :use beta-guard))))

 (must-be-defiso)

 (must-be-redundant-theorems-nonguard
  :a1...an (a1 a2)
  :b1...bm (b1 b2)
  :aa1...aan (a1$ a2$)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :a1...an (a1 a2)
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With no output.")

 (must-not-be-defiso)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defiso iso doma domb alpha beta :print nil)

 (must-be-defiso)

 (must-be-redundant-theorems-nonguard
  :a1...an (a1 a2)
  :b1...bm (b1 b2)
  :aa1...aan (a1$ a2$)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :a1...an (a1 a2)
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With error output.")

 (must-not-be-defiso)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defiso iso doma domb alpha beta :print :error)

 (must-be-defiso)

 (must-be-redundant-theorems-nonguard
  :a1...an (a1 a2)
  :b1...bm (b1 b2)
  :aa1...aan (a1$ a2$)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :a1...an (a1 a2)
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With error and result output.")

 (must-not-be-defiso)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defiso iso doma domb alpha beta :print :result)

 (must-be-defiso)

 (must-be-redundant-theorems-nonguard
  :a1...an (a1 a2)
  :b1...bm (b1 b2)
  :aa1...aan (a1$ a2$)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :a1...an (a1 a2)
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With error, result, and information output.")

 (must-not-be-defiso)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defiso iso doma domb alpha beta :print :info)

 (must-be-defiso)

 (must-be-redundant-theorems-nonguard
  :a1...an (a1 a2)
  :b1...bm (b1 b2)
  :aa1...aan (a1$ a2$)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :a1...an (a1 a2)
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With all output.")

 (must-not-be-defiso)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defiso iso doma domb alpha beta :print :all)

 (must-be-defiso)

 (must-be-redundant-theorems-nonguard
  :a1...an (a1 a2)
  :b1...bm (b1 b2)
  :aa1...aan (a1$ a2$)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :a1...an (a1 a2)
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With events submitted.")

 (must-not-be-defiso)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defiso iso doma domb alpha beta :show-only nil)

 (must-be-defiso)

 (must-be-redundant-theorems-nonguard
  :a1...an (a1 a2)
  :b1...bm (b1 b2)
  :aa1...aan (a1$ a2$)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :a1...an (a1 a2)
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With events only displayed.")

 (must-not-be-defiso)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defiso iso doma domb alpha beta :show-only t)

 (must-not-be-defiso)

 (must-not-be-theorems-default))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With lambda expressions.")

 (must-not-be-defiso)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defiso iso
   (lambda (a1 a2) (doma a1 a2))
   (lambda (b1 b2) (domb b1 b2))
   (lambda (a1 a2) (alpha a1 a2))
   (lambda (b1 b2) (beta b1 b2)))

 (must-be-defiso :doma (lambda (a1 a2) (doma a1 a2))
                 :domb (lambda (b1 b2) (domb b1 b2))
                 :alpha (lambda (a1 a2) (alpha a1 a2))
                 :beta (lambda (b1 b2) (beta b1 b2)))

 (must-be-redundant-theorems-nonguard
  :a1...an (a1 a2)
  :b1...bm (b1 b2)
  :aa1...aan (a1$ a2$)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :a1...an (a1 a2)
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With macros.")

 (must-not-be-defiso)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defmacro doma$ (a1 a2) `(doma ,a1 ,a2))
 (defmacro domb$ (b1 b2) `(domb ,b1 ,b2))
 (defmacro alpha$ (a1 a2) `(alpha ,a1 ,a2))
 (defmacro beta$ (b1 b2) `(beta ,b1 ,b2))

 (defiso iso doma$ domb$ alpha$ beta$)

 (must-be-defiso :doma (lambda (a1 a2) (doma a1 a2))
                 :domb (lambda (b1 b2) (domb b1 b2))
                 :alpha (lambda (a1 a2) (alpha a1 a2))
                 :beta (lambda (b1 b2) (beta b1 b2)))

 (must-be-redundant-theorems-nonguard
  :a1...an (a1 a2)
  :b1...bm (b1 b2)
  :aa1...aan (a1$ a2$)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :a1...an (a1 a2)
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With the non-guard-verified variants.")

 (must-not-be-defiso :name iso*)

 (must-not-be-theorems iso*.alpha-image
                       iso*.beta-image
                       iso*.beta-of-alpha
                       iso*.alpha-of-beta
                       iso*.alpha-injective
                       iso*.beta-injective
                       iso*.doma-guard
                       iso*.domb-guard
                       iso*.alpha-guard
                       iso*.beta-guard)

 (local (enable-all))

 (must-fail (defiso iso* doma* domb* alpha* beta*))

 (defiso iso* doma* domb* alpha* beta* :guard-thms nil)

 (must-be-defiso :name iso*
                 :doma doma*
                 :domb domb*
                 :alpha alpha*
                 :beta beta*
                 :alpha-image iso*.alpha-image
                 :beta-image iso*.beta-image
                 :beta-of-alpha iso*.beta-of-alpha
                 :alpha-of-beta iso*.alpha-of-beta
                 :alpha-injective iso*.alpha-injective
                 :beta-injective iso*.beta-injective
                 :doma-guard nil
                 :domb-guard nil
                 :alpha-guard nil
                 :beta-guard nil)

 (must-be-redundant-theorems-nonguard
  :alpha-image iso*.alpha-image
  :beta-image iso*.beta-image
  :beta-of-alpha iso*.beta-of-alpha
  :alpha-of-beta iso*.alpha-of-beta
  :alpha-injective iso*.alpha-injective
  :beta-injective iso*.beta-injective
  :doma doma*
  :domb domb*
  :alpha alpha*
  :beta beta*
  :a1...an (a1 a2)
  :b1...bm (b1 b2)
  :aa1...aan (a1$ a2$)
  :bb1...bbm (b1$ b2$))

 (must-not-be-theorems iso*.doma-guard
                       iso*.domb-guard
                       iso*.alpha-guard
                       iso*.beta-guard)

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Redundancy handling.")

 (local (enable-all))

 (defiso iso doma domb alpha beta)

 (must-be-redundant
  (defiso iso doma domb alpha beta)
  (defiso iso doma domb alpha beta :print :all)
  (defiso iso doma domb alpha beta :show-only t)
  (defiso iso doma domb alpha beta :print nil :show-only t)))

(must-succeed*

 (local (enable-all))

 (defiso iso doma domb alpha beta :print :info)

 (must-be-redundant
  (defiso iso doma domb alpha beta)
  (defiso iso doma domb alpha beta :print :error)
  (defiso iso doma domb alpha beta :show-only t)
  (defiso iso doma domb alpha beta :print nil :show-only t)))

(must-succeed*

 (local (enable-all))

 (defiso iso doma domb alpha beta :show-only t)

 (must-fail-local
  (must-be-redundant
   (defiso iso doma domb alpha beta)))

 (must-fail-local
  (must-be-redundant
   (defiso iso doma domb alpha beta :print :all))))

(must-succeed*

 (local (enable-all))

 (defiso iso doma domb alpha beta :print :info :show-only t)

 (must-fail-local
  (must-be-redundant
   (defiso iso doma domb alpha beta)))

 (must-fail-local
  (must-be-redundant
   (defiso iso doma domb alpha beta :print :result)))

 (must-be-redundant
  (defiso iso doma domb alpha beta :show-only t))

 (must-be-redundant
  (defiso iso doma domb alpha beta :print :all :show-only t)))

(must-succeed*

 (local (enable-all))

 (defiso iso doma domb alpha beta)

 (must-fail
  (defiso iso doma* domb* alpha* beta*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "Proof failures.")

(must-fail
 (defiso iso doma domb alpha beta))

(must-fail
 (defiso iso doma domb alpha beta
   :hints (:alpha-image (("Goal" :by alpha-image)))))

(must-fail
 (defiso iso doma domb alpha beta
   :hints (:alpha-image (("Goal" :by alpha-image))
           :beta-image (("Goal" :by beta-image)))))

(must-fail
 (defiso iso doma domb alpha beta
   :hints (:alpha-image (("Goal" :by alpha-image))
           :beta-image (("Goal" :by beta-image))
           :beta-of-alpha (("Goal" :by beta-of-alpha)))))

(must-fail
 (defiso iso doma domb alpha beta
   :hints (:alpha-image (("Goal" :by alpha-image))
           :beta-image (("Goal" :by beta-image))
           :beta-of-alpha (("Goal" :by beta-of-alpha))
           :alpha-of-beta (("Goal" :by alpha-of-beta)))))

(must-fail
 (defiso iso doma domb alpha beta
   :hints (:alpha-image (("Goal" :by alpha-image))
           :beta-image (("Goal" :by beta-image))
           :beta-of-alpha (("Goal" :by beta-of-alpha))
           :alpha-of-beta (("Goal" :by alpha-of-beta))
           :doma-guard (("Goal" :by doma-guard)))))

(must-fail
 (defiso iso doma domb alpha beta
   :hints (:alpha-image (("Goal" :by alpha-image))
           :beta-image (("Goal" :by beta-image))
           :beta-of-alpha (("Goal" :by beta-of-alpha))
           :alpha-of-beta (("Goal" :by alpha-of-beta))
           :doma-guard (("Goal" :by doma-guard))
           :domb-guard (("Goal" :by domb-guard)))))

(must-fail
 (defiso iso doma domb alpha beta
   :hints (:alpha-image (("Goal" :by alpha-image))
           :beta-image (("Goal" :by beta-image))
           :beta-of-alpha (("Goal" :by beta-of-alpha))
           :alpha-of-beta (("Goal" :by alpha-of-beta))
           :doma-guard (("Goal" :by doma-guard))
           :domb-guard (("Goal" :by domb-guard))
           :alpha-guard (("Goal" :by alpha-guard)))))
