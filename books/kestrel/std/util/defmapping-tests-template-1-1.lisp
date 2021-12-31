; Standard Utilities Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defmapping-templates")
(include-book "defmapping-tests-utils")

(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-fail-local" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Template-based tests for n = m = 1.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definputs-guarded-1-1)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Non-guard-verified variants of the generic domains and conversions.

(progn
  (defun doma* (a) (doma a))
  (defun domb* (b) (domb b))
  (defun alpha* (a) (alpha a))
  (defun beta* (b) (beta b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "Default options.")
 (must-be-before-defmapping)
 (enable-all)
 (defmapping map doma domb alpha beta)
 (must-be-after-defmapping)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "Injective alpha.")
 (must-be-before-defmapping :beta-of-alpha-thm t)
 (enable-all)
 (defmapping map doma domb alpha beta :beta-of-alpha-thm t)
 (must-be-after-defmapping :beta-of-alpha-thm t)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "Injective alpha, unconditional.")
 (must-be-before-defmapping :beta-of-alpha-thm t)
 (enable-all-uncond)
 (defmapping map doma domb alpha beta :beta-of-alpha-thm t :unconditional t)
 (must-be-after-defmapping :beta-of-alpha-thm t :unconditional t)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "Surjective alpha.")
 (must-be-before-defmapping :alpha-of-beta-thm t)
 (enable-all)
 (defmapping map doma domb alpha beta :alpha-of-beta-thm t)
 (must-be-after-defmapping :alpha-of-beta-thm t)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "Surjective alpha, unconditional.")
 (must-be-before-defmapping :alpha-of-beta-thm t)
 (enable-all-uncond)
 (defmapping map doma domb alpha beta :alpha-of-beta-thm t :unconditional t)
 (must-be-after-defmapping :alpha-of-beta-thm t :unconditional t)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "Bijective alpha.")
 (must-be-before-defmapping :beta-of-alpha-thm t :alpha-of-beta-thm t)
 (enable-all)
 (defmapping map doma domb alpha beta :beta-of-alpha-thm t :alpha-of-beta-thm t)
 (must-be-after-defmapping :beta-of-alpha-thm t :alpha-of-beta-thm t)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "Bijective alpha, unconditional.")
 (must-be-before-defmapping :beta-of-alpha-thm t :alpha-of-beta-thm t)
 (enable-all-uncond)
 (defmapping map doma domb alpha beta
   :beta-of-alpha-thm t :alpha-of-beta-thm t :unconditional t)
 (must-be-after-defmapping :beta-of-alpha-thm t
                           :alpha-of-beta-thm t
                           :unconditional t)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "No guard theorems.")
 (must-be-before-defmapping :guard-thms nil)
 (enable-all)
 (defmapping map doma domb alpha beta :guard-thms nil)
 (must-be-after-defmapping :guard-thms nil)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "Injective alpha, no guard theorems.")
 (must-be-before-defmapping :beta-of-alpha-thm t :guard-thms nil)
 (enable-all)
 (defmapping map doma domb alpha beta :beta-of-alpha-thm t :guard-thms nil)
 (must-be-after-defmapping :beta-of-alpha-thm t :guard-thms nil)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "Injective alpha, unconditional, no guard theorems.")
 (must-be-before-defmapping :beta-of-alpha-thm t :guard-thms nil)
 (enable-all-uncond)
 (defmapping map doma domb alpha beta
   :beta-of-alpha-thm t :guard-thms nil :unconditional t)
 (must-be-after-defmapping :beta-of-alpha-thm t
                           :guard-thms nil
                           :unconditional t)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "Surjective alpha, no guard theorems.")
 (must-be-before-defmapping :alpha-of-beta-thm t :guard-thms nil)
 (enable-all)
 (defmapping map doma domb alpha beta :alpha-of-beta-thm t :guard-thms nil)
 (must-be-after-defmapping :alpha-of-beta-thm t :guard-thms nil)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "Surjective alpha, unconditional, no guard theorems.")
 (must-be-before-defmapping :alpha-of-beta-thm t :guard-thms nil)
 (enable-all-uncond)
 (defmapping map doma domb alpha beta
   :alpha-of-beta-thm t :guard-thms nil :unconditional t)
 (must-be-after-defmapping :alpha-of-beta-thm t
                           :guard-thms nil
                           :unconditional t)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "Bijective alpha, no guard theorems.")
 (must-be-before-defmapping :beta-of-alpha-thm t
                            :alpha-of-beta-thm t
                            :guard-thms nil)
 (enable-all)
 (defmapping map doma domb alpha beta
   :beta-of-alpha-thm t :alpha-of-beta-thm t :guard-thms nil)
 (must-be-after-defmapping :beta-of-alpha-thm t
                           :alpha-of-beta-thm t
                           :guard-thms nil)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "Bijective alpha, unconditional, no guard theorems.")
 (must-be-before-defmapping :beta-of-alpha-thm t
                            :alpha-of-beta-thm t
                            :guard-thms nil)
 (enable-all-uncond)
 (defmapping map doma domb alpha beta
   :beta-of-alpha-thm t :alpha-of-beta-thm t :guard-thms nil :unconditional t)
 (must-be-after-defmapping :beta-of-alpha-thm t
                           :alpha-of-beta-thm t
                           :guard-thms nil
                           :unconditional t)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "Some custom theorem names.")
 (must-be-before-defmapping :alpha-image my-alpha-image
                            :alpha-guard my-alpha-guard)
 (enable-all)
 (defmapping map doma domb alpha beta
   :thm-names (:alpha-image my-alpha-image
               :alpha-guard my-alpha-guard))
 (must-be-after-defmapping :alpha-image my-alpha-image
                           :alpha-guard my-alpha-guard)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "All (for default options) custom theorem names.")
 (must-be-before-defmapping :alpha-image my-alpha-image
                            :beta-image my-beta-image
                            :doma-guard my-doma-guard
                            :domb-guard my-domb-guard
                            :alpha-guard my-alpha-guard
                            :beta-guard my-beta-guard)
 (enable-all)
 (defmapping map doma domb alpha beta
   :thm-names (:alpha-image my-alpha-image
               :beta-image my-beta-image
               :doma-guard my-doma-guard
               :domb-guard my-domb-guard
               :alpha-guard my-alpha-guard
               :beta-guard my-beta-guard))
 (must-be-after-defmapping :alpha-image my-alpha-image
                           :beta-image my-beta-image
                           :doma-guard my-doma-guard
                           :domb-guard my-domb-guard
                           :alpha-guard my-alpha-guard
                           :beta-guard my-beta-guard)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "Some theorems enabled.")
 (must-be-before-defmapping)
 (enable-all)
 (defmapping map doma domb alpha beta :thm-enable (:alpha-image :domb-guard))
 (must-be-after-defmapping :alpha-image-enable t
                           :domb-guard-enable t)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "All (for default options) theorems enabled.")
 (must-be-before-defmapping)
 (enable-all)
 (defmapping map doma domb alpha beta :thm-enable (:alpha-image :beta-image
                                                   :doma-guard :domb-guard
                                                   :alpha-guard :beta-guard))
 (must-be-after-defmapping :alpha-image-enable t
                           :beta-image-enable t
                           :doma-guard-enable t
                           :domb-guard-enable t
                           :alpha-guard-enable t
                           :beta-guard-enable t)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "Some applicability condition hints.")
 (in-theory (enable alpha-image
                    doma-guard
                    alpha-guard
                    beta-guard))
 (defmapping map doma domb alpha beta
   :hints (:beta-image (("Goal" :by beta-image))
           :domb-guard (("Goal" :in-theory (enable domb-guard)))))
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "All (for default options) applicability condition hints.")
 (defmapping map doma domb alpha beta
   :hints (:alpha-image (("Goal" :use alpha-image))
           :beta-image (("Goal" :use beta-image))
           :doma-guard (("Goal" :use doma-guard))
           :domb-guard (("Goal" :use domb-guard))
           :alpha-guard (("Goal" :use alpha-guard))
           :beta-guard (("Goal" :use beta-guard))))
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "Uniform applicability condition hints.")
 (defmapping map doma domb alpha beta
   :hints (("Goal" :use (alpha-image
                         beta-image
                         doma-guard
                         domb-guard
                         alpha-guard
                         beta-guard))))
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "No output.")
 (enable-all)
 (defmapping map doma domb alpha beta :print nil)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "Error output.")
 (enable-all)
 (defmapping map doma domb alpha beta :print :error)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "Error and result output.")
 (enable-all)
 (defmapping map doma domb alpha beta :print :result)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "Error, result, and information output.")
 (enable-all)
 (defmapping map doma domb alpha beta :print :info)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "All output.")
 (enable-all)
 (defmapping map doma domb alpha beta :print :all)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "Events only displayed.")
 (enable-all)
 (defmapping map doma domb alpha beta :show-only t)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "Lambda expressions.")
 (enable-all)
 (defmapping map
   (lambda (a) (doma a))
   (lambda (b) (domb b))
   (lambda (a) (alpha a))
   (lambda (b) (beta b)))
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "Macros.")
 (enable-all)
 (defmacro doma$ (a) `(doma ,a))
 (defmacro domb$ (b) `(domb ,b))
 (defmacro alpha$ (a) `(alpha ,a))
 (defmacro beta$ (b) `(beta ,b))
 (defmapping map doma$ domb$ alpha$ beta$)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (test-title "Non-guard-verified variants.")
 (must-be-before-defmapping)
 (enable-all)
 (must-fail (defmapping map doma* domb* alpha* beta*))
 (defmapping map doma* domb* alpha* beta* :guard-thms nil)
 (must-be-after-defmapping :guard-thms nil
                           :doma doma*
                           :domb domb*
                           :alpha alpha*
                           :beta beta*)
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "Redundancy handling.")

(must-succeed*
 (enable-all)
 (defmapping map doma domb alpha beta)
 (must-be-redundant
  (defmapping map doma domb alpha beta)
  (defmapping map doma domb alpha beta :print :all)
  (defmapping map doma domb alpha beta :show-only t)
  (defmapping map doma domb alpha beta :print nil :show-only t))
 :with-output-off nil)

(must-succeed*
 (enable-all)
 (defmapping map doma domb alpha beta :print :info)
 (must-be-redundant
  (defmapping map doma domb alpha beta)
  (defmapping map doma domb alpha beta :print :error)
  (defmapping map doma domb alpha beta :show-only t)
  (defmapping map doma domb alpha beta :print nil :show-only t))
 :with-output-off nil)

(must-succeed*
 (enable-all)
 (defmapping map doma domb alpha beta :show-only t)
 (must-fail-local
  (must-be-redundant
   (defmapping map doma domb alpha beta)))
 (must-fail-local
  (must-be-redundant
   (defmapping map doma domb alpha beta :print :all)))
 :with-output-off nil)

(must-succeed*
 (enable-all)
 (defmapping map doma domb alpha beta :print :info :show-only t)
 (must-fail-local
  (must-be-redundant
   (defmapping map doma domb alpha beta)))
 (must-fail-local
  (must-be-redundant
   (defmapping map doma domb alpha beta :print :result)))
 (must-be-redundant
  (defmapping map doma domb alpha beta :show-only t))
 (must-be-redundant
  (defmapping map doma domb alpha beta :print :all :show-only t))
 :with-output-off nil)

(must-succeed*
 (enable-all)
 (defmapping map doma domb alpha beta)
 (must-fail
  (defmapping map doma* domb* alpha* beta*))
 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "Proof failures.")

(must-fail
 (defmapping map doma domb alpha beta))

(must-fail
 (defmapping map doma domb alpha beta
   :hints (:alpha-image (("Goal" :by alpha-image)))))

(must-fail
 (defmapping map doma domb alpha beta
   :hints (:alpha-image (("Goal" :by alpha-image))
           :beta-image (("Goal" :by beta-image)))))

(must-fail
 (defmapping map doma domb alpha beta
   :hints (:alpha-image (("Goal" :by alpha-image))
           :beta-image (("Goal" :by beta-image))
           :doma-guard (("Goal" :by doma-guard)))))

(must-fail
 (defmapping map doma domb alpha beta
   :hints (:alpha-image (("Goal" :by alpha-image))
           :beta-image (("Goal" :by beta-image))
           :doma-guard (("Goal" :by doma-guard))
           :domb-guard (("Goal" :by domb-guard)))))

(must-fail
 (defmapping map doma domb alpha beta
   :hints (:alpha-image (("Goal" :by alpha-image))
           :beta-image (("Goal" :by beta-image))
           :doma-guard (("Goal" :by doma-guard))
           :domb-guard (("Goal" :by domb-guard))
           :alpha-guard (("Goal" :by alpha-guard)))))
