; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defsurj-templates")
(include-book "defsurj-tests-utils")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Template-based tests for n = 1 and m = 2.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(definputs-guarded-1-2)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Non-guard-verified variants of the generic domains and conversions.

(progn
  (defun doma* (a) (doma a))
  (defun domb* (b1 b2) (domb b1 b2))
  (defun alpha* (a) (alpha a))
  (defun beta* (b1 b2) (beta b1 b2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Default options.")

 (must-not-be-defsurj)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defsurj surj doma domb alpha beta)

 (must-be-defsurj)

 (must-be-redundant-theorems-nonguard
  :b1...bm (b1 b2)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With guard-related theorems.")

 (must-not-be-defsurj)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defsurj surj doma domb alpha beta :guard-thms t)

 (must-be-defsurj)

 (must-be-redundant-theorems-nonguard
  :b1...bm (b1 b2)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Without guard-related theorems.")

 (must-not-be-defsurj)

 (must-not-be-theorems surj.alpha-image
                       surj.beta-image
                       surj.alpha-of-beta)

 (local (enable-all))

 (defsurj surj doma domb alpha beta :guard-thms nil)

 (must-be-defsurj :doma-guard nil
                  :domb-guard nil
                  :alpha-guard nil
                  :beta-guard nil)

 (must-be-redundant-theorems-nonguard
  :b1...bm (b1 b2)
  :bb1...bbm (b1$ b2$))

 (must-not-be-theorems surj.doma-guard
                       surj.domb-guard
                       surj.alpha-guard
                       surj.beta-guard)

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Without custom theorem names.")

 (must-not-be-defsurj)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defsurj surj doma domb alpha beta :thm-names nil)

 (must-be-defsurj)

 (must-be-redundant-theorems-nonguard
  :b1...bm (b1 b2)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With some custom theorem names.")

 (must-not-be-defsurj)

 (must-not-be-theorems my-alpha-image
                       surj.beta-image
                       surj.alpha-of-beta
                       my-alpha-of-beta
                       surj.doma-guard
                       surj.domb-guard
                       my-alpha-guard
                       surj.beta-guard)

 (local (enable-all))

 (defsurj surj doma domb alpha beta
   :thm-names (:alpha-image my-alpha-image
               :alpha-of-beta my-alpha-of-beta
               :alpha-guard my-alpha-guard))

 (must-be-defsurj :alpha-image my-alpha-image
                  :alpha-of-beta my-alpha-of-beta
                  :alpha-guard my-alpha-guard)

 (must-be-redundant-theorems-nonguard
  :alpha-image my-alpha-image
  :alpha-of-beta my-alpha-of-beta
  :b1...bm (b1 b2)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :alpha-guard my-alpha-guard
  :b1...bm (b1 b2))

 (must-not-be-theorems surj.alpha-image
                       surj.alpha-of-beta
                       surj.alpha-guard)

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With all custom theorem names.")

 (must-not-be-defsurj)

 (must-not-be-theorems my-alpha-image
                       my-beta-image
                       my-alpha-of-beta
                       my-doma-guard
                       my-domb-guard
                       my-alpha-guard
                       my-beta-guard)

 (local (enable-all))

 (defsurj surj doma domb alpha beta
   :thm-names (:alpha-image my-alpha-image
               :beta-image my-beta-image
               :alpha-of-beta my-alpha-of-beta
               :doma-guard my-doma-guard
               :domb-guard my-domb-guard
               :alpha-guard my-alpha-guard
               :beta-guard my-beta-guard))

 (must-be-defsurj :alpha-image my-alpha-image
                  :beta-image my-beta-image
                  :alpha-of-beta my-alpha-of-beta
                  :doma-guard my-doma-guard
                  :domb-guard my-domb-guard
                  :alpha-guard my-alpha-guard
                  :beta-guard my-beta-guard)

 (must-be-redundant-theorems-nonguard
  :alpha-image my-alpha-image
  :beta-image my-beta-image
  :alpha-of-beta my-alpha-of-beta
  :b1...bm (b1 b2)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :doma-guard my-doma-guard
  :domb-guard my-domb-guard
  :alpha-guard my-alpha-guard
  :beta-guard my-beta-guard
  :b1...bm (b1 b2))

 (must-not-be-theorems-default)

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With no applicability condition hints.")

 (must-not-be-defsurj)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defsurj surj doma domb alpha beta :hints nil)

 (must-be-defsurj)

 (must-be-redundant-theorems-nonguard
  :b1...bm (b1 b2)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With some applicability condition hints.")

 (must-not-be-defsurj)

 (must-not-be-theorems-default)

 (local (in-theory (enable alpha-image
                           alpha-of-beta
                           doma-guard
                           alpha-guard
                           beta-guard)))

 (defsurj surj doma domb alpha beta
   :hints (:beta-image (("Goal" :by beta-image))
           :alpha-of-beta (("Goal" :by alpha-of-beta))
           :domb-guard (("Goal" :in-theory (enable domb-guard)))))

 (must-be-defsurj)

 (must-be-redundant-theorems-nonguard
  :b1...bm (b1 b2)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With all applicability condition hints.")

 (must-not-be-defsurj)

 (must-not-be-theorems-default)

 (defsurj surj doma domb alpha beta
   :hints (:alpha-image (("Goal" :use alpha-image))
           :beta-image (("Goal" :use beta-image))
           :alpha-of-beta (("Goal" :use alpha-of-beta))
           :doma-guard (("Goal" :use doma-guard))
           :domb-guard (("Goal" :use domb-guard))
           :alpha-guard (("Goal" :use alpha-guard))
           :beta-guard (("Goal" :use beta-guard))))

 (must-be-defsurj)

 (must-be-redundant-theorems-nonguard
  :b1...bm (b1 b2)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With no output.")

 (must-not-be-defsurj)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defsurj surj doma domb alpha beta :print nil)

 (must-be-defsurj)

 (must-be-redundant-theorems-nonguard
  :b1...bm (b1 b2)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With error output.")

 (must-not-be-defsurj)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defsurj surj doma domb alpha beta :print :error)

 (must-be-defsurj)

 (must-be-redundant-theorems-nonguard
  :b1...bm (b1 b2)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With error and result output.")

 (must-not-be-defsurj)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defsurj surj doma domb alpha beta :print :result)

 (must-be-defsurj)

 (must-be-redundant-theorems-nonguard
  :b1...bm (b1 b2)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With error, result, and information output.")

 (must-not-be-defsurj)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defsurj surj doma domb alpha beta :print :info)

 (must-be-defsurj)

 (must-be-redundant-theorems-nonguard
  :b1...bm (b1 b2)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With all output.")

 (must-not-be-defsurj)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defsurj surj doma domb alpha beta :print :all)

 (must-be-defsurj)

 (must-be-redundant-theorems-nonguard
  :b1...bm (b1 b2)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With events submitted.")

 (must-not-be-defsurj)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defsurj surj doma domb alpha beta :show-only nil)

 (must-be-defsurj)

 (must-be-redundant-theorems-nonguard
  :b1...bm (b1 b2)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With events only displayed.")

 (must-not-be-defsurj)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defsurj surj doma domb alpha beta :show-only t)

 (must-not-be-defsurj)

 (must-not-be-theorems-default)

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With lambda expressions.")

 (must-not-be-defsurj)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defsurj surj
   (lambda (a) (doma a))
   (lambda (b1 b2) (domb b1 b2))
   (lambda (a) (alpha a))
   (lambda (b1 b2) (beta b1 b2)))

 (must-be-defsurj :doma (lambda (a) (doma a))
                  :domb (lambda (b1 b2) (domb b1 b2))
                  :alpha (lambda (a) (alpha a))
                  :beta (lambda (b1 b2) (beta b1 b2)))

 (must-be-redundant-theorems-nonguard
  :b1...bm (b1 b2)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With macros.")

 (must-not-be-defsurj)

 (must-not-be-theorems-default)

 (local (enable-all))

 (defmacro doma$ (a) `(doma ,a))
 (defmacro domb$ (b1 b2) `(domb ,b1 ,b2))
 (defmacro alpha$ (a) `(alpha ,a))
 (defmacro beta$ (b1 b2) `(beta ,b1 ,b2))

 (defsurj surj doma$ domb$ alpha$ beta$)

 (must-be-defsurj :doma (lambda (a) (doma a))
                  :domb (lambda (b1 b2) (domb b1 b2))
                  :alpha (lambda (a) (alpha a))
                  :beta (lambda (b1 b2) (beta b1 b2)))

 (must-be-redundant-theorems-nonguard
  :b1...bm (b1 b2)
  :bb1...bbm (b1$ b2$))

 (must-be-redundant-theorems-guard
  :b1...bm (b1 b2))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "With the non-guard-verified variants.")

 (must-not-be-defsurj :name surj*)

 (must-not-be-theorems surj*.alpha-image
                       surj*.beta-image
                       surj*.alpha-of-beta
                       surj*.doma-guard
                       surj*.domb-guard
                       surj*.alpha-guard
                       surj*.beta-guard)

 (local (enable-all))

 (must-fail (defsurj surj* doma* domb* alpha* beta*))

 (defsurj surj* doma* domb* alpha* beta* :guard-thms nil)

 (must-be-defsurj :name surj*
                  :doma doma*
                  :domb domb*
                  :alpha alpha*
                  :beta beta*
                  :alpha-image surj*.alpha-image
                  :beta-image surj*.beta-image
                  :alpha-of-beta surj*.alpha-of-beta
                  :doma-guard nil
                  :domb-guard nil
                  :alpha-guard nil
                  :beta-guard nil)

 (must-be-redundant-theorems-nonguard
  :alpha-image surj*.alpha-image
  :beta-image surj*.beta-image
  :alpha-of-beta surj*.alpha-of-beta
  :doma doma*
  :domb domb*
  :alpha alpha*
  :beta beta*
  :b1...bm (b1 b2)
  :bb1...bbm (b1$ b2$))

 (must-not-be-theorems surj*.doma-guard
                       surj*.domb-guard
                       surj*.alpha-guard
                       surj*.beta-guard)

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (test-title "Redundancy handling.")

 (local (enable-all))

 (defsurj surj doma domb alpha beta)

 (must-be-redundant
  (defsurj surj doma domb alpha beta)
  (defsurj surj doma domb alpha beta :print :all)
  (defsurj surj doma domb alpha beta :show-only t)
  (defsurj surj doma domb alpha beta :print nil :show-only t))

 :with-output-off nil)

(must-succeed*

 (local (enable-all))

 (defsurj surj doma domb alpha beta :print :info)

 (must-be-redundant
  (defsurj surj doma domb alpha beta)
  (defsurj surj doma domb alpha beta :print :error)
  (defsurj surj doma domb alpha beta :show-only t)
  (defsurj surj doma domb alpha beta :print nil :show-only t))

 :with-output-off nil)

(must-succeed*

 (local (enable-all))

 (defsurj surj doma domb alpha beta :show-only t)

 (must-fail-local
  (must-be-redundant
   (defsurj surj doma domb alpha beta)))

 (must-fail-local
  (must-be-redundant
   (defsurj surj doma domb alpha beta :print :all)))

 :with-output-off nil)

(must-succeed*

 (local (enable-all))

 (defsurj surj doma domb alpha beta :print :info :show-only t)

 (must-fail-local
  (must-be-redundant
   (defsurj surj doma domb alpha beta)))

 (must-fail-local
  (must-be-redundant
   (defsurj surj doma domb alpha beta :print :result)))

 (must-be-redundant
  (defsurj surj doma domb alpha beta :show-only t))

 (must-be-redundant
  (defsurj surj doma domb alpha beta :print :all :show-only t))

 :with-output-off nil)

(must-succeed*

 (local (enable-all))

 (defsurj surj doma domb alpha beta)

 (must-fail
  (defsurj surj doma* domb* alpha* beta*))

 :with-output-off nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-title "Proof failures.")

(must-fail
 (defsurj surj doma domb alpha beta))

(must-fail
 (defsurj surj doma domb alpha beta
   :hints (:alpha-image (("Goal" :by alpha-image)))))

(must-fail
 (defsurj surj doma domb alpha beta
   :hints (:alpha-image (("Goal" :by alpha-image))
           :beta-image (("Goal" :by beta-image)))))

(must-fail
 (defsurj surj doma domb alpha beta
   :hints (:alpha-image (("Goal" :by alpha-image))
           :beta-image (("Goal" :by beta-image))
           :alpha-of-beta (("Goal" :by alpha-of-beta)))))

(must-fail
 (defsurj surj doma domb alpha beta
   :hints (:alpha-image (("Goal" :by alpha-image))
           :beta-image (("Goal" :by beta-image))
           :alpha-of-beta (("Goal" :by alpha-of-beta))
           :doma-guard (("Goal" :by doma-guard)))))

(must-fail
 (defsurj surj doma domb alpha beta
   :hints (:alpha-image (("Goal" :by alpha-image))
           :beta-image (("Goal" :by beta-image))
           :alpha-of-beta (("Goal" :by alpha-of-beta))
           :doma-guard (("Goal" :by doma-guard))
           :domb-guard (("Goal" :by domb-guard)))))

(must-fail
 (defsurj surj doma domb alpha beta
   :hints (:alpha-image (("Goal" :by alpha-image))
           :beta-image (("Goal" :by beta-image))
           :alpha-of-beta (("Goal" :by alpha-of-beta))
           :doma-guard (("Goal" :by doma-guard))
           :domb-guard (("Goal" :by domb-guard))
           :alpha-guard (("Goal" :by alpha-guard)))))
