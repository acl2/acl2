; Standard Utilities Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defmapping")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/must-be-redundant" :dir :system)
(include-book "std/testing/must-be-table-key" :dir :system)
(include-book "std/testing/must-not-be-table-key" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Utilities for the DEFMAPPING tests.
; The actual tests are in the other defmapping-tests*.lisp files.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; library extensions:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; show an easily searchable title of a test:

(defmacro test-title (str)
  `(cw-event (concatenate 'string "~%~%~%********** " ,str "~%~%")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test that a given symbol names a theorem:

(defmacro must-be-theorem (name)
  (declare (xargs :guard (symbolp name)))
  `(assert! (theorem-symbolp ',name (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test that some given symbols do name theorems:

(define must-be-theorems-fn ((names symbol-listp))
  :returns (events pseudo-event-form-listp)
  (cond ((endp names) nil)
        (t (cons `(must-be-theorem ,(car names))
                 (must-be-theorems-fn (cdr names))))))

(defmacro must-be-theorems (&rest names)
  (declare (xargs :guard (symbol-listp names)))
  `(progn ,@(must-be-theorems-fn names)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test that a given symbol does not name a theorem:

(defmacro must-not-be-theorem (name)
  (declare (xargs :guard (symbolp name)))
  `(assert! (not (theorem-symbolp ',name (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test that some given symbols do not name theorems:

(define must-not-be-theorems-fn ((names symbol-listp))
  :returns (events pseudo-event-form-listp)
  (cond ((endp names) nil)
        (t (cons `(must-not-be-theorem ,(car names))
                 (must-not-be-theorems-fn (cdr names))))))

(defmacro must-not-be-theorems (&rest names)
  (declare (xargs :guard (symbol-listp names)))
  `(progn ,@(must-not-be-theorems-fn names)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test that some rewrite rule is enabled or disabled:

(defmacro must-be-enabled-rewrite-rule (name yes/no)
  (if yes/no
      `(assert! (rune-enabledp '(:rewrite ,name) state))
    `(assert! (rune-disabledp '(:rewrite ,name) state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test that the DEFMAPPING table does not have an entry with the given name:

(defmacro must-not-be-defmapping-entry (&key (name 'map))
  (declare (xargs :guard (symbolp name)))
  `(must-not-be-table-key ,name ,*defmapping-table-name*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test that the DEFMAPPING table has an entry
; with the given name and information:

(defmacro must-be-defmapping-entry (&key
                                    (name 'map)
                                    (doma 'doma)
                                    (domb 'domb)
                                    (alpha 'alpha)
                                    (beta 'beta)
                                    unconditional
                                    (alpha-image 'map.alpha-image)
                                    (beta-image 'map.beta-image)
                                    (beta-of-alpha 'map.beta-of-alpha)
                                    (alpha-of-beta 'map.alpha-of-beta)
                                    (alpha-injective 'map.alpha-injective)
                                    (beta-injective 'map.beta-injective)
                                    (doma-guard 'map.doma-guard)
                                    (domb-guard 'map.domb-guard)
                                    (alpha-guard 'map.alpha-guard)
                                    (beta-guard 'map.beta-guard))
  `(assert!
    (b* ((table (table-alist *defmapping-table-name* (w state)))
         (pair (assoc-eq ',name table))
         ((unless pair) nil)
         (info (cdr pair))
         ((unless (defmapping-infop info)) nil))
      (and (equal (defmapping-info->doma info) ',doma)
           (equal (defmapping-info->domb info) ',domb)
           (equal (defmapping-info->alpha info) ',alpha)
           (equal (defmapping-info->beta info) ',beta)
           (equal (defmapping-info->alpha-image info) ',alpha-image)
           (equal (defmapping-info->beta-image info) ',beta-image)
           (equal (defmapping-info->beta-of-alpha info) ',beta-of-alpha)
           (equal (defmapping-info->alpha-of-beta info) ',alpha-of-beta)
           (equal (defmapping-info->alpha-injective info) ',alpha-injective)
           (equal (defmapping-info->beta-injective info) ',beta-injective)
           (equal (defmapping-info->doma-guard info) ',doma-guard)
           (equal (defmapping-info->domb-guard info) ',domb-guard)
           (equal (defmapping-info->alpha-guard info) ',alpha-guard)
           (equal (defmapping-info->beta-guard info) ',beta-guard)
           (equal (defmapping-info->unconditional info) ,unconditional)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test that the DEFMAPPING theorems with given names and attributes exist:

(defmacro must-be-defmapping-theorems
    (&key (doma 'doma)
          (domb 'domb)
          (alpha 'alpha)
          (beta 'beta)
          unconditional
          (alpha-image 'map.alpha-image)
          (beta-image 'map.beta-image)
          (beta-of-alpha 'map.beta-of-alpha)
          (alpha-of-beta 'map.alpha-of-beta)
          (alpha-injective 'map.alpha-injective)
          (beta-injective 'map.beta-injective)
          (doma-guard 'map.doma-guard)
          (domb-guard 'map.domb-guard)
          (alpha-guard 'map.alpha-guard)
          (beta-guard 'map.beta-guard)
          (g-doma 'g-doma)
          (g-domb 'g-domb)
          (g-alpha 'g-alpha)
          (g-beta 'g-beta)
          (a1...an '(a))
          (b1...bm '(b))
          (aa1...aan '(a$))
          (bb1...bbm '(b$)))
  `(must-be-redundant
    (defthm-all
      :alpha-image ,alpha-image
      :beta-image ,beta-image
      :beta-of-alpha ,beta-of-alpha
      :alpha-of-beta ,alpha-of-beta
      :alpha-injective ,alpha-injective
      :beta-injective ,beta-injective
      :doma-guard ,doma-guard
      :domb-guard ,domb-guard
      :alpha-guard ,alpha-guard
      :beta-guard ,beta-guard
      :unconditional ,unconditional
      :doma ,doma
      :domb ,domb
      :alpha ,alpha
      :beta ,beta
      :g-doma ,g-doma
      :g-domb ,g-domb
      :g-alpha ,g-alpha
      :g-beta ,g-beta
      :a1...an ,a1...an
      :b1...bm ,b1...bm
      :aa1...aan ,aa1...aan
      :bb1...bbm ,bb1...bbm)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test that things are as they should before a DEFMAPPING call,
; i.e. no entry in the table and no theorems:

(defmacro must-be-before-defmapping
    (&key (name 'map)
          beta-of-alpha-thm
          alpha-of-beta-thm
          (guard-thms 't)
          (alpha-image 'map.alpha-image)
          (beta-image 'map.beta-image)
          (beta-of-alpha 'map.beta-of-alpha)
          (alpha-of-beta 'map.alpha-of-beta)
          (alpha-injective 'map.alpha-injective)
          (beta-injective 'map.beta-injective)
          (doma-guard 'map.doma-guard)
          (domb-guard 'map.domb-guard)
          (alpha-guard 'map.alpha-guard)
          (beta-guard 'map.beta-guard))
  `(progn
     (must-not-be-defmapping-entry :name ,name)
     (must-not-be-theorems ,alpha-image
                           ,beta-image
                           ,@(and beta-of-alpha-thm
                                  (list beta-of-alpha))
                           ,@(and alpha-of-beta-thm
                                  (list alpha-of-beta))
                           ,@(and beta-of-alpha-thm
                                  (list alpha-injective))
                           ,@(and alpha-of-beta-thm
                                  (list beta-injective))
                           ,@(and guard-thms
                                  (list doma-guard))
                           ,@(and guard-thms
                                  (list domb-guard))
                           ,@(and guard-thms
                                  (list alpha-guard))
                           ,@(and guard-thms
                                  (list beta-guard)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test that things are as they should before a DEFMAPPING call,
; i.e. an entry in the table, some theorems, and not other theorems:

(defmacro must-be-after-defmapping
    (&key (name 'map)
          (doma 'doma)
          (domb 'domb)
          (alpha 'alpha)
          (beta 'beta)
          beta-of-alpha-thm
          alpha-of-beta-thm
          (guard-thms 't)
          unconditional
          (alpha-image 'map.alpha-image)
          (beta-image 'map.beta-image)
          (beta-of-alpha 'map.beta-of-alpha)
          (alpha-of-beta 'map.alpha-of-beta)
          (alpha-injective 'map.alpha-injective)
          (beta-injective 'map.beta-injective)
          (doma-guard 'map.doma-guard)
          (domb-guard 'map.domb-guard)
          (alpha-guard 'map.alpha-guard)
          (beta-guard 'map.beta-guard)
          (alpha-image-enable 'nil)
          (beta-image-enable 'nil)
          (beta-of-alpha-enable 'nil)
          (alpha-of-beta-enable 'nil)
          (alpha-injective-enable 'nil)
          (beta-injective-enable 'nil)
          (doma-guard-enable 'nil)
          (domb-guard-enable 'nil)
          (alpha-guard-enable 'nil)
          (beta-guard-enable 'nil)
          (g-doma 'g-doma)
          (g-domb 'g-domb)
          (g-alpha 'g-alpha)
          (g-beta 'g-beta)
          (a1...an '(a))
          (b1...bm '(b))
          (aa1...aan '(a$))
          (bb1...bbm '(b$)))
  `(progn
     (must-be-defmapping-entry :name ,name
                               :doma ,doma
                               :domb ,domb
                               :alpha ,alpha
                               :beta ,beta
                               :alpha-image ,alpha-image
                               :beta-image ,beta-image
                               :beta-of-alpha ,(and beta-of-alpha-thm
                                                    beta-of-alpha)
                               :alpha-of-beta ,(and alpha-of-beta-thm
                                                    alpha-of-beta)
                               :alpha-injective ,(and beta-of-alpha-thm
                                                      alpha-injective)
                               :beta-injective ,(and alpha-of-beta-thm
                                                     beta-injective)
                               :doma-guard ,(and guard-thms
                                                 doma-guard)
                               :domb-guard ,(and guard-thms
                                                 domb-guard)
                               :alpha-guard ,(and guard-thms
                                                  alpha-guard)
                               :beta-guard ,(and guard-thms
                                                 beta-guard)
                               :unconditional ,unconditional)
     (must-be-defmapping-theorems :alpha-image ,alpha-image
                                  :beta-image ,beta-image
                                  :beta-of-alpha ,(and beta-of-alpha-thm
                                                       beta-of-alpha)
                                  :alpha-of-beta ,(and alpha-of-beta-thm
                                                       alpha-of-beta)
                                  :alpha-injective ,(and beta-of-alpha-thm
                                                         alpha-injective)
                                  :beta-injective ,(and alpha-of-beta-thm
                                                        beta-injective)
                                  :doma-guard ,(and guard-thms
                                                    doma-guard)
                                  :domb-guard ,(and guard-thms
                                                    domb-guard)
                                  :alpha-guard ,(and guard-thms
                                                     alpha-guard)
                                  :beta-guard ,(and guard-thms
                                                    beta-guard)
                                  :unconditional ,unconditional
                                  :doma ,doma
                                  :domb ,domb
                                  :alpha ,alpha
                                  :beta ,beta
                                  :g-doma ,g-doma
                                  :g-domb ,g-domb
                                  :g-alpha ,g-alpha
                                  :g-beta ,g-beta
                                  :a1...an ,a1...an
                                  :b1...bm ,b1...bm
                                  :aa1...aan ,aa1...aan
                                  :bb1...bbm ,bb1...bbm)
     (must-not-be-theorems ,@(and (not beta-of-alpha-thm)
                                  (list beta-of-alpha))
                           ,@(and (not alpha-of-beta-thm)
                                  (list alpha-of-beta))
                           ,@(and (not beta-of-alpha-thm)
                                  (list alpha-injective))
                           ,@(and (not alpha-of-beta-thm)
                                  (list beta-injective))
                           ,@(and (not guard-thms)
                                  (list doma-guard))
                           ,@(and (not guard-thms)
                                  (list domb-guard))
                           ,@(and (not guard-thms)
                                  (list alpha-guard))
                           ,@(and (not guard-thms)
                                  (list beta-guard)))
     (must-be-enabled-rewrite-rule ,alpha-image ,alpha-image-enable)
     (must-be-enabled-rewrite-rule ,beta-image ,beta-image-enable)
     ,@(and beta-of-alpha-thm
            `((must-be-enabled-rewrite-rule ,beta-of-alpha
                                            ,beta-of-alpha-enable)))
     ,@(and alpha-of-beta-thm
            `((must-be-enabled-rewrite-rule ,alpha-of-beta
                                            ,alpha-of-beta-enable)))
     ,@(and beta-of-alpha-thm
            `((must-be-enabled-rewrite-rule ,alpha-injective
                                            ,alpha-injective-enable)))
     ,@(and alpha-of-beta-thm
            `((must-be-enabled-rewrite-rule ,beta-injective
                                            ,beta-injective-enable)))
     ,@(and guard-thms
            `((must-be-enabled-rewrite-rule ,doma-guard
                                            ,doma-guard-enable)))
     ,@(and guard-thms
            `((must-be-enabled-rewrite-rule ,domb-guard
                                            ,domb-guard-enable)))
     ,@(and guard-thms
            `((must-be-enabled-rewrite-rule ,alpha-guard
                                            ,alpha-guard-enable)))
     ,@(and guard-thms
            `((must-be-enabled-rewrite-rule ,beta-guard
                                            ,beta-guard-enable)))))
