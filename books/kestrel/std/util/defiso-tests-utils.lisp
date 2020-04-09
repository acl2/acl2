; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defiso")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/eval" :dir :system)
(include-book "std/testing/must-be-table-key" :dir :system)
(include-book "std/testing/must-not-be-table-key" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Utilities for the DEFISO tests.
; The actual tests are in the other defiso-tests*.lisp files.

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

; test that the DEFISO table does not have an entry with the given name:

(defmacro must-not-be-defiso (&key (name 'iso))
  (declare (xargs :guard (symbolp name)))
  `(must-not-be-table-key ,name ,*defiso-table-name*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test that the DEFISO table has an entry with the given name and information:

(defmacro must-be-defiso (&key
                          (name 'iso)
                          (doma 'doma)
                          (domb 'domb)
                          (alpha 'alpha)
                          (beta 'beta)
                          (alpha-image 'iso.alpha-image)
                          (beta-image 'iso.beta-image)
                          (beta-of-alpha 'iso.beta-of-alpha)
                          (alpha-of-beta 'iso.alpha-of-beta)
                          (alpha-injective 'iso.alpha-injective)
                          (beta-injective 'iso.beta-injective)
                          (doma-guard 'iso.doma-guard)
                          (domb-guard 'iso.domb-guard)
                          (alpha-guard 'iso.alpha-guard)
                          (beta-guard 'iso.beta-guard)
                          unconditional)
  (declare (xargs :guard (and (symbolp name)
                              (pseudo-termfnp doma)
                              (pseudo-termfnp domb)
                              (pseudo-termfnp alpha)
                              (pseudo-termfnp beta)
                              (symbolp alpha-image)
                              (symbolp beta-image)
                              (symbolp beta-of-alpha)
                              (symbolp alpha-of-beta)
                              (symbolp alpha-injective)
                              (symbolp beta-injective)
                              (symbolp doma-guard)
                              (symbolp domb-guard)
                              (symbolp alpha-guard)
                              (symbolp beta-guard)
                              (booleanp unconditional))))
  `(assert! (b* ((table (table-alist *defiso-table-name* (w state)))
                 (pair (assoc-eq ',name table))
                 ((unless pair) nil)
                 (info (cdr pair))
                 ((unless (defiso-infop info)) nil))
              (and (equal (defiso-info->doma info) ',doma)
                   (equal (defiso-info->domb info) ',domb)
                   (equal (defiso-info->alpha info) ',alpha)
                   (equal (defiso-info->beta info) ',beta)
                   (equal (defiso-info->alpha-image info) ',alpha-image)
                   (equal (defiso-info->beta-image info) ',beta-image)
                   (equal (defiso-info->beta-of-alpha info) ',beta-of-alpha)
                   (equal (defiso-info->alpha-of-beta info) ',alpha-of-beta)
                   (equal (defiso-info->alpha-injective info) ',alpha-injective)
                   (equal (defiso-info->beta-injective info) ',beta-injective)
                   (equal (defiso-info->doma-guard info) ',doma-guard)
                   (equal (defiso-info->domb-guard info) ',domb-guard)
                   (equal (defiso-info->alpha-guard info) ',alpha-guard)
                   (equal (defiso-info->beta-guard info) ',beta-guard)
                   (equal (defiso-info->unconditional info) ,unconditional)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test that the DEFISO theorems with the default names do not exist:

(defmacro must-not-be-theorems-default ()
  '(must-not-be-theorems iso.alpha-image
                         iso.beta-image
                         iso.beta-of-alpha
                         iso.alpha-of-beta
                         iso.alpha-injective
                         iso.beta-injective
                         iso.doma-guard
                         iso.domb-guard
                         iso.alpha-guard
                         iso.beta-guard))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test that the DEFISO theorems with given attributes are redundant:

(defmacro must-be-redundant-theorems-nonguard
    (&key (alpha-image 'iso.alpha-image)
          (beta-image 'iso.beta-image)
          (beta-of-alpha 'iso.beta-of-alpha)
          (alpha-of-beta 'iso.alpha-of-beta)
          (alpha-injective 'iso.alpha-injective)
          (beta-injective 'iso.beta-injective)
          (a1...an '(a))
          (b1...bm '(b))
          (aa1...aan '(a$))
          (bb1...bbm '(b$))
          (doma 'doma)
          (domb 'domb)
          (alpha 'alpha)
          (beta 'beta)
          unconditional)
  (declare (xargs :guard (and (symbolp alpha-image)
                              (symbolp beta-image)
                              (symbolp beta-of-alpha)
                              (symbolp alpha-of-beta)
                              (symbolp alpha-injective)
                              (symbolp beta-injective)
                              (symbol-listp a1...an)
                              (symbol-listp b1...bm)
                              (symbol-listp aa1...aan)
                              (symbol-listp bb1...bbm)
                              (symbolp doma)
                              (symbolp domb)
                              (symbolp alpha)
                              (symbolp beta)
                              (booleanp unconditional))))
  `(must-be-redundant
    (defthm-nonguard
      :alpha-image ,alpha-image
      :beta-image ,beta-image
      :beta-of-alpha ,beta-of-alpha
      :alpha-of-beta ,alpha-of-beta
      :alpha-injective ,alpha-injective
      :beta-injective ,beta-injective
      :a1...an ,a1...an
      :b1...bm ,b1...bm
      :aa1...aan ,aa1...aan
      :bb1...bbm ,bb1...bbm
      :doma ,doma
      :domb ,domb
      :alpha ,alpha
      :beta ,beta
      :unconditional ,unconditional)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro must-be-redundant-theorems-guard
    (&key (doma-guard 'iso.doma-guard)
          (domb-guard 'iso.domb-guard)
          (alpha-guard 'iso.alpha-guard)
          (beta-guard 'iso.beta-guard)
          (a1...an '(a))
          (b1...bm '(b))
          (g-doma 'g-doma)
          (g-domb 'g-domb)
          (doma 'doma)
          (domb 'domb)
          (g-alpha 'g-alpha)
          (g-beta 'g-beta))
  (declare (xargs :guard (and (symbolp doma-guard)
                              (symbolp domb-guard)
                              (symbolp alpha-guard)
                              (symbolp beta-guard)
                              (symbol-listp a1...an)
                              (symbol-listp b1...bm)
                              (symbolp g-doma)
                              (symbolp g-domb)
                              (symbolp doma)
                              (symbolp domb)
                              (symbolp g-alpha)
                              (symbolp g-beta))))
  `(must-be-redundant
    (defthm-guard
      :doma-guard ,doma-guard
      :domb-guard ,domb-guard
      :alpha-guard ,alpha-guard
      :beta-guard ,beta-guard
      :a1...an ,a1...an
      :b1...bm ,b1...bm
      :g-doma ,g-doma
      :g-domb ,g-domb
      :doma ,doma
      :domb ,domb
      :g-alpha ,g-alpha
      :g-beta ,g-beta)))
