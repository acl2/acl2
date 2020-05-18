; Standard Utilities Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defsurj")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/eval" :dir :system)
(include-book "std/testing/must-be-table-key" :dir :system)
(include-book "std/testing/must-not-be-table-key" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Utilities for the DEFSURJ tests.
; The actual tests are in the other defsurj-tests*.lisp files.

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

; test that the DEFSURJ table does not have an entry with the given name:

(defmacro must-not-be-defsurj (&key (name 'surj))
  (declare (xargs :guard (symbolp name)))
  `(must-not-be-table-key ,name ,*defsurj-table-name*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test that the DEFSURJ table has an entry with the given name and information:

(defmacro must-be-defsurj (&key
                           (name 'surj)
                           (doma 'doma)
                           (domb 'domb)
                           (alpha 'alpha)
                           (beta 'beta)
                           (alpha-image 'surj.alpha-image)
                           (beta-image 'surj.beta-image)
                           (alpha-of-beta 'surj.alpha-of-beta)
                           (doma-guard 'surj.doma-guard)
                           (domb-guard 'surj.domb-guard)
                           (alpha-guard 'surj.alpha-guard)
                           (beta-guard 'surj.beta-guard))
  (declare (xargs :guard (and (symbolp name)
                              (pseudo-termfnp doma)
                              (pseudo-termfnp domb)
                              (pseudo-termfnp alpha)
                              (pseudo-termfnp beta)
                              (symbolp alpha-image)
                              (symbolp beta-image)
                              (symbolp alpha-of-beta)
                              (symbolp doma-guard)
                              (symbolp domb-guard)
                              (symbolp alpha-guard)
                              (symbolp beta-guard))))
  `(assert! (b* ((table (table-alist *defsurj-table-name* (w state)))
                 (pair (assoc-eq ',name table))
                 ((unless pair) nil)
                 (info (cdr pair))
                 ((unless (defsurj-infop info)) nil))
              (and (equal (defsurj-info->doma info) ',doma)
                   (equal (defsurj-info->domb info) ',domb)
                   (equal (defsurj-info->alpha info) ',alpha)
                   (equal (defsurj-info->beta info) ',beta)
                   (equal (defsurj-info->alpha-image info) ',alpha-image)
                   (equal (defsurj-info->beta-image info) ',beta-image)
                   (equal (defsurj-info->alpha-of-beta info) ',alpha-of-beta)
                   (equal (defsurj-info->doma-guard info) ',doma-guard)
                   (equal (defsurj-info->domb-guard info) ',domb-guard)
                   (equal (defsurj-info->alpha-guard info) ',alpha-guard)
                   (equal (defsurj-info->beta-guard info) ',beta-guard)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test that the DEFSURJ theorems with the default names do not exist:

(defmacro must-not-be-theorems-default ()
  '(must-not-be-theorems surj.alpha-image
                         surj.beta-image
                         surj.alpha-of-beta
                         surj.doma-guard
                         surj.domb-guard
                         surj.alpha-guard
                         surj.beta-guard))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; test that the DEFSURJ theorems with given attributes are redundant:

(defmacro must-be-redundant-theorems-nonguard
    (&key (alpha-image 'surj.alpha-image)
          (beta-image 'surj.beta-image)
          (alpha-of-beta 'surj.alpha-of-beta)
          (a1...an '(a))
          (b1...bm '(b))
          (bb1...bbm '(b$))
          (doma 'doma)
          (domb 'domb)
          (alpha 'alpha)
          (beta 'beta))
  (declare (xargs :guard (and (symbolp alpha-image)
                              (symbolp beta-image)
                              (symbolp alpha-of-beta)
                              (symbol-listp a1...an)
                              (symbol-listp b1...bm)
                              (symbol-listp bb1...bbm)
                              (symbolp doma)
                              (symbolp domb)
                              (symbolp alpha)
                              (symbolp beta))))
  `(must-be-redundant
    (defthm-nonguard
      :alpha-image ,alpha-image
      :beta-image ,beta-image
      :alpha-of-beta ,alpha-of-beta
      :a1...an ,a1...an
      :b1...bm ,b1...bm
      :bb1...bbm ,bb1...bbm
      :doma ,doma
      :domb ,domb
      :alpha ,alpha
      :beta ,beta)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro must-be-redundant-theorems-guard
    (&key (doma-guard 'surj.doma-guard)
          (domb-guard 'surj.domb-guard)
          (alpha-guard 'surj.alpha-guard)
          (beta-guard 'surj.beta-guard)
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
