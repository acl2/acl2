;; SPDX-FileCopyrightText: Copyright (c) 2020 Andrew T. Walter <me@atwalter.com>
;; SPDX-License-Identifier: MIT
(defpackage #:z3-sort
  (:documentation "A package for all Z3 sort names"))

(defpackage #:z3
  (:documentation "The Lisp-Z3 interface frontend.")
  (:use #:cl #:z3-c)
  (:import-from :trivia :match)
  (:import-from :flexi-streams :octets-to-string)
  (:import-from :cffi :translate-to-foreign :foreign-string-to-lisp :with-foreign-pointer :mem-ref)
  (:export
   ;; Main API
   #:declare-const #:declare-fun #:z3-assert #:z3-assert-fn
   #:z3-assert-soft #:optimize-minimize #:optimize-maximize #:check-sat
   #:get-model #:get-model-as-assignment #:eval-under-model
   #:solver-push #:solver-pop #:solver-reset
   ;; Wrapper types
   #:config #:context #:ast #:func-decl #:func-entry #:func-interp
   #:z3-sort #:model #:solver #:optimizer #:params #:param-descrs
   #:statistics #:tactic #:ast-vector #:algebraic-number
   ;; Model
   #:model-functions #:model-constants #:model-get
   ;; Solver functions
   #:solver-init #:set-solver #:make-simple-solver
   #:make-composite-solver #:make-solver-for-logic
   #:make-solver-from-tactic #:make-optimizer  #:print-solver
   #:set-params #:get-solver-stats
   ;; Sorts
   #:register-sort #:register-parametric-sort #:register-indexed-sort
   #:register-enum-sort #:register-tuple-sort #:get-sort
   ;; Tactics
   #:make-tactic #:make-tactic-with-params
   ;; AST conversion and helpers
   #:convert-to-ast #:ast-to-value #:parse-smt2-file #:parse-smt2-string
   #:ast-vector-to-list
   ;; Z3 global parameters
   #:set-global-param #:get-global-param
   ;; Global variables
   #:*default-context* #:*default-solver*
   ;; Parameters related to algebraic numbers
   #:*ALGEBRAIC-NUMBER-PRINT-MODE*
   #:*ALGEBRAIC-NUMBER-PRINT-DECIMAL-PRECISION*
   #:*ALGEBRAIC-NUMBER-CONVERT-MODE*
   #:*ALGEBRAIC-NUMBER-CONVERT-DECIMAL-PRECISION*))
