; Utilities to support Axe's version of syntaxp, bind-free, etc.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; STATUS: In-progress.

(in-package "ACL2")

;; This book contains the Axe syntax functions, which are given special
;; treatment by the Axe rewriter (analogous to ACL2's syntaxp and bind-free).

;; An axe-syntaxp hyp is logically T, but during rewriting it serves as a
;; heuristic to decide whether to apply a rule.  The argument to axe-syntaxp
;; should be, in general, a nest of calls to IF and NOT whose leaves are all
;; either quoted constants or applications of axe-syntaxp functions.  An
;; application of an axe-syntaxp function is a function call where the function
;; is built into the rewriter as a supported axe-syntaxp function and the
;; arguments are all either variables or quoted constants.  The variables must
;; be already bound (in the alist used for applying the rule) by the time the
;; axe-syntaxp hyp is encountered, with one exception: an argument that is the
;; symbol DAG-ARRAY is treated specially (the array storing the current DAG is
;; passed into the axe-syntaxp function).  If axe-syntaxp function returns nil,
;; the hyp is considered not to have been relieved.  Otherwise, it is
;; considered to have been relieved.

;leaving this enabled, so that it vanishes during proofs
(defun axe-syntaxp (x)
  (declare (ignore x))
  t)

;; An axe-bind-free is logically T, but during rewriting it serves as a way to
;; heuristically bind free variables in the rule.  It should be of the form
;; (axe-bind-free <term> '<vars-to-bind>).  Note the quote applied to the
;; <vars-to-bind>.  The <term> argument to axe-bind-free should be an
;; application of an axe-bind-free function.  An application of an
;; axe-bind-free function is a function call where the function is built into
;; the rewriter as a supported axe-bind-free function and the arguments are all
;; either variables or quoted constants.  The arguments that are variables must
;; be already bound (in the alist used for applying the rule) by the time the
;; axe-bind-free hyp is encountered, with one exception: an argument that is
;; the symbol DAG-ARRAY is treated specially (the array storing the current DAG
;; is passed into the axe-bind-free function).  The <vars-to-bind> must be a
;; list of symbols disjoint from the variables bound so far when the
;; axe-bind-free hyp is encountered.  The result of the axe-bind-free function
;; must be either nil, indicating failure, or an alist whose keys are exactly
;; the <vars-to-bind>, in order, and whose values are quoted constants or node
;; numbers in the DAG.

;leaving this enabled, so that it vanishes during proofs
(defun axe-bind-free (x vars)
  (declare (ignore x vars))
  t)

;; TODO: Document.
;leaving this enabled, so that it vanishes during proofs
(defun axe-rewrite-objective (x)
  (declare (ignore x))
  t)

;; TODO: Document.
;; TODO: rename axe-work-hard?
;just the identity, but tells Axe (which parts?) to work hard to relieve the hyp that it encloses
(defun work-hard (x) x)
