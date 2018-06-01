; IPASIR - Link from ACL2 to IPASIR incremental sat solvers
; Copyright (C) 2017 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original authors: Sol Swords <sswords@centtech.com>
(defpackage :ipasir-raw (:use :common-lisp :cffi))


(in-package :ipasir-raw)


;; /**
;;  * Return the name and the version of the incremental SAT
;;  * solving library.
;;  */
;; const char * ipasir_signature ();
(defcfun "ipasir_signature" :pointer)

;; /**
;;  * Construct a new solver and return a pointer to it.
;;  * Use the returned pointer as the first parameter in each
;;  * of the following functions.
;;  *
;;  * Required state: N/A
;;  * State after: INPUT
;;  */
;; void * ipasir_init ();
(defcfun "ipasir_init" :pointer)

;; /**
;;  * Release the solver, i.e., all its resoruces and
;;  * allocated memory (destructor). The solver pointer
;;  * cannot be used for any purposes after this call.
;;  *
;;  * Required state: INPUT or SAT or UNSAT
;;  * State after: undefined
;;  */
;; void ipasir_release (void * solver);
(defcfun "ipasir_release" :void
  (solver :pointer))

;; /**
;;  * Add the given literal into the currently added clause
;;  * or finalize the clause with a 0.  Clauses added this way
;;  * cannot be removed. The addition of removable clauses
;;  * can be simulated using activation literals and assumptions.
;;  *
;;  * Required state: INPUT or SAT or UNSAT
;;  * State after: INPUT
;;  *
;;  * Literals are encoded as (non-zero) integers as in the
;;  * DIMACS formats.  They have to be smaller or equal to
;;  * INT_MAX and strictly larger than INT_MIN (to avoid
;;  * negation overflow).  This applies to all the literal
;;  * arguments in API functions.
;;  */
;; void ipasir_add (void * solver, int lit_or_zero);
(defcfun "ipasir_add" :void
  (solver :pointer)
  (lit_or_zero :int))

;; /**
;;  * Add an assumption for the next SAT search (the next call
;;  * of ipasir_solve). After calling ipasir_solve all the
;;  * previously added assumptions are cleared.
;;  *
;;  * Required state: INPUT or SAT or UNSAT
;;  * State after: INPUT
;;  */
;; void ipasir_assume (void * solver, int lit);
(defcfun "ipasir_assume" :void
  (solver :pointer)
  (lit :int))

;; /**
;;  * Solve the formula with specified clauses under the specified assumptions.
;;  * If the formula is satisfiable the function returns 10 and the state of the solver is changed to SAT.
;;  * If the formula is unsatisfiable the function returns 20 and the state of the solver is changed to UNSAT.
;;  * If the search is interrupted (see ipasir_set_terminate) the function returns 0 and the state of the solver remains INPUT.
;;  * This function can be called in any defined state of the solver.
;;  *
;;  * Required state: INPUT or SAT or UNSAT
;;  * State after: INPUT or SAT or UNSAT
;;  */
;; int ipasir_solve (void * solver);
(defcfun "ipasir_solve" :int
  (solver :pointer))

;; /**
;;  * Get the truth value of the given literal in the found satisfying
;;  * assignment. Return 'lit' if True, '-lit' if False, and 0 if not important.
;;  * This function can only be used if ipasir_solve has returned 10
;;  * and no 'ipasir_add' nor 'ipasir_assume' has been called
;;  * since then, i.e., the state of the solver is SAT.
;;  *
;;  * Required state: SAT
;;  * State after: SAT
;;  */
;; int ipasir_val (void * solver, int lit);
(defcfun "ipasir_val" :int
  (solver :pointer)
  (lit :int))

;; /**
;;  * Check if the given assumption literal was used to prove the
;;  * unsatisfiability of the formula under the assumptions
;;  * used for the last SAT search. Return 1 if so, 0 otherwise.
;;  * This function can only be used if ipasir_solve has returned 20 and
;;  * no ipasir_add or ipasir_assume has been called since then, i.e.,
;;  * the state of the solver is UNSAT.
;;  *
;;  * Required state: UNSAT
;;  * State after: UNSAT
;;  */
;; int ipasir_failed (void * solver, int lit);
(defcfun "ipasir_failed" :int
  (solver :pointer)
  (lit :int))



;; /**
;;  * Set a callback function used to indicate a termination requirement to the
;;  * solver. The solver will periodically call this function and check its return
;;  * value during the search. The ipasir_set_terminate function can be called in any
;;  * state of the solver, the state remains unchanged after the call.
;;  * The callback function is of the form "int terminate(void * state)"
;;  *   - it returns a non-zero value if the solver should terminate.
;;  *   - the solver calls the callback function with the parameter "state"
;;  *     having the value passed in the ipasir_set_terminate function (2nd parameter).
;;  *
;;  * Required state: INPUT or SAT or UNSAT
;;  * State after: INPUT or SAT or UNSAT
;;  */
;; void ipasir_set_terminate (void * solver, void * state, int (*terminate)(void * state));
(defcfun "ipasir_set_terminate" :void
  (solver :pointer)
  (state :pointer)
  (terminate :pointer))

;; The state-ptr is either NULL (meaning no limit) or a foreign array of two
;; ints of which the first is the current count and the second is the limit.
;; The state-ptr is null IFF the callback is null.  Limit of 0 means unlimited,
;; but still track callbacks.
(defcallback term :int ((st :pointer))
  ;; (format t "term called: ~a~%" st)
  ;; (if (null-pointer-p st)
  ;;     0
  ;; increment the count, then compare
  (incf (mem-aref st :int))
  (let* ((count (mem-aref st :int))
         (limit (mem-aref st :int 1)))
    ;; (format t "count: ~a limit: ~a~%" count limit)
    (if (eql count limit) 1 0)))


;; Limit state is a 3-int array:
;;    callback-count current-limit per-solve-limit
(defun ipasir-set-limit (solver limit-ptr n)
  (if n
      (let* ((ptr (if (or (not limit-ptr)
                          (null-pointer-p limit-ptr))
                      (foreign-alloc :int :initial-element 0 :count 3)
                    limit-ptr)))
        (setf (mem-aref ptr :int) 0) ;; reset callback count
        (setf (mem-aref ptr :int 2) n) ;; per-solve limit
        (ipasir-set-terminate solver ptr (callback term))
        ptr)
    (progn
      (unless (or (not limit-ptr) (null-pointer-p limit-ptr))
        (foreign-free limit-ptr))
      (let ((null-ptr (null-pointer)))
        (ipasir-set-terminate solver null-ptr null-ptr)
        null-ptr))))

(defun ipasir-reset-limit (limit-ptr)
  (unless (null-pointer-p limit-ptr)
    (let* ((count (mem-aref limit-ptr :int))
           (per-solve-limit (mem-aref limit-ptr :int 2)))
      (setf (mem-aref limit-ptr :int 1) (+ count per-solve-limit)))))

(defun ipasir-callback-count (limit-ptr)
  (if (null-pointer-p limit-ptr)
      0
    (mem-aref limit-ptr :int)))
      
  


(in-package "IPASIR")

(defun ipasir-get (ipasir$c)
  (er hard? 'ipasir-get "This function can't be executed once the ipasir execution environment is installed."))

(defun ipasir-set (ipasir$c)
  (er hard? 'ipasir-set "This function can't be executed once the ipasir execution environment is installed."))

(defun ipasir-limit-get (ipasir$c)
  (er hard? 'ipasir-get-limit "This function can't be executed once the ipasir execution environment is installed."))

(defun ipasir-limit-set (ipasir$c)
  (er hard? 'ipasir-set-limit "This function can't be executed once the ipasir execution environment is installed."))

(defun ipasir$cp (ipasir$c)
  (er hard? 'ipasir$cp "This function can't be executed once the ipasir execution environment is installed."))

(defmacro ipasir-get-raw (ipasir)
  `(svref (the (simple-array t (2)) ,ipasir) 0))

(defmacro ipasir-get-limit-raw (ipasir)
  `(svref (the (simple-array t (2)) ,ipasir) 1))

;; need to define both the regular function name and *1* for attachment to work
(defun acl2_*1*_ipasir::ipasir-signature-real ()
  ;; note: foreign-string-to-lisp returns 2 values, just want the first
  (let* ((ans (cffi::foreign-string-to-lisp (ipasir-raw::ipasir-signature))))
    ans))

(defun ipasir-signature-real ()
  ;; note: foreign-string-to-lisp returns 2 values, just want the first
  (let* ((ans (cffi::foreign-string-to-lisp (ipasir-raw::ipasir-signature))))
    ans))

(defattach ipasir-signature ipasir-signature-real)

(defun ipasir-reinit$c (ipasir)
  ;; Note: This function will throw if it is run before an ipasir library is
  ;; loaded.
  (handler-case (setf (ipasir-get-raw ipasir) (ipasir-raw::ipasir-init))
    (error () (er hard? 'ipasir-init "Ipasir-init failed: no ipasir shared library loaded?")))
  (setf (ipasir-get-limit-raw ipasir) (ipasir-raw::ipasir-set-limit (ipasir-get-raw ipasir)
                                                                      (ipasir-get-limit-raw ipasir)
                                                                      nil))
  ipasir)

(defun ipasir-init$c (ipasir state)
  (mv (ipasir-reinit$c ipasir) state))

(defun ipasir-release$c (ipasir)
  (ipasir-raw::ipasir-release (ipasir-get-raw ipasir))
  ipasir)

(defun ipasir-input$c (ipasir)
  ipasir)

(defun ipasir-add-lit$c (ipasir lit)
  (ipasir-raw::ipasir-add (ipasir-get-raw ipasir)
                          (satlink::satlink-to-dimacs-lit lit))
  ipasir)

(defun ipasir-finalize-clause$c (ipasir)
  (ipasir-raw::ipasir-add (ipasir-get-raw ipasir) 0)
  ipasir)

(defun ipasir-assume$c (ipasir lit)
  (ipasir-raw::ipasir-assume (ipasir-get-raw ipasir)
                             (satlink::satlink-to-dimacs-lit lit))
  ipasir)

(defun ipasir-solve$c (ipasir)
  (ipasir-raw::ipasir-reset-limit (ipasir-get-limit-raw ipasir))
  (let ((res (ipasir-raw::ipasir-solve (ipasir-get-raw ipasir))))
    (case res
      (10 (mv :sat ipasir))
      (20 (mv :unsat ipasir))
      (otherwise (mv :failed ipasir)))))

(defun ipasir-val$c (ipasir lit)
  (let* ((dimacs-lit (satlink::satlink-to-dimacs-lit lit))
         (result-lit (ipasir-raw::ipasir-val (ipasir-get-raw ipasir) dimacs-lit)))
    (cond ((int= result-lit 0) nil) ;; dont-care
          ((int= result-lit (- dimacs-lit)) 0)
          ((int= result-lit dimacs-lit) 1)
          (otherwise (er hard? 'ipasir-val
                         "Ipasir-val produced an unexpected result -- noncompliant implementation?~%")))))

(defun ipasir-failed$c (ipasir lit)
  (ipasir-raw::ipasir-failed (ipasir-get-raw ipasir)
                             (satlink::satlink-to-dimacs-lit lit)))

(defun ipasir-set-limit$c (ipasir limit)
  (setf (ipasir-get-limit-raw ipasir)
        (ipasir-raw::ipasir-set-limit (ipasir-get-raw ipasir)
                                      (ipasir-get-limit-raw ipasir)
                                      limit))
  ipasir)

(defun ipasir-callback-count$c (ipasir)
  (ipasir-raw::ipasir-callback-count (ipasir-get-limit-raw ipasir)))

;; (defun def-ipasir-ipasir-raw (template)
;;   (eval (acl2::template-subst-top *ipasir-raw-template* template)))

