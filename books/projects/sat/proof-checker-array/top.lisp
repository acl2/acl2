;; Copyright (c) 2016, Regents of the University of Texas
;;
;; License: The MIT License (MIT)
;;
;;   Permission is hereby granted, free of charge, to any person
;;   obtaining a copy of this software and associated documentation
;;   files (the "Software"), to deal in the Software without
;;   restriction, including without limitation the rights to use,
;;   copy, modify, merge, publish, distribute, sublicense, and/or sell
;;   copies of the Software, and to permit persons to whom the
;;   Software is furnished to do so, subject to the following
;;   conditions:
;;
;;   The above copyright notice and this permission notice shall be
;;   included in all copies or substantial portions of the Software.
;;
;;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;;   EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
;;   OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;;   NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
;;   HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
;;   WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
;;   OTHER DEALINGS IN THE SOFTWARE.
;;
;; Original author: Nathan Wetzler <nathan.wetzler@gmail.com>

;; Last Modified:  2016-10-15 20:24

;; ============================= PACKAGE =============================
(in-package "PROOF-CHECKER-ARRAY")


;; ============================ INCLUDES =============================

(include-book "xdoc/top" :dir :system)
;; (include-book "xdoc/debug" :dir :system)

(include-book "assignment-equiv")


;; ===================================================================
;; ============================== XDOC ===============================
;; ===================================================================

(defxdoc PROOF-CHECKER-ARRAY
  :parents (acl2::projects)
  :short "Array-based RAT Proof Checker"
  )

(xdoc::order-subtopics
 PROOF-CHECKER-ARRAY
 (;Background-And-Description
  ))

;; =========================== DESCRIPTION ===========================

(defsection Description
  :extension PROOF-CHECKER-ARRAY
  ;; :parents (PROOF-CHECKER-ARRAY)
  ;; :short ""
  :long
"<p>This proof is the supplemental material for Nathan Wetzler's dissertation
  entitled Efficient, Mechanically-Verified Validation of Satisfiability
  Solvers.  Abstract and links to the dissertation are below.</p>

<h2>Links</h2>

<p>This material is further described in Nathan Wetzler's dissertation
  available as a <a
  href='http://www.cs.utexas.edu/~nwetzler/publications/dissertation-preprint.pdf'>preprint</a>
  or on the <a href='https://repositories.lib.utexas.edu/handle/2152/30538'>UT
  Digital Repository</a>.</p>

<h2>Citation</h2>

<p>Wetzler, Nathan D.: Efficient, Mechanically-Verified Validation of Satisfiability
  Solvers.  The University of Texas at Austin (2015).</p>" )

;; ============================ ABSTRACT =============================

(defsection Abstract
  :extension PROOF-CHECKER-ARRAY
  ;; :parents (PROOF-CHECKER-ARRAY)
  ;; :short ""
  :long
"<h2>Abstract From Dissertation</h2>

<p>Satisfiability (SAT) solvers are commonly used for a variety of
applications, including hardware verification, software verification, theorem
proving, debugging, and hard combinatorial problems.  These applications rely
on the efficiency and correctness of SAT solvers.  When a problem is determined
to be unsatisfiable, how can one be confident that a SAT solver has fully
exhausted the search space?  Traditionally, unsatisfiability results have been
expressed using resolution or clausal proof systems.  Resolution-based proofs
contain perfect reconstruction information, but these proofs are extremely
large and difficult to emit from a solver.  Clausal proofs rely on rediscovery
of inferences using a limited number of techniques, which typically takes
several orders of magnitude longer than the solving time.  Moreover, neither of
these proof systems has been able to express contemporary solving techniques
such as bounded variable addition.  This combination of issues has left SAT
solver authors unmotivated to produce proofs of unsatisfiability.</p>

<p>The work from this dissertation focuses on validating satisfiability solver
output in the unsatisfiability case.  We developed a new clausal proof format
called DRAT that facilitates compact proofs that are easier to emit and capable
of expressing all contemporary solving and preprocessing techniques.
Furthermore, we implemented a validation utility called DRAT-trim that is able
to validate proofs in a time similar to that of the discovery time.  The DRAT
format has seen widespread adoption in the SAT community and the DRAT-trim
utility was used to validate the results of the 2014 SAT Competition.</p>

<p>DRAT-trim uses many advanced techniques to realize its performance gains, so
why should the results of DRAT-trim be trusted?  Mechanical verification
enables users to model programs and algorithms and then prove their correctness
with a proof assistant, such as ACL2.  We designed a new modeling technique for
ACL2 that combines efficient model execution with an agile and convenient
theory.  Finally, we used this new technique to construct a fast,
mechanically-verified validation tool for proofs of unsatisfiability.  This
research allows SAT solver authors and users to have greater confidence in
their results and applications by ensuring the validity of unsatisfiability
results.</p>" )


;; ===================================================================

(set-enforce-redundancy t)


;; ===================================================================
;; =========================== DEFINITIONS ===========================
;; ===================================================================

(defun assignmentp (x)
  (declare (xargs :guard t))
  (and (literal-listp x)
       (unique-literalsp x)
       (no-conflicting-literalsp x)))


(defun assignment-stp (st)
  (declare (xargs :guard t
                  :guard-debug t
                  :stobjs (st)))                  
  (and
   ;; farray
   (farrayp *s* st)
   ;; Four fields in assignment
   (equal (num-fields *s* st)
          4)
   ;; num-vars is length 1 fieldp
   (fieldp *num-vars* *s* st)
   (equal (flength *num-vars* *s* st)
          1)
   ;; let n be num-vars
   (let ((n (fread *num-vars* 0 *s* st)))
     (and
      ;; num-vars is positive
      (<= 0 n)
      ;; stack-end is length 1 fieldp
      (fieldp *stack-end* *s* st)
      (equal (flength *stack-end* *s* st)
             1)
      ;; stack is length n fieldp
      (fieldp *stack* *s* st)
      (equal (flength *stack* *s* st)
             (1+ n))
      ;; lookup is length 2n+2 fieldp
      (fieldp *lookup* *s* st)
      (equal (flength *lookup* *s* st)
             (+ 2 (* 2 n)))
      ;; let se be stack-end
      (let ((se (fread *stack-end* 0 *s* st)))
        (and 
         ;; stack-end is field-offsetp
         (field-offsetp se *stack* *s* st)
         ;; (or (field-offsetp (1- se) *stack* *s* st)
         ;;     (equal se 0))
         ;; stack contains literals
         (stack-contains-literalsp (1- se) st)
         ;; stack unique
         (stack-uniquep (1- se) st)
         ;; stack not conflicting
         (stack-not-conflictingp (1- se) st)
         ;; lookup corresponds to stack
         (lookup-corresponds-with-stackp 2 st)
         ;; 
         (stack-in-rangep (1- se) st)
         ;; stack corresponds with lookup
         (stack-corresponds-with-lookup-p (1- se) st)
         ;;
         (equal (count-assigned 2 st)
                se)
         ))))))


(defun assignedp (lit st)
  (declare (xargs :guard (and (assignment-stp st)
                              (literalp lit)
                              (lit-in-rangep lit st))
                  :stobjs (st)))                  
  (equal (fread *lookup* lit *s* st) 1))

(defun assign-lit (lit st)
  (declare (xargs :guard (and (assignment-stp st)
                              (literalp lit)
                              (lit-in-rangep lit st)
                              (not (field-memberp lit
                                                  (1- (fread *stack-end* 0
                                                             *s* st))
                                                  0 *stack* *s* st))
                              (not (field-memberp (negate lit)
                                                  (1- (fread *stack-end* 0
                                                             *s* st))
                                                  0 *stack* *s* st)))
                  :stobjs (st)))
  (let* ((stack-end (fread *stack-end* 0 *s* st))
         (st (fwrite *lookup* lit 1 *s* st))
         (st (fwrite *stack* stack-end lit *s* st))
         (st (fwrite *stack-end* 0 (1+ stack-end) *s* st)))
    st))


(defun unassign-one (st)
  (declare (xargs :guard (and (assignment-stp st)
                              (not (equal (fread *stack-end* 0 *s* st) 0))
                              (sb60p (1- (fread *stack-end* 0 *s* st))))
                  :stobjs (st)))
  (let* ((1--stack-end (1- (fread *stack-end* 0 *s* st)))
         (lit (fread *stack* 1--stack-end *s* st))
         (st (fwrite *lookup* lit 0 *s* st))
         ;; (st (fwrite *stack* 1--stack-end 0 *s* st))
         (st (fwrite *stack-end* 0 1--stack-end *s* st)))
    st))


(defun unassign-all (i st)
  (declare (xargs :guard (and (assignment-stp st)
                              ;; (sb60p (1- (fread *stack-end* 0 *s* st)))
                              (equal (fread *stack-end* 0 *s* st) i)
                              (or (field-offsetp i *stack* *s* st)
                                  (equal i 0))
                              )
                  :stobjs (st)
                  :measure (nfix i)
                  ))
  (if (not (mbt (and (assignment-stp st)
                     ;; (sb60p (1- (fread *stack-end* 0 *s* st)))
                     (equal (fread *stack-end* 0 *s* st) i)
                     (or (field-offsetp i *stack* *s* st)
                         (equal i 0))
                     )))
      st
    (if (equal i 0)
        st
      (let* ((st (unassign-one st))
             (st (unassign-all (1- i) st)))
        st))))


(defun project1 (i f start st)
  (declare (xargs :guard (and (farrayp start st)
                              (fieldp f start st)
                              (or (field-offsetp i f start st)
                                  (equal i -1)))
                  :stobjs (st)
                  :measure (nfix (1+ i))))
  (if (not (mbt (and (farrayp start st)
                     (fieldp f start st)
                     (or (field-offsetp i f start st)
                         (equal i -1)))))
      nil
    (if (equal i -1)
        nil
      (cons (fread f i start st)
            (project1 (1- i) f start st)))))


(defun project (st)
  (declare (xargs :guard (assignment-stp st)
                  :stobjs (st)))
  (project1 (1- (fread *stack-end* 0 *s* st)) *stack* *s* st))

;; ===================================================================

(defthm unit-propagation-equiv
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st))
           (equal (project (unit-propagation-st formula st))
                  (unit-propagation formula (project st)))))

;; ===================================================================
;; =========================== MAIN PROOF ============================
;; ===================================================================

(defthm exists-solution-implies-not-refutationp-st-contrapositive
  (implies (and (assignment-stp st)
                (formulap formula)
                (formula-in-rangep formula st)
                (clause-listp clause-list)
                (clause-list-in-rangep clause-list st)
                (mv-nth 0 (refutationp-st clause-list formula st)))
           (not (exists-solution formula))))

(defthm main-theorem
  (implies (and (formulap formula)
                (refutationp clause-list formula))
           (not (exists-solution formula))))
