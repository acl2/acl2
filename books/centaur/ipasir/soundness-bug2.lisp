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


(in-package "IPASIR")

; This book demonstrates a soundness hole in ipasir.  The problem is that we
; smash certain functions with under-the-hood implementations.  If these are
; used as intended, namely, only through the ipasir abstract stobj interface,
; then everything is ok (modulo your SAT library being buggy or other unknown
; problems).  However, the functions that are smashed are actually functions on
; a concrete stobj ipasir$c which has its own basic accessors and updaters.  If
; you call some interface function (with its smashed under-the-hood definition)
; and then access some field with a base accessor, you don't always get what
; logically should be there.

; To mitigate this unsoundness, we have made all the functions with smashed
; under-the-hood definitions untouchable, as well as the base
; accessors/updaters.  But this book demonstrates how to work around these problems:

; - One can make a stobj congruent to ipasir$c, thereby making new base
; accessors that aren't untouchable and do the same things as the old ones.

; - One can duplicate enough of the ttag-free ipasir-logic code to reproduce
; one of the functions that will (once ipasir-logic is loaded) be untouchable,
; and use it to create a function (called PROBLEM, below) that is provably T by
; its logical definition but will (once the backend is loaded) produce NIL when
; executed.  After loading ipasir-logic/backend, use this function to prove
; nil.

(include-book "centaur/satlink/cnf" :dir :system)
(include-book "std/util/defenum" :dir :system)
(include-book "std/stobjs/absstobjs" :dir :system)
(include-book "centaur/fty/fixequiv" :dir :system)
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (disable nfix)))

(local (std::add-default-post-define-hook :fix))


;; Dumb hack to prevent users from including this book.  First we use
;; make-event to save the certify-book-info from when this book was certified.
;; Then we check that the current certify-book-info is the same as that
;; constant.  If not, complain.

(make-event
 (let ((certinfo (f-get-global 'acl2::certify-book-info state)))
   `(defconst *my-certify-book-info* ',certinfo)))

(with-output :off :all
  (make-event
   (let* ((certinfo1 (f-get-global 'acl2::certify-book-info state))
          (certinfo2 *my-certify-book-info*))
     (if (equal certinfo1 certinfo2)
         '(value-triple :ok)
       (er hard? 'soundness-bug3 "Don't include this book! It contains a proof of NIL.")))
   :check-expansion t))

            
(std::defenum ipasir-status-p
  (:undef :input :unsat :sat))

(fty::defprod ipasir$a
  :parents (ipasir)
  :short "Datatype for the logical model of an ipasir incremental SAT solver."
  :long "<p>See @(see ipasir).</p>"
  ((formula lit-list-listp      "Permanent formula")
   (assumption lit-listp        "Current assumption, if status is :input, or assumption
                                 before latest solve, if status is :unsat.")
   (new-clause lit-listp          "Partial clause to add to the formula")
   (status ipasir-status-p      "Current status, determining which operations are allowed"
           :default ':undef)
   (solution   lit-listp        "Satisfying assignment from solver, when status = :sat,
                                 or subset of assumptions sufficient to prove unsat, when
                                 status = :unsat")
   (solved-assumption lit-listp "Assumption that was proved unsatisfiable, if status is :unsat.")
   (callback-count natp         "Number of times a callback function has been called during solve" :default 0)
   (history                     "Collects the history of all operations on this solver,
                                 so we can never execute the solver the same way twice")))

(define ipasir-get-status$a ((solver ipasir$a-p))
  :enabled t
  (ipasir$a->status solver))

(define ipasir-init$a ((solver ipasir$a-p)
                       state)
  :guard (eq (ipasir-get-status$a solver) :undef)
  :returns (mv (new-solver ipasir$a-p)
               (new-state (equal new-state (mv-nth 2 (read-acl2-oracle state)))))
  :short "Logic form of @(see ipasir-init).  See @(see ipasir) for usage."
  (b* (((ipasir$a solver))
       ((mv & initval state) (read-acl2-oracle state)))
    (mv (make-ipasir$a :status :input
                       :callback-count 0
                       :history (cons `(:init ,initval) solver.history))
        state))
  ///
  (std::defret ipasir-init$a-status
    (equal (ipasir$a->status new-solver) :input))

  (std::defret ipasir-init$a-formula
    (equal (ipasir$a->formula new-solver) nil))

  (std::defret ipasir-init$a-assumption
    (equal (ipasir$a->assumption new-solver) nil))

  (std::defret ipasir-init$a-new-clause
    (equal (ipasir$a->new-clause new-solver) nil)))

(make-event
 `(defstobj ipasir$c
    (ipasir-val
     :type (satisfies ipasir$a-p)
     :initially ,(make-ipasir$a :status :undef))
    (ipasir-limit)
    (ipasir-status-field :initially :undef)
    (ipasir-empty-new-clause-field :initially t)
    (ipasir-some-history-field :initially nil)
    (ipasir-assumption-field :initially nil)
    (ipasir-solved-assumption-field :initially nil)
    :renaming ((ipasir-val                            ipasir-get)
               (update-ipasir-val                     ipasir-set)
               (ipasir-limit                          ipasir-limit-get)
               (update-ipasir-limit                   ipasir-limit-set)
               (ipasir-status-field                   ipasir-status-get)
               (update-ipasir-status-field            ipasir-status-set)
               (ipasir-assumption-field               ipasir-assumption-get)
               (update-ipasir-assumption-field        ipasir-assumption-set)
               (ipasir-some-history-field             ipasir-some-history-get)
               (update-ipasir-some-history-field      ipasir-some-history-set)
               (ipasir-empty-new-clause-field         ipasir-empty-new-clause-get)
               (update-ipasir-empty-new-clause-field  ipasir-empty-new-clause-set)
               (ipasir-solved-assumption-field        ipasir-solved-assumption-get)
               (update-ipasir-solved-assumption-field ipasir-solved-assumption-set))))

(define ipasir-init$c (ipasir$c state)
  :guard (eq (ipasir$a->status (ipasir-get ipasir$c)) :undef)
  :enabled t
  (b* (((mv solver state) (ipasir-init$a (ipasir-get ipasir$c) state))
       (ipasir$c (ipasir-set solver ipasir$c)))
    (mv ipasir$c state)))


(make-event
 `(defstobj ipasir2$c
    (ipasir-val-2
     :type (satisfies ipasir$a-p)
     :initially ,(make-ipasir$a :status :undef))
    (ipasir-limit-2)
    (ipasir-status-field-2 :initially :undef)
    (ipasir-empty-new-clause-field-2 :initially t)
    (ipasir-some-history-field-2 :initially nil)
    (ipasir-assumption-field-2 :initially nil)
    (ipasir-solved-assumption-field-2 :initially nil)
    :congruent-to ipasir$c))


(define problem (state)
  (with-local-stobj ipasir$c
    (mv-let (ans state ipasir$c)
      (b* (((mv ipasir$c state) (ipasir-init$c ipasir$c state))
           (solver (ipasir-val-2 ipasir$c)))
        (mv (ipasir$a-p solver) state ipasir$c))
      (mv ans state)))
  ///
  (defthm problem-true
    (mv-nth 0 (problem state))))

(define problem-clause-proc ((clause pseudo-term-listp) hint state)
  (declare (ignore hint))
  (b* (((mv ans state) (problem state)))
    (value (if (not ans)
               nil ;; solve!
             (list clause))))
  ///
  (defevaluator problem-ev problem-ev-lst ((problem st) (if a b c)) :namedp t)

  (defthm problem-clause-proc-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp alist)
                  (problem-ev (acl2::conjoin-clauses
                               (acl2::clauses-result
                                (problem-clause-proc clause hint state)))
                              alist))
             (problem-ev (acl2::disjoin clause) alist))
    :hints(("Goal" :in-theory (enable acl2::conjoin)))
    :rule-classes :clause-processor))


(include-book "ipasir-backend")

(defthm bad nil
  :hints (("goal" :clause-processor (problem-clause-proc acl2::clause nil state)))
  :rule-classes nil)



