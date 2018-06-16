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

(include-book "centaur/satlink/cnf" :dir :system)
(include-book "std/util/defenum" :dir :system)
(include-book "std/stobjs/absstobjs" :dir :system)
(include-book "centaur/fty/fixequiv" :dir :system)
(local (include-book "arithmetic/top" :dir :system))
(local (in-theory (disable nfix)))

(local (std::add-default-post-define-hook :fix))

(define lit-cube-val ((lit litp)
                      (cube lit-listp))
  :returns (val (or (bitp val)
                    (not val))
                "nil if a don't-care, 1 or 0 for truth value"
                :rule-classes :type-prescription)
  (if (atom cube)
      nil
    (b* ((lit1 (car cube)))
      (cond ((lit-equiv lit lit1) 1)
            ((lit-equiv (lit-negate lit) lit1) 0)
            (t (lit-cube-val lit (cdr cube))))))
  ///

  (defthm lit-cube-val-of-lit-negate
    (equal (lit-cube-val (lit-negate lit) cube)
           (and (lit-cube-val lit cube)
                (b-not (lit-cube-val lit cube))))
    :hints(("Goal" :in-theory (e/d (satlink::equal-of-make-lit)
                                   (lit-negate))
            :induct (lit-cube-val lit cube)
            :expand ((:free (lit) (lit-cube-val lit cube)))))))

(define cube-to-env ((cube lit-listp)
                     (env$))
  :guard (< (max-index-clause cube) (bits-length env$))
  :verify-guards nil
  :returns (new-env$)
  (if (atom cube)
      env$
    (b* ((env$ (cube-to-env (cdr cube) env$))
         (lit (car cube)))
      (set-bit (lit->var lit) (b-not (lit->neg lit)) env$)))
  ///
  (defret len-of-cube-to-env
    (<= (len env$) (len new-env$))
    :rule-classes :linear)

  (verify-guards cube-to-env
    :hints(("Goal" :in-theory (enable max-index-clause))))

  (defret eval-lit-of-cube-to-env
    (equal (eval-lit lit new-env$)
           (or (lit-cube-val lit cube)
               (eval-lit lit env$)))
    :hints(("Goal" :in-theory (enable lit-cube-val eval-lit eval-var)))))
            
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


;; What needs to be proved about what?
;;  -- Every mutator needs to say what status it results in.
;;  -- Every mutator except release needs to say how it updates the formula,
;;     assumption, and new-clause it results in.
;;  -- Everything except solve preserves the callback-count (less important?)
;;  -- Ipasir-solve also needs to say what it does to the solution and solved-assumption.
;;  -- Nobody needs to know about the history field.

(encapsulate
  (((ipasir-signature) => *
    :guard t :formals nil))
  (local (defun ipasir-signature ()
           (declare (xargs :guard t))
           ""))
  (defthm stringp-of-ipasir-signature
    (stringp (ipasir-signature))
    :rule-classes :type-prescription))

(defun ipasir-signature-fake ()
  (declare (xargs :Guard t))
  (progn$ (er hard? 'ipasir-signature-fake
              "The under-the-hood version of ipasir-signature has not been installed.")
          "The under-the-hood version of ipasir-signature has not been installed."))

(defattach ipasir-signature ipasir-signature-fake)

(local (xdoc::set-default-parents ipasir$a))

(define ipasir-init$a ((solver ipasir$a-p)
                       state)
  :guard (non-exec (eq (ipasir$a->status solver) :undef))
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


(define ipasir-reinit$a ((solver ipasir$a-p))
  :guard (non-exec (and (eq (ipasir$a->status solver) :undef)
                        (consp (ipasir$a->history solver))))
  :returns (new-solver ipasir$a-p)
  :short "Logic form of @(see ipasir-reinit).  See @(see ipasir) for usage."
  (b* (((ipasir$a solver)))
    (make-ipasir$a :status :input
                   :callback-count 0
                   :history (cons :reinit solver.history)))
  ///
  (std::defret ipasir-reinit$a-status
    (equal (ipasir$a->status new-solver) :input))

  (std::defret ipasir-reinit$a-formula
    (equal (ipasir$a->formula new-solver) nil))

  (std::defret ipasir-reinit$a-assumption
    (equal (ipasir$a->assumption new-solver) nil))

  (std::defret ipasir-reinit$a-new-clause
    (equal (ipasir$a->new-clause new-solver) nil)))


(define ipasir-release$a ((solver ipasir$a-p))
  :guard (non-exec (not (eq (ipasir$a->status solver) :undef)))
  :returns (new-solver ipasir$a-p)
  :short "Logic form of @(see ipasir-release).  See @(see ipasir) for usage."
  (b* (((ipasir$a solver)))
    (change-ipasir$a solver :status :undef
                            :history (cons :release solver.history)))
  ///
  (std::defret ipasir-release$a-status
    (equal (ipasir$a->status new-solver) :undef))

  (std::defret ipasir-release$a-history
    (consp (ipasir$a->history new-solver))))

(define ipasir-input$a ((solver ipasir$a-p))
  :guard (non-exec (not (eq (ipasir$a->status solver) :undef)))
  :returns (new-solver ipasir$a-p)
  :short "Logic form of @(see ipasir-input).  See @(see ipasir) for usage."
  (b* (((ipasir$a solver)))
    (change-ipasir$a solver :status :input))
  ///
  (std::defret ipasir-input$a-status
    (equal (ipasir$a->status new-solver) :input))

  (defret new-clause-of-ipasir-input$a
    (equal (ipasir$a->new-clause new-solver)
           (ipasir$a->new-clause solver)))

  (defret formula-of-ipasir-input$a
    (equal (ipasir$a->formula new-solver)
           (ipasir$a->formula solver)))

  (defret assumption-of-ipasir-input$a
    (equal (ipasir$a->assumption new-solver)
           (ipasir$a->assumption solver))))

(define ipasir-add-lit$a ((solver ipasir$a-p)
                          (lit litp))
  :guard (non-exec (not (eq (ipasir$a->status solver) :undef)))
  :returns (new-solver ipasir$a-p)
  :short "Logic form of @(see ipasir-add-lit).  See @(see ipasir) for usage."
  (b* (((ipasir$a solver))
       ;; ((when (eql lit-or-zero 0))
       ;;  ;; finalize the current new-clause by adding it to the formula and emptying it
       ;;  (change-ipasir$a solver :formula (cons solver.new-clause solver.formula)
       ;;                   :new-clause nil
       ;;                   :status :input
       ;;                   :history (cons `(:add ,lit-or-zero) solver.history)))
       (- (mbe :logic nil
               :exec (and (not (signed-byte-p 32 lit))
                          (raise "Out of bounds literal: ~x0" lit)))))
    ;; add literal to first clause in formula
    (change-ipasir$a solver
                     :new-clause (cons (lit-fix lit) solver.new-clause)
                     :status :input
                     :history (cons `(:add ,(lit-fix lit)) solver.history)))
  ///
  (std::defret status-of-ipasir-add-lit$a
    (equal (ipasir$a->status new-solver) :input))

  (defret new-clause-of-ipasir-add-lit$a
    (equal (ipasir$a->new-clause new-solver)
           (cons (lit-fix lit) (ipasir$a->new-clause solver))))

  (defret formula-of-ipasir-add-lit$a
    (equal (ipasir$a->formula new-solver)
           ;; (if (eql (ifix lit-or-zero) 0)
           ;;     (cons (ipasir$a->new-clause solver)
           ;;           (ipasir$a->formula solver))
             (ipasir$a->formula solver)))

  (defret assumption-of-ipasir-add-lit$a
    (equal (ipasir$a->assumption new-solver)
           (ipasir$a->assumption solver))))

(define ipasir-finalize-clause$a ((solver ipasir$a-p))
  :guard (non-exec (not (eq (ipasir$a->status solver) :undef)))
  :returns (new-solver ipasir$a-p)
  :short "Logic form of @(see ipasir-finalize-clause).  See @(see ipasir) for usage."
  (b* (((ipasir$a solver)))
    ;; ((when (eql lit-or-zero 0))
    ;;  ;; finalize the current new-clause by adding it to the formula and emptying it
    (change-ipasir$a solver :formula (cons solver.new-clause solver.formula)
                     :new-clause nil
                     :status :input
                     :history (cons :finalize solver.history)))
  ///
  (std::defret status-of-ipasir-finalize-clause$a
    (equal (ipasir$a->status new-solver) :input))

  (defret new-clause-of-ipasir-finalize-clause$a
    (equal (ipasir$a->new-clause new-solver) nil))

  (defret formula-of-ipasir-finalize-clause$a
    (equal (ipasir$a->formula new-solver)
           (cons (ipasir$a->new-clause solver)
                 (ipasir$a->formula solver))))

  (defret assumption-of-ipasir-finalize-clause$a
    (equal (ipasir$a->assumption new-solver)
           (ipasir$a->assumption solver))))

(define ipasir-assume$a ((solver ipasir$a-p)
                         (lit litp))
  :guard (non-exec (not (eq (ipasir$a->status solver) :undef)))
  :returns (new-solver ipasir$a-p)
  :short "Logic form of @(see ipasir-assume).  See @(see ipasir) for usage."
  (b* (((ipasir$a solver))
       (lit (lit-fix lit)))
    (change-ipasir$a solver
                     :assumption (cons lit solver.assumption)
                     :status :input
                     :history (cons `(:assume ,lit) solver.history)))
  ///
  (std::defret status-of-ipasir-assume$a
    (equal (ipasir$a->status new-solver) :input))

  (defret new-clause-of-ipasir-assume$a
    (equal (ipasir$a->new-clause new-solver)
           (ipasir$a->new-clause solver)))

  (defret formula-of-ipasir-assume$a
    (equal (ipasir$a->formula new-solver)
           (ipasir$a->formula solver)))

  (defret assumption-of-ipasir-assume$a
    (b* (((ipasir$a solver))
         ((ipasir$a new-solver)))
      (equal new-solver.assumption
             (cons (lit-fix lit) solver.assumption)))))

(define ipasir-val$a ((solver ipasir$a-p)
                      (lit litp))
  :guard (non-exec (eq (ipasir$a->status solver) :sat))
  :Returns (val (or (bitp val)
                    (not val))
                :rule-classes :type-prescription)
  :short "Logic form of @(see ipasir-val).  See @(see ipasir) for usage."
  (b* (((ipasir$a solver))
       (lit (lit-fix lit)))
    (lit-cube-val lit solver.solution)))

(define ipasir-failed$a ((solver ipasir$a-p)
                         (lit litp))
  :guard (non-exec (b* (((ipasir$a solver)))
                     (and (eq solver.status :unsat)
                          (member lit solver.solved-assumption))))
  :short "Logic form of @(see ipasir-failed).  See @(see ipasir) for usage."
  (b* (((ipasir$a solver))
       (lit (lit-fix lit)))
    (if (member lit solver.solution) 1 0)))

(define ipasir-set-limit$a ((solver ipasir$a-p)
                            (limit acl2::maybe-natp))
  :guard (non-exec (not (eq (ipasir$a->status solver) :undef)))
  :returns (new-solver ipasir$a-p)
  :short "Logic form of @(see ipasir-set-limit).  See @(see ipasir) for usage."
  (b* (((ipasir$a solver)))
    (change-ipasir$a solver
                     :history (cons `(:limit ,(acl2::maybe-natp-fix limit)) solver.history)
                     :callback-count 0))
  ///
  (std::defret status-of-ipasir-set-limit$a
    (equal (ipasir$a->status new-solver)
           (ipasir$a->status solver)))

  (defret new-clause-of-ipasir-set-limit$a
    (equal (ipasir$a->new-clause new-solver)
           (ipasir$a->new-clause solver)))

  (defret formula-of-ipasir-set-limit$a
    (equal (ipasir$a->formula new-solver)
           (ipasir$a->formula solver)))

  (defret assumption-of-ipasir-set-limit$a
    (b* (((ipasir$a solver))
         ((ipasir$a new-solver)))
      (equal new-solver.assumption
             solver.assumption))))

(define ipasir-callback-count$a ((solver ipasir$a-p))
  :guard (non-exec (not (eq (ipasir$a->status solver) :undef)))
  :enabled t
  :short "Logic form of @(see ipasir-callback-count).  See @(see ipasir) for usage."
  (ipasir$a->callback-count solver))


(defun ipasir-useless-clauseproc (clause)
  (list clause))

(defttag ipasir-solve$a)

(define-trusted-clause-processor
  ipasir-useless-clauseproc
  nil
  :partial-theory
  (encapsulate
    (((ipasir-solve$a *) => (mv * *)
      :guard (and (ipasir$a-p solver)
                  (non-exec (and (not (equal (ipasir$a->status solver) :undef))
                                 (not (ipasir$a->new-clause solver)))))
      :formals (solver)))

    (local (define ipasir-solve$a ((solver ipasir$a-p))
             :enabled t
             ;; returns (mv status solver)
             (mv :failed
                 (change-ipasir$a solver
                                  :solution nil
                                  :assumption nil
                                  :status :input
                                  :new-clause nil
                                  ;; :solved-assumption (ipasir$a->assumption solver)
                                  :history (cons :solve (ipasir$a->history solver))))))

    (defthm ipasir-solve$a-status
      (let ((status (mv-nth 0 (ipasir-solve$a solver))))
        (or (equal status :failed)
            (equal status :unsat)
            (equal status :sat)))
      :rule-classes ((:forward-chaining :trigger-terms ((mv-nth 0 (ipasir-solve$a solver))))))

    (defthm ipasir-solve$a-general
      (b* (((ipasir$a solver))
           ((mv ?status (ipasir$a new-solver)) (ipasir-solve$a solver)))
        (and (equal new-solver.formula solver.formula)
             (not (equal new-solver.status :undef))
             (equal new-solver.new-clause nil)
             (ipasir$a-p new-solver)
             ;; (equal new-solver.solved-assumption solver.assumption)
             (equal new-solver.assumption nil)
             (equal new-solver.history (cons :solve solver.history)))))

    (defthm ipasir-solve$a-callback-count
      (b* (((ipasir$a solver))
           ((mv ?status (ipasir$a new-solver)) (ipasir-solve$a solver)))
        (<= solver.callback-count new-solver.callback-count)))


    (defthm ipasir-solve$a-unsat
      (b* (((ipasir$a solver))
           ((mv status (ipasir$a new-solver)) (ipasir-solve$a solver)))
        (implies (equal status :unsat)
                 (and (subsetp new-solver.solution solver.assumption)
                      (equal new-solver.solved-assumption solver.assumption)
                      (equal new-solver.status :unsat)
                      ;; no environment exists which satisfies the assumption (as an assignment) and the formula
                      (implies (equal (eval-formula solver.formula env$) 1)
                               (equal (eval-cube new-solver.solution env$) 0))))))

    (defthm ipasir-solve$a-sat
      (b* (((ipasir$a solver))
           ((mv status (ipasir$a new-solver)) (ipasir-solve$a solver)))
        (implies (equal status :sat)
                 (equal new-solver.status :sat))))
    ;; Won't assume the solution is a correct assignment because we can just
    ;; check it.  Note if we did want to assume something, the strongest
    ;; assumption to make is that the cube-to-env of the assignment satisfies the
    ;; formula/assumption (for any starting env).

    (defthm ipasir-solve$a-failed
      (b* (((ipasir$a solver))
           ((mv status (ipasir$a new-solver)) (ipasir-solve$a solver)))
        (implies (equal status :failed)
                 (equal new-solver.status :input))))))

(defthm symbolp-of-ipasir-solve$a-status
  (symbolp (mv-nth 0 (ipasir-solve$a solver)))
  :rule-classes :type-prescription)

(local (in-theory (disable ifix nth update-nth)))

(defxdoc ipasir-solve$a
  :parents (ipasir$a)
  :short "Logic form of @(see ipasir-solve).  See @(see ipasir) for usage.")

(local (xdoc::set-default-parents ipasir))




(make-event
 `(defstobj ipasir$c
    (ipasir-val
     :type (satisfies ipasir$a-p)
     :initially ,(make-ipasir$a :status :undef))
    (ipasir-limit)
    :renaming ((ipasir-val        ipasir-get)
               (update-ipasir-val ipasir-set)
               (ipasir-limit      ipasir-limit-get)
               (update-ipasir-limit ipasir-limit-set))))

(define create-ipasir$a ()
  :enabled t
  (make-ipasir$a :status :undef))

(define ipasir-init$c (ipasir$c state)
  :guard (eq (ipasir$a->status (ipasir-get ipasir$c)) :undef)
  :enabled t
  (b* (((mv solver state) (ipasir-init$a (ipasir-get ipasir$c) state))
       (ipasir$c (ipasir-set solver ipasir$c)))
    (mv ipasir$c state)))

(define ipasir-reinit$c (ipasir$c)
  :guard (and (eq (ipasir$a->status (ipasir-get ipasir$c)) :undef)
              (consp (ipasir$a->history (ipasir-get ipasir$c))))
  :enabled t
  (ipasir-set (ipasir-reinit$a (ipasir-get ipasir$c)) ipasir$c))

(define ipasir-release$c (ipasir$c)
  :guard (not (eq (ipasir$a->status (ipasir-get ipasir$c)) :undef))
  :enabled t
  (ipasir-set (ipasir-release$a (ipasir-get ipasir$c)) ipasir$c))

(define ipasir-add-lit$c (ipasir$c (lit litp))
  :guard (not (eq (ipasir$a->status (ipasir-get ipasir$c)) :undef))
  :enabled t
  (ipasir-set (ipasir-add-lit$a (ipasir-get ipasir$c) lit) ipasir$c))

(define ipasir-finalize-clause$c (ipasir$c)
  :guard (not (eq (ipasir$a->status (ipasir-get ipasir$c)) :undef))
  :enabled t
  (ipasir-set (ipasir-finalize-clause$a (ipasir-get ipasir$c)) ipasir$c))

(define ipasir-input$c (ipasir$c)
  :guard (not (eq (ipasir$a->status (ipasir-get ipasir$c)) :undef))
  :enabled t
  (ipasir-set (ipasir-input$a (ipasir-get ipasir$c)) ipasir$c))

(define ipasir-assume$c (ipasir$c (lit litp))
  :guard (not (eq (ipasir$a->status (ipasir-get ipasir$c)) :undef))
  :enabled t
  (ipasir-set (ipasir-assume$a (ipasir-get ipasir$c) lit) ipasir$c))

(define ipasir-val$c (ipasir$c (lit litp))
  :guard (eq (ipasir$a->status (ipasir-get ipasir$c)) :sat)
  :enabled t
  (ipasir-val$a (ipasir-get ipasir$c) lit))

(define ipasir-failed$c (ipasir$c (lit litp))
  :guard (b* (((ipasir$a solver) (ipasir-get ipasir$c)))
           (and (eq solver.status :unsat)
                (member lit solver.solved-assumption)))
  :enabled t
  (ipasir-failed$a (ipasir-get ipasir$c) lit))

(define ipasir-solve$c (ipasir$c)
  :guard (and (not (eq (ipasir$a->status (ipasir-get ipasir$c)) :undef))
              (eq (ipasir$a->new-clause (ipasir-get ipasir$c)) nil))
  :enabled t
  (b* (((mv status solver) (ipasir-solve$a (ipasir-get ipasir$c)))
       (ipasir$c (ipasir-set solver ipasir$c)))
    (mv status ipasir$c)))

(define ipasir-set-limit$c (ipasir$c (limit acl2::maybe-natp))
  :guard (not (eq (ipasir$a->status (ipasir-get ipasir$c)) :undef))
  :enabled t
  (ipasir-set (ipasir-set-limit$a (ipasir-get ipasir$c) limit) ipasir$c))

(define ipasir-callback-count$c (ipasir$c)
  :guard (not (eq (ipasir$a->status (ipasir-get ipasir$c)) :undef))
  :enabled t
  (ipasir$a->callback-count (ipasir-get ipasir$c)))



(local (define ipasir-corr (ipasir$c solver)
         :enabled t
         (equal (ipasir-get ipasir$c) solver)))

(acl2::defabsstobj-events ipasir
  :concrete ipasir$c
  :recognizer (ipasirp :logic ipasir$a-p :exec ipasir$cp)
  :creator (create-ipasir :logic create-ipasir$a
                            :exec create-ipasir$c)
  :corr-fn ipasir-corr
  :exports ((ipasir-init :logic ipasir-init$a :exec ipasir-init$c)
            (ipasir-reinit :logic ipasir-reinit$a :exec ipasir-reinit$c)
            (ipasir-release :logic ipasir-release$a :exec ipasir-release$c)
            (ipasir-input :logic ipasir-input$a :exec ipasir-input$c)
            (ipasir-add-lit :logic ipasir-add-lit$a :exec ipasir-add-lit$c)
            (ipasir-finalize-clause :logic ipasir-finalize-clause$a :exec ipasir-finalize-clause$c)
            (ipasir-assume :logic ipasir-assume$a :exec ipasir-assume$c)
            (ipasir-val :logic ipasir-val$a :exec ipasir-val$c)
            (ipasir-failed :logic ipasir-failed$a :exec ipasir-failed$c)
            (ipasir-solve :logic ipasir-solve$a :exec ipasir-solve$c)
            (ipasir-set-limit
             :logic ipasir-set-limit$a :exec ipasir-set-limit$c)
            (ipasir-callback-count
             :logic ipasir-callback-count$a :exec ipasir-callback-count$c)))

;; We used to make the following functions untouchable, but now we just install
;; executable definitions that produce errors. I think that's good enough.
;; Making them untouchable prevented cloning of the ipasir stobj.

;; ;; We need to make these untouchable because we're going to smash their
;; ;; definitions in raw Lisp.  We won't be able to tell this through the absstobj
;; ;; interface, but if we were able to run ipasir-get or ipasir-set on an actual
;; ;; ipasir$c we'd get the wrong answer.

;; (push-untouchable ipasir-get t)
;; (push-untouchable ipasir-set t)
;; (push-untouchable ipasir$cp t)

(acl2::defstobj-clone ipasir2 ipasir :suffix "2")
(acl2::defstobj-clone ipasir3 ipasir :suffix "3")

(push-untouchable ipasir-init$c t)
(push-untouchable ipasir-reinit$c t)
(push-untouchable ipasir-release$c t)
(push-untouchable ipasir-input$c t)
(push-untouchable ipasir-add-lit$c t)
(push-untouchable ipasir-finalize-clause$c t)
(push-untouchable ipasir-assume$c t)
(push-untouchable ipasir-val$c t)
(push-untouchable ipasir-failed$c t)
(push-untouchable ipasir-solve$c t)
(push-untouchable ipasir-set-limit$c t)
(push-untouchable ipasir-callback-count$c t)




(defun with-local-ipasir-core-fn (name bindings inner-form rest)
  (b* (((unless (symbolp name))
        (er hard? 'with-local-ipasir "Bad ipasir stobj name: ~x0~%" name)))
    `(with-local-stobj ,name
       (mv-let ,bindings
         (mv-let ,bindings
           (mv-let (,name state) (ipasir-init ,name state)
             ,inner-form)
           (let* ((,name (ipasir-release ,name)))
             (mv . ,bindings)))
         . ,rest))))

(defun with-local-ipasir-fn (args)
  (case-match args
    ((stobj ('mv-let bindings inner-form . rest))
     (with-local-ipasir-core-fn stobj bindings inner-form rest))
    ((('mv-let bindings inner-form . rest))
     (with-local-ipasir-core-fn 'ipasir bindings inner-form rest))
    (& (er hard? 'with-local-ipasir "Bad arguments to with-local-ipasir: ~x0" args))))

(defmacro with-local-ipasir (&rest args)
  (with-local-ipasir-fn args))

(acl2::def-b*-binder local-ipasir
  :body
  (b* ((forms acl2::forms)
       (rest-expr acl2::rest-expr)
       ((unless (or (not args)
                    (and (consp args)
                         (symbolp (car args))
                         (not (cdr args)))))
        (er hard? 'local-ipasir "Bad local-ipasir args: ~x0~%" args))
       ((unless (and (eql (len forms) 1)
                     (symbol-listp (car forms))
                     (eq (caar forms) 'mv)))
        (er hard? 'local-ipasir "Bound form must be an mv of some symbols, giving the return values.")))
    `(with-local-ipasir ,@args
       (mv-let ,(cdar forms)
         ,rest-expr
         ,@(b* ((returns (remove (if args (car args) 'ipasir) (cdar forms))))
             (if (consp (cdr returns))
                 `((mv . ,returns))
               returns))))))



(defxdoc ipasir
  :parents (acl2::boolean-reasoning)
  :short "ACL2 bindings for the ipasir incremental SAT solving interface"
  :long "<p>IPASIR is a simple C interface to incremental SAT solvers.  (It
stands for Reentrant Incremental Sat solver API, in reverse.) This interface is
supported by a few different solvers because it is used in the SAT
competition's incremental track.  The ipasir distribution, containing the
interface and some sample solvers, can be found at <a
href=\"https://github.com/biotomas/ipasir\">this GitHub repository</a>.  The
ACL2 ipasir library is an attempt to semi-soundly allow ACL2 programs to
interface with such SAT solver libraries.</p>

<h3>Getting Started</h3>

<p>First, if you just want to reason about an incremental solver without
actually running it, you can include \"ipasir-logic.lisp\", which sets up the
abstract stobj representing the solver and its logical story, but doesn't
install the under-the-hood backend and therefore doesn't require any trust
tags.  Additionally, \"ipasir-tools.lisp\" builds on that to create some useful
shortcuts, also without any trust tags.</p>

<p>To load the backend, include \"ipasir-backend.lisp\".  This book first loads
the shared library specified by the environmnent variable
IPASIR_SHARED_LIBRARY, which should contain the path to a SAT solver shared
library. It then overrides the executable definitions of the ipasir interface
functions so that they instead call the appropriate functions from the shared
library.</p>

<p>To build a suitable SAT solver shared library, you can start with the examples
included in the ipasir distribution, available 
<a href=\"https://github.com/biotomas/ipasir\">here</a>.
Additionally, the incremental solvers that competed in the
<a href=\"http://baldur.iti.kit.edu/sat-competition-2016/\">2016 SAT Competition</a>
are available from its website
<a href=\"http://baldur.iti.kit.edu/sat-competition-2016/index.php?cat=solvers\">here</a>.
</p>

<h3>Using ipasir functions</h3>

<p>Note: If you are familiar with ipasir, you'll notice that the ACL2 wrappers
work slightly differently than the underlying ipasir implementation.  The
differences are listed below under \"Departures from the C Interface.\"</p>

<p>One oddity of the ipasir library is that the guards for most of the
interface functions are non-executable, which means you can't run anything on
the global ipasir stobj.  Instead, you need to create a local stobj with @(see
with-local-stobj), or with @(see with-local-ipasir), which also takes care of
initializing and releasing the solver object.  The guards are stated in terms
of the underlying logical model of the solver, which can't actually be accessed
by executable code.  In particular, the solver is said to be in one of the
states @(':undef'), @(':input'), @(':sat''), or @(':unsat'); each function has
certain constraints on the state when it is called.  Note the solver is in the
@(':undef') state when first created.</p>

<p>The following interfacing
functions are provided:</p>

<ul>

<li>@('(ipasir-init ipasir state)') initializes the solver object so that other
functions can then be used.  This is already done for you if you use
@('with-local-ipasir').  It requires that the state of the solver is
@(':undef') and it puts the solver in state @(':input').  It takes and returns
state because (in the logical story) it reads the oracle into the @('init')
field in order to eliminate a source of unsoundness.</li>

<li>@('(ipasir-reinit ipasir)') initializes a solver object, just like
@('ipasir-init'), except that it has an additional guard, @('(consp
ipasir.history)'), which ensures that it can only be called on a solver that
has previously been initialized and subsequently released.</li>

<li>@('(ipasir-release ipasir)') frees the solver object when you are done with
it.  This is also taken care of by @('with-local-ipasir').  It requires that
the solver state not be @(':undef') and it puts it in state @(':undef').</li>

<li>@('(ipasir-add-lit ipasir lit)') is the mechanism by which new clauses may
be added to the formula.  A clause is added by calling this function once for
each literal in the clause, then calling @('ipasir-finalize-clause'), which
adds the clause to the formula.  (Literals are represented as natural numbers
where the LSB indicates negation and the rest is the variable number; see @(see
litp).) Requires that the solver not be in state @(':undef'), and puts the
solver in state @(':input').</li>

<li>@('(ipasir-finalize-clause ipasir)') adds the clause built up by calls of
@('ipasir-add-lit') to the formula, and empties the clause buffer.  Requires
that the solver not be in state @(':undef'), and puts the solver in state
@(':input').</li>

<li>@('(ipasir-assume ipasir lit)') adds a literal to the current assumption
cube.  Whereas clauses added with @('ipasir-add-lit') are permanent, the assumption
is emptied each time @('ipasir-solve') is called.  Requires that the solver not
be in state @(':undef'), and puts the solver in state @(':input').</li>

<li>@('(ipasir-input ipasir)') requires that the solver not be in state
@(':undef') and puts the solver in state @(':input').  In reality, this is a
logical fiction that is convenient for functions that normally add some
literals, clauses, or assumptions but may sometimes not do anything.</li>

<li>@('(ipasir-solve ipasir)') determines the satisfiability of the formula
under the assumption.  It returns @('(mv status ipasir)'), where status is one
of @(':unsat'), @(':sat'), or @(':failed').  When it returns @(':sat'), then
until the next call of @('ipasir-add-lit') or @('ipasir-assume'), the solver can be
queried with @('ipasir-val') to assess the values of literals under the
satisfying assignment.  Similarly, when it returns @(':unsat'), then until the
next call of @('ipasir-add-lit') or @('ipasir-assume') the solver can be queried
with @('ipasir-failed') to determine whether a given assumption literal was in
the unsatisfiable core subset of the assumption.  Requires that the solver not
be in state @(':undef'), and puts the solver in state @(':sat'), @(':unsat'),
or (when failed) @(':input).</li>

<li>@('(ipasir-val ipasir lit)') determines the value of lit under the current
satisfying assignment, returning 1 if true, 0 if false, or @('nil')
if not determined.  Requires that the solver be in state @(':sat') and leaves
it in that state.</li>

<li>@('(ipasir-failed ipasir lit)') determines whether lit, which must be a
member of the assumptions from the previous call of @('ipasir-solve'), was in
the unsatisfiable core, which is a subset of that assumption under which the
formula is unsat.  Requires that the solver be in state @(':unsat') and leaves
it in that state.</li>

<li>@('(ipasir-set-limit ipasir count-or-nil)') limits the effort spent by the
solver.  Logically, all this does is cons something onto the history and reset
the callback count to 0.  Under the hood, it sets a callback function for the
solver to call every so often.  If count-or-nil is a positive number, then each
call of solve may only call the callback that many times before it fails.
Setting it to nil or 0 removes the limit.  If 0, the callbacks are still
performed and counted, but will not cause termination.  The frequency with
which the callback is called varies by solver.</li>

<li>@('(ipasir-callback-count ipasir)') queries how many times the
@('ipasir-set-limit') callback has been called since the last initialization or
call of @('ipasir-set-limit').</li>

</ul>

<h4>Departures from the C Interface</h4>

<ul>

<li>Literals are represented as @('(var << 1) | neg') rather than
@('var*(-1^^neg)'), for compatibility with other ACL2 libraries such as @(see
acl2::satlink) and @(see acl2::aignet).</li>

<li> @('ipasir-solve') returns a symbol as its status rather than an integer
code.</li>

<li> @('ipasir-finalize-clause') is used to complete a clause and add it to the
formula, rather than @('ipasir-add-lit') with literal 0.</li>

<li> @('ipasir-val') returns a bit or NIL rather than a
literal to indicate the value of the literal in the counterexample.</li>

<li> @('ipasir-set-limit') is used to set resource limitations, replacing the
callback mechanism of ipasir_set_terminate.</li>

<li> The ACL2 interface does not yet support the API @('ipasir_set_learn').</li>

</ul>


<h3>Logical story</h3>

<p>There are several problems to solve when trying to soundly model an
interface with an external library in ACL2.  First, we need a logical
description of the behavior of the external library that is specific enough to
be useful, but not so specific that unexpected behaviors produce soundness
bugs.  Second, we need to restrict user access to functions that break the
abstraction that allows us to model the external behavior logically.  Third, we
need to think about possible nondeterminism and how we can rule it out or
soundly account for it.</p>

<h4>Logical description of behavior</h4>

<p>The logical definitions for the ipasir abstract stobj's interface functions
are described in terms of a product data structure, @(see ipasir$a).
The fields of the @('ipasir$a') contain information such as the full
clausal formula and the current assumption, solver status, and current
satisfying assignment or unsat core.  The behavior of the interface functions
above is modeled by updating and retrieving information from these fields.
However, the @('ipasir-solve') function is special because it is a constrained
function: we don't know for any given solver state whether it will solve the
SAT problem or fail due to resource limitations.  We constrain it so that when
it returns @(':unsat') it implies the formula is unsatisfiable under the
assumption, and assume certain other behaviors, e.g., it doesn't change the
formula and it updates the assumption, solution, and status fields
appropriately.</p>

<h4>Preventing Abstraction Breakage</h4>

<p>The concrete stobj used to introduce the abstract stobj (prior to loading
the under-the-hood C interface) is a single-field stobj whose one field is
the (logical) solver object.  The under-the-hood code smashes definitions built
upon this stobj's accessor/updater.  So if a user were to use this concrete
stobj, after calling any of these smashed definitions he/she would find that
the stobj accessor (e.g.) returns some foreign pointer object.  This would be a
logical problem, so we disallow execution of the accessor and updater for the
concrete stobj.</p>

<h4>Handling Nondeterminism</h4>

<p>A possible soundness problem with any external tool is that the logical
model may pretend something is a function which actually isn't.  Calling an
external SAT solver on the same problem multiple times could yield different
results even if the solver is correct; e.g., it could produce different
satisfying assignments.</p>

<p>One way this could occur is by calling @('ipasir-solve') on the same solver
object twice, without changing the formula and with the same assumptions.  We
deal with this possibility in the logical story by having every function that
updates the solver also extend a history field in the solver model, so that you
can't ever get back to the same solver object on which you already called
@('ipasir-solve').</p>

<p>This takes care of multiple calls on the same solver object.  But we could
also construct two different solvers and run exactly the same series of
functions on them, and possibly yield different results due to nondeterminism
in the external library.  To solve this, @('ipasir-init') sets the @('init')
field of the solver model to the result of reading the ACL2 state's oracle.
The abstract stobj interface provides no way to access this field so we can't
know what its value is for any particular instance of the solver, and there's
no way to provably get the same value from the oracle twice, so this ensures
there's no way to make two solvers in such a way that they can logically be
proven to be equal.</p>

<p>This solution is a bit onerous because it means that any function that ever
uses an ipasir solver has to take and return state.  This can be worked around
using @('with-local-state') if necessary, at the cost of possible unsoundness
due to nondeterminism in the external library.  Additionally,
@('ipasir-reinit') can be used to reinitialize a previously released solver
without involving state.</p>")


(defxdoc ipasir-init
  :parents (ipasir)
  :short "Initializes the ipasir solver to a useful state."
  :long "<p>See @(see ipasir) for details.</p>")

(defxdoc ipasir-reinit
  :parents (ipasir)
  :short "Reinitializes a previously released ipasir solver to a useful state."
  :long "<p>See @(see ipasir) for details.</p>")

(defxdoc ipasir-release
  :parents (ipasir)
  :short "Frees the ipasir solver object."
  :long "<p>See @(see ipasir) for details.</p>")

(defxdoc ipasir-add-lit
  :parents (ipasir)
  :short "Add a new literal to the clause being accumulated."
  :long "<p>See @(see ipasir) for details.</p>")

(defxdoc ipasir-finalize-clause
  :parents (ipasir)
  :short "Add the accumulated clause to the formula."
  :long "<p>See @(see ipasir) for details.</p>")

(defxdoc ipasir-assume
  :parents (ipasir)
  :short "Add a literal to the current assumption cube."
  :long "<p>See @(see ipasir) for details.</p>")

(defxdoc ipasir-input
  :parents (ipasir)
  :short "Coerce the solver into the :input state."
  :long "<p>See @(see ipasir) for details.</p>")

(defxdoc ipasir-solve
  :parents (ipasir)
  :short "Attempt to solve the formula under the current assumption."
  :long "<p>See @(see ipasir) for details.</p>")

(defxdoc ipasir-val
  :parents (ipasir)
  :short "Retrieve the value of the given literal under the current satisfying assignment."
  :long "<p>See @(see ipasir) for details.</p>")

(defxdoc ipasir-failed
  :parents (ipasir)
  :short "Check whether a literal is in the current unsatisfiable assumption core."
  :long "<p>See @(see ipasir) for details.</p>")

(defxdoc ipasir-set-limit
  :parents (ipasir)
  :short "Set a limit on the effort spent on each solve attempt."
  :long "<p>See @(see ipasir) for details.</p>")

(defxdoc ipasir-callback-count
  :parents (ipasir)
  :short "Return the number of times the @(see ipasir-set-limit) counter was incremented."
  :long "<p>See @(see ipasir) for details.</p>")

(defxdoc with-local-ipasir
  :parents (ipasir)
  :short "Create a local @(see ipasir) solver object, initialize it, and
properly release it when done."
  :long "<p>The syntax of with-local-ipasir is similar to that of @(see
with-local-stobj), but the first argument (stobj name) is optional and defaults
to @('ipasir').  However, note that @('state') must be available and must be
one of the objects returned by the inner @('mv-let') form; this is because
@(see ipasir-init) returns state.</p>")
