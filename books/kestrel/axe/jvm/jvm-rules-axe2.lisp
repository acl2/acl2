; More Axe rules about the JVM
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; These are only needed when lifting loops

(include-book "axe-syntax-functions-jvm2") ;for choose-state-to-step
(include-book "kestrel/jvm/execution2" :dir :system) ;for run-until-exit-segment-or-hit-loop-header
(include-book "kestrel/jvm/symbolic-execution2" :dir :system) ;for step-state-with-pc-designator-stack
(include-book "kestrel/utilities/def-constant-opener" :dir :system)
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))

(defthmd not-equal-when-lens-differ
  (implies (not (equal (len x) (len y)))
           (not (equal x y))))

;restricted to avoid case splits.
;needed to compare pc-designator-stacks
(defthm equal-of-cons-and-cons-constants
  (implies (syntaxp (and (quotep a)
                         (quotep b)))
           (equal (equal (cons a x) (cons b y))
                  (and (equal a b) ;gets computed
                       (equal x y)))))

(def-constant-opener pc-designator-pc) ;; used by the loop lifter

;; (defun get-pc-designator-stack-from-call-stack-base-stack (call-stack)
;;   (declare (xargs :guard (and (jvm::call-stackp call-stack)
;;                               (all-framep call-stack) ;drop someday
;;                               )
;;                   :hints (("Goal" :in-theory (enable JVM::POP-FRAME JVM::EMPTY-CALL-STACKP))) ;todo
;;                   ))
;;   (if (equal call-stack base-stack)
;;       (list (get-pc-designator-from-frame (jvm::top-frame call-stack)))
;;   (if (jvm::empty-call-stackp call-stack)
;;       nil ;error
;;     (cons (get-pc-designator-from-frame (jvm::top-frame call-stack))
;;           (get-pc-designator-stack-from-call-stack (jvm::pop-frame call-stack)))))

;; (defun pc-designator-stack-of-state-above-base-stack (base-stack s)
;;   (get-pc-designator-stack-from-call-stack-base-stack (jvm::binding (th) (jvm::thread-table s))))

;; todo: maybe step-state-with-pc-designator-stack needs to just look at the
;; top few frames of the stack, so using the whole pc-designator-stack may be
;; overkill (but we do need to know something about its height)

;; The main symbolic execution rule used for handling branches when lifting loops
;; TODO: Build the myif into the structure of the rule?  But then only insert the call to step-state-with-pc-designator-stack on the right branch?
(defthm run-until-exit-segment-or-hit-loop-header-of-myif-axe
  (implies (and (axe-syntaxp (is-a-myif s dag-array))
                (axe-bind-free (choose-state-to-step s base-stack segment-pcs loop-headers dag-array)
                               '(pc-designator-stack))
                ;;the pc-designator-stack includes one entry for the base frame (that contains the code segment of interest), and perhaps more
                (not (member-equal (first pc-designator-stack) loop-headers))
                ;; (not (jvm::empty-call-stackp base-stack)) ;since we pop a frame off
                (or (< 1 (len pc-designator-stack)) ;test whether we are in a subroutine (ok to step)
                    ;; test whether we are not in a subroutine but are still in the code segment (ok to step):
                    (and (equal 1 (len pc-designator-stack))
                         (member-equal (pc-designator-pc (first pc-designator-stack)) segment-pcs))))
           (equal (run-until-exit-segment-or-hit-loop-header (jvm::call-stack-size base-stack)
                                                             segment-pcs loop-headers
                                                             s)
                  (run-until-exit-segment-or-hit-loop-header
                   (jvm::call-stack-size base-stack)
                   segment-pcs loop-headers
                   (step-state-with-pc-designator-stack (append pc-designator-stack
                                                                (get-pc-designator-stack-from-call-stack
                                                                 (jvm::pop-frame base-stack)))
                                                        s))))
  :rule-classes nil ;; because this rule uses axe-syntaxp and axe-bind-free
  :hints (("Goal" :expand ((get-pc-designator-stack-from-call-stack (jvm::binding (th) (jvm::thread-table s))))
;           :do-not '(generalize)
           :in-theory (enable step-state-with-pc-designator-stack
                            stack-height
                            run-until-exit-segment-or-hit-loop-header-opener-1
                            run-until-exit-segment-or-hit-loop-header-opener-2
                            get-pc-designator-stack-from-call-stack
                            MAKE-PC-DESIGNATOR
                            PC-DESIGNATOR-PC
                            JVM::CALL-STACK-SIZE
                            JVM::EMPTY-CALL-STACKP
                            not-equal-when-lens-differ
                            get-pc-designator-stack-from-call-stack-of-pop-frame))))

(defthm run-until-exit-segment-or-hit-loop-header-opener-1-non-myif
  (implies (and (axe-syntaxp (not-is-a-myif s dag-array)) ;; todo: will it always be a make-state?
                (< segment-stack-height (stack-height s))
                (not (member-equal (get-pc-designator-from-state s) loop-headers)))
           (equal (run-until-exit-segment-or-hit-loop-header segment-stack-height segment-pcs loop-headers s)
                  (run-until-exit-segment-or-hit-loop-header segment-stack-height segment-pcs loop-headers (jvm::step (th) s))))
  :rule-classes nil ;; since this calls axe-syntaxp
  )

(defthm run-until-exit-segment-or-hit-loop-header-opener-2-non-myif
  (implies (and (axe-syntaxp (not-is-a-myif s dag-array)) ;; todo: will it always be a make-state?
                (equal segment-stack-height (stack-height s))
                (member-equal (jvm::pc (jvm::thread-top-frame (th) s)) segment-pcs)
                (not (member-equal (get-pc-designator-from-state s) loop-headers)))
           (equal (run-until-exit-segment-or-hit-loop-header segment-stack-height segment-pcs loop-headers s)
                  (run-until-exit-segment-or-hit-loop-header segment-stack-height segment-pcs loop-headers (jvm::step (th) s))))
  :rule-classes nil ;; since this calls axe-syntaxp
  )

;; Lift the IF where there is no more stepping to do (exception branches may remain).  TODO: Would it suffice for just one of the branches to have no more stepping?
(defthm run-until-exit-segment-or-hit-loop-header-of-myif-axe-lift
  (implies (and (axe-syntaxp (no-state-to-step-for-loop-lifter-p tp base-stack segment-pcs loop-headers dag-array))
                (axe-syntaxp (no-state-to-step-for-loop-lifter-p ep base-stack segment-pcs loop-headers dag-array)))
           (equal (run-until-exit-segment-or-hit-loop-header (jvm::call-stack-size base-stack) segment-pcs loop-headers (myif test tp ep))
                  (myif test
                        (run-until-exit-segment-or-hit-loop-header (jvm::call-stack-size base-stack) segment-pcs loop-headers tp)
                        (run-until-exit-segment-or-hit-loop-header (jvm::call-stack-size base-stack) segment-pcs loop-headers ep))))
  :rule-classes nil ;; because this calls axe-syntaxp
  :hints (("Goal" :in-theory (enable myif))))

;; Only applies when S is a make-state.
(defthm step-state-with-pc-designator-stack-becomes-step-axe
  (implies (and (axe-syntaxp (syntactic-call-of 'jvm::make-state s dag-array))
                (equal pc-designator-stack (pc-designator-stack-of-state s)))
           (equal (step-state-with-pc-designator-stack pc-designator-stack s)
                  (jvm::step (th) s)))
  :rule-classes nil ;; because this calls axe-syntaxp
  :hints (("Goal" :in-theory (enable step-state-with-pc-designator-stack))))

;; Only applies when S is a make-state.
(defthm step-state-with-pc-designator-stack-does-nothing-axe
  (implies (and (axe-syntaxp (syntactic-call-of 'jvm::make-state s dag-array))
                (not (equal pc-designator-stack (pc-designator-stack-of-state s))))
           (equal (step-state-with-pc-designator-stack pc-designator-stack s)
                  s))
  :rule-classes nil ;; because this calls axe-syntaxp
  :hints (("Goal" :in-theory (enable step-state-with-pc-designator-stack))))
