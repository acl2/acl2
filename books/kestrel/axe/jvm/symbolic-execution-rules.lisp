; Axe rules for JVM symbolic execution
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/jvm/symbolic-execution" :dir :system) ; for run-n-steps
(include-book "kestrel/jvm/symbolic-execution2" :dir :system)
(include-book "kestrel/jvm/execution" :dir :system)
(include-book "kestrel/jvm/pc-designators" :dir :system)
(include-book "axe-syntax-functions-jvm") ;for get-stack-height-and-pc-to-step-from-myif-nest
(include-book "kestrel/utilities/def-constant-opener" :dir :system)

(defthm run-n-steps-opener-axe
  (implies (and (axe-syntaxp (syntactic-call-of 'jvm::make-state s dag-array)) ;(axe-syntaxp (is-a-make-statep s dag-array))
                (not (zp n)))
           (equal (jvm::run-n-steps n s)
                  (jvm::run-n-steps (+ -1 n) (jvm::step (th) s))))
  :rule-classes nil ;; since this calls-axe-syntaxp
  :hints (("Goal" :in-theory (enable jvm::run-n-steps next))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This can only fire on a make-state, not a myif.
(defthm run-until-return-from-stack-height-base-axe
  (implies (and (axe-syntaxp (syntactic-call-of 'jvm::make-state s dag-array))
                (< (stack-height s) sh))
           (equal (run-until-return-from-stack-height sh s)
                  s))
  :rule-classes nil ;; since this calls axe-syntaxp
  )

;; This can only fire on a make-state, not a myif.
;; This variant directly introduces do-inst.
(defthm run-until-return-from-stack-height-opener-fast-axe
  (implies (and (axe-syntaxp (syntactic-call-of 'jvm::make-state s dag-array))
                (<= sh (jvm::call-stack-size (jvm::call-stack (th) s))))
           (equal (run-until-return-from-stack-height sh s)
                  (run-until-return-from-stack-height
                   sh
                   (let* ((top-frame (jvm::thread-top-frame (th) s))
                          (instr (lookup (jvm::pc top-frame)
                                         (jvm::method-program (jvm::method-info top-frame)))))
                     (jvm::do-inst (car instr) instr (th) s)))))
  :rule-classes nil ;; since this calls axe-syntaxp
  :hints (("Goal"
           :use (:instance run-until-return-from-stack-height-opener-fast)
           :in-theory (e/d (stack-height jvm::step jvm::op-code th) ()))))

;; This can only fire on a make-state, not a myif.
;; This version introduces STEP, not DO-INST.
(defthm run-until-return-from-stack-height-opener-axe
  (implies (and (axe-syntaxp (syntactic-call-of 'jvm::make-state s dag-array))
                (<= sh (stack-height s)))
           (equal (run-until-return-from-stack-height sh s)
                  (run-until-return-from-stack-height sh (jvm::step (th) s))))
  :rule-classes nil ;; since this calls axe-syntaxp
  :hints (("Goal" :in-theory (enable run-until-return-from-stack-height-opener))))

;; (defthmd run-until-return-from-stack-height-opener-fast-print
;;   (implies (<= sh (jvm::call-stack-size (jvm::call-stack (th) s)))
;;            (equal (run-until-return-from-stack-height sh s)
;;                   (run-until-return-from-stack-height
;;                    sh
;;                    (let* ((top-frame (jvm::thread-top-frame (th) s))
;;                           (instr (lookup (jvm::pc top-frame)
;;                                          (jvm::program top-frame))))
;;                      (jvm::do-inst (car instr) (print-constant instr) ;this is what does the printing
;;                                    (th) s)))))
;;   :hints (("Goal" :use (:instance run-until-return-from-stack-height-opener-fast))))

;; The main symbolic execution rule used for handling branches during unrolling.
;; The 2 is here because we usually take a symbolic base stack, add a dummy
;; frame to catch the result, and add the frame in which execution begins.
;; TODO: Build the myif into the structure of the rule?  But then only insert the call to step-state-with-pc-and-call-stack-height on the right branch?
(defthm run-until-return-from-stack-height-of-myif-axe
  (implies (and (axe-syntaxp (is-a-myif myif-nest dag-array)) ;todo: just use SYNTACTIC-CALL-OF? ;could incorporate this check into get-stack-height-and-pc-to-step-from-myif-nest...
                (axe-bind-free (get-stack-height-and-pc-to-step-from-myif-nest myif-nest base-stack dag-array)
                               '(sh2 pc)) ;binds sh2 and pc ;bozo pass in call-stack?
;                (syntaxp (quotep pc))
;                (syntaxp (quotep sh2))
                (<= 2 sh2)
                ;;(>= (jvm::call-stack-size (jvm::call-stack (th) myif-nest) (+ 2 (jvm::call-stack-size base-stack)))) ;this implies that it's okay to step it
                )
           (equal (run-until-return-from-stack-height (+ 2 (jvm::call-stack-size base-stack)) myif-nest)
                  (run-until-return-from-stack-height (+ 2 (jvm::call-stack-size base-stack))
                                                      (step-state-with-pc-and-call-stack-height pc
                                                                                                (+ sh2 (jvm::call-stack-size base-stack))
                                                                                                myif-nest))))
  :rule-classes nil ;; because this calls axe-syntaxp and axe-bind-free
  :hints (("Goal" :in-theory (e/d (step-state-with-pc-and-call-stack-height stack-height
                                                                            run-until-return-from-stack-height-opener)
                                  (jvm::step)))))

;; this version doesn't assume the presence of a dummy frame to catch the result
;; TODO: Build the myif into the structure of the rule?  But then only insert the call to step-state-with-pc-and-call-stack-height on the right branch?
(defthm run-until-return-from-stack-height-of-myif-alt-axe
  (implies (and (axe-syntaxp (is-a-myif myif-nest dag-array)) ;todo: just use SYNTACTIC-CALL-OF?
                (axe-bind-free (get-stack-height-and-pc-to-step-from-myif-nest myif-nest base-stack dag-array)
                               '(sh2 pc)) ;binds sh2 and pc ;bozo pass in call-stack?
;                (syntaxp (quotep pc))
;                (syntaxp (quotep sh2))
                (<= 1 sh2)
                ;;(>= (jvm::call-stack-size (jvm::call-stack (th) myif-nest) (+ 2 (jvm::call-stack-size base-stack)))) ;this implies that it's okay to step it
                )
           (equal (run-until-return-from-stack-height (+ 1 (jvm::call-stack-size base-stack)) myif-nest)
                  (run-until-return-from-stack-height (+ 1 (jvm::call-stack-size base-stack))
                                                      (step-state-with-pc-and-call-stack-height pc
                                                                                                (+ sh2 (jvm::call-stack-size base-stack))
                                                                                                myif-nest))))
  :rule-classes nil ;; because this calls axe-syntaxp and axe-bind-free
  :hints (("Goal" :in-theory (e/d (step-state-with-pc-and-call-stack-height stack-height
                                                                            run-until-return-from-stack-height-opener)
                                  (jvm::step)))))

;; Lift the IF where there is no more stepping to do in the then-part
;; (exception branches may remain).  For example, consider the case where the
;; then-part is finished and the else-part is stuck.
;rename
(defthm run-until-return-from-stack-height-of-myif-axe-split-1
  (implies (axe-syntaxp (no-state-to-step-p tp base-stack dag-array))
           (equal (run-until-return-from-stack-height (+ 2 (jvm::call-stack-size base-stack)) (myif test tp ep))
                  (myif test
                        (run-until-return-from-stack-height (+ 2 (jvm::call-stack-size base-stack)) tp)
                        (run-until-return-from-stack-height (+ 2 (jvm::call-stack-size base-stack)) ep))))
  :rule-classes nil ;; Not for use by the ACL2 rewriter.
  :hints (("Goal" :in-theory (enable myif))))

;; Lift the IF where there is no more stepping to do in the else-part
;; (exception branches may remain). For example, consider the case where the
;; else-part is finished and the then-part is stuck.
;rename
(defthm run-until-return-from-stack-height-of-myif-axe-split-2
  (implies (axe-syntaxp (no-state-to-step-p ep base-stack dag-array))
           (equal (run-until-return-from-stack-height (+ 2 (jvm::call-stack-size base-stack)) (myif test tp ep))
                  (myif test
                        (run-until-return-from-stack-height (+ 2 (jvm::call-stack-size base-stack)) tp)
                        (run-until-return-from-stack-height (+ 2 (jvm::call-stack-size base-stack)) ep))))
  :rule-classes nil ;; Not for use by the ACL2 rewriter.
  :hints (("Goal" :in-theory (enable myif))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We use step-state-with-pc-and-call-stack-height-of-myif to push
;; step-state-with-pc-and-call-stack-height to the leaves of the MYIF nest.
;; When it reaches a leaf (a make-state), one of these 3 rules applies:

;; Only applies when S is a make-state.
(defthm step-state-with-pc-and-call-stack-height-becomes-step-axe
  (implies (and (axe-syntaxp (syntactic-call-of 'jvm::make-state s dag-array))
                (equal pc (jvm::pc (jvm::thread-top-frame (th) s)))
                (equal call-stack-height
                       (jvm::call-stack-size (jvm::call-stack (th) s))))
           (equal (step-state-with-pc-and-call-stack-height pc call-stack-height s)
                  (jvm::step (th) s)))
  :rule-classes nil ;; because this calls axe-syntaxp
  :hints (("Goal" :in-theory (enable step-state-with-pc-and-call-stack-height))))

;; Only applies when S is a make-state.
(defthm step-state-with-pc-and-call-stack-height-does-nothing-1-axe
  (implies (and (axe-syntaxp (syntactic-call-of 'jvm::make-state s dag-array))
                (not (equal pc (jvm::pc (jvm::thread-top-frame (th) s)))))
           (equal (step-state-with-pc-and-call-stack-height pc call-stack-height s)
                  s))
  :rule-classes nil ;; because this calls axe-syntaxp
  :hints (("Goal" :in-theory (enable step-state-with-pc-and-call-stack-height))))

;; Only applies when S is a make-state.
(defthm step-state-with-pc-and-call-stack-height-does-nothing-2-axe
  (implies (and (axe-syntaxp (syntactic-call-of 'jvm::make-state s dag-array))
                (not (equal call-stack-height
                            (jvm::call-stack-size (jvm::call-stack (th) s)))))
           (equal (step-state-with-pc-and-call-stack-height pc call-stack-height s)
                  s))
  :rule-classes nil ;; because this calls axe-syntaxp
  :hints (("Goal" :in-theory (enable step-state-with-pc-and-call-stack-height))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; New scheme using PC designator stacks (TODO: Convert things to just using this scheme?)
;; TODO: Add smart if handling to this scheme.

(def-constant-opener pc-designator-pc) ;; used by the loop lifter

;; Only applies when S is a make-state.
(defthm step-state-with-pc-designator-stack-becomes-step-axe
  (implies (and (axe-syntaxp (syntactic-call-of 'jvm::make-state s dag-array))
                (equal pc-designator-stack (pc-designator-stack-of-state s)))
           (equal (step-state-with-pc-designator-stack pc-designator-stack s)
                  (jvm::step (th) s)))
  :rule-classes nil ;; because this calls axe-syntaxp
  :hints (("Goal" :in-theory (enable step-state-with-pc-designator-stack))))

;; Only applies when S is a make-state (todo: build that in?).
;; It might be faster to combine this rule with step-state-with-pc-designator-stack-becomes-step-axe,
;; but that could lead to unresolved case splits if something goes wrong.
;; TODO: Optimize this to fail fast when, e.g., the top frame tells us this state is not one to step.
(defthm step-state-with-pc-designator-stack-does-nothing-axe
  (implies (and (axe-syntaxp (syntactic-call-of 'jvm::make-state s dag-array))
                (not (equal pc-designator-stack (pc-designator-stack-of-state s))))
           (equal (step-state-with-pc-designator-stack pc-designator-stack s)
                  s))
  :rule-classes nil ;; because this calls axe-syntaxp
  :hints (("Goal" :in-theory (enable step-state-with-pc-designator-stack))))
