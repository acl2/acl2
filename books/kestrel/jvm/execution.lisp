; Concrete (non-symbolic) execution of the JVM.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "misc/defpun" :dir :system)
(include-book "misc/defp" :dir :system)
(include-book "execution-common")

;new (this stuff extracted from the compositional cutpoints stuff, which was for a generic machine):

;;
;; NEXT - step thread (th)
;;

(defund next (s) (jvm::step (th) s))

;;
;; RUN-N-STEPS - run thread (th) a given number of steps
;;

;; Run thread (th) in state S for N steps.
;; Param n comes first because it is likely to be a much smaller term than s.
(defund jvm::run-n-steps (n s)
  (if (zp n)
      s
    (jvm::run-n-steps (+ -1 n) (next s))))

(defthm run-n-steps-zp
  (implies (zp n)
           (equal (jvm::run-n-steps n s)
                  s))
  :hints (("Goal" :in-theory (enable jvm::run-n-steps))))

;; This is restricted to the case where we can resolve the instructions (we
;; check that the state is a make-state).
;; TODO: What about IFs/MYIFs?
(defthmd run-n-steps-opener
  (implies (and (not (zp n))
                (syntaxp (and (consp s)
                              (eq 'jvm::make-state (ffn-symb s)))))
           (equal (jvm::run-n-steps n s)
                  (jvm::run-n-steps (+ -1 n) (jvm::step (th) s))))
  :hints (("Goal" :in-theory (enable jvm::run-n-steps next))))

(defthmd run-n-steps-of-myif-split
  (implies (not (zp n))
           (equal (jvm::run-n-steps n (myif test s1 s2))
                  (myif test
                        (jvm::run-n-steps n s1)
                        (jvm::run-n-steps n s2))))
  :hints (("Goal" :in-theory (enable myif))))

;;
;; STACK-HEIGHT-LESS-THAN
;;

;An exit state with respect to stack-height SH is just any state in which the stack height is less than SH.
(defund stack-height-less-than (sh s)
  (< (stack-height s) sh))

;; ;;
;; ;; STEPS-UNTIL-RETURN-FROM-STACK-HEIGHT-TAIL
;; ;;

;; ;If running s will eventually yield an exit state, this returns the number of steps required to reach that state.
;; ;Otherwise, we don't know anything about what this returns.
;; (defpun steps-until-return-from-stack-height-tail (sh s i)
;;   (if (stack-height-less-than sh s)
;;       i
;;     (steps-until-return-from-stack-height-tail sh (next s) (1+ i))))

;; ;;
;; ;; STEPS-UNTIL-RETURN-FROM-STACK-HEIGHT
;; ;;

;; ;If running s will eventually yield an exit state, this returns the number of steps required to reach that state.
;; ;Otherwise, it returns (omega).
;; (defund steps-until-return-from-stack-height (sh s)
;;   (let ((steps (steps-until-return-from-stack-height-tail sh s 0)))
;;     (if (stack-height-less-than sh (jvm::run-n-steps steps s))
;;         steps
;;       (omega) ;fixme think about this
;;       )))

;; ;;
;; ;; RUN-UNTIL-RETURN-FROM-STACK-HEIGHT
;; ;;

;; ;; ;BOZO think about this...
;; ;; (defstub state-about-which-we-know-nothing () t)

;; ;bozo should state-about-which-we-know-nothing take an argument?
;; ;bad name for it, since we know at least that it equals itself!
;; (defund run-until-return-from-stack-height (k s)
;;   (let ((steps (steps-until-return-from-stack-height k s)))
;;     (if (natp steps)
;;         (jvm::run-n-steps steps s)
;;       (jvm::run-n-steps steps s) ;(state-about-which-we-know-nothing) ;(default-state)
;;       )))

;; ;fixme for things like this, can we pass in the exact stack we expect to return to, to save re-computation of the length?
;; (defthm run-until-return-from-stack-height-base
;;    (implies (< (stack-height s) k)
;;             (equal (run-until-return-from-stack-height k s)
;;                    s))
;;    :hints (("Goal" :in-theory (enable RUN-UNTIL-RETURN-FROM-STACK-HEIGHT
;;                                       STEPS-UNTIL-RETURN-FROM-STACK-HEIGHT
;;                                       STACK-HEIGHT-LESS-THAN
;;                                       ;STEPS-UNTIL-RETURN-FROM-STACK-HEIGHT-TAIL
;;                                       ))))



;; ;;
;; ;; EVENTUALLY-RETURNS-FROM-STACK-HEIGHT
;; ;;

;; ;is this the same as steps-until-return-from-stack-height returning an integer?
;; (defund eventually-returns-from-stack-height (sh s)
;;   (stack-height-less-than sh (jvm::run-n-steps (steps-until-return-from-stack-height sh s) s)))

;; ;;
;; ;; EVENTUALLY-RETURNS
;; ;;

;; ;fixme use this or drop it
;; (defund eventually-returns (s)
;;   (eventually-returns-from-stack-height (stack-height s) s))

;; ;fixme prove?!
;; ;deprecated in favor of the fast version but is used to prove it
;; (skip-proofs
;;  (defthmd run-until-return-from-stack-height-opener ;disabled tue may 25 03:50:31 2010
;;    (implies (<= k (stack-height s))
;;             (equal (run-until-return-from-stack-height k s)
;;                    (run-until-return-from-stack-height k (jvm::step (th) s))))
;;    :hints (("Goal" :in-theory (enable run-until-return-from-stack-height
;;                                       steps-until-return-from-stack-height
;;                                       stack-height-less-than)))))

;;
;; run-until-return-from-stack-height
;;

;; A partial function that steps a state until the stack height is less than
;; the given height (if such a state is eventually reachable).  If running s
;; will eventually yield such a state, this returns that state.  Otherwise, we
;; don't know anything about what this returns.
(defpun run-until-return-from-stack-height (sh s)
  (if (stack-height-less-than sh s)
      s
    (run-until-return-from-stack-height sh (next s))))

(defthm run-until-return-from-stack-height-base
  (implies (< (stack-height s) sh)
           (equal (run-until-return-from-stack-height sh s)
                  s))
  :hints (("Goal" :in-theory (enable run-until-return-from-stack-height-def
                                     stack-height-less-than))))

;only used to prove the fast version?
(defthmd run-until-return-from-stack-height-opener
  (implies (<= sh (stack-height s))
           (equal (run-until-return-from-stack-height sh s)
                  (run-until-return-from-stack-height sh (jvm::step (th) s))))
  :hints (("Goal" :in-theory (enable run-until-return-from-stack-height-def
                                     stack-height-less-than
                                     next))))

;; This variant directly introduces do-inst.
(defthmd run-until-return-from-stack-height-opener-fast
  (implies (<= sh (jvm::call-stack-size (jvm::call-stack (th) s)))
           (equal (run-until-return-from-stack-height sh s)
                  (run-until-return-from-stack-height
                   sh
                   (let* ((top-frame (jvm::thread-top-frame (th) s))
                          (instr (lookup (jvm::pc top-frame)
                                         (jvm::method-program (jvm::method-info top-frame)))))
                     (jvm::do-inst (car instr) instr (th) s)))))
  :hints (("Goal"
           :use (:instance run-until-return-from-stack-height-opener)
           :in-theory (e/d (stack-height jvm::step jvm::op-code th) ()))))

;this really splits the simulation
(defthmd run-until-return-from-stack-height-of-myif-split
  (equal (run-until-return-from-stack-height sh (myif test s1 s2))
         (myif test (run-until-return-from-stack-height sh s1)
               (run-until-return-from-stack-height sh s2)))
  :hints (("Goal" :in-theory (enable myif))))

;; The function that we use to symbolically simulate a whole program
(defund run-until-return (s)
  (run-until-return-from-stack-height (stack-height s) s))

;;;
;;; Bounded execution (used in build-class-objects.lisp)
;;;

;This one terminates because it counts down the number of steps left
;fixme: should this stop when it hits an error state?
(defun run-until-return-from-stack-height2 (sh steps-left s)
  (if (zp steps-left)
      s
    (if (stack-height-less-than sh s)
        s
      (run-until-return-from-stack-height2 sh (+ -1 steps-left) (jvm::step (th) s)))))

;This one terminates because it executes at most 1000000000 steps
(defund run-until-return2 (s)
  (run-until-return-from-stack-height2 (stack-height s) 1000000000 s))

 ;; ;move
;; (defthm BOUND-IN-ALISTP-of-step
;;   (implies (and (JVM::JVM-STATEP S)
;;                 (JVM::BOUND-IN-ALISTP thread-designator (JVM::THREAD-TABLE S)))
;;            (JVM::BOUND-IN-ALISTP thread-designator (JVM::THREAD-TABLE (JVM::STEP thread-designator S))))
;;   :otf-flg t
;;   :hints (("Goal" :in-theory (enable JVM::STEP JVM::DO-INST myif))))

;let's see if/when we need this..
;; (defthm jvm-statep-of-run-until-return-from-stack-height2
;;   (implies (and (jvm::jvm-statep s)
;;                 (jvm::bound-in-alistp (th) (jvm::thread-table s)) ;new
;;                 )
;;            (jvm::jvm-statep (run-until-return-from-stack-height2 sh steps-left s))))

;let's see if/when we need this:
;; (defthm jvm-statep-of-run-until-return2
;;   (implies (jvm::jvm-statep s)
;;            (jvm::jvm-statep (run-until-return2 s)))
;;   :hints (("Goal" :in-theory (enable RUN-UNTIL-RETURN2))))

;;
;; run-until-exit-segment
;;

;; Step state S until the stack height is less than segment-stack-height or the
;; stack height is equal to segment-stack-height but execution has exited the
;; code segment indicated by the segment-pcs.
(defp run-until-exit-segment (segment-stack-height segment-pcs s)
   (if (< (stack-height s) segment-stack-height) ;we've exited the segment because we've exited the subroutine call
       s
     (if (< segment-stack-height (stack-height s)) ;if we are in a subroutine call, take another step
         (run-until-exit-segment segment-stack-height segment-pcs (jvm::step (th) s))
       ;;the stack height is the same as the height of the segment:
       (let ((pc (jvm::pc (jvm::thread-top-frame (th) s))))
         (if (not (member-equal pc segment-pcs))
             s ;if we are at the right stack height and not at one of the segment pcs, we've exited the segment
           ;;otherwise, take a step
           (run-until-exit-segment segment-stack-height segment-pcs (jvm::step (th) s)))))))

(defthm run-until-exit-segment-opener-1
  (implies (< segment-stack-height (stack-height s))
           (equal (run-until-exit-segment segment-stack-height segment-pcs s)
                  (run-until-exit-segment segment-stack-height segment-pcs  (jvm::step (th) s)))))

(defthm run-until-exit-segment-opener-2
  (implies (and (equal segment-stack-height (stack-height s))
                (member-equal (jvm::pc (jvm::thread-top-frame (th) s)) segment-pcs))
           (equal (run-until-exit-segment segment-stack-height segment-pcs s)
                  (run-until-exit-segment segment-stack-height segment-pcs  (jvm::step (th) s)))))

(defthm run-until-exit-segment-base-case-1
  (implies (< (stack-height s) segment-stack-height)
           (equal (run-until-exit-segment segment-stack-height segment-pcs s)
                  s)))

(defthm run-until-exit-segment-base-case-2
  (implies (and (equal (stack-height s) segment-stack-height)
                (not (member-equal (jvm::pc (jvm::thread-top-frame (th) s)) segment-pcs)))
           (equal (run-until-exit-segment
                   segment-stack-height
                   segment-pcs s)
                  s)))

(defthm run-until-exit-segment-of-myif
  (equal (run-until-exit-segment segment-stack-height segment-pcs (myif test s1 s2))
         (myif test
               (run-until-exit-segment segment-stack-height segment-pcs s1)
               (run-until-exit-segment segment-stack-height segment-pcs s2)))
  :hints (("Goal" :in-theory (enable myif))))
