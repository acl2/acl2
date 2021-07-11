; Support for symbolic execution
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "execution-common")
(local (include-book "kestrel/lists-light/len" :dir :system))

;;
;; Re-joining the execution
;;

;if we have (if test state1 state2) but the two states have the same control information on their stack, we can push the if down without having any ifs remain in the control information (ifs may remain in the locals and heap - fixme ifs in the heap might be bad, given that new-address terms might then contain ifs)
;; todo: maybe also include the locked-object from the frame
(defun extract-control-information-from-stack (stack)
  (declare (xargs :measure (jvm::call-stack-size stack)))
  (if (jvm::empty-call-stackp stack)
      nil
    (cons (let ((frame (jvm::top-frame stack)))
            (list (jvm::pc frame)
                  ;; (jvm::method-program (jvm::method-info frame)) ;todo: drop since we have the method-designator?
                  (jvm::method-designator frame)))
          (extract-control-information-from-stack (jvm::pop-frame stack)))))

(defthm len-of-extract-control-information-from-stack
  (equal (len (extract-control-information-from-stack call-stack))
         (jvm::call-stack-size call-stack))
  :hints (("Goal" :in-theory (enable extract-control-information-from-stack))))

(defthm extract-control-information-from-stack-of-push-frame
  (equal (extract-control-information-from-stack (jvm::push-frame frame stack))
         (cons (list (jvm::pc frame)
                     ;; (jvm::method-program (jvm::method-info frame))
                     (jvm::method-designator frame))
               (extract-control-information-from-stack stack))))

;; This fires at join points and allows states with the same control
;; information to be merged.  This is true even without the hyp, but we include
;; it to prevent merging incompatible states (e.g., states at different PCs)
;; since resolving the next instruction in the resulting merged state would
;; fail.
;; This allows the ifs affect the thread-table, not just the heap.
(defthm jvm::myif-of-make-state-and-make-state
  (implies (equal (extract-control-information-from-stack (jvm::binding (th) tt1)) ;;todo: can we make this into a quick syntactic check?
                  (extract-control-information-from-stack (jvm::binding (th) tt2)))
           (equal (myif test
                        (jvm::make-state tt1 h1 ct1 hrt1 monitor-table1 sfm1 ic1 intern-table1)
                        (jvm::make-state tt2 h2 ct2 hrt2 monitor-table2 sfm2 ic2 intern-table2))
                  (jvm::make-state (myif test tt1 tt2) ;improve this to reflect the pushing?
                                   (myif test h1 h2)
                                   (myif test ct1 ct2)
                                   (myif test hrt1 hrt2)
                                   (myif test monitor-table1 monitor-table2)
                                   (myif test sfm1 sfm2)
                                   (myif test ic1 ic2)
                                   (myif test intern-table1 intern-table2))))
  :hints (("Goal" :in-theory (enable myif))))
