; Execution for loop lifting
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book deals with running the JVM until a loop header is reached or a
;; code segment is exited.

(include-book "misc/defp" :dir :system)
(include-book "execution-common")
(include-book "pc-designators")

;;
;; run-until-exit-segment-or-hit-loop-header (for when we are not unrolling loops)
;;

;todo: pass in the thread (this assumes thread (th))
;;Defp is needed to define this because there is more than 1 recursive call.
(defp run-until-exit-segment-or-hit-loop-header (segment-stack-height segment-pcs loop-headers s)
  (if (< (stack-height s) segment-stack-height) ;we've exited the segment because we've exited the subroutine (by popping off a stack frame)
      s
    ;;check if we are at a loop header:
    (if (member-equal (get-pc-designator-from-state s) ;possible-loop-header
                      loop-headers)
        s ;stop
      ;;otherwise, we are not at a loop header:
      (if (< segment-stack-height (stack-height s)) ;if we are in a nested subroutine call, take another step
          (run-until-exit-segment-or-hit-loop-header segment-stack-height segment-pcs loop-headers (jvm::step (th) s))
        ;;the stack height is the same as the height of the segment:
        (if (not (member (jvm::pc (jvm::thread-top-frame (th) s)) segment-pcs))
            s ;if we are at the right stack height and not at one of the segment pcs, we've exited the segment
          ;;otherwise, take a step
          (run-until-exit-segment-or-hit-loop-header segment-stack-height segment-pcs loop-headers (jvm::step (th) s)))))))

;; We might be able to use defopeners to obtain these next 5 rules:

(defthm run-until-exit-segment-or-hit-loop-header-opener-1
  (implies (and (< segment-stack-height (stack-height s))
                (not (member-equal (get-pc-designator-from-state s) loop-headers)))
           (equal (run-until-exit-segment-or-hit-loop-header segment-stack-height segment-pcs loop-headers s)
                  (run-until-exit-segment-or-hit-loop-header segment-stack-height segment-pcs loop-headers (jvm::step (th) s)))))

(defthm run-until-exit-segment-or-hit-loop-header-opener-2
  (implies (and (equal segment-stack-height (stack-height s))
                (member-equal (jvm::pc (jvm::thread-top-frame (th) s)) segment-pcs)
                (not (member-equal (get-pc-designator-from-state s) loop-headers)))
           (equal (run-until-exit-segment-or-hit-loop-header segment-stack-height segment-pcs loop-headers s)
                  (run-until-exit-segment-or-hit-loop-header segment-stack-height segment-pcs loop-headers (jvm::step (th) s)))))

(defthm run-until-exit-segment-or-hit-loop-header-base-case-1
  (implies (< (stack-height s) segment-stack-height)
           (equal (run-until-exit-segment-or-hit-loop-header segment-stack-height segment-pcs loop-headers s)
                  s)))

(defthm run-until-exit-segment-or-hit-loop-header-base-case-2
  (implies (member-equal (get-pc-designator-from-state s) loop-headers)
           (equal (run-until-exit-segment-or-hit-loop-header segment-stack-height segment-pcs loop-headers s)
                  s)))

(defthm run-until-exit-segment-or-hit-loop-header-base-case-3
  (implies (and (equal (stack-height s) segment-stack-height)
                (not (member-equal (jvm::pc (jvm::thread-top-frame (th) s)) segment-pcs)))
           (equal (run-until-exit-segment-or-hit-loop-header
                   segment-stack-height
                   segment-pcs loop-headers s)
                  s)))

;; Push run-until-exit-segment-or-hit-loop-header into the myif branches.
;; This guarantees that when rewriting finishes, each branch has been executed
;; as far as possible.
(defthm run-until-exit-segment-or-hit-loop-header-of-myif-split
  (equal (run-until-exit-segment-or-hit-loop-header segment-stack-height segment-pcs loop-headers (myif test s1 s2))
         (myif test
               (run-until-exit-segment-or-hit-loop-header segment-stack-height segment-pcs loop-headers s1)
               (run-until-exit-segment-or-hit-loop-header segment-stack-height segment-pcs loop-headers s2)))
  :hints (("Goal" :in-theory (enable myif))))
