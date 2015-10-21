; Copyright (C) 2015, Regents of the University of Texas
; Written by Ben Selfridge
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "SB")

(include-book "../sb")
(set-ignore-ok t)

(defconst *dekker-0*
  (list (immov 1 'f0)
        (fence)
        (mrmov 'f1 'rf1)
        (ifz 'rf1 3)
        ;; FAILED TO ENTER CRITICAL SECTION
        ; first set our waiting flag back to 0
        (immov 0 'f0)
        (goto 0)
        ;; CRITICAL SECTION
        (irmov 0 'shared)
        ;; DONE
        ))

(defconst *dekker-1*
  (list (immov 1 'f1)
        (fence)
        (mrmov 'f0 'rf0)
        (ifz 'rf0 3)
        ;; FAILED TO ENTER CRITICAL SECTION
        ; first set our waiting flag back to 0
        (immov 0 'f1)
        (goto 0)
        ;; CRITICAL SECTION
        (irmov 1 'shared)
        ;; DONE
        ))

;; Both programs can't enter their critical section at the same time; however,
;; they could get caught in an infinite deadlock if they both set their
;; ``waiting'' flags simultaneously before testing the other's waiting flags.
;; However, the critical section property only holds on SC. If the writes are
;; buffered and then retrieved by both processors before they are committed to
;; memory, then both can enter the critical section simultaneously.
