; This book (below this paragraph) was produced by Claude and passed along by
; Eric Smith.  It illustrates a soundness bug fixed before ACL2 Version 8.8
; (which however might not have been present in Version 8.7, as noted in a
; comment in (defxdoc note-8-8 ...) in community book
; system/doc/acl2-doc.lisp).

; Finding 40: three :logic-mode functions with raw code and a state formal have no
; (or no dominating) live-state-p test, so their raw body runs on the CONSTANT
; *default-state* -- which is a state-p, and to which ACL2's rewriter applies
; executable-counterparts.  Definition and evaluation then disagree on a ground
; term whose guard is fully satisfied.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

; increment-file-clock: raw returns state unchanged (the clock is the Lisp global
; *file-clock*); the logical body increments (file-clock state).
(must-fail
 (progn
   (defthm eval-says-1
     (equal (file-clock (increment-file-clock *default-state*)) 1)
     :rule-classes nil)
   (defthm logic-says-2
     (equal (file-clock (increment-file-clock *default-state*)) 2)
     :rule-classes nil
     :hints (("Goal" :in-theory (disable (:executable-counterpart increment-file-clock)
                                         (:executable-counterpart file-clock)))))))

; symbol-in-current-package-p: raw calls (find-symbol "CAR" "ACL2") and says T;
; the logic consults the empty known-package-alist of *default-state* and says NIL.
(must-fail
 (progn
   (defthm eval-says-t
     (equal (symbol-in-current-package-p 'car *default-state*) t)
     :rule-classes nil)
   (defthm logic-says-nil
     (equal (symbol-in-current-package-p 'car *default-state*) nil)
     :rule-classes nil
     :hints (("Goal" :in-theory
              (disable (:executable-counterpart symbol-in-current-package-p)))))))
