; [Jared]: I moved assert.lisp and eval.lisp from make-event/ to misc/.  But,
; for compatibility I'm leaving this stupid book here that just includes it out
; of misc.  Normally I think these kinds of compatibility wrappers are a bad
; idea, but perhaps these books are widely used enough to warrant some extra
; care.

; Why do this at all?  It appears that for several other directories, including
; at least hints, security, defsort, str, cutil, and misc/misc2, moving just
; the assert.lisp and eval.lisp books into misc/ is sufficient to eliminate the
; dependency on the make-event directory.  This seems like a good win because
; the make-event directory has some pretty significant dependencies due to the
; proof-by-arith book.

(in-package "ACL2")
(include-book "misc/assert" :dir :system)


