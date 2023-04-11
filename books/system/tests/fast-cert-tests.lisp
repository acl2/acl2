; Copyright (C) 2023, ForrestHunt, Inc.
; Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See also fast-cert-tests.acl2, which contains tests pertaining to fast-cert
; mode for events executed at the top level.  The events below are to be
; executed during certify-book.

(in-package "ACL2")

;;;;;;;;;;
;;; Test 0: Redundant defun
;;;;;;;;;;

(local (defun f0 (x) x))

; Local events do not extend the top-level-cltl-command-stack (called "the
; stack" in comments below).
(extend-stack nil)

(defun f0 (x) x)

; Even though the non-local defun just above is redundant on the first pass of
; certify-book, it will not be redundant when including the book.  So it is
; accounted for by extending the stack.
(extend-stack
 ((DEFUNS :LOGIC NIL (F0 (X) X))))

;;;;;;;;;;
;;; Test 1: Redundant encapsulate containing non-local redundant defun
;;;;;;;;;;

; Let's first review what happens when fast-cert mode is not active (i.e., what
; happens by default).  At the top level (hence in forming a porcullis), the
; encapsulate below would be empty; it adds no event.  But inside a book being
; certified, the include-book pass will see only the second defun of f1.  So:
; if the events above are in the portcullis, then including the book will not
; define f1, but if they are in the book itself, then including the book will
; define f1.

; Our scheme preserves these properties.  In the portcullis, i.e., at the top
; level, the second defun of f1 will cause the top-level-cltl-command-stack to
; be extended for f, but at the conclusion of the encapsulate that extension
; will be discarded.  But when the forms are in the book itself, there are two
; cases.  If fast-cert is not active, then the world will be rolled back to
; before the encapsulate, so the defun of f1 there will not be redundant.  If
; fast-cert is active, then during certification's only pass the
; top-level-cltl-command-stack will be extended for the redundant defun of f1.
; Either way, f1 will be represented, as it should be, in the
; top-level-cltl-command-stack.

(local (defun f1 (x) x))

(encapsulate
  ()
  (defun f1 (x) x)
  (local (defun f2 (x) x)))

; Unlike the corresponding Test 1 events in fast-cert-tests.acl2, here we know
; that f1 will be defined during include-book, so we must account for it on the
; stack.
(extend-stack
 ((DEFUNS :LOGIC NIL (F1 (X) X))))

;;;;;;;;;;
;;; Test 2: Encapsulate redundant with encapsulate
;;;;;;;;;;

(local
 (encapsulate
   ()
   (defun f3 (x) x)))

(encapsulate
  ()
  (defun f3 (x) x))

; The stack is extended, because f3 will be defined when including the book.
(extend-stack
 ((DEFUNS :LOGIC NIL (F3 (X) X))))

;;;;;;;;;;
;;; Test 3: Non-local defun redundant with local and non-local defuns
;;;;;;;;;;

; Just for fun, let's make the redundant definition be program-mode.  Since
; it's local, it doesn't extend top-level-cltl-command-stack.
(local (defun f3 (x)
         (declare (xargs :mode :program))
         x))

(extend-stack nil)

; If it's non-local, then it does extend the stack; but we will be compressing
; the stack at the of certify-book.
(defun f3 (x)
  (declare (xargs :mode :program))
  x)

(extend-stack
 ((DEFUNS :PROGRAM NIL (F3 (X)
                           (DECLARE (XARGS :MODE :PROGRAM))
                           X))))

;;;;;;;;;;
;;; Test 3: Event local to portcullis but non-local in book
;;;;;;;;;;

; H was defined locally in fast-cert-tests.acl2.
(defun h (x) x)

(extend-stack
 ((DEFUNS :LOGIC NIL (H (X) X))))

;;;;;;;;;;
;;; Test 4: Redundancy with earlier progn
;;;;;;;;;;

(progn
  (defun f4 (x) x)
  (local (defun f5 (x) x)))

; The stack is extended for f4 but not f5: only non-local definiitons extend
; the stack.
(extend-stack
 ((DEFUNS :LOGIC NIL (F4 (X) X))))

; Unlike the corresponding test in fast-cert-tests.acl2, this time the
; following event adds the defun of f5 to the stack.  That's necessary because
; when including the book, f5 will be defined.

(progn
  (defun f4 (x) x)
  (defun f5 (x) x))

(extend-stack
 ((DEFUNS :LOGIC NIL (F5 (X) X))))

; This is handled similarly to the preceding event.  Thus, the defun of f5 is
; added again to the stack; but it will ultimately be eliminated by
; compressing the stack near the end of certify-book.
(encapsulate
  ()
  (defun f4 (x) x)
  (defun f5 (x) x))

(extend-stack
 ((DEFUNS :LOGIC NIL (F5 (X) X))))

; Excess stack elements are removed by compressing the stack (as is done near
; the end of certify-book).
(assert-event
 (equal (compress-cltl-command-stack
         (global-val 'top-level-cltl-command-stack (w state)))
        (append '((DEFUNS :LOGIC NIL (F5 (X) X))
                  (DEFUNS :LOGIC NIL (F4 (X) X))
                  (DEFUNS :LOGIC NIL (H (X) X))
                  (DEFUNS :LOGIC NIL (F3 (X) X))
                  (DEFUNS :LOGIC NIL (F1 (X) X))
                  (DEFUNS :LOGIC NIL (F0 (X) X)))
                (port-cltl-command-stack :compressed))))

;;;;;;;;;;
;;; Test 5: Redundancy of progn with defun
;;;;;;;;;;

; No surprises here -- the version of Test 5 in fast-cert-tests.acl2 is more
; interesting.

(local (defun f6 (x) x))

(progn
  (defun f7 (x) x)
  (defun f6 (x) x))

(extend-stack
 ((DEFUNS :LOGIC NIL (F6 (X) X))
  (DEFUNS :LOGIC NIL (F7 (X) X))))

;;;;;;;;;;
;;; Test 6: Handling of defun-mode
;;;;;;;;;;

; This example illustrates handling of the defun-mode of a defun.  It shows
; that when a non-local program-mode defun is redundant with a local logic-mode
; defun, the old cltl-cmd (which is not on the stack, because the defun was
; local) is be changed so that its cadr is :program instead of logic.

(local (defun f8 (x) x)) ; :logic mode
(defun f8 (x) (declare (xargs :mode :program)) x) ; :program mode
(defun f8 (x) x) ; :logic mode

; Extend the stack with the non-redundant definitions (see preceding comment).
(extend-stack
 ((DEFUNS :LOGIC NIL (F8 (X) X))
  (DEFUNS :PROGRAM NIL (F8 (X) (DECLARE (XARGS :MODE :PROGRAM)) X))))

; The following variant, which involves verify-termination, would work
; out the same way.

(local (defun f9 (x) (declare (xargs :mode :program)) x))
(local (verify-termination f9))
(defun f9 (x) (declare (xargs :mode :program)) x)
(defun f9 (x) (declare (xargs :mode :logic)) x)

(value-triple (global-val 'top-level-cltl-command-stack (w state)))

(extend-stack
 ((DEFUNS :LOGIC NIL (F9 (X) (DECLARE (XARGS :MODE :LOGIC)) X))
  (DEFUNS :PROGRAM NIL (F9 (X) (DECLARE (XARGS :MODE :PROGRAM)) X))))

; This also works out the same way if the final defun is replaced by
; (verify-termination f9), since that's a macro generating a make-event whose
; expansion is exactly the final defun above.
