; This book, modified by Matt Kaufmann only as noted below (and by the addition
; of this paragraph), was produced by Claude and passed along by Eric Smith.
; It illustrates a soundness bug fixed before ACL2 Version 8.8.  The bug was
; originally fixed by checking make-event expansions with bad-lisp-objectp.
; But a later fix (also made before ACL2 Version 8.8) was to avoid importing
; common-lisp::code-char into the "ACL2" package and defining acl2::code-char
; in raw Lisp so that it causes an error on any bad input (and similarly for
; expt and coerce).  That later fix made the earlier one unnecessary, but for
; technical reasons we have kept it as well; see the call of bad-lisp-objectp
; in ACL2 source function make-event-fn.

; Proof of nil exploiting MAKE-EVENT with :program-mode code.
;
; MAKE-EVENT evaluates its form with :program-mode functions running in raw
; Lisp (not in safe-mode, unlike DEFCONST and macroexpansion).  So the
; expansion can contain non-ACL2 objects such as a character with code 300,
; and ACL2 does not check the expansion for bad Lisp objects.  Evaluation of
; CHAR-CODE on the leaked character then contradicts CHAR-CODE-LINEAR.
;
; The LOCAL wrappers keep the bad object out of the .cert file (whose writer
; would otherwise fail with a Latin-1 encoding error); the exported theorem
; NIL-PROVED has formula NIL.

(in-package "ACL2")

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

(defun my-pl ()
  (declare (xargs :mode :program))
  (list (code-char 300)))

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(local
 (make-event
  (value `(defconst *c* ',(my-pl)))))
)

#|
(local
 (defthm b
   (equal (char-code (car *c*)) 300)
   :rule-classes nil))

(defthm c
  (< (char-code x) 256)
  :rule-classes nil)

(defthm nil-proved
  nil
  :rule-classes nil
  :hints (("Goal" :use (b (:instance c (x (car *c*)))))))
|#
