; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  We exclude GCL, however, since (code-char 300) returns
; nil in a version of GCL circa 2025 or 2026.
; cert_param: (non-gcl)

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

(defun my-pl ()
  (declare (xargs :mode :program))
  (list (code-char 300)))

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(local
 (make-event
  (value `(defconst *c* ',(my-pl)))))
:expected :hard
)

; Commented out by Matt Kaufmann:
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
