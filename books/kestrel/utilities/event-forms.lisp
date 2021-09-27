; Utilities dealing with recognizing and manipulating event forms
;
; Copyright (C) 2014-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

(include-book "defun-forms")
(include-book "verify-guards-forms")
(include-book "defthm-forms")
(include-book "kestrel/event-macros/cw-event" :dir :system)

;; Drops :hints, :otf-flg, :guard-debug, and :guard-simplify from VERIFY-GUARDS.
(defun clean-up-hints-in-verify-guards (verify-guards)
  (declare (xargs :guard (verify-guards-formp verify-guards)
                  :guard-hints (("Goal" :in-theory (enable verify-guards-formp)))))
  (let* ((verify-guards-variant (first verify-guards))
         (name (second verify-guards)))
    `(,verify-guards-variant ,name)))

;; This also removes :instructions and :otf-flg.
(mutual-recursion
 (defun clean-up-hints-in-event (event)
   (declare (xargs :guard t))
   (if (defun-formp event)
       (remove-hints-from-defun event)
     (if (defthm-formp event)
         (clean-up-defthm event)
       (if (verify-guards-formp event)
           (clean-up-hints-in-verify-guards event)
         (if (and (consp event)
                  (eq 'mutual-recursion (car event)))
             `(,(car event) ,@(clean-up-hints-in-events (cdr event)))
           (if (and (consp event)
                    (eq 'make-flag (car event)))
               event ;todo: remove this case eventually (but transformations are exporting the make-flags)
             (if (and (consp event) ;todo: remove this case eventually
                      (consp (cdr event))
                      (eq 'skip-proofs (car event)))
                 `(skip-proofs ,(clean-up-hints-in-event (cadr event)))
               event ;(er hard? 'clean-up-hints-in-events "Unexpected event: ~x0." event) ;tod: put this back, but defthm-flag-XXX is showing up.  change the xforms to not export those
               )))))))

 (defun clean-up-hints-in-events (events)
   (declare (xargs :guard t))
   (if (atom events)
       nil
     (cons (clean-up-hints-in-event (first events))
           (clean-up-hints-in-events (rest events))))))

;; Print an event, after quoting it, followed by a possible newline (to ensure
;; that the next thing printed starts at the margin)."
(defmacro print-event (event)
  `(cw-event "~x0~|" ',event))
