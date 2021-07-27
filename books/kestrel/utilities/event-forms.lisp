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

(include-book "kestrel/utilities/defun-events" :dir :system)
(include-book "kestrel/utilities/defthm-events" :dir :system)

(defconst *verify-guards-types* '(verify-guards verify-guards$)) ;todo: include verify-guards$ in this book

(defund verify-guards-formp (form)
  (declare (xargs :guard t))
  (and (true-listp form)
       (>= (len form) 2)
       (member-eq (first form) *verify-guards-types*)
       (symbolp (second form))     ;the function name
       ;; what to say about the body?  may contain macros?
       (keyword-value-listp (cdr (cdr form))) ;skip the verify-guards and name
       ))

;; Drops :hints, :otf-flg, and :gaurd-debug from VERIFY-GUARDS.
(defun clean-up-hints-in-verify-guards (verify-guards)
  (declare (xargs :guard (verify-guards-formp verify-guards)
                  :guard-hints (("Goal" :in-theory (enable verify-guards-formp)))))
  (let* ((verify-guards-variant (first verify-guards))
         (name (second verify-guards)))
    `(,verify-guards-variant ,name)))

;; todo: rename, since we are dropping the hints
(defun clean-up-hints-in-defun (defun)
  (declare (xargs :guard (defun-formp defun)
                  :guard-hints (("Goal" :in-theory (enable defun-formp)))))
  (let* ((declares (get-declares-from-defun defun))
         (declares (remove-xarg-in-declares :hints declares))
         (declares (remove-xarg-in-declares :guard-hints declares)))
    (replace-declares-in-defun defun declares)))

;; This also removes :instructions and :otf-flg.
(mutual-recursion
 (defun clean-up-hints-in-event (event)
   (declare (xargs :guard t))
   (if (defun-formp event)
       (clean-up-hints-in-defun event)
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
