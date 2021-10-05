; Utilities for processing defun/mutual-recursion forms
;
; Copyright (C) 2015-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "mutual-recursion-forms")

;;;
;;; forms that may be defuns or mutual-recursions
;;;

(defun defun-or-mutual-recursion-formp (event)
  (declare (xargs :guard t))
  (or (defun-formp event)
      (mutual-recursion-formp event)))

;; todo: remove "event" from some of these names (use defining-form?)

(defun get-declares-from-event (fn event)
  (declare (xargs :guard (and (symbolp fn)
                              (defun-or-mutual-recursion-formp event))
                  :guard-hints (("Goal" :in-theory (enable defun-formp
                                                           mutual-recursion-formp)))))
  (let ((event-type (car event)))
    (if (member-eq event-type *defun-types*)
        (get-declares-from-defun event)
      (if (mbt (eq 'mutual-recursion event-type))
          (let ((defun (find-defun-in-mut-rec fn (fargs event))))
            (if (not (defun-formp defun))
                (er hard? 'get-declares-from-event "Failed to find a defun for ~x0 in ~x1." fn event)
              (get-declares-from-event fn defun)))
        (hard-error 'get-declares-from-event "Unknown type of event for ~x0." (acons #\0 fn nil))))))

(defthm all-declarep-of-get-declares-from-event
  (implies (defun-or-mutual-recursion-formp fn-event)
           (all-declarep (get-declares-from-event fn fn-event)))
  :hints (("Goal" :in-theory (enable defun-formp))))

(defun get-xargs-from-event (fn event)
  (declare (xargs :guard (and (symbolp fn)
                              (defun-or-mutual-recursion-formp event))
                  :guard-hints (("Goal" :in-theory (enable defun-formp
                                                           mutual-recursion-formp)))))
  (get-xargs-from-declares (get-declares-from-event fn event)))

;; Returns the *untranslated* body provided for FN in EVENT, which should be a DEFUN or MUTUAL-RECURSION.
;; TODO: Perhaps add support for DEFUNS, which is like MUTUAL-RECURSION.
(defund get-body-from-event (fn event)
  (declare (xargs :guard (and (symbolp fn)
                              (defun-or-mutual-recursion-formp event))
                  :guard-hints (("Goal" :in-theory (enable defun-formp
                                                           mutual-recursion-formp)))))
  (let ((event-type (ffn-symb event)))
    (if (member-eq event-type *defun-types*)
        (get-body-from-defun event)
      (if (eq 'mutual-recursion event-type)
          (let ((defun (find-defun-in-mut-rec fn (fargs event))))
            (if (not (defun-formp defun))
                (er hard? 'get-body-from-event "Failed to find a body for ~x0 in the event ~x1." fn event)
              (get-body-from-event fn defun)))
        (er hard? 'get-body-from-event "Unknown type of event for ~x0." fn)))))

;; This assumes the verify-guard-eagerness is 1 (the usual value).
(defun event-demands-guard-verificationp (event)
  (declare (xargs :guard (defun-or-mutual-recursion-formp event)
                  :guard-hints (("Goal" :in-theory (enable defun-formp
                                                           mutual-recursion-formp)))))
  (if (member-eq (ffn-symb event) *defun-types*)
      (defun-demands-guard-verificationp event)
    ;; it's a mutual-recursion:
    (mutual-recursion-demands-guard-verificationp event)))

(defund ensure-event-demands-guard-verification (event)
  (declare (xargs :guard (defun-or-mutual-recursion-formp event)
                  :guard-hints (("Goal" :in-theory (enable defun-formp
                                                           mutual-recursion-formp)))))
  (if (member-eq (ffn-symb event) *defun-types*)
      (ensure-defun-demands-guard-verification event)
    ;; it's a mutual-recursion:
    (ensure-mutual-recursion-demands-guard-verification event)))
