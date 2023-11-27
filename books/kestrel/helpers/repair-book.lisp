; A tool to suggest repairs for broken proofs
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: Minimal working prototype

;(include-book "system/pseudo-good-worldp" :dir :system) ;for pseudo-runep; reduce?
(include-book "kestrel/world-light/defthm-or-defaxiom-symbolp" :dir :system)
(include-book "kestrel/world-light/defined-functionp" :dir :system)
(include-book "kestrel/utilities/submit-events" :dir :system) ; reduce?
(include-book "kestrel/utilities/ld-history" :dir :system)

;dup in books/system/pseudo-good-worldp
(defun pseudo-runep (rune)
  (and (consp rune)
       (keywordp (car rune))
       (consp (cdr rune))
       (symbolp (cadr rune))
       (or (null (cddr rune))
           (natp (cddr rune)))))
(verify-guards pseudo-runep)

;; TODO: Figure out which exact event failed (what if not at top level)?
;; TODO: Actually try the suggestions, and provide new hints for the event.
;; TODO: Try the advice tool!
(defun print-info-on-old-rune (old-rune info-type state)
  (declare (xargs :guard (and (or (eq :major info-type)
                                  (eq :minor info-type)))
                  :verify-guards nil ; todo
                  :stobjs state))
  (if (not (pseudo-runep old-rune))
      (er hard? 'print-info-on-old-runes "Bad old rune: ~x0." old-rune)
    (let ((rule-class (first old-rune))
          (name (second old-rune)) ; todo: consider corollaries (what if they have changed?)
          )
      (if (member-eq rule-class (strip-cars *fake-rune-alist*))
          nil
        (if (eq rule-class :executable-counterpart)
            (if (not (function-symbolp name (w state)))
                (and (eq :major info-type) (cw "Function ~x0 is no longer present!~%" name))
              (if (not (enabled-runep old-rune (ens state) (w state)))
                  (and (eq :major info-type) (cw "Rune ~x0 is no longer enabled!~%" old-rune))
                (and (eq :minor info-type) (cw "(Rune ~x0 did not fire.)~%" old-rune))))
          (prog2$ (if (defthm-or-defaxiom-symbolp name (w state))
                      (if (enabled-runep old-rune (ens state) (w state))
                          (and (eq :minor info-type) (cw "(Rule ~x0 did not fire.)~%" name))
                      ;; todo: of course, a hint might enable the rune!
                        (and (eq :major info-type) (cw "Rule ~x0 did not fire and is disabled. Try enabling!~%" name)))
                    (if (defined-functionp name (w state))
                        (if (enabled-runep old-rune (ens state) (w state))
                            (and (eq :minor info-type) (cw "(Function ~x0 was not opened.)~%" name))
                          (and (eq :major info-type) (cw "function ~x0 did not open and is disabled. Try enabling!~%" name)))
                      (and (eq :major info-type) (cw "Old rule ~x0 is not present!~%" old-rune))))
                  nil))))))

(defun print-info-on-old-runes (old-runes info-type state)
  (declare (xargs :guard (and (true-listp old-runes)
                              (or (eq :major info-type)
                                  (eq :minor info-type)))
                  :verify-guards nil ; todo
                  :stobjs state))
  (if (endp old-runes)
      nil
    (prog2$ (print-info-on-old-rune (first old-runes) info-type state)
            (print-info-on-old-runes (rest old-runes) info-type state))))

(defun print-info-on-new-runes (new-runes info-type state)
  (declare (xargs :guard (and (true-listp new-runes)
                              (or (eq :major info-type)
                                  (eq :minor info-type)))
                  :stobjs state))
  (if (endp new-runes)
      nil
    (let* ((new-rune (first new-runes)))
      (if (not (pseudo-runep new-rune))
          (er hard? 'print-info-on-new-runes "Bad new rune: ~x0." new-rune)
        (let (;(rule-class (first new-rune))
              (name (second new-rune)) ; todo: consider corollaries (what if they have changed?)
              )
          (prog2$ (if (defthm-or-defaxiom-symbolp name (w state))
                      (and (eq :minor info-type) (cw "(Rule ~x0 fired only in the new proof. Try disabling?)~%" name))
                    (if (defined-functionp name (w state))
                        (and (eq :major info-type) (cw "FUNCTION ~x0 OPENED ONLY IN THE NEW PROOF. Try disabling!~%" name))
                      nil))
                  (print-info-on-new-runes (rest new-runes) info-type state)))))))

;todo: add .lisp if needed to book-string
;todo: support :dir arg
;todo: widen margins
(defun repair-book-fn (book-string state)
  (declare (xargs :mode :program
                  :stobjs state))
  ;; Call LD on the book while saving event-data:
  (let* ((state (submit-event-quiet `(saving-event-data (ld ,book-string)) state)) ; todo: make this even quieter
         (most-recent-failed-theorem (acl2::most-recent-failed-command acl2::*theorem-event-types* state)))
    (prog2$
      (cw "~%~%Failure seems to be in ~x0.~%" most-recent-failed-theorem)
      ;; Compute the runes diffs for the failed event:
      (mv-let (erp old-and-new-runes state)
        (runes-diff-fn book-string nil nil nil 'runes-diff
                       state)
        (declare (ignore erp))
        (let ((old-runes (second (assoc-eq :old old-and-new-runes)))
              (new-runes (second (assoc-eq :new old-and-new-runes))))
          (progn$ (cw "~%~%BEST REPAIR SUGGESTIONS:~%") ; todo: figure out which event failed and print its name here?
                  (print-info-on-old-runes old-runes :major state)
                  (print-info-on-new-runes new-runes :major state)
                  (cw "~%Other observations:~%") ; todo: make this shorter, so it doesn't distract from the best suggestions above
                  (print-info-on-old-runes old-runes :minor state)
                  (print-info-on-new-runes new-runes :minor state)
                  (mv nil '(value-triple :invisible) state)))))))

;; This attempts to repair the given book using information in an
;; @event-data.lsp file saved by a previous successful certification (see :doc
;; saving-event-data).  Currently it only prints advice for fixing the first
;; failure in the book.
(defmacro repair-book (book-string)
  `(make-event (repair-book-fn ,book-string state)))

;; Example:
;; (repair-book "expt.lisp")
