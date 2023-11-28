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

(include-book "std/util/bstar" :dir :system)
(include-book "replay-book-helpers")
;(include-book "system/pseudo-good-worldp" :dir :system) ;for pseudo-runep; reduce?
(include-book "kestrel/world-light/defthm-or-defaxiom-symbolp" :dir :system)
(include-book "kestrel/world-light/defined-functionp" :dir :system)
(include-book "kestrel/utilities/submit-events" :dir :system) ; reduce?
(include-book "kestrel/utilities/ld-history" :dir :system)
(include-book "kestrel/utilities/maybe-add-dot-lisp-extension" :dir :system)
(include-book "kestrel/utilities/make-event-quiet" :dir :system)

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
                        ;; todo: of course, a hint might enable the rune!  check for that
                        (and (eq :major info-type) (cw "Enable ~x0 (disabled now but fired before)~%" name)))
                    (if (defined-functionp name (w state))
                        (if (enabled-runep old-rune (ens state) (w state))
                            (and (eq :minor info-type) (cw "(Function ~x0 was not opened.)~%" name))
                          (and (eq :major info-type) (cw "Function ~x0 did not open and is disabled. Try enabling!~%" name)))
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
        (let ((rule-class (first new-rune))
              (name (second new-rune)) ; todo: consider corollaries (what if they have changed?)
              )
          (prog2$ (if (defthm-or-defaxiom-symbolp name (w state))
                      (and (eq :minor info-type) (cw "(Rule ~x0 fired only in the new proof. Try disabling?)~%" name))
                    (if (defined-functionp name (w state))
                        (if (eq :definition rule-class)
                            (and (eq :major info-type) (cw "Function ~x0 opened only in the new proof. Try disabling!~%" name))
                          (if (eq :type-prescription rule-class)
                              (and (eq :minor info-type) (cw "Function ~x0's :type-prescription rule fires opened only in the new proof. Try disabling.~%" name))
                            nil ; todo: think about this
                            ))
                      ;; todo: what else could it be?
                      nil))
                  (print-info-on-new-runes (rest new-runes) info-type state)))))))

(defun consume-event-data-forms (names event-data-forms)
  (if (endp names)
      (if (not (endp event-data-forms))
          event-data-forms
        nil)
    (let ((name (first names)))
      (if (not (and (consp event-data-forms) (eq name (car (first event-data-forms)))))
          (er hard? 'consume-event-data-forms "Bad event-data forms (expected one for ~x0): ~x1." name event-data-forms)
        (consume-event-data-forms (rest names) (rest event-data-forms))))))

;; TODO: If event-data gets out of sync, look for any event data for the given name (perhaps count occurrences of each name as we go?)
;; Returns (mv erp state).
(defun repair-events-with-event-data (events event-data-forms state)
  (declare (xargs :guard (and (true-listp events)
                              (true-listp event-data-forms))
                  :stobjs state
                  :mode :program))
  (if (endp events)
      (if (consp event-data-forms)
          (prog2$ (cw "Warning: Extra event-data forms: ~x0." event-data-forms)
                  (mv :extra-event-forms state))
        (progn$ (cw "Done repairing book.~%") ; todo: print warning if no failure found
                (mv nil state)))
    (b* ((event (first events))
         ;; Clear event-data:
         (state (f-put-global 'event-data-fal nil state))
         ;; Submit the event, saving event-data:
         ((mv erp state) (submit-event-core `(saving-event-data ,event) nil state)) ; todo: make this even quieter
         (new-event-data-fal (f-get-global 'event-data-fal state)) ; a fast alist whose final cdr is event-data-fal
         )
      (if erp
          ;; this event failed!
          (b* ((- (cw "Failed Event: ~x0~%" event)) ; print better
               ((when (not (and (consp event) (member-eq (car event) '(defthm defthmd))))) ; todo
                (cw "Error: Can only repair defthms.~%")
                (mv t state))
               (event-data-form (first event-data-forms))
               (name (cadr event)) ;todo gen
               ((when (not (and (consp event-data-forms) (eq name (car event-data-form)))))
                (cw "Error: No event data for ~x0." name)
                (mv t state))
               (this-event-data (car (cdr (hons-get name new-event-data-fal))))
               (old-event-data (cdr event-data-form))
               ;; (- (cw "New event data: ~x0.~%" this-event-data))
               ;; (- (cw "Old event data: ~x0.~%" old-event-data))
               (new-runes (get-event-data-1 'rules this-event-data))
               (old-runes (get-event-data-1 'rules old-event-data))
               (new-only-runes (set-difference-equal new-runes old-runes))
               (old-only-runes (set-difference-equal old-runes new-runes))
               (- (progn$ (cw "~%~%BEST REPAIR SUGGESTIONS:~%~%") ; todo: figure out which event failed and print its name here?
                          (print-info-on-old-runes old-only-runes :major state)
                          (print-info-on-new-runes new-only-runes :major state)
                          (cw "~%Other observations:~%") ; todo: make this shorter, so it doesn't distract from the best suggestions above
                          (print-info-on-old-runes old-only-runes :minor state)
                          (print-info-on-new-runes new-only-runes :minor state)))
               (event-data-forms (consume-event-data-forms (list name) event-data-forms)))
            (repair-events-with-event-data (rest events) event-data-forms state))
        (b* ((names-with-event-data (strip-cars (true-list-fix new-event-data-fal)))
             (event-data-forms (consume-event-data-forms names-with-event-data event-data-forms)))
          (repair-events-with-event-data (rest events) event-data-forms state))))))

;todo: support :dir arg?
;todo: widen margins
;; Returns (mv erp result state).
(defun repair-book-fn (book-path state)
  (declare (xargs :mode :program
                  :stobjs state))
  ;; Call LD on the book while saving event-data:
  (b* (;; Add .lisp extension:
       (book-path (maybe-add-dot-lisp-extension book-path))
       ;; Check that the book exists:
       ((mv book-existsp state) (file-existsp book-path state))
       ((when (not book-existsp))
        (er hard? 'repair-book-fn "The book ~x0 does not exist." book-path)
        (mv :book-does-not-exist nil state))
       ;; Start repairing
       (- (cw "~%~%*** REPAIRING ~s0 ***~%~%" book-path))
       ;; Load the .port file (may be help resolve #. constants [and packages?] in read-objects-from-book):
       (state (load-port-file-if-exists (remove-lisp-suffix book-path t) state))
       ;; Read all the forms in the book:
       ((mv erp events state)
        (read-objects-from-book book-path state))
       ((when erp) (cw "Error: ~x0.~%" erp) (mv erp nil state))
       ;; (- (cw "Book contains ~x0 forms.~%" (len events)))
       ;; Read the saved event data:
       (event-data-file-path (concatenate 'string (remove-lisp-suffix book-path t) "@event-data.lsp"))
       ((mv erp event-data-forms state) (read-objects-from-file-with-pkg event-data-file-path "ACL2" state))
       ((when erp) (cw "Error (~x0) reading: ~x1.~%" erp event-data-file-path) (mv erp nil state))
       ;; (- (cw "Saved event data contains ~x0 forms.~%" (len event-data-forms)))
       ;; Walk through the book events and that file in sync
       ((mv erp state) (repair-events-with-event-data events event-data-forms state))
       ((when erp) (mv erp nil state))
       ;; ;; todo: this still print stuff:
       ;; (state (submit-event-quiet `(saving-event-data (ld ,book-path)) state)) ; todo: make this even quieter
       ;; (most-recent-failed-theorem (acl2::most-recent-failed-command acl2::*theorem-event-types* state))
       )
    (mv nil '(value-triple :invisible) state)
    ;; (prog2$
    ;;   (cw "~%~%Failure seems to be in ~x0.~%" most-recent-failed-theorem)
    ;;   ;; Compute the runes diffs for the failed event:
    ;;   (mv-let (erp old-and-new-runes state)
    ;;     (runes-diff-fn book-path nil nil nil 'runes-diff
    ;;                    state)
    ;;     (declare (ignore erp))
    ;;     (let ((old-runes (second (assoc-eq :old old-and-new-runes)))
    ;;           (new-runes (second (assoc-eq :new old-and-new-runes))))
    ;;       (progn$ (cw "~%~%BEST REPAIR SUGGESTIONS:~%") ; todo: figure out which event failed and print its name here?
    ;;               (print-info-on-old-runes old-runes :major state)
    ;;               (print-info-on-new-runes new-runes :major state)
    ;;               (cw "~%Other observations:~%") ; todo: make this shorter, so it doesn't distract from the best suggestions above
    ;;               (print-info-on-old-runes old-runes :minor state)
    ;;               (print-info-on-new-runes new-runes :minor state)
    ;;               (mv nil '(value-triple :invisible) state)))))
    ))

;; This attempts to repair the given book using information in an
;; @event-data.lsp file saved by a previous successful certification (see :doc
;; saving-event-data).
;; Example: (repair-book "../lists-light/append").
(defmacro repair-book (book-path)
  `(make-event-quiet (repair-book-fn ,book-path state)))

;; Example:
;; (repair-book "expt.lisp")
