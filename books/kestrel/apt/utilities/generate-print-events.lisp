; A utility to assist in printing the results of APT transformations
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "extract-non-local-events")
(include-book "remove-event-types")
(include-book "../../utilities/event-forms") ;for clean-up-hints-in-events
(include-book "../../utilities/wrap-all")

;; Indication of which results of the transformation to print (listed by name, also support :defuns and :defthms).
;;TODO: Simplify this since only t is supported
(defun apt-result-print-specifierp (result-print-specifier)
  (declare (xargs :guard t))
  (or (eq t result-print-specifier) ;print everything
      (and (symbol-listp result-print-specifier)
           ;; todo: check that all keywords are either :defuns or :defthms.  names of events are also allowed
           )));; Returns (mv erp EVENTS state) where EVENTS is a list of print-event events.

;;
;; Filtering events and printing them
;;

(defun filter-events (types names events)
  (declare (xargs :guard (and (symbol-listp types)
                              (symbol-listp names))))
  (if (atom events)
      nil
    (let ((event (first events)))
      (if (and (consp event) ;for guards
               (consp (cdr event)) ;for guards
               (or (member-eq (car event) types)
                   (member-eq (cadr event) names)))
          (cons event (filter-events types names (rest events)))
        (filter-events types names (rest events))))))

(defun get-events-to-print-for-type-or-name (type-or-name events)
  (declare (xargs :guard (symbolp type-or-name)))
  (if (eq type-or-name :defthms)
      (filter-events '(defthm defthmd) nil events)
    (if (eq type-or-name :defuns)
        (filter-events '(defun defund mutual-recursion) nil events)
      (filter-events nil (list type-or-name) events))))

;; Returns (mv erp events-to-print state)
(defun get-events-to-print-for-types-or-names (ctx types-or-names events state)
  (declare (xargs :guard (symbol-listp types-or-names)
                  :stobjs state))
  (if (atom types-or-names)
      (mv nil nil state)
    (let* ((name-or-type (first types-or-names))
           (res (get-events-to-print-for-type-or-name name-or-type events)))
      (if (null res)
          (er-soft+ ctx :bad-input nil "No events to print named ~x0." name-or-type)
        (b* (((er res2)
              (get-events-to-print-for-types-or-names ctx (rest types-or-names) events state)))
          (mv nil (append res res2) state))))))

(defconst *event-types-not-to-print*
  '(set-inhibit-warnings
    set-ignore-ok
    set-irrelevant-formals-ok
    set-bogus-mutual-recursion-ok
    set-default-hints
    set-override-hints
    table ;drop?
    cw-event ; maybe will not be needed soon?
    print-event ; maybe will not be needed soon?
    value-triple
    logic ; e.g., inserted at beginning by simplify-defun-impl
    ))

;;TODO: Simplify this since only t is supported
(defun generate-print-events (ctx result-print-specifier event state)
  (declare (xargs :stobjs state))
  (if (not (apt-result-print-specifierp result-print-specifier))
      ;; TTODO: Improve this message
      (er-soft+ ctx :bad-input nil "The :print option should satisfy apt-result-print-specifierp, but it is ~x0." result-print-specifier)
    (b* ( ;; Elaborate the result-print-specifier argument:
         ;; (result-print-specifier (if (and (symbolp result-print-specifier)
         ;;                                  (not (eq t result-print-specifier))
         ;;                                  (not (eq nil result-print-specifier)))
         ;;                             (list result-print-specifier)
         ;;                           result-print-specifier))
         (events (extract-non-local-events :all event))
         (events (remove-event-types *event-types-not-to-print* events))
         ((er events) (if (eq t result-print-specifier)
                          ;; If result-print-specifier is t, we print all non-local events except those in
                          ;; *event-types-not-to-print*, in the order in which they occur in the
                          ;; encapsulate.
                          (mv nil events state)
                        (get-events-to-print-for-types-or-names ctx result-print-specifier events state)))
         (events (clean-up-hints-in-events events)))
      (mv nil (wrap-all 'print-event events) state))))
