; Utilities dealing with redundant events
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; To record an event, we add an entry to a table whose name is derived from
;; the kind of the event.  Later, to check whether the event is redundant, we
;; consult the table.

(defund redundancy-table-name (command-name)
  (declare (xargs :guard (symbolp command-name)))
  (add-suffix command-name "-TABLE"))

;; WHOLE-FORM is a call of the command, e.g, (prove-equal-with-axe ...)
(defund command-is-redundantp (whole-form state)
  (declare (xargs :guard (and (consp whole-form)
                              (symbolp (car whole-form)))
                  :stobjs state))
  (let* ((command-name (car whole-form))
         (table-name (redundancy-table-name command-name))
         (table-alist (table-alist table-name (w state))))
    (if (not (alistp table-alist))
        (er hard? 'command-is-redundantp "The table ~x0 is ill-formed.  Table-alist failed to return an alist, instead giving ~x1."
            table-name
            table-alist)
      ;; the match must be exact (no attempt to detect equivalent commands):
      (if (assoc-equal whole-form table-alist)
          (prog2$ (let ((args (fargs whole-form)))
                    (if (and (consp args)
                             (atom (first args)))
                        ;; prints the first arg too if it is an atom:
                        (cw "NOTE: The command (~x0 ~x1 ...) is redundant.~%" command-name (first args))
                      (cw "NOTE: The command (~x0 ...) is redundant.~%" command-name)))
                  t)
        nil))))

;; Returns an event which, when submitted, records the fact that WHOLE-FORM has
;; been submitted and produced RESULT.
(defund redundancy-table-event (whole-form result)
  (declare (xargs :guard (and (consp whole-form)
                              (symbolp (car whole-form)))))
  (let* ((command-name (car whole-form))
         (table-name (redundancy-table-name command-name)))
    ;; Avoids printing the whole result, since it might be large (e.g., the
    ;; result of lifting code into logic):
    `(with-output :off :all (table ,table-name ',whole-form ',result))))
