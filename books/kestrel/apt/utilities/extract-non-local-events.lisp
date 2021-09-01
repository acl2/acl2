; A utility to filter a list of events
;
; Copyright (C) 2017-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/forms" :dir :system) ;for call-of

(mutual-recursion
 ;; target-types might be '(defun defund)
 (defun extract-non-local-events (target-types event)
   (declare (xargs :guard (or (eq :all target-types)
                              (symbol-listp target-types)))) ;;should not include anything that we handle specially here (e.g., 'encapsulate)
   (cond
    ((and (call-of 'encapsulate event)
          (consp (cdr event)) ; must have the signatures arg
          )
     (extract-non-local-events-list target-types (cdr (rest event)))) ;skip the signatures
    ((and (call-of 'encapsulate-report-errors event)
          (consp (cdr event)) ; must have the ctx arg
          (consp (cddr event)) ; must have the signatures arg
          )
     (extract-non-local-events-list target-types (cddr (rest event)))) ;skip the ctx and signatures
    ((call-of 'progn event)
     (extract-non-local-events-list target-types (rest event)))
    ((call-of 'local event)
     nil) ;skip anything inside a local
    ((call-of 'logic event)  ;(logic) is local to the encapsulate
     nil)
    ((call-of 'program event) ;(program) is local to the encapsulate
     nil)
    ((call-of 'with-output event)
     (extract-non-local-events target-types (car (last event))))
    ((and (call-of 'on-failure event)
          (consp (cdr event)))
     (extract-non-local-events target-types (cadr event)))
    ((and (consp event)
          (or (eq :all target-types)
              (member-eq (car event) target-types)))
     (list event))
    ((and (consp event)
          ;; stuff we know about and can ignore if it's not what we are looking for:
          (member-eq (car event) '(set-inhibit-warnings ;;todo: compare this list to *event-types-not-to-print*
                                   set-ignore-ok
                                   set-irrelevant-formals-ok
                                   defthm
                                   defthmd
                                   defun
                                   defund
                                   table
                                   cw-event   ; maybe will not be needed soon?
                                   print-event ; maybe will not be needed soon?
                                   value-triple
                                   dont-remove-trivial-equivalences ;essentially a call to defattach-system
                                   )))
     nil)
    (t
     ;; If something triggers this, it might need to be treated like progn or encapsulate (see above), but most likely
     ;; it can be added to the list of events just above.  We could call that something like *events-with-no-nested-events*.
     (prog2$ (cw "Note: unexpected thing, ~x0, encountered by extract-non-local-events.  Consider adding support for it.~%" event)
             nil))))

 (defun extract-non-local-events-list (target-types events)
   (declare (xargs :guard (or (eq :all target-types)
                              (symbol-listp target-types))))
   (if (atom events)
       nil
     (append (extract-non-local-events target-types (first events))
             (extract-non-local-events-list target-types (rest events))))))

(defun extract-non-local-defuns (event)
  ;; todo: consider adding other defune variants, such as defun-nx and defund-nx
  (extract-non-local-events '(defun defund) event))

(defun extract-single-non-local-defun (events)
  (let ((defuns (extract-non-local-defuns events)))
    (if (not (eql 1 (len defuns)))
        (er hard? 'extract-single-non-local-defun "Expected a single exported defun, but we got ~x0.~%" defuns)
      (first defuns))))
