; A utility to get the (untranslated) event that introduced a function
;
; Copyright (C) 2015-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;; A tool to get the event (the defun, or defthm, or mutual-recursion, etc.)
;; corresponding to a given name, in untranslated form.  This works better than
;; the built-in utility get-event (e.g., on built-in functions introduced in
;; :program mode and later lifted to :logic mode, such as all-vars1).

;; See tests in my-get-event-tests.lisp.

;; TODO: If a function was introduced in :program mode and later lifted to
;; :logic mode, the result of my-get-event may contain :mode :program in the
;; xargs.  We could consider removing this.

;; TODO: We could consider changing DEFUNS to MUTUAL-RECURSION in the result,
;; but functions defined with DEFUNS seem rare.

;; TDOO: Consider using get-defun-event, which works for :program mode
;; functions too (but check that the :verify-guards xarg is right).

(include-book "std/util/bstar" :dir :system) ; todo: drop this

;; Similar to get-event-tuple in books/std/util/defredundant.lisp but without
;; some cruft that brings in dependencies.
(defun get-event-tuple2 (name world)
  (declare (xargs :mode :program))
  (b* ((ev-world (decode-logical-name name world))
       ((unless (consp ev-world))
        (er hard 'get-event-tuple2 "Not a logical name: ~x0." name))
       (landmark (car ev-world))
       ((unless (and (consp landmark)
                     (eq (first landmark) 'acl2::event-landmark)
                     (eq (second landmark) 'acl2::global-value)))
        (er hard 'get-event-tuple2 "Expected (EVENT-LANDMARK GLOBAL-VALUE . <event-tuple>) but found ~x0."
            landmark))
       (tuple (cddr landmark))
       (form (access-event-tuple-form tuple)))
    (cond ((and (consp form)
                (eq (car form) 'acl2::verify-termination-boot-strap))
; Check added by Matt K.  (Without it, the check below involving
;   (get-event-tuple 'binary-append world)
; was failing after a 3/20/2015 modification to ACL2 source file axioms.lisp.
           (get-event-tuple2 name (acl2::scan-to-event (cdr ev-world))))
          (t tuple))))

;; todo: add more kinds of events?
(defun my-get-event (name wrld)
  (declare (xargs :mode :program))
  (let ((event (access-event-tuple-form (get-event-tuple2 name wrld))))
    (if (not (member-eq (car event)
                        '(defun mutual-recursion defaxiom defthm defstobj defabsstobj
                                defuns ;todo: handle
                                encapsulate ;todo: handle?
                                deftheory
                                defmacro)))
        (er hard 'my-get-event "Unxpected kind of event for ~x0: ~x1" name event)
      event)))
