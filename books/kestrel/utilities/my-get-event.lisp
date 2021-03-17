; A utility to get the (untranslated) event that introduced a function
;
; Copyright (C) 2015-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;; A tool to get the event (defun or mutual-recursion or defuns) corresponding
;; to a given name, in untranslated form.  This works better than the built-in
;; utility get-event (e.g., on built-in functions introduced in :program mode
;; and later lifted to :logic mode).

(include-book "std/util/bstar" :dir :system) ;could drop even this

;; ;dup in axe
;; (DEFUN CONS-ONTO-ALL (ITEM LSTS)
;;   (IF (ENDP LSTS)
;;       NIL
;;       (CONS (CONS ITEM (CAR LSTS))
;;             (CONS-ONTO-ALL ITEM (CDR LSTS)))))

;; ;like get-event but turns a defuns into a mutual recursion (TODO: think about this more)
;; ;; get-event doesn't work too well when the function was originally introduced in program mode and later lifted to logic mode.
;; ;;TODO: this should also remove program mode from all the xargs?
;; (defun my-get-event (name wrld)
;;   (declare (xargs :mode :program))
;;   (let ((event (get-event name wrld)))
;;     (if (eq 'defuns (ffn-symb event))
;;         `(mutual-recursion ,@(cons-onto-all 'defun (fargs event)))
;;       event)))

;; Similar to get-event-tuple in books/std/util/defredundant.lisp but without
;; some cruft that brings in dependencies.
(defun get-event-tuple2 (name world)
  (declare (xargs :mode :program))
  (b* ((ev-world (acl2::decode-logical-name name world))
       ((unless (consp ev-world))
        (er hard 'get-event-tuple2 "Not a logical name: ~x0." name))
       (landmark (car ev-world))
       ((unless (and (consp landmark)
                     (eq (first landmark) 'acl2::event-landmark)
                     (eq (second landmark) 'acl2::global-value)))
        (er hard 'get-event-tuple2 "Expected (EVENT-LANDMARK GLOBAL-VALUE . <event-tuple>) but found ~x0."
            landmark))
       (tuple (cddr landmark))
       (form (acl2::access-event-tuple-form tuple)))
    (cond ((and (consp form)
                (eq (car form) 'acl2::verify-termination-boot-strap))
; Check added by Matt K.  (Without it, the check below involving
;   (get-event-tuple 'binary-append world)
; was failing after a 3/20/2015 modification to ACL2 source file axioms.lisp.
           (get-event-tuple2 name (acl2::scan-to-event (cdr ev-world))))
          (t tuple))))

;; TODO: Is there still an issue with a 'defuns' event (need to
;; change to a mutual-recursion?)  TODO: Perhaps this should remove the :mode
;; :program xargs for defuns / mutual-recursions that have been lifted to logic
;; mode.
(defun my-get-event (name wrld)
  (declare (xargs :mode :program))
  (let ((event (access-event-tuple-form (get-event-tuple2 name wrld))))
    (if (not (member-eq (car event)
                        '(defun mutual-recursion defaxiom defthm defstobj defabsstobj
                                defuns ;todo: handle
                                encapsulate ;todo: handle?
                                )))
        (er hard 'my-get-event "Unxpected kind of event for ~x0: ~x1" name event)
      event)))
