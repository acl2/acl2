; Utilities for submitting events to ACL2
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Make a version of this that returns soft errors.

(include-book "forms")
(include-book "trans-eval-error-triple")

(defun defthmp (event)
  (declare (xargs :guard t))
  (and (TRUE-LISTP EVENT)
       (<= 3 (len event))
       (KEYWORD-VALUE-LISTP (NTHCDR 3 EVENT))))

(defun defunp (event)
  (declare (xargs :guard t))
  (and (TRUE-LISTP EVENT)
       (<= 4 (len event))
;       (KEYWORD-VALUE-LISTP (NTHCDR 3 EVENT))
       (let* ((declare-presentp (equal 5 (len event)))
              (body (if declare-presentp (fifth event) (fourth event))))
         (pseudo-termp body)))) ;what about macros?

;if the hints are small, just print them!  which hints can be big?  just calls to the clause processor (usually inside computed hints?  print everything else?)
(defun print-defthm-elided (event)
  (declare (xargs :guard (defthmp event)))
  (let* ((command (first event))
         (name (second event))
         (term (third event))
         ;;now printing the rule-classes..
         (keyword-alist (nthcdr 3 event))
         (rule-classes (cadr (assoc-keyword :rule-classes keyword-alist))))
    (cw "(~x0 ~y1 ~y2 :rule-classes ~x3 :hints :elided)~%" command name term rule-classes)))

;print something to indicate that the hints are elided - or print them if they are small?
;fixme generalize the Axe-specific stuff here..
(defun print-defun-elided (event)
;  (declare (xargs :guard (defunp event)))
  (let* ((declare-presentp (equal 5 (len event)))
         (body (if declare-presentp (fifth event) (fourth event))))
    (if (and (call-of 'dag-val-with-axe-evaluator body) ; fixme could just check the size of the whole body, including the sizes of defconsts..
             (quotep (second body))
             (< 1000 (len (unquote (second body))))) ; might ifns also be too big?
        ;;it has a big embedded dag:
        (cw "~x0" `(,(first event)       ;the command (might be defund)
                    ,(second event)      ;the name
                    ,(third event)       ;the args
                    ,@(if declare-presentp (fourth event) nil)
                    :elided-call-to-dag-val-with-axe-evaluator ;could show the alist?
                    ))
      (cw "~x0" event))))

(defun print-event-with-elision (event)
  (let* ((command (car event)))
    (if (eq 'defthm command) ;defthmd?
        (print-defthm-elided event)
      (if (eq 'defun command) ;defund?
          (print-defun-elided event)
        (cw "~x0~%" event)))))

(defun print-events-with-elision (events)
  (if (endp events)
      nil
    (prog2$ (print-event-with-elision (first events))
            (print-events-with-elision (rest events)))))

;Returns (mv erp state) where erp is non-nil if the event failed
;throws an error if the event fails
;TODO: Consider using PSO to print proof output only upon failure.
(defun submit-event-helper (event print throw-errorp state)
  (declare (xargs :mode :program ;; because we call trans-eval-error-triple
                  :guard (member-eq print '(nil :brief :verbose))
                  :stobjs state))
  (progn$ (and print (cw "(Submitting event:~%")) ;todo: it would be nice print the event name (if there is one) or to say "event 3 of 9" or whatever
          (and print
               (if (eq :verbose print)
                   (cw "~x0" event)
                 (print-event-with-elision event)))
          (let ( ;; TODO: Think about this:
                ;; todo: inhibit more output if print is nil?
                (additional-output-types-to-inhibit (if (eq print :verbose)
                                                        nil
                                                      '(event))))
            (mv-let (erp result state)
              ;;this magic incantation comes from :doc with-output:
              (state-global-let*
               ((inhibit-output-lst
                 (union-eq (f-get-global 'inhibit-output-lst state)
                           additional-output-types-to-inhibit)))
               (trans-eval-error-triple event
                                        'submit-event-helper ;todo: pass in a better context
                                        state))
              (if erp
                  (if throw-errorp
                      (prog2$ (er hard? 'submit-event-helper "Failed to submit event: ~X01" event nil)
                              (mv erp state))
                    (prog2$ (and print (cw "EVENT FAILED!)~%"))
                            (mv erp state)))
                ;; Success:
                (prog2$ (and print (cw "~x0)~%" result))
                        (mv nil state)))))))

;returns state
;throws an error if the event fails
(defun submit-event-quiet (event state)
  (declare (xargs :mode :program :stobjs state))
  (mv-let (erp state)
    (submit-event-helper event nil t state)
    (declare (ignore erp))
    state))

;returns state
;throws an error if the event fails
(defun submit-event-verbose (event state)
  (declare (xargs :mode :program :stobjs state))
  (mv-let (erp state)
    (submit-event-helper event :verbose t state)
    (declare (ignore erp))
    state))

;returns state
;throws an error if the event fails
(defun submit-event-brief (event state)
  (declare (xargs :mode :program :stobjs state))
  (mv-let (erp state)
    (submit-event-helper event :brief t state)
    (declare (ignore erp))
    state))

;deprecate?  or improve to take a :print argument (will have to make it a macro) and replace the 3 versions above
;returns state
;throws an error if the event fails
(defun submit-event (event state)
  (declare (xargs :mode :program :stobjs state))
  (submit-event-brief event state))

;returns state
;throws an error if any event fails
(defun submit-events-aux (events print state)
  (declare (xargs :mode :program
                  :guard (member-eq print '(nil :brief :verbose))
                  :stobjs state))
  (if (endp events)
      state
    (let* ((event (first events)))
      (mv-let (erp state)
        (submit-event-helper event print t state)
        (declare (ignore erp))
        (submit-events-aux (rest events) print state)))))

;returns state
;throws an error if any event fails
; This uses :brief printing.
(defun submit-events (events state)
  (declare (xargs :mode :program :stobjs state))
  (let ((more-than-one-eventp (and (consp events) (consp (cdr events)))))
    (progn$ (and more-than-one-eventp (cw "(Submitting ~x0 events:~%" (len events)))
            (let ((state (submit-events-aux events :brief state)))
              (prog2$ (and more-than-one-eventp (cw ")~%"))
                      state)))))

;returns state
(defun submit-events-verbose (events state)
  (declare (xargs :mode :program :stobjs state))
  (let ((more-than-one-eventp (and (consp events) (consp (cdr events)))))
    (progn$ (and more-than-one-eventp (cw "(Submitting ~x0 events:~%" (len events)))
            (let ((state (submit-events-aux events :verbose state)))
              (prog2$ (and more-than-one-eventp (cw ")~%"))
                      state)))))

;returns state
(defun submit-events-quiet (events state)
  (declare (xargs :mode :program :stobjs state))
  (submit-events-aux events nil state))
