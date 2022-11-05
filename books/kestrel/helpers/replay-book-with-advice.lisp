; A tool to try proof advice on each defthm in a book
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "replay-book")
(include-book "advice")

;; TODO: Exclude theorems not in the testing set!
;; TODO: Don't take credit if the defthms needs no hints?
;; TODO: Try advice on defthms inside encapsulates

;; Example:
;; (replay-book-with-advice "../lists-light" "append")

;; Determines whether the Proof Advice tool can find advice for DEFTHM.  Either way, this also submits the defthm.
;; Returns (mv erp result state) where result is :yes, :no, or: maybe.
(defun submit-defthm-event-with-advice (defthm n print state)
  (declare (xargs :mode :program
                  :guard (and (natp n)
                              (acl2::print-levelp print))
                  :stobjs state))
  (b* ((defthm-variant (car defthm))
       (theorem-name (cadr defthm))
       (theorem-body (caddr defthm))
       (rule-classes-result (assoc-keyword :rule-classes (cdddr defthm)))
       (rule-classes (if rule-classes-result
                         (cadr rule-classes-result)
                       ;; means don't put in any :rule-classes arg at all:
                       '(:rewrite)))
       ((mv erp successp best-rec state)
        (help::get-and-try-advice-for-theorem theorem-name
                                              theorem-body
                                              nil ; don't use any hints
                                              nil ; theorem-otf-flg
                                              n ; number of recommendations from ML requested
                                              print
                                              nil ; server-url (get from environment var)
                                              nil ; debug
                                              100000 ; step-limit
                                              1      ; max-wins
                                              :all   ; model
                                              state))
       ((when erp) (mv erp :no state)))
    (if (not successp)
        (prog2$ (cw "ADVICE: NO for ~x0).~%" theorem-name)
                (b* (((mv erp state) (submit-event-helper-core defthm nil state))
                     ((when erp) (mv erp :no state)))
                  (mv nil :no state)))
      (if (eq :add-hyp (help::successful-recommendationp-type best-rec))
          (prog2$ (cw "ADVICE: ADD-HYP recommendation for ~x0 but submitting original version.~%" theorem-name)
                  (b* (((mv erp state) (submit-event-helper-core defthm nil state))
                       ((when erp) (mv erp :no state)))
                    (mv nil :maybe state)))
        (b* ((- (progn$ (cw "ADVICE: YES for ~x0: " theorem-name)
                        (help::show-successful-recommendation best-rec)
                        (cw ".~%")))
             ((mv erp state)
              ;; We submit the event with the hints found by ML, to ensure it works:
              ;; TODO: Instead, have th advice tool check the req and submit the original event here.
              (submit-event-helper-core (help::successful-rec-to-defthm defthm-variant theorem-name best-rec rule-classes) nil state))
             ((when erp)
              (er hard? 'submit-defthm-event-with-advice "The discovered advice for ~x0 did not work!" theorem-name)
              (mv :advice-didnt-work :no state)))
          (mv nil :yes state))))))

;Returns (mv erp yes-count no-count maybe-count state).
;throws an error if any event fails
; This uses :brief printing.
(defun submit-events-with-advice (events n print yes-count no-count maybe-count state)
  (declare (xargs :guard (and (true-listp events)
                              (acl2::print-levelp print)
                              (natp n))
                  :mode :program
                  :stobjs state))
  (if (endp events)
      (mv nil yes-count no-count maybe-count state)
    (let ((event (first events)))
      (if (or (call-of 'defthm event) ; todo: maybe handle thms
              (call-of 'defthmd event))
          (b* (((mv erp result state)
                (submit-defthm-event-with-advice event n print state))
               ((when erp)
                (er hard? 'submit-events-with-advice "ERROR (~x0) with advice attempt for event ~X12.~%" erp event nil)
                (mv erp yes-count no-count maybe-count state)))
            (submit-events-with-advice (rest events) n print
                                       (if (eq :yes result) (+ 1 yes-count) yes-count)
                                       (if (eq :no result) (+ 1 no-count) no-count)
                                       (if (eq :maybe result) (+ 1 maybe-count) maybe-count)
                                       state))
        ;; Not something for which we will try advice, so submit it and continue:
        (b* (((mv erp state)
              (submit-event-helper-core event print state))
             ((when erp)
              (er hard? 'submit-events-with-advice "ERROR (~x0) with event ~X12.~%" erp event nil)
              (mv erp yes-count no-count maybe-count state))
             (- (cw "~x0~%" (shorten-event event))))
          (submit-events-with-advice (rest events) n print yes-count no-count maybe-count state))))))

;; Reads and then submits all the events in FILENAME, trying advice for the theorems.
;; Returns (mv erp state).
;; Example: (replay-book-with-advice "helper.lisp" state)
(defun replay-book-with-advice-fn (dir      ; no trailing slash
                                   bookname ; no extension
                                   n
                                   print state)
  (declare (xargs :guard (and (stringp dir)
                              (stringp bookname)
                              (natp n)
                              (acl2::print-levelp print))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (b* ( ;; Read all the forms from the file:
       ((mv erp events state)
        (read-objects-from-file (concatenate 'string dir "/" bookname ".lisp") state))
       ((when erp) (mv erp state))
       ;; Ensure we are working in the same dir as the book:
       ((mv erp & state)
        (set-cbd-fn dir state))
       ((when erp) (mv erp state))
       ;; Make margins wider for nicer printing:
       (state (widen-margins state))
       ;; Submit all the events, trying advice for each defthm:
       ((mv erp yes-count no-count maybe-count state)
        (submit-events-with-advice events n print 0 0 0 state))
       ((when erp) (mv erp state))
       ;; Print stats:
       (- (progn$ (cw "Stats for book ~s1/~s2:~%" dir bookname)
                  (cw "(Used n=~x0.)" n)
                  (cw "YES  : ~x0~%" yes-count)
                  (cw "NO   : ~x0~%" no-count)
                  (cw "MAYBE: ~x0~%" maybe-count)))
       ;; Undo margin widening:
       (state (unwiden-margins state)))
    ;; No error:
    (mv nil state)))

(defmacro replay-book-with-advice (dir ; no trailing slash
                                   bookname ; no extension
                                   &key
                                   (n '10)
                                   (print 'nil))
  `(replay-book-with-advice-fn ,dir ,bookname ,n ,print state))
