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
(include-book "kestrel/utilities/split-path" :dir :system)

;; TODO: Exclude theorems not in the testing set!
;; TODO: Don't take credit if the defthms needs no hints?
;; TODO: Try advice on defthms inside encapsulates

;; Example:
;; (replay-book-with-advice "../lists-light" "append")

;; Determines whether the Proof Advice tool can find advice for DEFTHM.  Either way, this also submits the defthm.
;; Returns (mv erp result state) where result is :yes, :no, :maybe, or :trivial.
(defun submit-defthm-event-with-advice (defthm n print server-url state)
  (declare (xargs :mode :program
                  :guard (and (natp n)
                              (acl2::print-levelp print)
                              (or (null server-url)
                                  (stringp server-url)))
                  :stobjs state))
  (b* ((defthm-variant (car defthm))
       (theorem-name (cadr defthm))
       (theorem-body (caddr defthm))
       (rule-classes-result (assoc-keyword :rule-classes (cdddr defthm)))
       (rule-classes (if rule-classes-result
                         (cadr rule-classes-result)
                       ;; means don't put in any :rule-classes arg at all:
                       '(:rewrite)))
       (- (cw "(ADVICE: ~x0: " theorem-name))
       ((mv erp successp best-rec state)
        (help::get-and-try-advice-for-theorem theorem-name
                                              theorem-body
                                              nil ; don't use any hints
                                              nil ; theorem-otf-flg
                                              n ; number of recommendations from ML requested
                                              print
                                              server-url
                                              nil ; debug
                                              100000 ; step-limit
                                              '(:add-hyp) ; disallow :add-hyp, because no hyps are needed for these theorems
                                              nil ; disallowed-rec-sources, todo: allow passing these in
                                              1      ; max-wins
                                              :all   ; model
                                              t ; suppress warning about trivial rec, because below we ask if "original" is the best rec and handle trivial recs there
                                              state))
       ((when erp) (mv erp :no state)))
    (if (not successp)
        (prog2$ (cw "NO).~%") ; close paren matches (ADVICE
                (b* (((mv erp state) (submit-event-helper-core defthm nil state))
                     ((when erp) (mv erp :no state)))
                  (mv nil :no state)))
      (if (eq :add-hyp (help::successful-recommendationp-type best-rec))
          (prog2$ (cw "Maybe: hyp added: ~x0)~%" (help::successful-recommendationp-object best-rec)) ; close paren matches (ADVICE
                  (b* (((mv erp state) (submit-event-helper-core defthm nil state))
                       ((when erp) (mv erp :no state)))
                    (mv nil :maybe state)))
        (b* ((trivialp (equal "original" (help::successful-recommendationp-name best-rec)))
             (- (if trivialp
                    (cw "TRIVIAL (no hints needed))~%") ; close paren matches (ADVICE
                  (progn$ (cw "YES: ")
                          (help::show-successful-recommendation best-rec)
                          (cw ")~%")))) ; close paren matches (ADVICE
             ((mv erp state)
              ;; We submit the event with the hints found by ML, to ensure it works:
              ;; TODO: Instead, have the advice tool check the rec and submit the original event here.
              (submit-event-helper-core (help::successful-rec-to-defthm defthm-variant theorem-name best-rec rule-classes) nil state))
             ((when erp)
              (er hard? 'submit-defthm-event-with-advice "The discovered advice for ~x0 did not work!" theorem-name)
              (mv :advice-didnt-work :no state)))
          (mv nil (if trivialp :trivial :yes) state))))))

;Returns (mv erp yes-count no-count maybe-count trivial-count state).
;throws an error if any event fails
; This uses :brief printing.
(defun submit-events-with-advice (events n print server-url yes-count no-count maybe-count trivial-count state)
  (declare (xargs :guard (and (true-listp events)
                              (natp n)
                              (acl2::print-levelp print)
                              (or (null server-url)
                                  (stringp server-url)))
                  :mode :program
                  :stobjs state))
  (if (endp events)
      (mv nil yes-count no-count maybe-count trivial-count state)
    (let ((event (first events)))
      (if (or (call-of 'defthm event) ; todo: maybe handle thms
              (call-of 'defthmd event))
          (b* (((mv erp result state)
                (submit-defthm-event-with-advice event n print server-url state))
               ((when erp)
                (er hard? 'submit-events-with-advice "ERROR (~x0) with advice attempt for event ~X12.~%" erp event nil)
                (mv erp yes-count no-count maybe-count trivial-count state)))
            (submit-events-with-advice (rest events) n print server-url
                                       (if (eq :yes result) (+ 1 yes-count) yes-count)
                                       (if (eq :no result) (+ 1 no-count) no-count)
                                       (if (eq :maybe result) (+ 1 maybe-count) maybe-count)
                                       (if (eq :trivial result) (+ 1 trivial-count) trivial-count)
                                       state))
        ;; Not something for which we will try advice, so submit it and continue:
        (b* (((mv erp state)
              (submit-event-helper-core event print state))
             ((when erp)
              (er hard? 'submit-events-with-advice "ERROR (~x0) with event ~X12.~%" erp event nil)
              (mv erp yes-count no-count maybe-count trivial-count state))
             (- (cw "~x0~%" (shorten-event event))))
          (submit-events-with-advice (rest events) n print server-url yes-count no-count maybe-count trivial-count state))))))

;; Reads and then submits all the events in FILENAME, trying advice for the theorems.
;; Returns (mv erp event state).
;; Example: (replay-book-with-advice "helper.lisp" state)
(defun replay-book-with-advice-fn (filename ; the book, with .lisp extension
                                   n
                                   print
                                   server-url
                                   state)
  (declare (xargs :guard (and (stringp filename)
                              (natp n)
                              (acl2::print-levelp print)
                              (or (null server-url)
                                  (stringp server-url)))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (b* (((mv dir &) (split-path filename))
       (- (cw "REPLAYING ~s0 with advice:~%~%" filename))
       ;; Read all the forms from the file:
       ((mv erp events state)
        (read-objects-from-book filename state))
       ((when erp) (cw "Error: ~x0.~%" erp) (mv erp nil state))
       ;; Ensure we are working in the same dir as the book:
       ((mv erp & state)
        (set-cbd-fn dir state))
       ((when erp) (mv erp nil state))
       ;; Make margins wider for nicer printing:
       (state (widen-margins state))
       ;; Submit all the events, trying advice for each defthm:
       ((mv erp yes-count no-count maybe-count trivial-count state)
        (submit-events-with-advice events n print server-url 0 0 0 0 state))
       ((when erp)
        (cw "Error: ~x0.~%" erp)
        (mv erp nil state))
       ;; Print stats:
       (- (progn$ (cw "~%SUMMARY for book ~s0:~%" filename)
                  (cw "(Asked each model for ~x0 recommendations.)~%" n)
                  (cw "YES    : ~x0~%" yes-count)
                  (cw "NO     : ~x0~%" no-count)
                  (cw "MAYBE  : ~x0~%" maybe-count)
                  (cw "TRIVIAL: ~x0~%" trivial-count)))
       ;; Undo margin widening:
       (state (unwiden-margins state)))
    ;; No error:
    (mv nil '(value-triple :invisible) state)))

(defmacro replay-book-with-advice (filename ; the book, with .lisp extension
                                   &key
                                   (n '10)
                                   (print 'nil)
                                   (server-url 'nil) ; nil means get from environment var
                                   )
  `(make-event-quiet (replay-book-with-advice-fn ,filename ,n ,print ,server-url state)))
