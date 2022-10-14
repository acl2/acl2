; Replaying the events in a book (perhaps with changes).
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/file-io-light/read-objects-from-file" :dir :system)
(include-book "kestrel/utilities/submit-events" :dir :system)

;; Prints VAL, rounded to the hundredths place.
;; Returns nil
(defund print-rounded-val (val)
  (let* ((integer-part (floor val 1))
         (fraction-part (- val integer-part))
         (tenths (floor (* fraction-part 10) 1))
         (fraction-part-no-tenths (- fraction-part (/ tenths 10)))
         (hundredths (ceiling (* fraction-part-no-tenths 100) 1)) ; todo: do a proper rounding
         )
    (cw "~c0.~c1~c2" (cons integer-part 10) (cons tenths 1) (cons hundredths 1))))

(defun shorten-event (event)
  (if (not (consp event))
      event
    (case (car event)
      ((defun defund defthm defthmd) (cadr event))
      (local `(local ,(shorten-event (cadr event))))
      (theory-invariant '(theory-invariant <elided>))
      (t event))))

;Returns (mv erp state).
;throws an error if any event fails
; This uses :brief printing.
(defun submit-and-time-events (events print state)
  (declare (xargs :guard (member-eq print '(nil :brief :verbose))
                  :mode :program
                  :stobjs state))
  (if (endp events)
      (mv nil state)
    (let ((event (first events)))
      (mv-let (start-time state)
        (get-real-time state)
        (mv-let (erp state)
          (submit-event-helper-core event print state)
          (if erp
              (prog2$ (cw "ERROR (~x0) with event ~X12." erp event nil)
                      (mv erp state))
            ;; no error:
            (mv-let (end-time state)
              (get-real-time state)
              (let ((time (/ (ceiling (* (- end-time start-time) 100) 1) 100)))
                (progn$ (print-rounded-val time)
                        (cw "s: ~x1~%" time (shorten-event event))
                        (submit-and-time-events (rest events) print state))))))))))

;; Reads and then submits all the events in FILENAME.
;; Returns (mv erp state).
;; Example: (replay-book "helper.lisp" state)
(defun replay-book-fn (bookname ; no extension
                       print state)
  (declare (xargs :guard (and (stringp bookname)
                              (member-eq print '(nil :brief :verbose)))
                  :mode :program ; because this ultimately calls trans-eval-error-triple
                  :stobjs state))
  (mv-let (erp events state)
    (read-objects-from-file (concatenate 'string bookname ".lisp") state)
    (if erp
        (mv erp state)
      (submit-and-time-events events print state))))

(defmacro replay-book (bookname ; no extension
                        &key
                        (print 'nil))
  `(replay-book-fn ,bookname ,print state))
