; Replaying the events in a book
;
; Copyright (C) 2022-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "replay-book-helpers")
(include-book "kestrel/utilities/submit-events" :dir :system)
(include-book "kestrel/utilities/widen-margins" :dir :system)
(include-book "kestrel/utilities/make-event-quiet" :dir :system)

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
          (submit-event event print nil state)
          (if erp
              (prog2$ (cw "ERROR (~x0) with event ~X12." erp event nil)
                      (mv erp state))
            ;; no error:
            (mv-let (end-time state)
              (get-real-time state)
              (let ((time (/ (ceiling (* (- end-time start-time) 100) 1) 100)))
                (progn$ (print-rounded-val time)
                        ;; The "s:" here is to label the time just printed with "seconds".
                        (cw "s: ~x0~%" (shorten-event event))
                        (submit-and-time-events (rest events) print state))))))))))

;; Reads and then submits all the events in FILENAME.
;; Returns (mv erp event state).
;; TODO: Take just a filename
(defun replay-book-fn (dir      ; no trailing slash
                       bookname ; no extension
                       print state)
  (declare (xargs :guard (and (stringp dir)
                              (stringp bookname)
                              (member-eq print '(nil :brief :verbose)))
                  :mode :program ; because this ultimately calls trans-eval-error-triple and in-package-fn
                  :stobjs state))
  (let* ((book-path-no-extension (concatenate 'string dir "/" bookname))
         (book-path (concatenate 'string book-path-no-extension ".lisp")))
    (mv-let (book-existsp state)
      (file-existsp book-path state)
      (if (not book-existsp)
          (prog2$ (er hard? 'replay-book-fn "The book ~x0 does not exist." book-path)
                  (mv :book-does-not-exist nil state))
        (prog2$
          (cw "Replaying ~s0:~%" book-path)
        ;; We load the .port file mostly so that #. constants mentioned in the book are defined:
          (let ((state (load-port-file-if-exists book-path-no-extension state)))
            (mv-let (erp events state)
              (read-objects-from-book book-path state)
              (if erp
                  (mv erp nil state)
              ;; We set the CBD so that the book is replayed in its own directory:
                (mv-let (erp val state)
                  (set-cbd-fn dir state)
                  (declare (ignore val))
                  (if erp
                      (mv erp nil state)
                    (let ((state (widen-margins state)))
                      (mv-let (erp state)
                        (submit-and-time-events events print state)
                        (let ((state (unwiden-margins state)))
                        ;; No error:
                          (mv erp '(value-triple :replay-succeeded) state))))))))))))))

;; This has no effect on the world, because all the work is done in make-event
;; expansion and such changes do not persist.
;; Example: (replay-book "../lists-light" "append")
(defmacro replay-book (dir ; no trailing slash
                       bookname ; no extension
                       &key
                       (print 'nil))
  `(make-event-quiet (replay-book-fn ,dir ,bookname ,print state)))
