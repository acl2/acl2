; A tool to help generate depends-on forms for cert.pl
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book contains a utility to register non-book files that the current
;; book depends on and then to later spit out suitable depends-on forms for
;; cert.pl.

;; Dependencies should be added by forms like this:
;; (table acl2::depends-on-table PATH t)

;; Returns the list of all files that the current session has been declared to
;; depends on (not counting included books).  The paths are keys in the table
;; (all bound to t), so that we can add a new key with a simple table event.
(defund depends-on-files (wrld)
  ;; Reversing seems to give a result that starts with the dependencies that
  ;; were added earliest:
  (reverse (strip-cars (table-alist 'acl2::depends-on-table wrld))))

(defun make-depends-on-lines (files) ; files should be a list of strings
  (declare (xargs :guard t))
  (if (atom files)
      nil
    (let ((file (first files)))
      (if (not (stringp file))
          (er hard? 'make-depends-on-lines "Bad item in depends-on-table: ~x0" file)
        (cons (concatenate 'string "; (depends-on \"" (first files) "\")")
              (make-depends-on-lines (rest files)))))))

(defun cw-lines (lines)
  (if (endp lines)
      nil
    (prog2$ (cw "~S0~%" (first lines))
            (cw-lines (rest lines)))))

;; To register a new file in the table, submit the event (table acl2::depends-on-table <file> t).

(defun depends-on-lines-fn (wrld)
  (let* ((files (depends-on-files wrld))
         (lines (make-depends-on-lines files)))
    (prog2$ (cw-lines lines)
            '(value-triple :invisible))))

(defmacro depends-on-lines ()
  `(with-output
     :off :all
     (make-event (depends-on-lines-fn (w state)))))
