(in-package :cl-utilities)

(defun read-delimited (sequence stream &key (start 0) end
		       (delimiter #\Newline) (test #'eql) (key #'identity))
  ;; Check bounds on SEQUENCE
  (multiple-value-setq (start end)
    (%read-delimited-bounds-check sequence start end))
  ;; Loop until we run out of input characters or places to put them,
  ;; or until we encounter the delimiter.
  (loop for index from start
	for char = (read-char stream nil nil)
	for test-result = (funcall test (funcall key char) delimiter)
	while (and char
		   (< index end)
		   (not test-result))
	do (setf (elt sequence index) char)
	finally (return-from read-delimited
		  (values index test-result))))

;; Conditions
;;;;;;;;;;;;;

(define-condition read-delimited-bounds-error (error)
  ((start :initarg :start :reader read-delimited-bounds-error-start)
   (end :initarg :end :reader read-delimited-bounds-error-end)
   (sequence :initarg :sequence :reader read-delimited-bounds-error-sequence))
  (:report (lambda (condition stream)
	     (with-slots (start end sequence) condition
	       (format stream "The bounding indices ~S and ~S are bad for a sequence of length ~S"
		       start end (length sequence)))))
  (:documentation "There's a problem with the indices START and END
for SEQUENCE. See CLHS SUBSEQ-OUT-OF-BOUNDS:IS-AN-ERROR issue."))

;; Error checking for bounds
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun %read-delimited-bounds-check (sequence start end)
  "Check to make sure START and END are in bounds when calling
READ-DELIMITED with SEQUENCE"
  (check-type start (or integer null))
  (check-type end (or integer null))
  (let ((start (%read-delimited-bounds-check-start sequence start end))
	(end (%read-delimited-bounds-check-end sequence start end)))
    ;; Returns (values start end)
    (%read-delimited-bounds-check-order sequence start end)))

(defun %read-delimited-bounds-check-order (sequence start end)
  "Check the order of START and END bounds, and return them in the
correct order."
  (when (< end start)
    (restart-case (error 'read-delimited-bounds-error
			 :start start :end end :sequence sequence)
      (continue ()
	:report "Switch start and end"
	(rotatef start end))))
  (values start end))

(defun %read-delimited-bounds-check-start (sequence start end)
  "Check to make sure START is in bounds when calling READ-DELIMITED
with SEQUENCE"
  (when (and start (< start 0))
    (restart-case (error 'read-delimited-bounds-error
			 :start start :end end :sequence sequence)
      (continue ()
	:report "Use default for START instead"
	(setf start 0))))
  start)

(defun %read-delimited-bounds-check-end (sequence start end)
  "Check to make sure END is in bounds when calling READ-DELIMITED
with SEQUENCE"
  (when (and end (> end (length sequence)))
    (restart-case (error 'read-delimited-bounds-error
			 :start start :end end :sequence sequence)
      (continue ()
	:report "Use default for END instead"
	(setf end nil))))
  (or end (length sequence)))