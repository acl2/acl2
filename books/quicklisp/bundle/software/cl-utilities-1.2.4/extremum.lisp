(in-package :cl-utilities)

(define-condition no-extremum (error) ()
  (:report "Cannot find extremum of empty sequence")
  (:documentation "Raised when EXTREMUM is called on an empty
sequence, since there is no morally smallest element"))

(defun comparator (test &optional (key #'identity))
  "Comparison operator: auxilliary function used by EXTREMUM"
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 1)))
  (lambda (a b) (if (funcall test
                             (funcall key a)
                             (funcall key b))
                    a
                    b)))

;; This optimizes the case where KEY is #'identity
(define-compiler-macro comparator (&whole whole test
					  &optional (key #'identity))
  (if (eql key #'identity)
      `(lambda (a b)
	(declare (optimize (speed 3) (safety 0) (space 0) (debug 1)))
	(if (funcall ,test a b) a b))
      whole))

;; The normal way of testing the if length of a proper sequence equals
;; zero is to just use (zerop (length sequence)). And, while some
;; implementations may optimize this, it's probably a good idea to
;; just write an optimized version and use it. This method can speed
;; up list length testing.
(defun zero-length-p (sequence)
  "Is the length of SEQUENCE equal to zero?"
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 1)))
  (or (null sequence)
      (when (vectorp sequence)
	(zerop (length sequence)))))

(declaim (inline zero-length-p))

;; Checks the length of the subsequence of SEQUENCE specified by START
;; and END, and if it's 0 then a NO-EXTREMUM error is signalled. This
;; should only be used in EXTREMUM functions.
(defmacro with-check-length ((sequence start end) &body body)
  (once-only (sequence start end)
    `(if (or (zero-length-p ,sequence)
	  (>= ,start (or ,end (length ,sequence))))
      (restart-case (error 'no-extremum)
	(continue ()
	  :report "Return NIL instead"
	  nil))
      (progn ,@body))))

;; This is an extended version which takes START and END keyword
;; arguments. Any spec-compliant use of EXTREMUM will also work with
;; this extended version.
(defun extremum (sequence predicate
		 &key (key #'identity) (start 0) end)
  "Returns the element of SEQUENCE that would appear first if the
sequence were ordered according to SORT using PREDICATE and KEY using
an unstable sorting algorithm. See http://www.cliki.net/EXTREMUM for
the full specification."
  (with-check-length (sequence start end)
    (reduce (comparator predicate key) sequence
	    :start start :end end)))

;; This optimizes the case where KEY is #'identity
(define-compiler-macro extremum (&whole whole sequence predicate
					&key (key #'identity) (start 0) end)
  (if (eql key #'identity)
      (once-only (sequence predicate start end)
	`(with-check-length (,sequence ,start ,end)
	  (locally (declare (optimize (speed 3) (safety 0) (space 0) (debug 1)))
	    (reduce (comparator ,predicate) ,sequence
		    :start ,start :end ,end))))
      whole))

;; This is an "optimized" version which calls KEY less. REDUCE is
;; already so optimized that this will actually be slower unless KEY
;; is expensive. And on CLISP, of course, the regular version will be
;; much faster since built-in functions are ridiculously faster than
;; ones implemented in Lisp. Be warned, this isn't as carefully tested
;; as regular EXTREMUM and there's more that could go wrong.
(defun extremum-fastkey (sequence predicate
			 &key (key #'identity) (start 0) end)
  "EXTREMUM implemented so that it calls KEY less. This is only faster
if the KEY function is so slow that calling it less often would be a
significant improvement; ordinarily it's slower."
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 1)))
  (with-check-length (sequence start end)
    (let* ((smallest (elt sequence 0))
	   (smallest-key (funcall key smallest))
	   (current-index 0)
	   (real-end (or end (1- most-positive-fixnum))))
      (declare (type (integer 0) current-index real-end start)
	       (fixnum current-index real-end start))
      (map nil #'(lambda (x)
		   (when (<= start current-index real-end)
		     (let ((x-key (funcall key x)))
		       (when (funcall predicate
				      x-key
				      smallest-key)
			 (setf smallest x)
			 (setf smallest-key x-key))))
		   (incf current-index))
	   sequence)
      smallest)))

;; EXTREMA and N-MOST-EXTREME are based on code and ideas from Tobias
;; C. Rittweiler. They deal with the cases in which you are not
;; looking for a single extreme element, but for the extreme identical
;; elements or the N most extreme elements.

(defun extrema (sequence predicate &key (key #'identity) (start 0) end)
  (with-check-length (sequence start end)
    (let* ((sequence (subseq sequence start end))
	   (smallest-elements (list (elt sequence 0)))
	   (smallest-key (funcall key (elt smallest-elements 0))))
      (map nil
	   #'(lambda (x)
	       (let ((x-key (funcall key x)))
		 (cond ((funcall predicate x-key smallest-key)
			(setq smallest-elements (list x))
			(setq smallest-key x-key))
		       ;; both elements are considered equal if the predicate
		       ;; returns false for (PRED A B) and (PRED B A)
		       ((not (funcall predicate smallest-key x-key))
			(push x smallest-elements)))))
	   (subseq sequence 1))
      ;; We use NREVERSE to make this stable (in the sorting algorithm
      ;; sense of the word 'stable').
      (nreverse smallest-elements))))



(define-condition n-most-extreme-not-enough-elements (warning)
  ((n :initarg :n :reader n-most-extreme-not-enough-elements-n
      :documentation "The number of elements that need to be returned")
   (subsequence :initarg :subsequence 
		:reader n-most-extreme-not-enough-elements-subsequence
		:documentation "The subsequence from which elements
must be taken. This is determined by the sequence and the :start and
:end arguments to N-MOST-EXTREME."))
  (:report (lambda (condition stream)
	     (with-slots (n subsequence) condition
	       (format stream "There are not enough elements in the sequence ~S~% to return the ~D most extreme elements"
		       subsequence n))))
  (:documentation "There are not enough elements in the sequence given
to N-MOST-EXTREME to return the N most extreme elements."))

(defun n-most-extreme (n sequence predicate &key (key #'identity) (start 0) end)
  "Returns a list of the N elements of SEQUENCE that would appear
first if the sequence were ordered according to SORT using PREDICATE
and KEY with a stable sorting algorithm. If there are less than N
elements in the relevant part of the sequence, this will return all
the elements it can and signal the warning
N-MOST-EXTREME-NOT-ENOUGH-ELEMENTS"
  (check-type n (integer 0))
  (with-check-length (sequence start end)
    ;; This is faster on vectors than on lists.
    (let ((sequence (subseq sequence start end)))
      (if (> n (length sequence))
	  (progn
	    (warn 'n-most-extreme-not-enough-elements
		  :n n :subsequence sequence)
	    (stable-sort (copy-seq sequence) predicate :key key))
	  (subseq (stable-sort (copy-seq sequence) predicate :key key)
		  0 n)))))