(in-package #:trivial-backtrace-test)

(deftestsuite generates-backtrace (trivial-backtrace-test)
  ())

(addtest (generates-backtrace)
  test-1
  (let ((output nil))
    (handler-case 
	(let ((x 1))
	  (let ((y (- x (expt 1024 0))))
	    (declare (optimize (safety 3)))
	    (/ 2 y)))
      (error (c)
	(setf output (print-backtrace c :output nil))))
    (ensure (stringp output))
    (ensure (plusp (length output)))))

(addtest (generates-backtrace-to-string-stream)
  test-2
  (let ((output nil))
    (handler-case 
	(let ((x 1))
	  (let ((y (- x (expt 1024 0))))
	    (declare (optimize (safety 3)))
	    (/ 2 y)))
      (error (c)
	(setf output (with-output-to-string (stream)
		       (print-backtrace c :output nil)))))
    (ensure (stringp output))
    (ensure (plusp (length output)))))
