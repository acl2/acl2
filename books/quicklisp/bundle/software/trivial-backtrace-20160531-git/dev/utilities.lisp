(in-package #:trivial-backtrace)

(defparameter *date-time-format* "%Y-%m-%d-%H:%M"
  "The default format to use when printing dates and times.

* %% - A '%' character
* %d - Day of the month as a decimal number [01-31]
* %e - Same as %d but does not print the leading 0 for days 1 through 9 
     [unlike strftime[], does not print a leading space]
* %H - Hour based on a 24-hour clock as a decimal number [00-23]
*%I - Hour based on a 12-hour clock as a decimal number [01-12]
* %m - Month as a decimal number [01-12]
* %M - Minute as a decimal number [00-59]
* %S - Second as a decimal number [00-59]
* %w - Weekday as a decimal number [0-6], where Sunday is 0
* %y - Year without century [00-99]
* %Y - Year with century [such as 1990]

This code is borrowed from the `format-date` function in 
[metatilities-base][].")

;; modified from metatilities-base
(eval-when (:compile-toplevel :load-toplevel :execute)
  (defmacro generate-time-part-function (part-name position)
    (let ((function-name 
	   (intern 
	    (concatenate 'string
			 (symbol-name 'time) "-" (symbol-name part-name))
	    :trivial-backtrace)))
      `(eval-when (:compile-toplevel :load-toplevel :execute)
         (defun ,function-name
                (&optional (universal-time (get-universal-time))
                           (time-zone nil))
           ,(format nil "Returns the ~(~A~) part of the given time." part-name)
           (nth-value ,position 
		      (apply #'decode-universal-time
			     universal-time time-zone))))))

  (generate-time-part-function second 0)
  (generate-time-part-function minute 1)
  (generate-time-part-function hour 2)
  (generate-time-part-function date 3)
  (generate-time-part-function month 4)
  (generate-time-part-function year 5)
  (generate-time-part-function day-of-week 6)
  (generate-time-part-function daylight-savings-time-p 7))

(defun date-time-string (&key (date/time (get-universal-time))
			 (format *date-time-format*))
  (format-date format date/time nil))

(defun format-date (format date &optional stream time-zone)
  (declare (ignore time-zone))
  (let ((format-length (length format)))
    (format 
     stream "~{~A~}"
     (loop for index = 0 then (1+ index) 
	while (< index format-length) collect 
	(let ((char (aref format index)))
	  (cond 
	    ((char= #\% char)
	     (setf char (aref format (incf index)))
	     (cond 
	       ;; %% - A '%' character
	       ((char= char #\%) #\%)
                            
	       ;; %d - Day of the month as a decimal number [01-31]
	       ((char= char #\d) (format nil "~2,'0D" (time-date date)))
                            
	       ;; %e - Same as %d but does not print the leading 0 for 
	       ;; days 1 through 9. Unlike strftime, does not print a 
	       ;; leading space
	       ((char= char #\e) (format nil "~D" (time-date date)))
                            
	       ;; %H - Hour based on a 24-hour clock as a decimal number [00-23]
	       ((char= char #\H) (format nil "~2,'0D" (time-hour date)))
                            
	       ;; %I - Hour based on a 12-hour clock as a decimal number [01-12]
	       ((char= char #\I) (format nil "~2,'0D" 
					 (1+ (mod (time-hour date) 12))))
                            
	       ;; %m - Month as a decimal number [01-12]
	       ((char= char #\m) (format nil "~2,'0D" (time-month date)))
                            
	       ;; %M - Minute as a decimal number [00-59]
	       ((char= char #\M) (format nil "~2,'0D" (time-minute date)))
                            
	       ;; %S - Second as a decimal number [00-59]
	       ((char= char #\S) (format nil "~2,'0D" (time-second date)))
                            
	       ;; %w - Weekday as a decimal number [0-6], where Sunday is 0
	       ((char= char #\w) (format nil "~D" (time-day-of-week date)))
                            
	       ;; %y - Year without century [00-99]
	       ((char= char #\y) 
		(let ((year-string (format nil "~,2A" (time-year date))))
		  (subseq year-string (- (length year-string) 2))))
                            
	       ;; %Y - Year with century [such as 1990]
	       ((char= char #\Y) (format nil "~D" (time-year date)))
                            
	       (t
		(error "Ouch - unknown formatter '%~c" char))))
	    (t char)))))))
