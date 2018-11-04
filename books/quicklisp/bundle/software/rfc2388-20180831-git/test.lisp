(defpackage :rfc2388.test
  (:use :common-lisp))

(in-package :rfc2388.test)

(defconstant +crlf+ (format nil "~C~C" #\return #\linefeed))


(defun generate-test-strings (parts)
  (flet ((prepend (left list)
           (mapcar (lambda (right)
                     (format nil "~A~A" left right))
                   list))
         (postpend (right list)
           (mapcar (lambda (left)
                     (format nil "~A~A" left right))
                   list)))
    (cond ((null parts)
           nil)
          ((null (cdr parts))
           (list (format nil "~A" (first parts))))
          (t
           (list* (format nil "~A" (first parts))
                  (nconc (prepend (first parts) (rest parts))
                         (postpend (first parts) (rest parts))
                         (generate-test-strings (cdr parts))))))))


(defparameter *strings* (generate-test-strings `("X" " " "-" "--" "---" ,+crlf+ #\return #\linefeed)))
(defparameter *boundaries* '("x" "-x" "--x"))


(defun sanitize-test-string (string)
  (with-output-to-string (out)
    (loop for char across string
       do (case char
            (#\return   (write-string "[CR]" out))
            (#\linefeed (write-string "[LF]" out))
            (t (write-char char out))))))


(defun test-string (string &optional (boundary "boundary"))
  (with-input-from-string (stream string)
    (handler-bind ((simple-warning (lambda (condition)
                                     (declare (ignore condition))
                                     (format t "~&Testing: ~S (boundary ~S)~%"
                                             (sanitize-test-string string)
                                             boundary))))
      (rfc2388::read-until-next-boundary stream boundary))))


(defun test ()
  (declare (optimize debug))
  (flet ((last-char (string)
           (declare (type simple-string string))
           (schar string (1- (length string))))

         (test (test expected boundary)
           (multiple-value-bind (result more-p)
               (test-string test boundary)
             (unless (or (string= result expected)
                         more-p)
               (format t "~%String:   ~S (Boundary: ~S)~%Expected: ~S~%Got:      ~S~%More: ~S~%"
                       (sanitize-test-string test)
                       boundary
                       (sanitize-test-string expected)
                       (sanitize-test-string result)
                       more-p)
          (finish-output t)))))

    (dolist (string *strings*)
      (dolist (boundary *boundaries*)
        (dolist (trailing-separator '("--" ""))
          (test (concatenate 'string string +crlf+ "--" boundary trailing-separator +crlf+)
                string
                boundary)
          (unless (char= #\- (last-char string))
            (test (concatenate 'string string "--" boundary trailing-separator +crlf+)
                  (let ((end (- (length string) 2)))
                    (if (and (<= 0 end)
                             (string= string +crlf+ :start1 end))
                        (subseq string 0 end)
                        string))
                  boundary))))))
  t)
