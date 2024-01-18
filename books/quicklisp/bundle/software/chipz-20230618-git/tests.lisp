;; running the tests requires
;;   - ASDF
;;   - the salza2 library (http://www.xach.com/lisp/salza2)
;;   - "bzip2" program (in PATH)
;; how to run the tests:
;;   - load this file, tests.lisp, into your lisp environment
;;   - create an empty directory, known hereafter as <test-files-dir>
;;   - put some files into the directory, their extension shall be "uncompressed"
;;   - compress the test files by running (chipz-tests:compress-test-files <test-files-dir>)
;;     you only need to do this once
;;   - execute (chipz-tests:run-all-tests <test-files-dir>)

(asdf:oos 'asdf:load-op "chipz")
(asdf:oos 'asdf:load-op "salza2")

(defpackage :chipz-tests
  (:use :cl :chipz)
  (:export #:run-all-tests #:compress-test-files))

(in-package :chipz-tests)

(defun test/whole-file (format compressed-pathname original-pathname)
  (with-open-file (compressed-stream compressed-pathname :direction :input
                                     :element-type '(unsigned-byte 8))
    (with-open-file (stream original-pathname :direction :input
                            :element-type '(unsigned-byte 8))
      (let ((compressed-input (make-array (file-length compressed-stream)
                                          :element-type '(unsigned-byte 8)))
            (output (make-array (file-length stream)
                                :element-type '(unsigned-byte 8)))
            (original (make-array (file-length stream)
                                  :element-type '(unsigned-byte 8)))
            (zstream (make-dstate format)))
        (let ((compressed-bytes (read-sequence compressed-input compressed-stream)))
          (read-sequence original stream)
          (multiple-value-bind (bytes-read bytes-output)
              (decompress output zstream compressed-input :input-end compressed-bytes)
            (and (= bytes-read compressed-bytes)
                 (= bytes-output (length original))
                 (not (mismatch output original :end1 bytes-output
                                :end2 bytes-output)))))))))

(defun test/whole-file-cons (format compressed-pathname original-pathname)
  (with-open-file (compressed-stream compressed-pathname :direction :input
                                     :element-type '(unsigned-byte 8))
    (with-open-file (stream original-pathname :direction :input
                            :element-type '(unsigned-byte 8))
      (let ((compressed-input (make-array (file-length compressed-stream)
                                          :element-type '(unsigned-byte 8)))
            (original (make-array (file-length stream)
                                  :element-type '(unsigned-byte 8))))
        (read-sequence compressed-input compressed-stream)
        (let ((output (decompress nil format compressed-input)))
          (read-sequence original stream)
          (and (= (length original) (length output))
               (not (mismatch output original))))))))

(defun test/incremental-file (format compressed-pathname original-pathname)
  (with-open-file (compressed-stream compressed-pathname :direction :input
                                     :element-type '(unsigned-byte 8))
    (with-open-file (stream original-pathname :direction :input
                            :element-type '(unsigned-byte 8))
      (let ((compressed-input (make-array (file-length compressed-stream)
                                          :element-type '(unsigned-byte 8)))
            (output (make-array (file-length stream)
                                :element-type '(unsigned-byte 8)))
            (original (make-array (file-length stream)
                                  :element-type '(unsigned-byte 8)))
            (zstream (make-dstate format)))
        (read-sequence original stream)
        (let ((compressed-bytes (read-sequence compressed-input compressed-stream))
              (input-index 0)
              (output-index 0))
          (loop
             (multiple-value-bind (bytes-read bytes-output)
                 (decompress output zstream compressed-input
                             :input-start input-index
                             :input-end compressed-bytes
                             :output-start output-index
                             :output-end (1+ output-index))
               (when (zerop bytes-output) (return))
               (let ((ouch (mismatch original output
                                     :start1 output-index :start2 output-index
                                     :end1 (1+ output-index) :end2 (1+ output-index))))
                 (when ouch
                   (return nil)))
               (incf input-index bytes-read)
               (incf output-index)))
          (and (= input-index compressed-bytes))
               (= output-index (length original))
               (not (mismatch output original :end1 output-index
                              :end2 output-index)))))))

#+chipz-system:gray-streams
(defun test/gray-stream-read-sequence (format compressed-pathname original-pathname)
  (with-open-file (compressed-stream compressed-pathname :direction :input
                                     :element-type '(unsigned-byte 8))
    (with-open-file (stream original-pathname :direction :input
                            :element-type '(unsigned-byte 8))
      (let ((zstream (make-decompressing-stream format compressed-stream))
            (output (make-array (file-length stream)
                                :element-type '(unsigned-byte 8)))
            (original (make-array (file-length stream)
                                  :element-type '(unsigned-byte 8))))
        (read-sequence output zstream)
        (read-sequence original stream)
        (not (mismatch output original))))))

#+chipz-system:gray-streams
(defun test/gray-stream-read-byte (format compressed-pathname original-pathname)
  (with-open-file (compressed-stream compressed-pathname :direction :input
                                     :element-type '(unsigned-byte 8))
    (with-open-file (stream original-pathname :direction :input
                            :element-type '(unsigned-byte 8))
      (let ((zstream (make-decompressing-stream format compressed-stream))
            (output (make-array (file-length stream)
                                :element-type '(unsigned-byte 8)))
            (original (make-array (file-length stream)
                                  :element-type '(unsigned-byte 8))))
        (loop for i from 0 below (file-length stream) do
          (progn
            (setf (aref output i) (read-byte zstream))
            (setf (aref original i) (read-byte stream))))
        (not (mismatch output original))))))

(defparameter *default-test-files-dir*
   (make-pathname
     :directory (append (pathname-directory *LOAD-TRUENAME*) '("test-files"))
     :device (pathname-device *LOAD-TRUENAME*)
     :host (pathname-host *LOAD-TRUENAME*)))

(defparameter *test-functions*
  (list 'test/whole-file
        'test/whole-file-cons
        'test/incremental-file
        #+chipz-system:gray-streams 'test/gray-stream-read-sequence
        #+chipz-system:gray-streams 'test/gray-stream-read-byte))

(defparameter *formats*
  '(gzip zlib deflate bzip2))

(defmacro dolist/every ((var list-form) &body body)
  (let ((all-ok (gensym)))
    `(reduce
       (lambda (,all-ok ,var) (and (progn ,@body) ,all-ok))
       ,list-form :initial-value t)))

(defun run-all-tests (&optional (test-files-dir *default-test-files-dir*))
  (labels ((run-test (testfun format uncompressed-file)
             (let ((compressed (make-pathname :type (symbol-name format)
                                              :defaults uncompressed-file)))
               (format t "; ~A ~A~%" (symbol-name testfun) compressed)
               (with-simple-restart (skip-test "skip ~A ~A" (symbol-name testfun) compressed)
                 (assert (probe-file compressed))
                 (let* ((begin  (get-internal-run-time))
                        (result (funcall testfun format compressed uncompressed-file))
                        (end    (get-internal-run-time))
                        (secs   (/ (- end begin) internal-time-units-per-second)))
                   (if result
                     (format t "; PASSED (~4$ seconds)~%" secs)
                     (format t "; FAILED (~4$ seconds) ~A~%" secs result))
                   result)))))
    (let* ((uncompressed (make-pathname :name :wild :type "uncompressed"
                                        :defaults test-files-dir)))
      (dolist/every (testfun *test-functions*)
        (dolist/every (format *formats*)
          (dolist/every (file (directory uncompressed))
            (run-test testfun format file)))))))

(defun run-salza2 (compressor-class input-file output-file)
  (with-open-file (in-stream input-file :element-type '(unsigned-byte 8))
    (with-open-file (out-stream output-file :element-type '(unsigned-byte 8)
                                            :direction :output
                                            :if-exists :supersede)
      (let ((buffer (make-array 100000 :element-type '(unsigned-byte 8)))
            (callback (salza2:make-stream-output-callback out-stream)))
        (salza2:with-compressor (comp compressor-class :callback callback)
          (loop
            (let ((bytes-read (read-sequence buffer in-stream)))
              (if (zerop bytes-read)
                (return)
                (salza2:compress-octet-vector buffer comp :end bytes-read)))))))))

(defun run-external (output-file executable &rest args)
  #+lispworks
  (system:run-shell-command     ;; cmd        argv[0]    argv[1..]
    (map 'vector #'identity (list* executable executable args))
    :output output-file :if-output-exists :supersede)
  #+sbcl
  (sb-ext:run-program
    executable args :search t :output output-file :if-output-exists :supersede)
  #+openmcl
  (ccl:run-program
    executable args :output output-file :if-output-exists :supersede)
  #+cmu
  (extensions:run-program
    executable args :output output-file :if-output-exists :supersede)
  #+clisp
  (ext:run-program
   executable :arguments args :output output-file :if-output-exists :overwrite)
  #+ecl
  (ext:run-program
   executable args :output output-file :if-output-exists :supersede)
  #+clasp
  (ext:system (concatenate 'string executable " "
                           (with-output-to-string (stream)
                             (dolist (x args)
                               (princ x stream)(princ " " stream)))
                           " >" (namestring output-file)))
  #-(or lispworks sbcl openmcl cmu clisp ecl clasp)
  (error "run-external is not supported for this lisp implementation"))

(defun compress-test-files (&optional (test-files-dir *default-test-files-dir*))
  (let ((uncompressed (make-pathname :name :wild :type "uncompressed"
                                     :defaults test-files-dir)))
    (dolist (input (directory uncompressed))
      (format t "; compressing ~A~%" input)
      (dolist (format *formats*)
        (let ((output (make-pathname :type (symbol-name format) :defaults input)))
          (ecase format
             (deflate (run-salza2 'salza2:deflate-compressor input output))
             (zlib    (run-salza2 'salza2:zlib-compressor input output))
             (gzip    (run-salza2 'salza2:gzip-compressor input output))
             (bzip2   (run-external output "bzip2" "-c" (namestring input)))))))))
