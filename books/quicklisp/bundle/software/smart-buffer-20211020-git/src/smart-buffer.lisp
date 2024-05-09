(in-package :cl-user)
(defpackage smart-buffer
  (:use #:cl
        #:xsubseq)
  (:export #:*default-memory-limit*
           #:*default-disk-limit*

           #:smart-buffer
           #:make-smart-buffer
           #:write-to-buffer
           #:finalize-buffer
           #:with-smart-buffer
           #:buffer-on-memory-p
           #:delete-stream-file
           #:delete-temporary-files

           #:buffer-limit-exceeded))
(in-package :smart-buffer)

(defvar *default-memory-limit* (expt 2 20))
(defvar *default-disk-limit* (expt 2 30))

(defvar *temporary-directory*
  (uiop:ensure-directory-pathname
    (merge-pathnames (format nil "smart-buffer-~36R" (random (expt 36 #-gcl 8 #+gcl 5)))
                     (uiop:default-temporary-directory))))

(defstruct (smart-buffer (:conc-name :buffer-)
                         (:constructor %make-smart-buffer))
  (memory-limit *default-memory-limit*)
  (disk-limit *default-disk-limit*)
  (current-len 0)
  (on-memory-p t)
  (memory-buffer (make-concatenated-xsubseqs))
  (disk-buffer nil))

(defun make-smart-buffer (&rest initargs &key memory-limit disk-limit &allow-other-keys)
  (let ((buffer (apply #'%make-smart-buffer initargs)))
    (when (and memory-limit
               disk-limit
               (< disk-limit memory-limit))
      (setf (buffer-memory-limit buffer) disk-limit))
    buffer))

(define-condition buffer-limit-exceeded (error)
  ((limit :initarg :limit
          :initform nil))
  (:report (lambda (condition stream)
             (format stream "Buffer exceeded the limit~:[~;~:*: ~A~]"
                     (slot-value condition 'limit)))))

(defun write-to-buffer (buffer seq &optional (start 0) (end (length seq)))
  (check-type seq (array (unsigned-byte 8) (*)))
  (incf (buffer-current-len buffer) (- end start))
  (check-limit buffer)
  (if (buffer-on-memory-p buffer)
      (xnconcf (buffer-memory-buffer buffer) (xsubseq seq start end))
      (with-open-file (out (buffer-disk-buffer buffer)
                           :direction :output
                           :element-type '(unsigned-byte 8)
                           :if-exists :append)
        (write-sequence seq out :start start :end end))))

(defun check-limit (buffer)
  (cond
    ((and (buffer-on-memory-p buffer)
          (< (buffer-memory-limit buffer)
             (buffer-current-len buffer)))
     (when (< (buffer-disk-limit buffer)
              (buffer-current-len buffer))
       (error 'buffer-limit-exceeded :limit (buffer-disk-limit buffer)))
     (setf (buffer-disk-buffer buffer)
           (uiop:with-temporary-file (:stream stream :pathname tmp
                                      :directory *temporary-directory*
                                      :direction :output
                                      :element-type '(unsigned-byte 8)
                                      :keep t)
             (typecase (buffer-memory-buffer buffer)
               (null-concatenated-xsubseqs)
               (t (write-sequence (coerce-to-sequence (buffer-memory-buffer buffer)) stream)))
             tmp)
           (buffer-on-memory-p buffer) nil
           (buffer-memory-buffer buffer) nil))
    ((and (not (buffer-on-memory-p buffer))
          (< (buffer-disk-limit buffer)
             (buffer-current-len buffer)))
     (error 'buffer-limit-exceeded :limit (buffer-disk-limit buffer)))))

(defun finalize-buffer (buffer)
  (if (buffer-on-memory-p buffer)
      (flex:make-in-memory-input-stream
       (typecase (buffer-memory-buffer buffer)
         (null-concatenated-xsubseqs #())
         (t (coerce-to-sequence (buffer-memory-buffer buffer)))))
      (open (buffer-disk-buffer buffer) :direction :input :element-type '(unsigned-byte 8))))

(defmacro with-smart-buffer ((buffer &key
                                       (memory-limit '*default-memory-limit*)
                                       (disk-limit '*default-disk-limit*))
                             &body body)
  `(let ((,buffer (make-smart-buffer :memory-limit ,memory-limit :disk-limit ,disk-limit)))
     ,@body
     (finalize-buffer ,buffer)))

(defun delete-stream-file (stream)
  (when (typep stream 'file-stream)
    (ignore-errors (delete-file (pathname stream))))
  (values))

(defun delete-temporary-files (&key (stale-seconds 0))
  (let ((now (get-universal-time)))
    (mapc #'uiop:delete-file-if-exists
          (remove-if-not (lambda (file)
                           (< stale-seconds (- now (file-write-date file))))
                         (uiop:directory-files *temporary-directory*)))))
