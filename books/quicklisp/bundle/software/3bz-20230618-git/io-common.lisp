(in-package #:3bz)

(deftype octet () '(unsigned-byte 8))
(deftype octet-vector () '(simple-array octet (*)))

;; typed container for offsets and bounds of current input source, and
;; remaining bits of partially read octets
(defstruct (context-boxes (:conc-name cb-))
  ;; start of 'active' region of buffer
  (start 0 :type size-t)
  ;; end of 'active' region of buffer
  (end 0 :type size-t)
  ;; offset of next unread byte, (<= start offset end)
  (offset 0 :type size-t))


(defmacro context-common ((boxes) &body body)
  `(macrolet ((pos ()
                `(cb-offset ,',boxes))
              (end ()
                `(cb-end ,',boxes))
              (%octet (read-form
                       &optional (eob-form
                                  '(error "read past end of buffer")))
                `(progn
                   (when (>= (pos) (end))
                     ,eob-form)
                   (prog1
                       ,read-form
                     (incf (pos)))))
              (octets-left ()
                `(- (cb-end ,',boxes) (pos))))
     ,@body))


(defclass octet-vector-context ()
  ((octet-vector :reader octet-vector :initarg :octet-vector)
   (boxes :reader boxes :initarg :boxes)))

(defun make-octet-vector-context (vector &key (start 0) (offset start)
                                           (end (length vector)))
  (make-instance 'octet-vector-context
                 :octet-vector vector
                 :boxes (make-context-boxes
                         :start start :offset offset :end end)))

(defclass octet-stream-context ()
  ((octet-stream :reader octet-stream :initarg :octet-stream)
   (boxes :reader boxes :initarg :boxes)))

(defun make-octet-stream-context (file-stream &key (start 0) (offset 0)
                                                (end (file-length file-stream)))
  (make-instance 'octet-stream-context
                 :octet-stream file-stream
                 :boxes (make-context-boxes
                         :start start :offset offset :end end)))

;; hack to allow storing parts of a file to use as context later. call
;; before using context
(defmethod %resync-file-stream (context))
(defmethod %resync-file-stream ((context octet-stream-context))
  (file-position (octet-stream context)
                 (cb-offset (boxes context))))

(defun valid-octet-stream (os)
  (and (typep os 'stream)
       (subtypep (stream-element-type os) 'octet)
       (open-stream-p os)
       (input-stream-p os)))
