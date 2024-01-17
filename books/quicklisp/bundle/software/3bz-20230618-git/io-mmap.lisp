(in-package #:3bz)
;; we restrict size of these types a bit more on 64 bit platforms to
;; ensure intermediate results stay in reasonable range for
;; performance. 32bit probably needs tuned, might want to allow larger
;; than fixnum offsets for FFI use with implementations with small
;; fixnums?
(deftype size-t () (if (= 8 (cffi:foreign-type-size :pointer))
                       `(unsigned-byte
                         ,(min 60 (1- (integer-length most-positive-fixnum))))
                       `(unsigned-byte
                         ,(min 30 (integer-length most-positive-fixnum)))))
;; slightly larger so incrementing a size-t still fits
(deftype offset-t () (if (= 8 (cffi:foreign-type-size :pointer))
                         `(unsigned-byte
                           ,(min 61 (integer-length most-positive-fixnum)))
                         `(unsigned-byte
                           ,(min 31 (integer-length most-positive-fixnum)))))



(defclass octet-pointer ()
  ((base :reader base :initarg :base)
   (size :reader size :initarg :size) ;; end?
   (scope :reader scope :initarg :scope)))

(defmacro with-octet-pointer ((var pointer size) &body body)
  (with-gensyms (scope)
    (once-only (pointer size)
     `(let* ((,scope (cons t ',var)))
        (unwind-protect
             (let ((,var (make-instance 'octet-pointer :base ,pointer
                                                       :size ,size
                                                       :scope ,scope)))
               ,@body)
          (setf (car ,scope) nil))))))

(defun valid-octet-pointer (op)
  (and (car (scope op))
       (not (cffi:null-pointer-p (base op)))
       (plusp (size op))))

(defclass octet-pointer-context ()
  ((op :reader op :initarg :op)
   (pointer :reader %pointer :initarg :pointer)
   (boxes :reader boxes :initarg :boxes)))

(defun make-octet-pointer-context (octet-pointer
                                   &key (start 0) (offset 0)
                                     (end (size octet-pointer)))
  (make-instance 'octet-pointer-context
                 :op octet-pointer
                 :pointer (base octet-pointer)
                 :boxes (make-context-boxes
                         :start start :offset offset :end end)))


(defmacro with-pointer-context ((context) &body body)
  (with-gensyms (boxes pointer)
    (once-only (context)
      `(let* ((,boxes (boxes ,context))
              (,pointer (base (op ,context))))
         (declare (optimize speed)
                  (ignorable ,pointer ,boxes)
                  (type context-boxes ,boxes))
         (assert (valid-octet-pointer (op ,context)))
         (context-common (,boxes)
           (macrolet ((word64 ()
                        (with-gensyms (available result)
                          `(let ((,available (octets-left)))
                             (if (>= ,available 8)
                                 (let ((,result (cffi:mem-ref
                                                 ,',pointer :uint64 (pos))))
                                   (incf (pos) 8)
                                   (values ,result 8))
                                 (let ((,result 0))
                                   (declare (type (unsigned-byte 64) ,result))
                                   (loop
                                     for i fixnum below (min 8 ,available)
                                     do (setf ,result
                                              (ldb (byte 64 0)
                                                   (logior
                                                    ,result
                                                    (ash
                                                     (cffi:mem-ref
                                                      ,',pointer
                                                      :uint8
                                                      (+ (pos) i))
                                                     (* i 8))))))
                                   (incf (pos) ,available)
                                   (values ,result ,available))))))
                      (word32 ()
                        (with-gensyms (available result)
                          `(let ((,available (octets-left)))
                             (if (>= ,available 4)
                                 (let ((,result (cffi:mem-ref
                                                 ,',pointer :uint32 (pos))))
                                   (incf (pos) 4)
                                   (values ,result 4))
                                 (let ((,result 0))
                                   (declare (type (unsigned-byte 32) ,result))
                                   (loop
                                     for i of-type (unsigned-byte 2) below (min 4 ,available)
                                     do (setf ,result
                                              (ldb (byte 32 0)
                                                   (logior
                                                    ,result
                                                    (ash
                                                     (cffi:mem-ref
                                                      ,',pointer
                                                      :uint8
                                                      (+ (pos) i))
                                                     (* i 8))))))
                                   (incf (pos) ,available)
                                   (values ,result ,available)))))))
             ,@body))))))
