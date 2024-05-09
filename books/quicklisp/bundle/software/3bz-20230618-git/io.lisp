(in-package #:3bz)

(defmacro with-vector-context ((context) &body body)
  (with-gensyms (boxes vector)
    (once-only (context)
      `(let* ((,boxes (boxes ,context))
              (,vector (octet-vector ,context)))
         (declare (optimize speed)
                  (ignorable ,vector ,boxes)
                  (type context-boxes ,boxes))
         (check-type ,vector octet-vector)
         (locally (declare (type octet-vector ,vector))
           (context-common (,boxes)
             (macrolet (;; read up to 8 octets in LE order, return
                        ;; result + # of octets read as multiple
                        ;; values
                        (word64 ()
                          (with-gensyms (available result)
                            `(let ((,available (octets-left)))
                               (if (>= ,available 8)
                                   (let ((,result (ub64ref/le
                                                   ,',vector (pos))))
                                     (incf (pos) 8)
                                     (values ,result 8))
                                   (let ((,result 0))
                                     (loop
                                       for i fixnum below ,available
                                       do (setf ,result
                                                (ldb (byte 64 0)
                                                     (logior
                                                      ,result
                                                      (ash
                                                       (aref ,',vector
                                                             (+ (pos) i))
                                                       (* i 8))))))
                                     (incf (pos) ,available)
                                     (values ,result ,available))))))
                        (word32 ()
                          (with-gensyms (available result)
                            `(let ((,available (octets-left)))
                               (if (>= ,available 4)
                                   (let ((,result (ub32ref/le
                                                   ,',vector (pos))))
                                     (incf (pos) 4)
                                     (values ,result 4))
                                   (let ((,result 0))
                                     (loop
                                       for i of-type (unsigned-byte 2) below (min 4 ,available)
                                       do (setf ,result
                                                (ldb (byte 32 0)
                                                     (logior
                                                      ,result
                                                      (ash
                                                       (aref ,',vector
                                                             (+ (pos) i))
                                                       (* i 8))))))
                                     (incf (pos) ,available)
                                     (values ,result ,available)))))))
               ,@body)))))))

(defmacro with-stream-context ((context) &body body)
  (with-gensyms (boxes stream)
    (once-only (context)
      `(let* ((,boxes (boxes ,context))
              (,stream (octet-stream ,context)))
         (declare (optimize speed)
                  (ignorable ,stream ,boxes)
                  (type context-boxes ,boxes))
         (assert (valid-octet-stream ,stream))
         (context-common (,boxes)
           (macrolet (;; override POS/SET-POS for streams
                      (pos ()
                        `(file-position ,',stream))
                      (word64 ()
                        (with-gensyms (available result)
                          `(locally (declare (optimize (speed 1)))
                             (let ((,available (- (end) (pos))))
                               (if (>= ,available 8)
                                   (values (nibbles:read-ub64/le ,',stream) 8)
                                   (let ((,result 0))
                                     (declare (type (unsigned-byte 64) ,result)
                                              (type (mod 8) ,available))
                                     (loop
                                       for i fixnum below (min 8 ,available)
                                       do (setf (ldb (byte 8 (* i 8))
                                                     ,result)
                                                (read-byte ,',stream)))
                                     (values ,result ,available)))))))
                      (word32 ()
                        (with-gensyms (available result)
                          `(locally (declare (optimize (speed 1)))
                             (let ((,available (- (end) (pos))))
                               (if (>= ,available 4)
                                   (values (nibbles:read-ub32/le ,',stream) 4)
                                   (let ((,result 0))
                                     (declare (type (unsigned-byte 64) ,result)
                                              (type (mod 4) ,available))
                                     (loop
                                       for i fixnum below (min 4 ,available)
                                       do (setf (ldb (byte 8 (* i 8))
                                                     ,result)
                                                (read-byte ,',stream)))
                                     (values ,result ,available))))))))
             ,@body))))))



(defmacro defun-with-reader-contexts (base-name lambda-list (in) &body body)
  `(progn
     ,@(with-standard-io-syntax
         (loop for cc in '(vector stream pointer)
               for w = (find-symbol (format nil "~a-~a-~a" 'with cc 'context)
                                    (find-package :3bz))
               for n = (intern (format nil "~a/~a" base-name cc)
                               (find-package :3bz))
               collect `(defun ,n ,lambda-list
                          (,w (,in)
                              (let ()
                                ,@body)))))
     (defun ,base-name ,lambda-list
       (etypecase ,in
         ,@(with-standard-io-syntax
             (loop for cc in '(vector stream pointer)
                   for ct = (find-symbol (format nil "~a-~a-~a" 'octet cc 'context)
                                         (find-package :3bz))
                   for n = (find-symbol (format nil "~a/~a" base-name cc)
                                        (find-package :3bz))
                   collect `(,ct (,n ,@lambda-list))))))))

(defmacro with-reader-contexts ((context) &body body)
  `(etypecase ,context
     (octet-vector-context
      (with-vector-context (,context)
        ,@body))
     (octet-pointer-context
      (with-pointer-context (,context)
        ,@body))
     (octet-stream-context
      (with-stream-context (,context)
        ,@body))))

