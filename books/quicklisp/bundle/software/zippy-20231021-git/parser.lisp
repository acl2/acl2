(in-package #:org.shirakumo.zippy)

(defvar *structures* (make-hash-table :test 'eql))

(defun decode-structure (vector index)
  (let* ((signature (nibbles:ub32ref/le vector index))
         (parser (or (gethash signature *structures*)
                     (error 'unknown-block-signature :signature signature))))
    (funcall (first parser) vector (+ index 4))))

(defun read-structure (stream)
  (let* ((signature (nibbles:read-ub32/le stream))
         (parser (or (gethash signature *structures*)
                     (error 'unknown-block-signature :signature signature))))
    (funcall (second parser) stream)))

(defun encode-structure (structure vector index)
  (let ((parser (or (gethash (type-of structure) *structures*)
                    (error 'unknown-structure-type :object structure))))
    (funcall (third parser) structure vector index)))

(defun write-structure (structure stream)
  (let ((parser (or (gethash (type-of structure) *structures*)
                    (error 'unknown-structure-type :object structure))))
    (funcall (fourth parser) structure stream)))

(defun integer-binary-type (integer)
  (cond ((<= integer #xFF) 'ub8)
        ((<= integer #xFFFF) 'ub16)
        ((<= integer #xFFFFFFFF) 'ub32)
        ((<= integer #xFFFFFFFFFFFFFFFF) 'ub64)
        (T (error 'integer-too-large))))

(defun binary-type-size (type)
  (ecase type
    (ub8 1)
    (ub16 2)
    (ub32 4)
    (ub64 8)))

(defun binary-type-type (type)
  (ecase type
    (ub8 '(unsigned-byte 8))
    (ub16 '(unsigned-byte 16))
    (ub32 '(unsigned-byte 32))
    (ub64 '(unsigned-byte 64))))

(defun binary-type-decoder (type)
  (ecase type
    (ub8 'aref)
    (ub16 'nibbles:ub16ref/le)
    (ub32 'nibbles:ub32ref/le)
    (ub64 'nibbles:ub64ref/le)))

(defun binary-type-reader (type)
  (ecase type
    (ub8 'read-byte)
    (ub16 'nibbles:read-ub16/le)
    (ub32 'nibbles:read-ub32/le)
    (ub64 'nibbles:read-ub64/le)))

(defun binary-type-encoder (type)
  (ecase type
    (ub8 '(lambda (vector index value)
            (setf (aref vector index) value)))
    (ub16 '(lambda (vector index value)
             (setf (nibbles::ub16ref/le vector index) value)))
    (ub32 '(lambda (vector index value)
             (setf (nibbles::ub32ref/le vector index) value)))
    (ub64 '(lambda (vector index value)
             (setf (nibbles::ub64ref/le vector index) value)))))

(defun binary-type-writer (type)
  (ecase type
    (ub8 'write-byte)
    (ub16 'nibbles:write-ub16/le)
    (ub32 'nibbles:write-ub32/le)
    (ub64 'nibbles:write-ub64/le)))

(defun generate-record-decoder (record vector index)
  (destructuring-bind (name type &optional count) record
    (cond ((typep type 'integer)
           (let ((btype (integer-binary-type type)))
             `(progn
                (decf size ,(binary-type-size btype))
                (setf ,name (,(binary-type-decoder btype) ,vector ,index))
                (incf ,index ,(binary-type-size btype))
                (unless (= ,type ,name)
                  (error 'mismatched-type-signature :signature ,name)))))
          (count
           `(progn
              (setf ,name (make-array ,count :element-type ',(binary-type-type type)))
              (decf size (* (length ,name) ,(binary-type-size type)))
              (loop for i from 0 below (length ,name)
                    do (setf (aref ,name i) (,(binary-type-decoder type) ,vector ,index))
                       (incf ,index ,(binary-type-size type)))))
          (T
           `(progn
              (decf size ,(binary-type-size type))
              (setf ,name (,(binary-type-decoder type) ,vector ,index))
              (incf ,index ,(binary-type-size type)))))))

(defun generate-record-reader (record stream)
  (destructuring-bind (name type &optional count) record
    (cond ((typep type 'integer)
           (let ((btype (integer-binary-type type)))
             `(progn
                (setf ,name (,(binary-type-reader btype) ,stream))
                (unless (= ,type ,name)
                  (error 'mismatched-type-signature :signature ,name)))))
          (count
           `(progn
              (setf ,name (make-array ,count :element-type ',(binary-type-type type)))
              (loop for i from 0 below (length ,name)
                    do (setf (aref ,name i) (,(binary-type-reader type) ,stream)))))
          (T
           `(setf ,name (,(binary-type-reader type) ,stream))))))

(defun generate-record-encoder (record vector index)
  (destructuring-bind (name type &optional count) record
    (cond ((typep type 'integer)
           (let ((btype (integer-binary-type type)))
             `(progn (,(binary-type-encoder btype) ,vector ,index ,type)
                     (incf ,index ,(binary-type-size btype)))))
          (count
           (if (eql type 'character)
               `(let ((vec (babel:string-to-octets ,name :encoding :utf-8)))
                  (loop for char across vec
                        do (setf (aref ,vector ,index) char)
                           (incf ,index)
                        finally (return ,index)))
               `(loop for i from 0 below ,count
                      do (,(binary-type-encoder type) ,vector ,index (aref ,name i))
                         (incf ,index ,(binary-type-size type))
                      finally (return ,index))))
          (T
           `(progn (,(binary-type-encoder type) ,vector ,index ,name)
                   (incf ,index ,(binary-type-size type)))))))

(defun generate-record-writer (record stream)
  (destructuring-bind (name type &optional count) record
    (cond ((typep type 'integer)
           (let ((btype (integer-binary-type type)))
             `(,(binary-type-writer btype) ,type ,stream)))
          (count
           (if (eql type 'character)
               `(let ((vec (babel:string-to-octets ,name :encoding :utf-8)))
                  (loop for char across vec
                        do (write-byte char ,stream)))
               `(loop for i from 0 below ,count
                      do (,(binary-type-writer type) (aref ,name i) ,stream))))
          (T
           `(,(binary-type-writer type) ,name ,stream)))))

(defmacro define-byte-structure (name &body records)
  (destructuring-bind (name signature) (if (listp name) name (list name NIL))
    (let ((fields (mapcar #'first records))
          (constructor (intern (format NIL "~a-~a" 'make name)))
          (decode-name (intern (format NIL "~a-~a" 'decode name)))
          (read-name (intern (format NIL "~a-~a" 'read name)))
          (encode-name (intern (format NIL "~a-~a" 'encode name)))
          (write-name (intern (format NIL "~a-~a" 'write name))))
      `(progn
         (defstruct (,name (:constructor ,constructor ,fields))
           ,@fields)
         (defun ,decode-name (vector index &optional (size most-positive-fixnum))
           (let ,(remove 'size fields)
             (block NIL
               ,@(loop for record in records
                       collect `(when (<= size 0) (return))
                       collect (generate-record-decoder record 'vector 'index)))
             (values (,constructor ,@fields) index)))
         (defun ,read-name (stream)
           (let ,fields
             ,@(loop for record in records
                     collect (generate-record-reader record 'stream))
             (,constructor ,@fields)))
         (defun ,encode-name (structure vector index)
           ,@(typecase signature
               ((unsigned-byte 16)
                `((setf (nibbles:ub16ref/le vector index) ,signature)
                  (incf index 2)))
               ((unsigned-byte 32)
                `((setf (nibbles:ub32ref/le vector index) ,signature)
                  (incf index 4))))
           (with-slots ,fields structure
             ,@(loop for record in records
                     collect (generate-record-encoder record 'vector 'index))))
         (defun ,write-name (structure stream)
           ,@(typecase signature
               ((unsigned-byte 16)
                `((nibbles:write-ub16/le ,signature stream)))
               ((unsigned-byte 32)
                `((nibbles:write-ub32/le ,signature stream))))
           (with-slots ,fields structure
             ,@(loop for record in records
                     collect (generate-record-writer record 'stream))))
         ,@(when signature
             `((setf (gethash ',name *structures*)
                     (setf (gethash ,signature *structures*)
                           (list #',decode-name #',read-name #',encode-name #',write-name)))))))))

(defun decode-string (octets flags)
  (babel:octets-to-string octets :encoding (if (logbitp 11 flags) :utf-8 :cp437)))

(defun encode-string (string)
  (if string
      (babel:string-to-octets string :encoding :utf-8)
      #()))

(defun decode-msdos-timestamp (date time)
  (let ((yy (ldb (byte 7 9) date))
        (mm (ldb (byte 4 5) date))
        (dd (ldb (byte 5 0) date))
        (h (ldb (byte 5 11) time))
        (m (ldb (byte 6 5) time))
        (s (ldb (byte 5 0) time)))
    (flet ((clamp (l x h)
             (min h (max l x))))
      (encode-universal-time (clamp 0 (1+ (* 2 s)) 59) (clamp 0 (1- m) 59) (clamp 0 (1- h) 23) (clamp 1 dd 31) (clamp 1 mm 12) (+ 1980 yy) NIL))))

(defun encode-msdos-timestamp (timestamp)
  (multiple-value-bind (s m h dd mm yy) (decode-universal-time timestamp NIL)
    (let ((date 0)
          (time 0))
      (setf (ldb (byte 7 9) date) (- yy 1980))
      (setf (ldb (byte 4 5) date) mm)
      (setf (ldb (byte 5 0) date) dd)
      (setf (ldb (byte 5 11) time) (1+ h))
      (setf (ldb (byte 6 5) time) (1+ m))
      (setf (ldb (byte 5 0) time) (floor s 2))
      (values date time))))

(defun decode-version (version)
  (multiple-value-bind (major minor) (floor (ldb (byte 8 0) version) 10)
    (list major minor)))

(defun encode-version (version &optional compatibility)
  (check-type version (cons (integer 0 9) (cons (integer 0 9) null)))
  (let ((idx (etypecase compatibility
               (null 0)
               (integer compatibility)
               (keyword (file-attribute-id compatibility))))
        (int (+ (* 10 (first version)) (second version))))
    (setf (ldb (byte 8 8) int) idx)
    int))

(defun decode-file-attribute (compat attr)
  (let ((compat (file-attribute-name compat))
        (msdos (ldb (byte 8 0) attr))
        (os-specific (ldb (byte 16 16) attr)))
    (list (file-attributes:decode-attributes msdos :windows) compat os-specific)))

(defun encode-file-attribute (thing)
  (destructuring-bind (msdos compat os-specific) thing
    (declare (ignore compat))
    (let ((i 0))
      (setf (ldb (byte 8 0) i) (logand #xFF (file-attributes:encode-attributes msdos :windows)))
      (setf (ldb (byte 16 16) i) (logand #xFFFF os-specific))
      i)))
