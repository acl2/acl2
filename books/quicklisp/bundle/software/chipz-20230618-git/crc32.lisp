;;;; crc32.lisp -- implementation of the CRC32 checksum

(in-package :chipz)

#+sbcl
(progn
(defstruct (crc32
             (:copier copy-crc32))
  (crc #xffffffff :type (unsigned-byte 32)))

(defun update-crc32 (state vector start end)
  (declare (type simple-octet-vector vector))
  (declare (type index start end))
  (do ((crc (crc32-crc state))
       (i start (1+ i))
       (table +crc32-table+))
      ((>= i end)
       (setf (crc32-crc state) crc)
       state)
    (declare (type (unsigned-byte 32) crc))
    (setf crc (logxor (aref table
                            (logand (logxor crc (aref vector i)) #xff))
                      (ash crc -8)))))

(defun produce-crc32 (state)
  (logxor #xffffffff (crc32-crc state)))
)

;; An implementation that conses significantly less on most
;; implementations.  Credit to Zach Beane.
#-sbcl
(progn
(defstruct (crc32
             (:copier copy-crc32))
  (low #xffff)
  (high #xffff))

(defun crc32-table ()
  (let ((table (make-array 512 :element-type '(unsigned-byte 16))))
    (dotimes (n 256 table)
      (let ((c n))
        (declare (type (unsigned-byte 32) c))
        (dotimes (k 8)
          (if (logbitp 0 c)
              (setf c (logxor #xEDB88320 (ash c -1)))
              (setf c (ash c -1)))
          (setf (aref table (ash n 1)) (ldb (byte 16 16) c)
                (aref table (1+ (ash n 1))) (ldb (byte 16 0) c)))))))

(defvar *crc32-table* (crc32-table))

(defun crc32 (high low buf start count)
  (declare (type (unsigned-byte 16) high low)
           (type index start count)
           (type simple-octet-vector buf)
           (optimize speed))
  (let ((i start)
        (table *crc32-table*))
    (declare (type index i)
             (type (simple-array (unsigned-byte 16) (*)) table))
    (dotimes (j count (values high low))
      (let ((index (logxor (logand low #xFF) (aref buf i))))
        (declare (type (integer 0 255) index))
        (let ((high-index (ash index 1))
              (low-index (1+ (ash index 1))))
          (declare (type (integer 0 511) high-index low-index))
          (let ((t-high (aref table high-index))
                (t-low (aref table low-index)))
            (declare (type (unsigned-byte 16) t-high t-low))
            (incf i)
            (setf low (logxor (ash (logand high #xFF) 8)
                              (ash low -8)
                              t-low))
            (setf high (logxor (ash high -8) t-high))))))))

(defun update-crc32 (state vector start end)
  ;; ABCL used to miscompile (SETF (VALUES (ACCESSOR ...) ...) ...)
  ;; in case you were wondering why we take this route.
  (multiple-value-bind (high low) (crc32 (crc32-high state) (crc32-low state)
                                         vector start (- end start))
    (setf (crc32-high state) high
          (crc32-low state) low)
    (values high low)))

(defun produce-crc32 (state)
  (+ (ash (logxor (crc32-high state) #xFFFF) 16)
     (logxor (crc32-low state) #xFFFF)))
)
