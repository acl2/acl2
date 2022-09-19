;;;; vectors.lisp -- signed/unsigned byte accessors

(cl:in-package :nibbles)

(declaim (inline array-data-and-offsets))
(defun array-data-and-offsets (v start end)
  "Like ARRAY-DISPLACEMENT, only more useful."
  #+cmu
  (lisp::with-array-data ((v v) (start start) (end end))
    (values v start end))
  #+sbcl
  (sb-kernel:with-array-data ((v v) (start start) (end end))
    (values v start end))
  #-(or cmu sbcl)
  (values v start (or end (length v))))

(macrolet ((define-fetcher (bitsize signedp big-endian-p)
             (let ((ref-name (byte-ref-fun-name bitsize signedp big-endian-p))
                   (bytes (truncate bitsize 8)))
               `(defun ,ref-name (vector index)
                  (declare (type octet-vector vector))
                  (declare (type (integer 0 ,(- array-dimension-limit bytes)) index))
                  (multiple-value-bind (vector start end)
                      (array-data-and-offsets vector index (+ index ,bytes))
                     #+sbcl (declare (optimize (sb-c::insert-array-bounds-checks 0)))
                     (declare (type (integer 0 ,(- array-dimension-limit bytes)) start))
                    (declare (ignore end))
                    ,(ref-form 'vector 'start bytes signedp big-endian-p)))))
           (define-storer (bitsize signedp big-endian-p)
             (let ((ref-name (byte-ref-fun-name bitsize signedp big-endian-p))
                   (set-name (byte-set-fun-name bitsize signedp big-endian-p))
                   (bytes (truncate bitsize 8)))
               `(progn
                 (defun ,set-name (vector index value)
                   (declare (type octet-vector vector))
                   (declare (type (integer 0 ,(- array-dimension-limit bytes)) index))
                   (declare (type (,(if signedp
                                        'signed-byte
                                        'unsigned-byte) ,bitsize) value))
                   (multiple-value-bind (vector start end)
                       (array-data-and-offsets vector index (+ index ,bytes))
                     #+sbcl (declare (optimize (sb-c::insert-array-bounds-checks 0)))
                     (declare (type (integer 0 ,(- array-dimension-limit bytes)) start))
                     (declare (ignore end))
                     ,(set-form 'vector 'start 'value bytes big-endian-p)))
                 (defsetf ,ref-name ,set-name))))
           (define-fetchers-and-storers (bitsize)
               (loop for i from 0 below 4
                     for signedp = (logbitp 1 i)
                     for big-endian-p = (logbitp 0 i)
                     collect `(define-fetcher ,bitsize ,signedp ,big-endian-p) into forms
                     collect `(define-storer ,bitsize ,signedp ,big-endian-p) into forms
                     finally (return `(progn ,@forms)))))
  (define-fetchers-and-storers 16)
  (define-fetchers-and-storers 32)
  (define-fetchers-and-storers 64))

#-(or abcl allegro ccl cmu lispworks sbcl)
(defun make-single-float (bits)
  (let ((exponent-bits (ldb (byte 8 23) bits)))
    (when (= exponent-bits 255)
      (error "infinities and NaNs are not supported"))
    (let ((sign (if (zerop (ldb (byte 1 31) bits)) 1f0 -1f0))
          (significand (logior (ldb (byte 23 0) bits) (if (zerop exponent-bits) 0 (ash 1 23))))
          (exponent (if (zerop exponent-bits) -126 (- exponent-bits 127))))
      (* sign (scale-float (float significand 1f0) (- exponent 23))))))

#-(or abcl allegro ccl cmu lispworks sbcl)
(defun make-double-float (high low)
  (let ((exponent-bits (ldb (byte 11 20) high)))
    (when (= exponent-bits 2047)
      (error "infinities and NaNs are not supported"))
    (let ((sign (if (zerop (ldb (byte 1 31) high)) 1d0 -1d0))
          (significand
            (logior low
                    (ash (ldb (byte 20 0) high) 32)
                    (if (zerop exponent-bits) 0 (ash 1 52))))
          (exponent (if (zerop exponent-bits) -1022 (- exponent-bits 1023))))
      (* sign (scale-float (float significand 1d0) (- exponent 52))))))

#-(or abcl allegro ccl cmu lispworks sbcl)
(defun single-float-bits (float)
  (multiple-value-bind (significand exponent sign)
      (decode-float float)
    (let ((sign-bit (if (plusp sign) 0 1))
          (exponent-bits (if (zerop significand) 0 (+ exponent 127 -1)))
          (significand-bits (floor (* #.(expt 2s0 24) significand))))
      (when (<= exponent-bits 0)
        (setf significand-bits (ash significand-bits (1- exponent-bits)))
        (setf exponent-bits 0))
      (logior (ash sign-bit 31) (ash exponent-bits 23) (ldb (byte 23 0) significand-bits)))))

#-(or abcl allegro ccl cmu lispworks sbcl)
(defun double-float-bits (float)
  (multiple-value-bind (significand exponent sign)
      (decode-float float)
    (let ((sign-bit (if (plusp sign) 0 1))
          (exponent-bits (if (zerop significand) 0 (+ exponent 1023 -1)))
          (significand-bits (floor (* #.(expt 2d0 53) significand))))
      (when (<= exponent-bits 0)
        (setf significand-bits (ash significand-bits (1- exponent-bits)))
        (setf exponent-bits 0))
      (values
       (logior (ash sign-bit 31) (ash exponent-bits 20) (ldb (byte 20 32) significand-bits))
       (ldb (byte 32 0) significand-bits)))))

#+sbcl (declaim (sb-ext:maybe-inline ieee-single-ref/be))
(defun ieee-single-ref/be (vector index)
  #+abcl
  (system::make-single-float (sb32ref/be vector index))
  #+allegro
  (let ((high (ub16ref/be vector index))
        (low (ub16ref/be vector (+ index 2))))
    (excl:shorts-to-single-float high low))
  #+ccl
  (ccl::host-single-float-from-unsigned-byte-32 (ub32ref/be vector index))
  #+cmu
  (kernel:make-single-float (sb32ref/be vector index))
  #+lispworks
  (let* ((ub (ub32ref/be vector index))
         (v (sys:make-typed-aref-vector 4)))
    (declare (optimize (speed 3) (float 0) (safety 0)))
    (declare (dynamic-extent v))
    (setf (sys:typed-aref '(unsigned-byte 32) v 0) ub)
    (sys:typed-aref 'single-float v 0))
  #+sbcl
  (sb-kernel:make-single-float (sb32ref/be vector index))
  #-(or abcl allegro ccl cmu lispworks sbcl)
  (make-single-float (ub32ref/be vector index)))

#+sbcl (declaim (sb-ext:maybe-inline ieee-single-sef/be))
(defun ieee-single-set/be (vector index value)
  #+abcl
  (progn
    (setf (sb32ref/be vector index) (system:single-float-bits value))
    value)
  #+allegro
  (multiple-value-bind (high low) (excl:single-float-to-shorts value)
    (setf (ub16ref/be vector index) high
          (ub16ref/be vector (+ index 2)) low)
    value)
  #+ccl
  (progn
    (setf (ub32ref/be vector index) (ccl::single-float-bits value))
    value)
  #+cmu
  (progn
    (setf (sb32ref/be vector index) (kernel:single-float-bits value))
    value)
  #+lispworks
  (let* ((v (sys:make-typed-aref-vector 4)))
    (declare (optimize (speed 3) (float 0) (safety 0)))
    (declare (dynamic-extent v))
    (setf (sys:typed-aref 'single-float v 0) value)
    (setf (ub32ref/be vector index) (sys:typed-aref '(unsigned-byte 32) v 0))
    value)
  #+sbcl
  (progn
    (setf (sb32ref/be vector index) (sb-kernel:single-float-bits value))
    value)
  #-(or abcl allegro ccl cmu lispworks sbcl)
  (progn
    (setf (ub32ref/be vector index) (single-float-bits value))
    value))
(defsetf ieee-single-ref/be ieee-single-set/be)

#+sbcl (declaim (sb-ext:maybe-inline ieee-single-ref/le))
(defun ieee-single-ref/le (vector index)
  #+abcl
  (system::make-single-float (sb32ref/le vector index))
  #+allegro
  (let ((low (ub16ref/le vector index))
        (high (ub16ref/le vector (+ index 2))))
    (excl:shorts-to-single-float high low))
  #+ccl
  (ccl::host-single-float-from-unsigned-byte-32 (ub32ref/le vector index))
  #+cmu
  (kernel:make-single-float (sb32ref/le vector index))
  #+lispworks
  (let* ((ub (ub32ref/le vector index))
         (v (sys:make-typed-aref-vector 4)))
    (declare (optimize (speed 3) (float 0) (safety 0)))
    (declare (dynamic-extent v))
    (setf (sys:typed-aref '(unsigned-byte 32) v 0) ub)
    (sys:typed-aref 'single-float v 0))
  #+sbcl
  (sb-kernel:make-single-float (sb32ref/le vector index))
  #-(or abcl allegro ccl cmu lispworks sbcl)
  (make-single-float (ub32ref/le vector index))
)

#+sbcl (declaim (sb-ext:maybe-inline ieee-single-set/le))
(defun ieee-single-set/le (vector index value)
  #+abcl
  (progn
    (setf (sb32ref/le vector index) (system:single-float-bits value))
    value)
  #+allegro
  (multiple-value-bind (high low) (excl:single-float-to-shorts value)
    (setf (ub16ref/le vector index) low
          (ub16ref/le vector (+ index 2)) high)
    value)
  #+ccl
  (progn
    (setf (ub32ref/le vector index) (ccl::single-float-bits value))
    value)
  #+cmu
  (progn
    (setf (sb32ref/le vector index) (kernel:single-float-bits value))
    value)
  #+lispworks
  (let* ((v (sys:make-typed-aref-vector 4)))
    (declare (optimize (speed 3) (float 0) (safety 0)))
    (declare (dynamic-extent v))
    (setf (sys:typed-aref 'single-float v 0) value)
    (setf (ub32ref/le vector index) (sys:typed-aref '(unsigned-byte 32) v 0))
    value)
  #+sbcl
  (progn
    (setf (sb32ref/le vector index) (sb-kernel:single-float-bits value))
    value)
  #-(or abcl allegro ccl cmu lispworks sbcl)
  (progn
    (setf (ub32ref/le vector index) (single-float-bits value))
    value))
(defsetf ieee-single-ref/le ieee-single-set/le)

#+sbcl (declaim (sb-ext:maybe-inline ieee-double-ref/be))
(defun ieee-double-ref/be (vector index)
  #+abcl
  (let ((upper (sb32ref/be vector index))
        (lower (ub32ref/be vector (+ index 4))))
    (system:make-double-float (logior (ash upper 32) lower)))
  #+allegro
  (let ((u3 (ub16ref/be vector index))
        (u2 (ub16ref/be vector (+ index 2)))
        (u1 (ub16ref/be vector (+ index 4)))
        (u0 (ub16ref/be vector (+ index 6))))
    (excl:shorts-to-double-float u3 u2 u1 u0))
  #+ccl
  (let ((upper (ub32ref/be vector index))
        (lower (ub32ref/be vector (+ index 4))))
    (ccl::double-float-from-bits upper lower))
  #+cmu
  (let ((upper (sb32ref/be vector index))
        (lower (ub32ref/be vector (+ index 4))))
    (kernel:make-double-float upper lower))
  #+lispworks
  (let* ((upper (ub32ref/be vector index))
         (lower (ub32ref/be vector (+ index 4)))
         (v (sys:make-typed-aref-vector 8)))
    (declare (optimize (speed 3) (float 0) (safety 0)))
    (declare (dynamic-extent v))
    #+little-endian
    (progn
      (setf (sys:typed-aref '(unsigned-byte 32) v 0) lower)
      (setf (sys:typed-aref '(unsigned-byte 32) v 4) upper))
    #-little-endian
    (progn
      (setf (sys:typed-aref '(unsigned-byte 32) v 0) upper)
      (setf (sys:typed-aref '(unsigned-byte 32) v 4) lower))
    (sys:typed-aref 'double-float v 0))
  #+sbcl
  (let ((upper (sb32ref/be vector index))
        (lower (ub32ref/be vector (+ index 4))))
    (sb-kernel:make-double-float upper lower))
  #-(or abcl allegro ccl cmu lispworks sbcl)
  (let ((high (nibbles:ub32ref/be vector index))
        (low (nibbles:ub32ref/be vector (+ index 4))))
    (make-double-float high low)))

#+sbcl (declaim (sb-ext:maybe-inline ieee-double-set/be))
(defun ieee-double-set/be (vector index value)
  #+abcl
  (progn
    (setf (ub32ref/be vector index) (system::double-float-high-bits value)
          (ub32ref/be vector (+ index 4)) (system::double-float-low-bits value))
    value)
  #+allegro
  (multiple-value-bind (us3 us2 us1 us0) (excl:double-float-to-shorts value)
    (setf (ub16ref/be vector index) us3
          (ub16ref/be vector (+ index 2)) us2
          (ub16ref/be vector (+ index 4)) us1
          (ub16ref/be vector (+ index 6)) us0)
    value)
  #+ccl
  (multiple-value-bind (high low) (ccl::double-float-bits value)
    (setf (ub32ref/be vector index) high
          (ub32ref/be vector (+ index 4)) low)
    value)
  #+cmu
  (progn
    (setf (sb32ref/be vector index) (kernel:double-float-high-bits value)
          (ub32ref/be vector (+ index 4)) (kernel:double-float-low-bits value))
    value)
  #+lispworks
  (let* ((v (sys:make-typed-aref-vector 8)))
    (declare (optimize (speed 3) (float 0) (safety 0)))
    (declare (dynamic-extent v))
    (setf (sys:typed-aref 'double-float v 0) value)
    #+little-endian
    (progn
      (setf (ub32ref/be vector index) (sys:typed-aref '(unsigned-byte 32) v 4)
            (ub32ref/be vector (+ index 4)) (sys:typed-aref '(unsigned-byte 32) v 0)))
    #-little-endian
    (progn
      (setf (ub32ref/be vector index) (sys:typed-aref '(unsigned-byte 32) v 0)
            (ub32ref/be vector (+ index 4)) (sys:typed-aref '(unsigned-byte 32) v 4)))
    value)
  #+sbcl
  (progn
    (setf (sb32ref/be vector index) (sb-kernel:double-float-high-bits value)
          (ub32ref/be vector (+ index 4)) (sb-kernel:double-float-low-bits value))
    value)
  #-(or abcl allegro ccl cmu lispworks sbcl)
  (multiple-value-bind (high low) (double-float-bits value)
    (setf (ub32ref/be vector index) high
          (ub32ref/be vector (+ index 4)) low)
    value))
(defsetf ieee-double-ref/be ieee-double-set/be)

#+sbcl (declaim (sb-ext:maybe-inline ieee-double-ref/le))
(defun ieee-double-ref/le (vector index)
  #+abcl
  (let ((lower (ub32ref/le vector index))
        (upper (sb32ref/le vector (+ index 4))))
    (system:make-double-float (logior (ash upper 32) lower)))
  #+allegro
  (let ((u0 (ub16ref/le vector index))
        (u1 (ub16ref/le vector (+ index 2)))
        (u2 (ub16ref/le vector (+ index 4)))
        (u3 (ub16ref/le vector (+ index 6))))
    (excl:shorts-to-double-float u3 u2 u1 u0))
  #+ccl
  (let ((lower (ub32ref/le vector index))
        (upper (ub32ref/le vector (+ index 4))))
    (ccl::double-float-from-bits upper lower))
  #+cmu
  (let ((lower (ub32ref/le vector index))
        (upper (sb32ref/le vector (+ index 4))))
    (kernel:make-double-float upper lower))
  #+lispworks
  (let* ((lower (ub32ref/le vector index))
         (upper (ub32ref/le vector (+ index 4)))
         (v (sys:make-typed-aref-vector 8)))
    (declare (optimize (speed 3) (float 0) (safety 0)))
    (declare (dynamic-extent v))
    #+little-endian
    (progn
      (setf (sys:typed-aref '(unsigned-byte 32) v 0) lower)
      (setf (sys:typed-aref '(unsigned-byte 32) v 4) upper))
    #-little-endian
    (progn
      (setf (sys:typed-aref '(unsigned-byte 32) v 0) upper)
      (setf (sys:typed-aref '(unsigned-byte 32) v 4) lower))
    (sys:typed-aref 'double-float v 0))
  #+sbcl
  (let ((lower (ub32ref/le vector index))
        (upper (sb32ref/le vector (+ index 4))))
    (sb-kernel:make-double-float upper lower))
  #-(or abcl allegro ccl cmu lispworks sbcl)
  (let ((low (nibbles:ub32ref/le vector index))
        (high (nibbles:ub32ref/le vector (+ index 4))))
    (make-double-float high low)))

#+sbcl (declaim (sb-ext:maybe-inline ieee-double-set/le))
(defun ieee-double-set/le (vector index value)
  #+abcl
  (progn
    (setf (ub32ref/le vector index) (system::double-float-low-bits value)
          (ub32ref/le vector (+ index 4)) (system::double-float-high-bits value))
    value)
  #+allegro
  (multiple-value-bind (us3 us2 us1 us0) (excl:double-float-to-shorts value)
    (setf (ub16ref/le vector index) us0
          (ub16ref/le vector (+ index 2)) us1
          (ub16ref/le vector (+ index 4)) us2
          (ub16ref/le vector (+ index 6)) us3)
    value)
  #+ccl
  (multiple-value-bind (high low) (ccl::double-float-bits value)
    (setf (ub32ref/le vector index) low
          (ub32ref/le vector (+ index 4)) high)
    value)
  #+cmu
  (progn
    (setf (ub32ref/le vector index) (kernel:double-float-low-bits value)
          (sb32ref/le vector (+ index 4)) (kernel:double-float-high-bits value))
    value)
  #+lispworks
  (let* ((v (sys:make-typed-aref-vector 8)))
    (declare (optimize (speed 3) (float 0) (safety 0)))
    (declare (dynamic-extent v))
    (setf (sys:typed-aref 'double-float v 0) value)
    #+little-endian
    (progn
      (setf (ub32ref/le vector index) (sys:typed-aref '(unsigned-byte 32) v 0)
            (ub32ref/le vector (+ index 4)) (sys:typed-aref '(unsigned-byte 32) v 4)))
    #-little-endian
    (progn
      (setf (ub32ref/le vector index) (sys:typed-aref '(unsigned-byte 32) v 4)
            (ub32ref/le vector (+ index 4)) (sys:typed-aref '(unsigned-byte 32) v 0)))
    value)
  #+sbcl
  (progn
    (setf (ub32ref/le vector index) (sb-kernel:double-float-low-bits value)
          (sb32ref/le vector (+ index 4)) (sb-kernel:double-float-high-bits value))
    value)
  #-(or abcl allegro ccl cmu lispworks sbcl)
  (multiple-value-bind (high low) (double-float-bits value)
    (setf (ub32ref/le vector index) low
          (ub32ref/le vector (+ index 4)) high)
    value))
(defsetf ieee-double-ref/le ieee-double-set/le)
