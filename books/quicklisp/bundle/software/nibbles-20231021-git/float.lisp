;;;; float.lisp -- convert between IEEE floating point numbers and bits

(cl:in-package :nibbles)

(defun make-single-float (bits)
  (let ((exponent-bits (ldb (byte 8 23) bits)))
    (when (= exponent-bits 255)
      (error "infinities and NaNs are not supported"))
    (let ((sign (if (zerop (ldb (byte 1 31) bits)) 1f0 -1f0))
          (significand (logior (ldb (byte 23 0) bits) (if (zerop exponent-bits) 0 (ash 1 23))))
          (exponent (if (zerop exponent-bits) -126 (- exponent-bits 127))))
      (* sign (scale-float (float significand 1f0) (- exponent 23))))))

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
