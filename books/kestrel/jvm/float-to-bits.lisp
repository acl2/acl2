; Converting a float to bits -- Experimental!
;
; Copyright (C) 2017-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: Experimental !  May not be right

;; TODO: Rewrite this carefuly and cleanly
;; TODO: Prove inversion with parse-float and parse-double (from class-file-parser.lisp)

(include-book "floats")

(encapsulate ()
  (local (include-book "rtl/rel9/support/support/float" :dir :system))

; from rtl/rel9
  (defund acl2::expo (x)
    (declare (xargs :guard t
                    :measure (:? x)))
    (cond ((or (not (rationalp x)) (equal x 0)) 0)
          ((< x 0) (acl2::expo (- x)))
          ((< x 1) (1- (acl2::expo (* 2 x))))
          ((< x 2) 0)
          (t (1+ (acl2::expo (/ x 2))))))

; from rtl/rel9
  (defund acl2::sig (x)
    (declare (xargs :guard t))
    (if (rationalp x)
        (if (< x 0)
            (- (* x (expt 2 (- (acl2::expo x)))))
          (* x (expt 2 (- (acl2::expo x)))))
      0)))

;;TODO: Check this
(defund float-to-bits (float)
  (declare (xargs :guard (jvm::java-floatp float)
                  :verify-guards nil
                  ))
  (if (equal float jvm::*float-infinity*)
      #x7f800000
    (if (equal float jvm::*float-negative-infinity*)
        #xff800000
      (if (equal float jvm::*float-NaN*)
          #x7f800001 ;; TODO: check.  I just picked a NaN
        (let* ((sign (cadr float))
               (val (caddr float))
               (sign-bit (if (eq :pos sign) 0 1)))
          (if (eql 0 val)
              ;; special case for +0 and -0
              (bvcat 1 sign-bit
                     31 (bvcat 8 0 23 0))
            (let* ((exponent (acl2::expo val))
                   (biased-exponent (+ 127 exponent))
                   (mantissa (sig val))
                   (mantissa-bits (- (* mantissa (expt 2 23)) (expt 2 23)))
                   )
              (bvcat 1 sign-bit
                     31 (bvcat 8 biased-exponent
                               23 mantissa-bits)))))))))

;TODO: Make a -tests book
;(include-book "class-file-parser") ;for parse-float (for tests)
;(parse-float (FLOAT-TO-BITS jvm::*float-nan*))
;(parse-float (FLOAT-TO-BITS jvm::*float-negative-infinity*))
;(parse-float (FLOAT-TO-BITS jvm::*float-infinity*))
;(parse-float (FLOAT-TO-BITS (jvm::make-regular-float :neg 7/2)))
;(parse-float (FLOAT-TO-BITS (jvm::make-regular-float :pos 7/2)))
;(parse-float (FLOAT-TO-BITS (jvm::make-regular-float :neg 8)))
;(parse-float (FLOAT-TO-BITS (jvm::make-regular-float :pos 8)))
;(parse-float (FLOAT-TO-BITS (jvm::make-regular-float :pos 0)))
;(parse-float (FLOAT-TO-BITS (jvm::make-regular-float :neg 0)))

(defund double-to-bits (double)
  (declare (xargs :guard (jvm::java-doublep double)
                  :verify-guards nil
                  ))
  (if (equal double jvm::*double-infinity*)
      #x7ff0000000000000
    (if (equal double jvm::*double-negative-infinity*)
        #xfff0000000000000
      (if (equal double jvm::*double-NaN*)
          #x7ff0000000000001 ;; TODO: check.  I just picked a NaN
        (let* ((sign (cadr double))
               (val (caddr double))
               (sign-bit (if (eq :pos sign) 0 1)))
          (if (eql 0 val)
              ;; special case for +0 and -0
              (bvcat 1 sign-bit
                     63 (bvcat 11 0 52 0))
            (let* ((exponent (acl2::expo val))
                   (biased-exponent (+ 1023 exponent))
                   (mantissa (sig val))
                   (mantissa-bits (- (* mantissa (expt 2 52)) (expt 2 52)))
                   )
              (bvcat 1 sign-bit
                     63 (bvcat 11 biased-exponent
                               52 mantissa-bits)))))))))

;(parse-double (DOUBLE-TO-BITS jvm::*double-nan*))
;(parse-double (DOUBLE-TO-BITS jvm::*double-negative-infinity*))
;(parse-double (DOUBLE-TO-BITS jvm::*double-infinity*))
;(parse-double (DOUBLE-TO-BITS (jvm::make-regular-double :neg 7/2)))
;(parse-double (DOUBLE-TO-BITS (jvm::make-regular-double :pos 7/2)))
;(parse-double (DOUBLE-TO-BITS (jvm::make-regular-double :neg 8)))
;(parse-double (DOUBLE-TO-BITS (jvm::make-regular-double :pos 8)))
;(parse-double (DOUBLE-TO-BITS (jvm::make-regular-double :pos 0)))
;(parse-double (DOUBLE-TO-BITS (jvm::make-regular-double :neg 0)))
