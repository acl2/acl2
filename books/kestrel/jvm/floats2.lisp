; Java floats as bit-vectors -- Experimental!
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

;; STATUS: Experimental !

;; Representation of Java floats as bit-vectors (essentially IEEE 754 format,
;; except for different treatment of NaNs).

;; For now, we do not support the float extended-exponent value set or the
;; double extended-exponent value set.

;; TODO: Put this in when stable

(include-book "kestrel/bv/getbit-def" :dir :system)

;; An IEEE float (of the size used by Java) is just a bit-vector of size 32.
(defun ieee-floatp (f)
  (declare (xargs :guard t))
  (unsigned-byte-p 32 f))

;; An IEEE double (of the size used by Java) is just a bit-vector of size 64.
(defun ieee-doublep (d)
  (declare (xargs :guard t))
  (unsigned-byte-p 64 d))

;; These are constants so that we don't mistype the keyword by accident.
(defconst *float-nan* :float-NaN) ;; "not a number"
(defconst *float-infinity* :float-infinity)
(defconst *float-negative-infinity* :float-negative-infinity)
(defconst *float-zero* :float-zero)
(defconst *float-negative-zero* :float-negative-zero)

;; See the binary32 format in Tables 3.2 and 3.5 in IEEE 754.
(defconst *float-w* 8) ;number of exponent bits
(defconst *float-p* 24) ;number of significand bits
(defconst *float-emax* 127) ;(- (expt 2 (- *float-w* 1)) 1)
(defconst *float-bias* 127) ;(- (expt 2 (- *float-w* 1)) 1)
(defconst *float-emin* (- 1 *float-emax*))

;; Decode an IEEE float, giving a non-zero rational number or one of the five
;;special values.  TODO remove this and related stuff from the JVM package.
;; TODO: Compare to parse-float in class-file-parser.lisp
(defun decode-ieee-float (f)
  (declare (xargs :guard (ieee-floatp f)))
  (let ((sign (acl2::getbit 31 f)) ;sign bit
        (e (acl2::slice 30 23 f))    ;biased exponent
        (sig (acl2::bvchop 23 f)) ;trailing significand bits
        )
    (if (= e (+ (expt 2 8) -1)) ;all ones for exponent
        (if (= 0 sig)
            ;; an infinity:
            (if (= 1 sign)
                *float-negative-infinity*
              *float-infinity*)
          ;; a NaN:
          *float-nan*)
      (if (= e 0)
          (if (= sig 0)
              ;; a signed zero:
              (if (= 1 sign)
                  *float-negative-zero*
                *float-zero*)
            ;;subnormal number:
            (let ((val (* (expt 2 *float-emin*) (expt 2 (- 1 *float-p*)) sig)))
              (if (= 0 sign)
                  val
                (- val))))
        ;;normal case:
        (let ((val (* (expt 2 (- e *float-bias*)) (+ 1 (expt 2 (- 1 *float-p*)) sig))))
          (if (= 0 sign)
              val
            (- val)))))))

;; This is the single value that represents floating point NaNs in our model.
;; This is consistent with what the library method floatToIntBits does. TODO:
;; Need to change the parsing functions in the class-file-parser to use this.
(defconst *java-float-nan* #x7fc00000)

;; We represent floats bit-vectors of size 32.
;; TODO: We now need to tag any float values in parsed LDC instructions.
(defun java-floatp (f)
  (declare (xargs :guard t))
  (and (ieee-floatp f)
       (let ((val (decode-ieee-float f)))
         ;; The Java floats are the same as the IEEE floats except the
         ;; only allowed NaN is *java-float-nan*
         (if (eq *float-nan* val)
             (eql f *java-float-nan*)
           t))))

;TODO: Prove some more validation theorems.
(defthm ieee-floatp-when-java-floatp
  (implies (java-floatp f)
           (ieee-floatp f)))

(defun float-zerop (f)
  (declare (xargs :guard t))
  (or (eq *float-zero* f)
      (eq *float-negative-zero* f)))

;; Floating point "less than"
(defund float< (x y)
  (declare (xargs :guard (and (java-floatp x)
                              (java-floatp y))
                  :guard-hints (("Goal" :in-theory (enable java-floatp)))))
  (let* ((x (decode-ieee-float x))
         (x (if (float-zerop x) 0 x))
         (y (decode-ieee-float y))
         (y (if (float-zerop y) 0 y)))
    (if (or (eq *float-NaN* x)
            (eq *float-NaN* y))
        ;; If either is a NaN, the comparison returns false (2.3.2):
        nil
      (if (eq x *float-negative-infinity*)
          ;; If x is negative infinity, it's less than y unless y is also negative infinity
          (not (eq y *float-negative-infinity*))
        (if (eq x *float-infinity*)
            ;; infinity is never less than anything
            nil
          ;; x must be a regular float
          (if (eq y *float-negative-infinity*)
              ;; Nothing is less than negative infinity
              nil
            (if (eq y *float-infinity*)
                ;; Any regular value is less than infinity
                t
              (< x y))))))))

;; Floating point "greater than"
;; Let's try to leave this one enabled
(defun float> (x y)
  (declare (xargs :guard (and (java-floatp x)
                              (java-floatp y))))
  (float< y x))

;; Floating point equality
(defund float= (x y)
  (declare (xargs :guard (and (java-floatp x)
                              (java-floatp y))
                  :guard-hints (("Goal" :in-theory (enable java-floatp)))))
  (let* ((x (decode-ieee-float x))
         (x (if (float-zerop x) 0 x))
         (y (decode-ieee-float y))
         (y (if (float-zerop y) 0 y)))
    (if (or (eq *float-NaN* x)
            (eq *float-NaN* y))
        ;; If either is a NaN, the equality returns false (2.3.2):
        nil
      (if (eq x *float-negative-infinity*)
          ;; If x is negative infinity, it's only equal to y if y is also negative infinity
          (eq y *float-negative-infinity*)
        (if (eq x *float-infinity*)
            ;; If x is infinity, it's only equal to y if y is also infinity
            (eq y *float-infinity*)
          ;; x must be a regular float, so y must also be a regular float, and the values must be equal
          (and (rationalp y)
               (equal x y)))))))
