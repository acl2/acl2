; A partial formalization of Java floating point values
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

(include-book "kestrel/bv/bvshl-def" :dir :system)
(include-book "kestrel/bv/bvshr-def" :dir :system)
(include-book "kestrel/bv/defs-bitwise" :dir :system)
(include-book "ihs/basic-definitions" :dir :system) ;for logext
(local (include-book "kestrel/bv/bvshr" :dir :system))
(local (include-book "kestrel/bv/bvor" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

;; NOTE: This formalization does not handle rounding and models most floats as
;; infinite-precition rational numbers.

;; TODO: Add rounding!

;;
;; Floats
;;

;;For now, floats and doubles are represented as exact rational
;;numbers (or infinities or NaNs).

;; Representation of floating-point infinities and NaNs: (We use these
;; constants to avoid typos in typing these keywords.)
(defconst *float-nan* :float-NaN)
(defconst *float-infinity* :float-infinity)
(defconst *float-negative-infinity* :float-negative-infinity)

;We model the sign of a floating point number as either :pos or :neg
(defun float-signp (sign)
  (declare (xargs :guard t))
  (or (eq sign :pos)
      (eq sign :neg)))

;; Recognize a java-float, which (for now) is either NaN, an infinity, or a
;; pair of :float and a rational number (for now, these have infinite
;; precision).
(defund java-floatp (float) ;todo: remove java- from name?
  (declare (xargs :guard t))
  (or (eq float *float-nan*)
      (eq float *float-infinity*)
      (eq float *float-negative-infinity*)
      ;; A "regular float" is a float that is not an infinity or a NaN.  For
      ;; now, we represent a regular float as (:float <sign> <rat>) where rat
      ;; is a rational number with infinite precision.  FIXME: We need to add
      ;; support for rounding and restrict this to the set of representable
      ;; numbers.
      (and (true-listp float)
           (eql 3 (len float))
           (eq :float (car float))
           (float-signp (cadr float))
           (rationalp (caddr float))
           ;; non-negative since the sign bit is separate:
           (<= 0 (caddr float)))))

(defund regular-floatp (float)
  (declare (xargs :guard (java-floatp float)))
  (consp float)) ;given that we know it's a float, we can just check consp (all non-regular float are atoms)

(defund float-infinitep (float)
  (declare (xargs :guard (java-floatp float)))
  (or (eq float *float-negative-infinity*)
      (eq float *float-infinity*)))



;; Test whether a float is NaN
(defund float-nanp (float)
  (declare (xargs :guard (java-floatp float)))
  (eq float *float-NaN*))

;; Needed to distinguish constant values (e.g., in LDC)
(defthm floats-are-not-bvs
  (not (and (java-floatp val)
            (unsigned-byte-p n val)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable java-floatp))))

(defund make-regular-float (sign val)
  (declare (xargs :guard (and (float-signp sign)
                              (rationalp val)
                              (<= 0 val))))
  `(:float ,sign ,val))

;; Extract the sign (:pos or :neg)
(defun regular-float-sign (float)
  (declare (xargs :guard (and (java-floatp float)
                              (regular-floatp float))
                  :guard-hints (("Goal" :in-theory (enable regular-floatp java-floatp)))))
  (cadr float))

;; Extract the rational (without the sign, so this will always be non-negative)
(defun regular-float-rat (float)
  (declare (xargs :guard (and (java-floatp float)
                              (regular-floatp float))
                  :guard-hints (("Goal" :in-theory (enable regular-floatp java-floatp)))))
  (caddr float))

;; The value represented by a regular float
(defund regular-float-value (float)
  (declare (xargs :guard (and (java-floatp float)
                              (regular-floatp float))
                  :guard-hints (("Goal" :in-theory (enable regular-floatp java-floatp)))))
  (let ((sign (cadr float))
        (val (caddr float)))
    (* (if (eq :pos sign) 1 -1) val)))

;; Recognizes positive zero and negative zero
(defund float-zerop (float)
  (declare (xargs :guard (java-floatp float)))
  (and (regular-floatp float)
       (eql 0 (regular-float-rat float))))

(defthm rationalp-of-regular-float-value
  (implies (and (java-floatp f)
                (regular-floatp f))
           (rationalp (regular-float-value f)))
  :hints (("Goal" :in-theory (enable java-floatp regular-floatp regular-float-value))))

;; Floating point <
(defund float< (x y)
  (declare (xargs :guard (and (java-floatp x)
                              (java-floatp y))
                  :guard-hints (("Goal" :in-theory (enable JAVA-FLOATP regular-FLOATP)))))
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
            ;; x and y are both regular floats, so compare the values
            (< (regular-float-value x) (regular-float-value y))))))))

;; Floating point equality
(defund float= (x y)
  (declare (xargs :guard (and (java-floatp x)
                              (java-floatp y))
                  :guard-hints (("Goal" :in-theory (enable JAVA-FLOATP regular-FLOATP)))))
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
        (and (regular-floatp y)
             (equal (regular-float-value x) (regular-float-value y)))))))

;; Floating point >
;; Let's try to leave this one enabled
(defun float> (x y)
  (declare (xargs :guard (and (java-floatp x)
                              (java-floatp y))))
  (float< y x))

;;
;; Doubles (analogous to floats, see the comments for floats)
;;

;; We use these constants to avoid typos in typing these keywords:
(defconst *double-nan* :double-NaN)
(defconst *double-infinity* :double-infinity)
(defconst *double-negative-infinity* :double-negative-infinity)

(defund java-doublep (double)
  (declare (xargs :guard t))
  (or (eq double *double-NaN*)
      (eq double *double-infinity*)
      (eq double *double-negative-infinity*)
      (and (true-listp double)
           (eql 3 (len double))
           (eq :double (car double))
           (float-signp (cadr double))
           (rationalp (caddr double))
           (<= 0 (caddr double)))))

(defund regular-doublep (double)
  (declare (xargs :guard (java-doublep double)))
  (consp double))

;; Test whether a double is NaN
(defund double-nanp (double)
  (declare (xargs :guard (java-doublep double)))
  (eq double *double-NaN*))

;; Needed to distinguish constant values (e.g., in LDC)
(defthm doubles-are-not-bvs
  (not (and (java-doublep val)
            (unsigned-byte-p n val)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable java-doublep))))

(defund make-regular-double (sign val)
  (declare (xargs :guard (and (float-signp sign)
                              (rationalp val)
                              (<= 0 val))))
  `(:double ,sign ,val))

;; Extract the sign (:pos or :neg)
(defun regular-double-sign (double)
  (declare (xargs :guard (and (java-doublep double)
                              (regular-doublep double))
                  :guard-hints (("Goal" :in-theory (enable regular-doublep java-doublep)))))
  (cadr double))

;; Extract the rational (without the sign, so this will always be non-negative)
(defun regular-double-rat (double)
  (declare (xargs :guard (and (java-doublep double)
                              (regular-doublep double))
                  :guard-hints (("Goal" :in-theory (enable regular-doublep java-doublep)))))
  (caddr double))

(defund regular-double-value (double)
  (declare (xargs :guard (and (java-doublep double)
                              (regular-doublep double))
                  :guard-hints (("Goal" :in-theory (enable regular-doublep java-doublep)))))
  (let ((sign (cadr double))
        (val (caddr double)))
    (* (if (eq :pos sign) 1 -1) val)))

(defthm rationalp-of-regular-double-value
  (implies (and (java-doublep f)
                (regular-doublep f))
           (rationalp (regular-double-value f)))
  :hints (("Goal" :in-theory (enable java-doublep regular-doublep regular-double-value))))

;; Double-precision floating point <
(defund double< (x y)
  (declare (xargs :guard (and (java-doublep x)
                              (java-doublep y))
                  :guard-hints (("Goal" :in-theory (enable JAVA-DOUBLEP regular-DOUBLEP)))))
  (if (or (eq *double-NaN* x)
          (eq *double-NaN* y))
      ;; If either is a NaN, the comparison returns false (2.3.2):
      nil
    (if (eq x *double-negative-infinity*)
        ;; If x is negative infinity, it's less than y unless y is also negative infinity
        (not (eq y *double-negative-infinity*))
      (if (eq x *double-infinity*)
          ;; infinity is never less than anything
          nil
        ;; x must be a regular double
        (if (eq y *double-negative-infinity*)
            ;; Nothing is less than negative infinity
            nil
          (if (eq y *double-infinity*)
              ;; Any regular value is less than infinity
              t
            ;; x and y are both regular doubles, so compare the values
            (< (regular-double-value x) (regular-double-value y))))))))

;; Double-precision floating point equality
(defund double= (x y)
  (declare (xargs :guard (and (java-doublep x)
                              (java-doublep y))
                  :guard-hints (("Goal" :in-theory (enable JAVA-DOUBLEP regular-DOUBLEP)))))
  (if (or (eq *double-NaN* x)
          (eq *double-NaN* y))
      ;; If either is a NaN, the equality returns false (2.3.2):
      nil
    (if (eq x *double-negative-infinity*)
        ;; If x is negative infinity, it's only equal to y if y is also negative infinity
        (eq y *double-negative-infinity*)
      (if (eq x *double-infinity*)
          ;; If x is infinity, it's only equal to y if y is also infinity
          (eq y *double-infinity*)
        ;; x must be a regular double, so y must also be a regular double, and the values must be equal
        (and (regular-doublep y)
             (equal (regular-double-value x) (regular-double-value y)))))))

;; Double-precision floating point >
;; Let's try to leave this one enabled
(defun double> (x y)
  (declare (xargs :guard (and (java-doublep x)
                              (java-doublep y))))
  (double< y x))

;;; Conversions:

;; Convert double to float
;;TTTODO: Here and many other places we should round / chop and deal with over/underflow
(defun d2f (d)
  (declare (xargs :guard (java-doublep d)
                  :guard-hints (("Goal" :in-theory (enable java-doublep)))))
  (if (eq d *double-nan*)
      *float-nan*
    (if (eq d *double-infinity*)
        *float-infinity*
      (if (eq d *double-negative-infinity*)
          *float-negative-infinity*
        (let ((sign (regular-double-sign d))
              (rat (regular-double-rat d)))
          (make-regular-float sign rat))))))


(defconst *max-signed-int32* (+ -1 (expt 2 31)))
(defconst *min-signed-int32* (acl2::bvchop 32 (- (expt 2 31))))

(defconst *max-signed-int64* (+ -1 (expt 2 63)))
(defconst *min-signed-int64* (acl2::bvchop 64 (- (expt 2 63))))


;convert double to int
;;TODO: Do this right
(defun d2i (d)
  (declare (xargs :guard (java-doublep d)
                  :guard-hints (("Goal" :in-theory (enable java-doublep regular-doublep)))))
  (if (eq *double-nan* d)
      0 ;(encode-signed 0) ;as prescribed by the JVM spec
    (if (eq *double-infinity* d)
        *max-signed-int32*
      (if (eq *double-negative-infinity* d)
          *min-signed-int32*
        (let* ((val (regular-double-value d))
               (int-val (floor val 1)))
          (if (> int-val (acl2::logext 32 *max-signed-int32*))
              *max-signed-int32*
            (if (< int-val (acl2::logext 32 *min-signed-int32*))
                *min-signed-int32*
              int-val)))))))

;convert double to long
;;TODO: Do this right
(defun d2l (d)
  (declare (xargs :guard (java-doublep d)
                  :guard-hints (("Goal" :in-theory (enable java-doublep regular-doublep)))))
  (if (eq *double-nan* d)
      0 ;(encode-signed 0) ;as prescribed by the JVM spec
    (if (eq *double-infinity* d)
        *max-signed-int64*
      (if (eq *double-negative-infinity* d)
          *min-signed-int64*
        (let* ((val (regular-double-value d))
               (int-val (floor val 1)))
          (if (> int-val (acl2::logext 64 *max-signed-int64*))
              *max-signed-int64*
            (if (< int-val (acl2::logext 64 *min-signed-int64*))
                *min-signed-int64*
              int-val)))))))

;; TODO: This should perform rounding (and perhaps range checking)
(defun i2f (int)
  (declare (xargs :guard (unsigned-byte-p 32 int)))
  (make-regular-float (if (< int 0) :neg :pos) int))

;; (can't call this float-sign because that symbol is already in the main LISP package)
(defun sign-of-float (f)
  (declare (xargs :guard (and (java-floatp f)
                              (not (float-nanp f)))
                  :guard-hints (("Goal" :in-theory (enable java-floatp)))))
  (if (regular-floatp f)
      (regular-float-sign f)
    (if (eq f *float-infinity*)
        :pos
      (if (eq f *float-negative-infinity*)
          :neg
        (er hard! 'sign-of-float "Unexpected float.")))))

;; Floating point multiply for the FMUL instruction
(defun fmul (value1 value2)
  (declare (xargs :guard (and (java-floatp value1)
                              (java-floatp value2))
                  :guard-hints (("Goal" :in-theory (enable JAVA-FLOATP)))
                  ))
  (if (or (float-nanp value1)
          (float-nanp value2))
      *float-nan*
    (let* ((sign1 (sign-of-float value1))
           (sign2 (sign-of-float value2))
           (result-sign (if (eq sign1 sign2) :pos :neg))
           (value1-infinityp (float-infinitep value1))
           (value2-infinityp (float-infinitep value2))
           (value1-zerop (float-zerop value1))
           (value2-zerop (float-zerop value2))
           ;; (value1-finite-non-zerop (and (not value1-infinityp)
           ;;                               (not value1-zerop)))
           ;; (value2-finite-non-zerop (and (not value2-infinityp)
           ;;                               (not value2-zerop)))
           )
      (if (or (and value1-infinityp value2-zerop)
              (and value2-infinityp value1-zerop))
          *float-NaN*
        (if (or (and value1-infinityp ;(not value2-infinityp)
                     )
                (and value2-infinityp ;(not value1-infinityp)
                     ))
            (if (eq :pos result-sign)
                *float-infinity*
              *float-negative-infinity*)
          (let* ((rat1 (regular-float-rat value1))
                 (rat2 (regular-float-rat value2))
                 (result-rat (* rat1 rat2)) ;;ffixme round!
                 )
            (make-regular-float result-sign result-rat)))))))

;; See 4.4.4 The CONSTANT_Integer_info and CONSTANT_Float_info Structures
;TODO: Test this
(defund acl2::parse-float (bits)
  (declare (type (unsigned-byte 32) bits))
  (if (eql bits #x7f800000)
      jvm::*float-infinity*
    (if (eql bits #xff800000)
        jvm::*float-negative-infinity*
      (if (or (and (<= #x7f800001 bits)
                   (<= bits #x7fffffff))
              (and (<= #xff800001 bits)
                   (<= bits #xffffffff)))
          jvm::*float-NaN*
        (let* ((s (if (eql (acl2::bvshr 32 bits 31) 0) 1 -1)) ;sign
               (e (acl2::bvand 32 (acl2::bvshr 32 bits 23) #xff))   ;exponent
               (m (if (eql e 0)
                      (acl2::bvshl 32 (acl2::bvand 32 bits #x7fffff) 1)
                    (acl2::bvor 32 (acl2::bvand 32 bits #x7fffff) #x800000))))
          (jvm::make-regular-float (if (eql s 1) :pos :neg)
                                   (* m (expt 2 (- e 150)))))))))

(defthm java-floatp-of-parse-float
  (java-floatp (acl2::parse-float bits))
  :hints (("Goal" :in-theory (enable acl2::parse-float
                                     make-regular-float
                                     java-floatp))))

;; See 4.4.5 The CONSTANT_Long_info and CONSTANT_Double_info Structures
;TODO: Test this
(defund acl2::parse-double (bits)
  (declare (type (unsigned-byte 64) bits))
  (if (eql bits #x7ff0000000000000)
      jvm::*double-infinity*
    (if (eql bits #xfff0000000000000)
        jvm::*double-negative-infinity*
      (if (or (and (<= #x7ff0000000000001 bits)
                   (<= bits #x7fffffffffffffff))
              (and (<= #xfff0000000000001 bits)
                   (<= bits #xffffffffffffffff)))
          jvm::*double-NaN*
        (let* ((s (if (eql (acl2::bvshr 64 bits 63) 0) 1 -1)) ;sign
               (e (acl2::bvand 64 (acl2::bvshr 64 bits 52) #x7ff))   ;exponent
               (m (if (eql e 0)
                      (acl2::bvshl 64 (acl2::bvand 64 bits #xfffffffffffff) 1)
                    (acl2::bvor 64 (acl2::bvand 64 bits #xfffffffffffff) #x10000000000000))))
          (jvm::make-regular-double (if (eql s 1) :pos :neg)
                                    (* m (expt 2 (- e 1075)))))))))

(defthm java-doublep-of-parse-double
  (java-doublep (acl2::parse-double bits))
  :hints (("Goal" :in-theory (enable acl2::parse-double
                                     make-regular-double
                                     java-doublep))))

;; todo: make versions of this stuff for doubles:

(defthm float-trichotomy
  (implies (and (not (equal :float-nan x))
                (not (equal :float-nan y))
                (java-floatp x)
                (java-floatp y))
           (or (float= x y)
               (float< x y)
               (float> x y)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable float< float= JAVA-FLOATP))))

(defthm not-equal-of-float-nan-and-make-regular-float
  (not (equal :float-nan (make-regular-float sign val))))

(defthm java-floatp-of-make-regular-float
  (equal (java-floatp (make-regular-float sign val))
         (and (float-signp sign)
              (rationalp val)
              (<= 0 val)))
  :hints (("Goal" :in-theory (enable make-regular-float java-floatp))))
