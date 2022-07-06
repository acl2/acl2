; Java floats as bit-vectors -- Experimental!
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

;; STATUS: Experimental !

;; Representation of Java floats as bit-vectors (essentially IEEE 754 format,
;; except for different treatment of NaNs).

;; We do not support the float extended-exponent value set or the double
;; extended-exponent value set as these are no longer used as of Java SE 17.

;; TODO: Deal with the fact that even just moving a NaN can convert its bit
;; pattern from a signalling NaN to a quiet NaN.

;; TODO: Put this in when stable

(include-book "ieee-floats-as-bvs")
(include-book "kestrel/bv/getbit-def" :dir :system)


;; ;; Decode an IEEE float, giving a non-zero rational number or one of the five
;; ;; special values.  TODO remove this and related stuff from the JVM package.
;; ;; TODO: Compare to parse-float in class-file-parser.lisp
;; (defun decode-ieee-float (f)
;;   (declare (xargs :guard (acl2::ieee-float32p f)))
;;   (let ((sign (acl2::getbit 31 f)) ;sign bit
;;         (e (acl2::slice 30 23 f))    ;biased exponent
;;         (sig (acl2::bvchop 23 f)) ;trailing significand bits
;;         )
;;     (if (= e (+ (expt 2 8) -1)) ;all ones for exponent
;;         (if (= 0 sig)
;;             ;; an infinity:
;;             (if (= 1 sign)
;;                 acl2::*float-negative-infinity*
;;               acl2::*float-positive-infinity*)
;;           ;; a NaN:
;;           acl2::*float-nan*)
;;       (if (= e 0)
;;           (if (= sig 0)
;;               ;; a signed zero:
;;               (if (= 1 sign)
;;                   acl2::*float-negative-zero*
;;                 acl2::*float-positive-zero*)
;;             ;;subnormal number:
;;             (let ((val (* (expt 2 acl2::*binary32-emin*) (expt 2 (- 1 acl2::*binary32-p*)) sig)))
;;               (if (= 0 sign)
;;                   val
;;                 (- val))))
;;         ;;normal case:
;;         (let ((val (* (expt 2 (- e acl2::*binary32-bias*)) (+ 1 (expt 2 (- 1 acl2::*binary32-p*)) sig))))
;;           (if (= 0 sign)
;;               val
;;             (- val)))))))

;; This is the canonical value that represents floating point NaNs in our model.
;; This is consistent with what the library method floatToIntBits does. TODO:
;; Need to change the parsing functions in the class-file-parser to use this.
(defconst *java-float-nan* #x7fc00000)

;; We represent floats as bit-vectors of size 32.
(defun java-floatp (f)
  (declare (xargs :guard t))
  (and (acl2::bv-float32p f)
       ;; (let ((val (decode-ieee-float f)))
       ;;   ;; The Java floats are the same as the IEEE floats except the
       ;;   ;; only allowed NaN is *java-float-nan*
       ;;   (if (eq acl2::*float-nan* val)
       ;;       (eql f *java-float-nan*)
       ;;     t))
       ))

;; ;TODO: Prove some more validation theorems.
;; (defthm ieee-float32p-when-java-floatp
;;   (implies (java-floatp f)
;;            (acl2::ieee-float32p f)))

;; TODO: Seems wrong
(defun float-zerop (f)
  (declare (xargs :guard t))
  (or (eq acl2::*float-positive-zero* f)
      (eq acl2::*float-negative-zero* f)))

;; Floating point "less than"
(defund float< (x y)
  (declare (xargs :guard (and (java-floatp x)
                              (java-floatp y))
                  :guard-hints (("Goal" :in-theory (enable java-floatp)))))
  (let* ((x (acl2::decode-bv-float32 x))
         (y (acl2::decode-bv-float32 y)))
    (if (or (eq acl2::*float-NaN* x)
            (eq acl2::*float-NaN* y))
        nil ; If either is a NaN, the comparison returns false (2.3.2)
      (if (eq x acl2::*float-negative-infinity*)
          ;; If x is negative infinity, it's less than y unless y is also negative infinity
          (not (eq y acl2::*float-negative-infinity*))
        (if (eq x acl2::*float-positive-infinity*)
            nil ; positive infinity is never less than anything
          ;; x represents a rational number:
          (if (eq y acl2::*float-negative-infinity*)
              nil ; Nothing is less than negative infinity
            (if (eq y acl2::*float-positive-infinity*)
                t ; Any regular value is less than infinity
              ;; x and y both represents rational numbers:
              (let ((x (if (float-zerop x) 0 x)) ; treats positive zeros and negative zeros as 0
                    (y (if (float-zerop y) 0 y)))
                (< x y)))))))))

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
  (let* ((x (acl2::decode-bv-float32 x))
         (y (acl2::decode-bv-float32 y)))
    (if (or (eq acl2::*float-NaN* x)
            (eq acl2::*float-NaN* y))
        nil ; If either is a NaN, the equality returns false (2.3.2):
      (if (eq x acl2::*float-negative-infinity*)
          ;; If x is negative infinity, it's only equal to y if y is also negative infinity
          (eq y acl2::*float-negative-infinity*)
        (if (eq x acl2::*float-positive-infinity*)
            ;; If x is infinity, it's only equal to y if y is also infinity
            (eq y acl2::*float-positive-infinity*)
          ;; x represents a rational number, so y must also represent a rational number, and the values must be equal:
          (and (not (eq y acl2::*float-positive-infinity*))
               (not (eq y acl2::*float-negative-infinity*))
               (let ((x (if (float-zerop x) 0 x)) ; treats positive zeros and negative zeros as 0
                     (y (if (float-zerop y) 0 y)))
                 (equal x y))))))))

;todo
;; (defthm float-trichotomy
;;   (implies (and (not (equal :float-nan x))
;;                 (not (equal :float-nan y))
;;                 (java-floatp x)
;;                 (java-floatp y))
;;            (or (float= x y)
;;                (float< x y)
;;                (float> x y)))
;;   :rule-classes nil
;;   :hints (("Goal" :in-theory (enable float< float= java-floatp))))
