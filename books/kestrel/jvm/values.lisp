; Representing JVM values as bit vectors
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Note: Portions of this file may be taken from books/models/jvm/m5.  See the
; LICENSE file and authorship information there as well.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

(include-book "portcullis")
(include-book "kestrel/bv/logext-def" :dir :system)

;; I am now changing this over to store bit vectors as unsigned values (Mostly done now..).  So
;; the byte representing -1 (previously stored as -1) is now stored as 255.
;; This matches the bit-vector operators much better.  But note that things
;; like comparisons will have to be redone (e.g., use sbvlt instead of just <).

;this should only be applied to usb32s
(defmacro encode-unsigned (val)
  ;`(int-fix ,val)
  val
  )

(defmacro encode-unsigned-long (val)
  ;`(long-fix ,val)
  val
  )

;eventually this will call bvchop, but for now signed values are stored directly - i guess we switched it over...
;TODO: this should have 32 in the name
(defmacro encode-signed (val)
;;  val
  `(bvchop 32 ,val)
  )

;; ;eventually this will call bvchop, but for now signed values are stored directly - i guess we switched it over...
;; (defmacro encode-signed-long (val)
;;   ;;val
;;   `(bvchop 64 ,val))

;TODO: this should have 32 in the name
;the value stored is unsigned, so we must convert it before using is as a number
(defmacro decode-signed (val)
  `(acl2::logext 32 ,val))

; Decoding a usb32 that is known to not be negative (using sbvlt 32 as the
;comparison) does nothing in our current representation, but to keep the typing
;discipline we have this perform a conversion. fixme use this more?
(defun decode-signed-non-neg (val)
  (declare (xargs :guard (unsigned-byte-p 32 val))) ;val is a BV (TODO: use bvp)
  val ;(acl2::logext 32 val) ;val
  ) ;convert val to a signed-integer (TODO: use bv-to-sint)

;; ;this justifies leaving out calls of decode-signed in cases where we know the int value is non-negative:
;but this needs bv/bv.lisp to prove it, which is less than we are including here...
;; (defthm decode-signed-when-positive
;;   (implies (and (unsigned-byte-p 32 x)
;;                 (not (acl2::sbvlt 32 x 0)))
;;            (equal (decode-signed x)
;;                   x))
;;   :hints (("Goal" :in-theory (e/d (ACL2::SBVLT ACL2::LOGEXT) (ACL2::LOGEXT-DOES-NOTHING-REWRITE)))))

;; ;the value stored is unsigned, so we must convert it before using is as a number
;; (defmacro decode-signed-long (val)
;;   `(acl2::logext 64 ,val))
