(in-package #:3bz)
;;; stubs of mmap/pointer routines to allow compilation on mezzano/abcl
#- (or abcl mezzano)
(error "this code assume mezzano/abcl, patches welcome if some other OS needs it")

;; we restrict size of these types a bit more on 64 bit platforms to
;; ensure intermediate results stay in reasonable range for
;; performance.
(deftype size-t () `(unsigned-byte
                     ,(min 60 (1- (integer-length most-positive-fixnum)))))
;; slightly larger so incrementing a size-t still fits
(deftype offset-t () `(unsigned-byte
                       ,(min 61 (integer-length most-positive-fixnum))))

(defclass octet-pointer-context ()
  ())

(defmacro with-pointer-context ((context) &body body)
  (declare (ignore context body))
  `(error "pointer contexts not supported on this platform"))
