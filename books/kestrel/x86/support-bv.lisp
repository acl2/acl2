; Supporting rules about bit-vectors
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; todo: Push these back into libraries.

(include-book "kestrel/bv/bvcat" :dir :system)
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/bv/rules" :dir :system)) ; for slice-too-high-is-0-new (todo: move it)
;(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
;(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))

;; ;replace the other one!
;; (encapsulate ()
;;   (local (include-book "kestrel/arithmetic-light/expt" :dir :system))
;;   (defthm slice-of-times-of-expt-gen
;;     (implies (and            ;(<= j n) ;drop?
;;               (integerp x)   ;drop?
;;               (natp n)
;;               (natp j)
;;               (natp m))
;;              (equal (slice m n (* (expt 2 j) x))
;;                     (slice (- m j) (- n j) x)))
;;     :hints (("Goal" :in-theory (e/d (slice logtail nfix) ())))))

;move
;; ;avoids having to give a highsize
;; (defthm slice-of-logapp
;;   (implies (and (natp lowsize)
;;                 (natp low)
;;                 (natp high)
;;                 (integerp highval))
;;            (equal (slice high low (logapp lowsize lowval highval))
;;                   (slice high low (bvcat (+ 1 high (- lowsize)) highval lowsize lowval))))
;;   :otf-flg t
;;   :hints (("Goal" :use (:instance ACL2::BVCAT-RECOMBINE
;;                                   (acl2::lowsize lowsize)
;;                                   (acl2::lowval lowval)
;;                                   (acl2::highval highval)
;;                                   (acl2::highsize (+ 1 high (- lowsize)))))))


;;   :hints (("Goal" :in-theory (e/d (;bvcat logapp
;;                                          ;acl2::slice-of-sum-cases
;;                                          )
;;                                   (acl2::slice-of-*)))))

;move
(defthm slice-of-logapp-case-1
  (implies (and (natp high)
                (natp low)
                ;; (natp lowsize)
                (<= lowsize low) ; this case
                (unsigned-byte-p lowsize lowval)
                (integerp highval))
           (equal (acl2::slice high low (logapp lowsize lowval highval))
                  (acl2::slice (+ (- lowsize) high) (+ (- lowsize) low) highval)))
  :hints (("Goal" :in-theory (e/d (acl2::slice logapp) (acl2::logtail-of-plus
                                                  acl2::unsigned-byte-p-of-logapp-large-case))
           :use (:instance acl2::unsigned-byte-p-of-logapp-large-case
                           (size1 low)
                           (size lowsize)
                           (i lowval)
                           (j (acl2::BVCHOP (+ LOW (- LOWSIZE)) HIGHVAL))))))
