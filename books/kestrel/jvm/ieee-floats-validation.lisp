(in-package "ACL2")

(include-book "ieee-floats-as-bvs")

;; Some validation theorems for the floating-point model

(local (include-book "kestrel/bv/rules" :dir :system))

;; From the JVM spec 4.4.4
(thm
 (implies (bv-float32p bv)
          (iff (equal *float-positive-infinity* (decode-bv-float32 bv))
               (equal bv #x7f800000)))
 :hints (("Goal" :in-theory (enable decode-bv-float32 decode-bv-float decode))))

;; From the JVM spec 4.4.4
(thm
 (implies (bv-float32p bv)
          (iff (equal *float-negative-infinity* (decode-bv-float32 bv))
               (equal bv #xff800000)))
 :hints (("Goal" :in-theory (enable decode-bv-float32 decode-bv-float decode
                                    equal-of-bvchop-when-equal-of-getbit-widen))))

;; ;todo
;; ;; From the JVM spec 4.4.4
;; (thm
;;  (implies (bv-float32p bv)
;;           (iff (equal *float-nan* (decode-bv-float32 bv))
;;                (or (and (<= #x7f800001 bv)
;;                         (<= bv #x7fffffff))
;;                    (and (<= #xff800001 bv)
;;                         (<= bv #xffffffff)))))
;;  :otf-flg t
;;  :hints (("Goal" :cases ((equal 1 (getbit 31 bv)))
;;           :in-theory (enable decode-bv-float32 decode-bv-float decode
;;                              equal-of-bvchop-when-equal-of-getbit-widen))))


;; From the Java doc for Float.MAX_VALUE:
(thm (equal (largest-positive-normal 32 24) (* (- 2 (expt 2 -23)) (expt 2 127))))
;todo: prove things about the encoding

;; From the Java doc for Float.MIN_NORMAL:
(thm (equal (smallest-positive-normal 32 24) (expt 2 -126)))
