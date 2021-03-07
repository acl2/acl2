; Tests of bit-vector operations
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Test bit widths other than 32 (particularly sizes 0 and 1 for unsigned
;; and size 1 for signed)

(include-book "std/testing/assert-equal" :dir :system)
(include-book "bvdiv")
(include-book "sbvdiv")
(include-book "bvmod")
(include-book "sbvrem")
(include-book "putbits")
(include-book "sbvmoddown")

;todo: move
(defmacro without-guard-checking-events (&rest forms)
  `(with-guard-checking-event
    nil ;suppress guard checking (todo: do i want this or :none?)
    (encapsulate () ,@forms)))

;;;
;;; bvdiv
;;;

(defconst *max-int-32* (- (expt 2 32) 1))

;; bit width = 0: division is always 0
(without-guard-checking-events
 (assert-equal (bvdiv 0 1 1) 0)
 (assert-equal (bvdiv 0 5 2) 0)
 (assert-equal (bvdiv 0 5 3) 0)
 (assert-equal (bvdiv 0 *max-int-32* 2) 0)
 (assert-equal (bvdiv 0 *max-int-32* *max-int-32*) 0)
 )

;; bit width = 1
(assert-equal (bvdiv 1 1 1) 1)
(assert-equal (bvdiv 1 4 3) 0)
(assert-equal (bvdiv 1 5 3) 1)
(without-guard-checking-events
 (assert-equal (bvdiv 1 *max-int-32* 2) 0)
 (assert-equal (bvdiv 1 *max-int-32* *max-int-32*) 1)
)

;; bit width = 32
(assert-equal (bvdiv 32 5 3) 1)
(assert-equal (bvdiv 32 5 -3) 0)    ;; (bvdiv 32 5 4294967293)
(assert-equal (bvdiv 32 -5 3) 1431655763)   ;; (bvdiv 32 4294967291 3)
(assert-equal (bvdiv 32 -5 -3) 0)   ;; (bvdiv 32 4294967291 4294967293)
(assert-equal (bvdiv 32 -1 -1) 1)   ;; (bvdiv 32 4294967295 4294967295)

;; anything divided by 0 is 0:
(without-guard-checking-events
 (assert-equal (bvdiv 0 0 0) 0)
 (assert-equal (bvdiv 0 1 0) 0)
 (assert-equal (bvdiv 0 *max-int-32* 0) 0)

 (assert-equal (bvdiv 1 0 0) 0)
 (assert-equal (bvdiv 1 1 0) 0)
 (assert-equal (bvdiv 1 *max-int-32* 0) 0)

 (assert-equal (bvdiv 32 0 0) 0)
 (assert-equal (bvdiv 32 1 0) 0)
 (assert-equal (bvdiv 32 *max-int-32* 0) 0)
 )

;maxint / maxint = 1
(assert-equal (bvdiv 32 (+ -1 (expt 2 32)) (+ -1 (expt 2 32))) 1)

;;;
;;; bvmod
;;;

;; bit width = 0:  mod is always 0
(without-guard-checking-events
 (assert-equal (bvmod 0 1 1) 0)
 (assert-equal (bvmod 0 5 2) 0)
 (assert-equal (bvmod 0 5 3) 0)
 (assert-equal (bvmod 0 *max-int-32* 4) 0)
 (assert-equal (bvmod 0 *max-int-32* *max-int-32*) 0))

;; bit width = 1
(assert-equal (bvmod 1 1 1) 0)
(without-guard-checking-events
 (assert-equal (bvmod 1 5 2) 1))
(assert-equal (bvmod 1 5 3) 0)
(without-guard-checking-events
 (assert-equal (bvmod 1 *max-int-32* 4) 1)
 (assert-equal (bvmod 1 *max-int-32* *max-int-32*) 0))

;; bit width = 32
(assert-equal (bvmod 32 5 3) 2)
(assert-equal (bvmod 32 5 -3) 5)    ;; (bvmod 32 5 4294967293)
(assert-equal (bvmod 32 -5 3) 2)    ;; (bvmod 32 4294967291 3)
(assert-equal (bvmod 32 -5 -3) 4294967291)  ;; (bvmod 32 4294967291 4294967293)
(assert-equal (bvmod 32 -1 -1) 0)   ;; (bvmod 32 4294967295 4294967295)

;; anything modulo 0 is the n (bid width) low-order bits of itself:
(without-guard-checking-events
 (assert-equal (bvmod 0 0 0) 0)
 (assert-equal (bvmod 0 1 0) 0)
 (assert-equal (bvmod 0 *max-int-32* 0) 0)

 (assert-equal (bvmod 1 0 0) 0)
 (assert-equal (bvmod 1 1 0) 1)
 (assert-equal (bvmod 1 2 0) 0)
 (assert-equal (bvmod 1 *max-int-32* 0) 1)

 (assert-equal (bvmod 32 0 0) 0)
 (assert-equal (bvmod 32 1 0) 1)
 (assert-equal (bvmod 32 *max-int-32* 0) *max-int-32*)
 )

;;;
;;; signed operations
;;;

(defconst *min-sint-32* (bvchop 32 (- (expt 2 31))))
(defconst *max-sint-32* (bvchop 32 (- (expt 2 31) 1)))

;;;
;;; sbvdiv
;;;

;; bit width = 0: division is always 0
(without-guard-checking-events
 (assert-equal (sbvdiv 0 1 1) 0)
 (assert-equal (sbvdiv 0 5 2) 0)
 (assert-equal (sbvdiv 0 5 -3) 0)
 (assert-equal (sbvdiv 0 -5 3) 0)
 (assert-equal (sbvdiv 0 -5 -2) 0)
 (assert-equal (sbvdiv 0 *max-sint-32* 2) 0)
 (assert-equal (sbvdiv 0 *min-sint-32* *max-sint-32*) 0))

;; bit width = 1
(assert-equal (sbvdiv 1 1 1) 1)
(without-guard-checking-events
 (assert-equal (sbvdiv 1 5 2) 0))
(assert-equal (sbvdiv 1 5 -3) 1)
(assert-equal (sbvdiv 1 -5 3) 1)
(without-guard-checking-events
 (assert-equal (sbvdiv 1 -5 -2) 0)
 (assert-equal (sbvdiv 1 *max-sint-32* 2) 0))
(assert-equal (sbvdiv 1 *min-sint-32* *max-sint-32*) 0)

;; bit width = 32
(assert-equal (sbvdiv 32 5 3) 1)
(assert-equal (logext 32 (sbvdiv 32 5 -3)) -1)
(assert-equal (logext 32 (sbvdiv 32 -5 3)) -1)
(assert-equal (sbvdiv 32 -5 -3) 1)
(assert-equal (sbvdiv 32 -1 -1) 1)

;; anything divided by 0 is 0:
(without-guard-checking-events
 (assert-equal (sbvdiv 0 0 0) 0)
 (assert-equal (sbvdiv 0 1 0) 0)
 (assert-equal (sbvdiv 0 *max-sint-32* 0) 0)
 (assert-equal (sbvdiv 0 *min-sint-32* 0) 0)

 (assert-equal (sbvdiv 1 0 0) 0)
 (assert-equal (sbvdiv 1 1 0) 0)
 (assert-equal (sbvdiv 1 *max-sint-32* 0) 0)
 (assert-equal (sbvdiv 1 *min-sint-32* 0) 0)

 (assert-equal (sbvdiv 32 0 0) 0)
 (assert-equal (sbvdiv 32 5 0) 0)
 (assert-equal (sbvdiv 32 -5 0) 0)
 (assert-equal (sbvdiv 32 *max-sint-32* 0) 0)
 (assert-equal (sbvdiv 32 *min-sint-32* 0) 0)
 )

;; tricky case for signed division:
(assert-equal (sbvdiv 32 *min-sint-32* -1) *min-sint-32*)

;;;
;;; sbvrem
;;;

;; bit width = 0: remainder is always 0
(without-guard-checking-events
 (assert-equal (sbvrem 0 1 1) 0)
 (assert-equal (sbvrem 0 5 2) 0)
 (assert-equal (sbvrem 0 5 -3) 0)
 (assert-equal (sbvrem 0 -5 3) 0)
 (assert-equal (sbvrem 0 -5 -2) 0)
 (assert-equal (sbvrem 0 *max-sint-32* 2) 0)
 (assert-equal (sbvrem 0 *min-sint-32* *max-sint-32*) 0))

;; bit width = 1
(assert-equal (sbvrem 1 1 1) 0)
(without-guard-checking-events
 (assert-equal (logext 1 (sbvrem 1 5 2)) -1))
(assert-equal (sbvrem 1 5 -3) 0)
(assert-equal (sbvrem 1 -5 3) 0)
(without-guard-checking-events
 (assert-equal (logext 1 (sbvrem 1 -5 -2)) -1)
 (assert-equal (logext 1 (sbvrem 1 *max-sint-32* 2)) -1))
(assert-equal (sbvrem 1 *min-sint-32* *max-sint-32*) 0)

;; bit width = 32
(assert-equal (sbvrem 32 5 3) 2)
(assert-equal (sbvrem 32 5 -3) 2)
(assert-equal (logext 32 (sbvrem 32 -5 3)) -2)
(assert-equal (logext 32 (sbvrem 32 -5 -3)) -2)
(assert-equal (sbvrem 32 -1 -1) 0)

;; remainder of anything divided by 0 is the n (bid width) low-order bits of itself:
(without-guard-checking-events
 (assert-equal (sbvrem 0 0 0) 0)
 (assert-equal (sbvrem 0 1 0) 0)
 (assert-equal (sbvrem 0 *max-sint-32* 0) 0)
 (assert-equal (sbvrem 0 *min-sint-32* 0) 0)

 (assert-equal (sbvrem 1 0 0) 0)
 (assert-equal (logext 1 (sbvrem 1 1 0)) -1)
 (assert-equal (logext 1 (sbvrem 1 *max-sint-32* 0)) -1)
 (assert-equal (sbvrem 1 *min-sint-32* 0) 0)

 (assert-equal (sbvrem 32 0 0) 0)
 (assert-equal (sbvrem 32 5 0) 5)
 (assert-equal (logext 32 (sbvrem 32 -5 0)) -5)
 (assert-equal (sbvrem 32 *max-sint-32* 0) *max-sint-32*)
 (assert-equal (sbvrem 32 *min-sint-32* 0) *min-sint-32*)
 )

;; tricky case for signed division:
(assert-equal (sbvrem 32 *min-sint-32* -1) 0)

;;;
;;; sbvmoddown
;;;

;; bit width = 0: moddown is always 0
(without-guard-checking-events
 (assert-equal (sbvmoddown 0 1 1) 0)
 (assert-equal (sbvmoddown 0 5 2) 0)
 (assert-equal (sbvmoddown 0 5 -3) 0)
 (assert-equal (sbvmoddown 0 -5 3) 0)
 (assert-equal (sbvmoddown 0 -5 -2) 0)
 (assert-equal (sbvmoddown 0 *max-sint-32* 2) 0)
 (assert-equal (sbvmoddown 0 *min-sint-32* *max-sint-32*) 0))

;; bit width = 1
(assert-equal (sbvmoddown 1 1 1) 0)
(without-guard-checking-events
 (assert-equal (logext 1 (sbvmoddown 1 5 2)) -1))
(assert-equal (sbvmoddown 1 5 -3) 0)
(assert-equal (sbvmoddown 1 -5 3) 0)
(without-guard-checking-events
 (assert-equal (logext 1 (sbvmoddown 1 -5 -2)) -1)
 (assert-equal (logext 1 (sbvmoddown 1 *max-sint-32* 2)) -1))
(assert-equal (sbvmoddown 1 *min-sint-32* *max-sint-32*) 0)

;; bit width = 32
(assert-equal (sbvmoddown 32 5 3) 2)
(assert-equal (logext 32 (sbvmoddown 32 5 -3)) -1)
(assert-equal (sbvmoddown 32 -5 3) 1)
(assert-equal (logext 32 (sbvmoddown 32 -5 -3)) -2)
(assert-equal (sbvmoddown 32 -1 -1) 0)

;; anything modulo down 0 is the n (bit width) low-order bits of itself:
(without-guard-checking-events
 (assert-equal (sbvmoddown 0 0 0) 0)
 (assert-equal (sbvmoddown 0 1 0) 0)
 (assert-equal (sbvmoddown 0 *max-sint-32* 0) 0)
 (assert-equal (sbvmoddown 0 *min-sint-32* 0) 0)

 (assert-equal (sbvmoddown 1 0 0) 0)
 (assert-equal (logext 1 (sbvmoddown 1 1 0)) -1)
 (assert-equal (logext 1 (sbvmoddown 1 *max-sint-32* 0)) -1)
 (assert-equal (sbvmoddown 1 *min-sint-32* 0) 0)

 (assert-equal (sbvmoddown 32 0 0) 0)
 (assert-equal (sbvmoddown 32 5 0) 5)
 (assert-equal (logext 32 (sbvmoddown 32 -5 0)) -5)
 (assert-equal (sbvmoddown 32 *max-sint-32* 0) *max-sint-32*)
 (assert-equal (sbvmoddown 32 *min-sint-32* 0) *min-sint-32*)
 )

;; tricky case for signed division:
(assert-equal (sbvmoddown 32 *min-sint-32* -1) 0)

;;;
;;; putbit/putbits
;;;

;; set bit slice 5..3 to 7 in the bv 0
(assert-equal (putbits 8 5 3 7 0) #b111000)
(assert-equal (putbits 8 6 4 #b010 #b11111111) #b10101111)

(assert-equal (putbit 8 4 1 0) #b10000)
