; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "ihs/logops-definitions" :dir :system)
(include-book "xdoc/top" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "ihsext-basics"))
(local (include-book "misc/assert" :dir :system))

(defxdoc part-select
  :short "Select a portion of bits from an integer that represents a bit
          vector"
  :long "This is a hopefully more readable alternative to RDB.

         Sometimes RDB is exactly what you want, but other times you have a
         high/low index and you want to use them to select part of a vector.

         PART-SELECT is just a little wrapper around RDB that lets you do
         things like

 @({
 (part-select foo :low 10 :high 17)       ;; Like foo[17:10] in Verilog
 })

         You can still select parts of a vector using an index/size, e.g.:

 @({
 (part-select foo :low 10 :width 7)       ;; Like foo[16:10] in Verilog
 })

         This just macroexpands into RDB calls, to avoid making reasoning any
         more complicated.")


;; ;; this might be generally useful
;; (local
;;  (encapsulate
;;    ()
;;    (local (defun my-induct (x n)
;;             (if (zp n)
;;                 x
;;               (my-induct (logcdr x) (- n 1)))))

;;    (defthm logand-with-full-mask-to-logtail
;;      (implies (and (natp width)
;;                    (integerp x))
;;               (equal (logand (+ -1 (ash 1 width)) x)
;;                      (loghead width x)))
;;      :hints(("Goal"
;;              :induct (my-induct x width)
;;              :in-theory (e/d* (loghead* ash* logand** logcons)
;;                               (loghead logand ash)))))))


(defun part-select-width-low (x width low)
  ;; Don't call this, use the macro instead.
  (declare (xargs :guard (and (integerp x)
                              (natp width)
                              (natp low))))
  (mbe :logic (rdb (bsp width low) x)
       :exec
       (logand (1- (ash 1 width))
               (ash x (- low)))))

(defun part-select-low-high (x low high)
  ;; Don't call this, use the macro instead.
  (declare (xargs :guard (and (integerp x)
                              (natp low)
                              (natp high)
                              (<= low high))))
  (part-select-width-low x (+ 1 (- high low)) low))

(defmacro part-select (x &key low high width)
  (cond ((and high width)
         (er hard? 'part-select "Can't use :high and :width together"))
        ((and low high)
         `(part-select-low-high ,x ,low ,high))
        ((and low width)
         `(part-select-width-low ,x ,width ,low))
        (t
         (er hard? 'part-select "Need at least :low and :width, or else :low and :high"))))


(local
 (progn

   (assert! (equal (part-select #ux_AAAA_BBBB_CCCC_DDDD :low 0 :width 16) #ux_DDDD))
   (assert! (equal (part-select #ux_AAAA_BBBB_CCCC_DDDD :low 16 :width 16) #ux_CCCC))
   (assert! (equal (part-select #ux_AAAA_BBBB_CCCC_DDDD :low 32 :width 16) #ux_BBBB))
   (assert! (equal (part-select #ux_AAAA_BBBB_CCCC_DDDD :low 48 :width 16) #ux_AAAA))

   (assert! (equal (part-select #ux_AAAA_BBBB_CCCC_DDDD :low 0  :high 15) #ux_DDDD))
   (assert! (equal (part-select #ux_AAAA_BBBB_CCCC_DDDD :low 16 :high 31) #ux_CCCC))
   (assert! (equal (part-select #ux_AAAA_BBBB_CCCC_DDDD :low 32 :high 47) #ux_BBBB))
   (assert! (equal (part-select #ux_AAAA_BBBB_CCCC_DDDD :low 48 :high 63) #ux_AAAA))

   ))

