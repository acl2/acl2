; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>, Sol Swords <sswords@centtech.com>

; arith-equivs.lisp -- congruence reasoning about integers/naturals/bits


;; Note: To use this book at full strength, do:
;; (local (in-theory (enable* arith-equiv-forwarding)))

(in-package "ACL2")
(include-book "ihs/basic-definitions" :dir :system)
(include-book "tools/rulesets" :dir :system)

(defthm bitp-compound-recognizer
  ;; Questionable given the bitp-forward rule.  But I think we may still want
  ;; this.
  (implies (bitp x)
           (natp x))
  :rule-classes :compound-recognizer)

;; (defthm bitp-when-under-2
;;   ;; questionable to bring arithmetic into it
;;   (implies (< x 2)
;;            (equal (bitp x)
;;                   (natp x))))

;; (defthm bitp-when-over-1
;;   (implies (< 1 x)
;;            (not (bitp x))))

(defun int-equiv (a b)
  (declare (xargs :guard t))
  (equal (ifix a) (ifix b)))

(defun nat-equiv (a b)
  (declare (xargs :guard t))
  (equal (nfix a) (nfix b)))

(defun bit-equiv (x y)
  (declare (xargs :guard t))
  (equal (bfix x) (bfix y)))

(local (in-theory (enable int-equiv nat-equiv bit-equiv)))

(defequiv int-equiv)
(defequiv nat-equiv)
(defequiv bit-equiv)

(defrefinement int-equiv nat-equiv)
(defrefinement nat-equiv bit-equiv)
;; (defrefinement int-equiv bit-equiv) ;; already known

(defcong int-equiv equal (ifix a) 1)
(defcong nat-equiv equal (nfix a) 1)
(defcong bit-equiv equal (bfix a) 1)

(defthm ifix-under-int-equiv
  (int-equiv (ifix a) a))

(defthm nfix-under-nat-equiv
  (nat-equiv (nfix a) a))

(defthm bfix-under-bit-equiv
  (bit-equiv (bfix a) a))

(defcong int-equiv equal (zip a) 1)
(defcong nat-equiv equal (zp a)  1)
(defcong bit-equiv equal (zbp a) 1)

(defund-inline bool->bit (x)
  (declare (xargs :guard t))
  (if x 1 0))

(defund negp (x)
  (declare (xargs :guard t))
  (and (integerp x)
       (< x 0)))

(defthm negp-compound-recognizer
  (equal (negp x)
         (and (integerp x)
              (< x 0)))
  :hints(("Goal" :in-theory (enable negp)))
  :rule-classes :compound-recognizer)



