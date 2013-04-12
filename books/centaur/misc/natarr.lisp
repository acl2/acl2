; Centaur Miscellaneous Books
; Copyright (C) 2013 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "nats-equiv")
(include-book "std/lists/list-defuns" :dir :system)
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "std/lists/equiv" :dir :system))
(local (in-theory (enable* arith-equiv-forwarding)))
(local (include-book "std/typed-lists/nat-listp" :dir :system))

(include-book "1d-arr")

; General theorems about nth/update-nth and nat-lists.

(local (defthm equal-of-booleans-rewrite
         (implies (and (booleanp x)
                       (booleanp y))
                  (equal (equal x y)
                         (iff x y)))
         :rule-classes ((:rewrite :backchain-limit-lst 1))))

;; (defthm natp-of-nth-when-nat-listp
;;   (implies (nat-listp x)
;;            (equal (natp (nth n x))
;;                   (< (nfix n) (len x))))
;;   :rule-classes ((:rewrite)
;;                  (:linear :corollary
;;                           (implies (nat-listp x)
;;                                    (<= 0 (nth n x))))))

;; (defthm nat-listp-of-update-nth
;;   (implies (nat-listp x)
;;            (equal (nat-listp (update-nth n v x))
;;                   (and (<= (nfix n) (len (double-rewrite x)))
;;                        (natp v)))))

;; (defthm nat-listp-of-resize-list
;;   (implies (and (nat-listp x)
;;                 (natp default))
;;            (nat-listp (resize-list x n default))))



(def-1d-arr :arrname natarr
  :slotname nat
  :pred natp
  :fix nfix
  :type-decl (integer 0 *)
  :default-val 0)

(defun u32p (x)
  (declare (xargs :guard t))
  (unsigned-byte-p 32 x))

(encapsulate nil
  (local (defthm u32p-natp
           (implies (u32p x)
                    (natp x))))
  (local (defthm u32p-bound
           (implies (u32p x)
                    (< x 4294967296))))
  (local (in-theory (disable u32p)))
  (def-1d-arr :arrname u32arr
    :slotname u32
    :pred u32p
    :fix nfix
    :type-decl (unsigned-byte 32)
    :default-val 0))

(defun-inline set-u32n (i v u32arr)
  (declare (xargs :stobjs u32arr
                  :guard (and (natp i)
                              (< i (u32s-length u32arr))
                              (natp v))))
  (mbe :logic (set-u32 i v u32arr)
       :exec (if (< (the (integer 0 *) v) (expt 2 32))
                 (set-u32 i v u32arr)
               (ec-call (set-u32 i v u32arr)))))

