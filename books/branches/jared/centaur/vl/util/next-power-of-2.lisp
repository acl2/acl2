; VL Verilog Toolkit
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
(local (include-book "arithmetic"))

(defund next-power-of-2 (n)
  ;; Returns the smallest M such that n <= 2^M
  (declare (xargs :guard (posp n)))
  (integer-length (1- n)))

(local (in-theory (enable next-power-of-2)))

(defthm type-of-next-power-of-2
  (natp (next-power-of-2 n))
  :rule-classes :type-prescription)

(defthm lower-bound-of-next-power-of-2
  (implies (force (posp n))
           (<= n (expt 2 (next-power-of-2 n))))
  :rule-classes ((:rewrite) (:linear)))

(defthm upper-bound-of-next-power-of-2
  (implies (force (posp n))
           (< (expt 2 (1- (next-power-of-2 n)))
              n))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal"
          :in-theory (disable acl2::|2^{(integer-length n) - 1} <= n|)
          :use ((:instance acl2::|2^{(integer-length n) - 1} <= n|
                           (acl2::n (- n 1)))))))
