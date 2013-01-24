; Bit array abstract stobj
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "1d-arr")
(include-book "arith-equivs")

;; Abstract stobj containing an array of bits.  Represented by a list of bits,
;; accessed/updated by nth/update-nth.

(def-universal-equiv bits-equiv
  :qvars (i)
  :equiv-terms ((bit-equiv (nth i x))))

(defcong bits-equiv bit-equiv (nth i x) 2
  :hints(("Goal" :in-theory (e/d (bits-equiv-necc)
                                 (bit-equiv)))))

(defcong bits-equiv bits-equiv (update-nth i v x) 3
  :hints((and stable-under-simplificationp
              `(:expand (,(car (last clause)))))))

(defcong bit-equiv bits-equiv (update-nth i v x) 2
  :hints((and stable-under-simplificationp
              `(:expand (,(car (last clause)))))))


(def-1d-arr :arrname bitarr
  :slotname bit
  :pred bitp
  :fix bfix
  :type-decl bit
  :default-val 0)
