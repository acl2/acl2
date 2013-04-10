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

(defcong bits-equiv bits-equiv (cdr a) 1
    :hints (("goal" :in-theory (disable default-cdr nth))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))
            (and stable-under-simplificationp
                 '(:use ((:instance bits-equiv-necc
                          (i (+ 1 (nfix (bits-equiv-witness (cdr a) (cdr a-equiv)))))
                          (x a)
                          (y acl2::a-equiv)))
                   :in-theory (e/d ()
                                   (bits-equiv-necc
                                    bits-equiv-implies-bit-equiv-nth-2))))))

(defcong bits-equiv bit-equiv (car x) 1
  :hints (("goal" :use ((:instance bits-equiv-implies-bit-equiv-nth-2
                         (i 0)))
           :in-theory (disable bits-equiv-implies-bit-equiv-nth-2))))

(defcong bit-equiv bits-equiv (cons a b) 1
  :hints(("Goal" :in-theory (enable bits-equiv)
          :expand ((:free (a b c) (nth a (cons b c)))))))

(defcong bits-equiv bits-equiv (cons a b) 2
  :hints ((and stable-under-simplificationp
               `(:expand (,(car (last clause))
                          (:free (a b c) (nth a (cons b c))))
                 :in-theory (disable bit-equiv)))))

(def-1d-arr :arrname bitarr
  :slotname bit
  :pred bitp
  :fix bfix$inline
  :type-decl bit
  :default-val 0)
