; Centaur Miscellaneous Books
; Copyright (C) 2008-2013 Centaur Technology
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
(include-book "universal-equiv")

(def-universal-equiv nth-equiv
  :qvars n
  :equiv-terms ((equal (nth n x))))

(defcong nth-equiv equal (nth n x) 2
  :hints(("Goal" :in-theory (enable nth-equiv-necc))))

(defcong nth-equiv nth-equiv (update-nth n v x) 3
  :hints(("Goal" :in-theory (enable nth-equiv-necc)
          :expand ((:free (n v x y)
                    (nth-equiv (update-nth n v x) y))))))

(defthm update-nth-of-same-under-nth-equiv
  (nth-equiv (update-nth n (nth n x) x)
             x)
  :hints(("Goal" :in-theory (enable nth-equiv))))
