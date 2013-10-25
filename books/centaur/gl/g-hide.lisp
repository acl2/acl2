; GL - A Symbolic Simulation Framework for ACL2
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

(in-package "GL")
(include-book "g-primitives-help")
(include-book "eval-g-base")
(include-book "gtypes")
(include-book "g-if")
(local (include-book "gobjectp-thms"))

(def-g-fn hide '(gret x)
  :replace-g-ifs nil)

;; (def-gobjectp-thm hide)

(local (defthm hide-open
         (equal (hide x) x)
         :hints (("Goal" :expand ((:free (x) (hide x)))))))

(verify-g-guards hide)

(def-gobj-dependency-thm hide
  :hints `(("goal"
            :expand (,gcall)
            :in-theory (disable (:d ,gfn)))))

(def-g-correct-thm hide eval-g-base
  :hints `(("Goal" :in-theory '(hide-open ,gfn))))
