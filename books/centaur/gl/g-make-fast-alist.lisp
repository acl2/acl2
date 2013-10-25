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
(include-book "centaur/gl/g-primitives-help" :dir :system)
(include-book "centaur/gl/eval-g-base" :dir :system)
(include-book "centaur/gl/g-if" :dir :system)
(local (include-book "centaur/gl/eval-g-base-help" :dir :system))

(def-g-fn acl2::make-fast-alist
  `(let ((x acl2::alist))
     (if (general-concretep x)
         (gret (mk-g-concrete
                (acl2::make-fast-alist (general-concrete-obj x))))
       (pattern-match x
         ((g-ite test then else)
          (if (zp clk)
              (gret x)
            (g-if (gret test)
                  (,gfn then . ,params)
                  (,gfn else . ,params))))
         ((g-apply & &) (gret x))
         ((g-var &) (gret x))
         ((g-boolean &) (gret x))
         ((g-number &) (gret x))
         (& (gret (acl2::make-fast-alist x)))))))

;; (def-gobjectp-thm acl2::make-fast-alist)

;; (defthm gobjectp-impl-not-g-keyword-symbolp
;;   (implies (gobjectp x)
;;            (not (g-keyword-symbolp x)))
;;   :hints(("Goal" :in-theory (enable gobject-hierarchy-impl-not-g-keyword-symbolp
;;                                     gobjectp))))

(verify-g-guards acl2::make-fast-alist)

(def-gobj-dependency-thm acl2::make-fast-alist
  :hints `(("goal" :induct ,gcall
            :expand (,gcall)
            :in-theory (disable (:d ,gfn)))))

(def-g-correct-thm acl2::make-fast-alist eval-g-base
  :hints `(("Goal" :induct (,gfn acl2::alist . ,params)
            :expand (,gfn acl2::alist . ,params)
            :in-theory (disable (:definition ,gfn)))
           (and stable-under-simplificationp
                '(:expand ((:with eval-g-base (eval-g-base acl2::alist
                                                           env)))))))
