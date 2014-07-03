; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
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
