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
(include-book "g-if")
(include-book "g-primitives-help")
(include-book "symbolic-arithmetic")
(include-book "eval-g-base")

(local (include-book "eval-g-base-help"))
(local (include-book "hyp-fix"))
(set-inhibit-warnings "theory")

(def-g-fn lognot
  `(let ((x i))
     (if (atom x)
         (gret (lognot (ifix x)))
       (pattern-match x
         ((g-ite test then else)
          (if (zp clk)
              (gret (g-apply 'lognot (gl-list x)))
            (g-if (gret test)
                  (,gfn then . ,params)
                  (,gfn else . ,params))))
         ((g-apply & &)
          (gret (g-apply 'lognot (gl-list x))))
         ((g-concrete obj)
          (gret (lognot (ifix obj))))
         ((g-var &)
          (gret (g-apply 'lognot (gl-list x))))
         ((g-boolean &) (gret -1))
         ((g-number num)
          (b* (((mv rn rd in id)
                (break-g-number num))
               ((mv intp intp-known)
                (if (equal rd '(t))
                    (mv (bfr-or (bfr-=-ss in nil) (bfr-=-uu id nil)) t)
                  (mv nil nil))))
            (gret
             (if intp-known
                 (mk-g-number (list-fix (bfr-lognot-s (bfr-ite-bss-fn intp rn nil))))
               (g-apply 'lognot (gl-list x))))))
         (& (gret -1))))))



;; (local (defthm gobjectp-lognot
;;          (gobjectp (lognot x))
;;          :hints(("Goal" :in-theory (enable gobjectp-def)))))

;; (def-gobjectp-thm lognot
;;   :hints `(("Goal" :in-theory (e/d ()
;;                                    ((:definition ,gfn) lognot))
;;             :induct (,gfn i . ,params)
;;             :expand ((,gfn i . ,params)
;;                      (:free (x) (gobjectp (- x)))))))

(verify-g-guards
 lognot
 :hints `(("Goal" :in-theory (disable ,gfn))))

(def-gobj-dependency-thm lognot
  :hints `(("goal" :induct ,gcall
            :expand (,gcall)
            :in-theory (disable (:d ,gfn)))))

(local
 (progn
   (defthm lognot-non-acl2-numberp
     (implies (not (acl2-numberp n))
              (equal (lognot n) (lognot 0))))

   (defthm lognot-non-integer
     (implies (not (integerp n))
              (equal (lognot n) (lognot 0))))

   (local (include-book "arithmetic/top-with-meta" :dir :system))))

(def-g-correct-thm lognot eval-g-base
   :hints `(("Goal" :in-theory (e/d* (components-to-number-alt-def
                                      general-concrete-obj)
                                    ((:definition ,gfn) (force)
                                     general-number-components-ev
                                     general-numberp-eval-to-numberp
                                     lognot))
             :induct (,gfn i . ,params)
             :expand ((,gfn i . ,params)
                      (:with eval-g-base (eval-g-base i env))))))

