; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
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

(in-package "FGL")


(include-book "def-fgl-thm")
(include-book "centaur/bitops/extra-defs" :dir :system)
(include-book "centaur/bitops/merge" :dir :system)
(local (include-book "top"))
(local (include-book "centaur/ipasir/ipasir-backend" :dir :system))
(local (include-book "centaur/aignet/transforms" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :Dir :system))
; cert_param: (uses-glucose)
(value-triple (acl2::tshell-ensure))

(defmacro parallel-multiply-spec-lane (lane x y writemask)
  `(if (logbitp ,lane ,writemask)
       (loghead 32
                (* (acl2::nth-slice32 ,lane ,x)
                   (acl2::nth-slice32 ,lane ,y)))
     0))

(define parallel-multiply-spec ((x integerp)
                                (y integerp)
                                (writemask integerp))
  (acl2::merge-4-u32s (parallel-multiply-spec-lane 3 x y writemask)
                      (parallel-multiply-spec-lane 2 x y writemask)
                      (parallel-multiply-spec-lane 1 x y writemask)
                      (parallel-multiply-spec-lane 0 x y writemask)))


(defmacro parallel-multiply-impl-lane (lane x y x0 y0 writemask)
  ;; note: we need to bind these ahead of time, otherwise the (if (logbitp lane writemask) ...)
  ;; will get resolved by the path condition.
  `(let ((x (if (logbitp ,lane ,writemask) (acl2::nth-slice32 ,lane ,x) (acl2::nth-slice32 ,lane ,x0)))
         (y (if (logbitp ,lane ,writemask) (acl2::nth-slice32 ,lane ,y) (acl2::nth-slice32 ,lane ,y0))))
     (if (logbitp ,lane ,writemask)
         (loghead 32
                  (* x y))
       0)))

(define parallel-multiply-impl ((x integerp)
                                (y integerp)
                                (x0 integerp)
                                (y0 integerp)
                                (writemask integerp))
  (acl2::merge-4-u32s (parallel-multiply-impl-lane 3 x y x0 y0 writemask)
                      (parallel-multiply-impl-lane 2 x y x0 y0 writemask)
                      (parallel-multiply-impl-lane 1 x y x0 y0 writemask)
                      (parallel-multiply-impl-lane 0 x y x0 y0 writemask)))


(local
 (progn
   (defattach fgl-toplevel-sat-check-config monolithic-sat-with-transforms)


   (define my-aignet-transforms-config ()
     #!aignet
     (list (make-observability-config)
           (make-balance-config :search-higher-levels t
                                :search-second-lit t)
           (change-fraig-config *fraig-default-config*
                                :random-seed-name 'my-random-seed
                                :ctrex-queue-limit 32
                                :sim-words 1
                                :ctrex-force-resim nil
                                :ipasir-limit 1)

           (change-fraig-config *fraig-default-config*
                                :random-seed-name 'my-random-seed
                                :ctrex-queue-limit 32
                                :ipasir-limit 20)))

   (defattach fgl-aignet-transforms-config my-aignet-transforms-config)))
  
#||

;; This takes a long time if we don't use some kind of lane by lane observability trick.
(fgl::def-fgl-thm parallel-multiply-correct
  (equal (parallel-multiply-impl x y x0 y0 writemask)
         (parallel-multiply-spec x y writemask)))

||#


(encapsulate nil
  (local (def-fgl-rewrite top-level-equal-with-solve-lane-by-lane-masked
           (equal (top-level-equal x y)
                  (solve-lane-by-lane-masked x y
                                              (syntax-bind mask (g-var 'writemask))
                                              32))))
  (fgl::def-fgl-thm parallel-multiply-correct-masked
    (equal (parallel-multiply-impl x y x0 y0 writemask)
           (parallel-multiply-spec x y writemask))
    :hints (("Goal" :clause-processor replace-equal-with-top-level-equal))))


(encapsulate nil
  (local (def-fgl-rewrite top-level-equal-with-solve-lane-by-lane-masked+
           (equal (top-level-equal x y)
                  (solve-lane-by-lane-masked+ x y
                                              (syntax-bind mask (g-var 'writemask))
                                              32))))
  (fgl::def-fgl-thm parallel-multiply-correct-masked+
    (equal (parallel-multiply-impl x y x0 y0 writemask)
           (parallel-multiply-spec x y writemask))
    :hints (("Goal" :clause-processor replace-equal-with-top-level-equal))))
