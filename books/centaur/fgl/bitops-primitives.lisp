; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
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

(include-book "primitives")
(include-book "bitops")
(local (include-book "primitive-lemmas"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (std::add-default-post-define-hook :fix))


(def-formula-checks bitops-formula-checks
  (logapp acl2::logmask$inline acl2::logtail$inline acl2::loghead$inline logbitp))



(local (defthm fgl-objectlist-eval-when-atom
         (implies (not (consp x))
                  (equal (fgl-objectlist-eval x env) nil))
         :hints(("Goal" :in-theory (enable fgl-objectlist-eval)))))

(local (defthm gobj-bfr-list-eval-of-append
         (equal (gobj-bfr-list-eval (append x y) env)
                (append (gobj-bfr-list-eval x env)
                        (gobj-bfr-list-eval y env)))
         :hints(("Goal" :in-theory (enable gobj-bfr-list-eval)))))

(local (defthm gobj-bfr-list-eval-of-repeat
         (equal (gobj-bfr-list-eval (acl2::repeat n x) env)
                (acl2::repeat n (gobj-bfr-eval x env)))
         :hints(("Goal" :in-theory (enable gobj-bfr-list-eval acl2::repeat)))))

(local (defthm gobj-bfr-list-eval-of-take
         (equal (gobj-bfr-list-eval (take n x) env)
                (take n (gobj-bfr-list-eval x env)))
         :hints(("Goal" :in-theory (e/d (gobj-bfr-list-eval take acl2::default-cdr)
                                        (acl2::take-of-zero
                                         acl2::take-of-too-many))))))

(local (defthm bools->int-of-append
         (implies (consp y)
                  (equal (bools->int (append x y))
                         (logapp (len x) (bools->int x) (bools->int y))))
         :hints(("Goal" :in-theory (enable bools->int
                                           bitops::logapp**
                                           bitops::loghead**
                                           append len)))))

(local (defthm logcons-bit-identity
         (implies (bitp b)
                  (equal (logcons b (- b))
                         (- b)))
         :hints(("Goal" :in-theory (enable bitp)))))

(local (defthm logcdr-neg-bit-identity
         (implies (bitp b)
                  (equal (logcdr (- b))
                         (- b)))
         :hints(("Goal" :in-theory (enable bitp)))))

(define extend-bits ((n natp) x)
  :guard-hints (("goal" :in-theory (enable default-car)))
  (b* (((when (zp n)) nil)
       (first (mbe :logic (car x)
                   :exec (and (consp x) (car x))))
       ((when (eql n 1)) (list first))
       ((when (or (atom x) (atom (cdr x))))
        (cons first (extend-bits (1- n) x))))
    (cons first (extend-bits (1- n) (cdr x))))
  ///
  (defthm len-of-extend-bits
    (Equal (len (extend-bits n x)) (nfix n)))

  (defthm consp-of-extend-bits
    (Equal (consp (extend-bits n x))
           (posp n)))

  (defthm bools->int-of-extend-bits
    (equal (bools->int (extend-bits n x))
           (if (zp n)
               0
             (logext n (bools->int x))))
    :hints(("Goal" :in-theory (enable bools->int bitops::logext**))))

  
  (local (defthm gobj-bfr-list-eval-under-iff
           (iff (gobj-bfr-list-eval x env)
                (consp x))
           :hints(("Goal" :in-theory (enable gobj-bfr-list-eval)))))

  (defthm gobj-bfr-list-eval-of-extend-bits
    (equal (gobj-bfr-list-eval (extend-bits n x) env)
           (extend-bits n (gobj-bfr-list-eval x env)))
    :hints(("Goal" :in-theory (enable gobj-bfr-list-eval))))

  (defthm member-of-extend-bits
    (implies (and (not (member v x))
                  v)
             (not (member v (extend-bits n x))))))

(local (defthm bools->int-of-repeat
         (equal (bools->int (acl2::repeat n x))
                (if (zp n)
                    0
                  (- (bool->bit x))))
         :hints(("Goal" :in-theory (enable bools->int acl2::repeat)))))

(local (defthm logapp-bools->int-of-extend-bits
         (equal (logapp n (bools->int (extend-bits n x)) y)
                (logapp n (bools->int x) y))
         :hints(("Goal" :in-theory (enable bools->int
                                           bitops::logapp**
                                           bitops::logext**
                                           take)))))

(local (defthm fgl-object-eval-when-atom-gobj-syntactic-integer->bits
         (b* (((mv ok fix) (gobj-syntactic-integer-fix x)))
           (implies (and ok
                         (not (gobj-syntactic-integer->bits fix)))
                    (acl2::int-equiv (fgl-object-eval x env) 0)))
         :hints (("goal" :use ((:instance fgl-object-eval-of-gobj-syntactic-integer-fix))
                  :in-theory (disable fgl-object-eval-of-gobj-syntactic-integer-fix)))))

(local (in-theory (enable bitops::logapp** bitops::loghead** bitops::logtail**)))

(set-ignore-ok t)

(def-gl-primitive logapp (width lsbs msbs)
  (b* (((unless (gl-object-case width :g-concrete))
        (mv nil nil interp-st))
       ((mv ok lsbs) (gobj-syntactic-integer-fix lsbs))
       ((unless ok) (mv nil nil interp-st))
       ((mv ok msbs) (gobj-syntactic-integer-fix msbs))
       ((unless ok) (mv nil nil interp-st))
       (lsb-bits (gobj-syntactic-integer->bits lsbs))
       (msb-bits (gobj-syntactic-integer->bits msbs)))
    (mv t (mk-g-integer (append (extend-bits (nfix (g-concrete->val width))
                                             lsb-bits)
                                (if (atom msb-bits) '(nil) msb-bits)))
        interp-st))
  :formula-check bitops-formula-checks)

(define tail-bits ((n natp) x)
  (b* (((when (zp n)) x)
       ((when (mbe :logic (atom (cdr x))
                   :exec (or (atom x) (atom (cdr x)))))
        x))
    (tail-bits (1- n) (cdr x)))
  ///
  (local (defthm logtail-neg-bit
           (implies (bitp b)
                    (equal (logtail n (- b))
                           (- b)))
           :hints(("Goal" :in-theory (enable* bitops::logtail**
                                              bitops::ihsext-inductions)))))

  (defthm bools->int-of-tail-bits
    (equal (bools->int (tail-bits n x))
           (logtail n (bools->int x)))
    :hints(("Goal" :in-theory (enable bools->int bitops::logtail**))))

  

  (defthm gobj-bfr-list-eval-of-tail-bits
    (equal (gobj-bfr-list-eval (tail-bits n x) env)
           (tail-bits n (gobj-bfr-list-eval x env)))
    :hints(("Goal" :in-theory (enable gobj-bfr-list-eval))))

  (defthm member-of-tail-bits
    (implies (not (member v x))
             (not (member v (tail-bits n x)))))

  (defthm true-listp-of-tail-bits
    (iff (true-listp (tail-bits n x))
         (true-listp x))))

(def-gl-primitive acl2::logtail$inline (n x)
  (b* (((unless (gl-object-case n :g-concrete))
        (mv nil nil interp-st))
       ((mv ok x) (gobj-syntactic-integer-fix x))
       ((unless ok) (mv nil nil interp-st))
       (x-bits (gobj-syntactic-integer->bits x)))
    (mv t (mk-g-integer (tail-bits (nfix (g-concrete->val n)) x-bits))
        interp-st))
  :formula-check bitops-formula-checks)



(local (install-gl-primitives logapp))
(remove-gl-rewrite logapp-const-width)
(remove-gl-rewrite logtail-const-shift)

(def-gl-rewrite logapp-const-width-allow-primitive
  (implies (syntaxp (and (integerp n)
                         ;; Allow this only when x is a g-var or g-apply, so
                         ;; that the primitive would fail but this can
                         ;; potentially generate bits for x.
                         (gl-object-case x '(:g-var :g-apply))))
           (equal (logapp n x y)
                  (cond ((zp n) (int y))
                        (t (intcons (and (intcar x) t)
                                    (logapp (1- n) (intcdr x) y))))))
  :hints(("Goal" :in-theory (enable intcons intcar intcdr int-endp
                                    bitops::logapp**))))

