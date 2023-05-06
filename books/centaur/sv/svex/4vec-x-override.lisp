; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2022 Intel Corporation
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "SV")

(include-book "lattice")
(include-book "env-ops")
(local (include-book "centaur/bitops/ihsext-basics" :dir :System))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :System))
(local (std::add-default-post-define-hook :fix))


(define 4vec-x-override ((a 4vec-p)
                         (b 4vec-p))
  ;; For each bit, the result is the corresp bit of a unless that bit is x, else the corresponding bit of b.
  :returns (res 4vec-p)
  (b* (((4vec a))
       ((4vec b))
       (a-non-x-mask (logior (lognot a.upper) a.lower)))
    (4vec (logior (logand a-non-x-mask a.upper)
                  (logandc1 a-non-x-mask b.upper))
          (logior (logand a-non-x-mask a.lower)
                  (logandc1 a-non-x-mask b.lower))))
  ///
  (defret 4vec-bit-index-of-<fn>
    (equal (4vec-bit-index n res)
           (b* ((an (4vec-bit-index n a)))
             (if (equal an (4vec-1x))
                 (4vec-bit-index n b)
               an)))
    :hints(("Goal" :in-theory (enable 4vec-bit-index))))

  (defret 4vec-x-override->>=-a
    (4vec-<<= a res)
    :hints(("Goal" :in-theory (enable 4vec-<<=))
           (bitops::logbitp-reasoning)))

  (defret 4vec-x-override-when-a-<<=-b
    (implies (4vec-<<= a b)
             (equal res (4vec-fix b)))
    :hints(("Goal" :in-theory (enable 4vec-<<=))
           (bitops::logbitp-reasoning)))

  (defthm 4vec-x-override-of-x
    (and (equal (4vec-x-override (4vec-x) b) (4vec-fix b))
         (equal (4vec-x-override a (4vec-x)) (4vec-fix a)))
    :hints ((bitops::logbitp-reasoning)))

  (defthm 4vec-x-override-monotonic-on-b
    (implies (4vec-<<= b1 b2)
             (4vec-<<= (4vec-x-override a b1)
                       (4vec-x-override a b2)))
    :hints(("Goal" :in-theory (enable 4vec-<<=))
           (bitops::logbitp-reasoning))))


(define svex-env-x-override ((a svex-env-p) (b svex-env-p))
  :returns (res svex-env-p)
  (if (atom b)
      (svex-env-fix a)
    (if (mbt (and (consp (car b))
                  (svar-p (caar b))))
        (cons (cons (caar b)
                    (4vec-x-override (svex-env-lookup (caar b) a) (cdar b)))
              (svex-env-x-override a (cdr b)))
      (svex-env-x-override a (cdr b))))
  ///
  (defret lookup-in-<fn>
    (equal (svex-env-lookup v res)
           (4vec-x-override (svex-env-lookup v a)
                            (svex-env-lookup v b)))
    :hints(("Goal" :in-theory (enable svex-env-lookup))))

  (defret boundp-of-<fn>
    (equal (svex-env-boundp v res)
           (or (svex-env-boundp v b)
               (svex-env-boundp v a)))
    :hints(("Goal" :in-theory (enable svex-env-boundp))))

  (defret <fn>-when-a-<<=-b
    (implies (svex-env-<<= a b)
             (svex-envs-similar res b))
    :hints(("Goal" :in-theory (enable svex-envs-similar))))

  (defret <fn>-when-b-nil
    :pre-bind ((b nil))
    (equal res (svex-env-fix a)))

  (defret <fn>-when-b-empty
    (implies (svex-envs-similar b nil)
             (svex-envs-similar res a))
    :hints(("Goal" :in-theory (disable <fn>))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause)))))))

  (defret <fn>-lower-bound
    (svex-env-<<= a res)
    :hints(("Goal" :in-theory (e/d (svex-env-<<=)
                                   (<fn>)))))

  (defthm svex-env-x-override-monotonic-on-b
    (implies (svex-env-<<= b1 b2)
             (svex-env-<<= (svex-env-x-override a b1)
                           (svex-env-x-override a b2)))
    :hints(("Goal" :in-theory (e/d (svex-env-<<=)
                                   (svex-env-x-override)))))

  (local (in-theory (enable svex-env-fix))))
