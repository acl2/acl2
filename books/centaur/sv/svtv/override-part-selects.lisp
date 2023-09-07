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

(include-book "../svex/lattice")

(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))

(local (defthm logbitp-of-logeqv
         (equal (logbitp n (logeqv x y))
                (iff (logbitp n x) (logbitp n y)))))
(local (in-theory (disable logeqv)))

(local (defthm loghead-lemma
         (implies (and (equal -1 (logior (logand xu (lognot xl))
                                         (logand (logeqv xl yl)
                                                 (logeqv xu yu))))
                       (equal (loghead n xl)
                              (loghead n xu)))
                  (and (equal (loghead n yl) (loghead n xl))
                       (equal (loghead n yu) (loghead n xu))))
         :hints ((bitops::logbitp-reasoning))))



(defthmd svex-env-lookup-when-2vec-p-and-<<=
  (implies (and (svex-env-<<= env1 env2)
                (2vec-p (svex-env-lookup k env1)))
           (equal (svex-env-lookup k env2)
                  (svex-env-lookup k env1)))
  :hints (("goal" :use ((:instance svex-env-<<=-necc
                         (x env1) (y env2) (var k)))
           :in-theory (disable svex-env-<<=-necc))))

(encapsulate nil
  (defthmd zero-ext-equal-when-4vec-<<=-and-2vec-p
    (implies (and (4vec-<<= x y)
                  (sv::2vec-p (sv::4vec-zero-ext n x)))
             (equal (sv::4vec-zero-ext n y)
                    (sv::4vec-zero-ext n x)))
    :hints(("Goal" :in-theory (e/d (sv::4vec-zero-ext 4vec-<<=))
            :do-not-induct t))
    :otf-flg t)

  (defthmd zero-ext-equal-when-4vec-<<=-and-integerp
    (implies (and (4vec-<<= x y)
                  (integerp (sv::4vec-zero-ext n x)))
             (equal (sv::4vec-zero-ext n y)
                    (sv::4vec-zero-ext n x)))
    :hints(("Goal" :in-theory (e/d (4vec->upper 4vec->lower 4vec-fix))
            :use zero-ext-equal-when-4vec-<<=-and-2vec-p)))


  (defthmd zero-ext-of-svex-env-lookup-when-integerp-and-<<=
    (implies (and (svex-env-<<= env1 env2)
                  (integerp (sv::4vec-zero-ext n (svex-env-lookup k env1))))
             (equal (sv::4vec-zero-ext n (svex-env-lookup k env2))
                    (sv::4vec-zero-ext n (svex-env-lookup k env1))))
    :hints (("goal" :use ((:instance svex-env-<<=-necc
                           (x env1) (y env2) (var k)))
             :in-theory (e/d (zero-ext-equal-when-4vec-<<=-and-integerp)
                             (svex-env-<<=-necc))))))


(encapsulate nil

  (local (defthm loghead-logtail-lemma
           (implies (and (equal -1 (logior (logand xu (lognot xl))
                                           (logand (logeqv xl yl)
                                                   (logeqv xu yu))))
                         (equal (loghead w (logtail lsb xl))
                                (loghead w (logtail lsb xu))))
                    (and (equal (loghead w (logtail lsb yl))
                                (loghead w (logtail lsb xl)))
                         (equal (loghead w (logtail lsb yu))
                                (loghead w (logtail lsb xu)))))
           :hints ((bitops::logbitp-reasoning :prune-examples nil))))

  
  (local (defthm loghead-logapp-vs-ash-lemma
           (implies (posp w2)
                    (equal (equal (loghead w (logapp w2 -1 x))
                                  (loghead w (ash y w2)))
                           (zp w)))
           :hints (("goal" :expand ((:free (x) (loghead w x)))))))

  (defthmd part-select-equal-when-4vec-<<=-and-2vec-p
    (implies (and (4vec-<<= x y)
                  (sv::2vec-p (sv::4vec-part-select lsb w x)))
             (equal (sv::4vec-part-select lsb w y)
                    (sv::4vec-part-select lsb w x)))
    :hints(("Goal" :in-theory (e/d (sv::4vec-part-select 4vec-zero-ext 4vec-rsh 4vec-shift-core 4vec-concat 4vec-<<=))
            :do-not-induct t))
    :otf-flg t)

  (defthmd part-select-equal-when-4vec-<<=-and-integerp
    (implies (and (4vec-<<= x y)
                  (integerp (sv::4vec-part-select lsb w x)))
             (equal (sv::4vec-part-select lsb w y)
                    (sv::4vec-part-select lsb w x)))
    :hints(("Goal" :in-theory (e/d (4vec->upper 4vec->lower 4vec-fix))
            :use part-select-equal-when-4vec-<<=-and-2vec-p)))


  (defthmd part-select-of-svex-env-lookup-when-integerp-and-<<=
    (implies (and (svex-env-<<= env1 env2)
                  (integerp (sv::4vec-part-select lsb w (svex-env-lookup k env1))))
             (equal (sv::4vec-part-select lsb w (svex-env-lookup k env2))
                    (sv::4vec-part-select lsb w (svex-env-lookup k env1))))
    :hints (("goal" :use ((:instance svex-env-<<=-necc
                           (x env1) (y env2) (var k)))
             :in-theory (e/d (part-select-equal-when-4vec-<<=-and-integerp)
                             (svex-env-<<=-necc))))))



(encapsulate nil

  (local (defthm loghead-logtail-lemma
           (implies (and (equal -1 (logior (logand xu (lognot xl))
                                           (logand (logeqv xl yl)
                                                   (logeqv xu yu))))
                         (equal wu wl)
                         (equal (ash xu (- wl))
                                (ash xl (- wl))))
                    (and (equal (ash xl (- wl))
                                (ash yu (- wl)))
                         (equal (ash xl (- wl))
                                (ash yl (- wl)))
                         (equal (ash yl (- wl))
                                (ash yu (- wl)))))
           :hints ((bitops::logbitp-reasoning :prune-examples nil))))

  (defthmd rsh-equal-when-4vec-<<=-and-2vec-p
    (implies (and (4vec-<<= x y)
                  (sv::2vec-p (sv::4vec-rsh  w x)))
             (equal (sv::4vec-rsh w y)
                    (sv::4vec-rsh w x)))
    :hints(("Goal" :in-theory (e/d (sv::4vec-part-select 4vec-zero-ext 4vec-rsh 4vec-shift-core 4vec-concat 4vec-<<=))
            :do-not-induct t))
    :otf-flg t)

  (defthmd rsh-equal-when-4vec-<<=-and-integerp
    (implies (and (4vec-<<= x y)
                  (integerp (sv::4vec-rsh w x)))
             (equal (sv::4vec-rsh w y)
                    (sv::4vec-rsh w x)))
    :hints(("Goal" :in-theory (e/d (4vec->upper 4vec->lower 4vec-fix))
            :use rsh-equal-when-4vec-<<=-and-2vec-p)))


  (defthmd rsh-of-svex-env-lookup-when-integerp-and-<<=
    (implies (and (svex-env-<<= env1 env2)
                  (integerp (sv::4vec-rsh w (svex-env-lookup k env1))))
             (equal (sv::4vec-rsh w (svex-env-lookup k env2))
                    (sv::4vec-rsh w (svex-env-lookup k env1))))
    :hints (("goal" :use ((:instance svex-env-<<=-necc
                           (x env1) (y env2) (var k)))
             :in-theory (e/d (rsh-equal-when-4vec-<<=-and-integerp)
                             (svex-env-<<=-necc))))))

