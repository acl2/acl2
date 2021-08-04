; Centaur SV Hardware Verification Tutorial
; Copyright (C) 2016 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>


(in-package "SV")

(include-book "../svex/lists") ;fsm-base")
(include-book "../svex/alist-equiv")

(defprod svtv-probe
  ((signal svar-p)
   (time natp)))

(fty::defalist svtv-probealist :key-type svar :val-type svtv-probe :true-listp t)


(local (defthm svex-env-p-nth-of-svex-envlist
         (implies (svex-envlist-p x)
                  (svex-env-p (nth n x)))
         :hints(("Goal" :in-theory (enable svex-envlist-p)))))

(define svtv-probealist-extract ((probes svtv-probealist-p)
                                 ;; Should all be fast alists
                                 (vals svex-envlist-p))
  :returns (result svex-env-p)
  (b* (((when (atom probes)) nil)
       ((unless (mbt (consp (car probes))))
        (svtv-probealist-extract (cdr probes) vals))
       ((cons var (svtv-probe probe)) (car probes))
       (env (nth probe.time vals)))
    (cons (cons (svar-fix var)
                (svex-env-lookup probe.signal env))
          (svtv-probealist-extract (cdr probes) vals)))
  ///
  (defret lookup-of-<fn>
    (equal (svex-env-lookup name result)
           (b* ((look (hons-assoc-equal (svar-fix name) (svtv-probealist-fix probes)))
                ((unless look) (4vec-x))
                ((svtv-probe probe) (cdr look)))
             (svex-env-lookup probe.signal (nth probe.time vals))))
    :hints(("Goal" :in-theory (enable svtv-probealist-fix svex-env-lookup))))

  (defret boundp-of-<fn>
    (equal (svex-env-boundp name result)
           (and (hons-assoc-equal (svar-fix name) (svtv-probealist-fix probes)) t))
    :hints(("Goal" :in-theory (enable svex-env-boundp svtv-probealist-fix))))


  (defcong svex-envlists-similar equal (svtv-probealist-extract probes vals) 2)
  (local (in-theory (enable svtv-probealist-fix))))


(defsection svex-alistlist-eval-equiv
  (def-universal-equiv svex-alistlist-eval-equiv
    :qvars (n)
    :equiv-terms ((svex-alist-eval-equiv (nth n x))
                  (equal (len x)))
    :defquant t)

  (in-theory (disable svex-alistlist-eval-equiv svex-alistlist-eval-equiv-necc))

  (defcong svex-alistlist-eval-equiv svex-alist-eval-equiv (car x) 1
    :hints (("goal" :use ((:instance svex-alistlist-eval-equiv-necc (n 0) (y x-equiv))))))

  (defcong svex-alistlist-eval-equiv svex-alistlist-eval-equiv (cdr x) 1
    :hints (("goal" :use ((:instance svex-alistlist-eval-equiv-necc
                           (n (+ (nfix (svex-alistlist-eval-equiv-witness (cdr x) (cdr x-equiv))) 1))
                           (y x-equiv)))
             :expand ((:free (x y) (svex-alistlist-eval-equiv (cdr x) y))
                      (:free (x y) (svex-alistlist-eval-equiv y (cdr x)))))))

  (defcong svex-alistlist-eval-equiv svex-alist-eval-equiv (nth n x) 2
    :hints (("goal" :use ((:instance svex-alistlist-eval-equiv-necc (n n) (y x-equiv))))))

  (defcong svex-alistlist-eval-equiv svex-envlists-similar (svex-alistlist-eval x env) 1
    :hints ((witness)
            (and stable-under-simplificationp
                 '(:in-theory (enable svex-alistlist-eval-equiv))))))

;; (local (defthm svex-alist-eval-equiv-of-cons
;;          (implies (and (svex-alist-eval-equiv rest1 rest2)
;;                        (svex-eval-equiv v1 v2))
;;                   (equal (svex-alist-eval-equiv (cons (cons k v1) rest1)
;;                                                 (cons (cons k v2) rest2))

(local (defthm svex-alist-p-nth-of-svex-alistlist
         (implies (svex-alistlist-p x)
                  (svex-alist-p (nth n x)))
         :hints(("Goal" :in-theory (enable svex-alistlist-p)))))





(define svtv-probealist-extract-alist ((probes svtv-probealist-p)
                                       (vals svex-alistlist-p))
  :returns (result svex-alist-p)
  (b* (((when (atom probes)) nil)
       ((unless (mbt (consp (car probes))))
        (svtv-probealist-extract-alist (cdr probes) vals))
       ((cons var (svtv-probe probe)) (car probes))
       (alist (nth probe.time vals)))
    (cons (cons (svar-fix var)
                (or (svex-fastlookup probe.signal alist) (svex-x)))
          (svtv-probealist-extract-alist (cdr probes) vals)))
  ///
  (defret eval-of-<fn>
    (equal (svex-alist-eval result env)
           (svtv-probealist-extract probes (svex-alistlist-eval vals env)))
    :hints(("Goal" :in-theory (enable svtv-probealist-extract svex-alist-eval))))

  (defret eval-lookup-of-<fn>
    (equal (svex-eval (svex-lookup var result) env)
           (svex-env-lookup var (svtv-probealist-extract probes (svex-alistlist-eval vals env))))
    :hints(("Goal" :use eval-of-<fn>
            :in-theory (disable eval-of-<fn> <fn>
                                lookup-of-svtv-probealist-extract))))

  (local
   (defret lookup-exists-of-<fn>
     (iff (svex-lookup var result)
          (svex-env-boundp var (svtv-probealist-extract probes (svex-alistlist-eval vals env))))
    :hints(("Goal" :use eval-of-<fn>
            :in-theory (disable eval-of-<fn> <fn>)))))

  ;; (local
  ;;  (defret len-of-<fn>
  ;;    (equal (len result)
  ;;           (svex-env-boundp var (svtv-probealist-extract probes (svex-alistlist-eval vals env))))
  ;;   :hints(("Goal" :use eval-of-<fn>
  ;;           :in-theory (disable eval-of-<fn> <fn>)))))


  (defcong svex-alistlist-eval-equiv svex-alist-eval-equiv (svtv-probealist-extract-alist probes vals) 2
    :hints (("goal" :in-theory (disable svtv-probealist-extract-alist))
            (witness) (witness)))

  (local (in-theory (enable svtv-probealist-fix))))


(local (defthm svarlist-list-p-of-update-nth
         (implies (and (svarlist-list-p x)
                       (svarlist-p v))
                  (svarlist-list-p (update-nth n v x)))
         :hints(("Goal" :in-theory (enable update-nth svarlist-list-p)))))

(local (defthm svarlist-p-of-nth
         (implies (svarlist-list-p x)
                  (svarlist-p (nth n x)))
         :hints(("Goal" :in-theory (enable nth svarlist-p)))))

(define svtv-probealist-outvars ((probes svtv-probealist-p))
  :returns (outvars svarlist-list-p)
  (b* (((when (atom probes)) nil)
       ((unless (mbt (consp (car probes))))
        (svtv-probealist-outvars (cdr probes)))
       (rest (svtv-probealist-outvars (cdr probes)))
       ((cons ?var (svtv-probe probe)) (car probes))
       (vars1 (nth probe.time rest)))
    (update-nth probe.time (cons probe.signal vars1) rest))
  ///
  (defret member-of-<fn>
    (iff (member var (nth time outvars))
         (and (svar-p var)
              (rassoc-equal (make-svtv-probe :signal var :time time)
                            (svtv-probealist-fix probes))))
    :hints(("Goal" :in-theory (enable svtv-probealist-fix))))

  (local (in-theory (enable svtv-probealist-fix))))
