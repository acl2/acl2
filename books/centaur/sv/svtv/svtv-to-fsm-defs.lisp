; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2023 Intel Corporation
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


(include-book "svtv-generalize-defs")
(local (std::add-default-post-define-hook :fix))

(define svar/4vec-p (x)
  :short "Recognizer for an object that is either an @(see svar) or @(see 4vec)"
  (or (svar-p x) (4vec-p x)))

(define svar/4vec-kind ((x svar/4vec-p))
  :parents (svar/4vec-p)
  :short "Kind function for svar/4vec type"
  :returns (kind (and (symbolp kind)
                      (not (booleanp kind)))
                 :rule-classes :type-prescription)
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable svar/4vec-p svar-p 4vec-p))))
  (if (consp x)
      (if (integerp (car x))
          :4vec
        :svar)
    (if (integerp x) :4vec (if (mbt (and x t)) :svar :4vec)))
  ///
  (defthm svar/4vec-kind-possibilities
    (or (equal (svar/4vec-kind x) :4vec)
        (equal (svar/4vec-kind x) :svar))
    :rule-classes ((:forward-chaining :trigger-terms ((svar/4vec-kind x)))))
  
  (defthm svar/4vec-p-when-when-kind-is-4vec
    (implies (equal (svar/4vec-kind x) :4vec)
             (equal (svar/4vec-p x) (4vec-p x)))
    :hints(("Goal" :in-theory (enable svar/4vec-p svar-p))))

  (defthm svar/4vec-p-when-when-kind-is-svar
    (implies (equal (svar/4vec-kind x) :svar)
             (equal (svar/4vec-p x) (svar-p x)))
    :hints(("Goal" :in-theory (enable svar/4vec-p 4vec-p))))

  (defthm svar/4vec-kind-when-svar-p
    (implies (svar-p x)
             (Equal (svar/4vec-kind x) :svar))
    :hints(("Goal" :in-theory (enable svar-p))))

  (defthm svar/4vec-kind-when-4vec-p
    (implies (4vec-p x)
             (Equal (svar/4vec-kind x) :4vec))
    :hints(("Goal" :in-theory (enable 4vec-p)))))

(defmacro svar/4vec-case (x &rest args)
  (fty::kind-casemacro-fn x args
                          '(svar/4vec-case svar/4vec-kind (:4vec 4vec) (:svar svar))))

(define svar/4vec-fix ((x svar/4vec-p))
  :returns (new-x svar/4vec-p :hints(("Goal" :in-theory (enable svar/4vec-p))))
  :parents (svar/4vec-p)
  :short "Fixing function for svar/4vec type"
  :hooks nil
  (mbe :logic (if (eq (svar/4vec-kind x) :4vec)
                  (4vec-fix x)
                (svar-fix x))
       :exec x)
  ///

  (defthm svar/4vec-fix-when-svar/4vec-p
    (implies (svar/4vec-p x)
             (equal (svar/4vec-fix x) x)))

  (fty::deffixtype svar/4vec :pred svar/4vec-p :fix svar/4vec-fix :equiv svar/4vec-equiv :define t)

  (defthm svar/4vec-fix-when-kind-is-4vec
    (implies (equal (svar/4vec-kind x) :4vec)
             (equal (svar/4vec-fix x) (4vec-fix x))))
  
  (defthm svar/4vec-fix-when-kind-is-svar
    (implies (equal (svar/4vec-kind x) :svar)
             (equal (svar/4vec-fix x) (svar-fix x))))

  (fty::deffixequiv svar/4vec-kind))


(defthm svex-p-when-svar/4vec-p
  (implies (svar/4vec-p x)
           (svex-p x))
  :hints(("Goal" :in-theory (enable svar/4vec-p svar-p 4vec-p svex-p))))

(defthm svar/4vec-p-when-svex-p
  (implies (and (not (svex-case x :call))
                (svex-p x))
           (svar/4vec-p x))
  :hints(("Goal" :in-theory (enable svar/4vec-p svar-p 4vec-p svex-p svex-kind))))

(defthm svar/4vec-fix-of-svex-fix
  (implies (not (svex-case x :call))
           (equal (svar/4vec-fix (svex-fix x))
                  (svar/4vec-fix x)))
  :hints(("Goal" :in-theory (enable svar/4vec-fix svex-fix svex-kind
                                    svar/4vec-kind)
          :expand ((svex-fix x)))))

(defthmd svar/4vec-fix-in-terms-of-svex-fix
  (implies (not (svex-case x :call))
           (equal (svar/4vec-fix x)
                  (svex-fix x)))
  :hints(("Goal" :in-theory (enable svar/4vec-fix svex-fix svex-kind
                                    svar/4vec-kind)
          :expand ((svex-fix x)))))

(defthmd svar/4vec-kind-when-svex-kind
  (implies (not (svex-case x :call))
           (equal (svar/4vec-kind x)
                  (if (equal (svex-kind x) :quote) :4vec :svar)))
  :hints(("Goal" :in-theory (enable svex-kind svar/4vec-kind))))

(define svar/4vec-eval ((x svar/4vec-p) (env svex-env-p))
  :returns (val 4vec-p)
  (svar/4vec-case x
    :4vec (4vec-fix x)
    :svar (svex-env-lookup x env))
  ///
  (defthmd svar/4vec-eval-in-terms-of-svex-eval
    (implies (not (svex-case x :call))
             (equal (svar/4vec-eval x env)
                    (svex-eval x env)))
    :hints (("goal" :expand ((svex-eval x env))
             :in-theory (enable svex-var->name svex-quote->val
                                svar/4vec-kind-when-svex-kind))))

  (defthm svar/4vec-eval-of-quote
    (implies (syntaxp (quotep x))
             (equal (svar/4vec-eval x env)
                    (svar/4vec-case x
                      :4vec (4vec-fix x)
                      :svar (svex-env-lookup x env))))))

(fty::defmap svar/4vec-alist :key-type svar :val-type svar/4vec-p :true-listp t)

(defthm svex-alist-p-when-svar/4vec-alist-p
  (implies (svar/4vec-alist-p x)
           (svex-alist-p x))
  :hints(("Goal" :in-theory (enable svar/4vec-alist-p svex-alist-p))))


(defthm svar/4vec-alist-p-when-svex-alist-p
  (implies (and (svex-alist-noncall-p x)
                (svex-alist-p x))
           (svar/4vec-alist-p x))
  :hints(("Goal" :in-theory (enable svex-alist-noncall-p
                                    svex-alist-p
                                    svar/4vec-alist-p))))

(defthm svar/4vec-alist-fix-of-svex-alist-fix
  (implies (svex-alist-noncall-p x)
           (equal (svar/4vec-alist-fix (svex-alist-fix x))
                  (svar/4vec-alist-fix x)))
  :hints(("Goal" :in-theory (enable svar/4vec-alist-fix svex-alist-fix
                                    svex-alist-noncall-p
                                    svar/4vec-fix-in-terms-of-svex-fix))))

(defthmd svar/4vec-alist-fix-in-terms-of-svex-alist-fix
  (implies (svex-alist-noncall-p x)
           (equal (svar/4vec-alist-fix x)
                  (svex-alist-fix x)))
  :hints(("Goal" :in-theory (enable svar/4vec-alist-fix svex-alist-fix
                                    svex-alist-noncall-p
                                    svar/4vec-fix-in-terms-of-svex-fix))))

(define svar/4vec-alist-eval ((x svar/4vec-alist-p) (env svex-env-p))
  :returns (val svex-env-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (svar/4vec-alist-eval (cdr x) env)))
    (cons (cons (caar x) (svar/4vec-eval (cdar x) env))
          (svar/4vec-alist-eval (cdr x) env)))
  ///
  (defthmd svar/4vec-alist-eval-in-terms-of-svex-alist-eval
    (implies (svex-alist-noncall-p x)
             (equal (svar/4vec-alist-eval x env)
                    (svex-alist-eval x env)))
    :hints(("Goal" :in-theory (enable svex-alist-eval
                                      svex-alist-noncall-p
                                      svar/4vec-eval-in-terms-of-svex-eval))))

  (defret svex-env-lookup-of-<fn>
    (equal (svex-env-lookup v val)
           (let ((look (hons-assoc-equal (svar-fix v) (svar/4vec-alist-fix x))))
             (if look
                 (svar/4vec-eval (cdr look) env)
               (4vec-x))))
    :hints(("Goal" :in-theory (enable svex-env-lookup-of-cons))))
  
  (local (in-theory (enable svar/4vec-alist-fix))))
       

(fty::deflist svar/4vec-alistlist :elt-type svar/4vec-alist :true-listp t)

(defthm svex-alistlist-p-when-svar/4vec-alistlist-p
  (implies (svar/4vec-alistlist-p x)
           (svex-alistlist-p x))
  :hints(("Goal" :in-theory (enable svar/4vec-alistlist-p svex-alistlist-p))))


(defthm svar/4vec-alistlist-p-when-svex-alistlist-p
  (implies (and (svex-alistlist-noncall-p x)
                (svex-alistlist-p x))
           (svar/4vec-alistlist-p x))
  :hints(("Goal" :in-theory (enable svex-alistlist-noncall-p
                                    svex-alistlist-p
                                    svar/4vec-alistlist-p))))

(defthm svar/4vec-alistlist-fix-of-svex-alistlist-fix
  (implies (svex-alistlist-noncall-p x)
           (equal (svar/4vec-alistlist-fix (svex-alistlist-fix x))
                  (svar/4vec-alistlist-fix x)))
  :hints(("Goal" :in-theory (enable svar/4vec-alistlist-fix svex-alistlist-fix
                                    svex-alistlist-noncall-p
                                    svar/4vec-alist-fix-in-terms-of-svex-alist-fix))))

(defthmd svar/4vec-alistlist-fix-in-terms-of-svex-alistlist-fix
  (implies (svex-alistlist-noncall-p x)
           (equal (svar/4vec-alistlist-fix x)
                  (svex-alistlist-fix x)))
  :hints(("Goal" :in-theory (enable svar/4vec-alistlist-fix svex-alistlist-fix
                                    svex-alistlist-noncall-p
                                    svar/4vec-alist-fix-in-terms-of-svex-alist-fix))))

(define svar/4vec-alistlist-eval ((x svar/4vec-alistlist-p) (env svex-env-p))
  :returns (val svex-envlist-p)
  (if (atom x)
      nil
    (cons (svar/4vec-alist-eval (car x) env)
          (svar/4vec-alistlist-eval (cdr x) env)))
  ///
  (defthmd svar/4vec-alistlist-eval-in-terms-of-svex-alistlist-eval
    (implies (svex-alistlist-noncall-p x)
             (equal (svar/4vec-alistlist-eval x env)
                    (svex-alistlist-eval x env)))
    :hints(("Goal" :in-theory (enable svex-alistlist-eval
                                      svex-alistlist-noncall-p
                                      svar/4vec-alist-eval-in-terms-of-svex-alist-eval)))))
  



(defprod lhprobe
  :short "Product type bundling an LHS (some list of FSM signal segments), a
time step, and a Boolean indicating signedness, signifying the concatenated
value of those segments at that time."
  :long "<p>These are used for mapping FSM signals to SVTV variables. The
signedness is relevant because of peculiarities of SVTV theorems.  In SVTV
runs, only a lower segment of the bits of any given variable are relevant, but
theorems about SVTV runs tend to specify the signedness of the variable.  E.g.,
many input variables are assumed unsigned-byte-p of some size, and
override-test variables are usually assumed to be -1 or 0.  Thus we need to map
the relevant portions of the FSM variables sometimes to unsigned and sometimes
to signed values.</p>"
  ((lhs lhs-p)
   (stage natp :rule-classes :type-prescription)
   (signedp booleanp :rule-classes :type-prescription))
  :layout :fulltree)


(defthm lhatom-eval-zero-when-envs-agree
  (implies (svex-envs-agree (lhatom-vars x) env1 env2)
           (equal (lhatom-eval-zero x env1)
                  (lhatom-eval-zero x env2)))
  :hints(("Goal" :in-theory (enable lhatom-eval-zero
                                    lhatom-vars)
          :expand ((:free (v) (svex-envs-agree (list v) env1 env2))))))

(define lhs-eval-ext ((x lhs-p) (env svex-env-p))
  :returns (val 4vec-p)
  (if (atom x)
      0
    (if (atom (cdr x))
        (4vec-sign-ext (2vec (lhrange->w (car x)))
                       (lhatom-eval-zero (lhrange->atom (car x)) env))
      (4vec-concat (2vec (lhrange->w (car x)))
                   (lhatom-eval-zero (lhrange->atom (car x)) env)
                   (lhs-eval-ext (cdr x) env))))
  ///
  (defcong svex-envs-similar equal (lhs-eval-ext x env) 2
    :hints(("Goal" :in-theory (enable lhatom-eval-zero)))))

(defthm lhs-eval-zero-when-envs-agree
  (implies (svex-envs-agree (lhs-vars x) env1 env2)
           (equal (lhs-eval-zero x env1)
                  (lhs-eval-zero x env2)))
  :hints(("Goal" :in-theory (enable lhs-eval-zero
                                    lhs-vars))))

(defthm lhs-eval-ext-when-envs-agree
  (implies (svex-envs-agree (lhs-vars x) env1 env2)
           (equal (lhs-eval-ext x env1)
                  (lhs-eval-ext x env2)))
  :hints(("Goal" :in-theory (enable lhs-eval-ext
                                    lhs-vars))))

(define svex-envlists-agree ((vars svarlist-p)
                             (x svex-envlist-p)
                             (y svex-envlist-p))
  (if (atom x)
      (atom y)
    (and (consp y)
         (svex-envs-agree vars (car x) (car y))
         (svex-envlists-agree vars (cdr x) (cdr y))))
  ///
  (defthm svex-envs-agree-nth-when-svex-envlists-agree
    (implies (svex-envlists-agree vars x y)
             (svex-envs-agree vars (nth n x) (nth n y))))

  (defthm svex-envlists-agree-of-append-vars
    (iff (svex-envlists-agree (append vars1 vars2) x y)
         (and (svex-envlists-agree vars1 x y)
              (svex-envlists-agree vars2 x y)))))





(define lhprobe-eval ((x lhprobe-p)
                      (envs svex-envlist-p))
  :parents (lhprobe)
  :short "Evaluator for an @(see lhprobe) with respect to an envlist giving the values of signals over time."
  :returns (val 4vec-p)
  (b* (((lhprobe x))
       (env (nth x.stage envs)))
    (if x.signedp
        (lhs-eval-ext x.lhs env)
      (lhs-eval-zero x.lhs env)))
  ///
  (local (in-theory (disable take)))
  (local (include-book "std/lists/nth" :dir :system))
  (defthm lhprobe-eval-of-take
    (implies (< (lhprobe->stage x) (nfix n))
             (equal (lhprobe-eval x (take n envs))
                    (lhprobe-eval x envs)))))



(define lhprobe-vars ((x lhprobe-p))
  :parents (lhprobe)
  :short "Collect variables present in an lhprobe"
  :returns (vars svarlist-p)
  (b* (((lhprobe x)))
    (lhs-vars x.lhs))
  ///


  (defthm svex-env-extract-nil-under-svex-envs-similar
    (svex-envs-similar (svex-env-extract vars nil) nil)
    :hints(("Goal" :in-theory (enable svex-envs-similar))))
  
  (defthm nth-of-svex-envlist-extract
    (svex-envs-similar (nth n (svex-envlist-extract-keys vars x))
                       (svex-env-extract vars (nth n x)))
    :hints(("Goal" :in-theory (enable svex-envlist-extract-keys))))


  (defthm lhs-eval-ext-of-svex-env-extract
    (implies (subsetp-equal (lhs-vars x) (Svarlist-fix vars))
             (equal (lhs-eval-ext x (svex-env-extract vars env))
                    (lhs-eval-ext x env)))
    :hints(("Goal" :in-theory (enable lhs-eval-ext
                                      lhatom-vars
                                      lhatom-eval-zero))))

  (defthm lhs-eval-zero-of-svex-env-extract
    (implies (subsetp-equal (lhs-vars x) (Svarlist-fix vars))
             (equal (lhs-eval-zero x (svex-env-extract vars env))
                    (lhs-eval-zero x env)))
    :hints(("Goal" :in-theory (enable lhs-eval-zero
                                      lhatom-vars
                                      lhatom-eval-zero))))
  
  (defthm lhprobe-eval-of-svex-envlist-extract-vars
    (implies (subsetp-equal (lhprobe-vars x) (Svarlist-fix vars))
             (equal (lhprobe-eval x (svex-envlist-extract-keys vars envs))
                    (lhprobe-eval x envs)))
    :hints(("Goal" :in-theory (enable lhprobe-eval))))

  (defthm lhprobe-eval-when-envs-agree
    (implies (svex-envlists-agree (lhprobe-vars x) envs1 envs2)
             (equal (lhprobe-eval x envs1)
                    (lhprobe-eval x envs2)))
    :hints(("Goal" :in-theory (enable lhprobe-eval
                                      lhprobe-vars))
           (and stable-under-simplificationp
                '(:use ((:instance lhs-eval-ext-when-envs-agree
                         (x (lhprobe->lhs x))
                         (env1 (nth (lhprobe->stage x) envs1))
                         (env2 (nth (lhprobe->stage x) envs2)))
                        (:instance lhs-eval-zero-when-envs-agree
                         (x (lhprobe->lhs x))
                         (env1 (nth (lhprobe->stage x) envs1))
                         (env2 (nth (lhprobe->stage x) envs2)))))))))


(define lhprobe-change-override ((x lhprobe-p)
                                 (type svar-overridetype-p))
  :returns (new-x lhprobe-p)
  (change-lhprobe x :lhs (lhs-change-override (lhprobe->lhs x) type)))



(fty::defmap lhprobe-map :key-type svar :val-type lhprobe :true-listp t
  :short "Mapping from variables to lhprobes, identifying SVTV variables with signals at a time")

(define lhprobe-map-eval ((x lhprobe-map-p)
                          (envs svex-envlist-p))
  :returns (eval svex-env-p)
  (b* (((when (atom x))
        nil)
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (lhprobe-map-eval (cdr x) envs)))
    (cons (cons (caar x) (lhprobe-eval (cdar x) envs))
          (lhprobe-map-eval (cdr x) envs)))
  ///
  (defret lookup-of-<fn>
    (equal (svex-env-lookup v eval)
           (let ((look (hons-assoc-equal (svar-fix v) (lhprobe-map-fix x))))
             (if look
                 (lhprobe-eval (cdr look) envs)
               (4vec-x))))
    :hints(("Goal" :in-theory (enable svex-env-lookup-of-cons))))
  (local (in-theory (enable lhprobe-map-fix))))


(define lhprobe-map-vars ((x lhprobe-map-p))
  :parents (lhprobe)
  :short "Collect variables present in an lhprobe-map"
  :returns (vars svarlist-p)
  (b* (((when (atom x))
        nil)
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (lhprobe-map-vars (cdr x))))
    (append (lhprobe-vars (cdar x))
            (lhprobe-map-vars (cdr x))))
  ///
  (local (include-book "std/lists/sets" :dir :system))
  (defthm lhprobe-map-eval-of-svex-envlist-extract-vars
    (implies (subsetp-equal (lhprobe-map-vars x) (Svarlist-fix vars))
             (equal (lhprobe-map-eval x (svex-envlist-extract-keys vars envs))
                    (lhprobe-map-eval x envs)))
    :hints(("Goal" :in-theory (enable lhprobe-map-eval))))

  (local (in-theory (enable lhprobe-map-fix)))

  (defthm lhprobe-map-eval-when-envs-agree
    (implies (svex-envlists-agree (lhprobe-map-vars x) envs1 envs2)
             (equal (lhprobe-map-eval x envs1)
                    (lhprobe-map-eval x envs2)))
    :hints(("Goal" :in-theory (enable lhprobe-map-eval
                                      lhprobe-map-vars)))))
       


(define lhprobe/4vec-p (x)
  :short "Recognizer for an object that is either a @(see lhprobe) or @(see 4vec)."
  (or (lhprobe-p x) (4vec-p x)))

(define lhprobe/4vec-kind ((x lhprobe/4vec-p))
  :parents (lhprobe/4vec-p)
  :short "Kind function for lhprobe/4vec type"
  :returns (kind (and (symbolp kind)
                      (not (booleanp kind)))
                 :rule-classes :type-prescription)
  (if (or (atom x)
          (integerp (car x)))
      :4vec
    :lhprobe)
  ///
  (defthm lhprobe/4vec-kind-possibilities
    (or (equal (lhprobe/4vec-kind x) :4vec)
        (equal (lhprobe/4vec-kind x) :lhprobe))
    :rule-classes ((:forward-chaining :trigger-terms ((lhprobe/4vec-kind x)))))
  
  (defthm lhprobe/4vec-p-when-when-kind-is-4vec
    (implies (equal (lhprobe/4vec-kind x) :4vec)
             (equal (lhprobe/4vec-p x) (4vec-p x)))
    :hints(("Goal" :in-theory (enable lhprobe/4vec-p lhprobe-p))))

  (defthm lhprobe/4vec-p-when-when-kind-is-lhprobe
    (implies (equal (lhprobe/4vec-kind x) :lhprobe)
             (equal (lhprobe/4vec-p x) (lhprobe-p x)))
    :hints(("Goal" :in-theory (enable lhprobe/4vec-p 4vec-p))))

  (defthm lhprobe/4vec-kind-when-lhprobe-p
    (implies (lhprobe-p x)
             (Equal (lhprobe/4vec-kind x) :lhprobe))
    :hints(("Goal" :in-theory (enable lhprobe-p))))

  (defthm lhprobe/4vec-kind-when-4vec-p
    (implies (4vec-p x)
             (Equal (lhprobe/4vec-kind x) :4vec))
    :hints(("Goal" :in-theory (enable 4vec-p)))))

(defmacro lhprobe/4vec-case (x &rest args)
  (fty::kind-casemacro-fn x args
                          '(lhprobe/4vec-case lhprobe/4vec-kind (:4vec 4vec) (:lhprobe lhprobe))))

(define lhprobe/4vec-fix ((x lhprobe/4vec-p))
  :parents (lhprobe/4vec-p)
  :hooks nil
  :short "Fixing function for lhprobe/4vec type"
  :returns (new-x lhprobe/4vec-p :hints(("Goal" :in-theory (enable lhprobe/4vec-p))))
  (mbe :logic (if (eq (lhprobe/4vec-kind x) :4vec)
                  (4vec-fix x)
                (lhprobe-fix x))
       :exec x)
  ///

  (defthm lhprobe/4vec-fix-when-lhprobe/4vec-p
    (implies (lhprobe/4vec-p x)
             (equal (lhprobe/4vec-fix x) x)))

  (fty::deffixtype lhprobe/4vec :pred lhprobe/4vec-p :fix lhprobe/4vec-fix :equiv lhprobe/4vec-equiv :define t)

  (defthm lhprobe/4vec-fix-when-kind-is-4vec
    (implies (equal (lhprobe/4vec-kind x) :4vec)
             (equal (lhprobe/4vec-fix x) (4vec-fix x))))
  
  (defthm lhprobe/4vec-fix-when-kind-is-lhprobe
    (implies (equal (lhprobe/4vec-kind x) :lhprobe)
             (equal (lhprobe/4vec-fix x) (lhprobe-fix x))))

  (fty::deffixequiv lhprobe/4vec-kind))

(define lhprobe/4vec-eval ((x lhprobe/4vec-p)
                           (envs svex-envlist-p))
  :short "Evaluator for @(see lhprobe/4vec-p) objects"
  :parents (lhprobe/4vec-p)
  :returns (val 4vec-p)
  (lhprobe/4vec-case x
    :lhprobe (lhprobe-eval x envs)
    :4vec (4vec-fix x)))


(define lhprobe/4vec-vars ((x lhprobe/4vec-p))
  :parents (lhprobe)
  :short "Collect variables present in an lhprobe/4vec"
  :returns (vars svarlist-p)
  (lhprobe/4vec-case x
    :4vec nil
    :lhprobe (lhprobe-vars x))
  ///


  
  (defthm lhprobe/4vec-eval-of-svex-envlist-extract-vars
    (implies (subsetp-equal (lhprobe/4vec-vars x) (Svarlist-fix vars))
             (equal (lhprobe/4vec-eval x (svex-envlist-extract-keys vars envs))
                    (lhprobe/4vec-eval x envs)))
    :hints(("Goal" :in-theory (enable lhprobe/4vec-eval)))))

(define lhprobe/4vec-change-override ((x lhprobe/4vec-p)
                                      (type svar-overridetype-p))
  :returns (new-x lhprobe/4vec-p)
  (lhprobe/4vec-case x
    :4vec (4vec-fix x)
    :lhprobe (lhprobe-change-override x type)))





(defprod lhprobe-constraint
  :short "Constraint equating an @(see lhprobe) (that is, a concatenation of signals at some time) equals either a @(see 4vec) constant or the value of another lhprobe."
  ((lhprobe lhprobe-p)
   (val lhprobe/4vec-p))
  :layout :fulltree)

(fty::deflist lhprobe-constraintlist :elt-type lhprobe-constraint-p :true-listp t)


(define lhprobe-constraint-eval ((x lhprobe-constraint-p)
                                 (envs svex-envlist-p))
  (b* (((lhprobe-constraint x)))
    (equal (lhprobe-eval x.lhprobe envs)
           (lhprobe/4vec-eval x.val envs))))

(define lhprobe-constraintlist-eval ((x lhprobe-constraintlist-p)
                                     (envs svex-envlist-p))
  (if (atom x)
      t
    (and (lhprobe-constraint-eval (car x) envs)
         (lhprobe-constraintlist-eval (cdr x) envs)))
  ///
  (defthm lhprobe-constraintlist-eval-of-append
    (equal (lhprobe-constraintlist-eval (append x y) envs)
           (and (lhprobe-constraintlist-eval x envs)
                (lhprobe-constraintlist-eval y envs)))))

(define lhatom-overridemux-eval ((x lhatom-p)
                                 (env svex-env-p)
                                 (out svex-env-p))
  :returns (val 4vec-p)
  (lhatom-case x
    :z 0
    :var (4vec-rsh (2vec x.rsh)
                   (if (svar-override-p x.name :val)
                       (4vec-bit?! (svex-env-fastlookup (svar-change-override x.name :test) env)
                                   (svex-env-fastlookup x.name env)
                                   (svex-env-fastlookup (svar-change-override x.name nil) out))
                     (svex-env-fastlookup x.name env)))))



(define lhs-overridemux-eval-ext ((x lhs-p)
                              (env svex-env-p)
                              (out svex-env-p))
  :returns (val 4vec-p)
  (if (atom x)
      0
    (if (atom (cdr x))
        (4vec-sign-ext (2vec (lhrange->w (car x)))
                       (lhatom-overridemux-eval (lhrange->atom (car x)) env out))
      (4vec-concat (2vec (lhrange->w (car x)))
                   (lhatom-overridemux-eval (lhrange->atom (car x)) env out)
                   (lhs-overridemux-eval-ext (cdr x) env out))))
  ///



  (defthm lhs-vars-of-lhs-change-override
    (equal (lhs-vars (lhs-change-override x type))
           (svarlist-change-override (lhs-vars x) type))
    :hints(("Goal" :in-theory (enable svarlist-change-override lhs-change-override lhatom-change-override lhs-vars lhatom-vars))))

  (defthm lhs-change-override-of-lhs-change-override
    (equal (lhs-change-override (lhs-change-override x type1) type2)
           (lhs-change-override x type2))
    :hints(("Goal" :in-theory (enable lhs-change-override lhatom-change-override)))))

(define lhs-overridemux-eval-zero ((x lhs-p)
                              (env svex-env-p)
                              (out svex-env-p))
  :returns (val 4vec-p)
  (if (atom x)
      0
    (4vec-concat (2vec (lhrange->w (car x)))
                 (lhatom-overridemux-eval (lhrange->atom (car x)) env out)
                 (lhs-overridemux-eval-zero (cdr x) env out)))
  ///


  (defthm lhs-vars-of-lhs-change-override
    (equal (lhs-vars (lhs-change-override x type))
           (svarlist-change-override (lhs-vars x) type))
    :hints(("Goal" :in-theory (enable svarlist-change-override lhs-change-override lhatom-change-override lhs-vars lhatom-vars))))

  (defthm lhs-change-override-of-lhs-change-override
    (equal (lhs-change-override (lhs-change-override x type1) type2)
           (lhs-change-override x type2))
    :hints(("Goal" :in-theory (enable lhs-change-override lhatom-change-override)))))


(define lhprobe-overridemux-eval ((x lhprobe-p)
                                  (envs svex-envlist-p)
                                  (outs svex-envlist-p))
  :returns (val 4vec-p)
  (b* (((lhprobe x))
       (env (nth x.stage envs))
       (out (nth x.stage outs)))
    (if x.signedp
        (lhs-overridemux-eval-ext x.lhs env out)
      (lhs-overridemux-eval-zero x.lhs env out)))
  ///
  (local (include-book "std/lists/nth" :dir :System)))


(define lhprobe/4vec-overridemux-eval ((x lhprobe/4vec-p)
                                       (envs svex-envlist-p)
                                       (outs svex-envlist-p))
  :returns (val 4vec-p)
  (lhprobe/4vec-case x
    :lhprobe (lhprobe-overridemux-eval x envs outs)
    :4vec (4vec-fix x)))

(define lhprobe-constraint-overridemux-eval ((x lhprobe-constraint-p)
                                             (envs svex-envlist-p)
                                             (outs svex-envlist-p))
  (b* (((lhprobe-constraint x)))
    (equal (lhprobe-overridemux-eval x.lhprobe envs outs)
           (lhprobe/4vec-overridemux-eval x.val envs outs))))

(define lhprobe-constraintlist-overridemux-eval ((x lhprobe-constraintlist-p)
                                                 (envs svex-envlist-p)
                                                 (outs svex-envlist-p))
  (if (atom x)
      t
    (and (lhprobe-constraint-overridemux-eval (car x) envs outs)
         (lhprobe-constraintlist-overridemux-eval (cdr x) envs outs)))
  ///
  (defthm lhprobe-constraintlist-overridemux-eval-of-append
    (equal (lhprobe-constraintlist-overridemux-eval (append x y) envs outs)
           (and (lhprobe-constraintlist-overridemux-eval x envs outs)
                (lhprobe-constraintlist-overridemux-eval y envs outs)))))


(define lhprobe-map-overridemux-eval ((x lhprobe-map-p)
                                      (envs svex-envlist-p)
                                      (outs svex-envlist-p))
  :returns (eval svex-env-p)
  (b* (((when (atom x))
        nil)
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (lhprobe-map-overridemux-eval (cdr x) envs outs)))
    (cons (cons (caar x) (lhprobe-overridemux-eval (cdar x) envs outs))
          (lhprobe-map-overridemux-eval (cdr x) envs outs)))
  ///
  (defret lookup-of-<fn>
    (equal (svex-env-lookup v eval)
           (let ((look (hons-assoc-equal (svar-fix v) (lhprobe-map-fix x))))
             (if look
                 (lhprobe-overridemux-eval (cdr look) envs outs)
               (4vec-x))))
    :hints(("Goal" :in-theory (enable svex-env-lookup-of-cons))))

  (defret boundp-of-<fn>
    (iff (svex-env-boundp v eval)
         (hons-assoc-equal (svar-fix v) (lhprobe-map-fix x)))
    :hints(("Goal" :in-theory (enable svex-env-boundp-of-cons-split))))
  
  (local (in-theory (enable lhprobe-map-fix))))



(define lhprobe-map-max-stage ((x lhprobe-map-p))
  :returns (stage integerp :rule-classes :type-prescription)
  (if (atom x)
      -1
    (if (mbt (and (consp (car x)) (svar-p (caar x))))
        (max (lhprobe->stage (cdar x))
             (lhprobe-map-max-stage (cdr x)))
      (lhprobe-map-max-stage (cdr x))))
  ///
  (local (in-theory (disable nth take ;; acl2::take-of-len-free acl2::take-when-atom acl2::take-of-too-many
                             )))
  (local (include-book "std/lists/nth" :dir :System))
  (defthm lhprobe-map-overridemux-eval-of-take-envs
    (implies (< (lhprobe-map-max-stage x) (nfix n))
             (equal (lhprobe-map-overridemux-eval x (take n envs) outs)
                    (lhprobe-map-overridemux-eval x envs outs)))
    :hints(("Goal" :in-theory (enable lhprobe-map-overridemux-eval
                                      lhprobe-overridemux-eval
                                      lhprobe/4vec-overridemux-eval))))
  (defthm lhprobe-map-overridemux-eval-of-take-outs
    (implies (< (lhprobe-map-max-stage x) (nfix n))
             (equal (lhprobe-map-overridemux-eval x envs (take n outs))
                    (lhprobe-map-overridemux-eval x envs outs)))
    :hints(("Goal" :in-theory (enable lhprobe-map-overridemux-eval
                                      lhprobe-overridemux-eval
                                      lhprobe/4vec-overridemux-eval))))

  (defthm lhprobe-map-eval-of-take-outs
    (implies (< (lhprobe-map-max-stage x) (nfix n))
             (equal (lhprobe-map-eval x (take n envs))
                    (lhprobe-map-eval x envs)))
    :hints(("Goal" :in-theory (enable lhprobe-map-eval
                                      lhprobe-eval
                                      lhprobe/4vec-eval))))

  (defthm lhprobe->stage-of-lookup-bound
    (implies (hons-assoc-equal v (lhprobe-map-fix x))
             (<= (lhprobe->stage (cdr (hons-assoc-equal v x)))
                 (lhprobe-map-max-stage x)))
    :rule-classes :linear)

  (defthm lhprobe-map-max-stage-lower-bound
    (<= -1 (lhprobe-map-max-stage x))
    :rule-classes :linear)
  
  (local (in-theory (enable lhprobe-map-fix))))

(define lhprobe-constraint-max-stage ((x lhprobe-constraint-p))
  :returns (stage natp :rule-classes :type-prescription)
  (b* (((lhprobe-constraint x)))
    (if (lhprobe/4vec-case x.val :lhprobe)
        (max (lhprobe->stage (lhprobe/4vec-fix x.val)) (lhprobe->stage x.lhprobe))
      (lhprobe->stage x.lhprobe)))
  ///
  (local (in-theory (disable nth take ;; acl2::take-of-len-free acl2::take-when-atom acl2::take-of-too-many
                             )))
  (local (include-book "std/lists/nth" :dir :system))

  (defthm lhprobe-constraint-overridemux-eval-of-take-envs
    (implies (< (lhprobe-constraint-max-stage x) (nfix n))
             (equal (lhprobe-constraint-overridemux-eval x (take n envs) outs)
                    (lhprobe-constraint-overridemux-eval x envs outs)))
    :hints(("Goal" :in-theory (enable lhprobe-constraint-overridemux-eval
                                      lhprobe-overridemux-eval
                                      lhprobe/4vec-overridemux-eval))))
  (defthm lhprobe-constraint-overridemux-eval-of-take-outs
    (implies (< (lhprobe-constraint-max-stage x) (nfix n))
             (equal (lhprobe-constraint-overridemux-eval x envs (take n outs))
                    (lhprobe-constraint-overridemux-eval x envs outs)))
    :hints(("Goal" :in-theory (enable lhprobe-constraint-overridemux-eval
                                      lhprobe-overridemux-eval
                                      lhprobe/4vec-overridemux-eval))))

  (defthm lhprobe-constraint-eval-of-take-outs
    (implies (< (lhprobe-constraint-max-stage x) (nfix n))
             (equal (lhprobe-constraint-eval x (take n envs))
                    (lhprobe-constraint-eval x envs)))
    :hints(("Goal" :in-theory (enable lhprobe-constraint-eval
                                      lhprobe-eval
                                      lhprobe/4vec-eval)))))


(define lhprobe-constraintlist-max-stage ((x lhprobe-constraintlist-p))
  :returns (stage integerp :rule-classes :type-prescription)
  (if (atom x)
      -1
    (max (lhprobe-constraint-max-stage (car x))
         (lhprobe-constraintlist-max-stage (cdr x))))
  ///
  (local (in-theory (disable nth take ;; acl2::take-of-len-free acl2::take-when-atom acl2::take-of-too-many
                             )))
  
  (defthm lhprobe-constraintlist-overridemux-eval-of-take-envs
    (implies (< (lhprobe-constraintlist-max-stage x) (nfix n))
             (equal (lhprobe-constraintlist-overridemux-eval x (take n envs) outs)
                    (lhprobe-constraintlist-overridemux-eval x envs outs)))
    :hints(("Goal" :in-theory (enable lhprobe-constraintlist-overridemux-eval))))
  
  (defthm lhprobe-constraintlist-overridemux-eval-of-take-outs
    (implies (< (lhprobe-constraintlist-max-stage x) (nfix n))
             (equal (lhprobe-constraintlist-overridemux-eval x envs (take n outs))
                    (lhprobe-constraintlist-overridemux-eval x envs outs)))
    :hints(("Goal" :in-theory (enable lhprobe-constraintlist-overridemux-eval))))

  (defthm lhprobe-constraintlist-eval-of-take-outs
    (implies (< (lhprobe-constraintlist-max-stage x) (nfix n))
             (equal (lhprobe-constraintlist-eval x (take n envs))
                    (lhprobe-constraintlist-eval x envs)))
    :hints(("Goal" :in-theory (enable lhprobe-constraintlist-eval))))

  (defthm lhprobe-constraintlist-max-stage-lower-bound
    (<= -1 (lhprobe-constraintlist-max-stage x))
    :rule-classes :linear)
  
  (defthm lhprobe-constraintlist-max-stage-of-append
    (Equal (lhprobe-constraintlist-max-stage (append x y))
           (max (lhprobe-constraintlist-max-stage x)
                (lhprobe-constraintlist-max-stage y)))))





(define svtv-fsm-namemap-envlist ((envs svex-envlist-p)
                                  (map svtv-name-lhs-map-p)
                                  (overridetype svar-overridetype-p))
  :returns (stage-envs svex-envlist-p)
  (if (atom envs)
      nil
    (cons (svtv-fsm-namemap-env (car envs) map overridetype)
          (svtv-fsm-namemap-envlist (cdr envs) map overridetype))))

(define svtv-fsm-namemap-alistlist ((alists svex-alistlist-p)
                                    (map svtv-name-lhs-map-p)
                                    (overridetype svar-overridetype-p))
  :returns (stage-alists svex-alistlist-p)
  (if (atom alists)
      nil
    (cons (svtv-fsm-namemap-alist-subst (car alists) map overridetype)
          (svtv-fsm-namemap-alistlist (cdr alists) map overridetype))))

(define svex-envlist-keys-list ((x svex-envlist-p))
  :returns (vars svarlist-list-p)
  (if (atom x)
      nil
    (cons  (alist-keys (svex-env-fix (car x)))
           (svex-envlist-keys-list (cdr x))))
  ///
  (defthm svex-envlist-keys-list-of-svex-alistlist-eval
    (equal (svex-envlist-keys-list (svex-alistlist-eval x env))
           (svex-alist-keys-list x))
    :hints(("Goal" :in-theory (enable svex-alist-keys-list
                                      svex-alistlist-eval)))))


(define svtv-spec-fsm-bindings-for-lhprobe ((lhprobe lhprobe-p)
                                            (binding svar/4vec-p)
                                            (bindings-acc lhprobe-map-p))
  :returns (bindings lhprobe-map-p)
  (svar/4vec-case binding
    :4vec (lhprobe-map-fix bindings-acc)
    :svar
    ;; svtv variable, add a binding unless there is one already
    (b* ((binding-look (hons-get (svar-fix binding) (lhprobe-map-fix bindings-acc)))
         ((unless binding-look)
          (hons-acons (svar-fix binding) (lhprobe-fix lhprobe)
                      (lhprobe-map-fix bindings-acc))))
      (lhprobe-map-fix bindings-acc)))
  ///
  (defret lhprobe-map-max-stage-of-<fn>
    (implies (and (<= (lhprobe->stage lhprobe) bound)
                  (<= (lhprobe-map-max-stage bindings-acc) bound))
             (<= (lhprobe-map-max-stage bindings) bound))
    :hints(("Goal" :in-theory (enable lhprobe-map-max-stage)))))


(define lhprobe-signedness-for-alist ((overridetype svar-overridetype-p)
                                      (val svar/4vec-p)
                                      ;; add config object?
                                      )
  ;; FIXME -- By default, it seems like it should mostly work to consider
  ;; override-test variables signed and input/override-val variables unsigned.
  ;; By convention, SVTV theorems usually set tests to -1 or 0 and assume other
  ;; variables unsigned-byte-p of their widths.  Here we also detect whether an
  ;; SVTV sets a signal to a non-zero-extended constant.  However, there's
  ;; nothing forbidding an SVTV theorem from assuming some variables to be
  ;; signed values.  In this case we might need to tweak the formula for
  ;; determining signedness, and possibly add a configuration option for it.
  (or (eq (svar-overridetype-fix overridetype) :test)
      (and (svar/4vec-case val :4vec)
           (or (< (4vec->upper val) 0)
               (< (4vec->lower val) 0)))))

(define svtv-spec-fsm-bindings-for-alist ((x svar/4vec-alist-p)
                                             (stage natp)
                                             (namemap svtv-name-lhs-map-p)
                                             (overridetype svar-overridetype-p)
                                             (bindings-acc lhprobe-map-p))
  :returns (bindings lhprobe-map-p)
  (b* (((when (atom x)) (lhprobe-map-fix bindings-acc))
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (svtv-spec-fsm-bindings-for-alist (cdr x) stage namemap overridetype bindings-acc))
       ((cons var val) (car x))
       (look (hons-get var (svtv-name-lhs-map-fix namemap)))
       ((unless look)
        (svtv-spec-fsm-bindings-for-alist (cdr x) stage namemap overridetype bindings-acc))
       (lhs (cdr look))
       (lhprobe (make-lhprobe :lhs (lhs-change-override lhs overridetype) :stage stage
                              :signedp (lhprobe-signedness-for-alist overridetype val)))
       (bindings-acc (svtv-spec-fsm-bindings-for-lhprobe lhprobe val bindings-acc)))
    (svtv-spec-fsm-bindings-for-alist (cdr x) stage namemap overridetype bindings-acc))
  ///
  (local (in-theory (enable svar/4vec-alist-fix)))

  (defret lhprobe-map-max-stage-of-<fn>
    (implies (and (<= (nfix stage) bound)
                  (<= (lhprobe-map-max-stage bindings-acc) bound))
             (<= (lhprobe-map-max-stage bindings) bound))))

(define svtv-spec-fsm-bindings-for-alists ((x svar/4vec-alistlist-p)
                                           (stage natp)
                                           (namemap svtv-name-lhs-map-p)
                                           (overridetype svar-overridetype-p)
                                           (bindings-acc lhprobe-map-p))
  :returns (bindings lhprobe-map-p)
  (if (atom x)
      (lhprobe-map-fix bindings-acc)
    (svtv-spec-fsm-bindings-for-alists
     (cdr x) (1+ (lnfix stage)) namemap overridetype
     (svtv-spec-fsm-bindings-for-alist (car x) stage namemap overridetype bindings-acc)))
  ///
  ;; (defret lhprobe-map-max-stage-of-<fn>
  ;;   (<= (lhprobe-map-max-stage bindings) (max (+ (len x) (nfix stage))
  ;;                                             (lhprobe-map-max-stage bindings-acc)))
  ;;   :hints (("Goal" :induct t)
  ;;           (and stable-under-simplificationp
  ;;                '(:use ((:instance lhprobe-map-max-stage-of-svtv-spec-fsm-bindings-for-alist
  ;;                         (x (car x))))
  ;;                  :in-theory (disable lhprobe-map-max-stage-of-svtv-spec-fsm-bindings-for-alist))))
  ;;   :rule-classes :linear)

  (defret lhprobe-map-max-stage-of-<fn>
    (implies (and (<= (+ -1 (len x) (nfix stage)) bound)
                  (<= (lhprobe-map-max-stage bindings-acc) bound))
             (<= (lhprobe-map-max-stage bindings) bound))))






(define svtv-spec-fsm-bindings ((x svtv-spec-p))
  :returns (bindings lhprobe-map-p)
  :guard (svtv-spec-fsm-syntax-check x)
  :guard-hints (("goal" :in-theory (enable svtv-spec-fsm-syntax-check)))
  (b* (((svtv-spec x))
       (len (len (svtv-probealist-outvars (svtv-spec->probes x))))
       ((acl2::with-fast x.namemap))
       (bindings (svtv-spec-fsm-bindings-for-alists (take len x.in-alists) 0 x.namemap nil nil))
       (bindings (svtv-spec-fsm-bindings-for-alists (take len x.override-val-alists) 0 x.namemap :val bindings)))
    (svtv-spec-fsm-bindings-for-alists (take len x.override-test-alists) 0 x.namemap :test bindings))
  ///
  (local (defthm len-of-take
           (Equal (len (take n x)) (nfix n))))
  (defret lhprobe-map-max-stage-of-<fn>
    (<= (lhprobe-map-max-stage bindings) (1- (len (svtv-probealist-outvars (svtv-spec->probes x)))))
    :rule-classes ((:linear :trigger-terms ((lhprobe-map-max-stage (svtv-spec-fsm-bindings x)))))))





(local (include-book "std/osets/element-list" :dir :system))
(local (fty::deflist svarlist :elt-type svar :elementp-of-nil nil))

(define svtv-spec-non-test-vars ((x svtv-spec-p))
  :returns (vars svarlist-p)
  (b* (((svtv-spec x))
       (len (len (svtv-probealist-outvars x.probes)))
       (ins (take len x.in-alists))
       (vals (take len x.override-val-alists)))
    (union (svex-alistlist-vars ins)
           (svex-alistlist-vars vals))))


(define svtv-spec-fsm-constraints-for-lhprobe ((lhprobe lhprobe-p)
                                               (binding svar/4vec-p)
                                               (bindings lhprobe-map-p))
  ;; Lhprobe is the LHS corresponding to some namemap name, which is mapped to binding in one of the input alists of the SVTV.

  ;; Add constraints based on equating lhprobe and binding under the assumption
  ;; that svtv variables are mapped to lhprobes as in bindings.

  
  
  :returns (constraints lhprobe-constraintlist-p)
  (svar/4vec-case binding
    :4vec
    ;; constant binding, add constraint
    (list (make-lhprobe-constraint
               :lhprobe lhprobe
               :val (4vec-fix binding)))
    :svar
    ;; svtv variable, must have a binding
    (b* ((binding-look (hons-get (svar-fix binding) (lhprobe-map-fix bindings)))
         ((unless binding-look)
          ;; add a constraint equating this hlprobe to x, I guess
          (list (make-lhprobe-constraint
                 :lhprobe lhprobe :val (4vec-x))))
         (binding-lhprobe (cdr binding-look))
         ((when (equal binding-lhprobe (lhprobe-fix lhprobe)))
          ;; same, no constraint necessary
          nil))
      (list (make-lhprobe-constraint
             :lhprobe lhprobe
             :val binding-lhprobe)))))



(define svtv-spec-fsm-constraints-for-alist ((x svar/4vec-alist-p)
                                             (stage natp)
                                             (namemap svtv-name-lhs-map-p)
                                             (overridetype svar-overridetype-p)
                                             (bindings lhprobe-map-p))
  :returns (constraints lhprobe-constraintlist-p)

  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (svtv-spec-fsm-constraints-for-alist (cdr x) stage namemap overridetype bindings))
       ((cons var val) (car x))
       (look (hons-get var (svtv-name-lhs-map-fix namemap)))
       ((unless look)
        (svtv-spec-fsm-constraints-for-alist (cdr x) stage namemap overridetype bindings))
       (lhs (cdr look))
       ;; FIXME -- See the comment about signedness in svtv-spec-fsm-bindings-for-alist.
       ;; 
       (lhprobe (make-lhprobe :lhs (lhs-change-override lhs overridetype) :stage stage
                              :signedp (lhprobe-signedness-for-alist overridetype val))))
    (append       
     (svtv-spec-fsm-constraints-for-lhprobe lhprobe val bindings)
     (svtv-spec-fsm-constraints-for-alist (cdr x) stage namemap overridetype bindings)))
  ///
  (local (in-theory (enable svar/4vec-alist-fix))))
       
(define svtv-spec-fsm-constraints-for-alists ((x svar/4vec-alistlist-p)
                                              (stage natp)
                                              (namemap svtv-name-lhs-map-p)
                                              (overridetype svar-overridetype-p)
                                              (bindings lhprobe-map-p))
  :returns (constraints lhprobe-constraintlist-p)
  (if (atom x)
      nil
    (append (svtv-spec-fsm-constraints-for-alist (car x) stage namemap overridetype bindings)
            (svtv-spec-fsm-constraints-for-alists (cdr x) (1+ (lnfix stage)) namemap overridetype bindings))))



(define svtv-spec-fsm-constraints ((x svtv-spec-p))
  :returns (constraints lhprobe-constraintlist-p)
  :guard (svtv-spec-fsm-syntax-check x)
  :guard-hints (("goal" :in-theory (enable svtv-spec-fsm-syntax-check)))
  (b* (((svtv-spec x))
       (bindings (svtv-spec-fsm-bindings x))
       (len (len (svtv-probealist-outvars (svtv-spec->probes x))))
       ((acl2::with-fast x.namemap bindings)))
    (append (svtv-spec-fsm-constraints-for-alists (take len x.in-alists) 0 x.namemap nil bindings)
            (svtv-spec-fsm-constraints-for-alists (take len x.override-val-alists) 0 x.namemap :val bindings))))


(define svtv-spec->override-test-alists* ((x svtv-spec-p))
  (b* (((svtv-spec x)))
    (take (len (svtv-probealist-outvars x.probes)) x.override-test-alists)))

(define svtv-spec->override-val-alists* ((x svtv-spec-p))
  (b* (((svtv-spec x)))
    (take (len (svtv-probealist-outvars x.probes)) x.override-val-alists)))

(define svtv-spec->in-alists* ((x svtv-spec-p))
  (b* (((svtv-spec x)))
    (take (len (svtv-probealist-outvars x.probes)) x.in-alists)))

(define force-execute (x) x)


(define svtv-probe-to-lhprobe ((x svtv-probe-p)
                               (namemap svtv-name-lhs-map-p))
  :returns (lhprobe lhprobe-p)
  (b* (((svtv-probe x)))
    ;; This is used on the output side, and SVTV outputs are always unsigned (the LHSes are evaluated with lhs-eval-zero).
    (make-lhprobe :stage x.time :lhs (cdr (hons-get x.signal (svtv-name-lhs-map-fix namemap))))))


(define svtv-probealist-to-lhprobe-map ((x svtv-probealist-p)
                                        (namemap svtv-name-lhs-map-p))
  :returns (map lhprobe-map-p)
  (if (atom x)
      nil
    (if (mbt (consp (car x)))
        (cons (cons (svar-fix (caar x)) (svtv-probe-to-lhprobe (cdar x) namemap))
              (svtv-probealist-to-lhprobe-map (cdr x) namemap))
      (svtv-probealist-to-lhprobe-map (cdr x) namemap)))
  ///
  (local (in-theory (enable svtv-probealist-fix))))



(defsection svex-envs-ovtestsimilar
  ;; (def-universal-equiv svex-envs-ovtestsimilar
  ;;   :qvars (k)
  ;;   :equiv-terms ((4vec-1mask-equiv (svex-env-lookup k x))))

  (defun-sk svex-envs-ovtestsimilar (x y)
    (forall k
            (implies (svar-override-p k :test)
                     (4vec-1mask-equiv (svex-env-lookup k x)
                                       (svex-env-lookup k y))))
    :rewrite :direct)

  (in-theory (disable svex-envs-ovtestsimilar
                      svex-envs-ovtestsimilar-necc))

  (defequiv svex-envs-ovtestsimilar
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (enable svex-envs-ovtestsimilar-necc)))))

  (defrefinement  svex-envs-similar svex-envs-ovtestsimilar
    :hints(("Goal" :in-theory (enable svex-envs-ovtestsimilar)))))


(define svex-envlists-ovtestsimilar ((x svex-envlist-p) (y svex-envlist-p))
  (if (Atom x)
      (atom y)
    (and (consp y)
         (ec-call (svex-envs-ovtestsimilar (car x) (car y)))
         (svex-envlists-ovtestsimilar (cdr x) (cdr y))))
  ///
  (defequiv svex-envlists-ovtestsimilar)

  (defrefinement svex-envlists-similar svex-envlists-ovtestsimilar
    :hints(("Goal" :in-theory (enable svex-envlists-similar-rec)))))
