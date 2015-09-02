; S-Expressions for 4-Valued Logic
; Copyright (C) 2010-2012 Centaur Technology
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

; sexpr-booleval.lisp
;  - Less-conservative evaluator for use with don't-care inputs.


(in-package "ACL2")
(include-book "sexpr-advanced")
(include-book "sexpr-rewrites")
(include-book "centaur/gl/gl-util" :dir :system)
(include-book "centaur/gl/def-gl-rewrite" :dir :system)
(include-book "centaur/vl/util/cwtime" :dir :system)

;; BOZO convert these comments into xdoc, some day

; Suppose you have a hardware module represented as a 4v-sexpr and you want to
; prove that it implements a certain function.
;
; Often, the module has inputs/initial states that you don't care about.  If
; you're lucky, these go away when you compose in the signals you do care about
; (using, say, 4v-sexpr-restrict-with-rw).  However, sometimes you're left with
; some function of don't-care variables.  This could be evidence of a
; counterexample: perhaps your answer truly depends on some input or initial
; state setting that you weren't expecting it to.  But another possibility is
; that the result is actually constant over all Boolean settings of those
; inputs/initial states.

; This book defines a function, 4v-sexpr-boolconst-val, that (logically)
; returns the constant value of such an expression if it is constant, and X if
; not.  It will only actually execute if the sexpr is syntactically constant.
; However, we define a GL symbolic counterpart for it (in g-sexpr-eval) that
; can use SAT/BDDs to find out if the sexpr is truly constant or not.


; The first two pieces to the puzzle are 4v-sexpr-eval-default and
; 4v-bool-alist-fix.  The theorem we will try to prove about (output sexprs
; from) modules with don't-care variables is something like:
;   (equal (4v-sexpr-eval-default (output-sexpr)
;                                 (append important-env
;                                         (4v-bool-alist-fix dontcare-env))
;                                 'f)
;          (spec ...))
; That is,
;    - for any setting of the "important" (non don't-care) inputs, and
;    - for any Boolean setting of the don't-care inputs,
; the implementation equals the spec.

; In order to prove this, we may want to do two separate proofs:
;  - if the don't-care variables are fixed (say, to false),
;     the implementation equals the spec:
;   (equal (4v-sexpr-eval-default (output-sexpr)
;                                 important-env
;                                 'f)
;          (spec ...))
;  - the result is independent of the don't-care variables:
;   (equal (4v-sexpr-eval-default (output-sexpr)
;                                 (append important-env
;                                         (4v-bool-alist-fix dontcare-env))
;                                 'f)
;          (4v-sexpr-eval-default (output-sexpr)
;                                 important-env
;                                 'f).
; It seems desirable to separate these because we might want to use different
; strategies for each: say, BDDs for the first, SAT for the second.

; For GL proofs, the strategy for the first is straightforward.  We prove that
; a call of 4v-sexpr-eval-default is equivalent to a call of 4v-sexpr-eval,
; with environment constructed by appending the given environment to a pairing
; of the variables of the AIG to the default value (f, above).  We have a
; reduction of 4v-sexpr-eval to AIG operations for GL proofs, so that should be
; sufficient once we add a GL alternate definition for 4v-sexpr-eval-default in
; terms of 4v-sexpr-eval.

; The strategy for the second kind of proof is slightly less straightforward,
; because we want to be very general about what the dontcare-env could be.
; Fortunately, we can prove that 4v-sexpr-eval-default only cares whether the
; sexpr variables of the term are bound to t or not, so we can effectively
; normalize the form of the dontcare-env to an alist that binds every sexpr
; variable to (if (lookup-var v dontcare-env) 't 'f).  Supposing that the
; dontcare-env is represented by a g-var in the symbolic execution, this will
; have the effect of generating a Boolean variable for the binding of each
; sexpr var in the dontcare-env, and allowing a counterexample to be
; constructed that binds these variables to the right things.


(defsection 4v-sexpr-eval-default
  (local (in-theory (enable 4v-sexpr-eval-default)))

  (defthm-4v-sexpr-flag
    (defthm 4v-sexpr-eval-default-in-terms-of-4v-sexpr-eval
      (implies (subsetp-equal (4v-sexpr-vars x) vars)
               (equal (4v-sexpr-eval-default x env default)
                      (4v-sexpr-eval x (append env (bind-to-each
                                                    (set-difference$ vars (alist-keys env))
                                                    default)))))
      :hints ('(:expand ((4v-sexpr-eval-default x env default)
                         (:free (env) (4v-sexpr-eval x env)))
                :in-theory (enable 4v-sexpr-apply)))
      :flag sexpr)
    (defthm 4v-sexpr-eval-default-list-in-terms-of-4v-sexpr-eval
      (implies (subsetp-equal (4v-sexpr-vars-list x) vars)
               (equal (4v-sexpr-eval-default-list x env default)
                      (4v-sexpr-eval-list x (append env (bind-to-each
                                                         (set-difference$ vars (alist-keys env))
                                                         default)))))
      :hints ('(:expand ((4v-sexpr-eval-default-list x env default)
                         (:free (env) (4v-sexpr-eval-list x env)))))
      :flag sexpr-list))

  (defthmd 4v-sexpr-eval-alist-default-in-terms-of-4v-sexpr-eval-alist
    (implies (subsetp-equal (4v-sexpr-vars-list (alist-vals x)) vars)
             (equal (4v-sexpr-eval-default-alist x env default)
                    (4v-sexpr-eval-alist x (append env (bind-to-each
                                                        (set-difference$ vars (alist-keys env))
                                                        default)))))
    :hints(("Goal" :in-theory (e/d (4v-sexpr-eval-default-alist)
                                   (4v-sexpr-eval-default
                                    4v-sexpr-eval)))))


  (local
   (defthm-4v-sexpr-flag
     (defthm 4v-sexpr-eval-default-append-envs-commute
       (equal (4v-sexpr-eval x (append (bind-to-each
                                        (set-difference$ vars (alist-keys env))
                                        default)
                                       env))
              (4v-sexpr-eval x (append env (bind-to-each
                                            (set-difference$ vars (alist-keys env))
                                            default))))
       :hints ('(:expand ((4v-sexpr-eval-default x env default)
                          (:free (env) (4v-sexpr-eval x env)))))
       :flag sexpr)
     (defthm 4v-sexpr-eval-default-list-append-envs-commute
       (equal (4v-sexpr-eval-list x (append (bind-to-each
                                             (set-difference$ vars (alist-keys env))
                                             default)
                                            env))
              (4v-sexpr-eval-list x (append env (bind-to-each
                                                 (set-difference$ vars (alist-keys env))
                                                 default))))
       :hints ('(:expand ((4v-sexpr-eval-default-list x env default)
                          (:free (env) (4v-sexpr-eval-list x env)))))
       :flag sexpr-list)))

  (local (defthm 4v-sexpr-eval-alist-append-envs-commute
           (equal (4v-sexpr-eval-alist x (append (bind-to-each
                                                  (set-difference$ vars (alist-keys env))
                                                  default)
                                                 env))
                  (4v-sexpr-eval-alist x (append env (bind-to-each
                                                      (set-difference$ vars (alist-keys env))
                                                      default))))
           :hints(("Goal" :in-theory (e/d (4v-sexpr-eval-default-alist)
                                          (4v-sexpr-eval-default
                                           4v-sexpr-eval))))))

  (local (in-theory (disable 4v-sexpr-eval-default-in-terms-of-4v-sexpr-eval
                             4v-sexpr-eval-default-list-in-terms-of-4v-sexpr-eval)))

  (defcong 4v-sexpr-equiv equal (4v-sexpr-eval-default x env default) 1
    :hints (("goal" :use ((:instance 4v-sexpr-eval-default-in-terms-of-4v-sexpr-eval
                           (vars (append (4v-sexpr-vars x)
                                         (4v-sexpr-vars x-equiv)))
                           (x x))
                          (:instance 4v-sexpr-eval-default-in-terms-of-4v-sexpr-eval
                           (vars (append (4v-sexpr-vars x)
                                         (4v-sexpr-vars x-equiv)))
                           (x x-equiv))))))

  (defun 4v-sexpr-eval-default-alist-gl (x env default)
    (b* ((vars (cwtime (4v-sexpr-vars-1pass-list (alist-vals x)) :mintime 1))
         (keys (alist-keys env))
         (vars (cwtime (hons-set-diff vars keys) :mintime 1))
         (defaults (cwtime (bind-to-each vars default) :mintime 1))
         (full-env (if (< (len keys) (len vars))
                       (cwtime (append env defaults) :mintime 1)
                     (cwtime (append defaults env) :mintime 1))))
      (cwtime (4v-sexpr-eval-alist
               x full-env))))

  (defthmd 4v-sexpr-eval-default-alist-gl-def
    (equal (4v-sexpr-eval-default-alist x env default)
           (4v-sexpr-eval-default-alist-gl x env default))
    :hints (("Goal" :use ((:instance 4v-sexpr-eval-alist-default-in-terms-of-4v-sexpr-eval-alist
                           (vars (4v-sexpr-vars-list (alist-vals x)))))))
    :rule-classes ((:definition :install-body nil)))

  (gl::set-preferred-def 4v-sexpr-eval-default-alist 4v-sexpr-eval-default-alist-gl-def)

  (defun 4v-sexpr-eval-default-list-gl (x env default)
    (b* ((vars (cwtime (4v-sexpr-vars-1pass-list x) :mintime 1))
         (keys (alist-keys env))
         (vars (cwtime (hons-set-diff vars keys) :mintime 1))
         (defaults (cwtime (bind-to-each vars default) :mintime 1))
         (full-env (if (< (len keys) (len vars))
                       (cwtime (append env defaults) :mintime 1)
                     (cwtime (append defaults env) :mintime 1))))
      (cwtime (4v-sexpr-eval-list x full-env) :mintime 1)))

  (defthmd 4v-sexpr-eval-default-list-gl-def
    (equal (4v-sexpr-eval-default-list x env default)
           (4v-sexpr-eval-default-list-gl x env default))
    :hints (("Goal" :use ((:instance 4v-sexpr-eval-default-list-in-terms-of-4v-sexpr-eval
                           (vars (4v-sexpr-vars-list x))))))
    :rule-classes ((:definition :install-body nil)))

  (gl::set-preferred-def 4v-sexpr-eval-default-list 4v-sexpr-eval-default-list-gl-def))


(defsection 4v-bool-alist-extract

  (defun 4v-bool-alist-lookup (var al)
    (declare (xargs :guard t))
    (cdr (hons-get var al)))

  (defund 4v-bool-alist-extract (vars al)
    (declare (xargs :Guard t))
    (if (atom vars)
        nil
      (cons (cons (car vars)
                  (if (eq (4v-bool-alist-lookup (car vars) al) t)
                      't 'f))
            (4v-bool-alist-extract (cdr vars) al))))

  (in-theory (enable 4v-bool-alist-extract))

  (defthm lookup-in-4v-bool-alist-extract
    (equal (hons-assoc-equal k (4v-bool-alist-extract vars al))
           (and (member k vars)
                (cons k (if (eq (4v-bool-alist-lookup k al) t) 't 'f))))))

(defsection 4v-sexpr-alist-check-independent
  (defthm alistp-of-4v-sexpr-eval-default-alist
    (alistp (4v-sexpr-eval-default-alist x al def))
    :hints(("Goal" :in-theory (enable 4v-sexpr-eval-default-alist))))

  (defthm len-of-4v-sexpr-eval-default-alist
    (equal (len (4v-sexpr-eval-default-alist x al def))
           (len (alist-keys x)))
    :hints(("Goal" :in-theory (enable 4v-sexpr-eval-default-alist alist-keys))))

  (defun 4v-sexpr-alist-check-ind-show-unequal-pairs (ev1 ev2)
    (declare (xargs :guard (and (alistp ev1) (alistp ev2)
                                (equal (len ev1) (len ev2)))))
    (if (atom ev1)
        nil
      (prog2$ (and (not (equal (cdar ev1) (cdar ev2)))
                   (cw "~x0:          ~x1          ~x2~%"
                       (caar ev1) (cdar ev1) (cdar ev2)))
              (4v-sexpr-alist-check-ind-show-unequal-pairs (cdr ev1) (cdr ev2)))))

  (defund 4v-sexpr-alist-check-independent (x cares dont-cares)
    (declare (xargs :guard t))
    (b* ((al1 (append-without-guard
               cares (4v-bool-alist-fix dont-cares)))
         ((with-fast cares al1))
         (ev1 (4v-sexpr-eval-default-alist x al1 'f))
         (ev2 (4v-sexpr-eval-default-alist x cares 'f))
         (equal (equal ev1 ev2)))
      (and (not equal)
           (prog2$ (cw "Key       Given env     All false~%")
                   (4v-sexpr-alist-check-ind-show-unequal-pairs ev1 ev2)))
      equal))

  (local (in-theory (enable 4v-sexpr-alist-check-independent)))

  (local (in-theory (disable 4v-sexpr-apply)))

  (defthm-4v-sexpr-flag
    (defthm 4v-sexpr-eval-default-of-4v-bool-alist-extract
      (implies (subsetp (4v-sexpr-vars x) vars)
               (equal (4v-sexpr-eval-default x (append env
                                                       (4v-bool-alist-extract
                                                        (set-difference$ vars (alist-keys env))
                                                        dc))
                                             'f)
                      (4v-sexpr-eval-default x (append env
                                                       (4v-bool-alist-fix dc))
                                             'f)))
      :hints ('(:expand ((:free (env) (4v-sexpr-eval-default x env 'f)))))
      :flag sexpr)
    (defthm 4v-sexpr-eval-default-list-of-4v-bool-alist-extract
      (implies (subsetp (4v-sexpr-vars-list x) vars)
               (equal (4v-sexpr-eval-default-list x (append env
                                                            (4v-bool-alist-extract
                                                             (set-difference$ vars (alist-keys env))
                                                             dc))
                                                  'f)
                      (4v-sexpr-eval-default-list x (append env
                                                            (4v-bool-alist-fix dc))
                                                  'f)))
      :hints ('(:expand ((:free (env) (4v-sexpr-eval-default-list x env 'f)))))
      :flag sexpr-list)
    :hints (("goal" :do-not-induct t)))

  (defthm 4v-sexpr-eval-default-alist-of-4v-bool-alist-extract
    (implies (subsetp (4v-sexpr-vars-list (alist-vals x)) vars)
             (equal (4v-sexpr-eval-default-alist x (append env
                                                          (4v-bool-alist-extract
                                                           (set-difference$ vars (alist-keys env))
                                                           dc))
                                                'f)
                    (4v-sexpr-eval-default-alist x (append env
                                                           (4v-bool-alist-fix dc))
                                                 'f)))
    :hints(("Goal" :in-theory (enable 4v-sexpr-eval-default-alist alist-vals))))

  (defun 4v-sexpr-alist-check-independent-gl (x cares dont-cares)
    (b* ((eval-squash
          (cwtime (4v-sexpr-eval-default-alist x cares 'f) :name eval-squash :mintime 1))
         (vars (cwtime (4v-sexpr-vars-1pass-list (alist-vals x)) :mintime 1))
         (vars (cwtime (hons-set-diff vars (alist-keys cares)) :mintime 1))
         (extract (cwtime (4v-bool-alist-extract
                           vars
                           (make-fast-alist dont-cares)) :mintime 1))
         (dce (cwtime (append cares extract) :name dce :mintime 1))
         (eval-dce (cwtime (4v-sexpr-eval-default-alist x dce 'f) :name eval-dce :mintime 1)))
      (equal eval-dce eval-squash)))

  (defthmd 4v-sexpr-alist-check-independent-fix-vars
    (equal (4v-sexpr-alist-check-independent x cares dont-cares)
           (4v-sexpr-alist-check-independent-gl x cares dont-cares))
    :rule-classes ((:definition :install-body nil)))

  (gl::set-preferred-def 4v-sexpr-alist-check-independent
                         4v-sexpr-alist-check-independent-fix-vars)

  (gl::gl-set-uninterpreted 4v-bool-alist-lookup)

  (gl::def-gl-rewrite 4v-bool-alist-lookup-of-cons
    (equal (4v-bool-alist-lookup k (cons a b))
           (cdr (hons-get k (cons a b)))))

  (gl::def-gl-rewrite 4v-bool-alist-lookup-of-nil
    (equal (4v-bool-alist-lookup k nil)
           nil))

  (gl::def-glcp-ctrex-rewrite
    ((equal (4v-bool-alist-lookup k al) t) nil)
    (al (if (eq 'f (cdr (hons-get k al)))
            al
          (hons-acons k 'f al)))
    :test (quotep k))

  (gl::def-glcp-ctrex-rewrite
    ((equal (4v-bool-alist-lookup k al) t) t)
    (al (if (eq t (cdr (hons-get k al)))
            al
          (hons-acons k t al)))
    :test (quotep k)))



;; (defsection 4v-sexpr-list-check-independent

;;   (local
;;    (defthm-4v-sexpr-flag
;;      (defthm 4v-sexpr-eval-of-append-4v-sexpr-eval-alist-of-4v-al-to-sexpr-al
;;        (equal (4v-sexpr-eval x (append (4v-sexpr-eval-alist (4v-al-to-sexpr-al al) env) rest))
;;               (4v-sexpr-eval x (append al rest)))
;;        :hints ('(:expand ((:free (env) (4v-sexpr-eval x env)))))
;;        :flag sexpr)
;;      (defthm 4v-sexpr-eval-list-of-append-4v-sexpr-eval-alist-of-4v-al-to-sexpr-al
;;        (equal (4v-sexpr-eval-list x (append (4v-sexpr-eval-alist (4v-al-to-sexpr-al al) env) rest))
;;               (4v-sexpr-eval-list x (append al rest)))
;;        :hints ('(:expand ((:free (env) (4v-sexpr-eval-list x env)))))
;;        :flag sexpr-list)))

;;   ;; (local (defthm 4v-sexpr-eval-alist-of-4v-al-to-sexpr-al-normalize
;;   ;;          (implies (syntaxp (not (equal env ''nil)))
;;   ;;                   (equal (4v-sexpr-eval-alist (4v-al-to-sexpr-al al) env)
;;   ;;                          (4v-sexpr-eval-alist (4v-al-to-sexpr-al al) nil)))))

;;   (local
;;    (defthm 4v-sexpr-eval-default-list-in-terms-of-4v-sexpr-eval-rw
;;      (implies (and (bind-free '((vars . (4v-sexpr-vars-list x))))
;;                    (subsetp-equal (4v-sexpr-vars-list x) vars))
;;               (equal (4v-sexpr-eval-default-list x env default)
;;                      (4v-sexpr-eval-list x (append env (bind-to-each
;;                                                         vars default)))))
;;      :hints (("goal" :use ((:instance 4v-sexpr-eval-default-list-in-terms-of-4v-sexpr-eval))))))

;;   (defthm 4v-sexpr-vars-list-of-4v-al-to-sexpr-al
;;     (equal (4v-sexpr-vars-list (alist-vals (4v-al-to-sexpr-al al)))
;;            nil))

;;   (defthm 4v-sexpr-vars-of-sexpr-restrict-with-rw-of-4v-al-to-sexpr-al
;;     (subsetp-equal (4v-sexpr-vars-list
;;                     (4v-sexpr-restrict-with-rw-list
;;                      x (4v-al-to-sexpr-al al)))
;;                    (4v-sexpr-vars-list x))
;;     :hints ((set-reasoning)))


;;   (defun 4v-sexpr-list-check-independent (x cares dont-cares)
;;     (declare (xargs :guard t))
;;     (mbe :logic (equal (4v-sexpr-eval-default-list
;;                         x (append cares (4v-bool-alist-fix dont-cares)) 'f)
;;                        (4v-sexpr-eval-default-list x cares 'f))
;;          :exec (b* ((cares-al (4v-al-to-sexpr-al cares))
;;                     (simp (with-fast-alist cares-al
;;                             (4v-sexpr-restrict-with-rw-list x cares-al)))
;;                     (dc (4v-bool-alist-fix dont-cares)))
;;                  (with-fast-alist dc
;;                    (equal (4v-sexpr-eval-default-list simp dc 'f)
;;                           (4v-sexpr-eval-default-list simp nil 'f)))))))




(defsection 4v-sexpr-bool-evals-constant


  (defun-sk 4v-sexpr-bool-evals-constant (x)
    (forall env
            (equal (4v-sexpr-eval-default x (4v-bool-alist-fix env) 'f)
                   (4v-sexpr-eval-default x nil 'f)))
    :rewrite :direct)

  (in-theory (disable 4v-sexpr-bool-evals-constant))

  (verify-guards 4v-sexpr-bool-evals-constant)

  (local (in-theory (disable 4v-sexpr-apply)))

  (local (defthmd 4v-sexpr-bool-evals-constant-when-4v-sexpr-equiv
           (implies (and (4v-sexpr-bool-evals-constant x)
                         (4v-sexpr-equiv x y))
                    (4v-sexpr-bool-evals-constant y))
           :hints (("goal" :expand ((4v-sexpr-bool-evals-constant y))
                    :use ((:instance 4v-sexpr-bool-evals-constant-necc
                           (env (4v-sexpr-bool-evals-constant-witness y))))))))

  (defcong 4v-sexpr-equiv equal (4v-sexpr-bool-evals-constant x) 1
    :hints (("goal" :cases ((4v-sexpr-bool-evals-constant x))
             :in-theory (enable 4v-sexpr-bool-evals-constant-when-4v-sexpr-equiv))))

  (defthm-4v-sexpr-flag
    (defthm 4v-sexpr-eval-default-constant-when-no-vars
      (implies (not (consp (4v-sexpr-vars x)))
               (equal (4v-sexpr-eval-default x env default)
                      (4v-sexpr-eval x nil)))
      :hints ('(:expand ((4v-sexpr-eval-default x env default)
                         (4v-sexpr-eval-default nil env default)
                         (:with 4v-sexpr-eval-redef (4v-sexpr-eval x nil)))))
      :flag sexpr)
    (defthm 4v-sexpr-eval-default-list-constant-when-no-vars
      (implies (not (consp (4v-sexpr-vars-list x)))
               (equal (4v-sexpr-eval-default-list x env default)
                      (4v-sexpr-eval-list x nil)))
      :flag sexpr-list))

  (defthm 4v-sexpr-bool-evals-constant-when-no-vars
    (implies (not (consp (4v-sexpr-vars x)))
             (4v-sexpr-bool-evals-constant x))
    :hints(("Goal" :in-theory (enable 4v-sexpr-bool-evals-constant))))

  (local (defthmd nth-const-open
           (implies (syntaxp (quotep n))
                    (equal (nth n x)
                           (if (zp n)
                               (car x)
                             (nth (1- n) (cdr x)))))))

  (defthm 4v-<=-nth-when-4v-list-<=
    (implies (4v-list-<= x y)
             (4v-<= (nth n x) (nth n y)))
    :hints(("Goal" :in-theory (enable nth))))

  (defthm 4v-sexpr-apply-monotonic
    (implies (4v-list-<= args1 args2)
             (4v-<= (4v-sexpr-apply f args1)
                    (4v-sexpr-apply f args2)))
    :hints(("Goal" :in-theory (e/d* (4v-sexpr-apply)
                                    (4v-<= 4v-op-defs
                                           nth
                                           ;nth-when-zp
                                           ))
            :do-not-induct t)))

  (defthm 4v-lookup-default-<=-4v-lookup
    (4v-<= (4v-lookup x env)
           (4v-lookup-default x env default)))

  (local (in-theory (disable 4v-lookup 4v-lookup-default
                             4v-sexpr-eval)))

  (defthm-4v-sexpr-flag
    (defthm 4v-sexpr-eval-default-<=-4v-sexpr-eval
      (4v-<= (4v-sexpr-eval x env)
             (4v-sexpr-eval-default x env default))
      :hints ('(:expand ((4v-sexpr-eval-default x env default)
                         (:with 4v-sexpr-eval-redef (4v-sexpr-eval x env)))
                :in-theory (disable 4v-<=)))
      :flag sexpr)
    (defthm 4v-sexpr-eval-default-list-<=-4v-sexpr-eval-list
      (4v-list-<= (4v-sexpr-eval-list x env)
                  (4v-sexpr-eval-default-list x env default))
      :flag sexpr-list))

  (defthm 4v-sexpr-eval-default-when-4v-sexpr-eval-non-x
    (implies (not (equal (4vx) (4v-sexpr-eval x env)))
             (equal (4v-sexpr-eval-default x env default)
                    (4v-sexpr-eval x env)))
    :hints (("goal" :use 4v-sexpr-eval-default-<=-4v-sexpr-eval
             :in-theory (disable 4v-sexpr-eval-default-<=-4v-sexpr-eval))))

  (defthm 4v-sexpr-bool-evals-constant-when-4v-sexpr-eval-non-x
    (implies (not (equal (4vx) (4v-sexpr-eval x nil)))
             (4v-sexpr-bool-evals-constant x))
    :hints (("goal" :in-theory (enable 4v-sexpr-bool-evals-constant)
             :use ((:instance 4v-sexpr-eval-monotonicp
                    (env nil)
                    (env1 (4v-bool-alist-fix (4v-sexpr-bool-evals-constant-witness x)))))))))




(defsection 4v-sexpr-boolconst-val

  (defund 4v-sexpr-boolconst-val (x)
    (declare (xargs :guard t))
    (mbe :logic (if (4v-sexpr-bool-evals-constant x)
                    (4v-sexpr-eval-default x nil 'f)
                  'x)
         :exec (let ((ev (4v-sexpr-eval x nil)))
                 (if (eq (4vx) ev)
                     ;; fails to execute
                     (if (4v-sexpr-bool-evals-constant x)
                         (4v-sexpr-eval-default x nil 'f)
                       'x)
                   ev))))

  (local (in-theory (enable 4v-sexpr-boolconst-val)))

  (defcong 4v-sexpr-equiv equal (4v-sexpr-boolconst-val x) 1)

  (defthm 4v-sexpr-boolconst-val-when-sexpr-eval
    (implies (not (equal (4vx) (4v-sexpr-eval x nil)))
             (equal (4v-sexpr-boolconst-val x)
                    (4v-sexpr-eval x nil))))

  (defun 4v-sexpr-boolconst-val-list (x)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (cons (4v-sexpr-boolconst-val (car x))
            (4v-sexpr-boolconst-val-list (cdr x)))))

  (defun 4v-sexpr-boolconst-val-alist (x)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (if (consp (car x))
          (cons (cons (caar x) (4v-sexpr-boolconst-val (cdar x)))
                (4v-sexpr-boolconst-val-alist (cdr x)))
        (4v-sexpr-boolconst-val-alist (cdr x))))))



(defsection 4v-sexpr-boolconst-eval

  (defun 4v-sexpr-boolconst-eval (x env)
    (declare (xargs :guard t))
    (mbe :logic (4v-sexpr-boolconst-val (4v-sexpr-restrict
                                         x (4v-al-to-sexpr-al env)))
         :exec (b* ((al (4v-al-to-sexpr-al env))
                    (sexpr (with-fast-alist al
                             (4v-sexpr-restrict-with-rw x al))))
                 (clear-memoize-table '4v-sexpr-restrict-with-rw)
                 (4v-sexpr-boolconst-val sexpr))))

  (local (in-theory (disable 4v-sexpr-eval
                             4v-key-bool-alistp
                             4v-sexpr-eval-default
                             4v-sexpr-boolconst-val)))

  (defcong 4v-sexpr-equiv equal (4v-sexpr-boolconst-eval x env) 1)

  (defun 4v-sexpr-boolconst-eval-list (x env)
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic (if (atom x)
                    nil
                  (cons (4v-sexpr-boolconst-eval (car x) env)
                        (4v-sexpr-boolconst-eval-list (cdr x) env)))
         :exec
         (b* ((al (4v-al-to-sexpr-al env))
              (sexprs (with-fast-alist al
                        (4v-sexpr-restrict-with-rw-list x al))))
           (clear-memoize-table '4v-sexpr-restrict-with-rw)
           (4v-sexpr-boolconst-val-list sexprs))))

  (local (defthm 4v-sexpr-boolconst-eval-list-exec
           (equal (b* ((al (4v-al-to-sexpr-al env))
                       (sexprs (with-fast-alist al
                                 (4v-sexpr-restrict-with-rw-list x al))))
                    (clear-memoize-table '4v-sexpr-restrict-with-rw)
                    (4v-sexpr-boolconst-val-list sexprs))
                  (4v-sexpr-boolconst-eval-list x env))))

  (verify-guards 4v-sexpr-boolconst-eval-list)

  (defun 4v-sexpr-boolconst-eval-alist (x env)
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic (if (atom x)
                    nil
                  (if (consp (car x))
                      (cons (cons (caar x) (4v-sexpr-boolconst-eval (cdar x) env))
                            (4v-sexpr-boolconst-eval-alist (cdr x) env))
                    (4v-sexpr-boolconst-eval-alist (cdr x) env)))
         :exec
         (b* ((al (4v-al-to-sexpr-al env))
              (sexpr-al (with-fast-alist al
                          (4v-sexpr-restrict-with-rw-alist x al))))
           (clear-memoize-table '4v-sexpr-restrict-with-rw)
           (4v-sexpr-boolconst-val-alist sexpr-al))))


  (local (defthm 4v-sexpr-boolconst-eval-alist-exec
           (equal (b* ((al (4v-al-to-sexpr-al env))
                       (sexprs (with-fast-alist al
                                 (4v-sexpr-restrict-with-rw-alist x al))))
                    (clear-memoize-table '4v-sexpr-restrict-with-rw)
                    (4v-sexpr-boolconst-val-alist sexprs))
                  (4v-sexpr-boolconst-eval-alist x env))))

  (verify-guards 4v-sexpr-boolconst-eval-alist)

  (defun 4v-sexpr-boolconst-eval-alist-find-env-for-diff (x env)
    (if (atom x)
        nil
      (if (and (consp (car x))
               (not (equal (4v-sexpr-boolconst-eval (cdar x) env)
                           (4v-sexpr-eval-default (cdar x) env 'f))))
          (4v-sexpr-bool-evals-constant-witness (4v-sexpr-restrict
                                                 (cdar x) (4v-al-to-sexpr-al env)))
        (4v-sexpr-boolconst-eval-alist-find-env-for-diff (cdr x) env))))

  ;; (defthm 4vp-of-4v-fix
  ;;   (4vp (4v-fix x)))

  (local (in-theory (disable 4v-fix)))

  (defthm 4vp-of-4v-sexpr-apply
    (4vp (4v-sexpr-apply fn args))
    :hints (("goal" :expand ((4v-sexpr-apply fn args))
             :in-theory (disable 4vp))))

  (defthm 4vp-of-4v-sexpr-eval-default
    (4vp (4v-sexpr-eval-default x env default))
    :hints (("goal" :expand ((4v-sexpr-eval-default x env default)))))

  (defthm-4v-sexpr-flag
    (defthm 4v-sexpr-eval-default-of-4v-sexpr-restrict
      (equal (4v-sexpr-eval-default
              (4v-sexpr-restrict x al) env default)
             (4v-sexpr-eval-default
              x (append (4v-sexpr-eval-default-alist al env default) env) default))
      :hints ('(:expand ((:free (env) (4v-sexpr-eval-default x env default))
                         (:free (env a b) (4v-sexpr-eval-default (cons a b) env default)))))
      :flag sexpr)
    (defthm 4v-sexpr-eval-default-list-of-4v-sexpr-restrict-list
      (equal (4v-sexpr-eval-default-list
              (4v-sexpr-restrict-list x al) env default)
             (4v-sexpr-eval-default-list
              x (append (4v-sexpr-eval-default-alist al env default) env) default))
      :hints ('(:expand ((:free (env) (4v-sexpr-eval-default-list x env default)))))
      :flag sexpr-list)
    :hints (("goal" :do-not-induct t)))

  (local
   (defthm-4v-sexpr-flag
     (defthm 4v-sexpr-eval-default-of-append-4v-sexpr-eval-alist-of-4v-al-to-sexpr-al
       (equal (4v-sexpr-eval-default x (append (4v-sexpr-eval-default-alist (4v-al-to-sexpr-al al) env def) rest) default)
              (4v-sexpr-eval-default x (append al rest) default))
       :hints ('(:expand ((:free (env) (4v-sexpr-eval-default x env default)))))
       :flag sexpr)
     (defthm 4v-sexpr-eval-default-list-of-append-4v-sexpr-eval-alist-of-4v-al-to-sexpr-al
       (equal (4v-sexpr-eval-default-list x (append (4v-sexpr-eval-default-alist (4v-al-to-sexpr-al al) env def) rest) default)
              (4v-sexpr-eval-default-list x (append al rest) default))
       :hints ('(:expand ((:free (env) (4v-sexpr-eval-default-list x env default)))))
       :flag sexpr-list)))

  (local
   (defthm-4v-sexpr-flag
     (defthm 4v-sexpr-eval-default-of-4v-sexpr-eval-alist-of-4v-al-to-sexpr-al
       (equal (4v-sexpr-eval-default x (4v-sexpr-eval-default-alist (4v-al-to-sexpr-al al) env def) default)
              (4v-sexpr-eval-default x al default))
       :hints ('(:expand ((:free (env) (4v-sexpr-eval-default x env default)))))
       :flag sexpr)
     (defthm 4v-sexpr-eval-default-list-of-4v-sexpr-eval-alist-of-4v-al-to-sexpr-al
       (equal (4v-sexpr-eval-default-list x (4v-sexpr-eval-default-alist (4v-al-to-sexpr-al al) env def) default)
              (4v-sexpr-eval-default-list x al default))
       :hints ('(:expand ((:free (env) (4v-sexpr-eval-default-list x env default)))))
       :flag sexpr-list)))


  (defthm 4v-sexpr-boolconst-eval-alist-when-independent
    (implies (not (equal (4v-sexpr-boolconst-eval-alist x env)
                         (4v-sexpr-eval-default-alist x env 'f)))
             (let ((witness (4v-sexpr-boolconst-eval-alist-find-env-for-diff x env)))
               (not (4v-sexpr-alist-check-independent x env witness))))
    :hints (("goal" :induct (len x)
             :in-theory (enable 4v-sexpr-eval-default-alist
                                4v-sexpr-boolconst-val
                                4v-sexpr-bool-evals-constant
                                4v-sexpr-alist-check-independent)))))
