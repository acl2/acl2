; S-Expressions for 4-Valued Logic
; Copyright (C) 2010-2012 Centaur Technology
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

(in-package "ACL2")
(include-book "sexpr-eval")
(include-book "sexpr-3v")
(include-book "centaur/aig/faig-base" :dir :system)
(include-book "centaur/aig/faig-constructors" :dir :system)
(include-book "centaur/aig/faig-equivs" :dir :system)
(include-book "centaur/aig/aig-equivs" :dir :system)
(include-book "centaur/misc/tuplep" :dir :system)
(local (include-book "centaur/aig/eval-restrict" :dir :system))

(local (in-theory (disable 4v-sexpr-eval)))

(local (in-theory (disable* (:ruleset t-aig-defs)
                            (:ruleset f-aig-defs)
                            (:ruleset 4v-op-defs))))



(defsection 4v-sexpr-to-faig
  :parents (4v-sexprs)
  :short "Translation from @(see 4v-sexprs) into a @(see faig)s."

  :long "<p>It is often useful to be able to convert a sexpr into a @(see
faig), since then you can apply AIG/FAIG based tools such as ABC, sat solvers,
the @(see bddify) algorithm, and so forth to sexpr-based models.  For instance,
we use this conversion to implement an efficient @(see gl) symbolic counterpart
for @(see 4v-sexpr-eval), which is used in practically all of our GL-based
hardware proofs.</p>

<p><b>Signature:</b> @(call 4v-sexpr-to-faig) builds an @(see faig).</p>

<p>@('x') is the sexpr you want to convert into an FAIG.</p>

<p>@('onoff') argument should be an alist that assigns an initial FAIG for
every variable of @('x').  Commonly the @('onoff') alist should bind each
variable @('v') to some pair of fresh variables like @('(v1 . v0)'), i.e.,
@('v1') is the onset variable and @('v0') is the offset variable for @('v'),
but other uses are also possible.  It is beneficial for @('onoff') to be a fast
alist, but it will be made fast if necessary.</p>

<p>@('optimize') is an optional flag that defaults to @('t').  When
optimization is allowed, we convert the sexpr in a smarter way that is
generally faster and produces smaller FAIGs which may be easier for other tools
to analyze.  You almost certainly want optimization <b>unless</b> you are doing
certain kinds of fragile AIG decomposition where you really want AIGs that are
exactly the same.  (If that sounds like nonsense, then you want
optimization.)</p>

<p>The basic idea of the optimization is to take advantage of the fact that
many sexpr operations are actually \"three-valued,\" i.e., they never produce
Z.  For instance, when we are converting a sexpr like @('(NOT (AND A B))') into
an @(see faig), since we know the result of an @('AND') gate is never Z, it
suffices to use @(see t-aig-not) instead of @(see f-aig-not).  There are
similar reductions for many gates; see @(see faig-constructors) for some
details.</p>

<p>You might regard @('4v-sexpr-to-faig') as a somewhat low-level function.
Its correctness theorem is rather elaborate and to make use of it you generally
need to construct an @('onoff') alist that sensibly accomplishes your goal.  A
good starting place and example might be @(see 4v-sexpr-eval-by-faig), which
generates an appropriate @('onoff') so that it can carry out a @(see
4v-sexpr-eval) computation using FAIG evaluation as the engine.</p>")


(local (defthm equal-len-0
         (equal (equal (len x) 0)
                (atom x))))

(local (defthmd nth-open-quotep
         (implies (syntaxp (quotep n))
                  (equal (nth n x)
                         (if (zp n)
                             (car x)
                           (nth (1- n) (cdr x)))))))


(defthm faig-eval-of-constants
  ;; BOZO find me a home
  (and (equal (faig-eval (faig-t) env) (faig-t))
       (equal (faig-eval (faig-f) env) (faig-f))
       (equal (faig-eval (faig-z) env) (faig-z))
       (equal (faig-eval (faig-x) env) (faig-x))
       (equal (faig-eval nil env)  (faig-x)))
  :hints(("Goal" :in-theory (enable faig-eval))))

(local (defthm faig-equiv-nil-x
         ;; BOZO find me a home?
         (equal (faig-equiv nil (faig-x)) t)
         :hints (("goal" :in-theory (enable faig-equiv)))))

(local (defthm faig-eval-when-atom
         (implies (atom x)
                  (equal (faig-eval x env)
                         (faig-x)))
         :hints(("Goal" :in-theory (enable faig-eval)))))


(defsection faig-const-p
  :parents (4v-sexpr-to-faig)
  :short "Recognizer for constant @(see faig)s."

  :long "<p>@(call faig-const-p) recognizes conses whose car/cdr are Booleans,
i.e., the four possible constant FAIGs.</p>

<p>This is the FAIG equivalent of @(see 4vp)</p>"

  (defun faig-const-p (x)
    (declare (xargs :guard t))
    (and (consp x)
         (booleanp (car x))
         (booleanp (cdr x)))))



(defsection faig-const-fix
  :parents (4v-sexpr-to-faig)
  :short "Identity for FAIG constants, or constant X otherwise."
  :long "<p>Note that an older version of this function independently coerced
the car/cdr of @('t') to a Booleans when they were conses, but it seems simpler
to just say anything malformed gets fixed to @('X').</p>"

  (defun faig-const-fix (x)
    (declare (xargs :guard t))
    (if (faig-const-p x)
        x
      (faig-x)))

  (defthm faig-const-fix-of-faig-eval
    (equal (faig-const-fix (faig-eval x env))
           (faig-eval x env))
    :hints(("Goal" :in-theory (enable faig-eval)))))



(defsection faig-const-<=
  :parents (4v-sexpr-to-faig)
  :short "Lattice ordering for FAIG constants."
  :long "<p>This is just the FAIG equivalent of @(see 4v-<=).</p>"

  (defun faig-const-<= (x y)
    (declare (xargs :guard t))
    (let ((x (faig-const-fix x))
          (y (faig-const-fix y)))
      (or (equal x y)
          (equal x (faig-x))))))





(defsection faig-const->4v
  :parents (4v-sexpr-to-faig)
  :short "Convert a @(see faig-const-p) into a @(see 4vp)."

  (defun faig-const->4v (x)
    (declare (xargs :guard t))
    (cond ((equal x (faig-t)) (4vt))
          ((equal x (faig-f)) (4vf))
          ((equal x (faig-z)) (4vz))
          (t              (4vx)))))

(defsection faig-const-list->4v-list
  :parents (faig-const->4v)

  (defun faig-const-list->4v-list (x)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (cons (faig-const->4v (car x))
            (faig-const-list->4v-list (cdr x))))))


(defsection faig-const-alist->4v-alist
  :parents (faig-const->4v)

  (defun faig-const-alist->4v-alist (x)
    (declare (xargs :guard t))
    (cond ((atom x)
           nil)
          ((atom (car x))
           ;; Bad alist convention
           (faig-const-alist->4v-alist (cdr x)))
          (t
           (cons (cons (caar x) (faig-const->4v (cdar x)))
                 (faig-const-alist->4v-alist (cdr x))))))

  (defthm lookup-faig-const-alist->4v-alist
    (equal (hons-assoc-equal k (faig-const-alist->4v-alist x))
           (and (hons-assoc-equal k x)
                (cons k (faig-const->4v (cdr (hons-assoc-equal k x))))))
    :hints(("Goal" :in-theory (disable faig-const->4v)))))






(defsection 4v->faig-const
  :parents (4v-sexpr-to-faig)
  :short "Convert a @(see 4vp) into a @(see faig-const-p)."

  (defun 4v->faig-const (x)
    "4V constant --> FAIG constant"
    (declare (xargs :guard t))
    (cond ((eq x (4vt)) (faig-t))
          ((eq x (4vf)) (faig-f))
          ((eq x (4vz)) (faig-z))
          (t            (faig-x))))

  (local (in-theory (enable 4v-fix)))

  (defthm 4v->faig-const-of-faig-const->4v
    (equal (4v->faig-const (faig-const->4v x))
           (faig-const-fix x)))

  (defthm faig-const->4v-of-4v->faig-const
    (equal (faig-const->4v (4v->faig-const x))
           (4v-fix x)))

  (defthm faig-const-<=-4v->faig-const
    (equal (faig-const-<= (4v->faig-const a) b)
           (4v-<= a (faig-const->4v b))))

  (defthm 4v-<=-faig-const->4v
    (equal (4v-<= (faig-const->4v a) b)
           (faig-const-<= a (4v->faig-const b)))))


(defsection 4v-list->faig-const-list
  :parents (4v->faig-const)

  (defun 4v-list->faig-const-list (x)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (cons (4v->faig-const (car x))
            (4v-list->faig-const-list (cdr x)))))

  (defthm faig-fix-nth-4v-list->faig-const-list
    (equal (faig-fix (nth n (4v-list->faig-const-list x)))
           (4v->faig-const (nth n x)))))




(defsection 4v-alist->faig-const-alist
  :parents (4v->faig-const)

  (defun 4v-alist->faig-const-alist (x)
    (declare (Xargs :guard t))
    (cond ((atom x)
           nil)
          ((atom (car x))
           ;; Bad alist convention
           (4v-alist->faig-const-alist (cdr x)))
          (t
           (cons (cons (caar x) (4v->faig-const (cdar x)))
                 (4v-alist->faig-const-alist (cdr x))))))

   (defthm hons-assoc-equal-4v-alist->faig-const-alist
     (equal (hons-assoc-equal k (4v-alist->faig-const-alist al))
            (and (hons-assoc-equal k al)
                 (cons k (4v->faig-const (cdr (hons-assoc-equal k al))))))))




(defsection 4v-and-faig-operations-commute
  :parents (4v-sexpr-to-faig)
  :short "Lemmas showing that equivalence of @(see 4v-operations) to @(see
faig-constructors)."

  (local (in-theory (enable* (:ruleset f-aig-defs)
                             (:ruleset 4v-op-defs))))

  (defun apply-to-args (fn args)
    (declare (xargs :guard t))
    (if (atom args)
        nil
      (cons (list fn (car args))
            (apply-to-args fn (cdr args)))))

  (defmacro fv-4v-commute (4vfn fvfn args)
    `(defthm ,(intern-in-package-of-symbol
               (concatenate 'string "4V->FAIG-CONST-OF-" (symbol-name 4vfn))
               4vfn)
       (equal (4v->faig-const (,4vfn . ,args))
              (,fvfn . ,(apply-to-args '4v->faig-const args)))))

  (fv-4v-commute 4v-fix      faig-const-fix (a))
  (fv-4v-commute 4v-unfloat  f-aig-unfloat      (a))
  (fv-4v-commute 4v-not      f-aig-not      (a))
  (fv-4v-commute 4v-and      f-aig-and      (a b))
  (fv-4v-commute 4v-or       f-aig-or       (a b))
  (fv-4v-commute 4v-xor      f-aig-xor      (a b))
  (fv-4v-commute 4v-iff      f-aig-iff      (a b))
  (fv-4v-commute 4v-ite      f-aig-ite      (a b c))
  (fv-4v-commute 4v-ite*     f-aig-ite*     (a b c))
  (fv-4v-commute 4v-zif      f-aig-zif      (a b c))
  (fv-4v-commute 4v-tristate t-aig-tristate      (c a))
  (fv-4v-commute 4v-pullup   f-aig-pullup   (a))
  (fv-4v-commute 4v-res      f-aig-res      (a b)))





(defsection 4v-sexpr-to-faig-plain
  :parents (4v-sexpr-to-faig)
  :short "Non-optimized conversion from sexprs into faigs."
  :long "<p>This is a straightforward, non-optimizing conversion where we just
use the @('f-') versions of the @(see faig-constructors) at each level.</p>"

  (mutual-recursion
   (defun 4v-sexpr-to-faig-plain (x onoff)
     (declare (xargs :guard t
                     :verify-guards nil))
     (b* (((when (atom x))
           (if x
               (let ((look (hons-get x onoff)))
                 (if (consp (cdr look))
                     (cdr look)
                   (faig-x)))
             (faig-x)))
          (fn (car x))
          ((when (eq fn (4vt))) (faig-t))
          ((when (eq fn (4vf))) (faig-f))
          ((when (eq fn (4vz))) (faig-z))
          ((when (eq fn (4vx))) (faig-x))
          (args (4v-sexpr-to-faig-plain-list (cdr x) onoff))
          (arg1 (4v-first  args))
          (arg2 (4v-second args))
          (arg3 (4v-third  args)))
       (case fn
         (not       (f-aig-not    arg1))
         (and       (f-aig-and    arg1 arg2))
         (xor       (f-aig-xor    arg1 arg2))
         (iff       (f-aig-iff    arg1 arg2))
         (or        (f-aig-or     arg1 arg2))
         (ite*      (f-aig-ite*   arg1 arg2 arg3))
         (zif       (f-aig-zif    arg1 arg2 arg3))
         (buf       (f-aig-unfloat    arg1))
         (res       (f-aig-res    arg1 arg2))
         (tristate  (t-aig-tristate    arg1 arg2))
         (ite       (f-aig-ite    arg1 arg2 arg3))
         (pullup    (f-aig-pullup arg1))
         (id        (faig-fix     arg1))
         (otherwise (faig-x)))))

   (defun 4v-sexpr-to-faig-plain-list (x onoff)
     (declare (xargs :guard t))
     (if (atom x)
         nil
       (cons (4v-sexpr-to-faig-plain (car x) onoff)
             (4v-sexpr-to-faig-plain-list (cdr x) onoff)))))

  (verify-guards 4v-sexpr-to-faig-plain
    :hints (("goal" :in-theory (enable nth-open-quotep))))

  (memoize '4v-sexpr-to-faig-plain
           :condition '(and (consp x) (consp (cdr x))))

  (defthm-4v-sexpr-flag
    (defthm consp-4v-sexpr-to-faig-plain
      (consp (4v-sexpr-to-faig-plain x al))
      :rule-classes :type-prescription
      :flag sexpr)
    (defthm alistp-4v-sexpr-to-faig-plain-list
      (alistp (4v-sexpr-to-faig-plain-list x al))
      :flag sexpr-list))


  (local (defthm 4v->faig-const-nth-when-lists-equal
           (let ((4v-env (faig-const-alist->4v-alist (faig-eval-alist onoff env))))
             (implies (equal (faig-eval-list (4v-sexpr-to-faig-plain-list x onoff) env)
                             (4v-list->faig-const-list (4v-sexpr-eval-list x 4v-env)))
                      (equal (4v->faig-const (nth n (4v-sexpr-eval-list x 4v-env)))
                             (faig-eval (nth n (4v-sexpr-to-faig-plain-list x onoff)) env))))
           :hints (("goal"
                    :in-theory (disable 4v->faig-const faig-eval
                                        4v-sexpr-to-faig-plain
                                        faig-const-alist->4v-alist
                                        faig-eval-alist)
                    :induct (nth n x)))))

  (defthm-4v-sexpr-flag
    (defthm faig-eval-4v-sexpr-to-faig-plain
      (let ((4v-env (faig-const-alist->4v-alist (faig-eval-alist onoff env))))
        (equal (faig-eval (4v-sexpr-to-faig-plain x onoff) env)
               (4v->faig-const (4v-sexpr-eval x 4v-env))))
      :flag sexpr)
    (defthm faig-eval-4v-sexpr-to-faig-plain-list
      (let ((4v-env (faig-const-alist->4v-alist (faig-eval-alist onoff env))))
        (equal (faig-eval-list (4v-sexpr-to-faig-plain-list x onoff) env)
               (4v-list->faig-const-list (4v-sexpr-eval-list x 4v-env))))
      :flag sexpr-list)
    :hints(("Goal"
            :expand ((4v-sexpr-eval x (faig-const-alist->4v-alist (faig-eval-alist onoff env))))
            :in-theory
            (e/d* ()
                  (4v->faig-const
                   nth
                   nth-when-zp
                   faig-const-fix
                   faig-const-alist->4v-alist
                   faig-const->4v
                   faig-eval
                   (:ruleset 4v-op-defs)
                   (:ruleset f-aig-defs)))
            :induct (4v-sexpr-flag flag x)))))



(local
 (defsection promote-t-aig-ops-to-f-aig-ops

   (local (in-theory (enable* (:ruleset f-aig-defs)
                              (:ruleset t-aig-defs))))

   (defthm t-aig-not-of-f-aig-unfloat
     (equal (t-aig-not (f-aig-unfloat x))
            (f-aig-not x)))

   (defthm t-aig-and-f-aig-unfloat
     (equal (t-aig-and (f-aig-unfloat x) (f-aig-unfloat y))
            (f-aig-and x y)))

   (defthm t-aig-or-f-aig-unfloat
     (equal (t-aig-or (f-aig-unfloat x) (f-aig-unfloat y))
            (f-aig-or x y)))

   (defthm t-aig-xor-f-aig-unfloat
     (equal (t-aig-xor (f-aig-unfloat x) (f-aig-unfloat y))
            (f-aig-xor x y)))

   (defthm t-aig-iff-f-aig-unfloat
     (equal (t-aig-iff (f-aig-unfloat x) (f-aig-unfloat y))
            (f-aig-iff x y)))

   (defthm t-aig-ite-f-aig-unfloat
     (equal (t-aig-ite (f-aig-unfloat c) (f-aig-unfloat x) (f-aig-unfloat y))
            (f-aig-ite c x y)))

   (defthm t-aig-ite*-unfloat-is-f-aig-zif-unfloat
     (equal (t-aig-ite* (f-aig-unfloat c) x y)
            (f-aig-zif c x y)))

   (defthm t-aig-ite*-f-aig-unfloat
     (equal (f-aig-zif c (f-aig-unfloat x) (f-aig-unfloat y))
            (f-aig-ite* c x y)))))



(local (defun nth-both-ind (n x y)
         (if (zp n)
             (cons x y)
           (nth-both-ind (1- n) (cdr x) (cdr y)))))



(defsection maybe-f-aig-unfloat

  (defund maybe-f-aig-unfloat (sexpr faig)
    (declare (xargs :guard t))
    (if (3v-syntax-sexprp sexpr)
        faig
      (f-aig-unfloat faig)))

  (local (in-theory (enable maybe-f-aig-unfloat)))

  (defthm faig-eval-maybe-f-aig-unfloat
    (implies (equal (faig-eval x fenv)
                    (4v->faig-const (4v-sexpr-eval sexpr senv)))
             (equal (faig-eval (maybe-f-aig-unfloat sexpr x) fenv)
                    (faig-eval (f-aig-unfloat x) fenv)))))



(defsection maybe-f-aig-unfloat-list

  (defun maybe-f-aig-unfloat-list (sexprs faigs)
    (declare (xargs :guard (equal (len sexprs) (len faigs))))
    (if (atom sexprs)
        nil
      (cons (maybe-f-aig-unfloat (car sexprs) (car faigs))
            (maybe-f-aig-unfloat-list (cdr sexprs) (cdr faigs)))))

  (defthm nth-maybe-f-aig-unfloat-list
    (implies (equal (len x) (len sexprs))
             (equal (faig-fix (nth n (maybe-f-aig-unfloat-list sexprs x)))
                    (faig-fix (maybe-f-aig-unfloat (nth n sexprs) (nth n x)))))
    :hints(("Goal"
            :induct (nth-both-ind n sexprs x)
            :expand ((maybe-f-aig-unfloat-list sexprs x)))))

  (defthm nth-maybe-f-aig-unfloat-list-faig-equiv
    (implies (equal (len x) (len sexprs))
             (faig-equiv (nth n (maybe-f-aig-unfloat-list sexprs x))
                         (maybe-f-aig-unfloat (nth n sexprs) (nth n x))))
    :hints(("Goal"
            :induct (nth-both-ind n sexprs x)
            :expand ((maybe-f-aig-unfloat-list sexprs x))))))





(defsection 4v-sexpr-to-faig-opt
  :parents (4v-sexpr-to-faig)
  :short "Optimized conversion from sexprs into faigs."

  (mutual-recursion
   (defun 4v-sexpr-to-faig-opt (x onoff)
     (declare (xargs :guard t :verify-guards nil))
     (b* (((when (atom x))
           (if x
               (let ((look (hons-get x onoff)))
                 (if (consp (cdr look))
                     (cdr look)
                   (faig-x)))
             (faig-x)))
          (fn (car x))
          ((when (eq fn (4vt))) (faig-t))
          ((when (eq fn (4vf))) (faig-f))
          ((when (eq fn (4vz))) (faig-z))
          ((when (eq fn (4vx))) (faig-x))
          (sargs (cdr x))
          (args (4v-sexpr-to-faig-opt-list sargs onoff))
          ;; There are a few functions where we don't really get any benefit from
          ;; knowing the args are three-valued:
          ((when (eq fn 'id))       (faig-fix (4v-first args))) ;; bozo why??
          ((when (eq fn 'res))      (f-aig-res (4v-first args) (4v-second args)))
          ((when (eq fn 'tristate)) (t-aig-tristate (4v-first args) (4v-second args)))
          ((when (eq fn 'pullup))   (f-aig-pullup (4v-first args)))
          ((when (eq fn 'zif))
           (t-aig-ite* (maybe-f-aig-unfloat
                        (mbe :logic (first sargs)
                             :exec (and (consp sargs) (car sargs)))
                        (4v-first args))
                       (4v-second args)
                       (4v-third args)))
          ;; Otherwise, fixup only those subexpressions that might produce Zs
          (args (maybe-f-aig-unfloat-list sargs args))
          (arg1 (4v-first args))
          (arg2 (4v-second args))
          (arg3 (4v-third args)))
       (case fn
         (not       (t-aig-not  arg1))
         (and       (t-aig-and  arg1 arg2))
         (xor       (t-aig-xor  arg1 arg2))
         (iff       (t-aig-iff  arg1 arg2))
         (ite*      (t-aig-ite* arg1 arg2 arg3))
         (or        (t-aig-or   arg1 arg2))
         (buf       (faig-fix   arg1))
         (ite       (t-aig-ite  arg1 arg2 arg3))
         (otherwise (faig-x)))))
   (defun 4v-sexpr-to-faig-opt-list (x onoff)
     (declare (xargs :guard t))
     (if (atom x)
         nil
       (cons (4v-sexpr-to-faig-opt (car x) onoff)
             (4v-sexpr-to-faig-opt-list (cdr x) onoff)))))

  (defthm len-4v-sexpr-to-faig-opt-list
    (equal (len (4v-sexpr-to-faig-opt-list x onoff))
           (len x)))

  (defthm-4v-sexpr-flag
    (defthm consp-4v-sexpr-to-faig-opt
      (consp (4v-sexpr-to-faig-opt x al))
      :rule-classes :type-prescription
      :flag sexpr)
    (defthm alistp-4v-sexpr-to-faig-opt-list
      (alistp (4v-sexpr-to-faig-opt-list x al))
      :flag sexpr-list))


  (verify-guards 4v-sexpr-to-faig-opt
    :hints (("goal" :in-theory (enable nth-open-quotep))))

  (memoize '4v-sexpr-to-faig-opt
           :condition '(and (consp x) (consp (cdr x))))

  (local
   (defthm substitute-4v-sexpr-to-faig-plain-3v-when-lists-equal
     (implies (equal (faig-eval-list (4v-sexpr-to-faig-opt-list x al) env)
                     (faig-eval-list (4v-sexpr-to-faig-plain-list x al) env))
              (equal (faig-eval (nth n (4v-sexpr-to-faig-opt-list x al)) env)
                     (faig-eval (nth n (4v-sexpr-to-faig-plain-list x al)) env)))
     :hints(("Goal" :in-theory (disable 4v-sexpr-to-faig-plain
                                        4v-sexpr-to-faig-opt)
             :induct (nth n x)
             :expand ((4v-sexpr-to-faig-opt-list x al)
                      (4v-sexpr-to-faig-plain-list x al))))))

  (local (defthm faig-eval-nth-when-faig-eval-list-equal
           (implies (equal (faig-eval-list x env)
                           (4v-list->faig-const-list y))
                    (equal (faig-eval (nth n x) env)
                           (4v->faig-const (nth n y))))))



  (local (defthm faig-eval-maybe-f-aig-unfloat-rw
           (let ((4v-env (faig-const-alist->4v-alist (faig-eval-alist al fenv))))
             (implies (and (bind-free '((al . al)) (al))
                           (equal (faig-eval x fenv)
                                  (4v->faig-const (4v-sexpr-eval sexpr 4v-env))))
                      (equal (faig-eval (maybe-f-aig-unfloat sexpr x) fenv)
                             (faig-eval (f-aig-unfloat x) fenv))))
           :hints(("Goal" :in-theory (enable maybe-f-aig-unfloat)))))

  (local (defthm faig-eval-maybe-f-aig-unfloat-rw1
           (let ((4v-env (faig-const-alist->4v-alist (faig-eval-alist al fenv))))
             (implies
              (and (bind-free '((al . al)) (al))
                   (equal (faig-eval-list x fenv)
                          (4v-list->faig-const-list (4v-sexpr-eval-list sexprs 4v-env))))
              (equal (faig-eval (maybe-f-aig-unfloat (nth n sexprs) (nth n x)) fenv)
                     (faig-eval (f-aig-unfloat (nth n x)) fenv))))
           :hints(("Goal"
                   :in-theory (disable* maybe-f-aig-unfloat)
                   :expand ((faig-eval-list x fenv)
                            (:free (a) (4v-sexpr-eval-list sexprs a))
                            (:free (a b) (4v-list->faig-const-list (cons a b))))
                   :induct (nth-both-ind n sexprs x)))))

  (local (defthm faig-eval-nth-maybe-f-aig-unfloat-list
           (implies (and (equal (faig-eval (nth n x) fenv)
                                (4v->faig-const (4v-sexpr-eval (nth n sexprs) senv)))
                         (equal (len x) (len sexprs)))
                    (equal (faig-eval (nth n (maybe-f-aig-unfloat-list sexprs x)) fenv)
                           (faig-eval (f-aig-unfloat (nth n x)) fenv)))
           :hints(("Goal" :in-theory (disable* 4v->faig-const)))))

  (defthm-4v-sexpr-flag
    (defthm faig-eval-4v-sexpr-to-faig-opt
      (equal (faig-eval (4v-sexpr-to-faig-opt x al) env)
             (faig-eval (4v-sexpr-to-faig-plain x al) env))
      :flag sexpr)
    (defthm faig-eval-4v-sexpr-to-faig-opt-list
      (equal (faig-eval-list (4v-sexpr-to-faig-opt-list x al) env)
             (faig-eval-list (4v-sexpr-to-faig-plain-list x al) env))
      :flag sexpr-list)
    :hints(("Goal"
            :expand ((4v-sexpr-eval x (faig-const-alist->4v-alist (faig-eval-alist al env))))
            :in-theory
            (e/d* ()
                  (4v->faig-const nth
                                  faig-const-fix
                                  faig-const-alist->4v-alist
                                  faig-const->4v
                                  maybe-f-aig-unfloat
                                  )))
           (and stable-under-simplificationp
                '(:expand ((4v-sexpr-to-faig-opt-list (cdr x) al)))))))



(defsection wrapper
  :extension 4v-sexpr-to-faig

  (defund 4v-sexpr-to-faig-fn1 (x onoff optimizep)
    "Assumes ONOFF is fast."
    (declare (xargs :guard t))
    (if optimizep
        (4v-sexpr-to-faig-opt x onoff)
      (4v-sexpr-to-faig-plain x onoff)))

  (defund 4v-sexpr-to-faig-fn (x onoff optimizep)
    "Assumes ONOFF is fast."
    (declare (xargs :guard t))
    (with-fast-alist onoff
      (if optimizep
          (4v-sexpr-to-faig-opt x onoff)
        (4v-sexpr-to-faig-plain x onoff))))

  (defmacro 4v-sexpr-to-faig (x onoff &key (optimize 't))
    `(4v-sexpr-to-faig-fn ,x ,onoff ,optimize))

  (add-macro-alias 4v-sexpr-to-faig 4v-sexpr-to-faig-fn)

  (local (in-theory (enable 4v-sexpr-to-faig-fn1
                            4v-sexpr-to-faig-fn)))

  (defthm 4v-sexpr-to-faig-fn1-removal
    (equal (4v-sexpr-to-faig-fn1 x onoff optimizep)
           (4v-sexpr-to-faig-fn x onoff optimizep)))

  (defthm consp-of-4v-sexpr-to-faig-fn
    (consp (4v-sexpr-to-faig-fn x onoff optimize))
    :rule-classes :type-prescription)

  (defthm faig-eval-of-4v-sexpr-to-faig
    (equal (faig-eval (4v-sexpr-to-faig-fn x onoff optimize) env)
           (faig-eval (4v-sexpr-to-faig-plain x onoff) env))))



(defsection 4v-sexpr-to-faig-list
  :parents (4v-sexpr-to-faig)
  :short "Convert a sexpr list into a @(see faig) list."

  (defund 4v-sexpr-to-faig-list-fn1 (x onoff optimizep)
    "Assumes ONOFF is fast."
    (declare (xargs :guard t))
    (if optimizep
        (4v-sexpr-to-faig-opt-list x onoff)
      (4v-sexpr-to-faig-plain-list x onoff)))

  (defund 4v-sexpr-to-faig-list-fn (x onoff optimizep)
    "Assumes ONOFF is fast."
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic
         (if (atom x)
             nil
           (cons (4v-sexpr-to-faig-fn (car x) onoff optimizep)
                 (4v-sexpr-to-faig-list-fn (cdr x) onoff optimizep)))
         :exec
         (with-fast-alist onoff
           (4v-sexpr-to-faig-list-fn1 x onoff optimizep))))

  (defmacro 4v-sexpr-to-faig-list (x onoff &key (optimize 't))
    `(4v-sexpr-to-faig-list-fn ,x ,onoff ,optimize))

  (add-macro-alias 4v-sexpr-to-faig-list 4v-sexpr-to-faig-list-fn)

  (local (in-theory (enable 4v-sexpr-to-faig-list-fn1
                            4v-sexpr-to-faig-list-fn
                            4v-sexpr-to-faig-fn)))

  (defthm 4v-sexpr-to-faig-list-fn1-removal
    (equal (4v-sexpr-to-faig-list-fn1 x onoff optimizep)
           (4v-sexpr-to-faig-list-fn x onoff optimizep)))

  (verify-guards 4v-sexpr-to-faig-list-fn)

  (defthm alistp-of-4v-sexpr-to-faig-list-fn
    ;; Sort of an abuse of alistp, just showing that they're all conses.
    (alistp (4v-sexpr-to-faig-list-fn x onoff optimize))
    :rule-classes :type-prescription)

  (defthm len-of-4v-sexpr-to-faig-list-fn
    (equal (len (4v-sexpr-to-faig-list-fn x onoff optimize))
           (len x)))

  (defthm faig-eval-list-of-4v-sexpr-to-faig
    (equal (faig-eval-list (4v-sexpr-to-faig-list-fn x onoff optimize) env)
           (faig-eval-list (4v-sexpr-to-faig-plain-list x onoff) env))))




(defsection 4v-sexpr-to-faig-alist
  :parents (4v-sexpr-to-faig)
  :short "Convert a sexpr alist into an @(see faig) alist."

  (defund 4v-sexpr-to-faig-alist-fn1 (x onoff optimizep)
    "Assumes ONOFF is fast."
    (declare (xargs :guard t))
    (cond ((atom x)
           nil)
          ((atom (car x))
           (4v-sexpr-to-faig-alist-fn1 (cdr x) onoff optimizep))
          (t
           (cons (cons (caar x)
                       (4v-sexpr-to-faig-fn1 (cdar x) onoff optimizep))
                 (4v-sexpr-to-faig-alist-fn1 (cdr x) onoff optimizep)))))

  (defun 4v-sexpr-to-faig-alist-fn (x onoff optimizep)
    "Assumes ONOFF is fast."
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic
         (cond ((atom x)
                nil)
               ((atom (car x))
                (4v-sexpr-to-faig-alist-fn (cdr x) onoff optimizep))
               (t
                (cons (cons (caar x)
                            (4v-sexpr-to-faig-fn (cdar x) onoff optimizep))
                      (4v-sexpr-to-faig-alist-fn (cdr x) onoff optimizep))))
         :exec
         (with-fast-alist onoff
           (4v-sexpr-to-faig-alist-fn1 x onoff optimizep))))

  (defmacro 4v-sexpr-to-faig-alist (x onoff &key (optimize 't))
    `(4v-sexpr-to-faig-alist-fn ,x ,onoff ,optimize))

  (add-macro-alias 4v-sexpr-to-faig-alist 4v-sexpr-to-faig-alist-fn)

  (local (in-theory (enable 4v-sexpr-to-faig-alist-fn1
                            4v-sexpr-to-faig-alist-fn)))

  (defthm 4v-sexpr-to-faig-alist-fn1-removal
    (equal (4v-sexpr-to-faig-alist-fn1 x onoff optimizep)
           (4v-sexpr-to-faig-alist-fn x onoff optimizep)))

  (verify-guards 4v-sexpr-to-faig-alist-fn))

