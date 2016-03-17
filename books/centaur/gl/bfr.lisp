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
(include-book "centaur/misc/universal-equiv" :dir :system)
(include-book "std/basic/arith-equiv-defs" :dir :system)
(include-book "centaur/ubdds/lite" :dir :system)
(include-book "centaur/ubdds/param" :dir :system)
(include-book "centaur/aig/misc" :dir :system)
(local (include-book "centaur/aig/aig-vars" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))

(defsection bfr
  :parents (reference)
  :short "An abstraction of the <b>B</b>oolean <b>F</b>unction
<b>R</b>epresentation used by GL."

  :long "<p>GL was originally designed to operate on @(see ubdds), with
support for @(see aig)s being added later.  To avoid redoing a lot of proof
work, a small level of indirection was added.</p>

<p>The particular Boolean function representation that we are using at any
particular time is governed by @(see bfr-mode), and operations like @(see
bfr-and) allow us to construct new function nodes using whatever the current
representation is.</p>")

(local (xdoc::set-default-parents bfr))

;; [Jared]: Note that I deleted a lot of old commented-out code relating to
;; defining bfr-p and proving related things about bfr-p.  I think that idea
;; has been long abandoned.  If you ever want to review it, you can go back to
;; Git revision 1207333ab8e09e338b7216c473c8f6654410c360 or earlier.

(defsection bfr-mode
  :short "Determine the current @(see bfr) mode we are using."
  :long "<p>GL users should generally not use this.</p>

<p>@(call bfr-mode) is an attachable function which is typically attached to
either @('bfr-aig') or @('bfr-bdd').  When it returns true, we are to use @(see
aig)s, otherwise we use @(see ubdds).</p>

@(def bfr-mode)"

  (defstub bfr-mode () t)
  (defun bfr-aig () (declare (xargs :guard t)) t)
  (defun bfr-bdd () (declare (xargs :guard t)) nil)

  ;; Default to using BDDs
  (defattach bfr-mode bfr-bdd))

(defsection bfr-case
  :short "Choose behavior based on the current @(see bfr) mode."
  :long "<p>Usage:</p>

@({
     (brf-case :aig aigcode
               :bdd bddcode)
})

<p>expands to @('aigcode') if we are currently in AIG mode, or @('bddcode') if
we are currently in BDD mode.  This is often used to implement basic wrappers
like @(see bfr-and).</p>

@(def bfr-case)"

  (defmacro bfr-case (&key aig bdd)
    `(if (bfr-mode)
         ,aig
       ,bdd)))

(local (in-theory (enable booleanp)))


(define bfr-eval (x env)
  :short "Evaluate a BFR under an appropriate BDD/AIG environment."
  :returns bool
  (mbe :logic
       (bfr-case :bdd (acl2::eval-bdd x env)
                 :aig (acl2::aig-eval x env))
       :exec
       (if (booleanp x)
           x
         (bfr-case :bdd (acl2::eval-bdd x env)
                   :aig (acl2::aig-eval x env))))
  ///
  (defthm bfr-eval-consts
    (and (equal (bfr-eval t env) t)
         (equal (bfr-eval nil env) nil))))


(acl2::def-universal-equiv bfr-equiv
  :qvars (env)
  :equiv-terms ((equal (bfr-eval acl2::x env)))
  :short "Semantics equivalence of BFRs, i.e., equal evaluation under every
possible environment.")

(defcong bfr-equiv equal (bfr-eval x env) 1
  :hints(("Goal" :in-theory (e/d (bfr-equiv-necc)))))


(define bfr-lookup ((n natp) env)
  :short "Look up a BFR variable in an appropriate BDD/AIG environment."
  (let ((n (lnfix n)))
    (bfr-case
      :bdd (and (acl2::with-guard-checking nil (ec-call (nth n env))) t)
      :aig (let ((look (hons-get n env)))
             (if look
                 (and (cdr look) t)
               t))))
  ///
  (in-theory (disable (:e bfr-lookup)))

  (defcong acl2::nat-equiv equal (bfr-lookup n env) 1
    :hints(("Goal" :in-theory (enable bfr-lookup)))))


(define bfr-set-var ((n natp) val env)
  :short "Set the @('n')th BFR variable to some value in an AIG/BDD environment."
  (let ((n (lnfix n)))
    (bfr-case :bdd (acl2::with-guard-checking
                    nil
                    (ec-call (update-nth n (and val t) env)))
              :aig (hons-acons n (and val t) env)))
  ///
  (in-theory (disable (:e bfr-set-var)))

  (defthm bfr-lookup-bfr-set-var
    (equal (bfr-lookup n (bfr-set-var m val env))
           (if (equal (nfix n) (nfix m))
               (and val t)
             (bfr-lookup n env)))
    :hints(("Goal" :in-theory (e/d (bfr-lookup bfr-set-var)
                                   (update-nth nth)))))

  (defcong acl2::nat-equiv equal (bfr-set-var n val env) 1
    :hints(("Goal" :in-theory (enable bfr-set-var)))))


(define bfr-var ((n natp))
  :short "Construct the @('n')th BFR variable."
  (let ((n (lnfix n)))
    (bfr-case :bdd (acl2::qv n)
              :aig n))
  ///
  (in-theory (disable (:e bfr-var)))

  (defthm bfr-eval-bfr-var
    (equal (bfr-eval (bfr-var n) env)
           (bfr-lookup n env))
    :hints(("Goal" :in-theory (enable bfr-lookup bfr-eval bfr-var
                                      acl2::eval-bdd))))

  (defcong acl2::nat-equiv equal (bfr-var n) 1
    :hints(("Goal" :in-theory (enable bfr-var)))))


(define bfr-not (x)
  :short "Construct the NOT of a BFR."
  :returns (bfr)
  (mbe :logic
       (bfr-case :bdd (acl2::q-not x)
                 :aig (acl2::aig-not x))
       :exec
       (if (booleanp x)
           (not x)
         (bfr-case :bdd (acl2::q-not x)
                   :aig (acl2::aig-not x))))
  ///
  (defthm bfr-eval-bfr-not
    (equal (bfr-eval (bfr-not x) env)
           (not (bfr-eval x env)))
    :hints(("Goal" :in-theory (enable bfr-eval))))

  (local (in-theory (disable bfr-not)))

  (defcong bfr-equiv bfr-equiv (bfr-not x) 1
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause))))))))


(define bfr-binary-and (x y)
  :parents (bfr-and)
  :returns (bfr)
  (mbe :logic
       (bfr-case :bdd (acl2::q-binary-and x y)
                 :aig (acl2::aig-and x y))
       :exec
       (cond ((not x) nil)
             ((not y) nil)
             ((and (eq x t) (eq y t)) t)
             (t (bfr-case :bdd (acl2::q-binary-and x y)
                          :aig (acl2::aig-and x y)))))
  ///
  (defthm bfr-eval-bfr-binary-and
    (equal (bfr-eval (bfr-binary-and x y) env)
           (and (bfr-eval x env)
                (bfr-eval y env)))
    :hints (("goal" :in-theory (e/d (bfr-eval) ((force))))))

  (defthm bfr-and-of-nil
    (and (equal (bfr-binary-and nil y) nil)
         (equal (bfr-binary-and x nil) nil))
    :hints(("Goal" :in-theory (enable acl2::aig-and))))

  (local (in-theory (disable bfr-binary-and)))

  (defcong bfr-equiv bfr-equiv (bfr-binary-and x y) 1
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defcong bfr-equiv bfr-equiv (bfr-binary-and x y) 2
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause))))))))

(define bfr-and-macro-logic-part (args)
  :parents (bfr-and)
  :short "Generates the :logic part for a bfr-and MBE call."
  :mode :program
  (cond ((atom args)
         t)
        ((atom (cdr args))
         (car args))
        (t
         `(bfr-binary-and ,(car args) ,(bfr-and-macro-logic-part (cdr args))))))

(define bfr-and-macro-exec-part (args)
  :parents (bfr-and)
  :short "Generates the :exec part for a bfr-and MBE call."
  :mode :program
  (cond ((atom args)
         t)
        ((atom (cdr args))
         (car args))
        (t
         `(let ((bfr-and-x-do-not-use-elsewhere ,(car args)))
            (and bfr-and-x-do-not-use-elsewhere
                 (bfr-binary-and
                  bfr-and-x-do-not-use-elsewhere
                  (check-vars-not-free
                   (bfr-and-x-do-not-use-elsewhere)
                   ,(bfr-and-macro-exec-part (cdr args)))))))))

(defsection bfr-and
  :short "@('(bfr-and x1 x2 ...)') constructs the AND of these BFRs."
  :long "@(def bfr-and)"
  (defmacro bfr-and (&rest args)
    `(mbe :logic ,(bfr-and-macro-logic-part args)
          :exec  ,(bfr-and-macro-exec-part  args))))


(define bfr-ite-fn (x y z)
  :parents (bfr-ite)
  :returns (bfr)
  (mbe :logic
       (bfr-case :bdd (acl2::q-ite x y z)
                 :aig (cond ((eq x t) y)
                            ((eq x nil) z)
                            (t (acl2::aig-ite x y z))))
       :exec
       (if (booleanp x)
           (if x y z)
         (bfr-case :bdd (acl2::q-ite x y z)
                   :aig (acl2::aig-ite x y z))))
  ///
  (defthm bfr-eval-bfr-ite-fn
    (equal (bfr-eval (bfr-ite-fn x y z) env)
           (if (bfr-eval x env)
               (bfr-eval y env)
             (bfr-eval z env)))
    :hints (("goal" :in-theory (enable booleanp bfr-eval))))

  (defthm bfr-ite-fn-bools
    (and (equal (bfr-ite-fn t y z) y)
         (equal (bfr-ite-fn nil y z) z)))

  (local (in-theory (disable bfr-ite-fn)))

  (defcong bfr-equiv bfr-equiv (bfr-ite-fn x y z) 1
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defcong bfr-equiv bfr-equiv (bfr-ite-fn x y z) 2
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defcong bfr-equiv bfr-equiv (bfr-ite-fn x y z) 3
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause))))))))


(defsection bfr-ite
  :short "@(call bfr-ite) constructs the If-Then-Else of these BFRs."
  :long "@(def bfr-ite)"
  (defmacro bfr-ite (x y z)
    ;; BOZO why not move the COND inside the ITE?
    (cond ((and (or (quotep y) (atom y))
                (or (quotep z) (atom z)))
           `(bfr-ite-fn ,x ,y ,z))
          (t
           `(mbe :logic (bfr-ite-fn ,x ,y ,z)
                 :exec (let ((bfr-ite-x-do-not-use-elsewhere ,x))
                         (cond
                          ((eq bfr-ite-x-do-not-use-elsewhere nil) ,z)
                          ((eq bfr-ite-x-do-not-use-elsewhere t) ,y)
                          (t
                           (bfr-ite-fn bfr-ite-x-do-not-use-elsewhere
                                       ,y ,z)))))))))

(define bfr-binary-or (x y)
  :parents (bfr-or)
  (mbe :logic
       (bfr-case :bdd (acl2::q-or x y)
                 :aig (acl2::aig-or x y))
       :exec
       (if (and (booleanp x) (booleanp y))
           (or x y)
         (bfr-case :bdd (acl2::q-or x y)
                   :aig (acl2::aig-or x y))))
  ///
  (defthm bfr-eval-bfr-binary-or
    (equal (bfr-eval (bfr-binary-or x y) env)
           (or (bfr-eval x env)
               (bfr-eval y env)))
    :hints (("goal" :in-theory (e/d (booleanp bfr-eval) ((force))))))

  (defthm bfr-or-of-t
    (and (equal (bfr-binary-or t y) t)
         (equal (bfr-binary-or y t) t))
    :hints(("Goal" :in-theory (enable acl2::aig-or
                                      acl2::aig-and
                                      acl2::aig-not))))

  (local (in-theory (disable bfr-binary-or)))

  (defcong bfr-equiv bfr-equiv (bfr-binary-or x y) 1
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defcong bfr-equiv bfr-equiv (bfr-binary-or x y) 2
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause))))))))

(define bfr-or-macro-logic-part (args)
  :parents (bfr-or)
  :mode :program
  (cond ((atom args)
         nil)
        ((atom (cdr args))
         (car args))
        (t
         `(bfr-binary-or ,(car args) ,(bfr-or-macro-logic-part (cdr args))))))

(define bfr-or-macro-exec-part (args)
  :parents (bfr-or)
  :mode :program
  (cond ((atom args)
         nil)
        ((atom (cdr args))
         (car args))
        (t
         `(let ((bfr-or-x-do-not-use-elsewhere ,(car args)))
            ;; We could be slightly more permissive and just check
            ;; for any non-nil atom here.  But it's probably faster
            ;; to check equality with t and we probably don't care
            ;; about performance on non-ubddp bdds?
            (if (eq t bfr-or-x-do-not-use-elsewhere)
                t
              (bfr-binary-or
               bfr-or-x-do-not-use-elsewhere
               (check-vars-not-free
                (bfr-or-x-do-not-use-elsewhere)
                ,(bfr-or-macro-exec-part (cdr args)))))))))

(defsection bfr-or
  :short "@('(bfr-or x1 x2 ...)') constructs the OR of these BFRs."
  :long "@(def bfr-or)"

  (defmacro bfr-or (&rest args)
    `(mbe :logic ,(bfr-or-macro-logic-part args)
          :exec  ,(bfr-or-macro-exec-part  args))))


(define bfr-xor (x y)
  :short "@(call bfr-xor) constructs the XOR of these BFRs."
  (mbe :logic
       (bfr-case :bdd (acl2::q-xor x y)
                 :aig (acl2::aig-xor x y))
       :exec
       (if (and (booleanp x) (booleanp y))
           (xor x y)
         (bfr-case :bdd (acl2::q-xor x y)
                   :aig (acl2::aig-xor x y))))
  ///
  (defthm bfr-eval-bfr-xor
    (equal (bfr-eval (bfr-xor x y) env)
           (xor (bfr-eval x env)
                (bfr-eval y env)))
    :hints (("goal" :in-theory (e/d (bfr-eval) ((force))))))

  (local (in-theory (disable bfr-xor)))

  (defcong bfr-equiv bfr-equiv (bfr-xor x y) 1
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defcong bfr-equiv bfr-equiv (bfr-xor x y) 2
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause))))))))


(define bfr-iff (x y)
  :short "@(call bfr-iff) constructs the IFF of these BFRs."
  (mbe :logic
       (bfr-case :bdd (acl2::q-iff x y)
                 :aig (acl2::aig-iff x y))
       :exec
       (if (and (booleanp x) (booleanp y))
           (iff x y)
         (bfr-case :bdd (acl2::q-iff x y)
                   :aig (acl2::aig-iff x y))))
  ///
  (defthm bfr-eval-bfr-iff
    (equal (bfr-eval (bfr-iff x y) env)
           (iff (bfr-eval x env)
                (bfr-eval y env)))
    :hints (("goal" :in-theory (e/d (bfr-eval) ((force))))))

  (local (in-theory (disable bfr-iff)))

  (defcong bfr-equiv bfr-equiv (bfr-iff x y) 1
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defcong bfr-equiv bfr-equiv (bfr-iff x y) 2
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause))))))))


(define bfr-nor (x y)
  :short "@(call bfr-nor) constructs the NOR of these BFRs."
  (mbe :logic
       (bfr-case :bdd (acl2::q-nor x y)
                 :aig (acl2::aig-nor x y))
       :exec
       (if (and (booleanp x) (booleanp y))
           (not (or x y))
         (bfr-case :bdd (acl2::q-nor x y)
                   :aig (acl2::aig-nor x y))))
  ///
  (defthm bfr-eval-bfr-nor
    (equal (bfr-eval (bfr-nor x y) env)
           (not (or (bfr-eval x env)
                    (bfr-eval y env))))
    :hints (("goal" :in-theory (e/d (bfr-eval) ((force))))))

  (local (in-theory (disable bfr-nor)))

  (defcong bfr-equiv bfr-equiv (bfr-nor x y) 1
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defcong bfr-equiv bfr-equiv (bfr-nor x y) 2
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause))))))))


(define bfr-nand (x y)
  :short "@(call bfr-nand) constructs the NAND of these BFRs."
  (mbe :logic
       (bfr-case :bdd (acl2::q-nand x y)
                 :aig (acl2::aig-nand x y))
       :exec
       (if (and (booleanp x) (booleanp y))
           (not (and x y))
         (bfr-case :bdd (acl2::q-nand x y)
                   :aig (acl2::aig-nand x y))))
  ///
  (defthm bfr-eval-bfr-nand
    (equal (bfr-eval (bfr-nand x y) env)
           (not (and (bfr-eval x env)
                     (bfr-eval y env))))
    :hints (("goal" :in-theory (e/d (bfr-eval) ((force))))))

  (local (in-theory (disable bfr-nand)))

  (defcong bfr-equiv bfr-equiv (bfr-nand x y) 1
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defcong bfr-equiv bfr-equiv (bfr-nand x y) 2
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause))))))))


(define bfr-andc1 (x y)
  :short "@(call bfr-andc1) constructs the ANDC1 of these BFRs."
  (mbe :logic
       (bfr-case :bdd (acl2::q-and-c1 x y)
                 :aig (acl2::aig-andc1 x y))
       :exec
       (if (and (booleanp x) (booleanp y))
           (and (not x) y)
         (bfr-case :bdd (acl2::q-and-c1 x y)
                   :aig (acl2::aig-andc1 x y))))
  ///
  (defthm bfr-eval-bfr-andc1
    (equal (bfr-eval (bfr-andc1 x y) env)
           (and (not (bfr-eval x env))
                (bfr-eval y env)))
    :hints (("goal" :in-theory (e/d (bfr-eval) ((force))))))

  (local (in-theory (disable bfr-andc1)))

  (defcong bfr-equiv bfr-equiv (bfr-andc1 x y) 1
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defcong bfr-equiv bfr-equiv (bfr-andc1 x y) 2
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause))))))))


(define bfr-andc2 (x y)
  :short "@(call bfr-andc2) constructs the ANDC2 of these BFRs."
  (mbe :logic
       (bfr-case :bdd (acl2::q-and-c2 x y)
                 :aig (acl2::aig-andc2 x y))
       :exec
       (if (and (booleanp x) (booleanp y))
           (and x (not y))
         (bfr-case :bdd (acl2::q-and-c2 x y)
                   :aig (acl2::aig-andc2 x y))))
  ///
  (defthm bfr-eval-bfr-andc2
    (equal (bfr-eval (bfr-andc2 x y) env)
           (and (bfr-eval x env)
                (not (bfr-eval y env))))
    :hints (("goal" :in-theory (e/d (bfr-eval) ((force))))))

  (local (in-theory (disable bfr-andc2)))

  (defcong bfr-equiv bfr-equiv (bfr-andc2 x y) 1
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defcong bfr-equiv bfr-equiv (bfr-andc2 x y) 2
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause))))))))





(define bfr-to-param-space (p x)
  :short "Perhaps strengthen a BFR under some hypothesis."

  :long "<p>The general idea here is to use the hypothesis in order to
strengthen the variables that are going to be used while symbolically
simulating the conclusion.  The BFR @('p') is a representation of the
hypothesis, and @('x') is some BFR, typically a variable, that our hypothesis
might tell us something about.</p>

<p>In BDD mode, we use BDD parameterization to produce a new BDD that is
similar to @('x') but that may be collapsed in cases where @('p') is false.  In
AIG mode, we do something much lighter weight, and essentially just look for
variables that we happen to know are true or false.</p>"

  (bfr-case :bdd (acl2::to-param-space p x)
            :aig (acl2::aig-restrict
                  x (acl2::aig-extract-iterated-assigns-alist p 10))))

(define bfr-to-param-space-weak (p x)
  :parents (bfr-to-param-space)
  :short "Same as @(see bfr-to-param-space) for BDDs, but don't bother to do
anything if we're working with AIGs."
  (bfr-case :bdd (acl2::to-param-space p x)
            :aig x))

(define bfr-from-param-space (p x)
  :parents (bfr-to-param-space)
  (bfr-case :bdd (acl2::from-param-space p x)
            :aig x))


(define bfr-param-env (p env)
  (bfr-case :bdd (acl2::param-env p env)
            :aig env)
  ///
  (defthmd bfr-eval-to-param-space
    (implies (bfr-eval p env)
             (equal (bfr-eval (bfr-to-param-space p x)
                              (bfr-param-env p env))
                    (bfr-eval x env)))
    :hints(("Goal" :in-theory (e/d* (bfr-eval
                                     bfr-to-param-space
                                     acl2::param-env-to-param-space)))))

  (defthm bfr-eval-to-param-space-weak
    (implies (bfr-eval p env)
             (equal (bfr-eval (bfr-to-param-space-weak p x)
                              (bfr-param-env p env))
                    (bfr-eval x env)))
    :hints(("Goal" :in-theory (e/d* (bfr-eval
                                     bfr-to-param-space-weak
                                     acl2::param-env-to-param-space)))))


  (defthm bfr-eval-from-param-space
    (implies (bfr-eval p env)
             (equal (bfr-eval (bfr-from-param-space p x) env)
                    (bfr-eval x (bfr-param-env p env))))
    :hints(("Goal" :in-theory (e/d* (bfr-eval
                                     bfr-param-env
                                     bfr-from-param-space
                                     acl2::param-env-to-param-space))))))


(define bfr-unparam-env (p env)
  (bfr-case :bdd (acl2::unparam-env p env)
            :aig (append (acl2::aig-extract-iterated-assigns-alist p 10)
                         env))
  ///
  (local (in-theory (enable bfr-to-param-space
                            bfr-param-env)))

  (defthm bfr-eval-to-param-space-with-unparam-env
    (equal (bfr-eval (bfr-to-param-space p x) env)
           (bfr-eval x (bfr-unparam-env p env)))
    :hints (("goal" :do-not-induct t
             :in-theory (enable bfr-eval
                                acl2::unparam-env-to-param-space)))
    :otf-flg t)

  (local (defthm aig-eval-of-extract-iterated-assigns-self
           (implies (acl2::aig-eval x env)
                    (equal (acl2::aig-eval x
                                           (append
                                            (acl2::aig-extract-iterated-assigns-alist
                                             x n)
                                            env))
                           t))))

  (defthm bfr-eval-to-param-space-weak-with-unparam-env
    (implies (not (bfr-eval x (bfr-unparam-env x env)))
             (not (bfr-eval (bfr-to-param-space-weak x x) env)))
    :hints(("Goal" :in-theory (e/d (bfr-eval bfr-to-param-space-weak
                                             acl2::unparam-env-to-param-space
                                             bfr-unparam-env)
                                   (acl2::eval-bdd acl2::aig-eval)))))

  (defthm bfr-unparam-env-of-param-env
    (implies (bfr-eval p env)
             (equal (bfr-eval x (bfr-unparam-env p (bfr-param-env p env)))
                    (bfr-eval x env)))
    :hints(("Goal" :in-theory (enable bfr-eval))))

  (defthm bfr-param-env-of-unparam-env-of-param-env
    (implies (bfr-eval p env)
             (equal (bfr-eval x (bfr-param-env
                                 p
                                 (bfr-unparam-env
                                  p
                                  (bfr-param-env p env))))
                    (bfr-eval x (bfr-param-env p env))))
    :hints(("Goal" :in-theory (disable bfr-param-env bfr-unparam-env
                                       bfr-from-param-space)
            :use ((:instance bfr-eval-from-param-space
                   (env (bfr-unparam-env p (bfr-param-env p env))))))))

  (defthm bfr-lookup-of-unparam-env-of-param-env
    (implies (bfr-eval p env)
             (equal (bfr-lookup x (bfr-unparam-env p (bfr-param-env p env)))
                    (bfr-lookup x env)))
    :hints(("Goal" :use ((:instance bfr-unparam-env-of-param-env
                          (x (bfr-var x))))
            :in-theory (disable bfr-unparam-env-of-param-env)))))


(defsection bfr-semantic-depends-on

  (defun-sk bfr-semantic-depends-on (k x)
    (exists (env v)
            (not (equal (bfr-eval x (bfr-set-var k v env))
                        (bfr-eval x env)))))

  (defthm bfr-semantic-depends-on-of-set-var
    (implies (not (bfr-semantic-depends-on k x))
             (equal (bfr-eval x (bfr-set-var k v env))
                    (bfr-eval x env))))

  (in-theory (disable bfr-semantic-depends-on
                      bfr-semantic-depends-on-suff)))


(define bfr-depends-on (k x)
  :verify-guards nil
  (bfr-case :bdd (bfr-semantic-depends-on k x)
            :aig (set::in (nfix k) (acl2::aig-vars x)))
  ///
  (local (defthm aig-eval-under-env-with-non-aig-var-member
           (implies (not (set::in k (acl2::aig-vars x)))
                    (equal (acl2::aig-eval x (cons (cons k v) env))
                           (acl2::aig-eval x env)))
           :hints(("Goal" :in-theory (enable acl2::aig-eval acl2::aig-vars)))))

  (defthm bfr-eval-of-set-non-dep
    (implies (not (bfr-depends-on k x))
             (equal (bfr-eval x (bfr-set-var k v env))
                    (bfr-eval x env)))
    :hints(("Goal" :in-theory (enable bfr-depends-on
                                      bfr-semantic-depends-on-suff))
           (and stable-under-simplificationp
                '(:in-theory (enable bfr-eval bfr-set-var)))))

;; (defthm bfr-eval-of-set-non-dep
;;   (implies (not (bfr-depends-on k x))
;;            (equal (bfr-eval x (bfr-set-var k v env))
;;                   (bfr-eval x env)))
;;   :hints(("Goal" :use bfr-depends-on-suff)))

  (defthm bfr-depends-on-of-bfr-var
    (equal (bfr-depends-on m (bfr-var n))
           (equal (nfix m) (nfix n)))
    :hints(("goal" :in-theory (e/d (bfr-depends-on) (nfix)))
           (cond ((member-equal '(bfr-mode) clause)
                  (and stable-under-simplificationp
                       (if (eq (caar clause) 'not)
                           '(:use ((:instance bfr-semantic-depends-on-suff
                                    (k m) (x (bfr-var n))
                                    (v (not (bfr-lookup n env)))))
                             :in-theory (disable nfix))
                         '(:expand ((bfr-semantic-depends-on m (bfr-var n)))))))
                 ((member-equal '(not (bfr-mode)) clause)
                  '(:in-theory (e/d (bfr-depends-on bfr-var) (nfix))))))
    :otf-flg t)

  (defthm no-new-deps-of-bfr-not
    (implies (not (bfr-depends-on k x))
             (not (bfr-depends-on k (bfr-not x))))
    :hints(("goal" :in-theory (e/d (bfr-depends-on)))
           (cond ((member-equal '(bfr-mode) clause)
                  '(:expand ((bfr-semantic-depends-on k (bfr-not x)))
                    :use ((:instance bfr-semantic-depends-on-suff))))
                 ((member-equal '(not (bfr-mode)) clause)
                  '(:in-theory (e/d (bfr-depends-on bfr-not)))))))

  (defthm no-new-deps-of-bfr-and
    (implies (and (not (bfr-depends-on k x))
                  (not (bfr-depends-on k y)))
             (not (bfr-depends-on k (bfr-binary-and x y))))
    :hints(("goal" :in-theory (e/d (bfr-depends-on)))
           (cond ((member-equal '(bfr-mode) clause)
                  '(:expand ((bfr-semantic-depends-on k (bfr-binary-and x y)))
                    :use ((:instance bfr-semantic-depends-on-suff)
                          (:instance bfr-semantic-depends-on-suff (x y)))))
                 ((member-equal '(not (bfr-mode)) clause)
                  '(:in-theory (e/d (bfr-depends-on bfr-binary-and)))))))

  (defthm no-new-deps-of-bfr-or
    (implies (and (not (bfr-depends-on k x))
                  (not (bfr-depends-on k y)))
             (not (bfr-depends-on k (bfr-binary-or x y))))
    :hints(("goal" :in-theory (e/d (bfr-depends-on)))
           (cond ((member-equal '(bfr-mode) clause)
                  '(:expand ((bfr-semantic-depends-on k (bfr-binary-or x y)))
                    :use ((:instance bfr-semantic-depends-on-suff)
                          (:instance bfr-semantic-depends-on-suff (x y)))))
                 ((member-equal '(not (bfr-mode)) clause)
                  '(:in-theory (e/d (bfr-depends-on bfr-binary-or acl2::aig-or)))))))

  (defthm no-new-deps-of-bfr-xor
    (implies (and (not (bfr-depends-on k x))
                  (not (bfr-depends-on k y)))
             (not (bfr-depends-on k (bfr-xor x y))))
    :hints(("goal" :in-theory (e/d (bfr-depends-on)))
           (cond ((member-equal '(bfr-mode) clause)
                  '(:expand ((bfr-semantic-depends-on k (bfr-xor x y)))
                    :use ((:instance bfr-semantic-depends-on-suff)
                          (:instance bfr-semantic-depends-on-suff (x y)))))
                 ((member-equal '(not (bfr-mode)) clause)
                  '(:in-theory (e/d (bfr-depends-on bfr-xor acl2::aig-xor
                                                    acl2::aig-or)))))))

  (defthm no-new-deps-of-bfr-iff
    (implies (and (not (bfr-depends-on k x))
                  (not (bfr-depends-on k y)))
             (not (bfr-depends-on k (bfr-iff x y))))
    :hints(("goal" :in-theory (e/d (bfr-depends-on)))
           (cond ((member-equal '(bfr-mode) clause)
                  '(:expand ((bfr-semantic-depends-on k (bfr-iff x y)))
                    :use ((:instance bfr-semantic-depends-on-suff)
                          (:instance bfr-semantic-depends-on-suff (x y)))))
                 ((member-equal '(not (bfr-mode)) clause)
                  '(:in-theory (e/d (bfr-depends-on bfr-iff acl2::aig-iff
                                                    acl2::aig-or)))))))

  (defthm no-new-deps-of-bfr-ite
    (implies (and (not (bfr-depends-on k x))
                  (not (bfr-depends-on k y))
                  (not (bfr-depends-on k z)))
             (not (bfr-depends-on k (bfr-ite-fn x y z))))
    :hints(("goal" :in-theory (e/d (bfr-depends-on)))
           (cond ((member-equal '(bfr-mode) clause)
                  '(:expand ((bfr-semantic-depends-on k (bfr-ite-fn x y z)))
                    :use ((:instance bfr-semantic-depends-on-suff)
                          (:instance bfr-semantic-depends-on-suff (x y))
                          (:instance bfr-semantic-depends-on-suff (x z)))))
                 ((member-equal '(not (bfr-mode)) clause)
                  '(:in-theory (e/d (bfr-depends-on bfr-ite-fn acl2::aig-ite
                                                    acl2::aig-or)))))))

  (defthm no-deps-of-bfr-constants
    (and (not (bfr-depends-on k t))
         (not (bfr-depends-on k nil)))
    :hints (("goal" :expand ((bfr-depends-on k nil)
                             (bfr-depends-on k t)
                             (bfr-semantic-depends-on k t)
                             (bfr-semantic-depends-on k nil))))))


(defsection pbfr-semantic-depends-on

  (defun-sk pbfr-semantic-depends-on (k p x)
    (exists (env v)
            (and (bfr-eval p env)
                 (bfr-eval p (bfr-set-var k v env))
                 (not (equal (bfr-eval x (bfr-param-env p (bfr-set-var k v env)))
                             (bfr-eval x (bfr-param-env p env)))))))


  (defthm pbfr-semantic-depends-on-of-set-var
    (implies (and (not (pbfr-semantic-depends-on k p x))
                  (bfr-eval p env)
                  (bfr-eval p (bfr-set-var k v env)))
             (equal (bfr-eval x (bfr-param-env p (bfr-set-var k v env)))
                    (bfr-eval x (bfr-param-env p env)))))

  (in-theory (disable pbfr-semantic-depends-on
                      pbfr-semantic-depends-on-suff)))


(define pbfr-depends-on (k p x)
  :verify-guards nil
  (bfr-case :bdd (pbfr-semantic-depends-on k p x)
    :aig (bfr-depends-on k (bfr-from-param-space p x)))
  ///
  (in-theory (disable pbfr-depends-on))

  (defthm pbfr-eval-of-set-non-dep
    (implies (and (not (pbfr-depends-on k p x))
                  (bfr-eval p env)
                  (bfr-eval p (bfr-set-var k v env)))
             (equal (bfr-eval x (bfr-param-env p (bfr-set-var k v env)))
                    (bfr-eval x (bfr-param-env p env))))
    :hints (("goal" :in-theory (e/d (pbfr-depends-on)
                                    (bfr-eval-of-set-non-dep))
             :use ((:instance bfr-eval-of-set-non-dep
                    (x (bfr-from-param-space p x)))))))

  (local (defthm non-var-implies-not-member-extract-assigns
           (implies (not (set::in v (acl2::aig-vars x)))
                    (and (not (member v (mv-nth 0 (acl2::aig-extract-assigns x))))
                         (not (member v (mv-nth 1 (acl2::aig-extract-assigns x))))))))

  (local (defthm non-var-implies-not-in-aig-extract-assigns-alist
           (implies (not (set::in v (acl2::aig-vars x)))
                    (not (hons-assoc-equal v (acl2::aig-extract-assigns-alist x))))
           :hints(("Goal" :in-theory (enable acl2::aig-extract-assigns-alist)))))

  (local (defthm non-var-implies-non-var-in-restrict-with-assigns-alist
           (implies (not (set::in v (acl2::aig-vars x)))
                    (not (set::in v (acl2::aig-vars
                                     (acl2::aig-restrict
                                      x (acl2::aig-extract-assigns-alist y))))))
           :hints(("Goal" :in-theory (enable acl2::aig-restrict
                                             acl2::aig-extract-assigns-alist-lookup-boolean)))))

  (local (defthm non-var-implies-not-in-aig-extract-iterated-assigns-alist
           (implies (not (set::in v (acl2::aig-vars x)))
                    (not (hons-assoc-equal v (acl2::aig-extract-iterated-assigns-alist x clk))))
           :hints(("Goal" :in-theory (enable
                                      acl2::aig-extract-iterated-assigns-alist)))))

  (defthm non-var-implies-non-var-in-restrict-with-iterated-assigns-alist
    (implies (not (set::in v (acl2::aig-vars x)))
             (not (set::in v (acl2::aig-vars
                              (acl2::aig-restrict
                               x
                               (acl2::aig-extract-iterated-assigns-alist
                                y clk))))))
    :hints(("Goal" :in-theory (e/d (acl2::aig-restrict
                                    acl2::aig-extract-iterated-assigns-alist-lookup-boolean)
                                   (acl2::aig-extract-iterated-assigns-alist)))))

  (defthm pbfr-depends-on-of-bfr-var
    (implies (and (not (bfr-depends-on m p))
                  (bfr-eval p env))
             (equal (pbfr-depends-on m p (bfr-to-param-space p (bfr-var n)))
                    (equal (nfix m) (nfix n))))
    :hints(("Goal" :in-theory (e/d (pbfr-depends-on
                                    bfr-depends-on)
                                   (nfix))
            :do-not-induct t)
           (cond ((member-equal '(bfr-mode) clause)
                  (and stable-under-simplificationp
                       (if (eq (caar (last clause)) 'not)
                           `(:expand (,(cadar (last clause))))
                         '(:use ((:instance pbfr-semantic-depends-on-of-set-var
                                  (k m) (x (bfr-to-param-space p (bfr-var n)))
                                  (v (not (bfr-lookup n env)))))
                           :in-theory (disable pbfr-semantic-depends-on-of-set-var)))))
                 ((member-equal '(not (bfr-mode)) clause)
                  '(:in-theory (enable bfr-to-param-space
                                       bfr-from-param-space
                                       bfr-var
                                       acl2::aig-extract-iterated-assigns-alist-lookup-boolean)))))
    :otf-flg t)

  (defthm pbfr-depends-on-of-constants
    (and (not (pbfr-depends-on k p t))
         (not (pbfr-depends-on k p nil)))
    :hints (("goal" :in-theory (enable pbfr-depends-on
                                       bfr-from-param-space
                                       pbfr-semantic-depends-on))))

  (defthm no-new-deps-of-pbfr-not
    (implies (not (pbfr-depends-on k p x))
             (not (pbfr-depends-on k p (bfr-not x))))
    :hints(("Goal" :in-theory (enable pbfr-depends-on
                                      bfr-depends-on))
           (cond ((member-equal '(not (bfr-mode)) clause)
                  '(:in-theory (enable bfr-from-param-space bfr-not) ))
                 ((member-equal '(bfr-mode) clause)
                  '(:expand ((pbfr-semantic-depends-on k p (bfr-not x))))))))

  (defthm no-new-deps-of-pbfr-and
    (implies (and (not (pbfr-depends-on k p x))
                  (not (pbfr-depends-on k p y)))
             (not (pbfr-depends-on k p (bfr-binary-and x y))))
    :hints(("Goal" :in-theory (enable pbfr-depends-on
                                      bfr-depends-on))
           (cond ((member-equal '(not (bfr-mode)) clause)
                  '(:in-theory (enable bfr-from-param-space bfr-binary-and) ))
                 ((member-equal '(bfr-mode) clause)
                  '(:expand ((pbfr-semantic-depends-on k p (bfr-binary-and x y))))))))

  (defthm no-new-deps-of-pbfr-or
    (implies (and (not (pbfr-depends-on k p x))
                  (not (pbfr-depends-on k p y)))
             (not (pbfr-depends-on k p (bfr-binary-or x y))))
    :hints(("Goal" :in-theory (enable pbfr-depends-on
                                      bfr-depends-on))
           (cond ((member-equal '(not (bfr-mode)) clause)
                  '(:in-theory (enable bfr-from-param-space bfr-binary-or acl2::aig-or)))
                 ((member-equal '(bfr-mode) clause)
                  '(:expand ((pbfr-semantic-depends-on k p (bfr-binary-or x y))))))))

  (defthm no-new-deps-of-pbfr-xor
    (implies (and (not (pbfr-depends-on k p x))
                  (not (pbfr-depends-on k p y)))
             (not (pbfr-depends-on k p (bfr-xor x y))))
    :hints(("Goal" :in-theory (enable pbfr-depends-on
                                      bfr-depends-on))
           (cond ((member-equal '(not (bfr-mode)) clause)
                  '(:in-theory (enable bfr-from-param-space bfr-xor acl2::aig-xor
                                       acl2::aig-or)))
                 ((member-equal '(bfr-mode) clause)
                  '(:expand ((pbfr-semantic-depends-on k p (bfr-xor x y))))))))

  (defthm no-new-deps-of-pbfr-iff
    (implies (and (not (pbfr-depends-on k p x))
                  (not (pbfr-depends-on k p y)))
             (not (pbfr-depends-on k p (bfr-iff x y))))
    :hints(("Goal" :in-theory (enable pbfr-depends-on
                                      bfr-depends-on))
           (cond ((member-equal '(not (bfr-mode)) clause)
                  '(:in-theory (enable bfr-from-param-space bfr-iff acl2::aig-iff
                                       acl2::aig-or)))
                 ((member-equal '(bfr-mode) clause)
                  '(:expand ((pbfr-semantic-depends-on k p (bfr-iff x y))))))))

  (defthm no-new-deps-of-pbfr-nor
    (implies (and (not (pbfr-depends-on k p x))
                  (not (pbfr-depends-on k p y)))
             (not (pbfr-depends-on k p (bfr-nor x y))))
    :hints(("Goal" :in-theory (enable pbfr-depends-on
                                      bfr-depends-on))
           (cond ((member-equal '(not (bfr-mode)) clause)
                  '(:in-theory (enable bfr-from-param-space bfr-nor acl2::aig-or)))
                 ((member-equal '(bfr-mode) clause)
                  '(:expand ((pbfr-semantic-depends-on k p (bfr-nor x y))))))))

  (defthm no-new-deps-of-pbfr-nand
    (implies (and (not (pbfr-depends-on k p x))
                  (not (pbfr-depends-on k p y)))
             (not (pbfr-depends-on k p (bfr-nand x y))))
    :hints(("Goal" :in-theory (enable pbfr-depends-on
                                      bfr-depends-on))
           (cond ((member-equal '(not (bfr-mode)) clause)
                  '(:in-theory (enable bfr-from-param-space bfr-nand acl2::aig-or)))
                 ((member-equal '(bfr-mode) clause)
                  '(:expand ((pbfr-semantic-depends-on k p (bfr-nand x y))))))))

  (defthm no-new-deps-of-pbfr-andc1
    (implies (and (not (pbfr-depends-on k p x))
                  (not (pbfr-depends-on k p y)))
             (not (pbfr-depends-on k p (bfr-andc1 x y))))
    :hints(("Goal" :in-theory (enable pbfr-depends-on
                                      bfr-depends-on))
           (cond ((member-equal '(not (bfr-mode)) clause)
                  '(:in-theory (enable bfr-from-param-space bfr-andc1)))
                 ((member-equal '(bfr-mode) clause)
                  '(:expand ((pbfr-semantic-depends-on k p (bfr-andc1 x y))))))))

  (defthm no-new-deps-of-pbfr-andc2
    (implies (and (not (pbfr-depends-on k p x))
                  (not (pbfr-depends-on k p y)))
             (not (pbfr-depends-on k p (bfr-andc2 x y))))
    :hints(("Goal" :in-theory (enable pbfr-depends-on
                                      bfr-depends-on))
           (cond ((member-equal '(not (bfr-mode)) clause)
                  '(:in-theory (enable bfr-from-param-space bfr-andc2)))
                 ((member-equal '(bfr-mode) clause)
                  '(:expand ((pbfr-semantic-depends-on k p (bfr-andc2 x y))))))))

  (defthm no-new-deps-of-pbfr-ite
    (implies (and (not (pbfr-depends-on k p x))
                  (not (pbfr-depends-on k p y))
                  (not (pbfr-depends-on k p z)))
             (not (pbfr-depends-on k p (bfr-ite-fn x y z))))
    :hints(("Goal" :in-theory (enable pbfr-depends-on
                                      bfr-depends-on))
           (cond ((member-equal '(not (bfr-mode)) clause)
                  '(:in-theory (enable bfr-from-param-space bfr-ite-fn acl2::aig-ite
                                       acl2::aig-or)))
                 ((member-equal '(bfr-mode) clause)
                  '(:expand ((pbfr-semantic-depends-on k p (bfr-ite-fn x y z))))))))

  (defthm pbfr-depends-on-when-booleanp
    (implies (booleanp y)
             (not (pbfr-depends-on k p y)))
    :hints(("Goal" :in-theory (enable booleanp)))
    :rule-classes ((:rewrite :backchain-limit-lst 0))))
