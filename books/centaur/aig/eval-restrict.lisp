; Centaur AIG Library
; Copyright (C) 2008-2011 Centaur Technology
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
;
; July 2011, Jared added documentation, organized things into sections.


(in-package "ACL2")

(include-book "base")
(include-book "aig-equivs")
(include-book "three-four")
(include-book "aig-vars")

(in-theory (disable aig-env-lookup))
(in-theory (disable aig-restrict))
(in-theory (disable aig-partial-eval))
(in-theory (disable aig-compose))

(set-default-hints '('(:do-not-induct t)))


(defwitness alist-equiv-witnessing
  :predicate (not (alist-equiv al1 al2))
  :expr (not (let ((bg (alist-equiv-bad-guy al1 al2)))
               (equal (hons-assoc-equal bg al1)
                      (hons-assoc-equal bg al2))))
  :hints('(:use alist-equiv-when-agree-on-bad-guy
                 :in-theory nil))
  :generalize (((alist-equiv-bad-guy al1 al2) . aeqkey)))



(defexample aig-equiv-example
    :pattern (aig-eval x env)
    :templates (env)
    :instance-rulename aig-equiv-instancing)

(defexample aig-alist-equiv-aig-equiv-example
    :pattern (aig-equiv (cdr (hons-assoc-equal k x))
                        (cdr (hons-assoc-equal k y)))
    :templates (k)
    :instance-rulename aig-alist-equiv-instancing)

(defexample aig-alist-equiv-example
    :pattern (hons-assoc-equal k (aig-eval-alist x env))
    :templates (k)
    :instance-rulename aig-alist-equiv-instancing)

(defexample aig-alist-equiv-not-hons-assoc-equal-ex
    :pattern (not (hons-assoc-equal k x))
    :templates (k)
    :instance-rulename aig-alist-equiv-instancing)

(defexample aig-alist-equiv-restrict-example
  :pattern (hons-assoc-equal k (aig-restrict-alist x env))
  :templates (k)
  :instance-rulename aig-alist-equiv-instancing)

(defexample aig-alist-equiv-compose-example
  :pattern (hons-assoc-equal k (aig-compose-alist x env))
  :templates (k)
  :instance-rulename aig-alist-equiv-instancing)

(defexample aig-alist-equiv-partial-eval-example
  :pattern (hons-assoc-equal k (aig-partial-eval-alist x env))
  :templates (k)
  :instance-rulename aig-alist-equiv-instancing)



(defcong aig-alist-equiv iff (hons-assoc-equal x al) 2
  :hints((witness)))



(defsection aig-eval-thms
  :extension aig-eval

  (local (in-theory (enable aig-eval)))

  (defcong aig-equiv equal (aig-eval x env) 1
    :hints((witness)))

  (defcong aig-env-equiv iff (aig-env-lookup key al) 2
    :hints(("Goal" :use ((:instance aig-env-equiv-necc
                                     (x al) (y al-equiv))))))

  (defcong aig-env-equiv equal (aig-eval x env) 2
    :hints(("Goal" :induct t)))

  (defthm aig-eval-append-when-not-intersecting-alist-keys
    (implies (not (intersectp-equal (alist-keys env) (aig-vars x)))
             (equal (aig-eval x (append env rest))
                    (aig-eval x rest)))
    :hints(("Goal"
            :induct t
            :in-theory (enable aig-env-lookup)))))




(defsection aig-eval-alist-thms
  :extension aig-eval-alist

  (defcong aig-alist-equiv alist-equiv (aig-eval-alist x env) 1
    :hints((witness)))

  (defcong aig-env-equiv equal (aig-eval-alist x env) 2
    :hints(("Goal" :induct t)))

  (defcong aig-alist-equiv aig-alist-equiv (append a b) 1
    :hints((witness)))

  (defcong aig-alist-equiv aig-alist-equiv (append a b) 2
    :hints((witness)))

  (defthm aig-eval-alist-append
    (equal (aig-eval-alist (append a b) env)
           (append (aig-eval-alist a env)
                   (aig-eval-alist b env)))
    :hints(("Goal" :induct t)))

  (defthm alist-keys-aig-eval-alist
    (equal (alist-keys (aig-eval-alist a b))
           (alist-keys a))
    :hints(("Goal" :induct t))))




(defsection aig-restrict-thms
  :extension aig-restrict

  (local (in-theory (enable aig-restrict)))

  (defcong aig-equiv aig-equiv (aig-restrict x al) 1
    :hints((witness :ruleset aig-equiv-witnessing)))

  (defcong aig-alist-equiv aig-equiv (aig-restrict x al) 2
    :hints((witness :ruleset aig-equiv-witnessing)))

  (defcong alist-equiv equal (aig-restrict x env) 2
    :hints(("Goal" :induct t))))



(defsection aig-restrict-alist-thms
  :extension aig-restrict-alist

  (local (in-theory (enable aig-restrict-alist)))

  (defthm lookup-in-aig-restrict-alist
    (equal (hons-assoc-equal k (aig-restrict-alist x env))
           (and (hons-assoc-equal k x)
                (cons k (aig-restrict (cdr (hons-assoc-equal k x))
                                      env))))
    :hints(("Goal" :induct t)))

  (defcong aig-alist-equiv aig-alist-equiv (aig-restrict-alist x al) 1
    :hints((witness)))

  (defcong aig-alist-equiv aig-alist-equiv (aig-restrict-alist x al) 2
    :hints((witness :ruleset aig-alist-equiv-witnessing)))

  (defthm aig-eval-alist-of-aig-restrict-alist
    (equal (aig-eval-alist (aig-restrict-alist x al1) al2)
           (aig-eval-alist x (append (aig-eval-alist al1 al2) al2)))
    :hints(("Goal" :induct t)))

  ;; No alist-keys thm?
  )



(defsection aig-restrict-aig-restrict
  :extension aig-restrict

  ;; This belongs in aig-restrict-thms, but needs our aig-restrict-alist
  ;; reasoning to work.

  (defthm aig-restrict-aig-restrict
    (aig-equiv (aig-restrict (aig-restrict x al1) al2)
               (aig-restrict x (append (aig-restrict-alist al1 al2) al2)))
    :hints((witness))))


(defsection aig-restrict-alist-aig-restrict-alist
  :extension aig-restrict-alist

  ;; Similarly we need aig-restrict-aig-restrict to prove this.

  (defthm aig-restrict-alist-aig-restrict-alist
    (aig-alist-equiv (aig-restrict-alist (aig-restrict-alist x al1) al2)
                     (aig-restrict-alist x (append (aig-restrict-alist al1 al2) al2)))
    :hints((witness))))




(defsection aig-partial-eval-thms
  :extension aig-partial-eval

  (local (in-theory (enable aig-partial-eval)))

  (defthm aig-eval-of-aig-partial-eval
    (equal (aig-eval (aig-partial-eval x al1) al2)
           (aig-eval x (append al1 al2)))
    :hints(("Goal"
             :induct t
             :in-theory (enable aig-env-lookup))))

  (defcong aig-equiv aig-equiv (aig-partial-eval x al) 1
    :hints((witness :ruleset aig-equiv-witnessing)))

  (defthm aig-partial-eval-aig-partial-eval
    (aig-equiv (aig-partial-eval (aig-partial-eval x al1) al2)
               (aig-partial-eval x (append al1 al2)))
    :hints((witness)))

  (defcong alist-equiv equal (aig-partial-eval x env) 2
    :hints(("Goal" :induct t))))



(defsection aig-partial-eval-alist-thms
  :extension aig-partial-eval-alist

  (local (in-theory (enable aig-partial-eval-alist)))

  (defthm lookup-in-aig-partial-eval-alist
    (equal (hons-assoc-equal k (aig-partial-eval-alist x env))
           (and (hons-assoc-equal k x)
                (cons k (aig-partial-eval (cdr (hons-assoc-equal k x))
                                          env))))
    :hints(("Goal" :induct t)))

  (defcong aig-alist-equiv aig-alist-equiv (aig-partial-eval-alist x al) 1
    :hints((witness)))

  ;; BOZO maybe want some kind of env-equiv congruence too

  (defthm aig-eval-alist-of-aig-partial-eval-alist
    (equal (aig-eval-alist (aig-partial-eval-alist x al1) al2)
           (aig-eval-alist x (append al1 al2)))
    :hints(("Goal" :induct t)))

  (defthm aig-partial-eval-alist-aig-partial-eval-alist
    (aig-alist-equiv (aig-partial-eval-alist (aig-partial-eval-alist x al1) al2)
                     (aig-partial-eval-alist x (append al1 al2)))
    :hints((witness)))

  ;; No alist-keys thm?
  )



(defsection aig-compose-thms
  :extension aig-compose

  (local (in-theory (enable aig-compose)))

  (defthm aig-eval-of-aig-compose
    (equal (aig-eval (aig-compose x al1) al2)
           (aig-eval x (aig-eval-alist al1 al2)))
    :hints(("Goal"
            :induct t
            :in-theory (enable aig-env-lookup))))

  (defcong aig-equiv aig-equiv (aig-compose x al) 1
    :hints((witness :ruleset aig-equiv-witnessing)))

  (defcong aig-alist-equiv aig-equiv (aig-compose x al) 2
    :hints((witness :ruleset aig-equiv-witnessing)))

  (defcong alist-equiv equal (aig-compose x env) 2
    :hints(("Goal"
             :induct t
             :in-theory (enable aig-env-lookup)))))




(defsection aig-compose-alist-thms
  :extension aig-compose-alist

  (local (in-theory (enable aig-compose-alist)))

  (defthm lookup-in-aig-compose-alist
    (equal (hons-assoc-equal k (aig-compose-alist x env))
           (and (hons-assoc-equal k x)
                (cons k (aig-compose (cdr (hons-assoc-equal k x))
                                     env))))
    :hints(("Goal" :induct t)))

  (defcong aig-alist-equiv aig-alist-equiv (aig-compose-alist x al) 1
    :hints((witness)))

  (defcong aig-alist-equiv aig-alist-equiv (aig-compose-alist x al) 2
    :hints((witness :ruleset aig-alist-equiv-witnessing)))

  (defthm aig-eval-alist-of-aig-compose-alist
    (equal (aig-eval-alist (aig-compose-alist x al1) al2)
           (aig-eval-alist x (aig-eval-alist al1 al2)))
    :hints(("Goal" :induct t)))

  ;; No alist-keys thm?
  )


;; BOZO should probably also disable FAIG-FIX
(in-theory (disable faig-eval))
(in-theory (disable faig-restrict))
(in-theory (disable faig-partial-eval))
(in-theory (disable faig-compose))


(defexample faig-equiv-aig-eval-ex
  :pattern (aig-eval x env)
  :templates (env)
  :instance-rulename faig-equiv-instancing)

(defexample faig-equiv-example
  :pattern (faig-eval x env)
  :templates (env)
  :instance-rulename faig-equiv-instancing)

(defexample faig-alist-equiv-example
  :pattern (hons-assoc-equal k (faig-eval-alist x env))
  :templates (k)
  :instance-rulename faig-alist-equiv-instancing)

(defexample faig-alist-equiv-faig-equiv-example
  :pattern (faig-equiv (cdr (hons-assoc-equal k x))
                       (cdr (hons-assoc-equal k y)))
  :templates (k)
  :instance-rulename faig-alist-equiv-instancing)

(defexample faig-alist-equiv-not-hons-assoc-equal-ex
  :pattern (not (hons-assoc-equal k x))
  :templates (k)
  :instance-rulename faig-alist-equiv-instancing)

(defexample faig-alist-equiv-restrict-example
  :pattern (hons-assoc-equal k (faig-restrict-alist x env))
  :templates (k)
  :instance-rulename faig-alist-equiv-instancing)

(defexample faig-alist-equiv-compose-example
  :pattern (hons-assoc-equal k (faig-compose-alist x env))
  :templates (k)
  :instance-rulename faig-alist-equiv-instancing)

(defexample faig-alist-equiv-partial-eval-example
  :pattern (hons-assoc-equal k (faig-partial-eval-alist x env))
  :templates (k)
  :instance-rulename faig-alist-equiv-instancing)




(defsection faig-eval-thms
  :extension faig-eval

  (defcong aig-env-equiv equal (faig-eval x env) 2
    :hints(("Goal" :in-theory (enable faig-eval))))

  (defcong faig-equiv equal (faig-eval x env) 1
    :hints((witness)))

  (defthm faig-eval-append-when-not-intersecting-alist-keys
    (implies (not (intersectp-equal (alist-keys env) (aig-vars x)))
             (equal (faig-eval x (append env rest))
                    (faig-eval x rest)))
    :hints(("Goal"
            :in-theory (e/d (faig-eval) (aig-eval))))))



(defsection faig-equiv-thms
  :extension faig-equiv

  (local (in-theory (enable faig-eval)))

  (defcong aig-equiv faig-equiv (cons a b) 1
    :hints((witness)))

  (defcong aig-equiv faig-equiv (cons a b) 2
    :hints((witness))))



(defsection faig-alist-equiv-thms
  :extension faig-alist-equiv

  (defcong faig-alist-equiv iff (hons-assoc-equal x al) 2
    :hints((witness)))

  (defcong faig-alist-equiv faig-alist-equiv (append a b) 1
    :hints((witness)))

  (defcong faig-alist-equiv faig-alist-equiv (append a b) 2
    :hints((witness))))



(defsection faig-eval-alist-thms
  :extension faig-eval-alist

  (defthm faig-eval-alist-append
    (equal (faig-eval-alist (append a b) env)
           (append (faig-eval-alist a env)
                   (faig-eval-alist b env)))
    :hints(("Goal" :induct t)))

  (defcong aig-env-equiv equal (faig-eval-alist x env) 2
    :hints(("Goal" :induct t)))

  (defthm lookup-in-faig-eval-alist
    (equal (hons-assoc-equal k (faig-eval-alist x env))
           (and (hons-assoc-equal k x)
                (cons k (faig-eval (cdr (hons-assoc-equal k x)) env))))
    :hints(("Goal" :induct t)))

  (defcong faig-alist-equiv alist-equiv (faig-eval-alist x env) 1
    :hints((witness)))

  (defthm alist-keys-faig-eval-alist
    (equal (alist-keys (faig-eval-alist al env))
           (alist-keys al))
    :hints(("Goal" :induct t))))



(defsection faig-restrict-thms
  :extension faig-restrict

  (local (in-theory (enable faig-restrict)))

  (defthm faig-eval-of-faig-restrict
    (equal (faig-eval (faig-restrict x al1) al2)
           (faig-eval x (append (aig-eval-alist al1 al2) al2)))
    :hints(("Goal" :in-theory (enable faig-eval))))

  (defcong aig-alist-equiv faig-equiv (faig-restrict x al) 2
    :hints((witness :ruleset faig-equiv-witnessing)))

  (defcong alist-equiv equal (faig-restrict x env) 2
    :hints(("Goal" :in-theory (enable faig-restrict))))

  (local (in-theory (disable faig-restrict)))

  (defcong faig-equiv faig-equiv (faig-restrict x al) 1
    :hints((witness :ruleset faig-equiv-witnessing)))

  (defthm faig-restrict-faig-restrict
    (faig-equiv (faig-restrict (faig-restrict x al1) al2)
                (faig-restrict x (append (aig-restrict-alist al1 al2) al2)))
    :hints((witness))))



(defsection faig-restrict-alist-thms
  :extension faig-restrict-alist

  (defcong alist-equiv equal (faig-restrict-alist x env) 2
    :hints(("Goal" :induct t)))

  (defthm lookup-in-faig-restrict-alist
    (equal (hons-assoc-equal k (faig-restrict-alist x env))
           (and (hons-assoc-equal k x)
                (cons k (faig-restrict (cdr (hons-assoc-equal k x))
                                       env))))
    :hints(("Goal" :induct t)))

  (defcong faig-alist-equiv faig-alist-equiv (faig-restrict-alist x al) 1
    :hints((witness)))

  (defthm faig-eval-alist-of-faig-restrict-alist
    (equal (faig-eval-alist (faig-restrict-alist x al1) al2)
           (faig-eval-alist x (append (aig-eval-alist al1 al2) al2)))
    :hints(("Goal" :induct t)))

  (defcong aig-alist-equiv faig-alist-equiv (faig-restrict-alist x al) 2
    :hints((witness :ruleset faig-alist-equiv-witnessing)))

  (defthm faig-restrict-alist-faig-restrict-alist
    (faig-alist-equiv (faig-restrict-alist (faig-restrict-alist x al1) al2)
                      (faig-restrict-alist x (append (aig-restrict-alist al1 al2) al2)))
    :hints((witness)))

  (defthm alist-keys-faig-restrict-alist
    (equal (alist-keys (faig-restrict-alist al env))
           (alist-keys al))
    :hints(("Goal" :induct t))))



(defsection faig-partial-eval-thms
  :extension faig-partial-eval

  (local (in-theory (enable faig-partial-eval)))

  (defthm faig-eval-of-faig-partial-eval
    (equal (faig-eval (faig-partial-eval x al1) al2)
           (faig-eval x (append al1 al2)))
    :hints(("Goal" :in-theory (enable faig-eval))))

  (defcong alist-equiv equal (faig-partial-eval x env) 2)

  (local (in-theory (disable faig-partial-eval)))

  (defcong faig-equiv faig-equiv (faig-partial-eval x al) 1
    :hints((witness :ruleset faig-equiv-witnessing)))

  (defthm faig-partial-eval-faig-partial-eval
    (faig-equiv (faig-partial-eval (faig-partial-eval x al1) al2)
                (faig-partial-eval x (append al1 al2)))
    :hints((witness))))



(defsection faig-partial-eval-alist-thms
  :extension faig-partial-eval-alist

  (defthm faig-eval-alist-of-faig-partial-eval-alist
    (equal (faig-eval-alist (faig-partial-eval-alist x al1) al2)
           (faig-eval-alist x (append al1 al2)))
    :hints(("Goal" :induct t)))

  (defthm lookup-in-faig-partial-eval-alist
    (equal (hons-assoc-equal k (faig-partial-eval-alist x env))
           (and (hons-assoc-equal k x)
                (cons k (faig-partial-eval (cdr (hons-assoc-equal k x))
                                           env))))
    :hints(("Goal" :induct t)))

  (defcong faig-alist-equiv faig-alist-equiv (faig-partial-eval-alist x al) 1
    :hints((witness)))

  (defcong alist-equiv equal (faig-partial-eval-alist x env) 2
    :hints(("Goal" :induct t)))

  (defthm faig-partial-eval-alist-faig-partial-eval-alist
    (faig-alist-equiv (faig-partial-eval-alist (faig-partial-eval-alist x al1) al2)
                      (faig-partial-eval-alist x (append al1 al2)))
    :hints((witness)))

  (defthm alist-keys-faig-partial-eval-alist
    (equal (alist-keys (faig-partial-eval-alist al env))
           (alist-keys al))
    :hints(("Goal" :induct t))))




(defsection faig-compose-thms
  :extension faig-compose

  (local (in-theory (enable faig-compose)))

  (defthm faig-eval-of-faig-compose
    (equal (faig-eval (faig-compose x al1) al2)
           (faig-eval x (aig-eval-alist al1 al2)))
    :hints(("Goal" :in-theory (enable faig-eval))))

  (local (in-theory (disable faig-compose)))

  (defcong faig-equiv faig-equiv (faig-compose x al) 1
    :hints((witness :ruleset faig-equiv-witnessing)))

  (defcong aig-alist-equiv faig-equiv (faig-compose x al) 2
    :hints((witness :ruleset faig-equiv-witnessing)))

  (defcong alist-equiv equal (faig-compose x env) 2
    :hints(("Goal" :in-theory (enable faig-compose)))))




(defsection faig-compose-alist-thms
  :extension faig-compose-alist

  (defthm faig-eval-alist-of-faig-compose-alist
    (equal (faig-eval-alist (faig-compose-alist x al1) al2)
           (faig-eval-alist x (aig-eval-alist al1 al2)))
    :hints(("Goal" :induct t)))

  (defthm lookup-in-faig-compose-alist
    (equal (hons-assoc-equal k (faig-compose-alist x env))
           (and (hons-assoc-equal k x)
                (cons k (faig-compose (cdr (hons-assoc-equal k x))
                                      env))))
    :hints(("Goal" :induct t)))

  (defcong faig-alist-equiv faig-alist-equiv (faig-compose-alist x al) 1
    :hints((witness)))

  (defcong aig-alist-equiv faig-alist-equiv (faig-compose-alist x al) 2
    :hints((witness :ruleset faig-alist-equiv-witnessing)))

  (defcong alist-equiv equal (faig-compose-alist x env) 2
    :hints(("Goal" :induct t))))




(defsection faig-fix-equiv
  :parents (faig)
  :short "We say the objects @('X') and @('Y') are equivalent if they are (1)
@(see faig-equiv), and (2) both atoms or both conses."

  :long "<p>This might seem kind of strange at first, but it has some nice
congruence properties that aren't true of ordinary @(see faig-equiv).</p>

<p>In particular, FAIG operations like @(see faig-eval) and @(see
faig-restrict) generally treat any malformed FAIGs (i.e., atoms) as \"X\", that
is, @('(t . t)').  This is nice because in some sense it is conservative with
respect to our ordinary interpretation of FAIGs.</p>

<p>Unfortunately, this means that @('faig-equiv') is <b>not</b> sufficient to
imply that the car/cdr are @(see aig-equiv).  For instance, let @('x') be 5 and
let @('y') be @('(t . t)').  Then, @('x') and @('y') are @('faig-equiv'), but
their cars are not @('aig-equiv') because the car of @('x') is @('nil'),
constant false, whereas the car of @('y') is @('t'), constant true.</p>

<p>So, @(call faig-fix-equiv) corrects for this by insisting that @('x') and
@('y') are either both atoms or both conses.  This way, the car/cdr of
@('faig-fix-equiv') objects are always @(see aig-equiv).</p>"

  (def-universal-equiv faig-fix-equiv
    :equiv-terms ((iff (consp x))
                  (faig-equiv x)))

  (defrefinement faig-fix-equiv faig-equiv
    :hints(("Goal" :in-theory (enable faig-fix-equiv))))

  (defcong faig-equiv faig-fix-equiv (faig-fix x) 1
    :hints(("Goal" :in-theory (enable faig-fix faig-fix-equiv
                                      faig-eval))
           (witness :ruleset (faig-equiv-witnessing
                              faig-equiv-instancing
                              faig-equiv-example)))
    :otf-flg t)

  (defcong faig-fix-equiv aig-equiv (car x) 1
    :hints(("Goal" :in-theory (enable faig-eval faig-fix-equiv))
           (witness :ruleset (aig-equiv-witnessing
                              faig-equiv-instancing
                              faig-equiv-aig-eval-ex))))

  (defcong faig-fix-equiv aig-equiv (cdr x) 1
    :hints(("Goal" :in-theory (enable faig-eval faig-fix-equiv))
           (witness :ruleset (aig-equiv-witnessing
                              faig-equiv-instancing
                              faig-equiv-aig-eval-ex)))))




(defsection faig-fix-thms
  :extension faig-fix

  (defthm faig-eval-faig-fix
    (equal (faig-eval (faig-fix x) env)
           (faig-eval x env))
    :hints(("Goal" :in-theory (enable faig-eval faig-fix))))

  (defthm faig-restrict-faig-fix
    (equal (faig-restrict (faig-fix x) al)
           (faig-restrict x al))
    :hints(("Goal" :in-theory (e/d (faig-restrict aig-restrict)))))

  (defthm faig-partial-eval-faig-fix
    (equal (faig-partial-eval (faig-fix x) al)
           (faig-partial-eval x al))
    :hints(("Goal" :in-theory (e/d (faig-partial-eval aig-partial-eval)))))

  ;; BOZO faig-compose?
  )


(defsection faig-fix-alist-thms
  :extension faig-fix-alist

  (defthm hons-assoc-equal-faig-fix-alist
    (equal (hons-assoc-equal x (faig-fix-alist a))
           (and (hons-assoc-equal x a)
                (cons x (faig-fix (cdr (hons-assoc-equal x a))))))
    :hints(("Goal" :induct t)))

  (defthm faig-restrict-alist-faig-fix-alist
    (equal (faig-restrict-alist (faig-fix-alist a) env)
           (faig-restrict-alist a env))
    :hints(("Goal"
            :induct t
            :in-theory (disable faig-fix))))

  (defthm faig-partial-eval-alist-faig-fix-alist
    (equal (faig-partial-eval-alist (faig-fix-alist a) env)
           (faig-partial-eval-alist a env))
    :hints(("Goal"
            :induct t
            :in-theory (disable faig-fix)))))







(defmacro prove-faig-congruence (f args n)
  (let* ((arg (nth (1- n) args))
         (arg-equiv (intern-in-package-of-symbol
                     (concatenate 'string (symbol-name arg) "-EQUIV")
                     arg))
         (args-equiv (update-nth (1- n) arg-equiv args)))
    `(defsection nil
       :extension ,f
       (defcong faig-equiv faig-equiv (,f . ,args) ,n
         :hints(("Goal" :in-theory (disable ,f)
                 :expand ((faig-equiv (,f . ,args)
                                      (,f . ,args-equiv)))
                 :use ((:instance faig-equiv-necc
                                  (x ,arg) (y ,arg-equiv)
                                  (env (faig-equiv-witness
                                     (,f . ,args)
                                     (,f . ,args-equiv)))))))))))

(defun prove-faig-congruences-fn (n f args)
  (if (zp n)
      nil
    (cons `(prove-faig-congruence ,f ,args ,n)
          (prove-faig-congruences-fn (1- n) f args))))

(defmacro prove-faig-congruences (f args)
  `(progn . ,(prove-faig-congruences-fn (len args) f args)))

(prove-faig-congruences t-aig-fix (a))
(prove-faig-congruences t-aig-not (a))
(prove-faig-congruences f-aig-not (a))
(prove-faig-congruences t-aig-and (a b))
(prove-faig-congruences f-aig-and (a b))
(prove-faig-congruences t-aig-or  (a b))
(prove-faig-congruences f-aig-or  (a b))
(prove-faig-congruences t-aig-xor (a b))
(prove-faig-congruences f-aig-xor (a b))
(prove-faig-congruences t-aig-iff (a b))
(prove-faig-congruences f-aig-iff (a b))
(prove-faig-congruences t-aig-ite (c a b))
(prove-faig-congruences f-aig-ite (c a b))
(prove-faig-congruences t-aig-ite* (c a b))
(prove-faig-congruences f-aig-ite* (c a b))
(prove-faig-congruences t-aig-buf (c a))
(prove-faig-congruences f-aig-pullup (a))
(prove-faig-congruences f-aig-bi-buf (c a b))




;; Pat stuff, could maybe move to EMOD/ESIM books...

(defthm faig-eval-pat-of-faig-restrict-pat
  (equal (faig-eval-pat pat (faig-restrict-pat pat aigs al1) al2)
         (faig-eval-pat pat aigs (append (aig-eval-alist al1 al2) al2)))
  :hints(("Goal" :induct t)))

(defthm faig-eval-pat-of-faig-partial-eval-pat
  (equal (faig-eval-pat pat (faig-partial-eval-pat pat aigs al1) al2)
         (faig-eval-pat pat aigs (append al1 al2)))
  :hints(("Goal" :induct t)))

(defthm faig-eval-pat-of-faig-compose-pat
  (equal (faig-eval-pat pat (faig-compose-pat pat aigs al1) al2)
         (faig-eval-pat pat aigs (aig-eval-alist al1 al2)))
  :hints(("Goal" :induct t)))

(defcong aig-env-equiv equal (faig-eval-pat pat x env) 3
  :hints(("Goal" :induct t)))
