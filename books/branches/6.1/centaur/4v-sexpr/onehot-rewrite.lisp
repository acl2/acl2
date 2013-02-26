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
; Original author: Jared Davis <jared@centtech.com>

; onehot-rewrite.lisp
;   - onehot rewriting for s-expressions

(in-package "ACL2")
(include-book "sexpr-rewrites")
(include-book "sexpr-building")
(include-book "cutil/defprojection" :dir :system)
(local (include-book "centaur/misc/filter-alist" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(set-inhibit-warnings "theory" "non-rec")


(defxdoc onehot-rewriting
  :parents (sexpr-rewriting)
  :short "Conservatively rewrite @(see 4v-sexprs) by assuming some variables
are one-hot."

  :long "<h3>Introduction</h3>

<p>Sometimes you know that certain inputs to a module are supposed to be
one-hot.  Using this information, it may be possible to simplify the sexprs
produced during @(see esim) runs.  For example, if we know that the variables
@('A1') and @('A2') are one-hot, we might like to rewrite a sexpr like:</p>

@({
 (ITE A1 (AND A2 FOO) BAR)
})

<p>Here, we can \"see\" that @('A2') has to be false in the true-branch since
to get there we must have that @('A1') is true.  Accordingly, we would like to
replace the sexpr with something like:</p>

@({
 (AND (NOT A1) BAR)
})

<p>This sort of rewriting may occasionally help to avoid combinational loops
that are only broken when the inputs are truly one-hot, e.g., notice how the
variable @('FOO') has dropped out of the expression above.</p>


<h3>The Basic Transformation</h3>

<p>Our main function for onehot rewriting is @(see 4v-onehot-rw-sexpr).  Given
a list of variables @('A1...AN') that we think are one-hot, and an s-expression
@('SEXPR') to rewrite, it basically constructs:</p>

@({
 (ITE* ONEHOT-P SEXPR' (X))
})

<p>Where:</p>

<ul> <li>@('ONEHOT-P') is constructed by @(see 4vs-onehot) and evaluates to
@('T') when the @('A1...N') are one-hot, and</li> <li>@('SEXPR'') is formed
from @('SEXPR') by assuming @('A1...N') are indeed one-hot; see @(see
4v-onehot-sexpr-prime) for details.</li> </ul>

<p>We prove this conservatively approximates @('SEXPR'), but keep in mind that
this approximation is <b>not an equivalent</b> term!  For instance, the
rewritten expression will always produce @('X') if it turns out that the inputs
were not really one-hot.  Accordingly, you should only use this rewrite when
you are really are certain the variables will be one-hot.</p>


<h3>The Alist Transformation</h3>

<p>Our main use for onehot rewriting is in simplifiers for @(see
esim-simplify-update-fns), where the goal is to rewrite a whole alist binding
names to sexprs.</p>

<p>Our main function for this is @(see 4v-onehot-rw-sexpr-alist), which
takes the list of one-hot variables and the alist to rewrite as arguments.
This function is reasonably clever: it avoids changing sexprs that don't
mention any of the onehot variables, and it has some other performance
optimizations that are geared toward reusing memoized results across
sexprs.</p>")

(local (in-theory (enable 4v-<=-trans1 4v-<=-trans2)))
(local (in-theory (disable member-equal-of-alist-vals-under-iff))) ;; bad rule

(local (defthm equal-of-booleans-rewrite
         (implies (and (booleanp a)
                       (booleanp b))
                  (equal (equal a b)
                         (iff a b)))
         :rule-classes ((:rewrite :backchain-limit-lst 1))))

(local (defthm equal-of-cons-rewrite
         (equal (equal x (cons a b))
                (and (consp x)
                     (equal (car x) a)
                     (equal (cdr x) b)))))


(local
 (defsection bozo-misplaced-lemmas

   ;; BOZO find most of this stuff a proper home.

   (defthm equal-len-zero
     (equal (equal (len x) 0)
            (atom x)))

   (defthm atom-when-member-of-atom-list
     (implies (and (atom-listp x)
                   (member-equal a x))
              (not (consp a)))
     :rule-classes ((:rewrite)
                    (:rewrite :corollary
                              (implies (and (member-equal a x)
                                            (atom-listp x))
                                       (not (consp a))))))

   (defthm member-equal-of-list-fix
     (equal (member-equal a (list-fix x))
            (list-fix (member-equal a x))))

   (defthm list-fix-under-set-equiv
     (set-equiv (list-fix x)
                 x)
     :hints((witness)))

   (defthm car-of-repeat
     (equal (car (repeat a n))
            (if (zp n)
                nil
              a))
     :hints(("Goal" :in-theory (enable repeat))))

   (defthm cdr-of-repeat
     (equal (cdr (repeat a n))
            (repeat a (- n 1)))
     :hints(("Goal" :in-theory (enable repeat))))

   (defthm consp-of-repeat
     (equal (consp (repeat a n))
            (posp n))
     :hints(("Goal" :in-theory (enable repeat))))

   (defthm hons-assoc-equal-of-atom
     (implies (atom alist)
              (equal (hons-assoc-equal a alist)
                     nil)))

   (defthm hons-assoc-equal-of-proper-cons
     (equal (hons-assoc-equal a (cons (cons b val) alist))
            (if (equal a b)
                (cons b val)
              (hons-assoc-equal a alist))))

   (in-theory (disable hons-assoc-equal))

   (defthm consp-of-4v-sexpr-restrict-with-rw-list
     (equal (consp (4v-sexpr-restrict-with-rw-list x alist))
            (consp x))
     :hints(("Goal"
             :in-theory (enable 4v-sexpr-restrict-with-rw-list)
             :induct (len x))))

   (defthm car-of-4v-sexpr-restrict-with-rw-list
     (equal (car (4v-sexpr-restrict-with-rw-list x alist))
            (4v-sexpr-restrict-with-rw (car x) alist)))

   (defthm cdr-of-4v-sexpr-restrict-with-rw-list
     (equal (cdr (4v-sexpr-restrict-with-rw-list x alist))
            (4v-sexpr-restrict-with-rw-list (cdr x) alist)))

   (defthm len-of-4v-sexpr-restrict-with-rw-list
     (equal (len (4v-sexpr-restrict-with-rw-list x alist))
            (len x)))

   (defthm consp-of-member-equal
     (equal (consp (member-equal a x))
            (if (member-equal a x)
                t
              nil)))

   (defthm 4v-sexpr-vars-list-when-atom
     (implies (atom x)
              (equal (4v-sexpr-vars-list x)
                     nil)))

   (defthm 4v-sexpr-vars-list-of-cons
     (equal (4v-sexpr-vars-list (cons a x))
            (hons-alphorder-merge (4v-sexpr-vars a)
                                  (4v-sexpr-vars-list x))))

   (defthm-4v-sexpr-flag
     (defthm 4v-sexpr-vars-nonnil
       (not (member-equal nil (4v-sexpr-vars x)))
       :flag sexpr)
     (defthm 4v-sexpr-vars-list-nonnil
       (not (member-equal nil (4v-sexpr-vars-list x)))
       :flag sexpr-list))

   (defsection no-duplicatesp-equal-of-alist-keys-of-hons-shrink-alist

     ;; BOZO this is a nice theorem, it would be nice to give it a better home.

     (local (defthm l0
              (implies (hons-assoc-equal key ans)
                       (equal (duplicity key (alist-keys (hons-shrink-alist alist ans)))
                              (duplicity key (alist-keys ans))))
              :hints(("Goal" :induct (hons-shrink-alist alist ans)))))

     (local (defthm l1
              (implies (and (not (hons-assoc-equal key ans))
                            (hons-assoc-equal key alist))
                       (equal (duplicity key (alist-keys (hons-shrink-alist alist ans)))
                              1))
              :hints(("Goal"
                      :in-theory (enable hons-assoc-equal)
                      :induct (hons-shrink-alist alist ans)))))

     (local (defthm l2
              (equal (duplicity key (alist-keys (hons-shrink-alist alist ans)))
                     (if (hons-assoc-equal key ans)
                         (duplicity key (alist-keys ans))
                       (if (hons-assoc-equal key alist)
                           1
                         0)))
              :hints(("Goal" :in-theory (enable hons-shrink-alist)))))

     (local (in-theory (disable hons-shrink-alist
                                hons-assoc-equal
                                alist-keys)))

     (local (defthm l3
              (not (duplicity-badguy1 dom (alist-keys (hons-shrink-alist alist nil))))
              :hints(("Goal" :in-theory (enable duplicity-badguy1)))))

     (local (defthm l4
              (not (duplicity-badguy (alist-keys (hons-shrink-alist alist nil))))
              :hints(("Goal"
                      :in-theory (e/d (duplicity-badguy)
                                      (duplicity-badguy-under-iff))))))

     (defthm no-duplicatsep-equal-of-alist-keys-of-hons-shrink-alist
       (no-duplicatesp-equal (alist-keys (hons-shrink-alist alist nil)))
       :hints(("Goal"
               :use ((:instance duplicity-badguy-under-iff
                                (x (alist-keys (hons-shrink-alist alist nil)))))))))


   (encapsulate
     ()
     (local (defthm l0
              (implies (and (member-equal a x)
                            (member-equal k (4v-sexpr-vars a)))
                       (member-equal k (4v-sexpr-vars-list x)))))

     (defthm member-of-4v-sexpr-vars-list-when-subsetp
       (implies (and (subsetp-equal a b)
                     (member-equal k (4v-sexpr-vars-list a)))
                (member-equal k (4v-sexpr-vars-list b)))
       :hints(("Goal"
               :induct (len a)
               :do-not '(generalize fertilize)
               :do-not-induct t))))

   (defthm subsetp-of-4v-sexpr-vars-list-when-subsetp
     (implies (subsetp-equal (double-rewrite a) (double-rewrite b))
              (subsetp-equal (4v-sexpr-vars-list a)
                             (4v-sexpr-vars-list b)))
     :hints((witness :ruleset subsetp-witnessing)))

   (defcong set-equiv set-equiv (4v-sexpr-vars-list x) 1
     :hints(("Goal" :in-theory (enable set-equiv))))


   (defthm 4v-sexpr-vars-list-of-append
     (set-equiv (4v-sexpr-vars-list (append x y))
                 (append (4v-sexpr-vars-list x)
                         (4v-sexpr-vars-list y)))
     :hints(("Goal" :induct (len x))))


   (encapsulate
     ()
     (local (defthm l0
              (iff (member-equal a (alist-vals (rev x)))
                   (member-equal a (rev (alist-vals x))))
              :hints(("Goal" :induct (len x)))))

     (defthm 4v-sexpr-vars-list-alist-vals-rev
       (set-equiv (alist-vals (rev x))
                   (rev (alist-vals x)))
       :hints((witness))))

   (encapsulate
     ()
     (local (defthm member-equal-of-rev
              (iff (member-equal a (rev x))
                   (member-equal a x))))

     (defthm rev-under-set-equiv
       (set-equiv (rev x)
                   x)
       :hints((witness))))


   (encapsulate
     ()
     (local (defthm crock
              (implies (member-equal a (alist-vals (hons-shrink-alist alist ans)))
                       (or (member-equal a (alist-vals alist))
                           (member-equal a (alist-vals ans))))
              :rule-classes nil))

     (local (defthm crock2
              (implies (member-equal a (alist-vals (hons-shrink-alist alist nil)))
                       (member-equal a (alist-vals alist)))
              :hints(("Goal" :use ((:instance crock (ans nil)))))))

     (defthm subsetp-equal-of-alist-vals-of-hons-shrink-alist
       (subsetp-equal (alist-vals (hons-shrink-alist alist nil))
                      (alist-vals alist))
       :hints((witness))))

   (encapsulate
     ()
     (local
      (defthm-4v-sexpr-flag
        (defthm l0
          (implies (alist-equiv alist alist2)
                   (equal (4v-sexpr-restrict-with-rw x alist)
                          (4v-sexpr-restrict-with-rw x alist2)))
          :flag sexpr)
        (defthm l1
          (implies (alist-equiv alist alist2)
                   (equal (4v-sexpr-restrict-with-rw-list x alist)
                          (4v-sexpr-restrict-with-rw-list x alist2)))
          :flag sexpr-list)))

     (defcong alist-equiv equal (4v-sexpr-restrict-with-rw x alist) 2
       :hints(("Goal"
               :in-theory (disable l0 l1)
               :use ((:instance l0 (alist2 alist-equiv))))))

     (defcong alist-equiv equal (4v-sexpr-restrict-with-rw-list x alist) 2
       :hints(("Goal"
               :in-theory (disable l0 l1)
               :use ((:instance l1 (alist2 alist-equiv)))))))

   (defthm alist-equiv-of-shadowing-conses
     (alist-equiv (list* (cons a val1)
                         (cons a val2)
                         alist)
                  (list* (cons a val1)
                         alist))
     :hints((witness)))))




(defsection all-equalp

  (defund all-equalp (a x)
    (declare (xargs :guard t))
    (if (atom x)
        t
      (and (equal a (car x))
           (all-equalp a (cdr x)))))

  (local (in-theory (enable all-equalp)))

  (defthm all-equalp-of-atom
    (implies (atom x)
             (all-equalp a x)))

  (defthm all-equalp-of-cons
    (equal (all-equalp a (cons b x))
           (and (equal a b)
                (all-equalp a x)))))



(defsection 4vs-ite*-list-dumb
  :parents (4vs-constructors onehot-rewriting)
  :short "@(call 4vs-ite*-list-dumb) produces a list of sexprs, basically
@('(4V-ITE* C Ai Bi)') for the corresponding elements of @('AS') and @('BS')."

  (defund 4vs-ite*-list-dumb (c as bs)
    (declare (xargs :guard (equal (len as) (len bs))))
    (if (atom as)
        nil
      (cons (4vs-ite*-dumb c (car as) (car bs))
            (4vs-ite*-list-dumb c (cdr as) (cdr bs)))))

  (local (in-theory (enable 4vs-ite*-list-dumb)))

  (defthm 4vs-ite*-list-dumb-when-atom
    (implies (atom as)
             (equal (4vs-ite*-list-dumb c as bs)
                    nil)))

  (defthm 4vs-ite*-list-dumb-of-cons
    (equal (4vs-ite*-list-dumb c (cons a as) (cons b bs))
           (cons (4vs-ite*-dumb c a b)
                 (4vs-ite*-list-dumb c as bs))))

  (defthm consp-of-4vs-ite*-list-dumb
    (equal (consp (4vs-ite*-list-dumb c as bs))
           (consp as)))

  (defthm len-of-4vs-ite*-list-dumb
    (equal (len (4vs-ite*-list-dumb c as bs))
           (len as)))

  (defthm car-of-4vs-ite*-list-dumb
    (equal (car (4vs-ite*-list-dumb c as bs))
           (if (consp as)
               (4vs-ite*-dumb c (car as) (car bs))
             nil)))

  (defthm cdr-of-4vs-ite*-list-dumb
    (equal (cdr (4vs-ite*-list-dumb c as bs))
           (4vs-ite*-list-dumb c (cdr as) (cdr bs))))

  (local (defthm l0
           (implies (equal (len a) (len b))
                    (iff (member-equal v (4v-sexpr-vars-list (4vs-ite*-list-dumb c a b)))
                         (if (consp a)
                             (or (member-equal v (4v-sexpr-vars c))
                                 (member-equal v (4v-sexpr-vars-list a))
                                 (member-equal v (4v-sexpr-vars-list b)))
                           nil)))
           :hints(("Goal"
                   :induct (4vs-ite*-list-dumb c a b)
                   :do-not '(generalize fertilize)))))

  (defthm 4v-sexpr-vars-list-of-4vs-ite*-list-dumb
    (implies (equal (len a) (len b))
             (set-equiv (4v-sexpr-vars-list (4vs-ite*-list-dumb c a b))
                         (if (consp a)
                             (hons-alphorder-merge (4v-sexpr-vars c)
                                                   (hons-alphorder-merge (4v-sexpr-vars-list a)
                                                                         (4v-sexpr-vars-list b)))
                           nil)))
    :hints((witness))))




(defsection 4v-onehot-list-p
  :parents (4vs-onehot onehot-rewriting)
  :short "@(call 4v-onehot-list-p) determines if a list of @(see 4vp)s has
exactly one member that is @('T') while the rest are @('F')."

  (defund 4v-onehot-list-p (x)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (4vcases (car x)
        (f (4v-onehot-list-p (cdr x)))
        (t (all-equalp *4vf* (cdr x)))
        (& nil))))

  (local (in-theory (enable 4v-onehot-list-p)))

  (defthm 4v-onehot-list-p-when-atom
    (implies (atom x)
             (equal (4v-onehot-list-p x)
                    nil)))

  (defthm 4v-onehot-list-p-of-cons
    (equal (4v-onehot-list-p (cons a x))
           (4vcases a
             (f (4v-onehot-list-p x))
             (t (all-equalp *4vf* x))
             (& nil)))))



(defsection 4vs-onehot
  :parents (4vs-constructors onehot-rewriting)
  :short "@(call 4vs-onehot) constructs an s-expression that is @('T') when the
members of @('X') are one-hot."

  :long "<p>@('X') should be a list of s-expressions, say @('(A1 ... AN)').
The s-expression we construct to check whether these are one-hot is somewhat
ugly, and looks something like this:</p>

@({
  (ITE* A1
        (AND (NOT A2) (NOT A3) ... (NOT AN))
    (ITE* A2
          (AND (NOT A3) ... (NOT AN))
      (ITE* AN
            (T)
          (F)) ...))
})

<p>Note that although the printed representation is particularly large looking,
the @('AND') terms here can be mostly structure shared.  For instance, the
@('[~A2...~AN]') term is really just @('(AND (NOT A2) [~A3...~AN])'), so by
honsing sexprs we get a lot of reuse here.</p>

<p>See also @(see 4v-onehot-list-p).</p>"

  (defund 4vs-onehot (sexprs)
    (declare (xargs :guard t))
    (if (atom sexprs)
        (4vs-f)
      (4vs-ite*-dumb (car sexprs)
                     (4vs-and-list-dumb (4vs-not-list (cdr sexprs)))
                     (4vs-onehot (cdr sexprs)))))

  (local (in-theory (enable 4v-onehot-list-p 4vs-onehot)))

  (local (defun my-induct (x env)
           (if (atom x)
               nil
             (if (eq (4v-sexpr-eval (car x) env) *4vf*)
                 (my-induct (cdr x) env)
               (if (eq (4v-sexpr-eval (car x) env) *4vt*)
                   nil
                 nil)))))

  (local (defthm l1
           (implies (4v-onehot-list-p sexprs)
                    (equal (4v-and-list (4v-not-list sexprs))
                           *4vf*))
           :hints(("Goal" :in-theory (enable 4v-onehot-list-p)))))

  (local (defthm l2
           (equal (equal (4v-and-list (4v-not-list sexprs)) t)
                  (all-equalp *4vf* sexprs))
           :hints(("Goal" :induct (len sexprs)))))

  (defthm 4v-sexpr-eval-of-4vs-onehot
    ;; This is kind of a goofy formulation because the onehot-sexpr can
    ;; evaluate to X.  But that will be okay.
    (equal (equal (4v-sexpr-eval (4vs-onehot sexprs) env) *4vt*)
           (4v-onehot-list-p (4v-sexpr-eval-list sexprs env)))
    :hints(("Goal" :induct (my-induct sexprs env))))

  (defthm 4v-sexpr-vars-of-4vs-onehot
    (set-equiv (4v-sexpr-vars (4vs-onehot sexprs))
                (4v-sexpr-vars-list sexprs))
    :hints(("Goal" :in-theory (enable 4vs-onehot))
           (witness))))




(local
 (defsection 4v-helper-lemmas

   (defthm 4v-<=-of-4v-ite*-t
     (equal (4v-<= (4v-ite* *4vt* a b) rhs)
            (4v-<= (4v-unfloat a) rhs)))

   (defthm 4v-<=-of-4v-ite*-f
     (equal (4v-<= (4v-ite* *4vf* a b) rhs)
            (4v-<= (4v-unfloat b) rhs)))

   (defthm 4v-ite*-when-x/z
     (implies (and (case-split (not (equal a *4vf*)))
                   (case-split (not (equal a *4vt*))))
              (equal (4v-ite* a b c)
                     *4vx*)))

   (defthm 4v-<=-of-4v-unfloat-1
     (4v-<= (4v-unfloat a) a))

   (defthm 4v-<=-of-4v-unfloat-2
     (implies (4v-<= a b)
              (4v-<= (4v-unfloat a) b)))

   (in-theory (disable 4v-<= 4v-ite* 4v-unfloat))))




(defsection 4v-onehot-sexpr-prime
  :parents (onehot-rewriting)
  :short "@(call 4v-onehot-sexpr-prime) rewrites @('sexpr') under the
assumption that @('vars') are one-hot."

  :long "<p>How is this reduction accomplished?  Well, in the implementation of
@(see 4v-shannon-expansion), reduced expressions are formed by using @(see
sexpr-restrict) to assume that the variable being is first true, and then
false.  Our approach is basically similar, and our new sexpr is essentially the
following:</p>

@({
 (ITE* A1 SEXPR|_{A1=T,A2=NIL,A3=NIL,...AN=NIL)
  (ITE* A2 SEXPR|_{A1=NIL,A2=T,A3=NIL,...AN=NIL}
   ...
    (ITE* AN SEXPR|_{A1=NIL,A2=NIL,A3=NIL,...,AN=T} (X)) ...))
})

<p>We prove this produces a conservative approximation of @('SEXPR') under the
assumption that the @('Ai') really are one-hot.</p>"

  (defund 4v-onehot-false-bindings (vars)
    ;; Make an alist binding each var to (F)
    (declare (xargs :guard t))
    (if (atom vars)
        nil
      (cons (cons (car vars) (4vs-f))
            (4v-onehot-false-bindings (cdr vars)))))

  (defund 4v-onehot-sexpr-prime-aux
    (vars           ;; the list of AI, which we recur down
     false-bindings ;; fast alist that binds all AI to (F), which we mangle and free
     sexpr          ;; the sexpr we're reducing
     )
    "Returns SEXPR'"
    (declare (xargs :guard t))
    (b* (((when (atom vars))
          (fast-alist-free false-bindings)
          (4vs-x))
         ;; Probably silly performance hack: we avoid constructing many fast
         ;; alists by rebinding the variable after we're done with it.
         (var            (car vars))
         (bindings       (hons-acons var (4vs-t) false-bindings))
         ;; Note: can use sexpr-restrict without rewrite instead, but Sol thinks
         ;; this might be cheap enough to do inline.
         (sexpr/bindings (4v-sexpr-restrict-with-rw sexpr bindings))
         (false-bindings (hons-acons var (4vs-f) bindings)))
      (4vs-ite*-dumb (car vars)
                     sexpr/bindings
                     (4v-onehot-sexpr-prime-aux (cdr vars) false-bindings sexpr))))

  (defund 4v-onehot-sexpr-prime (vars sexpr)
    (declare (xargs :guard (and (atom-listp vars)
                                (not (member-equal nil vars)))))
    (4v-onehot-sexpr-prime-aux vars
                               (make-fast-alist ;; Freed by the aux function
                                (4v-onehot-false-bindings vars))
                               sexpr))


  (defcong alist-equiv equal (4v-onehot-sexpr-prime-aux vars false-bindings sexpr) 2
    :hints(("Goal" :in-theory (enable 4v-onehot-sexpr-prime-aux))))

  (local
   (defthm alist-keys-of-4v-onehot-false-bindings
     (equal (alist-keys (4v-onehot-false-bindings vars))
            (list-fix vars))
     :hints(("Goal" :in-theory (enable 4v-onehot-false-bindings)))))


  (local
   (defsection all-bound-to-false-p

; A basic invariant is that everything in false-bindings is bound to false.

     (defquant all-bound-to-false-p (alist)
       (forall var (implies (hons-assoc-equal var alist)
                            (equal (cdr (hons-assoc-equal var alist))
                                   (4vs-f)))))

     (defexample all-bound-to-false-p-example
       :pattern (hons-assoc-equal var alist)
       :templates (var)
       :instance-rulename all-bound-to-false-p-instancing)

     (defthm cdr-hons-assoc-equal-when-all-bound-to-false-p
       (implies (and (all-bound-to-false-p alist)
                     (hons-assoc-equal var alist))
                (equal (hons-assoc-equal var alist)
                       (cons var (4vs-f))))
       :hints((witness))
       :rule-classes ((:rewrite)
                      (:rewrite :corollary
                                (implies (and (hons-assoc-equal var alist)
                                              (all-bound-to-false-p alist))
                                         (equal (hons-assoc-equal var alist)
                                                (cons var (4vs-f)))))))

     (defcong alist-equiv equal (all-bound-to-false-p alist) 1
       :hints((witness)))

     (defthm all-bound-to-false-p-of-cons-rhs
       ;; Lemma to show that the invariant is maintained as we recur in
       ;; the aux function.
       (implies (all-bound-to-false-p false-bindings)
                (all-bound-to-false-p (cons (cons var (4vs-f))
                                            false-bindings)))
       :hints((witness)))

     (local (defthm l0
              (equal (hons-assoc-equal a (4v-onehot-false-bindings vars))
                     (if (member-equal a vars)
                         (cons a (4vs-f))
                       nil))
              :hints(("Goal"
                      :in-theory (enable 4v-onehot-false-bindings
                                         hons-assoc-equal
                                         equal-of-cons-rewrite)))))

     (defthm all-bound-to-false-p-of-4v-onehot-false-bindings
       ;; Lemma to show that the invariant holds at the start of the computation.
       (all-bound-to-false-p (4v-onehot-false-bindings vars))
       :hints(("Goal" :in-theory (enable 4v-onehot-false-bindings))
              (witness)))))


  (local
   (defsection main-lemma-for-the-true-case

; We now show that, given:
;
;   - some VARS that are onehot in ENV
;   - some alist bindings VARS -> FALSE
;   - the VAR in VARS that is bound to TRUE in ENV
;
; It follows that: SEXPR|{VAR=T}@{VARS=F}@ENV == SEXPR|ENV
;
; An informal proof is very straightforward:
;
;  - We can show that SEXPR|ENV1 == SEXPR|ENV2 if we can show ENV1 and ENV2
;    bind all variables to equivalent values.
;
;  - So, to prove our goal it suffices to show {VAR=T}@{VARS=F}@ENV and ENV
;    bind all variables to the same values.
;
;  - This is obvious from the assumption that VARS are onehot in ENV and that
;    VAR is T in ENV.
;
; Q.E.D
;
; The proof below is basically the same thing, but is long in order to prove
; the "obvious" step.

     (local (in-theory (disable 4v-lookup 4v-sexpr-eval-alist)))

     (local (defthm 4v-lookup-of-proper-cons
              (equal (4v-lookup a (cons (cons b val) env))
                     (if (equal a b)
                         (4v-fix val)
                       (4v-lookup a env)))
              :hints(("Goal" :in-theory (enable 4v-lookup)))))

     (local (defthm 4v-lookup-of-append
              (equal (4v-lookup a (append env1 env2))
                     (if (hons-assoc-equal a (double-rewrite env1))
                         (4v-lookup a (double-rewrite env1))
                       (4v-lookup a env2)))
              :hints(("Goal" :in-theory (enable 4v-lookup)))))

     (local (defthm h1
              (implies (and (all-bound-to-false-p false-bindings)
                            (hons-assoc-equal key false-bindings))
                       (equal (4v-lookup key (4v-sexpr-eval-alist false-bindings env))
                              *4vf*))
              :hints(("Goal" :in-theory (enable 4v-lookup)))))

     (local (defthm h2
              (implies (and (all-equalp *4vf* (4v-sexpr-eval-list x env))
                            (member-equal a x))
                       (equal (4v-sexpr-eval a env)
                              *4vf*))))

     (local (defthm h3
              (implies (and (4v-onehot-list-p (4v-sexpr-eval-list sexprs env))
                            (member-equal a sexprs)
                            (member-equal b sexprs)
                            (not (equal a b))
                            (equal (4v-sexpr-eval a env) *4vt*))
                       (equal (4v-sexpr-eval b env) *4vf*))
              :hints(("Goal"
                      :induct (len sexprs)
                      :in-theory (enable 4v-onehot-list-p)))))

     (local (defthm atom-when-member-of-atom-list
              (implies (and (atom-listp x)
                            (member-equal a x))
                       (not (consp a)))
              :rule-classes ((:rewrite)
                             (:rewrite :corollary
                                       (implies (and (member-equal a x)
                                                     (atom-listp x))
                                                (not (consp a)))))))

     (local (defthm h4
              (implies (and (equal (4v-lookup a env) *4vt*)
                            (not (equal a b))
                            (atom-listp sexprs)
                            (not (member nil sexprs))
                            (4v-onehot-list-p (4v-sexpr-eval-list sexprs env))
                            (member-equal a sexprs)
                            (member-equal b sexprs))
                       (equal (4v-lookup b env) *4vf*))
              :hints(("Goal"
                      :expand ((4v-sexpr-eval b env))
                      :in-theory (disable h3)
                      :use ((:instance h3))
                      :do-not-induct t))))

     (local (defthm h5
              (implies (and (consp a)
                            (atom b))
                       (equal (4v-lookup a (cons (cons b val) env))
                              (4v-lookup a env)))))

     (local (defthm h6
              (implies (and (consp a)
                            (atom-listp (alist-keys env1)))
                       (equal (hons-assoc-equal a (append env1 env2))
                              (hons-assoc-equal a env2)))
              :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

     (local (defthm h7
              (implies (and (consp a)
                            (atom-listp (alist-keys env1)))
                       (equal (4v-lookup a (append env1 env2))
                              (4v-lookup a env2)))
              :hints(("Goal" :in-theory (enable 4v-lookup)))))

     (local (defthm obvious
              (implies
               (and
                ;; The false-bindings bind proper variables to (4vs-f)
                (atom-listp (alist-keys false-bindings))
                (not (member-equal nil (alist-keys false-bindings)))
                (all-bound-to-false-p false-bindings)
                ;; The variables bound in the false-bindings are one-hot in ENV
                (4v-onehot-list-p (4v-sexpr-eval-list (alist-keys false-bindings) env))
                ;; VAR is the one variable that evaluates to TRUE in ENV.
                (member-equal var (alist-keys false-bindings))
                (equal (4v-sexpr-eval var env) *4vt*))
               ;; Then, any arbitrary KEY evaluates to the same value in
               ;; {var=T}@{vars=NIL}@ENV as it does in ENV
               (equal (4v-lookup key (cons (cons var *4vt*)
                                           (append (4v-sexpr-eval-alist false-bindings env)
                                                   env)))
                      (4v-lookup key env)))
              :hints(("Goal"
                      :cases ((equal key var)
                              (hons-assoc-equal key false-bindings))))))

     (local (defthm 4v-env-equiv-of-envs
              (implies
               (and
                ;; The false-bindings bind proper variables to (4vs-f)
                (atom-listp (alist-keys false-bindings))
                (not (member-equal nil (alist-keys false-bindings)))
                (all-bound-to-false-p false-bindings)
                ;; The variables bound in the false-bindings are one-hot in ENV
                (4v-onehot-list-p (4v-sexpr-eval-list (alist-keys false-bindings) env))
                ;; VAR is the one variable that evaluates to TRUE in ENV.
                (member-equal var (alist-keys false-bindings))
                (equal (4v-sexpr-eval var env) *4vt*))
               (4v-env-equiv (cons (cons var *4vt*)
                                   (append (4v-sexpr-eval-alist false-bindings env)
                                           env))
                             env))
              :hints(("Goal"
                      :in-theory (disable 4v-lookup-of-proper-cons
                                          4v-lookup-of-append))
                     (witness :ruleset 4v-env-equiv-witnessing))))

     (defthm main-lemma-for-the-true-case
       (implies (and
                 ;; The false-bindings bind proper variables to (4vs-f)
                 (force (atom-listp (alist-keys false-bindings)))
                 (force (not (member-equal nil (alist-keys (double-rewrite false-bindings)))))
                 (force (all-bound-to-false-p false-bindings))
                 ;; The variables bound in the false-bindings are one-hot in ENV.
                 (force (4v-onehot-list-p (4v-sexpr-eval-list (alist-keys false-bindings) env)))
                 ;; VAR is the one variable that evalutes to TRUE in ENV
                 (force (member-equal var (alist-keys false-bindings)))
                 (case-split (equal (4v-sexpr-eval var env) *4vt*))
                 )
                (equal (4v-sexpr-eval sexpr
                                      (cons (cons var *4vt*)
                                            (append (4v-sexpr-eval-alist false-bindings env)
                                                    env)))
                       (4v-sexpr-eval sexpr env)))
       :hints((witness)))))


  (local
   (defthm main-lemma-for-the-aux-function
     (let* ((all-vars       (alist-keys false-bindings))
            (above-vars     (set-difference-equal all-vars vars))
            (all-vars@env   (4v-sexpr-eval-list all-vars env))
            (above-vars@env (4v-sexpr-eval-list above-vars env)))
       (implies (and (all-bound-to-false-p false-bindings)
                     (atom-listp (alist-keys false-bindings))
                     (not (member-equal nil (alist-keys false-bindings)))
                     (subsetp-equal vars all-vars)
                     (4v-onehot-list-p all-vars@env)
                     (all-equalp above-vars@env *4vf*))
                (4v-<= (4v-sexpr-eval (4v-onehot-sexpr-prime-aux vars false-bindings sexpr) env)
                       (4v-sexpr-eval sexpr env))))
     :hints(("Goal"
             :induct (4v-onehot-sexpr-prime-aux vars false-bindings sexpr)
             :in-theory (enable 4v-onehot-sexpr-prime-aux)
             :do-not '(generalize fertilize)
             :do-not-induct t))))

  (local (defthm hons-assoc-equal-under-iff
           (iff (hons-assoc-equal key alist)
                (member-equal key (alist-keys alist)))))

  (local (in-theory (disable alist-keys-member-hons-assoc-equal)))

  (local (defthm crock
           (implies (not (member-equal nil vars))
                    (not (hons-assoc-equal nil (4v-onehot-false-bindings vars))))))

  (defthm 4v-sexpr-eval-of-4v-onehot-sexpr-prime
    (implies (and (4v-onehot-list-p (4v-sexpr-eval-list vars env))
                  (atom-listp vars)
                  (not (member-equal nil vars)))
             (4v-<= (4v-sexpr-eval (4v-onehot-sexpr-prime vars sexpr) env)
                    (4v-sexpr-eval sexpr env)))
    :hints(("Goal"
            :in-theory (e/d (4v-onehot-sexpr-prime)
                            (main-lemma-for-the-aux-function))
            :use ((:instance main-lemma-for-the-aux-function
                             (false-bindings (4v-onehot-false-bindings vars))))
            :do-not '(generalize fertilize)
            :do-not-induct t)))


  (encapsulate
    ()
    (local (defthm l0
             (implies (atom-listp vars)
                      (iff (member-equal k (4v-sexpr-vars-list vars))
                           (and (member-equal k vars)
                                (not (equal k nil)))))
             :hints(("Goal" :in-theory (enable 4v-sexpr-vars-list)))))

    (local (defthm l1
             (implies
              (and (atom-listp vars)
                   (not (4v-sexpr-vars-list (alist-vals false-bindings)))
                   (not (member-equal k (4v-sexpr-vars sexpr)))
                   (not (member-equal k vars)))
              (not (member-equal k (4v-sexpr-vars
                                    (4v-onehot-sexpr-prime-aux vars false-bindings sexpr)))))
             :hints(("Goal"
                     :induct (4v-onehot-sexpr-prime-aux vars false-bindings sexpr)
                     :in-theory (enable 4v-onehot-sexpr-prime-aux)))))

    (local (defthm l2
             (implies (and (atom-listp vars)
                           (not (4v-sexpr-vars-list (alist-vals false-bindings))))
                      (subsetp-equal
                       (4v-sexpr-vars (4v-onehot-sexpr-prime-aux vars false-bindings sexpr))
                       (append vars (4v-sexpr-vars sexpr))))
             :hints((witness))))

    (local (defthm l3
             (equal (4v-sexpr-vars-list (alist-vals (4v-onehot-false-bindings vars)))
                    nil)
             :hints(("Goal" :in-theory (enable 4v-onehot-false-bindings)))))

    (defthm 4v-sexpr-vars-of-4v-onehot-sexpr-prime
      (implies (atom-listp vars)
               (subsetp-equal (4v-sexpr-vars (4v-onehot-sexpr-prime vars sexpr))
                              (append vars (4v-sexpr-vars sexpr))))
      :hints(("Goal"
              :in-theory (enable 4v-onehot-sexpr-prime))))))




(defsection 4v-onehot-sexpr-list-prime
  :parents (onehot-rewriting)
  :short "Efficiently reduce a list of sexprs under the assumption that some
variables are one-hot."

  :long "<p>Logically, this function does nothing more than compute @(see
4v-onehot-sexpr-prime) for each sexpr in a list.</p>

<p>With @(see mbe) we do something tricky for better performance.  The real
function we execute is basically a wide version of @(see
4v-onehot-sexpr-prime)'s auxilliary function.</p>

<p>What is this performance hack all about?  Our main goal in onehot rewriting
is to simplify the update functions of modules that have one-hot inputs.  In
this context, we have some particular set of variables that we think are
one-hot, say @('A1...An'), and a whole list of (related) update functions,
represented as the s-expressions @('S1...Sk').</p>

<p>We want to apply our onehot rewrite on on each of these expressions. The
simplest thing to do would be to call @(see 4v-onehot-rw-sexpr) on each
expression and just cons together the results, as in the logical definition.
But if we do this, then we are likely going to miss out on many opportunities
to reuse memoized results.</p>

<p>Why?  The problem is that each sexpr needs to be restrict/rewritten with a
number of alists.  Recall that we effectively replace each sexpr with:</p>

@({
 (ITE* A1 SEXPR|_{A1=T,A2=NIL,A3=NIL,...AN=NIL)
  (ITE* A2 SEXPR|_{A1=NIL,A2=T,A3=NIL,...AN=NIL}
   ...
    (ITE* AN SEXPR|_{A1=NIL,A2=NIL,A3=NIL,...,AN=T} (X)) ...))
})

<p>But these alists only depend on the variables @('Ai'), not on the sexprs
@('Si').  For better performance, we want to use the same alist to rewrite all
of the sexprs at once, since there is presumably a lot of sharing between the
update functions.  It turns out this optimization is not too bad to
implement.</p>"

  (defund 4v-onehot-sexpr-list-prime-exec
    (vars           ;; the list of AI, which we recur down
     false-bindings ;; fast alist that binds all AI to (F), which we mangle and free
     sexprs         ;; the sexpr list we're reducing
     )
    "Returns SEXPRS'"
    (declare (xargs :guard t :verify-guards nil))
    (b* (((when (atom vars))
          (fast-alist-free false-bindings)
          (repeat (4vs-x) (len sexprs)))

         (var             (car vars))
         (bindings        (hons-acons var (4vs-t) false-bindings))
         (sexprs/bindings (4v-sexpr-restrict-with-rw-list sexprs bindings))
         (-               (clear-memoize-table '4v-sexpr-restrict-with-rw))
         (false-bindings  (hons-acons var (4vs-f) bindings)))

      (4vs-ite*-list-dumb (car vars)
                     sexprs/bindings
                     (4v-onehot-sexpr-list-prime-exec (cdr vars) false-bindings sexprs))))

  (local (in-theory (enable 4v-onehot-sexpr-list-prime-exec)))

  (defcong alist-equiv equal (4v-onehot-sexpr-list-prime-exec vars false-bindings sexprs) 2)

  (defthm len-of-4v-onehot-sexpr-list-prime-exec
    (equal (len (4v-onehot-sexpr-list-prime-exec vars false-bindings sexprs))
           (len sexprs)))

  (verify-guards 4v-onehot-sexpr-list-prime-exec)

  (defund 4v-onehot-sexpr-list-prime-aux (vars false-bindings sexprs)
    ;; Same as the -exec function, but recurs over the sexprs instead.  The MBE
    ;; equivalence here is easy once you see the trick of proving the -exec
    ;; function's car and cdr, which avoids having to do any tricky merging of
    ;; induction schemes.
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic
         (if (atom sexprs)
             nil
           (cons (4v-onehot-sexpr-prime-aux vars false-bindings (car sexprs))
                 (4v-onehot-sexpr-list-prime-aux vars false-bindings (cdr sexprs))))
         :exec
         (4v-onehot-sexpr-list-prime-exec vars false-bindings sexprs)))

  (local (in-theory (enable 4v-onehot-sexpr-list-prime-aux)))

  (local (defthm l0
           (implies (atom sexprs)
                    (not (4v-onehot-sexpr-list-prime-exec vars false-bindings sexprs)))))

  (local (defthm l1
           (equal (consp (4v-onehot-sexpr-list-prime-exec vars false-bindings sexprs))
                  (consp sexprs))))

  (local (defthm l2
           (implies (consp sexprs)
                    (equal (car (4v-onehot-sexpr-list-prime-exec vars false-bindings sexprs))
                           (4v-onehot-sexpr-prime-aux vars false-bindings (car sexprs))))
           :hints(("Goal" :in-theory (enable 4v-onehot-sexpr-prime-aux)))))

  (local (defthm l3
           (equal (cdr (4v-onehot-sexpr-list-prime-exec vars false-bindings sexprs))
                  (4v-onehot-sexpr-list-prime-exec vars false-bindings (cdr sexprs)))))

  (local (in-theory (disable 4v-onehot-sexpr-list-prime-exec)))

  (defthm 4v-onehot-sexpr-list-prime-exec-removal
    (equal (4v-onehot-sexpr-list-prime-exec vars false-bindings sexprs)
           (4v-onehot-sexpr-list-prime-aux vars false-bindings sexprs)))

  (verify-guards 4v-onehot-sexpr-list-prime-aux)


  (defund 4v-onehot-sexpr-list-prime (vars sexprs)
    (declare (xargs :guard (and (atom-listp vars)
                                (not (member-equal nil vars)))
                    :verify-guards nil))
    (mbe :logic
         (if (atom sexprs)
             nil
           (cons (4v-onehot-sexpr-prime vars (car sexprs))
                 (4v-onehot-sexpr-list-prime vars (cdr sexprs))))
         :exec
         (4v-onehot-sexpr-list-prime-aux vars
                                         (make-fast-alist ;; Freed by the aux function
                                          (4v-onehot-false-bindings vars))
                                         sexprs)))

  (verify-guards 4v-onehot-sexpr-list-prime
    :hints(("Goal" :in-theory (enable 4v-onehot-sexpr-prime
                                      4v-onehot-sexpr-list-prime))))

  (defthm 4v-onehot-sexpr-list-prime-when-atom
    (implies (atom x)
             (equal (4v-onehot-sexpr-list-prime vars x)
                    nil))
    :hints(("Goal" :in-theory (enable 4v-onehot-sexpr-list-prime))))

  (defthm 4v-onehot-sexpr-list-prime-of-cons
    (equal (4v-onehot-sexpr-list-prime vars (cons a x))
           (cons (4v-onehot-sexpr-prime vars a)
                 (4v-onehot-sexpr-list-prime vars x)))
    :hints(("Goal" :in-theory (enable 4v-onehot-sexpr-list-prime))))

  (cutil::defprojection 4v-onehot-sexpr-list-prime (vars x)
    (4v-onehot-sexpr-prime vars x)
    :already-definedp t
    :nil-preservingp nil)


  ;; (defthm 4v-sexpr-vars-of-4v-onehot-sexpr-prime
  ;;   (implies (atom-listp vars)
  ;;            (subsetp-equal (4v-sexpr-vars (4v-onehot-sexpr-prime vars sexpr))
  ;;                           (append vars (4v-sexpr-vars sexpr))))

  (local (defthm c0
           (implies (subsetp-equal a (append b c))
                    (subsetp-equal a (append b c d)))))

  (defthm 4v-sexpr-vars-list-of-4v-onehot-sexpr-list-prime
    (implies (atom-listp vars)
             (subsetp-equal (4v-sexpr-vars-list (4v-onehot-sexpr-list-prime vars sexprs))
                            (append vars (4v-sexpr-vars-list sexprs))))
    :hints(("Goal"
            :induct (len sexprs)
            :do-not '(generalize fertilize)
            :do-not-induct t))))




(defsection 4v-onehot-rw-sexpr
  :parents (onehot-rewriting)
  :short "Apply @(see onehot-rewriting) to a single s-expression."

  :long "<p>@(call 4v-onehot-rw-sexpr) is given:</p> <ul> <li>@('vars'), which
must be a @('nil')-free list of atoms, and</li> <li>@('sexpr'), the
s-expression we want to reduce.</li> </ul>

<p>It returns a new sexpression that is a (possibly simpler) conservative
approximation of @('sexpr') where the vars are assumed to be one-hot.</p>

<p>We usually don't call this function in practice, because @(see
4v-onehot-rw-sexpr-alist) uses a more efficient scheme that bypasses it.
On the other hand, it's a nice function for reasoning about.</p>"

(defund 4v-onehot-rw-sexpr (vars sexpr)
    (declare (xargs :guard (and (atom-listp vars)
                                (not (member-equal nil vars)))))
    (4vs-ite*-dumb (4vs-onehot vars)
                   (4v-onehot-sexpr-prime vars sexpr)
                   (4vs-x)))

(local (in-theory (enable 4v-onehot-rw-sexpr)))

(defthm 4v-sexpr-eval-of-4v-onehot-rw-sexpr
    (implies (and (atom-listp vars)
                  (not (member-equal nil vars)))
             (4v-<= (4v-sexpr-eval (4v-onehot-rw-sexpr vars sexpr) env)
                    (4v-sexpr-eval sexpr env)))
    :hints(("Goal"
            :in-theory (e/d (4v-ite* 4v-unfloat 4v-<=)
                            (4v-sexpr-eval-of-4v-onehot-sexpr-prime
                             4v-sexpr-eval-of-4vs-onehot))
            :use ((:instance 4v-sexpr-eval-of-4v-onehot-sexpr-prime)
                  (:instance 4v-sexpr-eval-of-4vs-onehot
                             (sexprs vars)))
            :do-not '(generalize fertilize)
            :do-not-induct t)))

(defthm 4v-sexpr-<=-of-4v-onehot-rw-sexpr
    (implies (and (atom-listp vars)
                  (not (member-equal nil vars)))
             (4v-sexpr-<= (4v-onehot-rw-sexpr vars sexpr)
                          sexpr))
    :hints(("Goal" :in-theory (disable 4v-onehot-rw-sexpr))
           (witness)))

(defthm 4v-sexpr-vars-of-4v-onehot-rw-sexpr
    (implies (atom-listp vars)
             (subsetp-equal (4v-sexpr-vars (4v-onehot-rw-sexpr vars sexpr))
                            (append vars (4v-sexpr-vars sexpr))))))



(defsection 4v-onehot-rw-sexpr-alist-aux
  :parents (onehot-rewriting)
  :short "Apply one-hot rewriting to a sexpr-alist."

  :long "<p>Logically this just walks over the alist and applies @(see
4v-onehot-rw-sexpr) to each value.  But we actually use @(see mbe) to
provide a more efficient implementation; see @(see 4v-onehot-sexpr-list-prime)
for the basic idea and motivation.</p>

<p>This is only an @('-aux') function because it applies the onehot rewrite to
<b>every</b> sexpr in the alist.  Our main function, @(see
4v-onehot-rw-sexpr-alist), first filters the alist to avoid rewriting sexprs
that don't mention any of the variables we are assuming to be one-hot.</p>"

  (defund 4v-onehot-rw-sexpr-alist-fast (vars sexpr-alist)
    (declare (xargs :guard (and (atom-listp vars)
                                (not (member-equal nil vars)))))
    (let* ((names  (alist-keys sexpr-alist))
           (sexprs (alist-vals sexpr-alist))
           (new-sexprs
            (4vs-ite*-list-dumb (4vs-onehot vars)
                           (4v-onehot-sexpr-list-prime vars sexprs)
                           (repeat (4vs-x) (len sexprs)))))
      (pairlis$ names new-sexprs)))

  (defund 4v-onehot-rw-sexpr-alist-aux (vars sexpr-alist)
    (declare (xargs :guard (and (atom-listp vars)
                                (not (member-equal nil vars)))
                    :verify-guards nil))
    (mbe :logic
         (cond ((atom sexpr-alist)
                nil)
               ((atom (car sexpr-alist))
                (4v-onehot-rw-sexpr-alist-aux vars (cdr sexpr-alist)))
               (t
                (cons (cons (caar sexpr-alist)
                            (4v-onehot-rw-sexpr vars (cdar sexpr-alist)))
                      (4v-onehot-rw-sexpr-alist-aux vars (cdr sexpr-alist)))))
         :exec
         (4v-onehot-rw-sexpr-alist-fast vars sexpr-alist)))

  (local (in-theory (enable 4v-onehot-rw-sexpr-alist-fast
                            4v-onehot-rw-sexpr-alist-aux
                            )))

  (local (defthm l0
           (implies (atom sexpr-alist)
                    (equal (4v-onehot-rw-sexpr-alist-fast vars sexpr-alist)
                           nil))))

  (local (defthm l1
           (implies (and (consp sexpr-alist)
                         (atom (car sexpr-alist)))
                    (equal (4v-onehot-rw-sexpr-alist-fast vars sexpr-alist)
                           (4v-onehot-rw-sexpr-alist-fast vars (cdr sexpr-alist))))))

  (local (defthm l2
           (implies (and (consp sexpr-alist)
                         (consp (car sexpr-alist)))
                    (equal (4v-onehot-rw-sexpr-alist-fast vars sexpr-alist)
                           (cons (cons (caar sexpr-alist)
                                       (4v-onehot-rw-sexpr vars (cdar sexpr-alist)))
                                 (4v-onehot-rw-sexpr-alist-fast vars (cdr sexpr-alist)))))
           :hints(("Goal" :in-theory (enable alist-keys 4v-onehot-rw-sexpr)))))

  (local (in-theory (disable 4v-onehot-rw-sexpr-alist-fast)))

  (defthm 4v-onehot-rw-sexpr-alist-fast-removal
    (equal (4v-onehot-rw-sexpr-alist-fast vars sexpr-alist)
           (4v-onehot-rw-sexpr-alist-aux vars sexpr-alist)))

  (verify-guards 4v-onehot-rw-sexpr-alist-aux)

  (defthm hons-assoc-equal-of-4v-onehot-rw-sexpr-alist-aux
    (equal (hons-assoc-equal name (4v-onehot-rw-sexpr-alist-aux vars sexpr-alist))
           (if (hons-assoc-equal name sexpr-alist)
               (cons name
                     (4v-onehot-rw-sexpr
                      vars
                      (cdr (hons-assoc-equal name sexpr-alist))))
             nil))
    :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  (defthm 4v-sexpr-alist-<=-of-4v-onehot-rw-sexpr-alist-aux
    (implies (and (atom-listp vars)
                  (not (member-equal nil vars)))
             (4v-sexpr-alist-<= (4v-onehot-rw-sexpr-alist-aux vars sexpr-alist)
                                sexpr-alist))
    :hints((witness)))

  (local (defthm c0
           (implies (subsetp-equal a (append b c))
                    (subsetp-equal a (append b c d)))))

  (defthm 4v-sexpr-vars-list-of-4v-onehot-rw-sexpr-alist-aux
    (implies (atom-listp vars)
             (subsetp-equal
              (4v-sexpr-vars-list (alist-vals (4v-onehot-rw-sexpr-alist-aux vars sexpr-alist)))
              (append vars (4v-sexpr-vars-list (alist-vals sexpr-alist)))))
    :hints(("Goal"
            :in-theory (enable 4v-onehot-rw-sexpr-alist-aux)
            :induct (len sexpr-alist)
            :do-not '(generalize fertilize)
            :do-not-induct t))))



(defsection 4v-onehot-filter
  :parents (onehot-rewriting)
  :short "Filter a sexpr-alist to avoid unnecessary @(see onehot-rewriting)."

  (mutual-recursion
   (defund 4v-sexpr-mentions (x vars-fal)
     ;; Returns non-nil if X mentions any variables bound in vars-fal
     (declare (xargs :guard t))
     (if (atom x)
         (hons-get x vars-fal)
       (4v-sexpr-list-mentions (cdr x) vars-fal)))
   (defund 4v-sexpr-list-mentions (x vars-fal)
     (declare (xargs :guard t))
     (if (atom x)
         nil
       (or (4v-sexpr-mentions (car x) vars-fal)
           (4v-sexpr-list-mentions (cdr x) vars-fal)))))

  (memoize '4v-sexpr-mentions :condition '(consp x))

  ;; We assume X has no shadowed pairs.  Move all entries that don't mention
  ;; vars in vars-fal into SKIP, and put any entries mentioning the vars into
  ;; KEEP.

  (defund 4v-onehot-filter (x vars-fal keep skip)
    (declare (xargs :guard t))
    (cond ((atom x)
           (mv keep skip))
          ((atom (car x))
           (4v-onehot-filter (cdr x) vars-fal keep skip))
          ((4v-sexpr-mentions (cdar x) vars-fal)
           (4v-onehot-filter (cdr x) vars-fal (cons (car x) keep) skip))
          (t
           (4v-onehot-filter (cdr x) vars-fal keep (cons (car x) skip)))))

  (defthm 4v-onehot-filter-correct
    (b* (((mv keep skip) (4v-onehot-filter x vars-fal nil nil)))
      (implies (no-duplicatesp-equal (alist-keys x))
               (equal (hons-assoc-equal key x)
                      (or (hons-assoc-equal key keep)
                          (hons-assoc-equal key skip)))))
    :rule-classes nil
    :hints(("Goal"
            :in-theory (enable 4v-onehot-filter)
            :use ((:functional-instance filter-alist-correct
                    (filter-alist
                     (lambda (x keep skip)
                       (4v-onehot-filter x vars-fal keep skip)))
                    (filter-alist-criteria
                     (lambda (entry)
                       (4v-sexpr-mentions (cdr entry) vars-fal)))))))))



(defsection 4v-onehot-rw-sexpr-alist
  :parents (onehot-rewriting)
  :short "Apply @(see onehot-rewriting) to a sexpr alist."

  :long "<p>@(call 4v-onehot-rw-sexpr-alist) is given:</p> <ul> <li>@('vars'),
which must be a @('nil')-free list of atoms, and</li> <li>@('sexpr-alist'), an
alist binding names to sexprs.</li> </ul>

<p>We return a new, ordinary (slow) sexpr-alist which is a (possibly simpler)
conservative approximation of the original.  The basic idea is to apply @(see
4v-onehot-rw-sexpr) to any sexprs that mention any of the @('vars'), and leave
any other sexprs unchanged.</p>"

; Note.  We currently don't do anything to the irrelevant-part.
;
; It *might* make sense to rewrite it with ordinary sexpr-rewrite: if you want
; to do ordinary alist rewriting in addition to onehot rewriting, then with our
; current scheme you end up somewhat redundantly rewriting the relevant-part.
;
; On the other hand, it's somewhat likely that the relevant-part is relatively
; small, so the overhead there may be pretty small.

  (defund 4v-onehot-rw-sexpr-alist (vars sexpr-alist)
    (declare (xargs :guard (and (atom-listp vars)
                                (not (member-equal nil vars)))))
    (b* ((- (or (uniquep vars)
                (er hard? '4v-onehot-rw-sexpr-alist
                    "You really want to use unique variables for onehot ~
                   rewriting. Duplicated variables are: ~&0.~%"
                    (duplicated-members vars))))

         ;; Shrink the sexpr-alist so that we know the keys are unique, which we
         ;; need for our filtering function to work properly.
         (sexpr-alist (fast-alist-free (hons-shrink-alist sexpr-alist nil)))

         ;; Filter the alist so that we won't rewrite the irrelevant parts of it.
         (vars-fal    (make-fast-alist (pairlis$ vars nil)))
         ((mv relevant-part irrelevant-part)
          (4v-onehot-filter sexpr-alist vars-fal nil nil))
         (- (fast-alist-free vars-fal))
         (- (clear-memoize-table '4v-sexpr-mentions))

         ((unless relevant-part)
          ;; No need to rewrite anything, just return the reduced sexpr-alist.
          sexpr-alist))

      (append (4v-onehot-rw-sexpr-alist-aux vars relevant-part)
              irrelevant-part)))

  (local (in-theory (enable 4v-onehot-rw-sexpr-alist)))

  (encapsulate
    ()
    (local (defthm l0
             (b* (((mv ?keep ?skip) (4v-onehot-filter x vars-fal nil nil)))
               (implies (and (hons-assoc-equal key keep)
                             (force (no-duplicatesp-equal (alist-keys x))))
                        (equal (hons-assoc-equal key keep)
                               (hons-assoc-equal key x))))
             :hints(("Goal" :use ((:instance 4v-onehot-filter-correct))))))

    (local (defthm l1
             (b* (((mv ?keep ?skip) (4v-onehot-filter x vars-fal nil nil)))
               (implies (and (not (hons-assoc-equal key keep))
                             (force (no-duplicatesp-equal (alist-keys x))))
                        (equal (hons-assoc-equal key skip)
                               (hons-assoc-equal key x))))
             :hints(("Goal"
                     :in-theory (disable l0)
                     :use ((:instance 4v-onehot-filter-correct))))))

    (local (defthm main-lemma
             (let ((new-sexpr-alist (4v-onehot-rw-sexpr-alist vars sexpr-alist)))
               (implies (and (atom-listp vars)
                             (not (member-equal nil vars)))
                        (4v-<=
                         (4v-sexpr-eval (cdr (hons-assoc-equal key new-sexpr-alist)) env)
                         (4v-sexpr-eval (cdr (hons-assoc-equal key sexpr-alist)) env))))
             :hints(("Goal"
                     :do-not '(generalize fertilize)
                     :do-not-induct t))))

    (defthm 4v-sexpr-alist-<=-of-4v-onehot-rw-sexpr-alist
      (implies (and (atom-listp vars)
                    (not (member-equal nil vars)))
               (4v-sexpr-alist-<= (4v-onehot-rw-sexpr-alist vars sexpr-alist)
                                  sexpr-alist))
      :hints((witness))))


  (encapsulate
    ()
    (local (defthm c0
             (iff (hons-assoc-equal key (4v-onehot-rw-sexpr-alist vars sexpr-alist))
                  (hons-assoc-equal key sexpr-alist))
             :hints(("Goal"
                     :use ((:instance 4v-onehot-filter-correct
                                      (x (hons-shrink-alist sexpr-alist nil))
                                      (vars-fal (pairlis$ vars nil))))
                     :do-not '(generalize fertilize)
                     :do-not-induct t))))

    (defthm alist-keys-of-4v-onehot-rw-sexpr-alist
      (set-equiv (alist-keys (4v-onehot-rw-sexpr-alist vars sexpr-alist))
                  (alist-keys sexpr-alist))
      :hints(("Goal" :in-theory (disable 4v-onehot-rw-sexpr-alist))
             (witness))))


  ;; Oh man, the 4v-sexpr-vars proof is Terrrrrrible!
  ;; I couldn't see how to do it without just redefining 4v-onehot-filter to be
  ;; nicer.

  (local (defun relevant (x vars-fal)
           (cond ((atom x)
                  nil)
                 ((atom (car x))
                  (relevant (cdr x) vars-fal))
                 ((4v-sexpr-mentions (cdar x) vars-fal)
                  (cons (car x) (relevant (cdr x) vars-fal)))
                 (t
                  (relevant (cdr x) vars-fal)))))

  (local (defun irrelevant (x vars-fal)
           (cond ((atom x)
                  nil)
                 ((atom (car x))
                  (irrelevant (cdr x) vars-fal))
                 ((4v-sexpr-mentions (cdar x) vars-fal)
                  (irrelevant (cdr x) vars-fal))
                 (t
                  (cons (car x) (irrelevant (cdr x) vars-fal))))))

  (local
   (defsection 4v-onehot-filter-elim

     (local (defthm l0
              (equal (mv-nth 0 (4v-onehot-filter x vars-fal keep skip))
                     (revappend (relevant x vars-fal) keep))
              :hints(("Goal" :in-theory (enable 4v-onehot-filter)))))

     (local (defthm l1
              (equal (mv-nth 1 (4v-onehot-filter x vars-fal keep skip))
                     (revappend (irrelevant x vars-fal) skip))
              :hints(("Goal" :in-theory (enable 4v-onehot-filter)))))

     (local (defthm l2
              (equal (4v-onehot-filter x vars-fal keep skip)
                     (mv (mv-nth 0 (4v-onehot-filter x vars-fal keep skip))
                         (mv-nth 1 (4v-onehot-filter x vars-fal keep skip))))
              :rule-classes nil
              :hints(("Goal" :in-theory (enable 4v-onehot-filter)))))

     (defthm 4v-onehot-filter-elim
       (equal (4v-onehot-filter x vars-fal nil nil)
              (mv (rev (relevant x vars-fal))
                  (rev (irrelevant x vars-fal))))
       :hints(("Goal" :use ((:instance l2 (keep nil) (skip nil))))))))

  (local (defthm subsetp-equal-of-alist-vals-of-relevant
           (subsetp-equal (alist-vals (relevant x vars-fal))
                          (alist-vals x))))

  (local (defthm subsetp-equal-of-alist-vals-of-irrelevant
           (subsetp-equal (alist-vals (irrelevant x vars-fal))
                          (alist-vals x))))


  (local
   (defthm part3
     ;; This is for the degenerate case where we don't do anything but shrink
     ;; the alist.
     (implies (member-equal k (4v-sexpr-vars-list (alist-vals (hons-shrink-alist sexpr-alist nil))))
              (member-equal k (4v-sexpr-vars-list (alist-vals sexpr-alist))))
     :hints(("Goal"
             :in-theory (disable member-of-4v-sexpr-vars-list-when-subsetp)
             :use ((:instance member-of-4v-sexpr-vars-list-when-subsetp
                              (a (alist-vals (hons-shrink-alist sexpr-alist nil)))
                              (b (alist-vals sexpr-alist))))))))


  (local
   (defthm part2
     ;; This is for the sexprs that we skip instead of rewriting they're
     ;; irrelevant.

     ;; Basic argument: the irrelevant alist vals are a subset of the shrink
     ;; hence k is in the shrink.  then, since the shrink is a subset of the
     ;; whole, k is part of the whole.
     (IMPLIES
      (AND (ATOM-LISTP VARS)
           (MEMBER-EQUAL
            K
            (4V-SEXPR-VARS-LIST
             (ALIST-VALS (IRRELEVANT (HONS-SHRINK-ALIST SEXPR-ALIST NIL)
                                     (PAIRLIS$ VARS NIL)))))
           (NOT (MEMBER-EQUAL K VARS)))
      (MEMBER-EQUAL K
                    (4V-SEXPR-VARS-LIST (ALIST-VALS SEXPR-ALIST))))
     :hints(("Goal"
             :in-theory (disable member-of-4v-sexpr-vars-list-when-subsetp)
             :use ((:instance member-of-4v-sexpr-vars-list-when-subsetp
                              (a (alist-vals (IRRELEVANT (HONS-SHRINK-ALIST SEXPR-ALIST NIL)
                                                         (PAIRLIS$ VARS NIL))))
                              (b (alist-vals (HONS-SHRINK-ALIST SEXPR-ALIST NIL))))
;(:instance member-of-4v-sexpr-vars-list-when-subsetp
;           (a (alist-vals (HONS-SHRINK-ALIST SEXPR-ALIST NIL)))
;           (b (alist-vals sexpr-alist)))
                   )
             :do-not '(generalize fertilize)
             :do-not-induct t))))



  (local (defthm helper-for-part1
           (implies (and (subsetp-equal a (append b c))
                         (member-equal k a)
                         (not (member-equal k b)))
                    (member-equal k c))
           :hints((witness))))


  (local
   (defthm part1
     ;; This is for the sexprs that we actually onehot rewrite. q Basic argument
     ;; is just a chain of subsets.  See the hint.
     (IMPLIES
      (AND
       (ATOM-LISTP VARS)
       (MEMBER-EQUAL
        K
        (4V-SEXPR-VARS-LIST
         (ALIST-VALS (4V-ONEHOT-RW-SEXPR-ALIST-AUX
                      VARS
                      (REV (RELEVANT (HONS-SHRINK-ALIST SEXPR-ALIST NIL)
                                     (PAIRLIS$ VARS NIL)))))))
       (NOT (MEMBER-EQUAL K VARS)))
      (MEMBER-EQUAL K
                    (4V-SEXPR-VARS-LIST (ALIST-VALS SEXPR-ALIST))))
     :hints(("Goal"
             :in-theory (disable member-of-4v-sexpr-vars-list-when-subsetp
                                 4v-sexpr-vars-list-of-4v-onehot-rw-sexpr-alist-aux)
             :use ((:instance 4v-sexpr-vars-list-of-4v-onehot-rw-sexpr-alist-aux
                              (sexpr-alist (REV (RELEVANT (HONS-SHRINK-ALIST SEXPR-ALIST NIL)
                                                          (PAIRLIS$ VARS NIL)))))
                   (:instance member-of-4v-sexpr-vars-list-when-subsetp
                              (a (ALIST-VALS (REV (RELEVANT (HONS-SHRINK-ALIST SEXPR-ALIST NIL)
                                                            (PAIRLIS$ VARS NIL)))))
                              (b (alist-vals (HONS-SHRINK-ALIST SEXPR-ALIST NIL))))
                   ;; (:instance member-of-4v-sexpr-vars-list-when-subsetp
                   ;;            (a (alist-vals (HONS-SHRINK-ALIST SEXPR-ALIST NIL)))
                   ;;            (b (alist-vals sexpr-alist)))
                   )
             :do-not '(generalize fertilize)
             :do-not-induct t))))

  (local
   (defthm main-lemma
     ;; This should boil down to parts 1, 2, and 3.
     (let ((new-alist (4v-onehot-rw-sexpr-alist vars sexpr-alist)))
       (implies (and (atom-listp vars)
                     (member-equal k (4v-sexpr-vars-list (alist-vals new-alist))))
                (member-equal k (append vars (4v-sexpr-vars-list (alist-vals sexpr-alist))))))
     :hints(("Goal"
             :in-theory (enable 4v-onehot-rw-sexpr-alist)
             :do-not '(generalize fertilize)
             :do-not-induct t))))

  (defthm 4v-sexpr-vars-of-4v-onehot-rw-sexpr-alist
    (let ((new-alist (4v-onehot-rw-sexpr-alist vars sexpr-alist)))
      (implies (atom-listp vars)
               (subsetp-equal (4v-sexpr-vars-list (alist-vals new-alist))
                              (append vars (4v-sexpr-vars-list (alist-vals sexpr-alist))))))
    :hints((witness :ruleset subsetp-witnessing))))

