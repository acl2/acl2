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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

; sexpr-vars.lisp
;  - sexpr-vars gathers variables in a sexpr
;  - theorems about the vars after restrict, compose

(in-package "ACL2")
(include-book "sexpr-eval")
(include-book "centaur/misc/hons-alphorder-merge" :dir :system)

(defsection 4v-sexpr-vars
  :parents (4v-sexprs)
  :short "Collect the set of variables in an s-expression."

  :long "<p>@(call 4v-sexpr-vars) is one way to produce a list of all the
variables that occur in the sexpr @('x').</p>

<p><color rgb=\"#ff0000\">WARNING</color>: Variable collection is surprisingly
difficult to do efficiently, and is also <b>often unnecessary</b>.</p>

<p>Before deciding to collect variables, it may be worth considering whether
you really need to compute the <i>exact</i> set of variables for a sexpr.  It
is often possible to efficiently overapproximate the set of all variables,
e.g., if you have just carried out an @(see esim) run, the variables you
assigned to the input and state bits is probably readily available.</p>

<p>You can often use overapproximations in scenarios such as</p>

<ul>
 <li>evaluating sexprs with @(see 4v-sexpr-eval),</li>
 <li>substituting into sexprs with @(see 4v-sexpr-restrict), or</li>
 <li>converting sexprs into faigs with @(see 4v-sexpr-to-faig),</li>
</ul>

<p>because in these cases it is perfectly fine for the alists to include
extraneous bindings for variables that aren't in the sexpr.</p>

<p>Depending on your application, @(see 4v-sexpr-vars-1pass) may be a more
efficient way to collect variables than @('4v-sexpr-vars').</p>

<p>The basic approach taken by @('4v-sexpr-vars') is to</p>

<ul>

<li>@(see memoize) the entire computation to avoid revisiting shared
subexpressions,</li>

<li>produce honsed, ordered variable lists at each node so that merging is
linear, and</li>

<li>memoize the unioning operation @(see hons-alphorder-merge) to avoid
recomputing the same unions.</li>

</ul>

<p>This might be a reasonable strategy when you care about the precise set of
variables for a large number of closely-related sexprs.  However, it is <b>very
memory intensive</b>, and can be very slow unless you are really getting a lot
of reuse out of the variable sets being computed.  Moreover, computing the
precise set of variables for every subexpression may be far more work than you
really need to do, so @(see 4v-sexpr-vars-1pass) might be more appropriate.</p>

<p>See also @(see 4v-nsexpr-vars), which only works when the sexprs involved
have natural-numbered variables, but can use a sparse bitset representation
that generally performs very well.</p>"

  (defxdoc 4v-sexpr-vars-list
    :parents (4v-sexpr-vars)
    :short "Extension of @(see 4v-sexpr-vars) to a sexpr list."

    :long "<p>@(call 4v-sexpr-vars-list) is is the mutually recursive
counterpart of @(see 4v-sexpr-vars).  It is given a list of sexprs, and returns
a single set containing all the variables in these sexprs.</p>")

  (mutual-recursion
   (defun 4v-sexpr-vars (x)
     (declare (xargs :guard t :verify-guards nil))
     (if (atom x)
         (and x
              (mbe :logic (set::insert x nil)
                   :exec (hons x nil)))
       (4v-sexpr-vars-list (cdr x))))

   (defun 4v-sexpr-vars-list (x)
     (declare (xargs :guard t))
     (if (atom x)
         nil
       (mbe :logic (set::union (4v-sexpr-vars (car x))
                                (4v-sexpr-vars-list (cdr x)))
            :exec (hons-alphorder-merge (4v-sexpr-vars (car x))
                                        (4v-sexpr-vars-list (cdr x)))))))

  (defthm-4v-sexpr-flag
    (defthm atom-listp-4v-sexpr-vars
      (atom-listp (4v-sexpr-vars x))
      :flag sexpr)
    (defthm atom-listp-4v-sexpr-vars-list
      (atom-listp (4v-sexpr-vars-list x))
      :flag sexpr-list))

  (defthm-4v-sexpr-flag
    ;; BOZO I don't think we really want :rewrite on these
    (defthm true-listp-4v-sexpr-vars
      (true-listp (4v-sexpr-vars x))
      :flag sexpr
      :rule-classes (:rewrite :type-prescription))
    (defthm true-listp-4v-sexpr-vars-list
      (true-listp (4v-sexpr-vars-list x))
      :flag sexpr-list
      :rule-classes (:rewrite :type-prescription)))

  (defthm-4v-sexpr-flag
    (defthm setp-4v-sexpr-vars
      (set::setp (4v-sexpr-vars x))
      :flag sexpr)
    (defthm setp-4v-sexpr-vars-list
      (set::setp (4v-sexpr-vars-list x))
      :flag sexpr-list))

  (verify-guards 4v-sexpr-vars
    ;; For the hons instead of insert
    :hints(("Goal" :in-theory (enable* (:ruleset set::primitive-rules)))))

  (memoize '4v-sexpr-vars
           :condition '(and (consp x) (consp (cdr x))))

  (defthm not-member-4v-sexpr-vars-lookup-when-not-member-vars-alist-vals
    (implies (not (member-equal k (4v-sexpr-vars-list (alist-vals al))))
             (not (member-equal k (4v-sexpr-vars (cdr (hons-assoc-equal x al))))))
    :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  (defthm-4v-sexpr-flag
    (defthm 4v-sexpr-vars-4v-sexpr-compose
      (implies (not (member-equal v (4v-sexpr-vars-list (alist-vals al))))
               (not (member-equal v (4v-sexpr-vars (4v-sexpr-compose x al)))))
      :flag sexpr)
    (defthm 4v-sexpr-vars-list-4v-sexpr-compose-list
      (implies (not (member-equal v (4v-sexpr-vars-list (alist-vals al))))
               (not (member-equal v (4v-sexpr-vars-list (4v-sexpr-compose-list x al)))))
      :flag sexpr-list))

  (defthm-4v-sexpr-flag
    (defthm 4v-sexpr-vars-4v-sexpr-restrict
      (implies (and (not (member-equal k (4v-sexpr-vars-list (alist-vals al))))
                    (not (and (member-equal k (4v-sexpr-vars x))
                              (not (member-equal k (alist-keys al))))))
               (not (member-equal k (4v-sexpr-vars (4v-sexpr-restrict x al)))))
      :flag sexpr)
    (defthm 4v-sexpr-vars-list-4v-sexpr-restrict-list
      (implies
       (and (not (member-equal k (4v-sexpr-vars-list (alist-vals al))))
            (not (and (member-equal k (4v-sexpr-vars-list x))
                      (not (member-equal k (alist-keys al))))))
       (not (member-equal k (4v-sexpr-vars-list (4v-sexpr-restrict-list x al)))))
      :flag sexpr-list)))



(defsection 4v-sexpr-vars-alist
  :parents (4v-sexpr-vars)
  :short "Extension of @(see 4v-sexpr-vars) to a sexpr alist."

  :long "<p>@(call 4v-sexpr-vars-alist) is given an alist whose values should
be sexprs; it collects the variables and returns them all together as a single
set.</p>"

  (defun 4v-sexpr-vars-alist (x)
    (declare (xargs :guard t))
    (4v-sexpr-vars-list (alist-vals x))))


(defsection 4v-sexpr-vars-list-list
  :parents (4v-sexpr-vars)
  :short "Extension of @(see 4v-sexpr-vars) to a list of sexpr lists."

  (defun 4v-sexpr-vars-list-list (x)
    (declare (xargs :guard t :verify-guards nil))
    (if (atom x)
        nil
      (mbe :logic (set::union (4v-sexpr-vars-list (car x))
                               (4v-sexpr-vars-list-list (cdr x)))
           :exec (hons-alphorder-merge (4v-sexpr-vars-list (car x))
                                       (4v-sexpr-vars-list-list (cdr x))))))

  (defthm atom-listp-of-4v-sexpr-vars-list-list
    (atom-listp (4v-sexpr-vars-list-list x)))

  (defthm setp-of-4v-sexpr-vars-list-list
    (set::setp (4v-sexpr-vars-list-list x)))

  (verify-guards 4v-sexpr-vars-list-list))


(defsection 4v-sexpr-vars-alists
  :parents (4v-sexpr-vars)
  :short "Extension of @(see 4v-sexpr-vars-alists) to a list of sexpr alists."

  (defun 4v-sexpr-vars-alists (x)
    (declare (xargs :guard t :verify-guards nil))
    (if (atom x)
        nil
      (mbe :logic (set::union (4v-sexpr-vars-alist (car x))
                               (4v-sexpr-vars-alists (cdr x)))
           :exec (hons-alphorder-merge (4v-sexpr-vars-alist (car x))
                                       (4v-sexpr-vars-alists (cdr x))))))

  (defthm atom-listp-of-4v-sexpr-vars-alists
    (atom-listp (4v-sexpr-vars-alists x)))

  (defthm setp-of-4v-sexpr-vars-alists
    (set::setp (4v-sexpr-vars-alists x)))

  (verify-guards 4v-sexpr-vars-alists))
