; Base definitions of generic list predicates/projections/etc.
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

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc std/lists/abstract
  :parents (std/lists)
  :short "Abstract theories for listp, projection, and mapappend functions"
  :long "<p>This book defines various generic functions:</p>
<ul>
<li>element-p</li>
<li>element-fix</li>
<li>element-equiv</li>
<li>element-list-p</li>
<li>element-list-fix</li>
<li>element-list-equiv</li>
<li>element-list-projection</li>
<li>element-list-mapappend</li>
</ul>

<p>The idea is that in other books, we can add various theorems about how these
generic functions behave in relation to other functions such as nth, index-of,
member, etc, which we can use in pluggable forms of @(see std::deflist), @(see
std::defprojection), or @(see std::defmapappend).  However, as yet this
functionality is only implemented for @(see std::deflist) (and through @(see
std::deflist), also @(see fty::deflist)).</p>

<p>We'll describe in this documentation how to write theorems that can be
instantiated by @(see std::deflist) so that they can be used for arbitrary
typed lists.  Eventually, this will also apply to @(see std::defprojection) and
@(see std::defmapappend).</p>

<h2>Writing Generic Typed-list Rules</h2>

<h3>Generic Rule Macros</h3>
<p>Deflist creates theorems for each new list type it defines by instantiating
a list of theorems recorded in a table.  To create a new theorem and add it to
that table so that it is available to deflist, use the @(see def-listp-rule)
macro, which is similar to defthm.  There are other such macros for rules about
other kinds of functions as well:</p>

<ul>
<li>@('def-listp-rule') theorems will be instantiated by @(see std::deflist) and @(see fty::deflist)</li>
<li>@('def-listfix-rule') theorems will be instantiated by @(see fty::deflist), pertaining to the list-fix function it introduces</li>
<li>@('def-projection-rule') theorems will be instantiated by @(see std::defprojection)</li>
<li>@('def-mapappend-rule') theorems will be instantiated by @(see std::defmapappend).</li>
</ul>

<p>These macros all take the same basic arguments as @(see defthm) but some
additional keyword arguments as well; the following shows an elaborate example.</p>

@({
  (def-listp-rule element-list-p-when-not-consp-non-true-list
    (implies (and (element-list-final-cdr-p t)
                  (not (consp x)))
             (element-list-p x))
    :hints ((\"goal\" :expand ((element-list-p))))
    :rule-classes :rewrite
    :otf-flg nil
    :requirement (not true-listp)
    :name element-list-p-when-not-consp
    :body (implies (not (consp x))
                   (element-list-p x))
    :inst-rule-classes  ((:rewrite :backchain-limit-lst 2))
    :cheap-rule-classes ((:rewrite :backchain-limit-lst 0))
    :tags (:basic))
 })

<p>To briefly describe the keyword arguments:</p>
<ul>
<li>@(':hints'), @(':rule-classes'), and @(':otf-flg') are the same as in @(see
defthm) and do not affect what is stored for later instantiation</li>
<li>@(':requirement') restricts this rule to only apply to certain kinds of
typed lists; see the section \"Variants and Requirements\" below</li>
<li>@(':name') overrides the theorem name template used by instantiations of
this theorem</li>
<li>@(':body') overrides the theorem body as the template to be used for
instantiations; see the \"Variants and Requirements\" section</li>
<li>@(':inst-rule-classes') overrides the rule-classes used by instantiations
of this theorem</li>
<li>@(':cheap-rule-classes') provide an alternative rule-classes if the option
@(':cheap t') is given to deflist</li>
<li>@(':tags') are freeform annotations of the rules, which can be used to
disable in bulk certain sets of rules from being instantiated.</li>
</ul>

<h3>Variants and Requirements</h3>

<p>Some theorems pertaining to typed lists are best phrased differently when:</p>
<ul>
<li>the list recognizer requires/does not require a NIL final cdr</li>
<li>the list element recognizer is true of/is not true of NIL, or its value on
NIL is unknown or varies with other parameters.</li>
</ul>
<p>The example @('def-listp-rule') form above, here reproduced with irrelevant
parts removed, helps to show how we accommodate these variants:</p>

@({
  (def-listp-rule element-list-p-when-not-consp-non-true-list
    (implies (and (element-list-final-cdr-p t)
                  (not (consp x)))
             (element-list-p x))
    :requirement (not true-listp)
    :name element-list-p-when-not-consp
    :body (implies (not (consp x))
                   (element-list-p x)))
 })

<p>The @(':body') shows the theorem that will be produced by instantiations of
this rule.  However, this is only true when element-list-p is non-strict,
i.e. it allows a non-nil final cdr.  The generic definition of element-list-p
accomodates both strict and non-strict versions by calling a constrained
function @('element-list-final-cdr-p') on its final cdr.  This function is
constrained to either be true on every input, or to only be true on NIL; thus,
it matches the two typical final cdr behaviors of list recognizers.  To prove
that any non-cons is element-list-p, we need to assume we are in the non-strict
case -- where @('element-list-final-cdr-p') is true of every input -- which, by
its constraint, is true iff @('(element-list-final-cdr-p t)').  To avoid
instantiating this rule on typed lists that are strict, we add the
@(':requirement') field.  In @('std::deflist'), before instantiating a rule,
the @(':requirement') field is evaluated with variables such as @('true-listp')
bound to values based on the particular variant.  Finally, the @(':name') field
lets us consistently name the instantiated theorems when there are different
variants; e.g., for the strict case, we can have this other form that produces
a different theorem but uses the same naming convention:</p>

@({
  (def-listp-rule element-list-p-when-not-consp-true-list
    (implies (and (not (element-list-final-cdr-p t))
                  (not (consp x)))
             (equal (element-list-p x) (not x)))
    :requirement true-listp
    :name element-list-p-when-not-consp
    :body (implies (not (consp x))
                   (equal (element-list-p x)
                          (not x))))
 })

<h3>List of requirement variables recognized by @(see std::deflist)</h3>
<p>Note: All of these are symbols in the ACL2 package.</p>
<ul>
<li>@('element-p-of-nil') is true if NIL is known to be an element</li>
<li>@('not-element-p-of-nil') is true if NIL is known not to be an element.
Note: mutually exclusive with @('element-p-of-nil'), but both may be false in
cases where the status of NIL as an element is unknown or depends on other
input parameters.</li>
<li>@('negatedp') is true if we are creating a list that recognizes elements
defined by @('NOT') of some predicate, which may affect the correct formulation
of rewrite rules</li>
<li>@('true-listp') is true if the list recognizer is strict, i.e., implies true-listp</li>
<li>@('single-var') is true if the list recognizer has no parameters other than the list variable</li>
<li>@('cheap') is true if the user gave an extra option requesting cheaper versions of some rules.</li>
<li>@('simple') is true if the element recognizer is a simple function, rather
than some more complicated term.</li>
</ul>

<h3>Using Tags to Disable Instantiation</h3>

<p>Certain generic rules are tagged so as to group them with other rules.  For
example, all the rules defined in \"std/osets/element-list.lisp\" are tagged
with @(':osets').  This makes it easy to turn these rules off so that a
subsequent deflist form will not instantiate this set of rules.  This form does
that:</p>
@({
  (local (ruletable-delete-tags! acl2::listp-rules (:osets)))
 })

<p>On the other hand, in the unlikely event that you only wanted the rules
tagged with @(':osets') you could do:</p>
@({
  (local (ruletable-keep-tags! acl2::listp-rules (:osets)))
 })

")

(local (set-default-parents std/lists/abstract))



(defsection element-p
  :short "Generic typed list element recognizer."
  ;; Elementp functions for defining various types of list recognizers, with fixing functions.
  (encapsulate (((element-p *) => *)
                ((element-example) => *))

    (local (defun element-p (x) (natp x)))
    (local (defun element-example () 0)))

  (encapsulate
    (((non-element-p *) => *))
    (local (defun non-element-p (x)
             ;; Rewriting target for when element-p is (not (foo-p x))
             (not (element-p x))))
    (defthm non-element-p-def
      (iff (non-element-p x)
           (not (element-p x))))))



(defsection element-fix
  :short "Generic fixing function for typed list elements."

  (encapsulate (((element-fix *) => *))

    (local (defun element-fix (x)
             (if (element-p x) x (element-example))))

    (defthm element-p-of-element-fix
      (implies (element-p (element-example))
               (element-p (element-fix x))))

    (defthm element-fix-when-element-p
      (implies (element-p x)
               (equal (element-fix x) x)))

    (defthm element-fix-idempotent
      (equal (element-fix (element-fix x))
             (element-fix x)))))

(defsection element-equiv
  :short "Generic equivalence relation among typed list elements."

  ;; (fty::deffixtype element :pred element-p :fix element-fix
  ;;   :equiv element-equiv :define t :forward t)
  (defun element-equiv (x y)
    (declare (xargs :verify-guards nil))
    (equal (element-fix x) (element-fix y)))

  (defequiv element-equiv)

  (defcong element-equiv equal (element-fix x) 1)

  (defthm element-fix-under-element-equiv
    (element-equiv (element-fix x) x))

  (defthm equal-of-element-fix-1-forward-to-element-equiv
    (implies (equal (element-fix x) y)
             (element-equiv x y))
    :rule-classes :forward-chaining)

  (defthm equal-of-element-fix-2-forward-to-element-equiv
    (implies (equal x (element-fix y))
             (element-equiv x y))
    :rule-classes :forward-chaining)

  (defthm element-equiv-of-element-fix-1-forward
    (implies (element-equiv (element-fix x) y)
             (element-equiv x y))
    :rule-classes :forward-chaining)

  (defthm element-equiv-of-element-fix-2-forward
    (implies (element-equiv x (element-fix y))
             (element-equiv x y))
    :rule-classes :forward-chaining))

(encapsulate
  (((element-list-final-cdr-p *) => *))

  (local (defun element-list-final-cdr-p (x)
           (not x)))

  (defthm element-list-final-cdr-p-of-nil
    (element-list-final-cdr-p nil))

  (defthm element-list-final-cdr-p-type
    (or (equal (element-list-final-cdr-p x) t)
        (equal (element-list-final-cdr-p x) nil))
    :rule-classes :type-prescription)

  (defthm element-list-final-cdr-p-rewrite
    (implies (syntaxp (and (not (equal x ''t))
                           (not (equal x ''nil))))
             (equal (element-list-final-cdr-p x)
                    (or (equal x nil)
                        (element-list-final-cdr-p t))))))




;; Listp-rules table (and projection-rule table, etc) format:
;; each entry is:
;; generic-rule-name . t
;;   to denote straightforward instantiation with the same rule classes, no restrictions
;; generic-rule-name alist
;;   where alist may bind keys:
;;     :requirement :name :body :rule-classes
;;     to denote that you instantiate generic-rule-name to prove the theorem, as
;;     long as requirement-list is satisfied.
;; The following macros only support the straightforward form.

(defmacro def-generic-rule (tablename thmname thm
                                      &key
                                      (name 'nil name-p)
                                      (body 'nil body-p)
                                      disable
                                      (requirement 'nil requirement-p)
                                      (inst-rule-classes 'nil inst-rule-classes-p)
                                      (cheap-rule-classes 'nil cheap-rule-classes-p)
                                      (rule-classes ':rewrite)
                                      tags
                                      hints
                                      otf-flg)
  `(progn (defthm ,thmname ,thm :hints ,hints :rule-classes ,rule-classes :otf-flg ,otf-flg)
          (table ,tablename ',thmname
                 (or '(,@(and name-p `((:name ,name)))
                       ,@(and body-p `((:body ,body)))
                       ,@(and disable `((:disable t)))
                       ,@(and requirement-p `((:requirement ,requirement)))
                       ,@(and inst-rule-classes-p `((:rule-classes ,inst-rule-classes)))
                       ,@(and cheap-rule-classes-p `((:cheap-rule-classes ,cheap-rule-classes)))
                       ,@(and tags `((:tags . ,tags))))
                     t))))

(defun ruletable-delete-tags (tags table)
  (if (atom table)
      nil
    (if (and (consp (cdar table))
             (intersectp-eq tags (cdr (assoc :tags (cdar table)))))
        (ruletable-delete-tags tags (cdr table))
      (cons (car table) (ruletable-delete-tags tags (cdr table))))))

(defmacro ruletable-delete-tags! (table-name tags)
  `(table ,table-name nil (ruletable-delete-tags
                           ',tags (table-alist ',table-name world))
          :clear))

(defun ruletable-keep-tags (tags table)
  (if (atom table)
      nil
    (if (and (consp (cdar table))
             (intersectp-eq tags (cdr (assoc :tags (cdar table)))))
        (cons (car table) (ruletable-keep-tags tags (cdr table)))
      (ruletable-keep-tags tags (cdr table)))))

(defmacro ruletable-keep-tags! (table-name tags)
  `(table ,table-name nil (ruletable-keep-tags
                           ',tags (table-alist ',table-name world))
          :clear))


(defsection def-projection-rule
  :short "Define a theorem and save it in a table, denoting that it is a rule
about elementlist-projection."
  (defmacro def-projection-rule (&rest args)
    `(def-generic-rule projection-rules . ,args)))

(defsection def-listp-rule
  :short "Define a theorem and save it in a table, denoting that it is a rule
about element-list-p."
  (defmacro def-listp-rule (&rest args)
    `(def-generic-rule listp-rules . ,args)))

(defsection def-nonempty-listp-rule
  :short "Define a theorem and save it in a table, denoting that it is a rule
about element-list-nonempty-p."
  (defmacro def-nonempty-listp-rule (&rest args)
    `(def-generic-rule nonempty-listp-rules . ,args)))

(defsection def-listfix-rule
  :short "Define a theorem and save it in a table, denoting that it is a rule
about element-list-fix."
  (defmacro def-listfix-rule (&rest args)
    `(def-generic-rule listfix-rules . ,args)))

(defsection def-mapappend-rule
  :short "Define a theorem and save it in a table, denoting that it is a rule
about elementlist-mapappend."
  (defmacro def-mapappend-rule (&rest args)
    `(def-generic-rule mapappend-rules . ,args)))


(defsection element-list-p
  :short "Generic typed list recognizer function."

  (defun element-list-p (x)
    (if (atom x)
        (element-list-final-cdr-p x)
      (and (element-p (car x))
           (element-list-p (cdr x)))))

  (in-theory (disable (element-list-p)))

  (def-listp-rule element-list-p-of-cons
    (equal (element-list-p (cons a x))
           (and (element-p a) (element-list-p x))))

  (def-listp-rule element-list-p-of-cdr-when-element-list-p
    (implies (element-list-p (double-rewrite x))
             (element-list-p (cdr x))))

  (def-listp-rule element-list-p-when-not-consp-non-true-list
    (implies (and (element-list-final-cdr-p t)
                  (not (consp x)))
             (element-list-p x))

    :requirement (not true-listp)
    :name element-list-p-when-not-consp
    :body (implies (not (consp x))
                   (element-list-p x))
    ;; :rule-classes ((:rewrite :backchain-limit-lst 0))
    )

  (def-listp-rule element-list-p-when-not-consp-true-list
    (implies (and (not (element-list-final-cdr-p t))
                  (not (consp x)))
             (equal (element-list-p x) (not x)))
    :requirement true-listp
    :name element-list-p-when-not-consp
    :body (implies (not (consp x))
                   (equal (element-list-p x)
                          (not x)))
    ;; (:rule-classes ((:rewrite :backchain-limit-lst 0)))
    )



  (def-listp-rule element-p-of-car-when-element-list-p-when-element-p-nil
    (implies (and (element-p nil)
                  (element-list-p x))
             (element-p (car x)))
    :requirement (and element-p-of-nil simple)
    :name element-p-of-car-when-element-list-p
    :body (implies (element-list-p x)
                   (element-p (car x)))
    :cheap-rule-classes ((:rewrite :backchain-limit-lst 0)))

  (def-listp-rule element-p-of-car-when-element-list-p-when-not-element-p-nil-and-not-negated
    (implies (and (not (element-p nil))
                  (element-list-p x))
             (iff (element-p (car x))
                  (consp x)))
    :requirement (and not-element-p-of-nil
                      (not negatedp)
                      simple)
    :name element-p-of-car-when-element-list-p
    :body (implies (element-list-p x)
                   (iff (element-p (car x))
                        (consp x)))
    :cheap-rule-classes ((:rewrite :backchain-limit-lst 0)))

  (def-listp-rule element-p-of-car-when-element-list-p-when-not-element-p-nil-and-negated
    (implies (and (not (element-p nil))
                  (element-list-p x))
             (iff (non-element-p (car x))
                  (not (consp x))))
    :requirement (and not-element-p-of-nil
                      negatedp
                      simple)
    :name element-p-of-car-when-element-list-p
    :body (implies (element-list-p x)
                   (iff (non-element-p (car x))
                        (not (consp x))))
    :cheap-rule-classes ((:rewrite :backchain-limit-lst 0)))

  (def-listp-rule element-p-of-car-when-element-list-p-when-unknown-nil
    (implies (element-list-p x)
             (iff (element-p (car x))
                  (or (consp x)
                      (element-p nil))))
    :requirement (and (not element-p-of-nil)
                      (not not-element-p-of-nil)
                      (not negatedp)
                      simple)
    :name element-p-of-car-when-element-list-p
    :body (implies (element-list-p x)
                   (iff (element-p (car x))
                        (or (consp x)
                            (element-p nil))))
    :cheap-rule-classes ((:rewrite :backchain-limit-lst 0)))

  (def-listp-rule element-p-of-car-when-element-list-p-when-unknown-nil-negated
    (implies (element-list-p x)
             (iff (non-element-p (car x))
                  (and (not (consp x))
                       (non-element-p nil))))
    ;; :rule-classes ((:rewrite :backchain-limit-lst (0 nil)))

    :requirement (and (not element-p-of-nil)
                      (not not-element-p-of-nil)
                      negatedp
                      simple)
    :name element-p-of-car-when-element-list-p
    :body (implies (element-list-p x)
                   (iff (non-element-p (car x))
                        (and (not (consp x))
                             (non-element-p nil))))
    :cheap-rule-classes ((:rewrite :backchain-limit-lst 0)))

  (def-listp-rule true-listp-when-element-list-p-rewrite
    (implies (and (element-list-p x)
                  (not (element-list-final-cdr-p t)))
             (true-listp x))
    :name true-listp-when-element-list-p
    :requirement (and true-listp (not single-var))
    :body (implies (element-list-p x)
                   (true-listp x))
    :cheap-rule-classes ((:rewrite :backchain-limit-lst 0)))

  (def-listp-rule true-listp-when-element-list-p-compound-recognizer
    (implies (and (element-list-p x)
                  (not (element-list-final-cdr-p t)))
             (true-listp x))
    :rule-classes nil
    ;; NOTE: above should be a compound-recognizer.  We record that in the table
    ;; specially.
    :name true-listp-when-element-list-p
    :requirement (and true-listp single-var)
    :body (implies (element-list-p x)
                   (true-listp x))
    :inst-rule-classes :compound-recognizer)


  (def-listp-rule element-list-p-of-append-non-true-list
    (implies (element-list-final-cdr-p t)
             (equal (element-list-p (append a b))
                    (and (element-list-p a)
                         (element-list-p b))))
    :requirement (not true-listp)
    :name element-list-p-of-append
    :body (equal (element-list-p (append a b))
                 (and (element-list-p a)
                      (element-list-p b)))))

(defsection element-list-nonempty-p
  :short "Generic typed list recognizer function."

  (defun element-list-nonempty-p (x)
    (and (consp x)
         (element-p (car x))
         (let ((x (cdr x)))
           (if (consp x)
               (element-list-nonempty-p x)
             (element-list-final-cdr-p x)))))

  (in-theory (disable (element-list-nonempty-p)))

  (def-nonempty-listp-rule element-list-nonempty-p-of-cons
    (implies  (element-list-nonempty-p x)
              (iff (element-list-nonempty-p (cons a x))
                   (element-p a))))

  (def-nonempty-listp-rule element-list-nonempty-p-of-singleton-true-list
    (iff (element-list-nonempty-p (cons a nil))
         (element-p a))
    :requirement true-listp
    :name element-list-nonempty-p-of-singleton)

  (def-nonempty-listp-rule element-list-nonempty-p-of-singleton-non-true-list
    (implies (and (not (consp x))
                  (element-list-final-cdr-p t))
             (iff (element-list-nonempty-p (cons a x))
                  (element-p a)))
    :requirement (not true-listp)
    :name element-list-nonempty-p-of-singleton
    :body (implies (not (consp x))
                   (iff (element-list-nonempty-p (cons a x))
                        (element-p a))))

  (def-nonempty-listp-rule element-list-nonempty-p-of-cdr-when-element-list-nonempty-p
    (implies (and (element-list-nonempty-p (double-rewrite x))
                  (consp (cdr x)))
             (element-list-nonempty-p (cdr x))))

  (def-nonempty-listp-rule element-list-nonempty-p-when-not-consp
    (implies (not (consp x))
             (not (element-list-nonempty-p x))))

  (def-nonempty-listp-rule element-list-nonempty-p-implies-consp
    (implies (element-list-nonempty-p x)
             (consp x))
    :rule-classes :forward-chaining)

  (def-nonempty-listp-rule element-p-of-car-when-element-list-nonempty-p
    (implies (element-list-nonempty-p x)
             (element-p (car x)))
    :requirement simple
    :name element-p-of-car-when-element-list-nonempty-p
    :body (implies (element-list-nonempty-p x)
                   (element-p (car x)))
    :cheap-rule-classes ((:rewrite :backchain-limit-lst 0)))


  (def-nonempty-listp-rule true-listp-when-element-list-nonempty-p-rewrite
    (implies (and (element-list-nonempty-p x)
                  (not (element-list-final-cdr-p t)))
             (true-listp x))
    :rule-classes nil
    :name true-listp-when-element-list-nonempty-p
    :requirement (and true-listp (not single-var))
    :body (implies (element-list-nonempty-p x)
                   (true-listp x))
    :inst-rule-classes :rewrite
    :cheap-rule-classes ((:rewrite :backchain-limit-lst 0)))

  (def-nonempty-listp-rule true-listp-when-element-list-nonempty-p-compound-recognizer
    (implies (and (element-list-nonempty-p x)
                  (not (element-list-final-cdr-p t)))
             (true-listp x))
    :rule-classes nil
    ;; NOTE: above should be a compound-recognizer.  We record that in the table
    ;; specially.
    :name true-listp-when-element-list-nonempty-p
    :requirement (and true-listp single-var)
    :body (implies (element-list-nonempty-p x)
                   (true-listp x))
    :inst-rule-classes :compound-recognizer)


  (def-nonempty-listp-rule element-list-nonempty-p-of-append
    (implies (and (element-list-nonempty-p a)
                  (element-list-nonempty-p b))
             (element-list-nonempty-p (append a b)))))



(defsection element-list-fix
  :short "Generic typed list fixing function."
  (defun element-list-fix (x)
    (if (atom x)
        (and (element-list-final-cdr-p t) x)
      (cons (element-fix (car x))
            (element-list-fix (cdr x)))))

  (in-theory (disable (element-list-fix)))

  (def-listfix-rule element-list-p-of-element-list-fix
    (implies (element-p (element-example))
             (element-list-p (element-list-fix x)))
    :body (element-list-p (element-list-fix x)))

  (def-listfix-rule element-list-fix-when-element-list-p
    (implies (element-list-p x)
             (equal (element-list-fix x) x)))

  (def-listfix-rule consp-of-element-list-fix
    (equal (consp (element-list-fix x))
           (consp x)))

  (def-listfix-rule element-list-fix-of-cons
    (equal (element-list-fix (cons a x))
           (cons (element-fix a)
                 (element-list-fix x))))

  (def-listfix-rule len-of-element-list-fix
    (equal (len (element-list-fix x))
           (len x)))

  (def-listfix-rule element-fix-of-append
    (equal (element-list-fix (append a b))
           (append (element-list-fix a)
                   (element-list-fix b)))))


(defsection element-list-equiv
  :short "Generic typed list equivalence relation"
  (defun element-list-equiv (x y)
    (declare (xargs :verify-guards nil))
    (equal (element-list-fix x)
           (element-list-fix y)))

  (defequiv element-list-equiv)
  (table listfix-rules 'element-list-equiv t)
  (defcong element-list-equiv equal (element-list-fix x) 1)
  (table listfix-rules 'element-list-equiv-implies-equal-element-list-fix-1 t)
  (def-listfix-rule element-list-fix-under-element-list-equiv
    (element-list-equiv (element-list-fix x)
                        x))

  (def-listfix-rule equal-of-element-list-fix-1-forward-to-element-list-equiv
    (implies (equal (element-list-fix x) y)
             (element-list-equiv x y))
    :rule-classes :forward-chaining)
  (def-listfix-rule equal-of-element-list-fix-2-forward-to-element-list-equiv
    (implies (equal x (element-list-fix y))
             (element-list-equiv x y))
    :rule-classes :forward-chaining)
  (def-listfix-rule element-list-equiv-of-element-list-fix-1-forward
    (implies (element-list-equiv (element-list-fix x)
                                 y)
             (element-list-equiv x y))
    :rule-classes :forward-chaining)
  (def-listfix-rule element-list-equiv-of-element-list-fix-2-forward
    (implies (element-list-equiv x (element-list-fix y))
             (element-list-equiv x y))
    :rule-classes :forward-chaining)

  (defcong element-list-equiv element-equiv (car x) 1)
  (table listfix-rules 'element-list-equiv-implies-element-equiv-car-1 t)
  (defcong element-list-equiv element-list-equiv (cdr x) 1)
  (table listfix-rules 'element-list-equiv-implies-element-list-equiv-cdr-1 t)
  (defcong element-equiv element-list-equiv (cons x y) 1)
  (table listfix-rules 'element-equiv-implies-element-list-equiv-cons-1 t)
  (defcong element-list-equiv element-list-equiv (cons x y) 2)
  (table listfix-rules 'element-list-equiv-implies-element-list-equiv-cons-2 t))



;; Another element type, for projections/mapappends
(defsection outelement-p
  :short "Generic recognizer for the output element type of a projection."
  (encapsulate
    (((outelement-p *) => *)
     ((outelement-example) => *))

    (local (defun outelement-p (x) (natp x)))
    (local (defun outelement-example () 0))

    (defthm outelement-p-of-outelement-example
      (outelement-p (outelement-example)))))

(encapsulate
  (((outelement-list-final-cdr-p *) => *))

  (local (defun outelement-list-final-cdr-p (x)
           (not x)))

  (defthm outelement-list-final-cdr-p-of-nil
    (outelement-list-final-cdr-p nil))

  (defthm outelement-list-final-cdr-p-type
    (or (equal (outelement-list-final-cdr-p x) t)
        (equal (outelement-list-final-cdr-p x) nil))
    :rule-classes :type-prescription)

  (defthm outelement-list-final-cdr-p-rewrite
    (implies (syntaxp (and (not (equal x ''t))
                           (not (equal x ''nil))))
             (equal (outelement-list-final-cdr-p x)
                    (or (equal x nil)
                        (outelement-list-final-cdr-p t))))))

(defsection outelement-list-p
  :short "Generic recognizer for the output list type of a projection."

  (defun outelement-list-p (x)
    (if (atom x)
        (outelement-list-final-cdr-p x)
      (and (outelement-p (car x))
           (outelement-list-p (cdr x)))))

  (in-theory (disable (outelement-list-p)))

  (defthm outelement-list-p-of-append
    (implies (and (outelement-list-p x)
                  (outelement-list-p y))
             (outelement-list-p (append x y)))))


(defsection element-xformer
  :short "Generic transform to be projected over a typed list."
  (encapsulate (((element-xformer *) => *))

    (local (defun element-xformer (x)
             (declare (ignore x))
             (outelement-example)))

    (defthm outelement-p-of-element-xformer
      (implies (element-p x)
               (outelement-p (element-xformer x))))))


(defsection elementlist-projection
  :short "Generic projection over a typed list."
  (defun elementlist-projection (x)
    (if (atom x)
        nil
      (cons (element-xformer (car x))
            (elementlist-projection (cdr x)))))

  (def-projection-rule outelement-list-p-of-elementlist-projection
    (implies (element-list-p x)
             (outelement-list-p (elementlist-projection x)))
    :requirement resulttype)

  (def-projection-rule elementlist-projection-of-cons
    (equal (elementlist-projection (cons a b))
           (cons (element-xformer a)
                 (elementlist-projection b))))

  (def-projection-rule elementlist-projection-when-not-consp
    (implies (not (consp x))
             (equal (elementlist-projection x) nil)))

  (def-projection-rule true-listp-of-elementlist-projection
    (true-listp (elementlist-projection x))
    :rule-classes :type-prescription
    ;; hack: acl2 inserts :typed-term in rule-classes which screws us up
    :inst-rule-classes :type-prescription)

  (def-projection-rule len-of-elementlist-projection
    (equal (len (elementlist-projection x))
           (len x)))

  (def-projection-rule consp-of-elementlist-projection
    (equal (consp (elementlist-projection x))
           (consp x)))

  (def-projection-rule elementlist-projection-under-iff
    (iff (elementlist-projection x) (consp x)))

  (def-projection-rule car-of-elementlist-projection-when-nil-preservingp
    (implies (equal nil (element-xformer nil))
             (equal (car (elementlist-projection x))
                    (element-xformer (car x))))

    :requirement nil-preservingp
    :name car-of-elementlist-projection
    :body (equal (car (elementlist-projection x))
                 (element-xformer (car x))))

  (def-projection-rule car-of-elementlist-projection
    (equal (car (elementlist-projection x))
           (and (consp x)
                (element-xformer (car x))))
    :requirement (not nil-preservingp))

  (def-projection-rule cdr-of-elementlist-projection
    (equal (cdr (elementlist-projection x))
           (elementlist-projection (cdr x))))

  (def-projection-rule elementlist-projection-of-append
    (equal (elementlist-projection (append a b))
           (append (elementlist-projection a)
                   (elementlist-projection b)))))

;; list-fix
;; rev
;; revappend
;; take (nil-preserving)
;; nthcdr
;; member-of-xformer-in-projection
;; subsetp-of-projection-in-projection
;; nth-of-projection
;;

(defsection element-listxformer
  :short "Generic element-list transform for mapappend"

  (encapsulate (((element-listxformer *) => *))

    (local (defun element-listxformer (x)
             (declare (ignore x))
             (list (outelement-example))))

    (defthm outelement-list-p-of-element-listxformer
      (implies (element-p x)
               (outelement-list-p (element-listxformer x))))))


(defsection elementlist-mapappend
  :short "Generic mapappend over a typed list."
  (defun elementlist-mapappend (x)
    (if (atom x)
        nil
      (append (element-listxformer (car x))
              (elementlist-mapappend (cdr x)))))

  (def-mapappend-rule outelement-list-p-of-elementlist-mapappend
    (implies (element-list-p x)
             (outelement-list-p (elementlist-mapappend x)))
    :requirement resulttype)

  (def-mapappend-rule elementlist-mapappend-of-cons
    (equal (elementlist-mapappend (cons a b))
           (append (element-listxformer a)
                   (elementlist-mapappend b))))

  (def-mapappend-rule elementlist-mapappend-when-not-consp
    (implies (not (consp x))
             (equal (elementlist-mapappend x) nil)))

  (def-mapappend-rule elementlist-mapappend-of-append
    (equal (elementlist-mapappend (append a b))
           (append (elementlist-mapappend a)
                   (elementlist-mapappend b)))))


(in-theory (disable true-listp-when-element-list-p-rewrite))
