; VL Verilog Toolkit
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "expr-tools")
(local (include-book "../util/arithmetic"))


; STATEMENT TOOLS - Basic functions and theorems for working with statements.

(defthm vl-stmt-p-when-neither-atomic-nor-compound
  (implies (and (not (vl-atomicstmt-p x))
                (not (vl-compoundstmt-p x)))
           (not (vl-stmt-p x)))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable vl-stmt-p))))


(defthm vl-atomicstmt-p-of-vl-compoundstmt
  (not (vl-atomicstmt-p (vl-compoundstmt type exprs stmts name decls
                                         ctrl sequentialp casetype atts)))
  :hints(("Goal"
          :in-theory (disable tag-of-vl-compoundstmt)
          :use ((:instance tag-of-vl-compoundstmt)))))


(defsection vl-compoundstmt-basic-checksp-of-change-vl-compoundstmt
  :parents (vl-compoundstmt-p
            vl-compoundstmt-basic-checksp)

  :short "An important theorem for proving that altered statements still
satisfy @(see vl-compoundstmt-basic-checksp)."

  :autodoc nil

  :long "<p>This weird theorem requires some explanation.  It looks quite
complicated, but is actually pretty cool.  First off, here is the theorem:</p>

@(thm vl-compoundstmt-basic-checksp-of-change-vl-compoundstmt)

<p>What is this for?  The \"basic checks\" on compound statements are quite
complicated and elaborate; see @(see vl-compoundstmt-basic-checksp).  qBut many
transformations, such as substituting into statements, deciding signs and
widths, and so on, don't need to do anything except change all of the
expressions throughout a statement.  Such a transformation only wants to
recursively go into the expressions, sub-statements, declarations, etc., modify
them, and throw them back together.</p>

<p>Ultimately, such a transform ends up writing something like this:</p>

@({
 (change-vl-compoundstmt x
                         :exprs new-exprs
                         :stmts new-stmts
                         ...)
})

<p>The problem is: how can we show this produces a valid compound statement?
Well, the change macro expands to something like:</p>

@({
 (vl-compoundstmt (vl-compoundstmt->type x)
                  new-exprs
                  new-stmts
                  ...)
})

<p>To show that this thing is a vl-compoundstmt-p, we need to appeal to the
following theorem:</p>

@(thm vl-compoundstmt-p-of-vl-compoundstmt)

<p>It's generally straightforward to establish all of these hyps except for</p>

@({
 (vl-compoundstmt-basic-checksp type exprs stmts name decls ctrl)
})

<p>This is where our funny theorem comes in.  Although the basic checks are
rather elaborate, they only really care about</p>

<ul>
<li>whether there is a name and a control,</li>
<li>how many statements and expressions there are,</li>
<li>whether the declarations are empty or not</li>
</ul>

<p>As long as a transform maintains these things, our funny theorem will allow
us to show that the basic checks are satisfied after the transform is carried
out, so that we do not have to think about the specifics of the basic checks
any more deeply than this.  Here once again is the theorem:</p>

@(thm vl-compoundstmt-basic-checksp-of-change-vl-compoundstmt)

<p>The forcing here is perhaps overly aggressive, but we think it is usually
the rule you want unless you are doing something very sophisticated anyway, in
which case you should just turn off this rule and do what you want.</p>

<p>Using @('(vl-compoundstmt->type x)') here in the left-hand side, instead
of @('new-type') or something, is neat for two reasons.</p>

<p>First, when we match the target term, we get a binding for @('x') instead of
having to deal with a free variable or something.  Furthermore, since we're
running @('(vl-compoundstmt->type x)'), it should be the case that @('x')
really is a compound statement, reducing the chance of inappropriate
forcing.</p>

<p>Second, if the user is doing something sophisticated for particular types,
this rule probably won't match.  But that's <b>good</b>!  The rule is probably
too aggressive for such cases.  On the other hand, when the user really is
using @('(change-vl-compoundstmt x ...)') and doesn't change the type, then
this rule will match, and that's probably when the rule is appropriate.</p>

<p>For the other slots, we match anything.  Note that these new-foo variables
are <b>not</b> free: these are the new values that are being put into the new
compound-stmt begin formed.</p>"

  (defthm vl-compoundstmt-basic-checksp-of-change-vl-compoundstmt
    (implies
     (and (force (vl-compoundstmt-p x))
          (force (iff (double-rewrite new-name)  (vl-compoundstmt->name x)))
          (force (iff (double-rewrite new-ctrl)  (vl-compoundstmt->ctrl x)))
          (force (equal new-sequentialp          (vl-compoundstmt->sequentialp x)))
          (force (equal new-casetype             (vl-compoundstmt->casetype x)))
          (force (equal (consp new-decls) (consp (vl-compoundstmt->decls x))))
          (force (equal (len (double-rewrite new-stmts))
                        (len (vl-compoundstmt->stmts x))))
          (force (equal (len (double-rewrite new-exprs))
                        (len (vl-compoundstmt->exprs x)))))
     (vl-compoundstmt-basic-checksp (vl-compoundstmt->type x)
                                    new-exprs new-stmts new-name new-decls
                                    new-ctrl new-sequentialp new-casetype))
    :hints(("Goal"
            :use ((:instance vl-compoundstmt-basic-checksp-of-vl-compoundstmt))
            :in-theory (e/d (vl-compoundstmt-basic-checksp)
                            (vl-compoundstmt-basic-checksp-of-vl-compoundstmt))))))


; Ugh, the relationship between len and consp is really a pain in the ass.

(local
 (defthm slow-consp-by-len
   ;; Disadvantage: potentially very expensive.  Advantage: no free variables
   ;; means we can really backchain and find out if we know something about
   ;; (len x).
   (implies (not (zp (len x)))
            (consp x))))

(local
 (defthm len-of-cdr
   ;; Disadvantage: very strange.  Advantage: no free vars, figures out that
   ;; (len (cdr x)) is 1 when (len x) is known to be 2.
   (implies (not (zp (len x)))
            (equal (len (cdr x))
                   (1- (len x))))))

(local (defthm consp-when-vl-expr-p-rw
         ;; Could be too expensive in general
         (implies (vl-expr-p x)
                  (consp x))))

(local (defthm consp-when-vl-stmt-p-rw
         ;; Could be too expensive in general
         (implies (vl-stmt-p x)
                  (consp x))))

(local
 ;; BOZO do we want this thing?  What do we want our normal form to be?
 (in-theory (disable vl-compoundstmt-p-when-not-vl-atomicstmt-p)))



;               SUPPORTING OPERATIONS FOR EACH STATEMENT TYPE
;
; This rest of this file is ugly and really bulky.  We're basically doing what
; defaggregate would have done for us, if only we didn't need to worry about
; the mutual recursion and so on.
;
; I think this really isn't too terrible.  Yes it's a lot of code, and it's all
; completely boilerplate.  But the benefit is that you can choose to work with
; statements either
;
;   1. using these abstractions, which is generally appropriate when you are
;      doing specific-statement things (e.g., statement rewriting), or
;
;   2. using the unified representation, which is generally okay when you want
;      to do stuff to all statements (e.g., gathering names, sizing
;      expressions, substituting, etc.)
;
; And, e.g., for case statements, the custom accessors really do give us a much
; nicer interface that should be a lot less error-prone.


(defmacro vl-emulate-defaggregate-stuff (name fields)
  ;; Introduces defaggregate-like functions for statement stuff, e.g., for
  ;; if statements this gives us
  ;;  - (make-vl-ifstmt ...)
  ;;  - (change-vl-ifstmt ...)
  ;;  - a b* (vl-ifstmt x) binder
  ;; I don't bother with make-honsed-vl-ifstmt, but we could add that easily
  ;; enough, if desired...
  `(progn
     ,(cutil::da-make-maker-fn name fields)
     ,(cutil::da-make-maker name fields)
     ,(cutil::da-make-changer-fn name fields)
     ,(cutil::da-make-changer name fields)
     ,(cutil::da-make-binder name fields)))



(defsection if-statements
  :parents (vl-stmt-p)
  :short "Utilities for manipulating @('if') statements."

  :long "<p>These functions allow you to conveniently construct and access
parts of @('if') statements without needing to know the details of their
representation.</p>

<h4>General Form:</h4>

@({
if (<condition>)
   <truebranch>
else
   <falsebranch>
})"

  (definline vl-ifstmt-p (x)
    ;; Note: we leave this enabled and allow compoundstmt->type to open up.
    (declare (xargs :guard (vl-stmt-p x)))
    (and (vl-fast-compoundstmt-p x)
         (eq (vl-compoundstmt->type x) :vl-ifstmt)))

  (defthmd vl-compoundstmt-parts-when-vl-ifstmt
    ;; Just the natural consequence of basic-checks for if statements.
    ;; Note that we ordinarily leave this disabled.
    (implies (vl-ifstmt-p x)
             (and (not (vl-compoundstmt->name x))
                  (not (vl-compoundstmt->ctrl x))
                  (not (vl-compoundstmt->sequentialp x))
                  (not (vl-compoundstmt->casetype x))
                  (atom (vl-compoundstmt->decls x))
                  (equal (len (vl-compoundstmt->exprs x)) 1)
                  (equal (len (vl-compoundstmt->stmts x)) 2)))
    :hints(("Goal"
            :use ((:instance vl-compoundstmt-basic-checksp-of-vl-compoundstmt))
            :in-theory (e/d (vl-compoundstmt-basic-checksp)
                            (vl-compoundstmt-basic-checksp-of-vl-compoundstmt)))))

  (local (in-theory (enable vl-compoundstmt-parts-when-vl-ifstmt
                            vl-compoundstmt-basic-checksp)))

  (definlined vl-ifstmt (condition truebranch falsebranch atts)
    (declare (xargs :guard (and (vl-expr-p condition)
                                (vl-stmt-p truebranch)
                                (vl-stmt-p falsebranch)
                                (vl-atts-p atts))))
    (make-vl-compoundstmt :type :vl-ifstmt
                          :exprs (list condition)
                          :stmts (list truebranch falsebranch)
                          :atts atts))

  (vl-emulate-defaggregate-stuff vl-ifstmt
                                 (condition truebranch falsebranch atts))

  (definlined vl-ifstmt->condition (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-ifstmt-p x))))
    (car (vl-compoundstmt->exprs x)))

  (definlined vl-ifstmt->truebranch (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-ifstmt-p x))))
    (first (vl-compoundstmt->stmts x)))

  (definlined vl-ifstmt->falsebranch (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-ifstmt-p x))))
    (second (vl-compoundstmt->stmts x)))

  (definline vl-ifstmt->atts (x)
    ;; Note: we leave this enabled and just reason about vl-compoundstmt->atts.
    ;; Don't remove this function; it's needed for things like the b* binder.
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-ifstmt-p x))))
    (vl-compoundstmt->atts x))

  (local (in-theory (enable vl-ifstmt
                            vl-ifstmt->condition
                            vl-ifstmt->truebranch
                            vl-ifstmt->falsebranch)))

  (defthm vl-compoundstmt-p-of-vl-ifstmt
    (implies (and (force (vl-expr-p condition))
                  (force (vl-atts-p atts)))
             (vl-compoundstmt-p (make-vl-ifstmt :condition condition
                                                :truebranch truebranch
                                                :falsebranch falsebranch
                                                :atts atts))))

  (defthm vl-stmt-p-of-vl-ifstmt
    (implies (and (force (vl-expr-p condition))
                  (force (vl-stmt-p truebranch))
                  (force (vl-stmt-p falsebranch))
                  (force (vl-atts-p atts)))
             (vl-stmt-p (make-vl-ifstmt :condition condition
                                        :truebranch truebranch
                                        :falsebranch falsebranch
                                        :atts atts))))

  (defthm vl-expr-p-of-vl-ifstmt->condition
    (implies (force (vl-ifstmt-p x))
             (vl-expr-p (vl-ifstmt->condition x))))

  (defthm vl-stmt-p-of-vl-ifstmt->truebranch
    (implies (and (force (vl-ifstmt-p x))
                  (force (vl-stmt-p x)))
             (vl-stmt-p (vl-ifstmt->truebranch x))))

  (defthm vl-stmt-p-of-vl-ifstmt->falsebranch
    (implies (and (force (vl-ifstmt-p x))
                  (force (vl-stmt-p x)))
             (vl-stmt-p (vl-ifstmt->falsebranch x))))

  (defthm type-of-vl-ifstmt->condition
    (implies (force (vl-ifstmt-p x))
             (consp (vl-ifstmt->condition x)))
    :rule-classes :type-prescription)

  (defthm type-of-vl-ifstmt->truebranch
    (implies (and (force (vl-ifstmt-p x))
                  (force (vl-stmt-p x)))
             (consp (vl-ifstmt->truebranch x)))
    :rule-classes :type-prescription)

  (defthm type-of-vl-ifstmt->falsebranch
    (implies (and (force (vl-ifstmt-p x))
                  (force (vl-stmt-p x)))
             (consp (vl-ifstmt->falsebranch x)))
    :rule-classes :type-prescription)

  (defthm vl-ifstmt->condition-of-vl-ifstmt
    (equal (vl-ifstmt->condition (make-vl-ifstmt :condition condition
                                                 :truebranch truebranch
                                                 :falsebranch falsebranch
                                                 :atts atts))
           condition))

  (defthm vl-ifstmt->truebranch-of-vl-ifstmt
    (equal (vl-ifstmt->truebranch (make-vl-ifstmt :condition condition
                                                  :truebranch truebranch
                                                  :falsebranch falsebranch
                                                  :atts atts))
           truebranch))

  (defthm vl-ifstmt->falsebranch-of-vl-ifstmt
    (equal (vl-ifstmt->falsebranch (make-vl-ifstmt :condition condition
                                                   :truebranch truebranch
                                                   :falsebranch falsebranch
                                                   :atts atts))
           falsebranch))

  (defthm vl-compoundstmt->type-of-vl-ifstmt
    (equal (vl-compoundstmt->type (make-vl-ifstmt :condition condition
                                                  :truebranch truebranch
                                                  :falsebranch falsebranch
                                                  :atts atts))
           :vl-ifstmt))

  (defthm vl-compoundstmt->atts-of-vl-ifstmt
    (equal (vl-compoundstmt->atts (make-vl-ifstmt :condition condition
                                                  :truebranch truebranch
                                                  :falsebranch falsebranch
                                                  :atts atts))
           atts))

  (defthm acl2-count-of-vl-ifstmt->truebranch-weak
    (<= (acl2-count (vl-ifstmt->truebranch x))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-vl-ifstmt->truebranch-strong
    (implies (consp x)
             (< (acl2-count (vl-ifstmt->truebranch x))
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-vl-ifstmt->falsebranch-weak
    (<= (acl2-count (vl-ifstmt->falsebranch x))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-vl-ifstmt->falsebranch-strong
    (implies (consp x)
             (< (acl2-count (vl-ifstmt->falsebranch x))
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear))))


(local
 (defsection basic-vl-emulate-defaggregate-test

   (defconst *e1* (make-vl-atom
                   :guts (make-vl-constint :value 1
                                           :origtype :vl-unsigned
                                           :origwidth 5)))

   (defconst *e2* (make-vl-atom
                   :guts (make-vl-constint :value 2
                                           :origtype :vl-unsigned
                                           :origwidth 5)))

   (defconst *s1* (make-vl-assignstmt :type :vl-blocking
                                      :lvalue *e1*
                                      :expr *e2*
                                      :loc *vl-fakeloc*))

   (defconst *s2* (make-vl-nullstmt))

   (defconst *atts* '(("FOO")))

   (assert!
    (b* ((s (make-vl-ifstmt :condition *e1*
                            :truebranch *s1*
                            :falsebranch *s2*
                            :atts '(("FOO")))))
      (and (vl-stmt-p s)
           (vl-compoundstmt-p s)
           (vl-ifstmt-p s)
           (equal (vl-compoundstmt->type s) :vl-ifstmt)
           (equal (vl-ifstmt->truebranch s) *s1*)
           (equal (vl-ifstmt->falsebranch s) *s2*)
           (equal (vl-ifstmt->condition s) *e1*)
           (b* ((r (change-vl-ifstmt s :truebranch *s2*))
                ((vl-ifstmt r) r)
                ((vl-ifstmt s) s))
             (and (vl-ifstmt-p r)
                  (vl-ifstmt-p s)
                  (equal r.condition s.condition)
                  (equal r.falsebranch s.falsebranch)
                  (equal r.atts s.atts)
                  (equal r.truebranch *s2*)
                  (equal r.atts *atts*)
                  (equal s.atts *atts*))))))))


(defsection while-statements
  :parents (vl-stmt-p)
  :short "Utilities for manipulating @('while') statements."

  :long "<p>These functions allow you to conveniently construct and access
parts of @('while') statements without needing to know the details of their
representation.</p>

<h4>General Form:</h4>

@({
while (<condition>)
   <body>
})

<p>See Section 9.6 (page 130).  The semantics are like those of while loops in
C; <i>body</i> is executed until <i>condition</i> becomes false.  If
<i>condition</i> is false to begin with, then <i>body</i> is not executed at
all.</p>"

  (definline vl-whilestmt-p (x)
    ;; Note: we leave this enabled and allow compoundstmt->type to open up.
    (declare (xargs :guard (vl-stmt-p x)))
    (and (vl-fast-compoundstmt-p x)
         (eq (vl-compoundstmt->type x) :vl-whilestmt)))

  (defthmd vl-compoundstmt-parts-when-vl-whilestmt
    ;; Just the natural consequence of basic-checks for if statements.
    ;; Note that we ordinarily leave this disabled.
    (implies (vl-whilestmt-p x)
             (and (not (vl-compoundstmt->name x))
                  (not (vl-compoundstmt->ctrl x))
                  (not (vl-compoundstmt->sequentialp x))
                  (not (vl-compoundstmt->casetype x))
                  (atom (vl-compoundstmt->decls x))
                  (equal (len (vl-compoundstmt->exprs x)) 1)
                  (equal (len (vl-compoundstmt->stmts x)) 1)))
    :hints(("Goal"
            :use ((:instance vl-compoundstmt-basic-checksp-of-vl-compoundstmt))
            :in-theory (e/d (vl-compoundstmt-basic-checksp)
                            (vl-compoundstmt-basic-checksp-of-vl-compoundstmt)))))

  (local (in-theory (enable vl-compoundstmt-parts-when-vl-whilestmt
                            vl-compoundstmt-basic-checksp)))

  (defund vl-whilestmt (condition body atts)
    (declare (xargs :guard (and (vl-expr-p condition)
                                (vl-stmt-p body)
                                (vl-atts-p atts))))
    (make-vl-compoundstmt :type :vl-whilestmt
                          :exprs (list condition)
                          :stmts (list body)
                          :atts atts))

  (vl-emulate-defaggregate-stuff vl-whilestmt
                                 (condition body atts))

  (definlined vl-whilestmt->condition (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-whilestmt-p x))))
    (car (vl-compoundstmt->exprs x)))

  (definlined vl-whilestmt->body (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-whilestmt-p x))))
    (car (vl-compoundstmt->stmts x)))

  (definline vl-whilestmt->atts (x)
    ;; Note: we leave this enabled and just reason about vl-compoundstmt->atts.
    ;; Don't remove this function; it's needed for things like the b* binder.
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-whilestmt-p x))))
    (vl-compoundstmt->atts x))

  (local (in-theory (enable vl-whilestmt
                            vl-whilestmt->condition
                            vl-whilestmt->body)))

  (defthm vl-compoundstmt-p-of-vl-whilestmt
    (implies (and (force (vl-expr-p condition))
                  (force (vl-atts-p atts)))
             (vl-compoundstmt-p (make-vl-whilestmt :condition condition
                                                   :body body
                                                   :atts atts))))

  (defthm vl-stmt-p-of-vl-whilestmt
    (implies (and (force (vl-expr-p condition))
                  (force (vl-stmt-p body))
                  (force (vl-atts-p atts)))
             (vl-stmt-p (make-vl-whilestmt :condition condition
                                           :body body
                                           :atts atts))))

  (defthm vl-expr-p-of-vl-whilestmt->condition
    (implies (force (vl-whilestmt-p x))
             (vl-expr-p (vl-whilestmt->condition x))))

  (defthm vl-stmt-p-of-vl-whilestmt->body
    (implies (and (force (vl-whilestmt-p x))
                  (force (vl-stmt-p x)))
             (vl-stmt-p (vl-whilestmt->body x))))

  (defthm vl-whilestmt->condition-of-vl-whilestmt
    (equal (vl-whilestmt->condition (make-vl-whilestmt :condition condition
                                                       :body body
                                                       :atts atts))
           condition))

  (defthm vl-whilestmt->body-of-vl-whilestmt
    (equal (vl-whilestmt->body (make-vl-whilestmt :condition condition
                                                  :body body
                                                  :atts atts))
           body))

  (defthm vl-compoundstmt->type-of-vl-whilestmt
    (equal (vl-compoundstmt->type (make-vl-whilestmt :condition condition
                                                     :body body
                                                     :atts atts))
           :vl-whilestmt))

  (defthm vl-compoundstmt->atts-of-vl-whilestmt
    (equal (vl-compoundstmt->atts (make-vl-whilestmt :condition condition
                                                     :body body
                                                     :atts atts))
           atts))

  (defthm acl2-count-of-vl-whilestmt->body-weak
    (<= (acl2-count (vl-whilestmt->body x))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-vl-whilestmt->body-strong
    (implies (consp x)
             (< (acl2-count (vl-whilestmt->body x))
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear))))



(defsection repeat-statements
  :parents (vl-stmt-p)
  :short "Utilities for manipulating @('repeat') statements."

  :long "<p>These functions allow you to conveniently construct and access
parts of @('repeat') statements without needing to know the details of their
representation.</p>

<h4>General Form:</h4>

@({
repeat (<condition>)
   <body>
})

<p>See Section 9.6 (page 130).  The <i>condition</i> is presumably evaluated to
a natural number, and then <i>body</i> is executed that many times.  If the
expression evaluates to @('X') or @('Z'), it is supposed to be treated as zero
and the statement is not executed at all.  (What a crock!)</p>"

  (definline vl-repeatstmt-p (x)
    ;; Note: we leave this enabled and allow compoundstmt->type to open up.
    (declare (xargs :guard (vl-stmt-p x)))
    (and (vl-fast-compoundstmt-p x)
         (eq (vl-compoundstmt->type x) :vl-repeatstmt)))

  (defthmd vl-compoundstmt-parts-when-vl-repeatstmt
    ;; Just the natural consequence of basic-checks for if statements.
    ;; Note that we ordinarily leave this disabled.
    (implies (vl-repeatstmt-p x)
             (and (not (vl-compoundstmt->name x))
                  (not (vl-compoundstmt->ctrl x))
                  (not (vl-compoundstmt->sequentialp x))
                  (not (vl-compoundstmt->casetype x))
                  (atom (vl-compoundstmt->decls x))
                  (equal (len (vl-compoundstmt->exprs x)) 1)
                  (equal (len (vl-compoundstmt->stmts x)) 1)))
    :hints(("Goal"
            :use ((:instance vl-compoundstmt-basic-checksp-of-vl-compoundstmt))
            :in-theory (e/d (vl-compoundstmt-basic-checksp)
                            (vl-compoundstmt-basic-checksp-of-vl-compoundstmt)))))

  (local (in-theory (enable vl-compoundstmt-parts-when-vl-repeatstmt
                            vl-compoundstmt-basic-checksp)))

  (defund vl-repeatstmt (condition body atts)
    (declare (xargs :guard (and (vl-expr-p condition)
                                (vl-stmt-p body)
                                (vl-atts-p atts))))
    (make-vl-compoundstmt :type :vl-repeatstmt
                          :exprs (list condition)
                          :stmts (list body)
                          :atts atts))

  (vl-emulate-defaggregate-stuff vl-repeatstmt
                                 (condition body atts))

  (definlined vl-repeatstmt->condition (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-repeatstmt-p x))))
    (car (vl-compoundstmt->exprs x)))

  (definlined vl-repeatstmt->body (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-repeatstmt-p x))))
    (car (vl-compoundstmt->stmts x)))

  (definline vl-repeatstmt->atts (x)
    ;; Note: we leave this enabled and just reason about vl-compoundstmt->atts.
    ;; Don't remove this function; it's needed for things like the b* binder.
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-repeatstmt-p x))))
    (vl-compoundstmt->atts x))

  (local (in-theory (enable vl-repeatstmt
                            vl-repeatstmt->condition
                            vl-repeatstmt->body)))

  (defthm vl-compoundstmt-p-of-vl-repeatstmt
    (implies (and (force (vl-expr-p condition))
                  (force (vl-atts-p atts)))
             (vl-compoundstmt-p (make-vl-repeatstmt :condition condition
                                                    :body body
                                                    :atts atts))))

  (defthm vl-stmt-p-of-vl-repeatstmt
    (implies (and (force (vl-expr-p condition))
                  (force (vl-stmt-p body))
                  (force (vl-atts-p atts)))
             (vl-stmt-p (make-vl-repeatstmt :condition condition
                                            :body body
                                            :atts atts))))

  (defthm vl-expr-p-of-vl-repeatstmt->condition
    (implies (force (vl-repeatstmt-p x))
             (vl-expr-p (vl-repeatstmt->condition x))))

  (defthm vl-stmt-p-of-vl-repeatstmt->body
    (implies (and (force (vl-repeatstmt-p x))
                  (force (vl-stmt-p x)))
             (vl-stmt-p (vl-repeatstmt->body x))))

  (defthm vl-repeatstmt->condition-of-vl-repeatstmt
    (equal (vl-repeatstmt->condition (make-vl-repeatstmt :condition condition
                                                         :body body
                                                         :atts atts))
           condition))

  (defthm vl-repeatstmt->body-of-vl-repeatstmt
    (equal (vl-repeatstmt->body (make-vl-repeatstmt :condition condition
                                                    :body body
                                                    :atts atts))
           body))

  (defthm vl-compoundstmt->type-of-vl-repeatstmt
    (equal (vl-compoundstmt->type (make-vl-repeatstmt :condition condition
                                                      :body body
                                                      :atts atts))
           :vl-repeatstmt))

  (defthm vl-compoundstmt->atts-of-vl-repeatstmt
    (equal (vl-compoundstmt->atts (make-vl-repeatstmt :condition condition
                                                      :body body
                                                      :atts atts))
           atts))

  (defthm acl2-count-of-vl-repeatstmt->body-weak
    (<= (acl2-count (vl-repeatstmt->body x))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-vl-repeatstmt->body-strong
    (implies (consp x)
             (< (acl2-count (vl-repeatstmt->body x))
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear))))



(defsection wait-statements
  :parents (vl-stmt-p)
  :short "Utilities for manipulating @('wait') statements."

  :long "<p>These functions allow you to conveniently construct and access
parts of @('wait') statements without needing to know the details of their
representation.</p>

<h4>General Form:</h4>

@({
wait (<condition>)
   <body>
})

<p>See Section 9.7.6 (page 136).  The wait statement first evaluates
<i>condition</i>.  If the result is true, <i>body</i> is executed.  Otherwise,
this flow of execution blocks until <i>condition</i> becomes 1, at which point
it resumes and <i>body</i> is executed.  There is no discussion of what happens
when the <i>condition</i> is X or Z.  I would guess it is treated as 0 like in
if statements, but who knows.</p>"

  (definline vl-waitstmt-p (x)
    ;; Note: we leave this enabled and allow compoundstmt->type to open up.
    (declare (xargs :guard (vl-stmt-p x)))
    (and (vl-fast-compoundstmt-p x)
         (eq (vl-compoundstmt->type x) :vl-waitstmt)))

  (defthmd vl-compoundstmt-parts-when-vl-waitstmt
    ;; Just the natural consequence of basic-checks for if statements.
    ;; Note that we ordinarily leave this disabled.
    (implies (vl-waitstmt-p x)
             (and (not (vl-compoundstmt->name x))
                  (not (vl-compoundstmt->ctrl x))
                  (not (vl-compoundstmt->sequentialp x))
                  (not (vl-compoundstmt->casetype x))
                  (atom (vl-compoundstmt->decls x))
                  (equal (len (vl-compoundstmt->exprs x)) 1)
                  (equal (len (vl-compoundstmt->stmts x)) 1)))
    :hints(("Goal"
            :use ((:instance vl-compoundstmt-basic-checksp-of-vl-compoundstmt))
            :in-theory (e/d (vl-compoundstmt-basic-checksp)
                            (vl-compoundstmt-basic-checksp-of-vl-compoundstmt)))))

  (local (in-theory (enable vl-compoundstmt-parts-when-vl-waitstmt
                            vl-compoundstmt-basic-checksp)))

  (defund vl-waitstmt (condition body atts)
    (declare (xargs :guard (and (vl-expr-p condition)
                                (vl-stmt-p body)
                                (vl-atts-p atts))))
    (make-vl-compoundstmt :type :vl-waitstmt
                          :exprs (list condition)
                          :stmts (list body)
                          :atts atts))

  (vl-emulate-defaggregate-stuff vl-waitstmt
                                 (condition body atts))

  (definlined vl-waitstmt->condition (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-waitstmt-p x))))
    (car (vl-compoundstmt->exprs x)))

  (definlined vl-waitstmt->body (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-waitstmt-p x))))
    (car (vl-compoundstmt->stmts x)))

  (definline vl-waitstmt->atts (x)
    ;; Note: we leave this enabled and just reason about vl-compoundstmt->atts.
    ;; Don't remove this function; it's needed for things like the b* binder.
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-waitstmt-p x))))
    (vl-compoundstmt->atts x))

  (local (in-theory (enable vl-waitstmt
                            vl-waitstmt->condition
                            vl-waitstmt->body)))

  (defthm vl-compoundstmt-p-of-vl-waitstmt
    (implies (and (force (vl-expr-p condition))
                  (force (vl-atts-p atts)))
             (vl-compoundstmt-p (make-vl-waitstmt :condition condition
                                                  :body body
                                                  :atts atts))))

  (defthm vl-stmt-p-of-vl-waitstmt
    (implies (and (force (vl-expr-p condition))
                  (force (vl-stmt-p body))
                  (force (vl-atts-p atts)))
             (vl-stmt-p (make-vl-waitstmt :condition condition
                                          :body body
                                          :atts atts))))

  (defthm vl-expr-p-of-vl-waitstmt->condition
    (implies (force (vl-waitstmt-p x))
             (vl-expr-p (vl-waitstmt->condition x))))

  (defthm vl-stmt-p-of-vl-waitstmt->body
    (implies (and (force (vl-waitstmt-p x))
                  (force (vl-stmt-p x)))
             (vl-stmt-p (vl-waitstmt->body x))))

  (defthm vl-waitstmt->condition-of-vl-waitstmt
    (equal (vl-waitstmt->condition (make-vl-waitstmt :condition condition
                                                     :body body
                                                     :atts atts))
           condition))

  (defthm vl-waitstmt->body-of-vl-waitstmt
    (equal (vl-waitstmt->body (make-vl-waitstmt :condition condition
                                                :body body
                                                :atts atts))
           body))

  (defthm vl-compoundstmt->type-of-vl-waitstmt
    (equal (vl-compoundstmt->type (make-vl-waitstmt :condition condition
                                                    :body body
                                                    :atts atts))
           :vl-waitstmt))

  (defthm vl-compoundstmt->atts-of-vl-waitstmt
    (equal (vl-compoundstmt->atts (make-vl-waitstmt :condition condition
                                                    :body body
                                                    :atts atts))
           atts))

  (defthm acl2-count-of-vl-waitstmt->body-weak
    (<= (acl2-count (vl-waitstmt->body x))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-vl-waitstmt->body-strong
    (implies (consp x)
             (< (acl2-count (vl-waitstmt->body x))
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear))))



(defsection forever-statements
  :parents (vl-stmt-p)
  :short "Utilities for manipulating @('forever') statements."

  :long "<p>These functions allow you to conveniently construct and access
parts of @('forever') statements without needing to know the details of their
representation.</p>

<h4>General Form:</h4>

@({
forever <body>;
})

<p>See Section 9.6 (page 130).  The forever statement continuously executes
<i>body</i>.</p>"

  (definline vl-foreverstmt-p (x)
    ;; Note: we leave this enabled and allow compoundstmt->type to open up.
    (declare (xargs :guard (vl-stmt-p x)))
    (and (vl-fast-compoundstmt-p x)
         (eq (vl-compoundstmt->type x) :vl-foreverstmt)))

  (defthmd vl-compoundstmt-parts-when-vl-foreverstmt
    ;; Just the natural consequence of basic-checks for if statements.
    ;; Note that we ordinarily leave this disabled.
    (implies (vl-foreverstmt-p x)
             (and (not (vl-compoundstmt->name x))
                  (not (vl-compoundstmt->ctrl x))
                  (not (vl-compoundstmt->sequentialp x))
                  (not (vl-compoundstmt->casetype x))
                  (atom (vl-compoundstmt->decls x))
                  (atom (vl-compoundstmt->exprs x))
                  (equal (len (vl-compoundstmt->stmts x)) 1)))
    :hints(("Goal"
            :use ((:instance vl-compoundstmt-basic-checksp-of-vl-compoundstmt))
            :in-theory (e/d (vl-compoundstmt-basic-checksp)
                            (vl-compoundstmt-basic-checksp-of-vl-compoundstmt)))))

  (local (in-theory (enable vl-compoundstmt-parts-when-vl-foreverstmt
                            vl-compoundstmt-basic-checksp)))

  (defund vl-foreverstmt (body atts)
    (declare (xargs :guard (and (vl-stmt-p body)
                                (vl-atts-p atts))))
    (make-vl-compoundstmt :type :vl-foreverstmt
                          :stmts (list body)
                          :atts atts))

  (vl-emulate-defaggregate-stuff vl-foreverstmt
                                 (body atts))

  (definlined vl-foreverstmt->body (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-foreverstmt-p x))))
    (car (vl-compoundstmt->stmts x)))

  (definline vl-foreverstmt->atts (x)
    ;; Note: we leave this enabled and just reason about vl-compoundstmt->atts.
    ;; Don't remove this function; it's needed for things like the b* binder.
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-foreverstmt-p x))))
    (vl-compoundstmt->atts x))

  (local (in-theory (enable vl-foreverstmt
                            vl-foreverstmt->body)))

  (defthm vl-compoundstmt-p-of-vl-foreverstmt
    (implies (force (vl-atts-p atts))
             (vl-compoundstmt-p (make-vl-foreverstmt :body body
                                                     :atts atts))))

  (defthm vl-stmt-p-of-vl-foreverstmt
    (implies (and (force (vl-stmt-p body))
                  (force (vl-atts-p atts)))
             (vl-stmt-p (make-vl-foreverstmt :body body
                                             :atts atts))))

  (defthm vl-stmt-p-of-vl-foreverstmt->body
    (implies (and (force (vl-stmt-p x))
                  (force (vl-foreverstmt-p x)))
             (vl-stmt-p (vl-foreverstmt->body x))))

  (defthm vl-foreverstmt->body-of-vl-foreverstmt
    (equal (vl-foreverstmt->body (make-vl-foreverstmt :body body
                                                      :atts atts))
           body))

  (defthm vl-compoundstmt->type-of-vl-foreverstmt
    (equal (vl-compoundstmt->type (make-vl-foreverstmt :body body
                                                       :atts atts))
           :vl-foreverstmt))

  (defthm vl-compoundstmt->atts-of-vl-foreverstmt
    (equal (vl-compoundstmt->atts (make-vl-foreverstmt :body body
                                                       :atts atts))
           atts))

  (defthm acl2-count-of-vl-foreverstmt->body-weak
    (<= (acl2-count (vl-foreverstmt->body x))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-vl-foreverstmt->body-strong
    (implies (consp x)
             (< (acl2-count (vl-foreverstmt->body x))
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear))))



(defsection for-statements
  :parents (vl-stmt-p)
  :short "Utilities for manipulating @('for') statements."

  :long "<p>These functions allow you to conveniently construct and access
parts of @('for') statements without needing to know the details of their
representation.</p>

<h4>General Form:</h4>

@({
for( <initlhs> = <initrhs> ; <test> ; <nextlhs> = <nextrhs> )
   <body>
})

<p>See Section 9.6 (page 130).  The wait statement acts like a while-statement
in C.  First, outside the loop, it executes the assignment @('initlhs =
initrhs').  Then it evalutes <i>test</i>.  If <i>test</i> evaluates to zero (or
to X or Z) then the loop exists.  Otherwise, <i>body</i> is executed, the
assignment @('nextlhs = nextrhs') is performed, and we loop back to evaluating
<i>test</i>.</p>"

  (definline vl-forstmt-p (x)
    ;; Note: we leave this enabled and allow compoundstmt->type to open up.
    (declare (xargs :guard (vl-stmt-p x)))
    (and (vl-fast-compoundstmt-p x)
         (eq (vl-compoundstmt->type x) :vl-forstmt)))

  (defthmd vl-compoundstmt-parts-when-vl-forstmt
    ;; Just the natural consequence of basic-checks for if statements.
    ;; Note that we ordinarily leave this disabled.
    (implies (vl-forstmt-p x)
             (and (not (vl-compoundstmt->name x))
                  (not (vl-compoundstmt->ctrl x))
                  (not (vl-compoundstmt->sequentialp x))
                  (not (vl-compoundstmt->casetype x))
                  (atom (vl-compoundstmt->decls x))
                  (equal (len (vl-compoundstmt->exprs x)) 5)
                  (equal (len (vl-compoundstmt->stmts x)) 1)))
    :hints(("Goal"
            :use ((:instance vl-compoundstmt-basic-checksp-of-vl-compoundstmt))
            :in-theory (e/d (vl-compoundstmt-basic-checksp)
                            (vl-compoundstmt-basic-checksp-of-vl-compoundstmt)))))

  (local (in-theory (enable vl-compoundstmt-parts-when-vl-forstmt
                            vl-compoundstmt-basic-checksp)))


  (defund vl-forstmt (initlhs initrhs test nextlhs nextrhs body atts)
    (declare (xargs :guard (and (vl-expr-p initlhs)
                                (vl-expr-p initrhs)
                                (vl-expr-p test)
                                (vl-expr-p nextlhs)
                                (vl-expr-p nextrhs)
                                (vl-stmt-p body)
                                (vl-atts-p atts))))
    (make-vl-compoundstmt :type :vl-forstmt
                          :exprs (list initlhs initrhs test nextlhs nextrhs)
                          :stmts (list body)
                          :atts atts))

  (vl-emulate-defaggregate-stuff vl-forstmt
                                 (initlhs initrhs test nextlhs nextrhs
                                          body atts))

  (definlined vl-forstmt->initlhs (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-forstmt-p x))))
    (first (vl-compoundstmt->exprs x)))

  (definlined vl-forstmt->initrhs (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-forstmt-p x))))
    (second (vl-compoundstmt->exprs x)))

  (definlined vl-forstmt->test (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-forstmt-p x))))
    (third (vl-compoundstmt->exprs x)))

  (definlined vl-forstmt->nextlhs (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-forstmt-p x))))
    (fourth (vl-compoundstmt->exprs x)))

  (definlined vl-forstmt->nextrhs (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-forstmt-p x))))
    (fifth (vl-compoundstmt->exprs x)))

  (definlined vl-forstmt->body (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-forstmt-p x))))
    (first (vl-compoundstmt->stmts x)))

  (definline vl-forstmt->atts (x)
    ;; Note: we leave this enabled and just reason about vl-compoundstmt->atts.
    ;; Don't remove this function; it's needed for things like the b* binder.
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-forstmt-p x))))
    (vl-compoundstmt->atts x))

  (local (in-theory (enable vl-forstmt
                            vl-forstmt->initlhs
                            vl-forstmt->initrhs
                            vl-forstmt->test
                            vl-forstmt->nextlhs
                            vl-forstmt->nextrhs
                            vl-forstmt->body)))

  (defthm vl-compoundstmt-p-of-vl-forstmt
    (implies (and (force (vl-expr-p initlhs))
                  (force (vl-expr-p initrhs))
                  (force (vl-expr-p test))
                  (force (vl-expr-p nextlhs))
                  (force (vl-expr-p nextrhs))
                  (force (vl-atts-p atts)))
             (vl-compoundstmt-p (make-vl-forstmt :initlhs initlhs
                                                 :initrhs initrhs
                                                 :test test
                                                 :nextlhs nextlhs
                                                 :nextrhs nextrhs
                                                 :body body
                                                 :atts atts))))

  (defthm vl-stmt-p-of-vl-forstmt
    (implies (and (force (vl-expr-p initlhs))
                  (force (vl-expr-p initrhs))
                  (force (vl-expr-p test))
                  (force (vl-expr-p nextlhs))
                  (force (vl-expr-p nextrhs))
                  (force (vl-stmt-p body))
                  (force (vl-atts-p atts)))
             (vl-stmt-p (make-vl-forstmt :initlhs initlhs
                                         :initrhs initrhs
                                         :test test
                                         :nextlhs nextlhs
                                         :nextrhs nextrhs
                                         :body body
                                         :atts atts))))

  (defthm vl-expr-p-of-vl-forstmt->initlhs
    (implies (force (vl-forstmt-p x))
             (vl-expr-p (vl-forstmt->initlhs x))))

  ;; Interferes with our length lemmas, I guess
  (local (in-theory (disable VL-MAYBE-EXPR-P-WHEN-VL-EXPR-P)))

  (defthm vl-expr-p-of-vl-forstmt->initrhs
    (implies (force (vl-forstmt-p x))
             (vl-expr-p (vl-forstmt->initrhs x))))

  (defthm vl-expr-p-of-vl-forstmt->test
    (implies (force (vl-forstmt-p x))
             (vl-expr-p (vl-forstmt->test x))))

  (defthm vl-expr-p-of-vl-forstmt->nextlhs
    (implies (force (vl-forstmt-p x))
             (vl-expr-p (vl-forstmt->nextlhs x))))

  (defthm vl-expr-p-of-vl-forstmt->nextrhs
    (implies (force (vl-forstmt-p x))
             (vl-expr-p (vl-forstmt->nextrhs x))))

  (defthm vl-stmt-p-of-vl-forstmt->body
    (implies (and (force (vl-forstmt-p x))
                  (force (vl-stmt-p x)))
             (vl-stmt-p (vl-forstmt->body x))))



  (defthm vl-forstmt->initlhs-of-vl-forstmt
    (equal (vl-forstmt->initlhs (make-vl-forstmt :initlhs initlhs
                                                 :initrhs initrhs
                                                 :test test
                                                 :nextlhs nextlhs
                                                 :nextrhs nextrhs
                                                 :body body
                                                 :atts atts))
           initlhs))

  (defthm vl-forstmt->initrhs-of-vl-forstmt
    (equal (vl-forstmt->initrhs (make-vl-forstmt :initlhs initlhs
                                                 :initrhs initrhs
                                                 :test test
                                                 :nextlhs nextlhs
                                                 :nextrhs nextrhs
                                                 :body body
                                                 :atts atts))
           initrhs))

  (defthm vl-forstmt->test-of-vl-forstmt
    (equal (vl-forstmt->test (make-vl-forstmt :initlhs initlhs
                                              :initrhs initrhs
                                              :test test
                                              :nextlhs nextlhs
                                              :nextrhs nextrhs
                                              :body body
                                              :atts atts))
           test))

  (defthm vl-forstmt->nextlhs-of-vl-forstmt
    (equal (vl-forstmt->nextlhs (make-vl-forstmt :initlhs initlhs
                                                 :initrhs initrhs
                                                 :test test
                                                 :nextlhs nextlhs
                                                 :nextrhs nextrhs
                                                 :body body
                                                 :atts atts))
           nextlhs))

  (defthm vl-forstmt->nextrhs-of-vl-forstmt
    (equal (vl-forstmt->nextrhs (make-vl-forstmt :initlhs initlhs
                                                 :initrhs initrhs
                                                 :test test
                                                 :nextlhs nextlhs
                                                 :nextrhs nextrhs
                                                 :body body
                                                 :atts atts))
           nextrhs))

  (defthm vl-forstmt->body-of-vl-forstmt
    (equal (vl-forstmt->body (make-vl-forstmt :initlhs initlhs
                                              :initrhs initrhs
                                              :test test
                                              :nextlhs nextlhs
                                              :nextrhs nextrhs
                                              :body body
                                              :atts atts))
           body))

  (defthm vl-compoundstmt->type-of-vl-forstmt
    (equal (vl-compoundstmt->type (make-vl-forstmt :initlhs initlhs
                                                   :initrhs initrhs
                                                   :test test
                                                   :nextlhs nextlhs
                                                   :nextrhs nextrhs
                                                   :body body
                                                   :atts atts))
           :vl-forstmt))

  (defthm vl-compoundstmt->atts-of-vl-forstmt
    (equal (vl-compoundstmt->atts (make-vl-forstmt :initlhs initlhs
                                                   :initrhs initrhs
                                                   :test test
                                                   :nextlhs nextlhs
                                                   :nextrhs nextrhs
                                                   :body body
                                                   :atts atts))
           atts))

  (defthm acl2-count-of-vl-forstmt->body-weak
    (<= (acl2-count (vl-forstmt->body x))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-vl-forstmt->body-strong
    (implies (consp x)
             (< (acl2-count (vl-forstmt->body x))
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear))))



(defsection block-statements
  :parents (vl-stmt-p)
  :short "Utilities for manipulating sequential block (i.e., @('begin
... end'), or @('fork ... join')) statements."

  :long "<p>These functions allow you to conveniently construct and access
parts of block statements without needing to know the details of their
representation.</p>

<h4>General Form:</h4>

@({
begin [ : <name> <declarations> ]
  <statements>
end

fork [ :<name> <declarations> ]
  <statements>
join
})

<p>See Section 9.8.  The difference betwen the two kinds of blocks is that in a
@('begin/end') block, statements are to be executed in order, whereas in a
@('fork/join') block, statements are executed simultaneously.</p>

<p>Blocks that are named can have local declarations, and can be referenced by
other statements (e.g., disable statements).  With regards to declarations:
\"All variables shall be static; that is, a unique location exists for all
variables, and leaving or entering blocks shall not affect the values stored in
them.\"</p>

<p>A further remark is that \"Block names give a means of uniquely identifying
all variables at any simulation time.\" This seems to suggest that one might
try to flatten all of the declarations in a module by, e.g., prepending the
block name to each variable name.</p>"

  (definline vl-blockstmt-p (x)
    ;; Note: we leave this enabled and allow compoundstmt->type to open up.
    (declare (xargs :guard (vl-stmt-p x)))
    (and (vl-fast-compoundstmt-p x)
         (eq (vl-compoundstmt->type x) :vl-blockstmt)))

  (defthmd vl-compoundstmt-parts-when-vl-blockstmt
    ;; Just the natural consequence of basic-checks for if statements.
    ;; Note that we ordinarily leave this disabled.
    (implies (vl-blockstmt-p x)
             (and (not (vl-compoundstmt->ctrl x))
                  (not (vl-compoundstmt->casetype x))
                  (atom (vl-compoundstmt->exprs x))))
    :hints(("Goal"
            :use ((:instance vl-compoundstmt-basic-checksp-of-vl-compoundstmt))
            :in-theory (e/d (vl-compoundstmt-basic-checksp)
                            (vl-compoundstmt-basic-checksp-of-vl-compoundstmt)))))

  (local (in-theory (enable vl-compoundstmt-parts-when-vl-blockstmt
                            vl-compoundstmt-basic-checksp)))

  (defund vl-blockstmt (sequentialp name decls stmts atts)
    (declare (xargs :guard (and (booleanp sequentialp)
                                (vl-maybe-string-p name)
                                (vl-blockitemlist-p decls)
                                (vl-stmtlist-p stmts)
                                (vl-atts-p atts))))
    (make-vl-compoundstmt :type :vl-blockstmt
                          :sequentialp sequentialp
                          :name name
                          :decls decls
                          :stmts stmts
                          :atts atts))

  (vl-emulate-defaggregate-stuff vl-blockstmt
                                 (sequentialp name decls stmts atts))

  (definlined vl-blockstmt->sequentialp (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-blockstmt-p x))))
    (vl-compoundstmt->sequentialp x))

  (definlined vl-blockstmt->name (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-blockstmt-p x))))
    (vl-compoundstmt->name x))

  (definlined vl-blockstmt->decls (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-blockstmt-p x))))
    (vl-compoundstmt->decls x))

  (definlined vl-blockstmt->stmts (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-blockstmt-p x))))
    (vl-compoundstmt->stmts x))

  (definline vl-blockstmt->atts (x)
    ;; Note: we leave this enabled and just reason about vl-compoundstmt->atts.
    ;; Don't remove this function; it's needed for things like the b* binder.
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-blockstmt-p x))))
    (vl-compoundstmt->atts x))

  (local (in-theory (enable vl-blockstmt
                            vl-blockstmt->sequentialp
                            vl-blockstmt->name
                            vl-blockstmt->decls
                            vl-blockstmt->stmts)))

  (defthm vl-compoundstmt-p-of-vl-blockstmt
    (implies (and (force (booleanp sequentialp))
                  (force (vl-maybe-string-p name))
                  (force (vl-blockitemlist-p decls))
                  (force (vl-atts-p atts)))
             (vl-compoundstmt-p (make-vl-blockstmt :sequentialp sequentialp
                                                   :name name
                                                   :decls decls
                                                   :stmts stmts
                                                   :atts atts))))

  (defthm vl-stmt-p-of-vl-blockstmt
    (implies (and (force (booleanp sequentialp))
                  (force (vl-maybe-string-p name))
                  (force (vl-blockitemlist-p decls))
                  (force (vl-stmtlist-p stmts))
                  (force (vl-atts-p atts)))
             (vl-stmt-p (make-vl-blockstmt :sequentialp sequentialp
                                           :name name
                                           :decls decls
                                           :stmts stmts
                                           :atts atts))))

  (defthm booleanp-of-vl-blockstmt->sequentialp
    (implies (force (vl-blockstmt-p x))
             (booleanp (vl-blockstmt->sequentialp x)))
    :rule-classes :type-prescription)

  (defthm vl-maybe-string-p-of-vl-blockstmt->name
    (implies (force (vl-blockstmt-p x))
             (vl-maybe-string-p (vl-blockstmt->name x)))
    :rule-classes ((:rewrite)
                   (:type-prescription)))

  (defthm stringp-of-vl-blockstmt->name
    (implies (force (vl-blockstmt-p x))
             (equal (stringp (vl-blockstmt->name x))
                    (if (vl-blockstmt->name x)
                        t
                      nil))))

  (defthm vl-blockitemlist-p-of-vl-blockstmt->decls
    (implies (force (vl-blockstmt-p x))
             (vl-blockitemlist-p (vl-blockstmt->decls x))))

  (defthm vl-stmtlist-p-of-vl-blockstmt->stmts
    (implies (and (force (vl-blockstmt-p x))
                  (force (vl-stmt-p x)))
             (vl-stmtlist-p (vl-blockstmt->stmts x))))

  (defthm vl-blockstmt->sequentialp-of-vl-blockstmt
    (equal (vl-blockstmt->sequentialp (make-vl-blockstmt :sequentialp sequentialp
                                                         :name name
                                                         :decls decls
                                                         :stmts stmts
                                                         :atts atts))
           sequentialp))

  (defthm vl-blockstmt->name-of-vl-blockstmt
    (equal (vl-blockstmt->name (make-vl-blockstmt :sequentialp sequentialp
                                                  :name name
                                                  :decls decls
                                                  :stmts stmts
                                                  :atts atts))
           name))

  (defthm vl-blockstmt->decls-of-vl-blockstmt
    (equal (vl-blockstmt->decls (make-vl-blockstmt :sequentialp sequentialp
                                                   :name name
                                                   :decls decls
                                                   :stmts stmts
                                                   :atts atts))
           decls))

  (defthm vl-blockstmt->stmts-of-vl-blockstmt
    (equal (vl-blockstmt->stmts (make-vl-blockstmt :sequentialp sequentialp
                                                   :name name
                                                   :decls decls
                                                   :stmts stmts
                                                   :atts atts))
           stmts))

  (defthm vl-compoundstmt->type-of-vl-blockstmt
    (equal (vl-compoundstmt->type (make-vl-blockstmt :sequentialp sequentialp
                                                     :name name
                                                     :decls decls
                                                     :stmts stmts
                                                     :atts atts))
           :vl-blockstmt))

  (defthm vl-compoundstmt->atts-of-vl-blockstmt
    (equal (vl-compoundstmt->atts (make-vl-blockstmt :sequentialp sequentialp
                                                     :name name
                                                     :decls decls
                                                     :stmts stmts
                                                     :atts atts))
           atts))

  (defthm acl2-count-of-vl-blockstmt->stmts-weak
    (<= (acl2-count (vl-blockstmt->stmts x))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-vl-blockstmt->stmts-strong
    (implies (consp x)
             (< (acl2-count (vl-blockstmt->stmts x))
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear))))




(defsection timing-statements
  :parents (vl-stmt-p)
  :short "Utilities for manipulating timing statements."

  :long "<p>These functions allow you to conveniently construct and access
parts of timing statements without needing to know the details of their
representation.</p>

<h4>General Form:</h4>

@({
<ctrl> <body>
})

<h4>Examples:</h4>

@({
#3 foo = bar;
@@(posedge clk) foo = bar;
@@(bar or baz) foo = bar | baz;
})"

  (definline vl-timingstmt-p (x)
    ;; Note: we leave this enabled and allow compoundstmt->type to open up.
    (declare (xargs :guard (vl-stmt-p x)))
    (and (vl-fast-compoundstmt-p x)
         (eq (vl-compoundstmt->type x) :vl-timingstmt)))

  (defthmd vl-compoundstmt-parts-when-vl-timingstmt
    ;; Just the natural consequence of basic-checks for if statements.
    ;; Note that we ordinarily leave this disabled.
    (implies (vl-timingstmt-p x)
             (and (not (vl-compoundstmt->name x))
                  (vl-compoundstmt->ctrl x)
                  (not (vl-compoundstmt->sequentialp x))
                  (not (vl-compoundstmt->casetype x))
                  (atom (vl-compoundstmt->decls x))
                  (atom (vl-compoundstmt->exprs x))
                  (equal (len (vl-compoundstmt->stmts x)) 1)))
    :hints(("Goal"
            :use ((:instance vl-compoundstmt-basic-checksp-of-vl-compoundstmt))
            :in-theory (e/d (vl-compoundstmt-basic-checksp)
                            (vl-compoundstmt-basic-checksp-of-vl-compoundstmt)))))

  (local (in-theory (enable vl-compoundstmt-parts-when-vl-timingstmt
                            vl-compoundstmt-basic-checksp)))

  (defund vl-timingstmt (ctrl body atts)
    (declare (xargs :guard (and (vl-delayoreventcontrol-p ctrl)
                                (vl-stmt-p body)
                                (vl-atts-p atts))))
    (make-vl-compoundstmt :type :vl-timingstmt
                          :ctrl ctrl
                          :stmts (list body)
                          :atts atts))

  (vl-emulate-defaggregate-stuff vl-timingstmt
                                 (ctrl body atts))

  (definlined vl-timingstmt->ctrl (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-timingstmt-p x))))
    (vl-compoundstmt->ctrl x))

  (definlined vl-timingstmt->body (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-timingstmt-p x))))
    (car (vl-compoundstmt->stmts x)))

  (definline vl-timingstmt->atts (x)
    ;; Note: we leave this enabled and just reason about vl-compoundstmt->atts.
    ;; Don't remove this function; it's needed for things like the b* binder.
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-timingstmt-p x))))
    (vl-compoundstmt->atts x))

  (local (in-theory (enable vl-timingstmt
                            vl-timingstmt->ctrl
                            vl-timingstmt->body)))

  (defthm vl-compoundstmt-p-of-vl-timingstmt
    (implies (and (force (vl-delayoreventcontrol-p ctrl))
                  (force (vl-atts-p atts)))
             (vl-compoundstmt-p (make-vl-timingstmt :ctrl ctrl
                                                    :body body
                                                    :atts atts))))

  (defthm vl-stmt-p-of-vl-timingstmt
    (implies (and (force (vl-delayoreventcontrol-p ctrl))
                  (force (vl-stmt-p body))
                  (force (vl-atts-p atts)))
             (vl-stmt-p (make-vl-timingstmt :ctrl ctrl
                                            :body body
                                            :atts atts))))

  (defthm vl-delayoreventcontrol-p-of-vl-timingstmt->ctrl
    (implies (force (vl-timingstmt-p x))
             (vl-delayoreventcontrol-p (vl-timingstmt->ctrl x))))

  (defthm vl-stmt-p-of-vl-timingstmt->body
    (implies (and (force (vl-timingstmt-p x))
                  (force (vl-stmt-p x)))
             (vl-stmt-p (vl-timingstmt->body x))))

  (defthm vl-timingstmt->ctrl-of-vl-timingstmt
    (equal (vl-timingstmt->ctrl (make-vl-timingstmt :ctrl ctrl
                                                    :body body
                                                    :atts atts))
           ctrl))

  (defthm vl-timingstmt->body-of-vl-timingstmt
    (equal (vl-timingstmt->body (make-vl-timingstmt :ctrl ctrl
                                                    :body body
                                                    :atts atts))
           body))

  (defthm vl-compoundstmt->type-of-vl-timingstmt
    (equal (vl-compoundstmt->type (make-vl-timingstmt :ctrl ctrl
                                                      :body body
                                                      :atts atts))
           :vl-timingstmt))

  (defthm vl-compoundstmt->atts-of-vl-timingstmt
    (equal (vl-compoundstmt->atts (make-vl-timingstmt :ctrl ctrl
                                                      :body body
                                                      :atts atts))
           atts))

  (defthm acl2-count-of-vl-timingstmt->body-weak
    (<= (acl2-count (vl-timingstmt->body x))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-vl-timingstmt->body-strong
    (implies (consp x)
             (< (acl2-count (vl-timingstmt->body x))
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear))))



(defsection case-statements
  :parents (vl-stmt-p)
  :short "Utilities for manipulating @('case') statements."

  :long "<p>These functions allow you to conveniently construct and access
parts of @('case') statements without needing to know the details of their
representation.</p>

<h4>General Form:</h4>

@({
case ( <test> )
   <match-1> : <body-1>
   <match-2> : <body-2>
   ...
   <match-N> : <body-N>
   default : <default-body>
endcase
})

<p>Note that in Verilog, case statements can include multiple <i>match</i>
expressions on the same line, but our parser splits these up into separate
lines with the same body.  Note also that the default case is optional, but we
insert a null statement in such cases, so we can always give you a default
statement.</p>

<p>Case statements are discussed in Section 9.5 (page 127).  There are three
kinds of case statements, which we identify with @(see vl-casetype-p).</p>

<ul>

<li>@('vl-casestmt->casetype') returns the case type (i.e., @('case'),
@('casex'), or @('casez')); see @(see vl-casetype-p).</li>

<li>@('vl-casestmt->test') returns the <i>test</i> expression.</li>

<li>@('vl-casestmt->default') returns the <i>default-body</i> statement.</li>

<li>@('vl-casestmt->exprs') returns a list of expressions, (<i>match-1</i> ...
<i>match-N</i>).</li>

<li>@('vl-casestmt->bodies') returns a list of bodies that go along with the
match expressions; note that the <i>default-body</i> is NOT included in this
list.</li>

</ul>"

  (definline vl-casestmt-p (x)
    ;; Note: we leave this enabled and allow compoundstmt->type to open up.
    (declare (xargs :guard (vl-stmt-p x)))
    (and (vl-fast-compoundstmt-p x)
         (eq (vl-compoundstmt->type x) :vl-casestmt)))

  (defthmd vl-compoundstmt-parts-when-vl-casestmt
    ;; Just the natural consequence of basic-checks for if statements.
    ;; Note that we ordinarily leave this disabled.
    (implies (vl-casestmt-p x)
             (and (not (vl-compoundstmt->name x))
                  (not (vl-compoundstmt->ctrl x))
                  (not (vl-compoundstmt->sequentialp x))
                  (atom (vl-compoundstmt->decls x))
                  (consp (vl-compoundstmt->exprs x))
                  (equal (len (vl-compoundstmt->stmts x))
                         (len (vl-compoundstmt->exprs x)))))
    :hints(("Goal"
            :use ((:instance vl-compoundstmt-basic-checksp-of-vl-compoundstmt))
            :in-theory (e/d (vl-compoundstmt-basic-checksp)
                            (vl-compoundstmt-basic-checksp-of-vl-compoundstmt)))))

  (local (in-theory (enable vl-compoundstmt-parts-when-vl-casestmt
                            vl-compoundstmt-basic-checksp)))

  (defund vl-casestmt (casetype test exprs bodies default atts)
    (declare (xargs :guard (and (vl-casetype-p casetype)
                                (vl-expr-p test)
                                (vl-exprlist-p exprs)
                                (vl-stmtlist-p bodies)
                                (same-lengthp exprs bodies)
                                (vl-stmt-p default)
                                (vl-atts-p atts))))
    (make-vl-compoundstmt :type :vl-casestmt
                          :casetype casetype
                          :exprs (cons test exprs)
                          :stmts (cons default bodies)
                          :atts atts))

  (vl-emulate-defaggregate-stuff vl-casestmt
                                 (casetype test exprs bodies default atts))

  (definlined vl-casestmt->casetype (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-compoundstmt-p x)
                                (eq (vl-compoundstmt->type x) :vl-casestmt))))
    (vl-compoundstmt->casetype x))

  (definlined vl-casestmt->test (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-compoundstmt-p x)
                                (eq (vl-compoundstmt->type x) :vl-casestmt))))
    (car (vl-compoundstmt->exprs x)))

  (definlined vl-casestmt->exprs (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-compoundstmt-p x)
                                (eq (vl-compoundstmt->type x) :vl-casestmt))))
    (cdr (vl-compoundstmt->exprs x)))

  (definlined vl-casestmt->default (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-compoundstmt-p x)
                                (eq (vl-compoundstmt->type x) :vl-casestmt))
                    :guard-hints(("Goal"
                                  :in-theory (disable vl-compoundstmt-parts-when-vl-casestmt)
                                  :use ((:instance vl-compoundstmt-parts-when-vl-casestmt))))))
    (car (vl-compoundstmt->stmts x)))

  (definlined vl-casestmt->bodies (x)
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-compoundstmt-p x)
                                (eq (vl-compoundstmt->type x) :vl-casestmt))
                    :guard-hints(("Goal"
                                  :in-theory (disable vl-compoundstmt-parts-when-vl-casestmt)
                                  :use ((:instance vl-compoundstmt-parts-when-vl-casestmt))))))
    (cdr (vl-compoundstmt->stmts x)))

  (definline vl-casestmt->atts (x)
    ;; Note: we leave this enabled and just reason about vl-compoundstmt->atts.
    ;; Don't remove this function; it's needed for things like the b* binder.
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-casestmt-p x))))
    (vl-compoundstmt->atts x))

  (local (in-theory (enable vl-casestmt
                            vl-casestmt->casetype
                            vl-casestmt->test
                            vl-casestmt->exprs
                            vl-casestmt->default
                            vl-casestmt->bodies)))

  (defthm vl-compoundstmt-p-of-vl-casestmt
    (implies (and (force (vl-casetype-p casetype))
                  (force (vl-expr-p test))
                  (force (vl-exprlist-p exprs))
                  (force (same-lengthp exprs bodies))
                  (force (vl-atts-p atts)))
             (vl-compoundstmt-p (make-vl-casestmt :casetype casetype
                                                  :test test
                                                  :exprs exprs
                                                  :bodies bodies
                                                  :default default
                                                  :atts atts))))

  (defthm vl-stmt-p-of-vl-casestmt
    (implies (and (force (vl-casetype-p casetype))
                  (force (vl-expr-p test))
                  (force (vl-exprlist-p exprs))
                  (force (vl-stmtlist-p bodies))
                  (force (same-lengthp exprs bodies))
                  (force (vl-stmt-p default))
                  (force (vl-atts-p atts)))
             (vl-stmt-p (make-vl-casestmt :casetype casetype
                                          :test test
                                          :exprs exprs
                                          :bodies bodies
                                          :default default
                                          :atts atts))))

  (defthm vl-casetype-p-of-vl-casestmt->casetype
    (implies (force (vl-casestmt-p x))
             (vl-casetype-p (vl-casestmt->casetype x))))

  (defthm vl-expr-p-of-vl-casestmt->test
    (implies (force (vl-casestmt-p x))
             (vl-expr-p (vl-casestmt->test x))))

  (defthm vl-stmt-p-of-vl-casestmt->default
    (implies (and (force (vl-casestmt-p x))
                  (force (vl-stmt-p x)))
             (vl-stmt-p (vl-casestmt->default x))))

  (defthm vl-exprlist-p-of-vl-casestmt->exprs
    (implies (force (vl-casestmt-p x))
             (vl-exprlist-p (vl-casestmt->exprs x))))

  (defthm vl-stmtlist-p-of-vl-casestmt->bodies
    (implies (and (force (vl-casestmt-p x))
                  (force (vl-stmt-p x)))
             (vl-stmtlist-p (vl-casestmt->bodies x))))

  (defthm len-of-vl-casestmt->bodies
    (implies (force (vl-casestmt-p x))
             (equal (len (vl-casestmt->bodies x))
                    (len (vl-casestmt->exprs x)))))

  (defthm vl-casestmt->casetype-of-vl-casestmt
    (equal (vl-casestmt->casetype (make-vl-casestmt :casetype casetype
                                                    :test test
                                                    :exprs exprs
                                                    :bodies bodies
                                                    :default default
                                                    :atts atts))
           casetype))

  (defthm vl-casestmt->test-of-vl-casestmt
    (equal (vl-casestmt->test (make-vl-casestmt :casetype casetype
                                                :test test
                                                :exprs exprs
                                                :bodies bodies
                                                :default default
                                                :atts atts))
           test))

  (defthm vl-casestmt->default-of-vl-casestmt
    (equal (vl-casestmt->default (make-vl-casestmt :casetype casetype
                                                   :test test
                                                   :exprs exprs
                                                   :bodies bodies
                                                   :default default
                                                   :atts atts))
           default))

  (defthm vl-casestmt->exprs-of-vl-casestmt
    (equal (vl-casestmt->exprs (make-vl-casestmt :casetype casetype
                                                 :test test
                                                 :exprs exprs
                                                 :bodies bodies
                                                 :default default
                                                 :atts atts))
           exprs))

  (defthm vl-casestmt->bodies-of-vl-casestmt
    (equal (vl-casestmt->bodies (make-vl-casestmt :casetype casetype
                                                  :test test
                                                  :exprs exprs
                                                  :bodies bodies
                                                  :default default
                                                  :atts atts))
           bodies))

  (defthm vl-compoundstmt->type-of-vl-casestmt
    (equal (vl-compoundstmt->type (make-vl-casestmt :casetype casetype
                                                    :test test
                                                    :exprs exprs
                                                    :bodies bodies
                                                    :default default
                                                    :atts atts))
           :vl-casestmt))

  (defthm vl-compoundstmt->atts-of-vl-casestmt
    (equal (vl-compoundstmt->atts (make-vl-casestmt :casetype casetype
                                                    :test test
                                                    :exprs exprs
                                                    :bodies bodies
                                                    :default default
                                                    :atts atts))
           atts))


  (defthm acl2-count-of-vl-casestmt->default-weak
    (<= (acl2-count (vl-casestmt->default x))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-vl-casestmt->default-strong
    (implies (consp x)
             (< (acl2-count (vl-casestmt->default x))
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-vl-casestmt->bodies-weak
    (<= (acl2-count (vl-casestmt->bodies x))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-vl-casestmt->bodies-strong
    (implies (consp x)
             (< (acl2-count (vl-casestmt->bodies x))
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear))))



(deflist vl-atomicstmtlist-p (x)
  (vl-atomicstmt-p x)
  :elementp-of-nil nil)

(defsection vl-stmt-atomicstmts
  :parents (vl-stmt-p)
  :short "@(call vl-stmt-atomicstmts) returns a flat list of all atomic
statements in the statement @('x')."

  :long "<p>This is sometimes useful to avoid needing to write a mutually
recursive function to walk over statements.  For instance, if you want to look
at all of the assignments anywhere within a statement, you can first grab all
of the atomic statements, then filter it down to just the assignments, then
process them.</p>"

  (mutual-recursion
   (defund vl-stmt-atomicstmts-exec (x acc)
     (declare (xargs :guard (vl-stmt-p x)
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (cond ((vl-fast-atomicstmt-p x)
            (cons x acc))
           (t
            (vl-stmtlist-atomicstmts-exec (vl-compoundstmt->stmts x) acc))))

   (defund vl-stmtlist-atomicstmts-exec (x acc)
     (declare (xargs :guard (vl-stmtlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         acc
       (let ((acc (vl-stmt-atomicstmts-exec (car x) acc)))
         (vl-stmtlist-atomicstmts-exec (cdr x) acc)))))

  (mutual-recursion
   (defund vl-stmt-atomicstmts (x)
     (declare (xargs :guard (vl-stmt-p x)
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (mbe :logic
          (cond ((vl-atomicstmt-p x)
                 (list x))
                (t
                 (vl-stmtlist-atomicstmts (vl-compoundstmt->stmts x))))
          :exec
          (reverse (vl-stmt-atomicstmts-exec x nil))))

   (defund vl-stmtlist-atomicstmts (x)
     (declare (xargs :guard (vl-stmtlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (mbe :logic
          (if (atom x)
              nil
            (append (vl-stmt-atomicstmts (car x))
                    (vl-stmtlist-atomicstmts (cdr x))))
          :exec
          (reverse (vl-stmtlist-atomicstmts-exec x nil)))))

  (flag::make-flag vl-flag-stmt-atomicstmts-exec
                   vl-stmt-atomicstmts-exec
                   :flag-mapping ((vl-stmt-atomicstmts-exec . stmt)
                                  (vl-stmtlist-atomicstmts-exec . list)))

  (defthm-vl-flag-stmt-atomicstmts-exec lemma
    (stmt (equal (vl-stmt-atomicstmts-exec x acc)
                 (revappend (vl-stmt-atomicstmts x) acc))
          :name vl-stmt-atomicstmts-exec-removal)
    (list (equal (vl-stmtlist-atomicstmts-exec x acc)
                 (revappend (vl-stmtlist-atomicstmts x) acc))
          :name vl-stmtlist-atomicstmts-exec-removal)
    :hints(("Goal"
            :induct (vl-flag-stmt-atomicstmts-exec flag x acc)
            :expand ((vl-stmt-atomicstmts x)
                     (vl-stmtlist-atomicstmts x)
                     (vl-stmt-atomicstmts-exec x acc)
                     (vl-stmtlist-atomicstmts-exec x acc)))))

  (defthm-vl-flag-stmt-p lemma
    (stmt (implies (force (vl-stmt-p x))
                   (vl-atomicstmtlist-p (vl-stmt-atomicstmts x)))
          :name vl-atomicstmtlist-p-of-vl-stmt-atomicstmts)
    (list (implies (force (vl-stmtlist-p x))
                   (vl-atomicstmtlist-p (vl-stmtlist-atomicstmts x)))
          :name vl-atomicstmtlist-p-of-vl-stmtlist-atomicstmts)
    :hints(("Goal"
            :induct (vl-flag-stmt-p flag x)
            :expand ((vl-stmt-atomicstmts x)
                     (vl-stmtlist-atomicstmts x)))))

  (verify-guards vl-stmt-atomicstmts-exec)
  (verify-guards vl-stmt-atomicstmts
                 :hints(("Goal" :in-theory (enable vl-stmt-atomicstmts
                                                   vl-stmtlist-atomicstmts)))))


(defsection vl-filter-blockitems
  :parents (vl-blockitemlist-p)
  :short "Split up blockitems into lists by their type."

  (defund vl-filter-blockitems (x)
    "Returns (MV REGDECLS VARDECLS EVENTDECLS PARAMDECLS)"
    (declare (xargs :guard (vl-blockitemlist-p x)))
    (b* (((when (atom x))
          (mv nil nil nil nil))
         ((mv regdecls vardecls eventdecls paramdecls)
          (vl-filter-blockitems (cdr x))))
      (case (tag (car x))
        (:vl-regdecl   (mv (cons (car x) regdecls) vardecls eventdecls paramdecls))
        (:vl-vardecl   (mv regdecls (cons (car x) vardecls) eventdecls paramdecls))
        (:vl-eventdecl (mv regdecls vardecls (cons (car x) eventdecls) paramdecls))
        (:vl-paramdecl (mv regdecls vardecls eventdecls (cons (car x) paramdecls)))
        (otherwise
         (progn$
          (er hard 'vl-filter-blockitems "Impossible")
          (mv regdecls vardecls eventdecls paramdecls))))))

  (local (in-theory (enable vl-filter-blockitems)))

  (defmvtypes vl-filter-blockitems
    (true-listp true-listp true-listp true-listp))

  (defthm vl-filter-blockitems-basics
    (implies (vl-blockitemlist-p x)
             (let ((ret (vl-filter-blockitems x)))
               (and (vl-regdecllist-p (mv-nth 0 ret))
                    (vl-vardecllist-p (mv-nth 1 ret))
                    (vl-eventdecllist-p (mv-nth 2 ret))
                    (vl-paramdecllist-p (mv-nth 3 ret)))))))



(define vl-simpledelaycontrol-p ((x vl-delaycontrol-p))
  :returns bool
  :parents (vl-delaycontrol-p)
  :short "Recognizer for simple delays by some natural-number amount."
  :inline t
  (vl-expr-resolved-p (vl-delaycontrol->value x)))

(define vl-simpledelaycontrol->ticks ((x (and (vl-delaycontrol-p x)
                                              (vl-simpledelaycontrol-p x))))
  :returns (ticks natp)
  :parents (vl-simpledelaycontrol-p)
  :short "Number of ticks for a simple delay, e.g., @('#5') has 5 ticks."
  :guard-hints (("Goal" :in-theory (enable vl-simpledelaycontrol-p)))
  :inline t
  (lnfix (vl-resolved->val (vl-delaycontrol->value x))))

