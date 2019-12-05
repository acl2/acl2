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
(include-book "std/util/bstar" :dir :system)
(include-book "centaur/misc/beta-reduce-full" :dir :system)

(defun scan-lemmas-for-nume (lemmas nume)
  (declare (xargs :mode :program))
  (b* (((when (endp lemmas)) nil)
       (rule (car lemmas))
       ((when (eql (acl2::access acl2::rewrite-rule rule :nume) nume))
        (cons rule (scan-lemmas-for-nume (cdr lemmas) nume))))
    (scan-lemmas-for-nume (cdr lemmas) nume)))

(defun scan-props-for-nume-lemma (props nume)
  (declare (xargs :mode :program))
  (and (consp props)
       (append (and (eq (cadar props) 'acl2::lemmas)
                    (scan-lemmas-for-nume (cddar props) nume))
               (scan-props-for-nume-lemma (cdr props) nume))))


(defun collect-lemmas-for-rune (rune world)
  (declare (xargs :mode :program))
  (b* ((nume (acl2::runep rune world))
       ((unless nume) nil)
       (segment (acl2::world-to-next-event
                 (cdr (acl2::decode-logical-name (cadr rune) world)))))
    (scan-props-for-nume-lemma (acl2::actual-props segment nil nil) nume)))

(defun collect-lemmas-for-runes (runes world)
  (Declare (xargs :mode :program))
  (if (atom runes)
      nil
    (append (b* ((rune (car runes)))
              (collect-lemmas-for-rune (if (symbolp rune) `(:rewrite ,rune) rune) world))
            (collect-lemmas-for-runes (cdr runes) world))))

(defun gl-rewrite-table-entries-for-lemmas (rune lemmas)
  (if (atom lemmas)
      nil
    (cons (b* ((fnsym (car (acl2::access acl2::rewrite-rule (car lemmas) :lhs))))
            `(table gl-rewrite-rules ',fnsym
                    (b* ((rules (cdr (assoc ',fnsym
                                            (table-alist 'gl-rewrite-rules world)))))
                      (if (member-equal ',rune rules)
                          rules
                        (cons ',rune rules)))))
          (gl-rewrite-table-entries-for-lemmas rune (cdr lemmas)))))

(defun alist-add-gl-rules (rules alist)
  (declare (xargs :mode :program))
  (if (atom rules)
      alist
    (b* ((fnsym (car (acl2::access acl2::rewrite-rule (car rules) :lhs)))
         (rune (acl2::access acl2::rewrite-rule (car rules) :rune))
         (new-alist
          (acl2::put-assoc-eq fnsym (add-to-set-equal rune (cdr (assoc-eq fnsym alist))) alist)))
      (alist-add-gl-rules (cdr rules) new-alist))))

(defun alist-add-gl-rewrite (rune alist world)
  (declare (xargs :mode :program))
  (b* ((rune (if (symbolp rune) `(:rewrite ,rune) rune))
       (rules (collect-lemmas-for-rune rune world)))
    (alist-add-gl-rules rules alist)))


(defun alist-add-gl-rewrites (runes alist world)
  (declare (xargs :mode :program))
  (b* ((rules (collect-lemmas-for-runes runes world)))
    (alist-add-gl-rules rules alist)))



(defun add-gl-rewrite-fn (rune world)
  (declare (xargs :mode :program))
  (b* ((rune (if (symbolp rune) `(:rewrite ,rune) rune))
       (rules (collect-lemmas-for-rune rune world))
       ((unless rules)
        (er hard 'add-gl-rewrite-fn "No rules found for rune ~x0." rune)))
    `(table gl-rewrite-rules nil
            (alist-add-gl-rules ',rules (table-alist 'gl-rewrite-rules world))
            :clear)))

(defmacro add-gl-rewrite (rune)
  `(make-event (add-gl-rewrite-fn ',rune (w state))))




(defun alist-remove-gl-rules (rules alist)
  (declare (xargs :mode :program))
  (if (atom rules)
      alist
    (b* ((fnsym (car (acl2::access acl2::rewrite-rule (car rules) :lhs)))
         (rune (acl2::access acl2::rewrite-rule (car rules) :rune))
         (new-alist
          (acl2::put-assoc-eq fnsym (remove-equal rune (cdr (assoc-eq fnsym alist))) alist)))
      (alist-remove-gl-rules (cdr rules) new-alist))))

(defun alist-remove-gl-rewrite (rune alist world)
  (declare (xargs :mode :program))
  (b* ((rune (if (symbolp rune) `(:rewrite ,rune) rune))
       (rules (collect-lemmas-for-rune rune world)))
    (alist-remove-gl-rules rules alist)))


(defun alist-remove-gl-rewrites (runes alist world)
  (declare (xargs :mode :program))
  (b* ((rules (collect-lemmas-for-runes runes world)))
    (alist-remove-gl-rules rules alist)))



(defun remove-gl-rewrite-fn (rune world)
  (declare (xargs :mode :program))
  (b* ((rune (if (symbolp rune) `(:rewrite ,rune) rune))
       (rules (collect-lemmas-for-rune rune world))
       ((unless rules)
        (er hard 'remove-gl-rewrite-fn "No rules found for rune ~x0." rune)))
    `(table gl-rewrite-rules nil
            (alist-remove-gl-rules ',rules (table-alist 'gl-rewrite-rules world))
            :clear)))

(defmacro remove-gl-rewrite (rune)
  `(make-event (remove-gl-rewrite-fn ',rune (w state))))








(defsection def-gl-rewrite
  :parents (reference term-level-reasoning)
  :short "Define a rewrite rule for GL to use on term-level objects"
  :long
  "<p>GL can use ACL2-style rewrite rules to simplify term-level symbolic
objects.  However, typically one wants a different theory for ACL2 theorem
proving than one wants to use inside GL.  @('GL::DEF-GL-REWRITE') defines a
rewrite rule that is only used inside GL:</p>

@({
  (gl::def-gl-rewrite my-rewrite-rule
     (implies (and (syntaxp (and (integerp n) (< 0 (integer-length n))))
                   (< 0 m))
              (equal (logand n m)
                     (logcons (b-and (logcar n) (logcar m))
                              (logand (logcdr n) (logcdr m)))))
    :hints ...)
})

<p>This defines a disabled ACL2 rewrite rule called my-rewrite-rule, and adds
my-rewrite-rule to the table of rules GL is allowed to use. (GL will still use
it even though it is disabled, as long as it is in that table.)</p>

<p>Def-gl-rewrite supports syntaxp hypotheses, but the term representation used
is different from ACL2's.  Instead of being bound to TERMPs, the variables are
bound to symbolic objects.  See @(see gl::symbolic-objects) for
reference.</p>"

  (defmacro def-gl-rewrite (name &rest args)
    `(progn (defthmd ,name . ,args)
            (add-gl-rewrite ,name))))


(defun gl-rewrite-table-entries-for-lemma-removals (rune lemmas)
  (if (atom lemmas)
      nil
    (cons (b* ((fnsym (car (acl2::access acl2::rewrite-rule (car lemmas) :lhs))))
            `(table gl-rewrite-rules ',fnsym
                    (b* ((rules (cdr (assoc ',fnsym
                                            (table-alist 'gl-rewrite-rules world)))))
                      (if (member-equal ',rune rules)
                          (remove ',rune rules)
                        rules))))
          (gl-rewrite-table-entries-for-lemma-removals rune (cdr lemmas)))))



(defun gl-set-uninterpreted-fn (fn val world)
  (b* ((formals (getprop fn 'formals :none 'current-acl2-world world))
       (fn (if (eq formals :none)
               (cdr (assoc fn (table-alist 'acl2::macro-aliases-table world)))
             fn))
       (formals (if (eq formals :none)
                    (getprop fn 'formals :none 'current-acl2-world world)
                  formals))
       ((when (eq formals :none))
        (er hard? 'gl-set-uninterpreted-fn
            "~x0 is neither a function nor a macro-alias for a function~%" fn)))
    `(table gl-uninterpreted-functions ',fn ,val)))

(defsection gl-set-uninterpreted
  :parents (reference term-level-reasoning)
  :short "Prevent GL from interpreting a function's definition or concretely executing it."
  :long
  "<p>Usage:</p>
@({
  ;; disallow definition expansion and concrete execution
  (gl::gl-set-uninterpreted fnname)
  (gl::gl-set-uninterpreted fnname t) ;; same as above

  ;; disallow definition expansion but allow concrete execution
  (gl::gl-set-uninterpreted fnname :concrete-only)

  ;; disallow concrete execution but allow definition expansion
  (gl::gl-set-uninterpreted fnname :no-concrete)

  ;; remove restrictions
  (gl::gl-set-uninterpreted fnname nil)
  (gl::gl-unset-uninterpreted fnname) ;; same
})
<p>prevents GL from opening the definition of fnname and/or concretely executing
it.  GL will still apply rewrite rules to a call of @('fnname').  If the
call is not rewritten away, symbolic execution of a @('fnname') call will
simply produce an object (of the :g-apply type) representing a call of
@('fnname') on the given arguments.</p>

<p>@('gl::gl-unset-uninterpreted') undoes the effect of @('gl::gl-set-uninterpreted').</p>

<p>Note that @('gl::gl-set-uninterpreted') has virtually no effect when
applied to a GL primitive: a function that has its ``symbolic
counterpart'' built into the GL clause processor you're using.  (It
actually does do a little &mdash; it can prevent the function from being
applied to concrete values before rewrite rules are applied.  But that
could change in the future.)  But what is a GL primitive?  That
depends on the current GL clause processor, and can only be determined
reliably by looking at the definition of the following function
symbol:</p>

@({
(cdr (assoc-eq 'gl::run-gified
               (table-alist 'gl::latest-greatest-gl-clause-proc (w state))))
})

<p>For example, this function symbol is 'gl::glcp-run-gified immediately after
including the community-book @('\"centaur/gl/gl\"').  Now use @(':')@(tsee pe)
on this function symbol.  The body of that definition should be of the form
@('(case fn ...)'), which matches @('fn') against all the GL primitives for the
current GL clause processor.</p>

"

  (defmacro gl-set-uninterpreted (fn &optional (val 't))
    `(make-event
      (gl-set-uninterpreted-fn ',fn ,val (w state)))))

(defmacro gl-unset-uninterpreted (fn)
  `(make-event
    (gl-set-uninterpreted-fn ',fn nil (w state))))

(defun gl-branch-merge-rules (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (cdr (hons-assoc-equal 'gl-branch-merge-rules (table-alist 'gl-branch-merge-rules wrld))))

(defun add-gl-branch-merge-fn (rune)
  (declare (xargs :mode :program))
  (b* ((rune (if (symbolp rune) `(:rewrite ,rune) rune)))
    `(table gl-branch-merge-rules
            'gl-branch-merge-rules
            (add-to-set-equal ',rune (gl-branch-merge-rules world)))))

(defmacro add-gl-branch-merge (rune)
  (add-gl-branch-merge-fn rune))


(defsection def-gl-branch-merge
  :parents (reference term-level-reasoning)
  :short "Define a rule for GL to use in merging IF branches"
  :long
  "<p>Usage:</p>

@({
  (gl::def-gl-branch-merge my-branch-merge-rule
     (implies (and (syntaxp (integerp m))
                   (integerp m))
              (equal (if cond (logcons b n) m)
                     (logcons (if cond b (logcar m))
                              (if cond n (logcdr m)))))
   :hints ...)
})

<p>This form creates an ACL2 theorem with :rule-classes nil and installs it in
a table that GL references when attempting to merge branches of an IF term.</p>

<p>Branch merge rules work similarly to normal rewrite rules, except that:</p>
<ul>
<li>the LHS must be of the form: @('(if <var> <then-term> <else-term>)')</li>
<li>each rule is indexed by the function symbol of the then-term, so then-term
must be a function call.</li>
</ul>"

  (defun def-gl-branch-merge-fn (name body hints otf-flg)
    `(progn
       (defthm ,name
         ,body
         :hints ,hints
         :otf-flg ,otf-flg
         :rule-classes nil)
       (add-gl-branch-merge ,name)))

  (defmacro def-gl-branch-merge (name body &key hints otf-flg)
    (def-gl-branch-merge-fn name body hints otf-flg)))






;; recursively match patterns, e.g.:
;; set (equal (logcar (logcdr (logcdr x))) 1) to t
;; --> set (logcar (logcdr (logcdr x))) to 1
;; --> set (logbitp 0 (logcdr (logcdr x))) to t
;; --> set (logbitp 1 (logcdr x)) to t
;; --> set (logbitp 2 x) to t
;; --> set x to (logior (ash 1 2) x)

(defun translate-pair (pair ctx state)
  (declare (xargs :stobjs state :mode :program))
  (b* (((list a b) pair)
       ((er aa) (acl2::translate a t t t ctx (w state) state))
       ((er bb) (acl2::translate b t t t ctx (w state) state)))
    (value (list aa bb))))

(defun translate-pair-list (pairs ctx state)
  (declare (xargs :stobjs state :mode :program))
  (b* (((when (atom pairs)) (value nil))
       ((er first) (translate-pair (car pairs) ctx state))
       ((er rest) (translate-pair-list (cdr pairs) ctx state)))
    (value (cons first rest))))

(defun def-glcp-ctrex-rewrite-fn (from test tos state)
  (declare (xargs :mode :program :stobjs state))
  (b* (((er fromtrans) (translate-pair from 'def-gplcp-ctrex-rewrite state))
       ((er tostrans) (translate-pair-list tos 'def-gplcp-ctrex-rewrite state))
       ((er testtrans) (acl2::translate test t t t 'def-gplcp-ctrex-rewrite (w state) state))
       (entry (list* fromtrans testtrans tostrans))
       (fnsym (caar fromtrans)))
    (value `(table glcp-ctrex-rewrite
                   ',fnsym
                   (cons ',entry
                         (cdr (assoc ',fnsym (table-alist
                                              'glcp-ctrex-rewrite world))))))))

(defsection def-glcp-ctrex-rewrite
  :parents (reference term-level-reasoning)
  :short "Define a heuristic for GL to use when generating counterexamples"
  :long
  "<p>Usage:</p>

@({
 (gl::def-glcp-ctrex-rewrite
   ;; from:
   (lhs-lvalue lhs-rvalue)
   ;; to:
   (rhs-lvalue rhs-rvalue)
   :test syntaxp-term)
 })
<p>Example:</p>
@({
 (gl::def-glcp-ctrex-rewrite
   ((logbitp n x) t)
   (x (logior (ash 1 n) x))
   :test (quotep n))
})

<p>If GL has generated Boolean variables corresponding to term-level objects,
then an assignment to the Boolean variables does not directly induce an
assignment of ACL2 objects to the ACL2 variables.  Instead, we have terms that
are assigned true or false by the Boolean assignment, and to generate a
counterexample, we must find an assignment for the variables in those terms
that cause the terms to take the required truth values.  Ctrex-rewrite rules
tell GL how to move from a valuation of a term to valuations of its
components.</p>

<p>The example rule above says that if we want @('(logbitp n x)') to be @('t'),
and @('n') is (syntactically) a quoted constant, then assign @('x') a new value
by effectively setting its @('n')th bit to T (that is, bitwise ORing X with the
appropriate mask).</p>

<p>Note that this rule does not always yield the desired result -- for example,
in the case where N is a negative integer.  Because these are just heuristics
for generating counterexamples, there is no correctness requirement and no
checking of these rules.  Bad counterexample rules can't make anything unsound,
but they can cause generated counterexamples to be nonsense.  Be careful!</p>"

  (defmacro def-glcp-ctrex-rewrite (from to &key (test 't))
    `(make-event
      (def-glcp-ctrex-rewrite-fn ',from ',test ',(list to) state))))

(defmacro def-glcp-ctrex-split-rewrite (from tos &key (test 't))
  `(make-event
    (def-glcp-ctrex-rewrite-fn ',from ',test ',tos state)))
