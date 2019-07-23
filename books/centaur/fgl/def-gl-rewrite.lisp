; FGL - A Symbolic Simulation Framework for ACL2
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

(in-package "FGL")
(include-book "std/util/define" :dir :system)
(include-book "xdoc/top" :dir :system)

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
       ((unless nume)
        (er hard? 'collect-lemmas-for-rune
            "Found no nume for ~x0" rune))
       (segment (acl2::world-to-next-event
                 (cdr (acl2::decode-logical-name (cadr rune) world)))))
    (or (scan-props-for-nume-lemma (acl2::actual-props segment nil nil) nume)
        (er hard? 'collect-lemmas-for-rune
            "Found no lemmas for ~x0 (nume: ~x1)" rune nume))))

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



(defmacro add-gl-rewrite (rune)
  `(table gl-rewrite-rules
          nil
          (alist-add-gl-rewrite ',rune (table-alist 'gl-rewrite-rules world) world)
          :clear))




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



(defmacro remove-gl-rewrite (rune)
  `(table gl-rewrite-rules
          nil
          (alist-remove-gl-rewrite ',rune (table-alist 'gl-rewrite-rules world) world)
          :clear))



(defmacro add-gl-definition (rune)
  `(table gl-definition-rules
          nil
          (alist-add-gl-rewrite ',rune (table-alist 'gl-definition-rules world) world)
          :clear))

(defmacro remove-gl-definition (rune)
  `(table gl-definition-rules
          nil
          (alist-remove-gl-rewrite ',rune (table-alist 'gl-definition-rules world) world)
          :clear))

(defmacro disable-definition (fnname)
  `(remove-gl-definition (:definition ,fnname)))


(defsection def-gl-rewrite
  :parents (fgl-rewrite-rules)
  :short "Define a rewrite rule for FGL to use on term-level objects"
  :long
  "<p>FGL can use ACL2-style rewrite rules to simplify term-level symbolic
objects.  However, typically one wants a different theory for ACL2 theorem
proving than one wants to use inside FGL.  @('FGL::DEF-GL-REWRITE') defines a
rewrite rule that is only used inside FGL:</p>

@({
  (fgl::def-gl-rewrite my-rewrite-rule
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
bound to symbolic objects.  See @(see fgl::gl-object) for
reference.</p>"

  (defmacro def-gl-rewrite (name &rest args)
    `(progn (defthmd ,name . ,args)
            (add-gl-rewrite ,name))))


(defsection def-gl-definition
  :parents (fgl-rewrite-rules)
  :short "Define a rewrite rule for FGL to use on term-level objects, after applying primitives"
  :long
  "<p>This is similar to @(see def-gl-rewrite) but rules introduced with
@('def-gl-definition') will be tried after rules introduced with
@('def-gl-rewrite') and also after primitive functions (see @(see
fgl-primitives)). </p>"

  (defmacro def-gl-definition (name &rest args)
    `(progn (defthmd ,name . ,args)
            (add-gl-definition ,name))))


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



;; (defun gl-set-uninterpreted-fn (fn val world)
;;   (b* ((formals (getprop fn 'formals :none 'current-acl2-world world))
;;        (fn (if (eq formals :none)
;;                (cdr (assoc fn (table-alist 'acl2::macro-aliases-table world)))
;;              fn))
;;        (formals (if (eq formals :none)
;;                     (getprop fn 'formals :none 'current-acl2-world world)
;;                   formals))
;;        ((when (eq formals :none))
;;         (er hard? 'gl-set-uninterpreted-fn
;;             "~x0 is neither a function nor a macro-alias for a function~%" fn)))
;;     `(table gl-uninterpreted-functions ',fn ,val)))

;; (defsection gl-set-uninterpreted
;;   :parents (fgl-rewrite-rules)
;;   :short "Prevent GL from interpreting a function's definition or concretely executing it."
;;   :long
;;   "<p>Usage:</p>
;; @({
;;   ;; disallow definition expansion and concrete execution
;;   (gl::gl-set-uninterpreted fnname)
;;   (gl::gl-set-uninterpreted fnname t) ;; same as above

;;   ;; disallow definition expansion but allow concrete execution
;;   (gl::gl-set-uninterpreted fnname :concrete-only)

;;   ;; disallow concrete execution but allow definition expansion
;;   (gl::gl-set-uninterpreted fnname :no-concrete)

;;   ;; remove restrictions
;;   (gl::gl-set-uninterpreted fnname nil)
;;   (gl::gl-unset-uninterpreted fnname) ;; same
;; })
;; <p>prevents GL from opening the definition of fnname and/or concretely executing
;; it.  GL will still apply rewrite rules to a call of @('fnname').  If the
;; call is not rewritten away, symbolic execution of a @('fnname') call will
;; simply produce an object (of the :g-apply type) representing a call of
;; @('fnname') on the given arguments.</p>

;; <p>@('gl::gl-unset-uninterpreted') undoes the effect of @('gl::gl-set-uninterpreted').</p>

;; <p>Note that @('gl::gl-set-uninterpreted') has virtually no effect when
;; applied to a GL primitive: a function that has its ``symbolic
;; counterpart'' built into the GL clause processor you're using.  (It
;; actually does do a little &mdash; it can prevent the function from being
;; applied to concrete values before rewrite rules are applied.  But that
;; could change in the future.)  But what is a GL primitive?  That
;; depends on the current GL clause processor, and can only be determined
;; reliably by looking at the definition of the following function
;; symbol:</p>

;; @({
;; (cdr (assoc-eq 'gl::run-gified
;; 	       (table-alist 'gl::latest-greatest-gl-clause-proc (w state))))
;; })

;; <p>For example, this function symbol is 'gl::glcp-run-gified immediately after
;; including the community-book @('\"centaur/gl/gl\"').  Now use @(':')@(tsee pe)
;; on this function symbol.  The body of that definition should be of the form
;; @('(case fn ...)'), which matches @('fn') against all the GL primitives for the
;; current GL clause processor.</p>

;; "

;;   (defmacro gl-set-uninterpreted (fn &optional (val 't))
;;     `(make-event
;;       (gl-set-uninterpreted-fn ',fn ,val (w state)))))

;; (defmacro gl-unset-uninterpreted (fn)
;;   `(make-event
;;     (gl-set-uninterpreted-fn ',fn nil (w state))))

(defun gl-branch-merge-rules (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (cdr (hons-assoc-equal 'gl-branch-merge-rules (table-alist 'gl-branch-merge-rules wrld))))

(defun find-gl-branch-merge-lemma (lemmas)
  (b* (((when (atom lemmas)) nil)
       (x (car lemmas))
       (lhs (acl2::access acl2::rewrite-rule x :lhs))
       ((unless (case-match lhs
                  (('if & (fn . &) &)
                   (and (symbolp fn)
                        (not (eq fn 'quote))))
                  (& nil)))
        (find-gl-branch-merge-lemma (cdr lemmas))))
    x))
    
(defun check-gl-branch-merge-rule-fn (rune wrld)
  (Declare (Xargs :guard (plist-worldp wrld)
                  :mode :program))
  (b* ((lemmas (collect-lemmas-for-rune rune wrld))
       ((unless (find-gl-branch-merge-lemma lemmas))
        (er hard? 'check-gl-branch-merge-rule-fn
            "Couldn't find a suitable branch merge rule named ~x0.  Such a ~
             rule ought to have IF as the leading function symbol of the LHS." rune)))
    '(value-triple :ok)))
       

(defmacro check-gl-branch-merge-rule (rune)
  `(make-event (check-gl-branch-merge-rule-fn ',rune (w state))))

(defun add-gl-branch-merge-fn (rune)
  (declare (xargs :mode :program))
  (b* ((rune (if (symbolp rune) `(:rewrite ,rune) rune)))
    `(progn
       (check-gl-branch-merge-rule ,rune)
       (table gl-branch-merge-rules
              'gl-branch-merge-rules
              (add-to-set-equal ',rune (gl-branch-merge-rules world))))))

(defmacro add-gl-branch-merge (rune)
  (add-gl-branch-merge-fn rune))


(defsection def-gl-branch-merge
  :parents (fgl-rewrite-rules)
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
         :otf-flg ,otf-flg)
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

;; (defsection def-glcp-ctrex-rewrite
;;   :parents (reference term-level-reasoning)
;;   :short "Define a heuristic for GL to use when generating counterexamples"
;;   :long
;;   "<p>Usage:</p>

;; @({
;;  (gl::def-glcp-ctrex-rewrite
;;    ;; from:
;;    (lhs-lvalue lhs-rvalue)
;;    ;; to:
;;    (rhs-lvalue rhs-rvalue)
;;    :test syntaxp-term)
;;  })
;; <p>Example:</p>
;; @({
;;  (gl::def-glcp-ctrex-rewrite
;;    ((logbitp n x) t)
;;    (x (logior (ash 1 n) x))
;;    :test (quotep n))
;; })

;; <p>If GL has generated Boolean variables corresponding to term-level objects,
;; then an assignment to the Boolean variables does not directly induce an
;; assignment of ACL2 objects to the ACL2 variables.  Instead, we have terms that
;; are assigned true or false by the Boolean assignment, and to generate a
;; counterexample, we must find an assignment for the variables in those terms
;; that cause the terms to take the required truth values.  Ctrex-rewrite rules
;; tell GL how to move from a valuation of a term to valuations of its
;; components.</p>

;; <p>The example rule above says that if we want @('(logbitp n x)') to be @('t'),
;; and @('n') is (syntactically) a quoted constant, then assign @('x') a new value
;; by effectively setting its @('n')th bit to T (that is, bitwise ORing X with the
;; appropriate mask).</p>

;; <p>Note that this rule does not always yield the desired result -- for example,
;; in the case where N is a negative integer.  Because these are just heuristics
;; for generating counterexamples, there is no correctness requirement and no
;; checking of these rules.  Bad counterexample rules can't make anything unsound,
;; but they can cause generated counterexamples to be nonsense.  Be careful!</p>"

;;   (defmacro def-glcp-ctrex-rewrite (from to &key (test 't))
;;     `(make-event
;;       (def-glcp-ctrex-rewrite-fn ',from ',test ',(list to) state))))

;; (defmacro def-glcp-ctrex-split-rewrite (from tos &key (test 't))
;;   `(make-event
;;     (def-glcp-ctrex-rewrite-fn ',from ',test ',tos state)))

(defxdoc def-fgl-program
  :parents (fgl-rewrite-rules)
  :short "Define a function that is logically just NIL but has special extralogical behavior in FGL."
  :long "<p> Because of FGL's @(see bind-var) feature, it isn't always possible
to define a function the way you want it to run in FGL: if you want to use
@('bind-var'), then you must have a free variable in the RHS of the equation
defining the function, which isn't allowed for ACL2 definitions.  Instead, you
may provide a function definition without @('bind-var') calls, disable that
definition for FGL (using @(see disable-definition)), and add an FGL rewrite
rule with @(see def-gl-rewrite) that rewrites calls of the function to the body
containing the bind-var calls.</p>

<p>@('Def-fgl-program') provides a convenient macro for this. It wraps @(see
define) such that all the usual arguments for define may be used.  It may also
contain the additional keyword args @(':equiv'), giving the equivalence
relation for the generated rewrite rule (defaulting to @('all-equiv')), and
@(':fgl-hints'), which allows hints to be passed to the proof for the rewrite
rule.  Instead of providing the given function body as the body for the
@('define'), it modifies it as follows: if @(':equiv') is provided, it searches
the given body for calls of @('bind-var') and @('syntax-bind') and replaces
them with @('nil'), otherwise, it just provides a body of @('nil').</p>")


(defun remove-bind-var-calls (x)
  (cond ((atom x) x)
        ((and (consp x)
              (or (eq (car x) 'bind-var)
                  (eq (car x) 'syntax-bind))
              (consp (cdr x))
              (symbolp (cadr x))
              (cadr x)
              (consp (cddr x)))
         nil)
        (t (cons (remove-bind-var-calls (car x))
                 (remove-bind-var-calls (cdr x))))))
    


(defun def-fgl-program-fn (name args world)
  (declare (xargs :mode :program))
  (b* (((std::defguts guts) (std::parse-define name args '(:equiv :fgl-hints) world))
       ;; ugh, stores the fully constructed DEFUN in the guts, which we need to modify
       (body (car (last guts.main-def)))
       (nil-body-p (not (assoc :equiv guts.kwd-alist)))
       (def-body (if nil-body-p
                     nil
                   (remove-bind-var-calls body)))
       (new-main-def (append (butlast guts.main-def 1)
                             (list def-body)))
       (new-rest-events (append guts.rest-events
                                `((fgl::disable-definition ,name)
                                  (fgl::def-gl-rewrite ,(intern-in-package-of-symbol
                                                         (concatenate 'string (symbol-name name) "-FGL")
                                                         name)
                                    (,(std::getarg :equiv 'all-equiv guts.kwd-alist)
                                     (,name . ,(std::formallist->names guts.formals))
                                     ,body)
                                    :hints ,(cdr (assoc :fgl-hints guts.kwd-alist))))))
       (new-kwd-alist (if nil-body-p
                          ;; If we're using a body of NIL, force :ignore-ok and :irrelevant-formals-ok
                          `((:ignore-ok . t)
                            (:irrelevant-formals-ok . t)
                            . ,guts.kwd-alist)
                        guts.kwd-alist))
       (new-guts (std::change-defguts guts
                                      :main-def new-main-def
                                      :rest-events new-rest-events
                                      :pe-entry `(def-fgl-program ,name . ,args)
                                      :kwd-alist new-kwd-alist)))
    (std::events-from-guts new-guts world)))

(defmacro def-fgl-program (name &rest args)
  (let* ((verbose-tail (member :verbosep args))
         (verbosep (and verbose-tail (cadr verbose-tail))))
    `(with-output
       :stack :push
       ,@(and (not verbosep)
              '(:on (acl2::error) :off :all))
       (make-event
        (def-fgl-program-fn ',name ',args (w state))))))
