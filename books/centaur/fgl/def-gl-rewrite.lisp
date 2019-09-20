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
(include-book "rules")

;; We want to add/remove runes from the gl-rewrite-rules and
;; gl-branch-merge-rules tables.  To do this properly, we need to know which
;; leading function symbols (for rewrite rules) and branch function symbols
;; (for branch merge rules) to store/delete them under.  Since a rune can stand
;; for more than one rule, we may need to store/delete them under multiple
;; functions' entries, even though we're storing the FGL rune and not an
;; fgl-rule or lemma structure.  To handle all cases as smoothly as possible,
;; we'll start with a function that returns the set of LHSes for a rune.

;; =======================================================================
;; Find all the lemmas that have a given rune -- :rewrite or :definition.
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

;; ====================================================
;; For collecting rules from a term we have cmr::parse-rewrites-from-term.
;; Wrap this to get it from a name.
(define collect-cmr-rewrites-for-formula-name ((name symbolp) (world plist-worldp))
  :returns (rewrites cmr::rewritelist-p)
  :verify-guards nil
  (b* ((form (acl2::meta-extract-formula-w name world))
       ((mv err rewrites) (cmr::parse-rewrites-from-term form world))
       ((when (and err (not rewrites)))
        (er hard? 'collect-cmr-rewrites-for-formula-name
            "No rewrites parsed from ~x0: ~@1" name err)))
    (and err
         (cw "Warning: incomplete conversion from formula to rewrites for ~x0: ~@1~%" name err))
    rewrites))

;; ====================================================
;; Collect the LHSes from a list of lemmas.

(defun collect-lemma-lhses (lemmas)
  (Declare (xargs :mode :program))
  (if (atom lemmas)
      nil
    (cons (acl2::access acl2::rewrite-rule (car lemmas) :lhs)
          (collect-lemma-lhses (cdr lemmas)))))

;; ====================================================
;; Collect the LHSes from a list of cmr rewrites.
#!cmr
(define rewritelist->lhses ((x rewritelist-p))
  :returns (lhses pseudo-term-listp)
  (if (atom x)
      nil
    (cons (rewrite->lhs (car x))
          (rewritelist->lhses (cdr x)))))

;; ====================================================
;; Find the LHSes for a name signifying a formula, a :formula FGL rune, or a :rewrite/:definition rune.
(defun fgl-rune-lhses (rune world)
  (declare (xargs :mode :program))
  (cond ((eq (car rune) :formula)
         (b* ((rewrites (collect-cmr-rewrites-for-formula-name (cadr rune) world)))
           (cmr::rewritelist->lhses rewrites)))
        (t
         (b* ((lemmas (collect-lemmas-for-rune rune world)))
           (collect-lemma-lhses lemmas)))))

(defun fgl-name-to-rewrite-rune (name)
  (cond ((symbolp name) `(:formula ,name))
        ((and (consp name)
              (member-eq (car name) '(:rewrite :definition :formula)))
         name)
        (t (er hard? 'fgl-name-to-rewrite-rune
               "The name of a rewrite rule must either be a bare symbol or a ~
                :rewrite, :definition, or :formula FGL rune -- ~x0 is not." name))))

(define lhses->leading-function-syms ((lhses pseudo-term-listp))
  (b* (((when (atom lhses)) nil)
       (lhs (car lhses)))
    (pseudo-term-case lhs
      :fncall (add-to-set-eq lhs.fn (lhses->leading-function-syms (cdr lhses)))
      :otherwise (lhses->leading-function-syms (cdr lhses)))))

(define lhses->branch-function-syms ((lhses pseudo-term-listp))
  (b* (((when (atom lhses)) nil)
       (lhs (car lhses)))
    (pseudo-term-case lhs
      :fncall (if (and (eq lhs.fn 'if)
                       (eql (len lhs.args) 3))
                  (b* ((arg2 (second lhs.args)))
                    (pseudo-term-case arg2
                      :fncall (add-to-set-eq arg2.fn (lhses->branch-function-syms (cdr lhses)))
                      :otherwise (lhses->branch-function-syms (cdr lhses))))
                (lhses->branch-function-syms (cdr lhses)))
      :otherwise (lhses->branch-function-syms (cdr lhses)))))


(defun branch-merge-alist-add-rune-entries (fns rune alist)
  (b* (((when (atom fns)) alist)
       (alist (hons-acons (car fns)
                          (add-to-set-equal rune (fgl-branch-merge-rules-lookup (car fns) alist))
                          alist)))
    (branch-merge-alist-add-rune-entries (cdr fns) rune alist)))

;; Need a separate version of this because we want to use fgl-rewrite-rules-lookup.
(defun rewrite-alist-add-rune-entries (fns rune alist world)
  (b* (((when (atom fns)) alist)
       (alist (hons-acons (car fns)
                          (add-to-set-equal rune (fgl-rewrite-rules-lookup (car fns) alist world))
                          alist)))
    (rewrite-alist-add-rune-entries (cdr fns) rune alist world)))

(defun alist-remove-rune-entries (fns rune alist)
  (b* (((when (atom fns)) alist)
       (alist (hons-acons (car fns)
                          (remove-equal rune (cdr (hons-get (car fns) alist)))
                          alist)))
    (alist-remove-rune-entries (cdr fns) rune alist)))
    

(defun add-gl-rewrite-fn (name alist world)
  (declare (xargs :mode :program))
  (b* ((rune (fgl-name-to-rewrite-rune name))
       (lhses (fgl-rune-lhses rune world))
       (fns (lhses->leading-function-syms lhses))
       ((when (atom fns))
        (er hard? 'add-gl-rewrite-fn
            "No valid rewrite rules found for ~x0" name)))
    (rewrite-alist-add-rune-entries fns rune alist world)))

(defun remove-gl-rewrite-fn (name alist world)
  (declare (xargs :mode :program))
  (b* ((rune (fgl-name-to-rewrite-rune name))
       (lhses (fgl-rune-lhses rune world))
       (fns (lhses->leading-function-syms lhses))
       ((when (atom fns))
        (er hard? 'remove-gl-rewrite-fn
            "No valid rewrite rules found for ~x0" name)))
    (alist-remove-rune-entries fns rune alist)))

(defun add-gl-branch-merge-fn (name alist world)
  (declare (xargs :mode :program))
  (b* ((rune (fgl-name-to-rewrite-rune name))
       (lhses (fgl-rune-lhses rune world))
       (fns (lhses->branch-function-syms lhses))
       ((when (atom fns))
        (er hard? 'add-gl-branch-merge-fn
            "No valid branch-merge rules found for ~x0" name)))
    (branch-merge-alist-add-rune-entries fns rune alist)))

(defun remove-gl-branch-merge-fn (name alist world)
  (declare (xargs :mode :program))
  (b* ((rune (fgl-name-to-rewrite-rune name))
       (lhses (fgl-rune-lhses rune world))
       (fns (lhses->branch-function-syms lhses))
       ((when (atom fns))
        (er hard? 'remove-gl-branch-merge-fn
            "No valid branch-merge rules found for ~x0" name)))
    (alist-remove-rune-entries fns rune alist)))


(defun add-gl-rewrites-fn (names alist world)
  (declare (xargs :mode :program))
  (if (atom names)
      alist
    (add-gl-rewrites-fn (cdr names)
                        (add-gl-rewrite-fn (car names) alist world)
                        world)))

(defun remove-gl-rewrites-fn (names alist world)
  (declare (xargs :mode :program))
  (if (atom names)
      alist
    (remove-gl-rewrites-fn (cdr names)
                           (remove-gl-rewrite-fn (car names) alist world)
                           world)))

(defun add-gl-branch-merges-fn (names alist world)
  (declare (xargs :mode :program))
  (if (atom names)
      alist
    (add-gl-branch-merges-fn (cdr names)
                             (add-gl-branch-merge-fn (car names) alist world)
                             world)))

(defun remove-gl-branch-merges-fn (names alist world)
  (declare (xargs :mode :program))
  (if (atom names)
      alist
    (remove-gl-branch-merges-fn (cdr names)
                                (remove-gl-branch-merge-fn (car names) alist world)
                                world)))



(defmacro add-gl-rewrite (name)
  `(table gl-rewrite-rules
          nil
          (add-gl-rewrite-fn ',name (make-fast-alist (table-alist 'gl-rewrite-rules world)) world)
          :clear))

(defmacro remove-gl-rewrite (name)
  `(table gl-rewrite-rules
          nil
          (remove-gl-rewrite-fn ',name (make-fast-alist (table-alist 'gl-rewrite-rules world)) world)
          :clear))

(defmacro add-gl-branch-merge (name)
  `(table gl-branch-merge-rules
          nil
          (add-gl-branch-merge-fn ',name (make-fast-alist (table-alist 'gl-branch-merge-rules world)) world)
          :clear))

(defmacro remove-gl-branch-merge (name)
  `(table gl-branch-merge-rules
          nil
          (remove-gl-branch-merge-fn ',name (make-fast-alist (table-alist 'gl-branch-merge-rules world)) world)
          :clear))


(defmacro add-gl-rewrites (&rest names)
  `(table gl-rewrite-rules
          nil
          (add-gl-rewrites-fn ',names (make-fast-alist (table-alist 'gl-rewrite-rules world)) world)
          :clear))

(defmacro remove-gl-rewrites (&rest names)
  `(table gl-rewrite-rules
          nil
          (remove-gl-rewrites-fn ',names (make-fast-alist (table-alist 'gl-rewrite-rules world)) world)
          :clear))

(defmacro add-gl-branch-merges (&rest names)
  `(table gl-branch-merge-rules
          nil
          (add-gl-branch-merges-fn ',names (make-fast-alist (table-alist 'gl-branch-merge-rules world)) world)
          :clear))

(defmacro remove-gl-branch-merges (&rest names)
  `(table gl-branch-merge-rules
          nil
          (remove-gl-branch-merges-fn ',names (make-fast-alist (table-alist 'gl-branch-merge-rules world)) world)
          :clear))

(defmacro clean-gl-rewrite-table ()
  `(table gl-rewrite-rules
          nil
          (fast-alist-clean (make-fast-alist (table-alist 'gl-rewrite-rules world)))
          :clear))

(defmacro clean-gl-branch-merge-table ()
  `(table gl-branch-merge-rules
          nil
          (fast-alist-clean (make-fast-alist (table-alist 'gl-branch-merge-rules world)))
          :clear))


(defmacro add-gl-primitive (trigger-fn primitive-fn)
  `(table gl-rewrite-rules
          nil
          (rewrite-alist-add-rune-entries '(,trigger-fn)
                                          ',(fgl-rune-primitive primitive-fn)
                                          (make-fast-alist (table-alist 'gl-rewrite-rules world))
                                          world)
          :clear))

(defmacro remove-gl-primitive (trigger-fn primitive-fn)
  `(table gl-rewrite-rules
          nil
          (alist-remove-rune-entries '(,trigger-fn)
                                     ',(fgl-rune-primitive primitive-fn)
                                     (make-fast-alist (table-alist 'gl-rewrite-rules world)))
          :clear))

(defmacro add-gl-meta (trigger-fn meta-fn)
  `(table gl-rewrite-rules
          nil
          (rewrite-alist-add-rune-entries '(,trigger-fn)
                                          ',(fgl-rune-meta meta-fn)
                                          (make-fast-alist (table-alist 'gl-rewrite-rules world))
                                          world)
          :clear))

(defmacro remove-gl-meta (trigger-fn meta-fn)
  `(table gl-rewrite-rules
          nil
          (alist-remove-rune-entries '(,trigger-fn)
                                     ',(fgl-rune-meta meta-fn)
                                     (make-fast-alist (table-alist 'gl-rewrite-rules world)))
          :clear))



(defmacro disable-definition (fnname)
  `(remove-gl-rewrite ,fnname))

(defmacro disable-execution (fnname)
  `(table gl-fn-modes
          ',fnname
          (b* ((mode (gl-function-mode-lookup ',fnname (table-alist 'gl-fn-modes world))))
            (change-gl-function-mode mode :dont-concrete-exec t))))

(defmacro enable-execution (fnname)
  `(table gl-fn-modes
          ',fnname
          (b* ((mode (gl-function-mode-lookup ',fnname (table-alist 'gl-fn-modes world))))
            (change-gl-function-mode mode :dont-concrete-exec nil))))

(defmacro enable-split-ifs (fnname)
  `(table gl-fn-modes
          ',fnname
          (b* ((mode (gl-function-mode-lookup ',fnname (table-alist 'gl-fn-modes world))))
            (change-gl-function-mode mode :split-ifs t))))

(defmacro disable-split-ifs (fnname)
  `(table gl-fn-modes
          ',fnname
          (b* ((mode (gl-function-mode-lookup ',fnname (table-alist 'gl-fn-modes world))))
            (change-gl-function-mode mode :split-ifs nil))))


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



(defsection def-gl-branch-merge
  :parents (fgl-rewrite-rules)
  :short "Define a rule for GL to use in merging IF branches"
  :long
  "<p>Usage:</p>

@({
  (fgl::def-gl-branch-merge my-branch-merge-rule
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
       (defthmd ,name
         ,body
         :hints ,hints
         :otf-flg ,otf-flg)
       (add-gl-branch-merge ,name)))

  (defmacro def-gl-branch-merge (name body &key hints otf-flg)
    (def-gl-branch-merge-fn name body hints otf-flg)))






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
relation for the generated rewrite rule (defaulting to @('unequiv')), and
@(':fgl-hints'), which allows hints to be passed to the proof for the rewrite
rule.  Instead of providing the given function body as the body for the
@('define'), it modifies it as follows: if @(':equiv') is provided, it searches
the given body for calls of @('bind-var') and @('syntax-bind') and replaces
them with their second arguments; otherwise, it just provides a body of @('nil').</p>")


(defun remove-bind-var-calls (x)
  (cond ((atom x) x)
        ((and (consp x)
              (or (eq (car x) 'bind-var)
                  (eq (car x) 'syntax-bind))
              (consp (cdr x))
              (symbolp (cadr x))
              (cadr x)
              (consp (cddr x)))
         `(non-exec ,(remove-bind-var-calls (caddr x))))
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
                                `((disable-definition ,name)
                                  (disable-execution ,name)
                                  (def-gl-rewrite ,(intern-in-package-of-symbol
                                                         (concatenate 'string (symbol-name name) "-FGL")
                                                         name)
                                    (,(std::getarg :equiv 'unequiv guts.kwd-alist)
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
