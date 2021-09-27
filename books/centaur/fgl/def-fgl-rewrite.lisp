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
(include-book "binder-rules")

(local (xdoc::set-default-parents fgl-rewrite-rules))

;; We want to add/remove runes from the fgl-rewrite-rules and
;; fgl-branch-merge-rules tables.  To do this properly, we need to know which
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

(defun fgl-binder-rune-lhses (rune world)
  (declare (xargs :mode :program))
  (cond ((eq (car rune) :bformula)
         (b* ((rewrites (collect-cmr-rewrites-for-formula-name (cadr rune) world)))
           (cmr::rewritelist->lhses rewrites)))
        (t
         (b* ((lemmas (collect-lemmas-for-rune `(:rewrite . ,(cdr rune)) world)))
           (collect-lemma-lhses lemmas)))))

(defun fgl-name-to-brewrite-rune (name)
  (cond ((symbolp name) `(:bformula ,name))
        ((and (consp name) (eq (car name) :rewrite))
         `(:brewrite . ,(cdr name)))
        ((and (consp name) (eq (car name) :formula))
         `(:bformula . ,(cdr name)))
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

(defun binder-alist-add-rune-entries (fns rune alist)
  (b* (((when (atom fns)) alist)
       (alist (hons-acons (car fns)
                          (add-to-set-equal rune (fgl-binder-rules-lookup (car fns) alist))
                          alist)))
    (binder-alist-add-rune-entries (cdr fns) rune alist)))

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


(defun add-fgl-rewrite-fn (name alist world)
  (declare (xargs :mode :program))
  (b* ((rune (fgl-name-to-rewrite-rune name))
       (lhses (fgl-rune-lhses rune world))
       (fns (lhses->leading-function-syms lhses))
       ((when (atom fns))
        (er hard? 'add-fgl-rewrite-fn
            "No valid rewrite rules found for ~x0" name)))
    (rewrite-alist-add-rune-entries fns rune alist world)))

(defun remove-fgl-rewrite-fn (name alist world)
  (declare (xargs :mode :program))
  (b* ((rune (fgl-name-to-rewrite-rune name))
       (lhses (fgl-rune-lhses rune world))
       (fns (lhses->leading-function-syms lhses))
       ((when (atom fns))
        (er hard? 'remove-fgl-rewrite-fn
            "No valid rewrite rules found for ~x0" name)))
    (alist-remove-rune-entries fns rune alist)))

(defun add-fgl-branch-merge-fn (name alist world)
  (declare (xargs :mode :program))
  (b* ((rune (fgl-name-to-rewrite-rune name))
       (lhses (fgl-rune-lhses rune world))
       (fns (lhses->branch-function-syms lhses))
       ((when (atom fns))
        (er hard? 'add-fgl-branch-merge-fn
            "No valid branch-merge rules found for ~x0.  Note: The LHS of the ~
             rewrite rule must be an IF with a function call as the THEN ~
             branch.  Due to special handling in the FGL unifier, the rule ~
             will also apply to branch merges where that function call is the ~
             ELSE branch." name)))
    (branch-merge-alist-add-rune-entries fns rune alist)))

(defun remove-fgl-branch-merge-fn (name alist world)
  (declare (xargs :mode :program))
  (b* ((rune (fgl-name-to-rewrite-rune name))
       (lhses (fgl-rune-lhses rune world))
       (fns (lhses->branch-function-syms lhses))
       ((when (atom fns))
        (er hard? 'remove-fgl-branch-merge-fn
            "No valid branch-merge rules found for ~x0" name)))
    (alist-remove-rune-entries fns rune alist)))


(defun add-fgl-brewrite-fn (name alist world)
  (declare (xargs :mode :program))
  (b* ((rune (fgl-name-to-brewrite-rune name))
       (lhses (fgl-binder-rune-lhses rune world))
       (fns (lhses->leading-function-syms lhses))
       ((when (atom fns))
        (er hard? 'add-fgl-rewrite-fn
            "No valid rewrite rules found for ~x0" name)))
    (binder-alist-add-rune-entries fns rune alist)))

(defun remove-fgl-brewrite-fn (name alist world)
  (declare (xargs :mode :program))
  (b* ((rune (fgl-name-to-brewrite-rune name))
       (lhses (fgl-binder-rune-lhses rune world))
       (fns (lhses->leading-function-syms lhses))
       ((when (atom fns))
        (er hard? 'remove-fgl-rewrite-fn
            "No valid rewrite rules found for ~x0" name)))
    (alist-remove-rune-entries fns rune alist)))


(defun add-fgl-rewrites-fn (names alist world)
  (declare (xargs :mode :program))
  (if (atom names)
      alist
    (add-fgl-rewrites-fn (cdr names)
                        (add-fgl-rewrite-fn (car names) alist world)
                        world)))

(defun remove-fgl-rewrites-fn (names alist world)
  (declare (xargs :mode :program))
  (if (atom names)
      alist
    (remove-fgl-rewrites-fn (cdr names)
                           (remove-fgl-rewrite-fn (car names) alist world)
                           world)))

(defun add-fgl-branch-merges-fn (names alist world)
  (declare (xargs :mode :program))
  (if (atom names)
      alist
    (add-fgl-branch-merges-fn (cdr names)
                              (add-fgl-branch-merge-fn (car names) alist world)
                             world)))

(defun remove-fgl-branch-merges-fn (names alist world)
  (declare (xargs :mode :program))
  (if (atom names)
      alist
    (remove-fgl-branch-merges-fn (cdr names)
                                (remove-fgl-branch-merge-fn (car names) alist world)
                                world)))

(defun add-fgl-brewrites-fn (names alist world)
  (declare (xargs :mode :program))
  (if (atom names)
      alist
    (add-fgl-brewrites-fn (cdr names)
                        (add-fgl-brewrite-fn (car names) alist world)
                        world)))

(defun remove-fgl-brewrites-fn (names alist world)
  (declare (xargs :mode :program))
  (if (atom names)
      alist
    (remove-fgl-brewrites-fn (cdr names)
                           (remove-fgl-brewrite-fn (car names) alist world)
                           world)))


(defxdoc add-fgl-rewrites
  :short "Enable some rewrite rules for use in FGL"
  :long "<p>Adds the given rewrite rule runes to the @('fgl-rewrite-rules') table so
that each such rule will be attempted when terms with its LHS's leading
function symbol is encountered.  The exact form of the rule that is used
depends on the invocation: if a name given is simply a symbol, then the formula
of that theorem or function name is used.  If a name is instead a @(':rewrite')
or @(':definition') rune, then the corresponding lemma is used.  A
@(':formula') rune (which is not a valid ACL2 rune but is a valid FGL rune) is
treated the same as a bare symbol.</p>")

(defmacro add-fgl-rewrites (&rest names)
  `(table fgl-rewrite-rules
          nil
          (add-fgl-rewrites-fn ',names (make-fast-alist (table-alist 'fgl-rewrite-rules world)) world)
          :clear))

(defxdoc add-fgl-rewrite
  :parents (add-fgl-rewrites)
  :short "Alias for @('add-fgl-rewrites') that just takes one name.")

(defmacro add-fgl-rewrite (name)
  `(add-fgl-rewrites ,name))

(defxdoc remove-fgl-rewrites
  :short "Disable some rewrite rules' use in FGL."
  :long "<p>Removes the given rewrite rule runes from the @('fgl-rewrite-rules') table
so that they will not be used in FGL.  See @(see add-fgl-rewrites) for details on
rewrite rule runes recognized in FGL.</p>")

(defmacro remove-fgl-rewrites (&rest names)
  `(table fgl-rewrite-rules
          nil
          (remove-fgl-rewrites-fn ',names (make-fast-alist (table-alist 'fgl-rewrite-rules world)) world)
          :clear))

(defxdoc remove-fgl-rewrite
  :parents (remove-fgl-rewrites)
  :short "Alias for @(see remove-fgl-rewrites) that just takes one name.")

(defmacro remove-fgl-rewrite (name)
  `(remove-fgl-rewrites ,name))

(defxdoc add-fgl-branch-merges
  :short "Enable some rewrite rules's use for branch merging in FGL."
  :long "<p>Adds the given rewrite rule runes to the @('fgl-branch-merge-rules') table so
that they can be used to merge @('if') branches in FGL. See @(see
add-fgl-rewrites) for details on rewrite rule runes recognized in FGL.  Each rule
must have as its LHS a call of @('if') with a function call as its @('then')
branch.</p>")


(defmacro add-fgl-branch-merges (&rest names)
  `(table fgl-branch-merge-rules
          nil
          (add-fgl-branch-merges-fn ',names (make-fast-alist (table-alist 'fgl-branch-merge-rules world)) world)
          :clear))

(defxdoc add-fgl-branch-merge
  :parents (add-fgl-branch-merges)
  :short "Alias for @(see add-fgl-branch-merges) that just takes one name.")

(defmacro add-fgl-branch-merge (name)
  `(add-fgl-branch-merges ,name))

(defxdoc remove-fgl-branch-merges
  :short "Disable some rewrite rules' use for branch merging in FGL."
  :long "<p>Removes the given rewrite rule runes from the
@('fgl-branch-merge-rules') table so that they won't be used to merge @('if')
branches in FGL. See @(see add-fgl-rewrites) for details on rewrite rule runes
recognized in FGL.</p>")


(defmacro remove-fgl-branch-merges (&rest names)
  `(table fgl-branch-merge-rules
          nil
          (remove-fgl-branch-merges-fn ',names (make-fast-alist (table-alist 'fgl-branch-merge-rules world)) world)
          :clear))

(defxdoc remove-fgl-branch-merge
  :parents (remove-fgl-branch-merges)
  :short "Alias for @(see remove-fgl-branch-merges) that just takes one name.")

(defmacro remove-fgl-branch-merge (name)
  `(remove-fgl-branch-merges ,name))


(defxdoc add-fgl-brewrites
  :short "Enable some binder rewrite rules for use in FGL"
  :long "<p>Adds the given binder rewrite rule runes to the
@('fgl-binder-rules') table so that each such rule will be attempted when terms
with its LHS's leading function symbol is encountered.  The exact form of the
rule that is used depends on the invocation: if the name given is simply a
symbol, then the formula of that theorem or function name is used.  If the name
is instead a @(':rewrite') rune, then the corresponding lemma is used.  A
@(':formula') rune (which is not a valid ACL2 rune but is a valid FGL rune) is
treated the same as a bare symbol.</p>

<p>The literal runes stored in the table are slightly different than the ones
accepted as input: a formula rune is stored as @('(:bformula name)') whereas a
rewrite rune is stored as @('(:brewrite name)').</p>")


(defmacro add-fgl-brewrites (&rest names)
  `(table fgl-binder-rules
          nil
          (add-fgl-brewrites-fn ',names (make-fast-alist (table-alist 'fgl-binder-rules world)) world)
          :clear))

(defxdoc add-fgl-brewrite
  :parents (add-fgl-brewrites)
  :short "Alias for @(see add-fgl-brewrites) that just takes one name.")

(defmacro add-fgl-brewrite (name)
  `(add-fgl-brewrites ,name))

(defsection def-fgl-brewrite
  :parents (fgl-rewrite-rules)
  :short "Define a binder rewrite rule for FGL to use on term-level objects"
  :long "<p>Just expands to a DEFTHMD followed by an @(see add-fgl-brewrite) event.</p>"

  (defmacro def-fgl-brewrite (name &rest args)
    `(progn (defthmd ,name . ,args)
            (add-fgl-brewrite ,name))))

(defxdoc remove-fgl-brewrites
  :short "Disable some binder rewrite rules' use in FGL."
  :long "<p>Removes the given binder rewrite rule runes from the @('fgl-binder-rules')
table so that they won't be used in FGL. See @(see add-fgl-brewrites) for details
on binder rewrite rule runes recognized in FGL.</p>")

(defmacro remove-fgl-brewrites (&rest names)
  `(table fgl-binder-rules
          nil
          (remove-fgl-brewrites-fn ',names (make-fast-alist (table-alist 'fgl-binder-rules world)) world)
          :clear))

(defxdoc remove-fgl-brewrite
  :parents (remove-fgl-brewrites)
  :short "Alias for @(see remove-fgl-brewrites) that just takes one name.")

(defmacro remove-fgl-brewrite (name)
  `(table fgl-binder-rules
          nil
          (remove-fgl-brewrite-fn ',name (make-fast-alist (table-alist 'fgl-binder-rules world)) world)
          :clear))




(defmacro clean-fgl-rewrite-table ()
  `(table fgl-rewrite-rules
          nil
          (fast-alist-clean (make-fast-alist (table-alist 'fgl-rewrite-rules world)))
          :clear))

(defmacro clean-fgl-branch-merge-table ()
  `(table fgl-branch-merge-rules
          nil
          (fast-alist-clean (make-fast-alist (table-alist 'fgl-branch-merge-rules world)))
          :clear))

(defmacro clean-fgl-binder-table ()
  `(table fgl-binder-rules
          nil
          (fast-alist-clean (make-fast-alist (table-alist 'fgl-binder-rules world)))
          :clear))

(defxdoc add-fgl-primitive
  :short "Register a primitive function for use in rewriting calls of a trigger
          function in FGL."
  :long "<p>This is invoked as follows:</p>
@({
 (add-fgl-primitive trigger-fn primitive-fn)
 })

<p>This invocation adds an entry in the @('fgl-rewrite-rules') table that
allows @('primitive-fn') to be tried when symbolically interpreting
@('trigger-fn') invocations.  For this to work, @('primitive-fn') must be
defined as an FGL primitive and installed in the current attachment for
@('fgl-primitive-fncall-stub') using the @('install-fgl-metafns') event.</p>")


(defmacro add-fgl-primitive (trigger-fn primitive-fn)
  `(table fgl-rewrite-rules
          nil
          (rewrite-alist-add-rune-entries '(,trigger-fn)
                                          ',(fgl-rune-primitive primitive-fn)
                                          (make-fast-alist (table-alist 'fgl-rewrite-rules world))
                                          world)
          :clear))

(defxdoc remove-fgl-primitive
  :short "Deregister a primitive function for use in FGL."
  :long "<p>This is invoked as follows:</p>
@({
 (remove-fgl-primitive trigger-fn primitive-fn)
 })

<p>This invocation removes the entry in the @('fgl-rewrite-rules') table that
allows @('primitive-fn') to be used in symbolic interpretation of
@('trigger-fn') invocations, preventing the use of @('primitive-fn').</p>")

(defmacro remove-fgl-primitive (trigger-fn primitive-fn)
  `(table fgl-rewrite-rules
          nil
          (alist-remove-rune-entries '(,trigger-fn)
                                     ',(fgl-rune-primitive primitive-fn)
                                     (make-fast-alist (table-alist 'fgl-rewrite-rules world)))
          :clear))

(defmacro add-fgl-meta (trigger-fn meta-fn)
  `(table fgl-rewrite-rules
          nil
          (rewrite-alist-add-rune-entries '(,trigger-fn)
                                          ',(fgl-rune-meta meta-fn)
                                          (make-fast-alist (table-alist 'fgl-rewrite-rules world))
                                          world)
          :clear))

(defxdoc add-fgl-meta
  :short "Register a metafunction for use in rewriting calls of a trigger function
          in FGL."
  :long "<p>This is invoked as follows:</p>
@({
 (add-fgl-meta trigger-fn meta-fn)
 })

<p>This invocation adds an entry in the @('fgl-rewrite-rules') table that
allows @('meta-fn') to be used in symbolic interpretation of @('trigger-fn')
invocations.  For this to work, @('meta-fn') must be defined as an FGL
metafunction and installed in the current attachment for
@('fgl-meta-fncall-stub') using the @('install-fgl-metafns') event.</p>")

(defmacro remove-fgl-meta (trigger-fn meta-fn)
  `(table fgl-rewrite-rules
          nil
          (alist-remove-rune-entries '(,trigger-fn)
                                     ',(fgl-rune-meta meta-fn)
                                     (make-fast-alist (table-alist 'fgl-rewrite-rules world)))
          :clear))

(defxdoc remove-fgl-meta
  :short "Deregister a metafunction for use in FGL."
  :long "<p>This is invoked as follows:</p>
@({
 (remove-fgl-meta trigger-fn meta-fn)
 })

<p>This invocation removes the entry in the @('fgl-rewrite-rules') table that
allows @('meta-fn') to be used in symbolic interpretation of @('trigger-fn')
invocations, preventing the use of @('meta-fn').</p>")

(defmacro add-fgl-binder-meta (trigger-fn meta-fn)
  `(table fgl-binder-rules
          nil
          (binder-alist-add-rune-entries '(,trigger-fn)
                                         ',(fgl-binder-rune-bmeta meta-fn)
                                         (make-fast-alist (table-alist 'fgl-binder-rules world)))
          :clear))

(defxdoc add-fgl-binder-meta
  :short "Register a metafunction for use in rewriting binder invocations of a
          trigger function in FGL."
  :long "<p>This is invoked as follows:</p>
@({
 (add-fgl-binder-meta trigger-fn meta-fn)
 })

<p>This invocation adds an entry in the @('fgl-binder-rules') table that allows
@('meta-fn') to be used in symbolic interpretation of @('trigger-fn') binder
invocations.  For this to work, @('meta-fn') must be defined as an FGL binder
metafunction and installed in the current attachment for
@('fgl-binder-fncall-stub') using the @('install-fgl-metafns') event.</p>")

(defmacro remove-fgl-binder-meta (trigger-fn meta-fn)
  `(table fgl-binder-rules
          nil
          (alist-remove-rune-entries '(,trigger-fn)
                                     ',(fgl-binder-rune-bmeta meta-fn)
                                     (make-fast-alist (table-alist 'fgl-binder-rules world)))
          :clear))

(defxdoc remove-fgl-binder-meta
  :short "Deregister a binder metafunction for use in FGL."
  :long "<p>This is invoked as follows:</p>
@({
 (remove-fgl-binder-meta trigger-fn meta-fn)
 })

<p>This invocation removes the entry in the @('fgl-rewrite-rules') table that
allows @('meta-fn') to be used in symbolic interpretation of @('trigger-fn')
binder invocations, preventing the use of @('meta-fn').</p>")


(defxdoc disable-definition
  :short "Disable the use of the given formula in FGL rewriting."
  :long "<p>This is actually just an alias for @('remove-fgl-rewrite').</p>")

(defmacro disable-definition (fnname)
  `(remove-fgl-rewrite ,fnname))

(defxdoc disable-execution
  :short "Disable the use of concrete execution of a function in FGL rewriting."
  :long "<p>This sets the entry for the given function in the @('fgl-fn-modes')
table so that it can't be concretely executed when a call of that function on
concrete values is encountered in FGL rewriting.</p>")

(defmacro disable-execution (fnname)
  `(table fgl-fn-modes
          ',fnname
          (b* ((mode (fgl-function-mode-lookup ',fnname (table-alist 'fgl-fn-modes world))))
            (change-fgl-function-mode mode :dont-concrete-exec t))))

(defxdoc enable-execution
  :short "Enable the use of concrete execution of a function in FGL rewriting."
  :long "<p>This sets the entry for the given function in the @('fgl-fn-modes')
table so that it can be concretely executed when a call of that function on
concrete values is encountered in FGL rewriting.  This is the default setting,
but use of this event can counteract previous uses of @(see
disable-execution).</p>")

(defmacro enable-execution (fnname)
  `(table fgl-fn-modes
          ',fnname
          (b* ((mode (fgl-function-mode-lookup ',fnname (table-alist 'fgl-fn-modes world))))
            (change-fgl-function-mode mode :dont-concrete-exec nil))))

(defxdoc enable-split-ifs
  :parents (fgl-handling-if-then-elses)
  :short "Enable @('if') splitting for arguments of the given function in FGL rewriting."
  :long "<p>This sets the entry for the given function in the @('fgl-fn-modes')
table so that when a call of this function is encountered where one or more of
the arguments' rewritten form is a @('g-ite') (if-then-else) object, then the
FGL interpreter will split the interpretation of that function into cases, as
follows:</p>

@({
 (f ... (if a b c) ...)
 -->
 (if a
    (f ... b ...)
  (f ... c ...))
 })


<p>See @(see fgl-handling-if-then-elses) for more discussion of the handling of
@('g-ite') objects.</p>")


(defmacro enable-split-ifs (fnname)
  `(table fgl-fn-modes
          ',fnname
          (b* ((mode (fgl-function-mode-lookup ',fnname (table-alist 'fgl-fn-modes world))))
            (change-fgl-function-mode mode :split-ifs t))))

(defxdoc disable-split-ifs
  :parents (fgl-handling-if-then-elses)
  :short "Disable @('if') splitting for arguments to the given function in FGL rewriting."
  :long "<p>This sets the entry for the given function in the @('fgl-fn-modes')
table so that the FGL rewriter does not case-split on @('g-ite') arguments to
that function.  This is the default setting, but use of this event can
counteract previous uses of @(see enable-split-ifs).</p>")

(defmacro disable-split-ifs (fnname)
  `(table fgl-fn-modes
          ',fnname
          (b* ((mode (fgl-function-mode-lookup ',fnname (table-alist 'fgl-fn-modes world))))
            (change-fgl-function-mode mode :split-ifs nil))))


(defsection def-fgl-rewrite
  :parents (fgl-rewrite-rules)
  :short "Define a rewrite rule for FGL to use on term-level objects"
  :long
  "<p>FGL can use ACL2-style rewrite rules to simplify term-level symbolic
objects.  However, typically one wants a different theory for ACL2 theorem
proving than one wants to use inside FGL.  @('FGL::DEF-FGL-REWRITE') defines a
rewrite rule that is only used inside FGL:</p>

@({
  (fgl::def-fgl-rewrite my-rewrite-rule
     (implies (and (syntaxp (and (integerp n) (< 0 (integer-length n))))
                   (< 0 m))
              (equal (logand n m)
                     (logcons (b-and (logcar n) (logcar m))
                              (logand (logcdr n) (logcdr m)))))
    :hints ...)
})

<p>This defines a disabled ACL2 rewrite rule called my-rewrite-rule, and adds
my-rewrite-rule to the table of rules FGL is allowed to use. (FGL will still use
it even though it is disabled, as long as it is in that table.)</p>

<p>Def-fgl-rewrite supports syntaxp hypotheses, but the term representation used
is different from ACL2's.  Instead of being bound to TERMPs, the variables are
bound to symbolic objects.  See @(see fgl::fgl-object) for
reference.</p>"

  (defmacro def-fgl-rewrite (name &rest args)
    `(progn (defthmd ,name . ,args)
            (add-fgl-rewrite ,name))))



(defsection def-fgl-branch-merge
  :parents (fgl-rewrite-rules)
  :short "Define a rule for FGL to use in merging IF branches"
  :long
  "<p>Usage:</p>

@({
  (fgl::def-fgl-branch-merge my-branch-merge-rule
     (implies (and (syntaxp (integerp m))
                   (integerp m))
              (equal (if cond (logcons b n) m)
                     (logcons (if cond b (logcar m))
                              (if cond n (logcdr m)))))
   :hints ...)
})

<p>This form creates an ACL2 theorem with :rule-classes nil and installs it in
a table that FGL references when attempting to merge branches of an IF term.</p>

<p>Branch merge rules work similarly to normal rewrite rules, except that:</p>
<ul>
<li>the LHS must be of the form: @('(if <var> <then-term> <else-term>)')</li>
<li>each rule is indexed by the function symbol of the then-term, so then-term
must be a function call.</li>
</ul>"

  (defun def-fgl-branch-merge-fn (name body hints otf-flg)
    `(progn
       (defthmd ,name
         ,body
         :hints ,hints
         :otf-flg ,otf-flg)
       (add-fgl-branch-merge ,name)))

  (defmacro def-fgl-branch-merge (name body &key hints otf-flg)
    (def-fgl-branch-merge-fn name body hints otf-flg)))






(defxdoc def-fgl-program
  :parents (fgl-rewrite-rules)
  :short "Define a function that is logically just NIL but has special extralogical behavior in FGL."
  :long "<p> Because of FGL's @(see bind-var) feature, it isn't always possible
to define a function the way you want it to run in FGL: if you want to use
@('bind-var'), then you must have a free variable in the RHS of the equation
defining the function, which isn't allowed for ACL2 definitions.  Instead, you
may provide a function definition without @('bind-var') calls, disable that
definition for FGL (using @(see disable-definition)), and add an FGL rewrite
rule with @(see def-fgl-rewrite) that rewrites calls of the function to the body
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
                                  (def-fgl-rewrite ,(intern-in-package-of-symbol
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
