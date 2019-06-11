; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
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

(include-book "centaur/meta/unify" :dir :system)

(defxdoc syntax-bind
  :parents (fgl-rewrite-rules)
  :short "Form that can bind a free variable to a value computed from examining
the syntax of other bound variables in the RHS of a rewrite rule."
  :long "<p>The basic syntax of a syntax-bind form is:</p>

@({
 (syntax-bind fresh-variable binding-form)
 })

<p>where fresh-variable must be a variable not previously bound and
binding-form is a term that may mention previously bound variables.  See @(see
fgl-rewrite-rules) for further discussion.</p>")

(defxdoc abort-rewrite
  :parents (fgl-rewrite-rules)
  :short "Form that aborts the application of a rewrite rule when encountered in the RHS of a rule."
  :long "<p>The basic syntax of an abort-rewrite form is:</p>

@({
 (abort-rewrite value-term)
 })

<p>where value-term can be anything.  Usually value-term is selected so that
the rewrite rule is easy to prove -- e.g., it may just be the LHS of the
rule.</p>")

(defun syntax-bind-fn (form untrans-form dummy-var)
  (declare (ignorable form untrans-form)
           (xargs :guard t))
  dummy-var)

;; note: probably need to put this somewhere else
(defmacro syntax-bind (dummy-var form)
  `(syntax-bind-fn
    ,form ',form ,dummy-var))

;; For lack of a better place to put this.
(defun abort-rewrite (x)
  x)

(defevaluator synbind-ev synbind-ev-list ((syntax-bind-fn x y z)) :namedp t)

(local (acl2::def-ev-pseudo-term-fty-support synbind-ev synbind-ev-list))

(local (defthm assoc-when-key
         (implies k
                  (equal (assoc k a)
                         (hons-assoc-equal k a)))))

(define match-syntax-bind ((x pseudo-termp))
  :returns (mv (dummy-var symbolp
                          ;; note: not pseudo-var-p because we indicate no match by returning nil
                          :rule-classes :type-prescription)
               (form pseudo-termp))
  (b* (((mv ok alist)
        (cmr::pseudo-term-unify '(syntax-bind-fn trans-form untrans-form dummy-var)
                           x nil))
       ((unless ok) (mv nil nil))
       (untrans-form (cdr (assoc 'untrans-form alist)))
       (trans-form (cdr (assoc 'trans-form alist)))
       (dummy-var (cdr (assoc 'dummy-var alist)))
       ((unless (And (pseudo-term-case dummy-var :var)
                     (pseudo-term-case untrans-form :quote)))
        (mv nil nil)))
    (mv (acl2::pseudo-term-var->name dummy-var) trans-form))
  ///
  (std::defretd eval-when-<fn>
    (implies dummy-var
             (equal (synbind-ev x a)
                    (cdr (hons-assoc-equal dummy-var a))))
    :hints(("Goal" :expand ((:free (pat x alist) (cmr::pseudo-term-unify pat x alist))
                            (:free (pat x alist) (cmr::pseudo-term-list-unify pat x alist))))))

  (fty::deffixequiv match-syntax-bind)

  (local
   (make-event
    (b* (((mv err val state) (acl2::translate '(syntax-bind foo (and x y z)) t t nil 'match-syntax-bind-works
                                        (w state) state))
         ((when err) (mv err val state)))
      (value `(defthm match-syntax-bind-works
                (b* (((mv dummy-var form) (match-syntax-bind ',val)))
                  (and (equal dummy-var 'foo)
                       (equal form '(if x (if y z 'nil) 'nil))))))))))

