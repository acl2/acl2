; Instantiate hint
; Copyright (C) 2012 Centaur Technology
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
(include-book "unify-subst")
(include-book "tools/flag" :dir :system)
(include-book "std/util/bstar" :dir :system)

(defxdoc instantiate-thm-for-matching-terms
  :parents (computed-hints)
  :short "A computed hint which produces :use hints of the given theorem, based
on occurences of a pattern in the current goal clause."

  :long "<p>Syntax: @(call instantiate-thm-for-matching-terms).</p>

<p>Arguments: THM is a theorem/definition name or rune, SUBST is a list of
pairs such as</p>

@({
   ((var1 sub1)
    (var2 sub2) ... )
})

<p>where each vari is a variable name and each sub1 is a term, usually
containing free variables that are also free in PATTERN, and PATTERN is a
pattern (pseudo-term) to be matched against the clause.</p>

<p>We translate the PATTERN and each term in the SUBST, so it's ok to use
macros etc. within them.</p>

<p>For each subterm of CLAUSE that matches PATTERN, the unifying substitution
is computed and applied to each of the subi terms in the SUBST.</p>

<p>For example, if I have some theorem FOO-BOUND, such as:</p>

@({
    (defthm foo-bound
      (< (foo a b) (max (g a) (g b))))
})

<p>and I'm proving the goal:</p>

@({
   (implies (and (p (foo (bar z) (baz q)))
                 (q (bar z) (buz y)))
            (r (foo (baz q) (bar y))))
})

<p>and I provide the computed hint</p>

@({
    (instantiate-thm-for-matching-terms foo-bound
                                        ((a c) (b d))
                                        (foo c d))
})

<p>this produces the hint:</p>

@({
    :use ((:instance foo-bound
           (a (bar z)) (b (baz q)))
          (:instance foo-bound
           (a (baz q)) (b (bar y))))
})

<p>The process by which this happens: The provided pattern @('(foo c d)') is
matched against the clause, which contains two unifying instances,</p>

@({
    c -> (bar z), d -> (baz q)
})

<p>and</p>

@({
    c -> (baz q), d -> (bar y).
})

<p>These two unifying substitutions are applied to the user-provided
 substitution @('((a c) (b d))') to obtain the two instantiations.</p>

<p>Note: you may want to qualify this computed hint with
STABLE-UNDER-SIMPLIFICATIONP or other conditions, and perhaps disable the
theorem used.  For example:</p>

@({
    :hints ((and stable-under-simplificationp
                 (let ((res (instantiate-thm-for-matching-terms
                             foo-bound ((a c) (b d)) (foo c d))))
                   (and res (append res '(:in-theory (disable foo-bound)))))))
})")

(mutual-recursion
 (defun find-matching-terms (pattern restr x)
   (declare (xargs :guard (and (pseudo-termp pattern)
                               (alistp restr)
                               (pseudo-termp x))
                   :verify-guards nil))
   (b* (((when (or (mbe :logic (atom x) :exec (symbolp x))
                   (eq (car x) 'quote)))
         nil)
        ((mv succ1 alist1)
         (simple-one-way-unify pattern x restr))
        (alists (find-matching-terms-list pattern restr (cdr x))))
     (if (and succ1 (not (member-equal alist1 alists)))
         (cons alist1 alists)
       alists)))

 (defun find-matching-terms-list (pattern restr x)
   (declare (xargs :guard (and (pseudo-termp pattern)
                               (alistp restr)
                               (pseudo-term-listp x))))
   (if (endp x)
       nil
     (union-equal (find-matching-terms pattern restr (car x))
                  (find-matching-terms-list pattern restr (cdr x))))))

(make-flag find-matching-terms-flg find-matching-terms)

(defthm-find-matching-terms-flg
  (defthm true-listp-find-matching-terms
    (true-listp (find-matching-terms pattern restr x))
    :rule-classes (:rewrite :type-prescription)
    :flag find-matching-terms)
  (defthm true-listp-find-matching-terms-list
    (true-listp (find-matching-terms-list pattern restr x))
    :rule-classes (:rewrite :type-prescription)
    :flag find-matching-terms-list))

(verify-guards find-matching-terms)

(program)
(set-state-ok t)

(defun make-subst-for-match (subst match)
  (if (atom subst)
      nil
    (cons (list (caar subst) (substitute-into-term (cadar subst) match))
          (make-subst-for-match (cdr subst) match))))

(defun make-insts-for-matches (thm subst matches)
  (if (atom matches)
      nil
    (cons `(:instance ,thm . ,(make-subst-for-match subst (car matches)))
          (make-insts-for-matches thm subst (cdr matches)))))

(defun translate-subst-for-instantiate (subst state)
  (b* (((when (atom subst))
        (value-cmp nil))
       ((when (or (atom (car subst))
                  (atom (cdar subst))))
        (cw "skipping malformed substitution pair: ~x0~%" (car subst))
        (translate-subst-for-instantiate (cdr subst) state))
       ((cmp tterm)
        (translate-cmp (cadar subst) t t t 'instantiate-thm-for-matching-terms
                       (w state)
                       (default-state-vars t)))
       ((cmp rest)
        (translate-subst-for-instantiate (cdr subst) state)))
    (value-cmp (cons (list (caar subst) tterm) rest))))

(defun translate-restr-for-instantiate (restr state)
  (b* (((when (atom restr))
        (value-cmp nil))
       ((when (atom (car restr)))
        (cw "skipping malformed restriction pair: ~x0~%" (car restr))
        (translate-restr-for-instantiate (cdr restr) state))
       ((cmp tterm)
        (translate-cmp (cdar restr) t t t 'instantiate-thm-for-matching-terms
                       (w state)
                       (default-state-vars t)))
       ((cmp rest)
        (translate-restr-for-instantiate (cdr restr) state)))
    (value-cmp (cons (cons (caar restr) tterm) rest))))


(defun instantiate-thm-for-matching-terms-fn (thm subst pattern restr clause state)
  (b* (((mv ctx pattern)
        (translate-cmp pattern t t t
                       'instantiate-thm-for-matching-terms
                       (w state) (default-state-vars t)))
       ((when ctx)
        (if pattern
            (er hard? ctx "~@0" pattern)
          nil))
       ((mv ctx restr)
        (translate-restr-for-instantiate restr state))
       ((when ctx)
        (if pattern
            (er hard? ctx "~@0" pattern)
          nil))
       ((mv ctx subst)
        (translate-subst-for-instantiate subst state))
       ((when ctx)
        (if pattern
            (er hard? ctx "~@0" pattern)
          nil))
       (matches (find-matching-terms-list pattern restr clause))
       ;; matches is the list of unifying substitutions
       ((unless matches) nil))
    `(:use ,(make-insts-for-matches thm subst matches))))

(defmacro instantiate-thm-for-matching-terms (thm subst pattern &key restrict)
  `(instantiate-thm-for-matching-terms-fn
    ',thm ',subst ',pattern ',restrict clause state))
