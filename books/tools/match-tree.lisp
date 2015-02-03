; Match-tree.lisp: Term pattern matching and substitution for meta reasoning.
; Copyright (C) 2013 Centaur Technology
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
(include-book "std/util/bstar" :dir :system)

;; Notes.  This book defines a B* binder UNLESS-MATCH which uses a function
;; MATCH-TREE to check that a term matches a particular pattern and return an
;; alist of values of particular subterms.

;; It can be used for matching various sorts of cons trees, but is particularly
;; focused on terms and term lists, for purposes of meta-reasoning.

;; A pattern P matches a tree X and produces bindings as follows:

;; Match conditions                                 Bindings produced
;; P is an atom and P = X
;; P is (:? <symb>)                                 (<symb> . X)
;; P is (:! <symb>)                                 (<symb> . X)
;; P is (:?S <symb>) and X is a symbol              (<symb> . X)
;; P is (:?V <symb>) and X is a nonnil symbol       (<symb> . X)
;; P is (:?F <symb>) and X is a non-quote symbol    (<symb> . X)
;; P is (:?L <symb>) and X is not quote             (<symb> . X)
;; P is none of the above,
;;      (car P) matches (car X),
;;      (cdr P) matches (cdr X),                    car bindings
;;      and the car and cdrs' bindings                UNION
;;      agree on all symbols bound in both.         cdr bindings.

;; MATCH-TREE takes three arguments, P (pattern), X (target), and A
;; (alist/accumulator).  The above rules pertain to when A is empty.  If A is
;; not empty, then the match is OK iff the bindings to be produced agree with
;; the bindings in A on any symbols bound in both.

;; The various :?x pattern types are intended to support various parts of ACL2
;; terms:
;;    :?S matches any symbol
;;    :?V matches a variable symbol, by which we mean any other than NIL, which
;;        is treated differently from other symbols by evaluators
;;    :?F matches a function symbol, by which we mean any symbol other than
;;        QUOTE, which is not a function according to evalautors
;;    :?L matches anything but the symbol QUOTE, making it appropriate for
;;        cases where we might not care whether the result is a function or
;;        a lambda.


;; UNLESS-MATCH is a B* binder that applies match-tree to a certain value
;; and (explicit, not evaluated) pattern.  If it matches, the remainder of the
;; B* form is run with any symbols inside :? binders bound as variables; if it
;; doesn't match, an early-exit is taken.  For example:

;; (b* (((unless-match x (if (:? a) (:? a) ((:?f g) (:?v q))))
;;       (er hard? 'my-match-fn "X didn't match the IF term"))
;;      (g-call (list g q)))
;;   (cw "x matched: ~x0~%" `(or ,a ,g-call)))

;; expands to, more or less,

;; (mv-let (ok alist)
;;   (match-tree x '(if (:? a) (:? a) ((:?f g) (:?v q))) nil)
;;   (if ok
;;       ;; bind the variables of the pattern
;;       (let* ((a (cdr (assoc 'a alist)))
;;              (g (cdr (assoc 'g alist)))
;;              (q (cdr (assoc 'q alist))))
;;         ;; rest of the B* form:
;;         (b* ((g-call (list g q)))
;;           (cw "x matched: ~x0~%" `(or ,a ,g-call))))
;;     (er hard? 'my-match-fn "X didn't match the IF term")))

;; The difference between the :? and :! binders is in how UNLESS-MATCH treats
;; them -- MATCH-TREE treats them both the same.  The symbol inside a :! binder
;; should be already bound, and UNLESS-MATCH will put its binding in the
;; initial alist so that the corresponding subtree of the target must be equal
;; to that value.  For example,

;; (b* (((unless-match x (f (:? var1) (:! var2)))
;;       (er hard? 'sfdf "X didn't match")))
;;   var1)

;; expands to, approximately:
;; (mv-let (ok alist)
;;   (match-free x '(f (:? var1) (:! var2))
;;               ;; initial alist:
;;               (list (cons 'var2 var2)))
;;   (if ok
;;       (let* ((var1 (cdr (assoc 'var1 alist)))
;;              (var2 (cdr (assoc 'var2 alist))))
;;         var1)
;;     (er hard? 'sfdf "X didn't match")))


;; Using match-tree in meta-reasoning.

;; The crucial theorem here is MATCH-TREE-IS-SUBST-TREE:

;; (defthmd match-tree-is-subst-tree
;;   (b* (((mv ok alist) (match-tree pat x alist)))
;;     (implies ok
;;              (equal (subst-tree pat alist) x)))
;;   :hints (("goal" :induct (match-tree pat x alist))))

;;  However, generally, you won't see a term of the form on the LHS of this
;;  theorem, so it won't be used much.  Instead, use this to prove a similar
;;  theorem that rewrites X to the SUBST-TREE term, but in certain desirable
;;  contexts.  E.g., if you have an evaluator, MY-EV, you may want to prove:

;; (defthm match-tree-is-subst-tree-for-my-ev
;;   (b* (((mv ok alist) (match-tree pat x alist)))
;;     (implies ok
;;              (equal (my-ev x a)
;;                     (my-ev (subst-tree pat alist) a))))
;;   :hints (("goal" :induct (match-tree pat x alist))))

;; This could be expensive, since ACL2 will try to apply this rule for every
;; MY-EV term it encounters.  However, generally these applications will be
;; pretty cheap, because the first thing ACL2 will do is look in the type-alist
;; for a known-true term (mv-nth 0 (match-tree pat x alist)); if it doesn't
;; find one, then it'll give up.  For the case where it does find one, we
;; generally leave subst-tree enabled so that the subst-tree term will be
;; rewritten into a semi-explicit term, which is often what you want.

;; The following theorems are also important:
;;   - match-tree-binders-bound: the bound variables of pattern are bound in
;;     the alist
;;   - symbolp-by-match-tree-restrictions: elements bound by :?s, :?v, :?f are
;;     symbols
;;   - not-quote-by-match-tree-restrictions: elements bound by :?f, :?l are not
;;     quote
;;   - not-nil-by-match-tree-restrictions: elements bound by :?v are not nil

;; Finally, you may notice that your theorems get huge and difficult to read if
;; you make extensive use of unless-match.  To solve this problem, we offer a
;; utility DEF-MATCH-TREE-REWRITES.  This is an event-creating macro that makes
;; several functions named after the :?-bound symbols in a match-tree
;; pattern.  Each function's value is the binding of that symbol in the result,
;; and we introduce a rewrite rule to rewrite that lookup into the
;; function. So:

;; (def-match-tree-rewrites (fa (fip (:? my-fa-fip-arg))))
;; produces:
;; (defund my-fa-fip-arg (x)
;;   (declare (xargs :guard t))
;;   (mv-let (ok alist)
;;     (match-tree '(fa (fip (:? my-fa-fip-arg))) x nil)
;;     (and ok (cdr (assoc 'my-fa-fip-arg alist)))))
;; (defthm my-fa-fip-arg-rw
;;   (mv-let (ok alist)
;;     (match-tree '(fa (fip (:? my-fa-fip-arg))) x nil)
;;     (implies ok
;;              (equal (cdr (assoc 'my-fa-fip-arg alist))
;;                     (my-fa-fip-arg x))))).
;; Additional theorems about the types of these functions are produced when :?x
;; forms are used.  The functions take additional arguments when :! forms are
;; used.


;; Rager notes in May 2013 that it can be helpful to use variable names that
;; are the same.  For example, when submitting the following two forms, the use
;; of "id" in the first but "id-name" in the second is enough to keep the
;; prover from verifying the guards for the second define (Rager did not try
;; any hints).  This example had two accompanying uses of
;; def-match-tree-rewrites (not shown here).

;;; (define identifier-tree-p
;;;   ((tree t "Tree to check"))
;;;   :returns (ans booleanp)
;;;   (b* (((when-match tree
;;;                     ("IdentifierRag"
;;;                      ("Identifier" ("IDENTIFIER" (:? id)))))
;;;         (stringp id))
;;;        ((when-match tree
;;;                     ("IdentifierRag"
;;;                      ("Identifier" ("IDENTIFIER" (:? id)))
;;;                      ("PERIOD" ".")
;;;                      (:? nextrag)))
;;;         (and (stringp id)
;;;              (identifier-tree-p nextrag))))
;;;     nil))

;;; (define gather-identifiers
;;;   ((tree identifier-tree-p "parse tree"))
;;;   (b* (((when-match tree
;;;                     ("IdentifierRag"
;;;                      ("Identifier" ("IDENTIFIER" (:? id-name)))))
;;;         (list id-name))
;;;        ((when-match tree
;;;                     ("IdentifierRag"
;;;                      ("Identifier" ("IDENTIFIER" (:? id)))
;;;                      ("PERIOD" ".")
;;;                      (:? nextrag)))
;;;         (cons id
;;;               (gather-identifiers nextrag))))
;;;     (er hard? 'gather-identifiers
;;;         "Gather-identifiers given input that it doesn't know how to parse: ~x0"
;;;         tree))
;;;   :guard-hints (("Goal" :in-theory (enable identifier-tree-p))))


(defun match-tree-binder-p (pat)
  (declare (xargs :guard (consp pat)))
  (and (symbolp (car pat))
       (keywordp (car pat))
       (< 0 (length (symbol-name (car pat))))
       (member (char (symbol-name (car pat)) 0) '(#\? #\!))
       (consp (cdr pat))
       (symbolp (cadr pat))
       (eq (cddr pat) nil)))

(defthm symbolp-cadr-when-match-tree-binder-p
  (implies (match-tree-binder-p pat)
           (symbolp (cadr pat)))
  :rule-classes :forward-chaining)

(defun match-tree-check-binding (kw x)
  (declare (xargs :guard (keywordp kw)))
  (not (or (and (member kw '(:?s :?f :?v))
                (not (symbolp x)))
           (and (member kw '(:?f :?l))
                (eq x 'quote))
           (and (eq kw :?v)
                (eq x nil)))))

(defun match-tree (pat x alist)
  (declare (xargs :guard (symbol-alistp alist)
                  :verify-guards nil))
  (b* (((when (atom pat))
        (mv (equal pat x) alist))
       ((unless (match-tree-binder-p pat))
        (if (atom x)
            (mv nil alist)
          (b* (((mv ok alist) (match-tree (cdr pat) (cdr x) alist))
               ((unless ok) (mv nil alist)))
            (match-tree (car pat) (car x) alist))))
       (kw (car pat))
       ((unless (match-tree-check-binding kw x))
        (mv nil alist))
       (var (cadr pat))
       (look (assoc var alist))
       ((when look)
        (mv (equal (cdr look) x) alist)))
    (mv t (cons (cons var x) alist))))

(in-theory (disable match-tree-check-binding
                    match-tree-binder-p))

(defthm symbol-alistp-match-tree
  (implies (symbol-alistp alist)
           (and (symbol-alistp (mv-nth 1 (match-tree pat x alist)))
                (alistp (mv-nth 1 (match-tree pat x alist))))))

(verify-guards match-tree
  :hints(("Goal" :in-theory (enable match-tree-binder-p))))

(defthm assoc-in-match-tree
  (implies (assoc k alist)
           (equal (assoc k (mv-nth 1 (match-tree pat x alist)))
                  (assoc k alist))))

(defun subst-tree (pat alist)
  (declare (xargs :guard (symbol-alistp alist)
                  :guard-hints (("goal" :in-theory (enable match-tree-binder-p)))))
  (b* (((when (atom pat)) pat)
       ((unless (match-tree-binder-p pat))
        (cons (subst-tree (car pat) alist)
              (subst-tree (cdr pat) alist))))
    (cdr (assoc (cadr pat) alist))))

(defun match-tree-binders (pat)
  (b* (((when (atom pat)) nil)
       ((when (match-tree-binder-p pat))
        (list (cadr pat))))
    (append (match-tree-binders (car pat))
            (match-tree-binders (cdr pat)))))

(local (defthm member-append
         (iff (member x (append a b))
              (or (member x a)
                  (member x b)))))

(defthm match-tree-binders-bound
  (b* (((mv ok alist) (match-tree pat x alist0)))
    (implies (and (member k (match-tree-binders pat))
                  ok)
             (and (assoc k alist)
                  (implies (symbol-alistp alist0)
                           (consp (assoc k alist)))))))

(defun keys-subset (keys alist)
  (declare (xargs :guard (alistp alist)))
  (if (atom keys)
      t
    (and (assoc-equal (car keys) alist)
         (keys-subset (cdr keys) alist))))

(defthm match-tree-all-binders-bound
  (b* (((mv ok alist) (match-tree pat x alist)))
    (implies (and ok
                  (subsetp keys (match-tree-binders pat)))
             (keys-subset keys alist)))
  :hints(("Goal" :in-theory (enable subsetp keys-subset)
          :induct (len keys))))

(defthm keys-subset-of-append
  (equal (keys-subset (append x y) a)
         (and (keys-subset x a)
              (keys-subset y a))))

(defthm subst-tree-when-all-binders-bound
  (b* (((mv ?ok alist) (match-tree pat1 x alist0)))
    (implies (keys-subset (match-tree-binders pat) alist0)
             (equal (subst-tree pat alist)
                    (subst-tree pat alist0))))
  :hints (("goal" :induct (match-tree-binders pat))))


(local (defthm subsetp-when-subsetp-of-cdr
         (implies (subsetp x (cdr y))
                  (subsetp x y))))

(local (defthm subsetp-refl
         (subsetp x x)))

(defthmd match-tree-is-subst-tree
  (b* (((mv ok alist) (match-tree pat x alist)))
    (implies ok
             (equal (subst-tree pat alist) x)))
  :hints (("goal" :induct (match-tree pat x alist))))

(defun match-tree-!vars (pat acc)
  (declare (xargs :guard t
                  :guard-hints
                  (("goal" :in-theory (enable match-tree-binder-p)))))
  (b* (((when (atom pat)) acc)
       ((when (and (match-tree-binder-p pat)
                   (eql (char (symbol-name (car pat)) 0) #\!)))
        (cons (cadr pat) acc)))
    (match-tree-!vars
     (car pat) (match-tree-!vars (cdr pat) acc))))

(defun match-tree-initial-alist-lst (vars)
  (if (atom vars)
      nil
    (cons `(cons ',(car vars) ,(car vars))
          (match-tree-initial-alist-lst (cdr vars)))))

(defun match-tree-initial-alist-term (vars)
  `(list . ,(match-tree-initial-alist-lst vars)))

(defun prefix-?-vars (vars)
  (declare (xargs :guard (symbol-listp vars)))
  (if (atom vars)
      nil
    (cons (intern-in-package-of-symbol
           (concatenate 'string "?" (symbol-name (car vars)))
           (car vars))
          (prefix-?-vars (cdr vars)))))

(defun treematch-fn (x pat nomatch-body match-body)
  (let* ((allvars (remove-duplicates-eq (match-tree-binders pat)))
         (vars! (remove-duplicates-eq (match-tree-!vars pat nil)))
         (vars? (set-difference-eq allvars vars!)))
    `(b* (((mv _treematch-ok ?_treematch-alist)
           (match-tree ',pat ,x ,(match-tree-initial-alist-term vars!)))
          ((unless _treematch-ok)
           (check-vars-not-free
            (_treematch-ok _treematch-alist)
            ,nomatch-body))
          ((assocs . ,(prefix-?-vars vars?))
           _treematch-alist))
       (check-vars-not-free
        (_treematch-ok _treematch-alist)
        ,match-body))))

(def-b*-binder unless-match
  :decls ((declare (xargs :guard (equal (len args) 2))))
  :body
  (treematch-fn (car args) (cadr args)
                `(progn$ . ,forms)
                rest-expr))

(def-b*-binder when-match
  :decls ((declare (xargs :guard (equal (len args) 2))))
  :body
  (treematch-fn (car args) (cadr args)
                rest-expr
                `(progn$ . ,forms)))

(defun treematch*-fn (x pats)
  (cond ((atom pats) nil)
        ((eq (caar pats) '&) `(progn$ (cdar pats)))
        (t (treematch-fn x (caar pats)
                         (treematch*-fn x (cdr pats))
                         `(progn$ (cdar pats))))))

;; This emulates case-match...
(defmacro treematch (x pats)
  (if (atom x)
      (treematch*-fn x pats)
    (let ((var (pack x)))
      `(b* ((,var ,x))
         ,(treematch*-fn var pats)))))

(defun match-tree-restrictions (pat)
  (declare (xargs :guard t))
  (b* (((when (atom pat)) nil)
       ((unless (match-tree-binder-p pat))
        (append (match-tree-restrictions (car pat))
                (match-tree-restrictions (cdr pat)))))
    (list pat)))

(defthm match-tree-restrictions-of-lookup-lemma
  (b* (((mv ok alist) (match-tree pat x alist0)))
    (implies (and ok
                  (assoc var alist0)
                  (member (list kw var) (match-tree-restrictions pat)))
             (match-tree-check-binding kw (cdr (assoc var alist))))))

(defthmd lookup-when-member-match-tree-restrictions
  (b* (((mv ok alist) (match-tree pat x alist)))
    (implies (and ok
                  (member (list kw var) (match-tree-restrictions pat)))
             (assoc var alist))))

(defthm match-tree-restrictions-of-lookup
  (b* (((mv ok alist) (match-tree pat x alist)))
    (implies (and ok
                  (member (list kw var) (match-tree-restrictions pat)))
             (match-tree-check-binding kw (cdr (assoc var alist)))))
  :hints(("Goal" :in-theory (enable
                             lookup-when-member-match-tree-restrictions))))

(defthm symbolp-by-match-tree-restrictions
  (b* (((mv ok alist) (match-tree pat x alist)))
    (implies (and ok
                  (intersectp-equal (list (list :?s var)
                                          (list :?f var)
                                          (list :?v var))
                                    (match-tree-restrictions pat)))
             (symbolp (cdr (assoc var alist)))))
  :hints (("goal" :do-not-induct t)
          (and stable-under-simplificationp
               (let ((lit (cadr clause)))
                 (case-match lit
                   (('not ('member-equal ('cons ('quote kw) &) . &))
                    `(:use ((:instance match-tree-restrictions-of-lookup
                             (kw ,kw)))
                      :in-theory (e/d (match-tree-check-binding)
                                      (match-tree-restrictions-of-lookup)))))))))

(defthm not-quote-by-match-tree-restrictions
  (b* (((mv ok alist) (match-tree pat x alist)))
    (implies (and ok
                  (intersectp-equal (list (list :?l var)
                                          (list :?f var))
                                    (match-tree-restrictions pat)))
             (not (equal (cdr (assoc var alist)) 'quote))))
  :hints (("goal" :do-not-induct t)
          (and stable-under-simplificationp
               (let ((lit (cadr clause)))
                 (case-match lit
                   (('not ('member-equal ('cons ('quote kw) &) . &))
                    `(:use ((:instance match-tree-restrictions-of-lookup
                             (kw ,kw)))
                      :in-theory (e/d (match-tree-check-binding)
                                      (match-tree-restrictions-of-lookup)))))))))

(defthm not-nil-by-match-tree-restrictions
  (b* (((mv ok alist) (match-tree pat x alist)))
    (implies (and ok
                  (member-equal (list :?v var) (match-tree-restrictions pat)))
             (cdr (assoc var alist))))
  :hints (("goal" :do-not-induct t)
          (and stable-under-simplificationp
               (let ((lit (cadr clause)))
                 (case-match lit
                   (('not ('member-equal ('cons ('quote kw) &) . &))
                    `(:use ((:instance match-tree-restrictions-of-lookup
                             (kw ,kw)))
                      :in-theory (e/d (match-tree-check-binding)
                                      (match-tree-restrictions-of-lookup)))))))))

(in-theory (disable match-tree))


(local (in-theory (disable mv-nth)))

(defthm match-tree-measure-weak
  (implies (not (assoc k alist0))
           (<= (acl2-count (cdr (assoc k (mv-nth 1 (match-tree pat x alist0)))))
               (acl2-count x)))
  :hints(("Goal" :in-theory (e/d (match-tree) (acl2-count))
          :induct t)
         (and stable-under-simplificationp
              '(:in-theory (enable acl2-count))))
  :rule-classes :linear)

(defthm match-tree-measure-strong
  (mv-let (ok alist)
    (match-tree pat x alist0)
    (implies (and (not (assoc k alist0))
                  (not (match-tree-binder-p pat))
                  (consp pat)
                  ok)
             (< (acl2-count (cdr (assoc k alist)))
                (acl2-count x))))
  :hints(("Goal" :in-theory (e/d (match-tree))
          :induct t))
  :rule-classes :linear)



(defun replace-equalities-thm-fnsym (thmname w)
  (declare (xargs :guard (and (symbolp thmname)
                              (plist-worldp w))))
  (b* (((unless-match (getprop thmname 'theorem nil 'current-acl2-world w)
                      (implies ((:?f hyp-sym) . (:? hyp-args))
                               (equal (:? lhs)
                                      (:? rhs))))
        (er hard? 'add-replace-equalities-rule
            "Theorem ~x0 not of the right form") thmname))
    hyp-sym))

(defmacro add-replace-equalities-rule (thmname)
  `(table replace-equalities-rules
          (replace-equalities-thm-fnsym ',thmname world)
          (cons ',thmname
                (cdr (assoc (replace-equalities-thm-fnsym ',thmname world)
                            (table-alist 'replace-equalities-rules world))))))



(defun match-tree-rw-fname (prefix var)
  (declare (xargs :guard (and (symbolp prefix) (symbolp var))))
  (if prefix
      (intern-in-package-of-symbol (concatenate 'string (symbol-name prefix)
                                                (symbol-name var))
                                   prefix)
    var))

(defun match-tree-rewrites-var-fn (var vars! pat prefix)
  `(defund ,(match-tree-rw-fname prefix var) (x . ,vars!)
     (declare (xargs :guard t))
     (mv-let (ok alist)
       (match-tree ',pat x ,(match-tree-initial-alist-term vars!))
       (and ok (cdr (assoc ',var alist))))))

(defun match-tree-rewrites-fns (vars vars! pat prefix)
  (if (atom vars)
      nil
    (cons (match-tree-rewrites-var-fn (car vars) vars! pat prefix)
          (match-tree-rewrites-fns (cdr vars) vars! pat prefix))))

(defun match-tree-rw-measure-thm (var vars! pat prefix)
  (b* ((fnname (match-tree-rw-fname prefix var))
       (thmname-weak (intern-in-package-of-symbol
                      (concatenate 'string (symbol-name fnname) "-ACL2-COUNT-WEAK")
                      fnname))
       (thmname-strong (intern-in-package-of-symbol
                        (concatenate 'string (symbol-name fnname) "-ACL2-COUNT-STRONG")
                        fnname)))
    `((defthm ,thmname-weak
        (<= (acl2-count (,fnname x . ,vars!))
            (acl2-count x))
        :hints(("Goal" :in-theory (enable ,fnname)))
        :rule-classes :linear)
      . ,(and (not (atom pat))
              (not (match-tree-binder-p pat))
              `((defthm ,thmname-strong
                  (implies (mv-nth 0 (match-tree ',pat x ,(match-tree-initial-alist-term vars!)))
                           (< (acl2-count (,fnname x . ,vars!))
                              (acl2-count x)))
                  :hints(("Goal" :in-theory (enable ,fnname)))
                  :rule-classes :linear))))))

(defun match-tree-rw-measure-thms (vars vars! pat prefix)
  (if (atom vars)
      nil
    (append (match-tree-rw-measure-thm (car vars) vars! pat prefix)
            (match-tree-rw-measure-thms (cdr vars) vars! pat prefix))))


(defun match-tree-block-substs-var-fn (var vars! pat prefix)
  (let* ((fnname (match-tree-rw-fname prefix var))
         (thmname (intern-in-package-of-symbol
                   (concatenate 'string
                                (symbol-name fnname) "-BLOCK-EQUALITY-SUBST")
                   fnname)))
  `((defthm ,thmname
      (implies (mv-nth 0 (match-tree ',pat x ,(match-tree-initial-alist-term vars!)))
               (equal (,fnname x . ,vars!)
                      (,fnname x . ,vars!)))
      :rule-classes nil)
    (add-replace-equalities-rule ,thmname))))

(defun match-tree-block-substs-fns (vars vars! pat prefix)
  (if (atom vars)
      nil
    (append (match-tree-block-substs-var-fn (car vars) vars! pat prefix)
            (match-tree-block-substs-fns (cdr vars) vars! pat prefix))))

(defun match-tree-rewrites-var-rw (var vars! pat prefix)
  (let* ((fnname (match-tree-rw-fname prefix var)))
    `(defthm ,(intern-in-package-of-symbol
               (concatenate 'string (symbol-name fnname) "-RW")
               var)
       (mv-let (ok alist)
         (match-tree ',pat x ,(match-tree-initial-alist-term vars!))
         (implies ok
                  (equal (cdr (assoc ',var alist))
                         (,fnname x . ,vars!))))
       :hints(("Goal" :in-theory (enable ,fnname))))))

(defun match-tree-rewrites-rws (vars vars! pat prefix)
  (if (atom vars)
      nil
    (cons (match-tree-rewrites-var-rw (car vars) vars! pat prefix)
          (match-tree-rewrites-rws (cdr vars) vars! pat prefix))))


(defun match-tree-restr-events (restr vars! pat prefix)
  (b* (((list kw var) restr)
       (fnname (match-tree-rw-fname prefix var)))
    (and (member kw '(:?s :?v :?f :?l))
         `((defthm ,(intern-in-package-of-symbol
                     (concatenate 'string (symbol-name fnname) "-TYPE")
                     fnname)
             (implies (mv-nth 0 (match-tree
                                 ',pat x
                                 ,(match-tree-initial-alist-term vars!)))
                      ,(case kw
                         (:?s `(symbolp (,fnname x . ,vars!)))
                         (:?v `(and (symbolp (,fnname x . ,vars!))
                                    (,fnname x . ,vars!)))
                         (:?f `(and (symbolp (,fnname x . ,vars!))
                                    (not (equal (,fnname x . ,vars!) 'quote))))
                         (:?l `(not (equal (,fnname x . ,vars!) 'quote)))))
             :hints(("Goal" :in-theory (enable ,fnname))))))))

(defun match-tree-restrs-events (restrs vars! pat prefix)
  (if (atom restrs)
      nil
    (append (match-tree-restr-events (car restrs) vars! pat prefix)
            (match-tree-restrs-events (cdr restrs) vars! pat prefix))))




(defun def-match-tree-rewrites-fn (pat prefix)
  (b* ((allvars (remove-duplicates-eq (match-tree-binders pat)))
       (vars! (remove-duplicates-eq (match-tree-!vars pat nil)))
       (vars? (set-difference-eq allvars vars!))
       (fn-events (match-tree-rewrites-fns vars? vars! pat prefix))
       (meas-events (match-tree-rw-measure-thms vars? vars! pat prefix))
       (rw-events (match-tree-rewrites-rws vars? vars! pat prefix))
       (bs-events (match-tree-block-substs-fns vars? vars! pat prefix))
       (restrs (match-tree-restrictions pat))
       (type-events (match-tree-restrs-events restrs vars! pat prefix)))
    `(progn ,@fn-events ,@meas-events ,@bs-events ,@type-events . ,rw-events)))

(defmacro def-match-tree-rewrites (pat &key prefix)
  (def-match-tree-rewrites-fn pat prefix))

(local (def-match-tree-rewrites (if (:! foo) (:? bar) (:?s baz))))

(local (def-match-tree-rewrites (if (:! foo) (:? bar) (:?s baz))
         :prefix fooif->))
