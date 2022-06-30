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
(include-book "std/lists/mfc-utils" :dir :system)

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
        ((eq (caar pats) '&) `(progn$ . ,(cdar pats)))
        (t (treematch-fn x (caar pats)
                         (treematch*-fn x (cdr pats))
                         `(progn$ . ,(cdar pats))))))

;; This emulates case-match...
(defmacro treematch (x &rest pats)
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


;;; New reasoning support ---

;; Match-tree-alist
(defund match-tree-alist (pat x alist)
  (b* (((when (atom pat)) alist)
       ((unless (match-tree-binder-p pat))
        (b* ((alist (match-tree-alist (cdr pat) (cdr x) alist)))
          (match-tree-alist (car pat) (car x) alist))))
    (if (assoc (cadr pat) alist)
        alist
      (cons (cons (cadr pat) x) alist))))

(defthm match-tree-alist-rw-when-matched
  (b* (((mv match alist-out) (match-tree pat x alist)))
    (implies match
             (equal alist-out (match-tree-alist pat x alist))))
  :hints(("Goal" :in-theory (enable match-tree match-tree-alist))))

(defthmd match-tree-alist-expand-atom
  (implies (and (syntaxp (quotep pat))
                (not (consp pat)))
           (equal (match-tree-alist pat x alist) alist))
  :hints(("Goal" :in-theory (enable match-tree-alist))))

(defthmd match-tree-alist-expand-binder
  (implies (and (syntaxp (quotep pat))
                (match-tree-binder-p pat)
                (equal assoc (if (assoc (cadr pat) alist) t nil))
                (syntaxp (Quotep assoc)))
           (equal (match-tree-alist pat x alist)
                  (if assoc
                      alist
                    (cons (cons (cadr pat) x) alist))))
  :hints(("Goal" :in-theory (enable match-tree-alist
                                    match-tree-binder-p))))

(defthmd match-tree-alist-expand-cons
  (implies (and (syntaxp (quotep pat))
                (not (match-tree-binder-p pat))
                (consp pat))
           (equal (match-tree-alist pat x alist)
                  (match-tree-alist (car pat) (car x)
                                    (match-tree-alist (cdr pat) (cdr x) alist))))
  :hints(("Goal" :in-theory (enable match-tree-alist))))

(deftheory match-tree-alist-opener-theory
  '(match-tree-alist-expand-atom
    match-tree-alist-expand-binder
    match-tree-alist-expand-cons))

(defund match-tree-matchedp (pat x alist)
  (b* (((when (atom pat)) (equal pat x))
       ((unless (match-tree-binder-p pat))
        (and (consp x)
             (match-tree-matchedp (cdr pat) (cdr x) alist)
             (match-tree-matchedp
              (car pat) (car x) (match-tree-alist (cdr pat) (cdr x) alist)))))
    (and (match-tree-check-binding (car pat) x)
         (let ((look (assoc (cadr pat) alist)))
           (or (not look)
               (equal (cdr look) x))))))

(defthmd match-tree-matchedp-rw
  (equal (mv-nth 0 (match-tree pat x alist))
         (match-tree-matchedp pat x alist))
  :hints(("Goal" :in-theory (enable match-tree-matchedp match-tree))))

(defund match-tree-matchedp-open (pat x alist)
  (match-tree-matchedp pat x alist))

(defthmd match-tree-open
  (equal (mv-nth 0 (match-tree pat x alist))
         (match-tree-matchedp-open pat x alist))
  :hints(("Goal" :in-theory (enable match-tree-matchedp-rw
                                    match-tree-matchedp-open))))

(defthm match-tree-alist-rw-when-match-tree-matchedp
  (implies (match-tree-matchedp pat x alist)
           (equal (mv-nth 1 (match-tree pat x alist))
                  (match-tree-alist pat x alist)))
  :hints(("Goal" :in-theory (enable match-tree-matchedp-rw))))

(defthmd match-tree-equals-match-tree-matchedp-when-successful
  (implies (rewriting-negative-literal `(mv-nth '0 (match-tree ,pat ,x ,alist)))
           (iff (mv-nth 0 (match-tree pat x alist))
                (match-tree-matchedp pat x alist)))
  :hints(("Goal" :in-theory (enable match-tree-matchedp-rw))))

(defthmd match-tree-obj-equals-subst-when-successful
  (and (implies (rewriting-negative-literal `(mv-nth '0 (match-tree ,pat ,x ,alist)))
                (iff (mv-nth 0 (match-tree pat x alist))
                     (and (match-tree-matchedp pat x alist)
                          (equal (subst-tree pat (match-tree-alist pat x alist)) x)))))
  :hints (("goal" :expand ((:free (x) (hide x)))
           :use match-tree-is-subst-tree
           :in-theory (enable match-tree-matchedp-rw
                              match-tree-alist))))

(defthmd match-tree-open-when-successful
  (implies (rewriting-negative-literal `(mv-nth '0 (match-tree ,pat ,x ,alist)))
           (iff (mv-nth 0 (match-tree pat x alist))
                (and (match-tree-matchedp pat x alist)
                     (match-tree-matchedp-open pat x alist))))
  :hints (("goal" :expand ((:free (x) (hide x)))
           :use match-tree-is-subst-tree
           :in-theory (enable match-tree-matchedp-rw
                              match-tree-matchedp-open
                              match-tree-alist))))

(defthmd match-tree-obj-equals-subst-and-open-when-successful
  (and (implies (rewriting-negative-literal `(mv-nth '0 (match-tree ,pat ,x ,alist)))
                (iff (mv-nth 0 (match-tree pat x alist))
                     (and (match-tree-matchedp pat x alist)
                          (equal (subst-tree pat (match-tree-alist pat x alist)) x)
                          (match-tree-matchedp-open pat x alist)))))
  :hints (("goal" :expand ((:free (x) (hide x)))
           :use match-tree-is-subst-tree
           :in-theory (enable match-tree-matchedp-rw
                              match-tree-matchedp-open
                              match-tree-alist))))

(defthm match-tree-when-matchedp
  (implies (match-tree-matchedp pat x alist)
           (mv-nth 0 (match-tree pat x alist)))
  :hints(("Goal" :in-theory (enable match-tree-matchedp-rw))))

(defthm subst-tree-open
  (implies (syntaxp (quotep pat))
           (equal (subst-tree pat alist)
                  (if (atom pat)
                      pat
                    (if (match-tree-binder-p pat)
                        (cdr (assoc (cadr pat) alist))
                      (cons (subst-tree (car pat) alist)
                            (subst-tree (cdr pat) alist)))))))

(in-theory (disable subst-tree))

(defthmd match-tree-matchedp-opener
  (implies (syntaxp (quotep pat))
           (equal (match-tree-matchedp-open pat x alist)
                  (if (consp pat)
                      (if (match-tree-binder-p pat)
                          (and (match-tree-check-binding (car pat) x)
                               (let ((look (assoc-equal (cadr pat) alist)))
                                 (or (not look)
                                     (equal (cdr look) x))))
                        (and (consp x)
                             (match-tree-matchedp-open (cdr pat) (cdr x) alist)
                             (match-tree-matchedp-open
                              (car pat) (car x) (match-tree-alist (cdr pat) (cdr x) alist))))
                    (equal x pat))))
  :hints(("Goal" :in-theory (enable match-tree-matchedp
                                    match-tree-matchedp-open))))

(defthm match-tree-matchedp-open-when-binder
  (implies (and ;;(rewriting-positive-literal `(match-tree-matchedp ,pat ,x ,alist))
            (syntaxp (quotep pat))
            (match-tree-binder-p pat)
            (equal look (assoc-equal (cadr pat) alist))
            (equal not-look (if (consp look) nil (not look))) ;; ugh! somehow (not (cons x y)) doesn't rewrite to nil
            (syntaxp ;; (prog2$ (cw "not-look: ~x0~%" not-look)
                             (quotep not-look)))
           (equal (match-tree-matchedp-open pat x alist)
                  (and (match-tree-check-binding (car pat) x)
                       (or not-look 
                           (equal (cdr look) x)))))
  :hints(("Goal" :in-theory (enable match-tree-matchedp
                                    match-tree-binder-p
                                    match-tree-matchedp-open))))

(defthm match-tree-matchedp-open-when-consp
  (implies (and (syntaxp (quotep pat))
                (consp pat)
                (not (match-tree-binder-p pat)))
           (equal (match-tree-matchedp-open pat x alist)
                  (and (consp x)
                       (match-tree-matchedp-open (cdr pat) (cdr x) alist)
                       (match-tree-matchedp-open
                        (car pat) (car x) (match-tree-alist (cdr pat) (cdr x) alist)))))
  :hints(("Goal" :in-theory (enable match-tree-matchedp
                                    match-tree-matchedp-open))))

(defthm match-tree-matchedp-open-of-atom
  (implies (and ;;(rewriting-positive-literal `(match-tree-matchedp ,pat ,x ,alist))
            (syntaxp (quotep pat))
            (not (consp pat)))
           (equal (match-tree-matchedp-open pat x alist)
                  (equal x pat)))
  :hints(("Goal" :in-theory (enable match-tree-matchedp
                                    match-tree-matchedp-open))))


(deftheory match-tree-opener-theory
  '(match-tree-check-binding
    ;; match-tree-matchedp-open
    match-tree-matchedp-open-when-binder
    ;; ;; match-tree-matchedp-of-cons
    match-tree-matchedp-open-when-consp
    ;; ;; match-tree-matchedp-when-not-consp
    match-tree-matchedp-open-of-atom
    ))


(defund equal-of-cons-open (x y)
  (equal x y))

(defthm equal-of-cons-open-when-consp
  (implies (syntaxp (not (and (quotep a) (quotep b))))
           (equal (equal-of-cons-open x (cons a b))
                  (and (consp x)
                       (equal-of-cons-open (car x) a)
                       (equal-of-cons-open (cdr x) b))))
  :hints(("Goal" :in-theory (enable equal-of-cons-open))))

(defthm equal-of-cons-open-when-not-known-consp
  (implies (syntaxp (or (quotep y)
                        (not (and (Consp y) (eq (car y) 'cons)))))
           (equal (equal-of-cons-open x y)
                  (equal x y)))
  :hints(("Goal" :in-theory (enable equal-of-cons-open))))

(defthmd equal-of-cons-hyp-open
  (implies (and (syntaxp (not (and (quotep a) (quotep b))))
                (syntaxp (or (rewriting-negative-literal-fn `(equal (cons ,a ,b) ,x) mfc state)
                             (rewriting-negative-literal-fn `(equal ,x (cons ,a ,b)) mfc state))))
           (equal (equal (cons a b) x)
                  (equal-of-cons-open x (cons a b))))
  :hints(("Goal" :in-theory (enable equal-of-cons-open))))


(defthmd assoc-equal-of-cons-when-keys-known
  (implies (and (equal key1 (car pair))
                (consp pair)
                (syntaxp (and (quotep key)
                              (quotep key1))))
           (equal (assoc-equal key (cons pair rest))
                  (if (equal key key1)
                      pair
                    (assoc-equal key rest))))
  :hints(("Goal" :in-theory (enable assoc-equal))))


(defxdoc match-tree
  :parents (macro-libraries) ;; ugh, doesn't seem great
  :short "Match an object against a flexible pattern and return the unifying substitution"
  :long
  " 
<p>Match-tree is a function that takes a pattern, object, and alist, and
returns two values: matchedp, which is true only if the pattern matched the
object under the bindings already present in alist, and result-alist, an
extension of the input alist containing the unifying substitution.</p>

<p>Invocation:</p>
@({
  (match-tree pattern obj alist)
 -->
  (mv matchedp new-alist)
 )}     

<p>Pseudo-formally, if the input alist is empty, a pattern P matches an object
X and produces bindings as follows:</p>

@({
  Match conditions                                 Bindings produced
  P is an atom and P = X
  P is (:? <symb>)                                 (<symb> . X)
  P is (:! <symb>)                                 (<symb> . X)
  P is (:?S <symb>) and X is a symbol              (<symb> . X)
  P is (:?V <symb>) and X is a nonnil symbol       (<symb> . X)
  P is (:?F <symb>) and X is a non-quote symbol    (<symb> . X)
  P is (:?L <symb>) and X is not quote             (<symb> . X)
  P is none of the above,
       (car P) matches (car X),
       (cdr P) matches (cdr X),                    car bindings
       and the car and cdrs' bindings                UNION
       agree on all symbols bound in both.         cdr bindings.
 })

<p>If the input alist is not empty, then the bindings produced must also agree
with any bindings of the same symbols that are present in the input alist, and
the result alist is the bindings unioned with the input alist.</p>

<p>The @('(:! x)') binding pattern is the same as @('(:? x)') in match-tree
itself, but is treated differently by macros @(see treematch), @(see
when-match), and @(see unless-match); see below.</p>

<h2>Macro support</h2>

<p>Match-tree supports the utility @(see treematch), which is similar in spirit to @(see case-match); e.g., </p>

@({
 (treematch x
   ((cons (:? a) (:? b))    (list a b))
   ((foo (:v q))            (list q))
   (&                       (list x)))
 })
<p>expands to approximately:</p>
@({
 (b* (
      ;; (cons (:? a) (:? b)) case:
      ((mv matchedp alist) (match-tree '(cons (:? a) (:? b)) x nil))
      ((when matchedp)
       (let* ((a (cdr (assoc 'a alist)))
              (b (cdr (assoc 'b alist))))
          (list a b)))

      ;; (foo (:v q)) case:
      ((mv matchedp alist) (match-tree '(foo (:v q) (:? y)) x nil))
      ((when matchedp)
       (let* ((q (cdr (assoc 'q alist))))
          (list q))))

   ;; default case:
   (list x))
 })

<p>When a pattern contains @('(:! x)') binders, @('treematch') invokes
match-tree with an alist consisting of the previous bindings of those
variables; then, the pattern will only match if the corresponding location in
the object is equal to the existing binding of the variable, like in @(see
case-match) when a symbol is prefixed with @('!').  For example, in the
following form:</p>

@({
 (let ((y 'bar))
   (treematch x
      ((foo (:! y))  ...)
      ...))
 })
<p>the match-tree call generated is:</p>
@({
 (match-tree '(foo (:! y)) x (list (cons 'y y)))
 })
<p>which means that this match will only succeed if x equals @('(foo bar)').</p>

<p>Two @(see B*) binders @('unless-match') and @('when-match') also use match-tree.  One can think of them as expending to a call of @('treematch') with one pattern and a default:</p>

@({
 (b* (((when-match obj pattern)
       match-form))
    default-form)
 })
<p>and</p>
@({
 (b* (((unless-match obj pattern)
       default-form))
    match-form)
 })
<p>are both basically equivalent to</p>
@({
 (treematch obj
   (pattern match-form)
   (& default-form))
 })
    
<h2>Reasoning</h2>

<p>The main advantage of match-tree over case-match is reasoning
efficiency. When using case-match, each pattern-matching form macroexpands to a
conjunction of conditions followed by a series of bindings.  These are
relatively automatic to reason about, but they make it difficult to debug
problems in proofs (because it takes a lot of reading and decoding car/cdr
nests to figure out which patterns did and did not match), and they are
expensive to reason about because when a pattern does NOT match, ACL2 typically
splits into cases for the disjunction of the matching conditions.</p>

<p>Since match-tree is a function, the user can control how or whether to open
it.  We offer a couple of levels of reasoning about it, bundled in theories.</p>

<p>We generally rewrite the second (new-alist) return value of @('match-tree')
to @('match-tree-alist').  This is a simpler function with fewer conditionals
that equals that value whenever the pattern matches; presumably the alist isn't
relevant otherwise. The theory @('match-tree-alist-opener-theory') opens calls
of @('match-tree-alist').  You may additionally want a rule such as
@('assoc-equal-of-cons') to simplify lookups in the alist.</p>

<p>We generally rewrite the first return value (matchedp) to
@('match-tree-matchedp') (which is equivalent) when the match was successful.
However, we can use different rules to do this and these rules have different
side effects to help with reasoning:</p>

<ul>
<li>@('match-tree-equals-match-tree-matchedp-when-successful') simply
rewrites the @('matchedp') return value to @('match-tree-matchedp'), without side
effects.</li>

<li>@('match-tree-obj-equals-subst-when-successful') rewrites the @('matchedp')
value to the conjunction of @('match-tree-matchedp') and a term equating the
object with the substitution of the result alist into the pattern.  Rules that
expand the substitution are enabled by default, so this quickly produces a
hypothesis that gives the shape of the object defined by the pattern.</li>

<li>@('match-tree-open-when-successful') rewrites the @('matchedp') value to
the conjunction of @('match-tree-matchedp') and @('match-tree-matchedp-open'),
and equivalent function that has rules to open calls on known patterns enabled
by default (collected in the theory @('match-tree-opener-theory').</li>

<li>@('match-tree-obj-equals-subst-and-open-when-successful') rewrites the
@('matchedp') value to the conjunction of all three: @('match-tree-matchedp'),
@('match-tree-matchedp-open'), and the equivalence of the object with the
substitution.</li>

</ul>

<p>These rules only take effect when we see the @('matchedp') return value as a
negative literal (hypothesis/negated conclusion) of a clause, not when
backchaining or a positive literal (negated hypothesis/conclusion).  To prove
that a pattern does in fact match, or a consequence when it doesn't match, the
rule @('match-tree-open') unconditionally rewrites the matchedp value to
@('match-tree-matchedp-open'), which by default opens into a conjunction of
conditions.</p>



")


(defxdoc treematch
  :parents (match-tree)
  :short "Utility similar to @('case-match') that uses @('match-tree')."
  :long "<p>See @(see match-tree) for details.</p>")

(defxdoc when-match
  :parents (match-tree)
  :short "@('B*') binder for @('match-tree')"
  :long "<p>See @(see match-tree) for details.</p>")

(defxdoc unless-match
  :parents (match-tree)
  :short "@('B*') binder for @('match-tree')."
  :long "<p>See @(see match-tree) for details.</p>")


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
