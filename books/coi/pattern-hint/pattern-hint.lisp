;;
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
;; ===================================================================
;;
;; This book provides a pattern driven computed hint facility.
;;
;; For example, given the following pattern hint:
;;
;; :hints ((pattern::hint
;;           (< x y)
;;           :use ((:instance helpful-lemma (a x) (b y))))
;;
;; the following subboal:
;;
;; (implies
;;   (and
;;     (< (foo x) 7)
;;     (<= x (foo x)))
;;   (< (foo a) (foo 7)))
;;
;; will result in a hint with one instance of helpful-lemma:
;;
;; :use ((:instance helpful-lemma (a (foo x)) (b 7)))
;;
;; With the following pattern hint:
;;
;; :hints ((pattern::hint
;;           (<= x y)
;;           :use ((:instance helpful-lemma (a x) (b y))))
;;
;; it will result in a hint with two instances of helpful-lemma:
;;
;; :use ((:instance helpful-lemma (a x)       (b (foo x)))
;;       (:instance helpful-lemma (a (foo 7)) (b (foo a))))
;;
;; ===================================================================

(in-package "PATTERN")

(include-book "misc/bash" :dir :system)
(include-book "misc/beta-reduce" :dir :system)
(include-book "coi/util/pseudo-translate" :dir :system)
(include-book "coi/util/table" :dir :system)
(include-book "misc/total-order" :dir :system)
(include-book "pattern-hint-xdoc")

(set-state-ok t)

; Matt K. mod: Avoid ACL2(p) error from computed hint that returns state.
(set-waterfall-parallelism nil)

(defun not-term (term)
  (case-match term
    (('not term) term)
    (& `(not ,term))))

(defun pseudo-trans (term w)
  (declare (xargs :mode :program))
  (mv-let (hit exp) (acl2::pseudo-translate term nil w)
    (declare (ignore hit))
    exp))

(defun pseudo-trans-list (list w)
  (declare (xargs :mode :program))
  (if (not (consp list)) nil
    (cons (pseudo-trans (car list) w)
          (pseudo-trans-list (cdr list) w))))

(defun syntaxp-eval (term state)
  (declare (xargs :mode :program))
  (er-let* ((value (trans-eval term 'syntaxp-eval state t)))
    (value (cdr value))))

(defun akeys (alist)
  (if (not (consp alist)) nil
    (acl2::let ((entry (car alist)))
      (cons (car entry) (akeys (cdr alist))))))

(defun avals (alist)
  (if (not (consp alist)) nil
    (acl2::let ((entry (car alist)))
      (cons (cadr entry) (avals (cdr alist))))))

(defun instantiate-term (term binding)
  (acl2::beta-reduce-term nil term (akeys binding) (avals binding)))

(defun instantiate-soft-alist (alist binding)
  (if (not (consp alist)) nil
    (acl2::let ((entry (car alist)))
      (cons (list (car entry) (instantiate-term (cadr entry) binding))
            (instantiate-soft-alist (cdr alist) binding)))))

(defun map-instantiate-soft-alist (post blist)
  (if (not (consp blist)) nil
    (cons (instantiate-soft-alist post (car blist))
          (map-instantiate-soft-alist post (cdr blist)))))

(defun instantiate-term-list (args binding)
  (if (not (consp args)) nil
    (cons (instantiate-term (car args) binding)
          (instantiate-term-list (cdr args) binding))))

(defun instantiate-cases-with-bindings (cases blist)
  (if (not (consp blist)) nil
    (append (instantiate-term-list cases (car blist))
            (instantiate-cases-with-bindings cases (cdr blist)))))

(defun check (term clause state)
  (declare (xargs :mode :program))
  (er-let* ((ok (acl2::bash-fn `(or ,@clause ,term) nil nil nil state)))
    (value (not ok))))

(defun assocx (key alist)
  (declare (type t key alist))
  (if (not (consp alist)) nil
    (acl2::let ((entry (car alist)))
      (if (not (consp entry)) nil
        (if (equal key (car entry)) entry
          (assocx key (cdr alist)))))))

;; ;; Technically not equiv .. but subsumed.
;; (defun binding-equiv (binding zlist)
;;   (if (not (consp binding)) t
;;     (acl2::let ((entry (car binding)))
;;       (acl2::let ((hit (assocx (car entry) zlist)))
;;         (and (consp hit)
;;              (equal (cadr entry) (cadr hit))
;;              (binding-equiv (cdr binding) zlist))))))

;; (defun binding-member (binding blist)
;;   (if (not (consp blist)) nil
;;     (or (binding-equiv binding (car blist))
;;         (binding-member binding (cdr blist)))))

;; (defun uniquify-bindings (list)
;;   (if (not (consp list)) nil
;;     (if (binding-member (car list) (cdr list))
;;         (uniquify-bindings (cdr list))
;;       (cons (car list)
;;             (uniquify-bindings (cdr list))))))

(defun minus-bindings (blist blist0)
  (if (not (consp blist)) nil
    (if (member-equal (car blist) blist0)
        (minus-bindings (cdr blist) blist0)
      (cons (car blist)
            (minus-bindings (cdr blist) blist0)))))

;; (defun << (x y) (not (lexorder y x)))

(defun insert-entry (key value alist)
  (declare (type t key value alist))
  (if (not (consp alist)) (cons (list key value) alist)
    (acl2::let ((entry (car alist)))
      (if (not (consp entry)) (insert-entry key value (cdr alist))
        (if (acl2::<< key (car entry)) (cons (list key value) alist)
          (cons entry (insert-entry key value (cdr alist))))))))

(defun normalize-alist (alist res)
  (if (not (consp alist)) res
    (acl2::let ((entry (car alist)))
      (if (assocx (car entry) res)
          (normalize-alist (cdr alist) res)
        (acl2::let ((res (insert-entry (car entry) (cadr entry) res)))
          (normalize-alist (cdr alist) res))))))

(defun normalize-bindings (blist)
  (if (not (consp blist)) nil
    (cons (normalize-alist (car blist) t)
          (normalize-bindings (cdr blist)))))

(defun compress-normalized-bindings (blist)
  (if (not (consp blist)) nil
    (acl2::let ((binding (car blist)))
      (acl2::let ((blist (compress-normalized-bindings (cdr blist))))
        (if (member-equal binding blist) blist
          (cons binding blist))))))

(defun compress-bindings (blist)
  (compress-normalized-bindings (normalize-bindings blist)))

(defun update-binding (alist binding)
  (if (not (consp alist)) binding
    (cons (car alist)
          (update-binding (cdr alist) binding))))

(defun map-update-binding (blist binding)
  (if (not (consp blist)) nil
    (cons (update-binding (car blist) binding)
          (map-update-binding (cdr blist) binding))))

(defun equal-to-all (x list)
  (if (not (consp list)) t
    (and (equal x (car list))
         (equal-to-all x (cdr list)))))

(defun all-equal (list)
  (if (not (consp list)) t
    (equal-to-all (car list) (cdr list))))

(mutual-recursion

 (defun unify-pattern-match-args-aux (pargs targs bindings)
   (if (and (consp pargs)
            (consp targs))
       (acl2::let ((bindings (unify-pattern-match (car pargs) (car targs) bindings)))
         (and bindings
              (unify-pattern-match-args-aux (cdr pargs) (cdr targs) bindings)))
     bindings))

 (defun unify-pattern-match (pattern term bindings)
   (if (symbolp pattern)
       (acl2::let ((hit (assocx pattern bindings)))
         (if hit (and (equal term (cadr hit)) bindings)
           (cons (list pattern term) bindings)))
     (if (not (consp pattern))
         (and (not (consp term)) (equal pattern term) bindings)
       (and (consp term)
            (if (equal (car pattern) (car term))
                (unify-pattern-match-args-aux (cdr pattern) (cdr term) bindings)
              nil)))))
 )

(mutual-recursion

 (defun all-unify-pattern-match-args-fn (pfn pargs targs bindings)
   (declare (xargs :mode :program))
   (if (not (consp targs)) nil
     (append (all-unify-pattern-match-term-fn pfn pargs (car targs) bindings)
             (all-unify-pattern-match-args-fn pfn pargs (cdr targs) bindings))))

 (defun all-unify-pattern-match-term-fn (pfn pargs term bindings)
   (declare (xargs :mode :program))
   (and (consp term)
        (acl2::let ((hit (and (equal pfn (car term))
                        (unify-pattern-match-args-aux pargs (cdr term) bindings))))
          (append (and hit (list hit))
                  (all-unify-pattern-match-args-fn pfn pargs (cdr term) bindings)))))

 )

(defun all-unify-pattern-match-term (pattern term bindings)
   (declare (xargs :mode :program))
  (if (symbolp pattern)
      (acl2::let ((hit (assocx pattern bindings)))
        (if hit (and (equal term (cadr hit)) bindings)
          (if (not (equal pattern term)) nil
            (cons (list pattern term) bindings))))
    (if (not (consp pattern))
        (and (not (consp term)) (equal pattern term) bindings)
      (all-unify-pattern-match-term-fn (car pattern) (cdr pattern) term bindings))))

(defun all-unify-pattern-match-clause-term (pattern clause bindings)
   (declare (xargs :mode :program))
  (if (not (consp clause)) nil
    (acl2::let ((hits (all-unify-pattern-match-term pattern (car clause) bindings)))
      (append hits (all-unify-pattern-match-clause-term pattern (cdr clause) bindings)))))

(defun all-unify-pattern-match-clause (pattern clause bindings)
  (if (not (consp clause)) nil
    (acl2::let ((hit (unify-pattern-match pattern (car clause) bindings)))
      (if hit (cons hit (all-unify-pattern-match-clause pattern (cdr clause) bindings))
        (all-unify-pattern-match-clause pattern (cdr clause) bindings)))))

(defun add-literal-symbols (symbols binding)
  (if (not (consp symbols)) binding
    (acl2::let ((binding (cons (list (car symbols) (car symbols)) binding)))
      (add-literal-symbols (cdr symbols) binding))))

(defun keep-alist-keys (symbols binding)
  (declare (type (satisfies true-listp) symbols))
  (if (not (consp binding)) binding
    (acl2::let ((entry (car binding)))
      (if (not (consp entry)) (keep-alist-keys symbols (cdr binding))
        (acl2::let ((key (car entry)))
          (if (not (member-equal key symbols)) (keep-alist-keys symbols (cdr binding))
            (cons entry
                  (keep-alist-keys symbols (cdr binding)))))))))

(defun quote-values (binding)
  (if (not (consp binding)) nil
    (acl2::let ((entry (car binding)))
      (cons (list (car entry) `(quote ,(cadr entry)))
            (quote-values (cdr binding))))))

(defun bind-keys (keys alist)
  (if (not (consp keys)) t
    (acl2::let ((hit (assoc (car keys) alist)))
      (if (not (consp hit)) (hard-error :bind-free "Unbound variable: ~x0" (acons #\0 (car keys) nil))
        (cons (list (car hit) (cdr hit))
              (bind-keys (cdr keys) alist))))))

(defun map-bind-keys (keys vlist-list)
  (if (not (consp vlist-list)) nil
    (acl2::let ((binding (bind-keys keys (car vlist-list))))
      (acl2::let ((res (map-bind-keys keys (cdr vlist-list))))
        (if (not binding) res (cons binding res))))))

;; (replicate-bindings (((i 'a)) ((i 'b))) ((j i)))

;; (((i 'a) (j 'a))
;;  ((i 'a) (j 'b))
;;  ((i 'b) (j 'a))
;;  ((i 'b) (j 'b)))

(defun replicate-bindings (b0 b1 alist)
  (acl2::let ((alist (instantiate-soft-alist alist b0)))
    (update-binding alist b1)))

(defun map-replicate-bindings-2 (b0 blist1 alist)
  (if (not (consp blist1)) nil
    (cons (replicate-bindings b0 (car blist1) alist)
          (map-replicate-bindings-2 b0 (cdr blist1) alist))))

(defun map-replicate-bindings-1 (blist0 blist1 alist)
  (if (not (consp blist0)) nil
    (append (map-replicate-bindings-2 (car blist0) blist1 alist)
            (map-replicate-bindings-1 (cdr blist0) blist1 alist))))

(defun map-replicate-bindings (blist alist)
  (map-replicate-bindings-1 blist blist alist))

#+joe
(acl2::let ((blist (list (list (list :x 1) (list :a 0) (list :b 1))
                   (list (list :x 2) (list :a 2) (list :b 3))
                   (list (list :x 3) (list :a 4) (list :b 5))))
      (alist (list (list :a :b))))
  (acl2::let ((alist2 (append alist (invert-soft-alist alist))))
    (map-commutes blist alist2)))

#+joe
(acl2::let ((blist (list (list (list :a 0) (list :b 1))
                   (list (list :a 2) (list :b 3))
                   (list (list :a 4) (list :b 5))))
      (alist (list (list :a :b))))
  (acl2::let ((alist2 (append alist (invert-soft-alist alist))))
    (acl2::let ((blist (append blist (map-commutes blist alist2))))
      (map-transitive blist alist))))

#+joe
(acl2::let ((blist (list (list (list :a 0) (list :b 1))
                   (list (list :a 1) (list :b 2))
                   (list (list :a 2) (list :b 3))
                   (list (list :a 2) (list :b 7))))
      (alist (list (list :a :b))))
  (acl2::let ((blist (map-replicate-bindings blist alist)))
    (map-equiv blist alist)))

(defun commute-binding (binding alist)
  (declare (xargs :measure (len alist)))
  (if (not (consp alist)) binding
    (acl2::let ((entry (car alist)))
      (acl2::let ((skey (car entry))
            (dkey (cadr entry)))
        (acl2::let ((hit (assocx skey binding)))
          (if (not hit) (hard-error :commute "Unbound variable: ~x0" (acons #\0 skey nil))
            (cons (list dkey (cadr hit))
                  (commute-binding binding (cdr alist)))))))))

(defun map-commutes (blist alist)
  (if (not (consp blist)) nil
    (cons (commute-binding (car blist) alist)
          (map-commutes (cdr blist) alist))))

(defun invert-soft-alist (alist)
  (if (not (consp alist)) nil
    (acl2::let ((entry (car alist)))
      (cons (list (cadr entry) (car entry))
            (invert-soft-alist (cdr alist))))))

(mutual-recursion

 (defun filter-each-binding-by-pattern-rec (exp clause blist state)
   (if (not (consp blist)) (value nil)
     (er-let* ((b1  (unify-pattern-match-expression exp clause (car blist) state))
               (res (filter-each-binding-by-pattern-rec exp clause (cdr blist) state)))
       (value (append b1 res)))))

 (defun filter-each-binding-by-pattern (exp clause blist state)
   (filter-each-binding-by-pattern-rec exp clause blist state))

 (defun and-unify-pattern-match-expression-rec (elist clause blist state)
   (if (not (consp elist)) (value blist)
     (er-let* ((blist (filter-each-binding-by-pattern (car elist) clause blist state)))
       (and-unify-pattern-match-expression-rec (cdr elist) clause blist state))))

 (defun and-unify-pattern-match-expression (elist clause binding state)
   (and-unify-pattern-match-expression-rec elist clause (list binding) state))

 (defun or-unify-pattern-match-expression-rec (elist clause binding state)
   (declare (xargs :mode :program))
   (if (not (consp elist)) (value nil)
     (er-let* ((blist (unify-pattern-match-expression (car elist) clause binding state))
               (res   (or-unify-pattern-match-expression-rec (cdr elist) clause binding state)))
       (value (append blist res)))))

 (defun or-unify-pattern-match-expression (elist clause binding state)
   (or-unify-pattern-match-expression-rec elist clause binding state))

 (defun first-unify-pattern-match-expression-rec (elist clause binding state)
   (declare (xargs :mode :program))
   (if (not (consp elist)) (value nil)
     (er-let* ((blist (unify-pattern-match-expression (car elist) clause binding state)))
       (if blist (value blist)
         (first-unify-pattern-match-expression-rec (cdr elist) clause binding state)))))

 (defun first-unify-pattern-match-expression (elist clause binding state)
   (first-unify-pattern-match-expression-rec elist clause binding state))

 (defun unify-pattern-match-expression-call (fn body post clause call-binding state)
   (declare (ignorable fn))
   (er-let* ((blist (unify-pattern-match-expression body clause call-binding state)))
     (value (map-instantiate-soft-alist post blist))))

(defun unify-pattern-match-expression (exp clause binding state)
   (declare (xargs :mode :program))
   (case-match exp
     ;; ((:commutes ('not (fn a b)))
     ;;  (let* ((b1 (all-unify-pattern-match-clause `(not (,fn ,a ,b)) clause binding))
     ;;         (b2 (all-unify-pattern-match-clause `(not (,fn ,b ,a)) clause binding)))
     ;;    (value (append b1 b2))))
     ;; ((:commutes (fn a b))
     ;;  (let* ((b1 (all-unify-pattern-match-clause `(,fn ,a ,b) clause binding))
     ;;         (b2 (all-unify-pattern-match-clause `(,fn ,b ,a) clause binding)))
     ;;    (value (append b1 b2))))
     ((:and . elist)
      (and-unify-pattern-match-expression elist clause binding state))
     ((:or . elist)
      (or-unify-pattern-match-expression elist clause binding state))
     ((:first . elist)
      (first-unify-pattern-match-expression elist clause binding state))
     ((:implies a b)
      (er-let* ((blist (unify-pattern-match-expression a clause binding state)))
        (if (not blist) (value (list binding))
          (filter-each-binding-by-pattern b clause blist state))))
     ((:pass) (value (list binding)))
     ((:if x a b) ;; if/then/else construct
      (er-let* ((blist (unify-pattern-match-expression x clause binding state)))
        (if (not blist) (unify-pattern-match-expression b clause binding state)
          (filter-each-binding-by-pattern a clause blist state))))
     ((:context pre (fn body) post) ;; support for call/return
      (acl2::let ((call-binding (instantiate-soft-alist pre binding)))
        (er-let* ((blist (unify-pattern-match-expression-call fn body post clause call-binding state)))
          (value (map-update-binding blist binding)))))
     ((:not exp)
      (er-let* ((blist (unify-pattern-match-expression exp clause binding state)))
        (value (if (not blist) (list binding) nil))))
     ((:check exp)
      (acl2::let ((exp (instantiate-term exp binding)))
        (er-let* ((ok (check exp clause state)))
          (value (if ok (list binding) nil)))))
     ((:bind . alist)
      (acl2::let ((alist (instantiate-soft-alist alist binding)))
        (value (list (update-binding alist binding)))))
     ((:literally . symbols) ;; match symbol names exactly
      (value (list (add-literal-symbols symbols binding))))
     ;;
     ;; (:keep a b c)
     ;;
     ;; Filter out all bindings except for those associated with
     ;; the variables '(a b c)
     ((:keep . symbols)
      (value (list (keep-alist-keys symbols binding))))
     ;;
     ;; (:replicate (foo x y) (a x) (b y))
     ;;
     ;; (:and (foo x y) (foo a b))
     ;;
     ((:replicate exp . alist)
      (er-let* ((blist (unify-pattern-match-expression exp clause binding state)))
        (value (map-replicate-bindings blist alist))))
     ((:commutes exp . alist)
      (er-let* ((blist (unify-pattern-match-expression exp clause binding state)))
        (acl2::let ((alist (append alist (invert-soft-alist alist))))
          (acl2::let ((blist (append blist (map-commutes blist alist))))
            (value blist)))))
     ((:match var exp)
      (acl2::let ((var (instantiate-term var binding)))
        (unify-pattern-match-expression exp (list var) binding state)))
     ((:syntaxp exp)
      (acl2::let ((qbinding (quote-values binding)))
        (acl2::let ((exp (instantiate-term exp qbinding)))
          (er-let* ((value (syntaxp-eval exp state)))
            (value (if value (list binding) nil))))))
     ((:bind-free exp args)
      (acl2::let ((qbinding (quote-values binding)))
        (acl2::let ((exp (instantiate-term exp qbinding)))
          (er-let* ((vlist-list (syntaxp-eval exp state)))
            (if (not vlist-list) (value nil)
              (acl2::let ((blist (map-bind-keys args vlist-list)))
                (value (map-update-binding blist binding))))))))
     ((:equal . elist)
      (acl2::let ((elist (instantiate-term-list elist binding)))
        (value (and (all-equal elist) (list binding)))))
     ((:either exp)
      (value (append
              (all-unify-pattern-match-clause exp clause binding)
              (all-unify-pattern-match-clause `(not ,exp) clause binding))))
     ((:term exp)
      (acl2::let ((blist (all-unify-pattern-match-clause-term exp clause binding)))
        (acl2::let ((blist (compress-bindings blist)))
          (value blist))))
     (&
      (value (all-unify-pattern-match-clause exp clause binding)))))

 )

(defun map-formals-to-actuals (formals actuals)
  (if (not (and (consp formals) (consp actuals))) nil
    (cons (list (car formals) (car actuals))
          (map-formals-to-actuals (cdr formals) (cdr actuals)))))

;; A notional grammar for pattern-hint expressions.
;;
;; symbol-alist : nil | ((symbol symbol) . symbol-alist)
;; term-alist   : nil | ((symbol term) . term-alist)
;; term-list    : nil | (term . term-list)
;; expr-list    : nil | (expr . expr-list)
;; expr: (:and   . expr-list)                     | ;; Compute the intersection of all of the bindings computed for expr-list
;;       (:or    . expr-list)                     | ;; Compute the union of all of the bindings computed for expr-list
;;       (:first . expr-list)                     | ;; Return the first binding found for expr-list
;;       (:pass)                                  | ;; Continue
;;       (:if expr expr exp)                      | ;; Match the first expression.  If successful, continue with the second.  If not, match the third.
;;       (:implies expr expr)                     | ;; Match the first expression.  If successful, continue with the second.
;;       (:call (symbol . term-list) symbol-list) | ;; Call the specified pattern function, bind each symbol in symbol-list to the values returned.
;;       (:not expr)                              | ;; If expr does not generate a binding, continue
;;       (:commutes expr symbol-alist)            | ;; Treat the pairs of symbols in symbol-alist as "commuting" .. compute a binding that reflects that.
;;       (:replicate expr symbol-alist)           | ;; Compute a cartesian-product binding for each pair of symbols in symbol-alist.
;;       ;;
;;       (:syntaxp term)                          | ;; Instantiate and evaluate term.  If not nil, continue
;;       (:equal . term-list)                     | ;; If all instantiated terms are equal, continue
;;       (:bind-free term symbol-list)            | ;; Instantiate and evaluate term.  Bind each symbol in symbol-list to the values returned.
;;       (:check  term)                           | ;; Call the simplifier to establish an instance of term.  If successful, continue
;;
;;       (:bind . term-alist)                     | ;; Bind each symbol to its associated term instance (may overwrite bindings)
;;       (:literally . symbol-list)               | ;; Bind each symbol in the list to itself as a term
;;       (:keep . symbol-list)                    | ;; Keep only the symbols bound in symbol-list
;;       (:match term expr)                       | ;; pattern match term against expr
;;       (:either term)                           | ;; Match either true or negated versions of term in the clause
;;       (:term   term)                           | ;; Match subterms appearing in the clause against term
;;       term                                       ;; Match term against terms appearing in the clause
;;
(defun translate-term-soft-alist (alist w)
   (declare (xargs :mode :program))
  (if (not (consp alist)) nil
    (acl2::let ((entry (car alist)))
      (cons (list (car entry) (pseudo-trans (cadr entry) w))
            (translate-term-soft-alist (cdr alist) w)))))

(defun translate-term-list (tlist w)
   (declare (xargs :mode :program))
  (if (not (consp tlist)) nil
    (acl2::let ((term (car tlist)))
      (cons (pseudo-trans term w)
            (translate-term-list (cdr tlist) w)))))

(mutual-recursion

 (defun translate-expression-list (list w)
   (declare (xargs :mode :program))
   (if (not (consp list)) nil
     (cons (translate-expression (car list) w)
           (translate-expression-list (cdr list) w))))

 (defun translate-expression (exp w)
   (declare (xargs :mode :program))
   (case-match exp
     ((:and . elist)
      `(:and ,@(translate-expression-list elist w)))
     ((:or . elist)
      `(:or ,@(translate-expression-list elist w)))
     ((:first . elist)
      `(:first ,@(translate-expression-list elist w)))
     ((:implies a b)
      `(:implies ,(translate-expression a w)
                 ,(translate-expression b w)))
     ((:pass) exp)
     ((:if x a b)
      `(:if ,(translate-expression x w)
            ,(translate-expression a w)
            ,(translate-expression b w)))
     ((:call (fn . actuals) retvars)
      (acl2::let ((db (table::get :pattern-hint-definition-database w)))
        (acl2::let ((defn (cdr (assoc fn db))))
          (case-match defn
            ((fn formals body retexps)
             (acl2::let ((retexps (translate-term-list retexps w))
                   (actuals (translate-term-list actuals w)))
               (acl2::let ((body (translate-expression body w)))
                 `(:context ,(map-formals-to-actuals formals actuals)
                            (,fn ,body)
                            ,(map-formals-to-actuals retvars retexps)))))
            (&
             (acl2::let ((zed (hard-error 'translate-expression "Undefined pattern hint function ~x0" (acons #\0 fn nil))))
               (declare (ignore zed))
               `(:pass)))))))
     ((:context pre (fn body) post)
      `(:context ,(translate-term-soft-alist pre w)
                 (,fn ,(translate-expression body w))
                 ,(translate-term-soft-alist post w)))
     ((:not exp)
      `(:not ,(translate-expression exp w)))
     ((:commutes exp . alist)
      `(:commutes ,(translate-expression exp w) ,@alist))
     ((:check term)
      (acl2::let ((term (pseudo-trans term w)))
        `(:check ,term)))
     ((:either term)
      (acl2::let ((term (pseudo-trans term w)))
        `(:either ,term)))
     ((:syntaxp term)
      (acl2::let ((term (pseudo-trans term w)))
        `(:syntaxp ,term)))
     ((:bind-free term vars)
      (acl2::let ((term (pseudo-trans term w)))
        `(:bind-free ,term ,vars)))
     ((:bind . alist)
      `(:bind ,@(translate-term-soft-alist alist w)))
     ((:literally . symbols)
      `(:literally ,@symbols))
     ((:keep . symbols)
      `(:keep ,@symbols))
     ((:replicate exp . alist)
      (acl2::let ((exp (translate-expression exp w)))
        `(:replicate ,exp ,@alist)))
     ((:match term exp)
      `(:match ,(pseudo-trans term w) ,(translate-expression exp w)))
     ((:equal . tlist)
      `(:equal ,@(translate-term-list tlist w)))
     ((:term term)
      (acl2::let ((term (pseudo-trans term w)))
        `(:term ,term)))
     (&
      (pseudo-trans exp w))))

 )

(mutual-recursion

 (defun clausify-expression-list (list)
   (declare (xargs :mode :program))
   (if (not (consp list)) nil
     (cons (clausify-expression (car list))
           (clausify-expression-list (cdr list)))))

 (defun clausify-expression (exp)
   (declare (xargs :mode :program))
   (case-match exp
     ((:and . elist)
      `(:and ,@(clausify-expression-list elist)))
     ((:or . elist)
      `(:or ,@(clausify-expression-list elist)))
     ((:first . elist)
      `(:first ,@(clausify-expression-list elist)))
     ((:implies a b)
      `(:implies ,(clausify-expression a)
                 ,(clausify-expression b)))
     ((:pass) exp)
     ((:if x a b)
      `(:if ,(clausify-expression x)
            ,(clausify-expression a)
            ,(clausify-expression b)))
     ((:context pre (fn body) post)
      `(:context ,pre (,fn ,(clausify-expression body)) ,post))
     ((:not exp)
      `(:not ,(clausify-expression exp)))
     ((:commutes exp . alist)
      `(:commutes ,(clausify-expression exp) ,@alist))
     ((:check . &) exp)
     ((:either . &) exp)
     ((:bind . &) exp)
     ((:literally . &) exp)
     ((:keep . &) exp)
     ((:replicate exp . alist)
      `(:replicate ,(clausify-expression exp) ,@alist))
     ((:match . &) exp)
     ((:equal . &) exp)
     ((:term . &) exp)
     ((:syntaxp . &) exp)
     ((:bind-free . &) exp)
     (&
      (not-term exp))))

 )

#+joe
(trace$ (unify-pattern-match-expression-call
         :entry `(unify-pattern-match-expression-call ,(nth 0 arglist) ,(nth 4 arglist))
         :exit  (nth 1 values)))

(defmacro trace-pattern-calls (&rest args)
  `(trace$ (unify-pattern-match-expression-call
            :cond (member-equal (nth 0 arglist) '(,@args))
            :entry `(,(nth 0 arglist) ,(nth 4 arglist))
            :exit  (nth 1 values))))


(defun self-bind (vars)
  (if (not (consp vars)) nil
    (cons (list (car vars) (car vars))
          (self-bind (cdr vars)))))

(defun instantiate-expand (expand binding w)
  (declare (xargs :mode :program))
  (case-match expand
    ((:free vars term)
     (acl2::let ((binding (update-binding (self-bind vars) binding)))
       `(:free ,vars ,(instantiate-term (pseudo-trans term w) binding))))
    (& (instantiate-term (pseudo-trans expand w) binding))))

(defun instantiate-expand-list (list binding w)
  (declare (xargs :mode :program))
  (if (not (consp list)) nil
    (cons (instantiate-expand (car list) binding w)
          (instantiate-expand-list (cdr list) binding w))))

(defun instantiate-expansions-with-bindings (expansions blist w)
  (declare (xargs :mode :program))
  (if (not (consp blist)) nil
    (append (instantiate-expand-list expansions (car blist) w)
            (instantiate-expansions-with-bindings expansions (cdr blist) w))))

(defun instantiate-use (use binding)
  (case-match use
    ((:instance formula . instantiation)
     (prog2$
      #+joe
      (cw "Using ~x0 under ~x1 ~%" formula binding)
      (cw "Using ~x0~%" formula)
      `(:instance ,formula ,@(instantiate-soft-alist instantiation binding))))
    (& use)))

(defun instantiate-use-list (list binding)
  (if (not (consp list)) nil
    (cons (instantiate-use (car list) binding)
          (instantiate-use-list (cdr list) binding))))

(defun instantiate-uses-with-bindings (use blist)
  (if (not (consp blist)) nil
    (append (instantiate-use-list use (car blist))
            (instantiate-uses-with-bindings use (cdr blist)))))

(defun instantiate-restriction (restriction binding)
  (case-match restriction
    ((lemma instantiation)
     `(,lemma ,(instantiate-soft-alist instantiation binding)))
    (& restriction)))

(defun instantiate-restriction-list (list binding)
  (if (not (consp list)) nil
    (cons (instantiate-restriction (car list) binding)
          (instantiate-restriction-list (cdr list) binding))))

(defun instantiate-restrictions-with-bindings (restrictions blist)
  (if (not (consp blist)) nil
    (append (instantiate-restriction-list restrictions (car blist))
            (instantiate-restrictions-with-bindings restrictions (cdr blist)))))

;; Once you match a pattern, you should drop it
;; (via computed-hint-replacement)
(defun run-opener-hint1 (flg n)  ; flg = stable-under-simplificationp
  (if flg
      `(:computed-hint-replacement
         ((run-opener-hint1 stable-under-simplificationp ,(- n 1)))
        :in-theory (enable run-n+1)
        :restrict ((run-n+1 ((n ,n)))))
    nil))

(defun keep-only (n list)
  (if (or (not (consp list)) (zp n)) nil
    (cons (car list) (keep-only (1- n) (cdr list)))))

(defun pattern-hint-fn-instance (blist0 exp0 uses0 cases0 expansions0 restrictions0 in-theory do-not repeat slow stable name susp clause state)
  (declare (xargs :mode :program)
           (ignorable stable))
  ;;
  ;; DAG -- note that the call here uses 't' rather than nil for the
  ;; initial binding.  This was so that we could use a non-nil binding
  ;; as a signal that something succeeded.  We appear to have
  ;; (largely?) transitioned to using blist in this manner.  I wonder
  ;; about any vestiges of this old behavior ..
  ;;
  (if (and stable (not susp)) (mv nil nil nil nil nil nil nil nil state)
    (mv-let (err blist state) (unify-pattern-match-expression exp0 clause t state)
      (declare (ignore err))
      (acl2::let ((blist (normalize-bindings blist)))
        (acl2::let ((blist (minus-bindings blist blist0)))
          (if (not blist) (mv nil nil nil nil nil nil nil nil state)
            (acl2::let ((blist (compress-normalized-bindings blist)))
              (prog2$
               (if name (cw "Firing pattern hint ~x0~%" name)
                 (cw "Firing anonymous pattern hint~%"))
               ;; We only allow 1 case instantiation at a time ..
               (acl2::let ((blist (if cases0 (list (car blist))
                              (if (integerp slow) (keep-only slow blist)
                                (if slow (list (car blist)) blist)))))
                 (acl2::let ((blistN (if (not repeat) (append blist blist0) blist0)))
                   (acl2::let ((cases  (pseudo-trans-list cases0 (w state))))
                     (acl2::let ((uses         (instantiate-uses-with-bindings uses0 blist))
                                 (cases        (instantiate-cases-with-bindings cases blist))
                                 (expansions   (instantiate-expansions-with-bindings expansions0 blist (w state)))
                                 (restrictions (instantiate-restrictions-with-bindings restrictions0 blist)))
                       (mv t blistN uses cases expansions restrictions in-theory do-not state)))))))))))))

(defun get-kwlist-binding (key default alist)
  (if (and (consp alist) (consp (cdr alist)))
      (if (equal key (car alist)) (cadr alist)
        (get-kwlist-binding key default (cddr alist)))
    default))

(defun parse-hints (hints)
  (acl2::let ((kwlist (cddr hints)))
    (mv
     (get-kwlist-binding :name      nil kwlist)
     (cadr hints)
     (get-kwlist-binding :limit     nil kwlist)
     (get-kwlist-binding :use       nil kwlist)
     (get-kwlist-binding :cases     nil kwlist)
     (get-kwlist-binding :expand    nil kwlist)
     (get-kwlist-binding :restrict  nil kwlist)
     (get-kwlist-binding :in-theory nil kwlist)
     (get-kwlist-binding :do-not    nil kwlist)
     (get-kwlist-binding :repeat    nil kwlist)
     (get-kwlist-binding :slow      nil kwlist)
     (get-kwlist-binding :stable    t   kwlist)
     )))

(defun split-in-theory-hint (hint)
  (if (not hint) (mv nil nil)
    (case-match hint
      (('e/d elist dlist)
       (mv elist dlist))
      (('enable . elist)
       (mv elist nil))
      (('disable . dlist)
       (mv nil dlist))
      (&
       (acl2::let ((zed (hard-error 'pattern-hint "Unrecognized theory event ~x0" (acons #\0 hint nil))))
         (declare (ignore zed))
         (mv nil nil))))))

;; Sadly we may need to track the enable/disable theory.
;; :in-theory (disable )
;; :in-theory (enable )
;; :in-theory (e/d elist dlist)
;; This means we will probably want an initial e/d theory.
;; Same may be true of :do-not hints.
;; :do-not '(preprocess)
;;
(defun pattern-hint-list-fn-rec (blist hints hit res uses cases expansions restrictions etheory dtheory do-not susp clause state)
  (declare (xargs :mode :program))
  (if (not (and (consp blist) (consp hints))) (mv hit (revappend res nil) uses cases expansions restrictions etheory dtheory do-not state)
    (mv-let (name0 exp0 limit0 uses0 cases0 expansions0 restrictions0 in-theory0 do-not0 repeat0 slow0 stable0) (parse-hints (car hints))
      (declare (ignore limit0))
      (acl2::let ((binding0 (car blist)))
        (cond
         ((and do-not do-not0)
          (mv-let (err value state) (acl2::error1 'pattern-hint "" "Multiple do-not hints: ~x0 ~x1" (acons #\0 do-not (acons #\1 do-not0 nil)) state)
            (declare (ignore err value))
            (mv nil nil nil nil nil nil nil nil nil state)))
         (t
          (mv-let (hit1 binding1 uses1 cases1 expansions1 restrictions1 in-theory1 do-not1 state)
            (pattern-hint-fn-instance binding0 exp0 uses0 cases0 expansions0 restrictions0 in-theory0 do-not0 repeat0 slow0 stable0 name0 susp clause state)
            (cond
             ((not hit1)
              (acl2::let ((res (cons binding0 res)))
                (pattern-hint-list-fn-rec (cdr blist) (cdr hints) hit res uses cases expansions restrictions etheory dtheory do-not susp clause state)))
             (t
              (mv-let (etheory1 dtheory1) (split-in-theory-hint in-theory1)
                (acl2::let ((res          (cons binding1 res))
                            (uses         (append uses1 uses))
                            (cases        (append cases1 cases))
                            (expansions   (append expansions1 expansions))
                            (restrictions (append restrictions1 restrictions))
                            (etheory      (append etheory1 etheory))
                            (dtheory      (append dtheory1 dtheory))
                            (do-not       do-not1))
                  (pattern-hint-list-fn-rec (cdr blist) (cdr hints) t res uses cases expansions restrictions etheory dtheory do-not susp clause state))))))))))))

(defun pattern-hint-list-fn (limit0 blist hints clause susp state)
  (declare (xargs :mode :program))
  (mv-let (hit blist uses cases expansions restrictions etheory dtheory do-not state)
      (pattern-hint-list-fn-rec blist hints nil nil nil nil nil nil nil nil nil susp clause state)
    (if (not hit) (value nil)
      (acl2::let ((theory       (and (or etheory dtheory) `(:in-theory (e/d ,etheory ,dtheory))))
                  (dont         (and do-not `(:do-not ,do-not)))
                  (uses         (and uses `(:use ,uses)))
                  (cases        (and cases `(:cases ,cases)))
                  (expansions   (and expansions `(:expand ,expansions)))
                  (restrictions (and restrictions `(:restrict ,restrictions))))
        (acl2::let ((hint (append theory dont uses cases expansions restrictions)))
          (acl2::let ((limit (nfix (1- limit0))))
            (acl2::let ((hint (if (and (not (zp limit0)) (zp limit)) hint
                          `(:computed-hint-replacement
                            ((pattern-hint-list-fn ',limit ',blist ',hints clause stable-under-simplificationp state))
                            ,@hint))))
              (value hint))))))))

(defun process-hints-fn (hint wrld)
  (declare (xargs :mode :program))
  (case-match hint
    ((:hints exp . kwlist)
     (acl2::let* ((exp    (translate-expression exp wrld))
                  (exp    (clausify-expression exp))
                  (name   (get-kwlist-binding :name nil kwlist)))
                 ;;(name   (or name 'un-named)))
       (list* name exp kwlist)))
    (('acl2::pattern-hint exp . kwlist)
     (acl2::let* ((exp    (translate-expression exp wrld))
                  (exp    (clausify-expression exp))
                  (name   (get-kwlist-binding :name nil kwlist)))
                 ;;(name   (or name 'un-named)))
       (list* name exp kwlist)))
    (('pattern::hint exp . kwlist)
     (acl2::let* ((exp    (translate-expression exp wrld))
                  (exp    (clausify-expression exp))
                  (name   (get-kwlist-binding :name nil kwlist)))
                 ;;(name   (or name 'un-named)))
       (list* name exp kwlist)))
    (& (list* nil `(:all) nil))))

(defun process-hints-list (hints wrld)
  (declare (xargs :mode :program))
  (if (not (consp hints)) nil
    (cons (process-hints-fn (car hints) wrld)
          (process-hints-list (cdr hints) wrld))))

(defun nil-list (ref)
  (if (not (consp ref)) nil
    (cons nil (nil-list (cdr ref)))))

(defun resolve-hint-definitions (hints wrld)
  (declare (xargs :mode :program))
  (if (not (consp hints)) nil
    (acl2::let ((hint (car hints)))
      (if (symbolp hint)
          (acl2::let ((db (table::get :pattern-hint-database wrld)))
            (acl2::let ((hit (assoc hint db)))
              (if (not hit) (hard-error :named-pattern-hint "Undefined pattern hint rule: ~x0" (acons #\0 hint nil))
                (acl2::let ((hint-list (cdr hit)))
                  (append (resolve-hint-definitions hint-list wrld)
                          (resolve-hint-definitions (cdr hints) wrld))))))
        (cons hint (resolve-hint-definitions (cdr hints) wrld))))))

(defmacro acl2::pattern-hint* (&rest hints)
  `(acl2::let ((hints '(,@hints)))
     (acl2::let ((hints (resolve-hint-definitions hints (w state))))
       (acl2::let ((hints (process-hints-list hints (w state)))
                   (blist (nil-list hints)))
         (pattern-hint-list-fn 0 blist hints clause stable-under-simplificationp state)))))

(defmacro pattern::hint* (&rest hints)
  `(acl2::pattern-hint* ,@hints))

(defun pattern-hint-fn (blist0 limit0 exp0 uses0 cases0 expansions0 restrictions0 in-theory do-not repeat slow stable name id clause susp state)
  (declare (xargs :mode :program)
           (ignorable id)
           )
  (if (and stable (not susp)) (value nil)
    (acl2::let* ((exp    (translate-expression exp0 (w state)))
                 (exp    (clausify-expression exp)))
      (mv-let (hit binding1 uses1 cases1 expansions1 restrictions1 in-theory1 do-not1 state)
          (pattern-hint-fn-instance blist0 exp uses0 cases0 expansions0 restrictions0 in-theory do-not repeat slow stable name susp clause state)
        (if (not hit) (value nil)
          (acl2::let ((theory       (and in-theory1 `(:in-theory ,in-theory1)))
                      (dont         (and do-not1 `(:do-not ,do-not1)))
                      (uses         (and uses1 `(:use ,uses1)))
                      (cases        (and cases1 `(:cases ,cases1)))
                      (expansions   (and expansions1 `(:expand ,expansions1)))
                      (restrictions (and restrictions1 `(:restrict ,restrictions1))))
            (acl2::let ((hint (append theory dont uses cases expansions restrictions)))
              (acl2::let ((limit (nfix (1- limit0))))
                (acl2::let ((hint (if (and (not (zp limit0)) (zp limit)) hint
                              `(:computed-hint-replacement
                                ((pattern-hint-fn ',binding1 ',limit ',exp0 ',uses0 ',cases0
                                                  ',expansions0 ',restrictions0 ',in-theory ',do-not
                                                  ',repeat ',slow ',stable ',name
                                                  id clause stable-under-simplificationp state))
                                ,@hint))))
                  (value hint))))))))))

(defmacro acl2::pattern-hint (exp &key (limit '0) (use 'nil) (cases 'nil) (expand 'nil) (restrict 'nil) (in-theory 'nil)
                                  (do-not 'nil) (repeat 'nil) (slow 'nil) (stable 't) (name 'nil))
  (if (symbolp exp)
      `(acl2::let ((name ',exp))
         (acl2::let ((db (table::get :pattern-hint-database (w state))))
           ;; First element of list ..
           (acl2::let ((hit (assoc name db)))
             (acl2::let ((zed (if (not hit) (hard-error :named-pattern-hint "Undefined pattern hint rule: ~x0" (acons #\0 name nil)) nil)))
               (declare (ignore zed))
               (acl2::let ((hint (car (cdr hit))))
                 (mv-let (name exp limit use0 cases0 expand0 restrict0 in-theory0 do-not0 repeat0 slow0 stable0) (parse-hints hint)
                   (acl2::let ((use       (or ',use use0))
                               (cases     (or ',cases cases0))
                               (expand    (or ',expand expand0))
                               (restrict  (or ',restrict restrict0))
                               (in-theory (or ',in-theory in-theory0))
                               (do-not    (or ',do-not do-not0))
                               (repeat    (or ',repeat repeat0))
                               (slow      (or ',slow   slow0))
                               (stable    (or ',stable stable0)))
                     (pattern-hint-fn nil limit exp use cases expand restrict
                                      in-theory do-not repeat slow stable name id clause stable-under-simplificationp state))))))))
    `(pattern-hint-fn nil ',limit ',exp ',use ',cases ',expand ',restrict ',in-theory ',do-not
                      ',repeat ',slow ',stable ',name id clause stable-under-simplificationp state)))

(defmacro pattern::hint (&rest args)
  `(acl2::pattern-hint ,@args))

(defmacro acl2::def-pattern-hint (name body &key (limit '0) (use 'nil) (cases 'nil) (repeat 'nil) (slow 'nil) (stable 't)
                                  (expand 'nil) (restrict 'nil) (in-theory 'nil) (do-not 'nil))
  (acl2::let ((kwlist `(:limit    ,limit
                  :use       ,use
                  :cases     ,cases
                  :expand    ,expand
                  :restrict  ,restrict
                  :in-theory ,in-theory
                  :do-not    ,do-not
                  :slow      ,slow
                  :stable    ,stable
                  :repeat    ,repeat
                  :name      ,name)))
    (acl2::let ((hint `(pattern::hint ,body ,@kwlist)))
      `(table::set :pattern-hint-database (acons ',name '(,hint) (table::get :pattern-hint-database world))))))

(defmacro acl2::def-pattern-hint-list (name hints)
  `(table::set :pattern-hint-database (acons ',name ',hints (table::get :pattern-hint-database world))))

(defmacro acl2::def-pattern-function (name args body &key (returns 'nil))
  (acl2::let ((spec `(,name ,args ,body ,returns)))
    `(table::set :pattern-hint-definition-database (acons ',name ',spec (table::get :pattern-hint-definition-database world)))))

(defmacro def::pattern-hint (&rest args)
  `(acl2::def-pattern-hint ,@args))

(defmacro def::pattern-hint-list (&rest args)
  `(acl2::def-pattern-hint-list ,@args))

(defmacro def::pattern-function (&rest args)
  `(acl2::def-pattern-function ,@args))

(local
 (encapsulate

    ()

  (defstub foo (x) nil)
  (defstub goo (x) nil)
  (defstub alpha (x y) nil)

  (defthm silly-rule
    (implies
     (and
      (integerp x)
      (integerp y))
     (integerp (+ x y)))
    :rule-classes nil)

  (defund beta (x) (equal x 0))
  (in-theory (disable (beta)))

  (defund gamma (x y) (equal x y))
  (in-theory (disable (gamma)))

  (def::pattern-function :alpha (a)
    (alpha a b)
    :returns (b))

  (defthm test-thm
    (implies
     (and
      (foo 3)
      (alpha 7 9)
      (goo 5)
      (beta 5)
      (alpha 5 p)
      (alpha 3 q))
     nil)
    :hints ((pattern::hint
             (:and
              (:or
               (foo x)
               (goo x))
              (:check (equal x 5))
              (:syntaxp (quotep x))
              (:call (:alpha x) (y)))
             :use ((:instance silly-rule
                              (x x)
                              (y y)
                              ))
             :expand ((beta x))
             :cases ((gamma x y)))
            )
    :rule-classes nil)

  (def::pattern-hint joe
    (:and
     (:or
      (foo x)
      (goo x))
     (:check (equal x 5))
     (:syntaxp (quotep x))
     (:call (:alpha x) (y)))
    :use ((:instance silly-rule
                     (x x)
                     (y y)
                     ))
    :expand ((beta x))
    :cases ((gamma x y)))

  (defthm test-thm-2
    (implies
     (and
      (foo 3)
      (alpha 7 9)
      (goo 5)
      (beta 5)
      (alpha 5 p)
      (alpha 3 q))
     nil)
    :hints ((pattern::hint joe))
  :rule-classes nil)

  (defthm test-thm-3
    (implies
     (and
      (foo 3)
      (alpha 7 9)
      (goo 5)
      (beta 5)
      (alpha 5 p)
      (alpha 3 q))
     nil)
    :hints ((pattern::hint*
             joe))
    :rule-classes nil)

  ))

;;
;; lte pattern
;;

(encapsulate
    ()
  ;;   ba    bb
  ;;   |   |-----------------------
  ;;
  ;; (< (+ ba ca) (+ bb cb))
  ;; (< ba (+ bb (- cb ca)))
  ;; (< ba (+ bb (- cy cx)))
  (local
   (defthm test
     (implies
      (and
       (integerp ba)
       (integerp bb)
       (integerp ca)
       (integerp cb)
       (integerp cx)
       (integerp cy)
       ;; From hypothesis
       (<= (+ ba ca) (+ bb cb)))
      (implies
       ;; Syntax check
       (<= (- cb ca) (- cy cx) )
       ;; Conclusion
       (<= (+ ba cx) (+ bb cy))))))


  )

(defun lte-check-fn (ca cb cx cy)
  (<= (- cb ca) (- cy cx)))

(defun lte-check (ca cb cx cy)
  (acl2::let ((ca (cadr ca))
              (cb (cadr cb))
              (cx (cadr cx))
              (cy (cadr cy)))
    (lte-check-fn ca cb cx cy)))

(def::pattern-function acl2::base-offset (z)
  (:match z (:first (:and (:syntaxp (quotep z))
                          (:bind (offset z) (base 0)))
                    (:if (+ offset base) (:syntaxp (quotep offset))
                         (:bind (offset 0) (base z)))))
  :returns (offset base))

(def::pattern-function acl2::common-base-lte (x y)
  (:first
   (:equal x y)
   (:and
    (:call (acl2::base-offset x) (cx bx))
    (:call (acl2::base-offset y) (cy by))
    (:equal bx by)
    (:syntaxp (<= (cadr cx) (cadr cy))))))

(def::pattern-function acl2::lte-match ()
  (:or (< a b)
       ;;(equal a b) ;; sigh .. appears very expensive.
       (not (< b a)))
  :returns (a b))

;; (< w x)
;; (< x y)
;; (< w z)

(def::pattern-function lte-match-2 ()
  (:or (:bind-free (default-lte-match) (a b))
       (:and (:replicate (:call (acl2::lte-match) (a c)) (cc a) (b c))
             ;; (<= a c)
             ;; (<= cc b)
             ;;
             ;;  (cc b) |             (a c)
             ;; --------+----------------------------
             ;;         | (< w x) | (< x y) | (< w z)
             ;; --------+----------------------------
             ;; (< w x) |    *
             ;; (< x y) |    *         *
             ;; (< w z) |                        *
             ;;
             ;; DAG -- ah .. this logic must properly
             ;; handle base-offset conditions.
             ;;
             ;; (<= a c) (<= cc b)
             ;;
             (:first (:call (acl2::common-base-lte c cc) nil)
                     (:and (:equal cc a)
                           (:equal  b c)))
             (:bind-free (expand-lte-match 'a a 'b b) (a b))
             ))
  :returns (a b))

;;
;; bind-free functions must return a list of value lists
;;
(defun expand-lte-match-default (xk x yk y)
  (declare (xargs :guard t))
  (list `((,xk . ,x) (,yk . ,y))))

(defun default-lte-match-default ()
  (declare (xargs :guard t))
  nil)

(defun list-of-alistp (x)
  (declare (type t x))
  (if (not (consp x)) (null x)
    (and (alistp (car x))
         (list-of-alistp (cdr x)))))

(encapsulate
    (
     ((expand-lte-match * * * *) => *)
     ((default-lte-match)    => *)
     )

  (local (defun expand-lte-match (xk x yk y)
           (expand-lte-match-default xk x yk y)))
  (local (defun default-lte-match ()
           (default-lte-match-default)))

  (defthm list-of-alistp-expand-lte-match
    (list-of-alistp (expand-lte-match xk x yk y)))

  (defthm true-listp-default-lte-match
    (list-of-alistp (default-lte-match)))

  )

(defattach expand-lte-match  expand-lte-match-default)
(defattach default-lte-match default-lte-match-default)

(def::pattern-function acl2::lte-filter-sort (x y)
  (:and
   (:call (acl2::base-offset x) (cx bx))
   (:call (acl2::base-offset y) (cy by))
   (:if (:equal bx by)
        (:if (:syntaxp (<= (cadr cx) (cadr cy))) (:bind (n x) (p y))
             (:and (:syntaxp (<= (cadr cy) (cadr cx)))
                   (:bind (n y) (p x))))
        (:and
         (:call (lte-match-2) (a b))
         (:call (acl2::base-offset a) (ca ba))
         (:call (acl2::base-offset b) (cb bb))
         (:if (:equal bx ba)
              (:and (:equal by bb)
                    (:syntaxp (lte-check ca cb cx cy))
                    (:bind (n x) (p y)))
              (:and (:equal bx bb)
                    (:equal by ba)
                    (:syntaxp (lte-check ca cb cy cx))
                    (:bind (n y) (p x)))))))
  :returns (n p))

(def::pattern-function acl2::lte-filter (x y)
  ;(:or (:match x 0)
  ;     (:match y (n))
  ;     (:match y (+ -1 (n)))
  (:and
   (:call (acl2::base-offset x) (cx bx))
   (:call (acl2::base-offset y) (cy by))
   (:if (:equal bx by) (:and ;;(:syntaxp (not (cw "constant check (<= ~x0 ~x1)~%" cx cy)))
                        (:syntaxp (<= (cadr cx) (cadr cy))))
        (:and
         (:call (lte-match-2) (a b))
         ;;(:syntaxp (not (cw "consider that (<= ~x0 ~x1)~%" a b)))
         (:call (acl2::base-offset a) (ca ba))
         (:equal bx ba)
         (:call (acl2::base-offset b) (cb bb))
         (:equal by bb)
         ;;(:syntaxp (not (cw "(implies (<= ~x0 ~x1) (<= ~x2 ~x3))~%" a b x y)))
         (:syntaxp (lte-check ca cb cx cy))))))

