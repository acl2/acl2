;;
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")

(include-book "misc/bash" :dir :system)
(include-book "misc/beta-reduce" :dir :system)
(include-book "coi/util/pseudo-translate" :dir :system)
(include-book "coi/util/table" :dir :system)

(set-state-ok t)

; Matt K. mod: Avoid ACL2(p) error from computed hint that returns state.
(set-waterfall-parallelism nil)

(defun not-term (term)
  (case-match term
    (('not term) term)
    (& `(not ,term))))

(defun pseudo-trans (term w)
  (declare (xargs :mode :program))
  (mv-let (hit exp) (pseudo-translate term nil w)
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
    (let ((entry (car alist)))
      (cons (car entry) (akeys (cdr alist))))))

(defun avals (alist)
  (if (not (consp alist)) nil
    (let ((entry (car alist)))
      (cons (cadr entry) (avals (cdr alist))))))

(defun instantiate-term (term binding)
  (beta-reduce-term nil term (akeys binding) (avals binding)))

(defun instantiate-soft-alist (alist binding)
  (if (not (consp alist)) nil
    (let ((entry (car alist)))
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
  (er-let* ((ok (bash-fn `(or ,@clause ,term) nil nil nil state)))
    (value (not ok))))

(defun assocx (key alist)
  (declare (type t key alist))
  (if (not (consp alist)) nil
    (let ((entry (car alist)))
      (if (not (consp entry)) nil
        (if (equal key (car entry)) entry
          (assocx key (cdr alist)))))))

;; ;; Technically not equiv .. but subsumed.
;; (defun binding-equiv (binding zlist)
;;   (if (not (consp binding)) t
;;     (let ((entry (car binding)))
;;       (let ((hit (assocx (car entry) zlist)))
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

(defun << (x y) (not (lexorder y x)))

(defun insert-entry (key value alist)
  (if (not (consp alist)) (cons (list key value) alist)
    (let ((entry (car alist)))
      (if (<< key (car entry)) (cons (list key value) alist)
        (cons entry (insert-entry key value (cdr alist)))))))

(defun normalize-alist (alist res)
  (if (not (consp alist)) res
    (let ((entry (car alist)))
      (if (assocx (car entry) res)
          (normalize-alist (cdr alist) res)
        (let ((res (insert-entry (car entry) (cadr entry) res)))
          (normalize-alist (cdr alist) res))))))

(defun normalize-bindings (blist)
  (if (not (consp blist)) nil
    (cons (normalize-alist (car blist) t)
          (normalize-bindings (cdr blist)))))

(defun compress-normalized-bindings (blist)
  (if (not (consp blist)) nil
    (let ((binding (car blist)))
      (let ((blist (compress-normalized-bindings (cdr blist))))
        (if (member-equal binding blist) blist
          (cons binding blist))))))

(defun compress-bindings (blist)
  (let ((blist (normalize-bindings blist)))
    (compress-normalized-bindings blist)))

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

(defun wildcard-p (x)
  (declare (type symbol x))
  (or (equal (symbol-name x) "*")
      (equal (symbol-name x) "_")))

(mutual-recursion

 (defun unify-pattern-match-args (pargs targs bindings)
   (if (and (consp pargs)
            (consp targs))
       (let ((bindings (unify-pattern-match (car pargs) (car targs) bindings)))
         (and bindings
              (unify-pattern-match-args (cdr pargs) (cdr targs) bindings)))
     bindings))

 (defun unify-pattern-match (pattern term bindings)
   (if (symbolp pattern)
       (if (wildcard-p pattern) bindings
         (let ((hit (assocx pattern bindings)))
           (if hit (and (equal term (cadr hit)) bindings)
             (cons (list pattern term) bindings))))
     (if (not (consp pattern))
         (and (not (consp term)) (equal pattern term) bindings)
       (and (consp term)
            (if (equal (car pattern) (car term))
                (unify-pattern-match-args (cdr pattern) (cdr term) bindings)
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
        (let ((hit (and (equal pfn (car term))
                        (unify-pattern-match-args pargs (cdr term) bindings))))
          (append (and hit (list hit))
                  (all-unify-pattern-match-args-fn pfn pargs (cdr term) bindings)))))

 )

(defun all-unify-pattern-match-term (pattern term bindings)
   (declare (xargs :mode :program))
  (if (symbolp pattern)
      (let ((hit (assocx pattern bindings)))
        (if hit (and (equal term (cadr hit)) bindings)
          (if (not (equal pattern term)) nil
            (cons (list pattern term) bindings))))
    (if (not (consp pattern))
        (and (not (consp term)) (equal pattern term) bindings)
      (all-unify-pattern-match-term-fn (car pattern) (cdr pattern) term bindings))))

(defun all-unify-pattern-match-clause-term (pattern clause bindings)
   (declare (xargs :mode :program))
  (if (not (consp clause)) nil
    (let ((hits (all-unify-pattern-match-term pattern (car clause) bindings)))
      (append hits (all-unify-pattern-match-clause-term pattern (cdr clause) bindings)))))

(defun all-unify-pattern-match-clause (pattern clause bindings)
  (if (not (consp clause)) nil
    (let ((hit (unify-pattern-match pattern (car clause) bindings)))
      (if hit (cons hit (all-unify-pattern-match-clause pattern (cdr clause) bindings))
        (all-unify-pattern-match-clause pattern (cdr clause) bindings)))))

(defun add-literal-symbols (symbols binding)
  (if (not (consp symbols)) binding
    (let ((binding (cons (list (car symbols) (car symbols)) binding)))
      (add-literal-symbols (cdr symbols) binding))))

(defun quote-values (binding)
  (if (not (consp binding)) nil
    (let ((entry (car binding)))
      (cons (list (car entry) `(quote ,(cadr entry)))
            (quote-values (cdr binding))))))

(defun bind-keys (keys values)
  (if (not (consp keys)) t
    (if (not (consp values)) nil
      (let ((res (bind-keys (cdr keys) (cdr values))))
        (and res (cons (list (car keys) (car values)) res))))))

(defun map-bind-keys (keys vlist-list)
  (if (not (consp vlist-list)) nil
    (let ((binding (bind-keys keys (car vlist-list))))
      (let ((res (map-bind-keys keys (cdr vlist-list))))
        (if (not binding) res (cons binding res))))))

;; (replicate-bindings (((i 'a)) ((i 'b))) ((j i)))

;; (((i 'a) (j 'a))
;;  ((i 'a) (j 'b))
;;  ((i 'b) (j 'a))
;;  ((i 'b) (j 'b)))

(defun replicate-bindings (b0 b1 alist)
  (let ((alist (instantiate-soft-alist alist b0)))
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
(let ((blist (list (list (list :x 1) (list :a 0) (list :b 1))
                   (list (list :x 2) (list :a 2) (list :b 3))
                   (list (list :x 3) (list :a 4) (list :b 5))))
      (alist (list (list :a :b))))
  (let ((alist2 (append alist (invert-soft-alist alist))))
    (map-commutes blist alist2)))

#+joe
(let ((blist (list (list (list :a 0) (list :b 1))
                   (list (list :a 2) (list :b 3))
                   (list (list :a 4) (list :b 5))))
      (alist (list (list :a :b))))
  (let ((alist2 (append alist (invert-soft-alist alist))))
    (let ((blist (append blist (map-commutes blist alist2))))
      (map-transitive blist alist))))

#+joe
(let ((blist (list (list (list :a 0) (list :b 1))
                   (list (list :a 1) (list :b 2))
                   (list (list :a 2) (list :b 3))
                   (list (list :a 2) (list :b 7))))
      (alist (list (list :a :b))))
  (let ((blist (map-replicate-bindings blist alist)))
    (map-equiv blist alist)))

(defun commute-binding (binding alist)
  (declare (xargs :measure (len alist)))
  (if (not (consp alist)) binding
    (let ((entry (car alist)))
      (let ((skey (car entry))
            (dkey (cadr entry)))
        (let ((hit (assocx skey binding)))
          (if (not hit) (hard-error :commute "Unbound variable: ~x0" (acons #\0 skey nil))
            (cons (list dkey (cadr hit))
                  (commute-binding binding (cdr alist)))))))))

(defun map-commutes (blist alist)
  (if (not (consp blist)) nil
    (cons (commute-binding (car blist) alist)
          (map-commutes (cdr blist) alist))))

(defun invert-soft-alist (alist)
  (if (not (consp alist)) nil
    (let ((entry (car alist)))
      (cons (list (cadr entry) (car entry))
            (invert-soft-alist (cdr alist))))))

(defun find-bindings (akey bvalue blist)
  (if (not (consp blist)) nil
    (let ((binding (car blist)))
      (let ((hit (assocx akey binding)))
        (if (not hit) (find-bindings akey bvalue (cdr blist))
          (if (not (equal (cadr hit) bvalue)) (find-bindings akey bvalue (cdr blist))
            (cons binding (find-bindings akey bvalue (cdr blist)))))))))

(defun update-equivalence-classes (x y classes)
  (declare (type (satisfies true-list-listp) classes))
  (if (not (consp classes)) (list (list x y))
    (let ((class (car classes)))
      (if (member-equal x class)
          (if (member-equal y class)
              classes
            (cons (cons y class) (cdr classes)))
        (if (member-equal y class)
            (cons (cons x class) (cdr classes))
          (cons class (update-equivalence-classes x y (cdr classes))))))))

(defthm true-list-listp-update-equivalence-classes
  (implies
   (true-list-listp classes)
   (true-list-listp (update-equivalence-classes x y classes))))

(defun compute-equivalence-classes (x y blist classes)
  (declare (type (satisfies true-list-listp) classes))
  (if (not (consp blist)) classes
    (let ((binding (car blist)))
      (let ((left  (assocx x binding))
            (right (assocx y binding)))
        (if (or (not left) (atom (cdr left))) (hard-error :equiv "Unbound variable: ~x0" (acons #\0 left nil))
          (if (or (not right) (atom (cdr right))) (hard-error :equiv "Unbound variable: ~x0" (acons #\0 right nil))
            (let ((classes (update-equivalence-classes (cadr left) (cadr right) classes)))
              (compute-equivalence-classes x y (cdr blist) classes))))))))

;; I wonder if it is just a matter of rewriting all of these cases?

(mutual-recursion

 (defun complete-all-transitive-bindings (bkey blist2 binding blist alist)
   (declare (xargs :mode :program))
   (if (not (consp blist2)) nil
     (let ((bx (car blist2)))
       (let ((hit (assocx bkey bx)))
         (if (not hit) (hard-error :transitive "Unbound variable: ~x0" (acons #\0 bkey nil))
           (let ((cvalue (cadr hit)))
             (let ((b2 (cons (list bkey cvalue) binding)))
               (append (all-transitive-bindings b2 blist alist)
                       (complete-all-transitive-bindings bkey (cdr blist2) binding blist alist)))))))))

 (defun all-transitive-bindings (binding blist alist)
   (declare (xargs :mode :program))
   (if (not (consp alist)) (list binding)
     (let ((entry (car alist)))
       ;;
       ;; In :binding we have:
       ;; (< akey:avalue bkey:bvalue)
       ;; in blist we are looking for:
       ;; (< akey:bvalue bkey:cvalue)
       ;; we will create a new :binding with:
       ;; (< akey:avlue bkey:cvalue)
       ;;
       ;; (< (f akey:avalue xkey:xvalue) (f bkey:bvalue ykey:yvalue))
       ;; (< (f akey:bvalue xkey:yvalue) (f bkey:cvalue ykey:zvalue))
       ;; ------------------------------------------------------------
       ;; (< (f akey:avlue  xkey:xvalue) (f bkey:cvalue ykey:zvalue))
       ;;
       (let ((akey (car entry))
             (bkey (cadr entry)))
         (let ((hit (assocx bkey binding)))
           (if (not hit) (hard-error :transitive "Unbound variable: ~x0" (acons #\0 bkey nil))
             (let ((bvalue (cadr hit)))
               ;; Each blist2 is a complete binding ..
               (let ((blist2 (find-bindings akey bvalue blist)))
                 (complete-all-transitive-bindings bkey blist2 binding blist (cdr alist))))))))))

 )

(defun next-transitive-bindings (rst blist alist)
  (declare (xargs :mode :program))
  (if (not (consp rst)) nil
    (append (all-transitive-bindings (car rst) blist alist)
            (next-transitive-bindings (cdr rst) blist alist))))

(defun transitive-binding-fixpoint (rst blist alist)
  (declare (xargs :mode :program))
  (let ((next (next-transitive-bindings rst blist alist)))
    (if (not next) blist
      (append next (transitive-binding-fixpoint next blist alist)))))

(defun map-transitive (blist alist)
   (declare (xargs :mode :program))
   (transitive-binding-fixpoint blist blist alist))

#+joe
(map-transitive (list (list (list :a 1) (list :b 2))
                      (list (list :a 2) (list :b 3)))
                (list (list :a :b)))

#+joe
(map-transitive (list (list (list :a 0) (list :b 1))
                      (list (list :a 1) (list :b 2))
                      (list (list :a 2) (list :b 3))
                      (list (list :a 2) (list :b 7)))
                (list (list :a :b)))

(defun map-equiv (blist alist)
  (declare (xargs :mode :program))
  (transitive-binding-fixpoint blist blist alist))

(defun equivalence-closure (left right vlist binding)
  (if (not (consp vlist)) (list binding)
    (let ((var (car vlist)))
      (let ((hit (assocx var binding)))
        (if (not hit) (hard-error :rewrite "Unbound variable: ~x0" (acons #\0 var nil))
          (let ((value (cadr hit)))
            (cond
             ((equal left value)
              ;; NOTE: This rewrites (only) the whole term.
              ;; We could try to be more creative ..
              (cons (cons (list var right) binding)
                    (equivalence-closure left right (cdr vlist) binding)))
             (t
              (equivalence-closure left right (cdr vlist) binding)))))))))

(defun collect-equivalent-bindings (class value x y blist res)
  (if (not (consp blist)) (compress-normalized-bindings res)
    (let ((binding (car blist)))
      (let ((hit (assocx x binding)))
        (let ((res (if (not (member-equal (cadr hit) class)) res
                     (cons (normalize-alist (list* (list x value) (list y value) binding) t)
                           res))))
          (collect-equivalent-bindings class value x y (cdr blist) res))))))

(defun all-class-pairings-with-x (x left y class binding res)
  (if (not (consp class)) res
    (let ((right (car class)))
      (let ((res (cons (list* (list x left) (list y right) binding) res)))
        (all-class-pairings-with-x x left y (cdr class) binding res)))))

(defun all-class-pairings (x lclass y class binding res)
  (if (not (consp lclass)) res
    (let ((left (car lclass)))
      (let ((res (all-class-pairings-with-x x left y class binding res)))
        (all-class-pairings x (cdr lclass) y class binding res)))))

(defun all-class-pairings-of-binding-list (x y class blist res)
  (if (not (consp blist)) res
    (let ((res (all-class-pairings x class y class (car blist) res)))
      (all-class-pairings-of-binding-list x y class (cdr blist) res))))

;; We need to collect all of the bindings associated with the
;; same equivalence class.
;;
;; We should minimize this set [modulo the equivalence] as it is
;; likely to contain duplicates.
;;
;; ((x a) (y b) (w c))
;;

(defun duplicate-binding-list-by-class (x y classes blist0 res)
  (if (not (consp classes)) res
    (let ((class (car classes)))
      (let ((blist (collect-equivalent-bindings class (car class) x y blist0 nil)))
        (let ((res (all-class-pairings-of-binding-list x y class blist res)))
          (duplicate-binding-list-by-class x y (cdr classes) blist0 res))))))

(defun equiv-fixpoint (x y blist)
  (let ((classes (compute-equivalence-classes x y blist nil)))
    (duplicate-binding-list-by-class x y classes blist nil)))

#+joe
(let ((blist `(((:x :a) (:y :b) (:z 1)) ;; (equal :a :b)
               ((:x :a) (:y :c) (:z 1)) ;; (equal :a :c)
               ((:x :b) (:y :d) (:z 2)) ;; (equal :b :d)
               ((:x :k) (:y :m) (:z 4))
               ((:x :m) (:y :n) (:z 4))
               ((:x :q) (:y :p) (:z 4))
               )))
  (equiv-fixpoint :x :y blist))

(defun rewrite-binding (left right vlist binding)
  (if (not (consp vlist)) nil
    (let ((var (car vlist)))
      (let ((hit (assocx var binding)))
        (if (or (atom hit) (atom (cdr hit))) (hard-error :rewrite "Unbound variable: ~x0" (acons #\0 var nil))
          (let ((val (cadr hit)))
            (if (equal val left)
                (revappend
                 (let ((binding (cons (list var right) binding)))
                   (cons binding
                         (rewrite-binding left right (cdr vlist) binding)))
                 (rewrite-binding left right (cdr vlist) binding))
              (rewrite-binding left right (cdr vlist) binding))))))))

#+joe
(rewrite-binding :a :b '(:x :y) '((:x :a) (:y :a)))


;; (compute-equivalence-classes :x :y blist nil))
;; )

#+joe
(map-commutes '(((:a 1) (:b 0))
                ((:a 3) (:b 2)))
              '((:a :b) (:b :a)))

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
      (let ((call-binding (instantiate-soft-alist pre binding)))
        (er-let* ((blist (unify-pattern-match-expression-call fn body post clause call-binding state)))
          (value (map-update-binding blist binding)))))
     ((:not exp)
      (er-let* ((blist (unify-pattern-match-expression exp clause binding state)))
        (value (if (not blist) (list binding) nil))))
     ((:check exp)
      (let ((exp (instantiate-term exp binding)))
        (er-let* ((ok (check exp clause state)))
          (value (if ok (list binding) nil)))))
     ((:bind . alist)
      (let ((alist (instantiate-soft-alist alist binding)))
        (value (list (update-binding alist binding)))))
     ((:literally . symbols) ;; match symbol names exactly
      (value (list (add-literal-symbols symbols binding))))
     ((:replicate exp . alist)
      (er-let* ((blist (unify-pattern-match-expression exp clause binding state)))
        (value (map-replicate-bindings blist alist))))
     ((:commutes exp . alist)
      (er-let* ((blist (unify-pattern-match-expression exp clause binding state)))
        (let ((alist (append alist (invert-soft-alist alist))))
          (let ((blist (append blist (map-commutes blist alist))))
            (value blist)))))
     ;;
     ;; We might just want to find "all" possible (equiv x y) or (< x y) expressions.
     ;;
     ;; We might also want to rewrite some other binding under equiv.  I suppose there
     ;; are a number of ways we might do that .. we are currently considering just
     ;; using the cross product.  I think that means: we only keep bindings that
     ;; "hit".
     ;;       (a=a) (a=b) (a=c) (b=a) (b=b) (b=c) (c=a) (c=b) (c=c)
     ;; (a,b) (a,b) (b,b) (c,b) (a,a) (a,b) (a,c)   .     .     .
     ;; (a,c) (a,c) (b,c) (c,c)   .     .     .   (a,a) (a,b) (a,c)
     ;;
     ;; A simple cross product seems excessive in that it might contain many duplicates.
     ;;
     ;; What you really ought to do is normalization .. just like you are doing for
     ;;
     ;; Except you need a list of things you are rewriting.
     ;;
     ;; We assume that we are working under the cross-product of (x = y) and "a"
     ;;
     ;; Specifically, when a=x, we replace it with a=y
     ;;
     ;; We want to collapse the state space such that, if A=X then replace it with A=Y
     ;;
     ;; (:rewrite (a b c) <equiv> (x y))
     ;;
     ((:rewrite (x y) . vlist)
      (let ((x (instantiate-term x binding))
            (y (instantiate-term y binding)))
        (let ((blist (rewrite-binding x y vlist binding)))
          (value blist))))
     ((:equiv exp (x y))
      (er-let* ((blist (unify-pattern-match-expression exp clause binding state)))
        (let ((blist (equiv-fixpoint x y blist)))
          (value blist))))
     ((:transitive exp . alist)
      (er-let* ((blist (unify-pattern-match-expression exp clause binding state)))
        (value (map-transitive blist alist))))
     ((:match var exp)
      (let ((var (instantiate-term var binding)))
        (unify-pattern-match-expression exp (list var) binding state)))
     ((:syntaxp exp)
      (let ((qbinding (quote-values binding)))
        (let ((exp (instantiate-term exp qbinding)))
          (er-let* ((value (syntaxp-eval exp state)))
            (value (if value (list binding) nil))))))
     ((:bind-free exp args)
      (let ((qbinding (quote-values binding)))
        (let ((exp (instantiate-term exp qbinding)))
          (er-let* ((vlist-list (syntaxp-eval exp state)))
            (if (not vlist-list) (value nil)
              (let ((blist (map-bind-keys args vlist-list)))
                (value (map-update-binding blist binding))))))))
     ((:equal . elist)
      (let ((elist (instantiate-term-list elist binding)))
        (value (and (all-equal elist) (list binding)))))
     ((:either exp)
      (value (append
              (all-unify-pattern-match-clause exp clause binding)
              (all-unify-pattern-match-clause `(not ,exp) clause binding))))
     ((:term exp)
      (let ((blist (all-unify-pattern-match-clause-term exp clause binding)))
        (let ((blist (compress-bindings blist)))
          (value blist))))
     (&
      (value (all-unify-pattern-match-clause exp clause binding)))))

 )

(defun map-formals-to-actuals (formals actuals)
  (if (not (and (consp formals) (consp actuals))) nil
    (cons (list (car formals) (car actuals))
          (map-formals-to-actuals (cdr formals) (cdr actuals)))))

(mutual-recursion

 (defun translate-expression-list (list w)
   (declare (xargs :mode :program))
   (if (not (consp list)) nil
     (cons (translate-expression (car list) w)
           (translate-expression-list (cdr list) w))))

 (defun translate-expression-soft-alist (alist w)
   (declare (xargs :mode :program))
   (if (not (consp alist)) nil
     (let ((entry (car alist)))
       (cons (list (car entry) (translate-expression (cadr entry) w))
             (translate-expression-soft-alist (cdr alist) w)))))

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
      (let ((db (table::get :pattern-hint-definition-database w)))
        (let ((defn (cdr (assoc fn db))))
          (case-match defn
            ((fn formals body retexps)
             (let ((retexps (translate-expression-list retexps w))
                   (actuals (translate-expression-list actuals w)))
               (let ((body (translate-expression body w)))
                 `(:context ,(map-formals-to-actuals formals actuals)
                            (,fn ,(translate-expression body w))
                            ,(map-formals-to-actuals retvars retexps)))))
            (&
             (let ((zed (hard-error 'translate-expression "Undefined pattern hint function ~x0" (acons #\0 fn nil))))
               (declare (ignore zed))
               `(:pass)))))))
     ((:context pre (fn body) post)
      `(:context ,(translate-expression-soft-alist pre w)
                 (,fn ,(translate-expression body w))
                 ,(translate-expression-soft-alist post w)))
     ((:not exp)
      `(:not ,(translate-expression exp w)))
     ((:commutes exp . alist)
      `(:commutes ,(translate-expression exp w) ,@alist))
     ((:check exp)
      (let ((exp (pseudo-trans exp w)))
        `(:check ,exp)))
     ((:either exp)
      (let ((exp (pseudo-trans exp w)))
        `(:either ,exp)))
     ((:syntaxp exp)
      (let ((exp (pseudo-trans exp w)))
        `(:syntaxp ,exp)))
     ((:bind-free exp vars)
      (let ((exp (pseudo-trans exp w)))
        `(:bind-free ,exp ,vars)))
     ((:bind . alist)
      `(:bind ,@(translate-expression-soft-alist alist w)))
     ((:literally . symbols)
      `(:literally ,@symbols))
     ((:replicate exp . alist)
      (let ((exp (translate-expression exp w)))
        `(:replicate ,exp ,@(translate-expression-soft-alist alist w))))
     ((:equiv exp . alist)
      (let ((exp (translate-expression exp w)))
        `(:equiv ,exp ,@alist)))
     ((:transitive exp . alist)
      (let ((exp (translate-expression exp w)))
        `(:transitive ,exp ,@alist)))
     ((:match var exp)
      `(:match ,var ,(translate-expression exp w)))
     ((:equal . elist)
      `(:equal ,@(translate-expression-list elist w)))
     ((:term exp)
      (let ((exp (pseudo-trans exp w)))
        `(:term ,exp)))
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
     ((:replicate exp . alist)
      `(:replicate ,(clausify-expression exp) ,@alist))
     ((:equiv exp . alist)
      `(:equiv ,(clausify-expression exp) ,@alist))
     ((:transitive exp . alist)
      `(:transitive ,(clausify-expression exp) ,@alist))
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

(defun self-bind (vars)
  (if (not (consp vars)) nil
    (cons (list (car vars) (car vars))
          (self-bind (cdr vars)))))

(defun instantiate-expand (expand binding w)
  (declare (xargs :mode :program))
  (case-match expand
    ((:free vars term)
     (let ((binding (update-binding (self-bind vars) binding)))
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

(defun pattern-hint-fn-instance (blist0 exp0 uses0 cases0 expansions0 restrictions0 in-theory do-not repeat slow name clause state)
  (declare (xargs :mode :program))
  (mv-let (err blist state) (unify-pattern-match-expression exp0 clause t state)
    (declare (ignore err))
    (let ((blist (normalize-bindings blist)))
      (let ((blist (minus-bindings blist blist0)))
        (if (not blist) (mv nil nil nil nil nil nil nil nil state)
          (let ((blist (compress-normalized-bindings blist)))
            (prog2$
             (cw "Firing pattern hint ~x0~%" name)
             (let ((blist (if (integerp slow) (keep-only slow blist)
                            (if slow (list (car blist)) blist))))
               (let ((blistN (if (not repeat) (append blist blist0) blist0)))
                 (let ((cases  (pseudo-trans-list cases0 (w state))))
                   (let ((uses         (instantiate-uses-with-bindings uses0 blist))
                         (cases        (instantiate-cases-with-bindings cases blist))
                         (expansions   (instantiate-expansions-with-bindings expansions0 blist (w state)))
                         (restrictions (instantiate-restrictions-with-bindings restrictions0 blist)))
                     (mv t blistN uses cases expansions restrictions in-theory do-not state))))))))))))

(defun get-kwlist-binding (key alist)
  (if (and (consp alist) (consp (cdr alist)))
      (if (equal key (car alist)) (cadr alist)
        (get-kwlist-binding key (cddr alist)))
    nil))

(defun parse-hints (hints)
  (let ((kwlist (cddr hints)))
    (mv
     (get-kwlist-binding :name kwlist)
     (cadr hints)
     (get-kwlist-binding :limit kwlist)
     (get-kwlist-binding :use kwlist)
     (get-kwlist-binding :cases kwlist)
     (get-kwlist-binding :expand kwlist)
     (get-kwlist-binding :restrict kwlist)
     (get-kwlist-binding :in-theory kwlist)
     (get-kwlist-binding :do-not kwlist)
     (get-kwlist-binding :repeat kwlist)
     (get-kwlist-binding :slow kwlist))))

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
       (let ((zed (hard-error 'pattern-hint "Unrecognized theory event ~x0" (acons #\0 hint nil))))
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
(defun pattern-hint-list-fn-rec (blist hints hit res uses cases expansions restrictions etheory dtheory do-not clause state)
  (declare (xargs :mode :program))
  (if (not (and (consp blist) (consp hints))) (mv hit (revappend res nil) uses cases expansions restrictions etheory dtheory do-not state)
    (mv-let (name0 exp0 limit0 uses0 cases0 expansions0 restrictions0 in-theory0 do-not0 repeat0 slow0) (parse-hints (car hints))
      (declare (ignore limit0))
      (let ((binding0 (car blist)))
        (cond
         ((and do-not do-not0)
          (mv-let (err value state) (error1 'pattern-hint "" "Multiple do-not hints: ~x0 ~x1" (acons #\0 do-not (acons #\1 do-not0 nil)) state)
            (declare (ignore err value))
            (mv nil nil nil nil nil nil nil nil nil state)))
         (t
          (mv-let (hit1 binding1 uses1 cases1 expansions1 restrictions1 in-theory1 do-not1 state)
            (pattern-hint-fn-instance binding0 exp0 uses0 cases0 expansions0 restrictions0 in-theory0 do-not0 repeat0 slow0 name0 clause state)
            (cond
             ((not hit1)
              (let ((res (cons binding0 res)))
                (pattern-hint-list-fn-rec (cdr blist) (cdr hints) hit res uses cases expansions restrictions etheory dtheory do-not clause state)))
             (t
              (mv-let (etheory1 dtheory1) (split-in-theory-hint in-theory1)
                (let ((res          (cons binding1 res))
                      (uses         (append uses1 uses))
                      (cases        (append cases1 cases))
                      (expansions   (append expansions1 expansions))
                      (restrictions (append restrictions1 restrictions))
                      (etheory      (append etheory1 etheory))
                      (dtheory      (append dtheory1 dtheory))
                      (do-not       do-not1))
                  (pattern-hint-list-fn-rec (cdr blist) (cdr hints) t res uses cases expansions restrictions etheory dtheory do-not clause state))))))))))))

(defun pattern-hint-list-fn (limit0 blist hints clause stable state)
  (declare (xargs :mode :program))
  (if (not stable) (value nil)
    (mv-let (hit blist uses cases expansions restrictions etheory dtheory do-not state)
      (pattern-hint-list-fn-rec blist hints nil nil nil nil nil nil nil nil nil clause state)
      (if (not hit) (value nil)
        (let ((theory       (and (or etheory dtheory) `(:in-theory (e/d ,etheory ,dtheory))))
              (dont         (and do-not `(:do-not ,do-not)))
              (uses         (and uses `(:use ,uses)))
              (cases        (and cases `(:cases ,cases)))
              (expansions   (and expansions `(:expand ,expansions)))
              (restrictions (and restrictions `(:restrict ,restrictions))))
          (let ((hint (append theory dont uses cases expansions restrictions)))
            (let ((limit (nfix (1- limit0))))
              (let ((hint (if (and (not (zp limit0)) (zp limit)) hint
                            `(:computed-hint-replacement
                              ((pattern-hint-list-fn ',limit ',blist ',hints clause stable-under-simplificationp state))
                              ,@hint))))
                (value hint)))))))))

(defun process-hints-fn (hint wrld)
  (declare (xargs :mode :program))
  (case-match hint
    ((:hints exp . kwlist)
     (let* ((exp    (translate-expression exp wrld))
            (exp    (clausify-expression exp))
            (name   (get-kwlist-binding :name kwlist))
            (name   (or name 'un-named)))
       (list* name exp kwlist)))
    (('pattern-hint exp . kwlist)
     (let* ((exp    (translate-expression exp wrld))
            (exp    (clausify-expression exp))
            (name   (get-kwlist-binding :name kwlist))
            (name   (or name 'un-named)))
       (list* name exp kwlist)))
    (& (list* 'un-named `(:all) nil))))

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
    (let ((hint (car hints)))
      (if (symbolp hint)
          (let ((db (table::get :pattern-hint-database wrld)))
            (let ((hint-list (cdr (assoc hint db))))
              (append (resolve-hint-definitions hint-list wrld)
                      (resolve-hint-definitions (cdr hints) wrld))))
        (cons hint (resolve-hint-definitions (cdr hints) wrld))))))

(defmacro pattern-hint-list (&rest hints)
  `(let ((hints '(,@hints)))
     (let ((hints (resolve-hint-definitions hints (w state))))
       (let ((hints (process-hints-list hints (w state)))
             (blist (nil-list hints)))
         (pattern-hint-list-fn 0 blist hints clause stable-under-simplificationp state)))))

(defun pattern-hint-fn (blist0 limit0 exp0 uses0 cases0 expansions0 restrictions0 in-theory do-not repeat slow name id clause stable state)
  (declare (xargs :mode :program)
           (ignorable id)
           )
  (if (not stable) (value nil)
    (let* ((exp    (translate-expression exp0 (w state)))
           (exp    (clausify-expression exp)))
      (mv-let (hit binding1 uses1 cases1 expansions1 restrictions1 in-theory1 do-not1 state)
          (pattern-hint-fn-instance blist0 exp uses0 cases0 expansions0 restrictions0 in-theory do-not repeat slow name clause state)
        (if (not hit) (value nil)
          (let ((theory       (and in-theory1 `(:in-theory ,in-theory1)))
                (dont         (and do-not1 `(:do-not ,do-not1)))
                (uses         (and uses1 `(:use ,uses1)))
                (cases        (and cases1 `(:cases ,cases1)))
                (expansions   (and expansions1 `(:expand ,expansions1)))
                (restrictions (and restrictions1 `(:restrict ,restrictions1))))
            (let ((hint (append theory dont uses cases expansions restrictions)))
              (let ((limit (nfix (1- limit0))))
                (let ((hint (if (and (not (zp limit0)) (zp limit)) hint
                              `(:computed-hint-replacement
                                ((pattern-hint-fn ',binding1 ',limit ',exp0 ',uses0 ',cases0
                                                  ',expansions0 ',restrictions0 ',in-theory ',do-not
                                                  ',repeat ',slow ',name
                                                  id clause stable-under-simplificationp state))
                                ,@hint))))
                  (value hint))))))))))

(defmacro pattern-hint (exp &key (limit '0) (use 'nil) (cases 'nil) (expand 'nil) (restrict 'nil) (in-theory 'nil)
                            (do-not 'nil) (repeat 'nil) (slow 'nil) (name 'un-named))
  (if (symbolp exp)
      `(let ((name ',exp))
         (let ((db (table::get :pattern-hint-database (w state))))
           ;; First element of list ..
           (let ((hint (car (cdr (assoc name db)))))
             (mv-let (name exp limit use0 cases0 expand0 restrict0 in-theory0 do-not0 repeat0 slow0) (parse-hints hint)
               (let ((use       (or ',use use0))
                     (cases     (or ',cases cases0))
                     (expand    (or ',expand expand0))
                     (restrict  (or ',restrict restrict0))
                     (in-theory (or ',in-theory in-theory0))
                     (do-not    (or ',do-not do-not0))
                     (repeat    (or ',repeat repeat0))
                     (slow      (or ',slow   slow0)))
                 (pattern-hint-fn nil limit exp use cases expand restrict
                                  in-theory do-not repeat slow name id clause stable-under-simplificationp state))))))
    `(pattern-hint-fn nil ',limit ',exp ',use ',cases ',expand ',restrict ',in-theory ',do-not
                      ',repeat ',slow ',name id clause stable-under-simplificationp state)))

(defmacro def::pattern-hint (name body &key (limit '0) (use 'nil) (cases 'nil) (repeat 'nil) (slow 'nil)
                                  (expand 'nil) (restrict 'nil) (in-theory 'nil) (do-not 'nil))
  (let ((kwlist `(:limit    ,limit
                  :use       ,use
                  :cases     ,cases
                  :expand    ,expand
                  :restrict  ,restrict
                  :in-theory ,in-theory
                  :do-not    ,do-not
                  :slow      ,slow
                  :repeat    ,repeat
                  :name      ,name)))
    (let ((hint `(pattern-hint ,body ,@kwlist)))
      `(table::set :pattern-hint-database (acons ',name '(,hint) (table::get :pattern-hint-database world))))))

(defmacro def::pattern-hint-list (name hints)
  `(table::set :pattern-hint-database (acons ',name ',hints (table::get :pattern-hint-database world))))

(defmacro def::pattern-function (name args body &key (returns 'nil))
  (let ((spec `(,name ,args ,body ,returns)))
    `(table::set :pattern-hint-definition-database (acons ',name ',spec (table::get :pattern-hint-definition-database world)))))

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
    :hints ((pattern-hint
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
    :hints ((pattern-hint joe))
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
    :hints ((pattern-hint-list
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
  (let ((ca (cadr ca))
        (cb (cadr cb))
        (cx (cadr cx))
        (cy (cadr cy)))
    (lte-check-fn ca cb cx cy)))

(def::pattern-function base-offset (z)
  (:match z (:first (:and (:syntaxp (quotep z))
                          (:bind (offset z) (base 0)))
                    (:if (+ offset base) (:syntaxp (quotep offset))
                         (:bind (offset 0) (base z)))))
  :returns (offset base))

(def::pattern-function lte-match ()
  (:or (< a b)
       (not (< b a)))
  :returns (a b))

;; (< w x)
;; (< x y)
;; (< w z)

(def::pattern-function lte-match-2 ()
  (:or (:bind-free (default-lte-match) (a b))
       (:and (:replicate (:call (lte-match) (a c)) (cc a) (b c))
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
             (:first (:and (:equal cc a)
                           (:equal  b c))
                     (:equal cc c))
             (:bind-free (expand-lte-match a b) (a b))
             ))
  :returns (a b))

;;
;; bind-free functions must return a list of value lists
;;
(defun expand-lte-match-default (x y)
  (declare (xargs :guard t))
  (list (list x y)))

(defun default-lte-match-default ()
  (declare (xargs :guard t))
  nil)

(encapsulate
    (
     ((expand-lte-match * *) => *)
     ((default-lte-match)    => *)
     )

  (local (defun expand-lte-match (x y)
           (expand-lte-match-default x y)))
  (local (defun default-lte-match ()
           (default-lte-match-default)))

  (defthm true-listp-expand-lte-match
    (true-listp (expand-lte-match x y)))

  (defthm true-listp-default-lte-match
    (true-listp (default-lte-match)))

  )

(defattach expand-lte-match  expand-lte-match-default)
(defattach default-lte-match default-lte-match-default)

(def::pattern-function lte-filter-sort (x y)
  (:and
   (:call (base-offset x) (cx bx))
   (:call (base-offset y) (cy by))
   (:if (:equal bx by)
        (:if (:syntaxp (<= (cadr cx) (cadr cy))) (:bind (n x) (p y))
             (:and (:syntaxp (<= (cadr cy) (cadr cx)))
                   (:bind (n y) (p x))))
        (:and
         (:call (lte-match-2) (a b))
         (:call (base-offset a) (ca ba))
         (:call (base-offset b) (cb bb))
         (:if (:equal bx ba)
              (:and (:equal by bb)
                    (:syntaxp (lte-check ca cb cx cy))
                    (:bind (n x) (p y)))
              (:and (:equal bx bb)
                    (:equal by ba)
                    (:syntaxp (lte-check ca cb cy cx))
                    (:bind (n y) (p x)))))))
  :returns (n p))

(def::pattern-function lte-filter (x y)
  ;(:or (:match x 0)
  ;     (:match y (n))
  ;     (:match y (+ -1 (n)))
  (:and
   (:call (base-offset x) (cx bx))
   (:call (base-offset y) (cy by))
   (:if (:equal bx by) (:and ;;(:syntaxp (not (cw "constant check (<= ~x0 ~x1)~%" cx cy)))
                        (:syntaxp (<= (cadr cx) (cadr cy))))
        (:and
         (:call (lte-match-2) (a b))
         ;;(:syntaxp (not (cw "consider that (<= ~x0 ~x1)~%" a b)))
         (:call (base-offset a) (ca ba))
         (:equal bx ba)
         (:call (base-offset b) (cb bb))
         (:equal by bb)
         ;;(:syntaxp (not (cw "(implies (<= ~x0 ~x1) (<= ~x2 ~x3))~%" a b x y)))
         (:syntaxp (lte-check ca cb cx cy))))))

