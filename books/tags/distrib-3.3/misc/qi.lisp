;  qi.lisp                                  Boyer & Hunt

; BDD operations.  BDD-based set operations.  Reachability.

; Legend:
;  q-  returns a BDD
;  qv- returns a list of BDDs
;

(in-package "ACL2")

(include-book "hons-help2")

(defabbrev qcar (x) (if (consp x) (car x) x))

(defabbrev qcdr (x) (if (consp x) (cdr x) x))

(defabbrev qcons (x y)
  (if (or (and (eq x t)   (eq y t))
          (and (eq x nil) (eq y nil)))
      x
    (hons x y)))

(defn q-not (x)
  (if (atom x)
      (if x nil t)
    (hons (q-not (car x))
          (q-not (cdr x)))))

(defn q-ite (x y z)
  (cond ((null x) z)
        ((atom x) y)
        (t (let ((y (if (hqual x y) t y))
                 (z (if (hqual x z) nil z)))
             (cond ((hqual y z) y)
                   ((and (eq y t) (eq z nil)) x)
                   ((and (eq y nil) (eq z t)) (q-not x))
                   (t (let ((a (q-ite (car x) (qcar y) (qcar z)))
                            (d (q-ite (cdr x) (qcdr y) (qcdr z))))
                        (qcons a d))))))))

(defn normp (x)
  (mbe :logic
       (if (atom x)
           (booleanp x)
         (and (normp (car x))
              (normp (cdr x))
              (if (atom (car x))
                  (not (equal (car x) (cdr x)))
                t)))

       :exec
       (cond ((eq x t) t)
             ((eq x nil) t)
             ((atom x) nil)
             (t (let ((a (car x))
                      (d (cdr x)))
                  (cond ((eq a t)
                         (cond ((eq d nil) t)
                               ((eq d t) nil)
                               (t (normp d))))
                        ((eq a nil)
                         (cond ((eq d nil) nil)
                               ((eq d t) t)
                               (t (normp d))))
                        (t (and (normp a) (normp d)))))))))

(defn normp-list (x)
  (if (atom x) t (and (normp (car x)) (normp-list (cdr x)))))

(defn length-<= (l n)
  (cond ((atom l) t)
        ((or (not (integerp n)) (<= n 0)) nil)
        (t (length-<= (cdr l) (1- n)))))

(defn locn-acc (v vs acc)
  (declare (xargs :guard (integerp acc)))
  (cond ((atom vs) acc)
        ((equal v (car vs)) acc)
        (t (locn-acc v (cdr vs) (1+ acc)))))

(defn locn (v vs)
  (declare (xargs :guard t
                  :verify-guards nil))
  (mbe
   :logic
   (cond ((atom vs) 0)
         ((equal v (car vs)) 0)
         (t (1+ (locn v (cdr vs)))))
   :exec
   (locn-acc v vs 0)))

(defthm locn-is-locn-acc
  (implies (natp acc)
           (equal (locn-acc v vars acc)
                  (+ acc (locn v vars)))))

(verify-guards locn)

(defn qvar-n (n)
  (declare (xargs :guard (integerp n)))
  (mbe
   :logic
   (cond ((or (not (integerp n)) (< n 0))
          nil)
         ((= n 0) (hons t nil))
         (t (let ((x (qvar-n (1- n))))
              (hons x x))))
   :exec
   (cond ((< n 0) nil)
         ((= n 0) (hons t nil))
         (t (let ((x (qvar-n (1- n))))
              (hons x x))))))

(defthm consp-qvar-n
  (implies (and (integerp n)
                (<= 0 n))
           (consp (qvar-n n))))

(defthm normp-qvar-n
  (implies (integerp n)
           (normp (qvar-n n))))

(in-theory (disable qvar-n))

(defn var-to-tree (var vars) (qvar-n (locn var vars)))

(defthm normp-var-to-tree
  (normp (var-to-tree var vars)))

(in-theory (disable var-to-tree))

(defn qnorm1-guard (x)
  (if (atom x)
      (symbolp x)
    (let ((fn (car x))
          (args (cdr x)))
      (case fn
        (if (and (consp args)
                 (consp (cdr args))
                 (consp (cddr args))
                 (null (cdddr args))
                 (qnorm1-guard (car args))
                 (qnorm1-guard (cadr args))
                 (qnorm1-guard (caddr args))))
        (quote (and (consp args)
                    (normp (car args))
                    (null (cdr args))))
        (otherwise nil)))))

(defn qnorm1 (term vars)
  (declare (xargs :measure (acl2-count term)
                  :guard (and (qnorm1-guard term)
                              (symbol-listp vars))))
  (cond ((eq term t) t)
        ((eq term nil) nil)
        ((atom term) (var-to-tree term vars))
        ((eq (car term) 'if)
         (let ((test (qnorm1 (cadr term) vars)))
           (cond ((eq test t)
                  (qnorm1 (caddr term) vars))
                 ((eq test nil)
                  (qnorm1 (cadddr term) vars))
                 (t (q-ite
                     test
                     (qnorm1 (caddr term) vars)
                     (qnorm1 (cadddr term) vars))))))
        ((eq (car term) 'quote) (cadr term))
        (t (list "Bad arg to qnorm1 ~a." term))))

(defn qnorm1-guard-list (l)
  (if (atom l) t
    (and (qnorm1-guard (car l))
         (qnorm1-guard-list (cdr l)))))

(defn qnorm1-list (l vars)
  (declare (xargs :guard (and (qnorm1-guard-list l)
                              (symbol-listp vars))))
  (if (atom l) nil
    (cons (qnorm1 (car l) vars) (qnorm1-list (cdr l) vars))))

(defn q-not-ite (x)
  (q-ite x nil t))

; There are 16 (i.e., 2^(2*2)) Bl functions of two arguments, x and y.
; Six of them we do not bother to define, namely the functions that
; return t and nil, x, y, (not x), and (not y).  Below we define the q
; versions of the other 10.

(defn q-and (x y)
  (if (atom x)
      (if (atom y)
          (and x y)
        (if x y nil))
    (if (atom y)
        (if y x nil)
      (let ((l (q-and (car x) (car y)))
            (r (q-and (cdr x) (cdr y))))
        (qcons l r)))))

(defn q-and-ite (x y)
  (q-ite x y nil))

(defn q-nand (x y)
  (q-not (q-and x y)))

(defn q-or (x y)
  (if (atom x)
      (if (atom y)
          (or x y)
        (if x t y))
    (if (atom y)
        (if y t x)
      (let ((l (q-or (car x) (car y)))
            (r (q-or (cdr x) (cdr y))))
        (qcons l r)))))

(defn q-or-ite (x y)
  (q-ite x t y))

(defn q-nor (x y)
  (q-not (q-or x y)))

(defn q-implies-ite (x y)
  ;; aka q-or-c1
  (q-ite x y t))

(defn q-or-c2-ite (x y)
  ;; aka y->x
  (q-ite y x t))

(defn q-and-c1-ite (x y)
  (q-ite x nil y))

(defn q-and-c2 (x y)
  (if (atom x)
      (if (atom y)
          (and x (not y))
        (if x (q-not y) nil))
    (if (atom y)
        (if y nil x)
      (let ((l (q-and-c2 (car x) (car y)))
            (r (q-and-c2 (cdr x) (cdr y))))
        (qcons l r)))))

(defn q-and-c2-ite (x y)
  (q-ite y nil x))

(defn q-iff-ite (x y)
  (q-ite x y (q-not y)))

(defn q-xor (x y)
  (q-ite x (q-not y) y))

(defn q-xor-ite (x y)
  (q-ite x (q-not y) y))

(defn q-nand-ite (x y)
  (q-ite x (q-not y) t))

(defn q-nor-ite (x y)
  (q-ite x nil (q-not y)))

; End of the 10 q-functions of two arguments.


(defn q-buf (x) x)

(defn q-or3   (w x y)   (q-or  w (q-or  x y)))

(defn q-and3  (w x y)   (q-and w (q-and x y)))

(defn q-or4   (w x y z) (q-or  w (q-or  x (q-or  y z))))

(defn q-and4  (w x y z) (q-and w (q-and x (q-and y z))))

(defn q-nor3  (w x y)   (q-not (q-or3  w x y)))

(defn q-nand3 (w x y)   (q-not (q-and3 w x y)))

(defn q-nor4  (w x y z) (q-not (q-or4  w x y z)))

(defn q-nand4 (w x y z) (q-not (q-and4 w x y z)))

(defn qs-equal (x y)
  (equal x y))

; Conjecture:
; (qs-subset x y) is an efficient implementation of
; (eq t (q-implies x y)).

; (defn qs-complement (x full-set)
;   (q-and-c1 x full-set))

(defn qs-subset (x y)
  (cond ((atom x)
         (if x (eq y t) t))
        ((atom y) y)
        (t (and (qs-subset (car x) (car y))
                (qs-subset (cdr x) (cdr y))))))

;; older def with guards
;; (defn var-to-tree-list (variables vars)
;;   (declare (xargs :guard (and (symbol-listp variables)
;;                               (symbol-listp vars))))
;;   (declare (xargs :guard t))
;;   (if (atom variables)
;;       nil
;;     (cons (var-to-tree (car variables) vars)
;;           (var-to-tree-list (cdr variables) vars))))

(defn var-to-tree-list (variables vars)
  (if (atom variables) nil
    (hons (var-to-tree (car variables) vars)
          (var-to-tree-list (cdr variables) vars))))


; Ev function for BDDs

;; older def with guard
;; (defn eval-bdd (x values)
;;   (declare (xargs :guard (boolean-listp values)))
;;   (if (atom x)
;;       x
;;     (if (car values)
;;         (eval-bdd (car x) (cdr values))
;;       (eval-bdd (cdr x) (cdr values)))))

(defn eval-bdd (x values)
  (if (atom x)
      x
    (if (atom values)
        (eval-bdd (cdr x) nil)
      (if (car values)
          (eval-bdd (car x) (cdr values))
        (eval-bdd (cdr x) (cdr values))))))

(defthm normp-implies-eval-bdd-blp
  (implies (normp x)
           (booleanp (eval-bdd x vals))))

; Some lemmas for proving the equality of BDDs with ACL2 functions.

;; (defthm open-eval-bdd
;;   (and (equal (eval-bdd t vals) t)
;;        (equal (eval-bdd nil vals) nil)
;;        (equal (eval-bdd (cons x y) vals)
;;               (if (car vals)
;;                   (eval-bdd x (cdr vals))
;;                 (eval-bdd y (cdr vals))))))

;; (in-theory (disable eval-bdd))

;; older def with guard
;; (defn eval-bdd-list (bdds values)
;;   (declare (xargs :guard (boolean-listp values)))
;;   (if (atom bdds)
;;       nil
;;     (cons (eval-bdd (car bdds) values)
;;           (eval-bdd-list (cdr bdds) values))))

(defn eval-bdd-list (bdds values)
  (if (atom bdds)
      nil
    (hons (eval-bdd (car bdds) values)
          (eval-bdd-list (cdr bdds) values))))

(defthm open-eval-bdd-list
  (and (equal (eval-bdd-list nil vals) nil)
       (equal (eval-bdd-list (hons x y) vals)
              (hons (eval-bdd x vals)
                    (eval-bdd-list y vals)))))

(in-theory (disable open-eval-bdd-list))

; Funny Bl fact.

(defthm blp-implies-t
  (implies (and (booleanp x) x)
           (equal (equal x t) t)))

; BDD Variable reorder.

(defn delete-hq (x l)
  (declare (xargs :guard (symbolp x)))
  (cond ((atom l) l)
        ((eq x (car l))
         (cdr l))
        (t (hons (car l) (delete-hq x (cdr l))))))

(defthm symbol-listp-delete-hq
  (implies (symbol-listp l)
           (symbol-listp (delete-hq x l))))

(defn q-restrict (x n v vars)
  ;; Needs to be memoized.  Q-RESTRICT takes a bdd X, a value N (t or
  ;; nil), a variable V, which is a member of the list of variables
  ;; VARS with respect to which X is a bdd.  Q-RESTRICT returns the
  ;; bdd corresponding to the formula that one obtains by simplifying
  ;; every internal node in X corresponding to variable V to N.  Thus,
  ;; if a BDD with variables '(A B C) has variable B restricted to
  ;; NIL, then both outgoing edges from every internal node Y at
  ;; "level" B will point to the (CDR Y).

  ;; This like forming (let ((v n)) x) and simplifying the resulting
  ;; expression.

  (declare (xargs :guard (and (symbolp v)
                              (symbol-listp vars))))
  (if (atom x)
      x
    (if (eq v (car vars))
        (if n
            (qcons (car x) (car x))
          (qcons (cdr x) (cdr x)))
      (qcons (q-restrict (car x) n v (cdr vars))
             (q-restrict (cdr x) n v (cdr vars))))))

(defn q-restrict-shrink (x n v vars)
  ;; Needs to be memoized.  q-restrict-shrink takes a bdd x, a value n
  ;; (t or nil), a variable v, which is a member of the list of
  ;; variables vars with respect to which x is a bdd.
  ;; q-restrict-shrink returns the bdd corresponding to the formula
  ;; that one obtains by substituting n for x in the formula to which
  ;; x corresponds.

  ;; Subtle point:  the var v is eliminated.  Always know which
  ;; var list you are working with!

  (declare (xargs :guard (and (symbolp v)
                              (symbol-listp vars))))
  (if (atom x)
      x
    (if (eq v (car vars))
        (if n (car x) (cdr x))
      (qcons (q-restrict-shrink (car x) n v (cdr vars))
             (q-restrict-shrink (cdr x) n v (cdr vars))))))

(defn q-reorder (x vars nvars)
  ;; Needs to be memoized.  vars and nvars should be of the same
  ;; length.  x is a bdd.  q-reorder returns the bdd whose meaning
  ;; with respect to nvars is equivalent to to the meaning of x with
  ;; respect to vars.
  (declare (xargs :guard (and (symbol-listp vars)
                              (symbol-listp nvars))
                  :measure (acl2-count nvars)))
  (if (or (atom x)
          (atom nvars)) ;; could be eliminated
      x
    (if (eq (car vars) (car nvars))
        ;; It may be possible to simplify the qcons function calls
        ;; here to hons function calls.
        (qcons (q-reorder (car x) (cdr vars) (cdr nvars))
               (q-reorder (cdr x) (cdr vars) (cdr nvars)))
      (qcons (q-reorder (q-restrict-shrink x t (car nvars) vars)
                        (delete-hq (car nvars) vars)
                        (cdr nvars))
             (q-reorder (q-restrict-shrink x nil (car nvars) vars)
                        (delete-hq (car nvars) vars)
                        (cdr nvars))))))

(defun q-restrict-alist (x bindings vars)
  ;; See q-restrict.  This like forming (let binding x) and
  ;; simplifying the resulting expression.
  ;; Should this be re-written to use Q-ITE and obviate the
  ;; need to memoize this function?  Probably not.
  (declare (xargs :guard (symbol-alistp bindings)))
  (if (atom x)
      x
    (if (atom vars)
        x
      (let ((pair (assoc (car vars) bindings)))
        (if pair
            (let ((x-below (q-restrict-alist
                            (if (cdr pair) (car x) (cdr x))
                            bindings (cdr vars))))
              (qcons x-below x-below))
          (qcons (q-restrict-alist (car x) bindings (cdr vars))
                 (q-restrict-alist (cdr x) bindings (cdr vars))))))))


(defun q-restrict-alist-list (x-lst bindings vars)
  (declare (xargs :guard (symbol-alistp bindings)))
  (if (atom x-lst)
      nil
    (cons (q-restrict-alist (car x-lst) bindings vars)
          (q-restrict-alist-list (cdr x-lst) bindings vars))))

#|| Needs guard work

(defn q-reorder-down-one (x vars var)
  ;; This function "swaps" variable var with the variable just below
  ;; it in the variable order.
  (if (atom x)
      x
    (if (atom vars)
        x
      (if (eq (car vars) var)
          ;; Perform the swap.  Finish this !!!
          x
        (hons (q-reorder-down-one (car x) (cdr vars) var)
              (q-reorder-down-one (cdr x) (cdr vars) var))))))

||#

(defn q-exists-shrink (x E-vars vars)
  ;; E-vars must be a subset of vars and its variables must appear in
  ;; the same order as they do in vars.  This version of q-exists
  ;; returns an answer that has meaning with respect to the deletion
  ;; of the members of E-vars from vars.
  (declare (xargs :guard (and (symbol-listp E-vars)
                              (symbol-listp vars))))
  (if (or (atom x)
          (atom E-vars))
      x
    (if (eq (car E-vars) (car vars))
        (q-or (q-exists-shrink (car x) (cdr E-vars) (cdr vars))
              (q-exists-shrink (cdr x) (cdr E-vars) (cdr vars)))
      (qcons (q-exists-shrink (car x) E-vars (cdr vars))
             (q-exists-shrink (cdr x) E-vars (cdr vars))))))

(defn q-exists (x E-vars vars)
  ;; E-vars must be a subset of vars and its variables must appear in
  ;; the same order as they do in vars.  This version of q-exists
  ;; returns an answer that has meaning with respect to vars.
  (declare (xargs :guard (and (symbol-listp E-vars)
                              (symbol-listp vars))))
  (if (or (atom x)
          (atom E-vars))
      x
    (if (eq (car E-vars) (car vars))
        (let ((below
               (q-or (q-exists (car x) (cdr E-vars) (cdr vars))
                     (q-exists (cdr x) (cdr E-vars) (cdr vars)))))
          (qcons below below))
      (qcons (q-exists (car x) E-vars (cdr vars))
             (q-exists (cdr x) E-vars (cdr vars))))))

(defn q-for-all-shrink (x E-vars vars)
  ;; E-vars must be a subset of vars and its variables must appear in
  ;; the same order as they do in vars.  This version of q-for-all
  ;; returns an answer that has meaning with respect to the deletion
  ;; of the members of E-vars from vars.
  (declare (xargs :guard (and (symbol-listp E-vars)
                              (symbol-listp vars))))
  (if (or (atom x)
          (atom E-vars))
      x
    (if (eq (car E-vars) (car vars))
        (q-and (q-for-all-shrink (car x) (cdr E-vars) (cdr vars))
               (q-for-all-shrink (cdr x) (cdr E-vars) (cdr vars)))
      (qcons (q-for-all-shrink (car x) E-vars (cdr vars))
             (q-for-all-shrink (cdr x) E-vars (cdr vars))))))

(defn q-for-all (x E-vars vars)
  ;; E-vars must be a subset of vars and its variables must appear in
  ;; the same order as they do in vars.  This version of q-for-all
  ;; returns an answer that has meaning with respect to vars.
  (declare (xargs :guard (and (symbol-listp E-vars)
                              (symbol-listp vars))))
  (if (or (atom x)
          (atom E-vars))
      x
    (if (eq (car E-vars) (car vars))
        (let ((below
               (q-and (q-for-all (car x) (cdr E-vars) (cdr vars))
                      (q-for-all (cdr x) (cdr E-vars) (cdr vars)))))
          (qcons below below))
      (qcons (q-for-all (car x) E-vars (cdr vars))
             (q-for-all (cdr x) E-vars (cdr vars))))))

(defn q-exists-one-var (x v vars)
  (declare (xargs :guard (and (symbolp v)
                              (symbol-listp vars))))
  (q-or (q-restrict x  t  v vars)
        (q-restrict x nil v vars)))

(defn q-for-all-one-var (x v vars)
  (declare (xargs :guard (and (symbolp v)
                              (symbol-listp vars))))
  (q-and (q-restrict x  t  v vars)
         (q-restrict x nil v vars)))

(defn q-exists-one-var-shrink (x v vars)
  (declare (xargs :guard (and (symbolp v)
                              (symbol-listp vars))))
  (q-or (q-restrict-shrink x  t  v vars)
        (q-restrict-shrink x nil v vars)))

(defn q-for-all-one-var-shrink (x v vars)
  (declare (xargs :guard (and (symbolp v)
                              (symbol-listp vars))))
  (q-and (q-restrict-shrink x  t  v vars)
         (q-restrict-shrink x nil v vars)))


;;;  Some heavy sledding...

(defn good-to-if-p (x)
  (if (atom x)
      (symbolp x)
    (let ((fn (car x))
          (args (cdr x)))
      (case fn
        (if (and (consp args)
                 (consp (cdr args))
                 (consp (cddr args))
                 (null (cdddr args))
                 (good-to-if-p (car args))
                 (good-to-if-p (cadr args))
                 (good-to-if-p (caddr args))))
        (otherwise nil)))))

(defn nmake-if (test true false)
  (declare (xargs :guard (and (good-to-if-p test)
                              (good-to-if-p true)
                              (good-to-if-p false))))
  (cond ((eq test t)
         true)
        ((eq test nil)
         false)
        ((and (consp test) (eq 'if (car test))
              (null (caddr test)) (eq t (cadddr test)))
         (nmake-if (cadr test) false true))
        (t (let* ((true (if (hqual test true) t true))
                  (true (if (and (consp true)
                                 (hqual test (cadr true)))
                            (caddr true)
                          true))
                  (false (if (hqual test false) nil false))
                  (false (if (and (consp false)
                                  (hqual test (cadr false)))
                             (cadddr false)
                           false)))
             (cond ((hqual true false) true)
                   ((and (eq true t) (eq false nil))
                    test)
                   (t (hist 'if test true false)))))))

(defn to-if-error-p (x)
  (and (consp x)
       (stringp (car x))))

(defthm good-to-if-nmake-if
  (implies (and (good-to-if-p x)
                (good-to-if-p y)
                (good-to-if-p z))
           (good-to-if-p (nmake-if x y z))))

(defthm symbolp-of-nmake-if
  (implies (and (good-to-if-p x)
                (good-to-if-p y)
                (good-to-if-p z)
                (not (consp (nmake-if x y z))))
           (symbolp (nmake-if x y z))))

(defthm consp-of-nmake-if
  (implies (and (good-to-if-p x)
                (good-to-if-p y)
                (good-to-if-p z)
                (not (symbolp (nmake-if x y z))))
           (consp (nmake-if x y z))))

(in-theory (disable nmake-if))

(defn to-if-subst (new old term)
  (declare (xargs :guard (good-to-if-p term)))
  (cond ((atom term)
         (cond ((eq term t) t)
               ((eq term nil) nil)
               ((equal term old) new)
               (t term)))
        (t (hist 'if
                 (to-if-subst new old (cadr term))
                 (to-if-subst new old (caddr term))
                 (to-if-subst new old (cadddr term))))))

(defthm good-to-if-p-to-if-subst
  (implies (and (good-to-if-p new)
                (good-to-if-p term))
           (good-to-if-p (to-if-subst new old term))))

(defthm atom-to-if-implies-symbolp-to-if-subst
  (implies (and (not (consp (to-if-subst new old term)))
                (good-to-if-p new)
                (good-to-if-p term))
           (symbolp (to-if-subst new old term))))

(defn to-if (term)
  (declare (xargs :verify-guards nil))
  (cond ((symbolp term) term)
        ((atom term) (hist "Illegal argument to to-if ~a." term))
        ;; Zero Arguments
        ((atom (cdr term))
         (cond ((not (null (cdr term)))
                (hist "Illegal argument to to-if ~a." term))
               ((member (car term) '(and & a)) t)
               ((member (car term) '(or \| v o)) nil)
               (t (hist "Illegal argument to to-if ~a." term))))
        ;; One Argument
        ((atom (cddr term))
         (cond ((not (null (cddr term)))
                (hist "Illegal argument to to-if ~a." term))
               (t (let ((arg1 (to-if (cadr term))))
                    (cond ((to-if-error-p arg1)
                           (hist "Illegal argument to to-if ~a."
                                 term))
                          ((member (car term) '(not ~ n))
                           (nmake-if arg1 nil t))
                          ((or (member (car term) '(and & a))
                               (member (car term) '(or \| v o)))
                           arg1)
                          (t (hist "Illegal arg to to-if ~a."
                                   term)))))))
        ;; Two Arguments
        ((atom (cdddr term))
         (cond ((not (null (cdddr term)))
                (hist "Illegal argument to to-if ~a." term))
               (t (let ((arg1 (to-if (cadr term)))
                        (arg2 (to-if (caddr term))))
                    (cond ((to-if-error-p arg1) arg1)
                          ((to-if-error-p arg2) arg2)
                          ((member (car term) '(and & a))
                           (nmake-if arg1 arg2 nil))
                          ((member (car term) '(or \| v o))
                           (nmake-if arg1 t arg2))
                          ((member (car term)
                                   '(equal = iff equiv <->))
                           (nmake-if arg1 arg2 (nmake-if arg2 nil t)))
                          ((member (car term) '(implies ->))
                           (nmake-if arg1 arg2 t))
                          ((member (car term) '(xor exor))
                           (nmake-if arg1 (nmake-if arg2 nil t) arg2))
                          ((eq (car term) 'nand)
                           (nmake-if arg1 (nmake-if arg2 nil t) t))
                          ((eq (car term) 'nor)
                           (nmake-if arg1 nil (nmake-if arg2 nil t)))
                          (t (hist "Illegal arg to to-if ~a."
                                   term)))))))
        ;; Let Expression
        ((and (null (cddddr term)) (eq (car term) 'let))
         (let ((var (cadr term))
               (val (caddr term))
               (body (cadddr term)))
           (cond ((or (not (symbolp var))
                      (eq var t)
                      (eq var nil))
                  (hist "Bad bound variable ~a." var))
                 (t (let ((valt (to-if val))
                          (bodyt (to-if body)))
                      (cond ((to-if-error-p valt) valt)
                            ((to-if-error-p bodyt) bodyt)
                            (t (to-if-subst valt var bodyt))))))))
        ;; IF Expression
        ((and (null (cddddr term)) (eq (car term) 'if))
         (let ((arg1 (to-if (cadr term)))
               (arg2 (to-if (caddr term)))
               (arg3 (to-if (cadddr term))))
           (cond ((to-if-error-p arg1) arg1)
                 ((to-if-error-p arg2) arg2)
                 ((to-if-error-p arg3) arg3)
                 (t (nmake-if arg1 arg2 arg3)))))
        (t (hist "Illegal argument to to-if ~a." term))))

(defthm good-to-if-p-to-if
  (implies (not (to-if-error-p (to-if term)))
           (good-to-if-p (to-if term))))

(defthm atom-to-if-implies-symbolp-to-if
  (implies (not (consp (to-if x)))
           (symbolp (to-if x))))

(verify-guards to-if)

(defn var-lessp (v1 v2 var-order)
  (declare (xargs :guard (and (symbolp v1)
                              (symbolp v2)
                              (symbol-listp var-order))))
  (let ((l1 (member-eq v1 var-order))
        (l2 (member-eq v2 var-order)))
    (if l1
        (if l2
            (and (not (eq v1 v2))
                 (member-eq v2 l1))
          t)
      (if l2
          nil
        (symbol-< v1 v2)))))

(defn nmerge (l1 l2 var-order)
  (declare (xargs :guard (and (symbol-listp l1)
                              (symbol-listp l2)
                              (symbol-listp var-order))
                  :measure (+ (acl2-count l1)
                              (acl2-count l2))))
  (cond ((atom l1) l2)
        ((atom l2) l1)
        ((eq (car l1) (car l2))
         (hons (car l1) (nmerge (cdr l1) (cdr l2) var-order)))
        ((var-lessp (car l1) (car l2) var-order)
         (hons (car l1)
               (nmerge (cdr l1) l2 var-order)))
        (t (hons (car l2)
                 (nmerge l1 (cdr l2) var-order)))))

(defthm symbol-listp-nmerge
  (implies (and (symbol-listp l1)
                (symbol-listp l2)
                (symbol-listp var-order))
           (symbol-listp (nmerge l1 l2 var-order))))

(defn vars-help (term var-order)
  (declare (xargs :guard (and (good-to-if-p term)
                              (symbol-listp var-order))
                  :verify-guards nil))
  (cond ((atom term)
         (cond ((or (eq term t) (eq term nil)) nil)
               (t (hist term))))
        (t (nmerge (vars-help (cadr term) var-order)
                   (nmerge (vars-help (caddr term) var-order)
                           (vars-help (cadddr term) var-order)
                           var-order)
                   var-order))))

(defthm symbol-listp-vars-help
  (implies (and (good-to-if-p term)
                (symbol-listp var-order))
           (symbol-listp (vars-help term var-order))))

(verify-guards vars-help)

; VARS was defined to allow the use of CONS for intermediate partially
; sorted lists of symbols, and here we finally then make the list
; unique.

(defn vars (term var-order)
  (declare (xargs :guard (and (good-to-if-p term)
                              (symbol-listp var-order))))
  (hopy-list-r (vars-help term var-order)))

(defthm symbol-listp-vars
  (implies (and (good-to-if-p term)
                (symbol-listp var-order))
           (symbol-listp (vars term var-order))))

(defthm good-to-if-p-implies-qnorm1-guard
  (implies (good-to-if-p term)
           (qnorm1-guard term)))

(defn qnorm (term)
  (let ((term (to-if term)))
    (cond ((to-if-error-p term) term)
          (t (qnorm1 term (vars term nil))))))

(defn qnorm-list (l vars)
  (declare (xargs :guard (symbol-listp vars)))
  (cond ((atom l) nil)
        (t (let* ((term (to-if (car l)))
                  (term (if (to-if-error-p term)
                            term
                          (qnorm1 term vars))))
           (hons term
                 (qnorm-list (cdr l) vars))))))

(defn qtaut (term)
  (let ((x (to-if term)))
    (cond ((to-if-error-p x) x)
          (t (let ((vars (vars x nil)))
               (eq 't
                   (qnorm1 x vars)))))))

(defn qsublis (alist term)
  (declare (xargs :guard (and (good-to-if-p term)
                              (eqlable-alistp alist))))
  (cond ((atom term)
         (let ((ans (assoc term alist)))
           (if ans (cdr ans) term)))
        (t (hist 'if
                 (qsublis alist (cadr term))
                 (qsublis alist (caddr term))
                 (qsublis alist (cadddr term))))))

(defn t-nil-tree (x)
  (cond ((atom x) (or (eq x t) (eq x nil)))
        (t (and (t-nil-tree (car x))
                (t-nil-tree (cdr x))))))

(defn q-to-if (term vars)
  (declare (xargs :guard (and (t-nil-tree term)
                              (symbol-listp vars))))
  (if (atom term) term
    (let ((l (q-to-if (car term) (cdr vars)))
          (r (q-to-if (cdr term) (cdr vars))))
      (nmake-if (car vars) l r))))

(defthm good-to-if-p-is-q-to-if
  (implies (and (t-nil-tree term)
                (symbol-listp vars))
           (good-to-if-p (q-to-if term vars))))

(defn re-order (term oldvars newvars)
  (declare (xargs :guard (and (t-nil-tree term)
                              (symbol-listp oldvars)
                              (symbol-listp newvars))))
  (qnorm1 (q-to-if term oldvars) newvars))

(defn common-tautologies ()
  '((iff a a)
    (implies (and a b) a)
    (implies a (or a b))
    (iff (implies a (implies b c))
         (implies (and a b) c))
    (iff (implies a b) (or (not a) b))
    (iff (iff a b) (and (implies a b) (implies b a)))
    (iff (iff a b) (or (and a b) (and (not a) (not b))))
    (iff (implies a b) (implies (not b) (not a)))
    (iff (not a) (implies a nil))
    (iff (and a t) a)
    (iff (and a nil) nil)
    (iff (not t) nil)
    (iff (not nil) t)
    (iff (or a t) t)
    (iff (or a nil) a)
    (iff (iff a t) a)
    (iff (iff a nil) (not a))
    (iff (and a b) (and b a))
    (iff (or a b) (or b a))
    (iff (or a a) a)
    (iff (not (not a)) a)
    (iff (and a a) a)
    (iff (iff a a) t)
    (iff (xor a a) nil)
    (iff (iff a b) (iff b a))
    (iff (iff a (iff b c)) (iff (iff a b) c))
    (implies (implies (not c) c) c)
    (iff (or a (or b c)) (or (or a b) c))
    (iff (and a (and b c)) (and (and a b) c))
    (iff (and a (or b c)) (or (and a b) (and a c)))
    (iff (or a (and b c)) (and (or a b) (or a c)))
    (iff (not (and a b)) (or (not a) (not b)))
    (iff (not (or a b)) (and (not a) (not b)))
    (iff (xor a b) (not (iff a b)))
    (iff (nor a b) (not (or a b)))
    (iff (nand a b) (not (and a b)))
    (iff (or a (iff b c)) (iff (or a b) (or a c)))
    (iff (and a (xor b c)) (xor (and a b) (and a c)))
    (iff (xor a (xor b c)) (xor (xor a b) c))
    (iff (if a b c) (and (implies a b) (implies (not a) c)))
    (iff (if t b c) b)
    (iff (if nil b c) c)
    (iff (if a b nil) (and a b))
    (iff (if a t b) (or a b))
    (iff (if a b b) b)
    (iff (if a a nil) a)
    (iff (if c b a) (if a (if b t (if c nil t)) (if b c nil)))
    (iff (if b2 a b1) (if a (if b1 t b2) (if b1 (if b2 nil t) nil)))
    (iff (if b1 a b2) (if a (if b1 t b2) (if b1 nil b2)))
    (iff (xor
          k
          (xor
           j
           (xor
            i
            (xor
             h
             (xor g (xor e (xor d (xor c (xor b a)))))))))
         (xor a (xor b (xor
                        c
                        (xor
                         d
                         (xor
                          e
                          (xor g (xor h (xor i (xor j k))))))))))))

(defn common-non-tautologies ()
  '(a
    (not a)
    (implies a b)
    (implies (or a b) (and a b))
    (iff (implies a b) (implies b a))
    (iff (implies a (implies b c)) (implies (implies a b) c))
    (iff (iff a (or b c)) (or (iff a b) (iff a c)))
    (iff (xor a (and b c)) (and (xor a b) (xor a c)))))

(defn check-q-true (l)
  (if (atom l)
      t
    (let ((term (to-if (car l))))
      (if (to-if-error-p term)
          nil
        (and (eq t (qnorm1 term (vars term nil)))
             (check-q-true (cdr l)))))))

(defn check-q-not-true (l)
  (if (atom l)
      t
    (let ((term (to-if (car l))))
      (if (to-if-error-p term)
          nil
        (and (not (eq t (qnorm1 term (vars term nil))))
             (check-q-not-true (cdr l)))))))

(in-theory (disable (:executable-counterpart common-tautologies)
                    (:executable-counterpart common-non-tautologies)))

(in-theory (disable common-tautologies common-non-tautologies))

(defn check-q ()
  (and (check-q-true (common-tautologies))
       (check-q-not-true (common-non-tautologies))))

; As a way to i

(defn set-bdd (bdd loc v)
  (cond
   ((atom loc) v)
   ((car loc) (qcons (set-bdd (qcar bdd) (cdr loc) v) (qcdr bdd)))
   (t (qcons (qcar bdd) (set-bdd (qcdr bdd) (cdr loc) v)))))

(defn set-bdd-list (bdds loc vs)
  (if (or (atom vs) (atom bdds))
      nil
    (hons (set-bdd      (car bdds) loc (car vs))
          (set-bdd-list (cdr bdds) loc (cdr vs)))))

(defn set-bdd-pair-list (bdd-pairs loc vs)
  (if (or (atom vs)
          (atom bdd-pairs)
          (atom (car vs))
          (atom (car bdd-pairs)))
      nil
    (hons (hons (set-bdd (caar bdd-pairs) loc (caar vs))
                (set-bdd (cdar bdd-pairs) loc (cdar vs)))
          (set-bdd-pair-list (cdr bdd-pairs) loc (cdr vs)))))

(defconst *2t* t)

(defconst *2f* nil)

(defconst *4x* (hons t t))

(defconst *4u* (hons nil nil))

(defconst *4t* (hons t nil))

(defconst *4f* (hons nil t))

(defn to (x)
  (cond ((or (null x) (eq x 'f))         *4f*)
        ((eq x t)                        *4t*)
        ((or (eq x 'floating) (eq x 'u)) *4u*)
        (t                               *4x*)))

(defn to-list (l)
  (if (atom l) nil
    (cons (to (car l)) (to-list (cdr l)))))

(defn b-fix-eval-bdd (x values)
  (if (eval-bdd x values) t nil))

(defn qv-ite (c a b)
  (if (or (atom a) (atom b))
      nil
    (cons (q-ite c (car a) (car b))
          (qv-ite c (cdr a) (cdr b)))))

(defthm true-listp-qv-ite-if
  (true-listp (qv-ite c a b)))


;!!!  I want to everywhere change Q-IFF-LIST to Q-PAND-IFF-LIST.

(defn q-iff-list (x y)
  (if (or (atom x) (atom y))
      t
    (q-and-ite (q-iff-ite (car x) (car y))
               (q-iff-list (cdr x) (cdr y)))))
