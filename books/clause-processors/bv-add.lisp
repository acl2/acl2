(in-package "ACL2")

(include-book "textbook/chap11/perm-append" :dir :system)

;; --------------------------------------------------------------

;; bv-add definition and some theorems about it

(include-book "arithmetic-3/floor-mod/floor-mod" :dir :system)

(defund bv-add (x y)
  (mod (+ (nfix x) (nfix y)) 32))

(defun bv-add-lex-< (x y)
  (lexorder x y))

(defthm bv-commute
  (implies (syntaxp (not (bv-add-lex-< x y)))
           (equal (bv-add x y)
                  (bv-add y x)))
  :hints (("Goal" :in-theory (enable bv-add))))

(defthm bv-commute-2
  (equal (bv-add x (bv-add y z))
         (bv-add y (bv-add x z)))
  :hints (("Goal" :in-theory (enable bv-add)))
  :rule-classes nil)

(defun make-bv-add (sym-list)
  (cond
   ((atom sym-list)
    nil)
   ((atom (cdr sym-list))
    (car sym-list))
   (t
    `(bv-add ,(car sym-list)
             ,(make-bv-add (cdr sym-list))))))

(defevaluator evl evl-list
  ((if a b c) (bv-add x y)))

(defthm not-consp-cddr-perm
  (implies
   (and (perm x y)
        (not (consp (cddr x))))
   (not (consp (cddr y))))
  :rule-classes nil)

(defthm perm-cdr
  (implies
   (and (perm x y)
        (not (consp (cdr x))))
   (not (consp (cdr y))))
  :rule-classes nil)

(defthm del-implies-bv-add-equality-2-0
  (IMPLIES (AND (CONSP X)
                (CONSP (CDR X))
                (IN A (CDR X))
                (NOT (EQUAL A (CAR X)))
                (NOT (CONSP (DEL A (CDR X)))))
           (EQUAL (BV-ADD (EVL (CAR X) ENV)
                          (EVL (MAKE-BV-ADD (CDR X)) ENV))
                  (BV-ADD (EVL A ENV)
                          (EVL (CAR X) ENV))))
  :hints (("Goal" :expand (in a (cdr x)))))

(defthm del-implies-bv-add-equality-2
  (implies (and (in a x)
                (consp x)
                (consp (cdr x)))
           (equal (evl (make-bv-add x) env)
                  (bv-add (evl a env) (evl (make-bv-add (del a x)) env))))
  :hints (("Subgoal *1/4.2'" :use ((:instance bv-commute-2 (x (evl a env))
                                                (y (evl (car x) env))
                                                (z (evl (make-bv-add (del a
                                                                          (cdr
                                                                           x)))
                                                        env)))))
          ("Subgoal *1/4.1" :in-theory (disable make-bv-add evl-constraint-1)))
  :rule-classes nil)

(defthm perm-implies-bv-add-equality
  (implies
   (perm sym-list perm-list)
   (equal (evl (make-bv-add sym-list) env)
          (evl (make-bv-add perm-list) env)))
  :hints (("Goal" :induct (perm sym-list perm-list))
          ("Subgoal *1/2"
           :use ((:instance del-implies-bv-add-equality-2
                            (a (car sym-list))
                            (x perm-list)
                            (env env))
                 (:instance perm-cdr
                            (x sym-list)
                            (y perm-list))))))

;; --------------------------------------------------------------

;; Definition and proof of Clause Processor

;; For now, lexorder will do.
(defun bv-add-lex-< (x y)
  (lexorder x y))

(defun split-list (x)
  (cond ((atom x) (mv nil nil))
	((atom (cdr x)) (mv x nil))
	(t (mv-let (a b)
		   (split-list (cddr x))
		   (mv (cons (car x) a) (cons (cadr x) b))))))

(defun merge2 (x y)
  (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
  (cond ((atom x) y)
	((atom y) x)
	((bv-add-lex-< (car x) (car y))
	 (cons (car x) (merge2 (cdr x) y)))
	(t (cons (car y) (merge2 x (cdr y))))))

(defthm split-list-smaller
  (implies (and (consp x) (consp (cdr x)))
           (and (< (acl2-count (car (split-list x)))
                   (acl2-count x))
                ;; Originally we used (cadr ..) instead of (mv-nth 1 ..) below,
                ;; but the mv-nth didn't open up to cadr in the termination
                ;; proof of mergesort, so we are going with mv-nth below.
                (< (acl2-count (mv-nth 1 (split-list x)))
                   (acl2-count x)))))

(defun mergesort (x)
  (cond ((atom x) nil)
	((atom (cdr x)) x)
	(t (mv-let (a b)
		   (split-list x)
		   (merge2 (mergesort a) (mergesort b))))))

(defthm perm-append
  (perm (append x y) (append y x)))

(defthm perm-append-del
  (implies (and (consp y)
                (in (car y) x))
           (perm (append (del (car y) x) y)
                 (append x (cdr y)))))

(defthm merge2-is-append
  (perm (merge2 x y)
        (append x y))
  :hints (("Goal" :induct (merge2 x y))))

(defthm perm-append-cons-2
  (perm (append x (cons a y))
        (cons a (append x y))))

(defthm perm-append-split-list
  (perm (append (car (split-list lst)) (mv-nth 1 (split-list lst)))
        lst))

(defthm perm-mergesort
  (perm (mergesort lst) lst))

(defun simplify-bv-adds-in-flg-num (flg)
  (cond
   ((equal 'expr-list flg)
    0)
   ((equal 'expr flg)
    1)
   (t ;;(equal 'bv-add flg)
    0)))

(defun simplify-bv-adds-in (flg x)
  (declare (xargs :measure
                  (list* (cons 1 (1+ (acl2-count x)))
                         (simplify-bv-adds-in-flg-num flg))))
  (cond
   ((equal 'expr-list flg)
    (cond
     ((atom x)
      nil)
     (t
      (cons (simplify-bv-adds-in 'expr (car x))
            (simplify-bv-adds-in 'expr-list (cdr x))))))

   ((equal 'expr flg)
    (cond
     ((atom x)
      x)
     ((quotep x)
      x)
     ((equal (car x) 'bv-add)
      (let* ((add-lst (simplify-bv-adds-in 'bv-add x))
             (add-lst (mergesort add-lst)))
        (make-bv-add add-lst)))

     (t
      (cons (car x)
            (simplify-bv-adds-in 'expr-list (cdr x))))))

   (t ;;(equal 'bv-add flg)
    ;; x=(bv-add a0 a1)
    (cond
     ((or (atom x) (not (equal (car x) 'bv-add)))
      ;; This case makes no sense but I added
      ;; it to make the termination proof easy.
      nil)

     (t
      (let ((a0 (cadr x))
            (a1 (caddr x)))
        (cond
         ((and (consp a1)
               (equal 'bv-add (car a1)))
          (cons (simplify-bv-adds-in 'expr a0)
                (simplify-bv-adds-in 'bv-add a1)))
         (t
          (list (simplify-bv-adds-in 'expr a0)
                (simplify-bv-adds-in 'expr a1))))))))))

(defun bv-add-sort-cp (clause)
  (list (simplify-bv-adds-in 'expr-list clause)))

(in-theory (disable mergesort perm))

(defthm bv-add-merge-sort-ok
  (implies
   (and (consp sym-lst)
        (consp (cdr sym-lst)))
   (equal (evl (make-bv-add (mergesort sym-lst)) env)
          (evl (make-bv-add sym-lst) env)))
  :hints (("Goal" :use ((:instance perm-implies-bv-add-equality
                                   (sym-list sym-lst)
                                   (perm-list (mergesort sym-lst))
                                   (env env))))))

(defthm lemma0
  (implies (and (consp x1)
                (equal fn (car x1))
                (not (equal fn 'quote))
                (equal (evl-list args0 env) (evl-list (cdr x1) env)))
           (equal (equal (evl (cons fn args0) env) (evl x1 env))
                  t))
  :hints (("Goal" :in-theory (enable evl-constraint-0))))

(defthm correctness-of-bv-adds-in
  (and (implies
        (equal flg 'expr)
        (equal (evl (simplify-bv-adds-in flg x) env)
               (evl x env)))

       (implies
        (equal flg 'expr-list)
        (equal (evl-list (simplify-bv-adds-in flg x) env)
               (evl-list x env)))

       (implies
        (and (not (equal flg 'expr))
             (not (equal flg 'expr-list))
             (consp x)
             (equal (car x) 'bv-add))
        (equal (evl (make-bv-add (simplify-bv-adds-in flg x)) env)
               (evl x env))))
  :hints (;;("Goal" :in-theory (enable evl-constraint-0)))
          ("Subgoal *1/6" :use ((:instance evl-constraint-0
                                           (x x) (a env)))))
  :rule-classes nil)

(defthm correctness-of-bv-adds-in-expr
  (equal (evl (simplify-bv-adds-in 'expr x) env)
         (evl x env))
  :hints (("Goal" :use ((:instance correctness-of-bv-adds-in
                                   (x x) (env env) (flg 'expr)))))
  :rule-classes nil)

(defthm correctness-of-bv-add-sort-cp
  (implies (and (pseudo-term-listp clause)
                (alistp env)
                (evl (conjoin-clauses (bv-add-sort-cp clause)) env))
           (evl (disjoin clause) env))
  :hints (("Goal" :induct (disjoin clause))
          ("Subgoal *1/3" :use ((:instance correctness-of-bv-adds-in-expr
                                           (x (car clause))
                                           (env env))))
          ("Subgoal *1/2" :use ((:instance correctness-of-bv-adds-in-expr
                                           (x (car clause))
                                           (env env)))))
  :rule-classes :clause-processor)

(in-theory (disable bv-commute))
