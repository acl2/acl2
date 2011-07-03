

(in-package "ACL2")

(include-book "base")
(include-book "centaur/misc/equal-sets" :dir :system)
(include-book "tools/mv-nth" :dir :system)
(include-book "misc/gentle" :dir :system)
(include-book "misc/hons-help" :dir :system)
(local (include-book "eval-restrict"))

(defn aig-print (x)
  (declare (xargs :verify-guards nil))
  (aig-cases
   x
   :true t
   :false nil
   :var x
   :inv `(not ,(aig-print (car x)))
   :and (let* ((a (aig-print (car x)))
               (d (aig-print (cdr x))))
          `(and ,@(if (and (consp a) (eq (car a) 'and))
                      (cdr a)
                    (list a))
                ,@(if (and (consp d) (eq (car d) 'and))
                      (cdr d)
                    (list d))))))

;; (local
;;  (defthm true-listp-append
;;    (implies (true-listp b)
;;             (true-listp (append a b)))))
(local
 (defthm true-listp-cdr-aig-print
   (implies (and (consp (aig-print x))
                 (eq (car (aig-print x)) 'and))
            (true-listp (cdr (aig-print x))))))

(verify-guards aig-print)

(memoize 'aig-print :condition '(consp x))



;; Forms an AIG from an ACL2-like term.
(mutual-recursion
 (defun expr-to-aig (expr)
   (declare (Xargs :guard t
                   :measure (+ 1 (* 2 (acl2-count expr)))))
   (if (atom expr)
       expr
     (let ((fn (car expr))
           (args (cdr expr)))
       (cond
        ((and (eq fn 'not) (= (len args) 1))
         (aig-not (expr-to-aig (car args))))
        ((eq fn 'and) (expr-to-aig-args 'and t args))
        ((eq fn 'or)  (expr-to-aig-args 'or nil args))
        ((eq fn 'nand) (aig-not (expr-to-aig-args 'and t args)))
        ((eq fn 'nor)  (aig-not (expr-to-aig-args 'or nil args)))
        ((and (eq fn 'iff) (= (len args) 2))
         (aig-iff (expr-to-aig (car args))
                  (expr-to-aig (cadr args))))
        ((and (eq fn 'xor) (= (len args) 2))
         (aig-xor (expr-to-aig (car args))
                  (expr-to-aig (cadr args))))
        ((and (eq fn 'implies) (= (len args) 2))
         (aig-or (aig-not (expr-to-aig (car args)))
                 (expr-to-aig (cadr args))))
        ((and (eq fn 'if) (= (len args) 3))
         (aig-ite (expr-to-aig (car args))
                  (expr-to-aig (cadr args))
                  (expr-to-aig (caddr args))))
        (t (prog2$ (er hard? 'expr-to-aig "Malformed: ~x0~%" expr)
                   nil))))))
 (defun expr-to-aig-args (op final exprs)
   (declare (xargs :guard t
                   :measure (* 2 (acl2-count exprs))))
   (if (atom exprs)
       final
     (let ((first (expr-to-aig (car exprs)))
           (rest (expr-to-aig-args op final (cdr exprs))))
       (case op
         (and (aig-and first rest))
         (or (aig-or first rest)))))))

(defun faig-vars-pat (pat aigs)
  (if pat
      (if (atom pat)
          (list :signal pat
                (aig-vars (car aigs))
                (aig-vars (cdr aigs)))
        (cons (faig-vars-pat (car pat) (car aigs))
              (faig-vars-pat (cdr pat) (cdr aigs))))
    nil))


;; Extracts necessary variable assignments from an AIG by breaking down its
;; top-level AND structure to the negations/variables.  Any such leaf it
;; reaches which is a variable or negation implies an assignment.
(defun aig-extract-assigns (x)
  (declare (xargs :guard t
                  :verify-guards nil))
  (aig-cases
   x
   :true (mv nil nil)
   :false (mv nil nil)
   :var (mv (list x) nil)
   :inv (if (and (atom (car x))
                 (not (booleanp (car x))))
            (mv nil (list (car x)))
          (mv nil nil))
   :and (mv-let (trues1 falses1)
          (aig-extract-assigns (car x))
          (mv-let (trues2 falses2)
            (aig-extract-assigns (cdr x))
            (mv (hons-alphorder-merge trues1 trues2)
                (hons-alphorder-merge falses1 falses2))))))

(defthm atom-listp-aig-extract-assigns
  (mv-let (trues falses)
    (aig-extract-assigns x)
    (and (atom-listp trues)
         (atom-listp falses))))

(verify-guards aig-extract-assigns)

(memoize 'aig-extract-assigns
         :condition '(and (consp x) (cdr x))
         :forget t)

(defthm aig-extract-assigns-member-impl
  (mv-let (trues falses)
    (aig-extract-assigns x)
    (and (implies (and (member-equal v trues)
                       (aig-eval x env))
                  (aig-eval v env))
         (implies (and (member-equal v falses)
                       (aig-eval x env))
                  (not (aig-eval v env)))))
  :rule-classes nil)


(defthm var-eval-extend-env
  (equal (aig-eval x (cons (cons v (aig-eval v env)) env))
         (aig-eval x env))
  :hints(("Goal" :in-theory (enable aig-env-lookup))))

(defthm aig-extract-assigns-extend-alist
  (mv-let (trues falses)
    (aig-extract-assigns x)
    (and (implies (and (member-equal v trues)
                       (aig-eval x env))
                  (equal (aig-eval y (cons (cons v t) env))
                         (aig-eval y env)))
         (implies (and (member-equal v falses)
                       (aig-eval x env))
                  (equal (aig-eval y (cons (cons v nil) env))
                         (aig-eval y env)))))
  :hints (("goal" :do-not-induct t
           :use (aig-extract-assigns-member-impl
                 (:instance var-eval-extend-env
                            (x y)))
           :in-theory (disable var-eval-extend-env))))

(defun assign-var-list (vars val)
  (declare (xargs :guard t))
  (if (atom vars)
      nil
    (cons (cons (car vars) val)
          (assign-var-list (cdr vars) val))))

(local
 (defthm aig-extract-assigns-assign-var-list1
   (mv-let (trues falses)
     (aig-extract-assigns x)
     (implies (aig-eval x env)
              (and (implies
                    (subsetp-equal vars trues)
                    (aig-eval x (append (assign-var-list vars t)
                                        env)))
                   (implies
                    (subsetp-equal vars falses)
                    (aig-eval x (append (assign-var-list vars nil)
                                        env))))))
   :hints ((and stable-under-simplificationp
                '(:induct (len vars) :in-theory (enable subsetp-equal))))
   :otf-flg t))

(defthm aig-extract-assigns-assign-var-list
  (mv-let (trues falses)
    (aig-extract-assigns x)
    (implies (aig-eval x env)
             (and (implies
                   (subsetp-equal vars trues)
                   (equal (aig-eval y (append (assign-var-list vars t)
                                              env))
                          (aig-eval y env)))
                  (implies
                   (subsetp-equal vars falses)
                   (equal (aig-eval y (append (assign-var-list vars nil)
                                              env))
                          (aig-eval y env))))))
  :hints ((and stable-under-simplificationp
               (not (cdr (car id))) ;; not under induction
               '(:induct (len vars) :in-theory (enable subsetp-equal)
                         :do-not-induct t)))
  :otf-flg t)

(defthm aig-extract-assigns-var-list-rw
  (mv-let (trues falses)
    (aig-extract-assigns x)
    (implies (aig-eval x env)
             (and (equal (aig-eval y (append (assign-var-list trues t)
                                             env))
                         (aig-eval y env))
                  (equal (aig-eval y (append (assign-var-list falses nil)
                                             env))
                         (aig-eval y env))))))


(defthm alistp-assign-var-list
  (alistp (assign-var-list vars val)))

(defthm aig-eval-alist-assign-var-list
  (equal (aig-eval-alist (assign-var-list vars val) env)
         (assign-var-list vars (aig-eval val env))))

(in-theory (disable assign-var-list))

(defun aig-extract-assigns-alist (x)
  (declare (xargs :guard t))
  (mv-let (trues falses)
    (aig-extract-assigns x)
    (make-fal (assign-var-list trues t)
              (make-fal (assign-var-list falses nil)
                        nil))))

(defthm make-fal-is-append
  (implies (alistp x)
           (equal (make-fal x y) (append x y))))



(defthm alistp-aig-extract-assigns-alist
  (alistp (aig-extract-assigns-alist x)))

(defthm aig-eval-alist-append
  (equal (aig-eval-alist (append a b) env)
         (append (aig-eval-alist a env)
                 (aig-eval-alist b env))))

(defthm aig-eval-alist-aig-extract-assigns-alist
  (equal (aig-eval-alist (aig-extract-assigns-alist x) env)
         (aig-extract-assigns-alist x)))


(defthm aig-extract-assigns-restrict
;;   (implies (aig-eval x env)
;;            (aig-eval (aig-restrict x (aig-extract-assigns-alist x)) env))
  (implies (aig-eval x env)
           (equal (aig-eval y (append (aig-extract-assigns-alist x) env))
                  (aig-eval y env)))
  :hints (("goal" :do-not-induct t)))



(defun aig-extract-iterated-assigns-alist (x clk)
  (declare (Xargs :measure (nfix clk)
                   :guard (natp clk)))
  (let* ((al (aig-extract-assigns-alist x))
         (newx (aig-restrict x al)))
    (prog2$
     (clear-memoize-table 'aig-restrict)
     (if (or (hons-equal newx x) (zp clk))
         al
       (let* ((more (aig-extract-iterated-assigns-alist newx (1- clk))))
         (make-fal (flush-hons-get-hash-table-link al) more))))))

(in-theory (disable aig-extract-assigns-alist))





(defthm alistp-aig-extract-iterated-assigns
  (alistp (aig-extract-iterated-assigns-alist x clk)))

(defthm aig-eval-alist-extract-iterated-assigns
  (equal (aig-eval-alist (aig-extract-iterated-assigns-alist x clk) env)
         (aig-extract-iterated-assigns-alist x clk)))

(local
 (defun aig-extract-iterated-assigns-restrict-ind (x y clk)
   (declare (Xargs :measure (nfix clk)))
   (let* ((al (aig-extract-assigns-alist x))
          (newx (aig-restrict x al)))
     (if (or (hons-equal newx x) (zp clk))
         (list al y)
       (list (aig-extract-iterated-assigns-restrict-ind newx y (1- clk))
             (aig-extract-iterated-assigns-restrict-ind newx x (1- clk)))))))

(defthm aig-extract-iterated-assigns-restrict
  ;;   (implies (aig-eval x env)
  ;;            (aig-eval (aig-restrict x (aig-extract-iterated-assigns-alist
  ;;                                       x clk))
  ;;                      env))
  (implies (aig-eval x env)
           (equal (aig-eval y (append (aig-extract-iterated-assigns-alist x clk)
                                      env))
                  (aig-eval y env)))
  :hints (("goal" :induct (aig-extract-iterated-assigns-restrict-ind x y clk))))

(defthm aig-extract-iterated-assigns-special-case
  (implies (aig-eval x nil)
           (equal (aig-eval y (aig-extract-iterated-assigns-alist x clk))
                  (aig-eval y nil)))
  :hints (("goal" :use ((:instance aig-extract-iterated-assigns-restrict
                                   (env nil))))))


(memoize 'aig-extract-iterated-assigns-alist
         :inline nil)
