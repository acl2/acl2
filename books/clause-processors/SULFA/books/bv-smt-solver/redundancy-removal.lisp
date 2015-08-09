
;; This file defines our own version of sat-add-expr that
;; remove redundancies and uninterpreted function calls.
;; I realize that this isn't really the best thing to do, considering
;; that the SAT system doesn't guarantee sat-add-expr's internals
;; won't change, but I didn't want to make a version of SAT that
;; understood the meaning of bv-eq-raw (needed to get rid of the
;; uninterpreted function) and I didn't want to rethink the tool
;; interface to make this possible without messing with internals...

(in-package "ACL2")

;; --------------------------------------------------------
;; I need a hash table for fast redundancy removal
;; --------------------------------------------------------

(encapsulate
 ()
 (defttag acl2::SMT)

 (defun eriks-ht-reset ()
   nil)

 (defun eriks-ht-lookup (key table)
   (assoc-equal key table))

 (defun eriks-ht-set (key val table)
   (cons (cons key val) table))

 (progn!
  (set-raw-mode t)
  (defparameter eriks-hash-table (make-hash-table :test #'equal))

  (defun eriks-ht-lookup (key table)
    (declare (ignore table))
    (multiple-value-bind
     (val foundp)
     (gethash key eriks-hash-table)
     (if foundp (cons key val) nil)))

  (defun eriks-ht-set (key val table)
    (declare (ignore table))
    (progn
      (setf (gethash key eriks-hash-table) val)
      'eriks-fake-alist))

  (defun eriks-ht-reset ()
    (progn
      (clrhash eriks-hash-table)
      'eriks-fake-alist))
  (set-raw-mode nil)))

;; --------------------------------------------------------

(include-book "../sat/sat" :ttags (sat))
;;(include-book "../clause-processors/sym-str")

(defund bv-eq-raw (n x y)
  (declare (xargs :guard (and (natp n)
                              (true-listp x)
                              (true-listp y))))
  (cond
   ((zp n)
    t)
   ((iff (car x) (car y))
    (bv-eq-raw (1- n) (cdr x) (cdr y)))
   (t
    nil)))

(set-state-ok t)
(program)

(defmacro sat-plus-stobj ()
  `(defstobj $sat-plus

     (fn-call-to-ivar-alist :type t :initially nil)

     (extra-fun-world :type t :initially nil)
     ))

(sat-plus-stobj)

(defun zero-sat-plus-stobj ($sat-plus)
  (declare (xargs :stobjs $sat-plus))
  (let* (($sat-plus (update-fn-call-to-ivar-alist (eriks-ht-reset) $sat-plus))
         ($sat-plus (update-extra-fun-world nil $sat-plus)))
    $sat-plus))

(defun construct-sat-plus-stobj ($sat-plus)
  (declare (xargs :stobjs $sat-plus))
  $sat-plus)

(defun create-uninterpreted-function-entry (var call)
  (cons var call))

(defun uce-args (uc-entry)
  (cddr uc-entry))

(defun uce-return-var (uc-entry)
  (car uc-entry))

(defun sig-arg-rv-types (sig) sig)

(defun sig-type-bv-size (type)
  (cond
   ((equal type 'bool)
    0)
   ((and (consp type) (equal (car type) 'bitvec))
    (cadr type))
   (t
    (er hard 'sig-type-bv-size "Unrecognized type: ~x0~%" type))))

(defun get-ivar-if-present (call $sat-plus)
  (declare (xargs :stobjs $sat-plus))
  (cdr (eriks-ht-lookup call (fn-call-to-ivar-alist $sat-plus))))

(defun add-new-fun-call (ivar call $sat-plus)
  (declare (xargs :stobjs $sat-plus))
  (let* ((alist (fn-call-to-ivar-alist $sat-plus))
         (alist (eriks-ht-set call ivar alist))
         ($sat-plus (update-fn-call-to-ivar-alist alist $sat-plus)))
    $sat-plus))

(defun lookup-extra-fun-sig (fn $sat-plus)
  (declare (xargs :stobjs $sat-plus))
  (let ((extra-fun-world (extra-fun-world $sat-plus)))
    (getprop fn 'acl2::sig nil 'extra-fun-world extra-fun-world)))

(defun add-extra-fn-list (extra-fn-list $sat-plus)
  (declare (xargs :stobjs $sat-plus))
  (cond
   ((endp extra-fn-list)
    $sat-plus)
   (t
    (let* ((fn (car (car extra-fn-list)))
           (sig (cdr (car extra-fn-list)))
           (extra-fun-world (extra-fun-world $sat-plus))
           (extra-fun-world (putprop fn 'acl2::sig sig extra-fun-world))
           ($sat-plus (update-extra-fun-world extra-fun-world $sat-plus)))
      (add-extra-fn-list (cdr extra-fn-list) $sat-plus)))))

(defun extra-funp (fn $sat-plus)
  (declare (xargs :stobjs $sat-plus))
  (lookup-extra-fun-sig fn $sat-plus))

(defun update-uce-list-pair (new-uce const-argsp uce-list-pair)
  (cond
   (const-argsp
    (cons (cons new-uce (car uce-list-pair))
          (cdr uce-list-pair)))
   (t
    (cons (car uce-list-pair)
          (cons new-uce (cdr uce-list-pair))))))

(defun const-uce-list (uce-list-pair) (car uce-list-pair))
(defun non-const-uce-list (uce-list-pair) (cdr uce-list-pair))

(defun lookup-extra-fun-call-list (fn const-argsp $sat-plus)
  (declare (xargs :stobjs $sat-plus))
  (let* ((extra-fun-world (extra-fun-world $sat-plus))
         (uce-list-pair (getprop fn 'acl2::uce-list-pair nil 'extra-fun-world extra-fun-world)))
    (cond
     (const-argsp
      (non-const-uce-list uce-list-pair))
     (t
      (revappend (non-const-uce-list uce-list-pair)
                 (const-uce-list uce-list-pair))))))

(defun add-new-extra-fun-call (var call const-argsp $sat-plus)
  (declare (xargs :stobjs $sat-plus))
  (let* ((fn (car call))
         (new-uce (create-uninterpreted-function-entry var call))
         (extra-fun-world (extra-fun-world $sat-plus))
         (uce-list-pair (getprop fn 'acl2::uce-list-pair nil 'extra-fun-world
                                 extra-fun-world))
         (uce-list-pair (update-uce-list-pair new-uce const-argsp uce-list-pair))
         (extra-fun-world (putprop fn 'acl2::uce-list-pair uce-list-pair
                                   extra-fun-world))
         ($sat-plus (update-extra-fun-world extra-fun-world $sat-plus)))
    $sat-plus))

(defun sp-constp (x)
  (quotep x))

(defun sp-const-val (x)
  (cond
   ((quotep x)
    (unquote x))
   (t
    x)))

(defun gen-eq-todo-expr (type arg1 arg2)
  (cond
   ((equal arg1 arg2)
    '(quote t))

   ((and (sp-constp arg1) (sp-constp arg2))
    (cond
     ((equal type 'bool)
      `(quote ,(iff (sp-const-val arg1) (sp-const-val arg2))))
     ((equal type 'nat)
      `(quote ,(equal (nfix (sp-const-val arg1)) (nfix (sp-const-val arg2)))))
     ((and (consp type) (equal (car type) 'bitvec))
      `(quote ,(bv-eq-raw (sig-type-bv-size type) (unquote arg1) (unquote arg2))))
     (t
      (er hard 'gen-eq-todo-expr "Not supported\n"))))

   ((term-order arg1 arg2)
    (cond
     ((equal type 'bool)
      `(iff (sat::i-expression ,arg1) (sat::i-expression ,arg2)))
     ((and (consp type) (equal (car type) 'bitvec))
      `(bv-eq-raw (quote ,(sig-type-bv-size type))
                  (sat::i-expression ,arg1)
                  (sat::i-expression ,arg2)))
     (t
      (er hard 'gen-eq-todo-expr "Not supported\n"))))

   (t
    (cond
     ((equal type 'bool)
      `(quote (iff ,arg2 ,arg1)))
     ((and (consp type) (equal (car type) 'bitvec))
      `(bv-eq-raw (quote ,(sig-type-bv-size type))
                  (sat::i-expression ,arg2)
                  (sat::i-expression ,arg1)))
     (t
      (er hard 'gen-eq-todo-expr "Not supported\n"))))))

(defun args-bv-eq-todo-expr (arg-rv-types args1 args2 acc-body)
  (cond
   ((endp args1)
    acc-body)
   (t
    (let ((bv-eq-expr (gen-eq-todo-expr (car arg-rv-types)
                                        (car args1)
                                        (car args2))))
      (cond
       ((not (quotep bv-eq-expr))
        (cond
         ((not (quotep acc-body))
          (args-bv-eq-todo-expr (cdr arg-rv-types)
                                (cdr args1)
                                (cdr args2)
                                `(if ,bv-eq-expr ,acc-body (quote nil))))
         ((unquote acc-body)
          (args-bv-eq-todo-expr (cdr arg-rv-types)
                                (cdr args1)
                                (cdr args2)
                                bv-eq-expr))
         (t
          ;; It's correct to return '(quote nil), but I don't think
          ;; this case can occur naturally.  Why call this function, if you
          ;; already know it's going to return '(quote nil)?
          (er hard 'args-bv-eq-todo-expr
              "'nil was input as the acc-body for args-bv-eq-todo-expr.  I didn't ~
               think this could happen~%"))))
       ((unquote bv-eq-expr)
        (args-bv-eq-todo-expr (cdr arg-rv-types)
                              (cdr args1)
                              (cdr args2)
                              acc-body))
       (t
        `(quote nil)))))))

(defun extra-fun-todo-expr (arg-rv-types args call-list acc-body)
  (cond
   ((endp call-list)
    acc-body)
   (t
    (let* ((uc-entry (car call-list))
           (uce-args (uce-args uc-entry))
           (uce-rv (uce-return-var uc-entry))
           (bv-eq-expr (args-bv-eq-todo-expr arg-rv-types args uce-args '(quote t))))
      (cond
       ((not (quotep bv-eq-expr))
        (extra-fun-todo-expr arg-rv-types args (cdr call-list)
                              `(if ,bv-eq-expr (sat::i-expression ,uce-rv) ,acc-body)))
       ((unquote bv-eq-expr)
        (extra-fun-todo-expr arg-rv-types args (cdr call-list)
                              uce-rv))
       (t
        (extra-fun-todo-expr arg-rv-types args (cdr call-list)
                              acc-body)))))))

(defun constant-listp (x)
  (cond
   ((endp x)
    t)
   ((quotep (car x))
    (constant-listp (cdr x)))
   (t
    nil)))

(defun create-todo-args-list (iargs-list acc)
  (cond
   ((endp iargs-list)
    (revappend acc nil))
   (t
    (create-todo-args-list
     (cdr iargs-list)
     (cons `(sat::i-expression ,(car iargs-list))
           acc)))))

;; Expr is either <sym> or (<sym> <iexpr> ... <iexpr>).
(defun lookup-ivar-from-fn-call (expr $sat $sat-plus)
  (declare (xargs :stobjs ($sat $sat-plus)))
  (let* ((ivar (get-ivar-if-present expr $sat-plus)))
    (cond
     (ivar
      (mv ivar $sat $sat-plus))

     ((atom expr)
      (mv-let
       (ivar $sat)
       (sat::new-top-i-var $sat)
       (let* (($sat-plus (add-new-fun-call ivar expr $sat-plus)))
         (mv ivar $sat $sat-plus))))

     ((not (extra-funp (car expr) $sat-plus))
      (let ((t-args (create-todo-args-list (cdr expr) nil)))
        (mv-let
         (ivar $sat)
         (sat::new-i-variable (cons (car expr) t-args) sat::*empty-at-entry* $sat)
         (let* (($sat-plus (add-new-fun-call ivar expr $sat-plus)))
           (mv ivar $sat $sat-plus)))))

     (t ;; extra-fun
      (mv-let
       (ivar $sat)
       (sat::new-top-i-var $sat)
       (let* ((const-argsp (constant-listp (cdr expr)))
              (call-list (lookup-extra-fun-call-list (car expr) const-argsp $sat-plus))
              (sig (lookup-extra-fun-sig (car expr) $sat-plus)))
         (cond
          ((endp call-list)
           (let* (($sat-plus (add-new-fun-call ivar expr $sat-plus))
                  ($sat-plus (add-new-extra-fun-call ivar expr const-argsp $sat-plus)))
             (mv ivar $sat $sat-plus)))
          (t
           (let ((t-expr (extra-fun-todo-expr (sig-arg-rv-types sig)
                                              (cdr expr)
                                              call-list
                                              `(sat::i-expression ,ivar))))
             (mv-let
              (ivar $sat)
              (sat::new-i-variable t-expr sat::*empty-at-entry* $sat)
              (let* (($sat-plus (add-new-fun-call ivar expr $sat-plus))
                     ($sat-plus (add-new-extra-fun-call ivar expr const-argsp $sat-plus)))
                (mv ivar $sat $sat-plus))))))))))))

(mutual-recursion
(defun redundancy-removal-list (expr-list alist acc $sat $sat-plus)
  (declare (xargs :stobjs ($sat $sat-plus)))
  (cond
   ((endp expr-list)
    (mv (revappend acc nil) $sat $sat-plus))
   (t
    (mv-let
     (expr $sat $sat-plus)
     (redundancy-removal (car expr-list) alist $sat $sat-plus)
     (redundancy-removal-list (cdr expr-list) alist
                              (cons expr acc)
                              $sat $sat-plus)))))

(defun redundancy-removal (expr alist $sat $sat-plus)
  (declare (xargs :stobjs ($sat $sat-plus)))
  (cond
   ((atom expr)
    (let ((entry (assoc-equal expr alist)))
      (cond
       (entry
        (mv (cdr entry) $sat $sat-plus))
       (t
         (lookup-ivar-from-fn-call expr $sat $sat-plus)))))
   ((quotep expr)
    (mv expr $sat $sat-plus))
   (t
    (mv-let
     (i-expr-list $sat $sat-plus)
     (redundancy-removal-list (cdr expr) alist nil $sat $sat-plus)
     (cond
      ((consp (car expr))
       (let* ((formals (cadr (car expr)))
              (body (caddr (car expr)))
              (alist (pairlis$ formals i-expr-list)))
         (redundancy-removal body alist $sat $sat-plus)))
      (t
       (lookup-ivar-from-fn-call (cons (car expr) i-expr-list)
                                 $sat $sat-plus)))))))
)


(defun smt-sat-add-expr (expr $sat $sat-plus state)
  (declare (xargs :stobjs ($sat $sat-plus)))
  ;;(prog2$
  ;; (cw ".")
  (mv-let
   (i-expr $sat $sat-plus)
   (redundancy-removal expr nil $sat $sat-plus)
   (mv-let
    ($sat state)
    (sat::add-expr-ivar-alist nil `(sat::i-expression ,i-expr) nil $sat state)
    (mv $sat $sat-plus state))))
;;)

(defun smt-sat-solve ($sat state)
  (declare (xargs :stobjs ($sat)))
  (let* (($sat (sat::update-problem-stack-depth 2 $sat)))
    (sat-solve $sat state)))

#|
(defun smt-sat-add-expr (expr $sat $sat-plus state)
  (declare (xargs :stobjs ($sat $sat-plus)))
  (let* (($sat (sat::update-problem-stack-depth 2 $sat))
         ($sat (sat::update-need-more-traversals t $sat)))
    (mv-let
     (i-expr $sat $sat-plus)
     (redundancy-removal expr nil $sat $sat-plus)
     (mv-let
      (f-expr $sat)
      (sat::i-expr-to-f-expr i-expr $sat)
      (mv-let
       ($sat state)
       (sat::add-cnf-clause `(,f-expr) $sat state)
       (mv $sat $sat-plus state))))))
|# ;|

