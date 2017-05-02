; Copyright (C) 2016, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; The Doppelgangers for user-defs.lisp

; We define the doppelgangers for the functions in user-defs.lisp.  See
; "Limited Second-Order Functionality in a First-Order Setting" for a
; description of what we're doing.

(in-package "MODAPP")

(include-book "../weights-and-measures")

(defconst *apply$-boot-fns-badge-alist*
  `((BADGE . ,*generic-tame-badge-1*)
    (TAMEP . ,*generic-tame-badge-1*)
    (TAMEP-FUNCTIONP . ,*generic-tame-badge-1*)
    (SUITABLY-TAMEP-LISTP . ,*generic-tame-badge-2*)
    (APPLY$ . ,*apply$-badge*)
    (EV$ . ,*ev$-badge*)))

(table badge-table
       :badge-userfn-structure
       nil)

(table badge-table
       :apply$-userfn!-supporters
       '(TAMEP-FUNCTIONP TAMEP SUITABLY-TAMEP-LISTP
         UNTAME-APPLY$ UNTAME-EV$)
       :put)

(defstub untame-apply$ (fn args) t)
(defstub untame-ev$ (x a) t)

(defun badge-userfn! (fn)
  (declare (xargs :guard t))
  (case fn
    (SQUARE
     (make apply$-badge
           :authorization-flg t
           :arity 1
           :ilks t))
    (NATS
     (make apply$-badge
           :authorization-flg t
           :arity 1
           :ilks t))
    (SUMLIST
     (make apply$-badge
           :authorization-flg t
           :arity 2
           :ilks '(nil :fn)))
    (FOLDR
     (make apply$-badge
           :authorization-flg t
           :arity 3
           :ilks '(nil :fn nil)))
    (PROW
     (make apply$-badge
           :authorization-flg t
           :arity 2
           :ilks '(nil :fn)))
    (PROW*
     (make apply$-badge
           :authorization-flg t
           :arity 2
           :ilks '(nil :fn)))
    (COLLECT-A
     (make apply$-badge
           :authorization-flg t
           :arity 2
           :ilks '(nil :fn)))
    (SUM-OF-PRODUCTS
     (make apply$-badge
           :authorization-flg t
           :arity 1
           :ilks T))
    (otherwise nil)))

(defun badge! (fn)
  (declare (xargs :guard t))
  (cond
   ((apply$-primp fn) (badge-prim fn))
   ((eq fn 'BADGE) *generic-tame-badge-1*)
   ((eq fn 'TAMEP) *generic-tame-badge-1*)
   ((eq fn 'TAMEP-FUNCTIONP) *generic-tame-badge-1*)
   ((eq fn 'SUITABLY-TAMEP-LISTP) *generic-tame-badge-3*)
   ((eq fn 'APPLY$) *apply$-badge*)
   ((eq fn 'EV$) *ev$-badge*)
   (t (badge-userfn! fn))))

(defthm badge!-type
  (or (null (badge! fn))
      (apply$-badgep (badge! fn)))
  :hints (("Goal" :in-theory (disable badge-prim)))
  :rule-classes
  ((:forward-chaining
    :corollary (implies (badge! fn)
                        (apply$-badgep (badge! fn))))))

(in-theory (disable badge!))

(defabbrev tamep-lambdap! (fn)
  (and (eq (car fn) 'LAMBDA)
       (consp (cdr fn))
       (symbol-listp (lambda-formals fn))
       (consp (cddr fn))
       (tamep! (lambda-body fn))
       (null (cdddr fn))))

(mutual-recursion
 (defun tamep! (x)
   (declare (xargs :measure (acl2-count x)
                   :guard t
                   :verify-guards nil
                   ))
   (cond ((atom x) (symbolp x))
         ((eq (car x) 'quote)
          (and (consp (cdr x))
               (null (cddr x))))
         ((symbolp (car x))
          (let ((bdg (badge! (car x))))
            (cond
             ((null bdg) nil)
             ((eq (access apply$-badge bdg :ilks) t)
              (suitably-tamep-listp! (access apply$-badge bdg :arity)
                                    nil
                                    (cdr x)))
             (t (suitably-tamep-listp! (access apply$-badge bdg :arity)
                                      (access apply$-badge bdg :ilks)
                                      (cdr x))))))
         ((consp (car x))
          (let ((fn (car x)))
            (and (tamep-lambdap! fn)
                 (suitably-tamep-listp! (length (cadr fn))
                                       nil
                                       (cdr x)))))
         (t nil)))

 (defun tamep-functionp! (fn)
   (declare (xargs :measure (acl2-count fn)
                   :guard t))
   (if (symbolp fn)
       (let ((bdg (badge! fn)))
         (and bdg (eq (access apply$-badge bdg :ilks) t)))
       (and (consp fn)
            (tamep-lambdap! fn))))

 (defun suitably-tamep-listp! (n flags args)
   (declare (xargs :measure (acl2-count args)
                   :guard (and (natp n)
                               (true-listp flags))))
   (cond
    ((zp n) (null args))
    ((atom args) nil)
    (t (and 
        (let ((arg (car args)))
          (case (car flags)
            (:FN
             (and (consp arg)
                  (eq (car arg) 'QUOTE)
                  (consp (cdr arg))
                  (null (cddr arg))
                  (tamep-functionp! (cadr arg))))
            (:EXPR
             (and (consp arg)
                  (eq (car arg) 'QUOTE)
                  (consp (cdr arg))
                  (null (cddr arg))
                  (tamep! (cadr arg))))
            (otherwise
             (tamep! arg))))
        (suitably-tamep-listp! (- n 1) (cdr flags) (cdr args))))))
 )

(in-theory (disable (:executable-counterpart tamep!)
                    (:executable-counterpart tamep-functionp!)
                    (:executable-counterpart suitably-tamep-listp!)))



(local (include-book "user-defs")) ; no_port
(weights-and-measures)

; G1 Doppelgangers -- these fns don't have doppelgangers, we just copy the
; user's defuns exactly:

(defun square (x) (* x x))

(defun nats (n)
  (if (zp n)
      nil
      (cons n (nats (- n 1)))))

; G2 Doppelgangers

(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(defun fn/expr-args (fn args)
; Sum-of-products omitted because it's a G2 fn with no :FN/:EXPR args.
  (case fn
    (SUMLIST
     (list (cadr args)))
    (FOLDR
     (list (cadr args)))
    (PROW
     (list (cadr args)))
    (PROW*
     (list (cadr args)))
    (COLLECT-A
     (list (cadr args)))
    (APPLY$
     (list (car args)))
    (EV$
     (list (car args)))
    (otherwise nil)))

(defun max-weight (lst)
  (if (endp lst)
      0
      (max (weight (car lst))
           (max-weight (cdr lst)))))

(defun apply$!-measure (fn args)
  (llist 0
         (max (weight fn)
              (if (fn/expr-args fn args)
                  (+ 1 (max-weight (fn/expr-args fn args)))
                  0))
         (chronological-position apply$)
         0
         1))

(defun ev$!-measure (x a)
  (declare (ignore a))
  (llist 0 (weight x) (chronological-position ev$) 0 1))

(defun ev$!-list-measure (x a)
  (declare (ignore a))
  (llist 0 (weight x)  (chronological-position ev$-list) 0 1))

(defun sumlist!-measure (lst fn)
  (llist (tameness-bit sumlist)
         (max-internal-weight sumlist)
         (chronological-position sumlist)
         (original-measure sumlist)
         1))

(defun foldr!-measure (lst fn init)
  (declare (ignore init))
  (llist (tameness-bit foldr)
         (max-internal-weight foldr)
         (chronological-position foldr)
         (original-measure foldr)
         1))

(defun prow!-measure (lst fn)
  (llist (tameness-bit prow)
         (max-internal-weight prow)
         (chronological-position prow)
         (original-measure prow)
         1))

(defun prow*!-measure (lst fn)
  (llist (tameness-bit prow*)
         (max-internal-weight prow*)
         (chronological-position prow*)
         (original-measure prow*)
         1))

(defun collect-a!-measure (lst fn)
  (llist (tameness-bit collect-a)
         (max-internal-weight collect-a)
         (chronological-position collect-a)
         (original-measure collect-a)
         1))

(defun sum-of-products!-measure (lst)
  (declare (ignore lst))
  (llist (tameness-bit sum-of-products)
         (max-internal-weight sum-of-products)
         (chronological-position sum-of-products)
         (original-measure sum-of-products)
         1))

(defun apply$-userfn1!-measure (fn args)
  (llist 0
         (max (weight fn)
              (if (fn/expr-args fn args)
                  (+ 1 (max-weight (fn/expr-args fn args)))
                  0))
         (chronological-position apply$-userfn)
         0
         0))

(local (in-theory (disable hons-assoc-equal)))

(mutual-recursion
 (defun APPLY$! (fn args)
   (declare (xargs :measure (apply$!-measure fn args)
                   :well-founded-relation l<
                   ))
   (cond
    ((consp fn)
     (EV$!
      (lambda-body fn)
      (pairlis$ (lambda-formals fn) args)))
    ((apply$-primp fn)
     (apply$-prim fn args))
    ((eq fn 'BADGE)
     (badge! (car args)))
    ((eq fn 'TAMEP)
     (tamep! (car args)))
    ((eq fn 'TAMEP-FUNCTIONP)
     (tamep-functionp! (car args)))
    ((eq fn 'SUITABLY-TAMEP-LISTP)
     (suitably-tamep-listp! (car args) (cadr args) (caddr args)))
    ((eq fn 'APPLY$)
     (if (tamep-functionp! (car args))
         (APPLY$! (car args) (cadr args))
         (untame-apply$ fn args)))
    ((eq fn 'EV$)
     (if (tamep! (car args))
         (ev$! (car args) (cadr args))
         (untame-apply$ fn args)))
    (t (apply$-userfn1! fn args))))

 (defun EV$! (x a)
   (declare (xargs :measure (ev$!-measure x a)
                   :well-founded-relation l<))
   (cond
    ((not (tamep! x))
     (untame-ev$ x a))
    ((variablep x)
     (cdr (assoc-equal x a)))
    ((fquotep x)
     (cadr x))
    ((eq (car x) 'if)
     (if (ev$! (cadr x) a)
         (ev$! (caddr x) a)
         (ev$! (cadddr x) a)))
    ((eq (car x) 'APPLY$)
     (apply$! 'APPLY$
              (list (cadr (cadr x)) (EV$! (caddr x) a))))
    ((eq (car x) 'EV$)
     (apply$! 'EV$ (list (cadr (cadr x)) (EV$! (caddr x) a))))
    ((eq (car x) 'SUMLIST)
     (apply$! 'SUMLIST
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'FOLDR)
     (apply$! 'FOLDR
              (list (ev$! (cadr x) a)
                    (cadr (caddr x))
                    (ev$! (cadddr x) a))))
    ((eq (car x) 'PROW)
     (apply$! 'PROW
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'PROW*)
     (apply$! 'PROW*
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'COLLECT-A)
     (apply$! 'COLLECT-A
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
; sum-of-products omitted because it has no :FN/:EXPR formals.
    (t
     (APPLY$! (car x)
              (EV$!-LIST (cdr x) a)))))

 (defun EV$!-LIST (x a)
   (declare (xargs :measure (ev$!-list-measure x a)
                   :well-founded-relation l<))
   (cond
    ((atom x) nil)
    (t (cons (EV$! (car x) a)
             (EV$!-LIST (cdr x) a)))))

 (defun SUMLIST! (lst fn)
   (declare (xargs :measure (sumlist!-measure lst fn)
                   :well-founded-relation l<))
   (cond
    ((endp lst) 0)
    (t (+ (APPLY$! fn (list (car lst)))
          (SUMLIST! (cdr lst) fn)))))

 (defun FOLDR! (lst fn init)
   (declare (xargs :measure (foldr!-measure lst fn init)
                   :well-founded-relation l<))
   (cond
    ((endp lst) init)
    (t (apply$! fn
                (list (car lst)
                      (foldr! (cdr lst) fn init))))))

 (defun PROW! (lst fn)
   (declare (xargs :measure (prow!-measure lst fn)
                   :well-founded-relation l<))
   (cond ((or (endp lst) (endp (cdr lst)))
          nil)
         (t (cons (apply$! fn (list (car lst) (cadr lst)))
                  (prow! (cdr lst) fn)))))
 (defun PROW*! (lst fn)
   (declare (xargs :measure (prow*!-measure lst fn)
                   :well-founded-relation l<))
   (cond ((or (endp lst)
              (endp (cdr lst)))
          (apply$! fn (list lst lst)))
         ((o< (len (prow! lst fn)) (len lst))
          (prow*! (prow! lst fn) fn))
         (t nil)))

 (defun COLLECT-A! (lst fn)
   (declare (xargs :measure (collect-a!-measure lst fn)
                   :well-founded-relation l<))
   (cond
    ((endp lst) nil)
    (t (cons (APPLY$! fn (list
                          (sumlist! (nats (car lst))
                                    '(lambda (i)
                                       (foldr (nats i)
                                              '(lambda (j k)
                                                 (binary-* (square j) k))
                                              '1)))))
             (COLLECT-A! (cdr lst) fn)))))

 (defun sum-of-products! (lst)
   (declare (xargs :measure (sum-of-products!-measure lst)
                   :well-founded-relation l<))
   (sumlist! lst
             '(LAMBDA (X)
                      (FOLDR X
                             '(LAMBDA (I A)
                                      (BINARY-* I A))
                             '1))))

 (defun apply$-userfn1! (fn args)
   (declare (xargs :measure (apply$-userfn1!-measure fn args)
                   :well-founded-relation l<))
   (case fn
     (SQUARE (square (car args)))
     (NATS (nats (car args)))
     (SUMLIST
      (if (tamep-functionp! (cadr args))
          (SUMLIST! (car args) (cadr args))
          (untame-apply$ fn args)))
     (FOLDR
      (if (tamep-functionp! (cadr args))
          (FOLDR! (car args) (cadr args) (caddr args))
          (untame-apply$ fn args)))
     (PROW
      (if (tamep-functionp! (cadr args))
          (PROW! (car args) (cadr args))
          (untame-apply$ fn args)))
     (PROW*
      (if (tamep-functionp! (cadr args))
          (PROW*! (car args) (cadr args))
          (untame-apply$ fn args)))
     (COLLECT-A
      (if (tamep-functionp! (cadr args))
          (collect-a! (car args) (cadr args))
          (untame-apply$ fn args)))
     (SUM-OF-PRODUCTS (sum-of-products! (car args)))
     (otherwise (untame-apply$ fn args))))

 )

(defthm len-prow!
  (implies (not (endp x))
           (< (len (prow! x fn)) (len x)))
  :hints (("Subgoal *1/2" :expand (prow! x fn)))
  :rule-classes :linear)

(defun apply$-lambda! (fn args)
  (declare (xargs :guard (and (consp fn) (true-listp args))
                  :guard-hints (("Goal" :do-not-induct t))
                  ))
  (ec-call
   (EV$! (ec-call (car (ec-call (cdr (cdr fn))))) ; = (lambda-body fn)
         (ec-call
          (pairlis$ (ec-call (car (cdr fn))) ; = (lambda-formals fn)
                    args)))))

(defun apply$-userfn! (fn args)
  (declare (xargs :guard t))
  (ec-call (apply$-userfn1! fn args)))





