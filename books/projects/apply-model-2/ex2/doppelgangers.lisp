; Copyright (C) 2019, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; The Doppelgangers for user-book.lisp

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

(defun badge-userfn! (fn)
  (declare (xargs :guard t))
  (case fn
    (SQUARE
     (make apply$-badge
           :arity 1
           :out-arity 1
           :ilks t))
    (CUBE
     (make apply$-badge
           :arity 1
           :out-arity 1
           :ilks t))
    (MY-APPEND1
     (make apply$-badge
           :arity 2
           :out-arity 1
           :ilks t))
    (MY-REV
     (make apply$-badge
           :arity 1
           :out-arity 1
           :ilks t))
    (NATS
     (make apply$-badge
           :arity 1
           :out-arity 1
           :ilks t))

    (EXPT-2-AND-EXPT-3
     (make apply$-badge
           :arity 1
           :out-arity 2
           :ilks t))
    (EXPT-5
     (make apply$-badge
           :arity 1
           :out-arity 1
           :ilks t))
    (OK-FNP
     (make apply$-badge
           :arity 1
           :out-arity 1
           :ilks t))
    (COUNT-ATOMS
     (make apply$-badge
           :arity 1
           :out-arity 1
           :ilks t))
; G2:
    (COLLECT
     (make apply$-badge
           :arity 2
           :out-arity 1
           :ilks '(nil :fn)))
    (SUMLIST
     (make apply$-badge
           :arity 2
           :out-arity 1
           :ilks '(nil :fn)))
    (SUMLIST-WITH-PARAMS
     (make apply$-badge
           :arity 3
           :out-arity 1
           :ilks '(nil :fn nil)))
    (FILTER
     (make apply$-badge
           :arity 2
           :out-arity 1
           :ilks '(nil :fn)))
    (ALL
     (make apply$-badge
           :arity 2
           :out-arity 1
           :ilks '(nil :fn)))
    (XISTS
     (make apply$-badge
           :arity 2
           :out-arity 1
           :ilks '(nil :fn)))
    (MAXLIST
     (make apply$-badge
           :arity 2
           :out-arity 1
           :ilks '(nil :fn)))
    (COLLECT-ON
     (make apply$-badge
           :arity 2
           :out-arity 1
           :ilks '(nil :fn)))
    (COLLECT-TIPS
     (make apply$-badge
           :arity 2
           :out-arity 1
           :ilks '(nil :fn)))
    (APPLY$2
     (make apply$-badge
           :arity 3
           :out-arity 1
           :ilks '(:fn nil nil)))
    (APPLY$2x
     (make apply$-badge
           :arity 3
           :out-arity 1
           :ilks '(:fn nil nil)))
    (APPLY$2xx
     (make apply$-badge
           :arity 3
           :out-arity 1
           :ilks '(:fn nil nil)))
    (RUSSELL
     (make apply$-badge
           :arity 2
           :out-arity 1
           :ilks '(:fn nil)))
    (FOLDR
     (make apply$-badge
           :arity 3
           :out-arity 1
           :ilks '(nil :fn nil)))
    (FOLDL
     (make apply$-badge
           :arity 3
           :out-arity 1
           :ilks '(nil :fn nil)))
    (COLLECT-FROM-TO
     (make apply$-badge
           :arity 3
           :out-arity 1
           :ilks '(nil nil :fn)))
    (COLLECT*
     (make apply$-badge
           :arity 2
           :out-arity 1
           :ilks '(nil :fn)))
    (COLLECT2
     (make apply$-badge
           :arity 3
           :out-arity 1
           :ilks '(nil :fn :fn)))
    (RECUR-BY-COLLECT
     (make apply$-badge
           :arity 2
           :out-arity 1
           :ilks '(nil :fn)))
    (PROW
     (make apply$-badge
           :arity 2
           :out-arity 1
           :ilks '(nil :fn)))
    (PROW*
     (make apply$-badge
           :arity 2
           :out-arity 1
           :ilks '(nil :fn)))
; FN-2-AND-FN-3 is omitted for the same reason EXPT-2-AND-EXPT-3 was.

    (FN-5
     (make apply$-badge
           :arity 2
           :out-arity 1
           :ilks '(:fn nil)))
    (MAP-FN-5
     (make apply$-badge
           :arity 2
           :out-arity 1
           :ilks '(nil :fn)))
    (SUMLIST-EXPR
     (make apply$-badge
           :arity 3
           :out-arity 1
           :ilks '(nil :expr nil)))
    (TWOFER
     (make apply$-badge
           :arity 4
           :out-arity 1
           :ilks '(nil :fn :expr nil)))
    (COLLECT-A
     (make apply$-badge
           :arity 2
           :out-arity 1
           :ilks '(nil :fn)))
    (COLLECT-B
     (make apply$-badge
           :arity 2
           :out-arity 1
           :ilks '(nil :fn)))
    (COLLECT-C
     (make apply$-badge
           :arity 3
           :out-arity 1
           :ilks '(nil :fn :fn)))
    (COLLECT-D
     (make apply$-badge
           :arity 3
           :out-arity 1
           :ilks '(nil :fn :fn)))
; No userfn of this name exists, only a ``doppelganger'' for PIF purposes.
; It doesn't need a badge because it is not known to APPLY$.

;   (COLLECT-D-INSTANCE
;    (make apply$-badge
;          :arity 2
;          :out-arity 1
;          :ilks '(nil :fn)))
    (COLLECT-E
     (make apply$-badge
           :arity 2
           :out-arity 1
           :ilks '(nil :fn)))
    (MY-APPLY-2
     (make apply$-badge
           :arity 3
           :out-arity 1
           :ilks '(:fn :fn nil)))
    (MY-APPLY-2-1
     (make apply$-badge
           :arity 2
           :out-arity 1
           :ilks '(:fn nil)))
    (COLLECT-MY-REV
     (make apply$-badge
           :arity 1
           :out-arity 1
           :ilks t))
    (MY-APPEND2
     (make apply$-badge
           :arity 2
           :out-arity 1
           :ilks t))
    (SQNATS
     (make apply$-badge
           :arity 1
           :out-arity 1
           :ilks t))
    (SUM-OF-PRODUCTS
     (make apply$-badge
           :arity 1
           :out-arity 1
           :ilks T))
    (COLLECT-COMPOSITION
     (make apply$-badge
           :arity 3
           :out-arity 1
           :ilks '(nil :fn :fn)))
    (COLLECT-X1000
     (make apply$-badge
           :arity 2
           :out-arity 1
           :ilks '(nil :fn)))
    (COLLECT-X1000-caller
     (make apply$-badge
           :arity 2
           :out-arity 1
           :ilks '(nil :fn)))
    (GUARDED-COLLECT
     (make apply$-badge
           :arity 2
           :out-arity 1
           :ilks '(nil :fn)))

    (ACK$
     (make apply$-badge
           :arity 4
           :out-arity 1
           :ilks '(:fn nil nil nil)))
    (SILLY$
     (make apply$-badge
           :arity 4
           :out-arity 1
           :ilks '(:fn nil nil nil)))

; See Note on Strengthening the Constraint in badge-userfn-type, in
; constraints.lisp.

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

(defun untame-apply$! (fn args)
  (declare (xargs :guard (true-listp args)
                  :guard-hints (("Goal"
                                 :use badge!-type
                                 :in-theory (disable badge!-type)))))
; (access apply$-badge badge :arity) = (cadr badge).
  (cond ((badge! fn)
         (list 'untame-apply$! fn (take (cadr (badge! fn)) args)))
        (t (list 'untame-apply$! fn))))

(defstub untame-ev$ (x a) t)

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

(defun cube (x) (* x (square x)))

(defun my-append1 (x y)
  (if (consp x)
      (cons (car x) (my-append1 (cdr x) y))
      y))

(defun my-rev (x)
  (if (consp x)
      (my-append1 (my-rev (cdr x)) (cons (car x) nil))
      nil))

(defun nats (n)
  (if (zp n)
      nil
      (cons n (nats (- n 1)))))

(defun expt-2-and-expt-3 (x)
  (let ((x2 (* x x)))
    (mv x2 (* x x2))))

(defun expt-5 (x)
  (mv-let (x2 x3)
    (expt-2-and-expt-3 x)
    (* x2 x3)))

(defun ok-fnp! (fn)                 ; <--- This is a G1 function with a doppelganger!
  (and (not (equal fn 'QUOTE))
       (not (equal fn 'IF))
       (tamep! `(,fn X))))

(defstobj st (counter :type integer :initially 0))

(defun count-atoms1 (x st)
  (declare (xargs :stobjs (st)))
  (cond ((atom x)
         (update-counter (+ 1 (counter st)) st))
        (t (let ((st (count-atoms1 (car x) st)))
             (count-atoms1 (cdr x) st)))))

(defun count-atoms (x)
  (with-local-stobj
    st
    (mv-let (val st)
      (let ((st (count-atoms1 x st)))
        (mv (counter st) st))
      val)))

; G2 Doppelgangers

(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(defun fn/expr-args (fn args)
  (case fn
    (COLLECT
     (list (cadr args)))
    (SUMLIST
     (list (cadr args)))
    (SUMLIST-WITH-PARAMS
     (list (cadr args)))
    (FILTER
     (list (cadr args)))
    (ALL
     (list (cadr args)))
    (XISTS
     (list (cadr args)))
    (MAXLIST
     (list (cadr args)))
    (COLLECT-ON
     (list (cadr args)))
    (COLLECT-TIPS
     (list (cadr args)))
    (APPLY$2
     (list (car args)))
    (APPLY$2x
     (list (car args)))
    (APPLY$2xx
     (list (car args)))
    (RUSSELL
     (list (car args)))
    (FOLDR
     (list (cadr args)))
    (FOLDL
     (list (cadr args)))
    (COLLECT-FROM-TO
     (list (caddr args)))
    (COLLECT*
     (list (cadr args)))
    (COLLECT2
     (list (cadr args) (caddr args)))
    (RECUR-BY-COLLECT
     (list (cadr args)))
    (PROW
     (list (cadr args)))
    (PROW*
     (list (cadr args)))
    (FN-5
     (list (car args)))
    (MAP-FN-5
     (list (cadr args)))
    (SUMLIST-EXPR
     (list (cadr args)))
    (TWOFER
     (list (cadr args) (caddr args)))
    (COLLECT-A
     (list (cadr args)))
    (COLLECT-B
     (list (cadr args)))
    (COLLECT-C
     (list (cadr args) (caddr args)))
    (COLLECT-D
     (list (cadr args) (caddr args)))
    (COLLECT-E
     (list (cadr args)))
    (COLLECT-COMPOSITION
     (list (cadr args) (caddr args)))
    (COLLECT-X1000
     (list (cadr args)))
    (COLLECT-X1000-CALLER
     (list (cadr args)))
    (MY-APPLY-2
     (list (car args) (cadr args)))
    (MY-APPLY-2-1
     (list (car args)))
    (GUARDED-COLLECT
     (list (cadr args)))
    (ACK$
     (list (car args)))
    (SILLY$
     (list (car args)))
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
  (xllist 0
         (max (weight fn)
              (if (fn/expr-args fn args)
                  (+ 1 (max-weight (fn/expr-args fn args)))
                  0))
         (chronological-position apply$)
             1))

(defun ev$!-measure (x a)
  (declare (ignore a))
  (xllist 0 (weight x) (chronological-position ev$) 1))

(defun ev$!-list-measure (x a)
  (declare (ignore a))
  (xllist 0 (weight x)  (chronological-position ev$-list) 1))

(defun apply$-userfn1!-measure (fn args)
  (xllist 0
          (max (weight fn)
               (if (fn/expr-args fn args)
                   (+ 1 (max-weight (fn/expr-args fn args)))
                   0))
          (chronological-position apply$-userfn)
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
         (untame-apply$! fn args)))
    ((eq fn 'EV$)
     (if (tamep! (car args))
         (ev$! (car args) (cadr args))
         (untame-apply$! fn args)))
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
    ((eq (car x) 'COLLECT)
     (apply$! 'COLLECT
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'SUMLIST)
     (apply$! 'SUMLIST
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'SUMLIST-WITH-PARAMS)
     (apply$! 'SUMLIST-WITH-PARAMS
              (list (ev$! (cadr x) a)
                    (cadr (caddr x))
                    (ev$! (cadddr x) a))))
    ((eq (car x) 'FILTER)
     (apply$! 'FILTER
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'ALL)
     (apply$! 'ALL
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'XISTS)
     (apply$! 'XISTS
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'MAXLIST)
     (apply$! 'MAXLIST
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'COLLECT-ON)
     (apply$! 'COLLECT-ON
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'COLLECT-TIPS)
     (apply$! 'COLLECT-TIPS
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'APPLY$2)
     (apply$! 'APPLY$2
              (list (cadr (cadr x))
                    (ev$! (caddr x) a)
                    (ev$! (cadddr x) a))))
    ((eq (car x) 'APPLY$2x)
     (apply$! 'APPLY$2x
              (list (cadr (cadr x))
                    (ev$! (caddr x) a)
                    (ev$! (cadddr x) a))))
    ((eq (car x) 'APPLY$2xx)
     (apply$! 'APPLY$2xx
              (list (cadr (cadr x))
                    (ev$! (caddr x) a)
                    (ev$! (cadddr x) a))))
    ((eq (car x) 'RUSSELL)
     (apply$! 'RUSSELL
              (list (cadr (cadr x))
                    (ev$! (caddr x) a))))
    ((eq (car x) 'FOLDR)
     (apply$! 'FOLDR
              (list (ev$! (cadr x) a)
                    (cadr (caddr x))
                    (ev$! (cadddr x) a))))
    ((eq (car x) 'FOLDL)
     (apply$! 'FOLDL
              (list (ev$! (cadr x) a)
                    (cadr (caddr x))
                    (ev$! (cadddr x) a))))
    ((eq (car x) 'COLLECT-FROM-TO)
     (apply$! 'COLLECT-FROM-TO
              (list (ev$! (cadr x) a)
                    (ev$! (caddr x) a)
                    (cadr (cadddr x)))))
    ((eq (car x) 'COLLECT*)
     (apply$! 'COLLECT*
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'COLLECT2)
     (apply$! 'COLLECT2
              (list (ev$! (cadr x) a)
                    (cadr (caddr x))
                    (cadr (cadddr x)))))
    ((eq (car x) 'RECUR-BY-COLLECT)
     (apply$! 'RECUR-BY-COLLECT
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'PROW)
     (apply$! 'PROW
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'PROW*)
     (apply$! 'PROW*
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'FN-5)
     (apply$! 'FN-5
              (list (cadr (cadr x))
                    (ev$! (caddr x) a))))
    ((eq (car x) 'MAP-FN-5)
     (apply$! 'MAP-FN-5
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'SUMLIST-EXPR)
     (apply$! 'SUMLIST-EXPR
              (list (ev$! (cadr x) a)
                    (cadr (caddr x))
                    (ev$! (cadddr x) a))))
    ((eq (car x) 'TWOFER)
     (apply$! 'TWOFER
              (list (ev$! (cadr x) a)
                    (cadr (caddr x))
                    (cadr (cadddr x))
                    (ev$! (car (cddddr x)) a))))
    ((eq (car x) 'COLLECT-A)
     (apply$! 'COLLECT-A
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'COLLECT-B)
     (apply$! 'COLLECT-B
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'COLLECT-C)
     (apply$! 'COLLECT-C
              (list (ev$! (cadr x) a)
                    (cadr (caddr x))
                    (cadr (cadddr x)))))
    ((eq (car x) 'COLLECT-D)
     (apply$! 'COLLECT-D
              (list (ev$! (cadr x) a)
                    (cadr (caddr x))
                    (cadr (cadddr x)))))
    ((eq (car x) 'COLLECT-E)
     (apply$! 'COLLECT-E
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'MY-APPLY-2)
     (apply$! 'MY-APPLY-2
              (list (cadr (cadr x))
                    (cadr (caddr x))
                    (ev$! (cadddr x) a))))
    ((eq (car x) 'MY-APPLY-2-1)
     (apply$! 'MY-APPLY-2-1
              (list (cadr (cadr x))
                    (ev$! (caddr x) a))))
    ((eq (car x) 'COLLECT-COMPOSITION)
     (apply$! 'COLLECT-COMPOSITION
              (list (ev$! (cadr x) a)
                    (cadr (caddr x))
                    (cadr (cadddr x)))))
    ((eq (car x) 'COLLECT-X1000)
     (apply$! 'COLLECT-X1000
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'COLLECT-X1000-CALLER)
     (apply$! 'COLLECT-X1000-CALLER
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'GUARDED-COLLECT)
     (apply$! 'GUARDED-COLLECT
              (list (ev$! (cadr x) a)
                    (cadr (caddr x)))))
    ((eq (car x) 'ACK$)
     (apply$! 'ACK$
              (list (cadr (cadr x))
                    (ev$! (caddr x) a)
                    (ev$! (cadddr x) a)
                    (ev$! (car (cddddr x)) a))))
    ((eq (car x) 'SILLY$)
     (apply$! 'SILLY$
              (list (cadr (cadr x))
                    (ev$! (caddr x) a)
                    (ev$! (cadddr x) a)
                    (ev$! (car (cddddr x)) a))))
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

; Now the user's mapping functions:

 (defun COLLECT! (lst fn)
   (declare (xargs :measure (standard-g2-userfn-measure collect)
                   :well-founded-relation l<))
   (cond
    ((endp lst) nil)
    (t (cons (APPLY$! fn (list (car lst)))
             (COLLECT! (cdr lst) fn)))))

 (defun SUMLIST! (lst fn)
   (declare (xargs :measure (standard-g2-userfn-measure sumlist)
                   :well-founded-relation l<))
   (cond
    ((endp lst) 0)
    (t (+ (APPLY$! fn (list (car lst)))
          (SUMLIST! (cdr lst) fn)))))

 (defun SUMLIST-WITH-PARAMS! (lst fn params)
   (declare (xargs :measure (standard-g2-userfn-measure sumlist-with-params)
                   :well-founded-relation l<))
   (cond
    ((endp lst) 0)
    (t (+ (APPLY$! fn (cons (car lst) params))
          (SUMLIST-WITH-PARAMS! (cdr lst) fn params)))))

 (defun FILTER! (lst fn)
   (declare (xargs :measure (standard-g2-userfn-measure filter)
                   :well-founded-relation l<))
   (cond
    ((endp lst) nil)
    ((APPLY$! fn (list (car lst)))
     (cons (car lst) (FILTER! (cdr lst) fn)))
    (t (FILTER! (cdr lst) fn))))

 (defun ALL! (lst fn)
   (declare (xargs :measure (standard-g2-userfn-measure all)
                   :well-founded-relation l<))
   (cond
    ((endp lst) t)
    (t (and (APPLY$! fn (list (car lst)))
            (ALL! (cdr lst) fn)))))

 (defun XISTS! (lst fn)
   (declare (xargs :measure (standard-g2-userfn-measure xists)
                   :well-founded-relation l<))
   (cond ((endp lst) nil)
         ((APPLY$! fn (list (car lst))) t)
         (t (XISTS! (cdr lst) fn))))

 (defun maxlist! (lst fn)
   (declare (xargs :measure (standard-g2-userfn-measure maxlist)
                   :well-founded-relation l<))
   (cond ((endp lst) nil)
         ((endp (cdr lst)) (APPLY$! fn (list (car lst))))
         (t (max (APPLY$! fn (list (car lst)))
                 (MAXLIST! (cdr lst) fn)))))

 (defun COLLECT-ON! (lst fn)
   (declare (xargs :measure (standard-g2-userfn-measure collect-on)
                   :well-founded-relation l<))
   (cond
    ((endp lst) nil)
    (t (cons (apply$! fn (list lst))
             (COLLECT-ON! (cdr lst) fn)))))

 (defun COLLECT-TIPS! (x fn)
   (declare (xargs :measure (standard-g2-userfn-measure collect-tips)
                   :well-founded-relation l<))
   (cond
    ((atom x) (apply$! fn (list x)))
    (t (cons (COLLECT-TIPS! (car x) fn)
             (COLLECT-TIPS! (cdr x) fn)))))

 (defun APPLY$2! (fn x y)
   (declare (xargs :measure (standard-g2-userfn-measure apply$2)
                   :well-founded-relation l<))
   (APPLY$! fn (list x y)))

 (defun APPLY$2x! (fn x y)
   (declare (xargs :measure (standard-g2-userfn-measure apply$2x)
                   :well-founded-relation l<))
   (APPLY$2! fn x y))

 (defun APPLY$2xx! (fn x y)
   (declare (xargs :measure (standard-g2-userfn-measure apply$2xx)
                   :well-founded-relation l<))
   (APPLY$2x! fn x y))

 (defun RUSSELL! (fn x)
   (declare (xargs :measure (standard-g2-userfn-measure russell)
                   :well-founded-relation l<))
   (NOT (APPLY$! fn (list x x))))

 (defun FOLDR! (lst fn init)
   (declare (xargs :measure (standard-g2-userfn-measure foldr)
                   :well-founded-relation l<))
   (cond
    ((endp lst) init)
    (t (apply$! fn
                (list (car lst)
                      (foldr! (cdr lst) fn init))))))

 (defun FOLDL! (lst fn ans)
   (declare (xargs :measure (standard-g2-userfn-measure foldl)
                   :well-founded-relation l<))
   (if (endp lst)
       ans
       (foldl! (cdr lst)
               fn
               (apply$! fn (list (car lst) ans)))))

 (defun COLLECT-FROM-TO! (i max fn)
   (declare (xargs :measure (standard-g2-userfn-measure collect-from-to)
                   :well-founded-relation l<))
   (let ((i (ifix i))
         (max (ifix max)))
     (cond
      ((> i max)
       nil)
      (t (cons (apply$! fn (list i))
               (collect-from-to! (+ i 1) max fn))))))

 (defun COLLECT*! (lst fn)
   (declare (xargs :measure (standard-g2-userfn-measure collect*)
                   :well-founded-relation l<))
   (if (endp lst)
       nil
       (cons (apply$! fn (car lst))
             (collect*! (cdr lst) fn))))

 (defun COLLECT2! (lst fn1 fn2)
   (declare (xargs :measure (standard-g2-userfn-measure collect2)
                   :well-founded-relation l<))
   (if (endp lst)
       nil
       (cons (cons (apply$! fn1 (list (car lst)))
                   (apply$! fn2 (list (car lst))))
             (collect2! (cdr lst) fn1 fn2))))

 (defun RECUR-BY-COLLECT! (lst fn)
   (declare (xargs :measure (standard-g2-userfn-measure recur-by-collect)
                   :well-founded-relation l<))
   (if (endp lst)
       nil
       (if (< (len (collect! (cdr lst) fn))
              (len lst))
           (cons (car lst)
                 (recur-by-collect! (collect! (cdr lst) fn) fn))
           nil)))

 (defun PROW! (lst fn)
   (declare (xargs :measure (standard-g2-userfn-measure prow)
                   :well-founded-relation l<))
   (cond ((or (endp lst) (endp (cdr lst)))
          nil)
         (t (cons (apply$! fn (list (car lst) (cadr lst)))
                  (prow! (cdr lst) fn)))))
 (defun PROW*! (lst fn)
   (declare (xargs :measure (standard-g2-userfn-measure prow*)
                   :well-founded-relation l<))
   (cond ((or (endp lst)
              (endp (cdr lst)))
          (apply$! fn (list lst lst)))
         ((< (len (prow! lst fn)) (len lst))
          (prow*! (prow! lst fn) fn))
         (t nil)))

 (defun FN-2-AND-FN-3! (fn x)
   (declare (xargs :measure (standard-g2-userfn-measure fn-2-and-fn-3)
                   :well-founded-relation l<))
   (let ((x2 (apply$! fn (list x x))))
     (mv x2 (apply$! fn (list x x2)))))

 (defun FN-5! (fn x)
   (declare (xargs :measure (standard-g2-userfn-measure fn-5)
                   :well-founded-relation l<))
   (mv-let (x2 x3)
     (fn-2-and-fn-3! fn x)
     (apply$! fn (list x2 x3))))

 (defun MAP-FN-5! (lst fn)
   (declare (xargs :measure (standard-g2-userfn-measure map-fn-5)
                   :well-founded-relation l<))
   (if (endp lst)
       nil
       (cons (fn-5! fn (car lst))
             (map-fn-5! (cdr lst) fn))))
 (defun SUMLIST-EXPR! (lst expr alist)
   (declare (xargs :measure (standard-g2-userfn-measure sumlist-expr)
                   :well-founded-relation l<))
   (cond ((endp lst) 0)
         (t (+ (ev$! expr (cons (cons 'x (car lst)) alist))
               (sumlist-expr! (cdr lst) expr alist)))))

 (defun TWOFER! (lst fn xpr alist)
   (declare (xargs :measure (standard-g2-userfn-measure twofer)
                   :well-founded-relation l<))
   (if (endp lst)
       nil
       (cons (cons (APPLY$! fn (list (car lst)))
                   (EV$! xpr (cons (cons 'TAIL lst) alist)))
             (TWOFER! (cdr lst) fn xpr alist))))

 (defun COLLECT-A! (lst fn)
   (declare (xargs :measure (standard-g2-userfn-measure collect-a)
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

 (defun COLLECT-B! (lst fn)
   (declare (xargs :measure (standard-g2-userfn-measure collect-b)
                   :well-founded-relation l<))
   (cond ((endp lst) nil)
         (t (cons (APPLY$! fn (list (SUMLIST! (nats (car lst)) fn)))
                  (COLLECT-B! (cdr lst) fn)))))

 (defun COLLECT-C! (lst fn1 fn2)
   (declare (xargs :measure (standard-g2-userfn-measure collect-c)
                   :well-founded-relation l<))
   (cond ((endp lst) nil)
         (t (cons (APPLY$! fn1 (list (SUMLIST! (nats (car lst)) fn2)))
                  (COLLECT-C! (cdr lst) fn1 fn2)))))

 (defun collect-d! (lst fn1 fn2)
   (declare (xargs :measure (standard-g2-userfn-measure collect-d)
                   :well-founded-relation l<))
   (if (endp lst)
       nil
       (cons (cons (apply$! fn1 (list (car lst)))
                   (apply$! fn2 (list (car lst))))
             (collect-d! (cdr lst) fn1 fn2))))

 (defun collect-e! (lst fn)
   (declare (xargs :measure (standard-g2-userfn-measure collect-e)
                   :well-founded-relation l<))
   (if (endp lst)
       nil
       (cons (collect-d! lst fn '(lambda (x) (binary-+ '10 (square x))))
             (collect-e! (cdr lst) fn))))

 (defun my-apply-2! (fn1 fn2 x)
   (declare (xargs :measure (standard-g2-userfn-measure my-apply-2)
                   :well-founded-relation l<))
   (list (apply$! fn1 x)
         (apply$! fn2 x)))

 (defun my-apply-2-1! (fn x)
   (declare (xargs :measure (standard-g2-userfn-measure my-apply-2-1)
                   :well-founded-relation l<))
   (my-apply-2! fn fn x))

 (defun collect-my-rev! (lst)
   (declare (xargs :measure (standard-g2-userfn-measure collect-my-rev)
                   :well-founded-relation l<))
   (collect! lst 'MY-REV))

 (defun my-append2! (x y)
   (declare (xargs :measure (standard-g2-userfn-measure my-append2)
                   :well-founded-relation l<))
   (foldr! x 'CONS y))

 (defun sqnats! (x)
   (declare (xargs :measure (standard-g2-userfn-measure sqnats)
                   :well-founded-relation l<))
   (collect! (filter! x 'NATP) 'SQUARE))

 (defun sum-of-products! (lst)
   (declare (xargs :measure (standard-g2-userfn-measure sum-of-products)
                   :well-founded-relation l<))
   (sumlist! lst
             '(LAMBDA (X)
                      (FOLDR X
                             '(LAMBDA (I A)
                                      (BINARY-* I A))
                             '1))))
 (defun collect-composition! (lst fn gn)
   (declare (xargs :measure (standard-g2-userfn-measure collect-composition)
                   :well-founded-relation l<))
   (if (endp lst)
       nil
       (cons (apply$! fn (list (apply$! gn (list (car lst)))))
             (collect-composition! (cdr lst) fn gn))))

 (defun collect-x1000! (lst fn)
   (declare (xargs :measure (standard-g2-userfn-measure collect-x1000)
                   :well-founded-relation l<))
   (collect-composition! lst fn '(lambda (x) (binary-* '1000 x))))

 (defun collect-x1000-caller! (lst fn)
   (declare (xargs :measure (standard-g2-userfn-measure collect-x1000-caller)
                   :well-founded-relation l<))
   (if (endp lst)
       nil
       (cons (collect-x1000! (car lst) fn)
             (collect-x1000-caller! (cdr lst) fn))))

 (defun guarded-collect! (lst fn)
   (declare (xargs ; :guard (true-listp lst) ; <--- guard eliminated
             :measure (standard-g2-userfn-measure guarded-collect)
             :well-founded-relation l<))
   (if (endp lst)
       nil
       (cons (apply$! fn (list (car lst)))
             (guarded-collect! (cdr lst) fn))))

 (defun ack$! (fn k n m)
   (declare (xargs :measure (standard-g2-userfn-measure ack$)
                   :well-founded-relation l<))
   (if (zp k)
       (apply$! fn (list (+ 1 n)))
       (if (zp m)
           (if (equal k 2)
               0
               (if (equal k 3)
                   1
                   n))
           (ack$! fn
                  (- k 1)
                  (ack$! fn k n (- m 1))
                  n))))

 (defun silly$! (fn k n m)
   (declare (xargs :measure (standard-g2-userfn-measure silly$)
                   :well-founded-relation l<))
   (if (zp k)
       (apply$! fn (list n))
       (if (zp n)
           (apply$! fn (list k))
           (if (zp m)
               (apply$! fn (list n))
               (silly$! fn
                        (- k 1)
                        (silly$! fn
                                 k
                                 (- n 1)
                                 (silly$! fn
                                          k
                                          n
                                          (- m 1)))
                        m)))))

 (defun apply$-userfn1! (fn args)
   (declare (xargs :measure (apply$-userfn1!-measure fn args)
                   :well-founded-relation l<))
   (case fn
     (SQUARE (square (car args)))
     (CUBE (cube (car args)))
     (MY-APPEND1 (my-append1 (car args) (cadr args)))
     (MY-REV (my-rev (car args)))
     (NATS (nats (car args)))
     (EXPT-2-AND-EXPT-3 (mv-list 2 (expt-2-and-expt-3 (car args))))
     (EXPT-5 (expt-5 (car args)))
     (OK-FNP (ok-fnp! (car args))) 
     (COUNT-ATOMS (count-atoms (car args)))

     (COLLECT
      (if (tamep-functionp! (cadr args))
          (COLLECT! (car args) (cadr args))
          (untame-apply$! fn args)))
     (SUMLIST
      (if (tamep-functionp! (cadr args))
          (SUMLIST! (car args) (cadr args))
          (untame-apply$! fn args)))
     (SUMLIST-WITH-PARAMS
      (if (tamep-functionp! (cadr args))
          (SUMLIST-WITH-PARAMS! (car args)
                                (cadr args)
                                (caddr args))
          (untame-apply$! fn args)))
     (FILTER
      (if (tamep-functionp! (cadr args))
          (FILTER! (car args) (cadr args))
          (untame-apply$! fn args)))
     (ALL
      (if (tamep-functionp! (cadr args))
          (ALL! (car args) (cadr args))
          (untame-apply$! fn args)))
     (XISTS
      (if (tamep-functionp! (cadr args))
          (XISTS! (car args) (cadr args))
          (untame-apply$! fn args)))
     (MAXLIST
      (if (tamep-functionp! (cadr args))
          (maxlist! (car args) (cadr args))
          (untame-apply$! fn args)))
     (COLLECT-ON
      (if (tamep-functionp! (cadr args))
          (COLLECT-ON! (car args) (cadr args))
          (untame-apply$! fn args)))
     (COLLECT-TIPS
      (if (tamep-functionp! (cadr args))
          (COLLECT-TIPS! (car args)
                         (cadr args))
          (untame-apply$! fn args)))
     (APPLY$2
      (if (tamep-functionp! (car args))
          (APPLY$2! (car args)
                    (cadr args)
                    (caddr args))
          (untame-apply$! fn args)))
     (APPLY$2x
      (if (tamep-functionp! (car args))
          (APPLY$2x! (car args)
                     (cadr args)
                     (caddr args))
          (untame-apply$! fn args)))
     (APPLY$2xx
      (if (tamep-functionp! (car args))
          (APPLY$2xx! (car args)
                      (cadr args)
                      (caddr args))
          (untame-apply$! fn args)))
     (RUSSELL
      (if (tamep-functionp! (car args))
          (RUSSELL! (car args)
                    (cadr args))
          (untame-apply$! fn args)))
     (FOLDR
      (if (tamep-functionp! (cadr args))
          (FOLDR! (car args)
                  (cadr args)
                  (caddr args))
          (untame-apply$! fn args)))
     (FOLDL
      (if (tamep-functionp! (cadr args))
          (FOLDL! (car args)
                  (cadr args)
                  (caddr args))
          (untame-apply$! fn args)))
     (COLLECT-FROM-TO
      (if (tamep-functionp! (caddr args))
          (COLLECT-FROM-TO! (car args)
                            (cadr args)
                            (caddr args))
          (untame-apply$! fn args)))
     (COLLECT*
      (if (tamep-functionp! (cadr args))
          (COLLECT*! (car args)
                     (cadr args))
          (untame-apply$! fn args)))
     (COLLECT2
      (if (and (tamep-functionp! (cadr args))
               (tamep-functionp! (caddr args)))
          (COLLECT2! (car args)
                     (cadr args)
                     (caddr args))
          (untame-apply$! fn args)))
     (RECUR-BY-COLLECT
      (if (tamep-functionp! (cadr args))
          (RECUR-BY-COLLECT! (car args)
                             (cadr args))
          (untame-apply$! fn args)))
     (PROW
      (if (tamep-functionp! (cadr args))
          (PROW! (car args)
                 (cadr args))
          (untame-apply$! fn args)))
     (PROW*
      (if (tamep-functionp! (cadr args))
          (PROW*! (car args)
                  (cadr args))
          (untame-apply$! fn args)))
     (FN-5
      (if (tamep-functionp! (car args))
          (FN-5! (car args)
                 (cadr args))
          (untame-apply$! fn args)))
     (MAP-FN-5
      (if (tamep-functionp! (cadr args))
          (MAP-FN-5! (car args)
                     (cadr args))
          (untame-apply$! fn args)))
     (SUMLIST-EXPR
      (if (tamep! (cadr args))
          (SUMLIST-EXPR! (car args)
                         (cadr args)
                         (caddr args))
          (untame-apply$! fn args)))
     (TWOFER
      (if (and (tamep-functionp! (cadr args))
               (tamep! (caddr args)))
          (TWOFER! (car args)
                   (cadr args)
                   (caddr args)
                   (cadddr args))
          (untame-apply$! fn args)))
     (COLLECT-A
      (if (tamep-functionp! (cadr args))
          (collect-a! (car args)
                      (cadr args))
          (untame-apply$! fn args)))
     (COLLECT-B
      (if (tamep-functionp! (cadr args))
          (collect-b! (car args)
                      (cadr args))
          (untame-apply$! fn args)))
     (COLLECT-C
      (if (and (tamep-functionp! (cadr args))
               (tamep-functionp! (caddr args)))
          (collect-c! (car args)
                      (cadr args)
                      (caddr args))
          (untame-apply$! fn args)))
     (COLLECT-D
      (if (and (tamep-functionp! (cadr args))
               (tamep-functionp! (caddr args)))
          (collect-d! (car args)
                      (cadr args)
                      (caddr args))
          (untame-apply$! fn args)))
     (COLLECT-E
      (if (tamep-functionp! (cadr args))
          (collect-e! (car args)
                      (cadr args))
          (untame-apply$! fn args)))
     (MY-APPLY-2
      (if (and (tamep-functionp! (car args))
               (tamep-functionp! (cadr args)))
          (my-apply-2! (car args)
                       (cadr args)
                       (caddr args))
          (untame-apply$! fn args)))
     (MY-APPLY-2-1
      (if (tamep-functionp! (car args))
          (my-apply-2-1! (car args)
                         (cadr args))
          (untame-apply$! fn args)))
     (COLLECT-MY-REV
      (collect-my-rev! (car args)))
     (MY-APPEND2
      (my-append2! (car args)
                   (cadr args)))
     (SQNATS
      (sqnats! (car args)))
     (SUM-OF-PRODUCTS
      (sum-of-products! (car args)))
     (COLLECT-COMPOSITION
      (if (and (tamep-functionp! (cadr args))
               (tamep-functionp! (caddr args)))
          (collect-composition! (car args)
                                (cadr args)
                                (caddr args))
          (untame-apply$! fn args)))
     (COLLECT-X1000
      (if (tamep-functionp! (cadr args))
          (collect-x1000! (car args)
                          (cadr args))
          (untame-apply$! fn args)))
     (COLLECT-X1000-CALLER
      (if (tamep-functionp! (cadr args))
          (collect-x1000-caller! (car args)
                                 (cadr args))
          (untame-apply$! fn args)))
     (GUARDED-COLLECT
      (if (tamep-functionp! (cadr args))
          (GUARDED-COLLECT! (car args)
                            (cadr args))
          (untame-apply$! fn args)))
     (ACK$
      (if (tamep-functionp! (car args))
          (ack$! (car args) (cadr args) (caddr args) (cadddr args))
          (untame-apply$! fn args)))
     (SILLY$
      (if (tamep-functionp! (car args))
          (silly$! (car args) (cadr args) (caddr args) (cadddr args))
          (untame-apply$! fn args)))
     (otherwise (untame-apply$! fn args))))

 )

(defthm len-collect!
  (equal (len (collect! x fn)) (len x))
  :hints (("Subgoal *1/1" :expand (collect! x fn))))

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
  (declare (xargs :guard (true-listp args)))
  (ec-call (apply$-userfn1! fn args)))





