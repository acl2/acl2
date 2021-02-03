; Expressions that can appear in DAGs
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "all-dargp")

;;;
;;; dag-function-call-exprp
;;;

;; See dag-function-call-exprp-redef below for a better definition.
(defund dag-function-call-exprp (expr)
  (declare (xargs :guard t))
  (and (consp expr)
       (symbolp (ffn-symb expr)) ; disallows lambdas (they should be immediately beta reduced)
       (not (eq 'quote (ffn-symb expr)))
       (true-listp (fargs expr))
       (all-dargp (fargs expr))))

;;;
;;; dargs
;;;

;; Extract the arguments of a DAG expr that is a function call.
;; keep this closed to make DAG reasoning more abstract
(defund-inline dargs (expr)
  (declare (xargs :guard (dag-function-call-exprp expr)
                  :guard-hints (("Goal" :in-theory (enable dag-function-call-exprp)))))
  (cdr expr))

(defthm dargs-of-cons
  (equal (dargs (cons fn args))
         args)
  :hints (("Goal" :in-theory (enable dargs))))

(defthmd dargs-when-not-consp-cheap
  (implies (not (consp expr))
           (equal (dargs expr)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable dargs))))

(defthm acl2-count-of-dargs-bound-weak
  (<= (acl2-count (dargs expr)) (acl2-count expr))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable dargs))))

(defthm acl2-count-of-dargs-bound-strong
  (implies (consp expr)
           (< (acl2-count (dargs expr)) (acl2-count expr)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable dargs))))

(defun-inline darg1 (x) (declare (xargs :guard (and (dag-function-call-exprp x) (<= 1 (len (dargs x)))))) (first (dargs x)))
(defun-inline darg2 (x) (declare (xargs :guard (and (dag-function-call-exprp x) (<= 2 (len (dargs x)))))) (second (dargs x)))
(defun-inline darg3 (x) (declare (xargs :guard (and (dag-function-call-exprp x) (<= 3 (len (dargs x)))))) (third (dargs x)))
(defun-inline darg4 (x) (declare (xargs :guard (and (dag-function-call-exprp x) (<= 4 (len (dargs x)))))) (fourth (dargs x)))
(defun-inline darg5 (x) (declare (xargs :guard (and (dag-function-call-exprp x) (<= 5 (len (dargs x)))))) (fifth (dargs x)))
(defun-inline darg6 (x) (declare (xargs :guard (and (dag-function-call-exprp x) (<= 6 (len (dargs x)))))) (sixth (dargs x)))

;; Now that dargs has been defined, we redefine dag-function-call-exprp so that
;; its expansion mentions dargs instead of fargs.
(defthm dag-function-call-exprp-redef
  (equal (dag-function-call-exprp expr)
         (and (consp expr)
              (symbolp (ffn-symb expr)) ;this disallows lambdas (think about that?  they should be immediately beta reduced)
              (not (eq 'quote (ffn-symb expr)))
              (true-listp (dargs expr))
              (all-dargp (dargs expr))))
  :rule-classes :definition
  :hints (("Goal" :in-theory (enable dag-function-call-exprp dargs))))

(defthm dag-function-call-exprp-forward-to-true-listp-of-dargs
  (implies (dag-function-call-exprp expr)
           (true-listp (dargs expr)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable dag-function-call-exprp))))

;todo: rename to dag-exprp once that one is renamed
;; A expression that can appear at a DAG node must be a variable, quoted constant, or function symbol applied to nodenums/constants.
;; Note that we do not allow simply the number of another node.  Also, note that lambdas applications are not allowed  (each function must be a symbol).
(defund dag-exprp0 (expr)
  (declare (xargs :guard t))
  (or (symbolp expr) ;a variable
      (myquotep expr) ; a quoted constant
      ;; a function call:
      (dag-function-call-exprp expr)))

(defthm all-dargp-of-dargs-when-dag-exprp0
  (implies (and (dag-exprp0 expr)
                (not (eq 'quote (car expr))))
           (all-dargp (dargs expr)))
  :hints (("Goal" :in-theory (enable dag-exprp0))))

;drop?
(local (in-theory (enable consp-of-cdr-of-nth-when-all-dargp)))

(local (in-theory (enable equal-of-quote-and-car-of-nth-when-all-dargp)))

(local (in-theory (enable equal-of-quote-and-nth-0-of-nth-when-all-dargp)))

;; We normalize claims about dag-args to consp.
(defthm consp-of-cdr-of-nth-of-dargs
  (implies (and (dag-exprp0 expr)
                (< n (len (dargs expr)))
                (natp n)
                (not (equal 'quote (car expr)))
;               (not (consp (nth n (aref1 dag-array-name dag-array nodenum)))) ;rules out a quotep
                )
           (equal (consp (cdr (nth n (dargs expr))))
                  (consp (nth n (dargs expr)))))
  :hints (("Goal" :in-theory (enable dag-exprp0))))

;; same as below except uses car instead of nth 0
(defthm equal-of-quote-and-car-of-nth-of-dargs
  (implies (and (dag-exprp0 expr)
                (< n (len (dargs expr)))
                (natp n)
                (not (equal 'quote (car expr)))
;               (not (consp (nth n (aref1 dag-array-name dag-array nodenum)))) ;rules out a quotep
                )
           (equal (equal 'quote (car (nth n (dargs expr))))
                  (consp (nth n (dargs expr))))))

(defthm myquotep-of-nth-of-dargs
  (implies (and (dag-exprp0 expr)
                (< n (len (dargs expr)))
                (natp n)
                (not (equal 'quote (car expr)))
;               (not (consp (nth n (aref1 dag-array-name dag-array nodenum)))) ;rules out a quotep
                )
           (equal (myquotep (nth n (dargs expr)))
                  (consp (nth n (dargs expr)))))
  :hints (("Goal" :in-theory (e/d (myquotep-of-nth-when-all-dargp)
                                  (myquotep)))))

(defthm dargp-of-nth-of-dargs
  (implies (and (dag-exprp0 expr)
                (< n (len (dargs expr)))
                (natp n)
                (not (equal 'quote (car expr)))
;               (not (consp (nth n (aref1 dag-array-name dag-array nodenum)))) ;rules out a quotep
                )
           (dargp (nth n (dargs expr))))
  :hints (("Goal" :in-theory (e/d (myquotep-of-nth-when-all-dargp)
                                  (myquotep)))))

(defthm equal-of-quote-and-nth-0-of-nth-of-dargs
  (implies (and (dag-exprp0 expr)
                (< n (len (dargs expr)))
                (natp n)
                (not (equal 'quote (nth 0 expr)))
;               (not (consp (nth n (aref1 dag-array-name dag-array nodenum)))) ;rules out a quotep
                )
           (equal (equal 'quote (nth 0 (nth n (dargs expr))))
                  (consp (nth n (dargs expr))))))

(defthm equal-of-len-of-nth-of-dargs-and-2
  (implies (and (dag-exprp0 expr)
                (< n (len (dargs expr)))
                (natp n)
                (not (equal 'quote (car expr)))
;               (not (consp (nth n (aref1 dag-array-name dag-array nodenum)))) ;rules out a quotep
                )
           (equal (equal 2 (len (nth n (dargs expr))))
                  (consp (nth n (dargs expr)))))
  :hints (("Goal" :in-theory (enable equal-of-len-of-nth-and-2-when-all-dargp))))

(defthm natp-of-nth-of-dargs
  (implies (and (dag-exprp0 expr)
                (< n (len (dargs expr)))
                (natp n)
                (not (equal 'quote (nth 0 expr))))
           (equal (natp (nth n (dargs expr)))
                  (not (consp (nth n (dargs expr))))))
  :hints (("Goal" :in-theory (enable integerp-of-nth-when-all-dargp
                                     not-<-of-0-and-nth-when-all-dargp))))

(defthm not-equal-of-header-and-nth-of-dargs
  (implies (and (dag-exprp0 expr)
                (not (equal 'quote (car expr))))
           (not (equal :header (nth n (dargs expr)))))
  :hints (("Goal" :in-theory (enable dag-exprp0
                                     integerp-of-nth-when-all-dargp
                                     not-<-of-0-and-nth-when-all-dargp))))

(defthm integerp-of-nth-of-dargs
  (implies (and (dag-exprp0 expr)
                (< n (len (dargs expr)))
                (natp n)
                (not (equal 'quote (nth 0 expr))))
           (equal (integerp (nth n (dargs expr)))
                  (not (consp (nth n (dargs expr))))))
  :hints (("Goal" :in-theory (enable integerp-of-nth-when-all-dargp))))

(defthm not-<-of-0-and-nth-of-dargs
  (implies (and (dag-exprp0 expr)
                (< n (len (dargs expr)))
                (natp n)
                (not (equal 'quote (car expr)))
                )
           (not (< (nth n (dargs expr)) 0)))
  :hints (("Goal" :in-theory (enable integerp-of-nth-when-all-dargp))))

(defthm true-listp-of-cdr-of-nth-of-dargs
  (implies (and (dag-exprp0 expr)
;                (< n (len (dargs expr)))
                (natp n)
                (not (equal 'quote (car expr)))
;               (not (consp (nth n (aref1 dag-array-name dag-array nodenum)))) ;rules out a quotep
                )
           (true-listp (cdr (nth n (dargs expr)))))
  :hints (("Goal" :in-theory (enable true-listp-of-cdr-of-nth-when-all-dargp
                                     dag-exprp0))))

;; use consp as our normal form
(defthm len-of-nth-of-dargs
  (implies (and (dag-exprp0 expr)
                (< n (len (dargs expr)))
                (natp n)
                (not (equal 'quote (car expr))))
           (equal (len (nth n (dargs expr)))
                  (if (consp (nth n (dargs expr)))
                      2
                    0)))
  :hints (("Goal" :in-theory (enable <-of-1-and-len-of-nth-when-all-dargp))))

;; too expensive to leave enabled
(defthmd symbolp-of-car-when-dag-exprp0
  (implies (dag-exprp0 expr)
           (symbolp (car expr)))
  :hints (("Goal" :in-theory (enable dag-exprp0))))

;; too expensive to leave enabled
(defthmd symbolp-of-nth-0-when-dag-exprp0
  (implies (dag-exprp0 expr)
           (symbolp (nth 0 expr)))
  :hints (("Goal" :in-theory (enable dag-exprp0))))

(defthmd true-list-of-cdr--when-dag-exprp0-and-quotep
  (implies (and (dag-exprp0 expr)
                (equal 'quote (car expr)))
           (true-listp (cdr expr)))
  :hints (("Goal" :in-theory (enable dag-exprp0))))

;move
;compromise.  we leave car but turn cadr etc into nth.
(defthmd cadr-becomes-nth-of-1
  (equal (cadr x)
         (nth 1 x)))

(defthmd not-cddr-when-dag-exprp0-and-quotep
  (implies (and (dag-exprp0 expr)
                (equal 'quote (car expr)))
           (equal (cddr expr)
                  nil))
  :hints (("Goal" :in-theory (enable dag-exprp0))))

(defthm dag-exprp0-and-consp-forward-to-true-listp-of-dargs
  (implies (and (dag-exprp0 expr)
                (consp expr))
           (true-listp (dargs expr)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable dag-exprp0
                                     dargs ;todo: this theorem happens to be true for quoteps too
                                     ))))

(defthm dag-exprp0-and-not-consp-forward-to-symbolp
  (implies (and (dag-exprp0 expr)
                (not (consp expr)))
           (symbolp expr))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable dag-exprp0))))

(defthm dag-exprp0-and-forward-to-true-listp-when-quote
  (implies (and (dag-exprp0 expr)
                (eq 'quote (car expr)))
           (true-listp expr))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable dag-exprp0))))

(defthm dag-exprp0-of-cons
  (equal (dag-exprp0 (cons fn args))
         (and (symbolp fn)
              (true-listp args)
              (if (eq 'quote fn)
                  (equal 1 (len args))
                (all-dargp args))))
  :hints (("Goal" :in-theory (enable dag-exprp0))))

;; We use consp as the normal form
(defthmd symbolp-when-dag-exprp0
  (implies (dag-exprp0 expr)
           (equal (symbolp expr)
                  (not (consp expr)))))

(defthm dag-exprp0-when-equal-of-quote-and-car-cheap
  (implies (equal 'quote (car expr))
           (equal (dag-exprp0 expr)
                  (myquotep expr)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable dag-exprp0))))

;; In general, we need car-becomes-nth-of-0 to turn all things like this into nth.
(defthm car-of-dargs-becomes-nth-0-of-dargs
  (equal (car (dargs expr))
         (nth 0 (dargs expr)))
  :hints (("Goal" :in-theory (enable nth))))

(defthm cadr-of-dargs-becomes-nth-1-of-dargs
  (equal (cadr (dargs expr))
         (nth 1 (dargs expr)))
  :hints (("Goal" :expand (nth 1 (dargs expr))
           :in-theory (enable nth))))

(defthm caddr-of-dargs-becomes-nth-1-of-dargs
  (equal (caddr (dargs expr))
         (nth 2 (dargs expr)))
  :hints (("Goal" :expand ((nth 1 (cdr (dargs expr)))
                           (nth 2 (dargs expr)))
           :in-theory (enable nth))))
