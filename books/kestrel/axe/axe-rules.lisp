; Axe's representation of rewrite rules
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

;; See also stored-rules.lisp.

(include-book "kestrel/utilities/quote" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/utilities/terms" :dir :system) ; for lambda-free-termp
(include-book "kestrel/lists-light/reverse-list" :dir :system)

(defund list-of-variables-and-constantsp (items)
  (declare (xargs :guard t))
  (if (atom items)
      (null items)
    (and (or (symbolp (first items))
             (myquotep (first items)))
         (list-of-variables-and-constantsp (rest items)))))

(defthm list-of-variables-and-constantsp-of-take
  (implies (list-of-variables-and-constantsp x)
           (list-of-variables-and-constantsp (take n x)))
  :hints (("Goal" :in-theory (enable list-of-variables-and-constantsp))))

(defthm list-of-variables-and-constantsp-forward-to-pseudo-term-listp
  (implies (list-of-variables-and-constantsp args)
           (pseudo-term-listp args))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable list-of-variables-and-constantsp))))

;; An axe-syntaxp-function-application is an application of a function (a
;; symbol) to arguments that are all either variables or quoted constants.
;; Note that dag-array, if needed, is omitted from args stored in the expr.
(defund axe-syntaxp-function-applicationp (expr)
  (declare (xargs :guard (pseudo-termp expr)))
  (and (consp expr)
       (symbolp (ffn-symb expr))
       (not (eq 'quote (ffn-symb expr)))
       (list-of-variables-and-constantsp (fargs expr))
       ;; special case:
       (implies (eq (ffn-symb expr) 'axe-quotep)
                (variablep (farg1 expr)))))

;; An axe-syntaxp expression is a nest of calls of IF and NOT with constants
;; and axe-syntaxp-function-applications at the leaves.
(defund axe-syntaxp-exprp (expr)
  (declare (xargs :guard (pseudo-termp expr)))
  (if (atom expr)
      nil ; a variable is not allowed
    (if (myquotep expr)
        t ;could check that it is t or nil...
      (if (call-of 'if expr)
          (and (= 3 (len (fargs expr)))
               (axe-syntaxp-exprp (farg1 expr))
               (axe-syntaxp-exprp (farg2 expr))
               (axe-syntaxp-exprp (farg3 expr)))
        (if (call-of 'not expr)
            (and (= 1 (len (fargs expr)))
                 (axe-syntaxp-exprp (farg1 expr)))
          (axe-syntaxp-function-applicationp expr))))))

;; For the second arg of an axe-bind-free, as given by the user.  TODO: Avoid the need for the quoting?
(defun quoted-symbol-listp (item)
  (declare (xargs :guard t))
  (and (true-listp item)
       (eql 2 (len item))
       (eq 'quote (car item))
       (symbol-listp (cadr item))))

(defund axe-bind-free-function-applicationp (expr)
  (declare (xargs :guard (pseudo-termp expr)))
  (and (consp expr)
       (symbolp (ffn-symb expr))
       (not (eq 'quote (ffn-symb expr)))
       (list-of-variables-and-constantsp (fargs expr))))

(defthm axe-bind-free-function-applicationp-forward-to-pseudo-term-listp-of-cdr
  (implies (axe-bind-free-function-applicationp expr)
           (pseudo-term-listp (cdr expr)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-bind-free-function-applicationp))))

(defthm axe-bind-free-function-applicationp-forward-to-list-of-variables-and-constantsp
  (implies (axe-bind-free-function-applicationp expr)
           (list-of-variables-and-constantsp (cdr expr)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-bind-free-function-applicationp))))

(defthm axe-bind-free-function-applicationp-forward-to-true-listp-of-cdr
  (implies (axe-bind-free-function-applicationp expr)
           (true-listp (cdr expr)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-bind-free-function-applicationp))))

(defthm axe-bind-free-function-applicationp-forward-to-true-listp
  (implies (axe-bind-free-function-applicationp expr)
           (true-listp expr))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-bind-free-function-applicationp))))

(defthm axe-bind-free-function-applicationp-forward-to-symbolp-of-car
  (implies (axe-bind-free-function-applicationp expr)
           (symbolp (car expr)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-bind-free-function-applicationp))))

(defthm axe-bind-free-function-applicationp-forward-to-consp
  (implies (axe-bind-free-function-applicationp expr)
           (consp expr))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-bind-free-function-applicationp))))

;;;
;;; axe-rule-hypp
;;;

;; An axe-rule-hyp (hypothesis of an axe rule) is an axe-syntaxp hyp, an
;; axe-bind-free hyp, or a lambda-free (currently) function call.  TODO:
;; Consider not expanding lambdas in hyps (if they don't have free vars?).
(defund axe-rule-hypp (hyp)
  (declare (xargs :guard t))
  (and (consp hyp)
       (let ((fn (ffn-symb hyp)))
         (and (not (eq 'quote fn))
              (if (eq 'axe-syntaxp fn) ;; (axe-syntaxp <expr>)
                  (and (= 1 (len (fargs hyp)))
                       (pseudo-termp (farg1 hyp))
                       (axe-syntaxp-exprp (farg1 hyp)))
                (if (eq 'axe-bind-free fn)
                    (and (= 2 (len (fargs hyp)))
                         (pseudo-termp (farg1 hyp))
                         (axe-bind-free-function-applicationp (farg1 hyp))
                         ;; This list of vars to bind is quoted when supplied by the user but is unquoted when we process the hyp
                         (symbol-listp (farg2 hyp)))
                  (and (pseudo-termp hyp)
                       (lambda-free-termp hyp))))))))

(defthm axe-rule-hypp-when-not-special
  (implies (and (consp hyp)
                (not (equal 'axe-syntaxp (car hyp)))
                (not (equal 'axe-bind-free (car hyp)))
                (not (equal 'quote (car hyp))))
           (equal (axe-rule-hypp hyp)
                  (and (pseudo-termp hyp)
                       (lambda-free-termp hyp))))
  :hints (("Goal" :in-theory (enable axe-rule-hypp)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0 0 0))))

(defthm axe-rule-hypp-when-equal-of-car-and-work-hard-cheap
  (implies (equal 'work-hard (car hyp))
           (equal (axe-rule-hypp hyp)
                  (and (pseudo-termp hyp)
                       (lambda-free-termp hyp))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable axe-rule-hypp))))

(defthm axe-rule-hypp-when-simple
  (implies (and (not (equal 'axe-syntaxp (car hyp)))
                (not (equal 'axe-bind-free (car hyp))))
           (equal (axe-rule-hypp hyp)
                  (and (consp hyp)
                       (not (equal 'quote (car hyp)))
                       (pseudo-termp hyp)
                       (lambda-free-termp hyp))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :hints (("Goal" :in-theory (enable axe-rule-hypp))))

(defthm axe-rule-hypp-when-axe-bind-free
  (implies (equal 'axe-bind-free (car hyp))
           (equal (axe-rule-hypp hyp)
                  (and (equal 2 (len (fargs hyp)))
                       (pseudo-termp (farg1 hyp))
                       (axe-bind-free-function-applicationp (farg1 hyp))
                       (symbol-listp (farg2 hyp)))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable axe-rule-hypp))))

;; Shows that an axe-rule-hyp must be a cons (and so can't be a symbol):
(thm
 (implies (axe-rule-hypp hyp)
          (and (consp hyp)
               (not (symbolp hyp))))
 :hints (("Goal" :in-theory (enable axe-rule-hypp))))

;; Shows that an axe-rule-hyp can't be a quoted constant:
(thm
 (implies (axe-rule-hypp hyp)
          (not (quotep hyp)))
 :hints (("Goal" :in-theory (enable axe-rule-hypp))))

;;;
;;; axe-rule-hyp-listp
;;;

(defun axe-rule-hyp-listp (hyps)
  (declare (xargs :guard t))
  (if (atom hyps)
      (null hyps)
    (and (axe-rule-hypp (first hyps))
         (axe-rule-hyp-listp (rest hyps)))))

(defthm axe-rule-hyp-listp-of-reverse-list
  (implies (axe-rule-hyp-listp acc)
           (axe-rule-hyp-listp (reverse-list acc)))
  :hints (("Goal" :in-theory (enable axe-rule-hyp-listp reverse-list))))

(defthm axe-rule-hyp-listp-of-append
  (equal (axe-rule-hyp-listp (append x y))
         (and (axe-rule-hyp-listp (true-list-fix x))
              (axe-rule-hyp-listp y)))
  :hints (("Goal" :in-theory (enable axe-rule-hyp-listp append))))

(defthm axe-rule-hyp-listp-of-cdr
  (implies (axe-rule-hyp-listp x)
           (axe-rule-hyp-listp (cdr x)))
  :hints (("Goal" :in-theory (enable axe-rule-hyp-listp))))

(defthm axe-rule-hyp-listp-forward-to-true-listp
  (implies (axe-rule-hyp-listp hyps)
           (true-listp hyps))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-rule-hyp-listp))))

;; We put this in when a hyp is bad (we also throw a hard error).  This hyp should never be able to be relieved.
(defstub bad-rule-hyp () t)

(defconst *unrelievable-hyp*
  '(bad-rule-hyp))

(defconst *unrelievable-hyps*
  (list *unrelievable-hyp*))

(defund-inline rule-lhs (axe-rule)
  (declare (xargs :guard (equal 4 (len axe-rule))))
  (first axe-rule))

(defund-inline rule-rhs (axe-rule)
  (declare (xargs :guard (equal 4 (len axe-rule))))
  (second axe-rule))

(defund-inline rule-symbol (axe-rule)
  (declare (xargs :guard (equal 4 (len axe-rule))))
  (third axe-rule))

(defund-inline rule-hyps (axe-rule)
  (declare (xargs :guard (equal 4 (len axe-rule))))
  (fourth axe-rule))

;;;
;;; axe-rule-lhsp
;;;

;; The LHS of an Axe rule is a lambda-free pseudo-term that is not a function
;; call (i.e., not a variable or constant)..
(defund axe-rule-lhsp (lhs)
  (declare (xargs :guard t))
  (and (pseudo-termp lhs)
       (lambda-free-termp lhs)
       (consp lhs)
       (not (eq 'quote (ffn-symb lhs)))))

(defthm axe-rule-lhsp-forward-to-pseudo-termp
  (implies (axe-rule-lhsp lhs)
           (pseudo-termp lhs))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-rule-lhsp))))

(defthm axe-rule-lhsp-forward-to-consp
  (implies (axe-rule-lhsp lhs)
           (consp lhs))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-rule-lhsp))))

(defthm axe-rule-lhsp-of-cons
  (equal (axe-rule-lhsp (cons fn args))
         (and (symbolp fn)
              (not (equal 'quote fn))
              (pseudo-term-listp args)
              (lambda-free-termsp args)))
  :hints (("Goal" :in-theory (enable axe-rule-lhsp))))


;;;
;;; axe-rulep
;;;

;; An axe-rule is a 4-tuple containing: LHS, RHS, rule name ("rule-symbol"), and hyps.
;; See also stored-axe-rulep.
(defund axe-rulep (item)
  (declare (xargs :guard t))
  (and (equal 4 (len item))
       (symbolp (rule-symbol item))
       (let ((lhs (rule-lhs item)))
         (and (axe-rule-lhsp lhs)))
       (let ((rhs (rule-rhs item))) ;todo: require no free vars (that is checked in make-axe-rule)
         (pseudo-termp rhs))
       (let ((hyps (rule-hyps item)))
         (axe-rule-hyp-listp hyps))))
