; certify with cert.pl -a acl2s
; If acl2s is not in your path, provide the full path above.


(in-package "ACL2S")

(include-book "kestrel/utilities/er-soft-plus" :dir :system)

#|
Author: Pete Manolios
Date: 5/19/2020

This file has code for generating induction schemes and also uses
defdata to turn pseudo-termp into a type.  Some of this may wind up
making it into ACL2s.

Here is the definition of a pseudo-termp and a pseudo-term-listp.

(mutual-recursion
 (defun pseudo-termp (x)
   (declare (xargs :guard t :mode :logic))
   (cond ((atom x) (symbolp x))
         ((eq (car x) 'quote)
          (and (consp (cdr x))
               (null (cdr (cdr x)))))
         ((not (true-listp x)) nil)
         ((not (pseudo-term-listp (cdr x)))
          nil)
         (t (or (symbolp (car x))
                (and (true-listp (car x))
                     (equal (length (car x)) 3)
                     (eq (car (car x)) 'lambda)
                     (symbol-listp (cadr (car x)))
                     (pseudo-termp (caddr (car x)))
                     (equal (length (cadr (car x)))
                            (length (cdr x))))))))
 (defun pseudo-term-listp (lst)
   (declare (xargs :guard t))
   (cond ((atom lst) (equal lst nil))
         (t (and (pseudo-termp (car lst))
                 (pseudo-term-listp (cdr lst)))))))
|#

(check= (pseudo-termp
         '((lambda (x y z) (app x y z)) '(1 2) a b))
        t)

(check= (pseudo-termp
         '((lambda (x y z) (app x y z)) '(1 2) b))
        nil)

(definec non-quote-symbolp (x :all) :bool
  (and (symbolp x)
       (!= x 'quote)))

(register-type non-quote-symbol
  :predicate non-quote-symbolp
  :enumerator nth-symbol)

(defdata 
  (pterm1 (or symbol 
              quote 
              (cons non-quote-symbol lo-pterm1)
              (cons (list 'lambda symbol-list pterm1) 
                    lo-pterm1)))
  (lo-pterm1 (listof pterm1)))

(register-type pseudo-term
  :predicate pseudo-termp
  :enumerator nth-pterm1)

(defdata lo-pterm (listof pseudo-term))
(defdata lo-lo-pterm (listof lo-pterm))

(local
  (defthm lo-pterm=pseudo-term-list
    (== (lo-ptermp x)
        (pseudo-term-listp x))
    :rule-classes 
    ((:forward-chaining 
      :trigger-terms ((lo-ptermp x) 
                      (pseudo-term-listp x))))))

(local
  (defthm lo-lo-pterm=pseudo-term-list-list
    (== (lo-lo-ptermp x)
        (acl2::pseudo-term-list-listp x))
    :rule-classes 
    ((:forward-chaining 
      :trigger-terms ((lo-lo-ptermp x) 
                      (acl2::pseudo-term-list-listp x))))))

(local
  (defdata-subtype-strict symbol-list lo-pterm1))

(local
  (defdata-subtype-strict symbol-list lo-pterm))

(defun pterm-induct (x)
  (if (pseudo-termp x)
      (cond ((atom x) x)
            ((quotep x) (pterm-induct (cdr x)))
            ((non-quote-symbolp (car x)) (pterm-induct (cdr x)))
            ((and (equal (caar x) 'lambda)
                  (symbol-listp (cadr (car x)))
                  (pseudo-termp (caddr (car x)))
                  (equal (len (cadr (car x)))
                         (len (cdr x))))
             (list (pterm-induct (cdr x))
                   (pterm-induct (caddr (car x)))))
            (t  (pterm-induct (cdr x))))
    (if (atom x) x
      (list (pterm-induct (car x))
            (pterm-induct (cdr x))))))

(local
  (defthm pseudo-termp=>ptermp1
    (and (=> (pseudo-termp x) (pterm1p x))
         (=> (pseudo-term-listp x) (lo-pterm1p x)))
    :hints (("goal" :induct (pterm-induct x)))))

(definecd neg (exp :pseudo-term) :pseudo-term
  (if (and (consp exp)
           (equal (car exp) 'not))
      (second exp)
    `(not ,exp)))

(check= (neg '(not (== (app x y) (app y x))))
        '(== (app x y) (app y x)))
        
(check= (neg '(== (app x y) (app y x)))
        '(not (== (app x y) (app y x))))

(definecd neglist (exp :lo-pterm) :lo-pterm
  (if (endp exp)
      nil
    (cons (neg (car exp))
          (neglist (cdr exp)))))

(check= (neglist '((not (== (app x y) (app y x)))
                   (== (app x y) (app y x))))
        '((== (app x y) (app y x))
          (not (== (app x y) (app y x)))))

(local
  (defthm pseudo-term-list-with-take
    (=> (pseudo-term-listp l)
        (pseudo-term-listp (take n l)))
    :hints (("Goal" :in-theory (enable take)
             :induct (take n l)))))

(definecd termify-clause (clause :lo-pterm) :pseudo-term
  (cond ((endp clause) nil)
        ((endp (cdr clause)) (car clause))
        ((endp (cddr clause)) 
         `(implies ,(neg (car clause))
                   ,(cadr clause)))
        (t `(implies (and ,@(neglist (butlast clause 1)))
                     ,(car (last clause))))))

(check= (termify-clause nil)
        nil)

(check= (termify-clause '((in a x)))
        '(in a x))

(check= (termify-clause '((not (in a x)) (in a y)))
        '(implies (in a x) (in a y)))

(check= (termify-clause '((not (in a x)) (not (in a z)) (in a (app u y))))
        '(implies (and (in a x) (in a z)) (in a (app u y))))

(definecd termify-clauses (clauses :lo-lo-pterm) :lo-pterm
  (if (endp clauses)
      nil
    (cons (termify-clause (car clauses))
          (termify-clauses (cdr clauses)))))

(check= (termify-clauses '(nil
                           ((in a x))
                           ((not (in a x)) (in a y))
                           ((not (in a x)) (not (in a z)) (in a (app u y)))))
        '(nil
          (in a x)
          (implies (in a x) (in a y))
          (implies (and (in a x) (in a z)) (in a (app u y)))))

(defmacro fmx-str (str &rest args)
  (declare (xargs :guard (<= (length args) 10)))
  `(fms-to-string ,str
         ,(make-fmt-bindings '(#\0 #\1 #\2 #\3 #\4
                               #\5 #\6 #\7 #\8 #\9)
                             args)))


(defmacro ind-err (val msg &rest params)
  `(acl2::er-soft+ 'induction t (list ,val (fmx-str ,msg ,@params)) ,msg ,@params))

(defun induction-proof-obligations (conjecture induction-scheme state)
  (declare (xargs :mode :program
                  :stobjs state
                  :guard (and ;; (pseudo-termp conjecture)
                          ;; What we want is something that after
                          ;; translation is a pseudo-termp, and we
                          ;; check for that below
                              (consp induction-scheme)
                              (symbol-listp induction-scheme)
                              (boundp-global 'gag-mode state))))
  (b* (((unless (no-duplicatesp (cdr induction-scheme)))
        (ind-err :duplicate-variables
                        "~%Your induction scheme, ~x0, has duplicates variables.~
                    ~%This is not allowed." induction-scheme))
       (wrld (w state))
       (fn0 (car induction-scheme))
       (mtbl (table-alist 'acl2::macro-aliases-table wrld))
       
       (fn (if (acl2::function-namep fn0 wrld) fn0
             (get-alist fn0 mtbl)))
       ((unless fn)
        (ind-err :undefined "~%~x0 is undefined." fn0))
       ((when (and (== fn fn0) (not (acl2::recursivep fn nil wrld))))
        (ind-err :non-recursive "~%~x0 is not a recursive function." fn))
       ((unless (acl2::recursivep fn nil wrld))
        (ind-err :non-recursive-alias "~%~x0 is an alias for ~x1, which is not a recursive function." fn0 fn))
       (formals (formals fn wrld))
       (scheme-args (cdr induction-scheme))
       ((unless (= (len scheme-args) (len formals)))
        (ind-err :incorrect-number-of-arguments
                  "~%~x0 takes ~x1 arguments, but you provided ~x2 arguments: ~x3."
                  fn (len formals) (len scheme-args) scheme-args))
       
       (machine (getpropc fn 'induction-machine nil wrld))
       (quick-block-info
        (getpropc fn 'acl2::quick-block-info
                  '(:error "Quick-Block-Info missing.") wrld))
       (justification 
        (getpropc fn 'acl2::justification
                  '(:error "Justification missing.")  wrld))
       (mask (acl2::sound-induction-principle-mask
              induction-scheme formals quick-block-info
              (access acl2::justification justification :subset)))

       ((er tconjecture) (acl2::translate conjecture t t t 'ctx wrld state))
       (clauses (list (list tconjecture)))
       (cl-set (acl2::remove-guard-holders-lst-lst clauses wrld))
       (ta-lst (acl2::tests-and-alists-lst
                (pairlis$ formals scheme-args) scheme-args mask machine))
       (induct-formula
        ;; the signature for this changed in ACL2 commit 3c7c671f64ac61907f01f0446059ad88e082712c
        (acl2::induction-formula 
         (list (list (acl2::termify-clause-set cl-set)))
         induction-scheme ;; induction term
         :all ;; see the comment on select-do$-induction-q in induct.lisp - this is only relevant if doing a do$ induction
         nil ;; measure-term, which is only relevant if doing a do$ induction
         ta-lst))
       (t-formula (termify-clauses induct-formula))
       (u-formula (acl2::untranslate-lst t-formula t wrld)))
    (value u-formula)))


(must-succeed
 (induction-proof-obligations '(=> (in b l) (in b l)) '(in b l) state))

; duplicate variables in induction scheme
(must-fail
 (induction-proof-obligations '(=> (in b l) (in b l)) '(in b b) state)
 :expected :soft)

; in2 is undefined
(must-fail
 (induction-proof-obligations '(=> (in2 b l) (in2 b l)) '(in2 b l) state)
 :expected :soft)

(must-succeed
 (induction-proof-obligations '(=> (and (tlp x) (tlp y) (tlp z))
                                   (== (app (app x y) z)
                                       (app x (app y z))))
                              '(append x y)
                              state))

; wrong number of arguments in induction-scheme for in, which takes 2 arguments
(must-fail
 (induction-proof-obligations '(=> (in b l) (in b l)) '(in b) state)
 :expected :soft)

; wrong number of arguments in conjecture for in, which takes 2 arguments
(must-fail
 (induction-proof-obligations '(=> (in b l) (in a b l)) '(in b l) state))

; bin-app is not recursive
(must-fail
 (induction-proof-obligations '(=> (and (tlp x) (tlp y) (tlp z))
                                   (== (app (app x y) z)
                                       (app x (app y z))))
                              '(bin-app x y)
                              state)
 :expected :soft)

; app is a macro alias for bin-app, which is not recursive
(must-fail
 (induction-proof-obligations '(=> (and (tlp x) (tlp y) (tlp z))
                                   (== (app (app x y) z)
                                       (app x (app y z))))
                              '(app x y)
                              state)
 :expected :soft)

(must-succeed
 (induction-proof-obligations '(=> (and (tlp x) (tlp y) (tlp z))
                                   (== (app (app x y) z)
                                       (app x (app y z))))
                              '(tlp x)
                              state))

; (+ n 1) is not a pseudo-term, but we use translate so that's OK
(must-succeed
 (induction-proof-obligations '(implies (natp n)
                                        (= (* n m) (/ (* n (+ n 1)) 2)))
                              '(tlp n)
                              state))

(in-theory (disable lo-ptermp pseudo-termp lo-lo-ptermp-implies-tlp))
