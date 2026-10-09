; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "hol")

(defconst *hol-arities*

; Warning: Keep this in sync with *hol-symbols* in package.lsp.

  '((equal . 2)
    (hp-comma . 2)
    (hp-none . 1)
    (hp-some . 1)
    (hp-nil . 1)
    (hp-cons . 2)
    (hp+ . 2)
    (hp* . 2)
    (hp-implies . 2)
    (hp-and . 2)
    (hp-or . 2)
    (hp= . 2)
    (hp< . 2)
    (hp-not . 1)
    (hp-forall . 1)
    (hp-exists . 1)
    (hp-true . 0)
    (hp-false . 0)))

(mutual-recursion

(defun hol-typep+ (type hta-arities arrow*-okp)

; This function defines our representation of hol types.

  (declare (xargs :guard (symbol-alistp hta-arities)))
  (cond
   ((atom type) (and (symbolp type)
                     (if (keywordp type)
                         (equal (cdr (assoc-eq type hta-arities))
                                0)
                       t)))
   ((true-listp type)
    (case (car type)
      (:arrow*
       (and arrow*-okp
            (hol-type-listp+ (cdr type) hta-arities t)))
      (typ (and (= (length type) 2)
                (hol-typep+ (nth 1 type) hta-arities t)))
      (otherwise
       (let* ((pair (assoc-eq (car type) hta-arities))
              (arity (cdr pair)))
         (and (equal (length (cdr type)) arity)
              (hol-type-listp+ (cdr type) hta-arities arrow*-okp))))))
   (t nil)))

(defun hol-type-listp+ (lst hta-arities arrow-okp)
  (declare (xargs :guard (and (symbol-alistp hta-arities)
                              (true-listp lst))))
  (cond ((endp lst) t)
        (t (and (hol-typep+ (car lst) hta-arities arrow-okp)
                (hol-type-listp+ (cdr lst) hta-arities arrow-okp)))))
)

(defun fn-type-symbolp (sym)
  (declare (xargs :guard t))
  (and (symbolp sym)
       (string-suffixp "$TYPE" (symbol-name sym))))

(mutual-recursion

(defun hol-termp-rec (x hta-arities fns vars arities typed-fns)

; This function recognizes when x is a term in a given context, defined as
; follows.  hta-arities is the list of known types, which are keywords that
; might include :num and :bool for example, paired with their arities.  Fn-list
; is the list of function symbols currently being defined, as in the :fns
; argument of defhol (see theories.lisp and any calls of defhol).  Vars is a
; list of variables (non-keyword symbols), which may be nil or may be from the
; first argument of a :forall call in a term provided to defhol.  Arities is an
; alist mapping function symbols to their arities, typically *hol-arities*.
; Typed-fns is the value of the :typed-fns field of the :hol-theory table,
; which is a list of doublets mapping known function symbols translated from
; HOL to their types, which may have variables (i.e., need not be ground types)
; and may use the abbreviation, arrow*.

  (declare (xargs :guard (and (symbol-alistp hta-arities)
                              (symbol-listp fns)
                              (symbol-listp vars)
                              (symbol-alistp arities)
                              (symbol-alistp typed-fns))))
  (cond ((atom x) (member-eq x vars))
        ((eq (car x) 'hp-num)
         (and (consp (cdr x))
              (natp (cadr x))
              (null (cddr x))))
        ((eq (car x) 'hp-bool)
         (and (consp (cdr x))
              (booleanp (cadr x))
              (null (cddr x))))
        ((eq (car x) 'hap*)
         (hol-term-listp (cdr x) hta-arities fns vars arities typed-fns))
        ((or (member-eq (car x) fns)
             (member-eq (car x) '(hp-none hp-nil)))
         (and (consp (cdr x))
              (null (cddr x))
              (let ((arg (cadr x)))
                (case-match arg
                  (('typ tp)
                   (hol-typep+ tp hta-arities t))
                  (& nil)))))
        (t (let* ((pair (assoc-eq (car x) arities))
                  (pair2 (and (null pair) ; optimization
                              (assoc-eq (car x) typed-fns))))
             (cond (pair2
                    (and (consp (cdr x))
                         (null (cddr x))
                         (hol-typep+ (cadr x) hta-arities nil)))
                   ((null pair) nil)
                   (t
                    (and (eql (cdr pair) (len (cdr x)))
                         (hol-term-listp (cdr x) hta-arities fns vars
                                         arities typed-fns))))))))

(defun hol-term-listp (lst hta-arities fns vars arities typed-fns)
  (declare (xargs :guard (and (symbol-alistp hta-arities)
                              (symbol-listp fns)
                              (symbol-listp vars)
                              (symbol-alistp arities)
                              (symbol-alistp typed-fns))))
  (cond
   ((atom lst) (null lst))
   (t (and (hol-termp-rec (car lst) hta-arities fns vars arities typed-fns)
           (hol-term-listp (cdr lst) hta-arities fns vars arities typed-fns)))))
)

(defun hol-termp (x hta-arities fns vars wrld)
  (declare (xargs
            :guard
            (and (symbol-listp fns)
                 (symbol-alistp hta-arities)
                 (symbol-listp vars)
                 (plist-worldp wrld)
                 (symbol-alistp (cdr (hons-assoc-equal
                                      :typed-fns
                                      (table-alist :hol-theory wrld)))))))
  (hol-termp-rec x hta-arities fns vars *hol-arities*
                 (cdr (hons-assoc-equal :typed-fns
                                        (table-alist :hol-theory wrld)))))
