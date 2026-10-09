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

(defun hol-typep+ (type hta-keys arrow*-okp)

; This function defines our representation of hol types.

  (declare (xargs :guard (symbol-listp hta-keys)))
  (cond
   ((atom type) (and (symbolp type)
                     (if (keywordp type)
                         (member-eq type hta-keys)
                       t)))
   ((true-listp type)
    (case (car type)
      ((:arrow :hash)
       (and (= (length type) 3)
            (and (hol-typep+ (nth 1 type) hta-keys arrow*-okp)
                 (hol-typep+ (nth 2 type) hta-keys arrow*-okp))))
      ((:list :option)
       (and (= (length type) 2)
            (hol-typep+ (nth 1 type) hta-keys arrow*-okp)))
      (:arrow*
       (and arrow*-okp
            (hol-type-listp+ (cdr type) hta-keys)))
      (typ (and (= (length type) 2)
                (hol-typep+ (nth 1 type) hta-keys t)))
      (otherwise nil)))
   (t nil)))

(defun hol-type-listp+ (lst hta-keys)
  (declare (xargs :guard (and (symbol-listp hta-keys)
                              (true-listp lst))))
  (cond ((endp lst) t)
        (t (and (hol-typep+ (car lst) hta-keys t)
                (hol-type-listp+ (cdr lst) hta-keys)))))
)

(defun fn-type-symbolp (sym)
  (declare (xargs :guard t))
  (and (symbolp sym)
       (string-suffixp "$TYPE" (symbol-name sym))))

(mutual-recursion

(defun hol-termp-rec (x hta-keys fns vars arities typed-fns)

; This function recognizes when x is a term in a given context, defined as
; follows.  Hta-keys is the list of known atomic types, which are keywords that
; might include :num and :bool for example.  Fn-list is the list of function
; symbols currently being defined, as in the :fns argument of defhol (see
; theories.lisp and any calls of defhol).  Vars is a list of variables
; (non-keyword symbols), which may be nil or may be from the first argument of
; a :forall call in a term provided to defhol.  Arities is an alist mapping
; function symbols to their arities, typically *hol-arities*.  Typed-fns is the
; value of the :typed-fns field of the :hol-theory table, which is a list of
; doublets mapping known function symbols translated from HOL to their types,
; which may have variables (i.e., need not be ground types) and may use the
; abbreviation, arrow*.

  (declare (xargs :guard (and (symbol-listp hta-keys)
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
         (hol-term-listp (cdr x) hta-keys fns vars arities typed-fns))
        ((or (member-eq (car x) fns)
             (member-eq (car x) '(hp-none hp-nil)))
         (and (consp (cdr x))
              (null (cddr x))
              (let ((arg (cadr x)))
                (case-match arg
                  (('typ tp)
                   (hol-typep+ tp hta-keys t))
                  (& nil)))))
        (t (let* ((pair (assoc-eq (car x) arities))
                  (pair2 (and (null pair) ; optimization
                              (assoc-eq (car x) typed-fns))))
             (cond (pair2
                    (and (consp (cdr x))
                         (null (cddr x))
                         (hol-typep+ (cadr x) hta-keys nil)))
                   ((null pair) nil)
                   (t
                    (and (eql (cdr pair) (len (cdr x)))
                         (hol-term-listp (cdr x) hta-keys fns vars
                                         arities typed-fns))))))))

(defun hol-term-listp (lst hta-keys fns vars arities typed-fns)
  (declare (xargs :guard (and (symbol-listp hta-keys)
                              (symbol-listp fns)
                              (symbol-listp vars)
                              (symbol-alistp arities)
                              (symbol-alistp typed-fns))))
  (cond
   ((atom lst) (null lst))
   (t (and (hol-termp-rec (car lst) hta-keys fns vars arities typed-fns)
           (hol-term-listp (cdr lst) hta-keys fns vars arities typed-fns)))))
)

(defun hol-termp (x hta-keys fns vars wrld)
  (declare (xargs
            :guard
            (and (symbol-listp fns)
                 (symbol-listp hta-keys)
                 (symbol-listp vars)
                 (plist-worldp wrld)
                 (symbol-alistp (cdr (hons-assoc-equal
                                      :typed-fns
                                      (table-alist :hol-theory wrld)))))))
  (hol-termp-rec x hta-keys fns vars *hol-arities*
                 (cdr (hons-assoc-equal :typed-fns
                                        (table-alist :hol-theory wrld)))))
