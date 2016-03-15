;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with this software


;; SMT-extract extracts the declarations, hypotheses and conclusion from a SMT formula in ACL2.
;; A typical SMT formula is in below format:
;; (implies (and <decl-list>
;;               <hypo-list>)
;;          <concl-list>)

(in-package "ACL2")
(include-book "./helper")
(include-book "std/util/bstar" :dir :system)
(program)

;; get-orig-param
(defun get-orig-param (decl-list)
  "get-orig-param: given a declaration list of a SMT formula, return a list of variables appearing in the declaration list"
  (if (endp decl-list) nil
      (cons (cadar decl-list) (get-orig-param (cdr decl-list)))))

(defun extract-is-decl (expr)
  (if (and (equal (len expr) 2)        ; a declaration
           (member (car expr) (list 'booleanp 'integerp 'rationalp))
           (and (symbolp (cadr expr)) (cadr expr)))
      t
    nil))


(mutual-recursion
(defun extract-disjunct (term)
  ;; looking for (typep var) where var *not* satisfying typep make term trivially true
  (cond ( (and (equal (car term) 'if) (equal (caddr term) ''t))
          (b* (((mv decl1 term1) (extract-disjunct (cadr term)))
               ((mv decl2 term2) (extract-disjunct (cadddr term))))
              (mv (append decl1 decl2)
                  (cond ((or (equal term1 ''t) (equal term2 ''t)) ''t)
                        ((equal term1 ''nil) term2)
                        ((equal term2 ''nil) term1)
                        (t `(if ,term1 't ,term2))))))
        ( (equal (car term) 'not)
          (b* (((mv decl0 term0) (extract-conjunct (cadr term))))
              (mv decl0
                  (cond ((equal term0 ''nil) ''t)
                        ((equal term0 ''t)   ''nil)
                        (t `(not ,term0))))))
        ( (equal (car term) 'implies)
          (b* (((mv decl1 term1) (extract-conjunct (cadr term)))
               ((mv decl2 term2) (extract-disjunct (caddr term))))
              (mv (append decl1 decl2)
                  (cond ((or (equal term1 ''nil) (equal term2 ''t)) ''t)
                        ((equal term1 ''t) term2)
                        ((equal term2 ''nil) `(not ,term1))
                        (t `(implies ,term1 ,term2))))))
        ( t (mv nil term))))

(defun extract-conjunct (term)
  ;; looking for (typep var) where var *not* satisfying typep make term trivially false
  (cond ( (and (equal (car term) 'if) (equal (cadddr term) ''nil))
          (b* (((mv decl1 term1) (extract-conjunct (cadr term)))
               ((mv decl2 term2) (extract-conjunct (caddr term))))
              (mv (append decl1 decl2)
                  (cond ((or (equal term1 ''nil) (equal term2 ''nil)) ''nil)
                        ((equal term1 ''t) term2)
                        ((equal term2 ''t) term1)
                        (t `(if ,term1 ,term2 'nil))))))
        ( (equal (car term) 'not)
          (b* (((mv decl0 term0) (extract-disjunct (cadr term))))
              (mv decl0
                  (cond ((equal term0 ''nil) ''t)
                        ((equal term0 ''t)   ''nil)
                        (t `(not ,term0))))))
        ( (extract-is-decl term)
          (mv (list term) ''t))
        ( t (mv nil term))))
)

;; Notes:
;;   How do we identify the "conclusion" from a list of hypotheses?
;;     note-note: Mark's RewriteExpt uses the hypothesis list to figure out
;;       which transformations can be applied.
;;     note-note-yan: Yan's returned clauses also depend on knowing the
;;       corresonding hypothesis.
;;     1:  Maybe we can just use the last disjunct as the conclusion?
;;     2:  Maybe we measure the size of each expression tree and assume that
;;           the largest is the conclusion?
;;     3:  Maybe we could add a function (defun conclusion (x) x), and
;;           recognized (conclusion concl) as indicating the conclusion?
;;     4:  Maybe Yan will have a better idea.

;; SMT-extract
(defun SMT-extract (term)
  (b*
   (((mv decl-list hypo-and-concl) (extract-disjunct term)))
   (prog2$ (cw "decl-list:~q0~%hypo-and-concl:~q1~%" decl-list hypo-and-concl)
           (mv decl-list (cadr hypo-and-concl) (caddr hypo-and-concl)))))


