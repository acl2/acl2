; Utilities for manipulating terms
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

(include-book "forms") ;for farg1, etc.
(include-book "kestrel/alists-light/lookup" :dir :system)
(include-book "substitution")
(include-book "symbol-term-alistp")
(include-book "expand-lambdas-in-term")
(include-book "tools/flag" :dir :system)
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/add-to-set-equal" :dir :system))
(local (include-book "kestrel/alists-light/pairlis-dollar" :dir :system))

;todo: use list fix to combine these into a nice rule?

(defthm pseudo-termp-of-lookup-equal-when-symbol-term-alistp
  (implies (and (symbol-term-alistp subst)
;                (assoc-equal term subst)
                )
           (pseudo-termp (lookup-equal term subst)))
  :hints (("Goal" :in-theory (enable symbol-term-alistp))))

(defthm pseudo-term-listp-of-append1
  (implies (true-listp l1)
           (equal (pseudo-term-listp (append l1 l2))
                  (and (pseudo-term-listp l2)
                       (pseudo-term-listp l1)))))

(defthm pseudo-term-listp-of-append2
  (implies (and (pseudo-term-listp x)
                (pseudo-term-listp y))
           (pseudo-term-listp (append x y)))
  :hints (("Goal" :in-theory (enable append pseudo-term-listp))))


;dups (but some of these are now guard verified)

;I guess this works for lambdas too, since they must be complete (i.e., the lambda formals must include all vars that are free in the lambda body)
;TODO: Compare to all-vars1
(mutual-recursion
 (defund get-vars-from-term-aux (term acc)
   (declare (xargs :guard (and (true-listp acc)
                               (pseudo-termp term))
                   :verify-guards nil ;;done below
                   ))
   (if (atom term)
       (add-to-set-eq term acc)
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           acc
         (get-vars-from-terms-aux (fargs term) acc)))))

 (defund get-vars-from-terms-aux (terms acc)
   (declare (xargs :guard (and (true-listp acc)
                               (true-listp terms)
                               (pseudo-term-listp terms))))
   (if (endp terms)
       acc
     (get-vars-from-terms-aux (cdr terms)
                          (get-vars-from-term-aux (car terms) acc)))))

(make-flag get-vars-from-term-aux)

(defthm-flag-get-vars-from-term-aux
  (defthm true-listp-of-get-vars-from-term-aux
    (implies (true-listp acc)
             (true-listp (get-vars-from-term-aux term acc)))
    :flag get-vars-from-term-aux)
  (defthm true-listp-of-get-vars-from-terms-aux
    (implies (true-listp acc)
             (true-listp (get-vars-from-terms-aux terms acc)))
    :flag get-vars-from-terms-aux)
  :hints (("Goal" :in-theory (enable get-vars-from-term-aux get-vars-from-terms-aux))))

(verify-guards get-vars-from-term-aux)

(defun get-vars-from-term (term)
  (declare (xargs :guard (pseudo-termp term)))
  (get-vars-from-term-aux term nil))

(defun get-vars-from-terms (terms)
  (declare (xargs :guard (pseudo-term-listp terms)))
  (get-vars-from-terms-aux terms nil))

(defthm-flag-get-vars-from-term-aux
  (defthm symbol-listp-of-get-vars-from-term-aux
    (implies (and (pseudo-termp term)
                  (symbol-listp acc))
             (symbol-listp (get-vars-from-term-aux term acc)))
    :flag get-vars-from-term-aux)
  (defthm symbol-listp-of-get-vars-from-terms-aux
    (implies (and (pseudo-term-listp terms)
                  (symbol-listp acc))
             (symbol-listp (get-vars-from-terms-aux terms acc)))
    :flag get-vars-from-terms-aux)
  :hints (("Goal" :in-theory (enable get-vars-from-term-aux get-vars-from-terms-aux))))

(defthm symbol-listp-of-get-vars-from-terms
  (implies (pseudo-term-listp terms)
           (symbol-listp (get-vars-from-terms terms)))
  :hints (("Goal" :in-theory (enable get-vars-from-terms))))

(defthm symbol-listp-of-get-vars-from-term
  (implies (pseudo-termp term)
           (symbol-listp (get-vars-from-term term)))
  :hints (("Goal" :in-theory (enable get-vars-from-term))))

(defthm true-listp-of-get-vars-from-terms
  (implies (pseudo-term-listp terms)
           (true-listp (get-vars-from-terms terms)))
  :hints (("Goal" :in-theory (enable get-vars-from-terms))))

(defthm true-listp-of-get-vars-from-term
  (implies (pseudo-termp term)
           (true-listp (get-vars-from-term term)))
  :hints (("Goal" :in-theory (enable get-vars-from-term))))

;recognize an alist from pseudo-terms to pseudo-terms
(defun pseudo-term-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (equal alist nil)
    (let ((pair (first alist)))
      (and (consp pair)
           (let* ((key (car pair))
                  (val (cdr pair)))
             (and (pseudo-termp key)
                  (pseudo-termp val)
                  (pseudo-term-alistp (rest alist))))))))

(defthmd alistp-when-pseudo-term-alistp
  (implies (pseudo-term-alistp alist)
           (alistp alist)))

(defthm alistp-when-pseudo-term-alistp-cheap
  (implies (pseudo-term-alistp alist)
           (alistp alist))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;;drop any pair in ALIST whose car mentions any of the variables in VARS
(defun drop-pairs-that-mention-vars (alist vars)
  (declare (xargs :guard (and (pseudo-term-alistp alist)
                              (symbol-listp vars))))
  (if (endp alist)
      nil
    (let* ((pair (first alist))
           (key (car pair))
           (val (cdr pair)))
      (if (or (intersection-eq (get-vars-from-term key) vars)
              (intersection-eq (get-vars-from-term val) vars)) ;todo: do we want this check?  if not, we can simplify this routine
          (drop-pairs-that-mention-vars (rest alist) vars) ;drop the pair
        (cons pair (drop-pairs-that-mention-vars (rest alist) vars))))))

(defthm pseudo-term-alistp-of-drop-pairs-that-mention-vars
  (implies (pseudo-term-alistp alist)
           (pseudo-term-alistp (drop-pairs-that-mention-vars alist vars))))


(defun vars-not-bound-to-themselves (formals actuals)
  (declare (xargs :guard (and (symbol-listp formals)
                              (true-listp actuals)
                              )))
  (if (endp formals)
      nil
    (let ((formal (first formals))
          (actual (first actuals)))
      (if (eq formal actual)
          ;;drop it:
          (vars-not-bound-to-themselves (rest formals) (rest actuals))
        ;; not bound to self, so keep it:
        (cons formal (vars-not-bound-to-themselves (rest formals) (rest actuals)))))))

(defthm symbol-listp-of-vars-not-bound-to-themselves
  (implies (symbol-listp formals)
           (symbol-listp (vars-not-bound-to-themselves formals actuals))))

;move?
;TODO: Do we really want to dive inside lambdas?
(mutual-recursion
 (defun replace-in-term (term alist)
   (declare (xargs :guard (and (pseudo-termp term)
                               (pseudo-term-alistp alist))
                   :guard-hints (("Goal" :in-theory (enable PSEUDO-TERMP)))))
   (let* ((match (assoc-equal term alist)))
     (if match
         (cdr match) ;could recur on this...
       (if (atom term)
           term
         (if (quotep term)
             term
           (cons (if (consp (ffn-symb term))
                     (let ((formals (farg1 (ffn-symb term)))
                           (body (farg2 (ffn-symb term))))
                       `(lambda ,formals
                          ;;since lambda formals are often bound to themselves (because the lambdas are complete) - we remove such self-bound vars from the list of formals here (they can't shadow anything)
                          ,(replace-in-term body (drop-pairs-that-mention-vars alist (vars-not-bound-to-themselves formals (fargs term)))))) ;must remove any pairs that are interfered with by the lambda vars...
                   ;;not a lambda:
                   (ffn-symb term))
                 (replace-in-terms (fargs term) alist)))))))

 (defun replace-in-terms (terms alist)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (pseudo-term-alistp alist))
                   :guard-hints (("Goal" :in-theory (enable PSEUDO-TERMP)))))
   (if (endp terms)
       nil
     (cons (replace-in-term (car terms) alist)
           (replace-in-terms (cdr terms) alist)))))

;drop any term in TERMS that mentions any of the variables in VARS
(defun drop-terms-that-mention-vars (terms vars)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (symbol-listp vars))))
  (if (endp terms)
      nil
    (let ((term (first terms)))
      (if (intersection-eq (get-vars-from-term term) vars)
          (drop-terms-that-mention-vars (rest terms) vars) ;drop the term
        (cons term (drop-terms-that-mention-vars (rest terms) vars))))))



;replace sym with its binding in the alist (if any).  otherwise, return sym
(defun replace-if-bound (sym alist)
   (declare (xargs :guard (and (symbolp sym)
                               (symbol-alistp alist))))
   (let ((res (assoc-eq sym alist)))
    (if res
        (cdr res)
      sym)))

;todo: guard could be (function-renamingp function-renaming)
;Rename all functions called in TERM that are mapped to new names by ALIST.
;; (RENAME-FNs  '(foo '1 (baz (foo x y))) '((foo . bar)))
;; This is similar to sublis-fn-lst-simple but does not evaluate ground terms for primitives, etc.
(mutual-recursion
 (defun rename-fns (term alist)
   (declare (xargs :guard (and (pseudo-termp term)
                               (symbol-alistp alist))))
   (if (variablep term)
       term
     (if (fquotep term)
         term
       ;;function call or lambda
       (let* ((fn (ffn-symb term))
              (fn (if (flambdap fn)
                      ;;if it's a lambda, replace calls in the body:
                      (let* ((lambda-formals (lambda-formals fn))
                             (lambda-body (lambda-body fn))
                             (new-lambda-body (rename-fns lambda-body alist))
                             (new-fn `(lambda ,lambda-formals ,new-lambda-body))) ;todo: use make-lambda here?
                        new-fn)
                    ;;if it's not a lambda:
                    (replace-if-bound fn alist))))
         (fcons-term fn (rename-fns-lst (fargs term) alist))))))

;Rename all functions called in TERMS according that are mapped to new names by ALIST.
 (defun rename-fns-lst (terms alist)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (symbol-alistp alist))))
   (if (endp terms)
       nil
     (cons (rename-fns (car terms) alist)
           (rename-fns-lst (cdr terms) alist)))))

;; Gather a list of all functions called in the term
;; Similar to ACL2 source function all-ffn-symbs.
(mutual-recursion
 (defun get-fns-in-term-aux (term acc)
   (declare (xargs :guard (and (true-listp acc)
                               (pseudo-termp term))
                   :verify-guards nil ;;done below
                   ))
   (if (variablep term)
       acc
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           acc
         (let ((acc (get-fns-in-terms-aux (fargs term) acc)))
           (if (consp fn) ;handle lambda
               (get-fns-in-term-aux (third fn) acc)
             (add-to-set-eq fn acc)))))))

 (defun get-fns-in-terms-aux (terms acc)
   (declare (xargs :guard (and (true-listp acc)
                               (true-listp terms)
                               (pseudo-term-listp terms))))
   (if (endp terms)
       acc
     (let* ((acc (get-fns-in-term-aux (first terms) acc))
            (acc (get-fns-in-terms-aux (rest terms) acc)))
       acc))))

(make-flag get-fns-in-term-aux)

(defthm-flag-get-fns-in-term-aux
  (defthm true-listp-of-get-fns-in-term-aux
    (implies (true-listp acc)
             (true-listp (get-fns-in-term-aux term acc)))
    :flag get-fns-in-term-aux)
  (defthm true-listp-of-get-fns-in-terms-aux
    (implies (true-listp acc)
             (true-listp (get-fns-in-terms-aux terms acc)))
    :flag get-fns-in-terms-aux))

(defthm pseudo-termp-of-lambda-body-cheap
  (implies (and (consp term)
                (consp (car term))
                (pseudo-termp term))
           (pseudo-termp (caddr term)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0 0)))
  :hints (("Goal" :expand ((pseudo-termp term)))))

(defthm-flag-get-fns-in-term-aux
  (defthm symbol-listp-of-get-fns-in-term-aux
    (implies (and (pseudo-termp term)
                  (symbol-listp acc))
             (symbol-listp (get-fns-in-term-aux term acc)))
    :flag get-fns-in-term-aux)
  (defthm symbol-listp-of-get-fns-in-terms-aux
    (implies (and (pseudo-term-listp terms)
                  (symbol-listp acc))
             (symbol-listp (get-fns-in-terms-aux terms acc)))
    :flag get-fns-in-terms-aux))

(verify-guards get-fns-in-term-aux :hints (("Goal" :expand ((PSEUDO-TERMP TERM)))))

(defund get-fns-in-term (term)
  (declare (xargs :guard (pseudo-termp term)))
  (get-fns-in-term-aux term nil))

(defthm symbol-listp-of-get-fns-in-term
  (implies (pseudo-termp term)
           (symbol-listp (get-fns-in-term term)))
  :hints (("Goal" :in-theory (enable get-fns-in-term))))

(defund get-fns-in-terms (terms)
  (declare (xargs :guard (pseudo-term-listp terms)))
  (get-fns-in-terms-aux terms nil))

(defthm symbol-listp-of-get-fns-in-terms
  (implies (pseudo-term-listp terms)
           (symbol-listp (get-fns-in-terms terms)))
  :hints (("Goal" :in-theory (enable get-fns-in-terms))))

(mutual-recursion
 (defun expr-calls-fn (fn expr)
   (declare (xargs :measure (acl2-count expr)
                   :guard (and (symbolp fn)
                               (pseudo-termp expr))))
   (cond ((variablep expr) nil)
         ((fquotep expr) nil)
         ;;lambda:
         ((consp (ffn-symb expr))
          (or (expr-calls-fn fn (third (ffn-symb expr))) ;lambda body
              (some-expr-calls-fn fn (fargs expr))))
         (t (or (eq fn (ffn-symb expr))
                (some-expr-calls-fn fn (fargs expr))))))

 (defun some-expr-calls-fn (fn exprs)
   (declare (xargs :measure (acl2-count exprs)
                   :guard (and (symbolp fn)
                               (pseudo-term-listp exprs))))
   (if (atom exprs)
       nil
     (or (expr-calls-fn fn (car exprs))
         (some-expr-calls-fn fn (cdr exprs))))))

;; (RENAME-FN 'foo 'bar '(foo '1 (baz (foo x y))))
(mutual-recursion
 (defun rename-fn (old-name new-name term)
   (declare (xargs :guard (and (pseudo-termp term))))
   (if (variablep term)
       term
     (if (fquotep term)
         term
       ;;function call or lambda
       (let* ((fn (ffn-symb term))
              (fn (if (consp fn)
                      ;;if it's a lambda, replace calls in the term:
                      (let* ((lambda-formals (second fn))
                             (lambda-term (third fn))
                             (new-lambda-term (rename-fn old-name new-name lambda-term))
                             (new-fn `(lambda ,lambda-formals ,new-lambda-term)))
                        new-fn)
                    ;;if it's not a lambda:
                    (if (eq fn old-name)
                        new-name
                      fn))))
         (cons fn (rename-fn-lst old-name new-name (fargs term)))))))

 (defun rename-fn-lst (old-name new-name term-lst)
   (declare (xargs :guard (and (pseudo-term-listp term-lst))))
   (if (endp term-lst)
       nil
     (cons (rename-fn old-name new-name (car term-lst))
           (rename-fn-lst old-name new-name (cdr term-lst))))))


;TODO: apparently lambdas can have declares! (e.g., (declare (ignore x)).  but not in pseudo-terms?!  think about this
;TODO: Just use pseudo-lambdap?
(defun lambda-exprp (expr)
  (declare (xargs :guard t))
  (and (eql 3 (len expr))
       (true-listp expr)
       (eq 'lambda (car expr))
       (symbol-listp (second expr))
       (pseudo-termp (car (last expr)))))

;todo: this must exist elsewhere
(defun my-lambda-applicationp (expr)
  (declare (xargs :guard t))
  (and (true-listp expr)
       (lambda-exprp (first expr))))

;returns a term with one level of lambda removed...
;fixme what if the body is also a lambda?
(defun beta-reduce (lambda-expr)
  (declare (xargs :guard (my-lambda-applicationp lambda-expr)))
  (let* ((lambda-part (first lambda-expr))
         (formals (second lambda-part))
         (body (car (last lambda-part))) ;previously we took the third part, but declares sometime intervene?
         (actuals (cdr lambda-expr)))
    (my-sublis-var (pairlis$ formals actuals)
                   body)))

;; where should this go?
;; Negate TERM by adding or removing a call of not (avoids double negation)
(defun negate-term (term)
  (declare (xargs :guard t ;(pseudo-termp term)
                  ))
  (if (and (call-of 'not term)
           (consp (cdr term)) ;for guards
           )
      (farg1 term) ;negation of (not x) is just x
    `(not ,term)))

(defthm pseudo-term-listp-when-symbol-listp-cheap
  (implies (symbol-listp x)
           (pseudo-term-listp x))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;see also version in axe/

; a pretty strong rule
(defthm pseudo-termp-of-cons-1
  (equal (pseudo-termp (cons a b))
         (if (eq 'quote a)
             (and (consp b)
                  (null (cdr b)))
           (if (symbolp a)
               (pseudo-term-listp b)
             (and (true-listp a)
                  (equal (length a) 3)
                  (eq (car a) 'lambda)
                  (symbol-listp (cadr a))
                  (pseudo-termp (caddr a))
                  (pseudo-term-listp b)
                  (equal (length (cadr a))
                         (length b))))))
  :hints (("Goal" :in-theory (enable pseudo-termp))))

(defthm pseudo-termp-car-last
  (implies (pseudo-term-listp term)
           (pseudo-termp (car (last term)))))




;; (thm
;;  (implies (natp n)
;;           (equal (take (+ 1 n) x)
;;                  (cons (car x)
;;                        (take n x))))
;;  :hints (("Goal" :expand (first-n-ac n x nil)
;;           :in-theory (enable take))))

(defthm strip-cdrs-of-pairlis$-when-lengths-equal
  (implies (equal (len x) (len y))
           (equal (strip-cdrs (pairlis$ x y))
                  (true-list-fix y))))

(defthm symbolp-of-car-of-expand-lambdas-in-term
  (implies (and (symbolp (car term))
                ;; (consp term)
                ;;(not (equal 'quote (car term)))
                )
           (symbolp (car (expand-lambdas-in-term term))))
  :hints (("Goal" :in-theory (enable expand-lambdas-in-term))))

(defthm consp-of-expand-lambdas-in-term
  (implies (and (symbolp (car term))
                (consp term)
                ;;(not (equal 'quote (car term)))
                )
           (consp (expand-lambdas-in-term term)))
  :hints (("Goal" :expand ((expand-lambdas-in-term term))
           :in-theory (enable expand-lambdas-in-term))))

(defthm not-equal-of-quore-and-car-of-expand-lambdas-in-term
  (implies (and (symbolp (car term))
                (consp term)
                (not (equal 'quote (car term)))
                )
           (not (equal 'quote (car (expand-lambdas-in-term term)))))
  :hints (("Goal" :expand ((expand-lambdas-in-term term))
           :in-theory (enable expand-lambdas-in-term))))

;;;
;;; fns-in-term
;;;

;; The result contains only symbols (no lambdas).
;; This version doesn't have an accumulator
(mutual-recursion
 (defun fns-in-term (term)
   (declare (xargs :guard (pseudo-termp term)
                   :verify-guards nil ;done below
                   ))
   (if (or (atom term)
           (fquotep term))
       nil
     (let ((fn (ffn-symb term)))
       (if (consp fn)
           (union-eq (fns-in-term (lambda-body fn))
                     (fns-in-terms (fargs term)))
         (add-to-set-eq fn
                        (fns-in-terms (fargs term)))))))
 (defun fns-in-terms (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       nil
     (union-eq (fns-in-term (first terms))
               (fns-in-terms (rest terms))))))

(make-flag fns-in-term)

(defthm-flag-fns-in-term
  (defthm symbol-listp-of-fns-in-term
    (implies (pseudo-termp term)
             (symbol-listp (fns-in-term term)))
    :flag fns-in-term)
  (defthm symbol-listp-of-fns-in-terms
    (implies (pseudo-term-listp terms)
             (symbol-listp (fns-in-terms terms)))
    :flag fns-in-terms))

(defthm-flag-fns-in-term
  (defthm true-listp-of-fns-in-term
    (true-listp (fns-in-term term))
    :flag fns-in-term)
  (defthm true-listp-of-fns-in-terms
    (true-listp (fns-in-terms terms))
    :flag fns-in-terms))

(verify-guards fns-in-term)

(defthm fns-in-terms-of-true-list-fix
  (equal (fns-in-terms (true-list-fix terms))
         (fns-in-terms terms)))

(defthm not-member-equal-of-fns-in-term-of-cdr-of-assoc-equal
  (implies (not (member-equal fn (fns-in-terms (strip-cdrs alist))))
           (not (member-equal fn (fns-in-term (cdr (assoc-equal form alist)))))))

(defthm-flag-my-sublis-var
  (defthm not-member-equal-of-fns-in-term-of-my-sublis-var
    (implies (and (not (member-equal fn (fns-in-term form)))
                  (not (member-equal fn (fns-in-terms (strip-cdrs alist))))
                  (pseudo-termp form))
             (not (member-equal fn (fns-in-term (my-sublis-var alist form)))))
    :flag my-sublis-var)
  (defthm not-member-equal-of-fns-in-term-of-my-sublis-var-lst
    (implies (and (not (member-equal fn (fns-in-terms l)))
                  (not (member-equal fn (fns-in-terms (strip-cdrs alist))))
                  (pseudo-term-listp l))
             (not (member-equal fn (fns-in-terms (my-sublis-var-lst alist l)))))
    :flag my-sublis-var-lst)
  :hints (("Goal" :expand ((FNS-IN-TERM (CONS (CAR FORM)
                                              (MY-SUBLIS-VAR-LST ALIST (CDR FORM)))))
           :in-theory (enable fns-in-term
                              my-sublis-var
                              my-sublis-var-lst))))

(defthm-flag-expand-lambdas-in-term
  (defthm not-member-equal-of-fns-in-term-of-expand-lambdas-in-term
    (implies (and (pseudo-termp term)
                  (not (member-equal fn (fns-in-term term))))
             (not (member-equal fn (fns-in-term (expand-lambdas-in-term term)))))
    :flag expand-lambdas-in-term)
  (defthm not-member-equal-of-fns-in-terms-of-expand-lambdas-in-terms
    (implies (and (pseudo-term-listp terms)
                  (not (member-equal fn (fns-in-terms terms))))
             (not (member-equal fn (fns-in-terms (expand-lambdas-in-terms terms)))))
    :flag expand-lambdas-in-terms)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable expand-lambdas-in-term
                              expand-lambdas-in-terms))))

;; (defthm-flag-expand-lambdas-in-term
;;   (defthm member-equal-of-fns-in-term-of-expand-lambdas-in-term
;;     (implies (and (pseudo-termp term)
;;                   (member-equal fn (fns-in-term term)))
;;              (member-equal fn (fns-in-term (expand-lambdas-in-term term))))
;;     :flag expand-lambdas-in-term)
;;   (defthm member-equal-of-fns-in-terms-of-expand-lambdas-in-terms
;;     (implies (and (pseudo-term-listp terms)
;;                   (member-equal fn (fns-in-terms terms)))
;;              (member-equal fn (fns-in-terms (expand-lambdas-in-terms terms))))
;;     :flag expand-lambdas-in-terms)
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable expand-lambdas-in-term
;;                               expand-lambdas-in-terms))))
