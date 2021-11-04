; A more general variant of unifying a term and a DAG
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

;; A variant of unify-term-and-dag.lisp that passes through the dag-array-name
;; and so supports dag-arrays not named 'dag-array.

;keep in sync with the main one...
;; TODO: Make a -fast book like the one we made for the main version of this function (without -with-name).

(include-book "kestrel/utilities/forms" :dir :system)
(include-book "dag-arrays")
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

(mutual-recursion

;keep in sync with the main one...
 (defund unify-term-and-dag-with-name (term nodenum-or-quotep dag-array-name dag-array dag-len alist)
   (declare (xargs :guard (and (pseudo-termp term)
                               (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                               (or (myquotep nodenum-or-quotep)
                                   (and (natp nodenum-or-quotep)
                                        (< nodenum-or-quotep dag-len)))
                               (symbol-alistp alist))
                   :verify-guards nil ;done below
                   ))
   (if (consp term)
       ;; Term is a cons, so it's either a function call or a quoted constant:
       (let ((pat-fn (ffn-symb term)))
         (if (eq 'quote pat-fn)
             ;; Term is a quoted constant (the only thing that matches is that constant -- we are now inlining all constants)
             (if (and (consp nodenum-or-quotep) ;if it's a consp it must be a quotep (nodenums are integers)
                      (equal (unquote term) (unquote nodenum-or-quotep)))
                 alist
               :fail)

           ;; Term is a regular function call (the only thing that matches is a call to the same function with args that match)
           (if (consp nodenum-or-quotep) ;tests whether it's a quotep
               :fail ;can't unify a term that's a function call with an item that's a quoted constant (could add fancy support for this like acl2 has...)
             ;; The nodenum-or-quotep is a nodenum:
             (let ((item-expr (aref1 dag-array-name dag-array nodenum-or-quotep)))
               (if (call-of pat-fn item-expr) ;ffixme could we use 'eq here, or do we need to handle lambdas?
                   (unify-terms-and-dag-with-name (fargs term) (dargs item-expr) dag-array-name dag-array dag-len alist)
                 :fail)))))

     ;; Term is not a consp, so it must be a variable:
     (let ((previous-binding (assoc-eq term alist)))
       (if previous-binding
           ;; If there's a previous binding for the variable, it must match the current item:
           ;;( what if it was bound to a quotep and now we have the nodenum of the quotep - better to always inline?)
           (if (equal (cdr previous-binding) nodenum-or-quotep)
               alist
             :fail)

         ;; If there was no previous binding, make one now..
         (acons-fast term nodenum-or-quotep alist)))))


;keep in sync with the main one...
 (defund unify-terms-and-dag-with-name (terms nodenums-or-quoteps dag-array-name dag-array dag-len alist)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                               (and (true-listp nodenums-or-quoteps)
                                    (all-dargp-less-than nodenums-or-quoteps dag-len))
                               (symbol-alistp alist))
                   :verify-guards nil ;done below
                   ))
   (if (endp terms)
       ;;everything matched, so return the alist
       alist
     (if (consp nodenums-or-quoteps) ;for guards, could drop if we knew that all arities were consistent
         (let ((alist-or-fail (unify-term-and-dag-with-name (first terms) (first nodenums-or-quoteps) dag-array-name dag-array dag-len alist)))
           (if (eq :fail alist-or-fail)
               :fail
             (unify-terms-and-dag-with-name (rest terms) (rest nodenums-or-quoteps) dag-array-name dag-array dag-len alist-or-fail)))
       (prog2$ (er hard? 'unify-terms-and-dag-with-name "Arity mismatch.")
               :fail)))))

(make-flag unify-term-and-dag-with-name)

(defthm-flag-unify-term-and-dag-with-name
  (defthm symbol-alistp-of-unify-term-and-dag-with-name
    (implies (and (symbol-alistp alist)
                  (pseudo-termp term)
                  (not (equal :fail (unify-term-and-dag-with-name term nodenum-or-quotep dag-array-name dag-array dag-len alist))))
             (symbol-alistp (unify-term-and-dag-with-name term nodenum-or-quotep dag-array-name dag-array dag-len alist)))
    :flag unify-term-and-dag-with-name)
  (defthm symbol-alistp-of-unify-terms-and-dag-with-name
    (implies (and (symbol-alistp alist)
                  (pseudo-term-listp terms)
                  (not (equal :fail (unify-terms-and-dag-with-name terms nodenums-or-quoteps dag-array-name dag-array dag-len alist))))
             (symbol-alistp (unify-terms-and-dag-with-name terms nodenums-or-quoteps dag-array-name dag-array dag-len alist)))
    :flag unify-terms-and-dag-with-name)
  :hints (("Goal" :expand ((unify-terms-and-dag-with-name terms nodenums-or-quoteps dag-array-name dag-array dag-len alist)
                           (unify-terms-and-dag-with-name nil nodenums-or-quoteps dag-array-name dag-array dag-len alist)
                           (unify-term-and-dag-with-name term nodenum-or-quotep dag-array-name dag-array dag-len alist)
                           (unify-term-and-dag-with-name term (cdr (assoc-equal term alist)) dag-array-name dag-array dag-len alist)))))

(verify-guards unify-term-and-dag-with-name)

(mutual-recursion
 (defund term-skeleton-matches-dagp-with-name (term ;a tree with quoted constants and variables at the leaves (or a list of such iff lst-flag is true)
                                                     item ;a nodenum or quotep (or a list of such iff lst-flag is true)
                                                     dag-array-name dag-array)
   (declare (xargs :guard (and (pseudo-termp term)
                               (dargp item)
                               (if (natp item)
                                   (pseudo-dag-arrayp dag-array-name dag-array (+ 1 item))
                                 t))
                   :guard-hints (("Goal" :use (:instance symbolp-of-car-of-aref1 (nodenum item))
                                  :in-theory (disable symbolp-of-car-of-aref1)))))
   (if (consp term)
       ;; Term is a cons, so it's either a function call or a quoted constant:
       (let ((pat-fn (ffn-symb term)))
         (if (eq 'quote pat-fn)
             ;; Term is a quoted constant (the only thing that matches is that constant -- we are now inlining all constants)
             (and (consp item) ;if it's a consp it must be a quotep (nodenums are integers)
                  (equal (unquote term) (unquote item)))
           ;; Term is a regular function call (the only thing that matches is a call to the same function with args that match)
           (if (consp item) ;tests whether it's a quotep
               nil ;can't unify a term that's a function call with an item that's a quoted constant (could add fancy support for this like acl2 has...)
             ;; The item is a nodenum:
             (let ((item-expr (aref1 dag-array-name dag-array item)))
               (and (call-of pat-fn item-expr) ;ffixme could we use 'eq here, or do we need to handle lambdas?
                    (term-skeletons-match-dagp-with-name (fargs term) (dargs item-expr) dag-array-name dag-array))))))
     ;; Term is not a consp, so it must be a variable (this function always succeeds on variables - they will be checked later):
     t))

 (defund term-skeletons-match-dagp-with-name (terms ;a tree with quoted constants and variables at the leaves (or a list of such iff lst-flag is true)
                                                         items ;a nodenum or quotep (or a list of such iff lst-flag is true)
                                                         dag-array-name dag-array)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (all-dargp items)
                               (true-listp items)
                               (true-listp terms)
                               (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (largest-non-quotep items))))
                   :guard-hints (("Goal" :use (:instance symbolp-of-car-of-aref1 (nodenum items))
                                  :in-theory (disable symbolp-of-car-of-aref1)))))
   (if (endp terms)
       ;;everything matched:
       t
     (and (consp items) ;for guards, could drop if we knew that all arities were consistent
          (term-skeleton-matches-dagp-with-name (first terms) (first items) dag-array-name dag-array)
          (term-skeletons-match-dagp-with-name (rest terms) (rest items) dag-array-name dag-array)))))

;keep in sync with the main one...
(defun unify-term-and-dag-item2-with-name (term nodenum-or-quotep dag-array-name dag-array dag-len)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (dargp-less-than nodenum-or-quotep dag-len))
                  :guard-hints (("Goal" :use (:instance <-of-largest-non-quotep
                                                        (args nodenum-or-quotep)
                                                        (nodenum dag-len))
                                 :in-theory (disable <-of-largest-non-quotep)))))
  (if (term-skeleton-matches-dagp-with-name term nodenum-or-quotep dag-array-name dag-array) ;quick check that does no consing
      (unify-term-and-dag-with-name term nodenum-or-quotep dag-array-name dag-array dag-len nil)
    :fail))

(defun unify-terms-and-dag-items2-with-name (terms nodenums-or-quoteps dag-array-name dag-array dag-len)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (pseudo-dag-arrayp dag-array-name dag-array dag-len)
                              (true-listp nodenums-or-quoteps)
                              (all-dargp-less-than nodenums-or-quoteps dag-len))
                  :guard-hints (("Goal" :use (:instance <-of-largest-non-quotep
                                                        (args nodenums-or-quoteps)
                                                        (nodenum dag-len))
                                 :in-theory (disable <-of-largest-non-quotep)))))
  (if (term-skeletons-match-dagp-with-name terms nodenums-or-quoteps dag-array-name dag-array) ;quick check that does no consing
      (unify-terms-and-dag-with-name terms nodenums-or-quoteps dag-array-name dag-array dag-len nil)
    :fail))
