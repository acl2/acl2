; Utilities for dealing with lets
;
; Copyright (C) 2015-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Main Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/make-doublets" :dir :system)
(include-book "kestrel/utilities/legal-variable-listp" :dir :system)
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/utilities/greater-than-or-equal-len" :dir :system))
(local (include-book "kestrel/utilities/strip-cadrs" :dir :system))

;; A let looks like (let (...bindings...) ...declares... body)

;; Returns the bindings of TERM, which should be a LET.
(defun let-bindings (term)
  (declare (xargs :guard (true-listp term)))
  (first (rest term)))

;; Returns the declares of TERM, which should be a LET.  Returns a (possibly
;; empty) list.
(defun let-declares (term)
  (declare (xargs :guard (true-listp term)))
  (butlast (rest (fargs term)) 1))

;; Returns the body of TERM, which should be a LET.
(defun let-body (term)
  (declare (xargs :guard (true-listp term)))
  (car (last term)))

(defun legal-let-bindingp (binding)
  (declare (xargs :guard t))
  (and (true-listp binding)
       (= 2 (len binding))
       (legal-variablep (first binding))
       ;; no check on the term, since it is untranslated
       ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund legal-let-bindingsp-aux (bindings)
  (declare (xargs :guard t))
  (if (not (consp bindings))
      (null bindings)
    (and (legal-let-bindingp (first bindings))
         (legal-let-bindingsp-aux (rest bindings)))))

(defthm legal-let-bindingsp-aux-forward-to-alistp
  (implies (legal-let-bindingsp-aux bindings)
           (alistp bindings))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable legal-let-bindingsp-aux))))

(defthm legal-let-bindingsp-aux-forward-to-all->=-len-of-2
  (implies (legal-let-bindingsp-aux bindings)
           (all->=-len bindings 2))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable legal-let-bindingsp-aux
                                     >=-LEN-rewrite))))

(defthm legal-let-bindingsp-aux-of-cons
  (equal (legal-let-bindingsp-aux (cons binding bindings))
         (and (legal-let-bindingp binding)
              (legal-let-bindingsp-aux bindings)))
  :hints (("Goal" :in-theory (enable legal-let-bindingsp-aux))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: For let, but not let*, disallow repeated vars
(defund legal-let-bindingsp (bindings)
  (declare (xargs :guard t))
  (and (legal-let-bindingsp-aux bindings)
       (equal (len (strip-cars bindings))
              (len (strip-cadrs bindings)))))

(defthm legal-let-bindingsp-forward-to-alistp
  (implies (legal-let-bindingsp bindings)
           (alistp bindings))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable legal-let-bindingsp))))

(defthm legal-let-bindingsp-forward-to-all->=-len-of-2
  (implies (legal-let-bindingsp bindings)
           (all->=-len bindings 2))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable legal-let-bindingsp
                                     >=-LEN-rewrite))))

(defthm legal-let-bindingsp-of-cons
  (equal (legal-let-bindingsp (cons binding bindings))
         (and (legal-let-bindingp binding)
              (legal-let-bindingsp bindings)))
  :hints (("Goal" :in-theory (enable legal-let-bindingsp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund let-binding-vars (bindings)
  (declare (xargs :guard (legal-let-bindingsp bindings)))
  (strip-cars bindings))

(defthm symbol-listp-of-let-binding-vars
  (implies (legal-let-bindingsp bindings)
           (symbol-listp (let-binding-vars bindings)))
  :hints (("Goal" :in-theory (enable legal-let-bindingsp
                                     legal-let-bindingsp-aux
                                     let-binding-vars))))

(defthm legal-variable-listp-of-let-binding-vars
  (implies (legal-let-bindingsp bindings)
           (legal-variable-listp (let-binding-vars bindings)))
  :hints (("Goal" :in-theory (enable legal-let-bindingsp
                                     legal-let-bindingsp-aux
                                     let-binding-vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund let-binding-terms (bindings)
  (declare (xargs :guard (legal-let-bindingsp bindings)))
  (strip-cadrs bindings))

(defthm <=-of-acl2-count-of-let-binding-terms-linear
  (<= (acl2-count (let-binding-terms bindings))
      (acl2-count bindings))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable let-binding-terms))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We use the len of the vars are the normal form
(defthm len-of-let-binding-terms
  (implies (legal-let-bindingsp bindings)
           (equal (len (let-binding-terms bindings))
                  (len (let-binding-vars bindings))))
  :hints (("Goal" :in-theory (enable legal-let-bindingsp
                                     let-binding-terms
                                     let-binding-vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund make-let-bindings (vars terms)
  (declare (xargs :guard (and (symbol-listp vars) ; todo: strengthen?
                              (true-listp terms) ;; no strong claim about terms
                              (equal (len vars) (len terms))
                              )))
  (make-doublets vars terms))

(defthm len-of-make-let-bindings
  (equal (len (make-let-bindings vars terms))
         (len vars))
  :hints (("Goal" :in-theory (enable make-let-bindings))))

(defthm legal-let-bindingsp-aux-of-make-let-bindings
  (equal (legal-let-bindingsp-aux (make-let-bindings vars terms))
         (legal-variable-listp (true-list-fix vars)))
  :hints (("Goal" :in-theory (enable legal-let-bindingsp-aux make-let-bindings make-doublets))))

(defthm legal-let-bindingsp-of-make-let-bindings
  (equal (legal-let-bindingsp (make-let-bindings vars terms))
         (and (legal-variable-listp (true-list-fix vars))
              ))
  :hints (("Goal" :in-theory (enable legal-let-bindingsp))))

(defthm let-binding-terms-of-make-let-bindings
  (equal (let-binding-terms (make-let-bindings vars terms))
         (true-list-fix (take (len vars) terms)))
  :hints (("Goal" :in-theory (enable let-binding-terms make-let-bindings))))
