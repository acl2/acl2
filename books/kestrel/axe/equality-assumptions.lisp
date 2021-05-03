; Representing equality assumptions
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

;; This book is deprecated.

(include-book "equality-pairs")
(include-book "term-equal-dag")
(include-book "axe-trees")
;(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;; Returns a new term, or nil to indicate no change.
;; Looks for an equality-pair of the form (lhs . rhs), where LHS is equal to FN applied to ARGS and, if one is found, returns the term RHS.
(defund replace-fun-call-using-equality-pairs (equality-pairs fn args dag-array)
  (declare (xargs :guard (and (equality-pairsp equality-pairs) ;TOOD: Should these be lambda-free?
                              (symbolp fn)
                              (not (eq 'quote fn))
                              (true-listp args)
                              (all-dargp args)
                              (implies (not (all-myquotep args))
                                       (pseudo-dag-arrayp 'dag-array dag-array (+ 1 (largest-non-quotep args)))))
                  :guard-hints (("Goal" :in-theory (enable equality-pairsp)))))
  (if (endp equality-pairs)
      nil ;failure
    (let* ((equality-pair (first equality-pairs))
           (term (car equality-pair)))
      (if (term-equal-dag-exprp term fn args dag-array)
          (cdr equality-pair) ;the thing term is equated to
        (replace-fun-call-using-equality-pairs (rest equality-pairs) fn args dag-array)))))

(defthm axe-treep-of-replace-fun-call-using-equality-pairs
  (implies (equality-pairsp equality-pairs)
           (axe-treep (replace-fun-call-using-equality-pairs equality-pairs fn args dag-array)))
  :hints (("Goal" :expand ((all-equality-pairp equality-pairs))
           :in-theory (enable equality-pairsp replace-fun-call-using-equality-pairs))))

;since it is a pseudo-term, it's bounded for any bound
(defthm bounded-axe-treep-of-replace-fun-call-using-equality-pairs
  (implies (equality-pairsp equality-pairs)
           (bounded-axe-treep (replace-fun-call-using-equality-pairs equality-pairs fn args dag-array) bound))
  :hints (("Goal" :expand ((all-equality-pairp equality-pairs))
           :in-theory (enable equality-pairsp replace-fun-call-using-equality-pairs))))

;; looks for an equality-pair of the form (var . blah) and puts in blah for var
;; Returns a new term, or nil to indicate no change.
;use context?  what if we have an assumption that's just var?
(defund replace-var-using-equality-pairs (equality-pairs var)
  (declare (type symbol var)
           (xargs :guard (equality-pairsp equality-pairs)
                  :guard-hints (("Goal" :in-theory (enable equality-pairsp)))))
  (if (endp equality-pairs)
      nil ;failure
    (let* ((equality-pair (car equality-pairs)))
      (if (eq var (car equality-pair))
          (cdr equality-pair) ;the thing var is equated to
        (replace-var-using-equality-pairs (cdr equality-pairs) var)))))

(defthm axe-treep-of-replace-var-using-equality-pairs
  (implies (equality-pairsp equality-pairs)
           (axe-treep (replace-var-using-equality-pairs equality-pairs var)))
  :hints (("Goal" :expand ((all-equality-pairp equality-pairs))
           :in-theory (enable replace-var-using-equality-pairs equality-pairsp))))

;since it is a pseudo-term, it's bounded for any bound
(defthm bounded-axe-treep-of-replace-var-using-equality-pairs
  (implies (equality-pairsp equality-pairs)
           (bounded-axe-treep (replace-var-using-equality-pairs equality-pairs var) bound))
  :hints (("Goal" :expand ((all-equality-pairp equality-pairs))
           :in-theory (enable replace-var-using-equality-pairs equality-pairsp))))
