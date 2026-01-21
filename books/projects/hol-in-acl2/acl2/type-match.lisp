; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; The type-match utility was originally defined in hol.lisp, but since it is
; unused, it has been moved it out of the way, into the present book.

(in-package "ZF")

(include-book "hol")

(mutual-recursion

(defun type-match (pat type bindings)

; Pat is a type pattern, that is, a type expression that need not be ground.
; Type-match attempts to extend the given bindings by associating type
; variables with ground types, returning the extended bindings upon success and
; :fail upon failure.

  (declare (xargs :guard (and (weak-hol-typep pat nil)
                              (weak-hol-typep type t)
                              (weak-hol-type-alistp bindings))
                  :verify-guards nil
                  :measure (acl2-count pat)))
  (cond
   ((atom pat)
    (cond ((keywordp pat)
           (cond ((eq pat type) bindings)
                 (t :fail)))
          (t (let ((pair (assoc-hta pat bindings)))
               (cond ((null pair) (acons pat type bindings))
                     ((equal (cdr pair) type) bindings)
                     (t :fail))))))
   ((atom type)
    :fail)
   ((not (eq (car pat) (car type)))
    :fail)
   (t (type-match-lst (cdr pat) (cdr type) bindings))))

(defun type-match-lst (pat-lst type-lst bindings)

; Bindings is an alist.  It keys are symbols that represent types.  Its values
; are type expressions.

  (declare (xargs :guard (and (weak-hol-type-listp pat-lst nil)
                              (weak-hol-type-listp type-lst t)
                              (equal (length pat-lst) (length type-lst))
                              (weak-hol-type-alistp bindings))
                  :measure (acl2-count pat-lst)))
  (cond
   ((atom pat-lst)
    (if (and (null pat-lst)
             (null type-lst))
        bindings
      :fail))
   ((atom type-lst) :fail)
   (t (let ((bindings1 (type-match (car pat-lst) (car type-lst) bindings)))
        (cond ((eq bindings1 :fail)
               :fail)
              (t (type-match-lst (cdr pat-lst) (cdr type-lst) bindings1)))))))
)

(encapsulate
  ()

(local (include-book "tools/flag" :dir :system))

(local (acl2::make-flag type-match))

(local
 (defthm equal-plus-len
   (implies (and (syntaxp (quotep k))
                 (syntaxp (quotep n))
                 (natp n))
            (equal (equal (+ k (len x)) n)
                   (equal (len x) (- n k))))))

(local
 (defthm-flag-type-match
   (defthm weak-hol-type-alist-type-match
     (implies (and (weak-hol-typep pat nil)
                   (weak-hol-typep type t)
                   (weak-hol-type-alistp bindings)
                   (not (equal (type-match pat type bindings)
                               :fail)))
              (weak-hol-type-alistp (type-match pat type bindings)))
     :flag type-match)
   (defthm weak-hol-type-alist-type-match-lst
     (implies (and (weak-hol-type-listp pat-lst nil)
                   (weak-hol-type-listp type-lst t)
                   (equal (length pat-lst) (length type-lst))
                   (weak-hol-type-alistp bindings)
                   (not (equal (type-match-lst pat-lst type-lst bindings)
                               :fail)))
              (weak-hol-type-alistp (type-match-lst pat-lst type-lst
                                                    bindings)))
     :flag type-match-lst)))

(verify-guards type-match
  :hints (("Goal" :expand ((:free (groundp) (weak-hol-typep pat groundp))))))
)
