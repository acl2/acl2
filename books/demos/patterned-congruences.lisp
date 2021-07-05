; Copyright (C) 2013, ForrestHunt, Inc.
; Written by Matt Kaufmann, December, 2013
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book illustrates the use of patterned congruence rules: congruence rules
; of the form (implies (inner-equiv y1 y2) (outer-equiv (fn ...) (fn ...)))
; argument lists for fn are not simply duplicate-free lists of variables.  Some
; of the examples are lower-level than others, so this file serves several
; purposes, as follows.

; - It provides a demo of congruence-based reasoning and patterned congruences.
; - It serves as a regression test for patterned congruences.
; - It augments the user-level documentation.
; - It contains some lower-level discussion that can help ACL2 implementors
;   understand issues that might arise.

; We start with a demo, and then proceed with what are essentially regression
; tests.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Demo
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; In this demo we introduce a notion of tree equivalence, where two binary
; trees are equivalent if one can be obtained by the other by a sequence of
; "flips", swapping left and right child at a subtree.  It is split into the
; following sections.

; Demo Section 1: A tree equivalence
; Demo Section 2: An equivalence-based rewrite rule
; Demo Section 3: Traditional congruence-based reasoning example
; Demo Section 4: Patterned congruence example

;;;;;;;;;;
; Demo Section 1: A tree equivalence
;;;;;;;;;;

; We begin with some macros to assist those not fluent in Lisp.

(defmacro leaf-p (x) ; a leaf of a binary CONS tree
  `(atom ,x))
(defmacro left (x)
  `(car ,x))
(defmacro right (x)
  `(cdr ,x))

; The following equivalence relation on binary trees holds, roughly speaking,
; when one tree can be transformed to the other by a sequence of "flips":
; switching left and right children of a node.

(defun tree-equiv (t1 t2)
  (cond ((or (leaf-p t1) (leaf-p t2))
         (equal t1 t2))
        (t (or (and (tree-equiv (left t1) (left t2))
                    (tree-equiv (right t1) (right t2)))
               (and (tree-equiv (left t1) (right t2))
                    (tree-equiv (right t1) (left t2)))))))

; An induction hint is needed to prove transitivity (below):

(defun defequiv-tree-equiv-induction-hint (t1 t2 t3)
  (cond
   ((or (leaf-p t1) (leaf-p t2) (leaf-p t3))
    t)
   (t (and (defequiv-tree-equiv-induction-hint (left t1) (left t2) (left t3))
           (defequiv-tree-equiv-induction-hint (left t1) (left t2) (right t3))
           (defequiv-tree-equiv-induction-hint (left t1) (right t2) (left t3))
           (defequiv-tree-equiv-induction-hint (left t1) (right t2) (right t3))
           (defequiv-tree-equiv-induction-hint (right t1) (left t2) (left t3))
           (defequiv-tree-equiv-induction-hint (right t1) (left t2) (right t3))
           (defequiv-tree-equiv-induction-hint (right t1) (right t2) (left t3))
           (defequiv-tree-equiv-induction-hint (right t1) (right t2) (right t3))))))

(defequiv tree-equiv
  :hints (("Goal" :induct (defequiv-tree-equiv-induction-hint x y z))))

;;;;;;;;;;
; Demo Section 2: An equivalence-based rewrite rule
;;;;;;;;;;

; The following function swaps every pair of children in a binary tree.

(defun mirror (tree)
  (cond ((leaf-p tree) tree)
        (t (cons (mirror (right tree))
                 (mirror (left tree))))))

; Notice that the following rewrite rule is based on tree-equiv, not equal.  It
; will replace (mirror x) by x at a subterm occurrence for which it is
; sufficient to preserve the tree-equiv relation.

(defthm tree-equiv-mirror
  (tree-equiv (mirror x)
              x))

;;;;;;;;;;
; Demo Section 3: Traditional congruence-based reasoning example
;;;;;;;;;;

(defun tree-product (tree)

; Returns the product of the numeric fringe of tree.

  (cond ((acl2-numberp tree)
         tree)
        ((leaf-p tree)
         1)
        (t (* (tree-product (left tree))
              (tree-product (right tree))))))

; Just a test (proved by evaluation):

(defthm test-tree-product
  (equal (tree-product '((3 (4 (5 3 a 6) 7 b (4 2)))))
         (* 3 4 5 3 6 7 4 2))
  :rule-classes nil)

; This congruence rule says that the argument of tree-product can be rewritten
; to preserve the tree-equiv relation.

(defthm tree-equiv-->-equal-tree-product
  (implies (tree-equiv x y)
           (equal (tree-product x)
                  (tree-product y)))
  :rule-classes :congruence)

; This little example is proved automatically by rewriting the term (mirror x).
; Of course, it is easy to prove this theorem directly, without
; tree-equiv-mirror or tree-equiv-->-equal-tree-product; here, we are just
; giving a simple illustration of congruence-based rewriting.

(defthm tree-product-mirror
  (equal (tree-product (mirror y))
         (tree-product y))
  :rule-classes nil)

;;;;;;;;;;
; Demo Section 4: Patterned congruence example
;;;;;;;;;;

; Now suppose we want to sweep the tree to collect not only the product of the
; numeric leaves, but additional information as well.  Function tree-data does
; that, using function combine-tree-data to combine recursive calls.

(defun combine-tree-data (t1 t2)
  (list (* (first t1) (first t2))
        (append (second t1) (second t2))))

(defun tree-data (tree)

; Returns (list product leaves), where leaves is the numeric fringe of tree and
; product is the product of those leaves.

  (cond ((acl2-numberp tree)
         (list tree (list tree)))
        ((leaf-p tree)
         (list 1 nil))
        (t (combine-tree-data (tree-data (left tree))
                              (tree-data (right tree))))))

; Test (proved by evaluation):

(defthm tree-data-test
  (equal (tree-data '((3 (4 (5 3 a 6) 7 b (4 2)))))
         (list (* 3 4 5 3 6 7 4 2)
               '(3 4 5 3 6 7 4 2)))
  :rule-classes nil)

; Here comes a patterned congruence rule.

(defthm tree-equiv-->-equal-first-tree-data
  (implies (tree-equiv x y)
           (equal (first (tree-data x))
                  (first (tree-data y))))
  :rule-classes :congruence)

; The following example is proved by the rewrite of (mirror x) to x.  While
; this example is trivial, imagine that there are k1 functions like mirror and
; k2 like tree-data.  If we prove k1 rules like tree-equiv-mirror and k2 rules
; like tree-equiv-->-equal-first-tree-data, then these k1+k2 rules set us
; up to perform automatically all k1*k2 rewrites like first-tree-data-mirror.

(defthm first-tree-data-mirror
  (equal (first (tree-data (mirror y)))
         (first (tree-data y)))
  :rule-classes nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; General utilities for displaying pequivs and such
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun anon (termlist)
  (subst-var-lst '_ *anonymous-var* termlist))

(defun show-pequiv-pattern (pat)
  (declare (xargs :mode :program))
  (list 'pequiv-pattern
        :fn (access pequiv-pattern pat :fn)
        :posn (access pequiv-pattern pat :posn)
        :pre-rev (anon (access pequiv-pattern pat :pre-rev))
        :post (anon (access pequiv-pattern pat :post))
        :next (let ((next (access pequiv-pattern pat :next)))
                (cond ((symbolp next) :next-var)
                      (t (show-pequiv-pattern next))))))

(defun show-pequiv (pequiv)
  (declare (xargs :mode :program))
  (list 'pequiv
        :pattern
        (show-pequiv-pattern (access pequiv pequiv :pattern))
        :unify-subst (access pequiv pequiv :unify-subst)
        :congruence-rule (access congruence-rule
                                 (access pequiv pequiv :congruence-rule)
                                 :rune)))

(defun show-pequiv-lst (pequiv-lst)
  (declare (xargs :mode :program))
  (cond ((atom pequiv-lst) ; could be :none
         nil)
        (t (cons (show-pequiv (car pequiv-lst))
                 (show-pequiv-lst (cdr pequiv-lst))))))

(defun show-pequiv-alist (pequiv-alist)
  (declare (xargs :mode :program))
  (cond ((endp pequiv-alist) nil)
        (t (cons (cons (caar pequiv-alist)
                       (show-pequiv-lst (cdar pequiv-alist)))
                 (show-pequiv-alist (cdr pequiv-alist))))))

(defmacro show-pequivs (fn)
  `(let* ((prop (getprop ',fn 'pequivs nil 'current-acl2-world (w state))))
     (and prop
          (list 'pequivs-property
                :shallow
                (show-pequiv-alist (access pequivs-property prop :shallow))
                :deep
                (show-pequiv-alist (access pequivs-property prop :deep))
                :deep-pequiv-p
                (access pequivs-property prop :deep-pequiv-p)))))

(defun show-pequiv-info (pequiv-info)
  (declare (xargs :mode :program))
  (and pequiv-info
       (list 'pequiv-info
             :rewritten-args-rev (access pequiv-info pequiv-info
                                         :rewritten-args-rev)
             :rest-args (access pequiv-info pequiv-info :rest-args)
             :alist (access pequiv-info pequiv-info :alist)
             :bkptr (access pequiv-info pequiv-info :bkptr)
             :fn (access pequiv-info pequiv-info :fn)
             :geneqv (access pequiv-info pequiv-info :geneqv)
             :deep-pequiv-lst (access pequiv-info pequiv-info
                                      :deep-pequiv-lst))))

(defmacro trace-pequivs (allp)
  `(trace!
    (rewrite :entry (list 'rewrite :term term :alist alist :bkptr bkptr
                          :geneqv geneqv
                          :pequiv-info (show-pequiv-info pequiv-info))
             :notinline t)
    (rewrite-args :entry (list 'rewrite-args
                               :args args
                               :alist alist
                               :bkptr bkptr
                               :rewritten-args-rev rewritten-args-rev
                               :deep-pequiv-lst
                               (show-pequiv-lst deep-pequiv-lst)
                               :shallow-pequiv-lst
                               (show-pequiv-lst shallow-pequiv-lst)
                               :parent-geneqv parent-geneqv
                               :fn fn
                               :geneqv geneqv)
                  :notinline t)
    one-way-unify1-term-alist
    one-way-unify1-term-alist-lst
    ,@(and allp
           '(accumulate-shallow-pequiv-alist
             geneqv-refinementp
             (expand-abbreviations
              :entry (list 'expand-abbreviations :term term :alist alist
                           :geneqv geneqv
                           :pequiv-info (show-pequiv-info pequiv-info))
              :notinline t)
             (expand-abbreviations-lst
              :entry (list 'expand-abbreviations-lst
                           :lst lst
                           :alist alist
                           :bkptr bkptr
                           :rewritten-args-rev rewritten-args-rev
                           :deep-pequiv-lst
                           (show-pequiv-lst deep-pequiv-lst)
                           :shallow-pequiv-lst
                           (show-pequiv-lst shallow-pequiv-lst)
                           :parent-geneqv parent-geneqv
                           :fn fn
                           :geneqv-lst geneqv-lst)
              :notinline t)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Some basic tests for shallow pequivs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun f1 (x y z)
  (list x y z))

(defun f2 (x y)
  (declare (ignore y))
  x)

(defun e1 (x y)
  (equal x y))

(defequiv e1)

(defthm e1-implies-iff-f1-cong-1
  (implies (e1 y1 y2)
           (iff (f1 3 y1 (cons x x))
                (f1 3 y2 (cons x x))))
  :rule-classes (:congruence))

(defconst *pequiv-1*
  '(PEQUIV :PATTERN (PEQUIV-PATTERN :FN F1
                                    :POSN 2
                                    :PRE-REV ('3)
                                    :POST ((CONS X X))
                                    :NEXT :NEXT-VAR)
           :UNIFY-SUBST NIL
           :CONGRUENCE-RULE (:CONGRUENCE
                             E1-IMPLIES-IFF-F1-CONG-1)))

(assert-event
 (equal (show-pequivs f1)
        `(PEQUIVS-PROPERTY
          :SHALLOW ((IFF ,*pequiv-1*))
          :DEEP NIL
          :DEEP-PEQUIV-P NIL)))

(assert-event
 (equal (show-pequiv-lst
         (find-rules-of-rune
          '(:congruence e1-implies-iff-f1-cong-1)
          (w state)))
        (list *pequiv-1*)))

(defthm f2-returns-first-arg
  (e1 (f2 a b) a))

(in-theory (disable f1 f2 e1
                    (tau-system)
                    (:type-prescription f1)
                    (:type-prescription f2)))

#+skip ; only for interactive use
(trace-pequivs nil)

; Rewriting in the proof-builder comprehends patterned congruences:
(defthm test-1-proof-builder
  (iff (f1 3 (f2 z 8) (cons u u))
       (f1 3 z (cons u u)))
  :instructions ((:dv 1 2)
                 (:rewrite f2-returns-first-arg)
                 :top
                 :s-prop)
  :rule-classes nil)

(defthm test-1
  (iff (f1 3 (f2 z 8) (cons u u))
       (f1 3 z (cons u u))))

#+skip ; only for interactive use
(trace-pequivs t)

(must-fail ; outer equiv equal is not preserved (only iff)
 (thm
  (equal (f1 3 (f2 z 8) (cons u u))
         (f1 3 z (cons u u)))))

#+skip ; only for interactive use
(untrace$)

(defun e2 (x y)
  (equal x y))

(defequiv e2)

(defrefinement e2 iff)

(in-theory (disable e2))

(must-fail ; e2 refines iff, not the other way around
 (thm
  (e2 (f1 3 (f2 z 8) (cons u u))
      (f1 3 z (cons u u)))))

(defun e3 (x y)
  (iff x y))

(defequiv e3)

(must-fail ; we need the refinement rule just below
 (thm
  (e3 (f1 3 (f2 z 8) (cons u u))
      (f1 3 z (cons u u)))
  :hints (("Goal" :in-theory (disable e3)))))

(defrefinement iff e3)

(in-theory (disable e3))

; Succeeds because of test-1 and refinement:
(defthm test-2
  (e3 (f1 3 (f2 z 8) (cons u u))
      (f1 3 z (cons u u)))
  :rule-classes nil)

(in-theory (disable test-1))

; Pequiv applies because of refinement:
(defthm test-2-again
  (e3 (f1 3 (f2 z 8) (cons u u))
      (f1 3 z (cons u u)))
  :rule-classes nil)

; Fails because unification fails (u and v are distinct):
(must-fail
 (thm
  (e3 (f1 3 (f2 z 8) (cons u v))
      (f1 3 z (cons u v)))))

; Still fails, because we don't know about substituting into third arg.
(must-fail
 (thm
  (implies (e1 u v)
           (e3 (f1 3 (f2 z 8) (cons u v))
               (f1 3 z (cons u u))))))

(must-fail ; not a valid congruence rule
 (defthm e1-implies-iff-f1-cong-2-try1
   (implies (e1 z1 z2)
            (iff (f1 x (f2 a b) z1)
                 (f1 x a z2)))
   :hints (("Goal" :in-theory (enable f1 f2 e1)))
   :rule-classes (:congruence)))

(defthm e1-implies-iff-f1-cong-2
  (implies (e1 z1 z2)
           (iff (f1 x (f2 a b) z1)
                (f1 x (f2 a b) z2)))
   :hints (("Goal" :in-theory (enable f1 f2 e1)))
  :rule-classes (:congruence))

(defconst *pequiv-2*
  '(PEQUIV :PATTERN (PEQUIV-PATTERN :FN F1
                                    :POSN 3
                                    :PRE-REV ((F2 _ _)
                                              _)
                                    :POST NIL
                                    :NEXT :NEXT-VAR)
           :UNIFY-SUBST NIL
           :CONGRUENCE-RULE (:CONGRUENCE E1-IMPLIES-IFF-F1-CONG-2)))

(assert-event
 (equal
  (show-pequivs f1)
  `(PEQUIVS-PROPERTY
    :SHALLOW ((IFF ,*pequiv-2* ,*pequiv-1*))
    :DEEP NIL
    :DEEP-PEQUIV-P NIL)))

; Fails because v is under a cons, hence can't be replaced by u there:
(must-fail
 (defthm test-3
   (implies (e1 u v)
            (e3 (f1 3 (f2 z 8) (cons u v))
                (f1 3 z (cons u u))))
   :rule-classes nil))

(defcong e1 e1 (cons x y) 2
  :hints (("Goal" :in-theory (enable e1))))

; The following succeeds.  Note however that v is not immediately replaced by u
; (in low-level speak, remove-trivial-equivalences does not remove v).  Rather,
; rewriting replaces v with u (in low-level speak, rewrite-solidify does that
; replacement under (cons u v) because it suffices to preserve e1 there and (e1
; v 2) is true according to the type-alist).  If you trace
; remove-trivial-equivalences, you'll see its failure below (until after v has
; been removed by rewriting), but you'll see success if instead you change (e1
; u v) to (equal u v).
(defthm test-3
  (implies (e1 u v)
           (e3 (f1 3 (f2 z 8) (cons u v))
               (f1 3 z (cons u u))))
  :rule-classes nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Some basic tests for deep pequivs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun f3 (x)
  x)

(defthmd e1-implies-iff-f1-cong-3
  (implies (e1 y1 y2)
           (iff (f1 4 (f3 y1) (+ w w))
                (f1 4 (f3 y2) (+ w w))))
  :hints (("Goal" :in-theory (enable e1)))
  :rule-classes (:congruence))

(assert-event
 (equal
  (show-pequivs f1) ; unchanged except :deep-pequiv-p is now t
  `(PEQUIVS-PROPERTY
    :SHALLOW ((IFF ,*pequiv-2* ,*pequiv-1*))
    :DEEP NIL
    :DEEP-PEQUIV-P T)))

(defconst *pequiv-3*
  '(PEQUIV :PATTERN (PEQUIV-PATTERN :FN F1
                                    :POSN 2
                                    :PRE-REV ('4)
                                    :POST ((BINARY-+ W W))
                                    :NEXT (PEQUIV-PATTERN :FN F3
                                                          :POSN 1
                                                          :PRE-REV NIL
                                                          :POST NIL
                                                          :NEXT :NEXT-VAR))
           :UNIFY-SUBST NIL
           :CONGRUENCE-RULE (:CONGRUENCE E1-IMPLIES-IFF-F1-CONG-3)))

(assert-event
 (equal
  (show-pequivs f3)
  `(PEQUIVS-PROPERTY
    :SHALLOW NIL
    :DEEP ((IFF ,*pequiv-3*))
    :DEEP-PEQUIV-P NIL)))

(defun f4 (x)
  x)

(defthm f4-is-f2
  (e1 (f4 x)
      (f2 x x)))

(in-theory (disable f3 f4 f2-returns-first-arg))

(must-fail ; need to enable e1-implies-iff-f1-cong-3
 (defthm test-4
   (implies (f1 4 (f3 (f2 a a)) (+ b b))
            (f1 4 (f3 (f4 a)) (+ b b)))
   :rule-classes nil))

(in-theory (enable e1-implies-iff-f1-cong-3))

(defthm test-4
  (implies (f1 4 (f3 (f2 a a)) (+ b b))
           (f1 4 (f3 (f4 a)) (+ b b)))
  :rule-classes nil)

; Now let's try a variant of test-4 that requires some rewriting.

(defun f5 (x) ; avoid making this a simple rule; see below
  (car (list 4 x x)))

; We insist on making just one pass through the rewriter, so that we can see
; that the matcher uses the rewritten-args.  Since f5 is not a simple rule, we
; don't need a hint of :do-not '(preprocess) in order to ensure that the proof
; completes at "Goal".

(defthm test-5
  (implies (f1 4 (f3 (f2 a a)) (+ b b))
           (f1 (f5 x) (f3 (f4 a)) (+ b b)))
  :hints ((and (not (equal id *initial-clause-id*))
               '(:error "Didn't complete at main Goal!")))
  :rule-classes nil)

; We next consider a variant of the test above that exercises simple rules
; only, thus showing that the "preprocess" process can handle patterned
; congruences.

(in-theory (disable f4-is-f2))

(defun f5-simple (x)
  (car (list 4 x)))

(defthm f4-is-f2-simple
  (e1 (f4 x)
      (f2 x 7))
  :hints (("Goal" :in-theory (enable f2 f4))))

; (trace-pequivs t)

#||
          6> (EXPAND-ABBREVIATIONS
                  :TERM (F1 (F5-SIMPLE X)
                            (F3 (F4 A))
                            (BINARY-+ B B))
                  :ALIST NIL
                  :GENEQV ((NIL IFF
                                :FAKE-RUNE-FOR-ANONYMOUS-ENABLED-RULE NIL))
                  :PEQUIV-INFO NIL)
...
            7> (EXPAND-ABBREVIATIONS-LST
                :LST ((F5-SIMPLE X)
                      (F3 (F4 A))
                      (BINARY-+ B B))
                :ALIST NIL
                :BKPTR 1
                :REWRITTEN-ARGS-REV NIL
                :DEEP-PEQUIV-LST NIL
                :SHALLOW-PEQUIV-LST
                (...
                 (PEQUIV
                    :PATTERN (PEQUIV-PATTERN :FN F1
                                             :POSN 3
                                             :PRE-REV ((F2 _ _) _)
                                             :POST NIL
                                             :NEXT :NEXT-VAR)
                    :UNIFY-SUBST NIL
                    :CONGRUENCE-RULE (:CONGRUENCE E1-IMPLIES-IFF-F1-CONG-2)))
                :PARENT-GENEQV
                ((NIL IFF
                      :FAKE-RUNE-FOR-ANONYMOUS-ENABLED-RULE NIL))
                :FN F1
                :GENEQV-LST NIL)
...
              8> (EXPAND-ABBREVIATIONS-LST
                  :LST ((F3 (F4 A)) (BINARY-+ B B))
                  :ALIST NIL
                  :BKPTR 2
                  :REWRITTEN-ARGS-REV ('4)
                  :DEEP-PEQUIV-LST NIL
                  :SHALLOW-PEQUIV-LST
                  (...
                   (PEQUIV
                    :PATTERN (PEQUIV-PATTERN :FN F1
                                             :POSN 3
                                             :PRE-REV ((F2 _ _) _)
                                             :POST NIL
                                             :NEXT :NEXT-VAR)
                    :UNIFY-SUBST NIL
                    :CONGRUENCE-RULE (:CONGRUENCE E1-IMPLIES-IFF-F1-CONG-2)))
                  :PARENT-GENEQV
                  ((NIL IFF
                        :FAKE-RUNE-FOR-ANONYMOUS-ENABLED-RULE NIL))
                  :FN F1
                  :GENEQV-LST NIL)
...
                9> (EXPAND-ABBREVIATIONS
                       :TERM (F3 (F4 A))
                       :ALIST NIL
                       :GENEQV NIL
                       :PEQUIV-INFO
                       (PEQUIV-INFO
                            :REWRITTEN-ARGS-REV ('4)
                            :REST-ARGS ((BINARY-+ B B))
                            :ALIST NIL
                            :BKPTR 2
                            :FN F1
                            :GENEQV
                            ((NIL IFF
                                  :FAKE-RUNE-FOR-ANONYMOUS-ENABLED-RULE NIL))
                            :DEEP-PEQUIV-LST NIL))
...
                  10> (EXPAND-ABBREVIATIONS-LST
                           :LST ((F4 A))
                           :ALIST NIL
                           :BKPTR 1
                           :REWRITTEN-ARGS-REV NIL
                           :DEEP-PEQUIV-LST NIL
                           :SHALLOW-PEQUIV-LST
                           ((PEQUIV :PATTERN (PEQUIV-PATTERN :FN F3
                                                             :POSN 1
                                                             :PRE-REV NIL
                                                             :POST NIL
                                                             :NEXT :NEXT-VAR)
                                    :UNIFY-SUBST ((W . B))
                                    :CONGRUENCE-RULE
                                    (:CONGRUENCE E1-IMPLIES-IFF-F1-CONG-3)))
                           :PARENT-GENEQV NIL
                           :FN F3
                           :GENEQV-LST NIL)
...
                  11> (EXPAND-ABBREVIATIONS
                        :TERM (F4 A)
                        :ALIST NIL
                        :GENEQV ((3147 E1
                                       :CONGRUENCE E1-IMPLIES-IFF-F1-CONG-3))
                        :PEQUIV-INFO NIL)
...
                  <11 (EXPAND-ABBREVIATIONS
                           536870884 (F2 A '7)
                           ((LEMMA (:CONGRUENCE E1-IMPLIES-IFF-F1-CONG-3)
                                   (:REWRITE F4-IS-F2-SIMPLE)
                                   (:REWRITE CAR-CONS)
                                   (:DEFINITION F5-SIMPLE))))
...
                  <10 (EXPAND-ABBREVIATIONS-LST
                           536870884 ((F2 A '7))
                           ((LEMMA (:CONGRUENCE E1-IMPLIES-IFF-F1-CONG-3)
                                   (:REWRITE F4-IS-F2-SIMPLE)
                                   (:REWRITE CAR-CONS)
                                   (:DEFINITION F5-SIMPLE))))
                <9 (EXPAND-ABBREVIATIONS
                        536870884 (F3 (F2 A '7))
                        ((LEMMA (:CONGRUENCE E1-IMPLIES-IFF-F1-CONG-3)
                                (:REWRITE F4-IS-F2-SIMPLE)
                                (:REWRITE CAR-CONS)
                                (:DEFINITION F5-SIMPLE))))

||#

(defthm test-5-simple
  (implies (f1 4 (f3 (f2 a 7)) (+ b b))
           (f1 (f5-simple x) (f3 (f4 a)) (+ b b)))
  :hints (("Goal" :do-not '(simplify)))
  :rule-classes nil)

; Undo the effects of the test just above.
(in-theory (e/d (f4-is-f2) (f4-is-f2-simple)))

; The next one succeeds but takes more than one pass, since we need to wait for
; the last argument to be rewritten.

(defthm times-2
  (equal (* 2 x)
         (+ x x)))

(must-fail
 (defthm test-6
   (implies (f1 4 (f3 (f2 a a)) (* 2 b))
            (f1 (f5 x) (f3 (f4 a)) (* 2 b)))
   :hints ((and (not (equal id *initial-clause-id*))
                '(:error "Didn't complete at main Goal!")))
   :rule-classes nil))

(defthm test-6
  (implies (f1 4 (f3 (f2 a a)) (* 2 b))
           (f1 (f5 x) (f3 (f4 a)) (* 2 b)))
  :rule-classes nil)

; Next, we test the use of our matcher when the alist comes into play.

(defun f6 (k u y)
  (f1 k (f3 (f4 u)) y))

; For the following, (trace-pequivs nil) shows:

#||

    3> (REWRITE :TERM (F1 K (F3 (F4 U)) Y)
                :ALIST ((Y BINARY-+ B B) (U . A) (K QUOTE 4))
                :BKPTR RHS
                :GENEQV ((NIL IFF
                              :FAKE-RUNE-FOR-ANONYMOUS-ENABLED-RULE NIL))
                :PEQUIV-INFO NIL)
...
            7> (ONE-WAY-UNIFY1-TERM-ALIST-LST ((BINARY-+ W W))
                                              (Y)
                                              ((Y BINARY-+ B B) (U . A) (K QUOTE 4))
                                              NIL)
...
            <7 (ONE-WAY-UNIFY1-TERM-ALIST-LST T ((W . B)))

||#

(defthm test-7
  (implies (f1 4 (f3 (f2 a a)) (* 2 b))
           (f6 4 a (* 2 b)))
  :hints (("Goal" :do-not '(preprocess)) ; defeat premature expansion of f6
          (and (not (equal id *initial-clause-id*))
               '(:error "Didn't complete at main Goal!")))
  :rule-classes nil)

; We next construct an example for which our matching algorithm deals with
; alists that contain pairs of the form (v . (:sublis-var u . s)), where u is a
; term, meaning that v is bound to u/s.

(defun f6-a (k u y)
  (f1 k (f3 (f4 u)) (+ (* y y) (* y y))))

; For the following, (trace-pequivs nil) shows:

#||

    3> (REWRITE :TERM (F1 K (F3 (F4 U))
                          (BINARY-+ (BINARY-* Y Y)
                                    (BINARY-* Y Y)))
                :ALIST ((Y . B) (U . A) (K QUOTE 4))
                :BKPTR BODY
                :GENEQV ((NIL IFF
                              :FAKE-RUNE-FOR-ANONYMOUS-ENABLED-RULE NIL))
                :PEQUIV-INFO NIL)
...
            7> (ONE-WAY-UNIFY1-TERM-ALIST-LST ((BINARY-+ W W))
                                              ((BINARY-+ (BINARY-* Y Y)
                                                         (BINARY-* Y Y)))
                                              ((Y . B) (U . A) (K QUOTE 4))
                                              NIL)
...
            <7 (ONE-WAY-UNIFY1-TERM-ALIST-LST T
                                              ((W :SUBLIS-VAR (BINARY-* Y Y)
                                                  (Y . B)
                                                  (U . A)
                                                  (K QUOTE 4))))


||#

(defthm test-7-a
  (implies (f1 4 (f3 (f2 a a)) (* 2 b b))
           (f6-a 4 a b))
  :hints (("Goal" :do-not '(preprocess)) ; defeat premature expansion of f6
          (and (not (equal id *initial-clause-id*))
               '(:error "Didn't complete at main Goal!")))
  :rule-classes nil)

; A typical use will be mv-nth.  Let's try such an example.

(defund f7 (y)
  (mv (true-listp y) (len (append y y))))

(defun e4 (x y)
  (equal (len x) (len y)))
(defequiv e4)
(in-theory (disable e4))

(defthm len-append
  (equal (len (append x y))
         (+ (len x) (len y))))

(defthm e4-implies-equal-mv-nth-cong
  (implies (e4 y1 y2)
           (equal (mv-nth 1 (f7 y1))
                  (mv-nth 1 (f7 y2))))
  :hints (("Goal" :in-theory (enable e4 f7)))
  :rule-classes :congruence)

(defthm len-revappend
  (equal (len (revappend x y))
         (+ (len x) (len y))))

(defthm len-reverse
  (equal (len (reverse x))
         (len x)))

(defthm reverse-is-id
  (e4 (reverse x) x)
  :hints (("Goal" :in-theory (enable e4))))

(defthm test-8
  (equal (mv-nth 1 (f7 (reverse x)))
         (mv-nth 1 (f7 x)))
  :hints (("Goal" ; unnecessary hint, but avoids warning
           :in-theory (disable reverse))))

(defun id (x)
  x)

(in-theory (disable id (:type-prescription id)))

(defthm e4-implies-equal-mv-nth-cong-b
  (implies (e4 y1 y2)
           (equal (mv-nth 1 (id (f7 y1)))
                  (mv-nth 1 (id (f7 y2)))))
  :hints (("Goal" :in-theory (enable e4 f7 id)))
  :rule-classes :congruence)

(defthm test-8-b
  (equal (append (mv-nth 1 (id (f7 (reverse x))))
                 (list u v))
         (append (mv-nth 1 (id (f7 x)))
                 (list u v)))
  :hints (("Goal" ; unnecessary hint, but avoids warning
           :in-theory (disable reverse))))

(defconst *pequiv-4*
  '(PEQUIV
    :PATTERN
    (PEQUIV-PATTERN
     :FN MV-NTH
     :POSN 2
     :PRE-REV ('1)
     :POST NIL
     :NEXT (PEQUIV-PATTERN :FN ID
                           :POSN 1
                           :PRE-REV NIL
                           :POST NIL
                           :NEXT (PEQUIV-PATTERN :FN F7
                                                 :POSN 1
                                                 :PRE-REV NIL
                                                 :POST NIL
                                                 :NEXT :NEXT-VAR)))
    :UNIFY-SUBST NIL
    :CONGRUENCE-RULE (:CONGRUENCE E4-IMPLIES-EQUAL-MV-NTH-CONG-B)))

(assert-event
 (equal
  (show-pequivs id)
  `(PEQUIVS-PROPERTY
    :SHALLOW NIL
    :DEEP ((EQUAL ,*pequiv-4*))
    :DEEP-PEQUIV-P NIL)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Some soundness checks
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We introduce the trivial coarsest equivalence relation, in which everything
; is equivalent.

(defun triv-equiv (x y)
     (declare (ignore x y))
     t)
(defequiv triv-equiv)

; We next do checks showing that we prevent some unsound congruence-based
; reasoning due to inappropriate independent rewrites.

; The following is certainly a theorem, since (equal (id1 a) a) is equal to t
; for all a.  Now suppose the rewriter encounters the term (equal (identity b)
; b).  The following congruence rule would make it sufficient to maintain
; triv-equiv when rewriting (identity x).  But the following is a provable
; rewrite rule: (triv-equiv (identity x) 1).  Applying this rule, we would
; reduce the original equality to (equal 1 b).  We would have thus transformed
; a theorem into a non-theorem, from which we could easily prove nil.  Hence
; the defthm just below should produce the following error:

;   ACL2 Error in ( DEFTHM EQUIV-IMPLIES-EQUAL-EQUAL-2 ...):
;   EQUIV-IMPLIES-EQUAL-EQUAL-2 is an unacceptable :CONGRUENCE rule because
;   the variable X-EQUIV occurs more than once in
;   (EQUAL (IDENTITY X-EQUIV) X-EQUIV).  See :DOC congruence.

(must-fail
 (defthm equiv-implies-equal-equal-2
   (implies (triv-equiv x x-equiv)
            (equal (equal (identity x) x)
                   (equal (identity x-equiv) x-equiv)))
   :rule-classes (:congruence)))

; Here is another such example.

(defun some-consp (x y)
  (or (consp x) (consp y)))

(defthm triv-equiv-implies-equal-some-consp-1
  (implies (triv-equiv x x-equiv)
           (equal (some-consp x (cons a b))
                  (some-consp x-equiv (cons a b))))
  :rule-classes (:congruence))

(defthm triv-equiv-implies-equal-some-consp-2
  (implies (triv-equiv y y-equiv)
           (equal (some-consp (cons a b) y)
                  (some-consp (cons a b) y-equiv)))
  :rule-classes (:congruence))

(defthm cons-is-nil
  (triv-equiv (cons x y) nil))

(in-theory (disable some-consp (some-consp)))

(defthm some-consp-rewrite-1
  (equal (some-consp (cons a b) (cons c d))
         (some-consp nil (cons c d)))
  :rule-classes nil)

(must-fail
; Notice that congruence rule triv-equiv-implies-equal-some-consp-1 allows rule
; cons-is-nil to rewrite the first some-consp call below to (some-consp nil
; (cons c d)), and at that point, congruence rule
; triv-equiv-implies-equal-some-consp-2 does not apply.
 (defthm some-consp-rewrite-2
   (equal (some-consp (cons a b) (cons c d))
          (some-consp (cons a b) nil))
   :rule-classes nil))

(defthm some-consp-rewrite-2
  (equal (some-consp (cons a b) (cons c d))
         (some-consp (cons a b) nil))
  :hints (("Goal"
           :in-theory (disable triv-equiv-implies-equal-some-consp-1)))
  :rule-classes nil)

(must-fail
; [Same comment as for preceding must-fail form:]
; Notice that congruence rule triv-equiv-implies-equal-some-consp-1 allows rule
; cons-is-nil to rewrite the first some-consp call below to (some-consp nil
; (cons c d)), and at that point, congruence rule
; triv-equiv-implies-equal-some-consp-2 does not apply.
; [Additional comment:]
; Notice also that this alleged theorem is false: the left-hand side of the
; equality is true but the right-hand side is false.  So it is good that the
; two arguments of the first some-consp call were not both rewritten using
; cons-is-nil!  This shows why the set of relevant patterned equivalences for
; an argument (here, of some-consp) is computed with respect to sibling
; arguments to the left that have been rewritten and sibling arguments on the
; right to the right that have not yet been rewritten.
 (thm (equal (some-consp (cons c1 c2) (cons d1 d2))
             (some-consp nil nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; A few additional tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We make sure that if there is a duplicate variable in the argument list for
; the outer-equiv, then the congruence rule is treated as a (shallow) patterned
; congruence rule, not as a general (i.e., ordinary) congruence rule.

(defund f8 (x y z)
  (and (equal (len x) (len y))
       (equal (len y) (len z))))

(defthm e4-implies-equal-f8-cong
  (implies (e4 z1 z2)
           (equal (f8 x x z1)
                  (f8 x x z2)))
  :hints (("Goal" :in-theory (enable e4 f8)))
  :rule-classes :congruence)

(defthm test-9
  (equal (f8 a a (reverse u))
         (f8 a a u))
  :hints (("Goal" ; unnecessary hint, but avoids warning
           :in-theory (disable reverse)))
  :rule-classes nil)

; If the first two parameters of f8 are not syntactically equal, then the match
; fails for attempting rule e4-implies-equal-f8-cong.
(must-fail
 (thm
  (equal (f8 a b (reverse u))
         (f8 a b u))
  :hints (("Goal" ; unnecessary hint, but avoids warning
           :in-theory (disable reverse)))))

; We disallow calls in the conclusion of EQUAL, IF, IMPLIES, and lambdas.
; During development of support for patterned congruences, there was manual
; inspection of the error messages below.

(must-fail
 (defthm e4-implies-equal-f8-cong-bad-equal
   (implies (e4 z1 z2)
            (equal (f8 (equal a b) 17 z1)
                   (f8 (equal a b) 17 z2)))
   :hints (("Goal" :in-theory (enable e4 f8)))
   :rule-classes :congruence))

(must-fail
 (defthm e4-implies-equal-f8-cong-bad-if
   (implies (e4 z1 z2)
            (equal (f8 (if (consp x) (cons 0 (cdr x)) x) x z1)
                   (f8 (if (consp x) (cons 0 (cdr x)) x) x z2)))
   :hints (("Goal" :in-theory (enable e4 f8)))
   :rule-classes :congruence))

(must-fail
 (defthm e4-implies-equal-f8-cong-bad-equal
   (implies (e4 z1 z2)
            (equal (f8 (equal a b) 17 z1)
                   (f8 (equal a b) 17 z2)))
   :hints (("Goal" :in-theory (enable e4 f8)))
   :rule-classes :congruence))

(must-fail
 (defthm e4-implies-equal-f8-cong-bad-equal-if
   (implies (e4 z1 z2)
            (equal (f8 (if (and (consp x)
                                (consp (cdr x))
                                (equal (car x) (cdr x)))
                           (cons 0 (cdr x))
                         x)
                       x z1)
                   (f8 (if (and (consp x)
                                (consp (cdr x))
                                (equal (car x) (cdr x)))
                           (cons 0 (cdr x))
                         x)
                       x z2)))
   :hints (("Goal" :in-theory (enable e4 f8)))
   :rule-classes :congruence))

(must-fail
 (defthm e4-implies-equal-f8-cong-bad-implies
   (implies (e4 z1 z2)
            (equal (f8 (implies (consp x) (cons 0 (cdr x))) x z1)
                   (f8 (implies (consp x) (cons 0 (cdr x))) x z2)))
   :hints (("Goal" :in-theory (enable e4 f8)))
   :rule-classes :congruence))

;;; In July 2021 we extended remove-guard-holders to simplify
;;; (let ((var expr)) var) to expr.
#||
(must-fail
 (defthm e4-implies-equal-f8-cong-bad-lambda
   (implies (e4 z1 z2)
            (equal (f8 (let ((x (append nil x))) x)
                       x
                       z1)
                   (f8 (let ((x (append nil x))) x)
                       x
                       z2)))
   :hints (("Goal" :in-theory (enable e4 f8)))
   :rule-classes :congruence))
||#

(must-fail
 (defthm e4-implies-equal-f8-cong-bad-equal-lambda
   (implies (e4 z1 z2)
            (equal (f8 (let ((x (append (equal x x) x))) x)
                       x
                       z1)
                   (f8 (let ((x (append (equal x x) x))) x)
                       x
                       z2)))
   :hints (("Goal" :in-theory (enable e4 f8)))
   :rule-classes :congruence))

(must-fail
 (defthm e4-implies-equal-f8-cong-bad-equal-if-lambda
   (implies (e4 z1 z2)
            (equal (f8 (let ((x (append (equal (if (consp x) x nil) x) x))) x)
                       x
                       z1)
                   (f8 (let ((x (append (equal (if (consp x) x nil) x) x))) x)
                       x
                       z2)))
   :hints (("Goal" :in-theory (enable e4 f8)))
   :rule-classes :congruence))

; Each variable from the hypothesis must occur in the appropriate part of the
; conclusion.

(must-fail
 (defthm e4-implies-equal-f8-cong-no-var-1
   (implies (e4 z1 z2)
            (equal (f8 x x z-wrong)
                   (f8 x x z2)))
   :hints (("Goal" :in-theory (enable e4 f8)))
   :rule-classes :congruence))

(must-fail
 (defthm e4-implies-equal-f8-cong-no-var-2
   (implies (e4 z1 z2)
            (equal (f8 x x z1)
                   (f8 x x z-wrong)))
   :hints (("Goal" :in-theory (enable e4 f8)))
   :rule-classes :congruence))

(must-fail
 (defthm e4-implies-equal-f8-cong-no-var-1-alt
   (implies (e4 z1 z2)
            (equal (f8 x x z-wrong)
                   (f8 x x z1)))
   :hints (("Goal" :in-theory (enable e4 f8)))
   :rule-classes :congruence))

; The following form contains misellaneous lower-level tests, in particular of
; a low-level matching routine that is used in the implementation of patterned
; equivalence relations.

(progn

(defun e5 (x y) (equal (fix x) (fix y)))

(defequiv e5)

(defthm e5-implies-equal-a
  (implies (e5 y y-equiv)
           (equal (* x (+ y x)) (* x (+ y-equiv x))))
  :rule-classes (:congruence))

(assert-event
 (equal (getprop 'binary-+ 'pequivs nil 'current-acl2-world (w state))
        (let* ((lhs '(binary-* x (binary-+ y x)))
               (addr '(2 1))
               (rule (car (getprop 'e5-implies-equal-a
                                   'runic-mapping-pairs
                                   nil 'current-acl2-world (w state))))
               (nume (access congruence-rule rule :nume))
               (equiv 'e5)
               (rune '(:congruence e5-implies-equal-a))
               (deep-pequivs
                `((equal ,(make-pequiv lhs addr nume equiv rune)))))
          (make pequivs-property
                :deep deep-pequivs))))

(assert-event
 (equal (getprop 'binary-* 'pequivs nil 'current-acl2-world (w state))
        (make pequivs-property
              :deep-pequiv-p t)))

(assert-event
 (let ((pat  '(cons (f x     y) (g x     z)))
       (term '(cons (f (h a) b) (g (h a) c)))
       (term-alist nil)
       (alist '((y . b))))
   (mv-let
    (ans s)
    (one-way-unify1-term-alist pat term term-alist alist)
    (and ans
         (equal s '((z . c) (x . (h a)) (y . b)))))))

(assert-event
 (let ((pat  '(cons (f x     y) (g x     z)))
       (term '(cons (f (h a) b) (g (h a) c)))
       (term-alist '((b . bb)))
       (alist '((y . b))))
   (mv-let
    (ans s)
    (one-way-unify1-term-alist pat term term-alist alist)
    (declare (ignore s))
    (not ans))))

(assert-event
 (let ((pat  '(cons (f x     y) (g x     z)))
       (term '(cons (f (h a) b) (g (h a) c)))
       (term-alist '((b . bb)))
       (alist nil))
   (mv-let
    (ans s)
    (one-way-unify1-term-alist pat term term-alist alist)
    (and ans
         (equal s '((z . (:sublis-var c (b . bb)))
                    (y . (:sublis-var b (b . bb)))
                    (x . (:sublis-var (h a) (b . bb)))))))))

(assert-event
 (let ((pat  '(cons (f x     y) (g x     (p x w))))
       (term '(cons (f (h a) b) (g (h a) c)))
       (term-alist '((b . bb) (c . (p (r a1) a2))))
       (alist nil))
   (mv-let
    (ans s)
    (one-way-unify1-term-alist pat term term-alist alist)
    (declare (ignore s))
    (not ans))))

(assert-event
 (let ((pat  '(cons (f x     y) (g x     (p x w))))
       (term '(cons (f (h a) b) (g (h a) c)))
       (term-alist '((b . bb) (c . (p (h a) a2))))
       (alist nil))
   (mv-let
    (ans s)
    (one-way-unify1-term-alist pat term term-alist alist)
    (and ans
         (equal s '((w . a2)
                    (y . (:sublis-var b (b . bb) (c . (p (h a) a2))))
                    (x . (:sublis-var (h a) (b . bb) (c . (p (h a) a2))))))))))

(assert-event
 (let ((pat  '(cons (f x     y) (g x     (p x w))))
       (term '(cons (f (h a) b) (g (h a) c)))
       (term-alist '((b . bb) (c . (p (h a) a2))))
       (alist '((y . bb))))
   (mv-let
    (ans s)
    (one-way-unify1-term-alist pat term term-alist alist)
    (and ans
         (equal s '((w . a2)
                    (x . (:sublis-var (h a) (b . bb) (c . (p (h a) a2))))
                    (y . bb)))))))

(assert-event
 (let ((pat  '(r (f x     y) (g x     (p x w)) (s u)))
       (term '(r (f (h a) b) (g (h a) c)       (s (k b (g2 b)))))
       (term-alist '((b . bb) (c . (p (h a) a2))))
       (alist '((y . bb)
                (u . (:sublis-var (k x1 x2) (x1 . bb) (x2 . (g2 bb)))))))
   (mv-let
    (ans s)
    (one-way-unify1-term-alist pat term term-alist alist)
    (and ans
         (equal s
                '((w . a2)
                  (x . (:sublis-var (h a) (b . bb) (c . (p (h a) a2))))
                  (y . bb)
                  (u . (:sublis-var (k x1 x2) (x1 . bb) (x2 . (g2 bb))))))))))

(assert-event
 (let ((pat  '(r (f x     y) (g x     (p x w)) (s u)))
       (term '(r (f (h a) b) (g (h a) c)       (s (k b (g2 b)))))
       (term-alist '((b . bb) (c . (p (h a) a2))))
       (alist '((y . bb))))
   (mv-let
    (ans s)
    (one-way-unify1-term-alist pat term term-alist alist)
    (and ans
         (equal s
                '((u . (:sublis-var (k b (g2 b))
                                    (b . bb) (c . (p (h a) a2))))
                  (w . a2)
                  (x . (:sublis-var (h a) (b . bb) (c . (p (h a) a2))))
                  (y . bb)))))))

(assert-event
 (let ((pat  '(r (f x     y) (g x     (p x w)) (s u)))
       (term '(r (f (h a) b) (g (h a) c)       (s (k b (g2 b)))))
       (term-alist '((b . bb) (c . (p (h a) a2))))
       (alist '((y . bb)
                (u . (:sublis-var (k x1 x2) (x1 . bb))))))
   (mv-let
    (ans s)
    (one-way-unify1-term-alist pat term term-alist alist)
    (declare (ignore s))
    (null ans))))

)

; The next set of tests is based closely on those for f1, but replacing f1 with
; a function f9 that takes an extra argument before the position of the
; designated variable occurring on the lhs of the patterned congruence rule.
; This test is intended to stress the implementation's reversal of the
; arguments before that position, and also to test that the matching algorithm
; pays attention to variables occurring both before and after that position.

(defun f9 (x1 x2 y z1 z2)
  (list x1 x2 y z1 z2))

(defthm e1-implies-iff-f9-cong-1
  (implies (e1 y1 y2)
           (iff (f9 3 (car u) y1 (cons x x) (cdr u))
                (f9 3 (car u) y2 (cons x x) (cdr u))))
  :rule-classes (:congruence))

(defconst *pequiv-5*
  '(PEQUIV :PATTERN (PEQUIV-PATTERN :FN F9
                                    :POSN 3
                                    :PRE-REV ((CAR U) '3)
                                    :POST ((CONS X X) (CDR U))
                                    :NEXT :NEXT-VAR)
           :UNIFY-SUBST NIL
           :CONGRUENCE-RULE (:CONGRUENCE
                             E1-IMPLIES-IFF-F9-CONG-1)))

(assert-event
 (equal (show-pequivs f9)
        `(PEQUIVS-PROPERTY
          :SHALLOW ((IFF ,*pequiv-5*))
          :DEEP NIL
          :DEEP-PEQUIV-P NIL)))

(assert-event
 (equal (show-pequiv-lst
         (find-rules-of-rune
          '(:congruence e1-implies-iff-f9-cong-1)
          (w state)))
        (list *pequiv-5*)))

; (defthm f2-returns-first-arg
;   (e1 (f2 a b) a))
(in-theory (enable f2-returns-first-arg))

(in-theory (disable f9 f2 e1
                    (tau-system)
                    (:type-prescription f9)
                    (:type-prescription f2)))

(defthm test-10
  (iff (f9 3 (car v) (f2 z 8) (cons u u) (cdr v))
       (f9 3 (car v) z (cons u u) (cdr v)))
  :rule-classes nil)

(defthm test-10-proof-builder
  (iff (f9 3 (car v) (f2 z 8) (cons u u) (cdr v))
       (f9 3 (car v) z (cons u u) (cdr v)))
  :instructions ((:dv 1 3)
                 (:rewrite f2-returns-first-arg)
                 :top
                 :s-prop)
  :rule-classes nil)

(must-fail ; match fails between (car v) and w
 (thm
  (iff (f9 3 (car v) (f2 z 8) (cons u u) w)
       (f9 3 (car v) z (cons u u) w))))

(must-fail ; initial two args are in the wrong order
 (thm
  (iff (f9 (car v) 3 (f2 z 8) (cons u u) (cdr v))
       (f9 (car v) 3 z (cons u u) (cdr v)))))

; The implementation replaces uniquely occurring variables by a special
; "anonymous variable", as discussed in the Essay on Patterned Congruences and
; Equivalences.  It would likely be unsound to allow this variable to occur in
; the submitted patterned congruence rule, so we check here that this causes an
; error.

(assert-event (eq *anonymous-var* '|Anonymous variable|))

(must-fail
 (defthm e1-implies-iff-f9-cong-1-bad
   (implies (e1 y1 y2)
            (iff (f9 3 (car |Anonymous variable|)
                     y1
                     (cons x x) (cdr |Anonymous variable|))
                 (f9 3 (car |Anonymous variable|)
                     y2
                     (cons x x) (cdr |Anonymous variable|))))
   :rule-classes (:congruence)))

; The next test emphasizes a point made in :doc patterned-congruence: the match
; is done after preceding arguments have already been rewritten.

(defun f10 (x)
  (list 3 x x))

(defun f11 (x y)
  (declare (ignore y))
  x)

(defthm e1-implies-iff-f11-cong-2
  (implies (e1 y1 y2)
           (iff (f11 (f10 x) y1)
                (f11 (f10 x) y2)))
  :rule-classes (:congruence))

(in-theory (disable f11 (:t f11) e1))

(must-fail ; fails because f10 expands before matching the rule's lhs
 (thm (implies (e1 y1 y2)
               (iff (f11 (f10 x) y1)
                    (f11 (f10 x) y2)))))

(defthm test-11
  (implies (e1 y1 y2)
           (iff (f11 (f10 x) y1)
                (f11 (f10 x) y2)))
  :hints (("Goal" :in-theory (disable f10)))
  :rule-classes nil)

; Our next test checks that we account for matches connecting the argument
; containing the unique variable and arguments after that one.

(defun e6 (x y)
  (equal x y))

(defequiv e6)

(defun f12 (x y)
  (equal x y))

(defun f13 (x y)
  (declare (ignore y))
  x)

(defthm e1-implies-equal-f12-f13-cong-2
  (implies (e6 y1 y2)
           (equal (f12 (f13 x y1) x)
                  (f12 (f13 x y2) x)))
  :rule-classes (:congruence))

(defun f14 (x)
  x)

(defthm f14-is-id
  (e6 (f14 x) x))

(in-theory (disable e6 (:t e6) f12 (:t f12) f13 (:t f13) f14 (:t f14)))

(defthm test-12
  (equal (f12 (f13 x (f14 y)) x)
         (f12 (f13 x y) x))
  :rule-classes nil)

(must-fail
 (thm
  (equal (f12 (f13 x (f14 y)) x2)
         (f12 (f13 x y) x2))))
