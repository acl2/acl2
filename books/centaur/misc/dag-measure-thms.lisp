; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "tools/flag" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/basic/defs" :dir :system)
(include-book "misc/hons-help" :dir :system) ;; for alist-keys/vals
(local (include-book "std/lists/sets" :dir :system))





(defstub fg-nodes () nil)

(encapsulate
  (((fg-successors *) => *))
  (local (defun fg-successors (x)
           (declare (ignore x))
           nil))

  (defthm fg-successors-implies-member-nodes
    (implies (not (member-equal x (fg-nodes)))
             (not (consp (fg-successors x))))))




(define fg-unseen-count (x stack)
  :verify-guards nil
  "Counts the remaining nodes that are not in the stack."
  (if (atom x)
      0
    (if (member-equal (car x) stack)
        (fg-unseen-count (cdr x) stack)
      (+ 1 (fg-unseen-count (cdr x) stack))))
  ///
  (defthm fg-unseen-count-of-cons-weak
    (<= (fg-unseen-count x (cons k stack))
        (fg-unseen-count x stack))
    :rule-classes (:rewrite :linear))

  (defthm fg-unseen-count-of-cons
    (implies (and (member k x)
                  (not (member k stack)))
             (< (fg-unseen-count x (cons k stack))
                (fg-unseen-count x stack)))
    :rule-classes (:rewrite :linear))

  (defthm fg-unseen-count-equal-cons
    (implies (not (member k stack))
             (equal (equal (fg-unseen-count x (cons k stack))
                           (fg-unseen-count x stack))
                    (not (member k x))))))


(mutual-recursion
 (defun fg-depth-stack (x stack)
   "Finds the maximum length of a path starting from x, as long as there is no
cycle reachable from x.  Stack is a path consisting of the nodes we've already
seen.  This is just an aid to proving things about the faster, memoized version."
   (declare (xargs :measure (nat-list-measure
                             (list (fg-unseen-count (fg-nodes) stack)
                                   0 1))))
   (b* (((when (member-equal x stack)) :loop)
        (max-depth
         (fg-depth-stack-list (fg-successors x) (cons x stack))))
     (if (eq max-depth :loop) :loop (+ 1 max-depth))))
 (defun fg-depth-stack-list (x stack)
   (declare (xargs :measure (nat-list-measure
                             (list (fg-unseen-count (fg-nodes) stack)
                                   (len x) 0))))
   (b* (((when (atom x)) 0)
        (depth1 (fg-depth-stack (car x) stack))
        (depth2 (fg-depth-stack-list (cdr x) stack))
        ((when (or (eq depth1 :loop) (eq depth2 :loop)))
         :loop))
     (max depth1 depth2))))

(flag::make-flag fg-depth-stack-flag fg-depth-stack
                 :flag-mapping ((fg-depth-stack node)
                                (fg-depth-stack-list list)))

(in-theory (disable fg-depth-stack
                    fg-depth-stack-list))

(defthm-fg-depth-stack-flag
  (defthm fg-depth-stack-type
    (b* ((res (fg-depth-stack x stack)))
      (implies (not (eq res :loop))
               (and (natp res)
                    (integerp res)
                    (<= 0 res))))
    :hints ('(:expand ((fg-depth-stack x stack))))
    :flag node)
  (defthm fg-depth-stack-list-type
    (b* ((res (fg-depth-stack-list x stack)))
      (implies (not (eq res :loop))
               (and (integerp res)
                    (<= -1 res))))
    :hints ('(:expand ((fg-depth-stack-list x stack))))
    :flag list))


;; Fg-stack-depth is a fine measure for traversal depth, but it's slow (does
;; not recognize previously seen nodes) and requires a stack.  We'll eventually
;; introduce a fast version of it that passes around a memoization table.  But
;; to prove that that one gets the right answer, we need to show that this
;; function is, in an immportant way, independent of the stack input.
;; Specifically, if the stack input is a path through the graph (as it will be
;; on every recursive call if we start with an empty stack), then we get the
;; same answer as if we called it on the same node with the empty stack.



(mutual-recursion
 (defun fg-depth-dual-stack-ind (x stack stack2)
   "Finds the maximum length of a path starting from x, as long as there is no
cycle reachable from x.  Stack is a path consisting of the nodes we've already
seen.  This is just an aid to proving things about the faster, memoized version."
   (declare (xargs :measure (nat-list-measure
                             (list (fg-unseen-count (fg-nodes) stack)
                                   0 1)))
            (ignorable stack2))
   (b* (((when (member-equal x stack)) :loop))
     (fg-depth-dual-stack-list-ind (fg-successors x) (cons x stack) (cons x stack2))))
 (defun fg-depth-dual-stack-list-ind (x stack stack2)
   (declare (xargs :measure (nat-list-measure
                             (list (fg-unseen-count (fg-nodes) stack)
                                   (len x) 0))))
   (b* (((when (atom x)) 0))
     (list (fg-depth-dual-stack-ind (car x) stack stack2)
           (fg-depth-dual-stack-list-ind (cdr x) stack stack2)))))

(flag::make-flag fg-depth-dual-stack-flag fg-depth-dual-stack-ind
                 :flag-mapping ((fg-depth-dual-stack-ind node)
                                (fg-depth-dual-stack-list-ind list)))


;; (defthm increment-not-equal-fg-loop
;;   (implies (integerp x)
;;            (not (equal (+ 1 x) :loop)))
;;   :hints (("goal" :use fg-loop-not-integerp
;;            :in-theory (disable fg-loop-not-integerp))))

(defthm-fg-depth-dual-stack-flag
  (defthm fg-depth-stack-when-subsetp
    (implies (and (subsetp-equal stack stack2)
                  (equal (fg-depth-stack x stack) :loop))
             (equal (fg-depth-stack x stack2) :loop))
    :hints ('(:expand ((:free (stack) (fg-depth-stack x stack)))))
    :flag node)
  (defthm fg-depth-stack-list-when-subsetp
    (implies (and (subsetp-equal stack stack2)
                  (equal (fg-depth-stack-list x stack) :loop))
             (equal (fg-depth-stack-list x stack2) :loop))
    :hints ('(:expand ((:free (stack) (fg-depth-stack-list x stack)))))
    :flag list))


(defthm-fg-depth-dual-stack-flag
  (defthm fg-depth-stack-stacks-when-neither-loop
    (implies (and (not (equal (fg-depth-stack x stack) :loop))
                  (not (equal (fg-depth-stack x stack2) :loop)))
             (equal (equal (fg-depth-stack x stack)
                           (fg-depth-stack x stack2))
                    t))
    :hints ('(:expand ((:free (stack) (fg-depth-stack x stack)))))
    :flag node)
  (defthm fg-depth-stack-list-stacks-when-neither-loop
    (implies (and (not (equal (fg-depth-stack-list x stack) :loop))
                  (not (equal (fg-depth-stack-list x stack2) :loop)))
             (equal (equal (fg-depth-stack-list x stack)
                           (fg-depth-stack-list x stack2))
                    t))
    :hints ('(:expand ((:free (stack) (fg-depth-stack-list x stack)))
              :in-theory (disable max)))
    :flag list))


(local (in-theory (disable (force))))


(define fg-stackp (x)
  :verify-guards nil
  (b* (((when (atom x)) t)
       ((when (atom (cdr x))) t)
       ((unless (fg-stackp (cdr x))) nil))
    (member-equal (car x) (fg-successors (cadr x))))
  ///
  (defthm fg-stackp-of-cons
    (iff (fg-stackp (cons k x))
         (or (atom x)
             (and (fg-stackp x)
                  (member-equal k (fg-successors (car x))))))))

(define previous-elem (k x)
  (if (atom x)
      nil
    (if (atom (cdr x))
        nil
      (if (equal k (cadr x))
          (car x)
        (previous-elem k (cdr x)))))
  ///
  (defthm member-of-previous-elem
    (implies (member k (cdr x))
             (member (previous-elem k x) x)))

  (defthmd member-of-previous-elem-rw
    (implies (and (equal q (previous-elem k x))
                  (member k (cdr x)))
             (member q x)))

  (defthm previous-elem-member-of-list-when-fg-stackp
    (implies (and (fg-stackp stack)
                  (member x (cdr stack)))
             (member (previous-elem x stack) (fg-successors x)))))


(defthm-fg-depth-stack-flag
  (defthm fg-depth-stack-loop-implies-short-loop-base
    (implies (and (fg-stackp stack2)
                  (member x stack2)
                  (member (car stack2) stack))
             (equal (fg-depth-stack x stack) :loop))
    :hints ('(:expand ((fg-depth-stack x stack))))
    :flag node)
  (defthm fg-depth-stack-list-loop-implies-short-loop-base
    (implies (and (fg-stackp stack2)
                  (member (car stack) (cdr stack2))
                  (member (car stack2) stack)
                  (member (previous-elem (car stack) stack2) x))
             (equal (fg-depth-stack-list x stack) :loop))
    :hints ('(:expand ((fg-depth-stack-list x stack)
                       (:free (p) (member-equal p x)))
              :in-theory (e/d (member-of-previous-elem-rw)
                              (member))))
    :flag list))

;; Want to show that (fg-depth-stack x stack) is the same as
;; (fg-depth-stack x nil) as long as (cons x stack) is a stackp.
;; Since nil is a subset of stack, if (fg-depth-stack x stack)
;; hits no loop then we'red one.

;; Suppose (fg-depth-stack x stack) is t, i.e. there's a loop;
;; we'll show that (fg-depth-stack x s) is a loop.  Induct on both
;; stacks; every case is trivial except where x is a member of stack but not
;; of s.


(defthm-fg-depth-dual-stack-flag
  (defthm fg-depth-stack-loop-implies-always-loop
    (implies (and (fg-stackp (cons x stack2))
                  (equal (fg-depth-stack x stack2) :loop))
             (equal (fg-depth-stack x stack) :loop))
    :hints ('(:expand ((:free (stack) (fg-depth-stack x stack))))
            (and stable-under-simplificationp
                 '(:use ((:instance fg-depth-stack-list-loop-implies-short-loop-base
                          (stack2 (cons x stack2))
                          (stack (cons x stack))
                          (x (fg-successors x))))
                   :expand ((member-equal x stack2))
                   :in-theory (disable fg-depth-stack-list-loop-implies-short-loop-base))))
    :flag node)
  (defthm fg-depth-stack-list-loop-implies-always-loop
    (implies (and (fg-stackp stack2)
                  (subsetp-equal x (fg-successors (car stack2)))
                  (equal (fg-depth-stack-list x stack2) :loop))
             (equal (fg-depth-stack-list x stack) :loop))
    :hints ('(:expand ((:free (stack) (fg-depth-stack-list x stack))
                       (subsetp-equal x (fg-successors (car stack2))))))
    :flag list))


;; Yessss



(defthm fg-depth-stack-normalize
  (implies (and (syntaxp (not (equal stack ''nil)))
                (fg-stackp (cons x stack)))
           (equal (fg-depth-stack x stack)
                  (fg-depth-stack x nil)))
  :hints (("goal" :use ((:instance fg-depth-stack-when-subsetp
                         (stack2 stack) (stack nil))
                        (:instance fg-depth-stack-loop-implies-always-loop
                         (stack2 stack) (stack nil)))
           :in-theory (disable fg-depth-stack-when-subsetp
                               fg-depth-stack-loop-implies-always-loop)
           :do-not-induct t))
  :otf-flg t)

(defun fg-depth-logic (x)
  (fg-depth-stack x nil))

(defun fg-depth-logic-list (x)
  (b* (((when (atom x)) 0)
       (depth1 (fg-depth-logic (car x)))
       (depth2 (fg-depth-logic-list (cdr x)))
       ((when (or (eq depth1 :loop) (eq depth2 :loop)))
        :loop))
    (max depth1 depth2)))

(encapsulate nil
  (local (defthm fg-depth-logic-list-is-fg-depth-stack-list-with-singleton-stack
           (implies (subsetp-equal x (fg-successors prev))
                    (equal (fg-depth-stack-list x (list prev))
                           (fg-depth-logic-list x)))
           :hints (("goal" :in-theory (enable subsetp-equal)
                    :induct (fg-depth-logic-list x)
                    :expand ((fg-depth-stack-list x (list prev))
                             (subsetp-equal x (fg-successors prev)))))))

  (defthm fg-depth-logic-redef
    (equal (fg-depth-logic x)
           (b* ((max-depth (fg-depth-logic-list (fg-successors x))))
             (if (eq max-depth :loop)
                 :loop
               (+ 1 max-depth))))
    :hints (("goal" :expand ((fg-depth-stack x nil))))
    :rule-classes ((:definition :clique (fg-depth-logic fg-depth-logic-list)
                    :controller-alist ((fg-depth-logic t)
                                       (fg-depth-logic-list t))))))

(in-theory (disable fg-depth-logic))



(defthm len-of-set-diff-of-cons-weak
  (<= (len (set-difference$ x (cons k y)))
      (len (set-difference$ x y)))
  :hints(("Goal" :in-theory (enable len set-difference$)))
  :rule-classes (:rewrite :linear))


(encapsulate nil
  (local (defthm len-of-set-diff-of-cons-strong
           (implies (and (member k x)
                         (not (member k y)))
                    (< (len (set-difference$ x (cons k y)))
                       (len (set-difference$ x y))))
           :hints(("Goal" :in-theory (enable len set-difference$)
                   :induct (len x)))))

  (local (defthm member-alist-keys-is-hons-assoc-equal
           (iff (member k (alist-keys y))
                (hons-assoc-equal k y))
           :hints(("Goal" :in-theory (enable alist-keys)))))

  (defthm len-of-set-diff-of-alist-keys
    (implies (and (member k x)
                  (not (hons-assoc-equal k y)))
             (< (len (set-difference$ x (cons k (alist-keys y))))
                (len (set-difference$ x (alist-keys y)))))
    :hints (("goal" :in-theory (disable len-of-set-diff-of-cons-weak)))
    :rule-classes (:rewrite :linear))

  (defthm len-of-set-diff-of-alist-keys-equal
    (implies (not (hons-assoc-equal k y))
             (equal (equal (len (set-difference$ x (cons k (alist-keys y))))
                           (len (set-difference$ x (alist-keys y))))
                    (not (member k x))))))

(local (in-theory (enable alist-keys)))

;; We'll now introduce a faster version of fg-depth that uses a memo table
;; instead of a stack.

(mutual-recursion
 (defun fg-depth-memo (x memo)
   (declare (xargs :measure (nat-list-measure
                             (list (len (set-difference$
                                         (fg-nodes)
                                         (alist-keys memo)))
                                   0 1))))
   (b* ((look (hons-get x memo))
        ((when look)
         (let ((val (cdr look)))
           (if (or (eq val :back)
                   (eq val :loop))
               (mv :loop memo)
             (mv (lnfix val) memo))))
        (memo (hons-acons x :back memo))
        ((mv max-depth memo)
         (fg-depth-memo-list (fg-successors x) memo))
        (res (if (eq max-depth :loop)
                 :loop
               (+ 1 (lnfix max-depth)))))
     (mv res (hons-acons x res memo))))
 (defun fg-depth-memo-list (x memo)
   (declare (xargs :measure (nat-list-measure
                             (list (len (set-difference$
                                         (fg-nodes)
                                         (alist-keys memo)))
                                   (len x) 0))))
   (b* (((when (atom x)) (mv 0 memo))
        ((mv depth1 memo1) (fg-depth-memo (car x) memo))
        ((unless (mbt (<= (len (set-difference$
                                (fg-nodes)
                                (alist-keys memo1)))
                          (len (set-difference$
                                (fg-nodes)
                                (alist-keys memo))))))
         (mv :loop memo1))
        ((mv depth2 memo) (fg-depth-memo-list (cdr x) memo1))
        ((when (or (eq depth1 :loop) (eq depth2 :loop)))
         (mv :loop memo)))
     (mv (max depth1 depth2) memo))))


(flag::make-flag fg-depth-memo-flag fg-depth-memo
                 :flag-mapping ((fg-depth-memo node)
                                (fg-depth-memo-list list)))


(in-theory (disable fg-depth-memo fg-depth-memo-list))

(defthm-fg-depth-memo-flag
  (defthm fg-depth-memo-measure-decr
    (b* (((mv ?res memo1) (fg-depth-memo x memo)))
      (<= (len (set-difference$ (fg-nodes) (alist-keys memo1)))
          (len (set-difference$ (fg-nodes) (alist-keys memo)))))
    :hints ('(:expand ((fg-depth-memo x memo))))
    :flag node)
  (defthm fg-depth-memo-list-measure-decr
    (b* (((mv ?res memo1) (fg-depth-memo-list x memo)))
      (<= (len (set-difference$ (fg-nodes) (alist-keys memo1)))
          (len (set-difference$ (fg-nodes) (alist-keys memo)))))
    :hints ('(:expand ((fg-depth-memo-list x memo))))
    :flag list))

;; The following function maps a memo table into the
;; equivalent stack.

(define fg-depth-memo->stack (x)
  :verify-guards nil
  :returns (stack true-listp :rule-classes :type-prescription)
  (if (atom x)
      nil
    (if (not (consp (car x)))
        (fg-depth-memo->stack (cdr x))
      (if (eq (cdar x) :back)
          (cons (caar x) (fg-depth-memo->stack (cdr x)))
        (cdr (fg-depth-memo->stack (cdr x))))))
  ///

  (defthm fg-depth-memo->stack-of-cons
    (equal (fg-depth-memo->stack (cons (cons key val) memo))
           (if (eq val :back)
               (cons key (fg-depth-memo->stack memo))
             (cdr (fg-depth-memo->stack memo)))))

  (defthm fg-node-not-member-stack-when-not-in-memo
    (implies (not (hons-assoc-equal x memo))
             (not (member x (fg-depth-memo->stack memo))))
    :hints(("Goal" :in-theory (enable hons-assoc-equal)))))


(define fg-depth-memo-stackp (x)
  :verify-guards nil
  (if (atom x)
      t
    (and (or (not (consp (car x)))
             (eq (cdar x) :back)
             (and (equal (caar x) (car (fg-depth-memo->stack (cdr x))))
                  (not (member-equal (caar x) (cdr (fg-depth-memo->stack (cdr x)))))))
         (fg-depth-memo-stackp (cdr x))))
  ///
  (defthm fg-depth-memo-stackp-implies-lookup
    (implies (and (fg-depth-memo-stackp memo)
                  (hons-assoc-equal x memo))
             (iff (equal (cdr (hons-assoc-equal x memo)) :back)
                  (member-equal x (fg-depth-memo->stack memo))))
    :hints(("Goal" :in-theory (enable fg-depth-memo->stack
                                      member-equal hons-assoc-equal))))

  (defthm fg-depth-memo-stackp-of-acons
    (equal (fg-depth-memo-stackp (cons (cons k v) memo))
           (and (fg-depth-memo-stackp memo)
                (or (eq v :back)
                    (and (equal k (car (fg-depth-memo->stack memo)))
                         (not (member k (cdr (fg-depth-memo->stack memo))))))))))





(defthm-fg-depth-memo-flag
  (defthm fg-depth-memo-stack-preserved
    (b* (((mv & new-memo) (fg-depth-memo x memo)))
      (equal (fg-depth-memo->stack new-memo)
             (fg-depth-memo->stack memo)))
    :hints ('(:expand ((fg-depth-memo x memo))))
    :flag node)
  (defthm fg-depth-memo-list-stack-preserved
    (b* (((mv & new-memo) (fg-depth-memo-list x memo)))
      (equal (fg-depth-memo->stack new-memo)
             (fg-depth-memo->stack memo)))
    :hints ('(:expand ((fg-depth-memo-list x memo))))
    :flag list))

(defthm fg-depth-memo-list-redef
  (equal (fg-depth-memo-list x memo)
         (b* (((when (atom x)) (mv 0 memo))
              ((mv depth1 memo1) (fg-depth-memo (car x) memo))
              ((mv depth2 memo) (fg-depth-memo-list (cdr x) memo1))
              ((when (or (eq depth1 :loop) (eq depth2 :loop)))
               (mv :loop memo)))
           (mv (max depth1 depth2) memo)))
  :hints (("goal" :expand (fg-depth-memo-list x memo)))
  :rule-classes ((:definition :clique (fg-depth-memo fg-depth-memo-list)
                  :controller-alist ((fg-depth-memo t nil)
                                     (fg-depth-memo-list t nil)))))

(defthm-fg-depth-memo-flag
  (defthm fg-depth-memo-stackp-preserved
    (b* (((mv & new-memo) (fg-depth-memo x memo)))
      (implies (fg-depth-memo-stackp memo)
               (fg-depth-memo-stackp new-memo)))
    :hints ('(:expand ((fg-depth-memo x memo))))
    :flag node)
  (defthm fg-depth-memo-list-stackp-preserved
    (b* (((mv & new-memo) (fg-depth-memo-list x memo)))
      (implies (fg-depth-memo-stackp memo)
               (fg-depth-memo-stackp new-memo)))
    :hints ('(:expand ((fg-depth-memo-list x memo))))
    :flag list))


;; (define fg-back-edgep (x memo)
;;   (eq (cdr (hons-get x memo)) :back)
;;   ///
;;   (defthmd fg-back-edgep-rewrite
;;     (equal (equal (cdr (hons-assoc-equal x memo)) :back)
;;            (fg-back-edgep x memo))))

;; (local (in-theory (enable fg-back-edgep-rewrite)))

(define fg-depth-memo-correct (memo)
  :verify-guards nil
  (if (atom memo)
      t
    (if (atom (car memo))
        (fg-depth-memo-correct (cdr memo))
      (and (or (eq (cdar memo) :back)
               (equal (cdar memo) (fg-depth-logic (caar memo))))
           (fg-depth-memo-correct (cdr memo)))))
  ///

  (defthm lookup-when-fg-depth-memo-correct
    (implies (and (fg-depth-memo-correct x)
                  (hons-assoc-equal k x)
                  (not (equal (cdr (hons-assoc-equal k x)) :back)))
             (equal (cdr (hons-assoc-equal k x))
                    (fg-depth-logic k))))

  (defthm lookup-when-fg-depth-memo-correct-nonnegative
    (implies (fg-depth-memo-correct x)
             (<= 0 (cdr (hons-assoc-equal k x)))))

  ;; (defthm lookup-when-fg-depth-memo-correct-memo-stackp
  ;;   (implies (and (fg-depth-memo-correct x)
  ;;                 (hons-assoc-equal k x)
  ;;                 (fg-depth-memo-stackp x)
  ;;                 (not (member k (fg-depth-memo->stack x))))
  ;;            (equal (cdr (hons-assoc-equal k x))
  ;;                   (fg-depth-logic k))))

  ;; (implies (and (fg-depth-memo-stackp memo)
  ;;                 (hons-assoc-equal x memo))
  ;;            (iff (equal (cdr (hons-assoc-equal x memo)) :back)
  ;;                 (member-equal x (fg-depth-memo->stack memo))))

  ;; (defthm lookup-when-fg-depth-memo-correct-for-fg-memo-stackp
  ;;   (implies (and (fg-depth-memo-correct x)
  ;;                 (hons-assoc-equal k x)
  ;;                 (not (cdr (hons-assoc-equal k x))))
  ;;            (equal (cdr (hons-assoc-equal k x))
  ;;                   (fg-depth-logic k))))

  (defthm lookup-when-fg-depth-memo-correct-equal
    (implies (and (fg-depth-memo-correct x)
                  (hons-assoc-equal k x)
                  (not (equal val :back)))
             (equal (equal (cdr (hons-assoc-equal k x)) val)
                    (and (not (equal (cdr (hons-assoc-equal k x)) :back))
                         (equal (fg-depth-logic k) val)))))

  (defthm fg-depth-memo-correct-of-acons
    (equal (fg-depth-memo-correct (cons (cons k v) x))
           (and (fg-depth-memo-correct x)
                (or (equal v :back)
                    (equal v (fg-depth-logic k)))))))


(defthm natp-of-fg-depth-logic
  (implies (not (equal (fg-depth-logic x) :loop))
           (and (natp (fg-depth-logic x))
                (integerp (fg-depth-logic x))
                (<= 0 (fg-depth-logic x))
                (equal (equal 0 (fg-depth-logic x))
                       (not (< 0 (fg-depth-logic x))))))
  :hints(("Goal" :in-theory (e/d (fg-depth-logic)
                                 (fg-depth-stack-type))
          :use ((:instance fg-depth-stack-type (stack nil))))))

(defthm fg-depth-logic-linear
  (implies (not (equal (fg-depth-logic x) :loop))
           (<= 0 (fg-depth-logic x)))
  :rule-classes :linear)

(defthm fg-depth-logic-not-equal-backedge
  (not (equal (fg-depth-logic x) :back))
  :hints (("goal" :use natp-of-fg-depth-logic
           :in-theory (disable natp-of-fg-depth-logic))))

(defthm natp-of-fg-depth-logic-list
  (implies (not (equal (fg-depth-logic-list x) :loop))
           (and (natp (fg-depth-logic-list x))
                (integerp (fg-depth-logic-list x))
                (<= 0 (fg-depth-logic-list x)))))

(defthm fg-depth-logic-list-linear
  (implies (not (equal (fg-depth-logic-list x) :loop))
           (<= 0 (fg-depth-logic-list x)))
  :rule-classes :linear)

(defthm fg-depth-logic-loop-when-path-exists
  (implies (and (fg-stackp stack)
                (member x stack)
                (member x (fg-successors (car stack))))
           (equal (equal :loop (fg-depth-logic x)) t))
  :hints(("Goal" :in-theory (enable fg-depth-logic)
          :use ((:instance fg-depth-stack-normalize)
                fg-depth-stack))))

(defthm-fg-depth-memo-flag
  (defthm fg-depth-memo-correct-crux
    (b* (((mv res new-memo) (fg-depth-memo x memo)))
      (implies (and (fg-stackp (fg-depth-memo->stack memo))
                    (fg-depth-memo-stackp memo)
                    (or (atom (fg-depth-memo->stack memo))
                        (member-equal x (fg-successors (car (fg-depth-memo->stack memo)))))
                    (fg-depth-memo-correct memo))
               (and (equal res (fg-depth-logic x))
                    (fg-depth-memo-correct new-memo))))
    :hints ('(:expand ((fg-depth-memo x memo)))
            (and stable-under-simplificationp
                 '(:cases ((equal (cdr (hons-assoc-equal x memo))
                                  :back)))))
    :flag node)
  (defthm fg-depth-memo-list-correct-crux
    (b* (((mv res new-memo) (fg-depth-memo-list x memo)))
      (implies (and (fg-stackp (fg-depth-memo->stack memo))
                    (fg-depth-memo-stackp memo)
                    (or (atom (fg-depth-memo->stack memo))
                        (subsetp-equal x (fg-successors (car (fg-depth-memo->stack memo)))))
                    (fg-depth-memo-correct memo))
               (and (equal res (fg-depth-logic-list x))
                    (fg-depth-memo-correct new-memo))))
    :hints ('(:expand ((fg-depth-memo-list x memo)
                       (:free (y) (subsetp-equal x y)))))
    :flag list))


(defthm natp-of-fg-depth-memo
  (implies (not (equal (mv-nth 0 (fg-depth-memo x memo)) :loop))
           (and (natp (mv-nth 0 (fg-depth-memo x memo)))
                (integerp (mv-nth 0 (fg-depth-memo x memo)))
                (<= 0 (mv-nth 0 (fg-depth-memo x memo)))))
  :hints (("goal" :expand ((fg-depth-memo x memo)))))


(define fg-loopfree-p (x)
  :verify-guards nil
  (b* (((mv res memo) (fg-depth-memo x nil)))
    (fast-alist-free memo)
    (not (eq res :loop))))

(define fg-loopfreelist-p (x)
  :verify-guards nil
  (b* (((mv res memo) (fg-depth-memo-list x nil)))
    (fast-alist-free memo)
    (not (eq res :loop)))
  ///
  (defthm fg-loopfreelist-p-of-successors
    (implies (fg-loopfree-p x)
             (fg-loopfreelist-p (fg-successors x)))
    :hints(("Goal" :in-theory (enable fg-loopfree-p))))

  (defthm fg-loopfreelist-p-of-cdr
    (implies (and (fg-loopfreelist-p x)
                  (consp x))
             (fg-loopfreelist-p (cdr x))))

  (defthm fg-loopfree-p-of-car
    (implies (and (fg-loopfreelist-p x)
                  (consp x))
             (fg-loopfree-p (car x)))
    :hints(("Goal" :in-theory (enable fg-loopfree-p)))))

(define fg-measure (x)
  :verify-guards nil
  :returns (res o-p)
  (nat-list-measure
   (list (b* (((mv res memo) (fg-depth-memo x nil)))
           (fast-alist-free memo)
           res)
         0
         0)))

(define fg-list-measure-aux (x memo)
  :verify-guards nil
  (if (atom x)
      (mv 0 memo)
    (b* (((mv res1 memo) (fg-depth-memo (car x) memo))
         ((mv res2 memo) (fg-list-measure-aux (cdr x) memo)))
      (mv (max (if (eq res1 :loop) 0 res1) res2)
          memo)))
  ///
  (local (defun ind (x memo)
           (b* (((when (atom x)) memo)
                ((mv ?res1a memo1a) (fg-depth-memo (car x) memo))
                ((mv ?res1b memo1b) (fg-depth-memo (car x) nil)))
             (list (ind (cdr x) memo1a)
                   (ind (cdr x) memo1b)))))
  (defthm fg-list-measure-aux-lemma
    (implies (and (syntaxp (not (equal memo ''nil)))
                  (fg-depth-memo-stackp memo)
                  (equal (fg-depth-memo->stack memo) nil)
                  (fg-depth-memo-correct memo))
             (equal (mv-nth 0 (fg-list-measure-aux x memo))
                    (mv-nth 0 (fg-list-measure-aux x nil))))
    :hints (("goal" :induct (ind x memo))))

  (defthm fg-list-measure-is-fg-depth-logic-list
    (implies (and (fg-depth-memo-stackp memo)
                  (equal (fg-depth-memo->stack memo) nil)
                  (fg-depth-memo-correct memo)
                  (not (equal (fg-depth-logic-list x) :loop)))
             (equal (mv-nth 0 (fg-list-measure-aux x memo))
                    (fg-depth-logic-list x)))
    :hints (("goal" :induct (fg-list-measure-aux x memo)
             :in-theory (enable fg-depth-logic-list))))

  (defthm fg-list-measure-aux-type
    (natp (mv-nth 0 (fg-list-measure-aux x memo)))
    :rule-classes :type-prescription))



(define fg-list-measure (x)
  :verify-guards nil
  :returns (res o-p)
  (nat-list-measure
   (list (b* (((mv res memo) (fg-list-measure-aux x nil)))
           (fast-alist-free memo)
           res)
         1
         (len x)))
  ///

  (defthm fg-list-measure-of-cdr
    (implies (consp x)
             (o< (fg-list-measure (cdr x))
                 (fg-list-measure x)))
    :hints(("Goal" :in-theory (enable fg-list-measure-aux))))

  (defthm fg-measure-of-car
    (implies (consp x)
             (o< (fg-measure (car x))
                 (fg-list-measure x)))
    :hints(("Goal" :in-theory (enable fg-measure)
            :expand ((fg-list-measure-aux x nil)))))

  (local (defthm integerp-+-1
           (equal (integerp (+ 1 x))
                  (or (integerp x)
                      (not (acl2-numberp x))))))

  (defthm fg-list-measure-of-successors
    (implies (fg-loopfree-p x)
             (o< (fg-list-measure (fg-successors x))
                 (fg-measure x)))
    :hints(("Goal" :in-theory (enable fg-measure
                                      fg-loopfree-p)))))


(local
 ;; Example
 (mutual-recursion
  (defun fg-count (x)
    (declare (xargs :measure (fg-measure x)))
    (b* (((unless (fg-loopfree-p x)) 0))
      (+ 1 (fg-count-list (fg-successors x)))))
  (defun fg-count-list (x)
    (declare (xargs :measure (fg-list-measure x)))
    (if (atom x)
        0
      (+ 1 (fg-count (car x))
         (fg-count-list (cdr x)))))))

