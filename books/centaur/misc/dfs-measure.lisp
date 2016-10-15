; Centaur Miscellaneous Books
; Copyright (C) 2010-2012 Centaur Technology
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
;
; dfs-measure.lisp - a measure for depth-first search termination arguments

(in-package "ACL2")
(include-book "std/lists/suffixp" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "misc/hons-help" :dir :system)
(include-book "std/util/bstar" :dir :system)


(defthm len-set-difference-equal-weak
  (<= (len (set-difference-equal a (cons k b)))
      (len (set-difference-equal a b)))
  :hints(("Goal" :in-theory (enable set-difference-equal)))
  :rule-classes :linear)

(defthm len-set-difference-equal-strong
  (iff (< (len (set-difference-equal a (cons k b)))
          (len (set-difference-equal a b)))
       (and (member-equal k a)
            (not (member-equal k b))))
  :hints(("Goal" :in-theory (enable set-difference-equal))))

(defthm len-set-difference-equal-weak-rw
  (iff (equal (len (set-difference-equal a (cons k b)))
              (len (set-difference-equal a b)))
       (or (not (member-equal k a))
           (member-equal k b)))
  :hints(("Goal" :in-theory (enable set-difference-equal))))

(defthm len-set-difference-when-cons-member
  (implies (and (not (member-equal x b))
                (member-equal x a))
           (< (len (set-difference-equal a (cons x b)))
              (len (set-difference-equal a b))))
  :hints (("goal" :in-theory (enable set-difference-equal)))
  :rule-classes :linear)

(defthm subsetp-equal-bad-guy
  (implies (and (not (member-equal k c))
                (member-equal k b))
           (not (subsetp-equal b c))))

(defthm len-set-difference-when-subset
  (implies (subsetp-equal b c)
           (<= (len (set-difference-equal a c))
               (len (set-difference-equal a b))))
  :hints (("goal" :in-theory (enable set-difference-equal
                                     subsetp-equal)))
  :rule-classes :linear)

(defthm set-difference-equal-subset-containing-new-member
  (implies (and (member-equal k a)
                (not (member-equal k b))
                (subsetp-equal b c)
                (member-equal k c))
           (< (len (set-difference-equal a (cons k c)))
              (len (set-difference-equal a b))))
  :hints (("goal" :in-theory (e/d* ((:induction set-difference-equal))
                                   ((:rules-of-class :type-prescription :here)
                                    default-car default-cdr
                                    default-+-2))
           :expand ((:free (b) (set-difference-equal a b)))))
  :rule-classes :linear)

(defthm set-difference-equal-decr-when-cons-new-onto-superset
  (implies (and (member-equal k a)
                (not (member-equal k b))
                (subsetp-equal b c))
           (< (len (set-difference-equal a (cons k c)))
              (len (set-difference-equal a b))))
  :rule-classes (:rewrite :linear))

(defund dfs-nodesleft (edges stack)
  (declare (Xargs :guard t))
  (len (set-difference-equal (alist-keys edges)
                             (alist-keys stack))))

(defun dfs-measure (nodes edges stack)
  (declare (xargs :guard t))
  (list (dfs-nodesleft edges stack)
        (len nodes)))

(defthm dfs-nodesleft-decr-weak
  (<= (dfs-nodesleft edges (cons x stack))
      (dfs-nodesleft edges stack))
  :hints(("Goal" :in-theory (enable dfs-nodesleft alist-keys)))
  :rule-classes :linear)

(defthm dfs-nodesleft-decr-strong
  (implies (and (hons-assoc-equal node edges)
                (not (hons-assoc-equal node stack)))
           (< (dfs-nodesleft edges (cons (cons node v) stack))
              (dfs-nodesleft edges stack)))
  :hints(("Goal" :in-theory (enable dfs-nodesleft alist-keys)))
  :rule-classes :linear)

(defthm dfs-nodesleft-decr-strong-by-len
  (implies (and (case-split (hons-assoc-equal node edges))
                (not (hons-assoc-equal node stack)))
           (< (dfs-nodesleft edges (cons (cons node v) stack))
              (dfs-nodesleft edges stack)))
  :hints(("Goal" :in-theory (enable dfs-nodesleft alist-keys)))
  :rule-classes :linear)

(defthm set-difference-equal-suffix
  (implies (suffixp b c)
           (<= (len (set-difference-equal a c))
               (len (set-difference-equal a b))))
  :hints(("Goal" :in-theory (enable suffixp)))
  :rule-classes :linear)

(defthmd suffixp-alist-keys
  (implies (suffixp a b)
           (suffixp (alist-keys a) (alist-keys b)))
  :hints(("Goal" :in-theory (enable alist-keys suffixp))))

(defthm dfs-nodesleft-decr-suffix
  (implies (suffixp stack1 stack2)
           (<=  (dfs-nodesleft edges stack2)
                (dfs-nodesleft edges stack1)))
  :hints(("Goal" :in-theory (enable dfs-nodesleft suffixp)
          :use (:instance suffixp-alist-keys
                (a stack1) (b stack2))))
  :rule-classes :linear)



;; Illustration:

(defun dfs-collect (nodes edges stack)
  (declare (xargs :mode :logic
                  :well-founded-relation nat-list-<
                  :measure (dfs-measure nodes edges stack)
                  :guard t
                  :verify-guards nil))
  (b* (((when (atom nodes)) stack)
       (node (car nodes))
       ((when (hons-get node stack))
        (dfs-collect (cdr nodes) edges stack))
       (succs (cdr (hons-get node edges)))
       (stack1 (hons-acons node t stack))
       (stack1 (dfs-collect succs edges stack1))
       ((unless (mbt (suffixp stack stack1)))
        stack1))
    (dfs-collect (cdr nodes) edges stack1)))

(defthm dfs-collect-suffixp
  (suffixp stack (dfs-collect nodes edges stack))
  :hints(("Goal" :induct (dfs-collect nodes edges stack))))

(defthm dfs-collect-suffixp-cons
  (suffixp stack (dfs-collect nodes edges (cons x stack)))
  :hints(("Goal" :use (:instance suffixp-transitive
                       (a stack)
                       (b (cons x stack))
                       (c (dfs-collect nodes edges (cons x stack))))
          :in-theory (disable suffixp-transitive))))

(verify-guards dfs-collect)

(defthm dfs-collect-def
  (equal (dfs-collect nodes edges stack)
         (b* (((when (atom nodes)) stack)
              (node (car nodes))
              ((when (hons-get node stack))
               (dfs-collect (cdr nodes) edges stack))
              (succs (cdr (hons-get node edges)))
              (stack (hons-acons node t stack))
              (stack (dfs-collect succs edges stack)))
           (dfs-collect (cdr nodes) edges stack)))
  :rule-classes :definition)


