; Copyright 2025 Arm Limited and/or its affiliates <open-source-office@arm.com>
; Copyright (C) 2017 Centaur Technology
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
; Author: Sol Swords <sol.swords@arm.com>

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/util/defines" :dir :System)
(include-book "std/basic/defs" :dir :system)
(include-book "std/lists/list-defuns" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "centaur/fty/fixequiv" :dir :system)
(local (include-book "std/lists/sets" :dir :System))
(local (include-book "std/util/termhints" :dir :system))
(local (include-book "clause-processors/find-subterms" :dir :system))
(local (include-book "clause-processors/generalize" :dir :system))


;; Note: Derived from tarjan.lisp (Centaur, 2017); here extracted just the part
;; of the proof about the seen list of the DFS.


(encapsulate
  (((graph-nodes) => *)
   ((graph-node-succs *) => *))

  (local (defun graph-nodes () nil))

  (local (defun graph-node-succs (x)
           (declare (ignore x)) nil))

  ;; (defthm graph-node-succs-are-nodes
  ;;   (subsetp (graph-node-succs x) (graph-nodes)))

  (defthm graph-node-succs-true-listp
    (true-listp (graph-node-succs x)))

  (defthm graph-node-succs-empty-when-not-node
    (implies (not (member-equal x (graph-nodes)))
             (equal (graph-node-succs x) nil))))



(local (defthm len-set-difference-of-cons
         (<= (len (set-difference$ a (cons x b)))
             (len (set-difference$ a b)))
         :hints(("Goal" :in-theory (enable set-difference$)))
         :rule-classes :linear))

(local (defthm len-set-difference-of-cons-when-not-member
         (implies (and (member x a)
                       (not (member x b)))
                  (< (len (set-difference$ a (cons x b)))
                     (len (set-difference$ a b))))
         :hints(("Goal" :in-theory (enable set-difference$)))
         :rule-classes :linear))

(local (defthm len-set-difference-when-subsetp
         (implies (subsetp-equal b c)
                  (<= (len (set-difference$ a c))
                      (len (set-difference$ a b))))
         :hints(("Goal" :in-theory (enable set-difference$)))
         :rule-classes :linear))


(defines dfs-traverse
  :flag-local nil
  (define dfs-traverse-node (x (seen true-listp))
    :returns (new-seen true-listp :rule-classes :type-prescription)
    :well-founded-relation nat-list-<
    :measure (list (len (set-difference$ (graph-nodes) seen)) 0 1)
    :hints (("goal" :cases ((member-equal x (graph-nodes)))))
    :verify-guards nil
    (b* (((when (member-equal x seen))
          (llist-fix seen))
         (seen (cons x seen)))
      (dfs-traverse-list (graph-node-succs x) seen)))

  (define dfs-traverse-list (x (seen true-listp))
    :returns (new-seen true-listp :rule-classes :type-prescription)
    :measure (list (len (set-difference$ (graph-nodes) seen)) (len x) 0)
    (if (atom x)
        (llist-fix seen)
      (b* ((seen1 (dfs-traverse-node (car x) seen))
           ((unless (mbt (subsetp-equal seen seen1)))
            seen1))
        (dfs-traverse-list (cdr x) seen1))))
  ///
  (std::defret-mutual <fn>-seen-subsetp
    (defret <fn>-seen-subsetp
      (subsetp-equal seen new-seen)
      :hints ('(:expand (<call>)))
      :fn dfs-traverse-node)
    (defret <fn>-seen-subsetp
      (subsetp-equal seen new-seen)
      :hints ('(:expand (<call>)))
      :fn dfs-traverse-list))

  (verify-guards dfs-traverse-node)

  (defthmd dfs-traverse-list-redef
    (equal (dfs-traverse-list x seen)
           (if (atom x)
               (llist-fix seen)
             (b* ((seen1 (dfs-traverse-node (car x) seen)))
               (dfs-traverse-list (cdr x) seen1))))
    :hints (("goal" :expand ((dfs-traverse-list x seen))))
    :rule-classes ((:definition :install-body t
                    :clique (dfs-traverse-list dfs-traverse-node)
                    :controller-alist ((dfs-traverse-node t t)
                                       (dfs-traverse-list t t))))))



(define graph-path-p (x)
  (or (mbe :logic (atom (cdr x))
           :exec (or (atom x) (atom (cdr x))))
      (and (member-equal (cadr x) (graph-node-succs (car x)))
           (graph-path-p (cdr x))))
  ///
  (defthm graph-path-p-of-append-successor
    (implies (and (graph-path-p x)
                  (member y (graph-node-succs (car (last x)))))
             (graph-path-p (append x (list y)))))

  (defthm graph-path-p-of-cons-predecessor
    (implies (and (graph-path-p x)
                  (member (car x) (graph-node-succs y)))
             (graph-path-p (cons y x))))

  (defthm graph-path-p-of-append
    (implies (and (graph-path-p x)
                  (graph-path-p y)
                  (member (car y) (graph-node-succs (car (last x)))))
             (graph-path-p (append x y))))

  (defthm graph-path-p-of-append-overlapping
    (implies (and (graph-path-p x)
                  (graph-path-p y)
                  (equal (car y) (car (last x))))
             (graph-path-p (append x (cdr y)))))

  (defthm graph-path-p-of-cdr
    (implies (graph-path-p x)
             (graph-path-p (cdr x))))

  (defthm graph-path-p-of-member
    (implies (graph-path-p x)
             (graph-path-p (member k x))))

  (defthm cadr-member-of-successors-when-graph-path-p
    (implies (and (equal (car x) k)
                  (graph-path-p x)
                  (consp (cdr x)))
             (member (cadr x) (graph-node-succs k))))

  (fty::deffixequiv graph-path-p :args ((x true-listp))))
         


;; (local
;;  (defthm car-member-equal
;;    (equal (car (member-equal k x))
;;           (and (member-equal k x) k))))

;; (local
;;  (defthm nonmember-of-member
;;    (implies (not (member k x))
;;             (not (member k (member j x))))) )

;; (local
;;  (defthm car-last-member-equal
;;    (equal (car (last (member-equal k x)))
;;           (and (member-equal k x)
;;                (car (last x))))))

;; (local
;;  (defthm member-equal-of-true-list-fix-under-iff
;;    (iff (member-equal k (true-list-fix x))
;;         (member-equal k x))))

;; (local
;;  (defthm member-equal-of-true-list-fix-under-list-equiv
;;    (list-equiv (member-equal k (true-list-fix x))
;;                (member-equal k x))))




(local (defthm car-of-member
         (equal (car (member-equal k x))
                (and (member-equal k x) k))))

(local (defthm nonmember-of-member
         (implies (not (member k x))
                  (not (member k (member j x))))) )

(local (defthm no-intersection-of-member
         (implies (not (intersectp-equal x y))
                  (not (intersectp-equal (member k x) y)))
         :hints(("Goal" :in-theory (enable intersectp-equal)))))

(local (defthm last-of-member
         (equal (last (member k x))
                (and (member k x) (last x)))))

(local (defthm car-last-is-member
           (implies (consp x)
                    (member (car (last x)) x))
           :hints(("Goal" :in-theory (enable last)))))

(local (defthm len-of-member
         (<= (len (member k x)) (len x))
         :rule-classes :linear))

(local (defthm car-last-of-append
         (equal (car (last (append x y)))
                (if (consp y)
                    (car (last y))
                  (car (last x))))))

;; (local (defthm butlast-when-len-less
;;            (implies (<= (len x) (nfix n))
;;                     (equal (butlast x n) nil))))

;; (local (defthm butlast-when-len-greater
;;          (implies (< (nfix n) (len x))
;;                   (equal (butlast x n)
;;                          (cons (car x) (butlast (cdr x) n))))))

;; (local (defthm butlast-of-append
;;          (equal (butlast (append x y) n)
;;                 (if (<= (nfix n) (len y))
;;                     (append x (butlast y n))
;;                   (butlast x (- (nfix n) (len y)))))))

;; (local (defthm no-intersectp-of-butlast
;;          (implies (not (intersectp x y))
;;                   (not (intersectp (butlast x n) y)))
;;          :hints(("Goal" :in-theory (enable intersectp)))))

;; (local (defthm index-of-type-when-member
;;          (implies (member x y)
;;                   (natp (index-of x y)))
;;          :rule-classes :type-prescription))

(local (defthmd intersectp-by-subsetp
         (implies (and (intersectp x y)
                       (subsetp y z))
                  (intersectp x z))
         :hints(("Goal" :in-theory (enable intersectp)))))

(local (defthmd subsetp-when-prefixp
         (implies (prefixp x y)
                  (subsetp x y))
         :hints(("Goal" :in-theory (enable prefixp)))))

(local (defthm member-intersectp-witness
         (implies (intersectp a b)
                  (let ((w (intersectp-witness a b)))
                    (and (member w a)
                         (member w b))))
         :hints(("Goal" :in-theory (enable intersectp intersectp-witness)))))

(define graph-path-reduce (x)
  :returns (reduced-path)
  :prepwork ((local (defthm acl2-count-of-member
                      (<= (acl2-count (member k x))
                          (acl2-count x))
                      :rule-classes :linear))
             (local (defthm acl2-count-of-list-fix
                      (<= (acl2-count (list-fix x))
                          (acl2-count x))
                      :rule-classes :linear)))
  (if (atom x)
      nil
    (let ((find (member-equal (car x) (list-fix (cdr x)))))
      (if find
          (graph-path-reduce find)
        (cons (car x) (graph-path-reduce (cdr x))))))
  ///

  (defret car-of-graph-path-reduce
    (equal (car reduced-path)
           (car x)))

  (defthm graph-path-p-of-member
    (implies (graph-path-p x)
             (graph-path-p (member k x)))
    :hints(("Goal" :in-theory (enable graph-path-p))))

  (defret graph-path-reduce-is-path-p
    (implies (graph-path-p x)
             (graph-path-p reduced-path))
    :hints(("Goal" :in-theory (enable graph-path-p))))


  (defret consp-of-graph-path-reduce
    (equal (consp reduced-path)
           (consp x)))

  (defret last-of-graph-path-reduce
    (equal (car (last reduced-path))
           (car (last x))))

  (defret nonmember-of-graph-path-reduce
    (implies (not (member k x))
             (not (member k (graph-path-reduce x)))))

  (defret no-duplicates-of-graph-path-reduce
    (no-duplicatesp (graph-path-reduce x)))


  (defret no-intersection-of-graph-path-reduce
    (implies (not (intersectp-equal x y))
             (not (intersectp-equal reduced-path y)))
    :hints(("Goal" :in-theory (e/d (intersectp-equal) ())
            :induct <call>)))

  (defret len-of-graph-path-reduce
    (<= (len reduced-path) (len x))
    :rule-classes :linear)

  ;; (local (defthm intersectp-of-butlast-of-member
  ;;          (implies (not (intersectp (butlast x n) y))
  ;;                   (not (intersectp (butlast (member k x) n) y)))
  ;;          :hints(("Goal" :in-theory (e/d (intersectp)
  ;;                                         (butlast))))))

  ;; (defret no-intersection-of-graph-path-reduce-but-last
  ;;   (implies (not (intersectp-equal (butlast x 1) y))
  ;;            (not (intersectp-equal (butlast reduced-path 1) y)))
  ;;   :hints(("Goal" :in-theory (e/d (intersectp-equal)
  ;;                                  (butlast)))))
  )


(local
 (defthm intersectp-of-append
   (iff (intersectp-equal (append x y) z)
        (or (intersectp-equal x z)
            (intersectp-equal y z)))
   :hints(("Goal" :in-theory (enable intersectp-equal)))))

(local
 (defthm intersectp-of-append-2
   (iff (intersectp-equal z (append x y))
        (or (intersectp-equal z x)
            (intersectp-equal z y)))
   :hints(("Goal" :in-theory (enable intersectp-equal)))))

(local
 (defthm intersectp-of-cons
   (iff (intersectp-equal (cons x y) z)
        (or (member-equal x z)
            (intersectp-equal y z)))
   :hints(("Goal" :in-theory (enable intersectp-equal)))))

(local
 (defthm intersectp-of-cons2
   (iff (intersectp-equal z (cons x y))
        (or (member-equal x z)
            (intersectp-equal z y)))
   :hints(("Goal" :in-theory (enable intersectp-equal)))))


;; Reachable means there is a path to a node.
;; Reachable* means there is a path to a node through only unseen nodes.

(defsection reachable*-from-node
  (defun-sk reachable*-from-node (x y seen)
    (exists path
            (and (consp path)
                 (graph-path-p path)
                 (equal x (car path))
                 (equal y (car (last path)))
                 (not (intersectp-equal path seen)))))

  (in-theory (disable reachable*-from-node))

  (defthm reachable*-from-node-of-successors
    (implies (and (reachable*-from-node x y seen)
                  (member z (graph-node-succs y))
                  (not (member z seen)))
             (reachable*-from-node x z seen))
    :hints (("goal" :expand ((reachable*-from-node x y seen))
             :use ((:instance reachable*-from-node-suff
                    (x x) (y z) (path (append (reachable*-from-node-witness x y seen)
                                              (list z)))))
             :in-theory (e/d (intersectp-equal)
                             (reachable*-from-node-suff)))))

  (defthm reachable*-from-node-of-immediate-successors
    (implies (and (member z (graph-node-succs y))
                  (not (member z seen))
                  (not (member y seen)))
             (reachable*-from-node y z seen))
    :hints (("goal" :use ((:instance reachable*-from-node-suff
                           (x y) (y z) (path (list y z))))
             :in-theory (enable graph-path-p intersectp-equal))))


  (defthm reachable*-from-node-transitive1
    (implies (and (reachable*-from-node x y seen)
                  (reachable*-from-node y z seen))
             (reachable*-from-node x z seen))
    :hints (("goal" :expand ((reachable*-from-node x y seen)
                             (reachable*-from-node y z seen))
             :in-theory (e/d (intersectp-equal)
                             (reachable*-from-node-suff))
             :use ((:instance reachable*-from-node-suff
                    (x x) (y z) (path (append (reachable*-from-node-witness x y seen)
                                              (cdr (reachable*-from-node-witness y z seen)))))))))

  (defthm reachable*-from-node-transitive2
    (implies (and (reachable*-from-node y z seen)
                  (reachable*-from-node x y seen))
             (reachable*-from-node x z seen)))

  (fty::deffixequiv reachable*-from-node
    :args ((seen true-listp))
    :hints (("goal" :cases ((reachable*-from-node x y seen)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'reachable*-from-node clause))
                      ((unless lit) nil)
                      (other (if (equal (nth 3 lit) 'seen)
                                 '(list-fix seen)
                               'seen)))
                   `(:expand (,(update-nth 3 other lit))
                     :use ((:instance reachable*-from-node-suff
                            (seen ,(nth 3 lit))
                            (path (reachable*-from-node-witness
                                   . ,(cdr (update-nth 3 other lit)))))))))))

  (defthm reachable*-from-node-self
    (implies (not (member x seen))
             (reachable*-from-node x x seen))
    :hints (("goal" :use ((:instance reachable*-from-node-suff
                           (y x) (path (list x)) (seen seen)))
             :in-theory (e/d (graph-path-p intersectp-equal)
                             (reachable*-from-node-suff)))))

  (defthm not-reachable*-from-node-when-member-first
    (implies (member x seen)
             (not (reachable*-from-node x y seen)))
    :hints(("Goal" :in-theory (enable reachable*-from-node
                                      intersectp-equal))))

  (local (defthm intersectp-when-member-last
           (implies (and (member (car (last x)) y)
                         (consp x))
                    (intersectp x y))
           :hints(("Goal" :in-theory (enable intersectp)))))

  (defthm not-reachable*-from-node-when-member-last
    (implies (member y seen)
             (not (reachable*-from-node x y seen)))
    :hints(("Goal" :in-theory (enable reachable*-from-node
                                      intersectp-equal))))

  (defthm reachable*-from-node-of-seen-extension
    (implies (and (not (reachable*-from-node x y seen))
                  (subsetp seen new-seen))
             (not (reachable*-from-node x y new-seen)))
    :hints (("goal" :expand ((reachable*-from-node x y new-seen))
             :use ((:instance reachable*-from-node-suff
                    (seen seen)
                    (path (reachable*-from-node-witness x y new-seen))))
             :in-theory (e/d (intersectp-by-subsetp)
                             (reachable*-from-node-suff))))))


(define reachable*-from-node-canonical-witness (x y seen)
  (graph-path-reduce (reachable*-from-node-witness x y seen))
  ///
  (defthm reachable*-from-node-implies-canonical-witness
    (implies (reachable*-from-node x y seen)
             (let ((path (reachable*-from-node-canonical-witness x y seen)))
               (and (consp path)
                    (graph-path-p path)
                    (equal (car path) x)
                    (equal (car (last path)) y)
                    (not (intersectp-equal path seen)))))
    :hints (("goal" :expand ((reachable*-from-node x y seen)))))

  (defthm no-duplicatesp-of-reachable*-from-node-canonical-witness
    (no-duplicatesp (reachable*-from-node-canonical-witness x y seen)))

  (defthm reachable*-from-node-implies-x-not-in-cdr-of-canonical-witness
    (implies (reachable*-from-node x y seen)
             (let ((path (reachable*-from-node-canonical-witness x y seen)))
               (not (member x (cdr path)))))
    :hints (("goal" :use no-duplicatesp-of-reachable*-from-node-canonical-witness
             :in-theory (e/d (no-duplicatesp)
                             (no-duplicatesp-of-reachable*-from-node-canonical-witness
                              reachable*-from-node-canonical-witness)))))

  (defthm reachable*-from-node-implies-graph-path-p-cdr-of-canonical-witness
    (implies (reachable*-from-node x y seen)
             (let ((path (reachable*-from-node-canonical-witness x y seen)))
               (graph-path-p (cdr path))))
    :hints (("goal" :use reachable*-from-node-implies-canonical-witness
             :in-theory (e/d (graph-path-p)
                             (reachable*-from-node-implies-canonical-witness
                              reachable*-from-node-canonical-witness)))))

  (defthm reachable*-from-node-implies-cadr-successor-of-x-of-canonical-witness
    (implies (and (reachable*-from-node x y seen)
                  (not (equal x y)))
             (let ((path (reachable*-from-node-canonical-witness x y seen)))
               (member (cadr path) (graph-node-succs x))))
    :hints (("goal" :use (reachable*-from-node-implies-canonical-witness)
             :in-theory (e/d (graph-path-p)
                             (reachable*-from-node-implies-canonical-witness
                              reachable*-from-node-canonical-witness)))))

  (defthm reachable*-from-node-implies-no-intersect-cdr-of-canonical-witness
    (implies (reachable*-from-node x y seen)
             (let ((path (reachable*-from-node-canonical-witness x y seen)))
               (not (intersectp-equal (cdr path) seen))))
    :hints (("goal" :use reachable*-from-node-implies-canonical-witness
             :in-theory (e/d (intersectp-equal)
                             (reachable*-from-node-implies-canonical-witness
                              reachable*-from-node-canonical-witness)))))

  ;; (defwitness reachable*-from-node-witness
  ;;   :predicate (reachable*-from-node x y seen)
  ;;   :expr (let ((path (reachable*-from-node-canonical-witness x y seen)))
  ;;           (and (consp path)
  ;;                (graph-path-p path)
  ;;                (equal (car path) x)
  ;;                (equal (car (last path)) y)
  ;;                (not (intersectp path seen))
  ;;                (no-duplicatesp path)))
  ;;   :generalize (((reachable*-from-node-canonical-witness x y seen) . reachupath))
  ;;   :hints ('(:use (reachable*-from-node-implies-canonical-witness
  ;;                   no-duplicatesp-of-reachable*-from-node-canonical-witness)
  ;;             :in-theory (disable reachable*-from-node-implies-canonical-witness
  ;;                                 no-duplicatesp-of-reachable*-from-node-canonical-witness))))

  (defthmd reachable*-from-node-iff-canonical-witness
    (implies (rewriting-negative-literal `(reachable*-from-node ,x ,y ,seen))
             (iff (reachable*-from-node x y seen)
                  (let ((path (reachable*-from-node-canonical-witness x y seen)))
                    (and (consp path)
                         (graph-path-p path)
                         (equal (car path) x)
                         (equal (car (last path)) y)
                         (not (intersectp-equal path seen))
                         (no-duplicatesp path)))))
    :hints (("goal" :use ((:instance reachable*-from-node-suff
                           (seen seen)
                           (path (reachable*-from-node-canonical-witness x y seen)))))
            (and stable-under-simplificationp
                 '(:expand ((reachable*-from-node x y seen)))))))

(local
 (defthm intersectp-nil
   (and (not (intersectp-equal nil x))
        (not (intersectp-equal x nil)))
   :hints(("Goal" :in-theory (enable intersectp-equal)))))

(defsection reachable-from-node
  (defun-sk reachable-from-node (x y)
    (exists path
            (and (consp path)
                 (graph-path-p path)
                 (equal x (car path))
                 (equal y (car (last path))))))

  (in-theory (disable reachable-from-node))
  
  (defthm reachable-from-node-redef
    (equal (reachable-from-node x y)
           (reachable*-from-node x y nil))
    :hints (("goal" :cases ((reachable-from-node x y))
             :in-theory (enable reachable*-from-node-suff))
            (and stable-under-simplificationp
                 (let* ((lit (cadr (assoc 'not clause))))
                   `(:expand (,lit)))))))





(define reachable*-from-list (x y (seen true-listp))
  :returns (reachable)
  :hooks (:fix)
  (if (atom x)
      nil
    (or (ec-call (reachable*-from-node (car x) y seen))
        (reachable*-from-list (cdr x) y seen)))
  ///
  (defret reachable*-from-list-when-empty
    (implies (not (consp x))
             (not reachable))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defret reachable*-from-list-when-reachable-by-member
    (implies (and (reachable*-from-node k y seen)
                  (member k x))
             (reachable*-from-list x y seen)))

  (defthm reachable*-from-list-by-path
    (implies (and (graph-path-p path)
                  (consp path)
                  (member (car path) x)
                  (equal y (car (last path)))
                  (not (intersectp path seen)))
             (reachable*-from-list x y seen))
    :hints (("Goal" :induct (reachable*-from-list x y seen))))

  (local (defthmd consp-cdr-when-car-not-equal-last
           (implies (not (equal (car x) (car (last x))))
                    (consp (cdr x)))))

  (local (defthm last-is-last-of-cdr
           (implies (consp (cdr x))
                    (equal (last (cdr x))
                           (last x)))))

  ;; (local (in-theory (disable last)))
  (local (defun reachable*-from-node-implies-reachable-for-some-successor-hint (x y seen)
           ;; x has a path to y in the seen.
           (b* ((x-y (reachable*-from-node-canonical-witness x y seen))
                (new-seen (cons x seen))
                ;; ((unless (consp (cdr x-y)))
                ;;  ;; Must be because x not equal y.
                ;;  `'(:use ((:instance consp-cdr-when-car-not-equal-last
                ;;            (x ,(hq x-y))))))
                (succ (cadr x-y))
                (succ-y (cdr x-y))
                ((unless (and (consp (cdr x-y))
                              (member succ (graph-node-succs x))
                              (graph-path-p succ-y)))
                 `'(:use ((:instance reachable*-from-node-implies-canonical-witness))
                    :expand ((graph-path-p ,(hq x-y)))
                    :in-theory (disable reachable*-from-node-implies-canonical-witness)))
                ((unless (intersectp succ-y new-seen))
                 (b* (((unless (reachable*-from-node succ y new-seen))
                       `'(:use ((:instance reachable*-from-node-suff
                                 (x ,(hq succ)) (seen ,(hq new-seen))
                                 (path ,(hq succ-y)))))))
                   `'(:use ((:instance reachable*-from-list-when-reachable-by-member
                             (x ,(hq (graph-node-succs x)))
                             (k ,(hq succ)) (seen ,(hq new-seen)))))))
                ((unless (member x succ-y))
                 ;; done too?
                 nil))
             `'(:use ((:instance no-duplicatesp-of-reachable*-from-node-canonical-witness))
                :expand ((no-duplicatesp ,(hq x-y)))
                :in-theory (disable no-duplicatesp-of-reachable*-from-node-canonical-witness)))))


  (defthm reachable*-from-node-implies-reachable-for-some-successor
    (implies (and (reachable*-from-node x y seen)
                  (not (equal x y)))
             (reachable*-from-list
              (graph-node-succs x) y (cons x seen)))
    :hints (("goal" :in-theory (disable reachable*-from-list-when-reachable-by-member
                                        reachable*-from-node-suff)
             :do-not-induct t)
            (use-termhint (reachable*-from-node-implies-reachable-for-some-successor-hint x y seen)))))



(define reachable*-from-list-witness (x y seen)
  :verify-guards nil
  (if (atom x)
      nil
    (if (reachable*-from-node (car x) y seen)
        (reachable*-from-node-canonical-witness (car x) y seen)
      (reachable*-from-list-witness (cdr x) y seen)))
  ///
  (local (in-theory (enable reachable*-from-list)))

  (defthm reachable*-from-list-implies-witness
    (implies (reachable*-from-list x y seen)
             (b* ((path (reachable*-from-list-witness x y seen)))
               (and (consp path)
                    (member (car path) x)
                    (equal (car (last path)) y)
                    (graph-path-p path)
                    (not (intersectp path seen))
                    (no-duplicatesp path)))))

  (in-theory (disable reachable*-from-list-witness))

  (defthm reachable*-from-node-for-some-successor-implies-reachable
    (implies (and (reachable*-from-list
                   (graph-node-succs x) y (cons x seen))
                  (not (member x seen)))
             (reachable*-from-node x y seen))
    :hints (("goal" :use ((:instance reachable*-from-list-implies-witness
                           (x (graph-node-succs x))
                           (seen (cons x seen)))
                          (:instance reachable*-from-node-suff
                           (seen seen)
                           (path (cons x (reachable*-from-list-witness
                                          (graph-node-succs x) y (cons x seen) )))))
             :in-theory (e/d (intersectp)
                             (reachable*-from-list-implies-witness
                              reachable*-from-node-suff
                              reachable*-from-list))
             :do-not-induct t)))

  ;; (defwitness reachable*-from-list-witness
  ;;   :predicate (reachable*-from-list x y seen)
  ;;   :expr (let ((path (reachable*-from-list-witness x y seen)))
  ;;              (and (consp path)
  ;;                   (graph-path-p path)
  ;;                   (member (car path) x)
  ;;                   (equal (car (last path)) y)
  ;;                   (not (intersectp path seen))
  ;;                   (no-duplicatesp path)))
  ;;   :generalize (((reachable*-from-node-canonical-witness x y seen) . reachupath))
  ;;   :hints ('(:use reachable*-from-list-implies-witness
  ;;             :in-theory (disable reachable*-from-list-implies-witness))))
  )

(define reachable-from-list (x y)
  :returns (reachable)
  :hooks (:fix)
  (if (atom x)
      nil
    (or (ec-call (reachable-from-node (car x) y))
        (reachable-from-list (cdr x) y)))
  ///
  (defthm reachable-from-list-redef
    (equal (reachable-from-list x y)
           (reachable*-from-list x y nil))
    :hints(("Goal" :in-theory (enable reachable*-from-list)))))





(defsection dfs-seen-member-cond
  (defun-sk dfs-seen-member-cond (x seen new-seen)
    (forall y
            (iff (member y new-seen)
                 (or (member y seen)
                     (reachable*-from-node x y seen))))
    :rewrite :direct)
  (in-theory (disable dfs-seen-member-cond))

  (fty::deffixequiv dfs-seen-member-cond
    :args ((seen true-listp)
           (new-seen true-listp))
    :hints (("goal" :cases ((dfs-seen-member-cond x seen new-seen)))
            (and stable-under-simplificationp
                 (let ((pos-lit (assoc 'dfs-seen-member-cond clause))
                       (neg-lit (cadr (assoc 'not clause))))
                   `(:expand (,pos-lit)
                     :use ((:instance dfs-seen-member-cond-necc
                            (x ,(nth 1 neg-lit))
                            (seen ,(nth 2 neg-lit))
                            (new-seen ,(nth 3 neg-lit))
                            (y (dfs-seen-member-cond-witness . ,(cdr pos-lit))))))))))

  (defthm dfs-seen-member-cond-implies-intersect
    (implies (and (not (intersectp z new-seen))
                  (intersectp z seen))
             (not (dfs-seen-member-cond x seen new-seen)))
    :hints(("Goal" :in-theory (enable intersectp))))




  (local (defthm no-intersectp-of-cdr
           (implies (not (intersectp x y))
                    (not (intersectp (cdr x) y)))
           :hints(("Goal" :in-theory (enable intersectp)))))


  (local (defthm consp-cdr-when-car-not-equal-last
           (implies (not (equal (car x) (car (last x))))
                    (consp (cdr x)))))

  (local (defthm last-is-last-of-cdr
           (implies (consp (cdr x))
                    (equal (last (cdr x))
                           (last x)))))

  (local (in-theory (disable last)))

  ;; These two theorems (and the similar ones for
  ;; reachable-through-unseen-but-last) are the crux for reasoning that the
  ;; nodes reachable through unseen from a set of nodes is consistent with
  ;; the nodes reachable from the first node, or from the rest of the set when
  ;; considering those seen from the first.  I.e., a priori, a node y
  ;; reachable through unseen from z may not still be reachable after
  ;; visiting nodes reachable from x.  But we prove that either it is still
  ;; reachable from z or it was reachable from x.

  ;; This is the other direction -- adding nodes to the seen does not let
  ;; new nodes become reachable through unseen.
  (defthm reachable-through-unseen-by-member-cond-1
    (implies (and (dfs-seen-member-cond x seen new-seen)
                  (not (reachable*-from-node z y seen)))
             (not (reachable*-from-node z y new-seen)))
    :hints (("goal" :expand ((reachable*-from-node z y new-seen))
             :use ((:instance reachable*-from-node-suff
                    (x z) (seen seen)
                    (path (reachable*-from-node-witness z y new-seen))))))
    :rule-classes ((:rewrite :match-free :all)))



  (local (defun reachable-through-unseen-by-member-cond-2-hint (x y z seen new-seen)
           ;; Hyp assumes z reaches y in seen.
           (b* ((z-y (reachable*-from-node-canonical-witness z y seen))
                ;; If that doesn't intersect the new seen, then z reaches y
                ;; via that same path in the new seen.
                ((unless (intersectp z-y new-seen))
                 `'(:use ((:instance reachable*-from-node-suff
                           (x z) (seen new-seen)
                           (path ,(hq z-y))))
                    :in-theory (disable reachable*-from-node-suff)))
                (int (intersectp-witness z-y new-seen))
                ((when (member int seen))
                 ;; this can't be true because it's a member of z-y
                 `'(:use ((:instance intersectp-member
                           (a ,(hq int))
                           (x ,(hq z-y))
                           (y ,(hq seen))))
                    :in-theory (disable intersectp-member)))
                ;; Since this is a member of new-seen it's reachable from x
                ((unless (reachable*-from-node x int seen))
                 `'(:use ((:instance dfs-seen-member-cond-necc
                           (y ,(hq int))))
                    :in-theory (disable dfs-seen-member-cond-necc)))
                (x-int (reachable*-from-node-canonical-witness x int seen))
                (x-y (append x-int (cdr (member int z-y)))))
             `'(:use ((:instance reachable*-from-node-suff
                       (path ,(hq x-y)) (seen seen)))
                :in-theory (disable reachable*-from-node-suff)))))


  ;; This is the hard direction: if y is not reachable-through-unseen from
  ;; x, then it remains reachable from z (if it was before) after adding the
  ;; nodes reachable from x to the seen set.
  (defthm reachable-through-unseen-by-member-cond-2
    (implies (and (dfs-seen-member-cond x seen new-seen)
                  (reachable*-from-node z y seen)
                  (not (reachable*-from-node x y seen)))
             (reachable*-from-node z y new-seen))
    :hints ((use-termhint (reachable-through-unseen-by-member-cond-2-hint
                           x y z seen new-seen))))

  (defthm reachable*-from-list-by-member-cond-1
    (implies (and (dfs-seen-member-cond x seen new-seen)
                  (not (reachable*-from-list z y seen)))
             (not (reachable*-from-list z y new-seen)))
    :hints(("Goal" :in-theory (enable reachable*-from-list)))
    :rule-classes ((:rewrite :match-free :all)))

  (defthm reachable*-from-list-by-member-cond-2
    (implies (and (dfs-seen-member-cond x seen new-seen)
                  (not (reachable*-from-node x y seen))
                  (reachable*-from-list z y seen))
             (reachable*-from-list z y new-seen))
    :hints(("Goal" :in-theory (enable reachable*-from-list)))
    :rule-classes ((:rewrite :match-free :all)))
  
  (defcong set-equiv iff (dfs-seen-member-cond x seen new-seen) 3
    :hints ((and stable-under-simplificationp
                 (b* ((lit (assoc 'dfs-seen-member-cond clause))
                      (witness `(dfs-seen-member-cond-witness . ,(cdr lit)))
                      (other (if (eq (nth 3 lit) 'new-seen)
                                 'new-seen-equiv
                               'new-seen)))
                   `(:expand (,lit)
                     :use ((:instance dfs-seen-member-cond-necc
                            (y ,witness)
                            (new-seen ,other)))
                     :in-theory (disable dfs-seen-member-cond-necc)))))))




(defsection dfs-seen-member-cond-list
  (defun-sk dfs-seen-member-cond-list (x seen new-seen)
    (forall y
            (iff (member y new-seen)
                 (or (member y seen)
                     (reachable*-from-list x y seen))))
    :rewrite :direct)
  (in-theory (disable dfs-seen-member-cond-list))

  (fty::deffixequiv dfs-seen-member-cond-list
    :args ((seen true-listp)
           (new-seen true-listp))
    :hints (("goal" :cases ((dfs-seen-member-cond-list x seen new-seen)))
            (and stable-under-simplificationp
                 (let ((pos-lit (assoc 'dfs-seen-member-cond-list clause))
                       (neg-lit (cadr (assoc 'not clause))))
                   `(:expand (,pos-lit)
                     :use ((:instance dfs-seen-member-cond-list-necc
                            (x ,(nth 1 neg-lit))
                            (seen ,(nth 2 neg-lit))
                            (new-seen ,(nth 3 neg-lit))
                            (y (dfs-seen-member-cond-list-witness . ,(cdr pos-lit))))))))))

  (local (defthm intersectp-seen-implies-intersectp-new-seen
           (implies (and (dfs-seen-member-cond-list x seen new-seen)
                         (intersectp y seen))
                    (intersectp y new-seen))
           :hints(("Goal" :in-theory (enable intersectp-witness-rw)))))

  (defthm reachable-through-unseen-list-extension-by-member-cond-1
    (implies (and (dfs-seen-member-cond-list x seen new-seen)
                  (not (reachable*-from-node z y seen)))
             (not (reachable*-from-node z y new-seen)))
    :hints (("goal" :expand ((reachable*-from-node z y new-seen))
             :use ((:instance reachable*-from-node-suff
                    (x z) (seen seen)
                    (path (reachable*-from-node-witness z y new-seen))))))
    :rule-classes ((:rewrite :match-free :all)))

  (defthm reachable-through-unseen-list-extension-for-some-x-by-member-cond-1
    (implies (and (dfs-seen-member-cond-list x seen new-seen)
                  (not (reachable*-from-list z y seen)))
             (not (reachable*-from-list z y new-seen)))
    :hints(("Goal" :in-theory (enable reachable*-from-list)))
    :rule-classes ((:rewrite :match-free :all)))

  (defcong set-equiv iff (dfs-seen-member-cond-list x seen new-seen) 3
    :hints ((and stable-under-simplificationp
                 (b* ((lit (assoc 'dfs-seen-member-cond-list clause))
                      (witness `(dfs-seen-member-cond-list-witness . ,(cdr lit)))
                      (other (if (eq (nth 3 lit) 'new-seen)
                                 'new-seen-equiv
                               'new-seen)))
                   `(:expand (,lit)
                     :use ((:instance dfs-seen-member-cond-list-necc
                            (y ,witness)
                            (new-seen ,other)))
                     :in-theory (disable dfs-seen-member-cond-list-necc)))))))








;; First major property of the tarjan-sccs algorithm (and basically any
;; depth-first search): the new seen after finishing traversal of a node
;; satisfies the seen member condition, i.e. it contains those nodes that
;; were already in the seen, or were reachable from the node traversed
;; without intersecting the original seen.
(std::defret-mutual dfs-traverse-seen-member-property
  (defret dfs-traverse-node-seen-member-property
    (dfs-seen-member-cond x seen new-seen)
    :hints ('(:expand (<call>))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))
            (and stable-under-simplificationp
                 (let ((witness (find-call-lst
                                 'dfs-seen-member-cond-witness
                                 clause)))
                   (and witness
                        `(:clause-processor
                          (simple-generalize-cp
                           clause '((,witness . witness))))))))
    :fn dfs-traverse-node)

  (defret dfs-traverse-list-seen-member-property
    (dfs-seen-member-cond-list x seen new-seen)
    :hints ('(:expand (<call>))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause))
                            (:free (y)
                             (reachable*-from-list
                              x y seen)))))
            (and stable-under-simplificationp
                 (let ((witness (find-call-lst
                                 'dfs-seen-member-cond-list-witness
                                 clause)))
                   (and witness
                        `(:clause-processor
                          (simple-generalize-cp
                           clause '((,witness . witness))))))))
    :fn dfs-traverse-list)
  :mutual-recursion dfs-traverse)


(defret member-seen-of-dfs-traverse-node
  (iff (member-equal y new-seen)
       (or (member-equal y seen)
           (reachable*-from-node x y seen)))
  :hints (("goal" :use <fn>-seen-member-property
           :in-theory (disable <fn>-seen-member-property)))
  :fn dfs-traverse-node)

(defret member-seen-of-dfs-traverse-list
  (iff (member-equal y new-seen)
       (or (member-equal y seen)
           (reachable*-from-list x y seen)))
  :hints (("goal" :use <fn>-seen-member-property
           :in-theory (disable <fn>-seen-member-property)))
  :fn dfs-traverse-list)


(defthmd dfs-traverse-list-rec
  (set-equiv (dfs-traverse-list x nil)
             (if (atom x)
                 nil
               (append (dfs-traverse-node (car x) nil)
                       (dfs-traverse-list (cdr x) nil))))
  :hints(("Goal" :in-theory (enable set-unequal-witness-rw)
          :expand ((:free (w) (reachable*-from-list x w nil)))))
  :rule-classes ((:definition :install-body nil)))



(defthm dfs-traverse-node-rec
  (set-equiv (dfs-traverse-node x nil)
             (cons x (dfs-traverse-list (graph-node-succs x) nil)))
  :hints(("Goal" :in-theory (enable set-unequal-witness-rw)
          :do-not-induct t)
         (and stable-under-simplificationp
              (acl2::use-termhint
               (b* ((succs (graph-node-succs x))
                    (witness (set-unequal-witness (dfs-traverse-node x nil)
                                                  (cons x (dfs-traverse-list succs nil))))
                    (reach-from-x (reachable*-from-node x witness nil))
                    ;; (reach-from-list (reachable*-from-list succs witness nil))
                    ((when reach-from-x)
                     (b* ((?reach-witness (reachable*-from-node-canonical-witness x witness nil)))
                       `(:computed-hint-replacement
                         ((and stable-under-simplificationp
                               '(:clause-processor
                                 (simple-generalize-cp
                                  clause '((,(acl2::hq witness) . node)
                                           (,(acl2::hq reach-witness) . path))))))
                         :use ((:instance reachable*-from-node-implies-canonical-witness
                                (y ,(acl2::hq witness))
                                (seen nil))
                               (:instance reachable*-from-list-by-path
                                (path (cdr ,(acl2::hq reach-witness)))
                                (x ,(acl2::hq succs))
                                (y ,(acl2::hq witness))
                                (seen nil)))
                         :in-theory (disable reachable*-from-node-implies-canonical-witness
                                             reachable*-from-list-by-path))))
                    (?reach-witness (reachable*-from-list-witness succs witness nil)))
                 `(:computed-hint-replacement
                   ((and stable-under-simplificationp
                         '(:clause-processor
                           (simple-generalize-cp
                            clause '((,(acl2::hq witness) . node)
                                     (,(acl2::hq reach-witness) . path))))))
                   :use ((:instance reachable*-from-list-implies-witness
                          (x ,(acl2::hq succs))
                          (y ,(acl2::hq witness))
                          (seen nil))
                         (:instance reachable*-from-node-suff
                          (path (cons x ,(acl2::hq reach-witness)))
                          (y ,(acl2::hq witness))
                          (seen nil)))
                   :in-theory (disable reachable*-from-list-implies-witness))))))
  :otf-flg t)

