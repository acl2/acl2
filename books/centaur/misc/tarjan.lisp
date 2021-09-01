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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/util/defines" :dir :System)
(include-book "std/basic/defs" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "centaur/fty/baselists" :dir :system)
(include-book "std/util/termhints" :dir :system)
(include-book "std/lists/index-of" :dir :system)
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "clause-processors/find-subterms" :dir :system))
(local (include-book "clause-processors/generalize" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "data-structures/no-duplicates" :dir :system))
(local (in-theory (disable intersectp-equal-commute)))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/butlast" :dir :system))
(local (in-theory (disable butlast)))
(local (include-book "centaur/misc/equal-sets" :dir :system))
;; needed for nonlocal defwitness forms
(include-book "clause-processors/witness-cp" :dir :system)

(std::make-returnspec-config :hints-sub-returnnames t)


(encapsulate
  (((graph-nodes) => *)
   ((graph-node-succs *) => *))

  (local (defun graph-nodes () nil))

  (local (defun graph-node-succs (x)
           (declare (ignore x)) nil))

  (defthm graph-node-succs-are-nodes
    (subsetp (graph-node-succs x) (graph-nodes)))

  (defthm graph-node-succs-true-listp
    (true-listp (graph-node-succs x))))



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



(defines tarjan-sccs
  :flag-local nil
  (define tarjan-sccs (x
                       (preorder true-listp)
                       (stack true-listp))
    :well-founded-relation nat-list-<
    :measure (list
              (if (member x (graph-nodes))
                  (len (set-difference$ (graph-nodes) preorder))
                (+ 1 (len (set-difference$ (graph-nodes) preorder))))
              0
              1)
    :verify-guards nil
    :returns (mv (lowlink natp :rule-classes :type-prescription)
                 (new-preorder true-listp :rule-classes :type-prescription)
                 (new-stack true-listp :rule-classes :type-prescription)
                 (sccs true-list-listp))
    (b* ((preorder (mbe :logic (list-fix preorder) :exec preorder))
         (stack (mbe :logic (list-fix stack) :exec stack))
         (index (index-of x preorder))
         ((when index)
          (mv (if (member-equal x stack)
                  index
                (len preorder))
              preorder
              stack
              nil))
         (index (len preorder))
         (preorder (append preorder (list x)))
         (prev-stack stack)
         (stack (cons x stack))
         (successors (graph-node-succs x))
         ((mv lowlink preorder stack sccs)
          (tarjan-sccs-list successors preorder stack))
         (lowlink (min lowlink index))
         ((unless (eql lowlink index))
          ;; lower-numbered node is reachable, scc is not yet complete
          (mv lowlink preorder stack sccs))
         (new-scc (take (- (len stack) (len prev-stack)) stack)))
      (mv index preorder prev-stack (cons new-scc sccs))))

  (define tarjan-sccs-list (x
                            (preorder true-listp)
                            (stack true-listp))
    :returns (mv (lowlink natp :rule-classes :type-prescription)
                 (new-preorder true-listp :rule-classes :type-prescription)
                 (new-stack true-listp :rule-classes :type-prescription)
                 (sccs true-list-listp))
    :measure (list
              (if (subsetp x (graph-nodes))
                  (len (set-difference$ (graph-nodes) preorder))
                (+ 1 (len (set-difference$ (graph-nodes) preorder))))
              (len x)
              0)
    (b* ((preorder (mbe :logic (list-fix preorder) :exec preorder))
         (stack (mbe :logic (list-fix stack) :exec stack))
         ((when (atom x))
          (mv (len preorder) preorder stack nil))
         ((mv lowlink1 preorder stack sccs1)
          (b* (((mv lowlink1 new-preorder new-stack sccs1)
                (tarjan-sccs (car x) preorder stack))
               ((unless (mbt (<= (len (set-difference$ (graph-nodes) new-preorder))
                                 (len (set-difference$ (graph-nodes) preorder)))))
                (mv (len preorder) preorder stack nil)))
            (mv lowlink1 new-preorder new-stack sccs1)))
         ((mv lowlink2 preorder stack sccs2)
          (tarjan-sccs-list (cdr x) preorder stack)))
      (mv (min lowlink1 lowlink2) preorder stack
          (append sccs1 sccs2))))
  ///
  (local (defthm suffixp-transitive1
           (implies (and (suffixp a b)
                         (suffixp b c))
                    (suffixp a c))
           :hints(("Goal" :in-theory (enable suffixp)))))

  (local (defthm suffixp-transitive2
           (implies (and (suffixp b c)
                         (suffixp a b))
                    (suffixp a c))
           :hints(("Goal" :in-theory (enable suffixp)))))

  (local (defthm suffixp-self
           (suffixp x x)
           :hints(("Goal" :in-theory (enable suffixp)))))

  (local (defthm suffixp-cons
           (suffixp x (cons a x))
           :hints(("Goal" :in-theory (enable suffixp)))))

  (local (defthm prefixp-transitive1
           (implies (and (prefixp a b)
                         (prefixp b c))
                    (prefixp a c))
           :hints(("Goal" :in-theory (enable prefixp)))))

  (local (defthm prefixp-transitive2
           (implies (and (prefixp b c)
                         (prefixp a b))
                    (prefixp a c))
           :hints(("Goal" :in-theory (enable prefixp)))))

  (local (defthm prefixp-self
           (prefixp x x)
           :hints(("Goal" :in-theory (enable prefixp)))))

  (local (defthm prefixp-append
           (prefixp x (append x a))
           :hints(("Goal" :in-theory (enable prefixp)))))

  (local (fty::deffixcong list-equiv equal (prefixp x y) x
           :hints(("Goal" :in-theory (enable prefixp)))))
  (local (fty::deffixcong list-equiv equal (prefixp x y) y
           :hints(("Goal" :in-theory (enable prefixp)))))


  (std::defret-mutual tarjan-sccs-extend-preorder
    (defret tarjan-sccs-extend-preorder
      (prefixp preorder new-preorder)
      :hints ('(:expand (<call>)))
      :fn tarjan-sccs)
    (defret tarjan-sccs-list-extend-preorder
      (prefixp preorder new-preorder)
      :hints ('(:expand (<call>)))
      :fn tarjan-sccs-list))

  (std::defret-mutual tarjan-sccs-extend-stack
    (defret tarjan-sccs-extend-stack
      (suffixp (list-fix stack) new-stack)
      :hints ('(:expand (<call>)))
      :fn tarjan-sccs)
    (defret tarjan-sccs-list-extend-stack
      (suffixp (list-fix stack) new-stack)
      :hints ('(:expand (<call>)))
      :fn tarjan-sccs-list))

  (local (defthm set-difference-of-suffix
           (implies (suffixp a b)
                    (<= (len (set-difference$ x b))
                        (len (set-difference$ x a))))
           :hints(("Goal" :in-theory (enable suffixp)))
           :rule-classes (:rewrite :linear)))

  (local (defthm member-when-prefixp
           (implies (and (prefixp a b)
                         (member k a))
                    (member k b))
           :hints(("Goal" :in-theory (enable prefixp)))))

  (local (defthm set-difference-of-prefix
           (implies (prefixp a b)
                    (<= (len (set-difference$ x b))
                        (len (set-difference$ x a))))
           :hints(("Goal" :in-theory (enable prefixp set-difference$)))
           :rule-classes (:rewrite :linear)))

  (local (defthm len-of-suffix
           (implies (suffixp a b)
                    (<= (len a) (len b)))
           :hints(("Goal" :in-theory (enable suffixp)))
           :rule-classes (:rewrite :linear)))

  (local (defthm len-of-prefix
           (implies (prefixp a b)
                    (<= (len a) (len b)))
           :hints(("Goal" :in-theory (enable prefixp)))
           :rule-classes (:rewrite :linear)))

  (local (defret len-of-tarjan-sccs-list-stack
           (<= (len stack)
               (len new-stack))
           :hints (("goal" :use ((:instance len-of-suffix
                                  (a (list-fix stack)) (b new-stack)))
                    :in-theory (disable len-of-suffix)))
           :fn tarjan-sccs-list
           :rule-classes :linear))

  (defret set-difference-of-tarjan-sccs-preorder
    (<= (len (set-difference$ (graph-nodes) new-preorder))
        (len (set-difference$ (graph-nodes) preorder)))
    :hints(("Goal" :use ((:instance set-difference-of-suffix
                          (a preorder)
                          (b new-preorder)
                          (x (graph-nodes))))
            :in-theory (disable set-difference-of-suffix)))
    :fn tarjan-sccs
    :rule-classes :linear)

  (verify-guards tarjan-sccs
    :hints (("goal" :do-not-induct t))
    :otf-flg t)

  (fty::deffixequiv-mutual tarjan-sccs)

  (local (in-theory (disable NFIX-POSITIVE-TO-NON-ZP NFIX-GT-0 DEFAULT-<-1)))

  (local (defthm subsetp-when-suffix
           (implies (suffixp a b)
                    (subsetp a b))
           :hints(("Goal" :in-theory (enable suffixp)))))

  (local (defthm subsetp-when-prefix
           (implies (prefixp a b)
                    (subsetp a b))
           :hints(("Goal" :in-theory (enable prefixp)))))

  (local (defret preorder-prefix-of-tarjan-sccs-list-of-append
           (prefixp preorder
                    (let ((preorder (append preorder add)))
                      (mv-nth 1 <call>)))
           :hints (("goal" :use ((:instance tarjan-sccs-list-extend-preorder
                                  (preorder (append preorder add))))
                    :in-theory (e/d ()
                                    (tarjan-sccs-list-extend-preorder))))
           :fn tarjan-sccs-list))


  (std::defret-mutual tarjan-sccs-preserve-stack-subset-of-preorder
    (defret tarjan-sccs-preserve-stack-subset-of-preorder
      (implies (subsetp stack preorder)
               (subsetp new-stack new-preorder))
      :hints ('(:expand (<call>)))
      :fn tarjan-sccs)
    (defret tarjan-sccs-list-preserve-stack-subset-of-preorder
      (implies (subsetp stack preorder)
               (subsetp new-stack new-preorder))
      :hints ('(:expand (<call>)))
      :fn tarjan-sccs-list))

  (std::defret-mutual tarjan-sccs-preserves-stack-no-duplicates
    (defret tarjan-sccs-preserves-stack-no-duplicates
      (implies (and (subsetp stack preorder)
                    (no-duplicatesp stack))
               (no-duplicatesp new-stack))
      :hints ('(:expand (<call>)))
      :fn tarjan-sccs)
    (defret tarjan-sccs-list-preserve-stack-no-duplicates
      (implies (and (subsetp stack preorder)
                    (no-duplicatesp stack))
               (no-duplicatesp new-stack))
      :hints ('(:expand (<call>)))
      :fn tarjan-sccs-list)))





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

(local (defthm butlast-when-len-less
           (implies (<= (len x) (nfix n))
                    (equal (butlast x n) nil))))

(local (defthm butlast-when-len-greater
         (implies (< (nfix n) (len x))
                  (equal (butlast x n)
                         (cons (car x) (butlast (cdr x) n))))))

(local (defthm butlast-of-append
         (equal (butlast (append x y) n)
                (if (<= (nfix n) (len y))
                    (append x (butlast y n))
                  (butlast x (- (nfix n) (len y)))))))

(local (defthm no-intersectp-of-butlast
         (implies (not (intersectp x y))
                  (not (intersectp (butlast x n) y)))
         :hints(("Goal" :in-theory (enable intersectp)))))

(local (defthm index-of-type-when-member
         (implies (member x y)
                  (natp (index-of x y)))
         :rule-classes :type-prescription))

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


(local (defthm car-last-of-append
         (equal (car (last (append x y)))
                (if (consp y)
                    (car (last y))
                  (car (last x))))))

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

  (local (defthm intersectp-of-butlast-of-member
           (implies (not (intersectp (butlast x n) y))
                    (not (intersectp (butlast (member k x) n) y)))
           :hints(("Goal" :in-theory (e/d (intersectp)
                                          (butlast))))))

  (defret no-intersection-of-graph-path-reduce-but-last
    (implies (not (intersectp-equal (butlast x 1) y))
             (not (intersectp-equal (butlast reduced-path 1) y)))
    :hints(("Goal" :in-theory (e/d (intersectp-equal)
                                   (butlast))))))

(defsection graph-reachable-through-unvisited
  (defun-sk graph-reachable-through-unvisited-p (x y visited)
    (exists path
            (and (consp path)
                 (graph-path-p path)
                 (equal x (car path))
                 (equal y (car (last path)))
                 (not (intersectp-equal path visited)))))

  (in-theory (disable graph-reachable-through-unvisited-p))

  (defthm graph-reachable-through-unvisited-of-successors
    (implies (and (graph-reachable-through-unvisited-p x y visited)
                  (member z (graph-node-succs y))
                  (not (member z visited)))
             (graph-reachable-through-unvisited-p x z visited))
    :hints (("goal" :expand ((graph-reachable-through-unvisited-p x y visited))
             :use ((:instance graph-reachable-through-unvisited-p-suff
                    (x x) (y z) (path (append (graph-reachable-through-unvisited-p-witness x y visited)
                                              (list z)))))
             :in-theory (e/d (intersectp-equal)
                             (graph-reachable-through-unvisited-p-suff)))))

  (defthm graph-reachable-through-unvisited-of-immediate-successors
    (implies (and (member z (graph-node-succs y))
                  (not (member z visited))
                  (not (member y visited)))
             (graph-reachable-through-unvisited-p y z visited))
    :hints (("goal" :use ((:instance graph-reachable-through-unvisited-p-suff
                           (x y) (y z) (path (list y z))))
             :in-theory (enable graph-path-p intersectp-equal))))


  (defthm graph-reachable-through-unvisited-transitive1
    (implies (and (graph-reachable-through-unvisited-p x y visited)
                  (graph-reachable-through-unvisited-p y z visited))
             (graph-reachable-through-unvisited-p x z visited))
    :hints (("goal" :expand ((graph-reachable-through-unvisited-p x y visited)
                             (graph-reachable-through-unvisited-p y z visited))
             :in-theory (e/d (intersectp-equal)
                             (graph-reachable-through-unvisited-p-suff))
             :use ((:instance graph-reachable-through-unvisited-p-suff
                    (x x) (y z) (path (append (graph-reachable-through-unvisited-p-witness x y visited)
                                              (cdr (graph-reachable-through-unvisited-p-witness y z visited)))))))))

  (defthm graph-reachable-through-unvisited-transitive2
    (implies (and (graph-reachable-through-unvisited-p y z visited)
                  (graph-reachable-through-unvisited-p x y visited))
             (graph-reachable-through-unvisited-p x z visited)))

  (fty::deffixequiv graph-reachable-through-unvisited-p
    :args ((visited true-listp))
    :hints (("goal" :cases ((graph-reachable-through-unvisited-p x y visited)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'graph-reachable-through-unvisited-p clause))
                      ((unless lit) nil)
                      (other (if (equal (nth 3 lit) 'visited)
                                 '(list-fix visited)
                               'visited)))
                   `(:expand (,(update-nth 3 other lit))
                     :use ((:instance graph-reachable-through-unvisited-p-suff
                            (visited ,(nth 3 lit))
                            (path (graph-reachable-through-unvisited-p-witness
                                   . ,(cdr (update-nth 3 other lit)))))))))))

  (defthm graph-reachable-through-unvisited-p-self
    (implies (not (member x preorder))
             (graph-reachable-through-unvisited-p x x preorder))
    :hints (("goal" :use ((:instance graph-reachable-through-unvisited-p-suff
                           (y x) (path (list x)) (visited preorder)))
             :in-theory (e/d (graph-path-p intersectp-equal)
                             (graph-reachable-through-unvisited-p-suff)))))

  (defthm not-graph-reachable-through-unvisited-p-when-member-first
    (implies (member x visited)
             (not (graph-reachable-through-unvisited-p x y visited)))
    :hints(("Goal" :in-theory (enable graph-reachable-through-unvisited-p
                                      intersectp-equal))))

  (local (defthm intersectp-when-member-last
           (implies (and (member (car (last x)) y)
                         (consp x))
                    (intersectp x y))
           :hints(("Goal" :in-theory (enable intersectp)))))

  (defthm not-graph-reachable-through-unvisited-p-when-member-last
    (implies (member y visited)
             (not (graph-reachable-through-unvisited-p x y visited)))
    :hints(("Goal" :in-theory (enable graph-reachable-through-unvisited-p
                                      intersectp-equal))))

  (defthm graph-reachable-through-unvisited-p-of-preorder-extension
    (implies (and (not (graph-reachable-through-unvisited-p x y preorder))
                  (subsetp preorder new-preorder))
             (not (graph-reachable-through-unvisited-p x y new-preorder)))
    :hints (("goal" :expand ((graph-reachable-through-unvisited-p x y new-preorder))
             :use ((:instance graph-reachable-through-unvisited-p-suff
                    (visited preorder)
                    (path (graph-reachable-through-unvisited-p-witness x y new-preorder))))
             :in-theory (e/d (intersectp-by-subsetp)
                             (graph-reachable-through-unvisited-p-suff))))))

(define graph-reachable-through-unvisited-canonical-witness (x y preorder)
  (graph-path-reduce (graph-reachable-through-unvisited-p-witness x y preorder))
  ///
  (defthm graph-reachable-through-unvisited-implies-canonical-witness
    (implies (graph-reachable-through-unvisited-p x y preorder)
             (let ((path (graph-reachable-through-unvisited-canonical-witness x y preorder)))
               (and (consp path)
                    (graph-path-p path)
                    (equal (car path) x)
                    (equal (car (last path)) y)
                    (not (intersectp-equal path preorder)))))
    :hints (("goal" :expand ((graph-reachable-through-unvisited-p x y preorder)))))

  (defthm no-duplicatesp-of-graph-reachable-through-unvisited-canonical-witness
    (no-duplicatesp (graph-reachable-through-unvisited-canonical-witness x y preorder)))

  (defthm graph-reachable-through-unvisited-implies-x-not-in-cdr-of-canonical-witness
    (implies (graph-reachable-through-unvisited-p x y preorder)
             (let ((path (graph-reachable-through-unvisited-canonical-witness x y preorder)))
               (not (member x (cdr path)))))
    :hints (("goal" :use no-duplicatesp-of-graph-reachable-through-unvisited-canonical-witness
             :in-theory (e/d (no-duplicatesp)
                             (no-duplicatesp-of-graph-reachable-through-unvisited-canonical-witness
                              graph-reachable-through-unvisited-canonical-witness)))))

  (defthm graph-reachable-through-unvisited-implies-graph-path-p-cdr-of-canonical-witness
    (implies (graph-reachable-through-unvisited-p x y preorder)
             (let ((path (graph-reachable-through-unvisited-canonical-witness x y preorder)))
               (graph-path-p (cdr path))))
    :hints (("goal" :use graph-reachable-through-unvisited-implies-canonical-witness
             :in-theory (e/d (graph-path-p)
                             (graph-reachable-through-unvisited-implies-canonical-witness
                              graph-reachable-through-unvisited-canonical-witness)))))

  (defthm graph-reachable-through-unvisited-implies-cadr-successor-of-x-of-canonical-witness
    (implies (and (graph-reachable-through-unvisited-p x y preorder)
                  (not (equal x y)))
             (let ((path (graph-reachable-through-unvisited-canonical-witness x y preorder)))
               (member (cadr path) (graph-node-succs x))))
    :hints (("goal" :use (graph-reachable-through-unvisited-implies-canonical-witness)
             :in-theory (e/d (graph-path-p)
                             (graph-reachable-through-unvisited-implies-canonical-witness
                              graph-reachable-through-unvisited-canonical-witness)))))

  (defthm graph-reachable-through-unvisited-implies-no-intersect-cdr-of-canonical-witness
    (implies (graph-reachable-through-unvisited-p x y preorder)
             (let ((path (graph-reachable-through-unvisited-canonical-witness x y preorder)))
               (not (intersectp-equal (cdr path) preorder))))
    :hints (("goal" :use graph-reachable-through-unvisited-implies-canonical-witness
             :in-theory (e/d (intersectp-equal)
                             (graph-reachable-through-unvisited-implies-canonical-witness
                              graph-reachable-through-unvisited-canonical-witness)))))

  (defwitness graph-reachable-through-unvisited-witness
    :predicate (graph-reachable-through-unvisited-p x y preorder)
    :expr (let ((path (graph-reachable-through-unvisited-canonical-witness x y preorder)))
               (and (consp path)
                    (graph-path-p path)
                    (equal (car path) x)
                    (equal (car (last path)) y)
                    (not (intersectp path preorder))
                    (no-duplicatesp path)))
    :generalize (((graph-reachable-through-unvisited-canonical-witness x y preorder) . reachupath))
    :hints ('(:use (graph-reachable-through-unvisited-implies-canonical-witness
                    no-duplicatesp-of-graph-reachable-through-unvisited-canonical-witness)
              :in-theory (disable graph-reachable-through-unvisited-implies-canonical-witness
                                  no-duplicatesp-of-graph-reachable-through-unvisited-canonical-witness))))

  (defthmd graph-reachable-through-unvisited-iff-canonical-witness
    (implies (rewriting-negative-literal `(graph-reachable-through-unvisited-p ,x ,y ,preorder))
             (iff (graph-reachable-through-unvisited-p x y preorder)
                  (let ((path (graph-reachable-through-unvisited-canonical-witness x y preorder)))
                    (and (consp path)
                         (graph-path-p path)
                         (equal (car path) x)
                         (equal (car (last path)) y)
                         (not (intersectp-equal path preorder))
                         (no-duplicatesp path)))))
    :hints (("goal" :use ((:instance graph-reachable-through-unvisited-p-suff
                           (visited preorder)
                           (path (graph-reachable-through-unvisited-canonical-witness x y preorder)))))
            (and stable-under-simplificationp
                 '(:expand ((graph-reachable-through-unvisited-p x y preorder)))))))




(define graph-reachable-through-unvisited-for-some-x (x y (preorder true-listp))
  :returns (reachable)
  :hooks (:fix)
  (if (atom x)
      nil
    (or (ec-call (graph-reachable-through-unvisited-p (car x) y preorder))
        (graph-reachable-through-unvisited-for-some-x (cdr x) y preorder)))
  ///
  (defret graph-reachable-through-unvisited-for-some-x-when-empty
    (implies (not (consp x))
             (not reachable))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defret graph-reachable-through-unvisited-for-some-x-when-reachable-by-member
    (implies (and (graph-reachable-through-unvisited-p k y preorder)
                  (member k x))
             (graph-reachable-through-unvisited-for-some-x x y preorder)))

  (defthm graph-reachable-through-unvisited-for-some-x-by-path
    (implies (and (graph-path-p path)
                  (consp path)
                  (member (car path) x)
                  (equal y (car (last path)))
                  (not (intersectp path preorder)))
             (graph-reachable-through-unvisited-for-some-x x y preorder))
    :hints (("Goal" :induct (graph-reachable-through-unvisited-for-some-x x y preorder))))

  (local (defthmd consp-cdr-when-car-not-equal-last
           (implies (not (equal (car x) (car (last x))))
                    (consp (cdr x)))))

  (local (defthm last-is-last-of-cdr
           (implies (consp (cdr x))
                    (equal (last (cdr x))
                           (last x)))))

  ;; (local (in-theory (disable last)))
  (local (defun graph-reachable-through-unvisited-implies-reachable-for-some-successor-hint (x y preorder)
           ;; x has a path to y in the preorder.
           (b* ((x-y (graph-reachable-through-unvisited-canonical-witness x y preorder))
                (new-preorder (append preorder (list x)))
                ;; ((unless (consp (cdr x-y)))
                ;;  ;; Must be because x not equal y.
                ;;  `'(:use ((:instance consp-cdr-when-car-not-equal-last
                ;;            (x ,(hq x-y))))))
                (succ (cadr x-y))
                (succ-y (cdr x-y))
                ((unless (and (consp (cdr x-y))
                              (member succ (graph-node-succs x))
                              (graph-path-p succ-y)))
                 `'(:use ((:instance graph-reachable-through-unvisited-implies-canonical-witness))
                    :expand ((graph-path-p ,(hq x-y)))
                    :in-theory (disable graph-reachable-through-unvisited-implies-canonical-witness)))
                ((unless (intersectp succ-y new-preorder))
                 (b* (((unless (graph-reachable-through-unvisited-p succ y new-preorder))
                       `'(:use ((:instance graph-reachable-through-unvisited-p-suff
                                 (x ,(hq succ)) (visited ,(hq new-preorder))
                                 (path ,(hq succ-y)))))))
                   `'(:use ((:instance graph-reachable-through-unvisited-for-some-x-when-reachable-by-member
                             (x ,(hq (graph-node-succs x)))
                             (k ,(hq succ)) (preorder ,(hq new-preorder)))))))
                ((unless (member x succ-y))
                 ;; done too?
                 nil))
             `'(:use ((:instance no-duplicatesp-of-graph-reachable-through-unvisited-canonical-witness))
                :expand ((no-duplicatesp ,(hq x-y)))
                :in-theory (disable no-duplicatesp-of-graph-reachable-through-unvisited-canonical-witness)))))


  (defthm graph-reachable-through-unvisited-implies-reachable-for-some-successor
    (implies (and (graph-reachable-through-unvisited-p x y preorder)
                  (not (equal x y)))
             (graph-reachable-through-unvisited-for-some-x
              (graph-node-succs x) y (append preorder (list x))))
    :hints (("goal" :in-theory (disable graph-reachable-through-unvisited-for-some-x-when-reachable-by-member
                                        graph-reachable-through-unvisited-p-suff)
             :do-not-induct t)
            (use-termhint (graph-reachable-through-unvisited-implies-reachable-for-some-successor-hint x y preorder)))))

(define graph-reachable-through-unvisited-for-some-x-witness (x y preorder)
  :verify-guards nil
  (if (atom x)
      nil
    (if (graph-reachable-through-unvisited-p (car x) y preorder)
        (graph-reachable-through-unvisited-canonical-witness (car x) y preorder)
      (graph-reachable-through-unvisited-for-some-x-witness (cdr x) y preorder)))
  ///
  (local (in-theory (enable graph-reachable-through-unvisited-for-some-x)))

  (defthm graph-reachable-through-unvisited-for-some-x-implies-witness
    (implies (graph-reachable-through-unvisited-for-some-x x y preorder)
             (b* ((path (graph-reachable-through-unvisited-for-some-x-witness x y preorder)))
               (and (consp path)
                    (member (car path) x)
                    (equal (car (last path)) y)
                    (graph-path-p path)
                    (not (intersectp path preorder))
                    (no-duplicatesp path)))))

  (in-theory (disable graph-reachable-through-unvisited-for-some-x-witness))

  (defthm graph-reachable-through-unvisited-for-some-successor-implies-reachable
    (implies (and (graph-reachable-through-unvisited-for-some-x
                   (graph-node-succs x) y (append preorder (list x)))
                  (not (member x preorder)))
             (graph-reachable-through-unvisited-p x y preorder))
    :hints (("goal" :use ((:instance graph-reachable-through-unvisited-for-some-x-implies-witness
                           (x (graph-node-succs x))
                           (preorder (append preorder (list x))))
                          (:instance graph-reachable-through-unvisited-p-suff
                           (visited preorder)
                           (path (cons x (graph-reachable-through-unvisited-for-some-x-witness
                                          (graph-node-succs x) y (append preorder (list x)) )))))
             :in-theory (e/d (intersectp)
                             (graph-reachable-through-unvisited-for-some-x-implies-witness
                              graph-reachable-through-unvisited-p-suff
                              graph-reachable-through-unvisited-for-some-x))
             :do-not-induct t)))

  (defwitness graph-reachable-through-unvisited-for-some-x-witness
    :predicate (graph-reachable-through-unvisited-for-some-x x y preorder)
    :expr (let ((path (graph-reachable-through-unvisited-for-some-x-witness x y preorder)))
               (and (consp path)
                    (graph-path-p path)
                    (member (car path) x)
                    (equal (car (last path)) y)
                    (not (intersectp path preorder))
                    (no-duplicatesp path)))
    :generalize (((graph-reachable-through-unvisited-canonical-witness x y preorder) . reachupath))
    :hints ('(:use graph-reachable-through-unvisited-for-some-x-implies-witness
              :in-theory (disable graph-reachable-through-unvisited-for-some-x-implies-witness)))))




(defsection tarjan-preorder-member-cond
  (defun-sk tarjan-preorder-member-cond (x preorder new-preorder)
    (forall y
            (iff (member y new-preorder)
                 (or (member y preorder)
                     (graph-reachable-through-unvisited-p x y preorder))))
    :rewrite :direct)
  (in-theory (disable tarjan-preorder-member-cond))

  (fty::deffixequiv tarjan-preorder-member-cond
    :args ((preorder true-listp)
           (new-preorder true-listp))
    :hints (("goal" :cases ((tarjan-preorder-member-cond x preorder new-preorder)))
            (and stable-under-simplificationp
                 (let ((pos-lit (assoc 'tarjan-preorder-member-cond clause))
                       (neg-lit (cadr (assoc 'not clause))))
                   `(:expand (,pos-lit)
                     :use ((:instance tarjan-preorder-member-cond-necc
                            (x ,(nth 1 neg-lit))
                            (preorder ,(nth 2 neg-lit))
                            (new-preorder ,(nth 3 neg-lit))
                            (y (tarjan-preorder-member-cond-witness . ,(cdr pos-lit))))))))))

  (defthm tarjan-preorder-member-cond-implies-intersect
    (implies (and (not (intersectp z new-preorder))
                  (intersectp z preorder))
             (not (tarjan-preorder-member-cond x preorder new-preorder)))
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
  ;; reachable-through-unvisited-but-last) are the crux for reasoning that the
  ;; nodes reachable through unvisited from a set of nodes is consistent with
  ;; the nodes reachable from the first node, or from the rest of the set when
  ;; considering those visited from the first.  I.e., a priori, a node y
  ;; reachable through unvisited from z may not still be reachable after
  ;; visiting nodes reachable from x.  But we prove that either it is still
  ;; reachable from z or it was reachable from x.

  ;; This is the other direction -- adding nodes to the preorder does not let
  ;; new nodes become reachable through unvisited.
  (defthm reachable-through-unvisited-by-member-cond-1
    (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                  (not (graph-reachable-through-unvisited-p z y preorder)))
             (not (graph-reachable-through-unvisited-p z y new-preorder)))
    :hints (("goal" :expand ((graph-reachable-through-unvisited-p z y new-preorder))
             :use ((:instance graph-reachable-through-unvisited-p-suff
                    (x z) (visited preorder)
                    (path (graph-reachable-through-unvisited-p-witness z y new-preorder))))))
    :rule-classes ((:rewrite :match-free :all)))



  (local (defun reachable-through-unvisited-by-member-cond-2-hint (x y z preorder new-preorder)
           ;; Hyp assumes z reaches y in preorder.
           (b* ((z-y (graph-reachable-through-unvisited-canonical-witness z y preorder))
                ;; If that doesn't intersect the new preorder, then z reaches y
                ;; via that same path in the new preorder.
                ((unless (intersectp z-y new-preorder))
                 `'(:use ((:instance graph-reachable-through-unvisited-p-suff
                           (x z) (visited new-preorder)
                           (path ,(hq z-y))))
                    :in-theory (disable graph-reachable-through-unvisited-p-suff)))
                (int (intersectp-witness z-y new-preorder))
                ((when (member int preorder))
                 ;; this can't be true because it's a member of z-y
                 `'(:use ((:instance intersectp-member
                           (a ,(hq int))
                           (x ,(hq z-y))
                           (y ,(hq preorder))))
                    :in-theory (disable intersectp-member)))
                ;; Since this is a member of new-preorder it's reachable from x
                ((unless (graph-reachable-through-unvisited-p x int preorder))
                 `'(:use ((:instance tarjan-preorder-member-cond-necc
                           (y ,(hq int))))
                    :in-theory (disable tarjan-preorder-member-cond-necc)))
                (x-int (graph-reachable-through-unvisited-canonical-witness x int preorder))
                (x-y (append x-int (cdr (member int z-y)))))
             `'(:use ((:instance graph-reachable-through-unvisited-p-suff
                       (path ,(hq x-y)) (visited preorder)))
                :in-theory (disable graph-reachable-through-unvisited-p-suff)))))


  ;; This is the hard direction: if y is not reachable-through-unvisited from
  ;; x, then it remains reachable from z (if it was before) after adding the
  ;; nodes reachable from x to the visited set.
  (defthm reachable-through-unvisited-by-member-cond-2
    (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                  (graph-reachable-through-unvisited-p z y preorder)
                  (not (graph-reachable-through-unvisited-p x y preorder)))
             (graph-reachable-through-unvisited-p z y new-preorder))
    :hints ((use-termhint (reachable-through-unvisited-by-member-cond-2-hint
                           x y z preorder new-preorder))))

  (defthm reachable-through-unvisited-for-some-x-by-member-cond-1
    (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                  (not (graph-reachable-through-unvisited-for-some-x z y preorder)))
             (not (graph-reachable-through-unvisited-for-some-x z y new-preorder)))
    :hints(("Goal" :in-theory (enable graph-reachable-through-unvisited-for-some-x)))
    :rule-classes ((:rewrite :match-free :all)))

  (defthm reachable-through-unvisited-for-some-x-by-member-cond-2
    (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                  (not (graph-reachable-through-unvisited-p x y preorder))
                  (graph-reachable-through-unvisited-for-some-x z y preorder))
             (graph-reachable-through-unvisited-for-some-x z y new-preorder))
    :hints(("Goal" :in-theory (enable graph-reachable-through-unvisited-for-some-x)))
    :rule-classes ((:rewrite :match-free :all))))

(defsection tarjan-preorder-member-cond-list
  (defun-sk tarjan-preorder-member-cond-list (x preorder new-preorder)
    (forall y
            (iff (member y new-preorder)
                 (or (member y preorder)
                     (graph-reachable-through-unvisited-for-some-x x y preorder))))
    :rewrite :direct)
  (in-theory (disable tarjan-preorder-member-cond-list))

  (fty::deffixequiv tarjan-preorder-member-cond-list
    :args ((preorder true-listp)
           (new-preorder true-listp))
    :hints (("goal" :cases ((tarjan-preorder-member-cond-list x preorder new-preorder)))
            (and stable-under-simplificationp
                 (let ((pos-lit (assoc 'tarjan-preorder-member-cond-list clause))
                       (neg-lit (cadr (assoc 'not clause))))
                   `(:expand (,pos-lit)
                     :use ((:instance tarjan-preorder-member-cond-list-necc
                            (x ,(nth 1 neg-lit))
                            (preorder ,(nth 2 neg-lit))
                            (new-preorder ,(nth 3 neg-lit))
                            (y (tarjan-preorder-member-cond-list-witness . ,(cdr pos-lit))))))))))

  (local (defthm intersectp-preorder-implies-intersectp-new-preorder
           (implies (and (tarjan-preorder-member-cond-list x preorder new-preorder)
                         (intersectp y preorder))
                    (intersectp y new-preorder))
           :hints ((set-reasoning))))

  (defthm reachable-through-unvisited-list-extension-by-member-cond-1
    (implies (and (tarjan-preorder-member-cond-list x preorder new-preorder)
                  (not (graph-reachable-through-unvisited-p z y preorder)))
             (not (graph-reachable-through-unvisited-p z y new-preorder)))
    :hints (("goal" :expand ((graph-reachable-through-unvisited-p z y new-preorder))
             :use ((:instance graph-reachable-through-unvisited-p-suff
                    (x z) (visited preorder)
                    (path (graph-reachable-through-unvisited-p-witness z y new-preorder))))))
    :rule-classes ((:rewrite :match-free :all)))

  (defthm reachable-through-unvisited-list-extension-for-some-x-by-member-cond-1
    (implies (and (tarjan-preorder-member-cond-list x preorder new-preorder)
                  (not (graph-reachable-through-unvisited-for-some-x z y preorder)))
             (not (graph-reachable-through-unvisited-for-some-x z y new-preorder)))
    :hints(("Goal" :in-theory (enable graph-reachable-through-unvisited-for-some-x)))
    :rule-classes ((:rewrite :match-free :all))))




;; First major property of the tarjan-sccs algorithm (and basically any
;; depth-first search): the new preorder after finishing traversal of a node
;; satisfies the preorder member condition, i.e. it contains those nodes that
;; were already in the preorder, or were reachable from the node traversed
;; without intersecting the original preorder.
(std::defret-mutual tarjan-sccs-preorder-member-cond
  (defret tarjan-sccs-preorder-member-cond
    (tarjan-preorder-member-cond x preorder new-preorder)
    :hints ('(:expand (<call>))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))
            (and stable-under-simplificationp
                 (let ((witness (find-call-lst
                                 'tarjan-preorder-member-cond-witness
                                 clause)))
                   (and witness
                        `(:clause-processor
                          (simple-generalize-cp
                           clause '((,witness . witness))))))))
    :fn tarjan-sccs)

  (defret tarjan-sccs-list-preorder-member-cond
    (tarjan-preorder-member-cond-list x preorder new-preorder)
    :hints ('(:expand (<call>))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause))
                            (:free (y)
                             (graph-reachable-through-unvisited-for-some-x
                              x y preorder)))))
            (and stable-under-simplificationp
                 (let ((witness (find-call-lst
                                 'tarjan-preorder-member-cond-list-witness
                                 clause)))
                   (and witness
                        `(:clause-processor
                          (simple-generalize-cp
                           clause '((,witness . witness))))))))
    :fn tarjan-sccs-list))













(defsection graph-reachable-through-unvisited-but-last
  (defun-sk graph-reachable-through-unvisited-but-last-p (x y visited)
    (exists path
            (and (consp path)
                 (graph-path-p path)
                 (equal x (car path))
                 (equal y (car (last path)))
                 (not (intersectp-equal (butlast path 1) visited)))))

  (in-theory (disable graph-reachable-through-unvisited-but-last-p))

  (defthm graph-reachable-through-unvisited-but-last-of-successors
    (implies (and (graph-reachable-through-unvisited-p x y visited)
                  (member z (graph-node-succs y)))
             (graph-reachable-through-unvisited-but-last-p x z visited))
    :hints (("goal" :expand ((graph-reachable-through-unvisited-p x y visited))
             :use ((:instance graph-reachable-through-unvisited-but-last-p-suff
                    (x x) (y z) (path (append (graph-reachable-through-unvisited-p-witness x y visited)
                                              (list z)))))
             :in-theory (e/d (intersectp-equal)
                             (graph-reachable-through-unvisited-but-last-p-suff)))))

  (defthm graph-reachable-through-unvisited-but-last-of-immediate-successors
    (implies (and (member z (graph-node-succs y))
                  (not (member y visited)))
             (graph-reachable-through-unvisited-but-last-p y z visited))
    :hints (("goal" :use ((:instance graph-reachable-through-unvisited-but-last-p-suff
                           (x y) (y z) (path (list y z))))
             :in-theory (enable graph-path-p intersectp-equal))))

  (defthm graph-reachable-through-unvisited-but-last-of-self
    (graph-reachable-through-unvisited-but-last-p x x visited)
    :hints (("goal" :use ((:instance graph-reachable-through-unvisited-but-last-p-suff
                           (x x) (y x) (path (list x))))
             :in-theory (enable graph-path-p intersectp-equal))))

  (local (defthm len-when-car-not-equal-car-last
           (implies (not (equal (car x) (car (last x))))
                    (< 1 (len x)))
           :rule-classes :linear))

  (defthm graph-reachable-through-unvisited-but-last-p-when-start-node-visited
    (implies (member x visited)
             (iff (graph-reachable-through-unvisited-but-last-p x y visited)
                  (equal x y)))
    :hints ((and stable-under-simplificationp
                 '(:expand ((graph-reachable-through-unvisited-but-last-p x y visited)
                            ;; (butlast (graph-reachable-through-unvisited-but-last-p-witness x y visited) 1)
                            )
                   :in-theory (enable intersectp-equal)))))

  (fty::deffixequiv graph-reachable-through-unvisited-but-last-p
    :args ((visited true-listp))
    :hints (("goal" :cases ((graph-reachable-through-unvisited-but-last-p x y visited)))
            (and stable-under-simplificationp
                 (b* ((lit (assoc 'graph-reachable-through-unvisited-but-last-p clause))
                      ((unless lit) nil)
                      (other (if (equal (nth 3 lit) 'visited)
                                 '(list-fix visited)
                               'visited)))
                   `(:expand (,(update-nth 3 other lit))
                     :use ((:instance graph-reachable-through-unvisited-but-last-p-suff
                            (visited ,(nth 3 lit))
                            (path (graph-reachable-through-unvisited-but-last-p-witness
                                   . ,(cdr (update-nth 3 other lit)))))))))))

  (defthm graph-reachable-through-unvisited-but-last-when-reachable-through-unvisited
    (implies (graph-reachable-through-unvisited-p x y visited)
             (graph-reachable-through-unvisited-but-last-p x y visited))
    :hints (("goal" :expand ((graph-reachable-through-unvisited-p x y visited))
             :use ((:instance graph-reachable-through-unvisited-but-last-p-suff
                    (path (graph-reachable-through-unvisited-p-witness x y visited))))
             :in-theory (disable graph-reachable-through-unvisited-but-last-p-suff))))

  (defthm graph-reachable-through-unvisited-but-last-p-of-preorder-extension
    (implies (and (not (graph-reachable-through-unvisited-but-last-p x y preorder))
                  (subsetp preorder new-preorder))
             (not (graph-reachable-through-unvisited-but-last-p x y new-preorder)))
    :hints (("goal" :expand ((graph-reachable-through-unvisited-but-last-p x y new-preorder))
             :use ((:instance graph-reachable-through-unvisited-but-last-p-suff
                    (visited preorder)
                    (path (graph-reachable-through-unvisited-but-last-p-witness x y new-preorder))))
             :in-theory (e/d (intersectp-by-subsetp)
                             (graph-reachable-through-unvisited-but-last-p-suff)))))

  (defthm graph-reachable-through-unvisited-but-last-when-reachable-from-reachable
    (implies (and (graph-reachable-through-unvisited-p x y preorder)
                  (graph-reachable-through-unvisited-but-last-p y z preorder))
             (graph-reachable-through-unvisited-but-last-p x z preorder))
    :hints (("goal" :expand ((graph-reachable-through-unvisited-p x y preorder)
                             (graph-reachable-through-unvisited-but-last-p y z preorder))
             :use ((:instance graph-reachable-through-unvisited-but-last-p-suff
                    (y z) (visited preorder)
                    (path (append (graph-reachable-through-unvisited-p-witness x y preorder)
                                  (cdr (graph-reachable-through-unvisited-but-last-p-witness y z preorder))))))
             :in-theory (e/d (intersectp-equal)
                             (graph-reachable-through-unvisited-but-last-p-suff))))))



(define graph-reachable-through-unvisited-but-last-canonical-witness (x y preorder)
  (graph-path-reduce (graph-reachable-through-unvisited-but-last-p-witness x y preorder))
  ///
  (defthm graph-reachable-through-unvisited-but-last-implies-canonical-witness
    (implies (graph-reachable-through-unvisited-but-last-p x y preorder)
             (let ((path (graph-reachable-through-unvisited-but-last-canonical-witness x y preorder)))
               (and (consp path)
                    (graph-path-p path)
                    (equal (car path) x)
                    (equal (car (last path)) y)
                    (not (intersectp-equal (butlast path 1) preorder)))))
    :hints (("goal" :expand ((graph-reachable-through-unvisited-but-last-p x y preorder)))))

  (defthm no-duplicatesp-of-graph-reachable-through-unvisited-but-last-canonical-witness
    (no-duplicatesp (graph-reachable-through-unvisited-but-last-canonical-witness x y preorder)))

  (defthm graph-reachable-through-unvisited-but-last-implies-x-not-in-cdr-of-canonical-witness
    (implies (graph-reachable-through-unvisited-but-last-p x y preorder)
             (let ((path (graph-reachable-through-unvisited-but-last-canonical-witness x y preorder)))
               (not (member x (cdr path)))))
    :hints (("goal" :use no-duplicatesp-of-graph-reachable-through-unvisited-but-last-canonical-witness
             :in-theory (e/d (no-duplicatesp)
                             (no-duplicatesp-of-graph-reachable-through-unvisited-but-last-canonical-witness
                              graph-reachable-through-unvisited-but-last-canonical-witness)))))

  (defthm graph-reachable-through-unvisited-but-last-implies-graph-path-p-cdr-of-canonical-witness
    (implies (graph-reachable-through-unvisited-but-last-p x y preorder)
             (let ((path (graph-reachable-through-unvisited-but-last-canonical-witness x y preorder)))
               (graph-path-p (cdr path))))
    :hints (("goal" :use graph-reachable-through-unvisited-but-last-implies-canonical-witness
             :in-theory (e/d (graph-path-p)
                             (graph-reachable-through-unvisited-but-last-implies-canonical-witness
                              graph-reachable-through-unvisited-but-last-canonical-witness)))))

  (defthm graph-reachable-through-unvisited-but-last-implies-cadr-successor-of-x-of-canonical-witness
    (implies (and (graph-reachable-through-unvisited-but-last-p x y preorder)
                  (not (equal x y)))
             (let ((path (graph-reachable-through-unvisited-but-last-canonical-witness x y preorder)))
               (member (cadr path) (graph-node-succs x))))
    :hints (("goal" :use (graph-reachable-through-unvisited-but-last-implies-canonical-witness)
             :in-theory (e/d (graph-path-p)
                             (graph-reachable-through-unvisited-but-last-implies-canonical-witness
                              graph-reachable-through-unvisited-but-last-canonical-witness)))))

  (defthm graph-reachable-through-unvisited-but-last-implies-no-intersect-cdr-of-canonical-witness
    (implies (graph-reachable-through-unvisited-but-last-p x y preorder)
             (let ((path (graph-reachable-through-unvisited-but-last-canonical-witness x y preorder)))
               (not (intersectp-equal (butlast (cdr path) 1) preorder))))
    :hints (("goal" :use graph-reachable-through-unvisited-but-last-implies-canonical-witness
             :in-theory (e/d (intersectp-equal)
                             (graph-reachable-through-unvisited-but-last-implies-canonical-witness
                              graph-reachable-through-unvisited-but-last-canonical-witness)))))





  (defwitness graph-reachable-through-unvisited-but-last-witness
    :predicate (graph-reachable-through-unvisited-but-last-p x y preorder)
    :expr (let ((path (graph-reachable-through-unvisited-but-last-canonical-witness x y preorder)))
               (and (consp path)
                    (graph-path-p path)
                    (equal (car path) x)
                    (equal (car (last path)) y)
                    (not (intersectp (butlast path 1) preorder))
                    (no-duplicatesp path)))
    :generalize (((graph-reachable-through-unvisited-but-last-canonical-witness x y preorder) . reachupath))
    :hints ('(:use (graph-reachable-through-unvisited-but-last-implies-canonical-witness
                    no-duplicatesp-of-graph-reachable-through-unvisited-but-last-canonical-witness)
              :in-theory (disable graph-reachable-through-unvisited-but-last-implies-canonical-witness
                                  no-duplicatesp-of-graph-reachable-through-unvisited-but-last-canonical-witness))))

  (defthmd graph-reachable-through-unvisited-but-last-iff-canonical-witness
    (implies (rewriting-negative-literal `(graph-reachable-through-unvisited-but-last-p ,x ,y ,preorder))
             (iff (graph-reachable-through-unvisited-but-last-p x y preorder)
                  (let ((path (graph-reachable-through-unvisited-but-last-canonical-witness x y preorder)))
                    (and (consp path)
                         (graph-path-p path)
                         (equal (car path) x)
                         (equal (car (last path)) y)
                         (not (intersectp-equal (butlast path 1) preorder))
                         (no-duplicatesp path)))))
    :hints (("goal" :use ((:instance graph-reachable-through-unvisited-but-last-p-suff
                           (visited preorder)
                           (path (graph-reachable-through-unvisited-but-last-canonical-witness x y preorder)))))
            (and stable-under-simplificationp
                 '(:expand ((graph-reachable-through-unvisited-but-last-p x y preorder))))))

  ;; (defthm graph-reachable-through-unvisited-implies-but-last-canonical-witness
  ;;   (implies (graph-reachable-through-unvisited-p x y preorder)
  ;;            (let ((path (graph-reachable-through-unvisited-but-last-canonical-witness x y preorder)))
  ;;              (and (consp path)
  ;;                   (graph-path-p path)
  ;;                   (equal (car path) x)
  ;;                   (equal (car (last path)) y)
  ;;                   (not (intersectp-equal (butlast path 1) preorder)))))
  ;;   :hints (("goal" :use graph-reachable-through-unvisited-but-last-implies-canonical-witness
  ;;            :in-theory (disable graph-reachable-through-unvisited-but-last-implies-canonical-witness))))


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


  (defthm reachable-through-unvisited-but-last-by-member-cond-1
    (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                  (not (graph-reachable-through-unvisited-but-last-p z y preorder)))
             (not (graph-reachable-through-unvisited-but-last-p z y new-preorder)))
    :hints (("goal" :expand ((graph-reachable-through-unvisited-but-last-p z y new-preorder))
             :use ((:instance graph-reachable-through-unvisited-but-last-p-suff
                    (x z) (visited preorder)
                    (path (graph-reachable-through-unvisited-but-last-p-witness z y new-preorder))))))
    :rule-classes ((:rewrite :match-free :all)))


  (local (defthm member-butlast-implies-member-x
           (implies (member k (butlast x n))
                    (member k x))
           :rule-classes :forward-chaining))

  (local (defthm no-intersectp-of-butlast-cdr-member
           (implies (not (intersectp (butlast x n) y))
                    (not (intersectp (butlast (cdr (member k x)) n) y)))
           :hints(("Goal" :in-theory (enable intersectp)))))

  (local (in-theory (disable graph-reachable-through-unvisited-but-last-canonical-witness)))




  ;; (local (defun reachable-after-visiting-x-witness (x y z preorder new-preorder)
  ;;          ;; returns: flag, path
  ;;          ;; flag indicates whether the path is for z-y in the new preorder or x-y in the old preorder.
  ;;          ;; Hyp assumes z reaches y in preorder.
  ;;          (b* ((z-y-path (graph-reachable-through-unvisited-but-last-canonical-witness z y preorder))
  ;;               ;; If that doesn't intersect the new preorder, we're done.
  ;;               ((unless (intersectp (butlast z-y-path 1) new-preorder))
  ;;                (mv t z-y-path))
  ;;               ;; Otherwise, it does intersect the new preorder -- find the node where it intersects.
  ;;               (blocking-node (intersectp-witness (butlast z-y-path 1) new-preorder))
  ;;               ;; Since this is a member of new-preorder, it is reachable from x.
  ;;               (x-block-path (graph-reachable-through-unvisited-canonical-witness x blocking-node preorder))
  ;;               ;; Appending, get a path that connects x to y.
  ;;               (x-y-path (append x-block-path (cdr (member blocking-node z-y-path)))))
  ;;            (mv nil x-y-path))))


  ;; (local (defthm reachable-through-unvisited-but-last-by-member-cond-2-witness-correct
  ;;          (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
  ;;                        (graph-reachable-through-unvisited-but-last-p z y preorder))
  ;;                   (b* (((mv flag path) (reachable-after-visiting-x-witness x y z preorder new-preorder)))
  ;;                     (and (consp path)
  ;;                          (graph-path-p path)
  ;;                          (equal (car (last path)) y)
  ;;                          (if flag
  ;;                              (and (equal (car path) z)
  ;;                                   (not (intersectp (butlast path 1) new-preorder)))
  ;;                            (and (equal (car path) x)
  ;;                                 (not (intersectp (butlast path 1) preorder)))))))
  ;;          :hints(("Goal" :in-theory (enable preorder-cond-implies-new-intersect-witness-reachable)))
  ;;          :rule-classes nil))

  (local (defthm member-intersectp-butlast-witness
           (implies (intersectp (butlast x n) y)
                    (member (intersectp-witness (butlast x n) y) x))
           :hints (("goal" :use ((:instance member-intersectp-witness
                                  (a (butlast x n)) (b y)))
                    :in-theory (disable member-intersectp-witness)))))

  (local (defun reachable-through-unvisited-but-last-by-member-cond-2-hint (x y z preorder new-preorder)
           ;; Hyp assumes z reaches y in preorder.
           (b* ((z-y (graph-reachable-through-unvisited-but-last-canonical-witness z y preorder))
                ;; If that doesn't intersect the new preorder, then z reaches y
                ;; via that same path in the new preorder.
                ((unless (intersectp (butlast z-y 1) new-preorder))
                 `'(:use ((:instance graph-reachable-through-unvisited-but-last-p-suff
                           (x z) (visited new-preorder)
                           (path ,(hq z-y))))
                    :in-theory (disable graph-reachable-through-unvisited-but-last-p-suff)))
                (int (intersectp-witness (butlast z-y 1) new-preorder))
                ((when (member int preorder))
                 ;; this can't be true because then z-y intersects preorder too early.
                 `'(:use ((:instance intersectp-member
                           (a ,(hq int))
                           (x ,(hq (butlast z-y 1)))
                           (y ,(hq preorder))))
                    :in-theory (disable intersectp-member)))
                ;; Since int is a member of new-preorder and not preorder, it's reachable from x
                ((unless (graph-reachable-through-unvisited-p x int preorder))
                 `'(:use ((:instance tarjan-preorder-member-cond-necc
                           (y ,(hq int))))
                    :in-theory (disable tarjan-preorder-member-cond-necc)))
                (x-int (graph-reachable-through-unvisited-canonical-witness x int preorder))
                (x-y (append x-int (cdr (member int z-y)))))
             `'(:use ((:instance graph-reachable-through-unvisited-but-last-p-suff
                       (path ,(hq x-y)) (visited preorder)))
                :in-theory (disable graph-reachable-through-unvisited-but-last-p-suff
                                    tarjan-preorder-member-cond-necc)))))


  (defthm reachable-through-unvisited-but-last-by-member-cond-2
    (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                  (graph-reachable-through-unvisited-but-last-p z y preorder)
                  (not (graph-reachable-through-unvisited-but-last-p x y preorder)))
             (graph-reachable-through-unvisited-but-last-p z y new-preorder))
    :hints ((use-termhint (reachable-through-unvisited-but-last-by-member-cond-2-hint
                           x y z preorder new-preorder)))
    :rule-classes ((:rewrite :match-free :all))))


(defsection graph-reachable-through-unvisited-but-last-of-append-last
  (local
   (encapsulate nil
     (local (defthm last-is-a-member
              (implies (and (equal y (car (last x)))
                            (consp x))
                       (member y x))
              :hints(("Goal" :in-theory (enable last member)))))
     (local (Defthm consp-when-len-gt-0
              (implies (< 0 (len x))
                       (consp x))))

     (defthm member-butlast-when-is-last
       (implies (and (equal y (car (last x)))
                     (no-duplicatesp x))
                (not (member y (butlast x 1))))
       :hints(("Goal" :in-theory (enable last no-duplicatesp))))))

  (local (defthm graph-reachable-through-unvisited-but-last-of-append-last-1
           (implies (graph-reachable-through-unvisited-p x y preorder)
                    (graph-reachable-through-unvisited-but-last-p x y (append preorder (list y))))
           :hints (("goal"
                    :use (;;(:instance graph-reachable-through-unvisited-implies-canonical-witness)
                          (:instance graph-reachable-through-unvisited-but-last-p-suff
                           (visited (append preorder (list y)))
                           (path (graph-reachable-through-unvisited-canonical-witness
                                  x y preorder))))
                    :in-theory (disable graph-reachable-through-unvisited-but-last-p-suff)
                    :do-not-induct t))))

  (local (defthmd intersectp-when-not-intersectp-butlast
           (implies (and (not (intersectp (butlast x 1) y))
                         (consp x))
                    (iff (intersectp x y)
                         (member (car (last x)) y)))
           :hints(("Goal" :in-theory (enable intersectp last)))))

  (local (defthm graph-reachable-through-unvisited-but-last-of-append-last-2
           (implies (and (graph-reachable-through-unvisited-but-last-p x y (append preorder (list y)))
                         (not (member y preorder)))
                    (graph-reachable-through-unvisited-p x y preorder))
           :hints (("goal"
                    :use ((:instance graph-reachable-through-unvisited-but-last-implies-canonical-witness
                           (preorder (append preorder (list y))))
                          (:instance graph-reachable-through-unvisited-p-suff
                           (visited preorder)
                           (path (graph-reachable-through-unvisited-but-last-canonical-witness
                                  x y (append preorder (list y))))))
                    :in-theory (e/d (intersectp-when-not-intersectp-butlast)
                                    (graph-reachable-through-unvisited-p-suff
                                     graph-reachable-through-unvisited-but-last-implies-canonical-witness))
                    :do-not-induct t))))

  (defthm graph-reachable-through-unvisited-but-last-of-append-last
    (implies (not (member y preorder))
             (iff (graph-reachable-through-unvisited-but-last-p x y (append preorder (list y)))
                  (graph-reachable-through-unvisited-p x y preorder)))))




(local (fty::deffixcong list-equiv equal (index-of x y) y
         :hints(("Goal" :in-theory (enable index-of)))))





(define tarjan-node-reaches-stack ((node)
                                   (stack true-listp)
                                   (preorder true-listp))
  :hooks (:fix)
  (if (atom stack)
      nil
    (or (ec-call (graph-reachable-through-unvisited-but-last-p node (car stack) preorder))
        (tarjan-node-reaches-stack node (cdr stack) preorder)))
  ///
  (defthm tarjan-node-reaches-stack-sufficient
    (implies (and (member some-node stack)
                  (graph-reachable-through-unvisited-but-last-p node some-node preorder))
             (tarjan-node-reaches-stack node stack preorder)))

  (defthm tarjan-node-reaches-stack-of-preorder-extension
    (implies (and (not (tarjan-node-reaches-stack node stack preorder))
                  (subsetp preorder new-preorder))
             (not (tarjan-node-reaches-stack node stack new-preorder))))

  (defthm tarjan-node-reaches-stack-when-in-preorder
    (implies (member node preorder)
             (iff (tarjan-node-reaches-stack node stack preorder)
                  (member node stack))))

  (defthm tarjan-node-reaches-stack-when-cut-off-by-extension
    (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                  (tarjan-node-reaches-stack node stack preorder)
                  (not (tarjan-node-reaches-stack x stack preorder)))
             (tarjan-node-reaches-stack node stack new-preorder)))

  (defthm tarjan-node-reaches-stack-of-extension-when-not-blocked
    (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                  (graph-reachable-through-unvisited-but-last-p node some-node preorder)
                  (not (graph-reachable-through-unvisited-but-last-p
                        x some-node preorder))
                  (subsetp stack new-stack)
                  (member some-node stack))
             (tarjan-node-reaches-stack node new-stack new-preorder)))

  (defthm tarjan-node-reaches-stack-when-reaches-other-node
    (implies (and (graph-reachable-through-unvisited-p x y preorder)
                  (tarjan-node-reaches-stack y stack preorder))
             (tarjan-node-reaches-stack x stack preorder))
    :rule-classes ((:rewrite :match-free :all))))


(define tarjan-lowlink-node ((node)
                             (stack true-listp)
                             (preorder true-listp))
  :guard (subsetp-equal stack preorder)
  :returns (lowlink-node)
  :prepwork ((local (defthm index-of-rationalp-when-member
                      (implies (member k x)
                               (rationalp (index-of k x))))))
  :hooks (:fix)
  ;; :verify-guards nil
  (if (atom stack)
      nil
    (let ((other (tarjan-lowlink-node node (cdr stack) preorder)))
      (if (ec-call (graph-reachable-through-unvisited-but-last-p node (car stack) preorder))
          (if (and (member-equal other stack)
                   (ec-call (graph-reachable-through-unvisited-but-last-p node other preorder))
                   (< (index-of other preorder)
                      (index-of (car stack) preorder)))
              other
            (car stack))
        other)))
  ///
  (defret tarjan-lowlink-node-exists-when-node-reaches-stack
    (implies (tarjan-node-reaches-stack node stack preorder)
             (and (member lowlink-node stack)
                  (graph-reachable-through-unvisited-but-last-p node lowlink-node preorder)))
    :hints(("Goal" :in-theory (enable tarjan-node-reaches-stack))))

  (defret tarjan-lowlink-node-lowest-index
    (implies (and (graph-reachable-through-unvisited-but-last-p node other-node preorder)
                  (member other-node stack))
             (<= (index-of lowlink-node preorder)
                 (index-of other-node preorder)))
    :rule-classes (:rewrite :linear))

  (local (defthmd equal-of-plus-1
           (equal (equal (+ 1 x) (+ 1 y))
                  (equal (fix x) (fix y)))))

  (local (defthm equal-of-index-of
           (implies (member k1 x)
                    (equal (equal (index-of k1 x)
                                  (index-of k2 x))
                           (equal k1 k2)))
           :hints(("Goal" :in-theory (enable index-of
                                             equal-of-plus-1)))))

  (local (defthmd <-when-not-equal
           (implies (and (<= a b)
                         (not (equal a b))
                         (natp a) (natp b))
                    (< a b))))

  (defret tarjan-lowlink-node-lowest-index-strong
    (implies (and (graph-reachable-through-unvisited-but-last-p node other-node preorder)
                  (member other-node stack)
                  (subsetp stack preorder)
                  (not (equal other-node lowlink-node)))
             (< (index-of lowlink-node preorder)
                (index-of other-node preorder)))
    :hints (("goal" :induct t
             :in-theory (e/d (<-when-not-equal))))
    :rule-classes (:rewrite :linear))

  (local (defthm member-when-prefixp
           (implies (and (prefixp a b)
                         (member k a))
                    (member k b))
           :hints(("Goal" :in-theory (enable prefixp)))))

  (local (defthm index-of-prefix
           (implies (prefixp a b)
                    (<= (index-of k a) (index-of k b)))
           :hints(("Goal" :in-theory (enable prefixp index-of)))
           :rule-classes :linear))

  (local (defthm index-of-after-prefix
           (implies (and (prefixp a b)
                         (member k b)
                         (not (member k a)))
                    (<= (len a) (index-of k b)))
           :hints(("Goal" :in-theory (enable index-of prefixp)))
           :rule-classes :linear))

  (local (defret tarjan-lowlink-node-in-preorder-when-node-reaches-stack
           (implies (and (tarjan-node-reaches-stack node stack preorder)
                         (subsetp stack preorder))
                    (member lowlink-node preorder))))

  (local (defthm prefixp-implies-subsetp
           (implies (prefixp x y)
                    (subsetp x y))
           :hints ((set-reasoning))))

  (local (defun tarjan-lowlink-node-of-extension-hint (node stack preorder new-stack new-preorder)
           (b* ((new-lowlink (tarjan-lowlink-node node new-stack new-preorder))
                ((when (member new-lowlink preorder))
                 ;; must be in the original stack:
                 (b* (((unless (member new-lowlink stack))
                       '(witness :ruleset set-reasoning-no-consp))
                      ((unless (graph-reachable-through-unvisited-but-last-p node new-lowlink preorder))
                       ;; must be reachable in new preorder, therefore in old
                       `'(:use ((:instance graph-reachable-through-unvisited-but-last-p-of-preorder-extension
                                 (x ,(hq node)) (y ,(hq new-lowlink)))))))
                   ;; new-lowlink node is reachable, so old-lowlink index is less
                   `'(:use ((:instance tarjan-lowlink-node-lowest-index
                             (other-node ,(hq new-lowlink)))))))
                ((unless (member new-lowlink new-preorder))
                 '(witness :ruleset set-reasoning-no-consp)))
             ;; index-of-after-prefix
             `'(:use ((:instance index-of-after-prefix
                       (a ,(hq preorder))
                       (b ,(hq new-preorder))
                       (k ,(hq new-lowlink))))
                :in-theory (disable index-of-after-prefix)))))

  ;; If a node reaches an extension of the stack in an extension of the
  ;; preorder, and reaches the original stack in the original preorder, then
  ;; its new lowlink node index is greater than or equal the old
  (defthm tarjan-lowlink-node-of-extension
    (implies (and (tarjan-node-reaches-stack node new-stack new-preorder)
                  (tarjan-node-reaches-stack node stack preorder)
                  (prefixp preorder new-preorder)
                  ;; (subsetp stack new-stack)
                  (subsetp stack preorder)
                  ;; (subsetp new-stack new-preorder)
                  (subsetp (set-difference$ new-stack stack)
                           (set-difference$ new-preorder preorder)))
             (<= (index-of (tarjan-lowlink-node node stack preorder) preorder)
                 (index-of (tarjan-lowlink-node node new-stack new-preorder) new-preorder)))
    :hints (("goal" :do-not-induct t)
            (use-termhint (tarjan-lowlink-node-of-extension-hint node stack preorder new-stack new-preorder)))
    :otf-flg t)


  ;; If a node reaches an extension of the stack in an extension of the
  ;; preorder, but previously couldn't reach the stack through the preorder,
  ;; then its new lowlink node index is gte the original preorder length.
  (defthm tarjan-lowlink-node-of-extension-when-not-reached
    (implies (and (tarjan-node-reaches-stack node new-stack new-preorder)
                  (not (tarjan-node-reaches-stack node stack preorder))
                  (prefixp preorder new-preorder)
                  (subsetp stack preorder)
                  (subsetp (set-difference$ new-stack stack)
                           (set-difference$ new-preorder preorder)))
             (<= (len preorder)
                 (index-of (tarjan-lowlink-node node new-stack new-preorder) new-preorder)))
    :hints (("goal" :do-not-induct t)
            (use-termhint (tarjan-lowlink-node-of-extension-hint node stack preorder new-stack new-preorder))))

  (local (defthm index-of-when-in-prefix
           (implies (and (prefixp a b)
                         (member k a))
                    (equal (index-of k b)
                           (index-of k a)))
           :hints(("Goal" :in-theory (enable index-of prefixp)))))

  (defthm tarjan-node-reaches-stack-of-extension-when-not-blocked-special
    (let ((some-node (tarjan-lowlink-node node stack preorder)))
      (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                    (not (graph-reachable-through-unvisited-but-last-p
                          x some-node preorder))
                    (graph-reachable-through-unvisited-but-last-p node some-node preorder)
                    (subsetp stack new-stack)
                    (member some-node stack))
               (tarjan-node-reaches-stack node new-stack new-preorder)))
    :hints (("goal" :use ((:instance tarjan-node-reaches-stack-of-extension-when-not-blocked
                           (some-node (tarjan-lowlink-node node stack preorder))))
             :in-theory (disable tarjan-node-reaches-stack-of-extension-when-not-blocked))))

  (defthm tarjan-lowlink-node-of-extension-when-not-blocked
    (implies (and (tarjan-node-reaches-stack node stack preorder)
                  (tarjan-preorder-member-cond x preorder new-preorder)
                  (prefixp preorder new-preorder)
                  (subsetp stack preorder)
                  (subsetp stack new-stack)
                  (subsetp (set-difference$ new-stack stack)
                           (set-difference$ new-preorder preorder))
                  (not (graph-reachable-through-unvisited-but-last-p
                        x (tarjan-lowlink-node node stack preorder) preorder)))
             (equal (tarjan-lowlink-node node new-stack new-preorder)
                    (tarjan-lowlink-node node stack preorder)))
    :hints (("goal" :do-not-induct t
             :use ((:instance tarjan-lowlink-node-lowest-index-strong
                    (stack new-stack) (preorder new-preorder)
                    (other-node (tarjan-lowlink-node node stack preorder)))
                   (:instance reachable-through-unvisited-but-last-by-member-cond-2
                    (z node) (y (tarjan-lowlink-node node stack preorder))))
             :in-theory (disable tarjan-lowlink-node-lowest-index-strong
                                 reachable-through-unvisited-but-last-by-member-cond-2
                                 tarjan-lowlink-node))
            (witness :ruleset set-reasoning-no-consp))
    :otf-flg t)

  (defthm tarjan-lowlink-node-of-extension-when-lowlink-is-less
    (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                  (tarjan-node-reaches-stack node stack preorder)
                  (prefixp preorder new-preorder)
                  (subsetp stack preorder)
                  (subsetp stack new-stack)
                  (subsetp (set-difference$ new-stack stack)
                           (set-difference$ new-preorder preorder))
                  (< (index-of (tarjan-lowlink-node node stack preorder) preorder)
                     (index-of (tarjan-lowlink-node x stack preorder) preorder)))
             (equal (tarjan-lowlink-node node new-stack new-preorder)
                    (tarjan-lowlink-node node stack preorder)))
    :hints (("goal" :do-not-induct t
             :use ((:instance tarjan-lowlink-node-of-extension-when-not-blocked))
             :in-theory (disable tarjan-lowlink-node-of-extension-when-not-blocked
                                 tarjan-lowlink-node)))
    :otf-flg t
    :rule-classes ((:rewrite :match-free :all)))

  (defthm tarjan-node-reaches-stack-of-extension-when-lowlink-is-less
    (let ((some-node (tarjan-lowlink-node node stack preorder)))
      (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                    (< (index-of some-node preorder)
                       (index-of (tarjan-lowlink-node x stack preorder) preorder))
                    (graph-reachable-through-unvisited-but-last-p node some-node preorder)
                    (subsetp stack new-stack)
                    (member some-node stack))
               (tarjan-node-reaches-stack node new-stack new-preorder)))
    :hints (("goal" :do-not-induct t
             :use ((:instance tarjan-node-reaches-stack-of-extension-when-not-blocked-special))
             :in-theory (disable tarjan-node-reaches-stack-of-extension-when-not-blocked-special
                                 tarjan-node-reaches-stack-of-extension-when-not-blocked
                                 tarjan-lowlink-node)))
    :rule-classes ((:rewrite :match-free :all)))

  (defthm tarjan-lowlink-node-of-extension-when-stack-not-reachable
    (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                  (tarjan-node-reaches-stack node stack preorder)
                  (prefixp preorder new-preorder)
                  (subsetp stack preorder)
                  (subsetp stack new-stack)
                  (subsetp (set-difference$ new-stack stack)
                           (set-difference$ new-preorder preorder))
                  (not (tarjan-node-reaches-stack x stack preorder)))
             (equal (tarjan-lowlink-node node new-stack new-preorder)
                    (tarjan-lowlink-node node stack preorder)))
    :hints (("goal" :do-not-induct t
             :use ((:instance tarjan-lowlink-node-of-extension-when-not-blocked)
                   (:instance tarjan-node-reaches-stack-sufficient
                    (some-node (tarjan-lowlink-node node stack preorder))
                    (node x)))
             :in-theory (disable tarjan-lowlink-node-of-extension-when-not-blocked
                                 tarjan-node-reaches-stack-sufficient
                                 tarjan-lowlink-node)))
    :otf-flg t
    :rule-classes ((:rewrite :match-free :all)))


  (defthm tarjan-node-reaches-stack-of-extension-when-stack-not-reachable
    (let ((some-node (tarjan-lowlink-node node stack preorder)))
      (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                    (not (tarjan-node-reaches-stack x stack preorder))
                    (graph-reachable-through-unvisited-but-last-p node some-node preorder)
                    (subsetp stack new-stack)
                    (member some-node stack))
               (tarjan-node-reaches-stack node new-stack new-preorder)))
    :hints (("goal" :do-not-induct t
             :use ((:instance tarjan-node-reaches-stack-of-extension-when-not-blocked-special))
             :in-theory (disable tarjan-node-reaches-stack-of-extension-when-not-blocked-special
                                 tarjan-node-reaches-stack-of-extension-when-not-blocked
                                 tarjan-lowlink-node)))
    :rule-classes ((:rewrite :match-free :all)))

  (defthm tarjan-lowlink-node-of-extension-when-stack-not-reachable-special
    (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                  (tarjan-node-reaches-stack node stack preorder)
                  (prefixp preorder new-preorder)
                  (subsetp stack preorder)
                  (subsetp stack new-stack)
                  (subsetp (set-difference$ new-stack stack)
                           (set-difference$ new-preorder preorder))
                  (not (tarjan-node-reaches-stack x stack preorder)))
             (equal (tarjan-lowlink-node node new-stack new-preorder)
                    (tarjan-lowlink-node node stack preorder)))
    :hints (("goal" :do-not-induct t
             :use ((:instance tarjan-lowlink-node-of-extension-when-not-blocked)
                   (:instance tarjan-node-reaches-stack-sufficient
                    (some-node (tarjan-lowlink-node node stack preorder))
                    (node x)))
             :in-theory (disable tarjan-lowlink-node-of-extension-when-not-blocked
                                 tarjan-node-reaches-stack-sufficient
                                 tarjan-lowlink-node)))
    :otf-flg t
    :rule-classes ((:rewrite :match-free :all)))

  (defthm tarjan-node-reaches-stack-of-extension-when-stack-not-reachable-special
    (let ((some-node (tarjan-lowlink-node node stack preorder)))
      (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                    (member x preorder)
                    (not (member x stack))
                    (graph-reachable-through-unvisited-but-last-p node some-node preorder)
                    (subsetp stack new-stack)
                    (member some-node stack))
               (tarjan-node-reaches-stack node new-stack new-preorder)))
    :hints (("goal" :do-not-induct t
             :use ((:instance tarjan-node-reaches-stack-of-extension-when-stack-not-reachable))
             :in-theory (disable tarjan-node-reaches-stack-of-extension-when-stack-not-reachable)))
    :rule-classes ((:rewrite :match-free :all))))

(define tarjan-node-stack-path ((node)
                                (stack true-listp)
                                (preorder true-listp))
  :guard (subsetp-equal stack preorder)
  :returns (path)
  (ec-call (graph-reachable-through-unvisited-but-last-canonical-witness
            node (tarjan-lowlink-node node stack preorder) preorder))
  ///
  (defret tarjan-node-stack-path-when-reachable
    (implies (tarjan-node-reaches-stack node stack preorder)
             (and (consp path)
                  (graph-path-p path)
                  (equal (car path) node)
                  (member (car (last path)) stack)
                  (not (intersectp (butlast path 1) preorder)))))

  (defthm tarjan-node-reaches-stack-by-path
    (implies (and (graph-path-p path)
                  (equal (car path) node)
                  (member (car (last path)) stack)
                  (not (intersectp (butlast path 1) preorder)))
             (tarjan-node-reaches-stack node stack preorder))
    :hints(("Goal" :do-not-induct t
            :use ((:instance tarjan-node-reaches-stack-sufficient
                   (some-node (car (last path))))
                  (:instance graph-reachable-through-unvisited-but-last-p-suff
                   (x node) (y (car (last path))) (visited preorder)
                   (path path))))))

  (defret no-duplicatesp-of-tarjan-node-stack-path
    (no-duplicatesp path))

  (defret consp-cdr-of-tarjan-node-stack-path
    (implies (and (tarjan-node-reaches-stack node stack preorder)
                  (not (member node stack)))
             (consp (cdr path)))
    :hints (("goal" :use tarjan-node-stack-path-when-reachable
             :in-theory (disable tarjan-node-stack-path-when-reachable
                                 tarjan-node-stack-path))))

  (defret tarjan-node-stack-path-when-reachable-not-intersect-subset
    (implies (and (tarjan-node-reaches-stack node stack preorder)
                  (subsetp pre1 preorder))
             (not (intersectp (butlast path 1) pre1)))
    :hints(("Goal" :in-theory (e/d (intersectp-by-subsetp)
                                   (tarjan-node-stack-path
                                    tarjan-node-stack-path-when-reachable))
            :use tarjan-node-stack-path-when-reachable)))

  (defwitness stack-reachable-through-node-stack-path
    :predicate (tarjan-node-reaches-stack x stack preorder)
    :expr (let ((path (tarjan-node-stack-path x stack preorder)))
               (and (consp path)
                    (graph-path-p path)
                    (equal (car path) x)
                    (member (car (last path)) stack)
                    (not (intersectp (butlast path 1) preorder))
                    (no-duplicatesp path)))
    :generalize (((tarjan-node-stack-path x stack preorder) . reachstkpath))
    :hints ('(:use (tarjan-node-stack-path-when-reachable
                    no-duplicatesp-of-tarjan-node-stack-path)
              :in-theory (disable tarjan-node-stack-path-when-reachable
                                  no-duplicatesp-of-tarjan-node-stack-path))))

  (std::defretd tarjan-node-stack-endpoint-is-lowlink-node
    (implies (tarjan-node-reaches-stack node stack preorder)
             (equal (car (last path))
                    (tarjan-lowlink-node node stack preorder)))))



(define prefix-path-to (x (path true-listp))
  :guard (member-equal x path)
  :returns (prefix)
  (if (atom path)
      nil
    (if (equal x (car path))
        (list (car path))
      (cons (car path) (prefix-path-to x (cdr path)))))
  ///
  (defret subsetp-of-prefix-path-to
    (subsetp prefix path)
    :hints(("Goal" :in-theory (enable subsetp))))

  (defret graph-path-p-of-prefix-path-to
    (implies (graph-path-p path)
             (graph-path-p prefix))
    :hints(("Goal" :in-theory (enable graph-path-p))))

  (defret first-of-prefix-path-to
    (equal (car prefix) (car path)))

  (defret last-of-prefix-path-to
    (implies (member x path)
             (equal (car (last prefix)) x))
    :hints(("Goal" :in-theory (enable last))))

  (defret consp-of-prefix-path-to
    (implies (member x path)
             (consp prefix)))

  (defret not-member-of-prefix-path-to
    (implies (not (member k path))
             (not (member k prefix))))

  (defret no-duplicatesp-of-prefix-path-to
    (implies (no-duplicatesp path)
             (no-duplicatesp prefix)))

  (defret not-intersectp-of-prefix-path-to
    (implies (not (intersectp path y))
             (not (intersectp prefix y)))
    :hints(("Goal" :in-theory (enable intersectp))))

  (defret len-of-prefix-path-bound
    (<= (len prefix) (len path))
    :rule-classes :linear)

  (defret not-intersectp-butlast-of-prefix-path-to
    (implies (not (intersectp (butlast path n) y))
             (not (intersectp (butlast prefix n) y)))
    :hints(("Goal" :in-theory (enable intersectp)))))



(defsection tarjan-node-reaches-stack-preserved-by-add-one
  (local (defund tarjan-node-reaches-stack-of-add-x-no-witness (x y stack preorder)
           ;; If y reaches either x or the stack in the extended preorder,
           ;; but does not reach the stack in the original preorder, then it must reach x.
           (b* ((y-x-path (tarjan-node-stack-path y (cons x stack) (append preorder (list x))))
                ((unless (equal (car (last y-x-path)) x))
                 ;; already a path to the stack; it's valid for original preorder too
                 y-x-path)
                (x-stack-path (tarjan-node-stack-path x stack preorder)))
             ;; ok, so now we have a path from y to x and from x to path.
             (append y-x-path (cdr x-stack-path)))))

  (local (defthm last-is-last-of-cdr
           (implies (consp (cdr x))
                    (equal (last (cdr x))
                           (last x)))))
  (local (defthm intersectp-butlast-cdr
           (implies (not (intersectp (butlast x n) y))
                    (not (intersectp (butlast (cdr x) n) y)))
           :hints(("Goal" :in-theory (enable intersectp)))))

  (local (defthm len-equal-0
           (equal (equal (len x) 0)
                  (atom x))))

  (local (defthm no-intersectp-when-butlast-and-last
           (implies (And (not (intersectp (butlast x 1) y))
                         (not (member (car (last x)) y)))
                    (not (intersectp x y)))
           :hints(("Goal" :in-theory (enable intersectp)))))

  (local (in-theory (disable last butlast-redefinition len member no-duplicatesp)))

  (local (defthm tarjan-node-reaches-stack-of-add-x-no-witness-correct
           (implies (and (tarjan-node-reaches-stack x stack preorder)
                         (not (member x preorder))
                         (subsetp stack preorder)
                         (tarjan-node-reaches-stack y (cons x stack) (append preorder (list x))))
                    (b* ((path (tarjan-node-reaches-stack-of-add-x-no-witness x y stack preorder)))
                      (and (consp path)
                           (graph-path-p path)
                           (equal (car path) y)
                           (member (car (last path)) stack)
                           (not (intersectp (butlast path 1) preorder)))))
           :hints (("Goal" :do-not-induct t
                    :in-theory (enable tarjan-node-reaches-stack-of-add-x-no-witness))
                   (witness :ruleset stack-reachable-through-node-stack-path))))



  (local (defthm tarjan-node-reaches-stack-of-add-x-no
           (implies (and (tarjan-node-reaches-stack x stack preorder)
                         (not (member x preorder))
                         (subsetp stack preorder)
                         (not (tarjan-node-reaches-stack y stack preorder)))
                    (not (tarjan-node-reaches-stack y (cons x stack) (append preorder (list x)))))
           :hints (("goal" :use (tarjan-node-reaches-stack-of-add-x-no-witness-correct
                                 (:instance tarjan-node-reaches-stack-by-path
                                  (node y)
                                  (path (tarjan-node-reaches-stack-of-add-x-no-witness x y stack preorder))))
                    :in-theory nil
                    :do-not-induct t))))


  (local (defund tarjan-node-reaches-stack-of-add-x-yes-witness (x y stack preorder)
           (b* ((y-stack-path (tarjan-node-stack-path y stack preorder))
                ((when (member x y-stack-path))
                 (prefix-path-to x y-stack-path)))
             y-stack-path)))

  (local (defthm not-member-of-butlast-of-prefix-path
           (not (member x (butlast (prefix-path-to x path) 1)))
           :hints(("Goal" :in-theory (enable prefix-path-to
                                             butlast-redefinition len)))))


  (local (defthm not-mebmer-of-butlast
           (implies (not (member x path))
                    (not (member x (butlast path n))))
           :hints(("Goal" :in-theory (enable butlast-redefinition len)))))

  (local (defthm tarjan-node-reaches-stack-of-add-x-yes-witness-correct
           (implies (and ;; (tarjan-node-reaches-stack x stack preorder)
                         (tarjan-node-reaches-stack y stack preorder))
                    (b* ((path (tarjan-node-reaches-stack-of-add-x-yes-witness x y stack preorder)))
                      (and (consp path)
                           (graph-path-p path)
                           (equal (car path) y)
                           (member (car (last path)) (cons x stack))
                           (not (intersectp (butlast path 1) (append preorder (list x)))))))
           :hints (("Goal" :do-not-induct t
                    :in-theory (enable tarjan-node-reaches-stack-of-add-x-yes-witness))
                   (witness :ruleset stack-reachable-through-node-stack-path))))


  ;; y reaches the stack without x in the preorder.  If its path does not pass
  ;; through x, then it also reaches the stack with x.  If it does pass through x, then it reaches x.
  (defthm tarjan-node-reaches-stack-of-add-x-yes
    (implies (and ;; (tarjan-node-reaches-stack x stack preorder)
              (tarjan-node-reaches-stack y stack preorder))
             (tarjan-node-reaches-stack y (cons x stack) (append preorder (list x))))
    :hints (("goal" :use (tarjan-node-reaches-stack-of-add-x-yes-witness-correct
                          (:instance tarjan-node-reaches-stack-by-path
                           (node y) (stack (cons x stack))
                           (preorder (append preorder (list x)))
                           (path (tarjan-node-reaches-stack-of-add-x-yes-witness x y stack preorder))))
             :in-theory nil)))



  (defthm tarjan-node-reaches-stack-of-add-x
    (implies (and (tarjan-node-reaches-stack x stack preorder)
                  (not (member x preorder))
                  (subsetp stack preorder))
             (iff (tarjan-node-reaches-stack y (cons x stack) (append preorder (list x)))
                  (tarjan-node-reaches-stack y stack preorder)))))




(local (in-theory (disable min)))

(define tarjan-lowlink-spec ((node)
                             (stack true-listp)
                             (preorder true-listp))
  :returns (lowlink natp :rule-classes :type-prescription)
  :guard (subsetp-equal stack preorder)
  :hooks (:fix)
  (if (tarjan-node-reaches-stack node stack preorder)
      (let ((lowlink-node (tarjan-lowlink-node node stack preorder)))
        (lnfix (index-of lowlink-node preorder)))
    (len preorder))
  ///
  (local (defthm len-when-prefixp
           (implies (prefixp a b)
                    (<= (len a) (len b)))
           :hints(("Goal" :in-theory (enable prefixp)))
           :rule-classes :linear))

  (defret tarjan-lowlink-spec-when-not-in-preorder
    (implies (and (not (member node preorder))
                  (subsetp stack preorder))
             lowlink))

  (local (defthmd stack-subsetp-of-preorder-lemma
           (implies (and (subsetp preorder new-preorder)
                         (subsetp stack preorder)
                         (not (subsetp new-stack new-preorder)))
                    (not (subsetp (set-difference$ new-stack stack)
                                  (set-difference$ new-preorder preorder))))
           :hints ((set-reasoning))))

  (defthm tarjan-lowlink-spec-of-extension
    (implies (and (prefixp preorder new-preorder)
                  (subsetp stack preorder)
                  ;; (subsetp new-stack new-preorder)
                  (subsetp (set-difference$ new-stack stack)
                           (set-difference$ new-preorder preorder)))
             (<= (tarjan-lowlink-spec node stack preorder)
                 (tarjan-lowlink-spec node new-stack new-preorder)))
    :hints (("goal" :cases ((subsetp new-stack new-preorder)))
            (and stable-under-simplificationp
                 '(:in-theory (enable stack-subsetp-of-preorder-lemma
                                      subsetp-when-prefixp))))
    :rule-classes (:rewrite :linear))

  (defthm tarjan-lowlink-spec-of-extension-exists
    (implies (and (prefixp preorder new-preorder)
                  (subsetp stack preorder)
                  (subsetp (set-difference$ new-stack stack)
                           (set-difference$ new-preorder preorder))
                  (not (tarjan-lowlink-spec node stack preorder)))
             (not (tarjan-lowlink-spec node new-stack new-preorder)))
    :hints(("Goal" :in-theory (enable subsetp-when-prefixp))
           (witness :ruleset set-reasoning-no-consp)))

  ;; (defthm tarjan-lowlink-spec-of-extend-lesser
  ;;   (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
  ;;                 (prefixp preorder new-preorder)
  ;;                 (subsetp-equal stack preorder)
  ;;                 (subsetp-equal stack new-stack)
  ;;                 (subsetp-equal (set-difference-equal new-stack stack)
  ;;                                (set-difference-equal new-preorder preorder))
  ;;                 (not (member-equal x preorder))
  ;;                 (tarjan-lowlink-spec y stack preorder)
  ;;                 (< (tarjan-lowlink-spec y stack preorder)
  ;;                    (tarjan-lowlink-spec x stack preorder)))
  ;;            (equal (tarjan-lowlink-spec y new-stack new-preorder)
  ;;                   (tarjan-lowlink-spec y stack preorder)))
  ;;   :hints (("goal" :do-not-induct t)))

  (local (defthm index-of-when-in-prefix
           (implies (and (prefixp a b)
                         (member k a))
                    (equal (index-of k b)
                           (index-of k a)))
           :hints(("Goal" :in-theory (enable index-of prefixp)))))



  (defthm tarjan-lowlink-spec-of-extension-when-lowlink-is-less
    (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                  (prefixp preorder new-preorder)
                  (subsetp stack preorder)
                  (subsetp stack new-stack)
                  (subsetp (set-difference$ new-stack stack)
                           (set-difference$ new-preorder preorder))
                  (tarjan-lowlink-spec node stack preorder)
                  (< (tarjan-lowlink-spec node stack preorder)
                     (tarjan-lowlink-spec x stack preorder)))
             (equal (tarjan-lowlink-spec node new-stack new-preorder)
                    (tarjan-lowlink-spec node stack preorder)))
    :hints (("goal" :do-not-induct t)))

  (defthmd tarjan-lowlink-spec-min-of-extension-lemma
    (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                  (prefixp preorder new-preorder)
                  (subsetp stack preorder)
                  (subsetp stack new-stack)
                  (subsetp (set-difference$ new-stack stack)
                           (set-difference$ new-preorder preorder)))
             (equal (min (tarjan-lowlink-spec x stack preorder)
                         (tarjan-lowlink-spec node new-stack new-preorder))
                    (min (tarjan-lowlink-spec x stack preorder)
                         (tarjan-lowlink-spec node stack preorder))))
    :hints(("Goal" :in-theory (e/d (min)
                                   (tarjan-lowlink-spec
                                    tarjan-lowlink-spec-of-extension-when-lowlink-is-less))
            :use tarjan-lowlink-spec-of-extension-when-lowlink-is-less
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:cases ((tarjan-lowlink-spec node new-stack new-preorder)))))
    :otf-flg t)

  (defthm tarjan-lowlink-spec-bound
    (<= (tarjan-lowlink-spec x stack preorder) (len preorder))
    :rule-classes :linear)

  (defthm tarjan-lowlink-spec-when-stack-not-reached
    (implies (not (tarjan-node-reaches-stack x stack preorder))
             (equal (tarjan-lowlink-spec x stack preorder)
                    (len preorder)))))





(define tarjan-lowlink-successor ((node)
                                  (stack true-listp)
                                  (preorder true-listp))
  :guard (and (subsetp-equal stack preorder)
              (tarjan-node-reaches-stack node stack preorder)
              (not (member-equal node stack)))
  :returns (successor)
  (let ((path (tarjan-node-stack-path node stack preorder)))
    (cadr path))
  ///
  (local (defthm consp-cdr-when-car-not-last
           (implies (not (equal (car x) (car (last x))))
                    (consp (cdr x)))))

  (local (defthm node-is-not-lowlink-when-not-on-stack
           (implies (and (tarjan-node-reaches-stack node stack preorder)
                         (not (member node stack)))
                    (not (equal node (tarjan-lowlink-node node stack preorder))))
           :hints (("goal" :use tarjan-lowlink-node-exists-when-node-reaches-stack
                    :in-theory (disable tarjan-lowlink-node-exists-when-node-reaches-stack)))))



  (defret tarjan-lowlink-successor-is-a-successor
    (implies (and (tarjan-node-reaches-stack node stack preorder)
                  (not (member node stack)))
             (member successor (graph-node-succs node))))

  (local (defthmd last-of-cdr
           (implies (consp (cdr x))
                    (equal (last (cdr x))
                           (last x)))))

  (local (defthm intersectp-butlast-cdr
           (implies (not (intersectp (butlast x n) y))
                    (not (intersectp (butlast (cdr x) n) y)))
           :hints(("Goal" :in-theory (enable intersectp)))))

  (local (include-book "tools/trivial-ancestors-check" :dir :system))
  (local (use-trivial-ancestors-check))
  ;; (local (defun tarjan-lowlink-successor-reaches-lowlink-node-witness (node stack preorder)
  ;;          (b* ((node-stack-path (tarjan-node-stack-path node stack preorder)))


  (defret tarjan-lowlink-successor-reaches-lowlink-node
    (implies (and (tarjan-node-reaches-stack node stack preorder)
                  (not (member node stack)))
             (graph-reachable-through-unvisited-but-last-p
              successor (tarjan-lowlink-node node stack preorder) preorder))
    :hints (("goal" :use ((:instance graph-reachable-through-unvisited-but-last-p-suff
                           (x successor)
                           (y (tarjan-lowlink-node node stack preorder))
                           (visited preorder)
                           (path (cdr (tarjan-node-stack-path node stack preorder)))))
             :in-theory (e/d (last-of-cdr
                              tarjan-node-stack-endpoint-is-lowlink-node)
                             (graph-reachable-through-unvisited-but-last-p-suff
                              butlast-redefinition)))))



  (defret tarjan-node-reaches-stack-of-tarjan-lowlink-successor
    (implies (and (tarjan-node-reaches-stack node stack preorder)
                  (not (member node stack)))
             (tarjan-node-reaches-stack successor stack preorder))
    :hints (("goal" :use ((:instance tarjan-node-reaches-stack-by-path
                           (node successor)
                           (path (cdr (tarjan-node-stack-path node stack preorder)))))
             :in-theory (e/d (last-of-cdr)
                             (tarjan-node-reaches-stack-sufficient
                              butlast-redefinition)))))

  (local (defthm node-reaches-successor-lowlink
           (implies (and (tarjan-node-reaches-stack node stack preorder)
                         (not (member node stack))
                         (member succ (graph-node-succs node))
                         (tarjan-node-reaches-stack succ stack preorder))
                    (graph-reachable-through-unvisited-but-last-p
                     node (tarjan-lowlink-node succ stack preorder) preorder))
           :hints (("goal" :use ((:instance graph-reachable-through-unvisited-but-last-p-suff
                                  (x node)
                                  (y (tarjan-lowlink-node succ stack preorder))
                                  (path (cons node (tarjan-node-stack-path succ stack preorder)))
                                  (visited preorder)))
                    :in-theory (enable intersectp
                                       tarjan-node-stack-endpoint-is-lowlink-node)))))


  (defret tarjan-lowlink-node-of-tarjan-lowlink-successor
    (implies (and (tarjan-node-reaches-stack node stack preorder)
                  (not (member node stack))
                  (subsetp stack preorder))
             (equal (tarjan-lowlink-node successor stack preorder)
                    (tarjan-lowlink-node node stack preorder)))
    :hints (("goal" :use ((:instance tarjan-lowlink-node-lowest-index
                           (other-node (tarjan-lowlink-node successor stack preorder)))
                          (:instance tarjan-lowlink-node-lowest-index
                           (node successor)
                           (other-node (tarjan-lowlink-node node stack preorder))))
             :in-theory (e/d (last-of-cdr graph-path-p
                                          intersectp)
                             (tarjan-lowlink-node-lowest-index
                              graph-reachable-through-unvisited-but-last-p-suff
                              tarjan-lowlink-successor
                              butlast-redefinition)))))

  (local (defthm not-member-cdr-by-no-duplicatesp
           (implies (and (no-duplicatesp x)
                         (equal y (car x)))
                    (not (member y (cdr x))))
           :hints(("Goal" :in-theory (enable no-duplicatesp)))))

  (local (defthm not-member-butlast
           (implies (not (member k x))
                    (not (member k (butlast x n))))))

  (defret tarjan-node-reaches-stack-extended-of-tarjan-lowlink-successor
    (implies (and (tarjan-node-reaches-stack node stack preorder)
                  (not (member node stack)))
             (tarjan-node-reaches-stack successor (cons node stack)
                                        (append preorder (list node))))
    :hints (("goal" :use ((:instance tarjan-node-reaches-stack-by-path
                           (node successor)
                           (stack (cons node stack))
                           (preorder (append preorder (list node)))
                           (path (cdr (tarjan-node-stack-path node stack preorder)))))
             :in-theory (e/d (last-of-cdr)
                             (tarjan-node-reaches-stack-sufficient
                              butlast-redefinition)))))


  (defret tarjan-lowlink-successor-reaches-lowlink-node-without-x
    (implies (and (tarjan-node-reaches-stack node stack preorder)
                  (not (member node stack)))
             (graph-reachable-through-unvisited-but-last-p
              successor (tarjan-lowlink-node node stack preorder) (append preorder (list node))))
    :hints (("goal" :use ((:instance graph-reachable-through-unvisited-but-last-p-suff
                           (x successor)
                           (y (tarjan-lowlink-node node stack preorder))
                           (visited (append preorder (list node)))
                           (path (cdr (tarjan-node-stack-path node stack preorder)))))
             :in-theory (e/d (last-of-cdr
                              tarjan-node-stack-endpoint-is-lowlink-node)
                             (graph-reachable-through-unvisited-but-last-p-suff
                              butlast-redefinition)))))


  (local (defret node-reaches-extended-successor-lowlink
           (b* ((lowlink (tarjan-lowlink-node successor (cons node stack) (append preorder (list node)))))
             (implies (and (tarjan-node-reaches-stack node stack preorder)
                           (not (member node stack)))
                      (graph-reachable-through-unvisited-but-last-p
                       node lowlink preorder)))
           :hints (("goal" :use ((:instance graph-reachable-through-unvisited-but-last-p-suff
                                  (x node)
                                  (y (tarjan-lowlink-node successor (cons node stack) (append preorder (list node))))
                                  (visited preorder)
                                  (path (cons node (tarjan-node-stack-path successor (cons node stack) (append preorder (list node)))))))
                    :in-theory (e/d (last-of-cdr
                                     intersectp
                                     graph-path-p
                                     tarjan-node-stack-endpoint-is-lowlink-node)
                                    (graph-reachable-through-unvisited-but-last-p-suff
                                     tarjan-lowlink-successor))))))


  (local (defthm index-of-append
           (equal (index-of x (append a b))
                  (cond ((member x a) (index-of x a))
                        ((member x b) (+ (len a) (index-of x b)))
                        (t nil)))
           :hints(("Goal" :in-theory (enable index-of)))))

  (local (defthm index-of-lte-len
           (<= (index-of k x) (len x))
           :hints(("Goal" :in-theory (enable index-of)))
           :rule-classes :linear))

  (local (defthm index-of-lower-bound
           (<= 0 (index-of k x))
           :hints(("Goal" :in-theory (enable index-of)))
           :rule-classes :linear))
  (local (defthmd equal-of-plus-1
           (equal (equal (+ 1 x) (+ 1 y))
                  (equal (fix x) (fix y)))))
  (local (defthm equal-of-index-of
           (implies (member k1 x)
                    (equal (equal (index-of k1 x)
                                  (index-of k2 x))
                           (equal k1 k2)))
           :hints(("Goal" :in-theory (enable index-of
                                             equal-of-plus-1)))))

    (defret tarjan-lowlink-node-of-tarjan-lowlink-successor-extended
      (implies (and (tarjan-node-reaches-stack node stack preorder)
                    (not (member node stack))
                    (subsetp stack preorder))
               (equal (tarjan-lowlink-node successor (cons node stack)
                                           (append preorder (list node)))
                      (tarjan-lowlink-node node stack preorder)))
    :hints (("goal" :use ((:instance tarjan-lowlink-node-lowest-index
                           (other-node (tarjan-lowlink-node successor
                                                            (cons node stack)
                                                            (append preorder (list node)))))
                          (:instance tarjan-lowlink-node-lowest-index
                           (node successor)
                           (other-node (tarjan-lowlink-node node stack preorder))
                           (stack (cons node stack))
                           (preorder (append preorder (list node)))))
             :in-theory (e/d (last-of-cdr graph-path-p
                                          intersectp)
                             (tarjan-lowlink-node-lowest-index
                              graph-reachable-through-unvisited-but-last-p-suff
                              tarjan-lowlink-successor
                              butlast-redefinition
                              (force))))

            (and stable-under-simplificationp
                 '(:use ((:instance tarjan-lowlink-node-exists-when-node-reaches-stack
                          (node successor)
                          (stack (cons node stack))
                          (preorder (append preorder (list node)))))
                   :in-theory (disable tarjan-lowlink-successor
                                       tarjan-lowlink-node-exists-when-node-reaches-stack
                                       (force))))
            ))


  (defret tarjan-lowlink-spec-of-tarjan-lowlink-successor-extended
    (implies (and (tarjan-node-reaches-stack node stack preorder)
                  (not (member node stack))
                  (subsetp stack preorder))
             (equal (tarjan-lowlink-spec successor (cons node stack)
                                         (append preorder (list node)))
                    (tarjan-lowlink-spec node stack preorder)))
    :hints(("Goal" :in-theory (e/d (tarjan-lowlink-spec)
                                   (tarjan-lowlink-successor)))))


  (defret tarjan-lowlink-successor-minimizes-lowlink-lemma
    (implies (and (tarjan-node-reaches-stack node stack preorder)
                  (not (member node stack))
                  (subsetp stack preorder)
                  (member other-node (graph-node-succs node))
                  (tarjan-node-reaches-stack other-node (cons node stack) (append preorder (list node))))
             (<= (index-of (tarjan-lowlink-node node stack preorder) preorder)
                 (index-of (tarjan-lowlink-node other-node (cons node stack) (append preorder (list node)))
                           (append preorder (list node)))))
    :hints(("Goal" :in-theory (e/d (tarjan-lowlink-spec
                                    intersectp
                                    graph-path-p
                                    tarjan-node-stack-endpoint-is-lowlink-node)
                                   (tarjan-lowlink-node-lowest-index))
            :use ((:instance tarjan-lowlink-node-lowest-index
                   (other-node (tarjan-lowlink-node other-node (cons node stack) (append preorder (list node)))))
                  (:instance tarjan-lowlink-node-lowest-index
                   (node other-node)
                   (stack (cons node stack))
                   (preorder (append preorder (list node)))
                   (other-node (tarjan-lowlink-node node stack preorder)))
                  (:instance graph-reachable-through-unvisited-but-last-p-suff
                   (x node)
                   (y (tarjan-lowlink-node other-node (cons node stack) (append preorder (list node))))
                   (visited preorder)
                   (path (cons node (tarjan-node-stack-path other-node (cons node stack)
                                                            (append preorder (list node))))))
                  )
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:use ((:instance tarjan-lowlink-node-exists-when-node-reaches-stack
                         (node other-node)
                         (stack (cons node stack))
                         (preorder (append preorder (list node)))))
                  :in-theory (disable tarjan-lowlink-successor
                                      tarjan-lowlink-node-exists-when-node-reaches-stack)))))



  (local (defret tarjan-lowlink-node-exists-when-node-reaches-stack-superset
           (implies (and (tarjan-node-reaches-stack node stack preorder)
                         (subsetp stack stack2))
                    (member lowlink-node stack2))
           :fn tarjan-lowlink-node))


  (defret tarjan-lowlink-successor-minimizes-lowlink
    (implies (and (tarjan-node-reaches-stack node stack preorder)
                  (not (member node stack))
                  (subsetp stack preorder)
                  (member other-node (graph-node-succs node)))
             (<= (tarjan-lowlink-spec node stack preorder)
                 (tarjan-lowlink-spec other-node (cons node stack) (append preorder (list node)))))
    :hints(("Goal" :in-theory (e/d (tarjan-lowlink-spec)
                                   (index-of-append))
            :do-not-induct t)))


  (defthm tarjan-lowlink-node-of-successor-when-node-does-not-reach-stack
    (implies (and (not (tarjan-node-reaches-stack node stack preorder))
                  (not (member node preorder))
                  (subsetp stack preorder)
                  (member other-node (graph-node-succs node))
                  (tarjan-node-reaches-stack other-node (cons node stack) (append preorder (list node))))
             (equal (tarjan-lowlink-node other-node (cons node stack) (append preorder (list node)))
                    node))
    :hints (("goal" :use ((:instance tarjan-node-reaches-stack-by-path
                           (path (cons node (tarjan-node-stack-path other-node (cons node stack)
                                                                    (append preorder (list node))))))
                          (:instance tarjan-lowlink-node-exists-when-node-reaches-stack
                           (node other-node)
                           (stack (cons node stack))
                           (preorder (append preorder (list node)))))
             :in-theory (e/d (intersectp
                              tarjan-node-stack-endpoint-is-lowlink-node)
                             (tarjan-node-reaches-stack-sufficient
                              graph-reachable-through-unvisited-but-last-p-suff
                              tarjan-lowlink-node-exists-when-node-reaches-stack
                              tarjan-lowlink-node-exists-when-node-reaches-stack-superset))
             :do-not-induct t)))

  (defthm tarjan-lowlink-successor-when-node-does-not-reach-stack
    (implies (and (not (tarjan-node-reaches-stack node stack preorder))
                  (not (member node preorder))
                  (subsetp stack preorder)
                  (member other-node (graph-node-succs node)))
             (<= (len preorder)
                 (tarjan-lowlink-spec other-node (cons node stack) (append preorder (list node)))))
    :hints(("Goal" :in-theory (e/d (tarjan-lowlink-spec)
                                   (index-of-append))
            :do-not-induct t))))


(define tarjan-lowlink-spec-list ((nodes)
                                  (stack true-listp)
                                  (preorder true-listp))
  :guard (subsetp-equal stack preorder)
  :returns (lowlink natp :rule-classes :type-prescription
                    :hints(("Goal" :in-theory (enable min))))
  :hooks (:fix)
  (if (atom nodes)
      (len preorder)
    (min (tarjan-lowlink-spec (car nodes) stack preorder)
         (tarjan-lowlink-spec-list (cdr nodes) stack preorder)))
  ///
  (defret tarjan-lowlink-spec-list-empty
    (implies (not (consp nodes))
             (equal lowlink (len preorder)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm tarjan-lowlink-spec-list-bound
    (<= (tarjan-lowlink-spec-list x stack preorder) (len preorder))
    :hints(("Goal" :in-theory (enable min)))
    :rule-classes :linear)

  (local
   (defthm tarjan-lowlink-spec-list-when-successors
     (implies (and (tarjan-node-reaches-stack node stack preorder)
                   (not (member node stack))
                   (subsetp stack preorder)
                   (subsetp nodes (graph-node-succs node)))
              (<= (tarjan-lowlink-spec node stack preorder)
                  (tarjan-lowlink-spec-list nodes (cons node stack) (append preorder (list node)))))
     :hints(("Goal" :in-theory (e/d (subsetp min) (append))
             :induct (tarjan-lowlink-spec-list nodes (cons node stack) (append preorder (list node)))))
     :rule-classes :linear))

  (local
   (defthm tarjan-lowlink-spec-list-when-successors-if-successor-is-member
     (implies (and (tarjan-node-reaches-stack node stack preorder)
                   (not (member node stack))
                   (subsetp stack preorder)
                   (subsetp nodes (graph-node-succs node))
                   (member (tarjan-lowlink-successor node stack preorder) nodes))
              (equal (tarjan-lowlink-spec-list nodes (cons node stack) (append preorder (list node)))
                     (tarjan-lowlink-spec node stack preorder)))
     :hints(("Goal" :in-theory (e/d (subsetp min) (append))
             :induct (tarjan-lowlink-spec-list nodes (cons node stack) (append preorder (list node)))))))

  (defthm tarjan-lowlink-spec-list-of-successors
    (implies (and (tarjan-node-reaches-stack node stack preorder)
                  (not (member node stack))
                  (subsetp stack preorder))
             (equal (tarjan-lowlink-spec-list (graph-node-succs node)
                                              (cons node stack)
                                              (append preorder (list node)))
                    (tarjan-lowlink-spec node stack preorder))))

  (local
   (defthm tarjan-lowlink-spec-list-of-successors-bound-when-node-does-not-reach-stack-lemma
     (implies (and (not (tarjan-node-reaches-stack node stack preorder))
                   (not (member node preorder))
                   (subsetp stack preorder)
                   (subsetp nodes (graph-node-succs node)))
              (<= (len preorder)
                  (tarjan-lowlink-spec-list nodes (cons node stack) (append preorder (list node)))))
     :hints(("Goal" :in-theory (e/d (subsetp min) (append))
             :induct (tarjan-lowlink-spec-list nodes (cons node stack) (append preorder (list node)))))
     :rule-classes :linear))

  (defthm tarjan-lowlink-spec-list-of-successors-bound-when-node-does-not-reach-stack
    (implies (and (not (tarjan-node-reaches-stack node stack preorder))
                  (not (member node preorder))
                  (subsetp stack preorder))
             (<= (len preorder)
                 (tarjan-lowlink-spec-list (graph-node-succs node)
                                           (cons node stack)
                                           (append preorder (list node)))))
    :rule-classes :linear)

  (defthm min-tarjan-lowlink-spec-list-gives-node-reaches-stack
    (implies (and (not (member node preorder))
                  (subsetp stack preorder))
             (iff (equal (min (tarjan-lowlink-spec-list (graph-node-succs node)
                                                        (cons node stack)
                                                        (append preorder (list node)))
                              (len preorder))
                         (len preorder))
                  (not (tarjan-node-reaches-stack node stack preorder))))
    :hints(("Goal" :in-theory (e/d (min)
                                   (tarjan-lowlink-spec-list))
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:in-theory (enable tarjan-lowlink-spec))))))

(define prefix-path-to-blocked ((preorder true-listp) (path true-listp))
  :returns (prefix)
  (if (atom path)
      nil
    (if (member-equal (car path) preorder)
        (list (car path))
      (cons (car path) (prefix-path-to-blocked preorder (cdr path)))))
  ///
  (defret subsetp-of-prefix-path-to-blocked
    (subsetp prefix path)
    :hints(("Goal" :in-theory (enable subsetp))))

  (defret graph-path-p-of-prefix-path-to-blocked
    (implies (graph-path-p path)
             (graph-path-p prefix))
    :hints(("Goal" :in-theory (enable graph-path-p))))

  (defret first-of-prefix-path-to-blocked
    (equal (car prefix) (car path)))

  (defret consp-of-prefix-path-to-blocked
    (implies (consp path)
             (consp prefix)))

  (defret not-member-of-prefix-path-to-blocked
    (implies (not (member k path))
             (not (member k prefix))))

  (defret no-duplicatesp-of-prefix-path-to-blocked
    (implies (no-duplicatesp path)
             (no-duplicatesp prefix)))

  (defret not-intersectp-of-prefix-path-to-blocked
    (implies (not (intersectp path y))
             (not (intersectp prefix y)))
    :hints(("Goal" :in-theory (enable intersectp))))

  (defret len-of-prefix-path-to-blocked-bound
    (<= (len prefix) (len path))
    :rule-classes :linear)

  (defret preorder-not-intersecting-butlast-of-prefix-path-to-blocked
    (not (intersectp (butlast prefix 1) preorder))
    :hints(("Goal" :in-theory (enable intersectp))))

  (defret not-intersectp-butlast-of-prefix-path-to-blocked
    (implies (not (intersectp (butlast path n) y))
             (not (intersectp (butlast prefix n) y)))
    :hints(("Goal" :in-theory (enable intersectp)))))


(defsection tarjan-stack-member-cond-list
  (defun-sk tarjan-stack-member-cond-list (x stack preorder new-stack)
    (forall y
            (iff (member y new-stack)
                 (or (member y stack)
                     (and (graph-reachable-through-unvisited-for-some-x x y preorder)
                          (tarjan-node-reaches-stack y stack preorder)))))
    :rewrite :direct)
  (in-theory (disable tarjan-stack-member-cond-list))

  (defthm tarjan-stack-member-cond-list-for-empty-x
    (implies (not (consp x))
             (iff (tarjan-stack-member-cond-list x stack preorder new-stack)
                  (set-equiv new-stack stack)))
    :hints ((and stable-under-simplificationp
                 (cond ((eq (caar (last clause)) 'set-equiv)
                        '(:computed-hint-replacement
                          ((witness :ruleset set-reasoning-no-consp)
                           (and stable-under-simplificationp
                                '(:use ((:instance tarjan-stack-member-cond-list-necc
                                         (y k0)))
                                  :in-theory (disable tarjan-stack-member-cond-list-necc))))
                          :no-op t))
                       (t '(:computed-hint-replacement
                            ((set-reasoning))
                            :expand ((tarjan-stack-member-cond-list x stack preorder new-stack)))))))))

(defsection tarjan-stack-member-cond
  (defun-sk tarjan-stack-member-cond (x stack preorder new-stack)
    (forall y
            (iff (member y new-stack)
                 (or (member y stack)
                     (and (graph-reachable-through-unvisited-p x y preorder)
                          (tarjan-node-reaches-stack y stack preorder)))))
    :rewrite :direct)
  (in-theory (disable tarjan-stack-member-cond))

  (fty::deffixequiv tarjan-stack-member-cond
    :args ((stack true-listp)
           (preorder true-listp)
           (new-stack true-listp))
    :hints (("goal" :cases ((tarjan-stack-member-cond x stack preorder new-stack)))
            (and stable-under-simplificationp
                 (let ((pos-lit (assoc 'tarjan-stack-member-cond clause))
                       (neg-lit (cadr (assoc 'not clause))))
                   `(:expand (,pos-lit)
                     :use ((:instance tarjan-stack-member-cond-necc
                            (x ,(nth 1 neg-lit))
                            (stack ,(nth 2 neg-lit))
                            (preorder ,(nth 3 neg-lit))
                            (new-stack ,(nth 4 neg-lit))
                            (y (tarjan-stack-member-cond-witness . ,(cdr pos-lit))))))))))

  (local (defthmd equal-of-plus-1
           (equal (equal (+ 1 x) (+ 1 y))
                  (equal (fix x) (fix y)))))

  (local (defthm equal-of-index-of
           (implies (member k1 x)
                    (equal (equal (index-of k1 x)
                                  (index-of k2 x))
                           (equal k1 k2)))
           :hints(("Goal" :in-theory (enable index-of
                                             equal-of-plus-1)))))

  ;; Cases:
  ;; y.lowlink' < y.lowlink <= x.lowlink
  ;; y.lowlink < y.lowlink' <= x.lowlink
  ;; y.lowlink < x.lowlink <= y.lowlink'
  ;; y.lowlink' < x.lowlink <= y.lowlink
  ;; y.lowlink < x.lowlink and ! y.lowlink'
  ;; y.lowlink' < x.lowlink and ! y.lowlink
  ;; y.lowlink != y.lowlink' and ! x.lowlink
  ;; y.lowlink and ! y.lowlink' and ! x.lowlink
  ;; y.lowlink' and ! y.lowlink and ! x.lowlink

  ;; -- y.lowlink' >= y.lowlink (if both exist) because the preorder has grown:
  ;; any original stack node that y can reach with the new preorder can also be
  ;; reached with the old preorder.




  ;; Similarly, if y.lowlink' < x.lowlink, then y.lowlink must exist because
  ;; it can reach any stack node that y' can.

  ;; This gets rid of three of the above cases, leaving 6:

  ;; y.lowlink < y.lowlink' <= x.lowlink
  ;; y.lowlink < x.lowlink <= y.lowlink'
  ;; y.lowlink < x.lowlink and ! y.lowlink'
  ;; y.lowlink != y.lowlink' and ! x.lowlink
  ;; y.lowlink and ! y.lowlink' and ! x.lowlink
  ;; y.lowlink' and ! y.lowlink and ! x.lowlink

  ;; We actually don't have to worry about the cases where x is already in the
  ;; preorder, which rules out the bottom 3, so we are left with:

  ;; y.lowlink < y.lowlink' <= x.lowlink
  ;; y.lowlink < x.lowlink <= y.lowlink'
  ;; y.lowlink < x.lowlink and ! y.lowlink'


  ;; The crux of these is that the new-preorder is extended with nodes
  ;; reachable through unvisited paths from x. Thus for any path that y could
  ;; take to a stack node that was not available to y', that blockage is due to
  ;; something reachable from x, which will be reflected in x's lowlink.

  (local (defthm tarjan-stack-member-cond-implies-new-stack-superset
           (implies (tarjan-stack-member-cond x stack preorder new-stack)
                    (subsetp stack new-stack))
           :hints ((set-reasoning))))

  (local (defthm tarjan-stack-member-cond-implies-stack-new-elements-cond
           (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                         (tarjan-stack-member-cond x stack preorder new-stack))
                    (subsetp (set-difference$ new-stack stack)
                             (set-difference$ new-preorder preorder)))
           :hints ((set-reasoning))))

  (defthm tarjan-lowlink-spec-min-of-extension
    (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                  (tarjan-stack-member-cond x stack preorder new-stack)
                  (prefixp preorder new-preorder)
                  (subsetp stack preorder))
             (equal (min (tarjan-lowlink-spec x stack preorder)
                         (tarjan-lowlink-spec node new-stack new-preorder))
                    (min (tarjan-lowlink-spec x stack preorder)
                         (tarjan-lowlink-spec node stack preorder))))
    :hints(("Goal" :in-theory (enable tarjan-lowlink-spec-min-of-extension-lemma)))
    :otf-flg t)

  ;; (local (defthmd tarjan-lowlink-min-commutative
  ;;          (equal (tarjan-lowlink-min x y)
  ;;                 (tarjan-lowlink-min y x))
  ;;          :hints(("Goal" :in-theory (enable tarjan-lowlink-min)))))
  ;; (local (defthmd tarjan-lowlink-min-associative
  ;;          (equal (tarjan-lowlink-min (tarjan-lowlink-min x y) z)
  ;;                 (tarjan-lowlink-min x (tarjan-lowlink-min y z)))
  ;;          :hints(("Goal" :in-theory (enable tarjan-lowlink-min maybe-natp-fix)))))

  ;; (local (defthm tarjan-lowlink-min-special
  ;;          (implies (and (equal (tarjan-lowlink-min x lst1)
  ;;                               (tarjan-lowlink-min x lst))
  ;;                        (equal (tarjan-lowlink-min x y1)
  ;;                               (tarjan-lowlink-min x y)))
  ;;                   (equal (equal (tarjan-lowlink-min x (tarjan-lowlink-min y1 lst1))
  ;;                                 (tarjan-lowlink-min x (tarjan-lowlink-min y lst)))
  ;;                          t))
  ;;          :hints(("Goal" :use ((:instance tarjan-lowlink-min-associative
  ;;                                (x x) (y y1) (z lst1))
  ;;                               (:instance tarjan-lowlink-min-commutative
  ;;                                (x x) (y y))
  ;;                               (:instance tarjan-lowlink-min-associative
  ;;                                (x y) (y x) (z lst1))
  ;;                               (:instance tarjan-lowlink-min-associative
  ;;                                (x y) (y x) (z lst))
  ;;                               (:instance tarjan-lowlink-min-associative
  ;;                                (x x) (y y) (z lst)))))))


  (local (defthm min-special
           (implies (and (equal (min x lst1)
                                (min x lst))
                         (equal (min x y1)
                                (min x y))
                         (natp x) (natp y1) (natp y) (natp lst) (natp lst1))
                    (equal (equal (min x (min y1 lst1))
                                  (min x (min y lst)))
                           t))
           :hints(("Goal" :in-theory (enable min)))))



  (local (defthm len-when-prefixp
           (implies (prefixp a b)
                    (<= (len a) (len b)))
           :hints(("Goal" :in-theory (enable prefixp)))
           :rule-classes :linear))

  (defthm tarjan-lowlink-spec-list-min-of-extension
    (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                  (tarjan-stack-member-cond x stack preorder new-stack)
                  (prefixp preorder new-preorder)
                  (subsetp stack preorder))
             (equal (min (tarjan-lowlink-spec x stack preorder)
                         (tarjan-lowlink-spec-list nodes new-stack new-preorder))
                    (min (tarjan-lowlink-spec x stack preorder)
                         (tarjan-lowlink-spec-list nodes stack preorder))))
    :hints(("Goal" :in-theory (enable tarjan-lowlink-spec-list)
            :induct t)
           (and stable-under-simplificationp
                '(:in-theory (enable min)))))


  (local (defthmd last-of-cdr
           (implies (consp (cdr x))
                    (equal (last (cdr x))
                           (last x)))))

  (local (defthmd intersectp-when-not-intersectp-butlast
           (implies (and (not (intersectp (butlast x 1) y))
                         (consp x))
                    (iff (intersectp x y)
                         (member (car (last x)) y)))
           :hints(("Goal" :in-theory (enable intersectp last)))))


  (local (defthmd butlast-of-cdr
           (implies (< (nfix n) (len x))
                    (equal (butlast (cdr x) n)
                           (cdr (butlast x n))))))

  (local (defthm intersectp-cdr
           (implies (not (intersectp x y))
                    (not (intersectp (cdr x) y)))
           :hints(("Goal" :in-theory (enable intersectp)))))

  (local (defun tarjan-node-reaches-stack-of-member-cond-extension-no-hint
           (x y stack preorder new-stack new-preorder)
           (declare (ignorable x))
           (b* ((y-ns (tarjan-node-stack-path y new-stack new-preorder))
                (new-stack-node (car (last y-ns)))
                ((when (member new-stack-node stack))
                 ;; y reaches the old stack by the same path
                 `'(:use ((:instance tarjan-node-reaches-stack-by-path
                           (node ,(hq y)) (path ,(hq y-ns))))))
                ((unless (tarjan-node-reaches-stack new-stack-node stack preorder))
                 `'(:use ((:instance tarjan-stack-member-cond-necc
                           (y ,(hq new-stack-node))))))
                ((when (intersectp y-ns preorder))
                 `'(:use ((:instance intersectp-when-not-intersectp-butlast
                           (y preorder) (x ,(hq y-ns))))))

                ;; new-stack-node reaches stack and y reaches new-stack-node.
                (path (append y-ns (cdr (tarjan-node-stack-path new-stack-node stack preorder)))))

             `'(:use ((:instance tarjan-node-reaches-stack-by-path
                       (node ,(hq y)) (path ,(hq path))))))))


  (local (defthm tarjan-node-reaches-stack-of-member-cond-extension-no
           (implies (and (subsetp preorder new-preorder)
                         (tarjan-stack-member-cond x stack preorder new-stack)
                         (subsetp stack preorder)
                         (not (tarjan-node-reaches-stack y stack preorder)))
                    (not (tarjan-node-reaches-stack y new-stack new-preorder)))
           :hints (("goal" :in-theory (e/d (last-of-cdr butlast-of-cdr)
                                           (tarjan-stack-member-cond-necc
                                            last
                                            butlast-when-len-greater))
                    :do-not-induct t)
                   (use-termhint (tarjan-node-reaches-stack-of-member-cond-extension-no-hint
                                  x y stack preorder new-stack new-preorder)))))


  (local (defthmd prefix-path-to-blocked-last-is-member-of-preorder-special
           (implies (member (car (last path)) preorder)
                    (member (car (last (prefix-path-to-blocked preorder path))) preorder))
           :hints(("Goal" :in-theory (enable prefix-path-to-blocked last)))))

  (local (defthm prefix-path-to-blocked-when-butlast-not-intersecting-preorder
           (implies (and (member (car (last (prefix-path-to-blocked other-preorder path))) preorder)
                         (not (intersectp (butlast path 1) preorder)))
                    (equal (prefix-path-to-blocked other-preorder path)
                           (list-fix path)))
           :hints(("Goal" :in-theory (enable last prefix-path-to-blocked intersectp list-fix)))))

  (local (defthm intersectp-of-butlast-of-member
           (implies (not (intersectp (butlast x n) y))
                    (not (intersectp (butlast (member k x) n) y)))
           :hints(("Goal" :in-theory (e/d (intersectp)
                                          (butlast))))))

  (local (defthm node-reaches-stack-implies-member-of-path-reaches-stack
           (implies (and (tarjan-node-reaches-stack node stack preorder)
                         (member x (tarjan-node-stack-path node stack preorder)))
                    (tarjan-node-reaches-stack x stack preorder))
           :hints (("goal" :use ((:instance tarjan-node-reaches-stack-by-path
                                  (node x)
                                  (path (member x (tarjan-node-stack-path node stack preorder)))))))))

  (local (defthm car-last-prefix-path-to-blocked-is-member
           (implies (consp x)
                    (member (car (last (prefix-path-to-blocked preorder x))) x))
           :hints(("Goal" :in-theory (enable last prefix-path-to-blocked)))))


  (local (defthm tarjan-node-reaches-stack-of-member-cond-extension-yes
           (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                         (tarjan-stack-member-cond x stack preorder new-stack)
                         (subsetp stack preorder)
                         (tarjan-node-reaches-stack y stack preorder))
                    (tarjan-node-reaches-stack y new-stack new-preorder))
           ;; Let z be the first node that is in the new preorder in the path
           ;; from y to the old stack (must exist, since at least the last node
           ;; in the path is in the stack and therefore the old preorder.)  If
           ;; it is in the old preorder, it must be the last node, therefore is
           ;; in the stack and we're done.  Otherwise, since it is in the new
           ;; preorder it's reachable from x through unvisited, and it reaches
           ;; the old stack (via the rest of the original path).  Therefore z
           ;; is in the new stack, so we take the path to z.
           :hints (("goal" :use ((:instance tarjan-node-reaches-stack-by-path
                                  (node y)
                                  (stack new-stack)
                                  (preorder new-preorder)
                                  (path (prefix-path-to-blocked
                                         new-preorder
                                         (tarjan-node-stack-path y stack preorder))))
                                 (:instance prefix-path-to-blocked-last-is-member-of-preorder-special
                                  (preorder new-preorder)
                                  (path (tarjan-node-stack-path y stack preorder) )))
                    :do-not-induct t))
           :otf-flg t))

  (local (defthm subsetp-by-preorder-member-cond
           (implies (tarjan-preorder-member-cond x preorder new-preorder)
                    (subsetp preorder new-preorder))
           :hints ((set-reasoning))
           :rule-classes :forward-chaining))

  (defthm tarjan-node-reaches-stack-of-member-cond-extension
    (implies (and (tarjan-stack-member-cond x stack preorder new-stack)
                  (tarjan-preorder-member-cond x preorder new-preorder)
                  (subsetp stack preorder))
             (iff (tarjan-node-reaches-stack y new-stack new-preorder)
                  (tarjan-node-reaches-stack y stack preorder))))


  (local (defun tarjan-node-reaches-stack-of-member-cond-list-extension-no-hint
           (x y stack preorder new-stack new-preorder)
           (declare (ignorable x))
           (b* ((y-ns (tarjan-node-stack-path y new-stack new-preorder))
                (new-stack-node (car (last y-ns)))
                ((when (member new-stack-node stack))
                 ;; y reaches the old stack by the same path
                 `'(:use ((:instance tarjan-node-reaches-stack-by-path
                           (node ,(hq y)) (path ,(hq y-ns))))))
                ((unless (tarjan-node-reaches-stack new-stack-node stack preorder))
                 `'(:use ((:instance tarjan-stack-member-cond-list-necc
                           (y ,(hq new-stack-node))))))
                ((when (intersectp y-ns preorder))
                 `'(:use ((:instance intersectp-when-not-intersectp-butlast
                           (y preorder) (x ,(hq y-ns))))))

                ;; new-stack-node reaches stack and y reaches new-stack-node.
                (path (append y-ns (cdr (tarjan-node-stack-path new-stack-node stack preorder)))))

             `'(:use ((:instance tarjan-node-reaches-stack-by-path
                       (node ,(hq y)) (path ,(hq path))))))))


  (local (defthm tarjan-node-reaches-stack-of-member-cond-list-extension-no
           (implies (and (subsetp preorder new-preorder)
                         (tarjan-stack-member-cond-list x stack preorder new-stack)
                         (subsetp stack preorder)
                         (not (tarjan-node-reaches-stack y stack preorder)))
                    (not (tarjan-node-reaches-stack y new-stack new-preorder)))
           :hints (("goal" :in-theory (e/d (last-of-cdr butlast-of-cdr)
                                           (tarjan-stack-member-cond-list-necc
                                            last
                                            butlast-when-len-greater))
                    :do-not-induct t)
                   (use-termhint (tarjan-node-reaches-stack-of-member-cond-list-extension-no-hint
                                  x y stack preorder new-stack new-preorder)))))




  (local (defthm tarjan-node-reaches-stack-of-member-cond-list-extension-yes
           (implies (and (tarjan-preorder-member-cond-list x preorder new-preorder)
                         (tarjan-stack-member-cond-list x stack preorder new-stack)
                         (subsetp stack preorder)
                         (tarjan-node-reaches-stack y stack preorder))
                    (tarjan-node-reaches-stack y new-stack new-preorder))
           :hints (("goal" :use ((:instance tarjan-node-reaches-stack-by-path
                                  (node y)
                                  (stack new-stack)
                                  (preorder new-preorder)
                                  (path (prefix-path-to-blocked
                                         new-preorder
                                         (tarjan-node-stack-path y stack preorder))))
                                 (:instance prefix-path-to-blocked-last-is-member-of-preorder-special
                                  (preorder new-preorder)
                                  (path (tarjan-node-stack-path y stack preorder) )))
                    :do-not-induct t))
           :otf-flg t))


  (local (defthm subsetp-by-preorder-member-cond-list
           (implies (tarjan-preorder-member-cond-list x preorder new-preorder)
                    (subsetp preorder new-preorder))
           :hints ((set-reasoning))
           :rule-classes :forward-chaining))

  (defthm tarjan-node-reaches-stack-of-member-cond-list-extension
      (implies (and (tarjan-stack-member-cond-list x stack preorder new-stack)
                    (tarjan-preorder-member-cond-list x preorder new-preorder)
                    (subsetp stack preorder))
               (iff (tarjan-node-reaches-stack y new-stack new-preorder)
                    (tarjan-node-reaches-stack y stack preorder)))))






;; (fty::deflist true-list-listp :pred true-list-listp :elt-type true-listp :true-listp t)

(defsection tarjan-scc-stack/lowlink-conds

  (local (defthm tarjan-lowlink-node-when-member-preorder
           (implies (member x preorder)
                    (equal (tarjan-lowlink-node x stack preorder)
                           (and (member x stack) x)))
           :hints(("Goal" :in-theory (enable tarjan-lowlink-node)))))

  (local (defthm tarjan-lowlink-spec-when-member-preorder
           (implies (member x preorder)
                    (equal (tarjan-lowlink-spec x stack preorder)
                           (if (member x stack)
                               (index-of x preorder)
                             (len preorder))))
           :hints(("Goal" :in-theory (enable tarjan-lowlink-spec)))))

  (local (defthm min-when-a-greater
           (implies (and (<= b a)
                         (natp b) (natp a))
                    (equal (min a b) b))
           :hints(("Goal" :in-theory (enable min)))))
  (local (defthm min-when-b-greater
           (implies (and (<= a b)
                         (natp b) (natp a))
                    (equal (min a b) a))
           :hints(("Goal" :in-theory (enable min)))))

  (local (defthm reachable-through-unvisited-for-some-x-by-member-cond-1-rw
           (implies (and (bind-free '((preorder . preorder)
                                      (x . (car x))) (x preorder))
                         (tarjan-preorder-member-cond x preorder new-preorder)
                         (not (graph-reachable-through-unvisited-for-some-x z y preorder)))
                    (not (graph-reachable-through-unvisited-for-some-x z y new-preorder)))
           :hints(("Goal" :in-theory (enable graph-reachable-through-unvisited-for-some-x)))))

  (local (defthm reachable-through-unvisited-for-some-x-by-member-cond-2-rw
           (implies (and (bind-free '((preorder . preorder)
                                      (x . (car x))) (x preorder))
                         (tarjan-preorder-member-cond x preorder new-preorder)
                         (not (graph-reachable-through-unvisited-p x y preorder))
                         (graph-reachable-through-unvisited-for-some-x z y preorder))
                    (graph-reachable-through-unvisited-for-some-x z y new-preorder))
           :hints(("Goal" :in-theory (enable graph-reachable-through-unvisited-for-some-x)))
           :rule-classes ((:rewrite :match-free :all))))

  (std::defret-mutual tarjan-sccs-lowlink-correct
    (defret tarjan-sccs-lowlink-correct
      (implies (subsetp stack preorder)
               (and (equal lowlink (tarjan-lowlink-spec x stack preorder))
                    (tarjan-stack-member-cond x stack preorder new-stack)))
      :hints ('(:expand (<call>)
                :do-not-induct t)
              (and stable-under-simplificationp
                   (eq (caar (last clause)) 'tarjan-stack-member-cond)
                   `(:expand (,(car (last clause)))))
              (and stable-under-simplificationp
                   (let ((witness (find-call-lst
                                   'tarjan-stack-member-cond-witness
                                   clause)))
                     (and witness
                          `(:clause-processor
                            (simple-generalize-cp
                             clause '((,witness . witness))))))))
      :fn tarjan-sccs)
    (defret tarjan-sccs-list-lowlink-correct
      (implies (subsetp stack preorder)
               (and (equal lowlink (tarjan-lowlink-spec-list x stack preorder))
                    (tarjan-stack-member-cond-list x stack preorder new-stack)))
      :hints ('(:expand (<call>
                         (tarjan-lowlink-spec-list x stack preorder))
                :do-not-induct t)
              (and stable-under-simplificationp
                   (eq (caar (last clause)) 'tarjan-stack-member-cond-list)
                   `(:expand (,(car (last clause)))))
              (and stable-under-simplificationp
                   (let ((witness (find-call-lst
                                   'tarjan-stack-member-cond-list-witness
                                   clause)))
                     (and witness
                          `(:clause-processor
                            (simple-generalize-cp
                             clause '((,witness . witness)))))))
              (and stable-under-simplificationp
                   '(:expand ((graph-reachable-through-unvisited-for-some-x x witness preorder)))))
      :fn tarjan-sccs-list)
    :otf-flg t)

)


;; What gets added to the SCCs?

(defsection scc-in-preorder-p
  (defun-sk scc-in-preorder-p (scc preorder)
    (forall (x y)
            (implies (member x scc)
                     (iff (member y scc)
                          (and (graph-reachable-through-unvisited-p x y preorder)
                               (graph-reachable-through-unvisited-p y x preorder)))))
    :rewrite :direct)

  (in-theory (disable scc-in-preorder-p))

  (defwitness scc-in-preorder-p-witnessing
    :predicate (not (scc-in-preorder-p scc preorder))
    :expr (let ((x (mv-nth 0 (scc-in-preorder-p-witness scc preorder)))
                (y (mv-nth 1 (scc-in-preorder-p-witness scc preorder))))
            (not (implies (member x scc)
                          (iff (member y scc)
                               (and (graph-reachable-through-unvisited-p x y preorder)
                                    (graph-reachable-through-unvisited-p y x preorder))))))
    :generalize (((mv-nth 0 (scc-in-preorder-p-witness scc preorder)) . sccx)
                 ((mv-nth 1 (scc-in-preorder-p-witness scc preorder)) . sccy))
    :hints ('(:use (scc-in-preorder-p)
              :in-theory (disable scc-in-preorder-p))))

  (fty::deffixequiv scc-in-preorder-p
    :args ((preorder true-listp)
           (scc true-listp))
    :hints (("goal" :cases ((scc-in-preorder-p scc preorder)))
            (and stable-under-simplificationp
                 (let ((pos-lit (assoc 'scc-in-preorder-p clause))
                       (neg-lit (cadr (assoc 'not clause))))
                   `(:expand (,pos-lit)
                     :use ((:instance scc-in-preorder-p-necc
                            (scc ,(nth 1 neg-lit))
                            (preorder ,(nth 2 neg-lit))
                            (x (mv-nth 0 (scc-in-preorder-p-witness . ,(cdr pos-lit))))
                            (y (mv-nth 1 (scc-in-preorder-p-witness . ,(cdr pos-lit))))))
                     :in-theory (disable scc-in-preorder-p-necc))))))

  (defthm sccs-unique-up-to-set-equiv
    (implies (and (scc-in-preorder-p x preorder)
                  (scc-in-preorder-p y preorder)
                  (member k x)
                  (member k y))
             (set-equiv x y))
    :hints ((set-reasoning)
            (and stable-under-simplificationp
                 '(:use ((:instance scc-in-preorder-p-necc
                          (scc y)
                          (x k)
                          (y k0))
                         (:instance scc-in-preorder-p-necc
                          (scc x)
                          (x k)
                          (y k0)))
                   :do-not-induct t)))
    :otf-flg t)

  (defthmd member-of-scc-when-reached-and-reaches
    (implies (and (scc-in-preorder-p scc preorder)
                  (member x scc)
                  (member y scc)
                  (graph-reachable-through-unvisited-p x z preorder)
                  (graph-reachable-through-unvisited-p z y preorder))
             (member z scc))
    :hints (("goal" :use ((:instance scc-in-preorder-p-necc
                           (x x) (y z))
                          (:instance scc-in-preorder-p-necc
                           (x x) (y y)))
             :in-theory (disable scc-in-preorder-p-necc))))

  (defthmd scc-members-equivalently-reachable
    (implies (and (scc-in-preorder-p scc preorder)
                  (member x scc)
                  (member y scc)
                  (graph-reachable-through-unvisited-p z x preorder))
             (graph-reachable-through-unvisited-p z y preorder))
    :hints (("goal" :use ((:instance graph-reachable-through-unvisited-p-suff
                           (x z) (y y) (visited preorder)
                           (path (append (graph-reachable-through-unvisited-p-witness
                                          z x preorder)
                                         (cdr (graph-reachable-through-unvisited-p-witness
                                               x y preorder)))))
                          (:instance scc-in-preorder-p-necc))
             :in-theory (disable scc-in-preorder-p-necc))))

  (defthmd scc-members-equivalently-reach
    (implies (and (scc-in-preorder-p scc preorder)
                  (member x scc)
                  (member y scc)
                  (graph-reachable-through-unvisited-p x z preorder))
             (graph-reachable-through-unvisited-p y z preorder))
    :hints (("goal" :use ((:instance graph-reachable-through-unvisited-p-suff
                           (x x) (y z) (visited preorder)
                           (path (append (graph-reachable-through-unvisited-p-witness
                                          y x preorder)
                                         (cdr (graph-reachable-through-unvisited-p-witness
                                               x z preorder)))))
                          (:instance scc-in-preorder-p-necc))
             :in-theory (disable scc-in-preorder-p-necc))))

  (defthmd scc-paths-subset-of-scc-in-preorder
    (implies (and (scc-in-preorder-p scc preorder)
                  (consp path)
                  (member (car path) scc)
                  (member (car (last path)) scc)
                  (graph-path-p path)
                  (not (intersectp path preorder)))
             (subsetp path scc))
    :hints (("goal" :in-theory (disable scc-in-preorder-p-necc)
             :do-not-induct t)
            (witness :ruleset set-reasoning-no-consp)
            (and stable-under-simplificationp
                 '(:use ((:instance member-of-scc-when-reached-and-reaches
                          (x (car path))
                          (y (car (last path)))
                          (z k0))
                         (:instance graph-reachable-through-unvisited-p-suff
                          (x (car path))
                          (y k0) (visited preorder)
                          (path (prefix-path-to k0 path)))
                         (:instance graph-reachable-through-unvisited-p-suff
                          (x k0) (y (car (last path)))
                          (visited preorder)
                          (path (member k0 path))))
                   :expand ((:free (x) (hide x)))))))

  (defthmd scc-path-member-is-in-scc
    (implies (and (scc-in-preorder-p scc preorder)
                  (member (car path) scc)
                  (member (car (last path)) scc)
                  (member x path)
                  (graph-path-p path)
                  (not (intersectp path preorder)))
             (member x scc))
    :hints (("goal" :use scc-paths-subset-of-scc-in-preorder
             :in-theory (disable scc-paths-subset-of-scc-in-preorder))))

  (local (defthm intersectp-witness-is-in-sets
           (implies (intersectp x y)
                    (let ((k (intersectp-witness x y)))
                      (and (member k x)
                           (member k y))))
           :hints(("Goal" :in-theory (enable intersectp-witness intersectp)))))



  (local (defun scc-in-preorder-p-preserved-by-extension-lemma1-hint (x a b preorder new-preorder scc)
           (b* (((unless (graph-reachable-through-unvisited-p a b preorder))
                 `(:use ((:instance scc-in-preorder-p-necc
                           (x ,(hq a)) (y ,(hq b))))))
                (a-b (graph-reachable-through-unvisited-canonical-witness a b preorder))
                ((unless (intersectp a-b new-preorder))
                 `(:use ((:instance graph-reachable-through-unvisited-p-suff
                           (x ,(hq a)) (y ,(hq b)) (visited new-preorder)
                           (path ,(hq a-b))))))
                (int (intersectp-witness a-b new-preorder))
                ((when (member int preorder))
                 ;; int can't be in preorder or a-b is not actually a sufficient path
                 `(:use ((:instance intersectp-member
                           (a ,(hq int))
                           (x ,(hq a-b))
                           (y ,(hq preorder))))
                    :in-theory (disable intersectp-member
                                        scc-in-preorder-p-necc)))
                ((unless (graph-reachable-through-unvisited-p x int preorder))
                 ;; int is reachable from x in preorder
                 `(:use ((:instance tarjan-preorder-member-cond-necc
                           (y ,(hq int))))
                    :in-theory (disable tarjan-preorder-member-cond-necc
                                        scc-in-preorder-p-necc)))
                ((unless (member int scc))
                 `(:use ((:instance scc-path-member-is-in-scc
                           (x ,(hq int))
                           (path ,(hq a-b))))))
                ;; Now (car scc) is reachable from x because int is reachable from x.
                (use-hints `((:instance scc-members-equivalently-reachable
                              (z ,(hq x))
                              (x ,(hq int))
                              (y ,(hq (car scc)))))))
             `(:use ,use-hints
                :in-theory (disable tarjan-preorder-member-cond-necc
                                    scc-in-preorder-p-necc)))))



  (local (defthmd scc-in-preorder-p-preserved-by-extension-lemma1
           ;; ->: If a, b are members of scc, show that a reaches b in new-preorder:
           ;; Get the path from a to b in the old preorder. For any node in that path
           ;; intersecting the new preorder, we know that node is reachable from x in
           ;; the preorder by the preorder-member-cond. That implies (car scc) is reachable from x.
           (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                         (scc-in-preorder-p scc preorder)
                         (not (graph-reachable-through-unvisited-p x (car scc) preorder))
                         (member a scc)
                         (member b scc))
                    (graph-reachable-through-unvisited-p a b new-preorder))
           :hints (("goal"
                    :in-theory (disable scc-in-preorder-p-necc)
                    :do-not-induct t)
                   (use-termhint (scc-in-preorder-p-preserved-by-extension-lemma1-hint
                                  x a b preorder new-preorder scc)))
           :otf-flg t))


  (local (defun scc-in-preorder-p-preserved-by-extension-hint (x preorder new-preorder scc)
           (declare (ignore x preorder))
           (b* (((mv a b) (scc-in-preorder-p-witness scc new-preorder))
                ((when (and ;; (member a scc)
                            (member b scc)))
                 `'(:use ((:instance scc-in-preorder-p-preserved-by-extension-lemma1
                           (a ,(hq a))
                           (b ,(hq b)))
                          (:instance scc-in-preorder-p-preserved-by-extension-lemma1
                           (a ,(hq b))
                           (b ,(hq a))))
                    :in-theory (disable scc-in-preorder-p-preserved-by-extension-lemma1
                                        scc-in-preorder-p-necc)))
                ((when (and (graph-reachable-through-unvisited-p a b new-preorder)
                            (graph-reachable-through-unvisited-p b a new-preorder)))
                 `'(:use ((:instance scc-in-preorder-p-necc
                           (x ,(hq a))
                           (y ,(hq b))
                           (preorder preorder)))
                    :in-theory (disable scc-in-preorder-p-necc))))
             `'nil)))

  (local
   (defthm scc-in-preorder-p-preserved-by-extension
     ;; ->: If a, b are members of scc, show that a reaches b in new-preorder:
     ;; Get the path from a to b in the
     (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                   (scc-in-preorder-p scc preorder)
                   (not (graph-reachable-through-unvisited-p x (car scc) preorder)))
              (scc-in-preorder-p scc new-preorder))
     :hints (("goal" :expand ((scc-in-preorder-p scc new-preorder))
              :in-theory (disable scc-in-preorder-p-necc))
             (use-termhint (scc-in-preorder-p-preserved-by-extension-hint x preorder new-preorder scc)))))


  (local (defthmd not-scc-in-preorder-p-preserved-by-extension-lemma1
           ;; ->: If a, b are members of scc, show that a reaches b in new-preorder:
           ;; Get the path from a to b in the new preorder. For any node in that path
           ;; intersecting the new preorder, we know that node is reachable from x in
           ;; the preorder by the preorder-member-cond. That implies (car scc) is reachable from x.
           (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                         (scc-in-preorder-p scc new-preorder)
                         (not (graph-reachable-through-unvisited-p x (car scc) preorder))
                         (member a scc)
                         (member b scc))
                    (graph-reachable-through-unvisited-p a b preorder))
           :hints (("goal" :use ((:instance scc-in-preorder-p-necc
                                  (x a) (y b) (preorder new-preorder)))
                    :in-theory (disable scc-in-preorder-p-necc)))))

  (local (defun not-scc-in-preorder-lemma-hint (x a preorder new-preorder scc)
                 (b* (;; ((unless (graph-reachable-through-unvisited-p x a preorder))
                      ;;  ;; reachability is preserved by reachable-through-unvisited-by-member-cond-2.
                      ;;  `'(:use ((:instance reachable-through-unvisited-by-member-cond-2
                      ;;            (z ,(hq b)) (y ,(hq a))))))
                      ;; otherwise, since a reaches (car scc)...
                      ((unless (graph-reachable-through-unvisited-p a (car scc) preorder))
                       `'(:use ((:instance scc-in-preorder-p-necc
                                 (x ,(hq a)) (y ,(hq (car scc))) (preorder ,(hq new-preorder)))))))
                   ;; we show x reaches (car scc).
                   `'(:use ((:instance graph-reachable-through-unvisited-transitive1
                                 (x ,(hq x)) (y ,(hq a)) (z ,(hq (car scc)))
                                 (visited ,(hq preorder))))))))

  (local (defthmd not-scc-in-preorder-lemma
           (implies (and (member a scc)
                         (graph-reachable-through-unvisited-p x a preorder)
                         (tarjan-preorder-member-cond x preorder new-preorder)
                         (scc-in-preorder-p scc new-preorder))
                    (graph-reachable-through-unvisited-p x (car scc) preorder))
           :hints ((use-termhint (not-scc-in-preorder-lemma-hint x a preorder new-preorder scc)))))

  (defthmd not-scc-in-preorder-p-when-member-in-common-with-preorder
    (implies (and (member x scc)
                  (member x preorder))
             (not (scc-in-preorder-p scc preorder)))
    :hints (("goal" :use ((:instance scc-in-preorder-p-necc
                           (x x) (y x)))
             :expand ((graph-reachable-through-unvisited-p x x preorder)
                      (intersectp-equal
                       (graph-reachable-through-unvisited-p-witness x x preorder)
                       preorder))
             :in-theory (e/d (tarjan-preorder-member-cond-necc)
                             (scc-in-preorder-p-necc)))))

  (defthm not-scc-in-new-preorder-when-reachable
    (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                  (member a scc)
                  (graph-reachable-through-unvisited-p x a preorder))
             (not (scc-in-preorder-p scc new-preorder)))
    :hints (("goal" :use ((:instance scc-in-preorder-p-necc
                           (x a) (y a) (preorder new-preorder)))
             :expand ((graph-reachable-through-unvisited-p a a new-preorder)
                      (intersectp-equal
                       (graph-reachable-through-unvisited-p-witness a a new-preorder)
                       new-preorder))
             :in-theory (e/d (tarjan-preorder-member-cond-necc)
                             (scc-in-preorder-p-necc)))))

  (local (defun not-scc-in-preorder-p-preserved-by-extension-hint (x preorder new-preorder scc)
           ;; We assume (scc-in-preorder-p scc new-preorder) and need to show
           ;; it's an scc in the old preorder.
           (b* (((when (graph-reachable-through-unvisited-p x (car scc) preorder))
                 `'(:use ((:instance not-scc-in-new-preorder-when-reachable
                           (a (car scc))))))
                ((mv a b) (scc-in-preorder-p-witness scc preorder))
                ;; We have (member a scc), and need to show:
                ;; (iff (member b scc) (and (reaches a b) (reaches b a)))
                ;; If b is a member, then they reach each other (two instances of lemma above).
                ((when (member b scc))
                 `'(:use ((:instance not-scc-in-preorder-p-preserved-by-extension-lemma1
                           (a ,(hq a)) (b ,(hq b)))
                          (:instance not-scc-in-preorder-p-preserved-by-extension-lemma1
                           (b ,(hq a)) (a ,(hq b))))))
                ;; If b is not a member, then if a->b and b->a in the old
                ;; preorder, will prove that they do in the new preorder via
                ;; reachable-through-unvisited-by-member-cond-2.
                ((unless (graph-reachable-through-unvisited-p b a new-preorder))
                 ;; need to know (not (graph-reachable-through-unvisited-p x b preorder))
                 ;; BOZO this is much the same process as below -- prove a lemma instead
                 (b* (((unless (graph-reachable-through-unvisited-p x a preorder))
                       ;; reachability is preserved by reachable-through-unvisited-by-member-cond-2.
                       `'(:use ((:instance reachable-through-unvisited-by-member-cond-2
                                 (z ,(hq b)) (y ,(hq a)))))))
                 `'(:use ((:instance not-scc-in-preorder-lemma
                           (a ,(hq a)))))))
                ((unless (graph-reachable-through-unvisited-p a b new-preorder))
                 (b* (((unless (graph-reachable-through-unvisited-p x b preorder))
                       ;; reachability is preserved by reachable-through-unvisited-by-member-cond-2.
                       `'(:use ((:instance reachable-through-unvisited-by-member-cond-2
                                 (z ,(hq a)) (y ,(hq b))))))
                      ;; otherwise, x then reaches a ...
                      ((unless (graph-reachable-through-unvisited-p x a preorder))
                       `'(:use ((:instance graph-reachable-through-unvisited-transitive1
                                 (x ,(hq x)) (y ,(hq b)) (z ,(hq a))
                                 (visited ,(hq preorder)))))))
                   ;; which means x reaches (car scc).
                   `'(:use ((:instance not-scc-in-preorder-lemma
                             (a ,(hq a))))))))
             ;; Now we can disprove (scc-in-preorder-p scc new-preorder).
             `'(:use ((:instance scc-in-preorder-p-necc
                       (preorder new-preorder)
                       (x ,(hq a)) (y ,(hq b))))))))

  (local (in-theory (disable NOT-GRAPH-REACHABLE-THROUGH-UNVISITED-P-WHEN-MEMBER-LAST
                             NOT-GRAPH-REACHABLE-THROUGH-UNVISITED-P-WHEN-MEMBER-first
                             ;; reachable-through-unvisited-by-member-cond-1
                             tarjan-preorder-member-cond-necc)))


  (defthm not-scc-in-preorder-p-preserved-by-extension
    ;; ->: If a, b are members of scc, show that a reaches b in new-preorder:
    ;; Get the path from a to b in the
    (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                  (not (scc-in-preorder-p scc preorder)))
             (not (scc-in-preorder-p scc new-preorder)))
    :hints (("goal" :expand ((scc-in-preorder-p scc preorder))
             :in-theory (disable scc-in-preorder-p-necc
                                 graph-reachable-through-unvisited-transitive1
                                 graph-reachable-through-unvisited-transitive2
                                 not-scc-in-new-preorder-when-reachable)
             :do-not-induct t)
            (and stable-under-simplificationp
                 (use-termhint (not-scc-in-preorder-p-preserved-by-extension-hint x preorder new-preorder scc))))
    :otf-flg t)


  (defthm scc-in-preorder-p-of-extension-iff-previous
    (implies (and (tarjan-preorder-member-cond x preorder new-preorder)
                  (not (graph-reachable-through-unvisited-p x (car scc) preorder)))
             (iff (scc-in-preorder-p scc new-preorder)
                  (scc-in-preorder-p scc preorder))))

  (local (defun graph-reachable-through-unvisited-if-not-blocked-by-reachable-hint (a b x preorder)
           (b* ((a-b (graph-reachable-through-unvisited-p-witness a b preorder))
                (new-preorder (append preorder (list x)))
                ((unless (intersectp a-b new-preorder))
                 `'(:use ((:instance graph-reachable-through-unvisited-p-suff
                           (x ,(hq a)) (y ,(hq b)) (visited ,(hq new-preorder))
                           (path ,(hq a-b)))))))
             `'(:use ((:instance graph-reachable-through-unvisited-p-suff
                       (x ,(hq a)) (y ,(hq x)) (visited ,(hq preorder))
                       (path ,(hq (prefix-path-to x a-b)))))))))


  (defthmd graph-reachable-through-unvisited-if-not-blocked-by-reachable
    (implies (and (graph-reachable-through-unvisited-p a b preorder)
                  (not (graph-reachable-through-unvisited-p a x preorder)))
             (graph-reachable-through-unvisited-p a b (append preorder (list x))))
    :hints (("goal" :expand ((graph-reachable-through-unvisited-p a b preorder))
             :in-theory (disable graph-reachable-through-unvisited-p-suff)
             :do-not-induct t)
            (use-termhint (graph-reachable-through-unvisited-if-not-blocked-by-reachable-hint
                           a b x preorder)))
    :otf-flg t)

  (local (defun graph-reachable-through-unvisited-if-not-blocked-by-reaching-hint (a b x preorder)
           (b* ((a-b (graph-reachable-through-unvisited-p-witness a b preorder))
                (new-preorder (append preorder (list x)))
                ((unless (intersectp a-b new-preorder))
                 `'(:use ((:instance graph-reachable-through-unvisited-p-suff
                           (x ,(hq a)) (y ,(hq b)) (visited ,(hq new-preorder))
                           (path ,(hq a-b)))))))
             `'(:use ((:instance graph-reachable-through-unvisited-p-suff
                       (x ,(hq x)) (y ,(hq b)) (visited ,(hq preorder))
                       (path ,(hq (member x a-b)))))))))


  (defthmd graph-reachable-through-unvisited-if-not-blocked-by-reaching
    (implies (and (graph-reachable-through-unvisited-p a b preorder)
                  (not (graph-reachable-through-unvisited-p x b preorder)))
             (graph-reachable-through-unvisited-p a b (append preorder (list x))))
    :hints (("goal" :expand ((graph-reachable-through-unvisited-p a b preorder))
             :in-theory (disable graph-reachable-through-unvisited-p-suff)
             :do-not-induct t)
            (use-termhint (graph-reachable-through-unvisited-if-not-blocked-by-reaching-hint
                           a b x preorder)))
    :otf-flg t)

  (local (defun not-scc-in-preorder-p-preserved-by-add-to-preorder-hint (x scc preorder)
           (declare (xargs :normalize nil))
           (b* ((new-preorder (append preorder (list x)))
                ((when (member x scc))
                 `(:use ((:instance not-scc-in-preorder-p-when-member-in-common-with-preorder
                          (preorder ,(hq new-preorder))))))
                ((mv a b) (scc-in-preorder-p-witness scc preorder))
                ((when (let ((x a) (y b))
                           (implies (member x scc)
                                    (iff (member y scc)
                                         (and (graph-reachable-through-unvisited-p x y preorder)
                                              (graph-reachable-through-unvisited-p y x preorder))))))
                 `(:use ((:instance scc-in-preorder-p))))
                ;; ((termhint-seq ))
                ((when (member b scc))
                 `(:in-theory (enable scc-in-preorder-p-necc)))
                ((termhint-seq `(:use ((:instance scc-in-preorder-p-necc
                                         (x ,(hq a)) (y ,(hq b)) (preorder ,(hq new-preorder)))))))
                ((unless (graph-reachable-through-unvisited-p (car scc) a preorder))
                 `(:use ((:instance scc-in-preorder-p-necc
                           (x ,(hq (car scc))) (y ,(hq a)) (preorder ,(hq new-preorder))))))
                ((unless (graph-reachable-through-unvisited-p a b new-preorder))
                 (b* (((unless (graph-reachable-through-unvisited-p a x preorder))
                       `(:use ((:instance graph-reachable-through-unvisited-if-not-blocked-by-reachable
                                 (a ,(hq a)) (b ,(hq b)))))))
                   ;; transitivity
                   nil))
                ;; b can't reach a
                ((unless (graph-reachable-through-unvisited-p b x preorder))
                 `(:use ((:instance graph-reachable-through-unvisited-if-not-blocked-by-reachable
                           (a ,(hq b)) (b ,(hq a)))))))
             ;; transitivity
             nil)))


  ;;               ;; ((mv a b) (scc-in-preorder-p-witness scc preorder))
  ;;               ;; ((unless (member b preorder))
  ;;               ;;  ;; do we have to do anything?
  ;;               ;;  nil)

  (defthm not-scc-in-preorder-p-preserved-by-add-to-preorder-when-new-node-not-reachable
    (implies (and (not (scc-in-preorder-p scc preorder))
                  (not (graph-reachable-through-unvisited-p (car scc) x preorder)))
             (not (scc-in-preorder-p scc (append preorder (list x)))))
    :hints (("goal" ; :Expand ((scc-in-preorder-p scc preorder))
             :in-theory (disable scc-in-preorder-p-necc)
             :do-not-induct t)
            (use-termhint (not-scc-in-preorder-p-preserved-by-add-to-preorder-hint x scc preorder)))
    :otf-flg t)
  )



(define scc-reachable-from-node (scc node stack preorder)
  :verify-guards nil
  (and (consp scc)
       (graph-reachable-through-unvisited-p node (car scc) preorder)
       (not (tarjan-node-reaches-stack (car scc) stack preorder))))

(define scc-reachable-from-node-list (scc nodes stack preorder)
  :verify-guards nil
  (and (consp scc)
       (graph-reachable-through-unvisited-for-some-x nodes (car scc) preorder)
       (not (tarjan-node-reaches-stack (car scc) stack preorder))))


(defsection tarjan-sccs-produces-reachable-sccs-cond
  (defun-sk tarjan-sccs-produces-reachable-sccs-cond (x stack preorder sccs)
    (forall scc
            (implies (member scc sccs)
                     (and (consp scc)
                          (scc-in-preorder-p scc preorder)
                          (graph-reachable-through-unvisited-p x (car scc) preorder)
                          (not (tarjan-node-reaches-stack (car scc) stack preorder)))))
    :rewrite :direct)
  (in-theory (disable tarjan-sccs-produces-reachable-sccs-cond))

  (fty::deffixequiv tarjan-sccs-produces-reachable-sccs-cond
    :args ((preorder true-listp)
           (stack true-listp)
           (sccs true-listp))
    :hints (("goal" :cases ((tarjan-sccs-produces-reachable-sccs-cond x stack preorder sccs)))
            (and stable-under-simplificationp
                 (let ((pos-lit (assoc 'tarjan-sccs-produces-reachable-sccs-cond clause))
                       (neg-lit (cadr (assoc 'not clause))))
                   `(:expand (,pos-lit)
                     :use ((:instance tarjan-sccs-produces-reachable-sccs-cond-necc
                            (x ,(nth 1 neg-lit))
                            (stack ,(nth 2 neg-lit))
                            (preorder ,(nth 3 neg-lit))
                            (sccs ,(nth 4 neg-lit))
                            (scc (tarjan-sccs-produces-reachable-sccs-cond-witness . ,(cdr pos-lit))))))))))

  (defthm tarjan-sccs-produces-reachable-sccs-cond-when-in-preorder
    (implies (member x preorder)
             (tarjan-sccs-produces-reachable-sccs-cond x stack preorder nil))
    :hints (("goal" :expand ((tarjan-sccs-produces-reachable-sccs-cond x stack preorder nil)))))

  (defthm tarjan-sccs-produces-reachable-sccs-cond-of-cons
    (iff (tarjan-sccs-produces-reachable-sccs-cond x stack preorder (cons scc sccs))
         (and (consp scc)
              (scc-in-preorder-p scc preorder)
              (graph-reachable-through-unvisited-p x (car scc) preorder)
              (not (tarjan-node-reaches-stack (car scc) stack preorder))
              (tarjan-sccs-produces-reachable-sccs-cond x stack preorder sccs)))
    :hints ((and stable-under-simplificationp
                 (let ((pos-lit (assoc 'tarjan-sccs-produces-reachable-sccs-cond clause))
                       (neg-lit (cadr (assoc 'not clause))))
                   `(:expand (,pos-lit)
                     :use ((:instance tarjan-sccs-produces-reachable-sccs-cond-necc
                            (x ,(nth 1 neg-lit))
                            (stack ,(nth 2 neg-lit))
                            (preorder ,(nth 3 neg-lit))
                            (sccs ,(nth 4 neg-lit))
                            (scc (tarjan-sccs-produces-reachable-sccs-cond-witness . ,(cdr pos-lit))))))))))


)

  ;; (local (defun tarjan-sccs-produces-reachable-sccs-cond-of-extended-stack-lemma-hint
  ;;          (x scc stack preorder new-stack new-preorder sccs)
  ;;          (b* (((unless (and (consp scc)
  ;;                             (scc-in-preorder-p scc new-preorder)
  ;;                             (not (tarjan-node-reaches-stack (car scc) new-stack new-preorder))
  ;;                             (graph-reachable-through-unvisited-p x (car scc) new-preorder)))
  ;;                '(:use ((:instance tarjan-sccs-produces-reachable-sccs-cond-necc))))
  ;;               ((when (graph-reachable-through-unvisited-p x (car scc) preorder))

  ;;               ((unless (scc-in-preorder-p scc preorder))
  ;;                '(:use scc-in-preorder-p-of-extension-iff-previous))



  ;; (defthm tarjan-sccs-produces-reachable-sccs-cond-of-extended-stack-lemma
  ;;   (implies (and (tarjan-sccs-produces-reachable-sccs-cond x new-stack new-preorder sccs)
  ;;                 (tarjan-preorder-member-cond x preorder new-preorder)
  ;;                 (tarjan-stack-member-cond x stack preorder new-stack)
  ;;                 (subsetp stack preorder))
  ;;            (implies (member scc sccs)
  ;;                     (and (consp scc)
  ;;                          (scc-in-preorder-p scc preorder)
  ;;                          (graph-reachable-through-unvisited-p x (car scc) preorder)
  ;;                          (not (tarjan-node-reaches-stack (car scc) stack preorder)))))
  ;;   :hints(("Goal" :in-theory (disable tarjan-sccs-produces-reachable-sccs-cond-necc)





  ;; (defthm tarjan-sccs-produces-reachable-sccs-cond-of-extended-stack
  ;;   (implies (and (tarjan-sccs-produces-reachable-sccs-cond x new-stack new-preorder sccs)
  ;;                 (tarjan-preorder-member-cond x preorder new-preorder)
  ;;                 (tarjan-stack-member-cond x stack preorder new-stack)
  ;;                 (subsetp stack preorder))
  ;;            (tarjan-sccs-produces-reachable-sccs-cond x stack preorder sccs))
  ;;   :hints (("goal" :expand ((tarjan-sccs-produces-reachable-sccs-cond x stack preorder sccs))
  ;;            :use ((:instance tarjan-sccs-produces-reachable-sccs-cond-necc
  ;;                   (stack new-stack) (preorder new-preorder)
  ;;                   (scc (tarjan-sccs-produces-reachable-sccs-cond-witness x stack preorder sccs))))))))
  ;;           (and stable-under-simplificationp
  ;;                (let ((witness (find-call-lst
  ;;                                'tarjan-sccs-produces-reachable-sccs-cond-witness
  ;;                                clause)))
  ;;                  (and witness
  ;;                       `(:clause-processor
  ;;                         (simple-generalize-cp
  ;;                          clause '((,witness . witness)))))))
  ;;           (and stable-under-simplificationp
  ;;                '(:use ((:instance tarjan-sccs-produces-reachable-sccs-cond-necc
  ;;                         (stack new-stack) (preorder new-preorder)
  ;;                         (scc witness)))
  ;;                  :in-theory (disable tarjan-sccs-produces-reachable-sccs-cond-necc))))))


(defsection tarjan-sccs-list-produces-reachable-sccs-cond
  (defun-sk tarjan-sccs-list-produces-reachable-sccs-cond (x stack preorder sccs)
    (forall scc
            (implies (member scc sccs)
                     (and (consp scc)
                          (scc-in-preorder-p scc preorder)
                          (graph-reachable-through-unvisited-for-some-x x (car scc) preorder)
                          (not (tarjan-node-reaches-stack (car scc) stack preorder)))))
    :rewrite :direct)

  (in-theory (disable tarjan-sccs-list-produces-reachable-sccs-cond))

  (fty::deffixequiv tarjan-sccs-list-produces-reachable-sccs-cond
    :args ((preorder true-listp)
           (stack true-listp)
           (sccs true-listp))
    :hints (("goal" :cases ((tarjan-sccs-list-produces-reachable-sccs-cond x stack preorder sccs)))
            (and stable-under-simplificationp
                 (let ((pos-lit (assoc 'tarjan-sccs-list-produces-reachable-sccs-cond clause))
                       (neg-lit (cadr (assoc 'not clause))))
                   `(:expand (,pos-lit)
                     :use ((:instance tarjan-sccs-list-produces-reachable-sccs-cond-necc
                            (x ,(nth 1 neg-lit))
                            (stack ,(nth 2 neg-lit))
                            (preorder ,(nth 3 neg-lit))
                            (sccs ,(nth 4 neg-lit))
                            (scc (tarjan-sccs-list-produces-reachable-sccs-cond-witness . ,(cdr pos-lit))))))))))

  (defthm tarjan-sccs-list-produces-reachable-sccs-cond-of-empty
    (tarjan-sccs-list-produces-reachable-sccs-cond x stack preorder nil)
    :hints(("Goal" :expand ((tarjan-sccs-list-produces-reachable-sccs-cond x stack preorder nil)))))

  (defthm tarjan-sccs-list-produces-reachable-sccs-cond-of-append
    (iff (tarjan-sccs-list-produces-reachable-sccs-cond x stack preorder (append a b))
         (and (tarjan-sccs-list-produces-reachable-sccs-cond x stack preorder a)
              (tarjan-sccs-list-produces-reachable-sccs-cond x stack preorder b)))
    :hints((and stable-under-simplificationp
                `(:expand (,(assoc 'tarjan-sccs-list-produces-reachable-sccs-cond clause))))))

  (defthm tarjan-sccs-list-produces-reachable-sccs-cond-car-cdr
    (implies (and (consp x)
                  (not (tarjan-sccs-list-produces-reachable-sccs-cond x stack preorder sccs)))
             (and (not (tarjan-sccs-produces-reachable-sccs-cond (car x) stack preorder sccs))
                  (not (tarjan-sccs-list-produces-reachable-sccs-cond (cdr x) stack preorder sccs))))
    :hints(("goal" :expand ((tarjan-sccs-list-produces-reachable-sccs-cond x stack preorder sccs)
                            (graph-reachable-through-unvisited-for-some-x
                             x
                             (car (tarjan-sccs-list-produces-reachable-sccs-cond-witness
                                   x stack preorder sccs))
                             preorder))
            :use ((:instance tarjan-sccs-produces-reachable-sccs-cond-necc
                   (x (car x))
                   (scc (tarjan-sccs-list-produces-reachable-sccs-cond-witness x stack preorder sccs)))
                  (:instance tarjan-sccs-list-produces-reachable-sccs-cond-necc
                   (x (cdr x))
                   (scc (tarjan-sccs-list-produces-reachable-sccs-cond-witness x stack preorder sccs))))
            :in-theory (disable tarjan-sccs-list-produces-reachable-sccs-cond-necc
                                tarjan-sccs-produces-reachable-sccs-cond-necc))))






  ;; (local (defthm reachable-through-unvisited-for-some-x-by-member-cond-2-rw
  ;;          (implies (and (bind-free '((preorder . preorder)
  ;;                                     (x . (car x))) (x preorder))
  ;;                        (tarjan-preorder-member-cond x preorder new-preorder)
  ;;                        (not (graph-reachable-through-unvisited-p x y preorder))
  ;;                        (graph-reachable-through-unvisited-for-some-x z y preorder))
  ;;                   (graph-reachable-through-unvisited-for-some-x z y new-preorder))
  ;;          :hints(("Goal" :in-theory (enable graph-reachable-through-unvisited-for-some-x)))
  ;;          :rule-classes ((:rewrite :match-free :all))))



  (defthm tarjan-sccs-list-produces-reachable-sccs-cond-of-extended-stack
    (implies (and (tarjan-sccs-list-produces-reachable-sccs-cond x new-stack new-preorder sccs)
                  (tarjan-preorder-member-cond y preorder new-preorder)
                  (tarjan-stack-member-cond y stack preorder new-stack)
                  (subsetp stack preorder))
             (tarjan-sccs-list-produces-reachable-sccs-cond x stack preorder sccs))
    :hints (("goal" :expand ((tarjan-sccs-list-produces-reachable-sccs-cond x stack preorder sccs))
             :use ((:instance tarjan-sccs-list-produces-reachable-sccs-cond-necc
                    (stack new-stack) (preorder new-preorder)
                    (scc (tarjan-sccs-list-produces-reachable-sccs-cond-witness
                          x stack preorder sccs))))
             :in-theory (disable tarjan-sccs-list-produces-reachable-sccs-cond-necc)
             :do-not-induct t))
    :otf-flg t)


  (defthm tarjan-sccs-list-produces-reachable-sccs-when-cdr
    (implies (and (consp x)
                  (tarjan-sccs-list-produces-reachable-sccs-cond (cdr x) stack preorder sccs))
             (tarjan-sccs-list-produces-reachable-sccs-cond x stack preorder sccs)))





  ;; (local (defun tarjan-sccs-produces-reachable-sccs-cond-by-successors-hint
  ;;          (x stack preorder sccs)
  ;;          (b* ((scc (tarjan-sccs-produces-reachable-sccs-cond-witness
  ;;                     x stack preorder sccs))
  ;;               (?succs (graph-node-succs x))
  ;;               (?new-stack (cons x stack))
  ;;               (?new-preorder (append preorder (list x)))
  ;;               ((when (tarjan-node-reaches-stack (car scc) stack preorder))
  ;;                `'(:use ((:instance tarjan-node-reaches-stack-of-add-x-yes
  ;;                          (y ,(hq (car scc)))))))
  ;;               ((when (graph-reachable-through-unvisited-p (car scc) x preorder))
  ;;                ;; node reaches stack composition
  ;;                `'(:use ((:instance tarjan-node-reaches-stack-when-reaches-other-node
  ;;                          (x ,(hq (car scc))) (y ,(hq x))))))
  ;;            nil)))


  (defthm tarjan-sccs-produces-reachable-sccs-cond-by-successors
    (implies (and (tarjan-sccs-list-produces-reachable-sccs-cond
                   (graph-node-succs x)
                   (cons x stack)
                   (append preorder (list x))
                   sccs)
                  (not (member x preorder))
                  ;; (tarjan-node-reaches-stack x stack preorder)
                  (subsetp stack preorder)) ;; ?
             (tarjan-sccs-produces-reachable-sccs-cond
              x stack preorder sccs))
    :hints (("Goal" :expand ((tarjan-sccs-produces-reachable-sccs-cond
                              x stack preorder sccs))
             :use ((:instance tarjan-sccs-list-produces-reachable-sccs-cond-necc
                    (x (graph-node-succs x))
                    (stack (cons x stack))
                    (preorder (append preorder (list x)))
                    (scc (tarjan-sccs-produces-reachable-sccs-cond-witness
                          x stack preorder sccs)))
                   ;; (:instance tarjan-node-reaches-stack-when-reaches-other-node
                   ;;  (x (car (tarjan-sccs-produces-reachable-sccs-cond-witness
                   ;;        x stack preorder sccs)))
                   ;;  (y x))
                   (:instance tarjan-node-reaches-stack-sufficient
                    (some-node x)
                    (stack (cons x stack))
                    (node (car (tarjan-sccs-produces-reachable-sccs-cond-witness
                          x stack preorder sccs)))
                    (preorder (append preorder (list x))))
                   (:instance graph-reachable-through-unvisited-but-last-of-append-last
                    (y x)
                    (x (car (tarjan-sccs-produces-reachable-sccs-cond-witness
                          x stack preorder sccs))))
                   )
             :in-theory (disable tarjan-sccs-list-produces-reachable-sccs-cond-necc
                                 graph-reachable-through-unvisited-but-last-of-append-last)
             :do-not-induct t)
            ;; (use-termhint (tarjan-sccs-produces-reachable-sccs-cond-by-successors-hint
            ;;                x stack preorder sccs))
            )
    :otf-flg t)

  ;; (defthm tarjan-sccs-produces-reachable-sccs-cond-by-successors-when-x-not-reaches-stack
  ;;   (implies (and (tarjan-sccs-list-produces-reachable-sccs-cond
  ;;                  (graph-node-succs x)
  ;;                  (cons x stack)
  ;;                  (append preorder (list x))
  ;;                  sccs)
  ;;                 (not (member x preorder))
  ;;                 (not (tarjan-node-reaches-stack x stack preorder))
  ;;                 (subsetp stack preorder)) ;; ?
  ;;            (tarjan-sccs-produces-reachable-sccs-cond
  ;;             x stack preorder sccs))
  ;;   :hints (("Goal" :expand ((tarjan-sccs-produces-reachable-sccs-cond
  ;;                             x stack preorder sccs))
  ;;            :use ((:instance tarjan-sccs-list-produces-reachable-sccs-cond-necc
  ;;                   (x (graph-node-succs x))
  ;;                   (stack (cons x stack))
  ;;                   (preorder (append preorder (list x)))
  ;;                   (scc (tarjan-sccs-produces-reachable-sccs-cond-witness
  ;;                         x stack preorder sccs)))
  ;;                  ;; (:instance tarjan-node-reaches-stack-when-reaches-other-node
  ;;                  ;;  (x (car (tarjan-sccs-produces-reachable-sccs-cond-witness
  ;;                  ;;        x stack preorder sccs)))
  ;;                  ;;  (y x))
  ;;                  )
  ;;            :in-theory (disable tarjan-sccs-list-produces-reachable-sccs-cond-necc)
  ;;            :do-not-induct t)
  ;;           ;; (use-termhint (tarjan-sccs-produces-reachable-sccs-cond-by-successors-hint
  ;;           ;;                x stack preorder sccs))
  ;;           )
  ;;   :otf-flg t)

  )

(defsection new-part-of-stack-is-scc
  (local (defthm not-member-of-suffix
           (implies (and (suffixp x y)
                         (not (member k y)))
                    (not (member k x)))
           :hints(("Goal" :in-theory (enable suffixp)))))

  (local (defthm car-not-member-of-suffix
           (implies (and (suffixp x (cdr y))
                         (no-duplicatesp y))
                    (not (member (car y) x)))
           :hints(("Goal" :in-theory (enable suffixp no-duplicatesp)))))

  (local (defthm len-of-suffix
           (implies (suffixp a b)
                    (<= (len a) (len b)))
           :hints(("Goal" :in-theory (enable suffixp)))
           :rule-classes (:rewrite :linear)))

  (defthm take-difference-with-duplicate-free-suffix
    (implies (and (suffixp x y)
                  (no-duplicatesp y))
             (iff (member k (take (+ (- (len x)) (len y)) y))
                  (and (member k y)
                       (not (member k x)))))
    :hints(("Goal" :in-theory (enable suffixp no-duplicatesp))))

  (defthm take-difference-is-set-difference
    (implies (and (suffixp x y)
                  (no-duplicatesp y))
             (set-equiv (take (+ (- (len x)) (len y)) y)
                        (set-difference$ y x)))
    :hints ((set-reasoning)))

  (local (defthm take-difference-is-set-difference-list-fix
           (implies (and (suffixp (list-fix x) y)
                         (no-duplicatesp y))
                    (set-equiv (take (+ (- (len x)) (len y)) y)
                               (set-difference$ y x)))
           :hints (("goal" :use ((:instance take-difference-is-set-difference
                                  (x (list-fix x))))
                    :in-theory (disable take-difference-is-set-difference)))))

  (local (defthm take-difference-is-set-difference-list-fix-commute
           (implies (and (suffixp (list-fix x) y)
                         (no-duplicatesp y))
                    (set-equiv (take (+ (len y) (- (len x))) y)
                               (set-difference$ y x)))
           :hints (("goal" :use ((:instance take-difference-is-set-difference
                                  (x (list-fix x))))
                    :in-theory (disable take-difference-is-set-difference)))))


  (local (defthm suffixp-of-cons
           (implies (suffixp (cons x y) z)
                    (suffixp y z))
           :hints(("Goal" :in-theory (enable suffixp)))))

  (local (defthmd last-is-a-member
           (implies (and (equal y (car (last x)))
                         (consp x))
                    (member y x))))

  (local (defthm consp-when-len-<-0
           (implies (< 0 (len x))
                    (consp x))))

  (local (defthm last-not-member-of-butlast
           (implies (and (no-duplicatesp x)
                         (equal y (car (last x))))
                    (not (member y (butlast x 1))))
           :hints(("Goal" :in-theory (enable no-duplicatesp
                                             last-is-a-member
                                             last)))))

  (local (defthm not-tarjan-node-reaches-stack-of-cons-implies-not-reachable
           (implies (not (tarjan-node-reaches-stack y (cons x stack) (append preorder (list x))))
                    (not (graph-reachable-through-unvisited-p y x preorder)))
           :hints (("goal"
                    :use ((:instance graph-reachable-through-unvisited-implies-canonical-witness
                           (x y) (y x))
                          (:instance tarjan-node-reaches-stack-by-path
                           (node y) (stack (cons x stack)) (preorder (append preorder (list x)))
                           (path (graph-reachable-through-unvisited-canonical-witness y x preorder))))))))

  ;; (local (defthm reachable-through-succs-when-reachable


  (local (defun stack-nodes-reach-x-hints (x y stack preorder)
           (declare (xargs :normalize nil))
           (b* (((termhint-seq ''(:do-not-induct t)))
                (y-stack-node (tarjan-lowlink-node y (cons x stack)
                                                   (append preorder (list x))))
                ((termhint-seq
                  `(:use ((:instance tarjan-lowlink-node-exists-when-node-reaches-stack
                           (node y) (stack (cons x stack)) (preorder (append preorder (list x)))))
                    :in-theory (disable tarjan-lowlink-node-exists-when-node-reaches-stack
                                        graph-reachable-through-unvisited-but-last-when-reachable-from-reachable))))
                ((when (or (equal y-stack-node x)
                           (not (member y-stack-node stack))))
                 nil)
                ((unless (graph-reachable-through-unvisited-but-last-p
                          x y-stack-node preorder))
                 `(:use ((:instance graph-reachable-through-unvisited-but-last-when-reachable-from-reachable
                           (x x) (y y) (z ,(hq y-stack-node)))))))
             `(:use ((:instance tarjan-node-reaches-stack-sufficient
                       (some-node ,(hq y-stack-node))
                       (node x)))))))


  (local (defthm stack-nodes-reach-x
           ;; case where sccx and sccy are both in the scc,
           ;; therefore both reachable from (succs x) and reach back to the stack+x
           (implies (and (not (tarjan-node-reaches-stack x stack preorder))
                         (graph-reachable-through-unvisited-for-some-x
                          (graph-node-succs x) y (append preorder (list x)))
                         (not (member x preorder))
                         (tarjan-node-reaches-stack y (cons x stack) (append preorder (list x))))
                    (graph-reachable-through-unvisited-p y x preorder))
           :hints ((use-termhint (stack-nodes-reach-x-hints x y stack preorder)))
           :rule-classes nil))

  ;; (local (defun take-difference-of-new-stack-is-scc-lemma-case1-hint (x stack preorder new-stack sccx sccy)
  ;;          (b* ((

  (local (defthm take-difference-of-new-stack-is-scc-lemma-case1
           ;; When sccx and sccy are both members, they are both reachable from
           ;; (succs x) and therefore from x, and also both reach x, since they
           ;; reach (cons x stack) but not stack (or else x would reach stack
           ;; through them.  Therefore they are both in an SCC from x.
           (implies (and (not (tarjan-node-reaches-stack x stack preorder))
                         (tarjan-stack-member-cond-list (graph-node-succs x)
                                                        (cons x stack)
                                                        (append preorder (list x))
                                                        new-stack)
                         (not (member x preorder)))
                    (implies (and (member sccx new-stack) (not (member sccx stack))
                                  (member sccy new-stack) (not (member sccy stack)))
                             (graph-reachable-through-unvisited-p sccx sccy preorder)))
           :hints (("goal" :use ((:instance stack-nodes-reach-x
                                  (y sccx)))))
           :otf-flg t
           :rule-classes nil))

  (local (defun take-difference-of-new-stack-is-scc-lemma-case2-hint (x stack preorder new-stack sccx sccy)
           (declare (ignorable sccx new-stack))
           (b* (((when (tarjan-node-reaches-stack sccy (cons x stack) (append preorder (list x))))
                 nil)
                ((when (graph-reachable-through-unvisited-p sccy sccx (append preorder (list x))))
                 `(:use ((:instance tarjan-node-reaches-stack-when-reaches-other-node
                           (x sccy) (y sccx) (preorder (append preorder (list x)))
                           (stack (cons x stack))))
                    :in-theory (disable tarjan-node-reaches-stack-when-reaches-other-node)))
                ;; ((when (graph-reachable-through-unvisited-but-last-p sccy x (append preorder (list x))))
                ;;  `(:expand (,(hq (tarjan-node-reaches-stack sccy (cons x stack) (append preorder (list x)))))))
                )
             `(:use ((:instance graph-reachable-through-unvisited-if-not-blocked-by-reachable
                       (a sccy) (b sccx)))))))



  (local (defthm take-difference-of-new-stack-is-scc-lemma-case2
           ;; When sccx is a member but y is not, then either sccy is in the
           ;; original stack, or it is not reachable from (successors of) x, or
           ;; it does not reach (cons x stack).
           ;; If sccy is in the original stack, then it also can't be reached from x.
           ;; If it can't be reached from x, then since sccx can be reached from x,
           ;;    sccx can't reach sccy.
           ;; If it does not reach (cons x stack), then since we know sccx does reach the stack,
           ;;    then sccy can't reach sccx (in the extende preorder).
           ;;    We also know that sccy can't reach x.  So that means x can't block the path from
           ;;    sccy to sccx, which means it can't be reached in the original preorder.
           (implies (and (not (tarjan-node-reaches-stack x stack preorder))
                         (tarjan-stack-member-cond-list (graph-node-succs x)
                                                        (cons x stack)
                                                        (append preorder (list x))
                                                        new-stack)
                         (not (member x preorder))
                         (no-duplicatesp new-stack)
                         (suffixp (list-fix (cons x stack)) new-stack))
                    (implies (and (member sccx new-stack) (not (member sccx stack))
                                  (not (and (member sccy new-stack) (not (member sccy stack))))
                                  (graph-reachable-through-unvisited-p sccx sccy preorder))
                             (not (graph-reachable-through-unvisited-p sccy sccx preorder))))
           :hints (("goal" :do-not-induct t)
                   (use-termhint (take-difference-of-new-stack-is-scc-lemma-case2-hint
                                  x stack preorder new-stack sccx sccy)))
           :otf-flg t
           :rule-classes nil))

  (local (defun take-difference-of-new-stack-is-scc-hints (x stack preorder new-stack)
           (declare (xargs :normalize nil))
           (b* ((scc (take (+ (- (len stack)) (len new-stack)) new-stack))
                ((termhint-seq ``(:expand (,(car (last clause))))))
                ((mv sccx0 sccy0) (scc-in-preorder-p-witness scc preorder))
                ((unless (member sccy0 scc))
                 `(:use ((:instance take-difference-of-new-stack-is-scc-lemma-case2
                           (x ,(hq x)) (sccx ,(hq sccx0)) (sccy ,(hq sccy0))))))
                ((when (graph-reachable-through-unvisited-p sccx0 sccy0 preorder))
                 `(:use ((:instance take-difference-of-new-stack-is-scc-lemma-case1
                           (x ,(hq x)) (sccx ,(hq sccy0)) (sccy ,(hq sccx0)))))))
             `(:use ((:instance take-difference-of-new-stack-is-scc-lemma-case1
                       (x ,(hq x)) (sccx ,(hq sccx0)) (sccy ,(hq sccy0))))))))

  (defthm take-difference-of-new-stack-is-scc
    (implies (and (not (tarjan-node-reaches-stack x stack preorder))
                  (tarjan-stack-member-cond-list (graph-node-succs x)
                                                 (cons x stack)
                                                 (append preorder (list x))
                                            new-stack)
                  (not (member x preorder))
                  (no-duplicatesp new-stack)
                  (suffixp (list-fix (cons x stack)) new-stack))
             (scc-in-preorder-p (take (+ (- (len stack)) (len new-stack)) new-stack)
                                preorder))
    :hints (("goal" :do-not-induct t
             :in-theory (disable take len take-of-len-free member))
            (use-termhint (take-difference-of-new-stack-is-scc-hints x stack preorder new-stack)))
    :otf-flg t))

(defsection tarjan-sccs-produces-reachable-sccs
  (local (defthm tarjan-sccs-list-produces-reachable-sccs-cond-of-extended-stack-rw
           (implies (and (tarjan-sccs-list-produces-reachable-sccs-cond x new-stack new-preorder sccs)
                         (bind-free (case-match x
                                      (('cdr y) `((y . (car ,y))))
                                      (& nil))
                                    (y))
                         (tarjan-preorder-member-cond y preorder new-preorder)
                         (tarjan-stack-member-cond y stack preorder new-stack)
                         (subsetp stack preorder))
                    (tarjan-sccs-list-produces-reachable-sccs-cond x stack preorder sccs))))

  (local (defthmd len-of-suffix
           (implies (suffixp a b)
                    (<= (len a) (len b)))
           :hints(("Goal" :in-theory (enable suffixp)))
           :rule-classes (:rewrite :linear)))

  (defret tarjan-sccs-list-len-of-stack-increases
    (<= (len stack) (len new-stack))
    :hints(("Goal" :use ((:instance len-of-suffix (a (list-fix stack)) (b new-stack)))))
    :rule-classes :linear
    :fn tarjan-sccs-list)

  (local (Defthm len-equal-0
           (equal (equal (len x) 0)
                  (atom x))
           :hints(("Goal" :in-theory (enable len)))))


  (defret tarjan-sccs-list-stack-preserves-consp
    (implies (consp stack)
             (consp new-stack))
    :hints (("goal" :use tarjan-sccs-list-len-of-stack-increases
             :in-theory (e/d () (tarjan-sccs-list-len-of-stack-increases))))
    :fn tarjan-sccs-list)

  (local (defthmd car-not-member-of-duplicate-free-suffix
           (implies (and (suffixp (list-fix (cons a x)) y)
                         (no-duplicatesp y))
                    (not (member (car y) x)))
           :hints(("Goal" :in-theory (enable suffixp no-duplicatesp)))))


  (defthm tarjan-sccs-list-new-stack-car-reachable-from-x
    (implies (and (subsetp stack preorder)
                  (not (member x preorder))
                  (no-duplicatesp stack))
             (GRAPH-REACHABLE-THROUGH-UNVISITED-P
              X
              (CAR (MV-NTH 2
                           (TARJAN-SCCS-LIST (GRAPH-NODE-SUCCS X)
                                             (APPEND PREORDER (LIST X))
                                             (CONS X STACK))))
              PREORDER))
    :hints (("goal" :use ((:instance tarjan-stack-member-cond-list-necc
                           (x (graph-node-succs x))
                           (stack (cons x stack))
                           (preorder (append preorder (list x)))
                           (new-stack (mv-nth 2 (tarjan-sccs-list
                                                 (graph-node-succs x)
                                                 (append preorder (list x))
                                                 (cons x stack))))
                           (y (car (mv-nth 2 (tarjan-sccs-list
                                                 (graph-node-succs x)
                                                 (append preorder (list x))
                                                 (cons x stack))))))
                          (:instance car-not-member-of-duplicate-free-suffix
                           (a x)
                           (x stack)
                           (y (mv-nth 2 (tarjan-sccs-list
                                         (graph-node-succs x)
                                         (append preorder (list x))
                                         (cons x stack))))))
             :in-theory (disable list-fix-of-cons)
             :do-not-induct t))
    :otf-flg t)

  (defthm tarjan-sccs-list-stack-element-does-not-reach-stack
    (implies (and (subsetp stack preorder)
                  (not (member x preorder))
                  (no-duplicatesp stack)
                  (not (tarjan-node-reaches-stack x stack preorder)))
             (not (tarjan-node-reaches-stack
                   (CAR (MV-NTH 2
                                (TARJAN-SCCS-LIST (GRAPH-NODE-SUCCS X)
                                                  (APPEND PREORDER (LIST X))
                                                  (CONS X STACK))))
                   stack preorder)))
    :hints (("goal" :use ((:instance tarjan-node-reaches-stack-when-reaches-other-node
                           (x x)
                           (y (CAR (MV-NTH 2
                                (TARJAN-SCCS-LIST (GRAPH-NODE-SUCCS X)
                                                  (APPEND PREORDER (LIST X))
                                                  (CONS X STACK)))))))
             :in-theory (disable tarjan-node-reaches-stack-when-reaches-other-node)
             :do-not-induct t))
    :otf-flg t)

  (local (in-theory (disable list-fix-of-cons)))

  (std::defret-mutual tarjan-sccs-produces-reachable-sccs
    (defret tarjan-sccs-produces-reachable-sccs-lemma
      (implies (and (subsetp stack preorder)
                    (no-duplicatesp stack))
               (tarjan-sccs-produces-reachable-sccs-cond x stack preorder sccs))
      :hints ('(:expand (<call>)
                :do-not-induct t))
      :fn tarjan-sccs)
    (defret tarjan-sccs-list-produces-reachable-sccs-lemma
      (implies (and (subsetp stack preorder)
                    (no-duplicatesp stack))
               (tarjan-sccs-list-produces-reachable-sccs-cond x stack preorder sccs))
      :hints ('(:expand (<call>)
                :do-not-induct t))
      :fn tarjan-sccs-list)
    :otf-flg t)

  (defret tarjan-sccs-produces-preorder-reachable-sccs
    (implies (and (subsetp stack preorder)
                  (no-duplicatesp stack)
                  (member scc sccs))
             (and (consp scc)
                  (scc-in-preorder-p scc preorder)
                  (graph-reachable-through-unvisited-p x (car scc) preorder)
                  (not (tarjan-node-reaches-stack (car scc) stack preorder))))
    :hints (("goal" :use tarjan-sccs-produces-reachable-sccs-lemma
             :in-theory (disable tarjan-sccs-produces-reachable-sccs-lemma)))
    :fn tarjan-sccs)

  (defret tarjan-sccs-list-produces-preorder-reachable-sccs
    (implies (and (subsetp stack preorder)
                  (no-duplicatesp stack)
                  (member scc sccs))
             (and (consp scc)
                  (scc-in-preorder-p scc preorder)
                  (graph-reachable-through-unvisited-for-some-x x (car scc) preorder)
                  (not (tarjan-node-reaches-stack (car scc) stack preorder))))
    :hints (("goal" :use tarjan-sccs-list-produces-reachable-sccs-lemma
             :in-theory (disable tarjan-sccs-list-produces-reachable-sccs-lemma)))
    :fn tarjan-sccs-list)
)



;; Now we'll show:
;;  - every reachable node ends up either in the stack or an SCC
;;  - when starting from an empty stack, the final stack is empty
;; therefore:
;;  - every node ends up in an SCC when starting from an empty stack/preorder.

(defsection tarjan-sccs-collects-every-node

  (defund append-lists (x)
    (declare (xargs :guard (true-list-listp x)))
    (if (atom x)
        nil
      (append (car x) (append-lists (cdr x)))))

  (defun-sk tarjan-sccs-collects-every-node-cond (x preorder new-stack sccs)
    (forall y
            (implies (and (graph-reachable-through-unvisited-p x y preorder)
                          (not (member y new-stack)))
                     (member y (append-lists sccs))))
    :rewrite :direct)

  (defun-sk tarjan-sccs-list-collects-every-node-cond (x preorder new-stack sccs)
    (forall y
            (implies (and (graph-reachable-through-unvisited-for-some-x x y preorder)
                          (not (member y new-stack)))
                     (member y (append-lists sccs))))
    :rewrite :direct)

  (in-theory (disable tarjan-sccs-collects-every-node-cond
                      tarjan-sccs-list-collects-every-node-cond))



  (local (defthm suffixp-of-cons
           (implies (suffixp (cons x y) z)
                    (suffixp y z))
           :hints(("Goal" :in-theory (enable suffixp)))))

  (local (defthm take-diff-of-tarjan-sccs-list-is-set-difference-special
           (b* ((new-stack (mv-nth 2 (tarjan-sccs-list nodes preorder (cons x stack)))))
             (implies (and (no-duplicatesp (cons x stack))
                           (subsetp (cons x stack) preorder))
                      (set-equiv (take (+ (- (len stack)) (len new-stack)) new-stack)
                                 (set-difference$ new-stack stack))))
           :hints (("goal" :use ((:instance take-difference-is-set-difference
                                  (x (list-fix stack))
                                  (y (mv-nth 2 (tarjan-sccs-list nodes preorder (cons x stack)))))
                                 (:instance tarjan-sccs-list-extend-stack
                                  (stack (cons x stack)) (x nodes)))
                    :in-theory (disable take-difference-is-set-difference
                                        tarjan-sccs-list-extend-stack)))))




  (local (in-theory (disable list-fix-of-cons)))

  (local (defthm append-lists-of-append
           (equal (append-lists (append a b))
                  (append (append-lists a)
                          (append-lists b)))
           :hints(("Goal" :in-theory (enable append-lists)))))

  (local (defret tarjan-sccs-member-of-stack
           (implies (and (subsetp stack preorder)
                         (no-duplicatesp stack))
                    (iff (member y new-stack)
                         (or (member y stack)
                             (and (graph-reachable-through-unvisited-p x y preorder)
                                  (tarjan-node-reaches-stack y stack preorder)))))
           :hints (("goal" :use ((:instance tarjan-sccs-lowlink-correct))
                    :in-theory (disable tarjan-sccs-lowlink-correct)))
           :fn tarjan-sccs))

  (local (defret tarjan-sccs-member-reachable-through-unvisited
           (implies (and (not (graph-reachable-through-unvisited-p x y preorder))
                         (graph-reachable-through-unvisited-for-some-x z y preorder))
                    (graph-reachable-through-unvisited-for-some-x z y new-preorder))
           :hints (("goal" :use ((:instance tarjan-sccs-preorder-member-cond))
                    :in-theory (disable tarjan-sccs-preorder-member-cond)))
           :fn tarjan-sccs))

  (local (defret tarjan-sccs-list-member-of-stack
           (implies (and (subsetp stack preorder)
                         (no-duplicatesp stack))
                    (iff (member y new-stack)
                         (or (member y stack)
                             (and (graph-reachable-through-unvisited-for-some-x x y preorder)
                                  (tarjan-node-reaches-stack y stack preorder)))))
           :hints (("goal" :use ((:instance tarjan-sccs-list-lowlink-correct))
                    :in-theory (disable tarjan-sccs-list-lowlink-correct)))
           :fn tarjan-sccs-list))

  (defun tarjan-sccs-collects-node-bind-free (fn sccs)
    (case-match sccs
      (('mv-nth ''3 call)
       (case-match call
         ((!fn x preorder &)
          `((new-stack . (mv-nth '2 ,call))
            (x . ,x)
            (preorder . ,preorder)))))))

  (local (defthm TARJAN-SCCS-LIST-COLLECTS-EVERY-NODE-COND-NECC-match-free
           (IMPLIES (and (bind-free
                          (tarjan-sccs-collects-node-bind-free 'tarjan-sccs-list sccs)
                          (new-stack preorder x))
                         (TARJAN-SCCS-LIST-COLLECTS-EVERY-NODE-COND
                          X PREORDER NEW-STACK SCCS))
                    (IMPLIES (AND (GRAPH-REACHABLE-THROUGH-UNVISITED-FOR-SOME-X
                                   X Y PREORDER)
                                  (NOT (MEMBER Y NEW-STACK)))
                             (MEMBER Y (APPEND-LISTS SCCS))))
           :rule-classes ((:rewrite :match-free :all))))

  (local (defthm TARJAN-SCCS-COLLECTS-EVERY-NODE-COND-NECC-match
           (IMPLIES (and (bind-free
                          (tarjan-sccs-collects-node-bind-free 'tarjan-sccs sccs)
                          (new-stack preorder x))
                         (TARJAN-SCCS-COLLECTS-EVERY-NODE-COND
                          X PREORDER NEW-STACK SCCS))
                    (IMPLIES (AND (GRAPH-REACHABLE-THROUGH-UNVISITED-p
                                   X Y PREORDER)
                                  (NOT (MEMBER Y NEW-STACK)))
                             (MEMBER Y (APPEND-LISTS SCCS))))
           :rule-classes ((:rewrite :match-free :all))))

  (std::defret-mutual tarjan-sccs-collects-every-node
    (defret tarjan-sccs-collects-every-node
      (implies (and (subsetp stack preorder)
                    (no-duplicatesp stack))
               (tarjan-sccs-collects-every-node-cond x preorder new-stack sccs))
      :hints ('(:expand (<call>)
                :do-not-induct t)
              (and stable-under-simplificationp
                   `(:expand (,(car (last clause))
                              (:free (a b) (append-lists (cons a b)))))))
      :fn tarjan-sccs)
    (defret tarjan-sccs-list-collects-every-node
      (implies (and (subsetp stack preorder)
                    (no-duplicatesp stack))
               (tarjan-sccs-list-collects-every-node-cond x preorder new-stack sccs))
      :hints ('(:expand (<call>)
                :do-not-induct t)
              (and stable-under-simplificationp
                   `(:expand (,(car (last clause))
                              (:free (y) (graph-reachable-through-unvisited-for-some-x x y preorder))))))
      :fn tarjan-sccs-list)
    :otf-flg t)

  (local (defthm not-member-stack-when-not-reaches
           (implies (not (tarjan-node-reaches-stack y stack preorder))
                    (not (member y stack)))))

  (defret tarjan-sccs-contains-all-non-stack-reaching-nodes
    (implies (and (subsetp stack preorder)
                  (no-duplicatesp stack)
                  (graph-reachable-through-unvisited-p x y preorder)
                  (not (tarjan-node-reaches-stack y stack preorder)))
             (member y (append-lists sccs)))
    :hints (("goal" :use ((:instance tarjan-sccs-collects-every-node))
             :in-theory (disable tarjan-sccs-collects-every-node)))
    :fn tarjan-sccs)

  (defret tarjan-sccs-list-contains-all-non-stack-reaching-nodes
    (implies (and (subsetp stack preorder)
                  (no-duplicatesp stack)
                  (graph-reachable-through-unvisited-for-some-x x y preorder)
                  (not (tarjan-node-reaches-stack y stack preorder)))
             (member y (append-lists sccs)))
    :hints (("goal" :use ((:instance tarjan-sccs-list-collects-every-node))
             :in-theory (disable tarjan-sccs-list-collects-every-node)))
    :fn tarjan-sccs-list))




;; Now we translate back to simpler properties of the top-level call of the
;; algorithm, where stack and preorder are initially empty.

;; First define graph-reachable and graph-reachable-for-some-x without the visited list.


(defsection graph-reachable-p
  (defun-sk graph-reachable-p (x y)
    (exists path
            (and (consp path)
                 (graph-path-p path)
                 (equal x (car path))
                 (equal y (car (last path))))))

  (in-theory (disable graph-reachable-p))

  (defthm graph-reachable-of-successors
    (implies (and (graph-reachable-p x y)
                  (member z (graph-node-succs y)))
             (graph-reachable-p x z))
    :hints (("goal" :expand ((graph-reachable-p x y))
             :use ((:instance graph-reachable-p-suff
                    (x x) (y z) (path (append (graph-reachable-p-witness x y)
                                              (list z))))))))

  (defthm graph-reachable-of-immediate-successors
    (implies (member z (graph-node-succs y))
             (graph-reachable-p y z))
    :hints (("goal" :use ((:instance graph-reachable-p-suff
                           (x y) (y z) (path (list y z))))
             :in-theory (enable graph-path-p))))

  (defthm graph-reachable-transitive1
    (implies (and (graph-reachable-p x y)
                  (graph-reachable-p y z))
             (graph-reachable-p x z))
    :hints (("goal" :expand ((graph-reachable-p x y)
                             (graph-reachable-p y z))
             :use ((:instance graph-reachable-p-suff
                    (x x) (y z) (path (append (graph-reachable-p-witness x y)
                                              (cdr (graph-reachable-p-witness y z)))))))))

  (defthm graph-reachable-transitive2
    (implies (and (graph-reachable-p y z)
                  (graph-reachable-p x y))
             (graph-reachable-p x z)))

  (defthm graph-reachable-of-path
    (implies (and (graph-path-p path)
                  (consp path))
             (graph-reachable-p (car path) (car (last path))))
    :hints (("goal" :use ((:instance graph-reachable-p-suff
                           (x (car path)) (y (car (last path)))))
             :in-theory (disable graph-reachable-p-suff)))))

(define graph-reachable-canonical-witness (x y)
  (graph-path-reduce (graph-reachable-p-witness x y))
  ///
  (defthm graph-reachable-implies-canonical-witness
    (implies (graph-reachable-p x y)
             (let ((path (graph-reachable-canonical-witness x y)))
               (and (consp path)
                    (graph-path-p path)
                    (equal (car path) x)
                    (equal (car (last path)) y))))
    :hints (("goal" :expand ((graph-reachable-p x y)))))

  (defthm no-duplicatesp-of-graph-reachable-canonical-witness
    (no-duplicatesp (graph-reachable-canonical-witness x y)))

  (defthm graph-reachable-implies-x-not-in-cdr-of-canonical-witness
    (implies (graph-reachable-p x y)
             (let ((path (graph-reachable-canonical-witness x y)))
               (not (member x (cdr path)))))
    :hints (("goal" :use no-duplicatesp-of-graph-reachable-canonical-witness
             :in-theory (e/d (no-duplicatesp)
                             (no-duplicatesp-of-graph-reachable-canonical-witness
                              graph-reachable-canonical-witness)))))

  (defthm graph-reachable-implies-graph-path-p-cdr-of-canonical-witness
    (implies (graph-reachable-p x y)
             (let ((path (graph-reachable-canonical-witness x y)))
               (graph-path-p (cdr path))))
    :hints (("goal" :use graph-reachable-implies-canonical-witness
             :in-theory (e/d (graph-path-p)
                             (graph-reachable-implies-canonical-witness
                              graph-reachable-canonical-witness)))))

  (defthm graph-reachable-implies-cadr-successor-of-x-of-canonical-witness
    (implies (and (graph-reachable-p x y)
                  (not (equal x y)))
             (let ((path (graph-reachable-canonical-witness x y)))
               (member (cadr path) (graph-node-succs x))))
    :hints (("goal" :use (graph-reachable-implies-canonical-witness)
             :in-theory (e/d (graph-path-p)
                             (graph-reachable-implies-canonical-witness
                              graph-reachable-canonical-witness)))))

  (defwitness graph-reachable-witness
    :predicate (graph-reachable-p x y)
    :expr (let ((path (graph-reachable-canonical-witness x y)))
               (and (consp path)
                    (graph-path-p path)
                    (equal (car path) x)
                    (equal (car (last path)) y)
                    (no-duplicatesp path)))
    :generalize (((graph-reachable-canonical-witness x y) . reachpath))
    :hints ('(:use (graph-reachable-implies-canonical-witness
                    no-duplicatesp-of-graph-reachable-canonical-witness)
              :in-theory (disable graph-reachable-implies-canonical-witness
                                  no-duplicatesp-of-graph-reachable-canonical-witness)))))



(define graph-reachable-for-some-x (x y)
  :returns (reachable)
  :hooks (:fix)
  (if (atom x)
      nil
    (or (ec-call (graph-reachable-p (car x) y))
        (graph-reachable-for-some-x (cdr x) y)))
  ///
  (defret graph-reachable-for-some-x-when-empty
    (implies (not (consp x))
             (not reachable))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defret graph-reachable-for-some-x-when-reachable-by-member
    (implies (and (graph-reachable-p k y)
                  (member k x))
             (graph-reachable-for-some-x x y)))

  (defret graph-reachable-for-some-x-by-path
    (implies (and (graph-path-p path)
                  (consp path)
                  (member (car path) x)
                  (equal y (car (last path))))
             (graph-reachable-for-some-x x y))
    :hints (("Goal" :induct (graph-reachable-for-some-x x y)))))

(define graph-reachable-for-some-x-witness (x y)
  :verify-guards nil
  (if (atom x)
      nil
    (if (graph-reachable-p (car x) y)
        (graph-reachable-canonical-witness (car x) y)
      (graph-reachable-for-some-x-witness (cdr x) y)))
  ///
  (local (in-theory (enable graph-reachable-for-some-x)))

  (defthm graph-reachable-for-some-x-implies-witness
    (implies (graph-reachable-for-some-x x y)
             (b* ((path (graph-reachable-for-some-x-witness x y)))
               (and (consp path)
                    (member (car path) x)
                    (equal (car (last path)) y)
                    (graph-path-p path)))))

  (in-theory (disable graph-reachable-for-some-x-witness))

  (local (defthm graph-reachable-for-some-successor-implies-reachable
           (implies (graph-reachable-for-some-x (graph-node-succs x) y)
                    (graph-reachable-p x y))
           :hints (("goal" :use ((:instance graph-reachable-for-some-x-implies-witness
                                  (x (graph-node-succs x)))
                                 (:instance graph-reachable-p-suff
                                  (path (cons x (graph-reachable-for-some-x-witness
                                                 (graph-node-succs x) y )))))
                    :in-theory (e/d (intersectp)
                                    (graph-reachable-for-some-x-implies-witness
                                     graph-reachable-p-suff
                                     graph-reachable-for-some-x))
                    :do-not-induct t))))

  (local (defthm graph-reachable-implies-reachable-for-some-successor
           (implies (and (graph-reachable-p x y)
                         (not (equal x y)))
                    (graph-reachable-for-some-x (graph-node-succs x) y))
           :hints (("goal" :use ((:instance graph-reachable-implies-canonical-witness)
                                 (:instance graph-reachable-for-some-x-by-path
                                  (x (graph-node-succs x))
                                  (path (cdr (graph-reachable-canonical-witness x y)))))
                    :in-theory (disable graph-reachable-for-some-x-by-path)))))

  (defthm graph-reachable-for-some-successor
    (implies (not (equal x y))
             (iff (graph-reachable-for-some-x (graph-node-succs x) y)
                  (graph-reachable-p x y))))

  (defwitness graph-reachable-for-some-x-witness
    :predicate (graph-reachable-for-some-x x y)
    :expr (let ((path (graph-reachable-for-some-x-witness x y)))
               (and (consp path)
                    (graph-path-p path)
                    (member (car path) x)
                    (equal (car (last path)) y)))
    :generalize (((graph-reachable-canonical-witness x y) . reachpath))
    :hints ('(:use graph-reachable-for-some-x-implies-witness
              :in-theory (disable graph-reachable-for-some-x-implies-witness)))))





(defsection graph-reachable-through-unvisited-when-preorder-empty
  (local (defun graph-reachable-through-unvisited-when-empty-hint (x y)
           (if (graph-reachable-through-unvisited-p x y nil)
               (b* ((path (graph-reachable-through-unvisited-canonical-witness x y nil)))
                 `(:use ((:instance graph-reachable-p-suff
                           (x ,(hq x)) (y ,(hq y)) (path ,(hq path))))))
             (b* ((path (graph-reachable-canonical-witness x y)))
               `(:use ((:instance graph-reachable-through-unvisited-p-suff
                         (x ,(hq x)) (y ,(hq y)) (visited nil) (path ,(hq path)))))))))

  (defthm graph-reachable-through-unvisited-when-preorer-empty
    (iff (graph-reachable-through-unvisited-p x y nil)
         (graph-reachable-p x y))
    :hints ((use-termhint (graph-reachable-through-unvisited-when-empty-hint x y)))))

(defsection graph-reachable-through-unvisited-for-some-x-when-empty
  (local (defun graph-reachable-through-unvisited-for-some-x-when-preorder-empty-hint (x y)
           (if (graph-reachable-through-unvisited-for-some-x x y nil)
               (b* ((path (graph-reachable-through-unvisited-for-some-x-witness x y nil)))
                 `(:use ((:instance graph-reachable-for-some-x-by-path
                           (x ,(hq x)) (y ,(hq y)) (path ,(hq path))))))
             (b* ((path (graph-reachable-for-some-x-witness x y)))
               `(:use ((:instance graph-reachable-through-unvisited-for-some-x-by-path
                         (x ,(hq x)) (y ,(hq y)) (preorder nil) (path ,(hq path)))))))))

  (defthm graph-reachable-through-unvisited-for-some-x-when-preorder-empty
    (iff (graph-reachable-through-unvisited-for-some-x x y nil)
         (graph-reachable-for-some-x x y))
    :hints ((use-termhint (graph-reachable-through-unvisited-for-some-x-when-preorder-empty-hint x y)))))

(defsection scc-p
  (defun-sk scc-p (scc)
    (forall (x y)
            (implies (member x scc)
                     (iff (member y scc)
                          (and (graph-reachable-p x y)
                               (graph-reachable-p y x)))))
    :rewrite :direct)

  (in-theory (disable scc-p))

  (local (defun scc-in-preorder-when-empty-hint (scc)
           (if (scc-in-preorder-p scc nil)
               (b* (((mv x y) (scc-p-witness scc)))
                 `(:use ((:instance scc-in-preorder-p-necc
                           (x ,(hq x)) (y ,(hq y)) (preorder nil)))
                    :expand ((scc-p scc))
                    :in-theory (disable scc-in-preorder-p-necc)))
             (b* (((mv x y) (scc-in-preorder-p-witness scc nil)))
                 `(:use ((:instance scc-p-necc
                           (x ,(hq x)) (y ,(hq y))))
                    :expand ((scc-in-preorder-p scc nil))
                    :in-theory (disable scc-p-necc))))))

  (defthm scc-in-preorder-when-empty
    (iff (scc-in-preorder-p scc nil)
         (scc-p scc))
    :hints ((use-termhint (scc-in-preorder-when-empty-hint scc)))))


(defthm tarjan-sccs-top-produces-sccs
  (b* (((mv & & & sccs) (tarjan-sccs x nil nil)))
    (implies (member scc sccs)
             (and (consp scc)
                  (scc-p scc)
                  (graph-reachable-p x (car scc)))))
  :hints (("goal" :use ((:instance tarjan-sccs-produces-preorder-reachable-sccs
                         (stack nil) (preorder nil)))
           :in-theory (disable tarjan-sccs-produces-preorder-reachable-sccs))))

(defthm tarjan-sccs-list-top-produces-sccs
  (b* (((mv & & & sccs) (tarjan-sccs-list x nil nil)))
    (implies (member scc sccs)
             (and (consp scc)
                  (scc-p scc)
                  (graph-reachable-for-some-x x (car scc)))))
  :hints (("goal" :use ((:instance tarjan-sccs-list-produces-preorder-reachable-sccs
                         (stack nil) (preorder nil)))
           :in-theory (disable tarjan-sccs-list-produces-preorder-reachable-sccs))))


(local (defthm tarjan-node-reaches-empty-stack
         (not (tarjan-node-reaches-stack y nil preorder))
         :hints(("Goal" :in-theory (enable tarjan-node-reaches-stack)))))

(defthm tarjan-sccs-top-sorts-all-nodes
  (b* (((mv & & & sccs) (tarjan-sccs x nil nil)))
    (implies (graph-reachable-p x y)
             (member y (append-lists sccs))))
  :hints (("goal" :use ((:instance tarjan-sccs-contains-all-non-stack-reaching-nodes
                         (stack nil) (preorder nil)))
           :in-theory (disable tarjan-sccs-contains-all-non-stack-reaching-nodes))))

(defthm tarjan-sccs-list-top-sorts-all-nodes
  (b* (((mv & & & sccs) (tarjan-sccs-list x nil nil)))
    (implies (graph-reachable-for-some-x x y)
             (member y (append-lists sccs))))
  :hints (("goal" :use ((:instance tarjan-sccs-list-contains-all-non-stack-reaching-nodes
                         (stack nil) (preorder nil)))
           :in-theory (disable tarjan-sccs-list-contains-all-non-stack-reaching-nodes))))
