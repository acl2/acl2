; Simple graph theory for use by drone planner
;
; Copyright (C) 2017-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

#|
Graphs have nodes, an adjacency function, and distances as primitives, with paths and path costs as extensions.
We give an implementation with nodes as nats.
|#

(include-book "kestrel/sequences/defforall" :dir :system)
(include-book "kestrel/sequences/deffilter" :dir :system)

(include-book "centaur/fty/top" :dir :system)
(include-book "std/alists/alist-vals" :dir :system)
(include-book "kestrel/lists-light/len" :dir :system)
(include-book "kestrel/lists-light/member-equal" :dir :system)
(include-book "kestrel/lists-light/memberp" :dir :system)

(local (include-book "kestrel/utilities/lists/add-to-set-theorems" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/last" :dir :system))

(in-theory (disable acl2-count))

;;  general theorems

;; In kestrel-acl2/axe/dagify.lisp
(defthm car-of-last-of-append
  (equal (car (last (append x y)))
         (if (consp y)
             (car (last y))
           (car (last x))))
  :hints (("Goal" :in-theory (enable append))))

(defthm consp-last
  (equal (consp (last x))
         (consp x))
  :hints (("Goal" :in-theory (enable last))))

(defthm subsetp-equal-add-to-set-equal
  (implies (subsetp-equal x (double-rewrite y))
           (subsetp-equal x (add-to-set-equal z y)))
  :hints (("Goal" :in-theory (enable add-to-set-equal))))

(defthm union-equal-true-listp-nil
  (implies (true-listp l)
           (equal (union-equal l nil)
                  l)))

;;; lifted prefixp functions: order of arguments determined by underlying prefixp call
;; fa y:list a in l: list(list a) . (prefixp x y)
(defforall all-prefixed-p (x l) (prefixp x l) :fixed x :true-listp t)

(defthmd all-prefixed-p-non-null-alist
  (implies (and (consp x)
                (all-prefixed-p x l))
           (alistp l)))

;; fa y in l . (prefixp y x)
(defforall all-prefixes-p (l x) (prefixp x l) :fixed x :true-listp t)

;; ex y in l . (prefixp x y)
(defexists some-prefixed-p (x l) (prefixp x l) :fixed x)

;; ex y in l . (prefixp y x)
(defexists some-prefixes-p (l x) (prefixp l x) :fixed x)

;; fa y in l2: list(list a) . ex x in l1: list(list a) . (prefixp x y)
(defforall all-prefixed-by-some-p (l1 l2) (some-prefixes-p l1 l2) :fixed l1 :true-listp t)

;; (all-prefixed-by-some-p '((a s) (d f)) '((a s d f) (d f a s) (a s) (d f)))

(defthm all-prefixed-by-some-p-singleton
  (equal (all-prefixed-by-some-p (list x) y)
         (all-prefixed-p x y))
  :hints (("Goal" :in-theory (enable all-prefixed-by-some-p))))

(defthm all-prefixed-by-some-p-member
  (implies (and (all-prefixed-p x l2)
                (memberp x (double-rewrite l1)))
           (all-prefixed-by-some-p l1 l2))
  :hints (("Goal" :in-theory (enable some-prefixes-p all-prefixed-by-some-p))))

(defthm all-prefixed-p-transitive
  (implies (and (all-prefixed-p x l1)
                (all-prefixed-by-some-p l1 l2))
           (all-prefixed-p x l2))
  :hints (("Goal" :in-theory (enable all-prefixed-by-some-p all-prefixed-p))))

(defthm all-prefixed-by-some-p-transitive
  (implies (and (all-prefixed-by-some-p l1 l2)
                (all-prefixed-by-some-p l2 l3))
           (all-prefixed-by-some-p l1 l3))
  :hints (("Goal" :in-theory (enable some-prefixes-p all-prefixed-by-some-p))))

;; domain model
(define nodep (x)
  :returns (b booleanp)
  (natp x)
///
(defthm nodep-zero
  (nodep 0)))

(define node-fix (x)
  :returns (n nodep)
  (if (nodep x)
      x
    0)
///
(defthm nodep-node-fix
  (nodep (node-fix x)))

(defthm nodep-node-fix-id
  (implies (nodep x)
           (equal (node-fix x) x))))

(defun node-equiv (n1 n2)
  (declare (xargs :guard t))
  (equal (node-fix n1) (node-fix n2)))

(defequiv node-equiv)

(fty::deffixtype node :pred nodep :fix node-fix :equiv node-equiv)

(in-theory (disable node-equiv))

(defforall node-list-p (l) (nodep l) :true-listp t :guard t)

(defthm node-list-p-true-listp1
  (implies (node-list-p l)
           (true-listp l)))

(defthm nodep-car-node-list-p
  (implies (node-list-p x)
           (equal (nodep (car x))
                  (consp x))))

(defthm node-list-p-add-to-set-equal
  (implies (and (nodep n)
                (node-list-p l))
           (node-list-p (add-to-set-equal n l)))
  :hints (("Goal" :in-theory (enable add-to-set-equal))))

(defthm node-list-p-intersection-equal
  (implies (and (node-list-p x) (node-list-p y))
           (node-list-p (intersection-equal x y)))
  :hints (("Goal" :in-theory (enable intersection-equal))))

(defthm node-list-p-union-equal
  (implies (and (node-list-p new)
                (node-list-p new-visited-nodes))
           (node-list-p (union-equal new new-visited-nodes))))

(define node-list-fix (l)
  :returns (nl node-list-p)
  (if (node-list-p l)
      l
    ())
///
(defthm node-list-fix-node-list-p
  (implies (node-list-p x)
           (equal (node-list-fix x) x))))

(defun node-list-equiv (l1 l2)
  (declare (xargs :guard t))
  (equal (node-list-fix l1) (node-list-fix l2)))

(defequiv node-list-equiv)

(fty::deffixtype node-list :pred node-list-p :fix node-list-fix :equiv node-list-equiv)

(defthm node-list-p-set-difference-equal
  (implies (node-list-p l)
           (node-list-p (set-difference-equal l m)))
  :hints (("Goal" :in-theory (enable set-difference-equal))))

(defthm nodep-car-last
     (implies (and l (node-list-p l))
              (nodep (car (last l)))))

(defforall all-node-list-p (l) (node-list-p l) :true-listp t :guard t)

(defun all-node-list-fix (l)
  (declare (xargs :guard t))
  (if (all-node-list-p l)
      l
    ()))

(defun all-node-list-equiv (l1 l2)
  (declare (xargs :guard t))
  (equal (all-node-list-fix l1) (all-node-list-fix l2)))

(defequiv all-node-list-equiv)

(fty::deffixtype all-node-list :pred all-node-list-p :fix all-node-list-fix :equiv all-node-list-equiv)

(defthm all-node-list-p-alist-vals
  (implies (all-node-list-p ll)
           (all-node-list-p (alist-vals ll)))
  :hints (("Goal" :in-theory (enable alist-vals))))


(define nodep-or-null (x)
  :enabled t
  :returns (b booleanp)
  (or (null x) (nodep x)))

(define node-or-null-fix (x)
  (if (nodep x)
      x
    nil)
///
(defthm node-or-null-node-or-null-fix
  (nodep-or-null (node-or-null-fix x)))
(defthm node-or-null-fixid
  (implies (nodep-or-null x)
           (equal (node-or-null-fix x) x)))
) ; node-or-null-fix

(defun node-or-null-equiv (n1 n2)
  (declare (xargs :guard t))
  (equal (node-or-null-fix n1) (node-or-null-fix n2)))

(defequiv node-or-null-equiv)

(fty::deffixtype node-or-null :pred nodep-or-null :fix node-or-null-fix :equiv node-or-null-equiv)


(fty::defprod connection
  ((node1 node)
   (node2 node)
   (distance nat)))

(defforall connection-list-p (l) (connection-p l) :true-listp t :guard t)

(define connection-list-fix (l)
  :returns (nl connection-list-p)
  (if (connection-list-p l)
      l
    ())
///
(defthm connection-list-fix-connection-list-p
  (implies (connection-list-p x)
           (equal (connection-list-fix x) x))))

(defun connection-list-equiv (l1 l2)
  (declare (xargs :guard t))
  (equal (connection-list-fix l1) (connection-list-fix l2)))

(defequiv connection-list-equiv)

(fty::deffixtype connection-list :pred connection-list-p :fix connection-list-fix :equiv connection-list-equiv)


(define all-nodes-in-connections ((conns connection-list-p))
  :returns (nds node-list-p)
  (if (endp conns)
      ()
    (add-to-set-equal (connection->node1 (first conns))
                      (add-to-set-equal (connection->node2 (first conns))
                                        (all-nodes-in-connections (rest conns))))))

(define all-connections-in-nodes ((conns connection-list-p) (nodes node-list-p))
  :returns (b booleanp)
  (subsetp-equal (all-nodes-in-connections conns) nodes)
///
(defthm all-connections-in-nodes-member1
  (implies (and (all-connections-in-nodes conns nodes)
                (memberp c (double-rewrite conns)))
           (memberp (connection->node1 c) nodes))
  :hints (("Goal" :in-theory (enable all-nodes-in-connections))))

(defthm all-connections-in-nodes-member2
  (implies (and (all-connections-in-nodes conns nodes)
                (memberp c (double-rewrite conns)))
           (memberp (connection->node2 c) nodes))
  :hints (("Goal" :in-theory (enable all-nodes-in-connections))))
)

(fty::defprod dgraph
  ((nodes node-list)
   (connections connection-list))
  :verbosep t)

(define node-of-dgraph-p ((n nodep) (g dgraph-p))
  :returns (b booleanp)
  (memberp n (dgraph->nodes g))
///
(defthm node-of-dgraph-p-nodep
  (implies (node-of-dgraph-p n g)
           (nodep n))
  :rule-classes (:rewrite :forward-chaining))
)

(defconst *empty-graph* (dgraph () ()))

(define connection-of-dgraph-p ((c connection-p) (g dgraph-p))
  :returns (b booleanp)
  (memberp c (dgraph->connections g))
///
(defthm connection-of-dgraph-p-connectionp
  (implies (connection-of-dgraph-p c g)
           (connection-p c)))
)

(define wf-dgraph-p (g)
  :returns (b booleanp)
  (and (dgraph-p g)
       (all-connections-in-nodes (dgraph->connections g) (dgraph->nodes g)))
///
(defthm wf-dgraph-p-dgraph-p
  (implies (wf-dgraph-p g)
           (dgraph-p g)))
(defthm wf-dgraph-p-all-connections-in-nodes
  (implies (wf-dgraph-p g)
           (all-connections-in-nodes (dgraph->connections g) (dgraph->nodes g))))
)

(defthm connection-of-dgraph-p-node-of-dgraph-p-1
  (implies (and (wf-dgraph-p g)
                (connection-of-dgraph-p c g))
           (node-of-dgraph-p (connection->node1 c) g))
  :hints (("Goal" :in-theory (enable node-of-dgraph-p connection-of-dgraph-p wf-dgraph-p))))

(defthm connection-of-dgraph-p-node-of-dgraph-p-2
  (implies (and (wf-dgraph-p g)
                (connection-of-dgraph-p c g))
           (node-of-dgraph-p (connection->node2 c) g))
  :hints (("Goal" :in-theory (enable node-of-dgraph-p connection-of-dgraph-p wf-dgraph-p))))

(define connection-for ((n1 nodep) (n2 nodep) (connection connection-p))
  :returns (b booleanp)
  (or (and (equal n1 (connection->node1 connection))
           (equal n2 (connection->node2 connection)))
      (and (equal n1 (connection->node2 connection))
           (equal n2 (connection->node1 connection)))))

(define connection-to ((n nodep) (connection connection-p))
  :returns (nd1 node-list-p)
  (if (equal n (connection->node1 connection))
      (list (connection->node2 connection))
    (if (equal n (connection->node2 connection))
        (list (connection->node1 connection))
      nil))
///
(defthm all-nodes-in-connections-connection-of-dgraph-p
  (implies (and (memberp x (connection-to n c))
                (memberp c (double-rewrite conns)))
           (memberp x (all-nodes-in-connections conns)))
  :hints (("Goal" :in-theory (enable all-nodes-in-connections))))
(defthm connection-to-in-wf-dgraph0
  (implies (and (memberp x (connection-to n c))
                (memberp x (all-nodes-in-connections (dgraph->connections (double-rewrite g))))
                (wf-dgraph-p g)
                (connection-of-dgraph-p c g))
           (node-of-dgraph-p x g))
  :hints (("Goal" :in-theory (enable all-nodes-in-connections))))
(defthm connection-to-in-wf-dgraph
  (implies (and (memberp x (connection-to n c))
                (wf-dgraph-p g)
                (connection-of-dgraph-p c g))
           (node-of-dgraph-p x g)))
)


(define adj-distance-cns ((n1 nodep) (n2 nodep) (connections connection-list-p))
  :returns (dist natp)
  (if (endp connections)                ; Why does this work for guard=checking and not endp?
      10000000                          ; infinity? Shouldn't happen?
    (if (connection-for n1 n2 (first connections))
        (connection->distance (first connections))
      (adj-distance-cns n1 n2 (rest connections))))
///
(defthm adj-distance-cns-commutative
  (equal (adj-distance-cns n1 n2 connections)
         (adj-distance-cns n2 n1 connections))
  :hints (("Goal" :in-theory (enable connection-for))))
)

(define adj-distance ((n1 nodep) (n2 nodep) (g dgraph-p))
  :returns (dist natp)
  (adj-distance-cns n1 n2 (dgraph->connections g))
///
(defthm adj-distance-commutative
  (equal (adj-distance n1 n2 g)
         (adj-distance n2 n1 g)))
)

(define adj-nodes-cns ((n nodep) (connections connection-list-p))
  :returns (adj-nodes node-list-p)
  (if (consp connections)
      (append (connection-to n (first connections))
              (adj-nodes-cns n (rest connections)))
    nil))

(defthm adj-nodes-cns-subset-nodes
  (implies (and (nodep n) (connection-list-p conns))
           (subsetp-equal (adj-nodes-cns n conns) (all-nodes-in-connections conns)))
  :hints (("Goal" :in-theory (enable adj-nodes-cns all-nodes-in-connections connection-to))))

(defthm adj-nodes-cns-in-dgraph
  (implies (and (nodep n)
                (memberp x (adj-nodes-cns n (dgraph->connections (double-rewrite g))))
                (wf-dgraph-p g))
           (node-of-dgraph-p x g))
  :hints (("Goal" :in-theory (enable wf-dgraph-p all-connections-in-nodes node-of-dgraph-p))))

(define adj-nodes ((n nodep) (g dgraph-p))
  :returns (adj-nodes node-list-p)
  (adj-nodes-cns n (dgraph->connections g))
///
(defthm adj-nodes-subset-dgraph-nodes
  (implies (and (nodep n)
                (wf-dgraph-p g))
           (subsetp-equal (adj-nodes n g) (dgraph->nodes g)))
  :hints (("Goal" :in-theory (enable wf-dgraph-p all-connections-in-nodes))))
(defthm adj-nodes-in-dgraph
  (implies (and (nodep n)
                (memberp x (adj-nodes n g))
                (wf-dgraph-p g))
           (node-of-dgraph-p x g)))
)

(defthm not-nodep-not-member-adj-nodes
  (implies (not (nodep x))
           (not (memberp x (adj-nodes n g))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;;; Paths and connectivity

;; Whether a list of nodes has all nodes in the dgraph and adjacent nodes in the list are connected
(define node-path-p (l (g dgraph-p))
  :returns (b booleanp)
  (and (node-list-p l)
       (or (null l)
           (and (memberp (first l) (dgraph->nodes g))
                (or (null (rest l))
                    (memberp (cadr l) (adj-nodes (first l) g)))
                (node-path-p (rest l) g))))
///
(defthm node-path-p-nil
  (node-path-p () g))
(defthm node-path-p-append-nil
  (implies (and (node-path-p l1 g)
                (consp l1))
           (node-path-p (append l1 nil) g)))
(defthm node-path-p-append
  (implies (and (node-path-p l1 g)
                (node-path-p l2 g)
                (consp l1)
                (consp (double-rewrite l2))
                (memberp (car (double-rewrite l2)) (adj-nodes (car (last l1)) g)))
           (node-path-p (append l1 l2) g))
  :hints (("Goal" :induct (last l1)
           :in-theory (enable last append))))
(defthm node-path-p-append-1
  (implies (and (node-path-p l1 g)
                (consp l1)
                (wf-dgraph-p g)
                (memberp x (adj-nodes (car (last l1)) g)))
           (node-path-p (append l1 (list x)) g)))
(defthm cdr-node-path-p
  (implies (node-path-p l g)
           (node-path-p (cdr l) g)))
(defthm node-path-p-node-list-p
  (implies (node-path-p l g)
           (node-list-p l))
  :rule-classes (:forward-chaining :rewrite))
(defthm node-path-p-list
  (implies (and (dgraph-p g)
                (memberp n (dgraph->nodes (double-rewrite g))))
           (node-path-p (list n) g))
  :hints (("Goal" :in-theory (enable node-path-p))))
(defthm node-path-p-member-2
  (implies (and (consp l)
                (nodep n)
                (node-path-p l g)
                (memberp (car l) (adj-nodes n g))
                (consp (cdr l)))
           (memberp (cadr l)
                    (adj-nodes (car l) g))))
(defthm node-path-p-true-listp
  (implies (node-path-p l g)
           (true-listp l))
  :rule-classes (:forward-chaining))
(defthm node-path-p-sublistp-member
  (implies (and (node-path-p l g)
                (memberp x (double-rewrite l)))
           (node-path-p (list x) g)))
(defthm node-path-p-subsetp-equal
  (implies (node-path-p path g)
           (subsetp-equal path (dgraph->nodes g))))
)

(defthm node-path-p-singleton
  (implies (and (wf-dgraph-p g)
                (node-of-dgraph-p n g))
           (node-path-p (list n) g))
  :hints (("Goal" :in-theory (enable node-path-p node-of-dgraph-p wf-dgraph-p))))


(defforall all-node-path-p (l g) (node-path-p l g) :fixed g :true-listp t
  :guard (dgraph-p g))

(defthm all-node-path-p-all-node-list-p
  (implies (all-node-path-p l g)
           (all-node-list-p l))
  :hints (("Goal" :in-theory (enable all-node-path-p all-node-list-p node-path-p))))

(defthm all-node-path-p-alist-vals
  (implies (all-node-path-p ll g)
           (all-node-path-p (alist-vals ll) g))
  :hints (("Goal" :in-theory (enable alist-vals))))

(define node-path-from-p (n l (g dgraph-p))
  :returns (b booleanp)
  (and (nodep n)
       (node-path-p l g)
       (or (null l)
           (memberp (first l) (adj-nodes n g))))
///
(defthm node-path-from-p-nil
  (not (node-path-from-p nil l g)))
(defthm node-path-from-p-empty-list
  (implies (nodep n)
           (node-path-from-p n () g)))
(defthm node-path-from-p-append
  (implies (and (node-path-from-p n l1 g)
                (node-path-from-p (car (last l1)) l2 g)
                (consp l1)
                (consp (double-rewrite l2)))
           (node-path-from-p n (append l1 l2) g)))
(defthm node-path-from-p-append-1
  (implies (and (node-path-from-p n l1 g)
                (consp l1)
                (wf-dgraph-p g)
                (memberp x (adj-nodes (car (last l1)) g)))
           (node-path-from-p n (append l1 (list x)) g)))
(defthm node-path-p-node-path-from-p-append
  (implies (and (node-path-p l1 g)
                (consp l1)
                (wf-dgraph-p g)
                (node-path-from-p (car (last l1)) l2 g))
           (node-path-p (append l1 l2) g)))
(defthm cdr-node-path-from-p
  (implies (and (consp l)
                (node-path-from-p n l g))
           (node-path-from-p (car l) (cdr l) g)))
(defthm node-path-from-p-node-path-p
  (implies (node-path-from-p n l g)
           (node-path-p l g))
  :rule-classes (:forward-chaining :rewrite))
(defthm node-list-p-node-path-from-p
  (implies (and (node-path-p l g)
                (nodep n)
                (memberp (first (double-rewrite l)) (adj-nodes n g)))
           (node-path-from-p n l g)))
(defthm node-path-from-p-car-cdr
  (implies (and (node-path-p l g)
                (consp l))
           (node-path-from-p (car l) (cdr l) g))
  :hints (("Goal" :in-theory (enable node-path-p))))
(defthm node-path-from-p-implies-node-list-p
  (implies (node-path-from-p l p g)
           (node-list-p p)))
)

(defthm node-path-from-p-prefixp-singleton
  (implies (and (prefixp (list nd0) (double-rewrite path))
                (nodep nd0)
                (node-path-p path g))
           (node-path-from-p nd0 (cdr path) g))
  :hints (("Goal" :in-theory (enable node-path-p))))

(defforall all-node-path-from-p (n l g) (node-path-from-p n l g) :fixed (n g) :true-listp t
  :guard (dgraph-p g))

(defthm all-node-path-from-p-all-node-path-p-all-prefixed-p-singleton
  (implies (and (all-node-path-p paths g)
                (nodep nd0)
                (all-prefixed-p (list nd0) paths))
           (all-node-path-from-p nd0 (alist-vals paths) g))
  :hints (("Goal" :in-theory (enable alist-vals))))


;; Whether the final node in a path is in end-locs
(define path-ends-n-set-p ((path node-list-p) (end-locs node-list-p))
  (and (consp path)
       (memberp (car (last path))
                     end-locs)))

(defforall all-paths-ends-n-set-p (paths end-locs) (path-ends-n-set-p paths end-locs) :fixed (end-locs) :true-listp t)

(defthm len-set-difference-equal
  (<= (len (set-difference-equal x y)) (len x))
  :hints (("Goal" :in-theory (enable set-difference-equal))))

(defthm node-list-p-append-set-difference-equal
  (implies (node-list-p y)
           (node-list-p (append (set-difference-equal (adj-nodes x g)
                                                      seen-nodes)
                                y))))

(define connected-nodes-aux ((nds node-list-p) (seen-nodes node-list-p) (n natp) (g wf-dgraph-p))
   :returns (cnodes node-list-p)
   :measure (nfix n)
   (if (or (endp nds) (zp n) (not (mbt (node-list-p seen-nodes))))
       (node-list-fix seen-nodes)
     (let ((new-nds (set-difference-equal (adj-nodes (first nds) g) seen-nodes)))
       (connected-nodes-aux (append new-nds (rest nds)) (append new-nds seen-nodes) (- n 1) g))))

(define connected-nodes ((nd nodep) (g wf-dgraph-p))
  :returns (cnodes node-list-p)
  (connected-nodes-aux (list nd) (list nd) (len (dgraph->nodes g)) g))

(mutual-recursion
 (defun connected-to-some (nd nds n g)
   (declare (xargs :guard (and (nodep nd) (node-list-p nds) (natp n) (dgraph-p g))
                   :measure (nfix n)))
   (and (not (zp n))
        (consp nds)
        (or (connected-p-aux nd (first nds) (- n 1) g)
            (connected-to-some nd (rest nds) (- n 1) g))))

 (defun connected-p-aux (n1 n2 n g)
   (declare (xargs :guard (and (nodep n1) (nodep n2) (natp n) (dgraph-p g))
                   :measure (nfix n)))
   (or (equal n1 n2)
       (if (zp n)
           nil
         (connected-to-some n1 (adj-nodes n2 g) (- n 1) g))))
)

(defun connected-p (n1 n2 g)
  (declare (xargs :guard (and (nodep n1) (nodep n2) (dgraph-p g))))
  (connected-p-aux n1 n2 (* 4 (len (dgraph->connections g))) g)) ; ? TODO check (* 4 (len (dgraph->connections g)))

(defun connected-to-all-p (nd nds g)
  (declare (xargs :guard (and (nodep nd) (node-list-p nds) (dgraph-p g))))
  (or (endp nds)
      (and (connected-p nd (first nds) g)
           (connected-to-all-p nd (rest nds) g))))

(defun all-connected-p (nds1 nds2 g)
  (declare (xargs :guard (and (node-list-p nds1) (node-list-p nds2) (dgraph-p g))))
  (or (endp nds1)
      (and (connected-to-all-p (first nds1) nds2 g)
           (all-connected-p (rest nds1) nds2 g))))

(defun connected-dgraph-p (g)
  (declare (xargs :guard (dgraph-p g)))
  (and (dgraph-p g)
       (all-connected-p (dgraph->nodes g) (dgraph->nodes g) g)))

;; Avoid repetitions in paths
(define extend-path ((path node-list-p) (node nodep))
  :returns (rpath node-list-p)
  (if (memberp node path)
      (node-list-fix path)
    (append (node-list-fix path)
            (list (node-fix node))))
///
(defthm extend-path-consp
  (implies (node-list-p path)
           (consp (extend-path path node))))
(defthm prefixp-extend-path
  (implies (node-list-p path)
           (prefixp path (extend-path path node)))))

(defthm extend-path-node-path-p
  (implies (and (wf-dgraph-p g)
                (node-path-p path g)
                (nodep node)
                (consp (double-rewrite path))
                (memberp node (adj-nodes (car (last (double-rewrite path))) g)))
           (node-path-p (extend-path path node) g))
  :hints (("Goal" :in-theory (e/d (extend-path) (wf-dgraph-p)))))

(define extend-1-path ((path node-list-p) (nodes node-list-p))
  :returns (rpaths all-node-list-p)
  (if (endp nodes)
      nil
    (let ((rec-val (extend-1-path path (rest nodes)))
          (new-path (extend-path path (first nodes))))
      (if (equal new-path path)
          rec-val
        (cons new-path rec-val))))
///
(defthm extend-1-path-all-node-path-p-0
  (implies (and (wf-dgraph-p g)
                (node-path-p path g)
                (consp (double-rewrite path))
                (subsetp-equal (double-rewrite nodes) (adj-nodes (car (last (double-rewrite path))) g)))
           (all-node-path-p (extend-1-path path nodes) g)))
(defthm all-prefixed-p-extend-1-path
  (implies (node-list-p path)
           (all-prefixed-p path (extend-1-path path nodes))))
)

(defthm extend-1-path-all-node-path-p
    (implies (and (wf-dgraph-p g)
                  (node-path-p path g)
                  (consp path))
             (all-node-path-p (extend-1-path path (adj-nodes (car (last path)) g)) g)))

(define path-extensions ((path node-list-p) (g dgraph-p))
  :returns (rpaths all-node-list-p)
  (if (or (endp path) (not (mbt (dgraph-p g))))
      ()
    (extend-1-path path (adj-nodes (car (last path)) g)))
///
(defthm path-extensions-all-node-path-p
  (implies (and (wf-dgraph-p g)
                (node-path-p path g))
           (all-node-path-p (path-extensions path g) g)))
(defthm path-extensions-prefixp
  (implies (node-list-p path)
           (all-prefixed-p path (path-extensions path g))))
)

(define extend-paths ((paths all-node-list-p) (g dgraph-p))
  :returns (rpaths all-node-list-p)
  (if (endp paths)
      ()
    (append (path-extensions (first paths) g)
            (extend-paths (rest paths) g)))
///
(defthm extend-paths-all-node-path-p
  (implies (and (all-node-path-p paths g)
                (wf-dgraph-p g))
           (all-node-path-p (extend-paths paths g) g)))
)

(defthm all-prefixed-by-some-p-path-extensions-lemma
  (implies (and (consp paths)
                (all-prefixed-by-some-p (cdr paths)
                                        (extend-paths (cdr paths) g))
                (all-node-list-p paths))
           (all-prefixed-by-some-p paths (path-extensions (car paths) g)))
  :hints (("Goal" :in-theory (e/d (extend-paths) (path-extensions-prefixp))
           :use ((:instance path-extensions-prefixp (path (car paths)))))))

(defthm extend-paths-all-prefixed-p
  (implies (all-node-list-p paths)
           (all-prefixed-by-some-p paths (extend-paths paths g)))
  :hints (("Goal" :in-theory (enable extend-paths))))

(deffilter paths-not-ending-in-set (paths nodes) (not (memberp (car (last paths)) nodes)) :fixed (nodes)
  :guard (and (all-node-list-p paths) (node-list-p nodes)))

(defthm paths-not-ending-in-set-all-node-list-p
  (implies (and (all-node-list-p paths)
                ;;(node-list-p nodes)
                )
           (all-node-list-p (paths-not-ending-in-set paths nodes)))
  :hints (("Goal" :in-theory (enable paths-not-ending-in-set))))

(defthm paths-not-ending-in-set-all-node-path-p
  (implies (and (all-node-path-p paths g) (node-list-p nodes))
           (all-node-path-p (paths-not-ending-in-set paths nodes) g))
  :hints (("Goal" :in-theory (enable paths-not-ending-in-set))))

(defthm all-prefixed-by-some-p-paths-not-ending-in-set
  (implies (all-prefixed-by-some-p paths1 paths2)
           (all-prefixed-by-some-p paths1 (paths-not-ending-in-set paths2 nodes)))
  :hints (("Goal" :in-theory (enable paths-not-ending-in-set))))

(defthm paths-not-ending-in-set-id
  (implies (all-node-list-p paths)
           (equal (paths-not-ending-in-set paths ())
                  paths))
  :hints (("Goal" :in-theory (enable paths-not-ending-in-set))))

(define shortest-paths-not-ending-in-set-aux ((paths all-node-list-p)
                                              (min-path-length integerp)
                                              (nodes node-list-p)
                                              (n natp)
                                              (g dgraph-p))
  :returns (rpaths all-node-list-p :hyp (node-list-p nodes))
  :measure (nfix n)
  :guard (subsetp-equal nodes (dgraph->nodes g))
  (let ((new-paths (extend-paths paths g)))
    (if (or (equal new-paths paths) (zp n))
        nil
      (let ((good-paths (paths-not-ending-in-set new-paths nodes)))
        (if (and (not (null good-paths))
                 (<= min-path-length 1))
            good-paths
          (shortest-paths-not-ending-in-set-aux new-paths (- min-path-length 1) nodes (- n 1) g)))))
///
(defthm shortest-paths-not-ending-in-set-aux-all-node-path-p
  (implies (and (wf-dgraph-p g)
                (node-list-p nodes)
                (all-node-path-p paths g))
           (all-node-path-p (shortest-paths-not-ending-in-set-aux paths ml nodes n g) g)))
)

(defthm shortest-paths-not-ending-in-set-aux-all-prefixed-by-some-p-lemma
  (implies (and (all-prefixed-by-some-p
                 (extend-paths paths g)
                 (shortest-paths-not-ending-in-set-aux (extend-paths paths g)
                                                       (+ -1 ml)
                                                       nodes (+ -1 n)
                                                       g))
                (all-node-list-p paths))
           (all-prefixed-by-some-p paths
                                   (shortest-paths-not-ending-in-set-aux (extend-paths paths g)
                                                                         (+ -1 ml)
                                                                         nodes (+ -1 n)
                                                                         g)))
  :hints (("Goal" :in-theory (e/d () (all-prefixed-by-some-p-transitive))
           :use (:instance all-prefixed-by-some-p-transitive
                           (l1 paths)
                           (l2 (extend-paths paths g))
                           (l3 (shortest-paths-not-ending-in-set-aux (extend-paths paths g)
                                                                     (+ -1 ml)
                                                                     nodes (+ -1 n)
                                                                     g))))))

(defthm shortest-paths-not-ending-in-set-aux-all-prefixed-by-some-p
  (implies (all-node-list-p paths)
           (all-prefixed-by-some-p paths (shortest-paths-not-ending-in-set-aux paths ml nodes n g)))
  :hints (("Goal" :in-theory (e/d (shortest-paths-not-ending-in-set-aux) ()))))

(define shortest-paths-not-ending-in-set-0 ((nd0 nodep)
                                            (min-path-length integerp)
                                            (nodes node-list-p)
                                            (g dgraph-p))
  :returns (rpaths all-node-list-p :hyp (node-list-p nodes))
  (declare (xargs :guard (subsetp-equal nodes (dgraph->nodes g))))
  (shortest-paths-not-ending-in-set-aux (list (list nd0)) min-path-length nodes (len (dgraph->nodes g)) g)
///
(defthm shortest-paths-not-ending-in-set-0-all-node-path-p
  (implies (and (wf-dgraph-p g)
                (node-path-p (list nd0) g)
                (node-list-p nodes))
           (all-node-path-p (shortest-paths-not-ending-in-set-0 nd0 min-path-length nodes g) g)))
(defthmd shortest-paths-not-ending-in-set-0-prefix-lemma
  (implies (nodep nd0)
           (all-prefixed-by-some-p (list (list nd0)) (shortest-paths-not-ending-in-set-0 nd0 min-path-length nodes g)))
  :hints (("Goal" :in-theory (disable all-prefixed-by-some-p-singleton))))
)

(defthm shortest-paths-not-ending-in-set-0-prefix
  (implies (nodep nd0)
           (all-prefixed-p (list nd0) (shortest-paths-not-ending-in-set-0 nd0 min-path-length nodes g)))
  :hints (("Goal" :use (:instance shortest-paths-not-ending-in-set-0-prefix-lemma))))

(defthm shortest-paths-not-ending-in-set-0-alistp
  (implies (and (wf-dgraph-p g)
                (nodep nd0)
                (node-list-p nodes))
           (alistp (shortest-paths-not-ending-in-set-0 nd0 min-path-length nodes g)))
  :hints (("Goal" :use (:instance all-prefixed-p-non-null-alist
                                  (l (shortest-paths-not-ending-in-set-0 nd0 min-path-length nodes g))
                                  (x (list nd0))))))

(define shortest-paths-not-ending-in-set ((nd0 nodep)
                                          (min-path-length integerp)
                                          (nodes node-list-p)
                                          (g wf-dgraph-p))
  :returns (rpaths all-node-list-p :hyp :guard)
  (declare (xargs :guard (subsetp-equal nodes (dgraph->nodes g))))
  (alist-vals (shortest-paths-not-ending-in-set-0 nd0 min-path-length nodes g))
///
(defthm shortest-paths-not-ending-in-set-all-node-path-p
  (implies (and (wf-dgraph-p g)
                (node-path-p (list nd0) g)
                (node-list-p nodes))
           (all-node-path-p (shortest-paths-not-ending-in-set nd0 min-path-length nodes g) g)))
(defthm shortest-paths-not-ending-in-set-all-node-path-from-p
  (implies (and (wf-dgraph-p g)
                (node-path-p (list nd0) g)
                (node-list-p nodes))
           (all-node-path-from-p nd0 (shortest-paths-not-ending-in-set nd0 min-path-length nodes g) g)))
)
