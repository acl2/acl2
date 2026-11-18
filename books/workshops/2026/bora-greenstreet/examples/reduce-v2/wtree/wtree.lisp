; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "wtree-helpers")

(set-induction-depth-limit 1)

; Predicate for Lin & Snyder style reduce worker trees, specifically for the reduce
; defined in reduce-v2/reduce-proc.lisp

; The Predicate ----------------------------------------------------------------

; If a process is a node of a worker tree:
; - it is the root or a leaf,
; - its children, parent, and indices are consistent with the rest of net,
; - if it is the root, the index of its rightmost child is one less than the
;   size of the network. This ties the root's subtree to the whole network.
;   This could probably be replaced with a better property.
(define wtree-node-p ((pid pid-p) (net network-p))
  :returns (r booleanp)
  :guard-hints
    (("Goal" :use ((:instance node-p-of-rightmost-child (net net) (pid pid)))))
  (b* ((pid (pid-fix pid))
       (net (network-fix net))
       ((unless (omap::assoc pid net)) nil)
       (proc (omap::lookup pid net))
       ((unless (or (root-p proc) (leaf-p proc))) nil)
       (bind (wtree-bind proc))
       (index (erl-val-integer->val (omap::lookup 'Index bind)))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids bind)))
       (parent (omap::lookup 'Parent bind)))
    (and (check-children pid children net)
         (check-parent pid parent net)
         (check-indices index children net)
         (or (leaf-p proc)
             (b* ((rpid (rightmost-child pid net)))
               (and rpid
                    (equal (erl-val-integer->val
                             (omap::lookup 'Index
                               (wtree-bind (omap::lookup rpid net))))
                           (- (omap::size net) 1)))))))
  ///
    (defcong pid-equiv equal (wtree-node-p pid net) 1)
    (defcong network-equiv equal (wtree-node-p pid net) 2))

; Every node of net is well formed in net0 (the original network).
(define wtree0-p ((net network-p) (net0 network-p))
  :returns (r booleanp)
  :measure (acl2-count (network-fix net))
  (b* ((net (network-fix net))
       (net0 (network-fix net0))
       ((if (omap::emptyp net)) t))
    (and (wtree-node-p (omap::head-key net) net0)
         (wtree0-p (omap::tail net) net0)))
  ///
    (defcong network-equiv equal (wtree0-p net net0) 1)
    (defcong network-equiv equal (wtree0-p net net0) 2)

    (defrule wtree-node-p-when-wtree0-p
      (implies (and (wtree0-p net net0) (network-p net) (omap::assoc pid net))
               (wtree-node-p pid net0)))

    (defrule wtree0-p-when-subset-of-keys
      (implies
        (and (network-p net1) (network-p net) (wtree0-p net1 net0)
             (set::subset (omap::keys net) (omap::keys net1)))
        (wtree0-p net net0))
      :induct (wtree0-p net net0)))

; Every node of net is well formed in net.
(define wtree-p ((net network-p))
  :returns (r booleanp)
  (wtree0-p net net)
  ///
    (defcong network-equiv equal (wtree-p net) 1)

    (defrule wtree-node-p-when-wtree-p
      (implies (and (wtree-p net) (network-p net) (omap::assoc pid net))
               (wtree-node-p pid net))))

; Properties of the Nodes of a Wtree -------------------------------------------

(defrule wtree-nodes-are-leaf-or-root
  (implies
    (and (wtree-p net) (network-p net) (omap::assoc pid net))
    (or (leaf-p (omap::lookup pid net))
        (root-p (omap::lookup pid net))))
  :use wtree-node-p-when-wtree-p
  :enable wtree-node-p)

; The parent of a node is an erl-value.
(defrule erl-val-p-of-parent-of-wtree-node
  (implies
    (and (network-p net) (wtree-p net) (omap::assoc pid net))
    (erl-val-p (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))))
  :use wtree-nodes-are-leaf-or-root
  :disable wtree-nodes-are-leaf-or-root
  :enable (leaf-p root-p wtree-node0-p))

(defrule check-children-of-wtree-node
  (implies
    (and (network-p net) (wtree-p net) (omap::assoc pid net))
    (check-children pid
      (erl-val-cons->lst
        (omap::lookup 'ChildPids (wtree-bind (omap::lookup pid net))))
      net))
  :use wtree-node-p-when-wtree-p
  :enable wtree-node-p)

(defrule check-parent-of-wtree-p
  (implies
    (and (network-p net) (wtree-p net) (omap::assoc pid net))
    (check-parent pid
      (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
      net))
  :use wtree-node-p-when-wtree-p
  :enable wtree-node-p)

(defrule check-indices-of-wtree-node
  (implies
    (and (network-p net) (wtree-p net) (omap::assoc pid net))
    (check-indices
      (erl-val-integer->val
        (omap::lookup 'Index (wtree-bind (omap::lookup pid net))))
      (erl-val-cons->lst
        (omap::lookup 'ChildPids (wtree-bind (omap::lookup pid net))))
      net))
  :use wtree-node-p-when-wtree-p
  :enable wtree-node-p)

(defrule rightmost-child-of-wtree-root
  (implies
    (and (network-p net) (wtree-p net) (omap::assoc pid net)
         (root-p (omap::lookup pid net)))
    (rightmost-child pid net))
  :use wtree-node-p-when-wtree-p
  :enable wtree-node-p)

(defrule parent-not-self-of-wtree
  (implies
    (and (network-p net) (wtree-p net) (omap::assoc pid net))
    (not (equal (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
                pid)))
  :enable check-parent
  :disable check-parent-of-wtree-p
  :use check-parent-of-wtree-p)

; Rightmost Child of a Wtree Node ----------------------------------------------

; A suffix of a list without duplicates has no duplicates.
(defruled no-duplicatesp-of-suffix
  (implies (and (prefixp (rev x) (rev y)) (no-duplicatesp-equal y))
           (no-duplicatesp-equal x))
  :use ((:instance no-duplicatesp-of-prefix (x (rev x)) (y (rev y))))
  :disable no-duplicatesp-of-prefix
  :prep-lemmas
    ((defrule member-of-rev
       (iff (member-equal e (rev l)) (member-equal e l))
       :enable rev)
     (defrule no-duplicatesp-of-append-singleton
       (equal (no-duplicatesp-equal (append x (list a)))
              (and (no-duplicatesp-equal x) (not (member-equal a x)))))
     (defrule no-duplicatesp-of-rev
       (equal (no-duplicatesp-equal (rev l)) (no-duplicatesp-equal l))
       :enable rev)
     (defrule member-of-prefix
       (implies (and (prefixp x y) (member-equal e x)) (member-equal e y))
       :enable prefixp)
     (defruled no-duplicatesp-of-prefix
       (implies (and (prefixp x y) (no-duplicatesp-equal y))
                (no-duplicatesp-equal x))
       :enable prefixp)))

; the second child comes right after the rightmost child of the first one.
(defruled check-indices-next-child
  (implies
    (and (network-p net) (pid-lst-p children) (pid-lst-p cps)
         (consp (cdr cps))
         (prefixp (rev cps) (rev children))
         (check-indices i children net))
    (and (omap::assoc (car cps) net)
         (leaf-p (omap::lookup (car cps) net))
         (rightmost-child (car cps) net)
         (omap::assoc (cadr cps) net)
         (leaf-p (omap::lookup (cadr cps) net))
         (equal (erl-val-integer->val
                  (omap::lookup 'Index
                    (wtree-bind (omap::lookup (cadr cps) net))))
                (+ 1 (erl-val-integer->val
                       (omap::lookup 'Index
                         (wtree-bind
                           (omap::lookup (rightmost-child (car cps) net)
                                         net))))))))
  :expand ((:free (i) (check-indices i cps net))
           (:free (i) (check-indices i (cdr cps) net)))
  :use (check-indices-of-cdr
        (:instance node-p-of-rightmost-child (pid (car cps)))))

(defruled rightmost-child-when-member-of-check-indices
  (implies (and (network-p net) (pid-lst-p cps) (member-equal cpid cps)
                (check-indices i cps net))
           (rightmost-child cpid net))
  :induct (check-indices i cps net)
  :enable check-indices)

; Every node of a worker tree has a rightmost child.
(defruled rightmost-child-of-wtree-node
  (implies (and (network-p net) (wtree-p net) (omap::assoc pid net))
           (rightmost-child pid net))
  :enable check-parent
  :disable (wtree-nodes-are-leaf-or-root check-parent-of-wtree-p
            check-indices-of-wtree-node)
  :use ((:instance wtree-nodes-are-leaf-or-root)
        (:instance check-parent-of-wtree-p)
        (:instance check-indices-of-wtree-node
          (pid (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))))
        (:instance rightmost-child-when-member-of-check-indices
          (cpid pid)
          (cps (erl-val-cons->lst
                 (omap::lookup 'ChildPids
                   (wtree-bind
                     (omap::lookup
                       (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
                       net)))))
          (i (erl-val-integer->val
               (omap::lookup 'Index
                 (wtree-bind
                   (omap::lookup
                     (omap::lookup 'Parent (wtree-bind (omap::lookup pid net)))
                     net))))))))

; The rightmost child of a node is the rightmost child of its last child.
(defruled rightmost-child-of-last-child
  (implies
    (and (network-p net) (wtree-p net) (omap::assoc p net)
         (consp (erl-val-cons->lst
                  (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net)))))
         (omap::assoc
           (car (last (erl-val-cons->lst
                        (omap::lookup 'ChildPids
                          (wtree-bind (omap::lookup p net))))))
           net)
         (leaf-p
           (omap::lookup
             (car (last (erl-val-cons->lst
                          (omap::lookup 'ChildPids
                            (wtree-bind (omap::lookup p net))))))
             net)))
    (equal (rightmost-child
             (car (last (erl-val-cons->lst
                          (omap::lookup 'ChildPids
                            (wtree-bind (omap::lookup p net))))))
             net)
           (rightmost-child p net)))
  :enable rightmost-child
  :expand ((rightmost-child0 p net (omap::size net)))
  :use ((:instance rightmost-child-of-wtree-node (pid p))
        (:instance increase-fuel-of-rightmost-child0
          (pid (car (last (erl-val-cons->lst
                            (omap::lookup 'ChildPids
                              (wtree-bind (omap::lookup p net)))))))
          (f1 (- (omap::size net) 1)) (f2 (omap::size net)))))

; Updating a Wtree -------------------------------------------------------------

(defrule wtree-node-p-of-update-equal-fields
  (implies
    (and (network-p net) (network-p (omap::update pid proc net))
         (omap::assoc pid net) (pid-p p)
         (equal (wtree-fields proc) (wtree-fields (omap::lookup pid net))))
    (equal (wtree-node-p p (omap::update pid proc net))
           (wtree-node-p p net)))
  :enable wtree-node-p)

(defrule wtree0-p-of-update-equal-fields
  (implies
    (and (network-p net0) (network-p (omap::update pid proc net0))
         (network-p net) (omap::assoc pid net0)
         (equal (wtree-fields proc) (wtree-fields (omap::lookup pid net0))))
    (equal (wtree0-p net (omap::update pid proc net0))
           (wtree0-p net net0)))
  :enable wtree0-p)

(defrule wtree-p-of-update-equal-fields
  (implies
    (and (network-p net) (network-p (omap::update pid proc net))
         (omap::assoc pid net)
         (equal (wtree-fields proc) (wtree-fields (omap::lookup pid net))))
    (equal (wtree-p (omap::update pid proc net))
           (wtree-p net)))
  :enable (wtree-p omap::in-of-keys-to-assoc)
  :use ((:instance wtree0-p-when-subset-of-keys
          (net1 net) (net (omap::update pid proc net))
          (net0 (omap::update pid proc net)))
        (:instance wtree0-p-when-subset-of-keys
          (net1 (omap::update pid proc net)) (net net) (net0 net))))
          

; TODO: This is a temporary solution for a proof in run.lisp.
(defruled wtree-node-props
  (b* ((wbind (wtree-bind (omap::lookup p net)))
       (parent (omap::lookup 'Parent wbind))
       (index (erl-val-integer->val (omap::lookup 'Index wbind)))
       (children (erl-val-cons->lst (omap::lookup 'ChildPids wbind)))
       (chd (car children)))
    (implies
      (and (network-p net) (wtree-p net) (pid-p p) (omap::assoc p net)
           (omap::assoc pid net))
      (and
        (or (pid-p parent) (equal parent (make-erl-val-atom :val 'none)))
        (not (equal parent p))
        (natp index)
        (pid-lst-p children)
        (implies (consp children)
          (and (omap::assoc chd net)
               (not (equal chd p))
               (leaf-p (omap::lookup chd net))
               (equal (erl-val-integer->val
                        (omap::lookup 'Index (wtree-bind (omap::lookup chd net))))
                      (+ 1 index))))
        (or (not (equal (omap::lookup 'Parent (wtree-bind (omap::lookup pid net))) p))
            (member-equal pid children)))))
  :enable check-parent
  :disable (wtree-nodes-are-leaf-or-root check-parent-of-wtree-p
            check-indices-of-wtree-node check-children-of-wtree-node)
  :expand
    ((:free (i n)
      (check-indices i
        (erl-val-cons->lst (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net)))) n))
     (:free (n)
      (check-children p
        (erl-val-cons->lst (omap::lookup 'ChildPids (wtree-bind (omap::lookup p net)))) n)))
  :use ((:instance wtree-nodes-are-leaf-or-root (pid p))
        (:instance check-parent-of-wtree-p)
        (:instance check-indices-of-wtree-node (pid p))
        (:instance check-children-of-wtree-node (pid p))
        (:instance parent-not-self-of-wtree
          (pid (car (erl-val-cons->lst
                      (omap::lookup 'ChildPids
                        (wtree-bind (omap::lookup p net)))))))))