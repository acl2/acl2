(in-package "ACL2")
(include-book "acl2s/cgen/top" :dir :system :ttags :all)
(include-book "dsp-defuns" :ttags :all)
;(include-book "dsp-defthms" :ttags :all)


;DEFDATA types

;NOTE: fix vertex to be a bounded set (len = 124) of names that are easy to read
(defdata vertex
  (enum '(a u v w x y z
            u1 u2 v1 v2 w1 w2 x1 x2 y1 y2 z1 z2
            u3 u4 u5 v3 v4 v5 w3 w4 w5 w3 w4 w5 x3 x4 x5 y3 y4 y5 z3 z4 z5
            u6 u7 u8 u9 v6 v7 v8 v9 w6 w7 w8 w9 x6 x7 x8 x9 y6 y7 y8 y9 z6 z7 z8 z9
            a b c d e f g h i j k l m n o p q r s t0
            a1 b1 c1 d1 e1 f1 g1 h1 i1 j1 k1 l1 m1 n1 o1 p1 q1 r1 s1 t1
            a2 b2 c2 d2 e2 f2 g2 h2 i2 j2 k2 l2 m2 n2 o2 p2 q2 r2 s2 t2)))

(defdata source-vertex 'A)
(in-theory (disable vertexp source-vertexp))

(set-verify-guards-eagerness 0)

(defdata edge-list/e (alistof vertex acl2s::positive-rational))
(defdata edge-list>0/e (cons (cons vertex acl2s::positive-rational) edge-list/e))
(defdata edge-list>1/e (cons (cons vertex acl2s::positive-rational) edge-list>0/e))
(defdata edge-list>2/e (cons (cons vertex acl2s::positive-rational) edge-list>1/e))

(defun remove-duplicate-entries (alist)
  (declare (xargs :guard (alistp alist)))
  (if (endp alist)
      '()
    (if (assoc-equal (caar alist) (cdr alist))
        (remove-duplicate-entries (cdr alist))
      (cons (car alist)
            (remove-duplicate-entries (cdr alist))))))

;custom enumerator for edge-listp. give more weight to more edges
(defun edge-list-enum (n)
  (b* (((mv i ?x) (defdata::weighted-switch-nat '(1 2 4 8) n))
       (E (case i
                (0 (nth-edge-list/e n))
                (1 (nth-edge-list>0/e n))
                (2 (nth-edge-list>1/e n))
                (t (nth-edge-list>2/e n)))))
      (remove-duplicate-entries E)))

(defun edge-list-enum2 (n seed.)
  (b* (((mv i ?x) (defdata::weighted-switch-nat '(1 2 4 8) n))
      ((mv x seed.) (case i
                          (0 (nth-edge-list/e/acc n seed.))
                          (1 (nth-edge-list>0/e/acc n seed.))
                          (2 (nth-edge-list>1/e/acc n seed.))
                          (t (nth-edge-list>2/e/acc n seed.)))))

      (mv (remove-duplicate-entries x) seed.)))

;Register the enumerator for edge-list
(defdata::register-type edge-list
  :predicate edge-listp
  :enumerator edge-list-enum
  :enum/acc   edge-list-enum2)

(defdata graph0/e (alistof vertex edge-list))
(defdata graph/e (cons (cons source-vertex edge-list) graph0/e))

;register graph predicate with Cgen
(defdata::register-type G :predicate graphp
               :enumerator nth-graph/e
               :enum/acc nth-graph/e/acc)


(defdata vertex-list0 (listof vertex))
(defdata vertex-list>0 (cons vertex vertex-list0)) ; using vertex-list causes
                                                   ; cycle in the
                                                   ; defdata-attach below

;try to create vertex lists that have no duplicates
(defun vertex-list/e (n)
  (declare (xargs :mode :program))
  (b* ((x (nth-vertex-list>0-builtin n)))
      (if (= 0 (mod n 8))
        x
        (remove-duplicates x))))

(defun vertex-list/e/acc (n seed.)
  (declare (xargs :mode :program))
  (b* (((mv x seed.) (nth-vertex-list>0/acc-builtin n seed.)))
      (if (= 0 (mod n 5))
        (mv (add-to-set 'A x) seed.) ;sometimes add source vertex.
        (mv (remove-duplicates x) seed.)))) ;most of the time remove dups

(defdata vertex-list (listof vertex))
(acl2s::defdata-attach vertex-list :enumerator vertex-list/e)
(acl2s::defdata-attach vertex-list :enum/acc vertex-list/e/acc)


(defdata vertex-path-alist>0 (oneof (acons vertex vertex-list nil)
                                    (acons vertex vertex-list
                                           (acons vertex vertex-list nil))
                                    (acons vertex vertex-list vertex-path-alist>0)))

(defun remove-empty-entries (alist)
  (declare (xargs :guard (alistp alist)))
  (if (endp alist)
      '()
      (b* (((cons & val) (car alist)))
          (if (null val)
            (remove-empty-entries (cdr alist))
            (cons (car alist)
                  (remove-empty-entries (cdr alist)))))))

;try to create non-empty vertex-path-alist with non-empty paths and no duplicates
(defun vertex-path-alist/e (n)
  (declare (xargs :mode :program))
  (b* ((x (nth-vertex-path-alist>0-builtin n)))
      (remove-duplicate-entries (remove-empty-entries x))))

(defun vertex-path-alist/e/acc (n seed.)
  (declare (xargs :mode :program))
  (b* (((mv x seed.) (nth-vertex-path-alist>0/acc-builtin n seed.)))
      (mv (remove-duplicate-entries (remove-empty-entries x)) seed.)))

(defdata vertex-path-alist (alistof vertex vertex-list))
(acl2s::defdata-attach vertex-path-alist :enumerator vertex-path-alist/e)
(acl2s::defdata-attach vertex-path-alist :enum/acc vertex-path-alist/e/acc)


;FIXER functions

(defun tlp-fix (L)
  (declare (xargs :guard t))
  (if (atom L)
      nil
    (cons (car L) (tlp-fix (cdr L)))))

(defun del-fx2 (a L1 L)
  (if (equal L1 (del a L))
      L
    (cons a L1)))

(defun memp-fx1 (x L)
  (if (memp x L)
      x
    (b* ((n (len L))
         ;;(i (acl2-count x))
         ((unless (>= n 1)) x) ;return unchanged if impossible to satisfy memp
         (i (nfix (position x *vertex-values*))) ;specific to vertices
         (i (mod i n)))
      (nth i L))))

(defun memp-fx2 (a L)
  (if (memp a L)
      L
    (cons a L)))

(defun setp-fx (s)
  (remove-duplicates-equal (tlp-fix s)))



(defun my-subsetp-fx1 (X1 X2) ;only as good as X1, if X1 is null then it always returns nil
  (if (endp X1)
      '()
    (if (memp (car X1) X2)
        (cons (car X1) (my-subsetp-fx1 (cdr X1) X2))
      (my-subsetp-fx1 (cdr X1) X2))))

;Auxiliary function
(defun strip-non-empty-keys (alist)
  (if (endp alist)
    nil
    (b* (((cons key val) (car alist)))
        (if (null val)
          (strip-non-empty-keys (cdr alist))
          (cons key (strip-non-empty-keys (cdr alist)))))))

; this is not a good fixer. because it does not have good coverage, no
; variability. since n is used for variating, and (acl2-count symbol) is always
; 0, so two nodep calls, that are both unsatisfied, always give the same fixed
; node and this leads to skewed test data generation.
; (defun node-fx (n g) (memp-fx1 n (all-nodes g)))
; Also make it thrice more likely to return a node with neighbors, so that
; there is more chances of paths starting from x


(defun node-fx1 (x g)
  (if (nodep x g)
      x
    (b* ((vs (all-nodes g))
         (nodes-with-neighbors (strip-non-empty-keys g)) ;remove source vertex??
         (i (nfix (position x *vertex-values*)))
         ((when (null nodes-with-neighbors))
          (nth (mod i (len vs)) vs))
         ((mv choice &) (defdata::weighted-switch-nat '(4 1) i)))
        (case choice
              (0 (nth (mod i (len nodes-with-neighbors)) nodes-with-neighbors))
              (t (nth (mod i (len vs)) vs))))))



#|
(defun node-fx2 (x g)
; BAD fixer : does not have good variability. and especially it returns nodes
; with zero neighbors
  (if (nodep x g)
      g
    (add-node x g)))
|#

(defun node-fx2 (x g)
  (if (nodep x g)
      g
    (b* ((us (strip-non-empty-keys g))
         ((when (null us)) (put-assoc-equal x nil g))
         (i (nfix (position x *vertex-values*))) ;i acts as random seed
         (nbrs (take (mod i (len us)) us)) ;tend to more paths in g
         (nbrs (remove1 'A (remove-duplicates-eq nbrs))) ;remove source
         (edges (pairlis$ nbrs (make-list (len nbrs) :initial-element 1))))
        (put-assoc-equal x edges g))))

(defun path-non-empty-fix (u vs pt)
  (if (path u pt)
    pt
    (put-assoc-equal u (cons 'A (append vs (list u))) pt))) ;add source vertex


(progn ;Auxiliary functions for fixers and for instantiating defun-sk
  (defun count-non-members (x y)
   (cond ((endp x) 0)
         ((member (car x) y) (count-non-members (cdr x) y))
         (t (+ 1 (count-non-members (cdr x) y)))))

(defun measure (c stack g)
   (cons (+ 1 (count-non-members (strip-cars g) stack))
         (len c)))

(defun neighbors2 (node g)
  (cond ((endp g) nil)
        ((equal node (car (car g))) (cdr (car g)))
        (t (neighbors2 node (cdr g)))))

(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)
(in-theory (enable strip-cars))

(defun find-all-next-steps (c stack b g)
    (declare (xargs :measure (measure c stack g)))
    (cond
     ((endp c) nil)
     ((member (car c) stack)
      (find-all-next-steps (cdr c) stack b g))
     ((equal (car c) b)
      (cons (reverse (cons b stack))
            (find-all-next-steps (cdr c) stack b g)))
     (t (append (find-all-next-steps (neighbors2 (car c) g)
                                     (cons (car c) stack)
                                     b g)
                (find-all-next-steps (cdr c) stack b g)))))

(defun change-rep (vs g)
  ;remove weights and also add empty entries for non-neighbour vertices
  (if (endp vs)
    g
    (b* ((entry (assoc-equal (car vs) g))
         ((when (null entry)) (change-rep (cdr vs) (put-assoc-equal (car vs) nil g)))
         (edges-with-weights (cdr entry))
         (edges (strip-cars edges-with-weights)))
        (change-rep (cdr vs) (put-assoc-equal (car vs) edges g)))))

(defun find-all-simple-paths (a b g)
  (if (and (equal a b) (nodep a g)) ; added for type-safety and less-restrictive fixer rules
    (list (list a))
    (b* ((g1 (change-rep (all-nodes g) g)))
        (find-all-next-steps (neighbors2 a g1) ;(neighbors a g1) bug
                             (list a) b g1))))
)

(memoize 'find-all-simple-paths :ideal-okp t)

;fixer for pathp-from-to UNUSED
(defun path-from-to-fix1 (p a b g)
  (if (pathp-from-to p a b g)
    p
  (b* ((paths (find-all-simple-paths a b g))
       (n (len paths))
       ((when (zp n)) nil)
       (i (mod (acl2-count p) n)))
      (nth i paths))))

;Auxiliary function
(defun add-edge (a b wt g)
  (b* ((es (cdr (assoc-equal a g)))
       (es1 (put-assoc-equal b wt es)))
      (put-assoc-equal a es1 g)))
;Auxiliary function
(defun add-path/wts (p wts g); assume all of p are nodes in g
  (if (endp p)
    g
    (if (endp (cdr p))
      g
      (add-path/wts (cdr p) (cdr wts)
                (add-edge (car p) (cadr p) (car wts) g)))))
;Auxiliary function
(defun add-path (p g)
  (add-path/wts p (make-list (len p) :initial-element 1) g))

;Auxiliary function
(defun add-path-from-to (p a b g)
  (b* ((p (cons a (cdr p)))
       (p (if (consp (cdr p))
              (append (butlast p 1) (list b))
            (append p (list b))))
       (g (node-fx2 a g)) ;make sure a,b are in g
       (g (node-fx2 b g)))
    (mv p (add-path p g))))

(defund path-from-to-fix (p a b g)
  (if (pathp-from-to p a b g)
    (mv p g)
    (b* ((paths (find-all-simple-paths a b g))
         (n (len paths))
         ((when (zp n)) (add-path-from-to p a b g))
         (i (mod (acl2-count p) n)))
      (mv (nth i paths) g))))



(defund pathp-fx (P g)
  (if (pathp P g)
    (mv P g)
    (if (endp P)
        (mv (list (node-fx1 'u g)) g)
      (if (endp (cdr P))
          (mv (list (node-fx1 (car P) g)) g)
        (path-from-to-fix P (car P) (car (last P)) g)))))

(defund pt-propertyp-fix2 (a pt g)
  (if (endp pt)
      (mv '() g)
    (b* (((cons v path) (first pt))
         ;;(v (node-fx1 v g))
         (g (node-fx2 v g)) ;this is better because it avoid duplicate entries for small graphs
         ((mv path g) (path-from-to-fix path a v g))
         ((mv rest-pt-fixed g) (pt-propertyp-fix2 a (rest pt) g)))
      (mv (cons (cons v path) rest-pt-fixed) g))))

;Auxiliary function
(defun pick-shortest (paths g p)
  (if (endp paths)
      p
    (if (shorterp p (car paths) g)
        (pick-shortest (cdr paths) g p)
      (pick-shortest (cdr paths) g (car paths)))))

;Auxiliary function
(u::defloop confinedp-lst (paths fs)
            (for ((p in paths)) (append (and (confinedp p fs) (list p)))))

; nested fixers help fix multiple constraints at one go.  too complicated,
; changes the graph and the whole gamut of shortest path for various nodes
; changes and invariants about them are hard to keep
(defund shortest-confined-path-fxr2 (a b p fs g)
  (b* (((mv p g) (path-from-to-fix p a b g)))
      (mv (pick-shortest (confinedp-lst (find-all-simple-paths a b g) fs) g p) g)))

;just go with simpler
(defund shortest-confined-path-fxr (a b p fs g)
  (let ((p0 (pick-shortest (confinedp-lst (find-all-simple-paths a b g) fs) g p)))
    (if (shorterp p p0 g) p p0)))


(defund shortest-path-fxr2 (a b p g) ;dont use
  (b* (((mv p g) (path-from-to-fix p a b g)))
      ;lets add paths that might be shorter
      (mv (pick-shortest (find-all-simple-paths a b g) g p) g)))

;use simpler
(defund shortest-path-fxr (a b p g) ;used in fs-propertyp-fix1
  (let ((p0 (pick-shortest (find-all-simple-paths a b g) g nil)))
    (if (shorterp p p0 g) p p0)))

;Auxiliary function
(defun delete-all-assoc (key alist)
  (if (endp alist)
    nil
    (if (equal (caar alist) key)
      (delete-all-assoc key (cdr alist))
      (cons (car alist) (delete-all-assoc key (cdr alist))))))

(defund ts-propertyp-fix (a ts fs pt g)
  (if (endp ts)
      pt
    (b* ((p (path (car ts) pt))
         (p (shortest-confined-path-fxr a (car ts) p fs g))
         ((unless (confinedp p fs))
          (ts-propertyp-fix a (cdr ts) fs (delete-all-assoc (car ts) pt) g)) ;bug: remove1-assoc
         ;;update pt with this "fixed" confined path
         (pt (put-assoc-equal (car ts) p pt)))
      (ts-propertyp-fix a (cdr ts) fs pt g))))

;Auxiliary function
(defun delete-edges-to (b g)
; delete edges to b
  (if (endp g)
    '()
    (b* (((cons u edges) (car g))
         (edges~ (remove1-assoc-equal b edges)))
        (cons (cons u edges~)
              (delete-edges-to b (cdr g))))))
;Auxiliary
(defun delete-edges-to-but-keep-node (b g)
;but but make sure to add b as a node. This makes sure that
; (all-nodes g) is invariant
  (if (assoc-eq b g)
      (delete-edges-to b g)
    (delete-edges-to b (put-assoc-equal b '() g))))

;Auxiliary function
(defun remove-non-paths (pt g) ;ideally one should replace non-paths with alternative paths
  (if (endp pt)
    '()
    (if (pathp (CDAR PT) g)
      (cons (car pt) (remove-non-paths (cdr pt) g))
      (remove-non-paths (cdr pt) g))))

;invp has no fs0, so cannot use fs0 as a output
;the recommended fixer for fs-propertyp. But this is a non-monotonic change to g. Deletes stuff
(defund fs-propertyp-fix3 (a fs fs0 pt g)
  (if (endp fs)
      (mv pt g)
    (b* ((p (path (car fs) pt))
         (p (shortest-path-fxr a (car fs) p g))
          ((unless (confinedp p fs0))
           (b* ((g1 (delete-edges-to-but-keep-node (car fs) g))
                ;phew!! fix failed fixer rule (hyp pt-propertyp was not preserved) bugfix
                (pt1 (remove-non-paths pt g1)))
               (fs-propertyp-fix3 a (cdr fs) fs0 (delete-all-assoc (car fs) pt1) g1)))
         (pt (put-assoc-equal (car fs) p pt)))
      (fs-propertyp-fix3 a (cdr fs) fs0 pt g))))

(defund invp-fx (ts pt g a) ;fixes all three invariants
  (b* (((mv pt g) (pt-propertyp-fix2 a pt g))
       (fs (comp-set ts (all-nodes g)))

       (pt (ts-propertyp-fix a ts fs pt g))

       ((mv pt g) (fs-propertyp-fix3 a fs fs pt g))
       ((mv pt g) (fs-propertyp-fix3 a fs fs pt g)) ;twice!!
       )
    (mv pt g)))
