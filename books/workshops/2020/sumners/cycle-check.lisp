; Copyright (C) 2020, Rob Sumners
; Written by Rob Sumners
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;; cycle-check.lisp

(in-package "ACL2")

(include-book "std/top" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "centaur/misc/fast-alist-pop" :dir :system)

; Matt K. mod: On 8/16/2020, there were three successive failed attempts to
; certify this book in ACL2(p) with waterfall-parallelism enabled.  All
; failures seemed to be abrupt, and had no explanation.  An attempt to LD this
; file then succeeded; nevertheless, it seems simplest to disable
; waterfall-parallelism at this time to avoid ACL2(p) regression failures.
; Perhaps someone will look into this if it's important.
(set-waterfall-parallelism nil)

(set-slow-alist-action :break)

(defmacro nats-o (&rest x)
  (if (atom x) 0 `(make-ord ,(len x) ,(first x) (nats-o ,@(rest x)))))

(define assoc-hons-equal (e (x alistp))
  (cond ((endp x) nil)
        ((hons-equal e (caar x)) (car x))
        (t (assoc-hons-equal e (cdr x))))
  ///
  (defthm assoc-hons-equal-is-assoc
    (equal (assoc-hons-equal e x) (assoc e x))))

(define fast-alist-free-list (x)
  (if (atom x) ()
    (b* ((- (fast-alist-free (first x))))
      (fast-alist-free-list (rest x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; GRAPH datatypes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; checking wheher or not a given ordering "ord" is
;; decreasing or not from node src to node dest, should
;; return:
;;     :<< -- strictly decreasing
;;     t   -- possibly decreasing
;;     nil -- possibly increasing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ord-tag-p (x)
  (or (eq x t) (eq x nil) (eq x :<<)))

(define ord-tag-fix (x)
  :enabled t
  :inline t
  (if (ord-tag-p x) x t))

(fty::deffixtype ord-tag
  :pred  ord-tag-p
  :fix   ord-tag-fix
  :equiv ord-tag-equiv
  :define t)

;;;;

(define ord-p (x)
  ;; we use an ord-p predicate to ensure "type checking"
  ;; in our code below, but orders could be anything..
  ;; but they can't be nil (we need an option type for clarity..)
  :enabled t
  (if x t nil))

(define ord-fix (x)
  :enabled t
  :inline t
  (if x x t))

(fty::deffixtype ord
  :pred  ord-p
  :fix   ord-fix
  :equiv ord-equiv
  :define t)

(define ord= ((x ord-p) (y ord-p))
  :inline t
  (hons-equal x y))

;;;;

(define node-p (x)
  ;; we use a node-p predicate to ensure "type checking"
  ;; in our code below, but nodes could be anything..
  (declare (ignore x))
  t)

(define node-fix (x)
  :enabled t
  :inline t
  x)

(local (defthm node-fix-open
         (equal (node-fix x) x)
         :hints (("Goal" :in-theory (enable node-fix)))))

(fty::deffixtype node
  :pred  node-p
  :fix   node-fix
  :equiv node-equiv
  :define t)

(define node= ((x node-p) (y node-p))
  :inline t
  (hons-equal x y))

;;;;

(fty::defprod arc-descr
  ((src  node-p)
   (dest node-p)
   (ord  ord-p)))

(fty::defoption maybe-arc-descr arc-descr)

;;;;

(define w-ord-p (x)
  :enabled t
  (or (natp x) (ord-p x)))

(define w-ord-fix ((x w-ord-p))
  :enabled t
  :inline t
  (mbe :logic (if (w-ord-p x) x 0) :exec x))

(fty::deffixtype w-ord
  :pred  w-ord-p
  :fix   w-ord-fix
  :equiv w-ord-equiv
  :define t)

(fty::deflist arcs
  :elt-type node-p
  :true-listp t)

(fty::defalist graph
  :key-type node-p
  :val-type arcs-p
  :short "a mapping of nodes to a list of arcs defining the graph.. usually fast-alist"
  :true-listp t)

(fty::deflist graph-lst
   :elt-type graph-p
   :true-listp t)

(fty::defalist nmap
  :key-type node-p
  :val-type any-p
  :short "a mapping from nodes in a graph to .. something.. usually fast-alist"
  :true-listp t)

(fty::defalist gmap
  :key-type node-p
  :val-type graph-p
  :short "a mapping from nodes in a graph to other graphs (usually subgraphs)"
  :true-listp t)

(fty::deflist w-ord-lst
   :elt-type w-ord-p
   :true-listp t)

(fty::deflist ord-list
   :elt-type ord-p
   :true-listp t)

(fty::defoption maybe-ord ord-p)

(fty::defalist omap
  :key-type node-p
  :val-type w-ord-lst-p
  :short "a mapping from nodes in a graph to a w-ord list defining a well-order"
  :true-listp t)

(defmacro make-alist-thms (al-type val-type)
  `(progn
     (defthm ,(intern-in-package-of-symbol
               (str::cat (symbol-name al-type) "-IS-ALISTP")
               al-type)
       (implies (,al-type x) (alistp x))
       :hints (("Goal" :in-theory (enable ,al-type))))
     ,@(and val-type
            `((defthm ,(intern-in-package-of-symbol
                        (str::cat (symbol-name al-type) "-ASSOC-EQUAL")
                        al-type)
                (implies (and (,al-type x)
                              (assoc-equal a x))
                         (,val-type (cdr (assoc-equal a x))))
                :hints (("Goal" :in-theory (enable ,al-type))))))))

(make-alist-thms nmap-p  nil)
(make-alist-thms graph-p arcs-p)
(make-alist-thms gmap-p  graph-p)
(make-alist-thms omap-p  w-ord-lst-p)

(defthm graph-p-is-nmap-p
  (implies (graph-p x) (nmap-p x))
  :hints (("Goal" :in-theory (enable graph-p nmap-p))))

(defthm gmap-p-is-nmap-p
  (implies (gmap-p x) (nmap-p x))
  :hints (("Goal" :in-theory (enable gmap-p nmap-p))))

(defthm omap-p-is-nmap-p
  (implies (omap-p x) (nmap-p x))
  :hints (("Goal" :in-theory (enable omap-p nmap-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; GRAPH access/update
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define in-arcs ((e node-p) (x arcs-p))
  (and (not (endp x)) (or (node= e (first x)) (in-arcs e (rest x)))))

(define arcs-add ((e node-p) (x arcs-p))
  :enabled t
  :inline t
  :returns (r arcs-p)
  (arcs-fix (cons e x)))

(define graph-get ((e node-p) (x graph-p))
  :enabled t
  :inline t
  (hons-get e x))

(define graph-set ((e node-p) (v arcs-p) (x graph-p))
  :enabled t
  :inline t
  :returns (r graph-p)
  (graph-fix (hons-acons e v x)))

(define nmap-get ((e node-p) (x nmap-p))
  :enabled t
  :inline t
  (hons-get e x))

(define nmap-set ((e node-p) v (x nmap-p))
  :enabled t
  :inline t
  :returns (r nmap-p :hyp :guard)
  (hons-acons e v x))

(define nmap-push ((n node-p) (x nmap-p))
  :enabled t
  :inline t
  :returns (r nmap-p :hyp :guard)
  (hons-acons n t x))

(define nmap-pop ((x nmap-p))
  :enabled t
  :inline t
  :guard (not (hons-assoc-equal (caar x) (cdr x)))
  :returns (r nmap-p :hyp :guard)
  (fast-alist-pop x))

(encapsulate
 (((check-ord-arc * * *) => *
   :formals (src dst ord)
   :guard (and (node-p src) (node-p dst) (ord-p ord))))

 (local
  (define check-ord-arc ((src node-p) (dst node-p) (ord ord-p))
    :enabled t
    (declare (ignore src dst ord))
    t))

 (defthm check-ord-arc-returns-ord-tag-p
   (ord-tag-p (check-ord-arc src dst ord)))
 )

(define check-ord-arc-default ((src node-p) (dst node-p) (ord ord-p))
  :enabled t
  (declare (ignore src dst ord))
  t)

(defattach check-ord-arc check-ord-arc-default)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; GRAPH empty from a given nmap (or graph) domain
;;             or range (for the nmap mapping to nodes)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define graph-empty-dom ((m nmap-p) &key ((r graph-p) '()))
  :returns (r graph-p)
  (if (endp m) (graph-fix (fast-alist-clean r))
    (graph-empty-dom (rest m)
                     :r (hons-acons (caar m) () r))))

(define graph-empty-rng ((m nmap-p) &key ((r graph-p) '()))
  :returns (r graph-p)
  (if (endp m) (graph-fix (fast-alist-clean r))
    (graph-empty-rng (rest m)
                     :r (hons-acons (cdar m) () r))))

(define graph-empty-dom-match ((m nmap-p) (n node-p) &key ((r graph-p) '()))
  :returns (r graph-p)
  (if (endp m) (graph-fix (fast-alist-clean r))
    (graph-empty-dom-match (rest m) n
                           :r (if (node= (cdar m) n)
                                  (hons-acons (caar m) () r)
                                r))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; GRAPH inversion
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-invert-arc ((src node-p) (dst node-p) (g graph-p))
  :returns (r graph-p :hyp :guard)
  (graph-set dst (arcs-add src (cdr (graph-get dst g))) g))

(define add-invert-arcs ((a arcs-p) x (g graph-p))
  :returns (r graph-p)
  (if (endp a) (graph-fix g)
    (add-invert-arcs (rest a) x
                     (add-invert-arc x (first a) g))))

(define graph-invert* ((g graph-p) (r graph-p))
  :returns (r graph-p)
  (if (endp g) (graph-fix (fast-alist-clean r))
    (graph-invert* (cdr g)
                   (add-invert-arcs (cdar g) (caar g) r))))

(define graph-invert ((g graph-p))
  :short "returns the inverted graph for input graph"
  :returns (r graph-p)
  (graph-invert* g (graph-empty-dom g)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; GRAPH computing mapped graph
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-rep-map-arc (src dst (m nmap-p) (g graph-p))
  :returns (r graph-p :hyp :guard)
  (b* ((look (nmap-get src m))
       ((when (not look))
        (raise "internal error: this should not happen: ~x0" src))
       (src-r (cdr look))
       (look (nmap-get dst m))
       ((when (not look))
        (raise "internal error: this should not happen: ~x0" src))
       (dst-r (cdr look))
       ((when (node= src-r dst-r))
        ;; BOZO -- the "abstract" graph does not include self-cycles..
        ;;         ..by intent.. probably should change name of this
        ;;         function to something other than graph-abstract
        g)
       (curr (cdr (graph-get src-r g))))
    (if (in-arcs dst-r curr) g
      (graph-set src-r (arcs-add dst-r curr) g))))

(define add-rep-map-arcs ((a arcs-p) x (m nmap-p) (g graph-p))
  :returns (r graph-p)
  (if (endp a) (graph-fix g)
    (add-rep-map-arcs (rest a) x m
                      (add-rep-map-arc x (first a) m g))))

(define graph-abstract* ((g graph-p) (m nmap-p) (r graph-p))
  :returns (r graph-p)
  (if (endp g) (graph-fix (fast-alist-clean r))
    (graph-abstract* (cdr g) m
                     (add-rep-map-arcs (cdar g) (caar g) m r))))

(define graph-abstract ((g graph-p) (m nmap-p))
  :returns (r graph-p)
  (graph-abstract* g m (graph-empty-rng m)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; GRAPH projections
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-project-arc ((src node-p) (dst node-p)
                         (m nmap-p) (n node-p) (g graph-p))
  :returns (g graph-p :hyp :guard)
  (b* ((look (nmap-get dst m))
       ((when (not look))
        (raise "internal error: this should not happen: ~x0" dst))
       ((when (not (node= (cdr look) n)))
        ;; we only include arcs between nodes which map to n
        g)
       (curr (cdr (graph-get src g))))
    (graph-set src (arcs-add dst curr) g)))

(define add-project-arcs ((a arcs-p) (src node-p) (m nmap-p) (n node-p)
                          (g graph-p))
  :returns (r graph-p)
  (if (endp a) (graph-fix g)
    (add-project-arcs (rest a) src m n
                      (add-project-arc src (first a) m n g))))

(define graph-project* ((g graph-p) (m nmap-p) (n node-p)
                        (r graph-p))
  :returns (r graph-p)
  (if (endp g) (graph-fix (fast-alist-clean r))
    (graph-project* (cdr g) m n
                    (b* ((src (caar g))
                         (look (nmap-get src m))
                         ((when (not look))
                          (raise "internal error: this should not happen: ~x0" src))
                         ((when (not (node= (cdr look) n)))
                          ;; we only include arcs between nodes which map to n
                          r))
                      (add-project-arcs (cdar g) src m n r)))))

(define graph-project ((g graph-p) (m nmap-p) (n node-p))
  :returns (r graph-p)
  (graph-project* g m n (graph-empty-dom-match m n)))

(define graph-projects* ((g graph-p) (nodes nmap-p) (m nmap-p)
                         &key ((r graph-lst-p) '()))
  :returns (r graph-lst-p)
  (if (endp nodes) (graph-lst-fix r)
    (graph-projects* g (cdr nodes) m
                     :r (cons (graph-project g m (caar nodes)) r))))

(define rep-nodes-in-map ((m nmap-p) &key ((r nmap-p) '()))
  :returns (r nmap-p)
  (if (endp m) (nmap-fix r)
    (rep-nodes-in-map (cdr m)
                      :r (if (nmap-get (cdar m) r) r
                           (nmap-set (cdar m) t r)))))

(define graph-projects ((g graph-p) (m nmap-p))
  :returns (r graph-lst-p)
  (graph-projects* g (rep-nodes-in-map m) m))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; GRAPH order searches and cuts
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-ord-arcs ((a arcs-p) (src node-p) (ord ord-p)
                        &key (seen<< 'nil))
  (if (endp a) (if seen<< :<< t)
    (b* ((x (check-ord-arc src (first a) ord)))
      (if (not x) nil
        (check-ord-arcs (rest a) src ord
                        :seen<< (or seen<< (eq x :<<)))))))

(define check-ord-pick ((g graph-p) (ord ord-p)
                        &key (seen<< 'nil))
  (if (endp g) seen<<
    (b* ((x (check-ord-arcs (cdar g) (caar g) ord)))
      (if (not x) nil
        (check-ord-pick (cdr g) ord
                        :seen<< (or seen<< (eq x :<<)))))))

(define graph-pick-ord ((g graph-p) (ords ord-list-p))
  :returns (r maybe-ord-p :hyp (ord-list-p ords))
  (if (endp ords) nil
    (b* ((ord (first ords))
         ((when (not ord))
          (raise "order measure descriptors should not be NIL!")))
      (if (check-ord-pick g ord) ord
        (graph-pick-ord g (rest ords))))))

(define check-fail-arcs ((a arcs-p) (src node-p) (ord ord-p))
  :returns (r maybe-arc-descr-p)
  (if (endp a) nil
    (or (and (not (check-ord-arc src (first a) ord))
             (make-arc-descr :src src :dest (first a) :ord ord))
        (check-fail-arcs (rest a) src ord))))

(define check-ord-fail ((g graph-p) (ord ord-p))
  :returns (r maybe-arc-descr-p)
  (if (endp g) nil
    (or (check-fail-arcs (cdar g) (caar g) ord)
        (check-ord-fail (cdr g) ord))))

(define check-ords-fail ((g graph-p) (ords ord-list-p))
  :returns (r maybe-arc-descr-p)
  (if (endp ords) nil
    (or (check-ord-fail g (first ords))
        (check-ords-fail g (rest ords)))))

(define graph-failed-ord ((g graph-p) (ords ord-list-p))
  :returns (r maybe-ord-p :hyp (ord-list-p ords))
  (if (endp ords) nil
    (b* ((ord (first ords))
         ((when (not ord))
          (raise "order measure descriptors should not be NIL!")))
      (if (check-ord-fail g ord) ord
        (graph-failed-ord g (rest ords))))))

(define arcs-cut-ord<< ((a arcs-p) (src node-p) (ord ord-p)
                        &key ((r arcs-p) '()))
  :returns (a arcs-p)
  (if (endp a) (arcs-fix r)
    (arcs-cut-ord<< (rest a) src ord
                    :r (if (eq (check-ord-arc src (first a) ord) :<<)
                           r
                         (cons (first a) r)))))

(define graph-cut-ord* ((g graph-p) (ord ord-p) (r graph-p))
  :returns (r graph-p)
  (if (endp g) (graph-fix (fast-alist-clean r))
    (graph-cut-ord* (cdr g) ord
                    (b* ((src (caar g)))
                      (hons-acons src (arcs-cut-ord<< (cdar g) src ord) r)))))

(define graph-cut-ord ((g graph-p) (ord ord-p))
  :returns (r graph-p)
  (graph-cut-ord* g ord (graph-empty-dom g)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; GRAPH depth-first-search
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define subset-nmap ((x nmap-p) (y nmap-p))
  :enabled t
  (or (endp x)
      (and (nmap-get (caar x) y)
           (subset-nmap (cdr x) y)))
  ///
  (defthm subset-nmap-transitive
    (implies (and (subset-nmap x y)
                  (subset-nmap y z))
             (subset-nmap x z)))
  (defthm subset-nmap-reflexive-generalize
    (implies (and (nmap-p x) (nmap-p y)
                  (subset-nmap x y))
             (subset-nmap x (cons (cons a b) y))))
  (defthm subset-nmap-reflexive
    (implies (nmap-p x)
             (subset-nmap x x))))

(define num-not-in ((g graph-p) (v nmap-p))
  :returns (r natp)
  (cond ((endp g) 0)
        ((nmap-get (caar g) v) (num-not-in (cdr g) v))
        (t (1+ (num-not-in (cdr g) v))))
  ///
  (defthm num-not-in-subset-nmap
    (implies (subset-nmap x y)
             (<= (num-not-in g y) (num-not-in g x)))
    :rule-classes (:linear :rewrite))
  (defthm num-not-in-cons-open
    (implies (and (hons-assoc-equal n g)
                  (not (hons-assoc-equal n v)))
             (< (num-not-in g (cons (cons n a) v))
                (num-not-in g v)))
    :rule-classes (:linear :rewrite)))

;; IMPORTANT NOTE --
;;   we define a fairly generic DFS function below and use it for three different instances:
;;
;;   1) (ord-list-p dfs-type)
;;      in this case, we are detecting a cycle starting from top and trying to reach back to
;;      top.. in this case, the nmap r is irrelevant and will start and stay nil, and the acc
;;      will be nil if it did not find a cycle or otherwise will be a list of nodes forming
;;      a path to make the cycle.
;;
;;   2) (eq dfs-type :anchor)
;;      returns an updated nmap in r where the cdr is the "anchor" which reached this node
;;      and has the property that at every point in the generated nmap, all nodes x reachable
;;      from (caar r) satisfy (assoc x (cdr r)). accumulator is not used in this case and
;;      will be :top in all calls..
;;
;;   3) (eq dfs-type :enumerate)
;;      we are generating an enumeration of the nodes and the nmap r that we are returning
;;      that will map each node to a natural number such that if node n can reach node m
;;      but not vice versa, then r(n) > r(m) -- not as useful if there are cycles..
;;
;;  we instantiate the graph-dfs-top function below based on these predicates on acc and handle
;;  updating the acc and nmap r accordingly as well as generating a new "acc" for recursive
;;  calls.. and an early termination in the case where we have found a cycle..

(define upd-acc (dfs-type (a+ natp) (acc natp))
  :returns (r natp :hyp :guard)
  (cond ((eq dfs-type :enumerate) (max a+ acc))
        (t 0)))

(define upd-rmap (dfs-type (n node-p) (a+ natp) (top node-p) (r nmap-p))
  :returns (r nmap-p :hyp (and (node-p n) (nmap-p r)))
  (cond ((eq dfs-type :enumerate)
         (nmap-set n a+ r))      ;; map it to a+ (1 more than subnodes)..
        (t (nmap-set n top r)))) ;; mapping to top to return anchor of dfs..

(defmacro new-acc () 0)  ;; just set the acc to 0 for next-level calls..

(define rev-arcs ((x arcs-p) &key ((r arcs-p) '()))
  :returns (r arcs-p)
  (if (endp x) (arcs-fix r)
    (rev-arcs (rest x) :r (cons (first x) r))))

(define member-ord ((o ord-p) (x ord-list-p))
  (and (not (endp x))
       (or (ord= o (first x))
           (member-ord o (rest x)))))

(define add-ord ((o ord-p) (x ord-list-p))
  :returns (r ord-list-p :hyp :guard)
  (if (member-ord o x) x (cons o x)))

(define subset-ords ((x ord-list-p) (y ord-list-p))
  (or (endp x)
      (and (member-ord (first x) y)
           (subset-ords (rest x) y))))

(define add-chk-ords ((ords ord-list-p) (src node-p) (dest node-p)
                      (dec ord-list-p) (inc ord-list-p))
  :returns (mv (dec ord-list-p) (inc ord-list-p))
  (if (endp ords)
      (mv (ord-list-fix dec) (ord-list-fix inc))
    (b* ((ord (first ords))
         (chk (check-ord-arc src dest ord))
         (dec (if (eq chk :<<) (add-ord ord dec) dec))
         (inc (if (not chk)    (add-ord ord inc) inc)))
      (add-chk-ords (rest ords) src dest dec inc))))

(define is-valid-bad-cyc ((path nmap-p) (ords ord-list-p)
                          &key
                          ((dec ord-list-p) '())
                          ((inc ord-list-p) '())
                          ((r arcs-p) '()))
  :returns (r arcs-p)
  (cond ((endp path)
         (raise "internal error: should have hit a cycle!"))
        ((in-arcs (caar path) r)
         (and (subset-ords dec inc) (rev-arcs r)))
        ((endp (cdr path))
         (raise "internal error: still should have hit a cycle!"))
        (t
         (b* (((mv dec inc)
               (add-chk-ords ords (caar path) (caadr path) inc dec)))
           (is-valid-bad-cyc (cdr path) ords :dec dec :inc inc
                             :r (cons (caar path) r))))))

(define graph-dfs-top ((arcs arcs-p) (top node-p) (g graph-p)
                       (acc natp)    (r nmap-p)   (v nmap-p)
                       (stk nmap-p)  dfs-type)
  :guard (or (eq dfs-type :enumerate)
             (eq dfs-type :anchor)
             (ord-list-p dfs-type))
  :measure (nats-o (+ (num-not-in g v) 2) (1+ (len arcs)))
  :hints (("Goal" :in-theory (enable num-not-in)))
  :returns (mv rslt
               (r nmap-p :hyp (nmap-p r))
               (v nmap-p :hyp (nmap-p v)))
  :verify-guards nil
  (b* ((cyc-chk (listp dfs-type)))
    (if (endp arcs)
        (mv (if cyc-chk nil acc) r v)
      (b* ((n (first arcs))
           ((when (and cyc-chk (nmap-get n stk)))
            ;; potential valid cycle in cycle detection..
            (b* ((path (cons (cons n t) stk))
                 (cyc (is-valid-bad-cyc path dfs-type)))
              (if cyc
                  (fast-alist-free-on-exit stk (mv cyc r v))
                (graph-dfs-top (rest arcs) top g acc r v stk dfs-type))))
           ;; BOZO -- should probably work into guard for graphs that they are
           ;; well-formed with all nodes on arcs in the graphs..
           (n-g (graph-get n g))
           (n-r (nmap-get n r)))
        (if (or (not n-g) n-r (nmap-get n v))
            (b* ((acc (if (and n-g n-r)
                          (upd-acc dfs-type (nfix (cdr n-r)) acc)
                        acc)))
              (graph-dfs-top (rest arcs) top g acc r v stk dfs-type))
          (b* ((v (nmap-set n t v))
               (stk (if cyc-chk (nmap-push n stk) stk))
               ((mv a+ r v+)
                (graph-dfs-top (cdr n-g) top g (new-acc) r v stk dfs-type))
               ;; NOTE -- given the reflexive nature of the termination measure
               ;;         relative to a result (v+) from a recursive call, namely
               ;;         that the num-not-in decreases, we need to do a little
               ;;         logic check here that we will bypass at runtime..
               ((unless (mbe :logic (subset-nmap v v+) :exec t))
                (mv acc r v))
               ((when (and cyc-chk a+)) ;; found cycle, return immediately..
                (mv a+ r v+))
               ;; BOZO -- would be nice to include return type
               ;; specifier to avoid nfix here  :(
               (a++ (1+ (nfix a+)))
               (stk (if cyc-chk (nmap-pop stk) stk))
               (r   (upd-rmap dfs-type n a++ top r))
               (acc (upd-acc dfs-type a++ acc)))
            (graph-dfs-top (rest arcs) top g acc r v+ stk dfs-type))))))
  ///
  (defthm subset-nmap-graph-dfs-top
    (implies (nmap-p v)
             (subset-nmap v (mv-nth 2 (graph-dfs-top a x g
                                                     acc r v
                                                     stk dfs-type))))))

(verify-guards graph-dfs-top)

(define find-next-anchor ((nodes nmap-p) (r nmap-p))
  :returns (r nmap-p)
  (cond ((endp nodes) ())
        ((not (nmap-get (caar nodes) r)) (nmap-fix nodes))
        (t (find-next-anchor (cdr nodes) r)))
  ///
  (defthm find-next-anchor-smaller
    (<= (len (find-next-anchor x r))
        (len x))
    :rule-classes (:rewrite :linear)
    :hints (("Goal" :in-theory (enable nmap-fix)))))

(define arcs->nmap ((x arcs-p) &key ((r nmap-p) '()))
  :returns (r nmap-p :hyp :guard)
  (if (endp x) (nmap-fix r) (arcs->nmap (rest x) :r (cons (cons (first x) t) r))))

(define nmap->arcs ((x nmap-p) &key ((r arcs-p) '()))
  :returns (r arcs-p :hyp :guard)
  (if (endp x) (arcs-fix r) (nmap->arcs (cdr x) :r (cons (caar x) r))))

(define graph-dfs-each ((nodes nmap-p) (g graph-p) dfs-type
                        &key ((r nmap-p) '()))
  :guard (or (eq dfs-type :enumerate)
             (eq dfs-type :anchor)
             (ord-list-p dfs-type))
  :returns (r nmap-p)
  :measure (len nodes)
  (if (endp nodes)
      (if (listp dfs-type)
          nil ;; for cyc-check, when we get here, return nil!
        (nmap-fix r)) ;; BOZO -- ordering matters here! .. no
                      ;; fast-alist-clean, no reversal of the alist..
    (b* ((x (caar nodes))
         ((mv rslt r v)
          (graph-dfs-top (list x) x g
                         (new-acc) r nil
                         nil dfs-type))
         ((when (and rslt (listp dfs-type)))
          (if (arcs-p rslt) (arcs->nmap rslt)
            (raise "Internal Error: expected proper nmap result: ~x0"
                   (list rslt dfs-type))))
         (- (fast-alist-free v))
         (nodes (find-next-anchor (cdr nodes) r)))
      (graph-dfs-each nodes g dfs-type :r r))))

(define graph-dfs ((g graph-p) &key ((map nmap-p) '()))
  :short "performs dfs and returns map in depth-order pointing to anchors"
  :returns (r nmap-p)
  (graph-dfs-each (or map g) g :anchor))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; GRAPH computing SCCs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define graph-sccs ((g graph-p))
  :short "compute SCCs by doing forward dfs and feeding map to inverse dfs (effectively Kosaraju's algorithm)"
  ;; We use Kosaraju's algorithm for computing SCCs over Tarjan's or Djikstra's
  ;; simply because it is more elegant and functional in nature and easier to
  ;; extend and modify as needed.. the implementation is still O(V+E) with more
  ;; overhead, but the cost of SCC computation is not the major limit to the
  ;; algorithm.. if the cost of the second pass here is relevant, then Tarjan's
  ;; algorithm could be substituted as needed..
  :returns (r nmap-p)
  (graph-dfs (graph-invert g) :map (graph-dfs g)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; GRAPH computing enumeration
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define graph-enumerate ((g graph-p))
  :short "performs dfs and returns enumeration of graph from depth-first-search"
  :returns (r nmap-p)
  (graph-dfs-each g g :enumerate))

(define graph-indexing ((g graph-p))
  :returns (r nmap-p)
  (graph-enumerate (graph-abstract g (graph-sccs g))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; GRAPH finding cycles
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define find-min-cycle ((g graph-p) (ords ord-list-p))
  :returns (r arcs-p)
  (nmap->arcs (graph-dfs-each g g ords)))

(define graph-valid-cycle ((g graph-p) (ords ord-list-p))
  :short "Search for a valid simple cycle (one where no ord is decreasing) -- may not find one"
  (find-min-cycle g ords))

(define force-arc-first ((arc arc-descr-p) (g graph-p))
  :returns (r graph-p)
  (b* (((arc-descr a) arc)
       (curr-arcs (cdr (graph-get a.src g)))
       (new-arcs (arcs-add a.dest curr-arcs)))
    (graph-set a.src new-arcs g)))

(define graph-any-cycle ((g graph-p) (ords ord-list-p))
  :short "Search for any simple cycle where ord is not decreasing -- should find one"
  ;; NOTE -- there are two cases to consider.. we try to find an arc with a possibly
  ;;         increasing order.. if we find that arc, then we adjust the graph to put
  ;;         that node and arc at the head of the graph.. otherwise, there are no
  ;;         possibly increasing or strictly decreasing arcs and as such, any cycle
  ;;         in the graph will do (and would be a stronger example failure)..
  :returns (mv cyc (r graph-p))
  (b* ((fail (check-ords-fail g ords))
       (g+   (graph-fix (if fail (force-arc-first fail g) g)))
       (cyc  (find-min-cycle g+ nil))
       ((unless cyc)
        (fast-alist-free-on-exit g+
         (mv (raise "internal error: we should have found a cycle!") ()))))
    (mv cyc g+)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; GRAPH examples and tests..
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define arcs-make (x)
  :returns (r arcs-p)
  :verify-guards nil
  (cond ((null x) ())
        ((atom x)
         (raise "ill-formed arcs specifier input:~x0" x))
        (t (arcs-add (car x)
                     (arcs-make (cdr x))))))

(verify-guards arcs-make)

(define graph-make (x)
  :returns (r graph-p)
  :verify-guards nil
  (cond ((null x) ())
        ((or (atom x) (atom (car x)))
         (raise "ill-formed graph specifier input:~x0" x))
        (t (graph-set (caar x)
                      (arcs-make (cdar x))
                      (graph-make (cdr x))))))

(verify-guards graph-make)

(define make-asserts-fn (tsts)
  (cond ((atom tsts) ())
        ((or (atom (cdr tsts))
             (atom (cddr tsts))
             (not (equal (second tsts) '=)))
         (raise "oops.. bad form!"))
        (t (cons `(assert-event (equal ,(first tsts) (quote ,(third tsts))))
                 (make-asserts-fn (cdddr tsts))))))

(defmacro make-asserts (&rest tsts)
  (cons 'progn (make-asserts-fn tsts)))

(encapsulate ()
  ;; a quick little testing encapsulate
  (local
   (progn
     (defconst *g1*
       (graph-make '((0 1 2)
                     (1 0 3)
                     (2 0 3)
                     (3 0 1 2))))
     (defconst *g2*
       (graph-make '((0 1 2)
                     (1 0 3)
                     (2 )
                     (3 0 1 2))))
     (defconst *g3*
       (graph-make '((0 1 2)
                     (1 3)
                     (2 3)
                     (3 1 2))))
     (defconst *g4*
       (graph-make '((0 1 2)
                     (1 0)
                     (2 0)
                     (3 0))))))

  (make-asserts
   (graph-sccs *g1*) = ((0 . 0) (3 . 0) (1 . 0) (2 . 0))
   (graph-sccs *g2*) = ((2 . 2) (0 . 0) (3 . 0) (1 . 0))
   (graph-sccs *g3*) = ((1 . 1) (3 . 1) (2 . 1) (0 . 0))
   (graph-sccs *g4*) = ((0 . 0) (1 . 0) (2 . 0) (3 . 3))
   ;;
   (graph-indexing *g1*) = ((0 . 1))
   (graph-indexing *g2*) = ((0 . 2) (2 . 1))
   (graph-indexing *g3*) = ((0 . 2) (1 . 1))
   (graph-indexing *g4*) = ((3 . 2) (0 . 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ..... Main Algorithm ......
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prepend-ord ((m omap-p) (ord ord-p)
                     &key ((r omap-p) '()))
  :returns (r omap-p)
  (if (endp m) (omap-fix r)
    (prepend-ord (rest m) ord
                 :r (acons (caar m) (cons ord (cdar m)) r))))

(define prepend-enum ((m omap-p) (sccs nmap-p) (enum nmap-p)
                      &key ((r omap-p) '()))
  :returns (r omap-p)
  (if (endp m) (omap-fix r)
    (prepend-enum (rest m) sccs enum
                  :r (b* ((look (hons-get (caar m) sccs))
                          ((when (not look))
                           (raise "internal error encountered in sccs lookup!"))
                          (look (hons-get (cdr look) enum))
                          ((when (not look))
                           (raise "internal error encountered in enum lookup!"))
                          (v (cdr look))
                          ((when (not (natp v)))
                           (raise "internal error encountered in enum value!")))
                       (acons (caar m) (cons v (cdar m)) r)))))

(define remove-ord ((ord ord-p) (ords ord-list-p))
  :guard (consp ords)
  :returns (r ord-list-p :hyp (ord-list-p ords))
  :measure (len ords)
  :verify-guards nil
  (b* ((fst (first ords)))
    (if (ord= ord fst) (rest ords)
      (b* ((rst (rest ords)))
        (if (endp rst)
            (raise "internal error: did not find ord in list!:~x0"
                   (list ord fst))
          (cons fst (remove-ord ord rst)))))))

(verify-guards remove-ord)

(local (defthm remove-ord-len-rdx
         (implies (consp ords)
                  (< (len (remove-ord ord ords))
                     (len ords)))
         :hints (("Goal" :in-theory (enable remove-ord)))
         :rule-classes (:linear :rewrite)))

; We now proceed to define the main abstract rank construction
; algorithm which takes a graph with nodes representing the
; concrete values in the abstract mapping and get the tagging
; with ordering marks (either strictly-less-than, less-than-equal,
; or unknown) from check-ord-arc ... and find a decomposition of
; the graph which demonstrates a rank exists on the original
; structure.. or we have an SCC which has no strictly decreasing
; orders and we try to find a minimal cycle with no order
; reduction to present as a result...

(define chk-well-order (g (ords ord-list-p)
                        &key (lst? 'nil) (scc? 'nil))
  :guard   (if lst? (graph-lst-p g) (graph-p g))
  :measure (nats-o (+ (len ords) 3)
                   (if scc? 2 3)
                   (+ (if lst? (acl2-count g) 0) 2))
  :verify-guards nil
  :returns (mv err (r omap-p))
  (cond
   ((and lst? (endp g))
    (mv nil ()))
   (lst?
    (b* (((mv err fst) (chk-well-order (first g) ords
                                       :lst? nil :scc? scc?))
         ((when err)   (mv err ()))
         ((mv err rst) (chk-well-order (rest g) ords
                                       :lst? t :scc? scc?))
         ((when err)   (mv err ())))
      (mv nil (append fst rst))))
   ((endp g)
    (fast-alist-free-on-exit g
      (mv (raise "internal error: should not have empty graph here!")
          nil)))
   ((and (endp (cdr g)) (endp (cdar g)))
    ;; singleton graph with no self-cycle, so we simply return a default ordering..
    (fast-alist-free-on-exit g
      (mv nil (acons (caar g) (list 0) nil))))
   ((not scc?)
    (fast-alist-free-on-exit g
      ;; don't know if g is an scc, so compute SCCs and split it and then prepend
      ;; the enumeration of the abstract graph onto the resulting ord-maps from
      ;; the recursive call:
      (b* ((sccs       (graph-sccs g))
           (projs      (graph-projects g sccs))
           ((mv err r) (chk-well-order projs ords
                                       :lst? t :scc? t))
           ((when err) (mv err ()))
           (abs        (graph-abstract g sccs))
           (enum       (graph-enumerate abs))
           (r          (prepend-enum r sccs enum))
           (-          (fast-alist-free abs))
           (-          (fast-alist-free enum)))
        (mv nil r))))
   ((endp ords)
    (fast-alist-free-on-exit g
      (mv (list :valid nil (graph-valid-cycle g nil)) ())))
   (t ;; we have an SCC and we need to find an ordering which decreases to pick
      ;; for cutting arcs from the graph:
    (b* ((ord           (graph-pick-ord g ords))
         ;; if we have an SCC without a valid ord to pick then we have an error
         ;; and we are transitioning into trying to find the best minimal
         ;; counterexample as a simple cycle with certain characteristics...
         (no-ord        (not ord))
         (ord           (if no-ord (graph-failed-ord g ords) ord))
         (cyc           (if no-ord (graph-valid-cycle g ords) nil))
         ((when cyc)    (fast-alist-free-on-exit g
                          (mv (list :valid ord cyc) ())))
         ((unless ord)  (fast-alist-free-on-exit g
                          (mv (raise "internal error: should not get no order chosen here!")
                              nil)))
         (sub           (graph-cut-ord g ord))
         ((mv err r)    (chk-well-order sub (remove-ord ord ords)
                                        :lst? nil :scc? nil))
         ((when err)    (mv err ()))
         ;; Ok, we have failed to find a pure cycle which demonstrates failure,
         ;; so, we will resort to reporting a weaker cycle
         ((when no-ord) (b* (((mv cyc g) (graph-any-cycle g ords)))
                          (fast-alist-free-on-exit g
                            (mv (list :weak? ord cyc) nil))))
         (r             (prepend-ord r ord))
         (-             (fast-alist-free g)))
      (mv nil r)))))

(local (defthm omap-p-is-true-list
         (implies (omap-p x) (true-listp x))
         :hints (("Goal" :in-theory (enable omap-p)))))

(verify-guards chk-well-order-fn)

(fty::defprod w-ord-rslt
 (passed error-rslt (order-rslt omap-p)))

(define mk-well-order ((g graph-p) (ords ord-list-p))
  :short "Takes a graph and orderings and returns a well-order or failing cycle"
  (b* (((mv err rslt)
        (chk-well-order (make-fast-alist g) ords)))
    (make-w-ord-rslt
     :passed (not err)
     :error-rslt err
     :order-rslt rslt)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; MORE GRAPH examples and tests..
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (defthm ord-tag-p-of-<
         (ord-tag-p (< x y))
         :hints (("Goal" :in-theory (enable ord-tag-p)))))

(encapsulate ()
  ;; another quick little testing encapsulate
  (local
   (progn
     (defconst *g1*
       (graph-make '((0 1 2)
                     (1 0 3)
                     (2 0 3)
                     (3 0 1 2))))
     (defconst *g2*
       (graph-make '((0 1 2)
                     (1 0 3)
                     (2 )
                     (3 0 1 2))))
     (defconst *g3*
       (graph-make '((0 1 2)
                     (1 3)
                     (2 3)
                     (3 1 2))))
     (defconst *g4*
       (graph-make '((0 1 2)
                     (1 0)
                     (2 0)
                     (3 0))))))

  (local
   (define chk-arc-tst ((src node-p) (dst node-p) (ord ord-p))
     :returns (r ord-tag-p)
     (b* ((src (nfix src))
          (dst (nfix dst))
          (a   (if (ord= ord :up) src dst))
          (b   (if (ord= ord :up) dst src)))
       (cond ((< a b) :<<)
             ((>= (+ a b) 5) nil)
             (t t)))))

  (local (defattach check-ord-arc chk-arc-tst))

  (make-asserts
   (mk-well-order *g1* '(:up)) = ((PASSED)
                                  (ERROR-RSLT :VALID :UP (2 3))
                                  (ORDER-RSLT))
   (mk-well-order *g1* '(:dn)) = ((PASSED)
                                  (ERROR-RSLT :VALID :DN (3 1))
                                  (ORDER-RSLT))
   (mk-well-order *g1* '(:up :dn)) = ((PASSED)
                                      (ERROR-RSLT :VALID
                                                  :UP (0 1 3 2))
                                      (ORDER-RSLT))
   (mk-well-order *g2* '(:up)) = ((PASSED . T)
                                  (ERROR-RSLT)
                                  (ORDER-RSLT (3 2 :UP 3 0)
                                              (1 2 :UP 2 0)
                                              (0 2 :UP 1 0)
                                              (2 1 0)))
   (mk-well-order *g2* '(:dn)) = ((PASSED . T)
                                  (ERROR-RSLT)
                                  (ORDER-RSLT (0 2 :DN 3 0)
                                              (1 2 :DN 2 0)
                                              (3 2 :DN 1 0)
                                              (2 1 0)))
   (mk-well-order *g2* '(:up :dn)) = ((PASSED . T)
                                      (ERROR-RSLT)
                                      (ORDER-RSLT (3 2 :UP 3 0)
                                                  (1 2 :UP 2 0)
                                                  (0 2 :UP 1 0)
                                                  (2 1 0)))
   (mk-well-order *g3* '(:up)) = ((PASSED)
                                  (ERROR-RSLT :VALID :UP (1 3))
                                  (ORDER-RSLT))
   (mk-well-order *g3* '(:dn)) = ((PASSED)
                                  (ERROR-RSLT :VALID :DN (3 2))
                                  (ORDER-RSLT))
   (mk-well-order *g3* '(:up :dn)) = ((PASSED)
                                      (ERROR-RSLT :WEAK? :UP (3 2))
                                      (ORDER-RSLT))
   (mk-well-order *g4* '(:up)) = ((PASSED . T)
                                  (ERROR-RSLT)
                                  (ORDER-RSLT (3 2 0)
                                              (2 1 :UP 2 0)
                                              (1 1 :UP 2 0)
                                              (0 1 :UP 1 0)))
   (mk-well-order *g4* '(:dn)) = ((PASSED . T)
                                  (ERROR-RSLT)
                                  (ORDER-RSLT (3 2 0)
                                              (0 1 :DN 2 0)
                                              (2 1 :DN 1 0)
                                              (1 1 :DN 1 0)))
   (mk-well-order *g4* '(:up :dn)) = ((PASSED . T)
                                      (ERROR-RSLT)
                                      (ORDER-RSLT (3 2 0)
                                                  (2 1 :UP 2 0)
                                                  (1 1 :UP 2 0)
                                                  (0 1 :UP 1 0)))
   (mk-well-order *g4* ()) = ((PASSED)
                              (ERROR-RSLT :VALID NIL (0 2))
                              (ORDER-RSLT))))

