#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book t :ttags :all);$ACL2s-Preamble$|#

;Author: Harsh Raju Chamarthi (harshrc)

(in-package "CGEN")
(include-book "utilities")
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)

(defun make-n-upto-list (size ans)
;make a list of natural numbers upto (size-1)
;(make-n-upto-list 3 nil) ==> (0 1 2)
  (declare (xargs :guard (and (natp size)
                              (nat-listp ans))))
  (if (zp size)
    ans
    (make-n-upto-list  (1- size) (cons (1- size) ans))))

(set-verify-guards-eagerness 0)


(defmacro in (a X)
  `(member-equal ,a ,X))

(defun vertex-indexes (vs sym-lst)
;returns a natural number which is associated with
;v in mapping. vs is the original symbol-list
;used to create mapping
 (declare (xargs :guard (and (symbol-listp vs)
                             (symbol-listp sym-lst)
                             (subsetp vs sym-lst))))
 (if (endp vs)
     nil
   (cons (position (car vs) sym-lst)
         (vertex-indexes (cdr vs) sym-lst))))

(defstobj g$
  (adj-list-array :type (array T (0))
                  :initially nil
                  :resizable t)
  :renaming ((adj-list-arrayi ai)
             (update-adj-list-arrayi ui))
; Matt K. mod: :doc is no longer supported for defthm after v7-1
#||
  :doc "Graph represented as an adjacency list array.
        Key is vertex-index.
        Value is a record with the following fields:
        :name - (symbol) name of the vertex
        :adj - (nat-list) list of indexes of adjacent vertices
        :seen - boolean (bit) indicating wether this vertex has been visited
        :cc - (nat) indicating the connected component this vertex belongs to"
||#
  :inline t)

(defrec vinfo%
  (name adj seen cc)
  NIL)


(defmacro make-g$-array-value (name &key adj seen cc)
 `(acl2::make vinfo%
     :name ,name
     :adj ,adj
     :seen ,seen
     :cc ,(or cc 0)))

(defun symbol-alst->g$1 (alst vs g$)
 (declare (xargs :stobjs (g$)
                 :guard (and (symbol-alistp alst)
                            (symbol-listp vs)
                            (g$p g$)
                            )))
;transforms a symbol-alist graph adjacency list representation
;to an g$ adjacency list representation.
 (if (endp alst)
     g$
   (b* (((cons v adj-vs) (car alst))
        ((list i) (vertex-indexes (list v) vs))
        (adj-is (vertex-indexes adj-vs vs))
        (g$ (ui i (make-g$-array-value v :adj adj-is) g$)))
     (symbol-alst->g$1 (cdr alst) vs g$))))


(defun init-g$1 (i vs g$)
 (declare (xargs :stobjs (g$)
                 :guard (and (symbol-listp vs)
                             (g$p g$)
                             )))
;intializes a g$ to a graph with no edges
 (if (endp vs)
     g$
     (let ((g$ (ui i (make-g$-array-value (car vs)) g$)))
       (init-g$1 (1+ i) (cdr vs) g$))))

(defun init-g$ (vs size g$)
  ";intializes/resets a g$ to a graph with no edges"
  (declare (xargs :stobjs (g$)
                  :guard (and (symbol-listp vs)
                              (= (len vs) size)
                              (g$p g$)
                              )))
  (let ((g$ (resize-adj-list-array size g$)))
    (init-g$1 0 vs g$)))
#||
(defun reset-g$-aux (l g$)
  (if (zp l)
      g$
    (reset-g$-aux (1- l)
                  ;;index corresponding to l is (1- l) which is the last
                  ;;element initially
                  (ui (1- l) nil g$))))

(defun reset-g$ (g$)
  "reset the information stored for each vertice"
  (reset-g$-aux (adj-list-array-length g$) g$))
||#

(defun symbol-alist->g$ (alst g$)
"top-level call to populate g$ with adj-list information obtained
from alst. Assumption: (len alst) = number of vertices in graph and
[strip-cars alst] has distinct vertices"
 (declare (xargs :stobjs (g$)
                 :guard (and (symbol-alistp alst)
                             (g$p g$))))

 (b* ((vs (strip-cars alst))
      (size (len alst))
      (g$ (init-g$ vs size g$)))
   (symbol-alst->g$1 alst
                     vs ;find position (index)
                     g$
                     )))

(set-well-founded-relation acl2::l<)



;Dasgupta Algo
;Vertices are natural numbers.
(defun dfs-visit1 (g$ v n fin flag)
"explore the graph g$ (adj-list array) starting at v.
n is the number of vertices of g$ not seen,
initially it is just the total number of vertices.
fin is the list of finished vertices, with the
(car fin) being the last finished vertice, i.e
the vertice with the maximum post time."
  (declare (xargs :stobjs (g$)
                  :guard (and (g$p g$)
                              (or (natp v);vertice
                                  (nat-listp v));vertices
                              (nat-listp fin)
                              (natp n))
                  :measure (list (nfix n) (acl2-count v))))
  (if (zp n);visited all vertices
      (mv g$ fin)
    (if (equal 'dfs-visit flag)
;DFS-VISIT
        (b* ((v-entry (ai v g$))
             (adj-vs (acl2::access vinfo% v-entry :adj))
             (g$ (ui v (acl2::change vinfo% v-entry :seen t) g$));update/change seen
             ((mv g$ fin!)
              (dfs-visit1 g$ adj-vs (1- n) fin 'dfs-visit-lst)))
          ;;update finished vertices
          (mv g$ (cons v fin!)))
;DFS-VISIT-LST
      (if (endp v);visited all neighbours
          (mv g$ fin)
        (b* ((v-entry (ai (car v) g$))
             ;(- (cw "dfs-visit-lst: v-entry for ~x0 is ~x1~%" (car v) v-entry))
             )
          (if (acl2::access vinfo% v-entry :seen);already seen
              (dfs-visit1 g$ (cdr v) n fin 'dfs-visit-lst)
            (b* (((mv g$ fin!)
                  (dfs-visit1 g$ (car v) n fin 'dfs-visit)))
              (dfs-visit1 g$ (cdr v) n fin! 'dfs-visit-lst))))))))


(defun dfs-all-vertices (g$ vs n fin cnum)
  "Do DFS over all vertices in vs"
  (declare (xargs :stobjs (g$)
                  :guard (and (g$p g$)
                              (nat-listp vs);vertices
                              (nat-listp fin)
                              (natp cnum)
                              (natp n))))

  (if (endp vs);visited all neighbours
      (mv g$ fin)
      (b* ((v-entry (ai (car vs) g$)))
           ;(- (cw "dfs-all: v-entry for ~x0 is ~x1~%" (car vs) v-entry)))
        (if (acl2::access vinfo% v-entry :seen);already seen
            (dfs-all-vertices g$ (cdr vs) n fin cnum)
        (b* ((g$ (ui (car vs)
                     (acl2::change vinfo% v-entry :cc cnum)
                     g$))
             ((mv g$ fin!)
              (dfs-visit1 g$
                          ;;update current component as part of pre
                          (car vs) n fin
                          'dfs-visit)))
          (dfs-all-vertices g$ (cdr vs) n fin! (1+ cnum)))))))


(defun dfs1 (g$ vs)
;Depth First Search on adj list array g$ iterating
;over the vertices in vs.
  (declare (xargs :stobjs (g$)
                  :guard (and (nat-listp vs)
                              (g$p g$))))
  (dfs-all-vertices g$ vs (adj-list-array-length g$) nil 0))

;(defdata adjacency-list (map symbol symbol-list))
(defun adjacency-list1p (v)
  (if (null v)
      t
    (if (atom v)
        nil
      (let ((entry (car v)))
      (and (symbolp (car entry))
           (symbol-listp (cdr entry))
           (no-duplicatesp (cdr entry))
           (adjacency-list1p (cdr v)))))))

(defun adjacency-listp (v)
  (and (adjacency-list1p v)
       (no-duplicatesp (strip-cars v))))

(defun make-empty-adj-list (vars)
  (declare (xargs :guard (and (symbol-listp vars)
                              (no-duplicatesp vars))))
  ;order important
  ;order of keys alst created is the same as order of vars
  (if (endp vars)
    nil
    (cons (cons (car vars) nil)
          (make-empty-adj-list (cdr vars)))))



;fs means Functionaly dependent vars
;ASSUMPTION: alst has all the variables as keys already
;this function just updates the entries, doesnt insert
;new entries.
(defun union-entry-in-adj-list (var fvars alst)
  (declare (xargs :guard (and (adjacency-listp alst)
                              (true-listp fvars))))
  (if (endp alst)
      nil
    (if (eq var (caar alst))
      (cons (cons var (union-equal fvars
                                   (cdar alst)))
            (cdr alst))
      (cons (car alst)
            (union-entry-in-adj-list var fvars (cdr alst))))))


;recurse above fun over list of indices
(defun union-entries-in-adj-list (is fis alst)
 (declare (xargs :guard (and (adjacency-listp alst)
                             (true-listp is)
                             (true-listp fis))))
 (if (endp is)
    alst
    (union-entries-in-adj-list
     (cdr is) fis (union-entry-in-adj-list (car is) fis alst))))


(defun transpose-alst1 (alst ans)
;Scan G at index i and transpose the result corresponding to i in ans
  (declare (xargs :guard (and (adjacency-listp alst)
                              (adjacency-listp ans)
                              )))
  (if (endp alst)
      ans
    (b* (((cons v vs) (car alst)))
      (transpose-alst1 (cdr alst)
                       (union-entries-in-adj-list vs (list v) ans)))))


(defun transpose-alst (alst)
;Return transpose/reverse of alst
;INVARIANT: Order is very important
  (declare (xargs :guard (adjacency-listp alst)))
  (transpose-alst1 alst (make-empty-adj-list (strip-cars alst))))
#|
(defthm transpose-idempotent
  (implies (adjacency-list1p x)
           (equal (transpose-alst (transpose-alst x))
                  x)))

(defthm transpose-doesnt-change-order
  (implies (adjacency-list1p x)
           (equal (strip-cars (transpose-alst x))
                  (strip-cars x))))
|#




(defun scc1 (alst g$)
;Strongly Connected Components of adj list array G,
;alst is the same adj-list, but in form of an alist
  (declare (xargs :stobjs (g$)
                  :guard (and (symbol-alistp alst)
                              (adjacency-listp alst)
                              (g$p g$))))
  (b* ((r-alst (transpose-alst alst))
       (g$ (symbol-alist->g$ r-alst g$))
       (N (adj-list-array-length g$))
       ((mv g$ fin) (dfs1 g$ (make-n-upto-list N nil)))
       (g$ (symbol-alist->g$ alst g$))
       ((mv g$ fin!) (dfs1 g$ fin)))
    (mv g$ fin!)))


(defun g$->var-quotient-alst1 (g$ i size ans)
  "Given graph g$, where g$[v]=(record name adj-is seenBit ccnum), we will
return, symbol alist, which maps each vertex (name), to its component
number (ccnum). This is used in simple-var-hyp? for finding cycles."
  (declare (xargs  :stobjs (g$)
                   :measure (nfix (- size i))
                   :guard (and (natp i) (natp size)
                               (<= i size))))
  (if (zp (- size i))
      ans
    (let ((v-entry (ai i g$)))
      (g$->var-quotient-alst1 g$ (1+ i) size
                             (acons (acl2::access vinfo% v-entry :name)
                                    (acl2::access vinfo% v-entry :cc)
                                    ans)))))

(defun g$->var-quotient-alst (g$)
  (declare (xargs :stobjs (g$)))
  (g$->var-quotient-alst1 g$ 0 (adj-list-array-length g$) nil))

(defun vertex-names (is g$)
  (declare (xargs :stobjs (g$)
                  :guard (nat-listp is)))
  (if (endp is)
      nil
    (cons (acl2::access vinfo% (ai (car is) g$) :name)
          (vertex-names (cdr is) g$))))

(defun g$->alst1 (g$ i size ans)
  (declare (xargs  :stobjs (g$)
                   :measure (nfix (- size i))
                   :guard (and (natp i) (natp size)
                               (<= i size))))
  (if (zp (- size i))
      ans
    (let ((v-entry (ai i g$)))
      (g$->alst1 g$ (1+ i) size
                    (acons (acl2::access vinfo% v-entry :name)
                           (vertex-names (acl2::access vinfo% v-entry :adj) g$)
                           ans)))))

(defun g$->symbol-alist (g$)
  (declare (xargs  :stobjs (g$)))
  (g$->alst1 g$ 0 (adj-list-array-length g$) nil))


(defun scc0 (alst g$)
  (declare (xargs :stobjs (g$)
                  :guard (symbol-alistp alst)))
  (mv-let (g$ fin)
          (scc1 alst g$)
          (mv (g$->var-quotient-alst g$)
              (vertex-names fin g$)
              (g$->symbol-alist g$)
              g$)))

(defun union-lsts (lsts)
  (declare (xargs :mode :logic
                  :guard (true-list-listp lsts)))
  (if (endp lsts)
    nil
    (union-equal (car lsts)
                 (union-lsts (cdr lsts)))))

(defun fix-adjacency-list (alst)
  (declare (xargs :guard (adjacency-listp alst)))
  "Fix an adjacency list to have in it keys all the vertices."
  (b* ((adj-v-lst-lst (strip-cdrs alst))
       (vs (strip-cars alst))
       (adj-vs (union-lsts adj-v-lst-lst))
       (missing-vs (set-difference-eq adj-vs vs))
       (missing-alst (pairlis$ missing-vs nil)))
    (append alst missing-alst)))

(defun strongly-connected-components (alst debug-flag)
   "Strongly Connected Components of adj list graph alst.
Gives (mv map-ccnum finished-vertex-list) as result, where
map-ccnum, maps each vertex to its component number.
finished-vertex-list gives the list of vertexes in decreasing
post times."
   (declare (xargs :guard (adjacency-listp alst)))
    (b* ((alst! (fix-adjacency-list alst))
         (- (cw? (and (not (equal alst alst!))
                               debug-flag)
            "CEgen/Note: SCC: Got Adjacency list : ~x0 Fixed to : ~x1~%" alst alst!)))
      (acl2::with-local-stobj
       g$

       (mv-let (var-ccnum-alst decreasing-post-times-vertex-lst adj-alst g$)
               (scc0 alst! g$)
               (mv var-ccnum-alst
                   decreasing-post-times-vertex-lst
                   adj-alst)))))

;to check simple soundness (g$->symbol-alist g$) = alst!

(defun approximate-topological-sort (alst debug-flag)
;return vertices following the order ->, but
;since alst might not be a dag, the order
;inside a component might be skewed, but we
;are okay with it, since we choose arbitrarily
;from within a component
  (declare (xargs :guard (adjacency-listp alst)))
  (b* (((mv & fin-vs &)
        (strongly-connected-components alst debug-flag)))
    fin-vs))

#|

;example:
;(untrace$ dfs dfs-visit dfs-all-vertices)
(let* ((A '((a b)
            (b e c d)
            (c f)
            (d)
            (e b g f)
            (f c h)
            (g j h )
            (h k)
            (i g)
            (j i)
            (k l)
            (l j))))
  (approximate-topological-sort A))
;ans:(A B E C F D G H K L J I)
;ans by memories graph.lisp: (A B E C F D G H K L J I)
|#
;What correctness theorems can we prove?
