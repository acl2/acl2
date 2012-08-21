#|$ACL2s-Preamble$;
(ld ;; Newline to fool ACL2/cert.pl dependency scanner
 "cert.acl2")
(acl2::begin-book);$ACL2s-Preamble$|#

;Author: harshrc
;Started: June09? In mostly Finished state: Sep 5th 09.

(in-package "DEFDATA")
(include-book "utilities" :load-compiled-file :comp)

;;;; harshrc --
;;;; NOTE: This is an old graph book which will be replaced by the
;;;; simpler simple-graph-array book.


;*** START GLOBALS ***
;changed stobj to globals (how to assert the types? like in stobjs)
;dt1g stands for datatype 1dim array (adjacency list) graph implementation   (to store Explicit graph)
;dt2g stands for datatype 2dim array (adjacency matrix) graph implementation (to store Implicit graph)
;NOTE:we store the explicit (subtype and disjoint) graphs to record all the
;user-defined events and the implicit graphs to store information implied/inferred by SCC and Closure algos.
(make-event
 (er-progn
  ;explicit-vertMap maps typenames(symbols) to natural numbers(indexes of explicit graphs)
  (assign explicit-vertmap nil)
  
  ;implied-vertMap-arr maps indexes (of explicit graphs) to indexes(of implied graphs).
  (assign explicit-implied-index-map nil)
  
  ;subtype-dtg-alst is the explicit subtype relation datatype graph (with AdjList ALIST representation)
  (assign subtype-dtg-alst nil)
  ;implied-subtype-dt2g is the implied subtype relation datatype graph (with AdjMatrix matrix representation)
  (assign implied-subtype-dt2g nil)
  
  ;disjoint-dtg-alst is the explicit disjoint relation datatype graph (with AdjList ALIST representation)
  (assign disjoint-dtg-alst nil)
   ;implied-disjoint-dt2g is the implied disjoint relation datatype graph (with AdjMatrix matrix representation)
  (assign implied-disjoint-dt2g nil)
  
  ;I dont think we now need the following, as explicit graph size will be exactly of live-size(May change)
  ;(assign dtg-live-size 0)
  (value '(value-triple :DTG-GLOBALS-INITIALIZED))))



(defun get-explicit-vertmap (state)
  (declare (xargs :stobjs (state)))
  (if (f-boundp-global 'explicit-vertmap state)
    (let ((m (@ explicit-vertmap)))
      (if (symbol-alistp m)
        m
        nil))
    nil))

(defmacro set-explicit-vertmap (v)
 `(assign explicit-vertmap ,v))

(defun get-explicit-implied-index-map (state)
  (declare (xargs :stobjs (state)))
  (if (f-boundp-global 'explicit-implied-index-map state)
    (let ((m (@ explicit-implied-index-map)))
      (if (array1p 's-explicit-implied-index-map m)
        (cons 's-explicit-implied-index-map m) ;package the name with the array
        nil))
    nil))

(defmacro set-explicit-implied-index-map (v)
 `(assign explicit-implied-index-map ,v))

(defun nat-alistp (al)
  (declare (xargs :guard t))
  (if (null al)
    t
    (if (atom al)
      nil
      (and (consp (car al))
           (natp (caar al))
           (nat-alistp (cdr al))))))

(defun get-subtype-dtg-alst (state)
  (declare (xargs :stobjs (state)))
  (if (f-boundp-global 'subtype-dtg-alst state)
    (let ((g (@ subtype-dtg-alst)))
      (if (nat-alistp g);stored as an alist (adjlist with vertexes stored as indexes)
        g           ;we can easily get a 1-dim array graph from the alist rep using compress1
        nil))
    nil))

(defmacro set-subtype-dtg-alst (v)
 `(assign subtype-dtg-alst ,v))

(defun get-implied-subtype-dt2g (state)
  (declare (xargs :stobjs (state)))
  (if (f-boundp-global 'implied-subtype-dt2g state)
    (let ((g (@ implied-subtype-dt2g)))
      (if (array2p 'implied-subtype-dt2g g);same name as global ;CHECK
        (cons 'implied-subtype-dt2g g) ;package the name with the array
        nil))
    nil))

(defmacro set-implied-subtype-dt2g (v)
 `(assign implied-subtype-dt2g ,v))

(defun get-disjoint-dtg-alst (state)
  (declare (xargs :stobjs (state)))
  (if (f-boundp-global 'disjoint-dtg-alst state)
    (let ((g (@ disjoint-dtg-alst)))
      (if (nat-alistp g);stored as an alist (adjlist with vertexes stored as indexes)
        g
        nil))
    nil))

(defmacro set-disjoint-dtg-alst (v)
 `(assign disjoint-dtg-alst ,v))

(defun get-implied-disjoint-dt2g (state)
  (declare (xargs :stobjs (state)))
  (if (f-boundp-global 'implied-disjoint-dt2g state)
    (let ((g (@ implied-disjoint-dt2g)))
      (if (array2p 'implied-disjoint-dt2g g);same name as global ;CHECK
        (cons 'implied-disjoint-dt2g g) ;package the name with the array
        nil))
    nil))

(defmacro set-implied-disjoint-dt2g (v)
 `(assign implied-disjoint-dt2g ,v))
;*** END GLOBALS ***

;some utilities:
;1dim array
(defun defarray1 (name size initial-element)
  (compress1 name
             (cons (list :HEADER
                         :DIMENSIONS (list  size)
                         :MAXIMUM-LENGTH (1+ size)
                         :DEFAULT initial-element
                         )
                   nil)))

(defun alst-to-array1 (name size alst)
  (compress1 name
             (cons (list :HEADER
                         :DIMENSIONS (list  size)
                         :MAXIMUM-LENGTH (1+ size)
                         )
                   alst)))


;Adjacency Matrix (Square matrix) ; Can have a NameClash, get a different name!
(defun defarray2 (name size initial-element)
  (compress2 name
             (cons (list :HEADER
                         :DIMENSIONS (list size size)
                         :MAXIMUM-LENGTH (1+ (* size size))
                         :DEFAULT initial-element
                         )
                   nil)))



;copy-paste seq macro (taken from The ACL2 Book)
;sequential processing of state returning functions
(defmacro seq (stobj &rest rst)
  (cond ((endp rst) stobj)
        ((endp (cdr rst)) (car rst))
        (t `(let ((,stobj ,(car rst)))
             (seq ,stobj ,@(cdr rst))))))


;****shift to TABLES *******
(table explicit-vertex-index-map nil nil :guard
       (and (symbolp key)
            (natp val)
            (is-a-typeName key world)
            (<= val 999))) ;at the moment only 1000 types allowed because of colori

;table stores exactly one value, a 1-dim array which maps explicit indices to implicit ones.
;the key is the name of the 1-dim-array
 (table explicit-implicit-index-map nil nil :guard
       (and (symbolp key)
            (array1p key val)))
                        
;table storing the explicit(user-defined explicit information) subtype data-type graph
;with key as explicit index and val as adjacent list of explicit vertex indices
 (table subtype-dtg-alst nil nil :guard
       (and (natp key)
            (nat-listp val)))
;table storing the explicit(user-defined explicit information) disjoint data-type graph
;with key as explicit index and val as adjacent list of explicit vertex indices
(table disjoint-dtg-alst nil nil :guard
       (and (natp key)
            (nat-listp val)))

(defun matrixp (nm g)
  (declare (xargs :guard t))
  (and (symbolp nm)
       (array2p nm g)
       (equal (car (dimensions nm g))
              (cadr (dimensions nm g)))))

;table stores exactly one value, a adjacency matrix graph which is a 2-dim array.
;the key is the name of the graph. this 2-dim array stores the transitive closure
;of the subtype relation obtained from the explicit adj-list stored above. Hence
;it is aptly named implicit-subtype-dt2g. dt2g means data-type-2dim-graph.
(table implied-subtype-dt2g nil nil :guard
       (and (symbolp key)
            (matrixp key val)))
           
 
;table stores exactly one value, a adjacency matrix graph which is a 2-dim array.
;the key is the name of the graph. this 2-dim array stores the transitive closure
;of the disjoint relation obtained from the explicit adj-list stored above. 
(table implied-disjoint-dt2g nil nil :guard
       (and (symbolp key)
           (matrixp key val)))
            
 
;*** END TABLES ***



;(set-verify-guards-eagerness 2)

;make a list of natural numbers upto (size-1)
;(make-n-upto-list 3 nil) ==> (0 1 2)
(defun make-n-upto-list (size ans)
  (declare (xargs :guard (and (natp size)
                              (nat-listp ans))))
  (if (zp size)
    ans
    (make-n-upto-list  (1- size) (cons (1- size) ans))))  



(defun index1p (i nm g1)
  (declare (xargs :guard t))
  (if (array1p nm g1)
    (and (natp i)
         (< i (car (dimensions nm g1))))
    nil))

(defun index2p (i nm g2)
  (declare (xargs :guard t))
  (if (matrixp nm g2)
    (and (natp i)
         (< i (car (dimensions nm g2))))
    nil))

(defun index1-listp (x nm g1)
  (declare (xargs :guard t))
  (if (array1p nm g1)
    (if (atom x)
      (null x)
      (and (index1p (car x) nm g1)
           (index1-listp (cdr x) nm g1)))
    nil))
                              
(defun index2-listp (x nm g2)
  (declare (xargs :guard t))
  (if (matrixp nm g2)
    (if (atom x)
      (null x)
      (and (index2p (car x) nm g2)
           (index2-listp (cdr x) nm g2)))
    nil))

;(in-theory (disable index2-listp index2p))

(defthm index1-list-member-is-index1 
  (implies 
   (and (index1-listp x nm g1)
        (consp x))
   (and (index1p (car x) nm g1)
        (index1-listp (cdr x) nm g1))))

(defthm index2-list-member-is-index2 
  (implies 
   (and (index2-listp x nm g)
        (consp x))
   (and (index2p (car x) nm g)
        (index2-listp (cdr x) nm g))))



(defun g-2d-size (nm g)
  (declare (xargs :guard (matrixp nm g))) 
  (car (dimensions nm g)))

(defun g-1d-size (nm g)
  (declare (xargs :guard (array1p nm g))) 
  (car (dimensions nm g)))

(set-verify-guards-eagerness 0)
;;Find adjacent vertices to the vertex 'u' in the 
;;graph adj matrix 'g' of name 'name' and of size 'size'. 
(defun adj-vertices-loop (u name g ctr size ans)
  (declare (xargs :guard (and (matrixp name g) 
                              (natp size)
                              (natp ctr)
                              (<= ctr size)
                              (equal size (g-2d-size name g))
                              (implies (not (zp ctr));base case
                                       (let ((v (- size ctr)))
                                         (index2p v name g)))
                              (index2p u name g)
                              (index2-listp ans name g))))
  (if (zp ctr) ;reached end
    ans        ;order is maintained
    (let ((v (- size ctr)))
      (adj-vertices-loop u name g (1- ctr) size (if (aref2 name g u v )
                                                (append ans (list v))
                                                ans)))))

(defun adj-vertices (u nm g)
  (declare (xargs :guard (and (matrixp nm g) 
                              (index2p u nm g))))
   (let ((size (g-2d-size nm g)))
     (adj-vertices-loop u nm g size size nil)))

(set-verify-guards-eagerness 2)

;update 'new-g' with transposed entry in the adj matrix 'g'
(defun transpose-g-entry (nm g new-nm new-g row col)
  (declare (xargs :guard (and (matrixp nm g)
                              (matrixp new-nm new-g)
                              (equal (g-2d-size nm g)
                                     (g-2d-size new-nm new-g))
                              (index2p row nm g)
                              (index2p col nm g)
                              (index2p row new-nm new-g)
                              (index2p col new-nm new-g))))
                                       
  (let ((entry (aref2 nm g row col)))
    (aset2 new-nm new-g col row entry)))

;helps guards
(defun less-than (a b)
  (declare (xargs :guard t))
  (if (and (natp a)
           (natp b))
    (< a b)
    nil))

;if I could prove the foll theorem, a lot of the guard proofs will go through!
#| 
(defthm modify-graph-still-remains-graph
  (implies (and (matrixp nm g)
                (index2p row nm g)
                (index2p col nm g))
           (let ((new-g (aset2 nm g col row entry)))
             (and (matrixp nm new-g)
                  (index2p row nm new-g)
                  (index2p col nm new-g)))))
|#

(defun up-counterp (ctr size)
  (if (and (natp ctr) (natp size))
    (cond ((= ctr size) t)
          ((< ctr size) t)
          (t nil))
    nil))

(defun index2-up-counterp (ctr size nm g)
  (if (and (matrixp nm g)
           (equal size (g-2d-size nm g))) 
    (or (up-counterp ctr size)
        (index2p ctr nm g))
    nil))

(defun down-counterp (ctr size)
  (if (and (natp ctr) (natp size))
    (cond ((= ctr size) t)
          ((< ctr size) t)
          (t nil))
    nil))

(set-verify-guards-eagerness 0)

;*** START of transpose graph functions ***
;Main function call: (transpose-adjmatrix-graph new-nm nm g)
;Sig: Symbol * Symbol * Array2 -> Array2
;It takes an existing 2-dim matrix graph 'g' of name 'nm' and builds a new
;2-dim matrix graph of name 'new-nm'.

;loop over colums
(defun tg-loop-col (nm g new-nm new-g row col size)
  (declare (xargs :measure (acl2-count (- size col))
                  :guard (and (matrixp nm g)
                              (matrixp new-nm new-g)
                              (equal size (g-2d-size nm g))
                              (equal size (g-2d-size new-nm new-g))
                              (equal (g-2d-size nm g)
                                     (g-2d-size new-nm new-g))
                              (index2p row nm g)
                              (index2-up-counterp col size nm g)
                              (index2p row new-nm new-g)
                              (index2-up-counterp col size new-nm new-g))))
                              
  (if (not (less-than col size))
    new-g
    (let ((new-g (transpose-g-entry nm g new-nm new-g row col)))
      (tg-loop-col nm g new-nm new-g row (1+ col) size))))  


;loop over rows.
(defun tg-loop-row (nm g new-nm new-g row size)
  (declare (xargs :measure (acl2-count (- size row))
                  :guard (and (matrixp nm g)
                              (matrixp new-nm new-g)
                              (equal size (g-2d-size nm g))
                              (equal size (g-2d-size new-nm new-g))
                              (equal (g-2d-size nm g)
                                     (g-2d-size new-nm new-g))
                              (index2-up-counterp row size nm g)
                              (index2-up-counterp row size new-nm new-g))))
  (if (not (less-than row size))
    new-g
    (let ((new-g (tg-loop-col nm g new-nm new-g row 0 size)))
      (tg-loop-row nm g new-nm new-g (1+ row) size))))  

;transpose g to obtain new-g of same size
(defun transpose-adjmatrix-graph (new-nm nm g)
  (declare (xargs :guard (and (symbolp new-nm)
                              (matrixp nm g))))
                             
  (let* ((size (g-2d-size nm g))
         (new-g (defarray2 new-nm size nil)))
    (tg-loop-row nm g new-nm new-g 0 size)))
;*** END of transpose graph functions ***
  

;*** START functions for finding transpose of subtype-dtg adjlist graph ***
;Fun call: (transpose-dt1g new-nm nm dt1g)
;Sig: Symbol * Symbol * Array1 -> Array2
;Take a 1-dim array (graph) 'dt1g' of name 'nm' and returns 
;a 2-dim array (matrix) of name 'new-nm' of same size

; Nat * Symbol * Array2 * Integer-list -> Array2
;TODO:infinite loop while guard verification
(defun transpose-adjvertices-2g (i new-nm new-g adj-vertices-lsti)
  (declare (xargs :guard (and (symbolp new-nm)
                              (matrixp new-nm new-g)
                              (index2p i new-nm new-g)
                              (index2-listp adj-vertices-lsti new-nm new-g))))
  (if (endp adj-vertices-lsti)
    new-g
    (let* ((adj-verti (car adj-vertices-lsti))
           (new-g (aset2 new-nm new-g adj-verti i 't)))
      (transpose-adjvertices-2g i new-nm new-g (cdr adj-vertices-lsti)))))
  
;Symbol * Array2  * Subtype-dtg-st *  Nat -> Array2
(defun transpose-dt1g-aux (new-nm new-2g nm dt1g size down-ctr)
  (declare (xargs :guard (and (symbolp new-nm)
                              (symbolp nm)
                              (matrixp new-nm new-2g)
                              (array1p nm dt1g)
                              (natp down-ctr)
                              (natp size)
                              (equal size (g-2d-size new-nm new-2g))
                              (equal size (g-1d-size nm dt1g))
                              (<= down-ctr size))))
  (if (zp down-ctr)
    new-2g
    (let* ((i (- size down-ctr))
           (adj-vertices-lsti (aref1 nm dt1g i))  
           (new-2g (transpose-adjvertices-2g i new-nm new-2g adj-vertices-lsti)))
      (transpose-dt1g-aux new-nm new-2g nm dt1g size (1- down-ctr)))))
          
 ;Return the reverse of the subtype-dtg adjlist graph passed
(defun transpose-dt1g (new-nm nm dt1g)
  (declare (xargs :guard (and (symbolp new-nm)
                              (symbolp nm)
                              (array1p nm dt1g)
                              )))
  (let* ((size (g-1d-size nm dt1g))
         (rev-2g (defarray2 new-nm size nil)))
    (transpose-dt1g-aux new-nm rev-2g nm dt1g size size)))
;*** END functions for finding transpose of subtype-dtg adjlist graph ***  

;This stobj collects intermediate imperative state information
;about a graph traversal. In our case the DFS bookkeeping info.
;TODO: (IMP) cant 1000 be a parameter? -this is causing a bug if number of types exceed 1000!!!!
(defstobj g-visit-state
  (timer :type (integer 0 *) :initially 0) ;initialise time to 0
  (color :type (array t (1000)) :initially white :resizable t);initialize color
  (finish-times-lst :type t :initially nil)
  (vert-ft-lst :type t :initially nil) ;initialize decreasing finish times vertice list to be returned
  (df-forest :type t :initially nil) ;initialize the depth-first forest to be returned by dfs
  (dff-stub :type t :initially nil);temporary storage for answer returned by dfs-visit-lst/dfs-visit
  :inline t)


;DFS (from Cormen)
(mutual-recursion
 (defun dfs-visit-lst (nm g vs g-visit-state)
   (declare (xargs :stobjs (g-visit-state)
                   :guard (and (index2-listp vs nm g)
                               (matrixp nm g))
                   :mode :program))
   (if (endp vs) ;if not more vertices to visit, return book-keeping information
     g-visit-state
     (if (equal 'white (colori (car vs) g-visit-state))
        ;if (car vs) not visited before, then visit it and update book-keeping info
        (let* ((dff-tmp (dff-stub g-visit-state));store intermediate dff which might be reset in dfs-visit
               (g-visit-state (dfs-visit nm g (car vs) g-visit-state))
               (dft (dff-stub g-visit-state)));get dft tree(answer returned by dfs-visit)
          (seq g-visit-state
               (update-dff-stub (append dff-tmp (list dft)) g-visit-state) ;order important 
               (dfs-visit-lst nm g (cdr vs) g-visit-state)))
        (dfs-visit-lst nm g (cdr vs) g-visit-state ))
          ))
   
;visit 'u' in a dfs of 'g', do book-keeping in g-visit-state  
 (defun dfs-visit (nm g u g-visit-state)
   (declare (xargs :stobjs (g-visit-state) 
                   :guard (and (index2p u nm g)
                               (matrixp nm g))
                   :mode :program))
   (let ((adj-vs (adj-vertices u nm g))) ;get adjacent vertices
        (seq g-visit-state
             (update-colori u 'gray g-visit-state)                   ;update color of u to 'gray
             (update-timer (1+ (timer g-visit-state)) g-visit-state) ;update time
             (update-dff-stub nil g-visit-state)                     ;init dfs-forest as nil
             (dfs-visit-lst nm g adj-vs g-visit-state)               ;visit adjacent vertices
             (update-colori u 'black g-visit-state)                  ;update color of visited vertice
             (update-timer (1+ (timer g-visit-state)) g-visit-state) ;update finishing time
             (update-vert-ft-lst (cons u (vert-ft-lst g-visit-state)) 
                                 g-visit-state)                      ;update last finished vertex list 
             (update-finish-times-lst (cons (cons u (timer g-visit-state))
                                            (finish-times-lst g-visit-state))
                                      g-visit-state)                 ;update (vertex . finishing-time) alist
             (update-dff-stub (cons u (dff-stub g-visit-state))
                              g-visit-state))))                      ;update dfs forest stub to get dfs-tree
 
 )

  
;loop over vertices in 'v-lst' in the graph 'g'
(defun dfs-vertex-loop (nm g v-lst g-visit-state)
  (declare (xargs :mode :program
                  :stobjs (g-visit-state)
                  :guard (and (matrixp nm g)
                              (index2-listp v-lst nm g))))
                              
                              
  (if (endp v-lst)
    g-visit-state
    (let ((curr-v (car v-lst)))
      ;only do a dfs-visit of current vertice if it has not been visited before
      ;i.e its color is 'white'.
      (if (equal 'white (colori curr-v g-visit-state))
        (let* ((dff-old (df-forest g-visit-state))
               (g-visit-state (dfs-visit nm g curr-v g-visit-state))
               (dft-stub (dff-stub g-visit-state)) ;get dfs-tree for the current vertice
               (g-visit-state (update-df-forest (append dff-old (list dft-stub)) ;order important
                                                g-visit-state))) ;update dfs forest 
          (dfs-vertex-loop nm g (cdr v-lst) g-visit-state))
        (dfs-vertex-loop nm g (cdr v-lst) g-visit-state)))))
                        


  
;skeleton function calling dfs-vertex-loop
(defun compute-dfs (nm g v-lst g-visit-state)
  (declare (xargs :mode :program
                  :stobjs (g-visit-state)
                  :guard (and (matrixp nm g)
                              (index2-listp v-lst nm g))))
  (let* (;(g-visit-state (init-dfs nm g size g-visit-state))
         (g-visit-state (dfs-vertex-loop nm g v-lst g-visit-state)))
    (mv ;(finish-times-lst g-visit-state) 
        (vert-ft-lst g-visit-state)
        (df-forest g-visit-state)
        g-visit-state)))

;main dfs function using a local stobj to store book-keeping info   
;Symbol * Array2 * Nat-list ->  (Nat-list(decreasing finish times) * DFS-FOREST)
;Takes a matrix 'g' of name 'name' and ordered list of vertices 'v-lst' to visit
;and returns a multiple value: (vertex-list in decreasing finish times order * DFS-FOREST)
(defun dfs (name g v-lst)
  (declare (xargs :mode :program 
                  :guard (and (matrixp name g)
                              (index2-listp v-lst name g))))
  (acl2::with-local-stobj
   g-visit-state
     (mv-let (vert-ft-lst dfs-forest g-visit-state)
             (compute-dfs name g v-lst g-visit-state)
             (cons vert-ft-lst dfs-forest)))) 

(defun add-entry-2g (i nm g adj-vertices-lsti)
  (declare (xargs :guard (and (symbolp nm)
                              (matrixp nm g)
                              (index2p i nm g)
                              (index2-listp adj-vertices-lsti nm g))))
  (if (endp adj-vertices-lsti)
    g
    (let* ((adj-verti (car adj-vertices-lsti))
           (g (aset2 nm g i adj-verti 't)))
      (add-entry-2g i nm g (cdr adj-vertices-lsti)))))
  


;*** START functions for Build a 2-dim array (matrix) from a 1-dim array (adjlist) ***
;Sym * Array2  * Subtype-dtg-st *  Nat -> Array2
(defun make-dt2g-from-dt1g-aux (new-nm new-2g nm dt1g size n)
  (declare (xargs :guard (and (matrixp new-nm new-2g)
                              (array1p nm dt1g)
                              (natp size)
                              (equal size (g-1d-size nm dt1g))
                              (equal size (g-2d-size new-nm new-2g))
                              (down-counterp n size))))
  (if (zp n)
    new-2g
    (let* ((i (- size n))
           (adj-vertices-lsti (aref1 nm dt1g i))
           (new-2g (add-entry-2g i new-nm new-2g adj-vertices-lsti)))
      (make-dt2g-from-dt1g-aux new-nm new-2g nm dt1g size (1- n)))))

;Symbol * Array1 -> Array2 (2d Array representation of adjlist subtype graph with name nm) 
;Complexity same as Tranpose fn: O(|V|+|E|) 
(defun make-dt2g-from-dt1g (new-nm nm dt1g)
  (declare (xargs :guard (and (symbolp new-nm)
                              (array1p nm dt1g))))
  (let* ((size (g-1d-size nm dt1g))
         (new-2g (defarray2 new-nm size nil)))
    (make-dt2g-from-dt1g-aux new-nm new-2g nm dt1g size size)))
;*** END functions for Build a 2-dim array (matrix) from a 1-dim array (adjlist) ***
    

(defun dfs-on-dt1g (nm dt1g)
  (declare (xargs :mode :program
                  :guard (and (symbolp nm)
                              (array1p nm dt1g)
                              )))
  (let* ((size (g-1d-size nm dt1g))
         (v-lst (make-n-upto-list size nil)) ;get vertices in a list
         (new-nm 'subtype-dt2g)
         (new-2g (make-dt2g-from-dt1g new-nm nm dt1g))) ;take 2d impl
    (dfs new-nm new-2g v-lst)))

;Compute SCC of the 1-dim array 'dt1g' (adjlist) of name 'nm'
(defun scc(nm dt1g)
  (declare (xargs :mode :program
                  :guard (and (symbolp nm)
                              (array1p nm dt1g)
                              )))
  (let* ((ord-vlist (car (dfs-on-dt1g nm dt1g)));get the vertices in order of decreasing finish times
         (transpose-2g (transpose-dt1g 'dt2g-t nm dt1g)) ;take the 2d transpose of the original dt1g
         (scc-ans (dfs 'dt2g-t transpose-2g ord-vlist))) ;get back a dfs forest
    scc-ans)) ;return it

;find strongly connected components for the subtype graph
;the subtype adjlist graph alist is stored in the global 
;state -> List of strongly connected components (DFS-FOREST)
(defun scc-top-level (dt1g-alst)
  (declare (xargs :mode :program
                  :guard (alistp dt1g-alst)))
  (if (null dt1g-alst)
    nil
    (let* ((nm 'subtype-dt1g-scc);name it
           (len-dt1g (len dt1g-alst))
           (dt1g (compress1 nm (cons (list :header
                                           :dimensions (list len-dt1g)
                                           :maximum-length (1+ len-dt1g)
                                           :default nil
                                           :name nm)
                                     dt1g-alst))))
      
      (cdr (scc nm dt1g)))));discard the decreasing fin times vertex list and only give back the dfs-forest
  
(defun dfs-on-alst (nm alst)
  (declare (xargs :mode :program
                  :guard (and (symbolp nm)
                              (alistp alst))))
  (if (null alst)
    nil
    (let* ((len-dt1g (len alst))
           (dt1g (compress1 nm (cons (list :header
                                           :dimensions (list len-dt1g)
                                           :maximum-length (1+ len-dt1g)
                                           :default nil
                                           :name nm)
                                     alst)))
           (nm2g (modify-symbol nil nm "-2G"))
           (dt2g (make-dt2g-from-dt1g nm2g nm dt1g)) ;take 2d impl
           (v-lst (strip-cars alst))) ;get vertices in alst
      (dfs nm2g dt2g v-lst))))
           
           
           
      

#|
;(trace$ dfs)

(set-guard-checking :all)
(trace$  ADJ-VERTICES-LOOP)

(let* ((nm 'subtype-dt1g)
       (g (compress1 nm 
                    (cons (list :HEADER
                                 :DIMENSIONS (list 9)
                                 :MAXIMUM-LENGTH 10
                                 :DEFAULT nil
                                 :NAME nm)
                           '((0 . (1))
                             (1 . (4 2 5))
                             (2 . (3 6))
                             (3 . (2 7))
                             (4 . (0 5))
                             (5 . (6))
                             (6 . (5 7))
                             (7 . (7))
                             (8 . nil)))));sole point
       (size (g-1d-size nm g))
       (v-lst (make-n-upto-list size nil)) ;get vertices in a list
       (new-nm 'subtype-dt2g)
       (new-2g (make-dt2g-from-dt1g new-nm nm g)))
  (dfs new-nm new-2g v-lst))


(let* ((nm 'subtype-dt1g)
       (g (compress1 nm 
                    (cons (list :HEADER
                                 :DIMENSIONS (list 9)
                                 :MAXIMUM-LENGTH 10
                                 :DEFAULT nil
                                 :NAME nm)
                           '((0 . (1))
                             (1 . (4 2 5))
                             (2 . (3 6))
                             (3 . (2 7))
                             (4 . (0 5))
                             (5 . (6))
                             (6 . (5 7))
                             (7 . (7))
                             (8 . nil))))));no outgoing edge
    (scc nm g))
    
(let* ((nm 'subtype-dt1g)
      (g (compress1 nm 
                    (cons (list :HEADER
                                 :DIMENSIONS (list 12)
                                 :MAXIMUM-LENGTH 13
                                 :DEFAULT nil
                                 :NAME nm)
                           '((0 . (1 4))
                             (1 . (0))
                             (2 . (3 6 7))
                             (3 . (2 7))
                             (4 . (0 8 9))
                             (5 . ())
                             (6 . (2 7 10))
                             (7 . (2 3 6 10 11))
                             (8 . (4 9))
                             (9 . (4 8))
                             (10 . (6 7))
                             (11 . (7)))))))
    (scc nm g 12))
;==> ((0 1 4 9 8 5 2 7 3 10 6 11)
;      . ( (2 (7 (11) (10 (6)) (3)))
;          (5)
;          (0 (4 (9 (8))) (1))))
|#

         

(set-verify-guards-eagerness 0)

;*** start of initialising a matrix rep from the adjlist rep ***
;Fun call: (tc-init-dt2g-from-dt1g nmI M nmE s1g ctr size)
;Sig: Symbol *  Matrix * Symbol * AdjList * Down-counter * Nat -> Matrix
;Initialise the matrix 'M'(pre-initialised to 'inf) of name 'nmI' using the adjlist 's1g' of 
;name 'nmE' with Down-counter 'ctr' starting from 'size' and size of
;graphs 'size'.

;init for loop for j
(defun tc-init-dt2g-from-dt1g-entry (nmI M i adj-vlsti)
  (declare (xargs :guard (and (matrixp nmI M)
                              (index2p i nmI M)
                              (index2-listp adj-vlsti nmI M))))
  (if (endp adj-vlsti)
    M
    (let* ((M (aset2 nmI M i (car adj-vlsti) 1)) ;init d(i,j) = 1 if (i,j) is an Edge
           (M (aset2 nmI M i i 0))) ;init d(i,i) = 0
      (tc-init-dt2g-from-dt1g-entry nmI M i (cdr adj-vlsti)))))

;init for loop for i
(defun tc-init-dt2g-from-dt1g (nmI M nmE s1g ctr size)
  (declare (xargs :guard (and (matrixp nmI M)
                              (array1p nmE s1g)
                              (down-counterp ctr size)
                              (natp size)
                              (equal size (g-1d-size nmE s1g))
                              (equal size (g-2d-size nmI M)))))
  (if (zp ctr)
    M
    (let* ((i (- size ctr))
           (adj-vlsti (aref1 nmE s1g i))
           (M (tc-init-dt2g-from-dt1g-entry nmI M i adj-vlsti)))
      (tc-init-dt2g-from-dt1g nmI M nmE s1g (1- ctr) size))))
 ;*** end of initialising a matrix rep from the adjlist rep *** 

(defun dist-min (d1 d2)
  (cond ((equal d1 'inf) d2)
        ((equal d2 'inf) d1)
        (t (min d1 d2))))
  
(defun dist-add (d1 d2)
  (cond ((equal d1 'inf) d1)
        ((equal d2 'inf) d2)
        (t (+ d1 d2))))

;*** start Transitive closure for Subtype Graph ***
;Fun call: (subtype-implied-closure implied-nm dag-nm subtype-dag)
;Sig: Symbol * Symbol * Array1 -> Matrix
;Take a 1-dim dag (after SCC ) 'subtype=dag' of name 'dag-nm' to
;build transitive closure matrix of name 'implied-nm' of same size.

;;triple nested loop to calculate closure(no subscript version of floyd-warshall algo)
;nested for loop for j
(defun tc-loop-i-col (nm M k i ctr size)
  (declare (xargs :guard (and (matrixp nm M)
                              (index2p k nm M)
                              (index2p i nm M)
                              (down-counterp ctr size)
                              (natp size)
                              (equal size (g-2d-size nm M))
                              )))
  (if (zp ctr)
    M
    (let* ((j (- size ctr))
           (M (aset2 nm M i j (dist-min 
                               (aref2 nm M i j)
                               (dist-add (aref2 nm M i k)
                                         (aref2 nm M k j))))))
      (tc-loop-i-col nm M k i (1- ctr) size))))

;nested for loop for i
(defun tc-loop-i-row (nm M k ctr size)
  (declare (xargs :guard (and (matrixp nm M)
                              (index2p k nm M)
                              (down-counterp ctr size)
                              (equal size (g-2d-size nm M))
                              (natp size))))
  (if (zp ctr)
    M
    (let* ((row (- size ctr)) 
           (M (tc-loop-i-col nm M k row size size)))
      (tc-loop-i-row nm M k (1- ctr) size))))

;for loop for k
(defun tc-loop-intermediate (nm M ctr size)
  (declare (xargs :guard (and (matrixp nm M)
                              (down-counterp ctr size)
                              (equal size (g-2d-size nm M))
                              (natp size))))
  (if (zp ctr)
    M
    (let* ((k (- size ctr)) 
           (M (tc-loop-i-row nm M k size size)));calculate M(k)
      (tc-loop-intermediate nm M (1- ctr) size))))


;main function calculating transition closure in form of matrix (Tn)
;note that subtype-1g with name nm is not the explicit subtype graph stored
;in globals. It is the minimal dag obtained after doing scc.
(defun subtype-implied-closure (implied-nm dag-nm subtype-dag)
  (declare (xargs :guard (and (symbolp implied-nm)
                              (array1p dag-nm subtype-dag))))
  (let* ((size (g-1d-size dag-nm subtype-dag))
         (implied-M (defarray2 implied-nm size 'inf));initialise with infinity
         (implied-M (tc-init-dt2g-from-dt1g implied-nm implied-M dag-nm subtype-dag size size)));initialise
    (tc-loop-intermediate implied-nm implied-M size size))) ;get closure
;*** end Transitive closure for Subtype Graph ***

#|
;(trace$ tc-loop-intermediate)
(let ((T0 (defarray2 't0 4 'inf))
      (g (compress1 'dtg
             (cons (list :HEADER
                         :DIMENSIONS (list 4)
                         :MAXIMUM-LENGTH 5
                         :DEFAULT nil
                         :NAME 'dtg)
                   '((0 . (0)) 
                     (1 . (1 2 3))
                     (2 . (1 2))
                     (3 . (0 2 3))
                     ) 
                     ))))
  (compress2 't0 (tc-init-dt2g-from-dt1g 't0 T0 'dtg g 4 4)))

(let ((g (compress1 'dtg
             (cons (list :HEADER
                         :DIMENSIONS (list 4)
                         :MAXIMUM-LENGTH 5
                         :DEFAULT nil
                         :NAME 'dtg)
                   '((0 . nil) 
                     (1 . (2 3))
                     (2 . (1))
                     (3 . (0 2))
                     ) 
                     ))))
  (subtype-implied-closure 'implied-dtg 'dtg g))
  
  (subtype-implied-closure
           'implied-subtype-dt2g
            'subtype-dag-dt1g
            '((13)
             (:header :dimensions (14)
                      :maximum-length 15
                      :default nil
                      :name defdata::subtype-dag-dt1g)
             (0 3)
             (1 0)
             (2 3)
             (3 6)
             (4 6)
             (5 6)
             (6 8)
             (7 8)
             (8 13)
             (9 13)
             (10 13)
             (11 13)
             (12 13)))
 |#         


(set-verify-guards-eagerness 2)

;is t1 a subtype of t2, i.e. does (t1, t2) edge exist in the implied subtype adj matrix
(defun is-subtype-in-implied-graph (t1 t2 s-nmI s2gI)
  (declare (xargs :guard (and (matrixp s-nmI s2gI)
                              (index2p t1 s-nmI s2gI)
                              (index2p t2 s-nmI s2gI))))
  (natp (aref2 s-nmI s2gI t1 t2))) ;ofcourse t1 is its own subtype

;collect subtypes of a particular vertex in s2gI
;Fun call: (collect-subtypes s-nmI s2gI v1)
;Sig: Symbol * Matrix * Index2 -> Index2-list
;Takes a subtype implied matrix graph 's2gI' of name 's-nmI'
;and a vertex 'v1' and return a list of subtypes of 'v1'.
(defun collect-subtypes1 (s-nmI s2gI v1 ctr size ans)
 (declare (xargs :guard (and (matrixp s-nmI s2gI)
                              (index2p v1 s-nmI s2gI)
                              (natp ctr)
                              (equal size (car (dimensions s-nmI s2gI))) 
                              (<= ctr size)
                              (index2-listp ans s-nmI s2gI))))
  (if (zp ctr)
    ans
    (let* ((v3 (- size ctr))
           ;is v3 a subtype of v1
           (is-ST (is-subtype-in-implied-graph v3 v1 s-nmI s2gI))) ;ideally it shud be posp cos only self-edge has dist=0
      (collect-subtypes1 s-nmI s2gI v1 (1- ctr) size (if is-ST (cons v3 ans) ans)))));if it is then collect v3

;collect subtypes of index v1 using the implied subtype closure graph 's2gI'
(defun collect-subtypes (s-nmI s2gI v1)
  (declare (xargs :guard (and (matrixp s-nmI s2gI)
                              (index2p v1 s-nmI s2gI))))
  (let ((size (car (dimensions s-nmI s2gI))))
    (collect-subtypes1 s-nmI s2gI v1 size size nil)))


;*** START functions : Transitive closure of Disjoint graph
;Disjointedness relation closure algorithm

;aux fun to mark v3 and v4 disjoint in 'dis2gI' 
(defun mark-disjoint-vertex-vertex (d-nmI dis2gI v3 v4)
  (declare (xargs :guard (and (matrixp d-nmI dis2gI)
                              (index2p v3 d-nmI dis2gI)
                              (index2p v4 d-nmI dis2gI))))
  (let ((dis2gI (aset2 d-nmI dis2gI v3 v4 't))) ;'t means v3 and v4 are disjoint
    dis2gI))


(set-verify-guards-eagerness 0)
;aux fun to mark v3 and v4s disjoint in 'dis2gI' 
(defun mark-disjoint-vertex-vertexlist (d-nmI dis2gI v3 v4s)
  (declare (xargs :guard (and (matrixp d-nmI dis2gI)
                              (index2p v3 d-nmI dis2gI)
                              (index2-listp v4s d-nmI dis2gI)
                              )))
(if (endp v4s)
    dis2gI
    (let* ((dis2gI (mark-disjoint-vertex-vertex d-nmI dis2gI v3 (car v4s))))
      (mark-disjoint-vertex-vertexlist d-nmI dis2gI v3 (cdr v4s)))))

;mark v3s and v4s as pairwise disjoint in the implied disjoint matrix 'dis2gI'
(defun mark-disjoint-vertex-lists (d-nmI dis2gI v3s v4s)
  (declare (xargs :guard (and (matrixp d-nmI dis2gI)
                              (index2-listp v3s d-nmI dis2gI)
                              (index2-listp v4s d-nmI dis2gI))))
  (if (endp v3s)
    dis2gI
    (let* ((dis2gI (mark-disjoint-vertex-vertexlist d-nmI dis2gI (car v3s) v4s)))
      (mark-disjoint-vertex-lists d-nmI dis2gI (cdr v3s) v4s))))
  
;If v1 and v2 are disjoint in the disjoint dag then collect all their
;subtypes using 's2gI' are pairwise mark them disjoint in 'dis2gI'
(defun disjoint-implied-closure-aux2 (d-nmI dis2gI v1 v2 s-nmI s2gI)
  (declare (xargs :guard (and (matrixp d-nmI dis2gI)
                              (matrixp s-nmI s2gI)
                              (index2p v1 s-nmI s2gI)
                              (index2p v2 s-nmI s2gI)
                              (index2p v1 d-nmI dis2gI)
                              (index2p v2 d-nmI dis2gI))))
                              
  (let ((v3s (collect-subtypes s-nmI s2gI v1))
        (v4s (collect-subtypes s-nmI s2gI v2)))
    (mark-disjoint-vertex-lists d-nmI dis2gI v3s v4s))) ;mark v3s and v4s as pairwise disjoint
 
;Loop over all vertices disjoint with v1 and
;1. mark them disjoint in 'dis2gI' 
;2. call disjoint-implied-closure-aux2 to mark all subtypes of v1 and v2 as disjoint
(defun disjoint-implied-closure-aux1 (d-nmI dis2gI s-nmI s2gI v1 adj-vlst-v1)
  (declare (xargs :guard (and (matrixp d-nmI dis2gI)
                              (matrixp s-nmI s2gI)
                             (index2p v1 s-nmI s2gI)
                             (index2p v1 d-nmI dis2gI)
                             (index2-listp adj-vlst-v1 s-nmI s2gI)
                             (index2-listp adj-vlst-v1  d-nmI dis2gI))))
  (if (endp adj-vlst-v1)
    dis2gI
    (let* ((v2 (car adj-vlst-v1)) ;get fist vertex disjoint to v1
           (dis2gI (aset2 d-nmI dis2gI v1 v2 't)) ;init disjoint(i,j) = 't if (i,j) is an Edge in disjoint-g
           (dis2gI (disjoint-implied-closure-aux2 d-nmI dis2gI v1 v2 s-nmI s2gI)));all subtypes of v1, v2 mark as disjoint
      (disjoint-implied-closure-aux1 d-nmI dis2gI s-nmI s2gI v1 (cdr adj-vlst-v1)))))

;loop over all vertices in d1g
(defun disjoint-implied-closure-aux (d-nmI dis2gI dag-nm dag-d1g s-nmI s2gI ctr size)
  (declare (xargs :guard (and (matrixp d-nmI dis2gI)
                              (matrixp s-nmI s2gI)
                              (equal size (car (dimensions s-nmI s2gI))) 
                              (equal size (car (dimensions d-nmI dis2gI))) 
                              (array1p dag-nm dag-d1g)
                              (natp ctr)
                              (<= ctr size))))
  (if (zp ctr)
    dis2gI
    (let* ((i (- size ctr)) ;current vertex in disjoint graph
           (adj-vlsti (aref1 dag-nm dag-d1g i)) ;get all vertices disjoint to i
           (dis2gI (disjoint-implied-closure-aux1 d-nmI dis2gI s-nmI s2gI i adj-vlsti)))
      (disjoint-implied-closure-aux d-nmI dis2gI dag-nm dag-d1g s-nmI s2gI (1- ctr) size))))

;note d-nm d1g is not the explicit disjoint graph stored in globals but
;the dag obtained after performing scc analysis.
(defun disjoint-implied-closure (d-nmI dag-nm dag-d1g s-nmI s2gI)  
  (declare (xargs :guard (and (symbolp d-nmI)
                              (matrixp s-nmI s2gI)
                              (equal (g-1d-size dag-nm dag-d1g)
                                     (g-2d-size s-nmI s2gI))
                              (array1p dag-nm dag-d1g))))
  (let* ((size (car (dimensions s-nmI s2gI)))
         (dis2gI (defarray2 d-nmI size 'nil));init with nil (not disjoint)
         (dis2gI (disjoint-implied-closure-aux d-nmI dis2gI dag-nm dag-d1g s-nmI s2gI size size)));close
    dis2gI))
;*** END functions : Transitive closure of Disjoint graph  
#|
(disjoint-implied-closure
            'implied-disjoint-dt2g
            'disjoint-dag-dt1g
            (compress1 'disjoint-dag-dt1g
                       '((13)
                         (12 10)
                         (:header :dimensions (14)
                          :maximum-length 15
                          :default nil
                          :name disjoint-dag-dt1g)
                         (8 9 11 12 10)
                         (9 11 12 10)
                         (11 12 10)
                         (12 10)))
            'implied-subtype-dt2g
            (compress2 'implied-subtype-dt2g
             '((:header :dimensions (14 14)
                      :maximum-length 197
                      :default inf
                      :name implied-subtype-dt2g)
               ((13 . 13) . inf)
               ((0 . 0) . 0)
               ((0 . 3) . 1)
               ((0 . 6) . 2)
               ((0 . 8) . 3)
               ((0 . 13) . 4)
               ((1 . 0) . 1)
               ((1 . 1) . 0)
               ((1 . 3) . 2)
               ((1 . 6) . 3)
               ((1 . 8) . 4)
               ((1 . 13) . 5)
               ((2 . 2) . 0)
               ((2 . 3) . 1)
               ((2 . 6) . 2)
               ((2 . 8) . 3)
               ((2 . 13) . 4)
               ((3 . 3) . 0)
               ((3 . 6) . 1)
               ((3 . 8) . 2)
               ((3 . 13) . 3)
               ((4 . 4) . 0)
               ((4 . 6) . 1)
               ((4 . 8) . 2)
               ((4 . 13) . 3)
               ((5 . 5) . 0)
               ((5 . 6) . 1)
               ((5 . 8) . 2)
               ((5 . 13) . 3)
               ((6 . 6) . 0)
               ((6 . 8) . 1)
               ((6 . 13) . 2)
               ((7 . 7) . 0)
               ((7 . 8) . 1)
               ((7 . 13) . 2)
               ((8 . 8) . 0)
               ((8 . 13) . 1)
               ((9 . 9) . 0)
               ((9 . 13) . 1)
               ((10 . 10) . 0)
               ((10 . 13) . 1)
               ((11 . 11) . 0)
               ((11 . 13) . 1)
               ((12 . 12) . 0)
               ((12 . 13) . 1))))
|#

(set-verify-guards-eagerness 2)

(defun flatten-tree-tl (bt lst)
  (if (null bt)
    lst
    (if (atom bt)
      (cons bt lst)
      (flatten-tree-tl (car bt) (flatten-tree-tl (cdr bt) lst)))))

(defun flatten-tree (tree)
  (flatten-tree-tl tree nil))

(defun find-min-node-in-list-tl (lst min)
  (declare (xargs :guard (and (natp min)
                              (nat-listp lst))))
  (if(endp lst)
    min
    (find-min-node-in-list-tl (cdr lst) (min (car lst) min))))

(defun find-min-node-in-list (lst)
  (declare (xargs :guard (nat-listp lst)))
  (if (endp lst)
    nil
    (find-min-node-in-list-tl lst (car lst))))

(defun find-min-node-and-flatten-tree (tree)
  (declare (xargs :verify-guards nil))
  (let* ((lst (flatten-tree tree))
         (min (find-min-node-in-list lst)))
    (mv min lst)))


;keep 2 alists. Explicit Alist [TypeName . Explicit Number] and an SCC Alist [Explicit Number . Quotient Number]
;After each SCC, update the SCC Alist, the SCC Alist will give the new dag, both its adjlist and adjmatrix rep, the
;adjmatrix rep will be taken as the initial implicit closure graph.

;Global Explicit Graph will be kept in Alist representation (24-Aug-09)

;Complicated!
;This is the first pass
(defun fill-dag-and-make-mapping-from-explicit-graph-scc1 (scc-nm scc-arr 
                                                          size-e e-g-alist
                                                          up-ctr-dag dag-nm dag 
                                                          e-i-map-nm e-i-map-arr)
  (declare (xargs :verify-guards nil
                  :guard (and (array1p scc-nm scc-arr)
                              (array1p e-i-map-nm e-i-map-arr);explicit-implicit-map [explicit g index . implicit g index] same as dag-map-arr
                              (alistp e-g-alist)              ;but named because implicit graphs are obtained after SCC anyway. 
                              (array1p dag-nm dag)
                              (equal size-e (g-1d-size scc-nm scc-arr))
                              (equal size-e (g-1d-size e-i-map-nm e-i-map-arr))
                              (<= up-ctr-dag (car (dimensions dag-nm dag)))
                              (<= (g-1d-size dag-nm dag) size-e)
                              )))
  (if (endp e-g-alist)
    (mv (compress1 dag-nm dag)  (compress1 e-i-map-nm e-i-map-arr))
    (let* ((curr-entry (car e-g-alist)) ;current entry in explicit graph alist
           (i (car curr-entry))
           (eq-node (aref1 scc-nm scc-arr i));get equivalent node
           (adj-vs-i  (cdr curr-entry))) ;get adjacent vertices to current index
      (if (equal i eq-node) ;if i is same as eq node
        ;no change
        (let* ((dag (aset1 dag-nm dag up-ctr-dag adj-vs-i));fill dag with corresponding entry in explicit graph
               (e-i-map-arr (aset1 e-i-map-nm e-i-map-arr i up-ctr-dag)))
          (fill-dag-and-make-mapping-from-explicit-graph-scc1 scc-nm scc-arr 
                                                             size-e  (cdr e-g-alist)
                                                             (1+ up-ctr-dag) dag-nm dag 
                                                             e-i-map-nm e-i-map-arr))
        ;replace with equivalent node
        ;no update in dag in this pass(because eq node already exists), we basically skip
        ;one index(but later we make another pass to update edges)
        ;Caught Bug, but we should append its adj vertices to the existing eq node.
        ;Note: eq node will always be less than or equal to i(because we employ min) ;TODO.CHECK
        (let* ((dag (aset1 dag-nm dag eq-node (union-equal adj-vs-i (aref1 dag-nm dag eq-node))))
               (e-i-map-arr (aset1 e-i-map-nm e-i-map-arr i (aref1 e-i-map-nm e-i-map-arr eq-node))));update e-i-map
          (fill-dag-and-make-mapping-from-explicit-graph-scc1 scc-nm scc-arr 
                                                             size-e (cdr e-g-alist)
                                                             up-ctr-dag dag-nm dag ;skip one index 
                                                             e-i-map-nm e-i-map-arr))))))

;update the adj-vertex-list in dag(which contained old explicit indexes) 
;using dag-map which maps explicit indexes to new dag indexes
;also remove duplicates
(defun update-edges-using-dag-map (u adj-vs dag-map-nm dag-map-arr ans)
  (declare (xargs :verify-guards nil
                  :guard (and (natp u) ;u is an index in the new dag
                              (index1-listp adj-vs dag-map-nm dag-map-arr);these are old indexes which are to be mapped
                              (nat-listp ans);these are mapped indices in new dag
                              (array1p dag-map-nm dag-map-arr)
                              )))
  (if (endp adj-vs)
    ;;remove self-edges (these will arise when u collapse scc edges)
    ;;and also remove duplicates
    (remove1 u (remove-duplicates ans))
    (let* ((v (car adj-vs))
           (v-mapped (aref1 dag-map-nm dag-map-arr v))
           (ans (append ans (list v-mapped)))) ;in order!
      (update-edges-using-dag-map u (cdr adj-vs) dag-map-nm dag-map-arr ans))))
           

(defun fill-dag-from-dag-map-and-explicit-graph (down-ctr-dag size-dag 
                                                   dag-first-pass-nm dag-first-pass-finished
                                                   dag-nm dag 
                                                   dag-map-nm dag-map-arr)
   (declare (xargs :verify-guards nil
                   :guard (and (equal size-dag (g-1d-size dag-nm dag))
                               (down-counterp down-ctr-dag size-dag)
                               (array1p dag-first-pass-nm dag-first-pass-finished)
                               (array1p dag-map-nm dag-map-arr)
                               (array1p dag-nm dag))))
   (if (zp down-ctr-dag)
     (compress1 dag-nm dag)
     (let* ((i (- size-dag down-ctr-dag)) ;current index in dag graph
           (adj-vs (aref1 dag-first-pass-nm dag-first-pass-finished i))
           (adj-vs-updated (update-edges-using-dag-map i adj-vs dag-map-nm dag-map-arr nil))
           (dag (aset1 dag-nm dag i adj-vs-updated)));populate new dag
       ;walk down the one dim array
       (fill-dag-from-dag-map-and-explicit-graph (1- down-ctr-dag) 
                                                   size-dag
                                                   dag-first-pass-nm dag-first-pass-finished
                                                   dag-nm dag 
                                                   dag-map-nm dag-map-arr))))   
   
  
;dag-map-arr which maps explicit index to dag indexes
(defun fill-dag-and-make-mapping-from-explicit-graph-scc (scc-nm scc-arr 
                                                         size-e e-g-alist
                                                         dag-first-pass-nm dag-first-pass size-dag  
                                                         dag-nm
                                                         dag-map-nm dag-map-arr)
  (declare (xargs :verify-guards nil
                  :guard (and (array1p scc-nm scc-arr)
                              (array1p dag-map-nm dag-map-arr)
                              (alistp e-g-alist)
                              (array1p dag-first-pass-nm dag-first-pass)
                              (equal (g-1d-size scc-nm scc-arr)
                                     (g-1d-size dag-map-nm dag-map-arr)))))
                              
  (mv-let (dag-first-pass-finished dag-map-arr)
   ;first pass: walk down explicit graph e-g and fill dag and also make dag-map
          (fill-dag-and-make-mapping-from-explicit-graph-scc1 scc-nm scc-arr 
                                                              size-e e-g-alist
                                                              0 dag-first-pass-nm dag-first-pass 
                                                              dag-map-nm dag-map-arr)
   ;second pass, walk down the dag to update edges in dag using dag-map-arr
          (let* ((dag (defarray1 dag-nm size-dag nil));init
                 (dag (fill-dag-from-dag-map-and-explicit-graph 
                       size-dag size-dag
                       dag-first-pass-nm dag-first-pass-finished
                       dag-nm dag 
                       dag-map-nm dag-map-arr)))
            (mv dag dag-map-arr))))
                        

;Make SCC alist from SCCs of the original explicit subtype dt1g stored in globals.
; scc-alist is an alist storing: ((Explicit-index of node . Equivalent index of node) ...)
(defun fill-scc-alist-from-scc-component (representative equivalent-nodes scc-alist)
  (declare (xargs :verify-guards nil
                  :guard (and (natp representative)
                              (nat-listp equivalent-nodes)
                              (alistp scc-alist))))
  (if (endp equivalent-nodes)
    scc-alist
    (let ((scc-alist (acons (car equivalent-nodes) ;key
                            representative ;val
                            scc-alist)))
      (fill-scc-alist-from-scc-component representative
                                           (cdr equivalent-nodes)
                                           scc-alist
                                           ))))
                              

;FIll alist 'scc-alist' of name 'scc-nm'  using data from sccs
;scc-alist maps nodes(in the explicit dt1g) to their eq node. 
;'sccs' are just a dfs-forest, i.e a list of dfs-trees
(defun fill-scc-alist-from-sccs (sccs scc-alist)
  (declare (xargs :verify-guards nil
                  :guard (and (alistp scc-alist)
                              (true-listp sccs))))
  (if (endp sccs)
    scc-alist
    (let* ((scc (car sccs)));take first dfs tree
      (if (null scc)
        (fill-scc-alist-from-sccs (cdr sccs) scc-alist);skip if null, shjouldnt occur ideally
        (mv-let (representative equivalent-nodes)
                (find-min-node-and-flatten-tree scc)
                (let* ((scc-alist (fill-scc-alist-from-scc-component representative
                                                                   equivalent-nodes
                                                                   scc-alist)))
                  
                  (fill-scc-alist-from-sccs (cdr sccs) scc-alist)))))))

;copied from symbol-btree.lisp                                                                                                          
(progn
(defun merge-nat-alist-< (l1 l2 acc)
  (declare (xargs :guard (and (nat-alistp l1)
                              (nat-alistp l2)
                              (true-listp acc))
                  :measure (+ (len l1) (len l2))))
  (cond ((endp l1) (revappend acc l2))
        ((endp l2) (revappend acc l1))
        ((< (caar l1) (caar l2))
         (merge-nat-alist-< (cdr l1) l2 (cons (car l1) acc)))
        (t (merge-nat-alist-< l1 (cdr l2) (cons (car l2) acc)))))
(local (defthm len-evens-<
         (implies (consp (cdr x))
                  (< (len (evens x))
                     (len x)))
         :hints (("Goal" :induct (evens x)))
         :rule-classes :linear))

(local (defthm len-evens-<=
         (<= (len (evens x))
             (len x))
         :hints (("Goal" :induct (evens x)))
         :rule-classes :linear))

(defun merge-sort-nat-alist-< (l)
  (declare (xargs :guard (nat-alistp l)
                  :verify-guards nil
                  :measure (len l)))
  (cond ((endp (cdr l)) l)
        (t (merge-nat-alist-< (merge-sort-nat-alist-< (evens l))
                              (merge-sort-nat-alist-< (odds l))
                              nil))))
)
;end of copy paste

(defun make-dag-and-dag-map-from-explicit-graph-alist (sccs e-g-alist dag-nm dag-map-nm)
  (declare (xargs :verify-guards nil
                  :guard (and (symbolp dag-nm)
                              (symbolp dag-map-nm)
                              (nat-alistp e-g-alist)
                              (true-listp sccs))))
  (let* ((size-e (len e-g-alist))
         (size-dag (len sccs));number of dfs trees i.e number of distinct dag nodes
         (dag-first-pass-nm 'dag-first-pass-tmp-name)
         (dag-first-pass (defarray1 dag-first-pass-nm size-e nil));init
         (scc-nm 'scc-maparr)
         ;;maps nodes(in the explicit dt1g) to their eq node. 
         (scc-alist (fill-scc-alist-from-sccs sccs nil))
         ;;init dag-map-arr which maps explicit index to dag indexes
         (dag-map-arr (defarray1 dag-map-nm size-e nil)))
    (fill-dag-and-make-mapping-from-explicit-graph-scc scc-nm (alst-to-array1 scc-nm (len scc-alist) scc-alist)
                                                       size-e  (merge-sort-nat-alist-< e-g-alist)
                                                       dag-first-pass-nm dag-first-pass size-dag
                                                       dag-nm
                                                       dag-map-nm dag-map-arr)))
#|
(untrace$ fill-dag-and-make-mapping-from-explicit-graph-scc1  fill-scc-alist-from-sccs)

(DEFDATA::MAKE-DAG-AND-DAG-MAP-FROM-EXPLICIT-GRAPH-ALIST
          '((2 (3)) (0 (1 (4))))
          '((0 1 4) (1 0 4) (2 3) (3 2) (4 0 1 4))
          'DEP-DAG-NAME
          'IND-QUOTIENT-MAP-NM)

(DEFDATA::MAKE-DAG-AND-DAG-MAP-FROM-EXPLICIT-GRAPH-ALIST
            '((6 (7)) (4 (5)) (3) (2) (1) (0))
            '((0)
             (1)
             (2)
             (3)
             (4 5)
             (5 4)
             (6 7)
             (7 6))
            'DEP-DAG-NAME 'IND-QUOTIENT-MAP-NM)


((ATOM . 13)
 (STRING . 12)
 (CHARACTER . 11)
 (SYMBOL . 10)
 (BOOLEAN . 9)
 (ACL2-NUMBER . 8)
 (COMPLEX-RATIONAL . 7)
 (RATIONAL . 6)
 (NEGATIVE-RATIO . 5)
 (POSITIVE-RATIO . 4)
 (INTEGER . 3)
 (NEG . 2)
 (POS . 1)
 (NAT . 0))


(trace$ 
        fill-dag-and-make-mapping-from-explicit-graph-scc
        fill-dag-and-make-mapping-from-explicit-graph-scc1
        update-dag-from-dag-map-and-explicit-graph)
(MAKE-DAG-AND-DAG-MAP-FROM-EXPLICIT-GRAPH-ALIST
            '((12)
             (11)
             (10)
             (9)
             (7)
             (5)
             (4)
             (2)
             (1)
             (0)
             (3)
             (6)
             (8)
             (13))
            
            '((10 13)
             (8 13)
             (5 6)
             (3 6)
             (2 3)
             (4 6)
             (7 8)
             (6 8)
             (9 13)
             (12 13)
             (11 13)
             (13)
             (0 3)
             (1 0))
            'SUBTYPE-DAG-DT1G
            'S-EXPLICIT-IMPLIED-INDEX-MAP)
(MAKE-DAG-AND-DAG-MAP-FROM-EXPLICIT-GRAPH-ALIST
        '((12)
         (11)
         (10)
         (9)
         (8)
         (5)
         (0 (4) (7 (3 (6))))
         (2)
         (1))
        
        '((0 7 4)
         (1)
         (2)
         (3 7 6)
         (4 0)
         (5)
         (6 7 3)
         (7 1 2 0 6 7 3)
         (8 7 3)
         (9 7 4)
         (10 7 6)
         (11 3 4 5 6)
         (12 8 9 10))
        'DEP-DAG-NAME 'IND-QUOTIENT-MAP-NM)

|#
 

;*** TOP-LEVEL CALLS ******

;Now top-level calls will be:
;1. Is T1 a subtype of T2?
;2. Are T1 and T2 disjoint?
;*3. Add an node (type) to both the graphs
;*4. Add an edge to subtype-graph
;*5. Add an edge to disjoint-graph

;starred calls will compute scc using the explicit graphs stored in global
;and then create a dag temporarily and then 'create' the closure graphs to be stored in globals.

(defun is-disjoint-in-implied-graph (t1 t2 d-nmI d2gI)
  (declare (xargs :guard (and (matrixp d-nmI d2gI)
                              (index2p t1 d-nmI d2gI)
                              (index2p t2 d-nmI d2gI))))
  (or (aref2 d-nmI d2gI t1 t2)
      (aref2 d-nmI d2gI t2 t1))) ;simulate undirected graph (Possible BUG)

(defun is-disjoint (t1 t2 wrld)
  (declare (xargs :verify-guards nil
                  :guard (and (symbolp t1)
                              (symbolp t2)
                              (plist-worldp wrld))))
  (let* ((e-vert-map (table-alist 'explicit-vertex-index-map wrld)) ;get map
         (t1-entry (assoc-eq t1 e-vert-map))
         (t2-entry (assoc-eq t2 e-vert-map)))
    (if (and e-vert-map t1-entry t2-entry) ;only bother if they exist
      (let* ((t1-e-index (cdr t1-entry));get its explicit index
             (e-i-map-nm-alst (table-alist 'explicit-implicit-index-map wrld)) ;get implicit index map
             (e-i-map-nm (caar e-i-map-nm-alst)) ;get name of 1-dim array storing map
             (e-i-map-arr (cdar e-i-map-nm-alst)) ;get the 1-dim array
             (t1-index (aref1 e-i-map-nm e-i-map-arr t1-e-index)) ;get the implicit index
             (t2-e-index (cdr t2-entry)) ;get second explicit index
             (t2-index (aref1 e-i-map-nm e-i-map-arr t2-e-index)) ;get its implicit index
             (nm-d2gI (table-alist 'implied-disjoint-dt2g wrld)) ;get implied disjoint dtg alst
             (d-nmI (caar nm-d2gI)) ;get name of g
             (d2gI (cdar nm-d2gI))) ;get implied g
        (is-disjoint-in-implied-graph t1-index t2-index d-nmI d2gI))
      nil))) ;safely say that they are not disjoint?? can result in BUG?

;is t1 a subtype of t2 i.e is t1 < t2
(defun is-subtype (t1 t2 wrld)
  (declare (xargs :verify-guards nil
                  :guard (and (plist-worldp wrld)
                              (symbolp t1)
                              (symbolp t2))))
  (let* ((e-vert-map (table-alist 'explicit-vertex-index-map wrld)) ;get map
        (t1-entry (assoc-eq t1 e-vert-map))
        (t2-entry (assoc-eq t2 e-vert-map)))
    (if (and e-vert-map t1-entry t2-entry) ;only bother if they exist
      (let* ((t1-e-index (cdr t1-entry));get its explicit index
             (e-i-map-nm-alst (table-alist 'explicit-implicit-index-map wrld)) ;get implicit index map
             (e-i-map-nm (caar e-i-map-nm-alst));get name of 1-dim array storing map
             (e-i-map-arr (cdar e-i-map-nm-alst));get the 1-dim array
             (t1-index (aref1 e-i-map-nm e-i-map-arr t1-e-index));get the implicit index
             (t2-e-index (cdr t2-entry)) ;get second explicit index
             (t2-index (aref1 e-i-map-nm e-i-map-arr t2-e-index)) ;get its implicit index
             (nm-s2gI (table-alist 'implied-subtype-dt2g wrld));get implied subtype dtg alst
             (s-nmI (caar nm-s2gI));get name of implied subtype g storing TC
             (s2gI (cdar nm-s2gI)));get implied s2g
        (is-subtype-in-implied-graph t1-index t2-index s-nmI s2gI))
      nil)))






;WORLD CHANGING FUNCTION - EXTERNAL
;Just add a node to both subtype and disjoint alist explicit graphs with nil adj-vertices
;coding style adapted from 'using TABLES efficiently' doc entry
(defmacro add-datatype-node-batch (T1)
  (declare (xargs :guard (and (symbolp T1))))
  `(make-event
    (let* ((e-vert-map (table-alist 'explicit-vertex-index-map (w state))) ;get map
           (index (len e-vert-map)) ;another way is to use last, but i guess this is faster?
           (already-exists (assoc-eq ',T1 e-vert-map)))
      (if already-exists
        '(value-triple :Redundant-operation)
        `(progn 
          (table explicit-vertex-index-map ',',T1 ,index :put)
          (table subtype-dtg-alst ,index nil :put)
          (table disjoint-dtg-alst ,index nil :put))))))




;append the entry of datatype graph alist at the t1-index with t2-index-lst
;note that the ordering in the alist should not matter, because it will ultimately
;be converted into 1-dim array using compress1, but will it pose any performance issue?
;impl using tail-recursion
;walk through dtg-alst, reconstructing it into ans, find t1-index,
;add (union) the corresponding entry with t2-index-lst into ans, ordering is not maintained. BEWARE!
;Recognize redundant ops, but is it helping things get faster? maybe!
;NO LONGER USED
(defun add-to-dtg-alist (t1-index t2-index-lst dtg-alst ans)
  (declare (xargs :verify-guards nil
                  :guard (and (natp t1-index)
                              (alistp dtg-alst)
                              (nat-listp t2-index-lst))))
  (cond ((endp dtg-alst)
         ans) ;return accumulated updated alist
        ((eql t1-index (caar dtg-alst))
         ;add the t1-index entry in ans and then append the remaining dtg-alst, because we know there are no duplicate keys!?
         (append (acons t1-index 
                        (if (equal (cdar dtg-alst) t2-index-lst)
                          (union-equal (cdar dtg-alst) t2-index-lst)
                          t2-index-lst)
                        ans) 
                 (cdr dtg-alst)))
        (t (add-to-dtg-alist t1-index t2-index-lst (cdr dtg-alst) (cons (car dtg-alst) ans)))))


;WORLD CHANGING FUNCTION - EXTERNAL
;add edge from T1 to T2. T1 -> T2. hence T1 is a subtype of T2.
(defmacro add-edge-to-subtype-graph-batch (T1 T2)
  (declare (xargs :guard (and (symbolp T1)
                              (symbolp T2))))
  `(make-event
    (let* ((wrld (w state))
           (e-vert-map (table-alist 'explicit-vertex-index-map wrld)) ;get map
           (t1-entry (assoc-eq ',t1 e-vert-map))
           (t2-entry (assoc-eq ',t2 e-vert-map)))
      (if (and e-vert-map t1-entry t2-entry) ;only bother if they exist
        (let* ((t1-index (cdr t1-entry));assoc returns the whole (key . value) entry, we only need the val
               (t2-index (cdr t2-entry))
               (s-dtg-alst (table-alist 'subtype-dtg-alst wrld))
               (t1-adj-is (cdr (assoc-equal t1-index s-dtg-alst))))
          `(progn
            (table subtype-dtg-alst ',t1-index ',(union-equal t1-adj-is (list t2-index)) :put)
            (value-triple :EDGE-ADDED)))
        '(value-triple :FAILED-TO-ADD-EDGE)))))

;WORLD CHANGING FUNCTION - EXTERNAL
(defmacro add-edge-to-disjoint-graph-batch (T1 T2)
  (declare (xargs :guard (and (symbolp T1)
                              (symbolp T2))))
  `(make-event
    (let* ((wrld (w state))
           (e-vert-map (table-alist 'explicit-vertex-index-map wrld)) ;get map
           (t1-entry (assoc-eq ',t1 e-vert-map))
           (t2-entry (assoc-eq ',t2 e-vert-map)))
      (if (and e-vert-map t1-entry t2-entry) ;only bother if they exist
        (let* ((t1-index (cdr t1-entry))
               (t2-index (cdr t2-entry))
               (d-dtg-alst (table-alist 'disjoint-dtg-alst wrld))
               (t1-adj-is (cdr (assoc-equal t1-index d-dtg-alst))))
          `(progn
            (table disjoint-dtg-alst ',t1-index ',(union-equal t1-adj-is (list t2-index)) :put)
            (value-triple :EDGE-ADDED)))
        '(value-triple :FAILED-TO-ADD-EDGE)))))

(defun map-assoc-eq-only-value (keys alst)
  (declare (xargs :guard (and (symbol-listp keys)
                              (symbol-alistp alst))))
  (if (endp keys)
    nil
    (cons (cdr (assoc-eq (car keys) alst))
          (map-assoc-eq-only-value (cdr keys) alst))))


;;WORLD CHANGING FUNCTION - EXTERNAL
(defmacro add-edges-to-disjoint-graph-batch (T1 T2s)
  (declare (xargs :guard (and (symbolp T1)
                              (symbol-listp T2s))))
  `(make-event
    (let* ((wrld (w state))
           (e-vert-map (table-alist 'explicit-vertex-index-map wrld)) ;get map
           (t1-entry (assoc-eq ',t1 e-vert-map)))
      (if (and e-vert-map t1-entry)
        (let* ((t1-index (cdr t1-entry))
               (t2-index-lst (map-assoc-eq-only-value ',T2s e-vert-map))
               (d-dtg-alst (table-alist 'disjoint-dtg-alst wrld))
               (t1-adj-is (cdr (assoc-equal t1-index d-dtg-alst))))
           `(progn
             (table disjoint-dtg-alst ',t1-index ',(union-equal t1-adj-is t2-index-lst) :put)
             (value-triple :EDGES-ADDED)))
        '(value-triple :FAILED-TO-ADD-EDGES))))) ;TODO: Should i show error (in red)??



(defun maparr-equal1 (nm1 m1 nm2 m2 d-ctr len1)
   (declare (xargs :guard (and (array1p nm1 m1)
                               (array1p nm2 m2)
                               (equal len1 (g-1d-size nm1 m1))
                               (equal len1 (g-1d-size nm2 m2))
                               (natp d-ctr)
                               (<= d-ctr len1))))
   (if (zp d-ctr)
     t
     (let ((i (- len1 d-ctr)))
       (and (equal (aref1 nm1 m1 i)
                   (aref1 nm2 m2 i))
            (maparr-equal1 nm1 m1 nm2 m2 (1- d-ctr) len1)))))   

(defun maparr-equal (nm1 m1 nm2 m2)
  (declare (xargs :guard (and (array1p nm1 m1)
                              (array1p nm2 m2))))
  (if (equal (g-1d-size nm1 m1)
             (g-1d-size nm2 m2))
    (let ((len1 (g-1d-size nm1 m1)))
      (maparr-equal1 nm1 m1 nm2 m2 len1 len1))
    nil))
               
;for help in tracing
(defun my-equal (x1 x2)
 (equal x1 x2))

;;MAIN WORLD CHANGING FUNCTION - EXTERNAL
;SYNC the implicit graphs with the explicit graphs by computing SCC and closure algorithms
(defmacro sync-globals-for-dtg ()
  `(make-event
    (acl2::state-global-let*
     ((acl2::guard-checking-on t));for fast code
     (let* ((wrld (w state))
           (s-e-i-map-nm-l 'explicit-implied-index-map-local);global, to be computed
           (d-e-i-map-nm 'd-explicit-implied-index-map-local); to be computed
           (s2gI-nm-l 'implied-subtype-dt2g-local);global, to be computed 
           (d2gI-nm-l 'implied-disjoint-dt2g-local);global, to be computed
           (s-e-i-map-nm 'explicit-implied-index-map);global, to be computed
           (s2gI-nm 'implied-subtype-dt2g);global, to be computed 
           (d2gI-nm 'implied-disjoint-dt2g);global, to be computed
           (s1g-dag-nm 'subtype-dag-dt1g);to be created
           (d1g-dag-nm 'disjoint-dag-dt1g);to be computed
           (s-dtg-alst (table-alist 'subtype-dtg-alst wrld));global, to be used
           (d-dtg-alst (table-alist 'disjoint-dtg-alst wrld));global, to be used
           (sccs (scc-top-level s-dtg-alst)));Calculate SCCs of the subtype datatype graph
      (mv-let 
       (s1g-dag s-e-i-maparr) ;from scc create a dag and a explcit-to-implicit index map to reflect it
       (make-dag-and-dag-map-from-explicit-graph-alist sccs s-dtg-alst s1g-dag-nm s-e-i-map-nm-l)
       (mv-let
        (d1g-dag d-e-i-maparr);from scc create a dag and a explcit-to-implicit index map to reflect it
        (make-dag-and-dag-map-from-explicit-graph-alist sccs d-dtg-alst d1g-dag-nm d-e-i-map-nm)
        (if (maparr-equal s-e-i-map-nm-l s-e-i-maparr d-e-i-map-nm d-e-i-maparr) ;they should be equal
          (let* ((s-e-i-maparr (compress1 s-e-i-map-nm-l s-e-i-maparr)) ;BUG SOLVED due to this
                 ;(s-e-i-maparr-old (cdar (table-alist 'explicit-implicit-index-map wrld)))
                 ;(s-closure-old (cdar (table-alist 'implied-subtype-dt2g wrld)))
                 ;(d-closure-old (cdar (table-alist 'implied-disjoint-dt2g wrld)))
                 (s-closure (compress2 s2gI-nm-l (subtype-implied-closure s2gI-nm-l s1g-dag-nm s1g-dag)));helps output browsing
                 (d-closure (compress2 d2gI-nm-l (disjoint-implied-closure d2gI-nm-l d1g-dag-nm d1g-dag s2gI-nm-l s-closure))))
            (value 
             `(progn  ;add the name and 1-dim array (but make sure you have them compressed, so we have fast arrays)
;,(if (my-equal s-e-i-maparr-old s-e-i-maparr)
;  '(value-triple :REDUNDANT-explicit-implicit-index-map)
               (table explicit-implicit-index-map ',s-e-i-map-nm (compress1 ',s-e-i-map-nm ',s-e-i-maparr) :put)
;)
;,(if (my-equal s-closure-old s-closure)
;  '(value-triple :REDUNDANT-implied-subtype-dt2g)
               (table implied-subtype-dt2g ',s2gI-nm (compress2 ',s2gI-nm ',s-closure) :put) ;add/update the subtype datatype closure
; )
;,(if (my-equal d-closure-old d-closure)
;  '(value-triple :REDUNDANT-implied-disjoint-dt2g)
               (table implied-disjoint-dt2g ',d2gI-nm (compress2 ',d2gI-nm ',d-closure) :put) ;add/update the disjoint datatype closure
;)
               (value-triple :DTG-GLOBALS-ARE-IN-SYNC)))) ;Display success of the operation
          (value '(value-triple :ERROR-explicit-implicit-index-mapping-not-same-for-disjoint-and-subtype-graphs)))))))))#|ACL2s-ToDo-Line|#


#|
;GLOBAL CHANGE FUNCTION - EXTERNAL
(defun sync-globals-for-dtg-deprecated (state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (acl2::state-global-let*
   ((guard-checking-on nil)) 
   (let* ((s-e-i-map-nm 'explicit-implied-index-map);global, to be computed
          (d-e-i-map-nm 'd-explicit-implied-index-map); to be computed
          (s2gI-nm 'implied-subtype-dt2g);global, to be computed 
          (d2gI-nm 'implied-disjoint-dt2g);global, to be computed
          (s1g-dag-nm 'subtype-dag-dt1g);to be created
          (d1g-dag-nm 'disjoint-dag-dt1g);to be computed
          (s-dtg-alst (get-subtype-dtg-alst state));global, to be used
          (d-dtg-alst (get-disjoint-dtg-alst state));global, to be used
          (sccs (scc-top-level s-dtg-alst)));Calculate SCCs of the subtype datatype graph
     (mv-let 
      (s1g-dag s-e-i-maparr) ;from scc create a dag and a explcit-to-implicit index map to reflect it
      (make-dag-and-dag-map-from-explicit-graph-alist sccs s-dtg-alst s1g-dag-nm s-e-i-map-nm)
      (mv-let
       (d1g-dag d-e-i-maparr);from scc create a dag and a explicit-to-implicit index map to reflect it
       (make-dag-and-dag-map-from-explicit-graph-alist sccs d-dtg-alst d1g-dag-nm d-e-i-map-nm)
       (if (maparr-equal s-e-i-map-nm s-e-i-maparr d-e-i-map-nm d-e-i-maparr) ;they should be equal
         (let* ((s-closure (compress2 s2gI-nm (subtype-implied-closure s2gI-nm s1g-dag-nm s1g-dag)))
                (d-closure (compress2 d2gI-nm (disjoint-implied-closure d2gI-nm d1g-dag-nm d1g-dag s2gI-nm s-closure))))
           (er-progn 
            (set-explicit-implied-index-map s-e-i-maparr);update the e-i-map array
            (set-implied-subtype-dt2g  s-closure) ;update the subtype datatype closure
            (set-implied-disjoint-dt2g  d-closure) ;update the disjoint datatype closure
            (value ':DTG-GLOBALS-ARE-IN-SYNC))) ;Display success of the operation
         (er soft 'sync-globals-for-dtg 
             "The explicit-implicit index mapping should be same for disjoint and subtype graphs. BUG in code!")))))))
  
|#      
         

      
