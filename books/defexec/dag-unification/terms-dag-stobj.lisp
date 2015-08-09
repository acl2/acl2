;;; ============================================================================
;;; terms-dag-stobj.lisp
;;; Título: The single--threaded object {\tt terms-dag}
;;; ============================================================================

#| To certify this book:

(in-package "ACL2")

(certify-book "terms-dag-stobj")
|#

(in-package "ACL2")

(include-book "dag-unification-rules")

;;; ============================================================================
;;;
;;; 0) Introducción
;;;
;;; ============================================================================

;;; This short book ({\tt terms-dag-stobj.lisp}) contains the definition
;;; of the {\tt terms-dag} single--threaded object ({\em stobj}). This
;;; stobj will be used in a unification algorithm (described in the book
;;; {\tt unification-dag-st.lisp}) to store the terms as directed
;;; acyclic graphs. We also define some usuful functions for reasoning
;;; and computing with the stobj.


;;; The stobj is defined as follows, containing only one resizable array
;;; field, called @dag@:

(defstobj terms-dag
  (dag :type (array t (0))
       :resizable t))

;;; This array field will be used to store term dags, with the following
;;; conventions (see the book {\tt dags.lisp}) for more details. Viewing
;;; terms as graphs, every cell of the arry represents a node of the
;;; graph. That is, {\tt (dagi h g)} stores a symbol (function or
;;; variable) and information about the neighbors of the node @h@.

;;; There are two kinds of nodes: function nodes and variable nodes.
;;; Depending on the kind of a node @h@, we will store in the array cell
;;; @h@ the following information:

;;; *)
;;;   Variable nodes. They can be of two forms:
;;; *.*)
;;;              @N@ (integer numbers): bound variables. They are bound to
;;;              the node @N@ (these nodes are called "IS" nodes).
;;; *.*)
;;;              {\tt (X . T)} : they represent an unbound variable
;;;              @X@. These nodes are called "VARIABLES".
;;; *.-)
;;; *)
;;;   Non-variable nodes (function nodes): {\tt (F. L)} (where @L@ is
;;;   different from @T@), interpreted as the function symbol @F@ and the
;;;   list @L@ of its neighbors (its arguments). These are "NON-VARIABLE"
;;;   nodes.
;;; -)

;;; Examples (representing the array as a list):

;;; Graph representing the term $f(h(x), h(y), k(l(x,y)))$:
; ((F 1 3 5) (H 2) (X . T) (H 4) (Y . T) (K 6) (L 7 8) 2 4)

;;; Graph representing the term $f(h(x,x), h(y,y), k(l(x,y)))$:
; ((F 1 4 7) (H 2 3) (X . T) 2 (H 5 6) (Y . T) 5 (K 8) (L 9 10) 2 5)




;;; A function to display the array:

(defun show-dag (min max terms-dag)
  (declare (xargs :mode :program
		  :stobjs terms-dag))
  (if (<= min max)
      (cons (dagi min terms-dag)
	    (show-dag (1+ min) max terms-dag))
    nil))



;;; Reset the stobj:

(defun reset-unif-problem (min max terms-dag)
  (declare (xargs :mode :program
		  :stobjs (terms-dag)))
  (if (not (<= min max))
      terms-dag
    (let* ((terms-dag (update-dagi min nil terms-dag)))
      (reset-unif-problem (1+ min) max terms-dag))))



;;; Some macros, to improve readability:


(defmacro dag-variable-p (x)
  `(equal (cdr ,x) t))

(defmacro dag-args (x)
  `(cdr ,x))

(defmacro dag-symbol (x)
  `(car ,x))

(defmacro dag-bound-p (x)
  `(integerp ,x))

(defmacro terms-dag-graph (td)
  `(nth 0 ,td))



;;; The following function {\tt dag-component-st} obtains a list with
;;; same components than the array stored by @terms-dag@. Note that it
;;; is not possible to define it in a simpler way:


(defun dag-component-st-aux (n terms-dag)
  (declare (xargs :stobjs terms-dag
		  :measure (nfix (- (dag-length terms-dag) n))
		  :guard (natp n)))
  (if (and (integerp n) (< n (dag-length terms-dag)))
    (cons (dagi n terms-dag)
	  (dag-component-st-aux (+ n 1) terms-dag))
    nil))

(defun dag-component-st (terms-dag)
  (declare (xargs :stobjs terms-dag))
  (dag-component-st-aux 0 terms-dag))


;;; Due to the restrictions in the use of a stobj, we can not define the
;;; function {\tt dag-component-st} simply as {\tt (nth 0
;;; terms-dag)}. But we can prove in the logic that it is equal to that
;;; expression. The following lemmas are needed to show that, as
;;; established by the theorem {\tt dag-component-st-main-property}

(local
 (defun list-components-nth (n l)
   (declare (xargs :measure (nfix (- (len l) n))))
   (if (and (integerp n) (< n (len l)))
       (cons (nth n l) (list-components-nth (+ n 1) l))
     nil)))

(local
 (defun list-components (n l)
   (if (zp n)
       l
     (list-components (- n 1) (cdr l)))))


(local
 (defthm list-components-defined-with-nth
   (implies (and (< n (len l)) (consp l))
	    (equal (cons (nth n l) (list-components n (cdr l)))
		   (list-components n l)))))


(local
 (defthm list-components-nth-list-components-for-true-listp
   (implies (and (true-listp m) (natp n))
	    (equal (list-components-nth n m)
		   (list-components n m)))))

(local
 (defthm nth-fix-true-list
   (equal (nth n (fix-true-list l))
	  (nth n l))))

(local
 (defthm list-components-nth-true-listp
   (equal (list-components-nth n (fix-true-list l))
	  (list-components-nth n l))
   :rule-classes nil))


(local
 (defthm list-components-nth-main-property
   (equal (list-components-nth 0 l) (fix-true-list l))
   :hints (("Goal" :use (:instance list-components-nth-true-listp (n 0))))))


(local
 (defthm list-components-nth-aa-as-list-aux
   (equal (dag-component-st-aux n terms-dag)
	  (list-components-nth n (nth 0 terms-dag)))))


(defthm dag-component-st-main-property
  (equal (dag-component-st terms-dag)
         (fix-true-list (terms-dag-graph terms-dag))))

;;; This theorem {\tt dag-component-st-main-property} is crucial when we
;;; "export" the results about some functions defined on term dags
;;; representing the dag as a list to analogue functions defined on
;;; single--threaded object (see the book {\tt
;;; dag-unification-st.lisp}).

(in-theory (disable dag-component-st))

;;; ===============================================================

