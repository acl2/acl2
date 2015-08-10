#|$ACL2s-Preamble$;
;; Julien Schmaltz
;; July 28th 2005
;; File: 2D-mesh-nodeset.lisp
;; We define here the coordinates of the nodes in
;; a 2D mesh.
;; We show that it is a valid instance of the
;; generic nodeset definition.
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")#|ACL2s-ToDo-Line|#


;-------------------------------------
; the instantiations used in this file
;------------------------------------
(defmacro inst-NodeSetGenerator (P)
         (list '2DMesh-NodeSetGenerator P))
(defmacro inst-Validparamsp (Params)
         (list '2DMesh-Validparamsp Params))
(defmacro inst-Nodep (x)
         (list '2DMesh-Nodep x))
(defmacro inst-Nodesetp (x)
         (list '2DMesh-NodeSetp x))



(include-book "../../../generic-modules/GeNoC-nodeset")

;; functions to put elsewhere
(defun rev (x)
  ;; reverse a true-list
  (if (endp x)
      nil
    (append (rev (cdr x)) (list (car x)))))


;; 1 type of nodes (NodeSetp)
;; ------------------------------
;; in the mesh topology, nodes are coordinates
(defun 2DMesh-Nodep (x)
  (and (consp x)
       (consp (cdr x))
       (null (cddr x))
       (natp (car x)) (natp (cadr x))))

(defun 2DMesh-NodeSetp (x)
  (if (endp x)
      t
    (and (2DMesh-Nodep (car x))
         (2DMesh-NodeSetp (cdr x)))))

;; this function will be mapped to NodeSetp in
;; the functional instanciation

;; 2 nodeset generator (NodeSetGenerator)
;; ---------------------------------------

(defun x-dim-gen (X y)
  ;; generate the nodes along the x-dim, y is a constant
  (declare (xargs :guard (and (natp X) (natp y))))
  (if (zp X)
      nil
    (cons (list (1- X) y) (x-dim-gen (1- X) y))))

(defthm all-coordinatep-x-dim-gen
  ;; x-dim-gen produces valid coordinates
  (implies (and (natp x) (natp y))
           (2DMesh-NodeSetp (x-dim-gen x y))))


(defun coord-generator-1 (X Y)
  ;; generate a list of coordinates
  (if (zp Y)
      nil
    (append (x-dim-gen X (1- y))
            (coord-generator-1 X (1- Y)))))

(defthm valid-coordinates-coord-gen-1
  (implies (and (natp x) (natp y))
           (2DMesh-NodeSetp (coord-generator-1 x y))))

(defun coord-gen (X Y)
  (rev (coord-generator-1 X Y)))

(defthm valid-coordinates-coord-gen
  (implies (and (natp x) (natp y))
           (2DMesh-NodeSetp (coord-gen x y))))

(defthm truelistp-coord-gen
  (true-listp (coord-gen x y))
  :rule-classes :type-prescription
  )

;; as coord-gen is non-recursive function, we disable it
(in-theory (disable coord-gen))


;; 3. Parameters
;; ------------

(defun 2DMesh-Validparamsp (Params)
  ;; hyps on the parameters
  ;; Params is a consp as well as its cdr
  ;; each element of the cons is a natural
  (and (consp Params) (consp (cdr Params)) (null (cddr Params))
       (natp (car Params)) (natp (cadr Params))))

;; P is a list (x, y)
(defun 2DMesh-NodeSetGenerator (P)
  ;; NODE SET GENERATOR
  (coord-gen (car P) (cadr P)))

;; this function will be mapped to
;; NodeSetGenerator

;; 4. Prove the last constraint (subsetp)
;; --------------------------------------
(defthm subsets-are-valid-mesh-nodesetp
   (implies (and (2DMesh-NodeSetp x)
                 (subsetp y x))
            (2DMesh-NodeSetp y)))



;; the next lemma is needed for the instances (like XY Routing)
;(defthm 2d-mesh-nodesetgenerator
;  (implies (mesh-hyps params)
;           (2d-mesh-nodesetp (mesh-nodeset-gen params))))

;; 5. check that these definitions are compliant
;;    with the generic encapsulate
;; ---------------------------------------------
(definstance GenericNodeSet Mesh-Complies-NodeSet
  :functional-substitution
  ((NodeSetGenerator 2DMesh-NodeSetGenerator)
   (ValidParamsp 2DMesh-Validparamsp)
   (Nodep 2DMesh-Nodep)
   (Nodesetp 2DMesh-NodeSetp)))

