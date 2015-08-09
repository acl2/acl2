#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "../../../generic-modules/network");

;;2 nodeset generator
;;x-dim-gen generates the nodes along a y coordinate
(defun x-dim-gen (X y max)
  ;; generate the nodes along the x-dim, y is a constant
  (if (zp X)
    nil
    (let* ((curX (1- X))
           (conn (acons (list (list curX y) 'loc ) (list (list curX y) nil ) nil))
           (conn (if (< y max)
                   (acons (list (list curX y) 'S ) (list (list curX (1+ Y)) 'N) conn)
                   conn))
           (conn (if (< curX max)
                  (acons (list (list curX y) 'E ) (list (list X Y) 'W) conn)
                   conn))
           (conn (if (> y 0)
                   (acons (list (list curX y) 'N ) (list (list curX (1- Y)) 'S) conn)
                   conn))
           (conn (if (> curX 0)
                   (acons (list (list curX y)  'W ) (list (list (1- curX) Y) 'E) conn)
                   conn)))
      (append conn (x-dim-gen curX y max)))))

(defun coord-generator (X Y max)
  ;; generate a list of coordinates
  (if (zp Y)
      nil
    (append (x-dim-gen X (1- y) max)
            (coord-generator X (1- Y) max))))

(defun 2Dmesh-topology (x)
  ;; Generates a list of the connection pressent in the network.
  ;; Example:
  ;; (((0 0) LOC) (0 0) NIL)
  ;; (((0 0) S) (0 1) N)
  ;; ...
  ;; (((1 1) LOC) (1 1) NIL)
  ;; (((1 1) N) (1 0) S)
  ;; (((1 1) W) (0 1) E))
  ;;
  ;; Arguments:
  ;; - topo : Initialisation argument of the model. Often this is the size of the network.
  (reverse (coord-generator x x (1- x))))



(defun mem-gen-Y (x y)
    (if (zp y)
      nil
      (acons (list (1- x) (1- y)) nil (mem-gen-Y x (1- y)))))


(defun mem-gen (x y)
    (if (zp x)
      nil
      (append (mem-gen-Y x y) (mem-gen (1- x) y))))


(defun 2Dmesh-nodeMemory (x)
 (reverse (mem-gen x x)))#|ACL2s-ToDo-Line|#


(definstance GenericNetwork check-compliance-2dmesh-network
  :functional-substitution
  ((topology 2Dmesh-topology)
   (nodeMemory 2Dmesh-nodeMemory)))



