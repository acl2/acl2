#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "make-event/defspec"  :dir :system)
(include-book "types");

(defspec GenericNetwork
  (((topology *) => *)
   ((nodeMemory *) => *))

  ;;2 nodeset generator
  ;;x-dim-gen generates the nodes along a y coordinate
  (local (defun x-dim-gen (X y max)
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
               (append conn (x-dim-gen curX y max))))))

  (local (defun coord-generator (X Y max)
           ;; generate a list of coordinates
           (if (zp Y)
             nil
             (append (x-dim-gen X (1- y) max)
                     (coord-generator X (1- Y) max)))))

  (local (defun topology (x)
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
           ;; - x : Initialisation argument of the model. Often this is the size of the network.
           (reverse (coord-generator x x (1- x)))))

  (local (defun nodeMemory (x)
           (if (zp x)
             nil
             (acons x nil (nodeMemory (1- x))))))
  )





