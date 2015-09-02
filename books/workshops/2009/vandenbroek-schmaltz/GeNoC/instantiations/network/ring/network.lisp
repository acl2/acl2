#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "../../../generic-modules/network");
(include-book "../../../generic-modules/types");


(defun node-connections (id max topo)
  ;; Build a list with node ids the node with id x is connected to.
  ;; This first value will be nil since the local port is not connected to another node.
  ;; examples: (connections 2 3) = (nil 1 3), (connections 3 3) = (nil 2 0)
  ;;
  ;; Arguments:
  ;; - node : a node
  ;; - ports :  alist of ports
  (if (zp id)
    topo
    (let* ((nodeid (1- id))
           (cw (if (equal nodeid (1- max))
                 (acons (list nodeid 'cw ) (list 0 'ccw ) topo)
                 (acons (list nodeid 'cw ) (list (1+ nodeid) 'ccw ) topo)))
           (ccw (if (equal nodeid 0)
                  (acons (list nodeid 'ccw ) (list (1- max) 'cw ) cw )
                  (acons (list nodeid 'ccw ) (list (1- nodeid) 'cw ) cw)))

           (local (acons (list nodeid 'loc ) (list nodeid nil ) ccw)))

      (node-connections (1- id) max local))))

(defun ring-topology (x)
  (node-connections x x nil))

(defun nodeMemory_t (x y)
 (if (zp x)
   (acons x y  nil)
   (acons x y (nodeMemory_t (1- x) y))))

(defun ring-nodeMemory (x)
  (nodeMemory_t (1- x) x))

(definstance GenericNetwork check-compliance-ring-network
  :functional-substitution
  ((topology ring-topology)
   (nodeMemory ring-nodeMemory)))