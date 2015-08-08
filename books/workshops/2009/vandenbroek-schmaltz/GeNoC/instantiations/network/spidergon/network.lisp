#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "../../../generic-modules/network");
(include-book "../../../generic-modules/types");

(defun node-connections (id n topo)
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
           (cw (if (equal nodeid (1- (* 4 n)))
                 (acons (list nodeid 'cw ) (list 0 'ccw ) topo)
                 (acons (list nodeid 'cw ) (list (1+ nodeid) 'ccw ) topo)))
           (ccw (if (equal nodeid 0)
                  (acons (list nodeid 'ccw ) (list (1- (* 4 n)) 'cw ) cw )
                  (acons (list nodeid 'ccw ) (list (1- nodeid) 'cw ) cw)))
           (acr  (acons (list nodeid 'acr ) (list (mod (+ (* 2 n)  nodeid) (* 4 n)) 'acr ) ccw))
           (local (acons (list nodeid 'loc )(list nodeid nil ) acr)))

      (node-connections (1- id) n local))))

(defun spidergon-topology (x)
  (node-connections (* 4 x) x nil))

(defun nodeMemory_t (x y)
 (if (zp x)
   (acons x y  nil)
   (acons x y (nodeMemory_t (1- x) y))))

(defun spidergon-nodeMemory (x)
  (nodeMemory_t (1- (* 4 x)) x))

(definstance GenericNetwork check-compliance-spidergon-network
  :functional-substitution
  ((topology spidergon-topology)
   (nodeMemory spidergon-nodeMemory)))#|ACL2s-ToDo-Line|#


