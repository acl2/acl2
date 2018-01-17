(in-package #:metabang.gsn)

#|
Need to account for different kinds of links
  in gsn-nodes-from-json, need to return pairs of node and attributes

hash-table for nodes to prevent duplicates
queue or stack for nodes to expand
hash-table for links (triples of A link B?) to handle duplicates
|#

(defgeneric expand-node (context node)
  )

(defgeneric find-neighbors (context node)
  )

(defgeneric expand-node-p (context node)
  )

(defgeneric add-node (context node)
  )

(defgeneric add-link (context node neighbor direction)
  )

(defgeneric update-node-data (context node data)
  )

(defclass abstract-context ()
  ())

(defclass gsn-context (abstract-context)
  ())

(defparameter +gsn-root+ "http://socialgraph.apis.google.com/")

(defmethod expand-node ((context abstract-context) node)
  (bind (((to from) (find-neighbors context node)))
    (dolist (neighbor to)
      (add-node context neighbor)
      (add-link context node neighbor :to))
    (dolist (neighbor from)
      (add-node context neighbor)
      (add-link context node neighbor :from))))



(defmethod find-neighbors ((context gsn-context) node)
  (bind (((result headers stream)
	  (http-get 
	   (format nil "~alookup?edo=1&edi=1&pretty=1&q=~a" 
		   +gsn-root+ node)))
	 json)
    (unwind-protect 
	 (setf json (json:decode-json stream))
      (close strea))
    (update-node-data context node json)		      
    (list (gsn-nodes-from-json json :to)
	  (gsn-nodes-from-json json :from))))
  
(gsn-nodes-from-json x :from)  

(defun gsn-test (who)
  (destructuring-bind (result headers stream)
      (http-get 
       (format nil "http://socialgraph.apis.google.com/lookup?edo=1&edi=1&pretty=1&q=~a" who))
    (declare (ignore result headers))
    (json:decode-json stream)))

(assoc :nodes_referenced 
       (assoc :nodes (gsn-test "TWITTER.COM/GWKING") :key #'first))


(setf x (gsn-test "TWITTER.COM/GWKING")) 
