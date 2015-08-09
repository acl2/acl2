#|$ACL2s-Preamble$;
;;Amr helmy
;;31st october 2007
;; Rev. 31 Jan. 2008 by JS
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book  "GeNoC-nodeset")
(include-book "GeNoC-misc")
(include-book "GeNoC-types")
(include-book "make-event/defspec" :dir :system)#|ACL2s-ToDo-Line|#


(defspec GenericNodesetbuffers
  (((StateGenerator * *) => *)
   ;; Function StateGenerator generates
   ;; a state from two parameters
   ;; the first one is the parameter used to
   ;; generate the list of the nodes of the network
   ((ValidstateParamsp * *) => *)
   ;; recognizer for valid parameters
   ((loadbuffers * * *)=> *)
   ;; update the state
   ;; inputs = node_id (in NodeSet), a message and a state
   ;; return a new state
   ;;((unloadbuffers * *) => *))
   ((readbuffers * *) => *)
  ;; read the state
  ;; input = node_id (in NodeSet) and a state
  ;; returns the state entry corresponding to node_id
  ((generate-initial-ntkstate * *) => *))
  ;; put the list of transaction on the network
  ;;
  ;; A network state is a list of node representing the state of the network
  ;; a state entry  has the form :
  ;;           (             (coor (...))
  ;;                    (Buffers ...)
  ;;            )
  ;;
  ;;example :
  ;;        ( ((coor (2 3)) (buffers 4 3))
  ;;      ((coor (3 2)) (buffers 5 3))
  ;;      ((coor (5 4)) (buffers 2 3)))
  ;;
  ;; n: is the number of buffers on this specific coordinate
  ;; m: is the actual numbr of free buffers on this specific coordinate
  ;; example : ((coord (2 3)) (buffers 4 2))
  ;;                 this means that the node coordinate is (2 3) and that
  ;;it has 4 buffers of which only 2 are free
  ;; The functions in the defspec serve for the following


  ;;---------------------- Witness Functions -----------
  ;; Local functions for the next witness function
  ;; this function does not have to be instantiated
  (local
   (defun stategeneratorlocal (nodeset y)
     (if (endp nodeset)
         nil
       (append (list (list (list 'Coor  (car nodeset)) (list 'Buffers y)))
               (StateGeneratorlocal (cdr nodeset) y)))))


  (local
   ;;a function taking a natural as input and generating a list of nodes
   (defun StateGenerator (x y)
     (let ((nodes (nodesetgenerator x)))
       (stategeneratorlocal nodes y))))

  ;; A function that verifies the the input parameters of the state
  ;; genration function

  (local
   (defun ValidStateParamsp (x y)
     (declare (ignore y))
     (validparamsp x)))

  (local
   (defun loadbuffers (coordinates msgid ntkstate)
     (declare (ignore coordinates msgid))
     ;; this function takes as input the coordinates of a node and
     ;; loads a buffer
     ;; in case there's still free buffers
     ntkstate))

  (local
   (defun readbuffers (node_id ntkstate)
     (declare (ignore node_id))
     (car ntkstate)))

  (local
   (defun generate-initial-ntkstate (talst ntkstate)
     (declare (ignore talst))
     ntkstate))

;;---------------------- End Witness Functions -----------

  (local
   (defthm validstate-stategenerator
     (validstate (stategeneratorlocal listx params2))))

  ;; theoreme to prove the correctness
  (defthm nodeset-generates-valid-resources
    (implies (ValidStateParamsp params params2)
             (ValidState (StateGenerator params params2))))

  ;; The funciton loadbuffers returns a validstate
  (defthm validstate-loadbuffers-statep
    (implies  (validstate ntkstate)
              (validstate (loadbuffers coordinates msgid ntkstate))))

  (local
   (defthm valid-entry-car-stategeneratorlocal
     (validstate-entryp (car (stategeneratorlocal p1 p2)))))

  (defthm Readbuffers-valid-entryp
    ;; reading a valid state for a valid node
    ;; returns a valid state entry
    (let ((ntkstate (StateGenerator p1 p2))
          (NodeSet (NodeSetGenerator p1)))
      (implies (and (ValidStateParamsp p1 p2)
                    (member-equal node_id NodeSet))
               (ValidState-entryp (Readbuffers node_id ntkstate)))))


  ;; this proof obligation is important to do the link between the
  ;; nodesetgenerator and the stategenerator
  ;; it states that The Validity of the stategenerator inputs must
  ;; imply the validity of
  ;; the input of the nodeset
  (defthm Validstateparamsp-implies-validparamsp
    (implies (ValidStateparamsp  param1 param2)
             (Validparamsp  param1)))

  ;;this is an intermediate theorem used for the next one
  (local
   (defthm getcoordinates-stategenerator-local
     (implies (true-listp listx)
              (equal (getcoordinates (stategeneratorlocal listx params2))
                     listx))))

  ;; We prove the equality between the nodeset and the coordinates in
  ;; the stategenerator

  (defthm nodesetp-coordinates
    (implies  (ValidStateparamsp  param1 param2)
              (equal  (getcoordinates (StateGenerator  param1 param2))
                      (nodesetgenerator param1)))
    :hints (("Goal"
             :do-not '(generalize))))

  (defthm subsets-are-valid-resources
    ;; this lemma is used to prove that routes are made of valid state nodes
    (implies (and (ValidState nodelist)
                  (subsetp y nodelist))
             (ValidState y)))
  )