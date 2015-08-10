#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "network")
(include-book "departure")
(include-book "router")

(defmacro instantiateStepnetwork_t (genoc router)
`(defun ,(packn (list genoc '-stepnetwork_t)) (nstlist ntkmem ntkst)
    ;; This function applies the function Router on each of the nodes in nodeslist.
    ;; It returns the updated list of ports and nodememory
    ;;
    ;; Arguments:
    ;; - nodeslist : a list nodes
    ;; - nodesMemory : list of nodememories.
    ;; - nodesMemory : list of ports.
      (if (endp nstlist)
      (mv ntkst ntkmem)
      (mv-let (newnst newnmem)
              (,(packn (list router '-router)) (car nstlist) (cdr (assoc-equal (port-id (caar nstlist)) ntkmem)))
              (mv-let (newntkst newntkmem)
                      (,(packn (list genoc '-stepnetwork_t)) (cdr nstlist) ntkmem ntkst)
                      (mv (ports-update  newntkst newnst)
                          (put-assoc-equal (port-id newnst) newnmem newntkmem)))))))


(defmacro instantiateStepnetwork (genoc)
 `(defun ,(packn (list genoc '-stepnetwork)) (ntkst ntkmem topology)
    ;; Thansform the list of ports into a list of nodes and aplies the steprnetwork_t function.
    ;; Afterwards the list of ports returned is porcessed by the function updateNeigbours.
    ;;
    ;; Arguments:
    ;; - transactions : a list of transactions.
    ;; - nodes : the set of existing nodes.
    ;; - topology : The topology of fthe network.
    (mv-let (newntkst newntkmem)
            (,(packn (list genoc '-stepnetwork_t)) (ports-nodelist ntkst nil) ntkmem ntkst)
            (mv (updateNeighbours newntkst topology) newntkmem))))

(defmacro instantiateGenoc_t (genoc depart)
  `(defun ,(packn (list genoc '-genoc_t)) (transactions ntkst ntkMem arrived time topology timeLimit accup)
     ;; This function recusively applies the function stepnetwork on the nodes. Before step networks is applied the functions
     ;; Depart insert new transmissions into the nodes.
     ;;
     ;; Arguments:
     ;; - transactions : a list of transactions.
     ;; - nodes : the set of existing nodes.
     ;; - nodes : the set of existing nodes.
     ;; - arrived : the list of arrived transmissions.
     ;; - time : the time of the simulation step.
     ;; - topology : The topology of fthe network.
     ;; - timeLimit : the maximum time the model.
     ;; - accup : Accumulator list of the nodes after each call.
    (if (zp timeLimit)
      (mv arrived transactions accup)
      (mv-let (departing delayed)
              (,(packn (list depart '-depart)) (ntkst-clearLocalOutputs ntkst) transactions time)
              (mv-let (newntkst newNtkMem)
                      (,(packn (list genoc '-stepnetwork)) departing ntkMem topology)
                      (,(packn (list genoc '-genoc_t))  delayed
                                newntkst
                                newNtkMem
                                (append (list (list 'TIME time (ntkst-arrive newntkst))) arrived)
                                (1+ time)
                                topology
                                (1- timeLimit)
                                (append (list (list 'TIME time  newntkst)) accup)))))))

  (defmacro instantiateGenoc (genoc network)
    `(defun ,(packn (list genoc '-genoc)) (transactions param timeLimit)
       ;; The main function.
       ;;
       ;; Arguments:
       ;; - transactions : a list of transactions.
       ;; - param : The argument to initialize the network often the network size.
       ;; - timeLimit : the maximum time the model.
       (,(packn (list genoc '-genoc_t)) transactions
        (nodes (,(packn (list network '-topology)) param))
        (,(packn (list network '-nodeMemory)) param)
        nil
        '0
        (,(packn (list network '-topology)) param)
        timeLimit
        nil)))

  (defun updateNodePorts (ntkst new address)
    ;; Update the port(s) from ntkst that are connected to new.
    ;; Update means setting the remote status and if it is an input port update the data field.
    ;;
    ;; Arguments:
    ;; - ntkst : The list of ntkst that should be updated if connected to new
    ;; - new : The port with the new data
    ;; - adress : The id of the node new originates from.
    (if (endp ntkst)
      nil
      (let ((nst (car ntkst)))
        (if (and (equal (port-NodeAddress nst) address)
                 (not (equal (port-dir nst) (port-dir new))))
          (cons (port-updateStatus (if (equal (port-dir nst) 'in)
                                     (port-updateData nst (port-data new))
                                     nst)
                                   (update-nth 1 (car (port-status new)) (port-status nst)))
                (cdr ntkst))
          (cons nst (updateNodePorts (cdr ntkst) new address))))))

  (defun updateNeighbours_t (portlist ntkst topology)
    ;; This function applies the function updateNeighboursNode on each of the nodes in nodeslist.
    ;; - portslist : a list ports. This variable is used for the recursion.
    ;; - ports : a list ports. This portiablke is changed and returned
    ;; - topology : The topology of fthe network.
    (if (endp portlist)
      ntkst
      (let* ((nst (car portlist))
             (newntkst  (updateNodePorts ntkst nst (cdr (assoc-equal (port-nodeAddress nst) topology)))))
        (updateNeighbours_t (cdr portlist) newntkst topology))))

  (defun updateNeighbours (ntkst topology)
    ;; Wrapper function of updateNeighbours_t.
    ;; The function updates the status fields of the input and output ports of different nodes that are connected to each other.
    ;;
    ;; - ports : a list ports.
    ;; - topology : The topology of fthe network.
    (updateNeighbours_t ntkst ntkst topology))


  (defun stepnetwork_t (nstlist ntkmem ntkst)
    ;; This function applies the function Router on each of the nodes in nodeslist.
    ;; It returns the updated list of ports and nodememory
    ;;
    ;; Arguments:
    ;; - nodeslist : a list nodes
    ;; - nodesMemory : list of nodememories.
    ;; - nodesMemory : list of ports.

    (if (endp nstlist)
      (mv ntkst ntkmem)
      (mv-let (newnst newnmem)
              (router (car nstlist) (cdr (assoc-equal (port-id (caar nstlist)) ntkmem)))
              (mv-let (newntkst newntkmem)
                      (stepnetwork_t (cdr nstlist) ntkmem ntkst)
                      (mv (ports-update  newntkst newnst)
                          (put-assoc-equal (port-id (car newnst)) newnmem newntkmem))))))

  (defun stepnetwork (ntkst ntkmem topology)
    ;; Thansform the list of ports into a list of nodes and aplies the steprnetwork_t function.
    ;; Afterwards the list of ports returned is porcessed by the function updateNeigbours.
    ;;
    ;; Arguments:
    ;; - transactions : a list of transactions.
    ;; - nodes : the set of existing nodes.
    ;; - topology : The topology of fthe network.
    (mv-let (newntkst newntkmem)
            (stepnetwork_t (ports-nodelist ntkst nil) ntkmem ntkst)
            (mv (updateNeighbours newntkst topology) newntkmem)))

  (defun genoc_t (transactions ntkst ntkMem arrived time topology timeLimit accup)
    ;; This function recusively applies the function stepnetwork on the nodes. Before step networks is applied the functions
    ;; Depart insert new transmissions into the nodes.
    ;;
    ;; Arguments:
    ;; - transactions : a list of transactions.
    ;; - ntkst : list of ports. This tis the complete network state.
    ;; - nodes : the set of existing nodes.
    ;; - arrived : the list of arrived transmissions.
    ;; - time : the time of the simulation step.
    ;; - topology : The topology of fthe network.
    ;; - timeLimit : the maximum time the model.
    ;; - accup : Accumulator list of the nodes after each call.
    (if (zp timeLimit)
      (mv arrived transactions accup)
      (mv-let (departing delayed)
              (depart (ntkst-clearLocalOutputs ntkst) transactions time)
              (mv-let (newntkst newNtkMem)
                      (stepnetwork departing ntkMem topology)
                      (genoc_t  delayed
                                newntkst
                                newNtkMem
                                (append (list (list 'TIME time (ntkst-arrive newntkst))) arrived)
                                (1+ time)
                                topology
                                (1- timeLimit)
                                (append (list (list 'TIME time  newntkst)) accup))))))

  (defun genoc (transactions param timeLimit)
    ;; The main function.
    ;;
    ;; Arguments:
    ;; - transactions : a list of transactions.
    ;; - param : The argument to initialize the network often the network size.
    ;; - timeLimit : the maximum time the model.
    (genoc_t transactions
             (nodes (topology param))
             (nodeMemory param)
             nil
             '0
             (topology param)
             timeLimit
             nil))
