#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "make-event/defspec"  :dir :system)
(include-book "../../routing/XY/XYRouting")
(include-book "../../departure/simple/simple-R4D")
(include-book "../../scheduling/circuit-switching-global/circuit")
(include-book "../../simulation/simple/simple")
(include-book "../../interfaces/dummy-interfaces/interfaces-computes")
(include-book "ordinals/lexicographic-ordering" :dir :system)
(include-book "../../../generic-modules/GeNoC")
(include-book "sets")

;;-----------------------------
;; Defintion of GeNoC
;;-----------------------------


; Instantiation of GeNoC with a 2DMesh, XY Routing and packet scheduling,
; a simple network state (each node has a constant number of buffers)
; and simple R4D
(defun simple-genoc_t (missives nodeset measure trlst accup time ntkstate order)
  ;; the composition of routing and scheduling is built by function genoc_t.
  ;; it takes as arguments:
  ;; missives: List of missives
  ;; nodeset:  NodeSet
  ;; measure:  The measure that is decreased by the scheduler
  ;; trlst:    Accumulator of arrived travels
  ;; accup:    Accumulator of networkstates for simulation
  ;; time:     Notion of time
  ;; ntkstate: Network state
  ;; order:    Ordering
  ;; it returns:
  ;; - the arrived messages
  ;; - the en route messages
  ;; - the network state accumulator for simulation

  ;; the measure is set to the measure defined by the scheduler
  (declare (xargs :measure (acl2-count measure)
                  :hints (("Goal" :use (:instance ct-measure-decreases
                                               (trlst (xy-routing-top (mv-nth 1 (inst-readyfordeparture missives nil nil time)) nodeset)))))))
  (if (endp missives)
    ;; no more messsages to send
    (mv trlst nil accup)
    ;; else
    (mv-let (delayed departing)
            ;; call R4D to determine which missives are ready for departure
            (inst-readyfordeparture missives nil nil time)
            ;; determine set of routes for all departing missives
            (let ((v (XY-routing-top departing nodeset)))
              ;; check if it is possible to schedule
              (cond ((not (inst-legal-measure measure v nodeset ntkstate order))
                     ;; illegal measure supplied
                     (mv trlst missives accup))
                    ((inst-scheduling-assumptions v nodeset ntkstate order)
                     ;; schedule and recursivily call genoc_t
                     (mv-let (newtrlst arrived newmeasure newntkstate)
                             (inst-scheduling v nodeset ntkstate order)
                             (simple-genoc_t  (append newtrlst delayed)
                                              nodeset
                                              newmeasure
                                              (append arrived trlst)
                                              (append accup (list (simple-extract-simulation newntkstate)))
                                              (+ 1 time)
                                              newntkstate
                                              (inst-get_next_priority order))))
                    (t
                     ;; scheduler has instructed to terminate
                     (mv trlst missives accup)))))))


; talst     List of transactions
; p1:       Parameter for generating nodes, a coordinate (X Y)
; p2:       Parameter for generating ntkstate, isn't used and can be anything
; order:    Ordering. Isn't used, can be anything
(defun simple-genoc (talst p1 p2 order)
  ;; main function
  (if (simple-ValidStateParamsp p1 p2)
    (mv-let (responses aborted accup)
            (simple-genoc_t ;; compute traveling missives
                            (computetmissives talst)
                            ;; compute nodeset
                            (2DMesh-Nodesetgenerator p1)
                            ;; compute initial measure
                            (inst-initial-measure (xy-routing-top (computetmissives talst) (2DMesh-Nodesetgenerator p1))
                                      (2DMesh-Nodesetgenerator p1)
                                      (inst-generate-initial-ntkstate talst (inst-StateGenerator p1 p2))
                                      order)
                            ;; accumulator for arrived travels
                            nil
                            ;; accumulator for simulation
                            nil
                            ;; time
                            '0
                            ;; compute initial ntkstate
                            (inst-generate-initial-ntkstate talst (inst-StateGenerator p1 p2))
                            order)
            (declare (ignore accup))
            (mv (computeresults responses) aborted))
    (mv nil nil)))

;; non-tail version of first value of genoc: the arrived messages
(defun simple-genoc_t-nt-mv-nth0 (missives nodeset measure time ntkstate order)
  (declare (xargs :measure (acl2-count measure)
                  :hints (("Goal" :use (:instance ct-measure-decreases
                                               (trlst (xy-routing-top (mv-nth 1 (inst-readyfordeparture missives nil nil time)) nodeset)))))))
  (if (endp missives)
    nil
    (mv-let (delayed departing)
            (inst-readyfordeparture missives nil nil time)
            (let ((v (XY-routing-top departing nodeset)))
              (cond ((not (inst-legal-measure measure v nodeset ntkstate order))
                     nil)
                    ((inst-scheduling-assumptions v nodeset ntkstate order)
                     (mv-let (newtrlst arrived newmeasure newntkstate)
                             (ct-scheduling v nodeset ntkstate order)
                           (append
                             (simple-genoc_t-nt-mv-nth0  (append newtrlst delayed)
                                                         nodeset
                                                         newmeasure
                                                         (+ 1 time)
                                                         newntkstate
                                                         (inst-get_next_priority order))

                            arrived )))
                    (t
                     nil))))))
;; proof equality between tail and non-tailversion of GeNoC_t
(defthm simple-genoc_t-nt-mv-nth0=tail-mv-nth0
  (equal (mv-nth 0 (simple-genoc_t missives nodeset measure trlst accup time ntkstate order))
         (append (simple-genoc_t-nt-mv-nth0 missives nodeset measure time ntkstate order)
                 trlst))
  :hints (("Goal" :in-theory (disable xy-routing-top ct-scheduling))))

;; non-tail version of second value of genoc: the delayed messages
(defun simple-genoc_t-nt-mv-nth1 (missives nodeset measure time ntkstate order)
  (declare (xargs :measure (acl2-count measure)
                  :hints (("Goal" :use (:instance ct-measure-decreases
                                               (trlst (xy-routing-top (mv-nth 1 (inst-readyfordeparture missives nil nil time)) nodeset)))))))
  (if (endp missives)
    nil
    (mv-let (delayed departing)
            (inst-readyfordeparture missives nil nil time)
            (let ((v (XY-routing-top departing nodeset)))
              (cond ((not (inst-legal-measure measure v nodeset ntkstate order))
                     missives)
                    ((inst-scheduling-assumptions v nodeset ntkstate order)
                     (mv-let (newtrlst arrived newmeasure newntkstate)
                             (ct-scheduling v nodeset ntkstate order)
                             (declare (ignore arrived))
                             (simple-genoc_t-nt-mv-nth1  (append newtrlst delayed)
                                                         nodeset
                                                         newmeasure
                                                         (+ 1 time)
                                                         newntkstate
                                                         (inst-get_next_priority order))))
                    (t
                     missives))))))
;; proof equality between tail and non-tailversion of GeNoC_t
(defthm simple-genoc_t-nt-mv-nth1=tail-mv-nth1
  (equal (mv-nth 1 (simple-genoc_t missives nodeset measure trlst accup time ntkstate order))
         (simple-genoc_t-nt-mv-nth1 missives nodeset measure time ntkstate order))
  :hints (("Goal" :in-theory (disable xy-routing-top ct-scheduling))))


;;----------------------------------------
;; DEADLOCK FREEDOM FOR CIRCUIT SWITCHING
;;----------------------------------------
;; The proof is structured as follows:
;; 1.) We define a property P which implies deadlockfreedom
;; 2.) We proof P implies a possible route
;; 3.) We prove P is preserved by GeNoC, i.e., if
;;     it holds, then after one GeNoC-cycle it still holds.
;; 4.) We prove P implies en route is empty, by proving that
;;     scheduling always provides a legal measure.
;; 5.) We prove that if en route is empty, then arrived is full.
;;
;; Property P is defined as:
;; (and ---the nodeset doesn't contain nil---
;;      (not (member-equal nil nodeset))
;;      ---each node has *num-of-buffers* buffers---
;;      (buffersize ntkstate *num-of-buffers*)
;;      ---trlst has no travel whose frm is nil---
;;      (not (member-equal nil (V-Frms trlst)))
;;      ---the trlst is created by xy routing---
;;      (trlst-created-by-xy-routing trlst nodeset)
;;      ---trlst is a valid travel list---
;;      (trlstp trlst nodeset)
;;      ---the nodeset is created by parameter p1---
;;      (p1-created-ntkstate p1 ntkstate))
;;      ---the network and trlst relate to each other---
;;      (n==t ntkstate trlst)
;;      ---the situation is deadlockfree as defined below
;;      (deadlockfree 0 trlst ntkstate)


;;----------------------------------------
;; DEADLOCK FREEDOM FOR CIRCUIT SWITCHING
;; 1.) Definitions
;;----------------------------------------

;; 1.) Macro's used for convenience
(defmacro propertyP (trlst nodeset ntkstate p1)
  `(and (not (member-equal nil ,nodeset))
        (buffersize ,ntkstate 3)
        (not (member-equal nil (V-Frms ,trlst)))
        (trlst-created-by-xy-routing ,trlst ,nodeset)
        (trlstp trlst nodeset)
        (p1-created-ntkstate ,p1 ,ntkstate)
        (n==t ,ntkstate ,trlst)
        (deadlockfree 0 ,trlst ,ntkstate)))
;; checks if the node is full in the current ntkstate
(defmacro full-node (node ntkstate)
  (list 'not (list 'has-empty-buffer (list 'inst-readbuffers node ntkstate))))
;; return t iff n is in the range of the length of the list l
(defmacro in-range (n l)
  (list 'and (list 'natp n) (list '>= n 0) (list '< n (list 'len l))))
;; hop1 denotes the first element of the first route
;; of the first travel of trlst
(defmacro hop1 (trlst)
  (list 'caar (list 'RoutesV (list 'car trlst))))#|ACL2s-ToDo-Line|#



;; 1.) Definition of ntkstate-trlst relation
;; we assume that the ntkstate and the trlst relate to each
;; other in the following way: if an entry is full, then
;; there exists a travel currently in that entry. This
;; is expressed by (ntkstate-trlst-relate ntkstate trlst)

;; returns t iff there exists a travel v
;; in trlst with (FrmV v) = frm and
;; which is currently in entry
(defun frm-in-trlst (trlst frm node)
  (if (endp trlst)
    nil
    (if (and (equal (FrmV (car trlst)) frm)
             (equal (hop1 trlst) node))
      t
      (frm-in-trlst (cdr trlst) frm node))))
;; returns t iff each frame in the buffer is in
;; trlst
(defun buffercontents-in-trlst (buffer trlst node)
  (if (endp buffer)
    t
    (if (or (equal (car buffer) nil)
            (frm-in-trlst trlst (car buffer) node))
      (buffercontents-in-trlst (cdr buffer) trlst node)
      nil)))
;; returns t if all the contents of the entries in ntkstate
;; are in a travel in trlst
(defun ntkstate-relates-to-trlst (ntkstate trlst)
  (if (endp ntkstate)
    t
    (let* ((entry (car ntkstate))
           (buffer (get_buff entry)))
      (if (and (consp entry)
               (buffercontents-in-trlst buffer trlst (get_coor entry)))
        (ntkstate-relates-to-trlst (cdr ntkstate) trlst)
        nil))))
;; the following function expresses the previopus relation
;; in a more convenient way: an ntkstate and trlst relate to
;; each other if updating the ntkstate with trlst
;; doesn't change the ntkstate
(defun n==t (ntkstate trlst)
  (equal (update-ntkstate ntkstate trlst) ntkstate))


;; 1.) Definition of trlst-created-by-xy-routing relation
;; we assume that the routes of trlst have been created by
;; the currently used routing function, i.e. xy.
;; This is expressed by the following function.
(defun trlst-created-by-xy-routing (trlst nodeset)
  (equal (xy-routing-top (totmissives trlst) nodeset) trlst))


;; 1.) Definition of buffer size of nodes
;; returns t if all entries of the ntkstate have
;; size number of buffers
(defun buffersize (ntkstate size)
  (if (endp ntkstate)
    t
    (if (equal (len (get_buff (car ntkstate))) size)
      (buffersize (cdr ntkstate) size)
      nil)))


;; 1.) Defintion of p1-created-ntkstate
;; returns t iff the coordinates of the ntkstate are equal to the
;; nodeset generated by params
(defun p1-created-ntkstate (p1 ntkstate)
  (and (2DMesh-validparamsp p1)
       (equal (getcoordinates ntkstate) (2DMesh-NodesetGenerator p1))))


;; 1.) Misc. definitions used in proof
;; returns t iff ntkstate1 is less or equal full
;; than ntkstate2
(defun <=-full (ntkstate1 ntkstate2)
  (if (endp ntkstate1)
    t
    (if (has-empty-buffer (car ntkstate2))
      (and (has-empty-buffer (car ntkstate1))
           (<=-full (cdr ntkstate1) (cdr ntkstate2)))
      (<=-full (cdr ntkstate1) (cdr ntkstate2)))))
;; returns t if the list of buffers has at least
;; one full buffer
(defun E-full-buffer (buffer)
  (cond ((endp buffer) nil)
        ((car buffer) t)
        (t (E-full-buffer (cdr buffer)))))
;; creates a list of all travels currently in a node
;; of the route
(defun get-travels-route (route trlst)
  (if (endp route)
    nil
    (let ((recur (get-travels-route (cdr route) trlst)))
      (append (get-travels (car route) trlst)
              recur))))
;; returns the number of elements in lst2
;; that are not in lst1
(defun diff-size (lst1 lst2)
  (if (endp lst2)
    0
    (let ((recur (diff-size lst1 (cdr lst2))))
      (if (member-equal (car lst2) lst1)
        recur
        (nfix (1+ recur))))))

;; 1.) Definition of deadlockfree
;; theorems needed to prove termination of
;; the following function
(defthm subsetp-get-travels
  (subsetp (get-travels org trlst) trlst))
(defthm subsetp-get-travels-route
  (subsetp (get-travels-route route trlst) trlst))
(mutual-recursion
 ;; deadlockfree_v returns nil if the given travel
 ;; is or will be in deadlockstate and t otherwise.
 ;;
 ;; Parameters:
 ;; v: the travel that is currently checked
 ;; v-acc: an accumulator of travels already examined
 ;; trlst: the complete initial trlst
 ;; ntkstate: the network state
 ;;
 ;; A given travel v is deadlockfree if either
 ;; 1.) each node of the route has empty buffers
 ;; 2.) the travels that fill the nodes of the route are deadlockfree.
 ;; If while checking the second condition v must again be checked, a cycle is encountered
 ;; and thus v is in deadlockstate. Therefor the travels are accumulated in v-acc.
 ;;
 ;; From a computational point of view, this function can be much more effective.
 ;; First, instead of checking al travels in a route with A-deadlockfree_v, it
 ;; suffices to check if for all nodes in route there exists a travel that is deadlockfree.
 ;; However, for such function E-deadlockfree_v, we can't prove the needed theorem
 ;; subsetp-preverves-E-deadlockfree_v, because the witness can be outside the subset.
 ;; Secondly, it is sufficient to check only full nodes, since a non-full node can't
 ;; cause deadlock. This would increase complexity of the proof.
 ;; Thirdly, the function could check, before it enters recursion, whether the rest of
 ;; the route is free, and not go into recursion if so. Again this would increase
 ;; complexity of the proof.
 ;;
 ;; The measure is a list of four elements, lexicographically compared:
 ;; it is possible (but shouldn't occur) that v is not in the trlst. However this can occur
 ;; only with the first call, since get-travels returns travels from trlst (see the previous
 ;; theorem). The first element is 1 if v is not in trlst, and if so, decreases to 0 after the
 ;; first call. The same holds for travels of A-deadlockfree_v. Thus for correct input the
 ;; first element is always 0.
 ;; The second element decreases on each call of A-deadlockfree_v in deadlockfree_v and remains
 ;; equal on each call of deadlockfree_v in A-deadlockfree_v.
 ;; The third element decreases on each call of deadlockfree_v in A-deadlockfree_v.
 ;; The fourth element is the `self' decreasing measure: for deadlockfree_v this is constant
 ;; since it's non-recursive. For A-deadlockfree_v this is the length of travels, since this
 ;; decreases on each self-call.
 (defun deadlockfree_v (v v-acc trlst ntkstate)
   (declare (xargs :measure (list (if (member-equal v trlst) 0 1) (diff-size v-acc trlst) 0 0)
                   :well-founded-relation l<))
   (let* ((route (car (RoutesV v)))
          (travels (get-travels-route (cdr route) trlst)))
     (cond ((member-equal v v-acc)
            ;; we get into a circle, the route isn't deadlockfree
            nil)
           ((has-empty-buffers (cdr route) ntkstate)
            ;; the travel is possible, thus it is deadlockfree
            t)
           (t
            (A-deadlockfree_v travels (cons v v-acc) trlst ntkstate)))))
 ;; returns t iff all travels in travels
 ;; are deadlockfree
 (defun A-deadlockfree_v (travels v-acc trlst ntkstate)
   (declare (xargs :measure (list (if (subsetp travels trlst) 0 1) (diff-size v-acc trlst) 1 (len travels))))
   (if (endp travels)
     t
     (and (deadlockfree_v (car travels) v-acc trlst ntkstate)
          (A-deadlockfree_v (cdr travels) v-acc trlst ntkstate)))))

;; deadlockfree returns t iff we can prove
;; deadlockfree_v for the last (len trlst) - n
;; travels in trlst. In case n = 0, it thus returns
;; t iff all travels are deadlockfree.
;;
;; We can't simply perform recursion on the trlst,
;; since we need to supply deadlockfree_v with the
;; complete trlst in each call.
(defun deadlockfree (n trlst ntkstate)
  (declare (xargs :measure (nfix (- (len trlst) n))))
  (cond ((not (natp n))
         nil)
        ((not (in-range n trlst))
         t)
        (t
         (and (deadlockfree_v (nth n trlst) nil trlst ntkstate)
              (deadlockfree (1+ n) trlst ntkstate)))))

;; some constants to test the function
;; creates a 3 by 3 mesh, filled as follows:
;;       x   x   f
;;       x   x   x
;;       f   x   x
;; where x is a node with an empty buffer and
;; f a node with a full buffer.
;; For circuit and xy, this is deadlocked.
(defconst *dimension* '(3 3))
(defconst *TransactionList* '((0 (0 0) "msg1" (2 0) 1 0)
                              (1 (0 0) "msg2" (2 0) 1 0)
                              (2 (0 0) "msg3" (2 0) 1 0)
                              (3 (2 0) "msg4" (0 0) 1 0)
                              (4 (2 0) "msg5" (0 0) 1 0)
                              (5 (2 0) "msg6" (0 0) 1 0)))
(defconst *Nodeset* (2DMesh-Nodesetgenerator *dimension*))
(defconst *trlst* (xy-routing-top (computetmissives *Transactionlist*) *nodeset*))
(defconst *ntkstate* (inst-generate-initial-ntkstate *Transactionlist* (inst-StateGenerator *dimension* nil)))
;(deadlockfree 0 *trlst* *ntkstate*)

;; induction scheme that can be used to induct on deadlockfree_v
(defun deadlockfree_v-inductionscheme (flg v v-acc trlst ntkstate travels)
  (declare (xargs :measure (list (if flg
                                   (if (member-equal v trlst) 0 1)
                                   (if (subsetp travels trlst) 0 1))
                                 (diff-size v-acc trlst)
                                 (if flg 0 1)
                                 (if flg 0 (len travels)))
                  :well-founded-relation l<))
  (if flg
    (let* ((route (car (RoutesV v)))
           (travels1 (get-travels-route (cdr route) trlst)))
      (cond ((member-equal v v-acc) nil)
            ((has-empty-buffers (cdr route) ntkstate) nil)
            (t
             (deadlockfree_v-inductionscheme nil v (cons v v-acc) trlst ntkstate travels1))))
    (cond ((endp travels) nil)
          ((deadlockfree_v (car travels) v-acc trlst ntkstate)
           (list (deadlockfree_v-inductionscheme t (car travels) v-acc trlst ntkstate travels)
                 (deadlockfree_v-inductionscheme nil v v-acc trlst ntkstate (cdr travels))))
          (t
           nil))))


;;----------------------------------------------------------
;; THEOREM 2: deadlockfree implies that a route is possible
;;----------------------------------------------------------

;; update the ntkstate results in a ntkstate-trlst relation
(defthm buffercontents-cdr
  (implies (buffercontents-in-trlst buffer (cdr trlst) node)
           (buffercontents-in-trlst buffer trlst node)))
(defthm ntkstate-relates-updated-ntkstate
  (implies (n==t ntkstate trlst)
           (ntkstate-relates-to-trlst ntkstate trlst)))

;; a route without full nodes implies that a route is possible
(defthm has-empty-buffers-implies-route-possible
  (implies (and (trlstp trlst nodeset)
                (has-empty-buffers (cdar (RoutesV v)) ntkstate)
                (member-equal v trlst))
           (not (no-good-routes trlst ntkstate))))
(defthm buffer-implies-travels
  (implies (and (buffercontents-in-trlst buffer trlst node)
                (E-full-buffer buffer))
           (consp (get-travels node trlst))))
(defthm full-node-implies-travels
  (implies (and (full-node node ntkstate)
                (buffersize ntkstate 3)
                (ntkstate-relates-to-trlst ntkstate trlst)
                (member-equal node (getcoordinates ntkstate)))
           (consp (get-travels node trlst)))
  :hints (("Subgoal *1/2"
           :use (:instance buffer-implies-travels (node (get_coor (car ntkstate)))
                 (buffer (get_buff (car ntkstate)))))))
(defthm non-empty-route-implies-travels-in-route
  (implies (and (ntkstate-relates-to-trlst ntkstate trlst)
                (buffersize ntkstate 3)
                (subsetp route (getcoordinates ntkstate))
                (not (has-empty-buffers route ntkstate)))
           (consp (get-travels-route route trlst)))
  :hints (("Goal" :in-theory (disable has-empty-buffer))))
;; thanks to this theorem, trlstp can be disabled in
;; the following proof
(defthm trlstp-implies-subsetp-route
  (implies (and (trlstp trlst nodeset)
                (member-equal v trlst))
           (subsetp (cdar (RoutesV v)) nodeset)))
;; use induction scheme to prove deadlockfree_v returns a route that is free
(defthm deadlockfree_v-implies-route-possible-flg
  (if flg
    (let ((v1 (deadlockfree_v v v-acc trlst ntkstate)))
      (implies (and v1
                    (buffersize ntkstate 3)
                (ntkstate-relates-to-trlst ntkstate trlst)
                    (member-equal v trlst)
                    (trlstp trlst (getcoordinates ntkstate)))
               (not (no-good-routes trlst ntkstate))))
    (let ((v1 (A-deadlockfree_v travels v-acc trlst ntkstate)))
      (implies (and v1
                    (buffersize ntkstate 3)
                    (ntkstate-relates-to-trlst ntkstate trlst)
                    (subsetp travels trlst)
                    (trlstp trlst (getcoordinates ntkstate))
                    (consp travels))
               (not (no-good-routes trlst ntkstate)))))
    :rule-classes nil
  :hints (("Goal" :induct (deadlockfree_v-inductionscheme flg v v-acc trlst ntkstate travels)
                  :in-theory (disable trlstp routesv))))
(defthm deadlockfree_v-implies-route-possible
  (let ((v1 (deadlockfree_v v v-acc trlst ntkstate)))
    (implies (and v1
                  (buffersize ntkstate 3)
                  (ntkstate-relates-to-trlst ntkstate trlst)
                  (trlstp trlst (getcoordinates ntkstate))
                  (member-equal v trlst))
             (not (no-good-routes trlst ntkstate))))
  :hints (("Goal" :use (:instance deadlockfree_v-implies-route-possible-flg (flg t)))))
;; first proof by induction that if the nth cdr
;; from trlst is deadlockfree then there is a possible route
(defthm nth-cdr-deadlockfree-implies-route-possible
  (implies (and (consp trlst)
                (buffersize ntkstate 3)
                (ntkstate-relates-to-trlst ntkstate trlst)
                (trlstp trlst (getcoordinates ntkstate))
                (deadlockfree n trlst ntkstate)
                (in-range n trlst))
           (not (no-good-routes trlst ntkstate)))
  :hints (("Subgoal *1/4" :use ((:instance deadlockfree_v-implies-route-possible
                                 (v (nth n trlst)) (v-acc nil))))))

;; Theorem 2 is an instantiation of the previous theorem with n = 0
;; All assumptions are part of property P
(defthm deadlockfree-implies-route-possible
  (implies (and (consp trlst)
                (buffersize ntkstate 3)
                (n==t ntkstate trlst)
                (trlstp trlst (getcoordinates ntkstate))
                (deadlockfree 0 trlst ntkstate))
           (not (no-good-routes trlst ntkstate)))
  :hints (("Goal" :use (:instance nth-cdr-deadlockfree-implies-route-possible (n 0)))))


;;---------------------------------------------
;; THEOREM 3: Property P is preserved by GeNoC
;;---------------------------------------------
;; Proof: that (getcoordinates ntkstate) equals (getcoordinates newntkstate)
(defthm update-preserves-coor
  (equal (getcoordinates (update-ntkstate ntkstate trlst))
         (getcoordinates ntkstate)))
(defthm scheduling-preserves-coor
  (let* ((out (inst-scheduling trlst nodeset ntkstate order))
         (newntkstate (mv-nth 3 out)))
     (equal (getcoordinates newntkstate)
            (getcoordinates ntkstate))))

;; Proof: (buffersize ntkstate n) is preserved
(defthm update-preserves-buffersize
  (implies (buffersize ntkstate *num-of-buffers*)
           (buffersize (update-ntkstate ntkstate trlst) *num-of-buffers*)))
(defthm scheduling-preserves-buffersize
  (let* ((out (inst-scheduling trlst nodeset ntkstate order))
         (newntkstate (mv-nth 3 out)))
    (implies (buffersize ntkstate *num-of-buffers*)
             (buffersize newntkstate *num-of-buffers*))))

;; Proof: (not (member-equal nil (v-frms trlst))) is preserved
(defthm scheduler-preserves-v-frms
  (let ((newtrlst (ct-scheduler-nt-car trlst prev ntkstate)))
    (implies (not (member-equal frm (V-Frms trlst)))
             (not (member-equal frm (V-Frms newtrlst))))))
(defthm routing-preserves-v-frms
  (let ((newtrlst (xy-routing-top (totmissives trlst) nodeset)))
    (implies (not (member-equal frm (V-Frms trlst)))
             (not (member-equal frm (V-Frms newtrlst))))))
(defthm mv-nth-equals-car
  (implies (true-listp lst)
           (equal (mv-nth 0 lst)
                  (car lst))))
(defthm scheduling-preserves-v-frms
  (let* ((out (inst-scheduling trlst nodeset ntkstate order))
         (newtrlst (xy-routing-top (car out) nodeset)))
    (implies (not (member-equal frm (V-Frms trlst)))
             (not (member-equal frm (V-Frms newtrlst))))))


;; Proof: the routing remains the same for the delayed travels
;; Assume trlst is created by xy. If a.) newtrlst is a subset of trlst,
;; and b.) taking a subset preserves created-by-xy,
;; then newtrlst is created by xy as well.

;; A.)
(defthm scheduled-is-subsetp
  (let ((newtrlst (ct-scheduler-nt-car trlst prev ntkstate)))
    (subsetp newtrlst trlst)))

;; B.)
(defthm remove-twice-xyrouting
           (equal (xyrouting (car (xyrouting current to))
                             (car (last (xyrouting current to))))
                  (xyrouting current to)))
(defthm remove-twice-xy-routing-top
           (equal (xy-routing-top (totmissives (xy-routing-top missives nodeset)) nodeset)
                  (xy-routing-top missives nodeset)))
(defthm travel-from-xy-routing-list
  (implies (and (member-equal (car newtrlst) trlst)
                (trlst-created-by-xy-routing trlst nodeset))
           (equal (cons (list (caar newtrlst) (nth 1 (car newtrlst)) (nth 2 (car newtrlst))
                              (list (xyrouting (caar (nth 3 (car newtrlst)))
                                               (car (last (car (nth 3 (car newtrlst)))))))
                              (nth 4 (car newtrlst)) (nth 5 (car newtrlst)))
                        (cdr newtrlst))
            newtrlst)))
(defthm subsetp-preserves-created-by-xy
  (implies (and (subsetp newtrlst trlst)
                (true-listp newtrlst)
                (trlst-created-by-xy-routing trlst nodeset))
           (trlst-created-by-xy-routing newtrlst nodeset))
  :hints (("Subgoal *1/1" :use (:instance travel-from-xy-routing-list))))
;; Combing A.) and B.)
(defthm scheduler-preserves-created-by-xy
  (let ((newtrlst (ct-scheduler-nt-car trlst nil ntkstate)))
    (implies (trlst-created-by-xy-routing trlst nodeset)
             (trlst-created-by-xy-routing newtrlst nodeset)))
  :hints (("Goal" :use (:instance subsetp-preserves-created-by-xy (newtrlst (ct-scheduler-nt-car trlst nil ntkstate))))))
(defthm created-by-xy-xy
  (trlst-created-by-xy-routing (xy-routing-top trlst nodeset) nodeset))


;; Proof: (trlstp trlst nodeset) is preserved
;; this is done using proof obligations
(defthm scheduling-preserves-trlstp
    (let* ((nodeset (getcoordinates ntkstate))
           (out (inst-scheduling trlst nodeset ntkstate order))
           (newtrlst (car out)))
    (implies (and (p1-created-ntkstate params ntkstate)
                  (trlstp trlst nodeset))
             (trlstp (xy-routing-top newtrlst nodeset) nodeset)))
    :hints (("Goal" :in-theory (e/d (p1-created-ntkstate)
                                    (totmissives trlstp 2DMesh-Nodesetgenerator xy-routing-top
                                     2dmesh-validparamsp totmissives)))))


;; Proof: (p1-created-ntkstate p1 ntkstate) is preserved
(defthm scheduling-preserves-nodeset-parameter
      (let* ((nodeset (getcoordinates ntkstate))
             (out (inst-scheduling trlst nodeset ntkstate order))
             (newntkstate (mv-nth 3 out)))
        (implies (p1-created-ntkstate p1 ntkstate)
                 (p1-created-ntkstate p1 newntkstate)))
      :hints (("Goal" :in-theory (enable p1-created-ntkstate))))


;; Proof: (n==t ntkstate trlst) is preserved
(defthm remove-twice-update-ntkstate
  (implies (and (trlstp trlst2 nodeset)
                (not (member-equal nil nodeset)))
           (equal (update-ntkstate (update-ntkstate ntkstate trlst1) trlst2)
                  (update-ntkstate ntkstate trlst2))))
(defthm genoc-preserves-n==t
  (let* ((out (inst-scheduling trlst nodeset ntkstate order))
         (newntkstate (mv-nth 3 out))
         (newtrlst (xy-routing-top (car out) nodeset)))
    (implies (and (trlstp trlst nodeset)
                  (not (member-equal nil nodeset))
                  (trlst-created-by-xy-routing trlst nodeset)
                  (n==t ntkstate trlst))
             (n==t newntkstate newtrlst)))
  :hints (("Goal" :in-theory (disable trlstp))
          ("Subgoal 1" :use ((:instance remove-twice-update-ntkstate
                              (trlst1 (ct-scheduler-nt-car TrLst nil ntkstate))
                              (trlst2 (ct-scheduler-nt-car TrLst nil ntkstate)))
                              (:instance scheduler-preserves-created-by-xy)))))


;; Proof: (deadlockfree 0 ntrlst ntkstate) is preserved
;; We proof this theorem by first proving A.) it holds for an
;; abstraction of the ntkstate and trlst and then B.) that the
;; abstract properties hold for the output of the scheduler.
;; We abstract on the new ntkstate by using only
;; the property that it is 'less or equal full' than
;; the old one:
;; if an entry has an empty buffer then that is preserved.
;; We abstract on the new trlst by using only
;; the property that it is a subset of the old one.
;; This last abstraction holds for the global version
;; of circuit scheduling only.

;; A.) the abstraction preserves deadlockfreedom
(defthm <=-full-preserves-has-empty-buffers
  (implies (and (<=-full newntkstate ntkstate)
                (equal (getcoordinates ntkstate) (getcoordinates newntkstate))
                (has-empty-buffers route ntkstate))
           (has-empty-buffers route newntkstate)))
;; the following theorem can only be proven if we now
;; for all travels that they are deadlockfree, instead
;; of that we merely know there exists a deadlockfree
;; travel
(defthm subsetp-preverves-A-deadlockfree_v
  (implies (and (subsetp newtravels travels)
                (A-deadlockfree_v travels v-acc trlst ntkstate))
           (A-deadlockfree_v newtravels v-acc trlst ntkstate)))
(defthm member-equal-get-travels
  (implies (member-equal v trlst)
           (member-equal v (get-travels (caar (RoutesV v)) trlst))))
(defthm subsetp-trlst-get-travels
  (implies (subsetp newtrlst trlst)
           (subsetp (get-travels node newtrlst) (get-travels node trlst)))
  :hints (("Subgoal *1/3" :in-theory (disable routesv))))
(defthm subsetp-append-subsets
  (implies (and (subsetp lst1 lst2)
                (subsetp lst3 lst4))
           (subsetp (append lst1 lst3) (append lst2 lst4))))
(defthm subsetp-trlst-get-travels-route
  (implies (and (subsetp newtrlst trlst))
           (subsetp (get-travels-route route newtrlst) (get-travels-route route trlst))))
;; use induction scheme to prove that deadlockfree_v is
;; preserved by the abstraction
(defthm abstraction-preserves-deadlockfree_v-flg
  (implies (and (subsetp newtrlst trlst)
                (equal (getcoordinates ntkstate) (getcoordinates newntkstate))
                (<=-full newntkstate ntkstate))
           (if flg
             (implies (deadlockfree_v v v-acc trlst ntkstate)
                      (deadlockfree_v v v-acc newtrlst newntkstate))
             (implies (A-deadlockfree_v travels v-acc trlst ntkstate)
                      (A-deadlockfree_v travels v-acc newtrlst newntkstate))))
  :rule-classes nil
  :hints (("Goal" :induct (deadlockfree_v-inductionscheme flg v v-acc trlst ntkstate travels))
          ("Subgoal *1/3" :use ((:instance subsetp-preverves-A-deadlockfree_v
                                 (newtravels (get-travels-route (cdar (nth 3 v)) newtrlst))
                                 (travels (get-travels-route (cdar (nth 3 v)) trlst))
                                 (v-acc (cons v v-acc))
                                 (trlst newtrlst)
                                 (ntkstate newntkstate))))))
(defthm abstraction-preserves-deadlockfree_v
  (implies (and (subsetp newtrlst trlst)
                (equal (getcoordinates ntkstate) (getcoordinates newntkstate))
                (<=-full newntkstate ntkstate)
                (deadlockfree_v v v-acc trlst ntkstate))
           (deadlockfree_v v v-acc newtrlst newntkstate))
  :hints (("Goal" :use (:instance abstraction-preserves-deadlockfree_v-flg (flg t)))))

;; prove relation between deadlockfree_v and deadlockfree:
;; (deadlockfree 0 trlst ntkstate)
;; implies that for all travels deadlockfree_v
;; holds with the default parameters.
;; First prove it by induction on n, then
;; instantiate n with 0.
(defthm not-in-cdr-implies-equal-to-car
  (implies (and (natp n)
                (member-equal x (nthcdr n lst))
                (not (member-equal x (nthcdr (1+ n) lst))))
           (equal (nth n lst) x)))
(defthm member-equal-nth-element
  (implies (and (in-range n lst1)
                (subsetp lst1 lst2))
           (member-equal (nth n lst1) lst2)))
(defthm nth-cdr-deadlockfree-vs-deadlockfree_v
  (implies (and (deadlockfree n trlst ntkstate)
                (member-equal v (nthcdr n trlst)))
           (deadlockfree_v v nil trlst ntkstate)))
(defthm deadlockfree-vs-deadlockfree_v
  (implies (and (deadlockfree 0 trlst ntkstate)
                (member-equal v trlst))
           (deadlockfree_v v nil trlst ntkstate))
  :hints (("Goal" :use (:instance nth-cdr-deadlockfree-vs-deadlockfree_v (n 0)))))
;; the abstract version of the theorem:
;; the abstraction preserves deadlockfree
;; up to the nth cdr of the new trlst
(defthm abstraction-preserves-deadlockfree-nth-cdr
  (implies (and (subsetp newtrlst trlst)
                (equal (getcoordinates ntkstate) (getcoordinates newntkstate))
                (<=-full newntkstate ntkstate)
                (deadlockfree 0 trlst ntkstate)
                (in-range n newtrlst))
           (deadlockfree n newtrlst newntkstate)))


;; B.) the scheduler output is a concrete version
;;     of the abstraction
;; We already know that newtrlst is a subset of trlst.
;; Since newntkstate is obtained by updating ntkstate with
;; newtrlst, it suffices to proof that a ntkstate-update
;; with a smaller trlst results in a ntkstate that is lesser
;; or equal full. This holds only if the original ntkstate
;; relates to the original trlst, i.e. (n==t ntkstate trlst).
;; We use the book "sets" here.
(defthm frms-member-equal-nil-create-buffer
  (implies (and (natp n)
                (< (len travels) n))
           (member-equal nil (create-buffer n travels))))
(defthm create-buffer-frms<n
  (implies (and (not (member-equal nil (v-frms travels)))
                (member-equal nil (create-buffer n travels))
                (natp n))
           (< (len travels) n)))
(defthm len-remove-dups
  (implies (<= (len x) (len (remove-duplicates-equal y)))
           (<= (len x) (len y))))
(defthm subsetp-remove-dups
  (implies (subsetp x y)
           (subsetp x (remove-duplicates-equal y))))
(defthm <-and-<=-imply-<
  (implies (and (< x y)
                (<= z x))
           (< z y)))
(defthm member-equal-nil-create-buffer
  (implies (and (subsetp travels1 travels2)
                (<= (len travels1) (len travels2))
                (no-duplicatesp travels1)
                (natp n)
                (not (member-equal nil (v-frms travels2)))
                (member-equal nil (create-buffer n travels2)))
           (member-equal nil (create-buffer n travels1)))
  :hints (("Goal" :use  (:instance <-and-<=-imply-< (x (len travels2)) (y n) (z (len travels1))))))
(defthm get-travels-preserves-frms
  (implies (not (member-equal frm (V-Frms trlst)))
           (not (member-equal frm (V-Frms (get-travels node trlst))))))
(defthm get-travels-preserves-not-member
  (implies (not (member-equal v trlst))
           (not (member-equal v (get-travels node trlst)))))
(defthm get-travels-preserves-no-duplicatesp
  (implies (no-duplicatesp-equal trlst)
           (no-duplicatesp-equal (get-travels node trlst))))
(defthm subsetp-newtrlst-implies-<=-full
  (implies (and (not (member-equal nil (V-Frms trlst)))
                (subsetp newtrlst trlst)
                (no-duplicatesp newtrlst))
          (<=-full (update-ntkstate ntkstate newtrlst)
                   (update-ntkstate ntkstate trlst)))
  :hints (("Subgoal *1/2" :use (:instance member-equal-nil-create-buffer
                                (travels1 (get-travels (cadaar ntkstate) newtrlst))
                                (travels2 (get-travels (cadaar ntkstate) trlst))
                                (n *num-of-buffers*)))))
(defthm no-duplicatesp-trlst
  (implies (no-duplicatesp-equal (v-ids trlst))
           (no-duplicatesp-equal trlst))
  :hints (("Subgoal *1/2" :use (:instance member-equal-idv-v-ids
                                (v (car trlst)) (trlst (cdr trlst))))))
(defthm scheduled-is-<=-full
  (let* ((out (inst-scheduling trlst nodeset ntkstate order))
         (newntkstate (mv-nth 3 out)))
    (implies (and (trlstp trlst nodeset)
                  (not (member-equal nil nodeset))
                  (not (member-equal nil (V-Frms trlst)))
                  (n==t ntkstate trlst))
             (<=-full newntkstate ntkstate)))
  :hints (("Subgoal 1" :use ((:instance subsetp-newtrlst-implies-<=-full
                              (newtrlst (ct-scheduler-nt-car TrLst nil ntkstate)))))))


;; A.) + B.)
;; Then prove an instantiation of the abstract theorem with n = 0
;; and with newntkstate and newtrlst as provided by the scheduler
(defthm scheduler-preserves-deadlockfreedom
  (let* ((out (inst-scheduling trlst nodeset ntkstate order))
         (newntkstate (mv-nth 3 out))
         (newtrlst (ct-scheduler-nt-car trlst prev ntkstate)))
    (implies (and (trlstp trlst nodeset)
                  (not (member-equal nil nodeset))
                  (not (member-equal nil (V-Frms trlst)))
                  (n==t ntkstate trlst)
                  (deadlockfree 0 trlst ntkstate))
             (deadlockfree 0 newtrlst newntkstate)))
  :hints (("Goal" :use ((:instance abstraction-preserves-deadlockfree-nth-cdr
                         (newntkstate (mv-nth 3 (ct-scheduling trlst nodeset ntkstate order)))
                         (newtrlst (ct-scheduler-nt-car trlst prev ntkstate))
                         (n 0)))
                  :in-theory (disable ct-scheduling n==t trlstp))))

;; Now that is has been proven that scheduler preserves dlf,
;; prove that new routing on the delayed travels preserves dlf.
(defthm genoc-preserves-deadlockfreedom
  (let* ((nodeset (getcoordinates ntkstate))
         (out (inst-scheduling trlst nodeset ntkstate order))
         (newntkstate (mv-nth 3 out))
         (newtrlst (xy-routing-top (car out) nodeset)))
    (implies (and (trlstp trlst nodeset)
                  (not (member-equal nil nodeset))
                  (not (member-equal nil (V-Frms trlst)))
                  (n==t ntkstate trlst)
                  (trlst-created-by-xy-routing trlst nodeset)
                  (deadlockfree 0 trlst ntkstate))
             (deadlockfree 0 newtrlst newntkstate)))
  :otf-flg t
  :hints (("Goal" :in-theory (disable xy-routing-top ct-scheduling-assumptions ct-legal-measure
                                      ct-test_routes trlstp scheduler-preserves-deadlockfreedom
                                      scheduler-preserves-created-by-xy))
          ("Subgoal 2" :in-theory (e/d (trlst-created-by-xy-routing)
                                       (scheduler-preserves-deadlockfreedom scheduler-preserves-created-by-xy))
                       :use ((:instance scheduler-preserves-deadlockfreedom
                              (prev nil) (nodeset (getcoordinates ntkstate)))
                              (:instance scheduler-preserves-created-by-xy
                               (nodeset (getcoordinates ntkstate)))))))



;;-------------------------------------------------
;; THEOREM 4: Property P implies en route is empty
;;-------------------------------------------------

;; proof output of scheduler is legal measure
(defthm measure-is-routelengths
  (equal (sum-of-lst (RouteLengths-TrLst (ct-scheduler-nt-car trlst prev ntkstate)))
         (sum-of-lst (ct-scheduler-nt-mv2 TrLst prev ntkstate))))
(defthm scheduling-provides-legal-measure
  (let* ((out (inst-scheduling trlst nodeset ntkstate order))
         (newntkstate (mv-nth 3 out))
         (newmeasure (mv-nth 2 out))
         (newtrlst (xy-routing-top (car out) nodeset)))
    (implies (and (inst-scheduling-assumptions trlst nodeset ntkstate order)
                  (trlst-created-by-xy-routing trlst nodeset))
             (ct-legal-measure newmeasure newtrlst nodeset newntkstate order)))
  :hints (("Goal" :in-theory (e/d (trlst-created-by-xy-routing)
                                  (scheduler-preserves-created-by-xy))
                  :use (:instance scheduler-preserves-created-by-xy))))

;; we need the following theorem because otherwise
;; we would have to enable trlstp in theorem 4
(defthm routing-append-nil
  (equal (xy-routing-top (append trlst nil) nodeset)
         (xy-routing-top trlst nodeset)))
(defthm consp-routing
  (implies (consp missives)
           (consp (xy-routing-top missives nodeset))))

;; Theorem 4:
;; If the measure initially supplied to GeNoC_t is legal,
;; Property P implies that GeNoC terminates with no
;; en route messages
(defthm en-route-empty
  (let* ((nodeset (getcoordinates ntkstate))
         (trlst (XY-routing-top missives nodeset)))
    (implies (and (propertyP trlst nodeset ntkstate p1)
                  (inst-legal-measure measure trlst nodeset ntkstate order))
             (endp (mv-nth 1 (simple-genoc_t missives nodeset measure nil nil time ntkstate order)))))
  :hints (("Goal" :in-theory (disable XY-routing-top p1-created-ntkstate deadlockfree ct-scheduling
                                      ct-legal-measure trlstp n==t))))

;;-------------------------------------------------
;; THEOREM 5: If en route is empty, all travels
;; have arrived.
;;-------------------------------------------------

(defthm trlst-equal-routing-missives
  (trlst-equal (xy-routing-top missives nodeset)
               missives))
(defthm missives-equal-enroute+arrived
  (implies (true-listp missives)
           (trlst-equal (append (simple-genoc_t-nt-mv-nth0 missives nodeset measure time ntkstate order)
                                (simple-genoc_t-nt-mv-nth1 missives nodeset measure time ntkstate order))
                        missives))
  :hints (("Goal" :in-theory (disable XY-routing-top ct-scheduling trlst-equal))
          ("Subgoal *1/4" :use (:instance input=output (trlst (xy-routing-top missives nodeset))))))

(defthm trlst-equal-append-nil
  (implies (endp y)
           (trlst-equal (append x y) x))
  :rule-classes :rewrite)


(defthm enroute-empty->arrived-full
  (implies (and (true-listp missives)
                (endp (mv-nth 1 (simple-genoc_t missives nodeset measure nil nil time ntkstate order))))
           (trlst-equal (mv-nth 0 (simple-genoc_t missives nodeset measure nil nil time ntkstate order))
                  missives))
    :hints (("Goal" :in-theory (disable XY-routing-top ct-scheduling trlst-equal)
                    :use ((:instance trlst-equal-append-nil
                           (x (simple-genoc_t-nt-mv-nth0 missives nodeset measure time ntkstate order))
                           (y (simple-genoc_t-nt-mv-nth1 missives nodeset measure time ntkstate order)))
                          (:instance missives-equal-enroute+arrived)))))

;;----------------------
;; PROVING CORRECTNESS
;;----------------------
(defthm simple-genoc-is-correct
  (let ((nodeset (2dMesh-NodesetGenerator p1)))
    (mv-let (results aborted)
            (simple-genoc trs p1 p2 order)
            (declare (ignore aborted))
            (implies (and (transactionsp trs nodeset)
                          (inst-ValidStateParamsp p1 p2))
                     (genoc-correctness results
                                        (extract-sublst trs (r-ids results))))))
  :otf-flg t
  :hints (("goal":by
                 (:functional-instance genoc-is-correct
                  (generate-initial-ntkstate simple-generate-initial-ntkstate)
                  (readyfordeparture simple-readyfordeparture)
                  (genoc simple-genoc)
                  (genoc_t simple-genoc_t)
                  (validstateparamsp simple-ValidStateParamsp)
                  (stategenerator simple-StateGenerator)
                  (readbuffers simple-readbuffers)
                  (nodesetgenerator 2DMesh-NodeSetGenerator)
                  (extract-simulation simple-extract-simulation)
                  (loadbuffers simple-loadbuffers)
                  (validparamsp 2DMesh-ValidParamsp)
                  (nodesetp 2DMesh-NodeSetp)
                  (scheduling ct-scheduling)
                  (routing XY-Routing-top)
                  (get_next_priority ct-get_next_priority)
                  (scheduling-assumptions ct-scheduling-assumptions)
                  (legal-measure ct-legal-measure)
                  (initial-measure ct-initial-measure))
                 :in-theory (disable trlstp))

; Comment from J Moore for changes after v5-0 for tau:

; This comment contains (:executable-counterpart tau-system) just so that rune
; is a reliable marker for changes made to support tau.  These have had to be
; renamed so often (with changes in tau) that I have lost track of what they
; used to be!  Just don't be surprised if this proof fails after changing tau!

; However, an earlier version of this file had these notes:
;         ("Subgoal 32" ; tau on: {"Subgoal 32"} tau off: {"Subgoal 34"}
;          :in-theory (disable ct-scheduling xy-routing-top))
;         ("Subgoal 25" ; tau on: {"Subgoal 25"} tau off: {"Subgoal 26"}
;          :in-theory (disable ct-scheduling ct-scheduling-assumptions xy-routing-top
;                              simple-extract-simulation))
;         ("Subgoal 27" ; tau on: {"Subgoal 27"} tau off: {"Subgoal 28"}
;          :use (:instance CorrectRoutesp-XYRouting (tmissives m)))
;         ("Subgoal 26" ; tau on: {"Subgoal 26"} tau off: {"Subgoal 27"}
;          :use (:instance TrLstp-XYRouting (tmissives m)))
;         ("Subgoal 13.2'" :use (:instance not-in-v-ids-ct (prev nil)))
;         ("subgoal 10" :in-theory (disable consp-last trlstp))
;         ("subgoal 10.2" :in-theory (e/d (trlstp) (consp-last)))
;         ("subgoal 10.1" :use ((:instance tm-ids-tomissives-v-ids (x trlst))
;                               (:instance tomissives-extract-sublst
;                                          (l (totmissives trlst))
;                                          (ids (tm-ids (totmissives trlst))))
;                               (:instance totmissives-extract-sublst (l trlst) (ids (v-ids trlst)))
;                               (:instance extract-sublst-identity)))
;         ("Subgoal 9" :use (:instance ct-scheduled-correctness (prev nil)))
;         ("Subgoal 9.4" :use (:instance ct-delayed-correctness (st ntkstate) (prev nil)))
;         ("Subgoal 9.3" :use (:instance subsetp-scheduled-id-ct (prev nil)))
;         ("Subgoal 8.2" :use (:instance ct-scheduled-correctness (st ntkstate) (prev nil)))))

          ("Subgoal 30"
           :in-theory (disable ct-scheduling xy-routing-top))
          ("Subgoal 23"
           :in-theory (disable ct-scheduling ct-scheduling-assumptions xy-routing-top
                               simple-extract-simulation))
          ("Subgoal 25"
           :use (:instance CorrectRoutesp-XYRouting (tmissives m)))
          ("Subgoal 24"
           :use (:instance TrLstp-XYRouting (tmissives m)))
          ("Subgoal 13.2'" :use (:instance not-in-v-ids-ct (prev nil)))
          ("Subgoal 8" :in-theory (disable consp-last trlstp))
          ("Subgoal 8.2" :in-theory (e/d (trlstp) (consp-last)))
          ("Subgoal 8.1" :use ((:instance tm-ids-tomissives-v-ids (x trlst))
                                (:instance tomissives-extract-sublst
                                           (l (totmissives trlst))
                                           (ids (tm-ids (totmissives trlst))))
                                (:instance totmissives-extract-sublst (l trlst) (ids (v-ids trlst)))
                                (:instance extract-sublst-identity)))
          ))



