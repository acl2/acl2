#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book  "../../../generic-modules/GeNoC-ntkstate")
(include-book "../../nodeset/2DMesh-no-ports/2DMesh")

;; simple-ntkstate = (entry1, entry2, ...)
;; simple-entry = (((Coor (X1 Y1)) (Buffers data)))
;; where data = (consp b_1 b_2 b_3 ... b_c) with c a constant


(defconst *num-of-buffers* 3)

(defun nil-list (n)
  (if (zp n)
    nil
    (cons nil (nil-list (1- n)))))

(defun simple-Stategeneratorlocal (nodeset)
  (if (endp nodeset)
    nil
    (append (list (list (list 'Coor  (car nodeset))
                        (list 'Buffers (nil-list *num-of-buffers*))))
            (simple-StateGeneratorlocal (cdr nodeset)))))

;;Generates the states
;;P is the parameter for the NodeSetGenerator
;;The other parameter isn't used
(defun simple-StateGenerator (P optional-param)
  (declare (ignore optional-param))
  (simple-stategeneratorlocal (2DMesh-NodeSetGenerator P)))

;; A function that verifies the the input parameters of the state
;; generation function
(defun simple-ValidStateParamsp (P optional-param)
  (declare (ignore optional-param))
  (2DMesh-ValidParamsp P))
(in-theory (disable simple-ValidStateParamsp))

;; Updates the buffer bufnum of the entry with the new content
(defun update-buffer (entry content)
  (if (endp entry)
    (list (list 'Coor nil) (list 'Buffers (nil-list *num-of-buffers*)))
    (list (car entry) (list 'Buffers content))))


;; this function takes as input a list with as first elt
;; the coordinates of a node and as second the buffer nummer.
;; It loads the buffer with the content
;; returns: updated networkstate
(defun simple-loadbuffers (node-coor content ntkstate)
  (if (endp ntkstate)
    nil
    (let* ((entry (car ntkstate))
           (curr_coor (get_coor entry)))
      (if (equal node-coor curr_coor)
        ;; we have found the right element
        (cons (update-buffer entry content) (cdr ntkstate))
        ;; else keep searching
        (cons entry
              (simple-loadbuffers node-coor content (cdr ntkstate)))))))
(defun simple-readbuffers (node-coor ntkstate)
  (if (endp ntkstate)
    nil
    (let ((entry (car ntkstate)))
      (if (equal (get_coor entry) node-coor)
        ;; we have found the right element, we return it
        entry
        ;; else we keep searching
        (simple-readbuffers node-coor (cdr ntkstate))))))
;; returns t iff the entry has a buffer equal to nil
(defun has-empty-buffer (entry)
  (member-equal nil (get_buff entry)))#|ACL2s-ToDo-Line|#


;;-----------------------
;; update ntkstate
;;-----------------------
;; creates a list of all travels currently in node
(defun get-travels (node trlst)
  (if (endp trlst)
    nil
    (let ((recur (get-travels node (cdr trlst))))
      (if (equal (caar (RoutesV (car trlst))) node)
        (cons (car trlst) recur)
        recur))))
;; creates a bufffer with length 'size'
;; puts all frms in the buffer if possible
(defun create-buffer (size travels)
  (cond ((zp size) nil)
        ((endp travels) (nil-list size))
        (t
         (cons (FrmV (car travels)) (create-buffer (1- size) (cdr travels))))))
(defun update-ntkstate (ntkstate trlst)
  (if (endp ntkstate)
    nil
    (let* ((entry (car ntkstate))
           (coor (get_coor entry)))
      (cons (update-buffer entry (create-buffer *num-of-buffers* (get-travels coor trlst)))
            (update-ntkstate (cdr ntkstate) trlst)))))




;; generate the initial ntkstate from a transaction list
;; creates a list of all travels currently in node
(defun get-transactions (node talst)
  (if (endp talst)
    nil
    (let ((recur (get-transactions node (cdr talst)))
          (currTa (car talst)))
      (if (equal (OrgT currTa) node)
        (cons currTa recur)
        recur))))
(defun create-buffer-ta (size transactions)
  (cond ((zp size) nil)
        ((endp transactions) (nil-list size))
        (t
         (cons (MsgT (car transactions)) (create-buffer-ta (1- size) (cdr transactions))))))
(defun simple-generate-initial-ntkstate (talst ntkstate)
  (if (endp ntkstate)
    nil
    (let* ((entry (car ntkstate))
           (coor (get_coor entry)))
      (cons (update-buffer entry (create-buffer-ta *num-of-buffers* (get-transactions coor talst)))
            (simple-generate-initial-ntkstate talst (cdr ntkstate))))))



;-------------------------------------
; the instantiations used in this file
;------------------------------------
(defmacro inst-readbuffers (node-id ntkstate)
         (list 'simple-readbuffers node-id ntkstate))
(defmacro inst-loadbuffers (node-id frm ntkstate)
         (list 'simple-loadbuffers node-id frm ntkstate))
(defmacro inst-generate-initial-ntkstate (talst ntkstate)
         (list 'simple-generate-initial-ntkstate talst ntkstate))
(defmacro inst-StateGenerator (P optional-param)
         (list 'simple-StateGenerator P optional-param))
(defmacro inst-ValidStateParamsp (P optional-param)
         (list 'simple-ValidStateParamsp P optional-param))

;--------------
; Theorems
;--------------
(defthm simple-gen-validstates
  (implies (simple-validstateparamsp P1 P2)
           (Validstate (simple-stategeneratorlocal NodeSet))))
(defthm Stateparamsp=Paramsp
  (implies (simple-validstateparamsp P1 P2)
           (2DMesh-Validparamsp P1))
  :hints (("Goal" :use (:instance simple-ValidStateParamsp (P P1) (optional-param P2)))
))
(defthm simple-loadbufbers-validstates
  (implies (ValidState ntkstate)
           (ValidState (SIMPLE-LOADBUFFERS node-coor content ntkstate)))
)

(defthm simple-readbuffers-valid-entryp-local
  (implies
   (validstate ntkstate)
   (ValidState-entryp (simple-readbuffers node-coor ntkstate))))
(defthm validstate-update-ntkstate
  (implies (validstate ntkstate)
           (validstate (update-ntkstate ntkstate trlst))))
(defthm validstate-simple-generate-initial-ntkstate
  (implies (validstate ntkstate)
           (validstate (simple-generate-initial-ntkstate talst ntkstate))))

(defthm nodesetp-coordinates-simple
  (implies (true-listp NodeSet)
           (equal  (getcoordinates (simple-StateGeneratorlocal NodeSet))
                   NodeSet)))

;--------------
; Compliance
;--------------
(definstance GenericNodesetbuffers simple-ntkstate-complies-generic
  :functional-substitution
  ((ValidParamsp 2DMesh-Validparamsp)
   (NodeSetGenerator 2DMesh-NodeSetGenerator)
   (loadbuffers simple-Loadbuffers)
   (readbuffers simple-Readbuffers)
   (StateGenerator simple-StateGenerator)
   (generate-initial-ntkstate simple-generate-initial-ntkstate)
   (ValidstateParamsp simple-ValidStateParamsp))
  :otf-flg t
  :hints (("Goal" :in-theory (disable ValidState-entryp simple-ValidStateParamsp ValidState))
          ("Subgoal 1" :use (:instance nodesetp-coordinates-simple))
))
