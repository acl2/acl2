(in-package "ACL2")

;; The book contains tools to analyze the control flow of JVM bytecode programs
;; (e.g., find basic blocks, find loops).

;fixme what about exceptions and the athrow instruction?
;fix this up to use the fact that programs now contain pc/instr pairs

(include-book "classes")
(include-book "kestrel/alists-light/clear-key" :dir :system)
(include-book "kestrel/alists-light/lookup" :dir :system)
;; (include-book "coi/alists/clearkey" :dir :system) ;todo: brings in a lot
;; (in-theory (disable LIST::MEMBER-EQ-IS-MEMBERP-PROPOSITIONALLY
;;                     LIST::MEMBER-IS-MEMBERP-PROPOSITIONALLY
;;                     LIST::MEMBER-EQUAL-IS-MEMBERP-PROPOSITIONALLY))
(include-book "kestrel/maps/maps" :dir :system)
(local (include-book "kestrel/lists-light/memberp" :dir :system))

;set several keys to the same value
(defun s-all (keys val map)
  (if (endp keys)
      map
    (s-all (cdr keys)
           val
           (s (car keys) val map))))

;drop?
(defthm s-all-of-s-diff
  (equal (s-all keys val (s key val map))
         (if (memberp key keys)
             (s-all keys val map)
           (s key val (s-all keys val map))))
  :hints (("subGoal *1/2" :cases ((equal key (car keys))))))

(defun intersection-equal (l1 l2)
  (declare (xargs :guard (and (true-listp l1)
                              (true-listp l2))))
  (cond ((endp l1) nil)
        ((member-equal (car l1) l2)
         (cons (car l1)
               (intersection-equal (cdr l1) l2)))
        (t (intersection-equal (cdr l1) l2))))


;; (defun make-pc-instr-pairs-aux (instrs current-pc)
;;   (if (endp instrs)
;;       nil
;;     (acons current-pc
;;            (car instrs)
;;            (make-pc-instr-pairs-aux (cdr instrs) (+ current-pc (jvm::inst-length (car instrs)))))))

;; (defun make-pc-instr-pairs (instrs)
;;   (make-pc-instr-pairs-aux instrs 0))

;; ;now the code is always stored as an alist..
;; (defun make-pc-instr-pairs (instrs)
;;   instrs)

;;(make-pc-instr-pairs *code*)

(defun add-to-all (val vals)
  (if (endp vals)
      nil
    (cons (+ val (first vals))
          (add-to-all val (rest vals)))))

;the leaders are the targets of the branches and the instructions after the branches/returns (even for unconditional branches/returns)
;returns nil if the instr is not a branch/return
;fixme what about exceptions? can leaders be the PCs to which control can jump upon an exception?
(defun leaders-after-branch-or-return (pc instr)
  (let ((opcode (first instr)))
    (if (eq ':goto opcode)
        (list (+ pc (second instr))        ;the target of the GOTO
              (+ pc 3 ;(jvm::inst-length instr)
                 ) ;the instruction after the GOTO
              )
      (if (member-eq opcode '(:IF_ACMPEQ
                              :IF_ACMPNE
                              :IF_ICMPEQ
                              :IF_ICMPGE
                              :IF_ICMPGT
                              :IF_ICMPLE
                              :IF_ICMPLT
                              :IF_ICMPNE
                              :IFEQ
                              :IFGE
                              :IFGT
                              :IFLE
                              :IFLT
                              :IFNE
                              :IFNONNUL
                              :IFNULL))
          (list (+ pc (second instr))        ;the target of the branch
                (+ pc 3 ;(jvm::inst-length instr)
                   ) ;the instruction after the branch
                )
        (if (member-eq opcode '(:areturn
                                :ireturn
                                :lreturn
                                :return))
            (list (+ pc 4 ;(jvm::inst-length instr)
                     )) ;the instruction after the return
          (if (eq opcode :tableswitch)
              (let ((default-offset (farg1 instr))
                    (jump-offsets (farg4 instr)) ;each is a signed-byte-p
                    )
                (cons (+ pc default-offset)
                      (add-to-all pc jump-offsets)))
          nil))))))

;these do not include the instructions after returns or unconditional branches
;fixme where do we handle returns?
(defun successors-of-instruction (pc instr next-pc)
  (let ((opcode (first instr)))
    (if (eq ':goto opcode)
        (list (+ pc (second instr)) ;the target of the GOTO
              )
      (if (member-eq opcode '(:IF_ACMPEQ
                              :IF_ACMPNE
                              :IF_ICMPEQ
                              :IF_ICMPGE
                              :IF_ICMPGT
                              :IF_ICMPLE
                              :IF_ICMPLT
                              :IF_ICMPNE
                              :IFEQ
                              :IFGE
                              :IFGT
                              :IFLE
                              :IFLT
                              :IFNE
                              :IFNONNUL
                              :IFNULL))
          (list (+ pc (second instr)) ;the target of the branch
                next-pc               ;the instruction after the branch
                )
        ;; it's a reular instruction, so the (single) succesor is just the next instruction
        (list next-pc)))))

;leaders are the starts of basic blocks
;FIXME be sure i handle all jvm instructions!
(defun find-leader-pcs-aux (pc-instr-pairs leaders)
  (if (endp pc-instr-pairs)
      leaders
    (let* ((pair (car pc-instr-pairs))
           (pc (car pair))
           (instr (cdr pair))
           (new-leaders (leaders-after-branch-or-return pc instr)) ;fixme could pass in pc-after-instr?
           )
      (find-leader-pcs-aux (cdr pc-instr-pairs)
                           (append new-leaders leaders)))))

(defun find-leader-pcs (pc-instr-pairs)
  (find-leader-pcs-aux pc-instr-pairs (list 0)))  ;PC 0 is always a leader

;;(find-leader-pcs (make-pc-instr-pairs *code*)) ;out of date?

(defun find-basic-blocks-aux (pc-instr-pairs rev-current-block past-blocks leader-pcs)
  (if (endp pc-instr-pairs)
      (cons (reverse rev-current-block) past-blocks)
    (let* ((pair (car pc-instr-pairs))
           (pc (car pair)))
      (if (member-equal pc leader-pcs) ;use member
          (find-basic-blocks-aux (cdr pc-instr-pairs)
                                 (list pc)
                                 (cons (reverse rev-current-block) past-blocks)
                                 leader-pcs)
        (find-basic-blocks-aux (cdr pc-instr-pairs)
                               (cons pc rev-current-block)
                               past-blocks
                               leader-pcs)))))

(defun find-basic-blocks (pc-instr-pairs)
  (let* ((leader-pcs (find-leader-pcs pc-instr-pairs)))
    (find-basic-blocks-aux (cdr pc-instr-pairs) ;skip PC 0
                           (list 0)
                           nil
                           leader-pcs)))

;get the next program counter location after the given PC in CODE.
 ;fixme what if it's the last block?
(defun get-pc-after-pc (pc code)
  (if (endp code)
      :none ;(hard-error 'get-pc-after-pc "can't get next pc" nil)
    (let* ((pair (car code))
           (current-pc (car pair)))
      (if (eql pc current-pc)
          (car (car (cdr code)))
        (get-pc-after-pc pc (cdr code))))))

;pairs each basic block (indicated by its first PC) with a set of successor blocks (also indicated by first PCs)
(defun pair-blocks-with-successors-aux (basic-blocks code successor-alist)
  (if (endp basic-blocks)
      successor-alist
    (let* ((basic-block (first basic-blocks))
           (first-pc (car basic-block))
           (last-pc (car (last basic-block)))
           (last-instr (lookup last-pc code))
           (pc-after-last-instr (get-pc-after-pc last-pc code))
           (successors (successors-of-instruction last-pc last-instr pc-after-last-instr)))
      (pair-blocks-with-successors-aux (rest basic-blocks)
                                       code
                                       (acons first-pc successors successor-alist)))))

(defun pair-blocks-with-successors (basic-blocks code)
  (pair-blocks-with-successors-aux basic-blocks code nil))

;; (pair-blocks-with-successors (find-basic-blocks *code*)
;;                              (make-pc-instr-pairs *code*))

(defun add-value-for-keys (keys value alist)
  (if (endp keys)
      alist
    (let* ((key (car keys))
           (old-vals (cdr (assoc-equal key alist)))
           (new-vals (add-to-set-equal value old-vals))
           (new-alist (acons key new-vals alist)))
      (add-value-for-keys (cdr keys) value new-alist))))

(defun pair-blocks-with-predecessors-aux (block-successor-list-alist predecessor-list-alist)
  (if (endp block-successor-list-alist)
      predecessor-list-alist
    (let* ((pair (car block-successor-list-alist))
           (block (car pair))
           (successors (cdr pair))
           (predecessor-list-alist (add-value-for-keys successors block predecessor-list-alist)))
      (pair-blocks-with-predecessors-aux (cdr block-successor-list-alist) predecessor-list-alist))))

(defun pair-blocks-with-predecessors (block-successor-list-alist)
  (pair-blocks-with-predecessors-aux block-successor-list-alist nil))

;; (pair-blocks-with-predecessors
;;  (pair-blocks-with-successors (find-basic-blocks *code*)
;;                               (make-pc-instr-pairs *code*)))

(defun find-common-doms (blocks dominator-map)
  (if (endp blocks)
      'error ;fixme throw a hard-error?
    (if (endp (cdr blocks))
        (g (car blocks) dominator-map)
      (intersection-equal (g (car blocks) dominator-map)
                          (find-common-doms (cdr blocks) dominator-map)))))

(defun remove-some-dominators (blocks predecessor-list-alist dominator-map)
  (if (endp blocks)
      dominator-map
    (let* ((block (first blocks))
           (preds (cdr (assoc-equal block predecessor-list-alist))))
      (if preds
          (let* ((common-doms-of-preds (find-common-doms preds dominator-map))
                 (new-doms (union-equal (list block) common-doms-of-preds))
                 (dominator-map (s block new-doms dominator-map)))
            (remove-some-dominators (rest blocks) predecessor-list-alist dominator-map))
        ; the node has no preds. fixme think about this.  currently, it will be considered dominated by everything?  (think about exceptions...)
        (remove-some-dominators (rest blocks) predecessor-list-alist dominator-map)))))

(defun dominator-map-aux (non-start-blocks predecessor-list-alist dominator-map
                                           step-limit ;to ensure termination
                                           )
  (declare (xargs :measure (nfix step-limit)))
  (if (zp step-limit)
      (er hard? 'dominator-map-aux "Step limit reached when computing dominators!")
    (let ((new-dominator-map (remove-some-dominators non-start-blocks predecessor-list-alist dominator-map)))
      (if (equal new-dominator-map dominator-map)
          dominator-map
        (dominator-map-aux non-start-blocks
                           predecessor-list-alist
                           new-dominator-map
                           (- step-limit 1))))))

;fixme should we have a separate entry block?
;; A dominator of a block B is a block which occurs on all paths from the entry to block B.
(defun dominator-map (basic-block-ids predecessor-list-alist)
  (let* ((dominator-map (s 0 (list 0) nil)) ;the first block is only dominated by itself
         (non-start-block-ids (remove-equal 0 basic-block-ids)) ;use remove-eql? or remove?
         ;;initially, say that every (non-start) block is dominated by all blocks
         (dominator-map (s-all non-start-block-ids basic-block-ids dominator-map))
         ;;remove dominator relationships of the form A dom B where B has a predecessor not dominated by A
         (dominator-map (dominator-map-aux non-start-block-ids predecessor-list-alist dominator-map
                                           (* (len basic-block-ids) (len basic-block-ids)) ;this limit can be increased if needed
                                           )))
    dominator-map))

;; (dominator-map
;;  (strip-cars (find-basic-blocks *code*))
;;  (pair-blocks-with-predecessors
;;   (pair-blocks-with-successors (find-basic-blocks *code*)
;;                                (make-pc-instr-pairs *code*))))

(defun make-edges (key vals edges)
  (if (endp vals)
      edges
    (cons (cons key (car vals))
          (make-edges key (cdr vals) edges))))

(defun split-pairs (alist)
  (if (endp alist)
      nil
    (let* ((pair (car alist))
           (key (car pair))
           (vals (cdr pair)))
      (make-edges key vals (split-pairs (cdr alist))))))

(defun find-back-edges (edges dominator-map)
  (if (endp edges)
      nil
    (let* ((edge (car edges))
           (from-block (car edge))
           (to-block (cdr edge)))
      (if (member-equal to-block (g from-block dominator-map))
          (cons edge (find-back-edges (cdr edges) dominator-map))
        (find-back-edges (cdr edges) dominator-map)))))

;; (find-back-edges
;;  (split-pairs (pair-blocks-with-successors (find-basic-blocks *code*)
;;                                            (make-pc-instr-pairs *code*)))
;;  (dominator-map
;;   (strip-cars (find-basic-blocks *code*))
;;   (pair-blocks-with-predecessors
;;    (pair-blocks-with-successors (find-basic-blocks *code*)
;;                                 (make-pc-instr-pairs *code*)))))

(defun find-natural-loop-aux (worklist loop-nodes pred-alist step-limit)
  (declare (xargs :measure (nfix step-limit)))
  (if (zp step-limit)
      (er hard? 'find-natural-loop-aux "Step limit reached when finding natural loops!")
    (if (endp worklist)
        loop-nodes
      (let* ((node (car worklist)))
        (if (member-equal node loop-nodes) ;this prevents us from processing the preds of the header
            (find-natural-loop-aux (cdr worklist) loop-nodes pred-alist (- step-limit 1))
          (find-natural-loop-aux (append (cdr (assoc-equal node pred-alist))
                                         (cdr worklist))
                                 (cons node loop-nodes)
                                 pred-alist
                                 (- step-limit 1)))))))

;this pairs the headers with their loop nodes
(defun find-natural-loop (back-edge pred-alist)
  (let* ((from-node (car back-edge))
         (to-node (cdr back-edge)) ;this is the loop header
         ;; for the step-limit
         (num-possible-preds (len (append-lst (strip-cdrs pred-alist))))
         (step-limit (* num-possible-preds num-possible-preds)) ;this limit can be increased
         )
    (cons to-node (find-natural-loop-aux (list from-node) ;node to work backward from
                                         (list to-node)
                                         pred-alist
                                         step-limit))))

(defun find-natural-loops (back-edges pred-alist)
  (if (endp back-edges)
      nil
    (cons (find-natural-loop (car back-edges) pred-alist)
          (find-natural-loops (cdr back-edges) pred-alist))))

(defun get-pcs-for-loop (basic-block-ids basic-blocks)
  (if (endp basic-block-ids)
      nil
    (append (assoc-equal (car basic-block-ids) basic-blocks)
            (get-pcs-for-loop (cdr basic-block-ids) basic-blocks))))

(defun get-pcs-for-loops (loops basic-blocks)
  (if (endp loops)
      nil
    (let* ((loop-info (car loops))
           (header (car loop-info))
           (basic-block-ids (cdr loop-info)))
      (cons (s :header header (s :pcs (get-pcs-for-loop basic-block-ids basic-blocks) nil))
            (get-pcs-for-loops (cdr loops) basic-blocks)))))


;acc is an alist from loop headers to lists of basic-block-ids
;The result is an alist, which is essentially a list of loop-headers
(defun group-loops-aux (natural-loop-infos acc)
  (if (endp natural-loop-infos)
      acc
    (let* ((natural-loop-info (first natural-loop-infos))
           (header (car natural-loop-info))
           (basic-block-ids (cdr natural-loop-info))
           (prev-val (lookup header acc))
           (new-val (union-equal prev-val basic-block-ids))
           (acc (clear-key header acc)) ;ensure no duplicate keys in the result
           (acc (acons header new-val acc)))
      (group-loops-aux (rest natural-loop-infos) acc))))

;If two "natural loops" have the same header, they should be considered the same loop
(defun group-loops (natural-loop-infos)
  (group-loops-aux natural-loop-infos nil))

(defun decompose-into-loops (code)
  (let* ((basic-blocks (find-basic-blocks code))
         (successor-list (pair-blocks-with-successors basic-blocks code)) ;fixme what about blocks with no successors?
         (edges (split-pairs successor-list))
         (basic-block-ids (strip-cars basic-blocks))
         (pred-alist (pair-blocks-with-predecessors successor-list))
         (dominator-map (dominator-map basic-block-ids pred-alist)) ;associates each block with the blocks that dominate it
         ;; (dummy (progn$ (cw "(dominator map:~%")
         ;;                (print-list dominator-map)
         ;;                (cw ")~%")))
         (back-edges (find-back-edges edges dominator-map))
;these pair the headers with the loop nodes
         (natural-loops (find-natural-loops back-edges pred-alist))
         (all-loops (group-loops natural-loops))
         (full-loops (get-pcs-for-loops all-loops basic-blocks)))
;    (declare (ignore dummy))
    full-loops))


;fixme add a check for nested loops!
