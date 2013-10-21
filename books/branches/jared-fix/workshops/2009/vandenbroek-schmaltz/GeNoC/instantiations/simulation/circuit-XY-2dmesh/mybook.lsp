(include-book "misc/file-io"  :dir :system)
(include-book "../../genoc/circuit-XY-2Dmesh/GeNoC")

(set-state-ok t)
(set-ignore-ok t)

(defun demo (Trlst size timelimit filename state )
  (declare (xargs :stobjs state  :mode :program))
  (mv-let (Responses Aborted accup)
          (INST-genoc Trlst ; Compute missives from travel list
                 size ; param
                 timeLimit; number of simulation steps
                 )
          (write-list (list (cons 'RESPONSES Responses)
                            (cons 'ABORTED Aborted)
                            accup) filename 'top-level state)))

(defconst *size* 2)
(defconst *TransactionList* '((1 (0 0) "hallo1" (1 1) 1 0)))
                              


(defconst *TimeLimit* 10)
(demo *TransactionList* *size*  *TimeLimit* "demo.txt" state)#|ACL2s-ToDo-Line|#





