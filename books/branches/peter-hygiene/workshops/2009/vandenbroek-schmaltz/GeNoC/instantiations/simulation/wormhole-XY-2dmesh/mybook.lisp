(include-book "misc/file-io"  :dir :system)
(include-book "../../genoc/wormhole-XY-2Dmesh/GeNoC")

(set-state-ok t)
(set-ignore-ok t)

(defun demo (Trlst size timelimit filename state )
  (declare (xargs :stobjs state  :mode :program))
  (mv-let (Responses Aborted accup)
          (INST-genoc Trlst ; Compute missives from travel list
                 size ;Generate topology
                 timeLimit; 10 attempts
                 )
          (write-list (list (cons 'RESPONSES Responses)
                            (cons 'ABORTED Aborted)
                            accup) filename 'top-level state)))

(defconst *size* 2)
(defconst *TransactionList* '((1 (0 0) "header" (1 1) 2 0)
                              (1 (0 0) "data" nil 1 0)
                              (1 (0 0) "tail" nil 0 0)
                              (2 (1 0) "header" (1 1) 2 0)
                              (2 (1 0) "data" nil 1 0)
                              (2 (1 0) "data" nil 1 0)
                              (2 (1 0) "data" nil 1 0)
                              (2 (1 0) "tail" nil 0 0)
                              ))
                              


(defconst *TimeLimit* 20)

(demo *TransactionList* *size*  *TimeLimit* "demo.txt" state)#|ACL2s-ToDo-Line|#












