(in-package "ACL2")

(include-book "stepproc1")
(include-book "stepproc2")
(include-book "stepproc0")

(defun step-process (ms ps)                 ;; returns mstate
  (declare (xargs :guard (and (mstatep ms)
                              (pstatep ps))))

  (let ((stmt (if (zp (cc ps)) nil (ith (cc ps) (code ps)))))
    (cond
     ((atom stmt) ms)  ;; cc out of range
     (t (case (car stmt)
              (asgn                 (exec-asgn stmt ps ms))
              (setup-listener       (exec-setup-listener stmt ps ms))
              (connect              (exec-connect stmt ps ms))
              (accept               (exec-accept stmt ps ms))
              (my-hpid              (exec-my-hpid stmt ps ms))
              ((label procedure)    (exec-skip ps ms))
              (goto                 (exec-goto stmt ps ms))
              (call                 (exec-call stmt ps ms))
              (return               (exec-return ps ms))
              (branch               (exec-branch stmt ps ms))
              (send                 (exec-send stmt ps ms))
              (select               (exec-select stmt ps ms))
              (receive              (exec-receive stmt ps ms))
              (fork                 (exec-fork stmt ps ms))
              (exec                 (exec-exec stmt ps ms))
              (rsh                  (exec-rsh stmt ps ms))

	      (otherwise ms)))))) ;; bad statement

;; Prove that step-process preserves mstatep

(defthm step-process-mstatep
  (implies (and (mstatep ms)
                (pstatep ps))
           (mstatep (step-process ms ps)))
  :hints (("Goal"
           :in-theory (disable exec-asgn
			       exec-send
			       exec-select
			       exec-receive
			       exec-setup-listener
			       exec-connect
			       exec-accept
			       exec-my-hpid
			       exec-skip
			       exec-goto
			       exec-call
			       exec-return
			       exec-branch
			       exec-fork
			       exec-exec
			       exec-rsh
			       mstatep
			       pstatep
			       ))))


