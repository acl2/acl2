#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#


(in-package "ACL2")

(include-book "asynch")
(include-book "parse-state-machine-descriptions")#|ACL2s-ToDo-Line|#



;; Important theorem for automatic verification of the theorems below
(defthm member-equal-fwc
  (equal (member-equal e (cons a b))
         (if (equal e a) (cons a b)
             (member-equal e b))))


;; note that we exclude any environment in which the system can permanently not send a request to channel 'a.
;; in other words, the blocking equation holds under the assumption that something actually needs to happen on channel 'a.
;; Block(a) = Block(c) or Idle(b)
(defthm blocking-equation-join
  (and (xdi-smp-guard *xdi-sm-join*)
       (implies (member-equal env (reasonable-envs *xdi-sm-join* '((in0 R))))
                (iff (Blocked_ *xdi-sm-join* nil 'in0 env)
                     (or (Blocked_ *xdi-sm-join* nil 'out env)
                         (Idle_ *xdi-sm-join* nil 'in1 env)))))
  :otf-flg t
  :rule-classes nil)


(defthm idle-equation-join
  (and (xdi-smp-guard *xdi-sm-join*)
       (implies (member-equal env (reasonable-envs *xdi-sm-join* nil))
                (iff (Idle_ *xdi-sm-join* nil 'out (reasonable-envs *xdi-sm-join* nil))
                     (or (Idle_ *xdi-sm-join* nil 'in0 (reasonable-envs *xdi-sm-join* nil))
                         (Idle_ *xdi-sm-join* nil 'in1 (reasonable-envs *xdi-sm-join* nil))))))
  :otf-flg t
  :rule-classes nil)


;; Block(a) = Block(c) or Block(b)
(defthm blocking-equation-fork
  (and (xdi-smp-guard *xdi-sm-fork*)
       (implies (member-equal env (reasonable-envs *xdi-sm-fork* nil))
                (iff (Blocked_ *xdi-sm-fork* nil 'in env)
                     (or (Blocked_ *xdi-sm-fork* nil 'out0 env)
                         (Blocked_ *xdi-sm-fork* nil 'out1 env)))))
  :otf-flg t
  :rule-classes nil)
;; Idle(b) = Block(c) or Idle(a)
(defthm idle-equation-fork
  (and (xdi-smp-guard *xdi-sm-fork*)
       (implies (member-equal env (reasonable-envs *xdi-sm-fork* '((out0 A))))
                (iff (Idle_ *xdi-sm-fork* nil 'out0 env)
                     (or (Idle_ *xdi-sm-fork* nil 'in env)
                         (Blocked_ *xdi-sm-fork* nil 'out1 env)))))
  :otf-flg t
  :rule-classes nil)



;; Block(a) = Block(c)
(defthm blocking-equation-merge
  (and (xdi-smp-guard *xdi-sm-merge*)
       (implies (member-equal env (reasonable-envs *xdi-sm-merge* '((in0 R))))
                (iff (Blocked_ *xdi-sm-merge* nil 'in0 env)
                     (Blocked_ *xdi-sm-merge* nil 'out env))))
  :otf-flg t
  :rule-classes nil)
(defthm idle-equation-merge
  (and (xdi-smp-guard *xdi-sm-merge*)
       (implies (member-equal env (reasonable-envs *xdi-sm-merge* nil))
                (iff (Idle_ *xdi-sm-merge* nil 'out env)
                     (and (Idle_ *xdi-sm-merge* nil 'in0 env)
                          (Idle_ *xdi-sm-merge* nil 'in1 env)))))
  :otf-flg t
  :rule-classes nil)

;; Block(a) = Block(b)
(defthm blocking-equation-storage
  (and (xdi-smp-guard *xdi-sm-storage*)
       (implies (member-equal env (reasonable-envs *xdi-sm-storage* nil))
                (iff (Blocked_ *xdi-sm-storage* nil 'in env)
                     (Blocked_ *xdi-sm-storage* nil 'out env))))
  :otf-flg t
  :rule-classes nil)
;; Idle(b) = Block(a)
(defthm idle-equation-storage
  (and (xdi-smp-guard *xdi-sm-storage*)
       (implies (member-equal env (reasonable-envs *xdi-sm-storage* nil))
                (iff (Idle_ *xdi-sm-storage* nil 'out env)
                     (Idle_ *xdi-sm-storage* nil 'in env))))
  :otf-flg t
  :rule-classes nil)

;; Block(a) = Idle(select) or (not Idle(select01) and Block(c)) or (not Idle(select10) and Block(b))
(defthm blocking-equation-distributor
  (and (xdi-smp-guard *xdi-sm-distributor*)
       (acks-guard *xdi-sm-distributor-acks*)
       (implies (member-equal env (reasonable-envs *xdi-sm-distributor* '((in R))))
                (iff (Blocked_ *xdi-sm-distributor* *xdi-sm-distributor-acks* 'in env)
                     (or (and (Idle_ *xdi-sm-distributor* *xdi-sm-distributor-acks* 'select00 env)
                              (Idle_ *xdi-sm-distributor* *xdi-sm-distributor-acks* 'select01 env)
                              (Idle_ *xdi-sm-distributor* *xdi-sm-distributor-acks* 'select10 env))
                         (and (not (Idle_ *xdi-sm-distributor* *xdi-sm-distributor-acks* 'select01 env))
                              (Blocked_ *xdi-sm-distributor* *xdi-sm-distributor-acks* 'out1 env))
                         (and (not (Idle_ *xdi-sm-distributor* *xdi-sm-distributor-acks* 'select10 env))
                              (Blocked_ *xdi-sm-distributor* *xdi-sm-distributor-acks* 'out0 env)))
                     )))
  :otf-flg t
  :rule-classes nil)




#|
(check-persistency *xdi-sm-storage* nil 's0 'in nil nil)
(check-persistency *xdi-sm-join* nil 's0 'in0 nil nil)
(check-persistency *xdi-sm-fork* nil 's0 'in nil nil)
(check-persistency *xdi-sm-merge* nil 's0 'out nil nil)
(check-persistency *xdi-sm-distributor* *xdi-sm-distributor-acks* 's0 'select00 nil nil)
(check-persistency *xdi-sm-distributor* *xdi-sm-distributor-acks* 's0 'select01 nil nil)
(check-persistency *xdi-sm-distributor* *xdi-sm-distributor-acks* 's0 'select10 nil nil)
(check-persistency *xdi-sm-distributor* *xdi-sm-distributor-acks* 's0 'in nil nil)
|#
