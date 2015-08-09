#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#


(in-package "ACL2")

(include-book "asynch2")


;; The proof of correctness of the blocking equation:
;; Block(a) <--> Block(c) or Idle(b)
;; for the asynchronous join.

;; The first part of this book is generic for xdi state machines.

;; We apply the following internal ACL2 structure for storing xdi state machines:
;; (defun xdi-sm-join ()
;;   (list ;state initital type      transitions
;;         '(s0   t        box       (((a r ex) s1) ((b r ex) s2)))
;;         '(s1   nil      box       (((b r ex) s3)))
;;         '(s2   nil      box       (((a r ex) s3)))
;;         '(s3   nil      box       (((c r in) s4)))
;;         '(s4   nil      box       (((c a ex) s5)))
;;         '(s5   nil      box       (((a a in) s6) ((b a in) s7)))
;;         '(s6   nil      box       (((b a in) s0)))
;;         '(s7   nil      box       (((a a in) s0)))))
;; Each transition consists of a list (l s) where s denoted the state at the end of the transition, and l is a label.
;; Each label consists of (c R/A IN/EX), where c is a channel, on which either a Request or Ack occurs, which is an IN- or EXternal action.


;; The most intricate part is to define Blocked and Idle. We use the notions blocking and idling:
;; A state $s$ is \emph{blocking} wrt channel $c$ if it has send a request and still requires an acknowledgement.
;; Formally, if and only if is in between a $c.R$ input arrow and a $c.A$ output arrow.
;; Otherwise, i.e., if it has answered an acknowledgement and does not ask questions, it is idling.

;; The reason why a component can be stuck in some state is because the \emph{environment} prevents some transitions.
;; So we prove Blocking and Idle equations for any reasonable environment.
;; An example of an environment is '((b R)) indicating that the system will eventually never supply a request on channel $b$.
;; Similarly, environment '((c A)) indicates that the system will eventually never be able to send an ack to channel $c$.

;; The definition of Block of channel c in enviroment env is:
;; F G (blocking c env)
;; Similarly, Idle becomes:
;; F G (idling c env)

;; Function F-G-blocking_ and F-G-idling_ \emph{directly} formalize these definitions using defun-sk's.
;; Function F-G-blocking (without the underscore) is a \emph}{computational} function which given an xdi state, a channel, and an initial state
;; computes whether the state is eventualyl always blocking wrt to the channel.
;; The main part of this book is a proof that these executable functions correctly compute F-G-blocking (lemma's rewrite-non-exec-F-G-blocking_-to-exec-F-G-blocking-t and rewrite-non-exec-F-G-idling_-to-exec-F-G-blocking-nil).
;; Once this has been established, the following theorem is proven:
;;(defthm blocking-equation-join
;;  (and (xdi-smp-guard (xdi-sm-join))
;;       (implies (member-equal env (reasonable-envs (xdi-sm-join) '((a R))))
;;                (iff (Blocked_ (xdi-sm-join) 'a env)
;;                     (or (Blocked_ (xdi-sm-join) 'c env)
;;                         (Idle_ (xdi-sm-join) 'b env))))))
;; Using lemma's rewrite-non-exec-F-G-blocking_-to-exec-F-G-blocking-t and rewrite-non-exec-F-G-idling_-to-exec-F-G-blocking-nil, the non-executable functions Block_ and Idle_ which \emph{directly} formalize the corresponding definitions are rewritten to
;; their executable counterparts. ACL2 then automatically executes these functions for any environment $env$ in (reasonable-envs (xdi-sm-join) '((a R)))


;; -----
;; Valid input (i.e., guard conjectures):
;; -----
(defun transitionsp (transitions)
  (declare (xargs :guard t))
  (and (true-listp transitions)
       (A-len->= transitions 2)
       (A-true-listp (cars transitions))
       (A-len->= (cars transitions) 3)
       (eqlable-listp (cars (cars transitions)))
       (eqlable-listp (cadrs transitions))))
(defun A-transitionsp (x)
  (declare (xargs :guard (true-listp x)))
  (if (endp x)
    t
    (and (transitionsp (car x))
         (A-transitionsp (cdr x)))))
(defun xdi-smp (xdi-sm ss)
  (declare (xargs :guard (and (true-listp xdi-sm)
                              (A-true-listp xdi-sm)
                              (A-transitionsp (proj 3 xdi-sm))
                              (eqlable-listp ss))))
  (if (endp xdi-sm)
    t
    (and (subsetp (cadrs (nth 3 (car xdi-sm))) ss)
         (xdi-smp (cdr xdi-sm) ss))))
(defmacro xdi-smp-guard (xdi-sm)
  `(and (true-listp ,xdi-sm)
       (alistp ,xdi-sm)
       (A-len->= ,xdi-sm 1)
       (A-true-listp ,xdi-sm)
       (A-true-listp (proj 3 ,xdi-sm))
       (A-transitionsp (proj 3 ,xdi-sm))
       (eqlable-listp (cars ,xdi-sm))
       (xdi-smp ,xdi-sm (cars ,xdi-sm))))
(defmacro acks-guard (acks)
  `(and (alistp ,acks)
        (A-true-listp ,acks)))

(defthm spec-of-A-transitionsp
  (implies (and (A-transitionsp x)
                (member-equal a x))
           (transitionsp a)))
(defthm transition-has-at-least-two-elts
  (implies (transitionsp x)
           (A-len->= x 2)))
(defthm transitions-lead-to-valid-states
  (implies (and (xdi-smp xdi-sm ss)
                (member-equal x xdi-sm))
           (subsetp (cadrs (nth 3 x)) ss)))


;; -----
;; Function representing xdi state machines:
;; -----

;; Get initial state of xdi state machine
(defun xdi-get-initial-state (xdi-sm)
  (declare (xargs :guard (and (true-listp xdi-sm)
                              (A-true-listp xdi-sm))))
  (cond ((endp xdi-sm)
         nil)
        ((nth 1 (car xdi-sm))
         (caar xdi-sm))
        (t
         (xdi-get-initial-state (cdr xdi-sm)))))
;; Determine whether in the enviroment the channel is dead
;; Only external transitions can be dead
(defmacro dead (env channel/RA/IE)
  `(and (equal (nth 2 ,channel/RA/IE) 'ex)
        (member-equal (list (car ,channel/RA/IE) (cadr ,channel/RA/IE)) ,env)))
;; Do transitions:
(defun xdi-1step (s transition env)
  (declare (xargs :guard (and (>= (len transition) 2)
                              (true-listp (car transition))
                              (true-listp env))))
  (if (dead env (car transition))
    s
    (cadr transition)))
(defun xdi-1steps (s transitions env)
  (declare (xargs :guard (and (transitionsp transitions)
                              (true-listp env))))
  (if (endp transitions)
    nil
    (cons (xdi-1step s (car transitions) env)
          (xdi-1steps s (cdr transitions) env))))


(defun xdi-A-1steps (xdi-sm ss env)
  (declare (xargs :guard (and (xdi-smp-guard xdi-sm)
                              (eqlable-listp ss)
                              (subsetp ss (cars xdi-sm))
                              (true-listp env))
                  :guard-hints (("Subgoal 1" :use (:instance spec-of-A-transitionsp
                                                   (x (proj 3 xdi-sm))
                                                   (a (nth 3 (assoc (car ss) xdi-sm))))))))
  (if (endp ss)
    nil
    (append (xdi-1steps (car ss) (nth 3 (assoc (car ss) xdi-sm)) env)
            (xdi-A-1steps xdi-sm (cdr ss) env))))

;; -----
;; Compute whether channels are blocking/idling
;; -----
(defun acked_by (acks c0 c1)
  (declare (xargs :guard (and (eqlablep c0)
                              (acks-guard acks))))
  (if (assoc c0 acks)
    (equal (cadr (assoc c0 acks)) c1)
    (equal c0 c1)))
(defun compute-b/i (xdi-sm acks s/transitions channel flg result)
  (declare (xargs :well-founded-relation l<
                  :measure (list (len (remove-list (cars result) (cars xdi-sm)))
                                 (len s/transitions))
                  :verify-guards nil
                  :hints (("Goal" :in-theory (disable len-remove-equal)))
                  :guard (and (xdi-smp-guard xdi-sm)
                              (eqlablep channel)
                              (true-listp result)
                              (alistp result)
                              (A-len->= result 1)
                              (if (and s/transitions
                                       (atom s/transitions))
                                (and (eqlablep s/transitions)
                                     (member-equal s/transitions (cars xdi-sm)))
                                t)
                              (if (and s/transitions
                                       (not (atom s/transitions)))
                                (and (true-listp s/transitions)
                                     (transitionsp s/transitions)
                                     (subsetp (cadrs s/transitions) (cars xdi-sm)))
                                t)
                              (acks-guard acks)
                              )))
  (mbe :logic
       (cond ((not s/transitions)
              result)
             ((atom s/transitions)
              (cond ((not (member-equal s/transitions (cars xdi-sm)))
                     ;; Sanity check to ensure termination
                     nil)
                    ((assoc s/transitions result)
                     result)
                    (t
                     (seq result
                          (acons s/transitions `(,flg) result)
                          (compute-b/i xdi-sm acks (nth 3 (assoc s/transitions xdi-sm)) channel flg result)))))
             ((not (atom (cadar s/transitions)))
              ;; Sanity check to ensure termination
              nil)
             (t
              (let ((ret1 (cond ((and (equal (cadaar s/transitions) 'R)
                                      (equal (caaar s/transitions) channel))
                                 (compute-b/i xdi-sm acks (cadar s/transitions) channel (not flg) result))
                                ((and (equal (cadaar s/transitions) 'A)
                                      (acked_by acks channel (caaar s/transitions)))
                                 (compute-b/i xdi-sm acks (cadar s/transitions) channel nil result))
                                (t
                                 (compute-b/i xdi-sm acks (cadar s/transitions) channel flg result)))))
                (if (> (len (remove-list (cars ret1) (cars xdi-sm)))
                       (len (remove-list (cars result) (cars xdi-sm))))
                  ;; Sanity check to ensure termination
                  nil
                  (compute-b/i xdi-sm acks (cdr s/transitions) channel flg ret1)))))
       :exec
       (cond ((not s/transitions)
              result)
             ((atom s/transitions)
              (if (assoc s/transitions result)
                result
                (seq result
                     (acons s/transitions `(,flg) result)
                     (compute-b/i xdi-sm acks (nth 3 (assoc s/transitions xdi-sm)) channel flg result))))
             (t
              (seq result
                   (cond ((and (equal (cadaar s/transitions) 'R)
                                      (equal (caaar s/transitions) channel))
                                 (compute-b/i xdi-sm acks (cadar s/transitions) channel (not flg) result))
                                ((and (equal (cadaar s/transitions) 'A)
                                      (acked_by acks channel (caaar s/transitions)))
                                 (compute-b/i xdi-sm acks (cadar s/transitions) channel nil result))
                                (t
                                 (compute-b/i xdi-sm acks (cadar s/transitions) channel flg result)))
                   (compute-b/i xdi-sm acks (cdr s/transitions) channel flg result))))))



;; We prove that all sanity checks are unnecessary. Especially that the heck for termination is bogus (lemma correctness-measure-compute-b/i):
(defthm true-listp-compute-b/i
  (implies (true-listp result)
           (true-listp (compute-b/i xdi-sm acks s/transitions channel flg result)))
  :rule-classes :type-prescription)
(defthm alistp-compute-b/i
  (implies (alistp result)
           (alistp (compute-b/i xdi-sm acks s/transitions channel flg result)))
  :rule-classes :type-prescription)

(defthm correctness-measure-compute-b/i
  (implies (and (xdi-smp xdi-sm (cars xdi-sm))
                (A-true-listp (proj 3 xdi-sm))
                (A-transitionsp (proj 3 xdi-sm))
                (if (atom s/transitions)
                  (member-equal s/transitions (cars xdi-sm))
                  (and (transitionsp s/transitions)
                       (subsetp (cadrs s/transitions) (cars xdi-sm)))))
           (<= (len (remove-list (cars (compute-b/i xdi-sm acks s/transitions channel flg result)) (cars xdi-sm)))
               (len (remove-list (cars result) (cars xdi-sm)))))
  :rule-classes :linear
  :hints (("Subgoal *1/3.6" :use (:instance spec-of-a-true-listp
                                  (a (nth 3 (assoc-equal s/transitions xdi-sm)))
                                  (x (proj 3 xdi-sm))))))

(defthm eqlable-alistp-compute-b/i
  (implies (and (eqlable-listp (cars xdi-sm))
                (eqlable-alistp result))
           (eqlable-alistp (compute-b/i xdi-sm acks s/transitions channel flg result)))
  :rule-classes :type-prescription)
(defthm intial-state-is-a-valid-state
  (implies (xdi-get-initial-state xdi-sm)
           (member-equal (xdi-get-initial-state xdi-sm) (cars xdi-sm))))
(defthm result-compute-b/i-all-elts->=2
  (implies (A-len->= result 2)
           (A-len->= (compute-b/i xdi-sm acks s channel flg result) 2)))
(defthm result-compute-b/i-all-elts->=1
  (implies (A-len->= result 1)
           (A-len->= (compute-b/i xdi-sm acks s channel flg result) 1)))

(verify-guards compute-b/i
               :otf-flg t
               :hints (("Goal" :in-theory (disable spec-of-eqlable-listp))
                       ("Subgoal 1" :in-theory (disable spec-of-A-true-listp)
                                    :use ((:instance spec-of-a-true-listp
                                          (a (nth 3 (assoc-equal s/transitions xdi-sm)))
                                          (x (proj 3 xdi-sm)))
                                          (:instance spec-of-a-true-listp
                                          (a (assoc-equal s/transitions xdi-sm))
                                          (x xdi-sm))))))

(defthm all-elts->=2-implies-consp-values
  (implies (and (A-len->= x 2)
                (cdr (assoc a x)))
           (consp (cdr (assoc a x)))))

(defun blocking (xdi-sm acks s channel)
  (declare (xargs :guard (and (xdi-smp-guard xdi-sm)
                              (eqlablep channel)
                              (acks-guard acks))
                  :guard-hints (("Goal" :use ((:instance spec-of-eqlable-listp
                                               (a (xdi-get-initial-state xdi-sm))
                                               (x (cars xdi-sm))))))))
  (cadr (assoc s (compute-b/i xdi-sm acks (xdi-get-initial-state xdi-sm) channel nil nil))))
(defun idling (xdi-sm acks s channel)
  (declare (xargs :guard (and (xdi-smp-guard xdi-sm)
                              (eqlablep channel)
                              (acks-guard acks))))
  (not (blocking xdi-sm acks s channel)))


;; Compute whether channels are Generally blocking/idling
(defun G-blocking (xdi-sm acks visited ss channel positive env)
  (declare (xargs :well-founded-relation l<
                  :measure (list (len (remove-list visited (cars xdi-sm))) (len ss))
                  :verify-guards nil
                  :guard (and (xdi-smp-guard xdi-sm)
                              (eqlablep channel)
                              (acks-guard acks)
                              (true-listp ss)
                              (subsetp ss (cars xdi-sm))
                              (true-listp env)
                              (true-listp visited))))
  (cond ((not ss)
         visited)
        ((not (member-equal (car ss) (cars xdi-sm)))
         nil)
        ((endp (cdr ss))
         (if (not (member-equal (car ss) visited))
           (if (or (equal (nth 2 (assoc (car ss) xdi-sm)) 'transient)
                   (if positive
                     (blocking xdi-sm acks (car ss) channel)
                     (not (blocking xdi-sm acks (car ss) channel))))
             (G-blocking xdi-sm acks (cons (car ss) visited) (remove-equal (car ss) (xdi-A-1steps xdi-sm ss env)) channel positive env)
             nil)
           visited))
        (t
         (let ((ret (G-blocking xdi-sm acks visited (list (car ss)) channel positive env)))
           (cond ((equal ret nil)
                  ret)
                 (t
                  (let ((ret2 (G-blocking xdi-sm acks visited (cdr ss) channel positive env)))
                    (if ret2
                      (append ret ret2)
                      nil))))))))

(defthm new-states-in-recursive-step-are-valid-states
  (let ((newss (remove-equal a (xdi-1steps s transitions env))))
    (implies (and (xdi-smp xdi-sm ss)
                  (member-equal s ss)
                  (subsetp transitions (nth 3 (assoc s xdi-sm))))
             (subsetp newss ss))))
(defthm true-listp-G-blocking
  (implies (true-listp visited)
           (true-listp (G-blocking xdi-sm acks visited ss channel positive env)))
  :hints (("Subgoal *1/4.1" :expand (G-blocking xdi-sm acks visited ss channel nil env)))
  :rule-classes :type-prescription)
(verify-guards G-blocking
               :otf-flg t)

;; Compute whether channels are Finally Generally blocking/idling
(defun F-G-blocking (xdi-sm acks visited ss channel positive env)
  (declare (xargs :well-founded-relation l<
                  :measure (list (len (remove-list visited (cars xdi-sm))) (len ss))
                  :verify-guards nil
                  :guard (and (xdi-smp-guard xdi-sm)
                              (eqlablep channel)
                              (acks-guard acks)
                              (true-listp ss)
                              (true-listp env)
                              (true-listp visited))))
  (cond ((not ss)
         visited)
        ((not (member-equal (car ss) (cars xdi-sm)))
         nil)
        ((endp (cdr ss))
         (if (not (member-equal (car ss) visited))
           (if (G-blocking xdi-sm acks nil `(,(car ss)) channel positive env)
             t
             (F-G-blocking xdi-sm acks (cons (car ss) visited) (remove-equal (car ss) (xdi-A-1steps xdi-sm ss env)) channel positive env))
           visited))
        (t
         (let ((ret (F-G-blocking xdi-sm acks visited (list (car ss)) channel positive env)))
           (cond ((equal ret t)
                  ret)
                 (t
                  (let ((ret2 (F-G-blocking xdi-sm acks visited (cdr ss) channel positive env)))
                    (if (equal ret2 t)
                      ret2
                      (append ret ret2)))))))))
(defthm true-listp-F-G-blocking
  (implies (and (true-listp visited)
                (not (equal (F-G-blocking xdi-sm acks visited ss channel positive env) t)))
           (true-listp (F-G-blocking xdi-sm acks visited ss channel positive env))))
(verify-guards F-G-blocking
               :otf-flg t)

;; -----
;; Define Blocked/Idle
;; -----
(defun Blocked (xdi-sm acks channel env)
  (declare (xargs :guard (and (xdi-smp-guard xdi-sm)
                              (eqlablep channel)
                              (acks-guard acks))))
  (equal (F-G-blocking xdi-sm acks nil `(,(xdi-get-initial-state xdi-sm)) channel t (fix-true-listp env)) t))
(defun Idle (xdi-sm acks channel env)
  (declare (xargs :guard (and (xdi-smp-guard xdi-sm)
                              (eqlablep channel)
                              (acks-guard acks))))
  (equal (F-G-blocking xdi-sm acks nil `(,(xdi-get-initial-state xdi-sm)) channel nil (fix-true-listp env)) t))

;; -----
;; Compute all reasonable enviroments:
;; -----
(defun compute-external-actions-of-transitions (transitions live)
  (declare (xargs :guard (and (transitionsp transitions)
                              (true-listp live))))
  (cond ((endp transitions)
         nil)
        ((and (equal (nth 2 (caar transitions)) 'ex)
              (not (member-equal `(,(caaar transitions) ,(cadaar transitions)) live)))
         (cons `(,(caaar transitions) ,(cadaar transitions)) (compute-external-actions-of-transitions (cdr transitions) live)))
        (t
         (compute-external-actions-of-transitions (cdr transitions) live))))
(defun compute-external-actions (xdi-sm live)
 (if (endp xdi-sm)
    nil
    (append (compute-external-actions-of-transitions (nth 3 (car xdi-sm)) live)
            (compute-external-actions (cdr xdi-sm) live))))
(defun reasonable-envs (xdi-sm live)
  (powerset (remove-duplicates (compute-external-actions xdi-sm live))))


;; -----
;; We now define directly what we mean by F and G:
;; -----
(defun-sk E-transition (xdi-sm s1 s2 env)
  (exists (transition)
          (and (equal (xdi-1step s1 transition env) s2)
               (member-equal transition (nth 3 (assoc s1 xdi-sm))))))
(defun xdi-tracep (xdi-sm trace env)
  (cond ((endp trace)
         t)
        ((endp (cdr trace))
         t)
        (t
         (and (E-transition xdi-sm (car trace) (cadr trace) env)
              (xdi-tracep xdi-sm (cdr trace) env)))))

(defun-sk G-blocking_ (xdi-sm acks channel s env)
  (forall (trace)
          (implies (and (xdi-tracep xdi-sm trace env)
                        (equal (car trace) s))
                   (or (equal (nth 2 (assoc (car (last trace)) xdi-sm)) 'transient)
                       (blocking xdi-sm acks (car (last trace)) channel)))))
(defun-sk F-G-blocking_ (xdi-sm acks channel s env)
  (exists (trace)
          (and (xdi-tracep xdi-sm trace env)
               (equal (car trace) s)
               (G-blocking_ xdi-sm acks channel (car (last trace)) env))))
(defun-sk G-idling_ (xdi-sm acks channel s env)
  (forall (trace)
          (implies (and (xdi-tracep xdi-sm trace env)
                        (equal (car trace) s))
                   (or (equal (nth 2 (assoc (car (last trace)) xdi-sm)) 'transient)
                       (not (blocking xdi-sm acks (car (last trace)) channel))))))
(defun-sk F-G-idling_ (xdi-sm acks channel s env)
  (exists (trace)
          (and (xdi-tracep xdi-sm trace env)
               (equal (car trace) s)
               (G-idling_ xdi-sm acks channel (car (last trace)) env))))
(defmacro Blocked_ (xdi-sm acks channel env)
  `(F-G-blocking_ ,xdi-sm ,acks ,channel (xdi-get-initial-state ,xdi-sm) ,env))
(defmacro Idle_ (xdi-sm acks channel env)
  `(F-G-idling_ ,xdi-sm ,acks ,channel (xdi-get-initial-state ,xdi-sm) ,env))



;; Auxiliary functions:
(defun-sk xdi-reachable (xdi-sm env s1 s2)
  (exists (trace)
          (and (xdi-tracep xdi-sm trace env)
               (consp trace)
               (equal (car trace) s1)
               (equal (car (last trace)) s2))))
(defun A-xdi-reachable (xdi-sm env s ss)
  (if (endp ss)
    t
    (and (xdi-reachable xdi-sm env s (car ss))
         (A-xdi-reachable xdi-sm env s (cdr ss)))))

(defun A-blocking (xdi-sm acks ss positive channel)
  (if (endp ss)
    t
    (and (or (equal (nth 2 (assoc (car ss) xdi-sm)) 'transient)
             (if positive
               (blocking xdi-sm acks (car ss) channel)
               (not (blocking xdi-sm acks (car ss) channel))))
         (A-blocking xdi-sm acks (cdr ss) positive channel))))

(defun A-G-blocking_ (xdi-sm acks channel ss env)
  (if (endp ss)
    t
    (and (G-blocking_ xdi-sm acks channel (car ss) env)
         (A-G-blocking_ xdi-sm acks channel (cdr ss) env))))
(defun xdi-reach (xdi-sm visited ss env)
  (declare (xargs :well-founded-relation l<
                  :measure (list (len (remove-list visited (cars xdi-sm))) (len ss))))
  (cond ((not ss)
         nil)
        ((not (member-equal (car ss) (cars xdi-sm)))
         nil)
        ((endp (cdr ss))
         (if (not (member-equal (car ss) visited))
           (cons (car ss) (xdi-reach xdi-sm (cons (car ss) visited) (remove-equal (car ss) (xdi-A-1steps xdi-sm ss env)) env))
           visited))
        (t
         (append (xdi-reach xdi-sm visited (list (car ss)) env)
                 (xdi-reach xdi-sm visited (cdr ss) env)))))
(defun-sk xdi-reachable-wihout-visited (xdi-sm env s1 s2 visited)
  (exists (trace)
          (and (xdi-tracep xdi-sm trace env)
               (no-duplicatesp-equal trace)
               (consp trace)
               (not-in trace visited)
               (equal (car trace) s1)
               (equal (car (last trace)) s2))))
(defun-sk E-s-xdi-reachable-wihout-visited (xdi-sm env ss s visited)
  (exists (s1)
          (and (member-equal s1 ss)
               (xdi-reachable-wihout-visited xdi-sm env s1 s visited))))





;; A.) (G-blocking_ s) --> (G-blocking s)
;; The proof is by induction over G-blocking. We prove that G-blocking returns a result other than nil.
;; This ammounts to proving that the case in G-blocking where a idling state is encountered does not happen.
;; In order to prove this, we make an assumption that has to be proven is an invariant over G-blocking:
;; all states in the set of states ss currently under exploration can be reached from the initial state s.
;; To prove that this is actually an invariant we have to prove a conceptually trivial lemma (next-steps-are-still-reachable) which states
;; that if s1 ~~> s2, for any state s2' in the set of states obtained by doing one transition from s2, we have s1~~> s2'.
;; Using this invariant, the prove of our theorem becomes easy:
;; As soon as G-blocking encounters a state s_f, we now from the invariant that s ~~> s_f.
;; From the assumption (G-blocking_ s) we can prove that s_f is blocking, which is expressed by lemma spec-of-G-blocking_:
(defthm spec-of-G-blocking_
  (implies (and (G-blocking_ xdi-sm acks channel s env)
                (xdi-reachable xdi-sm env s s_f)
                (not (equal (nth 2 (assoc s_f xdi-sm)) 'transient)))
           (blocking xdi-sm acks s_f channel))
  :hints (("Goal" :use ((:instance G-blocking_-necc
                         (trace (xdi-reachable-witness xdi-sm env s s_f)))))))
(defthm spec-of-G-idling_
  (implies (and (G-idling_ xdi-sm acks channel s env)
                (xdi-reachable xdi-sm env s s_f)
                (not (equal (nth 2 (assoc s_f xdi-sm)) 'transient)))
           (not (blocking xdi-sm acks s_f channel)))
  :hints (("Goal" :use ((:instance G-idling_-necc
                         (trace (xdi-reachable-witness xdi-sm env s s_f)))))))
;; To prove that the invariant holds we have to show s1 ~~> s2' for any new state s2'.
;; We have to instantiate a new witness trace t_{s1~~>s2'} for this.
;; As we know that s1 ~~> s2, there is a witness trace t_{s1~~>s2}.
;; The witness is obtained by appending the new state to the existing witness:
;; t_{s1~~>s2'} := (append t_{s1~~>s2} (list s2'))
;; Thus we need lemma's about appending traces:
(defthm xdi-tracep-append
  (iff (xdi-tracep xdi-sm (append t1 t2) env)
       (and (xdi-tracep xdi-sm t1 env)
            (xdi-tracep xdi-sm t2 env)
            (or (endp t2)
                (endp t1)
                (E-transition xdi-sm (car (last t1)) (car t2) env)))))
;;; The hints instantiate the witness. We have to prove that the transition from s2 to s2' is a legal one.
(defthm next-steps-are-still-reachable
  (implies (and (xdi-reachable xdi-sm env s1 s2)
                (subsetp transitions (nth 3 (assoc-equal s2 xdi-sm))))
           (A-xdi-reachable xdi-sm env s1 (xdi-1steps s2 transitions env)))
  :hints (("Subgoal *1/2" :do-not '(eliminate-destructors generalize)
                          :use ((:instance xdi-reachable-suff
                                 (s2 (cadar transitions))
                                 (trace (append (xdi-reachable-witness xdi-sm env s1 s2) `(,(cadar transitions)))))
                                (:instance E-transition-suff
                                 (s1 s2)
                                 (s2 (cadar transitions))
                                 (transition (car transitions)))))))
;; Function G-blocking removes the current state from all next steps.
;; Lemma 1.1 proves the invariant for all next steps. We have to prove that removing states preserves the invariant:
(defthm A-xdi-reachable-preserved-by-remove
  (implies (A-xdi-reachable xdi-sm env s ss)
           (A-xdi-reachable xdi-sm env s (remove-equal x ss))))
;; We can prove theorem A.)
(defthm G-blocking_-->G-blocking-t
  (implies (and (xdi-smp xdi-sm (cars xdi-sm))
                (G-blocking_ xdi-sm acks channel s env)
                (consp ss)
                (subsetp ss (cars xdi-sm))
                (A-xdi-reachable xdi-sm env s ss))
           (G-blocking xdi-sm acks visited ss channel t env))
  :hints (("Goal" :in-theory (disable G-blocking_ blocking idling xdi-reachable))))
(defthm G-idling_-->G-blocking-nil
  (implies (and (xdi-smp xdi-sm (cars xdi-sm))
                (G-idling_ xdi-sm acks channel s env)
                (consp ss)
                (subsetp ss (cars xdi-sm))
                (A-xdi-reachable xdi-sm env s ss))
           (G-blocking xdi-sm acks visited ss channel nil env))
  :hints (("Goal" :in-theory (disable G-idling_ blocking idling xdi-reachable))))


;; B.) (G-blocking s) --> (G-blocking_ s)
;; The reasoning is as follows:
;; 1.) Any state returned by G_blocking is actually blocking (lemma all-states-in-G-blocking-are-blocking)
;; 2.) For any set of states ss, the set of states returned by (G-blocking ss) contains all states returned by (xdi-reach ss), assuming it
;;     it returns anything at all (lemma G-blocking-implies-all-reachable-states-in-G-blocking)
;; 3.) Any state reachable from any state in ss is actually in (xdi-reach ss). This is basically a proof that xdi-reach is correct.
;; 4.) We have to prove that any state s2 reachable from s is blocking. So we can assume a witness trace t_{s~~>s2} from s to s2.
;;     By 3.) it follows that s2 is in (xdi-reach (list s)),
;;     By 2.) it follows that s2 is in (G-blocking_ ss),
;;     by 1.) it follows that s2 is blocking.


;; 1.) Any state returned by G_blocking is actually blocking (lemma all-states-in-G-blocking-are-blocking)
(defthm all-states-in-G-blocking-are-blocking
  (implies (A-blocking xdi-sm acks visited positive channel)
           (A-blocking xdi-sm acks (G-blocking xdi-sm acks visited ss channel positive env) positive channel))
  :hints (("subgoal *1/4.1" :expand (G-blocking xdi-sm acks visited ss channel nil env))))
;; 2.) For any set of states ss, the set of states returned by (G-blocking ss) contains all states returned by (xdi-reach ss), assuming it
;;     it returns anything at all (lemma G-blocking-implies-all-reachable-states-in-G-blocking)
;; If it has already been added to visited, then it will certainly be in the return result:
(defthm G-blocking-implies-all-visited-states-in-G-blocking
  (implies (and (G-blocking xdi-sm acks visited ss channel positive env)
                (member-equal s visited))
           (member-equal s (G-blocking xdi-sm acks visited ss channel positive env)))
  :hints (("subgoal *1/5.1.2" :expand (G-blocking xdi-sm acks visited ss channel nil env))))
(defthm G-blocking-implies-all-reachable-states-in-G-blocking
  (implies (G-blocking xdi-sm acks visited ss channel positive env)
           (subsetp (xdi-reach xdi-sm visited ss env)
                    (G-blocking xdi-sm acks visited ss channel positive env)))
  :hints (("Goal" :do-not '(eliminate-destructors generalize))))
;; 3.) Any state reachable from any state in ss is actually in (xdi-reach ss). This is basically a proof that xdi-reach is correct.
;; This was a difficult proof:
;; It is done by induction over xdi-reach (lemma spec-of-xdi-reach).
;; You cannot simply formulate this lemma by saying that any state s2 reachable from any state in the set of states ss currently under
;; exploration will be added to the return value of xdi-reach, because this is not true: if the path towards s2 includes visited
;; states, then s2 is reachable from some state s in ss, but it will not be added to xdi-reach.
;; We have to formulate it more subtly: any state s2 for which there exists a state s in ss such that s~~s2 AND this trace does not
;; include any visited state, AND this path is simple, will be added to xdi-reach. This lemma (lemma spec-of-xdi-reach) can be proven inductively.

;; I will use s1~!v~>2 to denote that s2 i reachable from s1 without visiting any states in visited.
;; So first we have to prove lemma E-s-xdi-reachable-wihout-visited-is-invariant which states that assuming:
;;      exists s1 in ss . s1~!v~>s2
;; there exists a state s1' in the set of new states newss obtained at each recursive call of xdi-reach. Thus we prove:
;;      exists s1' in newss . s1'~!v~>s2
;; Note that s1 is added to visited, so the witness for s1'~!v~>s2 cannot contain s1 itselve. This is way we require simple paths.
(defthm live-transition-in-set-of-next-states
  (implies (and (member-equal transition transitions)
                (not (dead env (car transition))))
           (member-equal (cadr transition) (xdi-1steps s1 transitions env))))
(defthm 2nd-elt-of-trace-in-set-of-next-states-1st-elt
  (implies (and (xdi-tracep xdi-sm trace env)
                (not (member-equal (car trace) (cdr trace)))
                (consp (cdr trace)))
           (member-equal (cadr trace)
                         (remove-equal (car trace) (xdi-1steps (car trace) (nth 3 (assoc-equal (car trace) xdi-sm)) env))))
  :otf-flg t
  :hints (("Goal" :use (:instance live-transition-in-set-of-next-states
                        (transition (E-transition-witness xdi-sm (car trace) (cadr trace) env))
                        (s1 (car trace))
                        (transitions (nth 3 (assoc-equal (car trace) xdi-sm)))))))
(defthm xdi-reachable-wihout-visited-is-invariant
  (implies (and (xdi-reachable-wihout-visited xdi-sm env s1 s2 visited)
                (consp (cdr (xdi-reachable-wihout-visited-witness xdi-sm env s1 s2 visited))))
           (xdi-reachable-wihout-visited xdi-sm env (cadr (xdi-reachable-wihout-visited-witness xdi-sm env s1 s2 visited)) s2 (cons s1 visited)))
  :hints (("Goal" :use (:instance xdi-reachable-wihout-visited-suff
                        (visited (cons s1 visited))
                        (s1 (cadr (xdi-reachable-wihout-visited-witness xdi-sm env s1 s2 visited)))
                        (trace (cdr (xdi-reachable-wihout-visited-witness xdi-sm env s1 s2 visited)))))))
(defthm E-s-xdi-reachable-wihout-visited-is-invariant
  (let ((newss (remove-equal s1 (xdi-1steps s1 (nth 3 (assoc-equal s1 xdi-sm)) env))))
    (implies (and (xdi-reachable-wihout-visited xdi-sm env s1 s2 visited)
                  (not (member-equal s1 visited))
                  (not (equal s1 s2)))
             (E-s-xdi-reachable-wihout-visited xdi-sm env newss s2 (cons s1 visited))))
  :otf-flg t
  :hints (("Goal" :use ((:instance E-s-xdi-reachable-wihout-visited-suff
                         (s s2)
                         (visited (cons s1 visited))
                         (ss (remove-equal s1 (xdi-1steps s1 (nth 3 (assoc-equal s1 xdi-sm)) env)))
                         (s1 (cadr (xdi-reachable-wihout-visited-witness xdi-sm env s1 s2 visited))))
                        (:instance xdi-reachable-wihout-visited-is-invariant)
                        (:instance 2nd-elt-of-trace-in-set-of-next-states-1st-elt
                         (trace (xdi-reachable-wihout-visited-witness xdi-sm env s1 s2 visited)))
                        (:instance xdi-reachable-wihout-visited-suff
                         (trace (xdi-reachable-wihout-visited-witness xdi-sm env s1 s2 visited)))))))
;; We can now prove lemma spec-of-xdi-reach which states that any state s2 reachable from any state in ss without using visited states
;; will be added to the result of (xdi-reach ss)
(defthm spec-of-E-s-xdi-reachable-wihout-visited
  (implies (and (E-s-xdi-reachable-wihout-visited xdi-sm env ss s2 visited)
                (consp ss)
                (endp (cdr ss)))
           (xdi-reachable-wihout-visited xdi-sm env (car ss) s2 visited)))
(defthm E-s-xdi-reachable-wihout-visited-nil-if-no-states
  (implies (endp ss)
           (not (E-s-xdi-reachable-wihout-visited xdi-sm env ss s2 visited))))
(defthm E-s-xdi-reachable-wihout-visited-in-singleton-list
  (iff (E-s-xdi-reachable-wihout-visited xdi-sm env (list s1) s2 visited)
       (xdi-reachable-wihout-visited xdi-sm env s1 s2 visited))
  :hints (("Goal" :use ((:instance E-s-xdi-reachable-wihout-visited-suff
                         (s s2)
                         (ss (list s1)))
                        (:instance xdi-reachable-wihout-visited-suff
                         (trace (E-s-xdi-reachable-wihout-visited xdi-sm env (list s1) s2 visited)))))))
(defthm E-s-xdi-reachable-wihout-visited-split-into-two
  (implies (E-s-xdi-reachable-wihout-visited xdi-sm env ss s2 visited)
           (or (E-s-xdi-reachable-wihout-visited xdi-sm env (list (car ss)) s2 visited)
               (E-s-xdi-reachable-wihout-visited xdi-sm env (cdr ss) s2 visited)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance E-s-xdi-reachable-wihout-visited-suff
                         (s1 (E-s-xdi-reachable-wihout-visited-witness xdi-sm env ss s2 visited))
                         (ss (cdr ss)))))))
(defthm spec-of-xdi-reach
  (implies (and (xdi-smp xdi-sm (cars xdi-sm))
                (E-s-xdi-reachable-wihout-visited xdi-sm env ss s2 visited)
                (subsetp ss (cars xdi-sm)))
           (member-equal s2 (xdi-reach xdi-sm visited ss env)))
  :hints (("Goal" :induct (xdi-reach xdi-sm visited ss env))
          ("Subgoal *1/5" :use (:instance E-s-xdi-reachable-wihout-visited-split-into-two))))
;; Lemma spec-of-xdi-reach is instantiated with visited == nil and ss == (list s) and s2 the state of which we haveto show that it is blocking.
;; (E-s-xdi-reachable-wihout-visited xdi-sm env (list ss) s2 nil) is logically equivalent to s~~s2.
;; An existential quantifier over a singleton list is simplified automatically, and the fact that a path may not contain
;; any state in nil is automatically proven.
;; (G-blocking_ s) requires us to prove that for any state s2 such that s~~>s2, s2 is blocking.
;; To be able to use lemma spec-of-xdi-reach, we have to show that the trace t_{s~~>s2} can be transformed into a simple trace, i.e., one without
;; any duplicates.

;; We prove that any path from s1 to s2 can always be transformed to a simple path by applying function find-simple-path
(defthm xdi-tracep-member
  (implies (xdi-tracep xdi-sm trace env)
           (xdi-tracep xdi-sm (member-equal s trace) env)))
(defthm xdi-tracep-cdr
  (implies (xdi-tracep xdi-sm trace env)
           (xdi-tracep xdi-sm (cdr trace) env)))
(defthm xdi-tracep-skip-to-last
  (implies (xdi-tracep xdi-sm trace env)
           (xdi-tracep xdi-sm (skip-to-last trace s) env)))
(defthm xdi-tracep-implies-existence-of-transition-between-two-consecutive-members
  (implies (and (xdi-tracep xdi-sm trace env)
                (member-equal s trace)
                (not (equal (car (last trace)) s)))
            (E-transition xdi-sm
                         s
                         (car (skip-to-last trace s))
                         env))
  :hints (("Goal" :in-theory (disable E-transition))))
(defthm xdi-tracep-find-simple-path
  (implies (xdi-tracep xdi-sm trace env)
           (xdi-tracep xdi-sm (find-simple-path trace) env))
    :hints (("Goal" :in-theory (disable E-transition))))
;; Finally, we can apply 1--3.) to prove lemma G-blocking-t-->G-blocking_:
(defthm spec-of-A-blocking
  (implies (and (A-blocking xdi-sm acks ss positive channel)
                (member-equal s ss))
           (or (equal (nth 2 (assoc s xdi-sm)) 'transient)
               (if positive
                 (blocking xdi-sm acks s channel)
                 (not (blocking xdi-sm acks s channel)))))
  :rule-classes :forward-chaining)
(defthm A-blocking-subset
  (implies (and (A-blocking xdi-sm acks ss2 positive channel)
                (subsetp ss1 ss2))
           (A-blocking xdi-sm acks ss1 positive channel)))
(defthm G-blocking-t-->G-blocking_
  (implies (and (xdi-smp xdi-sm (cars xdi-sm))
                (member-equal s (cars xdi-sm))
                (G-blocking xdi-sm acks nil (list s) channel t env))
           (G-blocking_ xdi-sm acks channel s env))
  :hints (("Goal" :in-theory (disable G-blocking-implies-all-reachable-states-in-G-blocking all-states-in-G-blocking-are-blocking spec-of-xdi-reach xdi-reachable-wihout-visited)
                  :use ((:instance G-blocking-implies-all-reachable-states-in-G-blocking
                         (visited nil)
                         (positive t)
                         (ss (list s)))
                        (:instance all-states-in-G-blocking-are-blocking
                         (visited nil)
                         (positive t)
                         (ss (list s)))
                        (:instance spec-of-xdi-reach
                         (s2 (car (last (G-blocking_-witness xdi-sm acks channel s env))))
                         (ss (list s))
                         (visited nil))
                        (:instance xdi-reachable-wihout-visited-suff
                         (trace (find-simple-path (G-blocking_-witness xdi-sm acks channel s env)))
                         (visited nil)
                         (s1 s)
                         (s2 (car (last (G-blocking_-witness xdi-sm acks channel s env)))))
                        (:instance spec-of-A-blocking
                         (positive t)
                         (s (car (last (G-blocking_-witness xdi-sm acks channel s env))))
                         (ss (xdi-reach xdi-sm nil (list s) env)))))))
(defthm G-blocking-nil-->G-idling_
  (implies (and (xdi-smp xdi-sm (cars xdi-sm))
                (member-equal s (cars xdi-sm))
                (G-blocking xdi-sm acks nil (list s) channel nil env))
           (G-idling_ xdi-sm acks channel s env))
  :hints (("Goal" :in-theory (disable G-blocking-implies-all-reachable-states-in-G-blocking all-states-in-G-blocking-are-blocking spec-of-xdi-reach xdi-reachable-wihout-visited)
                  :use ((:instance G-blocking-implies-all-reachable-states-in-G-blocking
                         (visited nil)
                         (positive nil)
                         (ss (list s)))
                        (:instance all-states-in-G-blocking-are-blocking
                         (visited nil)
                         (positive nil)
                         (ss (list s)))
                        (:instance spec-of-xdi-reach
                         (s2 (car (last (G-idling_-witness xdi-sm acks channel s env))))
                         (ss (list s))
                         (visited nil))
                        (:instance xdi-reachable-wihout-visited-suff
                         (trace (find-simple-path (G-idling_-witness xdi-sm acks channel s env)))
                         (visited nil)
                         (s1 s)
                         (s2 (car (last (G-idling_-witness xdi-sm acks channel s env)))))
                        (:instance spec-of-a-blocking
                         (positive nil)
                         (s (car (last (G-idling_-witness xdi-sm acks channel s env))))
                         (ss (xdi-reach xdi-sm nil (list s) env)))))))



;; Correctness of our implementation of G-blocking_
(defthm rewrite-non-exec-G-blocking_-to-exec-G-blocking-t
  (implies (and (xdi-smp xdi-sm (cars xdi-sm))
                (member-equal s (cars xdi-sm)))
           (iff (G-blocking_ xdi-sm acks channel s env)
                (G-blocking xdi-sm acks nil (list s) channel t env)))
  :hints (("Goal" :in-theory (disable G-blocking G-blocking_ xdi-reachable)
                  :use ((:instance xdi-reachable-suff
                         (trace (list s))
                         (s1 s)
                         (s2 s))))))
(defthm rewrite-non-exec-G-idling_-to-exec-G-blocking-nil
  (implies (and (xdi-smp xdi-sm (cars xdi-sm))
                (member-equal s (cars xdi-sm)))
           (iff (G-idling_ xdi-sm acks channel s env)
                (G-blocking xdi-sm acks nil (list s) channel nil env)))
  :hints (("Goal" :in-theory (disable G-blocking G-idling_ xdi-reachable)
                  :use ((:instance xdi-reachable-suff
                         (trace (list s))
                         (s1 s)
                         (s2 s))))))

(in-theory (disable G-blocking-t-->G-blocking_ G-blocking-nil-->G-idling_ G-blocking_-->G-blocking-t G-idling_-->G-blocking-nil))

;; Correctness of our implementation of F-G-blocking_
(defthm F-G-blocking-t-->F-G-blocking_-inductive
  (implies (and (xdi-smp xdi-sm (cars xdi-sm))
                (equal (F-G-blocking xdi-sm acks visited ss channel t env) t)
                (consp ss)
                (subsetp ss (cars xdi-sm))
                (A-xdi-reachable xdi-sm env s ss))
           (F-G-blocking_ xdi-sm acks channel s env)))
(defthm F-G-blocking-nil-->F-G-idling_-inductive
  (implies (and (xdi-smp xdi-sm (cars xdi-sm))
                (equal (F-G-blocking xdi-sm acks visited ss channel nil env) t)
                (consp ss)
                (subsetp ss (cars xdi-sm))
                (A-xdi-reachable xdi-sm env s ss))
           (F-G-idling_ xdi-sm acks channel s env)))
(defthm F-G-blocking-t-->F-G-blocking_
  (implies (and (xdi-smp xdi-sm (cars xdi-sm))
                (member-equal s (cars xdi-sm))
                (equal (F-G-blocking xdi-sm acks nil (list s) channel t env) t))
           (F-G-blocking_ xdi-sm acks channel s env))
  :hints (("Goal" :in-theory (disable F-G-blocking-t-->F-G-blocking_-inductive xdi-reachable-wihout-visited)
                  :use ((:instance F-G-blocking-t-->F-G-blocking_-inductive
                         (visited nil)
                         (ss (list s)))
                        (:instance xdi-reachable-suff
                         (trace (list s))
                         (s1 s)
                         (s2 s))))))
(defthm F-G-blocking-nil-->F-G-idling_
  (implies (and (xdi-smp xdi-sm (cars xdi-sm))
                (member-equal s (cars xdi-sm))
                (equal (F-G-blocking xdi-sm acks nil (list s) channel nil env) t))
           (F-G-idling_ xdi-sm acks channel s env))
  :hints (("Goal" :in-theory (disable F-G-blocking-nil-->F-G-idling_-inductive xdi-reachable-wihout-visited)
                  :use ((:instance F-G-blocking-nil-->F-G-idling_-inductive
                         (visited nil)
                         (ss (list s)))
                        (:instance xdi-reachable-suff
                         (trace (list s))
                         (s1 s)
                         (s2 s))))))
(defun A-not-G-blocking (xdi-sm acks ss channel positive env)
  (if (endp ss)
    t
    (and (not (G-blocking xdi-sm acks nil (list (car ss)) channel positive env))
         (A-not-G-blocking xdi-sm acks (cdr ss) channel positive env))))
(defthm all-states-in-F-G-blocking-are-not-G-blocking
  (implies (A-not-G-blocking xdi-sm acks visited channel positive env)
           (A-not-G-blocking xdi-sm acks (F-G-blocking xdi-sm acks visited ss channel positive env) channel positive env)))
(defthm not-F-G-blocking-implies-visited-states-in-F-G-blocking
  (implies (and (xdi-smp xdi-sm (cars xdi-sm))
                (consp ss)
                (subsetp ss (cars xdi-sm))
                (not (equal (F-G-blocking xdi-sm acks visited ss channel positive env) t))
                (member-equal s visited))
           (member-equal s (F-G-blocking xdi-sm acks visited ss channel positive env)))
  :hints (("Goal" :in-theory (disable blocking))))
(defthm not-F-G-blocking-implies-all-reachable-states-in-F-G-blocking
  (implies (and (xdi-smp xdi-sm (cars xdi-sm))
                (subsetp ss (cars xdi-sm))
                (not (equal (F-G-blocking xdi-sm acks visited ss channel positive env) t)))
           (subsetp (xdi-reach xdi-sm visited ss env)
                    (F-G-blocking xdi-sm acks visited ss channel positive env)))
  :hints (("Subgoal *1/6.1" :use (:instance not-F-G-blocking-implies-visited-states-in-F-G-blocking
                                  (s (car ss))
                                  (ss (remove-equal (car ss) (xdi-1steps (car ss) (nth 3 (assoc-equal (car ss) xdi-sm)) env)))
                                  (visited (cons (car ss) visited))))))
(defthm spec-of-A-not-G-blocking
  (implies (and (A-not-G-blocking xdi-sm acks ss channel positive env)
                (member-equal s ss))
           (not (G-blocking xdi-sm acks nil `(,s) channel positive env))))
(defthm A-not-G-blocking-subset
  (implies (and (A-not-G-blocking xdi-sm acks ss2 channel positive env)
                (subsetp ss1 ss2))
           (A-not-G-blocking xdi-sm acks ss1 channel positive env)))
(defthm xdi-reach-contains-visited-states
  (implies (and (subsetp visited (cars xdi-sm))
                (member-equal s (xdi-reach xdi-sm visited ss env)))
           (member-equal s (cars xdi-sm))))
(defthm F-G-blocking_-->F-G-blocking-t
  (implies (and (xdi-smp xdi-sm (cars xdi-sm))
                (member-equal s (cars xdi-sm))
                (F-G-blocking_ xdi-sm acks channel s env))
           (equal (F-G-blocking xdi-sm acks nil (list s) channel t env) t))
  :hints (("Goal" :in-theory (disable all-states-in-F-G-blocking-are-not-G-blocking not-F-G-blocking-implies-all-reachable-states-in-F-G-blocking spec-of-xdi-reach G-blocking_ blocking idling xdi-reachable-wihout-visited)
                  :use ((:instance xdi-reach-contains-visited-states
                         (ss (list s))
                         (visited nil)
                         (s (car (last (F-G-blocking_-witness xdi-sm acks channel s env)))))
                        (:instance not-F-G-blocking-implies-all-reachable-states-in-F-G-blocking
                         (positive t)
                         (visited nil)
                         (ss (list s)))
                        (:instance all-states-in-F-G-blocking-are-not-G-blocking
                         (positive t)
                         (visited nil)
                         (ss (list s)))
                        (:instance spec-of-xdi-reach
                         (s2 (car (last (F-G-blocking_-witness xdi-sm acks channel s env))))
                         (ss (list s))
                         (visited nil))
                        (:instance xdi-reachable-wihout-visited-suff
                         (trace (find-simple-path (F-G-blocking_-witness xdi-sm acks channel s env)))
                         (visited nil)
                         (s1 s)
                         (s2 (car (last (F-G-blocking_-witness xdi-sm acks channel s env)))))
                        (:instance spec-of-A-not-G-blocking
                         (positive t)
                         (s (car (last (F-G-blocking_-witness xdi-sm acks channel s env))))
                         (ss (xdi-reach xdi-sm nil (list s) env)))))))
(defthm F-G-idling_-->F-G-blocking-nil
  (implies (and (xdi-smp xdi-sm (cars xdi-sm))
                (member-equal s (cars xdi-sm))
                (F-G-idling_ xdi-sm acks channel s env))
           (equal (F-G-blocking xdi-sm acks nil (list s) channel nil env) t))
  :hints (("Goal" :in-theory (disable all-states-in-F-G-blocking-are-not-G-blocking not-F-G-blocking-implies-all-reachable-states-in-F-G-blocking spec-of-xdi-reach G-idling_ blocking idling xdi-reachable-wihout-visited)
                  :use ((:instance xdi-reach-contains-visited-states
                         (ss (list s))
                         (visited nil)
                         (s (car (last (F-G-idling_-witness xdi-sm acks channel s env)))))
                        (:instance not-F-G-blocking-implies-all-reachable-states-in-F-G-blocking
                         (positive nil)
                         (visited nil)
                         (ss (list s)))
                        (:instance all-states-in-F-G-blocking-are-not-G-blocking
                         (positive nil)
                         (visited nil)
                         (ss (list s)))
                        (:instance spec-of-xdi-reach
                         (s2 (car (last (F-G-idling_-witness xdi-sm acks channel s env))))
                         (ss (list s))
                         (visited nil))
                        (:instance xdi-reachable-wihout-visited-suff
                         (trace (find-simple-path (F-G-idling_-witness xdi-sm acks channel s env)))
                         (visited nil)
                         (s1 s)
                         (s2 (car (last (F-G-idling_-witness xdi-sm acks channel s env)))))
                        (:instance spec-of-A-not-G-blocking
                         (positive nil)
                         (s (car (last (F-G-idling_-witness xdi-sm acks channel s env))))
                         (ss (xdi-reach xdi-sm nil (list s) env)))))))
(defthm rewrite-non-exec-F-G-blocking_-to-exec-F-G-blocking-t
  (implies (and (xdi-smp xdi-sm (cars xdi-sm))
                (member-equal s (cars xdi-sm)))
           (equal (F-G-blocking_ xdi-sm acks channel s env)
                  (equal (F-G-blocking xdi-sm acks nil (list s) channel t env) t)))
  :hints (("Goal" :use (:instance F-G-blocking-t-->F-G-blocking_)))
  :rule-classes :definition)
(defthm rewrite-non-exec-F-G-idling_-to-exec-F-G-blocking-nil
  (implies (and (xdi-smp xdi-sm (cars xdi-sm))
                (member-equal s (cars xdi-sm)))
           (equal (F-G-idling_ xdi-sm acks channel s env)
                  (equal (F-G-blocking xdi-sm acks nil (list s) channel nil env) t)))
  :hints (("Goal" :use (:instance F-G-blocking-nil-->F-G-idling_)))
  :rule-classes :definition)
(in-theory (disable F-G-blocking-t-->F-G-blocking_ F-G-blocking-nil-->F-G-idling_ F-G-blocking_-->F-G-blocking-t F-G-idling_-->F-G-blocking-nil F-G-blocking_ F-G-idling_))



;; Finally, we provide a function to decide whether the xdi-sm is persistent for some channel:
(defun check-persistency  (xdi-sm acks s/transitions channel flg result)
  (declare (xargs :mode :program))
  (cond ((not s/transitions)
         result)
        ((atom s/transitions)
         (if (assoc s/transitions result)
           (if (or (equal (cadr (assoc s/transitions result)) flg)
                   (equal (nth 2 (assoc s/transitions xdi-sm)) 'transient))
             result
             'error)
           (seq result
                (acons s/transitions `(,flg) result)
                (check-persistency xdi-sm acks (nth 3 (assoc s/transitions xdi-sm)) channel flg result))))
        (t
         (seq result
              (cond ((and (equal (cadaar s/transitions) 'R)
                          (equal (caaar s/transitions) channel))
                     (check-persistency xdi-sm acks (cadar s/transitions) channel (not flg) result))
                    ((and (equal (cadaar s/transitions) 'A)
                          (acked_by acks channel (caaar s/transitions)))
                     (check-persistency xdi-sm acks (cadar s/transitions) channel nil result))
                    (t
                     (check-persistency xdi-sm acks (cadar s/transitions) channel flg result)))
              (check-persistency xdi-sm acks (cdr s/transitions) channel flg result)))))


(defun input-wirep (xdi-sm wire)
  (member-equal (list (car wire) (cadr wire) 'ex) (strip-cars (uni (proj 3 xdi-sm)))))
(defun envp (xdi-sm env)
  (if (endp env)
    t
    (and (input-wirep xdi-sm (car env))
         (envp xdi-sm (cdr env)))))
(defun A-envp (xdi-sm envs)
  (if (endp envs)
    t
    (and (envp xdi-sm (car envs))
         (A-envp xdi-sm (cdr envs)))))

(defun remove-stable-wire-transitions (transitions env)
  (cond ((endp transitions)
         nil)
        ((dead env (caar transitions))
         (remove-stable-wire-transitions (cdr transitions) env))
        (t
         (cons (car transitions)
               (remove-stable-wire-transitions (cdr transitions) env)))))#|ACL2s-ToDo-Line|#
