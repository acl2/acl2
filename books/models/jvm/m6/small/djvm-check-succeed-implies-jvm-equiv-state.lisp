(in-package "ACL2")
(include-book "jvm-model")
(include-book "djvm-model")
(include-book "state-equiv-def")
(include-book "generic")


(local 
 (in-theory (enable
             djvm-check-INVOKE
             djvm-check-POP
             djvm-check-PUSH
             djvm-check-RETURN
             djvm-check-IFEQ)))



(defthm state-equiv-implies-pushStack-state-equiv
  (implies (state-equiv jvm-s djvm-s)
           (state-equiv (pushStack v jvm-s)
                        (pushStack v djvm-s))))




(defthm state-equiv-implies-call-frame-equiv-equal
  (implies (and (state-equiv jvm-s djvm-s)
                (consp (g 'call-stack djvm-s)))
           (call-frame-equiv (car (g 'call-stack jvm-s))
                             (car (g 'call-stack djvm-s))))
  :hints (("Goal" :in-theory (enable state-equiv))))



(defthm state-equiv-implies-topStack-equal
  (implies (state-equiv jvm-s djvm-s)
           (equal (topstack jvm-s)
                  (topstack djvm-s)))
  :hints (("Goal" :cases ((consp (g 'call-stack djvm-s)))
           :in-theory (disable state-equiv-implies-call-frame-equiv-equal))
          ("Subgoal 1" :use ((:instance state-equiv-implies-call-frame-equiv-equal)))))


(defthm state-equiv-implies-method-name-equal
  (implies (state-equiv jvm-s djvm-s)
           (equal (g 'method-name (car (g 'call-stack jvm-s)))
                  (g 'method-name (car (g 'call-stack djvm-s)))))
  :hints (("Goal" :cases ((consp (g 'call-stack djvm-s)))
           :in-theory (disable state-equiv-implies-call-frame-equiv-equal))
          ("Subgoal 1" :use ((:instance
                              state-equiv-implies-call-frame-equiv-equal)))))



(defthm state-equiv-implies-op-stack-equal
  (implies (state-equiv jvm-s djvm-s)
           (equal (g 'op-stack (car (g 'call-stack jvm-s)))
                  (g 'op-stack (car (g 'call-stack djvm-s)))))
  :hints (("Goal" :cases ((consp (g 'call-stack djvm-s)))
           :in-theory (disable state-equiv-implies-call-frame-equiv-equal))
          ("Subgoal 1" :use ((:instance
                              state-equiv-implies-call-frame-equiv-equal)))))






(defthm state-equiv-implies-popStack-state-equiv
  (implies (state-equiv jvm-s djvm-s)
           (state-equiv (popStack jvm-s)
                        (popStack djvm-s)))
  :hints (("Goal" :use ((:instance  state-equiv-implies-op-stack-equal)))))
                                    



(defthm state-equiv-implies-set-pc-state-equiv
  (implies (state-equiv jvm-s djvm-s)
           (state-equiv (set-pc pc jvm-s)
                        (set-pc pc djvm-s))))


(defthm state-equiv-implies-get-pc-equal
  (implies (state-equiv jvm-s djvm-s)
           (equal (get-pc jvm-s)
                  (get-pc djvm-s))))


(defthm state-equiv-implies-push-init-frame
  (implies (state-equiv jvm-s djvm-s)
           (state-equiv (pushInitFrame 
                           name locals jvm-s)
                        (pushInitFrame 
                          name locals djvm-s))))




(defthm state-equiv-implies-pop-call-stack
  (implies (state-equiv jvm-s djvm-s)
           (state-equiv (s 'call-stack
                           (cdr (g 'call-stack jvm-s))
                           jvm-s)
                        (s 'call-stack
                           (cdr (g 'call-stack djvm-s))
                           djvm-s))))

  

(in-theory (disable pushStack popStack set-pc get-pc
                    state-equiv
                    pushInitFrame
                    pushStack))




(defthm state-equiv-implies-popStack-n
  (implies (state-equiv jvm-s djvm-s)
           (state-equiv (popStack-n jvm-s n)
                        (popStack-n djvm-s n)))
  :hints (("Goal" :do-not '(generalize))))



(defthm call-stack-equiv-implies-consp
  (implies (CALL-STACK-EQUIV jvm-cs djvm-cs)
           (equal (consp jvm-cs)
                  (consp djvm-cs))))



(defthm state-equiv-implies-consp-call-stack
  (implies (state-equiv jvm-s djvm-s)
           (equal (consp (g 'call-stack jvm-s))
                  (consp (g 'call-stack djvm-s))))
  :hints (("Goal" :in-theory (enable state-equiv call-stack-equiv))))



(defthm state-equiv-implies-consp-call-stack-2
  (implies (state-equiv jvm-s djvm-s)
           (equal (consp (cdr (g 'call-stack jvm-s)))
                  (consp (cdr (g 'call-stack djvm-s)))))
  :hints (("Goal" :in-theory (enable state-equiv call-stack-equiv))))


(defthm class-table-equiv-implies-method-equiv
  (implies (and (class-table-equiv jvm-cl djvm-cl)
                (bound? name djvm-cl))
           (method-equiv (cdr (assoc-equal name jvm-cl))
                         (cdr (assoc-equal name djvm-cl)))))



(defthm state-equiv-implies-method-code-equal
  (implies (and (state-equiv jvm-s djvm-s)
                (case-split (bound? name (g 'method-table djvm-s))))
           (equal (g 'code (cdr (assoc-equal name (g 'method-table jvm-s))))
                  (g 'code (cdr (assoc-equal name (g 'method-table djvm-s))))))
  :hints (("Goal" :in-theory (e/d (state-equiv)
                                  (class-table-equiv 
                                   class-table-equiv-implies-method-equiv))
           :use ((:instance class-table-equiv-implies-method-equiv
                            (jvm-cl  (g 'method-table jvm-s))
                            (djvm-cl (g 'method-table djvm-s)))))))
           
(defthm state-equiv-implies-nargs-equal
  (implies (and (state-equiv jvm-s djvm-s)
                (case-split (bound? name (g 'method-table djvm-s))))
           (equal (g 'nargs (cdr (assoc-equal name (g 'method-table jvm-s))))
                  (g 'nargs(cdr (assoc-equal name (g 'method-table djvm-s))))))
  :hints (("Goal" :in-theory (e/d (state-equiv)
                                  (class-table-equiv 
                                   class-table-equiv-implies-method-equiv))
           :use ((:instance class-table-equiv-implies-method-equiv
                            (jvm-cl  (g 'method-table jvm-s))
                            (djvm-cl (g 'method-table djvm-s)))))))



(defthm if-not-nil-next-inst-then-bound-general
  (implies (not (assoc-equal name cl))
           (not (car (nth pc (G 'CODE (CDR (ASSOC-EQUAL name cl))))))))


(defthm if-not-nil-next-inst-then-bound-specific
  (implies (car (nth (get-pc djvm-s) 
                     (G 'CODE (CDR (ASSOC-EQUAL name (g 'method-table djvm-s))))))
           (assoc-equal name (g 'method-table djvm-s)))
  :hints (("Goal" :use ((:instance if-not-nil-next-inst-then-bound-general
                                   (pc (get-pc djvm-s))
                                   (cl (g 'method-table djvm-s)))))))


(defthm djvm-check-step-implies-method-bound
  (implies (djvm-check-step djvm-s)
           (assoc-equal (g 'method-name 
                           (car (g 'call-stack djvm-s)))
                        (g 'method-table djvm-s))))
           

(defthm get-pc-noramlize
  (equal (G 'PC (CAR (G 'CALL-STACK JVM-S)))
         (get-pc jvm-s))
  :hints (("Goal" :in-theory (enable get-pc))))


(defthm djvm-check-succeed-implies-jvm-equiv-state
  (implies (and (state-equiv jvm-s djvm-s)
                (djvm-check-step djvm-s))
           (state-equiv (m-step jvm-s)
                        (djvm-step djvm-s)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable consistent-state))))

