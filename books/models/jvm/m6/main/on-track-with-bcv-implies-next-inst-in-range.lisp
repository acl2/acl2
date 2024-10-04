(in-package "DJVM")
(include-book "../main/djvm-simple")
(include-book "../DJVM/consistent-state-bcv-on-track")



(encapsulate () 
  (local (include-book "djvm-consistent-state-facts"))
  (defthm consistent-state-wff-insts-f
    (implies (consistent-state s)
             (wff-insts (code-instrs (method-code (deref-method (current-method-ptr s)
                                                                (instance-class-table s))))))
    :rule-classes :forward-chaining))


(defthm consistent-state-wff-insts-b
    (implies (consistent-state s)
             (wff-insts (code-instrs (method-code (current-method s)))))
    :hints (("Goal" :use ((:instance consistent-state-wff-insts-f)))))
                                     




(defthm if-inst-by-offset-not-equal-invalid-offset
  (implies (and (wff-insts codes)
                (not (equal (inst-by-offset1 offset codes)
                            (LIST OFFSET '(JVM::INVALID-INST-OFFSET)))))
           (wff-inst (inst-by-offset1 offset codes)))
  :hints (("Goal" :in-theory (disable wff-inst))))



(local (in-theory (disable method-loaded-from consistent-state-bcv-on-track
                           consistent-callee-frame-bcv method-code
                           code-instrs
                           stack-maps-witness)))
                           

(skip-proofs 
 (defthm if-method-loaded-from-and-recorded-signature-exists
   (implies (and (method-loaded-from method-ptr cl scl)
                 (bcv::searchStackFrame  
                  pc 
                  (bcv::stack-map-wrap (stack-maps-witness method-ptr scl))))
            (not (equal (inst-by-offset1 pc (code-instrs (method-code 
                                                          (deref-method method-ptr cl))))
                        (LIST pc '(JVM::INVALID-INST-OFFSET)))))))



(defthm if-method-loaded-from-and-recorded-signature-exists-specific
  (implies (and (method-loaded-from (method-ptr (current-frame s))
                                    (instance-class-table s)
                                    (env-class-table (env s)))
                (bcv::searchStackFrame  
                 pc
                 (bcv::stack-map-wrap (stack-maps-witness (method-ptr
                                                           (current-frame s)) 
                                                          (env-class-table (env s))))))
           (not (equal (inst-by-offset1 pc (code-instrs (method-code
                                                         (current-method s))))
                       (LIST pc '(JVM::INVALID-INST-OFFSET)))))
  :hints (("Goal" :use ((:instance
                         if-method-loaded-from-and-recorded-signature-exists
                         (method-ptr (method-ptr (current-frame s)))
                         (cl (instance-class-table s))
                         (scl (env-class-table (env s))))))))


(skip-proofs 
 (defthm consistent-state-bcv-on-track-implies-consistent-frame-bcv
   (implies (and (consistent-state-bcv-on-track djvm-s)
                 (consistent-state djvm-s))
            (consistent-callee-frame-bcv 
             (pc djvm-s)
             (current-frame djvm-s)
             (heap djvm-s)
             (heap-init-map (aux djvm-s))
             (instance-class-table djvm-s)
             (env-class-table (env djvm-s))))
   :hints (("Goal" :in-theory (disable consistent-callee-frame-bcv)))
   :rule-classes :forward-chaining))


(defthm consistent-calleed-frame-bcv-implies-searchStackFrameFounnd
  (implies (consistent-callee-frame-bcv pc frame hp hp-init cl scl)
           (bcv::searchStackFrame  
            pc 
            (bcv::stack-map-wrap (stack-maps-witness (method-ptr frame) scl))))
  :hints (("Goal" :in-theory (e/d (consistent-callee-frame-bcv)
                                  (bcv::searchStackFrame
                                   stack-maps-witness
                                   consistent-frame-bcv0))))
  :rule-classes :forward-chaining)




(defthm consistent-calleed-frame-method-loaded-from
  (implies (consistent-callee-frame-bcv pc frame hp hp-init cl scl)
           (method-loaded-from (method-ptr frame) cl scl))
  :hints (("Goal" :in-theory (e/d (consistent-callee-frame-bcv
                                    consistent-frame-bcv0)
                                  (bcv::searchStackFrame
                                   stack-maps-witness))))
  :rule-classes :forward-chaining)




(defthm consistent-state-strong-implies-wff-inst-next-inst
  (IMPLIES (and (CONSISTENT-STATE-STRONG djvm-S)
                (consistent-state-bcv-on-track djvm-s))
           (WFF-INST (NEXT-INST djvm-S)))
  :hints (("Goal" :in-theory (e/d (next-inst consistent-state-strong)
                                  (consistent-state-bcv-on-track 
                                   consistent-callee-frame-bcv
                                   wff-inst)))))
