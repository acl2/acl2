(in-package "BCV")
(include-book "typechecker")
(include-book "typechecker-ext")
(include-book "typechecker-simple")
(include-book "bcv-base")


(encapsulate () 
  (local (include-book "bcv-searchStackFrame-reduce-support"))
  (defthm searchStackFrame-is-if-stack-map
  (implies (and (isStackMap (car mergedcode))
                (equal (forward-to-next-inst mergedcode) 
                       (forward-to-next-inst x))
                (is-suffix mergedcode all-merged-code)
                (PC-WFF-MERGEDCODE1 PC ALL-MERGED-CODE)
                (mergedcodeistypesafe env all-merged-code init-frame))
           (EQUAL
            (SEARCHSTACKFRAME
             (INSTROFFSET (CAR (FORWARD-TO-NEXT-INST x)))
             (STACK-MAP-WRAP (COLLECT-SIG-FRAME-VECTOR ENV all-merged-code
                                                       INIT-FRAME)))
            (NEXT-STACKFRAME mergedcode)))))



;; (skip-proofs 
;; (defthm searchStackFrame-is-if-stack-map-specific
;;    (implies (and (is-suffix (list* mergedcode3 mergedcode5 mergedcode6)
;;                             all-merged-code)
;;                  (isStackMap mergedcode3)
;;                  (isInstruction mergedcode6)
;;                  (PC-WFF-MERGEDCODE1 PC ALL-MERGED-CODE)
;;                  (mergedcodeistypesafe env all-merged-code init-frame))
;;             (EQUAL
;;              (SEARCHSTACKFRAME
;;               (INSTROFFSET mergedcode5)
;;               (STACK-MAP-WRAP (COLLECT-SIG-FRAME-VECTOR ENV all-merged-code
;;                                                         INIT-FRAME)))
;;              (mapFrame (getMap mergedcode3))))))


(encapsulate () 
  (local (include-book "bcv-searchStackFrame-reduce-support-2"))
  (defthm mergecodeIsTypeSafe-implies-collect-sig-vector-compatible-1
    (implies (and (mergedcodeIsTypeSafe env mergecode stackframe)
                  (member inst mergecode)
                  (isInstruction inst)
                  (isInstruction (next-inst inst mergecode))
                  (pc-wff-mergedcode1 (next-pc mergecode) mergecode))
             (equal (car (sig-do-inst inst
                                      env
                                      (searchStackFrame (instroffset inst)
                                                        (stack-map-wrap
                                                         (collect-sig-frame-vector
                                                          env mergecode
                                                          stackframe)))))
                    (searchStackFrame (instroffset (next-inst inst mergecode))
                                      (stack-map-wrap (collect-sig-frame-vector
                                                       env mergecode
                                                       stackframe)))))))





 

;; (encapsulate () 
;;   (local (include-book "bcv-searchStackFrame-reduce-support-2"))
;;   (defthm mergecodeIsTypeSafe-implies-collect-sig-vector-compatible-2
;;    (implies (and (mergedcodeIsTypeSafe env mergecode stackframe)
;;                  (member inst mergecode)
;;                  (member (next-inst inst mergecode) mergecode)
;;                  (isInstruction inst)
;;                  (isStackMap (next-inst inst mergecode))
;;                  (pc-wff-mergedcode1 pc mergecode))
;;             (equal (car (sig-do-inst inst
;;                                      env
;;                                      (searchStackFrame (instroffset inst)
;;                                                        (stack-map-wrap(collect-sig-frame-vector
;;                                                                        env mergecode
;;                                                                        stackframe)))))

