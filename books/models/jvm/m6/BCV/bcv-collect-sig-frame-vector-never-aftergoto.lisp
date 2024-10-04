(in-package "BCV")
(include-book "typechecker")
(include-book "typechecker-ext")
(include-book "typechecker-simple")
(include-book "bcv-base")



;; (encapsulate ()
;;   (local (include-book "bcv-instructionIsTypeSafe-if-verified"))
;;   (defthm mergedcodeIsTypesafe-implies-instructionIsTypeSafe
;;     (implies (and (mergedcodeIsTypesafe env mergedcode stackframe)
;;                   (pc-wff-mergedcode1 0 (allinstructions env))
;;                   (is-suffix mergedcode (allinstructions env))
;;                   (member inst (extract-code mergedcode)))
;;              (instructionIsTypeSafe 
;;               inst 
;;               env
;;               (searchStackFrame (instrOffset inst)
;;                                 (stack-map-wrap 
;;                                  (collect-sig-frame-vector env
;;                                                            mergedcode
;;                         


(local
(defun collect-frames (stack-maps)
  (if (endp stack-maps) nil
    (cons (mapFrame (car stack-maps))
          (collect-frames (cdr stack-maps))))))


  
(local 
(defthm not-member-aftergoto-collect-sig-frame-vector 
  (not (member 'aftergoto (collect-frames 
                           (collect-sig-frame-vector env code init-frame))))
  :hints (("Goal" :in-theory (disable instructionIsTypeSafe
                                      instructionSatisfiesHandlers
                                      instrOffset
                                      sig-do-inst
                                      allinstructions
                                      isEnd
                                      ;;mapFrame
                                      getMap mapOffset
                                      frameIsAssignable
                                      isInstruction
                                      isStackMap)
           :do-not '(generalize)))))

(local
(defthm not-member-aftergoto-then-not-found
  (implies (not (member 'aftergoto (collect-frames stack-maps)))
           (not (equal (searchStackFrame any (stack-map-wrap stack-maps))
                       'aftergoto)))))


(defthm collect-sig-frame-vector-never-aftergoto
  (not (equal (searchstackframe 
               any 
               (stack-map-wrap (collect-sig-frame-vector any-env any-code
                                                         any-init-frame)))
              'aftergoto))
  :hints (("Goal" :in-theory (disable instructionIsTypeSafe
                                      instructionSatisfiesHandlers
                                      instrOffset
                                      sig-do-inst
                                      allinstructions
                                      isEnd
                                      ;;mapFrame
                                      getMap mapOffset
                                      frameIsAssignable
                                      isInstruction
                                      isStackMap)
           :do-not '(generalize))))
