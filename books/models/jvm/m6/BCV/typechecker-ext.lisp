(in-package "BCV")
(include-book "typechecker")

;----------------------------------------------------------------------

(defun collect-sig-frame-vector (env mergedcode stackmap)
  (if (endp mergedcode) nil
    (if (endp (cdr mergedcode)) nil
      (if (equal stackmap 'afterGoto)
          (if (isStackMap (car Mergedcode))
              (collect-sig-frame-vector env (cdr mergedcode) 
                                        (mapFrame (getMap (car mergedcode))))
            nil)
        (cond ((isStackMap (car mergedcode))
               (and (frameIsAssignable stackmap 
                                       (mapFrame (getMap (car mergedcode)))
                                       env)
                    (collect-sig-frame-vector 
                     env (cdr mergedcode) (mapFrame (getMap (car mergedcode))))))
              ((isInstruction (car mergedcode))
               (let ((offset     (instrOffset (car MergedCode)))
                     (instr      (car MergedCode)))
                 (and (instructionIsTypeSafe instr env stackmap)
                      (mv-let (NextStackFrame ExceptionStackFrame)
                              (sig-do-inst instr env stackmap)
                              (and (instructionSatisfiesHandlers env offset
                                                                 ExceptionStackFrame)
                                   (mergedCodeIsTypeSafe env (cdr MergedCode)
                                                         NextStackFrame)
                                   (cons (list offset stackmap)
                                         (collect-sig-frame-vector 
                                          env 
                                          (cdr mergedcode) 
                                          NextStackFrame)))))))
              (t nil))))))

;----------------------------------------------------------------------

;; (defun pair-with-pc (parsedcode sig-frames)
;;   (if (endp parsedcode) nil
;;     (if (endp sig-frames) nil
;;       (cons (cons (instrOffset (car parsedcode))
;;                   (car sig-frames))
;;             (pair-with-pc (cdr parsedcode) (cdr sig-frames))))))
                
            
;----------------------------------------------------------------------

(defun collect-sig-frame-vector-for-method (class method static-class-table)
  (let*
   ((framesize (framesize method class))
    (maxstack (maxstack method class))
    (parsedcode (parsedcode method class))
    (handlers (handlers method class))
    (stackmap (stackmap method class))
    (mergedcode (mergestackmapandcode stackmap parsedcode))
    (stackframe
     (methodinitialstackframe class method framesize))
    (returntype (methodreturntype method))
    (environment
     (makeenvironment class method returntype
                      mergedcode maxstack handlers static-class-table)))
   (collect-sig-frame-vector environment mergedcode stackframe)))


;----------------------------------------------------------------------

(defun collect-sig-frame-vector-for-methods (class methods cl)
  (if (endp methods)
      nil
    (if (or (mem '*abstract*  (methodAccessFlags (car methods)))
            (mem '*native*  (methodAccessFlags (car methods))))
        (collect-sig-frame-vector-for-methods class (cdr methods) cl)
      (prog2$ 
       (cw "      method ~p0~%~%" (methodname (car methods)))
       (bind (car methods)
             (collect-sig-frame-vector-for-method class (car methods) cl)
             (collect-sig-frame-vector-for-methods class (cdr methods) cl))))))


(defun collect-sig-frame-vector-for-classes (l cl)
  (if (endp l)
      nil
    (prog2$ 
     (acl2::cw "class ~p0~%~%" (classClassName (car l)))
     (bind (car l)
           (collect-sig-frame-vector-for-methods (car l)
                                                 (classMethods (car l))
                                                 cl)
           (collect-sig-frame-vector-for-classes (cdr l) cl)))))
  

;----------------------------------------------------------------------



(defun simple-test-method (class method cl)
  (prog2$ 
   (cw "      method ~p0~%~%" (methodname method))
   (or (equal (len (parsedcode1 method))
              (+ 1 (len (collect-sig-frame-vector-for-method class method cl))))
       (prog2$ (cw "method code, frame does not match")
               nil))))


(defun simple-test-methods (class methods cl)
  (if (endp methods)
      t
    (if (or (mem '*abstract*  (methodAccessFlags (car methods)))
            (mem '*native*  (methodAccessFlags (car methods))))
        (simple-test-methods class (cdr methods) cl)
      (and (simple-test-method class (car methods) cl)
           (simple-test-methods class (cdr methods) cl)))))


(defun simple-test-classes (l cl)
  (if (endp l)
      t
    (prog2$ 
     (acl2::cw "class ~p0~%~%" (classClassName (car l)))
     (and (simple-test-methods (car l)
                               (classMethods (car l))
                               cl)
          (simple-test-classes (cdr l) cl)))))


;----------------------------------------------------------------------


                                        
                                         
                                         
                                          

                                          
                                          
                                          
                                                                   
                            
                      
                    
                                        
              
      

     
     
     
     
     

  