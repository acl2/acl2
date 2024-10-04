(in-package "ACL2")
(include-book "jvm-model")

;------------------------------------------------------------
;
;   The BCV for the Small Machine 
;
;------------------------------------------------------------


(defun stack-map? (map)
  (and (equal (g 'is-stack-map map) t)
       (equal (g 'is-inst map) nil)
       (integerp (g 'pc map))))

(defun inst? (inst)
  (and (equal (g 'is-inst inst) t)
       (equal (g 'is-stack-map inst) nil)
       (integerp (g 'pc inst))))

(defun wff-code1 (code pc)
  (if (endp code) 
      (equal code nil)
    (and (and (inst? (car code))
              (equal (g 'pc (car code)) pc)
              (not (stack-map? (car code))))
         (wff-code1 (cdr code) (+ 1 pc)))))


(defun wff-code (code)
  (and (consp code)
       (wff-code1 code 0)))

(defun wff-maps (maps)
  (if (endp maps) (equal maps nil)
    (and (stack-map? (car maps))
         (wff-maps (cdr maps)))))

(defun bcv-op-code (inst)
  (op-code (g 'inst inst)))

(defun bcv-arg (inst)
  (arg (g 'inst inst)))

;----------------------------------------------------------------------

(defun max-stack (sig-frame)
  (g 'max-stack sig-frame))

(defun bcv-check-PUSH (inst sig-frame)
  (declare (ignore inst))
  (<= (+ 1 (g 'op-stack sig-frame))
      (max-stack sig-frame)))

(defun advance-pc (sig-frame)
  (s 'pc 
     (+ 1 (g 'pc sig-frame))
     sig-frame))

(defun sig-frame-push-value (v sig-frame)
  (declare (ignore v))
  (s 'op-stack
     (+ 1 (g 'op-stack sig-frame))
     sig-frame))

(defun bcv-execute-PUSH (inst sig-frame)
  (advance-pc 
   (sig-frame-push-value (bcv-arg inst)
                         sig-frame)))


(defun bcv-check-POP (inst sig-frame)
  (declare (ignore inst))
  (<= 1 (g 'op-stack sig-frame)))

(defun sig-frame-pop-value (sig-frame)
  (if (zp (g 'op-stack sig-frame))
         sig-frame
    (s 'op-stack 
       (-  (g 'op-stack sig-frame) 1)
       sig-frame)))


(defun bcv-execute-POP (inst sig-frame)
  (declare (ignore inst))
  (advance-pc 
   (sig-frame-pop-value sig-frame)))

;;; The only important thing we care (in this example) is the size of the
;;; operand stack.
;;;
;;; Our BCV examine a program, method by method.
;;;
;;; We will show that verified program will never violate the operand stack
;;; size limit.


(defun sig-local-compatible (slocals glocals)
  (declare (ignore slocals glocals))
  ;; temp implementation
  t)

(defun sig-opstack-compatible (sframe gframe)
  (equal (g 'op-stack sframe)
         (g 'op-stack gframe)))


(defun sig-frame-compatible (sframe gframe)
  (and (equal (g 'pc sframe)
              (g 'pc gframe))
       (equal (g 'max-stack sframe)
              (g 'max-stack gframe))
       (equal (g 'method-name sframe)
              (g 'method-name gframe))
       (equal (g 'method-table sframe)
              (g 'method-table gframe))
       (sig-opstack-compatible sframe gframe)
       (sig-local-compatible (g 'locals sframe)
                             (g 'locals gframe))))




(defun targetIsSafe (pc sig-frame partial-sig-vector)
  (and (bound? pc partial-sig-vector)
       (stack-map? (binding pc partial-sig-vector))
       (sig-frame-compatible 
        sig-frame 
        (binding pc partial-sig-vector))))



;; (i-am-here) ;; Fri Oct 28 21:01:16 2005

(defun extract-partial-sig-vector (maps)
  (if (endp maps) nil
    (cons (cons (g 'pc (car maps))
                (car maps))
          (extract-partial-sig-vector (cdr maps)))))



;; (defun bcv-check-IFEQ (inst sig-frame)
;;   (and (<= 1 (g 'op-stack sig-frame))
;;        (targetIsSafe 
;;         (arg inst)
;;         (sig-frame-pop-value sig-frame)
;;         (extract-partial-sig-vector 
;;          (g 'stackmaps
;;             (binding (g 'method-name sig-frame)
;;                      (g 'method-table sig-frame)))))))
;;   ;; (extract-sig-vector (g 'stackmaps sig-frame)))
        

(defun update-maps-with-method-table (maps method-name method-table)
  (if (endp maps) maps
    (cons (s 'method-name method-name (s 'method-table method-table 
                                         (s 'max-stack 
                                            (g 'max-stack
                                               (binding method-name 
                                                        method-table))
                                            (car maps))))
          (update-maps-with-method-table (cdr maps) method-name method-table))))


(defun bcv-check-IFEQ (inst sig-frame)
  (and (<= 1 (g 'op-stack sig-frame))
       (targetIsSafe 
        (bcv-arg inst)
        (s 'pc (bcv-arg inst)
           (sig-frame-pop-value sig-frame))
        (extract-partial-sig-vector 
         (update-maps-with-method-table 
          (g 'stackmaps
             (binding (g 'method-name sig-frame)
                      (g 'method-table sig-frame)))
          (g 'method-name sig-frame)
          (g 'method-table sig-frame))))))
         
  ;; (extract-sig-vector (g 'stackmaps sig-frame)))


(defun bcv-execute-IFEQ (inst sig-frame)
  (declare (ignore inst))
  (advance-pc (sig-frame-pop-value sig-frame)))


;; note IFEQ has two possible return state! 

(defun bcv-check-INVOKE (inst sig-frame)
  (let* ((method-name (bcv-arg inst))
         (method-table (g 'method-table sig-frame))
         (method      (binding method-name method-table))
         (nargs       (g 'nargs method)))
    (and (bound? method-name method-table) 
         (<= 0 (g 'max-stack (binding method-name method-table)))
         (integerp nargs)
         (<= 0 nargs)
         (<= nargs (g 'op-stack sig-frame))
         (<= (+ 1 (- (g 'op-stack sig-frame)
                     nargs))
             (max-stack sig-frame)))))

;;; Note: 
;;;   make sure it has enough space for arguments
;;;   make sure the return value will not overflow the stack!! 
;;;        
;;; values are always of size 1!! (in JVM it could be size two)


(defun sig-frame-pop-n (n sig-frame)
  (if (zp n) 
      sig-frame
    (sig-frame-pop-n (- n 1) 
                     (sig-frame-pop-value sig-frame))))


(defun bcv-execute-INVOKE (inst sig-frame)
  (let* ((method-name (bcv-arg inst))
         (method-table (g 'method-table sig-frame))
         (method      (binding method-name method-table))
         (nargs       (g 'nargs method))
         (ret         (g 'ret method)))
    (advance-pc 
     (sig-frame-push-value ret 
                           (sig-frame-pop-n nargs sig-frame)))))


(defun bcv-check-HALT (inst sig-frame)
    (declare (ignore inst sig-frame))
    t)

(defun bcv-execute-HALT (inst sig-frame)
    (declare (ignore inst sig-frame))
    'aftergoto)

;;;
;;; the specially handling of this make the proof 
;;; a lot complicated!! 
;;;
;;; Mon Nov  7 13:32:14 2005

(defun bcv-check-RETURN (inst sig-frame)
    (declare (ignore inst))
    (<= 1 (g 'op-stack sig-frame)))


(defun bcv-execute-RETURN (inst sig-frame)
    (declare (ignore inst sig-frame))
    'aftergoto)
    

(defun bcv-check-step-pre (inst sig-frame)
  (let* ((opcode (bcv-op-code inst)))
    (cond ((equal opcode 'INVOKE)
           (bcv-check-INVOKE inst sig-frame))
          ((equal opcode 'PUSH)
           (bcv-check-PUSH inst sig-frame))
          ((equal opcode 'IFEQ)
           (bcv-check-IFEQ inst sig-frame))
          ((equal opcode 'HALT)
           (bcv-check-HALT inst sig-frame))
          ((equal opcode 'POP)
           (bcv-check-POP inst sig-frame))
          ((equal opcode 'RETURN)
           (bcv-check-RETURN inst sig-frame))
          (t nil))))
  


(defun bcv-execute-step (inst sig-frame)
  (let* ((opcode (bcv-op-code inst)))
    (cond ((equal opcode 'INVOKE) 
           (bcv-execute-INVOKE inst sig-frame))
          ((equal opcode 'PUSH)
           (bcv-execute-PUSH inst sig-frame))
          ((equal opcode 'IFEQ)
           (bcv-execute-IFEQ inst sig-frame))
          ((equal opcode 'HALT)
           (bcv-execute-HALT inst sig-frame))
          ((equal opcode 'POP)
           (bcv-execute-POP inst sig-frame))
          ((equal opcode 'RETURN)
           (bcv-execute-RETURN inst sig-frame))
          (t nil))))

;;
;; invariant of the following function.
;; if sig-vector contains a frame at (g 'pc (sig-frame))
;; then the next instruction must be at position (pc ..)
;; 
;; if all instruction is covered, then verification succeed!
;;
;; ;;
;; ;; (defun bcv-method1 (code sig-vector sig-frame) 
;; ;;   (mylet ((pc (g 'pc sig-frame)))
;; ;;


;;
;; The actual BCV is first to merge code with signature state
;;
;; then run through the code once.
;;
;; We will need to formalize that code is in fact consecutive.
;; 

;;(i-am-here) ;; Mon Oct 31 20:07:11 2005

(defun mapOffset (map)
  (g 'pc map))

(defun instrOffset (inst)
  (g 'pc inst))

(defun makeStackMap (map method-name method-table)
  (s 'is-stack-map t 
     (s 'is-inst nil 
        (s 'method-name method-name 
           (s 'method-table method-table
              (s 'max-stack 
                 (g 'max-stack 
                    (binding method-name method-table))
                 map))))))


(defun make-inst (inst)
  (s 'is-inst t
     (s 'is-stack-map nil inst)))

(defun mergeStackMapAndCode (maps ParsedCode method-name method-table)
  (if (endp maps)
      (append ParsedCode  (list 'END_OF_CODE))
    (if (endp ParsedCode)
        nil
      (let ((mpc (mapOffset (car maps)))
            (pc  (instrOffset (car ParsedCode))))
        (if (equal mpc pc)
            (cons (makeStackMap (car maps) method-name method-table)
                  (cons (make-inst (car ParsedCode))
                        (mergeStackMapAndCode  (cdr maps)
                                               (cdr ParsedCode)
                                               method-name
                                               method-table)))
          (if (< pc mpc)
              (cons (make-inst (car ParsedCode))
                    (mergeStackMapAndCode maps (cdr ParsedCode)
                                          method-name 
                                          method-table))
            nil))))))

(defun merged-code-safe (mergedcode sig-frame)
  (if (endp mergedcode) nil
    (if (endp (cdr mergedcode))
        (and (equal (car mergedcode) 'END_OF_CODE)
             (equal sig-frame 'aftergoto))
      (if (equal sig-frame 'aftergoto)
          (and (stack-map? (car mergedcode))
               (equal (g 'pc (car mergedcode))
                      (g 'pc (cadr mergedcode))) 
               (merged-code-safe (cdr mergedcode)
                                 (car mergedcode)))
        (cond ((stack-map? (car mergedcode))
               (and (sig-frame-compatible sig-frame (car mergedcode))
                    (merged-code-safe (cdr mergedcode)
                                      (car mergedcode))))
              ((inst? (car mergedcode))
               (and (equal (g 'pc sig-frame)
                           (g 'pc (car mergedcode)))
                    (bcv-check-step-pre (car mergedcode) sig-frame)
                    (merged-code-safe
                     (cdr mergedcode)
                     (bcv-execute-step (car mergedcode) sig-frame))))
              (t nil))))))
                

(defun sig-init-locals (method) 
  ;; tmp, we only deal with number of values on the operand stack!
  (declare (ignore method))
  nil)




(defun sig-method-init-frame (method method-table)
  (s 'is-stack-map t
     (s 'is-inst nil 
        (s 'method-table method-table 
           ;; note these method in method-table does
           ;; not have sig-vector
           (s 'method-name ;; these could be merged into one 
              (g 'method-name method) ;; structure called "env"!!
              (s 'max-stack ;; we will then to prove that "env"
                 (g 'max-stack method) ;; does not change.
                 (s 'pc 0 ;; instead of proving a lot of similiar things!!  
                    (s 'op-stack 0     
                       (s 'locals 
                          (sig-init-locals method) nil)))))))))
  



;; (defun extract-sig-vector (mergedcode)
;;   (if (endp mergedcode) nil
;;     (if (stack-map? (car mergedcode))
;;         (cons (cons (g 'pc (car mergedcode))
;;                     (car mergedcode))
;;               (extract-sig-vector (cdr mergedcode)))
;;       (extract-sig-vector (cdr mergedcode)))))

;; (i-am-here) ;; Tue Nov  8 13:39:26 2005

(defun parsecode1 (pc code)
  (if (endp code) code
    (cons (make-inst (s 'pc pc
                        (s 'inst (car code) nil)))
          (parsecode1 (+ 1 pc) (cdr code)))))


(defun parsecode (code)
  (parsecode1 0 code))

(defun bcv-method (method method-table)
  (let* ((code (g 'code method))
         (maps (g 'stackmaps method)))
    (and (wff-code (parsecode code))
         (wff-maps maps)
         (merged-code-safe
           (mergeStackMapAndCode
            maps (parsecode code) (g 'method-name method) method-table)
           (sig-method-init-frame method
                                  method-table)))))
           
          

;----------------------------------------------------------------------


(defun extract-sig-locals (frame)
  (declare (ignore frame)) 
  nil)


(defun extract-sig-frame (frame method-table)
  (s 'method-table method-table
     (s 'max-stack 
        (g 'max-stack frame)
        (s 'method-name 
           (g 'method-name frame)
           (s 'pc (g 'pc frame)
              (s 'op-stack (len (g 'op-stack frame))
                 (s 'locals
                    (extract-sig-locals frame) nil)))))))


;----------------------------------------------------------------------

(defun bcv-verified-method-table1 (method-table1 method-table)
  (if (endp method-table1) t
    (and (bcv-method (cdr (car method-table1)) method-table)
         (bcv-verified-method-table1 (cdr method-table1) method-table))))


(defun bcv-verified-method-table (method-table)
  (bcv-verified-method-table1 method-table method-table))


;----------------------------------------------------------------------
;; (defun merged-code-safe (mergedcode sig-frame)
;;   (if (endp mergedcode) nil
;;     (if (endp (cdr mergedcode))
;;         (and (equal (car mergedcode) 'END_OF_CODE)
;;              (equal sig-frame 'aftergoto))
;;       (if (equal sig-frame 'aftergoto)
;;           (and (stack-map? (car mergedcode))
;;                (equal (g 'pc (car mergedcode))
;;                       (+ 1 (g 'pc  (cadr mergedcode)))) ;; bug!! 
;;                (merged-code-safe (cdr mergedcode)
;;                                  (car mergedcode)))
;;         ;; error detected when we attend to reason about 
;;         ;; HALT ..
;;         (cond ((stack-map? (car mergedcode))
;;                (and (sig-frame-compatible sig-frame (car mergedcode))
;;                     (equal (g 'pc sig-frame)
;;                            (g 'pc (cdr mergedcode)))  ;; bug!! 
;;                     (merged-code-safe (cdr mergedcode)
;;                                       (car mergedcode))))
;;               ((inst? (car mergedcode))
;;                (and (equal (g 'pc sig-frame)
;;                            (g 'pc (car mergedcode)))
;;                     (bcv-check-step-pre (car mergedcode) sig-frame)
;;                     (merged-code-safe
;;                      (cdr mergedcode)
;;                      (bcv-execute-step (car mergedcode) sig-frame))))
;;               (t nil))))))
;; wrong one!! 
;;                 


;; (defun collect-witness-merged-code-safe (mergedcode sig-frame)
;;   (if (endp mergedcode) nil
;;     (if (endp (cdr mergedcode)) nil
;;       (if (equal sig-frame 'aftergoto)
;;           (and (stack-map? (car mergedcode))
;;                (equal (g 'pc (car mergedcode))   
;;                       (+ 1 (g 'pc sig-frame)))   ;; bug  !!!
;;                (collect-witness-merged-code-safe 
;;                 (cdr mergedcode) (car mergedcode)))
;;         (cond ((stack-map? (car mergedcode))
;;                (and (sig-frame-compatible sig-frame (car mergedcode))
;;                     (not (endp (cdr mergedcode)))
;;                     (equal (g 'pc (cdr mergedcode)) ;; bug!!! 
;;                            (g 'pc sig-frame))
;;                     (collect-witness-merged-code-safe 
;;                      (cdr mergedcode) (car mergedcode))))
;;               ((inst? (car mergedcode))
;;                (and (equal (g 'pc sig-frame)
;;                            (g 'pc (car mergedcode)))
;;                     (bcv-check-step-pre (car mergedcode) sig-frame)
;;                     (cons (cons (g 'pc sig-frame)
;;                                 sig-frame)
;;                           (collect-witness-merged-code-safe 
;;                            (cdr mergedcode)
;;                            (bcv-execute-step (car mergedcode)
;;                                              sig-frame)))))
;;               (t nil))))))
;;
;;

;; (defun merged-code-safe (mergedcode sig-frame)
;;   (if (endp mergedcode) nil
;;     (if (endp (cdr mergedcode))
;;         (and (equal (car mergedcode) 'END_OF_CODE)
;;              (equal sig-frame 'aftergoto))
;;       (if (equal sig-frame 'aftergoto)
;;           (and (stack-map? (car mergedcode))
;;                (equal (g 'pc (car mergedcode))
;;                       (g 'pc (cadr mergedcode))) 
;;                (merged-code-safe (cdr mergedcode)
;;                                  (car mergedcode)))
;;         (cond ((stack-map? (car mergedcode))
;;                (and (sig-frame-compatible sig-frame (car mergedcode))
;;                     (merged-code-safe (cdr mergedcode)
;;                                       (car mergedcode))))
;;               ((inst? (car mergedcode))
;;                (and (equal (g 'pc sig-frame)
;;                            (g 'pc (car mergedcode)))
;;                     (bcv-check-step-pre (car mergedcode) sig-frame)
;;                     (merged-code-safe
;;                      (cdr mergedcode)
;;                      (bcv-execute-step (car mergedcode) sig-frame))))
;;               (t nil))))))


(defun collect-witness-merged-code-safe (mergedcode sig-frame)
  (if (endp mergedcode) nil
    (if (endp (cdr mergedcode)) nil
      (if (equal sig-frame 'aftergoto)
          (and  (stack-map? (car mergedcode))
                (equal (g 'pc (car mergedcode))   
                       (g 'pc (cadr mergedcode)))
                (collect-witness-merged-code-safe 
                 (cdr mergedcode) (car mergedcode)))
        (cond ((stack-map? (car mergedcode))
               (and (sig-frame-compatible sig-frame (car mergedcode))
                    (merged-code-safe (cdr mergedcode)
                                      (car mergedcode))
                    (collect-witness-merged-code-safe 
                     (cdr mergedcode) (car mergedcode))))
              ((inst? (car mergedcode))
               (and (equal (g 'pc sig-frame)
                           (g 'pc (car mergedcode)))
                    (bcv-check-step-pre (car mergedcode) sig-frame)
                    (merged-code-safe
                     (cdr mergedcode)
                     (bcv-execute-step (car mergedcode) sig-frame))
                    (cons (cons (g 'pc sig-frame)
                                sig-frame)
                          (collect-witness-merged-code-safe 
                           (cdr mergedcode)
                           (bcv-execute-step (car mergedcode)
                                             sig-frame)))))
              (t nil))))))


(defun collect-witness-bcv-method (method method-table)
  (collect-witness-merged-code-safe
   (mergeStackMapAndCode 
    (g 'stackmaps method)
    (parsecode (g 'code method))
    (g 'method-name method)
    method-table)
   (SIG-METHOD-INIT-FRAME METHOD METHOD-TABLE)))


;----------------------------------------------------------------------


(defun extract-maps (merged-code) 
  (if (endp merged-code) nil
    (if (endp (cdr merged-code)) nil
      (if (stack-map? (car merged-code))
          (cons (car merged-code)
                (extract-maps (cdr merged-code)))
        (extract-maps (cdr merged-code))))))


(defun extract-code (merged-code)
  (if (endp merged-code) nil
    (if (endp (cdr merged-code)) nil
      (if (inst? (car merged-code))
          (cons (car merged-code)
                (extract-code (cdr merged-code)))
        (extract-code (cdr merged-code))))))


;----------------------------------------------------------------------


(defun partial-sig-vector-compatible1 (partial1 partial full)
   (if (endp partial1) t
     (and (sig-frame-compatible (binding (caar partial1)
                                         partial)
                                (binding (caar partial1) full))
          (partial-sig-vector-compatible1 (cdr partial1) partial full))))


(defun partial-sig-vector-compatible (partial full)
  (partial-sig-vector-compatible1 partial partial full))

;----------------------------------------------------------------------

(defun wff-maps-consistent (maps init-frame)
  (if (endp maps) t
    (and (equal (g 'method-name (car maps))
                (g 'method-name init-frame))
         (equal (g 'method-table (car maps))
                (g 'method-table init-frame))
         (wff-maps-consistent (cdr maps) init-frame))))

;----------------------------------------------------------------------


(defun collect-pc-merged-code (merged-code)
   (if (endp merged-code) nil
     (if (endp (cdr merged-code))
         nil
       (cons (g 'pc (car merged-code))
             (collect-pc-merged-code (cdr merged-code))))))


(defun ordered (pc-list)
  (if (endp pc-list) 
      t
    (if (endp (cdr pc-list)) 
        t
      (and (<= (car pc-list) 
               (cadr pc-list))
           (ordered (cdr pc-list))))))

;----------------------------------------------------------------------

(defun collect-keys-from-witness (sig-vector)
  (if (endp sig-vector) nil
    (cons (car (car sig-vector))
          (collect-keys-from-witness (cdr sig-vector)))))

