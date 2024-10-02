(in-package "ACL2")

(include-book "bcv-model")

;; (defun max-stack (sig-frame)
;;   (g 'max-stack sig-frame))

(defun bcv-simple-check-PUSH (inst sig-frame)
  (declare (ignore inst))
  (<= (+ 1 (g 'op-stack sig-frame))
      (max-stack sig-frame)))

;; (defun advance-pc (sig-frame)
;;   (s 'pc 
;;      (+ 1 (g 'pc sig-frame))
;;      sig-frame))


;; (defun sig-frame-push-value (v sig-frame)
;;   (declare (ignore v))
;;   (s 'op-stack
;;      (+ 1 (g 'op-stack sig-frame))
;;      sig-frame))


(defun bcv-simple-execute-PUSH (inst sig-frame)
  (list 
   (advance-pc 
    (sig-frame-push-value (arg inst)
                          sig-frame))))


(defun bcv-simple-check-POP (inst sig-frame)
  (declare (ignore inst))
  (<= 1 (g 'op-stack sig-frame)))


;; (defun sig-frame-pop-value (sig-frame)
;;   (if (zp (g 'op-stack sig-frame))
;;          sig-frame
;;     (s 'op-stack 
;;        (-  (g 'op-stack sig-frame) 1)
;;        sig-frame)))


(defun bcv-simple-execute-POP (inst sig-frame)
  (declare (ignore inst))
  (list (advance-pc 
         (sig-frame-pop-value sig-frame))))

;;; The only important thing we care (in this example) is the size of the
;;; operand stack.
;;;
;;; Our BCV examine a program, method by method.
;;;
;;; We will show that verified program will never violate the operand stack
;;; size limit.


(defun bcv-simple-check-IFEQ (inst sig-frame)
  (declare (ignore inst))
  (<= 1 (g 'op-stack sig-frame)))


(defun bcv-simple-execute-IFEQ (inst sig-frame)
  (list 
   (advance-pc (sig-frame-pop-value sig-frame))
   (s 'pc (arg inst)
      (sig-frame-pop-value sig-frame))))

;; note IFEQ has two possible return state! 




;; (defun bcv-simple-check-INVOKE (inst sig-frame)
;;   (let* ((method-name (arg inst))
;;          (method-table (g 'method-table sig-frame))
;;          (method      (binding method-name method-table))
;;          (nargs       (g 'nargs method)))
;;     (and (bound? method-name method-table)
;;          (<= 0 (g 'max-stack (binding method-name method-table)))

;;          (equal (g 'method-table 
;;                    (cdr (assoc-equal 0 (g 'sig-vector (binding method-name
;;                                                                method-table)))))
;;                 method-table)
;; ;;; 
;; ;;; note: this is WRONG!!! 
;; ;;; because nothing will satisfy it!!! 
;; ;;; Fri Nov 11 11:49:29 2005
;; ;;; 
;;          (equal (g 'op-stack
;;                    (cdr (assoc-equal 0 (g 'sig-vector (binding method-name
;;                                                                method-table)))))
;;                 0)
;;          (equal (g 'method-name (binding method-name
;;                                          method-table))
;;                 method-name)
;;          ;; we need these above three to assert that next state 
;;          ;; is compatible with 
;;          (integerp nargs)
;;          (<= 0 nargs)
;;          (<= nargs (g 'op-stack sig-frame))
;;          (<= (+ 1 (- (g 'op-stack sig-frame)
;;                      nargs))
;;              (max-stack sig-frame)))))


(defun bcv-simple-check-INVOKE (inst sig-frame)
  (let* ((method-name  (arg inst))                                            ;; ctx maps 
         (method-table (g 'method-table  sig-frame))                ;; the value into the frames of sig-vector
         (method       (binding method-name method-table))
         (nargs        (g 'nargs method)))
    (and (bound? method-name method-table)
         (<= 0 (g 'max-stack (binding method-name method-table)))
;;          (equal (g 'method-table 
;;                    (cdr (assoc-equal 0 (g 'sig-vector (binding method-name
;;                                                                method-table)))))
;;                 method-table) ;; add one level redirect! Fri Nov 11 12:03:50 2005
;;          (equal (g 'op-stack
;;                    (cdr (assoc-equal 0 (g 'sig-vector (binding method-name
;;                                                                method-table)))))
;;                 0)
;;          (equal (g 'method-name (binding method-name
;;                                          method-table))
;;                 method-name)
         ;; we need these above three to assert that next state 
         ;; is compatible with 
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


(defun bcv-simple-check-HALT (inst sig-frame)
    (declare (ignore inst sig-frame))
    t)

(defun bcv-simple-execute-HALT (inst sig-frame)
    (declare (ignore inst sig-frame))
    nil)


(defun bcv-simple-check-RETURN (inst sig-frame)
    (declare (ignore inst))
    (<= 1 (g 'op-stack sig-frame)))


(defun bcv-simple-execute-RETURN (inst sig-frame)
    (declare (ignore inst sig-frame))
    nil)
    

(defun bcv-simple-check-step-pre (inst sig-frame)
  (let* ((opcode (op-code inst)))
    (cond ((equal opcode 'INVOKE)
           (bcv-simple-check-INVOKE inst sig-frame))
          ((equal opcode 'PUSH)
           (bcv-simple-check-PUSH inst sig-frame))
          ((equal opcode 'IFEQ)
           (bcv-simple-check-IFEQ inst sig-frame))
          ((equal opcode 'HALT)
           (bcv-simple-check-HALT inst sig-frame))
          ((equal opcode 'POP)
           (bcv-simple-check-POP inst sig-frame))
          ((equal opcode 'RETURN)
           (bcv-simple-check-RETURN inst sig-frame))
          (t nil))))

;; (defun sig-frame-pop-n (n sig-frame)
;;   (if (zp n) 
;;       sig-frame
;;     (sig-frame-pop-n (- n 1) 
;;                      (sig-frame-pop-value sig-frame))))


(defun bcv-simple-execute-INVOKE (inst sig-frame)
  (let* ((method-name (arg inst))
         (method-table (g 'method-table sig-frame))
         (method      (binding method-name method-table))
         (nargs       (g 'nargs method))
         (ret         (g 'ret method)))
    (list 
     (advance-pc 
      (sig-frame-push-value ret 
                            (sig-frame-pop-n nargs sig-frame))))))
  


(defun bcv-simple-execute-step (inst sig-frame)
  (let* ((opcode (op-code inst)))
    (cond ((equal opcode 'INVOKE) 
           (bcv-simple-execute-INVOKE inst sig-frame))
          ((equal opcode 'PUSH)
           (bcv-simple-execute-PUSH inst sig-frame))
          ((equal opcode 'IFEQ)
           (bcv-simple-execute-IFEQ inst sig-frame))
          ((equal opcode 'HALT)
           (bcv-simple-execute-HALT inst sig-frame))
          ((equal opcode 'POP)
           (bcv-simple-execute-POP inst sig-frame))
          ((equal opcode 'RETURN)
           (bcv-simple-execute-RETURN inst sig-frame))
          (t nil))))


;; (defun sig-local-compatible (slocals glocals)
;;   (declare (ignore slocals glocals))
;;   ;; temp implementation
;;   t)

;; (defun sig-opstack-compatible (sframe gframe)
;;   (equal (g 'op-stack sframe)
;;          (g 'op-stack gframe)))


;; (defun sig-frame-compatible (sframe gframe)
;;   (and (equal (g 'pc sframe)
;;               (g 'pc gframe))
;;        (equal (g 'max-stack sframe)
;;               (g 'max-stack gframe))
;;        (equal (g 'method-table sframe)
;;               (g 'method-table gframe))
;;        (sig-opstack-compatible sframe gframe)
;;        (sig-local-compatible (g 'locals sframe)
;;                              (g 'locals gframe))))



(defun all-next-state-safe (sig-frames post-vector)
  (if (endp sig-frames) t
    (let* ((sig-frame (car sig-frames))
           (rest (cdr sig-frames))
           (pc   (g 'pc sig-frame))
           (post (binding pc post-vector)))
      (and (sig-frame-compatible 
             sig-frame 
             post)
           (all-next-state-safe rest post-vector)))))
             
      

(defun bcv-simple-inst (pc inst sig-vector)
  (let* ((pre-vector sig-vector)
         (post-vector sig-vector)
         (pre   (binding pc pre-vector)))
    (and (bcv-simple-check-step-pre inst pre)
         (all-next-state-safe 
          (bcv-simple-execute-step inst pre) 
          post-vector))))
          


(defun bcv-simple-method1 (pc code sig-vector)
  (declare (xargs :measure (len code)))
  (if (endp code) t
    (let* ((inst (car code)))
      (and (bcv-simple-inst pc inst sig-vector)
           (bcv-simple-method1 (+ 1 pc) (cdr code) sig-vector)))))
     

(defun sig-init-locals (method) 
  ;; tmp, we only deal with number of values on the operand stack!
  (declare (ignore method))
  nil)

;; (defun sig-method-init-frame (method)
;;   (s 'max-stack 
;;      (g 'max-stack method)
;;      (s 'pc 0 
;;         (s 'op-stack 0 
;;            (s 'locals 
;;               (sig-init-locals method) nil)))))
  

;;; even for such an simple model, we may need to show that execution does not
;;; fell off the end of the code.
;;;
;;;   which is not easy! especially, when we our BCV is expressed this way!!
;;; 
;;; Sat Oct 8 21:29:41 2005. this is simplified problem, we designed our m-run
;;; to "halt" when the execution fell off the end of code (next instruction is
;;; not well defined), in a real JVM, we need to show execution never "fall"
;;; off the end of the code


(defun bcv-simple-method (method method-table)
  (and (sig-frame-compatible 
        (sig-method-init-frame method method-table)
        (binding 0 (g 'sig-vector method)))
       (bcv-simple-method1 0 
                    (g 'code method) 
                    (g 'sig-vector method))))


;----------------------------------------------------------------------


