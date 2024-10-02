(in-package "ACL2")
(include-book "jvm-model")
(include-book "bcv-model")
;; (defmacro extract-sig-frame (frame method-table)
;;   `(s 'method-table ,method-table
;;      (s 'max-stack 
;;         (g 'max-stack ,frame)
;;         (s 'method-name 
;;            (g 'method-name ,frame)
;;            (s 'pc (g 'pc ,frame)
;;               (s 'op-stack (len (g 'op-stack ,frame))
;;                  (s 'locals
;;                     (extract-sig-locals ,frame) nil)))))))



(defun consistent-caller-frame (caller-frame callee-frame method-table)
  (let*  ((caller-name (g 'method-name caller-frame))
          (callee-name (g 'method-name callee-frame))
          (caller (binding caller-name method-table))
          (callee (binding callee-name method-table))
          (sig-frame (extract-sig-frame caller-frame
                                        method-table))
          (pc (g 'pc sig-frame))
          (record-frame-sig (binding pc (collect-witness-bcv-method caller method-table))))
    (and (bcv-method caller method-table)
         (<= (+ 1 (len (g 'op-stack caller-frame)))
             (g 'max-stack caller-frame))
         (equal (g 'method-name caller)
                caller-name)
         (integerp (g 'pc caller-frame))
         (<= 1 (g 'pc caller-frame))
         (< (g 'pc caller-frame) (len (g 'code caller)))
         ;; (equal (arg (nth (- pc 1) (g 'code caller)))
         ;;       callee-name)
         ;; do I need the above assertion? as long as return value size 
         ;; is the same for all method, we don't. 
         ;; However, this invariant should be easy to maintain. 
         ;; does not add more complexity (proof-wise) to have it. 
         (sig-frame-compatible
          (sig-frame-push-value (g 'ret callee) sig-frame)
          record-frame-sig))))



;; need to deal with top call frame and other call frames below it a bit
;; differently

;; because the caller's pc is pointing to the next instruction, however
;; caller's operand stack does not reflect that!! The hope is that when callee
;; returns it will return the correct number of arguments and the execution can
;; resume from a state. execution from such a state is within the "coverage" of
;; the BCV!!


;; (defun pc-in-range (frame method-table)
;;  (let* ((method-name (g 'method-name frame))
;;         (method (binding method-name method-table))
;;         (pc (g 'pc frame))
;;         (code (g 'code method)))
;;    (and (integerp pc)
;;         (<= 0 pc)
;;         (< pc (len code)))))

(defun consistent-frame (frame method-table)
  (let* ((method-name (g 'method-name frame))
         (method (binding method-name method-table)))
    (and ;; Sun Oct  2 04:29:07 2005
         ;; (pc-in-range frame method-table)
         ;; When PC is out of range, we know the next instruction will be
         ;; undefined. It will be treated as a halt.
         ;;
         ;; so consistent-state will be preserved. 
         ;; and our main goal can still be established under this weaker
         ;; consistent-state predicate. 
         ;; (integerp (g 'pc frame))
         ;; (equal (g 'method-name method)
         ;;         method-name)                 !!! Thu Nov  3 22:31:32 2005
         (bound? method-name method-table)
         (<= (len (g 'op-stack frame))
             (g 'max-stack frame))
         (equal (g 'max-stack frame)
                (g 'max-stack method)))))

;; only assert this! 

(defun consistent-callee-frame (frame method-table)
  (let* ((method-name (g 'method-name frame))
         (method (binding method-name method-table)))
    (and (bcv-method method method-table)
         (equal (g 'method-name method)
                method-name)
         (sig-frame-compatible
          (extract-sig-frame frame method-table)
          (binding (g 'pc frame) 
                   (collect-witness-bcv-method method method-table))))))



(defun consistent-call-stack1 (call-stack topframe method-table)
  (if (endp call-stack) t
    (and (consistent-frame (topx call-stack) method-table)
         (consistent-caller-frame (topx call-stack)
                                  topframe method-table)
         (consistent-call-stack1 
          (popx call-stack) (topx call-stack) method-table))))

;; (i-am-here) 

(defun consistent-call-stack (call-stack method-table)
  (and (consp call-stack)
       (consistent-frame (topx call-stack) method-table)
       (consistent-callee-frame (topx call-stack) method-table)
       (consistent-call-stack1 (popx call-stack) (topx call-stack) method-table)))
                               


(defun all-method-verified1 (method-table1 method-table)
  (if (endp method-table1) t
      (and (bcv-method (cdr (car method-table1))  method-table)
           (all-method-verified1 (cdr method-table1) method-table))))


(defun all-method-verified (method-table)
  (all-method-verified1 method-table method-table))

;;
;; note: this all-method-verified1 is using bcv-simple-method!!  we will have a
;; more "procedural" style bcv-simple-method and bcv-verified-method-table!!
;;


;;(i-am-here) ;; Sun Nov 20 17:19:14 2005


(defun wff-method (method)
  (declare (ignore method))
  t)

(defun wff-method-table (method-table)
  (if (endp method-table) t
    (and (equal (g 'method-name (cdar method-table))
                (caar method-table))
         (wff-method (cdr method-table))
         (wff-method-table (cdr method-table)))))


(defun consistent-state (st)
  (let*  ((method-table (g 'method-table st))
          (call-stack   (g 'call-stack st)))
    (and (pc-in-range st)
         (wff-method-table (g 'method-table st))
         (consistent-call-stack call-stack method-table)
         (all-method-verified method-table))))

;----------------------------------------------------------------------


;----------------------------------------------------------------------


