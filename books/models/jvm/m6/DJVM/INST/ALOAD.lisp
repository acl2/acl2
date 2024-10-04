(in-package "DJVM")

(include-book "base")
(include-book "base-consistent-state")
(include-book "base-locals")
(include-book "base-extra")
;;
;; Fri Aug  5 22:49:40 2005. ALOAD is a bit special
;; from ASTORE. in maintain consistent-state-strong! 
;;

;----------------------------------------------------------------------
;
;  ALOAD
;
;----------------------------------------------------------------------

(acl2::set-verify-guards-eagerness 2)

;----------------------------------------------------------------------

(defun wff-aload (inst)
  (and  (wff-one-arg inst)
        (integerp (arg inst))
        (<= 0 (arg inst))
        (< (arg inst) *local-index-limit*)))

;----------------------------------------------------------------------


(defun ALOAD-guard (inst s)
  (mylet* ((cframe (current-frame s))
           (locals (locals cframe))
           (opstack (operand-stack cframe))
           (index  (arg inst))
           (value  (local-at index s)))
          (and (wff-aload inst)
               (consistent-state-strong s)
               (< index (len locals))
               (valid-local-index index locals)
               (REFp value (heap s))
               ; (<= (len locals) (max-local s)) 
               ; this is easy to enforce by a simple pass checking. 
               ; ??? Thu Mar 10 15:32:22 2005
               (and (not (mem '*abstract* (method-accessflags (current-method s))))
                    ;; Mon Oct 18 09:33:08 2004. This above is implied by consistent-state 
                    (not (mem '*native* (method-accessflags (current-method s))))
                    ;; this is not 
                    (<= (+ (len opstack) 1)
                        (max-stack s))))))
       
;----------------------------------------------------------------------

(defun execute-ALOAD (inst s)
  (declare (xargs :guard (ALOAD-guard inst s)))
  (mylet* ((cframe (current-frame s))
           (locals (locals cframe))
           (index  (arg inst))
           (value  (local-at index s)))
          (ADVANCE-PC (safe-pushStack value s))))

;----------------------------------------------------------------------

(defun check-ALOAD (inst s)
  (declare (xargs :guard (consistent-state s)))
  (mylet* ((cframe (current-frame s))
           (locals (locals cframe))
           (opstack (operand-stack cframe))
           (index  (arg inst))
           (value  (local-at index s)))
          (and (wff-aload inst)
               (not (mem '*native* (method-accessflags (current-method s))))
               (< index (len locals)) 
               (valid-local-index index locals)
               (REFp value (heap s))
               (< index (max-local s))
               (<= (+ (len opstack) 1)
                   (max-stack s)))))

;----------------------------------------------------------------------
;; (i-am-here)

(defthm check-ALOAD-implies-guard-succeeds
  (implies (and (consistent-state-strong s)
               (check-ALOAD inst s))
          (ALOAD-guard inst s)))


;;; FIXED 
;;; Tue Aug 10 14:24:02 2004
;;; This is wrong!! 
;;; because of the uninitialized variable!!
;;; the wrong version of valid-index only asserts that 
;;; the index is on the right boundary!! We probably need assertions that it is
;;; of right type. 
;;;
;;; Since the consistent-locals's definition is also wrong. 
;;; The current definition will assert that locals with holes in it are not
;;; consistent!! 
;;;  
;;; 

;;; Wed May 18 12:49:12 2005

;----------------------------------------------------------------------


(defthm ALOAD-guard-implies-execute-ALOAD-perserve-consistency
  (implies (ALOAD-guard inst s)
           (consistent-state-strong (execute-ALOAD inst s)))
  :hints (("Goal" :in-theory (e/d () 
                                  (local-at arg locals REFp
                                   pushStack consistent-value-x)))))

;; Tue Mar 30 15:51:15 2004. I still have not dealt with
;; inst-size!!  nor raise-exception!!
;;
;; Thu Mar 10 15:50:54 2005. I am still dealing with these
;; instructions!! Still not inst-size and raise-exception!! 
;; Wed May 18 12:51:04 2005

;----------------------------------------------------------------------


;-- BCV::check-ALOAD implies DJVM::check-ALOAD on a corresponding state -----

;(i-am-here) ;; Fri May 20 23:56:43 2005


(encapsulate ()
  (local (include-book "base-bcv"))
  (local (include-book "base-bcv-locals"))
  (defthm bcv-check-ALOAD-ensures-djvm-check-ALOAD
    (implies (and (bcv::check-ALOAD inst (env-sig s) 
                                     (frame-sig  (current-frame s)
                                                 (instance-class-table s)
                                                 (heap s)
                                                 (heap-init-map (aux s))))
                  
                  (wff-aload inst) 
                  ;; implied by valid-local-index and in 
                  (not (mem '*native* (method-accessflags (current-method s))))
                  (consistent-state s))
             (djvm::check-ALOAD inst s))))



;-- BCV::check-ALOAD monotonic   -------------------------------------


; Matt K. mod: Avoid raw Lisp error in tau; see similar disable in
; BCV/bcv-isAssignable-transitive.lisp.
(local (in-theory (disable (:e tau-system))))

(encapsulate ()
    (local (include-book "base-bcv-check-monotonic"))
    (defthm sig-check-ALOAD-on-more-general-implies-more-specific
      (implies (and (bcv::good-icl icl)
                    (bcv::good-scl (bcv::classtableEnvironment env1))
                    (bcv::consistent-sig-locals (bcv::frameLocals gframe) icl)
                    (bcv::consistent-sig-locals (bcv::frameLocals sframe) icl)
                    (bcv::sig-frame-more-general gframe sframe env1)
                    (bcv::check-ALOAD inst env1 gframe)
                    (bcv::icl-scl-compatible icl (bcv::classtableEnvironment env1)))
               (bcv::check-ALOAD inst env1 sframe))))


;;;
;;; showing the next step is monotonic is more difficult!! 

;-- BCV::execute-ALOAD next step  monotonic ---------------------------

(encapsulate () 
     (local (include-book "base-bcv-step-monotonic"))
     (defthm ALOAD-monotonicity
       (implies (and (bcv::sig-frame-more-general gframe sframe env1)
                     (bcv::consistent-sig-locals (bcv::frameLocals gframe) icl)
                     (bcv::consistent-sig-locals (bcv::frameLocals sframe) icl)
                     (bcv::check-ALOAD inst env1 gframe) 
                     (bcv::check-ALOAD inst env1 sframe) 
                     (bcv::good-icl icl)
                     (bcv::good-scl (bcv::classtableEnvironment env1))
                     (bcv::icl-scl-compatible icl (bcv::classtableEnvironment env1)))
                (bcv::sig-frame-more-general 
                 (bcv::normal-frame (bcv::execute-ALOAD inst env gframe))
                 (bcv::normal-frame (bcv::execute-ALOAD inst env sframe)) env1))))


;----------------------------------------------------------------------



;-- DJVM::execute-ALOAD expansion -------------------------------------


;; (i-am-here) ;; Mon May 23 01:10:15 2005

(encapsulate ()
    (local (include-book "base-frame-sig-expansion"))   
    (defthm execute-ALOAD-frame-sig-is
      (mylet* ((ns (execute-ALOAD inst s)))
       (implies 
        (and (consistent-state s)
             (check-ALOAD inst s))
        (equal (frame-sig (current-frame ns)
                          (instance-class-table ns)
                          (heap ns)
                          (heap-init-map (aux ns)))
               (frame-push-value-sig (value-sig (nth (arg inst) 
                                                     (locals (current-frame s)))
                                                (instance-class-table s)
                                                (heap s)
                                                (heap-init-map (aux s))
                                                (method-ptr (current-frame s)))
                                     (frame-sig (current-frame s)
                                                (instance-class-table s)
                                                (heap s)
                                                (heap-init-map (aux s)))))))))
                                                  


;-- BCV::execute-ALOAD expansion --------------------------------------


(encapsulate ()
  (local (include-book "base-bcv-frame-sig-expansion"))
  (defthm bcv-execute-ALOAD-is
    (implies (and (consistent-state s)
                  (check-ALOAD inst s)
                  (bcv::check-ALOAD inst (env-sig s) 
                                    (frame-sig (current-frame s)
                                               (instance-class-table s)
                                               (heap s)
                                               (heap-init-map (aux s)))))
             (equal (mv-nth 0 (bcv::execute-ALOAD
                               inst (env-sig s) 
                               (frame-sig (current-frame s)
                                          (instance-class-table s)
                                          (heap s)
                                          (heap-init-map (aux s)))))
                    (frame-push-value-sig  (value-sig (nth (arg inst) 
                                                           (locals (current-frame s)))
                                                      (instance-class-table s)
                                                      (heap s)
                                                      (heap-init-map (aux s))
                                                      (method-ptr (current-frame s)))
                                           (frame-sig (current-frame s)
                                                      (instance-class-table s)
                                                      (heap s)
                                                      (heap-init-map (aux
                                                                      s))))))))

;--  bcv next-state is more general than djvm next-state ---------------



(encapsulate ()
  (local (include-book "base-next-state-more-specific"))
  (defthm next-state-no-more-general-aload
    (mylet* ((oframe (frame-sig (current-frame s)
                                (instance-class-table s)
                                (heap s)
                                (heap-init-map (aux s))))
             (ns   (execute-ALOAD inst s))
             (nframe (frame-sig (current-frame ns)
                                (instance-class-table ns)
                                (heap ns)
                                (heap-init-map (aux ns)))))
            (implies (and (consistent-state s)
                          (bcv::check-ALOAD inst (env-sig s) oframe)
                          (check-ALOAD inst s))
                     (bcv::sig-frame-more-general 
                      (mv-nth 0 (bcv::execute-ALOAD
                                 inst 
                                 (env-sig s)
                                 oframe))
                      nframe
                      (env-sig s))))
    :hints (("Goal" :in-theory (disable execute-ALOAD bcv::execute-ALOAD)))))


  
;----------------------------------------------------------------------

;; (i-am-here) ;; Tue Aug  2 13:54:38 2005


(include-book "../../M6/m6-bytecode")
(include-book "../../DJVM/consistent-state-to-untag-state")

;; (encapsulate ()
;;    (local (include-book "base-untag-state"))
;;    (defthm equal-ALOAD-when-guard-succeeds
;;      (implies (ALOAD-guard inst s)
;;               (equal (untag-state (djvm::execute-ALOAD inst s))
;;                      (m6::execute-ALOAD inst (untag-state s))))))

;; ;;
;; ;; this is not good enough for our purpose!! Sun Jul 31 18:59:52 2005
;; ;;
;; ;; need to be fixed!! 

(local (include-book "base-state-equiv"))

(encapsulate ()
    (local (include-book "base-state-equiv"))
    (defthm equal-ALOAD-when-guard-succeeds
      (implies (and (ALOAD-guard inst djvm::djvm-s)
                    (state-equiv m6::m6-s djvm::djvm-s))
               (state-equiv (m6::execute-ALOAD inst m6::m6-s)
                            (djvm::execute-ALOAD inst djvm::djvm-s)))))

;;;
;;; Tue Aug  2 16:10:21 2005
;;;
;----------------------------------------------------------------------

;----------------------------------------------------------------------
;
; Mon Aug 15 21:30:22 2005
;

;; (i-am-here) ;; Mon Aug 15 21:31:00 2005

(encapsulate () 
  (local (include-book "base-method-ptr-no-change"))
  (defthm execute-ALOAD-change-no-method-ptr
    (equal (method-ptr (current-frame (djvm::execute-ALOAD inst s)))
           (method-ptr (current-frame s)))))

;;; next need to prove loaded class method-does-not-change! 


(encapsulate () 
  (local (include-book "base-method-no-change"))
  (defthm deref-method-no-change-if-already-loaded-ALOAD
    (implies (consistent-state s)
             (equal (deref-method (method-ptr (current-frame s))
                                  (instance-class-table 
                                   (djvm::execute-ALOAD inst s)))
                    (deref-method (method-ptr (current-frame s))
                                  (instance-class-table s))))))


;----------------------------------------------------------------------



(in-theory (disable check-ALOAD ALOAD-guard execute-ALOAD wff-ALOAD))
