(in-package "DJVM")

(include-book "base")
(include-book "base-consistent-state")
(include-book "base-extra")


;-----------------------------------------------------------------
;
;  ACONST_NULL
;
; 

;-- Define guard first -------------------------------------------



(acl2::set-verify-guards-eagerness 2)

(defun wff-ACONST_NULL (inst)
  (wff-inst inst))

(defun ACONST_NULL-guard (inst s)
  (and (consistent-state-strong s)
       (wff-inst inst)
       (not (mem '*abstract* (method-accessflags (current-method s))))
       (not (mem '*native* (method-accessflags (current-method s))))
       (<= (+ (len (operand-stack (current-frame s))) 1)
           (max-stack s))))

;-- Definition of ACONST_NULL -------------------------------------


(defun execute-ACONST_NULL (inst s)
  (declare (xargs :guard (ACONST_NULL-guard inst s)))
  (ADVANCE-PC (safe-pushStack '(REF . -1) s)))


;-- Runtime checking of the ACONST_NULL ----------------------

; Note the difference between *-guard and check-* 
; 
; Tue Apr 19 10:10:29 2005


(defun check-ACONST_NULL (inst s)
  (declare (xargs :guard (consistent-state s)))
  (and (wff-inst inst)
       (not (mem '*abstract* (method-accessflags (current-method s))))
       (not (mem '*native* (method-accessflags (current-method s))))
       ;; we could add the check for max stack!!
       (<= (+ (len (operand-stack (current-frame s))) 1)
           (max-stack s))))


;----------------------------------------------------------------------
;----------------------------------------------------------------------


;;; Strive to make sure that the proof of these theorems depend only on lemma
;;; in base-* !!
;;; 

;-- ACONST_NULL-guard implies state consistency perserved -----------------

;; (i-am-here) ;; Sun Aug  7 22:21:15 2005


(defthm ACONST_NULL-guard-implies-execute-ACONST_NULL-perserve-consistency
  (implies (ACONST_NULL-guard inst s)
           (consistent-state-strong (execute-ACONST_NULL inst s))))


;-- check-ACONST_NULL implies ACONST_NULL-guard in a consistent state ----------

(defthm check-ACONST_NULL-implies-guard-succeeds
  (implies (and (consistent-state-strong s)
                (check-ACONST_NULL inst s))
          (ACONST_NULL-guard inst s)))


;-- BCV::check-ACONST_NULL implies DJVM::check-ACONST_NULL on a corresponding state -----

(encapsulate ()
 (local (include-book "base-bcv"))
 (defthm bcv-check-ACONST_NULL-ensures-djvm-check-ACONST_NULL
   (implies (and (bcv::check-ACONST_NULL inst (env-sig s) 
                                         (frame-sig  (current-frame s)
                                                     (instance-class-table s)
                                                     (heap s)
                                                     (heap-init-map (aux s))))
                 (wff-inst inst)
                 (not (mem '*native* (method-accessflags (current-method s))))
                 (consistent-state s))
            (djvm::check-ACONST_NULL inst s))))


;-- BCV::check-ACONST_NULL monotonic   -------------------------------------

(encapsulate () 
  (local (include-book "base-bcv-check-monotonic"))
  (defthm sig-check-ACONST_NULL-on-more-general-implies-more-specific
    (implies (and (bcv::sig-frame-more-general gframe sframe env)
                  (bcv::check-ACONST_NULL inst env gframe))
             (bcv::check-ACONST_NULL inst env sframe))))


; avoided loading base-bcv-check-monotonic.lisp
;-- BCV::execute-ACONST_NULL monotonic  ------------------------------------


(encapsulate () 
  (local (include-book "base-bcv-step-monotonic"))
  (defthm ACONST_NULL-monotonicity
  (implies (and (bcv::sig-frame-more-general gframe sframe env)
                (bcv::check-ACONST_NULL inst env gframe))
           (bcv::sig-frame-more-general 
            (bcv::normal-frame (bcv::execute-ACONST_NULL inst env gframe))
            (bcv::normal-frame (bcv::execute-ACONST_NULL inst env sframe)) env))))


;-- DJVM::step frame expansion  ---------------------------




(encapsulate ()
    (local (include-book "base-frame-sig-expansion"))
    (defthm execute-ACONST_NULL-frame-sig-is
      (mylet* ((ns (execute-ACONST_NULL inst s))
               (index (topStack s))
               (array-ref (topStack (popStack s))))
              (implies 
               (and (consistent-state s)
                    (check-ACONST_NULL inst s))
               (equal (frame-sig (current-frame ns)
                                 (instance-class-table ns)
                                 (heap ns)
                                 (heap-init-map (aux ns)))
                      (frame-push-value-sig  'NULL
                       (frame-sig (current-frame s)
                                  (instance-class-table s)
                                  (heap s)
                                  (heap-init-map (aux s)))))))))

;----------------------------------------------------------------------

;-- BCV::step frame expansion  ---------------------------

(encapsulate ()
       (local (include-book "base-bcv-frame-sig-expansion"))
       (defthm bcv-execute-ACONST_NULL-is
         (implies (and 
            (consistent-state s)
            (check-ACONST_NULL inst s)
            (bcv::check-ACONST_NULL inst (env-sig s) 
                                    (frame-sig (current-frame s)
                                               (instance-class-table s)
                                               (heap s)
                                               (heap-init-map (aux s)))))
           (equal (car (bcv::execute-ACONST_NULL inst (env-sig s) 
                                                 (frame-sig (current-frame s)
                                                            (instance-class-table s)
                                                            (heap s)
                                                            (heap-init-map (aux s)))))
                  (frame-push-value-sig 'NULL
                                        (frame-sig (current-frame s)
                                                   (instance-class-table s)
                                                   (heap s)
                                                   (heap-init-map (aux s))))))))

;----------------------------------------------------------------------

;;(i-am-here) ;; Mon Jul 25 16:50:01 2005. some proof break this!! 

(encapsulate ()
 (local (include-book "base-next-state-more-specific"))
 (defthm next-state-no-more-general-ACONST_NULL
  (mylet* ((oframe (frame-sig (current-frame s)
                              (instance-class-table s)
                              (heap s)
                              (heap-init-map (aux s))))
           (ns   (djvm::execute-ACONST_NULL inst s))
           (nframe (frame-sig (current-frame ns)
                              (instance-class-table ns)
                              (heap ns)
                              (heap-init-map (aux ns)))))
          (implies (and (consistent-state s)
                        (bcv::check-ACONST_NULL inst (env-sig s) oframe)
                        (djvm::check-ACONST_NULL inst s)
                        (not (check-null (topStack (popStack s)))))
                   (bcv::sig-frame-more-general 
                    (mv-nth 0 (bcv::execute-ACONST_NULL inst 
                                                        (env-sig s)
                                                        oframe))
                    nframe
                    (env-sig s))))))



             
;-- M6-DJVM-equal-when-check-succeeds.lisp ------------------------------

;; Tue Aug  2 16:10:50 2005

;; (i-am-here) ;; Tue Aug  2 16:10:56 2005

(include-book "../../M6/m6-bytecode")
(include-book "../../DJVM/consistent-state-to-untag-state")



;; (encapsulate ()
;;    (local (include-book "base-untag-state"))
;;    (defthm equal-ACONST_NULL-when-guard-succeeds
;;      (implies (ACONST_NULL-guard inst s)
;;               (equal (untag-state (djvm::execute-ACONST_NULL inst s))
;;                      (m6::execute-ACONST_NULL inst (untag-state s))))))



(encapsulate ()
   (local (include-book "base-state-equiv"))
   (defthm equal-ACONST_NULL-when-guard-succeeds
      (implies (and (state-equiv M6::m6-s DJVM::djvm-s)
                    (ACONST_NULL-guard inst DJVM::djvm-s))
               (state-equiv (m6::execute-ACONST_NULL inst M6::m6-s)
                            (djvm::execute-ACONST_NULL inst DJVM::djvm-s)))
      :hints (("Goal" :do-not '(generalize fertilize)))))


;;; Tue Aug  2 16:12:55 2005

;;; take only two minutes. compare with the time it takes to replay ALOAD.lisp
;;; proof! 

;----------------------------------------------------------------------


(encapsulate () 
  (local (include-book "base-method-ptr-no-change"))
  (defthm execute-ACONST_NULL-change-no-method-ptr
    (equal (method-ptr (current-frame (djvm::execute-ACONST_NULL inst s)))
           (method-ptr (current-frame s)))))

;;; next need to prove loaded class method-does-not-change! 


(encapsulate () 
  (local (include-book "base-method-no-change"))
  (defthm deref-method-no-change-if-already-loaded-ACONST_NULL
    (implies (consistent-state s)
             (equal (deref-method (method-ptr (current-frame s))
                                  (instance-class-table 
                                   (djvm::execute-ACONST_NULL inst s)))
                    (deref-method (method-ptr (current-frame s))
                                  (instance-class-table s))))))

(in-theory (disable check-ACONST_NULL ACONST_NULL-guard execute-ACONST_NULL wff-ACONST_NULL))