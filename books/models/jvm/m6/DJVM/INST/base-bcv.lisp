(in-package "DJVM")
(include-book "base")
(include-book "base-consistent-state")
(include-book "../../BCV/typechecker")
(include-book "base-branch-instrs")


(acl2::set-verify-guards-eagerness 0)

(in-theory (disable bcv::frameStack bcv::frameLocals bcv::frameFlags
                   locals operand-stack bcv::nth1OperandStackIs  
                   bcv::pushOperandStack popStack
                   nullp BCV::isMatchingType
                   CODE-STACKMAPS ENV-SIG HEAP-INIT-MAP 
                   MAKEENVIRONMENT BCV::ARRAYELEMENTTYPE
                   BCV::POP frame-sig BCV::SIZEOF
                   bcv::classtableEnvironment
                   BCV::popmatchingtype
                   BCV::MAXSTACKENVIRONMENT
                   bcv::make-sig-frame
                   value-sig
                   make-sig-frame))


(in-theory (disable frame-push-value-sig
                    frame-pop-opstack 
                    frame-top-opstack))



(defthm bcv-frame-Stack-frame-sig-is-opstack-sig
  (equal (bcv::frameStack (frame-sig frame cl hp hp-init))
         (opstack-sig (operand-stack frame) cl hp hp-init (method-ptr frame)))
  :hints (("Goal" :in-theory (enable frame-sig bcv::frameStack make-sig-frame))))

;;; normalize all bcv::frameStack reference into opstack-sig
;;; later we will have 




;; the following is a key lemma
;;  we will need proved it with theorems from the base-bcv-support.lisp
;;
;;
;; (encapsulate ()
;;   (local (include-book "base-bcv-support"))

;; (i-am-here) ;; Wed May 11 09:43:37 2005


(encapsulate ()
   (local (include-book "base-bcv-support"))

   (defthm isMatchingType-popMatchingType-form1
     (implies (and (bcv::ismatchingtype type (opstack-sig (operand-stack (current-frame s))
                                                          cl hp hp-init
                                                          method-ptr) (env-sig
                                                          s))
                   type
                   (not (equal type 'topx))
                   (equal (bcv::sizeof type) 1)
                   (not   (equal type 'void))
                   (consistent-state s)
                   (equal (instance-class-table s) cl)
                   (equal (heap s) hp)
                   (equal (heap-init-map (aux s)) hp-init)
                   (equal (method-ptr (current-frame s)) method-ptr))
              (equal (BCV::POPMATCHINGTYPE type
                                           (OPSTACK-SIG (OPERAND-STACK (CURRENT-FRAME S))
                                                        cl hp hp-init method-ptr))
                     (opstack-sig (operand-stack (current-frame (popStack s)))
                                  cl hp hp-init method-ptr)))
     :hints (("Goal" :in-theory (e/d () 
                                     ())))))
  






(defthm topstack-guard-strong-implied-by-canPopCategory1
  (implies (and (canPopCategory1 (operand-stack (current-frame s)))
                (consistent-state s)
                (NOT (MEM '*NATIVE*
                          (METHOD-ACCESSFLAGS (CURRENT-METHOD S)))))
           (topstack-guard-strong s))
  :hints (("Goal" :in-theory (enable topstack-guard-strong))))

;----------------------------------------------------------------------

;;; some facts about isMatchingType and canPopCategory
;;; there will be finite number of these. 
;;; Force ACL2 to try all these rules during backchaining

(include-book "base-bcv-fact-isMatchingType-canPopCategory1")

;----------------------------------------------------------------------

;
; for showing djvm::check-* implies djvm::*-guard we need provide some facts
; about consistent-state's component been consistent and their values matches
; their tags. 
;


;; (defthm REFp-implies-not-tag-of-specific
;;   (implies (REFp (topStack s) (heap s))
;;            (equal (tag-of (topStack s)) 'REF))
;;   :hints (("Goal" :in-theory (enable tag-of wff-REFp topStack REFp))))




; We then need to show isAssignable to an none primitive-type 
; in an consistent-state implies REFp!! 

; Note this will be a finite set of lemmas!!! 


(include-book "base-bcv-fact-isMatchingType-suitable-value")


;----------------------------------------------------------------------


(defthm len-bcv-pushOperandStack 
  (implies (and (syntaxp (equal (car v) 'QUOTE))
                (not   (equal v 'void))
                (equal (bcv::sizeof v) 1))
           (equal (LEN (BCV::PUSHOPERANDSTACK v  stk)) (+ 1 (len stk))))
  :hints (("Goal" :in-theory (enable bcv::pushoperandstack))))


;----------------------------------------------------------------------
;; (i-am-here) ;; Tue May 17 23:16:48 2005

(defthm bcv-max-stack-environment
  (equal (BCV::MAXSTACKENVIRONMENT (ENV-SIG S))
         (max-stack s))
  :hints (("Goal" :in-theory (enable env-sig max-stack makeenvironment 
                                     bcv::maxstackenvironment))))


;----------------------------------------------------------------------

;; because of AASTORE asserts that the value is not initialized. 
;;
;; We will need some facts to assert isMatching type java.lang.Object
;; ensures that (not (deref2-init ...))
;;


(include-book "base-bcv-fact-isMatchingType-value-initialized")


;----------------------------------------------------------------------
;;(i-am-here) ;; Wed Jul 27 15:16:30 2005

;;; this is not true! 

(local 
 (defthm wff-instr-implies-never-stackmap
   (implies (wff-insts insts)
            (not (bcv::isstackmapframe (car insts))))))

(local 
 (defthm get-map-make-map-same
   (equal (bcv::getmap (bcv::makeStackmap map))
          map)))

(local 
 (defthm isStackMapFrame-makestackmap
   (bcv::isstackmapframe (bcv::makeStackmap map))))

(local 
 (defthm bcv-search-in-merged-code-implies-target-exist
   (implies (and (wff-insts instrs)
                 (bcv::searchstackframe offset 
                                        (bcv::mergestackmapandcode maps instrs)))
            (branch-target-exists offset instrs))
   :hints (("Goal" :in-theory (disable bcv::getmap bcv::makeStackMap
                                       bcv::mapoffset
                                       bcv::isstackmapframe)))))


(local 
 (defthm allinstructions-make-env
   (equal (bcv::allinstructions
           (MAKEENVIRONMENT
            anyclassdecl
            currentmethod
            returntype
            merged-maps-insts
            maxstack
            exception-handlers
            scl))
          merged-maps-insts)
   :hints (("Goal" :in-theory (enable makeenvironment)))))


(defthm bcv-target-is-safe-implies-in-range
  (implies (and (bcv::targetistypesafe (env-sig s)
                                       anyframe 
                                       offset)
                (wff-insts (method-code (current-method s))))
           (branch-target-exists offset (method-code (current-method s))))
  :hints (("Goal" :in-theory (e/d (current-method env-sig)
                                  (bcv::mergestackmapandcode
                                   BCV::ALLINSTRUCTIONS
                                   bcv::searchstackframe)))))
                                      


;----------------------------------------------------------------------
