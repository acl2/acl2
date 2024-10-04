(in-package "BCV")
(include-book "../../BCV/typechecker")
(include-book "../../BCV/bcv-functions")


;; (local 
;;  (defthm nth-canPop1-f
;;   (implies (and (bcv::canPop1 (cons x anylist) stack env)
;;                 (equal (bcv::sizeof x) 1)
;;                 (< 0 i)
;;                 (integerp i))
;;            (equal (nth i stack)
;;                   (nth (- i 1) (cdr stack))))
;;   :rule-classes :forward-chaining))



;; (local (defthm consistent-sig-type-if-consistent-sig-stack
;;   (implies (and (bcv::consistent-sig-stack stk icl)
;;                 (equal (bcv::sizeof (car stk)) 1)
;;                 (not (equal (car stk) 'topx))
;;                 (consp stk))
;;            (bcv::consistent-sig-type (car stk) icl))
;;   :hints (("Goal" :in-theory (enable bcv::consistent-sig-stack)))))


(local (defthm consistent-sig-type-if-consistent-sig-stack-f
  (implies (and (bcv::consistent-sig-stack stk icl)
                (equal (bcv::sizeof (car stk)) 1)
                (not (equal (car stk) 'topx))
                (consp stk))
           (bcv::consistent-sig-type (car stk) icl))
  :hints (("Goal" :in-theory (enable bcv::consistent-sig-stack)))
  :rule-classes :forward-chaining))


(local 
 (defthm canPop1-nth1-fact-2-lemma-f
  (implies (and (canPop1 (cons 'int anylist) stk  env)
                (consistent-sig-stack stk icl))
           (bcv::consistent-sig-type (car stk) icl))
  :rule-classes :forward-chaining))

(local 
 (defthm canPop1-consp-f
   (implies (canPop1 (cons any anylist) stk env)
            (consp stk))
   :rule-classes :forward-chaining))


(defthm canPop1-nth1-fact-2
  (implies (and (canPop1 '(int (array (class "java.lang.Object")))
                         (framestack frame)  env)
                (consistent-sig-stack (frameStack frame) icl))
           (consistent-sig-type (nth1OperandStackIs 1 frame) icl))
  :hints (("Goal" :in-theory (disable canPop1 consistent-sig-stack consistent-sig-type))))



;; (local 
;;  (defthm nth-canPop1-f
;;   (implies (and (bcv::canPop1 (cons x anylist) stack env)
;;                 (equal (bcv::sizeof x) 1)
;;                 (< 0 i)
;;                 (integerp i))
;;            (equal (nth i stack)
;;                   (nth (- i 1) (cdr stack))))
;;   :rule-classes :forward-chaining))

;; (local 
;;  (defthm nth-canPop1-b
;;   (implies (and (< 0 i)
;;                 (integerp i))
;;            (equal (nth i stack)
;;                   (nth (- i 1) (cdr stack))))))


(local (defthm consistent-sig-type-if-consistent-sig-stack
  (implies (and (bcv::consistent-sig-stack stk icl)
                (equal (bcv::sizeof (car stk)) 1)
                (not (equal (car stk) 'topx))
                (consp stk))
           (bcv::consistent-sig-type (car stk) icl))
  :hints (("Goal" :in-theory (enable bcv::consistent-sig-stack)))))



(local 
 (defthm canPop1-nth1-fact-1-lemma-f
  (implies (and (canPop1 (cons '(array (class "java.lang.Object")) anylist) stk  env)
                (consistent-sig-stack stk icl))
           (bcv::consistent-sig-type (car stk) icl))
  :rule-classes :forward-chaining))


(local 
 (defthm canPop1-canPop1-f
   (implies (canPop1 (cons x anylist) stk env)
            (canPop1 anylist (popMatchingType x stk) env))
   :rule-classes :forward-chaining))


(local 
 (defthm nth-canPop1
  (implies (and (bcv::canPop1 (cons x anylist) stack icl)
                (equal (bcv::sizeof x) 1)
                (< 0 i)
                (integerp i))
           (equal (nth i stack)
                  (nth (- i 1) (popMatchingType x stack))))
  :rule-classes :forward-chaining))



(local 
 (defthm nth-canPop1-consistent-sig-type
  (implies (and (bcv::canPop1 (cons x anylist) stack env)
                (equal (bcv::sizeof x) 1)
                (< 0 i)
                (integerp i))
           (equal (consistent-sig-type (nth i stack) icl)
                  (consistent-sig-type (nth (- i 1) (popMatchingType x stack))
                                       icl)))
  :hints (("Goal" :in-theory (disable consistent-sig-type)))))


(local 
  (defthm canpop1-consistent-sig-type-pop
    (implies (and (bcv::canPop1 (cons x anylist) stack env)
                  (equal (sizeof x) 1)
                  (not (equal (car stack) 'topx))
                  (consistent-sig-stack stack icl))
             (consistent-sig-stack (popMatchingType x stack) icl))
    :hints (("Goal" :in-theory (disable consistent-sig-type
                                        isMatchingType)))))


(local 
 (defthm canpop1-consistent-sig-type-pop-f
   (implies (and (bcv::canPop1 (cons x anylist) stack env)
                 (equal (sizeof x) 1)
                 (not (equal (car stack) 'topx))
                 (consistent-sig-stack stack icl))
            (consistent-sig-stack (popMatchingType x stack) icl))
   :hints (("Goal" :in-theory (disable consistent-sig-type isMatchingType)))
   :rule-classes :forward-chaining))

                 

(local 
 (defthm canpop1-INT-not-top
   (implies (bcv::canPop1 (cons 'INT anylist) stack env)
            (not (equal (car stack) 'topx)))
   :hints (("Goal" :in-theory (disable consistent-sig-type)))
   :rule-classes :forward-chaining))




;; (local 
;;  (defthm canpop1-consistent-sig-type-pop-f-specific
;;    (implies (and (bcv::canPop1 '(INT (array (class "java.lang.Object"))) stack env)
;;                  (consistent-sig-stack stack icl))
;;             (consistent-sig-stack (popMatchingType 'INT stack) icl))
;;    :hints (("Goal" :in-theory (disable consistent-sig-type isMatchingType)))))



(defthm canPop1-nth1-fact-1
  (implies (and (canPop1 '(INT (array (class "java.lang.Object")))
                         (framestack frame)  env)
                (consistent-sig-stack (framestack frame) icl))
           (bcv::consistent-sig-type (nth1OperandStackIs 2 frame) icl))
  :hints (("Goal" :in-theory (disable consistent-sig-stack framestack canPop1
                                      popMatchingType
                                      consistent-sig-type)
           :restrict ((nth-canPop1-consistent-sig-type
                       ((env env)))))))
                       


(local 
 (defthm not-assignable-REFERENCE
   (NOT (ISASSIGNABLE 'REFERENCE
                      '(ARRAY (CLASS "java.lang.Object"))
                      ICL))
   :hints (("Goal" :expand (ISASSIGNABLE 'REFERENCE
                      '(ARRAY (CLASS "java.lang.Object"))
                      ICL)))))


(local 
 (defthm canPop1-array-is-isArrayType
   (implies (and (canPop1 '((array (class "java.lang.Object"))) stk env)
                 (not (equal (car stk) 'NULL)))
            (isArrayType (car stk)))
   :hints (("Goal" :in-theory (enable isAssignable)))))

 

(local 
 (defthm canPop1-canPop1-f-specific
   (implies (canPop1 '(INT (array (class "java.lang.Object")))  stk env)
            (canPop1 '((array (class "java.lang.Object")))
                     (cdr stk) env))
   :rule-classes :forward-chaining))





(local 
 (defthm nth-canPop1-b
  (implies (and (bcv::canPop1 (cons x anylist) stack icl)
                (equal (bcv::sizeof x) 1)
                (< 0 i)
                (integerp i))
           (equal (nth i stack)
                  (nth (- i 1) (popMatchingType x stack))))))


;; not so stable!! 

(defthm canPop1-nth1-fact-3-array-type
  (implies (and  (canPop1 '(int (array (class "java.lang.Object")))
                          (framestack frame)  env)
                 (not (equal (nth1OperandStackIs 2 frame) 'NULL)))
           (isArrayType (nth1OperandStackIs 2 frame)))
  :hints (("Goal" :in-theory (disable isArrayType canPop1 framestack)
           :restrict ((canPop1-array-is-isArrayType
                       ((icl icl)))))))


