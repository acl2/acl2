(in-package "BCV")
;----------------------------------------------------
;; (defun mem (c cl)
;;    (if (endp cl)
;;        nil
;;      (or (equal (car cl) c)
;;          (mem c (cdr cl)))))

;; (defun notMem (c cl)
;;    (not (mem c cl)))


;; (defun subset (s1 s2)
;;    (if (endp s1)
;;        t
;;      (and (mem (car s1) s2)
;;           (subset (cdr s1) s2))))



;;  (defun del (a y)
;;    (if (endp y)
;;        nil
;;      (if (equal (car y) a)
;;          (cdr y)
;;        (cons (car y) (del a (cdr y))))))


;;  (defun app (a b)
;;    (if (endp a)
;;        b
;;      (cons (car a) (app (cdr a) b))))
;;;
;;; These basic functions are defined in commmon no-dup-facts. 
;;; They are included as part of the BCV pakage definition
(acl2::set-ignore-ok t)


#| ; Commented out by Matt K.
(defmacro msg (&rest args) 
  (acl2::debug-print args))
|#


;;------------------------------------------------------------
;;
;;  Class Term Accessors
;;
;;------------------------------------------------------------

;;; Thu Jan 15 18:17:53 2004. Note this is different from isClassTerm in
;;; jvm-class-table.lisp
;;;
;;;

(defun isClassTerm (Class)
  (and (consp Class)
       (equal (len (cdr Class)) 8)))

;; Sun Mar 28 15:45:40 2004. A year after!!
;; Fri Apr  8 14:48:42 2005. Yet another year!! 
;; Mon Dec 19 20:28:25 2005. 

(defun classClassName (Class)
  (nth 1 Class))

(defun classIsInterface (Class)
  (nth 2 Class))

(defun classSuperClassName (Class)
  (nth 3 Class))

(defun classConstantPool (Class)
  (cdr (nth 4 Class)))

(defun classInterfaces (Class)
  (cdr (nth 5 Class)))

(defun classFields (Class)
  (cdr (nth 6 Class)))

(defun classMethods (Class)
  (cdr (nth 7 Class)))

(defun classAccessFlags (Class)
  (cdr (nth 8 Class)))


;; 
;; (defun classAttributes (Class)
;;   (cdr (nth 9 Class)))
;; Wed Jul 13 14:40:28 2005 
;;
;; Get ignore class attributes!! 
;;
;; in CLDC bytecode verifier. 

(defun make-class-term 
  (className isInterface superClassName cp interfaces
             fields methods accessflags)
  (list 'class className 
        isInterface 
        superClassName 
        (cons 'constant_pool cp)
        (cons 'interfaces    interfaces)
        (cons 'fields        fields)
        (cons 'methods       methods)
        (cons 'accessflags   accessflags)))


(defthm isClassTerm-make-class-term
  (isClassTerm (make-class-term n i s c is fs ms af)))

(defthm make-class-term-accessor 
  (and (equal (classClassName   (make-class-term n i s c is fs ms af)) n)
       (equal (classIsInterface (make-class-term n i s c is fs ms af)) i)
       (equal (classSuperClassName (make-class-term n i s c is fs ms af)) s)
       (equal (classConstantPool   (make-class-term n i s c is fs ms af)) c)
       (equal (classInterfaces   (make-class-term n i s c is fs ms af)) is)
       (equal (classFields       (make-class-term n i s c is fs ms af)) fs)
       (equal (classMethods      (make-class-term n i s c is fs ms af)) ms)
       (equal (classAccessFlags  (make-class-term n i s c is fs ms af)) af)))


(in-theory (disable classClassName classIsInterface classSuperClassName
                    classConstantPool classInterfaces classFields classMethods
                    classAccessFlags
                    make-class-term))


;;------------------------------------------------------------
;;
;;  Method Term Accessors
;;
;;------------------------------------------------------------

(defun isMethodTerm (Method)
  (and (consp Method)
       (equal (len (cdr Method)) 5)))


(defun methodName(Method)
  (nth 1 Method))

(defun methodParameters(Method)
  (cdr (nth 2 Method)))

(defun methodReturnType(Method)
  (cdr (nth 3 Method)))

(defun methodAccessFlags(Method)
  (cdr (nth 4 Method)))

(defun methodCodeAttribute(Method)
  (cdr (nth 5 Method)))

(defun make-method-term 
  (methodName parameters returnType accessFlags codeAttributes)
  (list 'method methodName 
        (cons 'parameters  parameters)
        (cons 'returntype  returnType)
        (cons 'accessflags accessFlags)
        (cons 'code        codeAttributes)))

(defthm make-method-term-accessor 
  (and (equal (methodName       (make-method-term n p r a c)) n)
       (equal (methodParameters (make-method-term n p r a c)) p)
       (equal (methodReturnType (make-method-term n p r a c)) r)
       (equal (methodAccessFlags (make-method-term n p r a c)) a)
       (equal (methodCodeAttribute (make-method-term n p r a c)) c)))

(in-theory (disable methodName methodParameters methodReturnType
                    methodAccessFlags methodCodeAttribute make-method-term))

;--------------------------------------------------------
(defun isFieldTerm (Field)
  (and (consp Field)
       ;;  (equal (car Method) 'method)
       (equal (len (cdr Field)) 5)))

(defun fieldName(Field)
  (nth 1 Field))

(defun fieldType(Field)
  (cadr (nth 2 Field)))

(defun fieldAccessFlags(Field)
  (cdr (nth 3 Field)))

(defun make-field-term 
  (name type accessFlags)
  (list 'field name 
        (list 'returntype  type)
        (cons 'accessflags accessFlags)))

(defthm make-field-term-accessor 
  (and (equal (fieldName       (make-field-term n p a)) n)
       (equal (fieldType       (make-field-term n p a)) p)
       (equal (fieldAccessFlags (make-field-term n p a)) a)))

(in-theory (disable fieldName fieldType fieldAccessFlags  make-field-term))

;---------------------------------
(defun MaxStack1 (Method)
  (cdr (nth 0 (methodCodeAttribute Method))))

(defun FrameSize1 (Method)
  (cdr (nth 1 (methodCodeAttribute Method))))

(defun ByteCodeLength1 (Method)
  (cdr (nth 2 (methodCodeAttribute Method))))

(defun ParsedCode1 (Method)
  (cdr (nth 3 (methodCodeAttribute Method))))

(defun Handlers1 (Method)
  (cdr (nth 4 (methodCodeAttribute Method))))

(defun StackMap1 (Method)
  (cdr (nth 5 (methodCodeAttribute Method))))


(defun MaxStack (Method Class)
  (declare (ignore Class))
  (MaxStack1 Method))

(defun FrameSize (Method Class)
  (declare (ignore Class))
  (FrameSize1 Method))

(defun ByteCodeLength (Method Class)
  (declare (ignore Class))
  (ByteCodeLength1 Method))

(defun ParsedCode (Method Class)
  (declare (ignore Class))
  (ParsedCode1 Method))

(defun Handlers (Method Class)
  (declare (ignore Class))
  (Handlers1 Method))

(defun StackMap (Method Class)
  (declare (ignore Class))
  (StackMap1 Method))


(defun make-code-attribute-term (maxStack frameSize bytecodeLength parsedCode
                                          handlers stackMap)
  (list (list 'max_stack maxStack)
        (list 'max_locals frameSize)
        (list 'code_length bytecodeLength)
        (list 'parsedcode  parsedCode)
        (list 'Exceptions  handlers)
        (list 'StackMap    stackMap)))



;-------------------------------------------------------

(defun make-class-table (cl)
  cl)


(defmacro make-class-table1 (&rest cl)
  (cons 'list cl))

;---------------------------------------------------------

(defun make-sig-frame (Locals Stack Flags) 
  (list 'frame (cons 'locals locals) (cons 'stack stack) Flags))


(defun frameLocals (frame)
  (cdr (nth 1 frame)))

(defun frameStack  (frame)
  (cdr (nth 2 frame)))

(defun frameFlags (frame)
  (nth 3 frame))


(defun Flags (ThisList)
  (if (equal ThisList '(uninitializedThis))
      '(flagThisUninit)
    nil))




;;--------------------------------------------------------
;;
;;   General comments 
;;
;;--------------------------------------------------------

;; Q:  How to deal with the parsing error? 
;;
;; A:  For example, the fact that a static method can't be <init> is
;; encoded as Part of the Prolog version's parser.  Let me seperate
;; those internal constraints into a consistent predicate later






;; ------------------------------
;;
;;  Compute the Type of ThisType  
;;
;; -------------------------------


(defun prefix-class (typ)
  (list 'CLASS typ))


;; assume well formed 
(defun instanceMethodInitialThisType (Class Method) 
  (let ((MethodName (methodName Method))
        (ClassName  (classClassName Class)))
    (if (not (equal MethodName "<init>"))
        (prefix-class ClassName)
      (if (equal ClassName "java.lang.Object")
          (prefix-class "java.lang.Object");; *1* 
        'uninitializedThis))))

;; *1* Note:
;;     Assume Object is initialized by default. 
;;     The standard library has only 1 constructor.
;; 

;; -- 3 cases  <init>, "java.lang.Object".<init>, not <init>


(defun methodInitialThisType (Class Method)       
  (let ((AccessFlags (methodAccessFlags Method)))
    (if (mem '*static* AccessFlags) nil;; *2*
      (list (instanceMethodInitialThisType Class Method)))))
      
;; *2* Note: 
;;     AccessFlags are modeled as list of *static* *native* 
;;     The *public*, *private*, *protected* *final* is not modeled
;;     UPDATE: modeled now. 




;; ----- utitilites --------


(defun sizeOf (Type) 
  (if (or (equal type 'twoword)
          (equal type 'long)
          (equal type 'double)) 2
    1))

(defun expandTypeList (RawArgs);; *3*
  (if (endp RawArgs)
      nil
    (cond ((equal (sizeOf (car RawArgs)) 1)
           (cons (car RawArgs) (expandTypeList (cdr RawArgs))))
          ((equal (sizeOf (car RawArgs)) 2)
           (cons (car RawArgs) (cons 'topx (expandTypeList (cdr RawArgs)))))
          (t nil))));; impossible.

;; outdated
;; *3* Note: 
;;     ExpandTypeList expands the raw typelist to type list with     
;;     padding -- so that Double, Long occupy two word. top is 
;;     explictly inserted. 
;;  
;;     In our implementation, we assume jvm2acl2 translator
;;     already does this.

;; march 02 we don't assume jvm2acl2 translator does this. 




;; ------------------------------
;;
;  Build Initial StackFrame 
;;
;; -------------------------------

;; fill up the slot with 'topx type
;; assuming (len Args) <= FrameSize

(defun top-list (len)
  (if (zp len)
      nil
    (cons 'topx (top-list (- len 1)))))
      

(defun expandToLength (Args FrameSize)
  (app Args (top-list (- FrameSize (len args)))))


(defun translate-type (type);; *** 
  (cond ((equal type 'boolean) 'int)
        ((equal type 'byte)    'int)
        ((equal type 'short)   'int)
        ((equal type 'char)    'int)
        (t type))) 

;;*** this method corresponds to the special treatment in 
;; signature.pl. util.pl the ----- primitiveArrayInfo

(defun translate-types (types)
  (if (endp types)
      nil
    (cons (translate-type (car types))
          (translate-types (cdr types)))))

(defun methodInitialStackFrame (Class Method FrameSize);; *4* 
  (let* ((RawArgs1 (methodParameters Method))
         (RawArgs  (translate-types RawArgs1))
         (Args     (expandTypeList RawArgs))    
         (ThisList (methodInitialThisType Class Method))
         (Flags    (Flags ThisList))
         (ThisArgs (append ThisList Args))
         (Locals   (expandToLength ThisArgs FrameSize)))
    (make-sig-frame 
     Locals  nil Flags)))


;; *4* Note: 
;;     Assume Well Formed Stack
;;



;;--------------------------------------------------------------
;;
;;  WellFormed Predicates 
;;
;;-------------------------------------------------------------- 

(defun isWellFormedCodeAttribute (Class Method) 
  (declare (ignore Class Method))
  t);; *5* 

;; *5* Note:  omitted here.   Feb 23
;;     To prove Properties, we eventually need this predicate 



;;-----------------------------------
;;
;;  Create a StackMap 
;;  
;;----------------------------------- 

;; <stackmap> ::= (stack_map (<offset> <frame>))
;; 
;; <offset> in bytes.
;; <frame>  refer to (defun make-sig-frame  ...)

(defun makeStackMap (map);; *6*
  (list 'stack_map map))

;; the only purpose of makeStackMap is to distinguish StackMap and
;; instructions in a MergedStackMapAndCode.


;; ---- StackMap Accessor -----

(defun  mapOffset (map)
  (car map))

(defun  mapFrame (map)
  (cadr map))

(defun  getMap (StackMapFrame)
  (cadr StackMapFrame))

;; ---  StackMap Recognizor ---- 

(defun isStackMapFrame (StackMapFrame)
  (and (consp StackMapFrame)
       (equal (car StackMapFrame) 'stack_map)))


;; OUTDATED --- FEB 23.
;;   
;; don't deal with byte offset, assume all reference to the code is in
;; instruction offsets. StackMap's offset is translated into instruction
;; offset. 
;; 
;; UPDATE   --- All offset mentioned is in Bytes. 
;;  including: instruction offset, exception handler offset, stackMap offset
;;  Offset measured in bytes.   




;; ---- Instruction Accessor -----

;; <instruction> ::= (<offset> (<opcode> [<args>]))

(defun instrOffset (instr)
  (car instr))

(defun instrBody (instr)
  (cadr instr))



;; ---- Instruction Recognizer ----

(defun isInstruction (carMergedCode);; *7*
  (and (consp carMergedCode)
       (consp (cadr carMergedCode))
       (integerp (instrOffset carMergedCode))))


(defun isStackMap (carMergedCode)
  (and (consp carMergedCode)
       (equal (car carMergedCode) 'stack_map)))

;; *7* Note: 
;;     Called to distinguish from StackMap. 
;;     refer to mergeStackMapAndCode


;; ---- endOfCode Recognizer ----

(defun isEnd (carMergedCode)
  (and (consp carMergedCode)
       (equal (car carMergedCode) 'endofcode)))



;;----------------------------------------------
;;
;;  Merge StackMap Attribute with Instructions
;;  
;;---------------------------------------------- 


;; (defun mergeStackMapAndCode (maps ParsedCode)
;;   (if (endp maps)
;;       ParsedCode  
;;     (if (endp ParsedCode);; *8*
;;         maps
;;       (let ((mpc (mapOffset (car maps)))
;;             (pc  (instrOffset (car ParsedCode))))
;;         (if (equal mpc pc)
;;             (cons (makeStackMap (car maps))
;;                   (cons (car ParsedCode)
;;                         (mergeStackMapAndCode  (cdr maps)
;;                                                (cdr ParsedCode))))
;;           (if (< pc mpc)
;;               (cons (car ParsedCode)  
;;                     (mergeStackMapAndCode maps (cdr ParsedCode)))
;;             (cons (makeStackMap (car maps))
;;                   (cons (car ParsedCode)
;;                         (mergeStackMapAndCode  (cdr maps)
;;                                                (cdr ParsedCode))))))))))


;;; Wed Jul 27 23:58:26 2005
;;; Wed Jul 27 23:58:28 2005

;;; Problem
;;; We have to assert that 
;;; If there is StackMap, then next instruction from the code, must be 
;;; at the same PC location!!! 
;;; 
;;; Otherwise, we could not prove the theorem in base-bcv.lisp!! 
;;; 

(defun mergeStackMapAndCode (maps ParsedCode)
  (if (endp maps)
      ParsedCode  
    (if (endp ParsedCode);; *8*
        nil ;; second modification ;; Thu Jul 28 00:28:23 2005
      (let ((mpc (mapOffset (car maps)))
            (pc  (instrOffset (car ParsedCode))))
        (if (equal mpc pc)
            (cons (makeStackMap (car maps))
                  (cons (car ParsedCode)
                        (mergeStackMapAndCode  (cdr maps)
                                               (cdr ParsedCode))))
          (if (< pc mpc)
              (cons (car ParsedCode)  
                    (mergeStackMapAndCode maps (cdr ParsedCode)))
            nil)))))) ;; something is wrong here!!!  
            ;;; because we always expect that a stack map appears right before
            ;;; a corresponding code with the same PC!!
            ;;; Thu Jul 28 00:03:39 2005


;; unreachable nil if the Class file is well formed. WRONG 

;; Assumption ParsedCode is a truelistp
          

;; *8* Note: 
;;      It is impossible for parsed code to end first?
;;      hanbing -- however for acl2 to admit the function we have to
;;      add this.



;;----------------------------------------------
;;
;;  Collect Environment Object
;;  
;;---------------------------------------------- 


;; Thu Dec 22 16:03:20 2005. note. the ReturnType is not used in this
;; definition!! 
;; 
(defun makeEnvironment (Class Method ReturnType MergedCode MaxStack Handlers CL)  
  (list Class Method ReturnType MergedCode MaxStack Handlers CL))

(defun AllInstructions (Environment)
  (nth 3 Environment))

(defun exceptionHandlers (Environment)
  (nth 5 Environment))

(defun classtableEnvironment (Environment)
  (nth 6 Environment))

(defun maxStackEnvironment (Environment)
  (nth 4 Environment))

(defun classEnvironment (Environment)
  (nth 0 Environment))

(defun thisClassEnvironment (Environment)
  (classClassName (classEnvironment Environment)))


(defun methodEnvironment (Environment)
  (nth 1 Environment))



;; -------------------------------------------
;;
;;  Type Hierachy 
;;
;; -------------------------------------------

        
;; OUTDATED -- Feb 23, ????
;;   how to define isAssignable? without Dynamic Loading?? 
;;   Don't what to deal with long and double, just assuming 
;;
;; UPDATE  
;;   Deal with Long and Double. 
;;   Assuming jvm2acl2 translate the "long" to "long top" etc. 


;; (defun isClassType (t1)
;;   (or (equal t1 'null)
;;   (and (consp t1)
;;        (equal (car t1) 'class))))

;; Sun Mar 28 15:43:56 2004

(defun isNullType (t1)
  (equal t1 'null))

(defun isClassType (t1)
  (and (consp t1)
       (equal (len t1) 2)
       (true-listp t1)
       (equal (car t1) 'class)))



;; (defun isClassType (t1)
;;   (and (consp t1)
;;        (equal (car t1) 'class)))

;;; Old definition. not enough. 
;;; Thu Apr  7 12:52:05 2005

  
;; (defun isArrayType (t1)
;;   (or (equal t1 'null)
;;       (and (consp t1)
;;            (equal (car t1) 'array))))

;; Sun Mar 28 15:44:01 2004

;; (defun isArrayType (t1)
;;   (and (consp t1)
;;        (equal (car t1) 'array)))

(defun isArrayType (t1)
   (and (consp t1)
        (equal (len t1) 2)
        (true-listp t1)
        (equal (car t1) 'array)))


(defun isUninitializedObject (t1)
  (and (consp t1)
       (equal (car t1) 'uninitialized)))
  

(defun isAssignableMeasure (t1)
  (cond ((equal t1 'oneWord) 1)
        ((equal t1 'twoWord) 1)
        ((equal t1 'int)     2)
        ((equal t1 'float)   2)
        ((equal t1 'long)    2)
        ((equal t1 'double)  2)
        ((equal t1 'reference) 2)
        ((equal t1 'uninitialized) 3)
        ((isClassType t1) 4)
        ((isArrayType t1) 4)
        ((equal t1 'uninitializedThis) 4)
        ((isUninitializedObject t1) 4)
        ((equal t1 'null)  5)
        (t 0)))

; --- accessor ----

(defun name-of (aClassType)
  (cadr aClassType));; need to apply on aClassType

; --- check if not primitive type ---
(defun compound (x)
  (consp x))

; -- used only on arrayType

;; (defun component-type (aArrayType)
;;   (if (isArrayType aArrayType)
;;       (cadr aArrayType)
;;     nil));; indicate undefined


;;; Thu Apr 14 15:24:35 2005

(defun component-type (aArrayType)
  (cadr aArrayType))




; --- class-by-name ---

; <class-table> ::= (<classterm> ... )

(defun class-by-name (name classtable);; *13*
  (if (endp classtable)
      nil
    (if (equal (classClassName (car classtable)) name)
        (car classtable)
      (class-by-name name (cdr classtable)))))

;; *13* Note:: 
;;      like assoc-equal  classtable is a list of classes
;;      to use class-by-name need to check (classClassName Class) 
;; 
;; assuming classtable is well formed, a list of ClassTerm



;; -------------------------------------------------------
;;
;;  Proof Script: SuperClass Resolution Process terminate
;; 
;; -------------------------------------------------------



;; ;;  ----- Basic Set Theory Stuff ----

;; ;----------------------------------------------------------

;; (defun set-diff (total seen);; *14* 
;;   (if (endp total)
;;       nil
;;     (if (mem (car total) seen)
;;         (set-diff (cdr total) seen)
;;       (cons (car total) (set-diff (cdr total) (cons (car total) seen))))))

;; ;; *14* Note: 
;; ;;       Set-Diff returns a non-duplicated list that represent
;; ;;       the set

;; ;; some work  Set Theory stuff
;; ;; mainly about set-diff, nodup-set, the size of the nodup-set
;; ;;
;; ;; this is used for proving termination of class superclass resolution

;; ;; Originally. I did somework with permuation. 
;; ;; Later found out Set-equal + Non-Dup suffice.

;; (defun set-equal (a b)
;;   (and (subset a b)
;;        (subset b a)))

;; (defthm mem-subset
;;   (implies (and (subset a b)
;;                 (mem x a))
;;            (mem x b)))

;; (defthm subset-cons 
;;   (implies (subset a b)
;;            (subset a (cons x b))))

;; (defthm subset-reflexive 
;;   (subset x x))

;; (defthm subset-transitive 
;;   (implies (and (subset a b)
;;                 (subset b c))
;;            (subset a c)))


;; (defthm set-equal-transitive
;;   (implies (and (set-equal a b)
;;                 (set-equal b c))
;;            (set-equal a c)))

;; (defequiv set-equal)


;; (defcong set-equal equal (mem x s) 2
;;   :hints (("Subgoal *1/4" :cases ((mem x (cdr s))))
;;           ("Subgoal *1/4.2'" 
;;            :use (:instance mem-subset  (a s-equiv) (b s))
;;            :in-theory (disable mem-subset))))



;; (defthm set-equal-cons
;;   (implies (set-equal a b)
;;            (set-equal (cons x a) (cons x b))))


;; (defthm set-equal-mem-cons-2
;;   (implies (mem x l)
;;            (set-equal (cons x l) l)))
                                             
;; (in-theory (disable set-equal))


;; (defun set-diff-cong-induct (s s-equiv total)
;;   (if (endp total)
;;       (cons s s-equiv)
;;     (if (mem (car total) s)
;;         (set-diff-cong-induct s s-equiv (cdr total))
;;       (set-diff-cong-induct (cons (car total) s) (cons (car total) s-equiv) (cdr total)))))


;; (defcong set-equal equal (set-diff total seen) 2
;;   :hints (("Goal" :induct (set-diff-cong-induct seen seen-equiv total))))


;; (defun subset-set-diff-induct (total a b)
;;   (if (endp total)
;;       (cons a b)
;;     (subset-set-diff-induct (cdr total) (cons (car total) a) (cons (car total) b)))) 
  

;; (defthm subset-set-diff
;;   (implies (subset a b) 
;;            (subset (set-diff total b) (set-diff total a)))
;;   :hints (("Goal" :induct (subset-set-diff-induct total a b))))


;; ;;-------------------------------------------------------------------- 

;; ; ---- nodup-set ----- 

;; (defun nodup-set (s)
;;   (if (endp s)
;;       t
;;     (and (not (mem (car s) (cdr s)))
;;          (nodup-set (cdr s)))))


;; (defthm mem-set-diff
;;   (implies (mem a seen)
;;            (not (mem a (set-diff total seen)))))


;; (defthm set-diff-is-a-nodup-set
;;   (nodup-set (set-diff total seen))
;;   :rule-classes :type-prescription)


;; (defun subset-nodup-set-size-induct (s1 s2)
;;   (if (endp s1)
;;       s2
;;     (subset-nodup-set-size-induct (cdr s1) (del (car s1) s2))))

;; (defthm del-set-len
;;   (implies (mem x s)
;;            (equal (len s)  (+ 1 (len (del x s))))))     

;; (defthm mem-del 
;;   (implies (not (equal a b))
;;            (equal (mem a (del b x))
;;                   (mem a x))))
           
;; (defthm del-nodups
;;   (implies (nodup-set s)
;;            (nodup-set (del x s))))


;; (defthm del-nodup-set-subset
;;   (implies (and (subset (cons x s1) s2)
;;                 (nodup-set (cons x s1)))
;;            (subset s1 (del x s2))))

;; ; --- to talk about termination, we talk about the number of unseen
;; ; --- classes decrease.


;; (defthm subset-nodup-set-size
;;   (implies (and (subset s1 s2)
;;                 (nodup-set s1)
;;                 (nodup-set s2))
;;            (<= (len s1) (len s2)))
;;   :hints (("Goal" :induct (subset-nodup-set-size-induct s1 s2)))
;;   :rule-classes :linear)


;; (defun len-set-equal-nodup-set-x-induct (s1 s2)
;;   (if (endp s1)
;;       s2
;;     (len-set-equal-nodup-set-x-induct (cdr s1) (del (car s1) s2))))

;; (defthm  len-set-equal-nodup-set-x
;;   (implies (and (mem a s2)
;;                 (not (mem a s1))
;;                 (subset s1 s2)
;;                 (nodup-set s1)
;;                 (nodup-set s2))
;;            (< (len s1) (len s2)))
;;   :hints (("Goal" :induct (len-set-equal-nodup-set-x-induct s1 s2))))


;; (defthm mem-set-diff-x
;;   (implies (and (mem a total)
;;                 (not (mem a seen)))
;;            (mem a (set-diff total seen))))


;; (defthm len-set-diff-mem
;;   (implies (and (not (mem a seen)) 
;;                 (mem a total))
;;            (< (len (set-diff total (cons a seen)))
;;               (len (set-diff total seen))))
;;   :hints (("Goal" :do-not-induct t
;;            :use ((:instance len-set-equal-nodup-set-x
;;                             (s1 (set-diff total (cons a seen)))
;;                             (s2 (set-diff total seen))))))
;;   :rule-classes :linear)
           
;; ;; ----------- Above enough rules about set-diff -----------





;; --------------------------------------------------------
;;
;;  Well Formed Direct SuperClass Relation Specification 
;;
;; --------------------------------------------------------


;; Write out the predicate that ensure that superclass doesn't contain
;; loops.  This requirement is needed to guarantee the superclass
;; resolving won't run forever. 


;;; We may want to share the isAssignableTest with DJVM. But for now. We keep
;;; them separate. It is not hard to prove those two are equivalent..  

(defun all-class-names (cl)
  (if (endp cl)
      nil
    (cons (classClassName (car cl))
          (all-class-names (cdr cl)))))

(defun unseen-class-measure (seen cl)
  (len (set-diff (all-class-names cl) seen)))

(defun superclass-no-loop1-measure (seen cl)
  (len (set-diff (all-class-names cl) seen)))

(defthm class-by-name-all-class-names
  (implies (isClassTerm (class-by-name n1 cl)) 
           (mem n1 (all-class-names cl))))

(in-theory (disable isClassTerm class-by-name))

(defun superclass-no-loop1 (n1 cl seen)
  (declare (xargs :measure (superclass-no-loop1-measure seen cl)))
  (let* ((theClass (class-by-name n1 cl))
         (n2 (classSuperClassName theClass)))
    (if  (not (isClassTerm theClass)) t
      (if (mem n1 seen)
          nil
        (superclass-no-loop1 n2 cl (cons n1 seen))))))


(defun superclass-no-loop (n1 cl)
  (superclass-no-loop1 n1 cl nil))
   
(defun collect-superclass-list1 (n1 cl ss)
  (declare (xargs :measure (superclass-no-loop1-measure ss cl)))
  (let* ((theClass (class-by-name n1 cl))
         (n2 (classSuperClassName theClass)))
    (if (isClassTerm theClass)
        (if (mem n1 ss)
            nil
          (cons n1 (collect-superclass-list1 n2 cl (cons n1 ss))))
      nil)))
             
(defun collect-superclass-list (n1 cl)
  (collect-superclass-list1 n1 cl nil))

; --- proofs for collect-superclass-list increase --- 

      
;; (defcong set-equal equal (collect-superclass-list1 n cl ss) 3)

(DEFTHM
  SET-EQUAL-IMPLIES-EQUAL-BCV-COLLECT-SUPERCLASS-LIST1-3
  (IMPLIES
   (SET-EQUAL SS SS-EQUIV)
   (EQUAL
    (COLLECT-SUPERCLASS-LIST1 N CL SS)
    (COLLECT-SUPERCLASS-LIST1 N CL SS-EQUIV)))
  :RULE-CLASSES (:CONGRUENCE))      


(defthm set-equal-cons-cons
  (set-equal (cons x (cons y a))
             (cons y (cons x a)))
  :hints (("Goal" :in-theory (enable set-equal))))


; ---- important observation I  -----
;
; If X doesn't belongs to superclasses of N, add it to SS doesn't matter
;
; SS represents the set that can't be superclasses of N under well formed
; Direct SuperClass Relation.

(defthm collect-superclass-list1-non-mem-cons
  (implies (and (not (mem x (collect-superclass-list1 n cl ss)))
                (superclass-no-loop1 n cl ss))
           (equal (collect-superclass-list1 n cl (cons x ss))
                  (collect-superclass-list1 n cl ss))))

;; (defcong set-equal equal (superclass-no-loop1 n cl ss) 3)

(acl2::set-match-free-default :all)

(DEFTHM
  SET-EQUAL-IMPLIES-EQUAL-BCV-SUPERCLASS-NO-LOOP1-3
  (IMPLIES
   (SET-EQUAL SS SS-EQUIV)
   (EQUAL (SUPERCLASS-NO-LOOP1 N CL SS)
          (SUPERCLASS-NO-LOOP1 N CL SS-EQUIV)))
  :RULE-CLASSES (:CONGRUENCE))


(defthm superclass-no-loop1-cons
  (implies (superclass-no-loop1 n cl (cons x ss))
           (superclass-no-loop1 n cl ss)))


; ---- important obseration II -----
;
; If superclass-no-loop is true, none of the superclasses of N can
; appear in SS.
(defthm mem-collect-superclass-no-loop
  (implies (mem n (collect-superclass-list1 n1 cl ss))
           (not (superclass-no-loop1 n1 cl (cons n ss)))))




; --- this also basically
;   (cdr (collect-superclass-list A cl))
;                   = (collect-superclass-list (super A cl))
(defthm collect-superclass-list1-equal-2
  (implies (and (superclass-no-loop1 n1 cl ss)
                (isClassTerm (class-by-name n1 cl)))
           (equal (collect-superclass-list1 (classSuperClassName (class-by-name n1 cl))
                                            cl 
                                            (cons n1 ss))
                  (collect-superclass-list1 (classSuperClassName (class-by-name n1 cl))
                                            cl
                                            ss)))
  :hints (("Goal" :in-theory (disable classSuperClassName isClassTerm
                                      collect-superclass-list1-non-mem-cons)
           :use ((:instance collect-superclass-list1-non-mem-cons
                            (x n1)
                            (n (classSuperClassName (class-by-name n1 cl))))))))


(defthm collect-superclass-list1-equal-1 
  (implies (and (superclass-no-loop1 n1 cl ss)
                (isClassTerm (class-by-name n1 cl)))
           (equal (collect-superclass-list1 n1 cl ss)
                  (cons n1 (collect-superclass-list1 (classSuperClassName (class-by-name n1 cl))
                                                     cl 
                                                     ss))))
  :hints (("Goal" :in-theory (disable classSuperClassName)
           :use collect-superclass-list1-equal-2)))




;; termination of superclass resolving LOADING
;------------------------------------------------------------------

(defun isJavaSubClassOf-measure (n1 cl)
  (len (collect-superclass-list n1 cl)))



(defun isJavaSubclassOf (n1 n2 cl)
  (declare (xargs :measure (isJavaSubClassOf-measure n1 cl)))
  (and (superclass-no-loop n1 cl);; *15*
       ;; only need for proving termination.
       (isClassTerm (class-by-name n1 cl))
       (or ;; (equal n2 "java.lang.Object") ;; short cut!! 
           ;; Sun Apr 10 21:39:55 2005
           (equal n1 n2)
           (let* ((SubClass (class-by-name n1 cl))
                  (n3 (classSuperClassName SubClass)))
             (isJavaSubclassOf n3 n2 cl)))))

;; *15* Note:
;;      Add this predicate. So that we can prove 
;;      this resolution process terminate
;; 
;; The isJavaSubclassOf can be proved to terminate if
;; superclass-no-loop n1 is true.


#| Superinterface relation is removed from bytecode verifier |#

#|
(defun isArrayInterface (t1)
  (or (equal t1 '(class "java.lang.Cloneable"))
      (equal t1 '(class "java.util.Serializable"))))

|# 
;; java.lang.Cloneable, java.util.Serializable does not exists

(defun isArrayInterface (t1)
  (declare (ignore t1))
  nil)
           

(defun isJavaAssignable (t1 t2 cl)
  (cond ((and (isClassType t1)
              (isClassType t2))
           (or (let ((ToClass (class-by-name (name-of t2) cl)))
                 (classIsInterface ToClass));; rule 1
                 (isJavaSubClassOf (name-of t1) (name-of t2) cl)));; rule 2
        ((and (isArrayType t1)
              (isClassType t2))
         (or (equal '(class "java.lang.Object") t2)
             (classIsInterface (class-by-name (name-of t2) cl))
             ;; NEW ADDITIONS TO KEEP
             ;; isJavaAssignable Transitive!!  ;;; Thu Apr  7 16:39:45 2005
             ;; NOTE: Deviate from the CLDC BCV SPEC!! 
             (isArrayInterface (name-of t2))))
        ((and (isArrayType t1)
              (isArrayType t2))
         (let ((x (component-type t1))
               (y (component-type t2)))
           (or (and (atom x)
                    (atom y)
                    (equal x y))
               (and (compound x)
                    (compound y)
                    (isJavaAssignable x y cl)))))))

;; Sun Mar 28 16:17:22 2004: not transitive!! fix it to make it transitive.
;; We know array in cldc does not implement any interface. 
;; so the above optimization should be ok. 

;;
;; But it change class verificaiton expection into a runtime exception!!
;;

;; (defun isJavaAssignable (t1 t2 cl)
;;   (cond ((and (isClassType t1)
;;               (isClassType t2))
;;            (or (let ((ToClass (class-by-name (name-of t2) cl)))
;;                  (classIsInterface ToClass));; rule 1
;;                  (isJavaSubClassOf (name-of t1) (name-of t2) cl)));; rule 2
;;         ((isClassType t2)  ;; new additions to make it transitive!!
;;          (classIsInterface (class-by-name (name-of t2) cl))) 
;;         ((and (isArrayType t1)
;;               (isClassType t2))
;;          (or (equal '(class "java.lang.Object") t2)
;;              (isArrayInterface (name-of t2))))
;;         ((and (isArrayType t1)
;;               (isArrayType t2))
;;          (let ((x (component-type t1))
;;                (y (component-type t2)))
;;            (or (and (atom x)
;;                     (atom y)
;;                     (equal x y))
;;                (and (compound x)
;;                     (compound y)
;;                     (isJavaAssignable x y cl)))))))


                  
;; hack for testing the top level program flow
#|  
(defun isAssignable (t1 t2 env)
  (declare (ignore t1 t2 env))
  t)
|#  



(defun isAssignable (t1 t2 Env)
  ;; complicated
  (declare (xargs :measure (isAssignableMeasure t1)))
  (let ((cl (classtableEnvironment Env)))
    (if (equal t1 t2) 
        t
      (cond ((and (equal t1 'oneWord)
                  (equal t2 'topx)) t)
            ((and (equal t1 'twoWord) 
                  (equal t2 'topx)) t)
            ((equal t1 'int) 
             (isAssignable 'oneWord t2 Env))
            ((equal t1 'float)
             (isAssignable 'oneWord t2 Env))
            ((equal t1 'long) 
             (isAssignable 'twoWord t2 Env))
            ((equal t1 'double) 
             (isAssignable 'twoWord t2 Env))
            ((equal t1 'reference) 
             (isAssignable 'oneWord t2 Env))
            ((equal 'uninitialized t1)
             (isAssignable 'reference t2 Env))
            ((isClassType t1) 
             (or (isAssignable 'reference t2 Env)
                 (isJavaAssignable t1 t2 cl)))
            ((isArrayType t1)
             (or
              (isAssignable 'reference t2 Env)
              (and (isClassType t2)
                   (isJavaAssignable t1 t2 cl))
              (and (isArrayType t2)
                   (isJavaAssignable t1 t2 cl))))
            ((equal t1 'uninitializedThis)
             (isAssignable 'uninitialized t2 Env))
            ((isUninitializedObject t1)
             (isAssignable 'uninitialized t2 Env))
            ((isNullType t1)
             (or
              (isClassType t2)
              (isArrayType t2)
              (isAssignable
               '(class "java.lang.Object") t2 Env)))
            (t nil)))))

;;
;; Guarantee there (Array NULL) is not a valid type!!

;; isAssignable(X, X) :- !.
;;
;; isAssignable(oneWord, topx).
;; isAssignable(twoWord, topx).
;;
;; isAssignable(int,           X) :- isAssignable(oneWord, X).
;; isAssignable(float,         X) :- isAssignable(oneWord, X).
;; isAssignable(long,          X) :- isAssignable(twoWord, X).
;; isAssignable(double,        X) :- isAssignable(twoWord, X).
;; isAssignable(reference,     X) :- isAssignable(oneWord, X).

;; isAssignable(uninitialized, X) :- isAssignable(reference, X).

;; % These rules may seem strange, but in some cases they have advantages.
;; % The rule below allows us to avoid loading classes when comparing
;; % them to the top types in the hierarchy.

;; isAssignable(class(_),   X) :- isAssignable(reference, X).
;; isAssignable(arrayOf(_), X) :- isAssignable(reference, X).

;; isAssignable(uninitializedThis, X) :- isAssignable(uninitialized, X).
;; isAssignable(uninitialized(_),    X) :- isAssignable(uninitialized, X).

;; isAssignable(null, class(_)).
;; isAssignable(null, arrayOf(_)).
;; isAssignable(null, X)  :- isAssignable(class('java/lang/Object'), X).

;; isAssignable(class(X), class(Y)) :- isJavaAssignable(class(X), class(Y)).
;; isAssignable(arrayOf(X), class(Y)) :- isJavaAssignable(arrayOf(X), class(Y)).
;; isAssignable(arrayOf(X), arrayOf(Y)) :- isJavaAssignable(arrayOf(X),arrayOf(Y)).


;; % For assignments, interface = Object



;; (defun typeListAssignable (l1 l2 env)
;;   (cond ((endp l1) (endp l2))
;;         ((endp l2) nil)
;;         (t (and (isAssignable (car l1) (car l2) env)
;;                 (typeListAssignable (cdr l1) (cdr l2) env)))))

;; ;;; What would happen if it is size 2 object? Tue Feb  1 13:47:16 2005
;; ;;; proof ... 


;; shall we make it more complicated?  Tue Feb  1 13:51:56 2005
;;

;; A = (INT LONG ...)
;; B = (TOP LONG ...)
;; A list assignable to B? 
;; This old version: Yes. 
;; 
;; New Version no. 
;; The problem how we differ from OPSTACK list and local list! 
;; 

(defun typeListAssignable (l1 l2 env)
   (cond ((endp l1) (endp l2))
         ((endp l2) nil)
         (t (and (isAssignable (car l1) (car l2) env)
                 (typeListAssignable (cdr l1) (cdr l2) env)))))



;; (frame (local <typelist>) (stack <typelist>) (<flags>))

(defun frameIsAssignable (Frame1 Frame2 env) 
  (let ((Locals1 (frameLocals Frame1))
        (Locals2 (frameLocals Frame2))
        (StackMap1 (frameStack Frame1))
        (StackMap2 (frameStack Frame2))
        (Flags1  (frameFlags Frame1))
        (Flags2  (frameFlags Frame2)))
    (and (equal (len StackMap1) 
                (len StackMap2))
         (typeListAssignable Locals1 Locals2 env)
         (typeListAssignable StackMap1 StackMap2 env)
         (subset Flags1 Flags2))))





;;----------------------------------------------
;;
;;  Individual Instruction Semantics 
;;  
;;---------------------------------------------- 

;--- primitive for operand stack ---

;; (defun pop (stack);; safe pop
;;   (if (consp stack)
;;       (cdr stack)
;;     nil));; indicate undefined

;; (defun push (value stack)
;;   (cons value stack))

;; (defun top (stack);; safe top
;;   (if (consp stack)
;;       (car stack)
;;     nil));; indicate undefined.

;;;
;;; Tue Aug 16 15:03:02 2005
;;;

(defun top (stack)
  (declare (xargs :guard (consp stack)))
  (car stack))

(defun pop (stack)
  (declare (xargs :guard (consp stack)))
  (cdr stack))

(defun push (value stack)
  (cons value stack))


;; Sat May 21 19:40:27 2005
;;
;; I could make this into a shared package!! 
;; (acl2::set-verify-guards-eagerness 0)

;; (defun pop (stack)
;;   (DECLARE (XARGS :GUARD (CONSP STACK)))
;;   (cdr stack))

;; (defun push (value stack)
;;   (cons value stack))

;; (DEFUN TOP (STACK)
;;   (DECLARE (XARGS :GUARD (CONSP STACK)))
;;   (CAR STACK))


(defun popn (n stack)
  (if (zp n)
      stack
    (popn (- n 1) (pop stack))))

(defun op-code (inst) (car (instrBody inst)))
(defun arg1 (inst) (car (cdr (instrBody inst))))
(defun arg2 (inst) (car (cdr (cdr (instrBody inst)))))
(defun arg3 (inst) (car (cdr (cdr (cdr (instrBody inst))))))


(defun inst (offset instrbody)
  (list offset instrbody))

(defun instructionHasEquivalentTypeRule(inst)
  (let ((op (op-code inst))
        (pc (instrOffset inst)))
    (cond ((equal op 'aload_0) (inst pc '(aload 0)))
          ((equal op 'aload_1) (inst pc '(aload 1)))
          ((equal op 'aload_2) (inst pc '(aload 2)))
          ((equal op 'aload_3) (inst pc '(aload 3)))
          ((equal op 'astore_0) (inst pc '(astore 0)))
          ((equal op 'astore_1) (inst pc '(astore 1)))          
          ((equal op 'astore_2) (inst pc '(astore 2)))          
          ((equal op 'astore_3) (inst pc '(astore 3)))
          ((equal op 'bipush)   (inst pc (list 'sipush (arg1 inst))))
          ((equal op 'dcmpl)    (inst pc '(dcmpg)))
          ((equal op 'dconst_1) (inst pc '(dconst_0)))
          ((equal op 'ddiv)     (inst pc '(dadd)))
          ((equal op 'dload_0) (inst pc '(dload 0)))
          ((equal op 'dload_1) (inst pc '(dload 1)))
          ((equal op 'dload_2) (inst pc '(dload 2)))
          ((equal op 'dload_3) (inst pc '(dload 3)))
          ((equal op 'dmul)     (inst pc '(dadd)))
          ((equal op 'drem)     (inst pc '(dadd)))
          ((equal op 'dstore_0) (inst pc '(dstore 0)))
          ((equal op 'dstore_1) (inst pc '(dstore 1)))          
          ((equal op 'dstore_2) (inst pc '(dstore 2)))          
          ((equal op 'dstore_3) (inst pc '(dstore 3)))
          ((equal op 'dsub)     (inst pc '(dadd)))
          ((equal op 'fcmpl)    (inst pc '(fcmpg)))
          ((equal op 'fconst_1) (inst pc '(fconst_0)))
          ((equal op 'fconst_2) (inst pc '(fconst_0)))
          ((equal op 'fdiv)     (inst pc '(fadd)))
          ((equal op 'fload_0) (inst pc '(fload 0)))
          ((equal op 'fload_1) (inst pc '(fload 1)))
          ((equal op 'fload_2) (inst pc '(fload 2)))
          ((equal op 'fload_3) (inst pc '(fload 3)))
          ((equal op 'fmul)     (inst pc '(fadd)))
          ((equal op 'frem)     (inst pc '(fadd)))
          ((equal op 'fstore_0) (inst pc '(fstore 0)))
          ((equal op 'fstore_1) (inst pc '(fstore 1)))          
          ((equal op 'fstore_2) (inst pc '(fstore 2)))          
          ((equal op 'fstore_3) (inst pc '(fstore 3)))
          ((equal op 'fsub)     (inst pc '(fadd)))
          ((equal op 'i2b)      (inst pc '(ineg)))
          ((equal op 'i2c)      (inst pc '(ineg)))
          ((equal op 'i2s)      (inst pc '(ineg)))
          ((equal op 'iand)      (inst pc '(iadd)))
          ((equal op 'iconst_0) (inst pc '(sipush 0)))
          ((equal op 'iconst_1) (inst pc '(sipush 1)))
          ((equal op 'iconst_2) (inst pc '(sipush 2)))
          ((equal op 'iconst_3) (inst pc '(sipush 3)))
          ((equal op 'iconst_4) (inst pc '(sipush 4)))
          ((equal op 'iconst_5) (inst pc '(sipush 5)))
          ((equal op 'iconst_m1) (inst pc '(sipush -1)))
          ((equal op 'idiv)      (inst pc '(iadd)))
          ((equal op 'if_acmpne) (inst pc (list 'if_acmpeq (arg1 inst))))
          ((equal op 'if_icmpge) (inst pc (list 'if_icmpeq (arg1 inst))))
          ((equal op 'if_icmpgt) (inst pc (list 'if_icmpeq (arg1 inst))))
          ((equal op 'if_icmple) (inst pc (list 'if_icmpeq (arg1 inst))))
          ((equal op 'if_icmplt) (inst pc (list 'if_icmpeq (arg1 inst))))
          ((equal op 'if_icmpne) (inst pc (list 'if_icmpeq (arg1 inst))))
          ((equal op 'ifge)      (inst pc (list 'ifeq (arg1 inst))))
          ((equal op 'ifgt)      (inst pc (list 'ifeq (arg1 inst))))
          ((equal op 'ifle)      (inst pc (list 'ifeq (arg1 inst))))
          ((equal op 'iflt)      (inst pc (list 'ifeq (arg1 inst))))
          ((equal op 'ifne)      (inst pc (list 'ifeq (arg1 inst))))
          ((equal op 'ifnull)    (inst pc (list 'ifnonnull (arg1 inst))))
          ((equal op 'iload_0) (inst pc '(iload 0)))
          ((equal op 'iload_1) (inst pc '(iload 1)))
          ((equal op 'iload_2) (inst pc '(iload 2)))
          ((equal op 'iload_3) (inst pc '(iload 3)))
          ((equal op 'imul)      (inst pc '(iadd)))
          ((equal op 'ior)       (inst pc '(iadd)))
          ((equal op 'irem)      (inst pc '(iadd)))
          ((equal op 'ishl)      (inst pc '(iadd)))
          ((equal op 'ishr)      (inst pc '(iadd)))
          ((equal op 'istore_0) (inst pc '(istore 0)))
          ((equal op 'istore_1) (inst pc '(istore 1)))          
          ((equal op 'istore_2) (inst pc '(istore 2)))          
          ((equal op 'istore_3) (inst pc '(istore 3)))
          ((equal op 'isub)      (inst pc '(iadd)))
          ((equal op 'iushr)    (inst pc '(iadd)))
          ((equal op 'ixor)      (inst pc '(iadd)))
          ((equal op 'land)      (inst pc '(ladd)))
          ((equal op 'lconst_1)      (inst pc '(lconst_0)))
          ((equal op 'ldc_w)      (inst pc (list 'ldc (arg1 inst))))
          ((equal op 'ldiv)       (inst pc '(ladd)))
          ((equal op 'lload_0) (inst pc '(lload 0)))
          ((equal op 'lload_1) (inst pc '(lload 1)))
          ((equal op 'lload_2) (inst pc '(lload 2)))
          ((equal op 'lload_3) (inst pc '(lload 3)))
          ((equal op 'lmul)      (inst pc '(ladd)))
          ((equal op 'lor)       (inst pc '(ladd)))
          ((equal op 'lrem)      (inst pc '(ladd)))
          ((equal op 'lshr)      (inst pc '(lshl)))
          ((equal op 'lstore_0) (inst pc '(lstore 0)))
          ((equal op 'lstore_1) (inst pc '(lstore 1)))          
          ((equal op 'lstore_2) (inst pc '(lstore 2)))          
          ((equal op 'lstore_3) (inst pc '(lstore 3)))
          ((equal op 'lsub)      (inst pc '(ladd)))
          ((equal op 'lushr)    (inst pc '(lshl)))
          ((equal op 'lxor)      (inst pc '(ladd)))
          ((equal op 'monitorexit) (inst pc '(monitorenter)))
          (t inst))))


;  utitlies for change sigstate

;--- prefix ---
;
; return the stack after pop out 
; all the matching type. 
;--

(defun  convertIfInt (type)
  (cond ((equal type 'byte) 'int)
        ((equal type 'short) 'int)
        ((equal type 'boolean) 'int)
        (t type)))
      
;;; not sure how they avoided 'short 'byte, etc.

;;; it is a global invariant that they never test for short and byte. 
;;; when execute-aaload, they push the element type
;;; when execute-saload, they push INT. 

;--
(defun isMatchingType (Type Stack Env)
  (cond ((equal (sizeOf Type) 1)  
        ;; (isAssignable (convertIfInt (top Stack))
        ;;               (convertIfInt Type) Env))
        ;; not the same as prolog
        ;; version. hanbing April. 02
        ;;
        ;; WHY??? Wed Nov 19 01:15:37 2003
        ;;
        ;; 
        (isAssignable (top Stack)
                       Type Env))

        ((equal (sizeOf Type) 2)
         ;; need a fix here. to match with DJVM's assumption. 
         ;; 
         ;;(and (equal (top (pop stack)) 'topx) 
         ;;     ;; top stack is the signature the one below 
         ;;     ;; it have to be a top. 
         ;;     (isAssignable (top stack) Type Env)))
         ;;  11/05/03  ;; Thu Dec 16 23:06:10 2004
         ;; We shall fix the untag!!! 
         ;; 
         (and (equal (top stack) 'topx)
              ;; top stack is the signature the one below 
              ;; it have to be a top. 
              (isAssignable (top (pop stack)) Type Env)))
        (t nil)))

(defun theMatchingType (type Stack)
  (cond ((equal (sizeOf type) 1) (top stack))
        ;; ((equal (sizeOf type) 2) (top stack)) ;; Thu Dec 16 23:18:42 2004
        ((equal (sizeOf type) 2) (top (pop stack)))
        (t nil)))


(defun popMatchingType (Type Stack)
  (cond ((equal (sizeOf Type) 1) (pop Stack))
        ((equal (sizeOf Type) 2) (pop (pop Stack)))
        (t nil)));; impossible 


;--
(defun CanPop1 (prefix Stack Env) 
  (if (endp prefix)
      t
    (if (endp Stack)
        nil;; can't pop
      (and (isMatchingType (car prefix) Stack Env)
           (canPop1 (cdr prefix) (popMatchingType (car prefix) Stack) Env)))))

(defun CanPop (Env StackFrame prefix)
  (CanPop1 prefix (frameStack StackFrame) Env))



(defun PopMatchingList1 (prefix Stack)
  (if (endp prefix)
      Stack
    (if (endp Stack)
        nil;; make sure it won't cause hard error.
      ;; indicate undefined 
      (PopMatchingList1 (cdr prefix) 
                        (PopMatchingType (car prefix) Stack)))))

;; because in some check-xxx we use this it (let* ((...)) body)
;; it may get evaluated before we know CanPop1 prefix...

(defun PopMatchingList (prefix curFrame)
  (make-sig-frame 
   (frameLocals curFrame)
   (PopMatchingList1 prefix (frameStack curFrame))
   (frameFlags curFrame)))

;--
(defun pushOperandStack (type stack) 
  (cond ((equal type 'void)  stack)
        ((equal (sizeOf type) 2) (push 'topx (push Type Stack)))
        ;; ((equal (sizeOf type) 2) (push Type (push 'topx Stack)))
        ;;  11/05/03  fix to match djvm. FIX to match the STACK MAP!! 
        
        ((equal (sizeOf type) 1) (push type Stack))
        (t nil)));; impossible


(defun operandStackHasLegalLength (env operandstack) 
  (let ((MaxStack (maxStackEnvironment env)))
    (<= (len operandStack) MaxStack)))

;---
(defun validTypeTransition (Env ExpectedTypesOnStack ResultType curFrame)
  (let ((InputOperandStack (frameStack curFrame)))
    (and (canPop1 ExpectedTypesOnStack InputOperandStack Env)
         (operandStackHasLegalLength Env (pushOperandStack ResultType
                                                           (popMatchingList1
                                                            ExpectedTypesOnStack InputOperandStack))))))


(defun TypeTransition (env toBePoped  ResultType curFrame)
  (declare (ignore env))
  (let ((locals (frameLocals curFrame))
        (stack  (frameStack  curFrame))
        (flags  (frameFlags  curFrame)))
    (make-sig-frame locals 
                    (pushOperandStack ResultType 
                                      (popMatchingList1 toBePoped stack))
                    flags)))


(defun exceptionStackFrame (curFrame)
  (let ((locals (frameLocals curFrame))
        (flags  (frameFlags  curFrame)))
    (make-sig-frame locals nil flags)))


;-- 
(defun nth1OperandStackExist (n curFrame)
  (let ((operandStack (frameStack curFrame)))
    (and (<= n (len operandStack))
         (<= 0 n))))

;; (defun nth1OperandStackIs (n curFrame)
;;   (let ((operandStack (frameStack curFrame)))
;;     (if (nth1OperandStackExist n curFrame)
;;         (nth (- n 1) operandStack)
;;       nil)));; indicate undefined

(defun nth1OperandStackIs (n curFrame)
  (let ((operandStack (frameStack curFrame)))
    (nth (- n 1) operandStack)))

;; move the check into the guard!!



(defun nthLocalsExist (n type curFrame)
  (let ((Locals (frameLocals curFrame)))
    (and (integerp n)
         (<= 0 n)
         (if (equal (sizeof type) 2)
             (< (+ n 1) (len Locals))
           (< n (len Locals))))))
;;
;; more problem with safe index. n > 0 is aways true. 
;; because local is accessed with unsign-int-fix
;;
;; Mon Mar 29 12:26:40 2004

;--
; assuming curFrame well formed
; assuming wellformed load instruction ensure index is not negative

(defun safe-nth (index lst)
  (nth index lst))

;; (defun safe-nth (index lst)
;;   (if (and (< index (len lst))
;;            (<= 0 index))
;;       (nth index lst)
;;     nil));; undefined

;; problem 0<= index test??

(defun loadIsTypeSafe (env index type curFrame)
  (let* ((locals (frameLocals curFrame))
         (ActualType (safe-nth index locals)))
    (and (nthLocalsExist index type curFrame)
         (isAssignable ActualType Type env)
         (validTypeTransition env nil ActualType curFrame))))

(defun do-load (env index type curFrame)
  (declare (ignore type))
  (let* ((locals (frameLocals curFrame))
         (ActualType (nth index locals)))
    (TypeTransition env nil ActualType curFrame)))

;;; WE need to fix the load of size two 
;;; 
;;;


;--
(defun storeIsTypeSafe (env index type curFrame)
  (let* ((stack  (frameStack  curFrame)))
    (and (nthLocalsExist index type curFrame)
         (isMatchingType type stack env))))

;;
;; error here. nthLocalExists depends on type. if size 2 we expect two slots.  
;; hanbing April 2003
;;

(defun modifyPreIndexVariable (type)
  (cond ((equal (sizeOf type) 1) type)
        ((equal (sizeOf type) 2) 'topx)))

(defun modifyLocalVariable (index type locals)
  (if (endp locals)
      nil
    (cond ((< 1 index) 
           (cons (car locals) (modifyLocalVariable (- index 1) type
                                                   (cdr locals))))
          ((equal index 1) (cons (modifyPreIndexVariable (car locals))
                                 ;; if we happen to write into a middle of a
                                 ;; two slot value We need to destroy the older
                                 ;; value. Tue Feb  1 14:01:19 2005
                                 (modifyLocalVariable 0 type (cdr
                                                              locals))))
          ((equal index 0)
           (cond ((equal (sizeOf type) 1) (cons type (cdr locals)))
                 ((equal (sizeOf type) 2) (cons type (cons 'topx (cddr
                                                                 locals))))
                 (t nil)));; impossible
          ;; problem here: Tue Feb  1 13:55:57 2005. We put (type 'topx ...) to
          ;; represent two slot. However in opstack, we use ('topx type) to
          ;; represent LONG! 
          ;; type list assignable needs to be redefined. 
          ;;
          (t nil))))
;--- 
;; *17* Note: For locals, we don't check whether FrameSize is
;; exceeded? Why? Because in Prolog version, we know the locals is
;; expand to list of length FrameSize in MethodInitialStackFrame
            

(defun do-store (env index type curFrame)
  (declare (ignore env))
  (let* ((locals (frameLocals curFrame))
         (stack  (frameStack curFrame))
         (flags  (frameFlags curFrame))
         (ActualType (theMatchingType type stack)))
    (make-sig-frame (modifyLocalVariable index ActualType locals)
                    (popMatchingType type stack)
                    flags)))

;;;; Thu Dec 16 23:18:03 2004. ActualType .. problem 

;--- 
;  
;    aaload :   
;
;  Assumption: all input parameter are well formed.
;              check. Env and curFrame


(defun ArrayElementType (ArrayType)
  (if (equal ArrayType 'null)
      'null
    (cadr ArrayType)))

;; we will prove guard!! 

;; (defun ArrayElementType (ArrayType)
;;     (if (isArrayType ArrayType);; to guard against hard error
;;       (cadr ArrayType))
;;     nil));; indicate undefined
       

(defun check-aaload (inst env curFrame) 
  (declare (ignore inst))
  (mylet* ((ArrayType (nth1OperandStackIs 2 curFrame))
           (ElementType (ArrayElementType ArrayType)))
    (and ;; (nth1OperandStackExist 2 curFrame) ;; Sun Mar 28 20:26:47 2004
         ;; part of the validTypeTransition!!
         ;; (or (isNullType arrayType)    
         ;;     (isArrayType ArrayType)) ;; BCV does not assert this?
         ;; This is not necessary.
         ;; should be derivable from validTypeTransition 'int (array ...)
         ;; Sun Mar 28 17:02:37 2004. Removed. Proof still go through.
         (validtypetransition env  
                              '(int (array (class "java.lang.Object")))
                              ElementType
                              curFrame))))


;; (defun check-aaload (inst env curFrame) 
;;   (declare (ignore inst))
;;   (mylet* ((ArrayType (nth1OperandStackIs 2 curFrame))
;;            (ElementType (ArrayElementType ArrayType)))
;;     (and (nth1OperandStackExist 2 curFrame)
;;          (or (isNullType arrayType)  
;;              (isArrayType ArrayType)) ;; bcv assert down there ...
;;          (validtypetransition env  
;;                               '(int (array (class "java.lang.Object")))
;;                               ElementType
;;                               curFrame))))

;;
;; Allow 
;;
;; execute-XXX return a pair of StackFrame (normal . exception)



(defun execute-aaload (inst env curFrame)
  (declare (ignore inst))
  (mylet* ((ArrayType (nth1OperandStackIs 2 curFrame))
           (ElementType (ArrayElementType ArrayType)))
    (mv  (TypeTransition env
                         '(int (array (class "java.lang.Object")))
                         ElementType
                         curFrame)
         (exceptionStackFrame curFrame))))

;--- 
(defun check-aastore (inst env curFrame)
  (declare (ignore inst))
  (canPop Env curFrame 
          '((class "java.lang.Object") int (array (class
                                                   "java.lang.Object")))))
;; type check is at runtime. 

(defun execute-aastore (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env 
                      '((class "java.lang.Object") 
                        int 
                        (array (class "java.lang.Object")))
                      'void;; use void to indicate push nothing.
                      curFrame)
      (exceptionStackFrame curFrame)))

;---                                    ;; nothing to do with offset 
(defun check-aconst_null (inst env curFrame);; those instruction has
  (declare (ignore inst))
  (validTypeTransition  env  nil 'null curFrame))

(defun execute-aconst_null (inst env curFrame)
  (declare (ignore inst))
  (mv  (TypeTransition env
                       nil
                       'null
                       curFrame)
       (exceptionStackFrame curFrame)))

;--- ;; assume (aload <arg1>)
(defun check-aload (inst env curFrame)
  (let ((index (arg1 inst)))
    (loadIsTypeSafe env index 'reference curFrame)))

;;;
;;; do we need to check wff-aload? 
;;; Shall we assume that wff-aload!! ;; Wed May 18 13:42:48 2005
;;;

(defun execute-aload (inst env curFrame)
  (mylet* ((index (arg1 inst)))
          (mv (do-load env index 'reference curFrame)
              (exceptionStackFrame curFrame))))

;;--- 
; missing well formed check ... 
; do-load may need to unsign-int fix it.
;;---
 

(defun check-anewarray (inst env curFrame)
  (mylet* ((cp   (arg1 inst)))
          (and (or (isClassType CP)
                   (isArrayType CP))
               (validTypeTransition env '(int) (list 'array CP) curFrame))))

(defun execute-anewarray (inst env curFrame)
  (mylet* ((cp (arg1 inst)))
          (mv (TypeTransition env '(int) (list 'array CP) curFrame)
              (exceptionStackFrame curFrame))))

;---

(defun check-areturn (inst env curFrame)
  (declare (ignore inst))
  (let* ((method (methodEnvironment env))
         (returnType (methodReturnType method)))
    (and (isAssignable returnType 'reference env)
         (canPop env curFrame (list returnType)))))

;; note: uninitialized is not assignable to any Java type.

(defun execute-areturn (inst env curFrame)
  (declare (ignore inst env))
  (mv 'aftergoto 
      (exceptionStackFrame curFrame)))

;--- 

(defun check-arraylength (inst env curFrame)
  (declare (ignore inst))
  (let ((ArrayType (nth1OperandStackIs 1 curFrame)))
    (and (nth1OperandStackExist 1 curFrame)
         (isArrayType ArrayType)
         (validTypeTransition env '(topx) 'int curFrame))))

(defun execute-arraylength (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(topx) 'int curFrame)
      (exceptionStackFrame curFrame)))
;---

(defun check-astore (inst env curFrame)
  (let ((index (arg1 inst)))
    (storeIsTypeSafe env index 'reference curFrame)))

(defun execute-astore (inst env curFrame)
  (let ((index (arg1 inst)))
    (mv (do-store env index 'reference curFrame)
        (exceptionStackFrame curFrame))))
;---
(defun check-athrow (inst env curFrame)
  (declare (ignore inst))
  (canPop env curFrame '((class "java.lang.Throwable"))))

(defun execute-athrow (inst env curFrame)
  (declare (ignore inst env))
  (mv 'aftergoto 
      (exceptionStackFrame curFrame)))
;---

(defun isSmallArray (type)
  (or (equal type 'null)
      (equal type '(array byte))
      ;;  (equal type '(array short))
      (equal type '(array boolean))))
  
;--
(defun check-baload (inst env curFrame)
  (declare (ignore inst))
  (let ((Array (nth1OperandStackIs 2 curFrame)))
    (and (nth1OperandStackExist 2 curFrame)
         (isSmallArray Array)
         (validTypeTransition env '(int topx) 'int  curFrame))))

(defun execute-baload (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition  env '(int topx) 'int  curFrame)
      (exceptionStackFrame curFrame)))

;---

(defun check-bastore (inst env curFrame)
  (declare (ignore inst))
  (let ((Array (nth1OperandStackIs 3 curFrame)))
    (and (nth1OperandStackExist 3 curFrame)
         (isSmallArray Array)
         (canPop env curFrame '(int int topx)))))

;; after ensure isSmallArray,  use top here is all right. refer to
;; original comments.

(defun execute-bastore (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(int int topx) 'void curFrame)
      (exceptionStackFrame curFrame)))

;---
(defun check-caload (inst env curFrame)
  (declare (ignore inst))
  (and (nth1OperandStackExist 2 curFrame)
       (validTypeTransition env '(int (array char)) 'int  curFrame)))

(defun execute-caload (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition  env '(int (array char)) 'int  curFrame)
      (exceptionStackFrame curFrame)))

;---

(defun check-castore (inst env curFrame)
  (declare (ignore inst))
  (and (nth1OperandStackExist 3 curFrame)
       (canPop env curFrame '(int int (array char)))))

(defun execute-castore (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(int int (array char)) 'void curFrame)
      (exceptionStackFrame curFrame)))

;---
  
(defun check-checkcast (inst env curFrame)
  (let ((CP (arg1 inst)))
    (and (or (isClassType CP)
             (isArrayType CP))
         (validTypeTransition env '((class "java.lang.Object")) 
                              CP   curFrame)))) 
         
       
(defun execute-checkcast (inst env curFrame)
  (let ((CP (arg1 inst)))
    (mv (TypeTransition env '((class "java.lang.Object")) 
                        CP curFrame)
        (exceptionStackFrame curFrame))))

;---
(defun check-d2f (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(double) 'float curFrame))

(defun execute-d2f (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(double) 'float curFrame)
      (exceptionStackFrame curFrame)))
;--

(defun check-d2i (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(double) 'int curFrame))

(defun execute-d2i (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(double) 'int curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-d2l (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(double) 'long curFrame))

(defun execute-d2l (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(double) 'long curFrame)
      (exceptionStackFrame curFrame)))
;--

(defun check-dadd (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(double double) 'double curFrame))

(defun execute-dadd (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(double double) 'double curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-daload (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(int (array double)) 'double curFrame))

(defun execute-daload (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(int (array double)) 'double curFrame)
      (exceptionStackFrame curFrame)))
;--

(defun check-dastore (inst env curFrame)
  (declare (ignore inst))
  (canPop env curFrame '(double int (array double))))

(defun execute-dastore (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(double int (array double)) 'void curFrame)
      (exceptionStackFrame curFrame)))


;--
(defun check-dcmpg (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(double double) 'int curFrame))

(defun execute-dcmpg (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(double double) 'int curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-dconst_0 (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env nil 'double curFrame))

(defun execute-dconst_0 (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env nil 'double curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-dload (inst env curFrame)
  (let ((index (arg1 inst)))
    (loadIsTypeSafe env index 'double curFrame)))


(defun execute-dload (inst env curFrame)
  (let* ((index (arg1 inst)))
    (mv (do-load env index 'double curFrame)
        (exceptionStackFrame curFrame))))
;--
(defun check-dneg (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(double) 'double curFrame))

(defun execute-dneg (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(double) 'double curFrame)
      (exceptionStackFrame curFrame)))

;--
(defun check-dreturn (inst env curFrame)
  (declare (ignore inst))
  (let ((method (methodEnvironment env)))
    (and (equal (methodReturnType method) 'double)
         (canPop env curFrame '(double)))))

(defun execute-dreturn (inst env curFrame)
  (declare (ignore inst env))
  (mv 'aftergoto 
      (exceptionStackFrame curFrame)))
;--
(defun check-dstore (inst env curFrame)
  (let ((index (arg1 inst)))
    (storeIsTypeSafe env index 'double curFrame)))

(defun execute-dstore (inst env curFrame)
  (let ((index (arg1 inst)))
    (mv (do-store env index 'double curFrame)
        (exceptionStackFrame curFrame))))
;--
(defun isTopCategory1 (stack)
  (let ((type (top stack)))
    (and (not (equal type 'topx))
         (equal (sizeOf type) 1))))

(defun category1top (stack)
  (top stack))

(defun popCategory1 (stack)
  (pop stack))

(defun canSafelyPush (env stack type)
  (operandStackHasLegallength env (pushOperandStack type stack)))


(defun check-dup (inst env curFrame)
  (declare (ignore inst))
  (let ((stack (frameStack curFrame)))
    (and (nth1OperandStackExist 1 curFrame)
         (isTopCategory1 stack)
         (canSafelyPush env stack (category1top stack)))))

(defun execute-dup (inst env curFrame)
  (declare (ignore inst env))
  (let ((stack (frameStack curFrame))
        (locals (frameLocals curFrame))
        (flags  (frameFlags curFrame)))
    (mv (make-sig-frame locals 
                        (pushOperandStack 
                         (category1top stack) stack) flags)
        (exceptionStackFrame curFrame))))
;--  

(defun isTopCategory2 (stack)
  (and (equal (top stack) 'topx)
       (equal (sizeOf (top (pop stack))) 2)))

(defun category2top (stack)
  (top (pop stack)))

(defun popCategory2 (stack)
  (pop (pop stack)))

(defun pushList (types stack)
  (if (endp types)
      stack
    (pushList (cdr types) (pushOperandStack (car types) stack))))

(defun canSafelyPushList (env stack types)
  (operandStackHasLegalLength env (pushList types stack)))


(defun check-dup_x1 (inst env curFrame)
  (declare (ignore inst))
  (let ((stack (frameStack curFrame)))
    (and (nth1OperandStackExist 2 curFrame)
         (isTopCategory1 stack)
         (isTopCategory1 (pop Stack))
         (canSafelyPushList env (popCategory1 (popCategory1 stack)) 
                            (list (category1top stack) 
                                  (category1top (popCategory1 stack))
                                  (category1top stack))))))
                              

(defun execute-dup_x1 (inst env curFrame)
  (declare (ignore inst env))
  (let ((stack (frameStack curFrame))
        (locals (frameLocals curFrame))
        (flags  (frameFlags curFrame)))
    (mv (make-sig-frame locals 
                        (pushList 
                         (list (category1top stack) 
                               (category1top (popCategory1 stack))
                               (category1top stack))
                         (popCategory1 (popCategory1 stack)))
                        flags)
        (exceptionStackFrame curFrame))))
;--
; the (let* part get evaluated and potentially cause hard error
; we replace the top and pop with guarded version.    

(defun is_dup_x2_form1 (env stack)
  (let* ((Type1  (category1top  stack))
         (Stack1 (popCategory1 stack))
         (Type2  (category1top  Stack1))
         (Stack2 (popCategory1 Stack1))
         (Type3  (category1top Stack2))
         (Rest   (popCategory1 Stack2)))
    (and (isTopCategory1 stack)
         (isTopCategory1 Stack1)
         (isTopCategory1 Stack2)
         (canSafelyPushList env Rest (list type1 type3 type2
                                           type1)))))

(defun do_dup_x2_form1 (env curFrame)
  (declare (ignore env))
  (let* ((stack  (frameStack curFrame))
         (locals (frameLocals curFrame))
         (flags  (frameFlags curFrame))
         (Type1  (category1top  stack))
         (Stack1 (popCategory1 stack))
         (Type2  (category1top  Stack1))
         (Stack2 (popCategory1 Stack1))
         (Type3  (category1top Stack2))
         (Rest   (popCategory1 Stack2)))
    (mv (make-sig-frame locals
                        (pushList 
                         (list type1 type3 type2 type1) rest)
                        flags)
        (exceptionStackFrame curFrame))))


(defun is_dup_x2_form2 (env stack)
  (let* ((Type1  (category1top  stack))
         (Stack1 (popCategory1 stack))
         (Type2  (category2top  Stack1))
         (Rest   (popCategory2 Stack1)))
    (and (isTopCategory1 stack)
         (isTopCategory2 Stack1)
         (canSafelyPushList env Rest (list type1 type2 type1)))))


(defun do_dup_x2_form2 (env curFrame)
  (declare (ignore env))
  (let* ((stack  (frameStack curFrame))
         (locals (frameLocals curFrame))
         (flags  (frameFlags curFrame))
         (Type1  (category1top  stack))
         (Stack1 (popCategory1 stack))
         (Type2  (category2top  Stack1))
         (rest (popCategory2 Stack1)))
    (mv (make-sig-frame locals
                        (pushList 
                         (list type1 type2 type1) rest)
                        flags)
        (exceptionStackFrame curFrame))))

;; I should have let those function to return a pair (t . return) 
;; now I have to write two functions.
         
(defun check-dup_x2 (inst env curFrame)
  (declare (ignore inst))
  (let ((stack (frameStack curFrame)))
    (and (nth1OperandStackExist 3 curFrame)
         (or (is_dup_x2_form1 env stack)
             (is_dup_x2_form2 env stack)))))
                              
(defun execute-dup_x2 (inst env curFrame)
  (declare (ignore inst))
  (let ((stack (frameStack curFrame)))
    (cond ((is_dup_x2_form1 env stack)
           (do_dup_x2_form1 env curFrame))
          ((is_dup_x2_form2 env stack)
           (do_dup_x2_form2 env curFrame))
          (t (mv nil nil)))));; impossible.
        
;--

(defun is_dup2_form1 (env stack)
  (let* ((Type1  (category1top  stack))
         (Stack1 (popCategory1 stack))
         (Type2  (category1top  Stack1)))
    (and (isTopCategory1 stack)
         (isTopCategory1 Stack1)
         (canSafelyPushList env stack (list type2 type1)))))

(defun do_dup2_form1 (env curFrame)
  (declare (ignore env))
  (let* ((stack  (frameStack curFrame))
         (locals (frameLocals curFrame))
         (flags  (frameFlags curFrame))
         (Type1  (category1top  stack))
         (Stack1 (popCategory1 stack))
         (Type2  (category1top  Stack1)))
    (mv (make-sig-frame locals
                        (pushList 
                         (list type2 type1) stack)
                        flags)
        (exceptionStackFrame curFrame))))
                          


(defun is_dup2_form2 (env stack)
  (let* ((Type1  (category2top  stack))
         (Rest   (popCategory2  stack)))
    (and (isTopCategory2 stack)
         (canSafelyPush env Rest Type1))))


(defun do_dup2_form2 (env curFrame)
  (declare (ignore env))
  (let* ((stack  (frameStack curFrame))
         (locals (frameLocals curFrame))
         (flags  (frameFlags curFrame))
         (Type1  (category2top  stack)))
    (mv (make-sig-frame locals
                        (pushOperandStack type1 stack)
                        flags)
        (exceptionStackFrame curFrame))))    


(defun check-dup2 (inst env curFrame)
  (declare (ignore inst))
  (let ((stack (frameStack curFrame)))
    (and (nth1OperandStackExist 2 curFrame)
         (or (is_dup2_form1 env stack)
             (is_dup2_form2 env stack)))))
                              
(defun execute-dup2 (inst env curFrame)
  (declare (ignore inst))
  (let ((stack (frameStack curFrame)))
    (cond ((is_dup2_form1 env stack)
           (do_dup2_form1 env curFrame))
          ((is_dup2_form2 env stack)
           (do_dup2_form2 env curFrame))
          (t (mv nil nil)))));; impossible.
                 
;--          

(defun is_dup2_x1_form1 (env stack)
  (let* ((Type1  (category1top  stack))
         (Stack1 (popCategory1 stack))
         (Type2  (category1top  Stack1))
         (Stack2 (popCategory1 Stack1))
         (Type3  (category1top Stack2))
         (rest   (popCategory1 Stack2))) 
    (and (isTopCategory1 stack)
         (isTopCategory1 Stack1)
         (isTopCategory1 Stack2)
         (canSafelyPushList env rest (list type2 type1 type3 type2 type1)))))

(defun do_dup2_x1_form1 (env curFrame)
  (declare (ignore env))
  (let* ((stack  (frameStack curFrame))
         (locals (frameLocals curFrame))
         (flags  (frameFlags curFrame))
         (Type1  (category1top  stack))
         (Stack1 (popCategory1 stack))
         (Type2  (category1top  Stack1))
         (Stack2 (popCategory1 Stack1))
         (Type3  (category1top Stack2))
         (rest   (popCategory1 Stack2))) 
    (mv (make-sig-frame locals
                        (pushList 
                         (list type2 type1 type3 type2 type1) rest)
                        flags)
        (exceptionStackFrame curFrame))))
                          


(defun is_dup2_x1_form2 (env stack)
  (let* ((Type1  (category2top  stack))
         (Stack1 (popCategory2 stack))
         (Type2  (category1top Stack1))
         (rest   (popCategory1 Stack1)))
    (and (isTopCategory2 stack)
         (isTopCategory1 Stack1)
         (canSafelyPushList env Rest (list Type1 Type2 Type1)))))

(defun do_dup2_x1_form2 (env curFrame)
  (declare (ignore env))
  (let* ((stack  (frameStack curFrame))
         (locals (frameLocals curFrame))
         (flags  (frameFlags curFrame))
         (Type1  (category2top  stack))
         (Stack1 (popCategory2  stack))
         (Type2  (category1top Stack1))
         (rest   (popCategory1 Stack1)))
    (mv (make-sig-frame locals
                        (pushList (list type1 type2 type1) rest)
                        flags)
        (exceptionStackFrame curFrame))))

(defun check-dup2_x1 (inst env curFrame)
  (declare (ignore inst))
  (let ((stack (frameStack curFrame)))
    (and (nth1OperandStackExist 3 curFrame)
         (or (is_dup2_form1 env stack)
             (is_dup2_form2 env stack)))))
                              
(defun execute-dup2_x1 (inst env curFrame)
  (declare (ignore inst))
  (let ((stack (frameStack curFrame)))
    (cond ((is_dup2_x1_form1 env stack)
           (do_dup2_x1_form1 env curFrame))
          ((is_dup2_x1_form2 env stack)
           (do_dup2_x1_form2 env curFrame))
          (t (mv nil nil)))));; impossible.
;--          

(defun is_dup2_x2_form1 (env stack)
  (let* ((Type1  (category1top  stack))
         (Stack1 (popCategory1 stack))
         (Type2  (category1top  Stack1))
         (Stack2 (popCategory1 Stack1))
         (Type3  (category1top Stack2))
         (Stack3 (popCategory1 Stack2))
         (Type4  (category1top Stack3))
         (rest   (popCategory1 Stack3)))
    (and (isTopCategory1 stack)
         (isTopCategory1 Stack1)
         (isTopCategory1 Stack2)
         (isTopCategory1 stack3)
         (canSafelyPushList env rest (list type2 type1 type4 type3 type2 type1)))))

(defun do_dup2_x2_form1 (env curFrame)
  (declare (ignore env))
  (let* ((stack  (frameStack curFrame))
         (locals (frameLocals curFrame))
         (flags  (frameFlags curFrame))
         (Type1  (category1top  stack))
         (Stack1 (popCategory1 stack))
         (Type2  (category1top  Stack1))
         (Stack2 (popCategory1 Stack1))
         (Type3  (category1top Stack2))
         (Stack3 (popCategory1 Stack2))
         (Type4  (category1top Stack3))
         (rest   (popCategory1 Stack3))) 
    (mv (make-sig-frame locals
                        (pushList 
                         (list type2 type1 type4 type3 type2 type1) rest)
                        flags)
        (exceptionStackFrame curFrame))))



(defun is_dup2_x2_form2 (env stack)
  (let* ((Type1  (category2top  stack))
         (Stack1 (popCategory2  stack))
         (Type2  (category1top Stack1))
         (Stack2 (popCategory1 Stack1))
         (Type3  (category1top Stack2))
         (rest   (popCategory1 Stack2)))
    (and (isTopCategory2 stack)
         (isTopCategory1 Stack1)
         (isTopCategory1 Stack2)
         (canSafelyPushList env Rest (list Type1 Type3 Type2 Type1)))))

(defun do_dup2_x2_form2 (env curFrame)
  (declare (ignore env))
  (let* ((stack  (frameStack curFrame))
         (locals (frameLocals curFrame))
         (flags  (frameFlags curFrame))
         (Type1  (category2top  stack))
         (Stack1 (popCategory2  stack))
         (Type2  (category1top    Stack1))
         (Stack2 (popCategory1 Stack1))
         (Type3  (category1top Stack2))
         (rest   (popCategory1 Stack2)))
    (mv (make-sig-frame locals
                        (pushList (list type1 type3 type2 type1) rest)
                        flags)
        (exceptionStackFrame curFrame))))


(defun is_dup2_x2_form3 (env stack)
  (let* ((Type1  (category1top  stack))
         (Stack1 (popCategory1 stack))
         (Type2  (category1top  Stack1))
         (Stack2 (popCategory1 Stack1))
         (Type3  (category2top Stack2))
         (rest   (popCategory2 Stack2))) 
    (and (isTopCategory1 stack)
         (isTopCategory1 Stack1)
         (isTopCategory2 Stack2)
         (canSafelyPushList env rest (list type2 type1 type3 type2 type1)))))

(defun do_dup2_x2_form3 (env curFrame)
  (declare (ignore env))
  (let* ((stack  (frameStack curFrame))
         (locals (frameLocals curFrame))
         (flags  (frameFlags curFrame))
         (Type1  (category1top  stack))
         (Stack1 (popCategory1 stack))
         (Type2  (category1top  Stack1))
         (Stack2 (popCategory1 Stack1))
         (Type3  (category2top Stack2))
         (rest   (popCategory2 Stack2))) 
    (mv (make-sig-frame locals
                        (pushList 
                         (list type2 type1 type3 type2 type1) rest)
                        flags)
        (exceptionStackFrame curFrame))))
                          


(defun is_dup2_x2_form4 (env stack)
  (let* ((Type1  (category2top  stack))
         (Stack1 (popCategory2 stack))
         (Type2  (category2top  Stack1))
         (Rest   (popCategory2 Stack1)))
    (and (isTopCategory2 stack)
         (isTopCategory2 Stack1)
         (canSafelyPushList env Rest (list type1 type2 type1)))))


(defun do_dup2_x2_form4 (env curFrame)
  (declare (ignore env))
  (let* ((stack  (frameStack curFrame))
         (locals (frameLocals curFrame))
         (flags  (frameFlags curFrame))
         (Type1  (category2top  stack))
         (Stack1 (popCategory2 stack))
         (Type2  (category2top  Stack1))
         (rest (popCategory2 Stack1)))
    (mv (make-sig-frame locals
                        (pushList 
                         (list type1 type2 type1) rest)
                        flags)
        (exceptionStackFrame curFrame))))

(defun check-dup2_x2 (inst env curFrame)
  (declare (ignore inst))
  (let ((stack (frameStack curFrame)))
    (and (nth1OperandStackExist 4 curFrame)
         (or (is_dup2_x2_form1 env stack)
             (is_dup2_x2_form2 env stack)
             (is_dup2_x2_form3 env stack)
             (is_dup2_x2_form4 env stack)))))
                              
(defun execute-dup2_x2 (inst env curFrame)
  (declare (ignore inst))
  (let ((stack (frameStack curFrame)))
    (cond ((is_dup2_x2_form1 env stack)
           (do_dup2_x2_form1 env curFrame))
          ((is_dup2_x2_form2 env stack)
           (do_dup2_x2_form2 env curFrame))
          ((is_dup2_x2_form3 env stack)
           (do_dup2_x2_form3 env curFrame))
          ((is_dup2_x2_form4 env stack)
           (do_dup2_x2_form4 env curFrame))
          (t (mv nil nil)))));; impossible.
;--          

;---
(defun check-f2d (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(float) 'double curFrame))

(defun execute-f2d (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(float) 'double curFrame)
      (exceptionStackFrame curFrame)))
;--

(defun check-f2i (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(float) 'int curFrame))

(defun execute-f2i (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(float) 'int curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-f2l (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(float) 'long curFrame))

(defun execute-f2l (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(float) 'long curFrame)
      (exceptionStackFrame curFrame)))
;--

(defun check-fadd (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(float float) 'float curFrame))

(defun execute-fadd (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(float float) 'float curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-faload (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(int (array float)) 'float curFrame))

(defun execute-faload (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(int (array float)) 'float curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-fastore (inst env curFrame)
  (declare (ignore inst))
  (canPop env curFrame '(float int (array float))))

(defun execute-fastore (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(float int (array float)) 'void curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-fcmpg (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(float float) 'int curFrame))

(defun execute-fcmpg (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(float float) 'int curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-fconst_0 (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env nil 'float curFrame))

(defun execute-fconst_0 (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env nil 'float curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-fload (inst env curFrame)
  (let ((index (arg1 inst)))
    (loadIsTypeSafe env index 'float curFrame)))


(defun execute-fload (inst env curFrame)
  (let* ((index (arg1 inst)))
    (mv (do-load env index 'float curFrame)
        (exceptionStackFrame curFrame))))
;--
(defun check-fneg (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(float) 'float curFrame))

(defun execute-fneg (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(float) 'float curFrame)
      (exceptionStackFrame curFrame)))

;--
(defun check-freturn (inst env curFrame)
  (declare (ignore inst))
  (let* ((method (methodEnvironment env))
         (returnType (methodReturnType method)))
    (and (equal returnType 'float)
         (canPop env curFrame '(float)))))

(defun execute-freturn (inst env curFrame)
  (declare (ignore inst env))
  (mv 'aftergoto 
      (exceptionStackFrame curFrame)))
;--
(defun check-fstore (inst env curFrame)
  (let ((index (arg1 inst)))
    (storeIsTypeSafe env index 'float curFrame)))

(defun execute-fstore (inst env curFrame)
  (let ((index (arg1 inst)))
    (mv (do-store env index 'float curFrame)
        (exceptionStackFrame curFrame))))
;---
;
; assume the field is well formed.

;; (fieldCP <name> <classname> type)
(defun fieldNameCP (FieldCP)
  (nth 1 fieldCP))
(defun fieldClassNameCP (FieldCP)
  (nth 2 fieldCP))

;; Thu Aug 12 19:07:57 2004
;;; bug. 
;;; in djvm fieldCP-fieldtype assume unnormalized
;;; 

(defun fieldTypeCP (FieldCP)
  (nth 3 fieldCP))


(defun superclassChain (n cl)
  (cdr (collect-superclass-list n cl)))


(defun find-field (fname type fields)
  (if (endp fields) nil
    (if (and (equal (fieldName (car fields)) fname)
             (equal (fieldType (car fields)) type))
        (car fields)
      (find-field fname type (cdr fields)))))


(defun lookupFieldInClasses (fname type classes cl)
  (if (endp classes) nil
    (let* ((Class (class-by-name (car classes) cl)) 
           ;; if loaded didn't fail, this class must exist. 
           (fields (classFields Class))
           (field  (find-field fname type fields)))
      (if ;; field  ;;; Fri Jan 28 16:08:32 2005. 
                    ;;; problem!!!. 
                    ;;; We use nil to indicate not found!!
          (and (equal (FIELDNAME field) FNAME)
               (equal (FIELDTYPE field) TYPE)) ;; actually find it.
          field
        (lookupFieldInClasses fname type (cdr classes) cl)))))
        

(defun isProtectedField (fclassname fname type cl)
  (let* ((classes (collect-superclass-list fclassname cl))
         (field   (lookupFieldInClasses fname type classes cl))
         ;; assume the resolution always find it.
         ;; because resolution is done
         (accessflags (fieldAccessFlags field)))
    (member '*protected* accessflags)))

;; under well formed condition:
;;
;;    isProtected == (not (isNotProtected))
;;
;; It is not true otherwise. Do we need to prove this? or 
;; define: isNotProtected to be not isProtected? 
;;
;; Hanbing   
;;

;;
;; this implemention means if not found assume it is not protected!!
;;
;; notice this resolution process is the same as the resolution step in the
;; execution time. --- April 18th. 

;; Sun Apr 17 14:10:26 2005. fixed!! 


(defun passesProtectedFieldCheck (env fclassname fname type target)
  (let* ((curClass (classEnvironment env))
         (curClassName (classClassName curClass))
         (cl  (classtableEnvironment env))
         (superchain   (superclassChain curClassName cl)))
    (or (not (mem fclassName superchain))
        (not (isProtectedField fclassname fname type cl))
        (isAssignable target (prefix-class curClassName) env))))


;;; Fri Jun 17 17:48:51 2005 modification! 
;;; more modification. 
;;; to assert that fieldcp-classname is not "java.lang.Object"
;;; not some interface type!! 
;;; 
 

;; ;; (defun check-getfield (inst env curFrame)
;; ;;   (let* ((CP (arg1 inst))
;; ;;          (fieldClassName (fieldClassNameCP cp))
;; ;;          (fieldName      (fieldNameCP cp))
;; ;;          (fieldType1      (fieldTypeCP  cp))
;; ;;          (fieldType       (translate-type fieldType1))
;; ;;          (operandStack    (frameStack curFrame))
;; ;;          (target          (top operandStack)))
;; ;;     (and 
;; ;;      (passesProtectedFieldCheck env fieldClassName fieldName fieldType target)
;; ;;      (not (equal fieldClassName "java.lang.Object"))
;; ;;      (class-by-name fieldClassName
;; ;;                     (classtableEnvironment env))
;; ;;      (not (classIsInterface
;; ;;            (class-by-name fieldClassName
;; ;;                           (classtableEnvironment env))))
;; ;;      (validTypeTransition env 
;; ;;                           (list (prefix-class fieldClassName))
;; ;;                           fieldType
;; ;;                           curFrame)
;; ;;      (not (isArrayType target)))))

;;;;;  after discussion with Gilad. This is not what he want!!
;;;;; 

(defun check-getfield (inst env curFrame)
  (let* ((CP (arg1 inst))
         (fieldClassName (fieldClassNameCP cp))
         (fieldName      (fieldNameCP cp))
         (fieldType1      (fieldTypeCP  cp))
         (fieldType       (translate-type fieldType1))
         (operandStack    (frameStack curFrame))
         (target          (top operandStack)))
    (and 
     (passesProtectedFieldCheck env fieldClassName fieldName fieldType target)
     (validTypeTransition env 
                          (list (prefix-class fieldClassName))
                          fieldType
                          curFrame))))

;;;  (not (isArrayType (fieldClassName 
;;;  (not (isArrayType target)))))
;;; 




(defun execute-getfield (inst env curFrame)
  (let* ((CP (arg1 inst))
         (fieldClassName (fieldClassNameCP cp))
         (fieldType1      (fieldTypeCP  cp))
         (fieldType       (translate-type fieldType1)))
    (mv (TypeTransition env 
                        (list (prefix-class fieldClassName))
                        fieldType
                        curFrame)
        (exceptionStackFrame curFrame))))

;---
(defun check-getstatic (inst env curFrame)
  (let* ((CP (arg1 inst))
         (fieldType1      (fieldTypeCP  cp))
         (fieldType       (translate-type fieldType1)))
    (validTypeTransition env 
                         nil
                         fieldType
                         curFrame)))

(defun execute-getstatic (inst env curFrame)
  (let* ((CP (arg1 inst))
         (fieldType1      (fieldTypeCP  cp))
         (fieldType       (translate-type fieldType1)))
    (mv (TypeTransition env 
                        nil
                        fieldType
                        curFrame)
        (exceptionStackFrame curFrame))))
;
;----
;

; --- search for StackFrame at offset Target --- 

(defun searchStackFrame (target Instructions);; *12*
  (if (endp Instructions) 
      nil
    (if (isStackMapFrame (car Instructions))
        (if (equal (mapOffset (getMap (car Instructions)))
                   target)
            (mapFrame (getMap (car Instructions)))
          (searchStackFrame target (cdr Instructions)))
      (searchStackFrame target (cdr Instructions)))))

;; *12* Note: 
;;      Instructions here is Merged Instruction
;;      produced by intermixed StackMap and Parsed Instruction.
  

(defun stackFrameAtOffset (Environment Target)
  (let ((Instructions (AllInstructions Environment)))
    (searchStackFrame target Instructions)))



(defun isStackFrame (stackFrame)
  (and (consp stackFrame)
       (equal (car stackFrame) 'frame)))


(defun targetIsTypeSafe (Environment StackFrame Target)
  (let ((Frame (stackFrameAtOffset Environment target)))
    (and ;; (isStackMapFrame Frame) 
         ;; added Wed Jul 27 23:37:22 2005. Tue Dec 20 19:56:07 2005!!! 
         ;; Wed Jul 27 23:37:24 2005
         ;; Tue Dec 20 19:55:42 2005
         (isStackFrame Frame) 
         (frameIsAssignable StackFrame Frame environment))))
;; you have to be a well formed frame for it tobe frame Assignable


(defun check-goto (inst env curFrame)
  (let ((target (arg1 inst)))
    (targetIsTypeSafe env curFrame target)))

(defun execute-goto (inst env curFrame)
  (declare (ignore inst env))
  (mv 'aftergoto 
      (exceptionStackFrame curFrame)))

;--
        
;---
(defun check-i2d (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(int) 'double curFrame))

(defun execute-i2d (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(int) 'double curFrame)
      (exceptionStackFrame curFrame)))

;---
(defun check-i2f (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(int) 'float curFrame))

(defun execute-i2f (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(int) 'float curFrame)
      (exceptionStackFrame curFrame)))
;--

(defun check-i2l (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(int) 'long curFrame))

(defun execute-i2l (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(int) 'long curFrame)
      (exceptionStackFrame curFrame)))
;--

(defun check-iadd (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(int int) 'int curFrame))

(defun execute-iadd (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(int int) 'int curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-iaload (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(int (array int)) 'int curFrame))

(defun execute-iaload (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(int (array int)) 'int curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-iastore (inst env curFrame)
  (declare (ignore inst))
  (canPop env curFrame '(int int  (array int))))

(defun execute-iastore (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(int int (array int)) 'void curFrame)
      (exceptionStackFrame curFrame)))
;--
;; assume the offset has been resolved. target gives the offset from
;; the beginning of the method. 

(defun check-if_acmpeq (inst env curFrame)
  (let ((target (arg1 inst))
        (nextframe (PopMatchingList '(reference reference)  curFrame)))
    (and (canPop env curFrame '(reference reference))
         (targetIsTypeSafe env nextFrame target))))

(defun execute-if_acmpeq (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env 
                      '(reference reference)
                      'void 
                      curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-if_icmpeq (inst env curFrame)
  (let ((target (arg1 inst))
        (nextframe (PopMatchingList '(int int) curFrame)))
    (and (canPop env curFrame '(int int))
         (targetIsTypeSafe env nextFrame target))))

(defun execute-if_icmpeq (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env 
                      '(int int)
                      'void 
                      curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-ifeq (inst env curFrame)
  (let ((target (arg1 inst))
        (nextFrame (PopMatchingList '(int) curFrame)))
    (and (canPop env curFrame '(int))
         (targetIsTypeSafe env nextFrame target))))

(defun execute-ifeq (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env 
                      '(int)
                      'void 
                      curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-ifnonnull (inst env curFrame)
  (let ((target (arg1 inst))
        (nextFrame (PopMatchingList '(reference) curFrame)))
    (and (canPop env curFrame '(reference))
         (targetIsTypeSafe env nextFrame target))))

(defun execute-ifnonnull (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env 
                      '(reference)
                      'void 
                      curFrame)
      (exceptionStackFrame curFrame)))
;--
; assume well formed inst
(defun check-iinc (inst env curFrame)
  (declare (ignore env))
  (let* ((locals (frameLocals curFrame))
         (index  (arg1 inst)))
    (and (nthLocalsExist index 'int curFrame)
         (equal (nth index locals) 'int))))

(defun execute-iinc (inst env curFrame)
  (declare (ignore inst env))
  (mv curFrame (exceptionStackFrame curFrame)))
;--
(defun check-iload (inst env curFrame)
  (let ((index (arg1 inst)))
    (loadIsTypeSafe env index 'int curFrame)))


(defun execute-iload (inst env curFrame)
  (let* ((index (arg1 inst)))
    (mv (do-load env index 'int curFrame)
        (exceptionStackFrame curFrame))))
;--
(defun check-ineg (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(int) 'int curFrame))

(defun execute-ineg (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(int) 'int curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-instanceof (inst env curFrame)
  (let ((CP (arg1 inst)))
    (and (or (isClassType CP)
             (isArrayType CP))
         (validTypeTransition env  '((class "java.lang.Object"))
                              'int  curFrame))))

(defun execute-instanceof (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env  '((class "java.lang.Object"))
                      'int curFrame)
      (exceptionStackFrame curFrame)))
;--
;; assume well formed inst, CP, Count , 0

(defun CountIsValid (count InFrame OutFrame)
  (equal count (- (len (frameStack InFrame)) 
                  (len (frameStack OutFrame)))))


;; (methodCP <name> <className> (<type>*) returntype)
(defun methodNameCP (MethodCP)
  (nth 1 MethodCP))
(defun methodClassNameCP (MethodCP)
  (nth 2 MethodCP))
(defun methodArgListCP (MethodCP)
  (nth 3 MethodCP))
(defun methodReturnTypeCP (MethodCP)
  (nth 4 MethodCP))

;;
;; assuming the last count is always zero, we 
;; omit it in the representation of the invokeinterface
;;

(defun check-invokeinterface (inst env curFrame)
  (let* ((CP (arg1 inst))
         (Count (arg2 inst)) 
         (methodName (methodNameCP CP))
         (returnType1 (methodReturnTypeCP CP))
         (returnType  (translate-type returnType1))
         (OperandArgList1 (methodArgListCP CP))
         (OperandArgList  (translate-types OperandArgList1))
         (MethodClassName (methodClassNameCP CP))
         (StackArgList    (reverse (cons (prefix-class MethodClassName) 
                                         OperandArgList)))
         (tempFrame (PopMatchingList StackArgList curFrame)))
    (and (not (equal MethodName "<init>"))
         (not (equal MethodName "<clinit>"))
         (canPop env curFrame StackArgList)
         (validTypeTransition env nil returnType tempFrame)
         (countIsValid Count curFrame TempFrame))))

(defun execute-invokeinterface (inst env curFrame)
  (let* ((CP (arg1 inst))
         (returnType1 (methodReturnTypeCP CP))
         (returnType  (translate-type returnType1))
         (OperandArgList1 (methodArgListCP CP))
         (OperandArgList  (translate-types OperandArgList1))
         (MethodClassName (methodClassNameCP CP))
         (StackArgList    (reverse (cons (prefix-class MethodClassName) 
                                         OperandArgList)))
         (tempFrame (PopMatchingList StackArgList curFrame)))
    (mv (TypeTransition env nil returnType tempFrame)
        (exceptionStackFrame curFrame))))
;--
;     CP = method(MethodClassName, MethodName, Signature) 
;--

(defun is-invoke-non-init (inst env curFrame)
  (let* ((CP (arg1 inst))
         (methodName (methodNameCP CP))
         (returnType1 (methodReturnTypeCP CP))
         (returnType  (translate-type returnType1))
         (OperandArgList1 (methodArgListCP CP))
         (OperandArgList  (translate-types OperandArgList1))
         (CurrentClass (thisClassEnvironment env))
         (StackArgList    (reverse (cons (prefix-class CurrentClass)
                                         OperandArgList)))
         (MethodClassName (methodClassNameCP CP))
         (StackArgList2  (reverse (cons (prefix-class MethodClassName) 
                                        OperandArgList))))
    (and (not (equal MethodName "<init>"))
         (not (equal MethodName "<clinit>"))
         (validTypeTransition env StackArgList  returnType curFrame)
         (validTypeTransition env StackArgList2 returnType curFrame))))


(defun do-invoke-non-init (inst env curFrame)
  (let* ((CP (arg1 inst))
         (returnType1 (methodReturnTypeCP CP))
         (returnType  (translate-type returnType1))
         (OperandArgList1 (methodArgListCP CP))
         (OperandArgList  (translate-types OperandArgList1))
         (MethodClassName (methodClassNameCP CP))
         (StackArgList    (reverse (cons (prefix-class MethodClassName) 
                                         OperandArgList)))
         (tempFrame (PopMatchingList StackArgList curFrame)))
    (mv (TypeTransition env nil returnType tempFrame)
        (exceptionStackFrame curFrame))))          

(defun address-uninit (uninit)
  (cadr uninit))

(defun make-inst1 (offset opcode arg1)
  (list offset (list opcode arg1)))

(defun is-invoke-init (inst env curFrame)
  (let* ((CP (arg1 inst))
         (methodName (methodNameCP CP))
         (methodClassName (methodClassNameCP CP))
         (OperandArgList1 (methodArgListCP CP))
         (OperandArgList  (translate-types OperandArgList1))
         (StackArgList (reverse OperandArgList))
         (TempFrame (popMatchingList StackArgList curFrame))
         (FullOperandStack (frameStack TempFrame))
         (UninitializedArg (top FullOperandStack)))
    (and (equal methodName "<init>")
         (or (equal UninitializedArg 'uninitializedThis)
             (and (isuninitializedObject UninitializedArg)
                  (mem (make-inst1 (address-uninit  uninitializedArg)
                                   'new
                                   (prefix-class methodClassName))
                       (allInstructions env))))
         ;; 'uninitializedThis comes from the original parameter of <init>
         ;; (what instruction inside of <init> see. (recursive invoke)
         ;; (uninitialized <offset>) is what code of outside <init> see
         ;; (invokespecial ...)
         (CanPop env curFrame StackArgList))))

(defun rewrittenUninitializedType (type env MethodClassCP)
  (cond ((equal type 'uninitializedThis)
         (prefix-class  (thisClassEnvironment env)))
        ((equal (car type) 'uninitialized)
         MethodClassCP)
        (t nil)))

(defun rewrittenInitializationFlags (type Flags)
  (cond ((equal type 'uninitializedThis) nil)
        ((isuninitializedObject type) Flags)
        (t nil)))
  
;--
(defun replacex (old new lst)
  (if (endp lst)
      nil
    (if (equal (car lst) old)
        (cons new (replacex old new (cdr lst)))
      (cons (car lst) (replacex old new (cdr lst))))))
;--


(defun do-invoke-init (inst env curFrame)
  (let* ((CP (arg1 inst))
         (methodClassName (methodClassNameCP CP))
         (OperandArgList1 (methodArgListCP CP))
         (OperandArgList  (translate-types OperandArgList1))
         (StackArgList (reverse OperandArgList))
         (TempFrame (popMatchingList StackArgList curFrame))
         (FullOperandStack (frameStack TempFrame))
         (Flags (frameFlags TempFrame))
         (Locals (frameLocals TempFrame))
         (UninitializedArg (top FullOperandStack))
         (This (rewrittenUninitializedType 
                UninitializedArg env (prefix-class MethodClassName)))
         (NextFlags (rewrittenInitializationFlags UninitializedArg Flags))
         (OperandStack (pop FullOperandStack))
         (NextOperandStack (replacex UninitializedArg This OperandStack))
         (NextLocals (replacex UninitializedArg This Locals)))
    (prog2$ 
     (acl2::debug-print "PC = ~p0 Initializing ~p1~%" (instrOffset inst) UninitializedArg)
     (mv (make-sig-frame NextLocals NextOperandStack NextFlags)
         (make-sig-frame NextLocals nil Flags)))))


(defun check-invokespecial (inst env curFrame)
  (or (is-invoke-init inst env curFrame)
      (is-invoke-non-init inst env curFrame)))

(defun execute-invokespecial (inst env curFrame)
  (cond ((is-invoke-non-init inst env curFrame) 
         (do-invoke-non-init inst env curFrame))
        ((is-invoke-init  inst env curFrame)
         (do-invoke-init inst env curFrame))
        (t (mv nil nil)))) 
;;
;; ERROR STATE well formed prevent it to happend
;;
;; What would happen if resolution failed??
;; bytecode verifier has to ensure resolution succeeds!!
;;

;--
(defun check-invokestatic (inst env curFrame)
  (let* ((CP (arg1 inst))
         (methodName     (methodNameCP CP))
         (OperandArgList1 (methodArgListCP CP))
         (OperandArgList  (translate-types OperandArgList1))
         (ReturnType1     (methodReturnTypeCP CP))
         (returnType  (translate-type returnType1))
         (StackArgList (reverse OperandArgList)))
    (and (not (equal methodName "<clinit>"))
         (validTypeTransition env StackArgList ReturnType
                              curFrame))))

(defun execute-invokestatic (inst env curFrame)
  (let* ((CP (arg1 inst))
         (OperandArgList1 (methodArgListCP CP))
         (OperandArgList  (translate-types OperandArgList1))
         (ReturnType1     (methodReturnTypeCP CP))
         (returnType  (translate-type returnType1))
         (StackArgList (reverse OperandArgList)))
    (mv (TypeTransition env StackArgList ReturnType
                        curFrame)
        (exceptionStackFrame curFrame))))
;--
(defun find-method (mName returnType argTypes methods)
  (if (endp methods) nil
    (if (and (equal (methodName (car methods)) mName)
             (equal (methodReturnType (car methods)) returnType)
             (equal (methodParameters (car methods)) argTypes))
        (car methods)
      (find-method mName returnType argTypes (cdr methods)))))


(defun lookupMethodInClasses (mName returnType argTypes classes cl)
  (if (endp classes) nil
    (let* ((Class (class-by-name (car classes) cl)) 
           ;; if loaded didn't fail, this class must exist. 
           (methods (classMethods Class))
           (method (find-method mName returnType argTypes methods)))
      (if ;; method ;; same problem as in lookupFieldInClasses
          (and (equal (methodName (car methods)) mName)
               (equal (methodReturnType (car methods)) returnType)
               (equal (methodParameters (car methods)) argTypes))
          method
        (lookupMethodInClasses mName returnType argTypes (cdr classes) cl)))))

(defun isProtectedMethod (mClassName mName returntype args cl)
  (let* ((classes (collect-superclass-list mClassName cl))
         (method  (lookupMethodInClasses mName returntype args classes cl))
         (accessflags (methodAccessFlags method)))
    (member '*protected* accessflags)))
;; assume the resolution always find it.
;; because resolution is done

(defun passesProtectedMethodCheck 
  (env mClassName mName returntype args target)
  (let* ((curClass (classEnvironment env))
         (curClassName (classClassName curClass))
         (cl  (classtableEnvironment env))
         (superchain   (superclassChain curClassName cl)))
    (or (not (mem curClassName superchain))
        (not (isProtectedMethod mClassname mName returntype args cl))
        (isAssignable target (prefix-class curClassName) env))))


(defun check-invokevirtual (inst env curFrame)
  (let* ((CP (arg1 inst))
         (methodName      (methodNameCP     CP))
         (methodClassName (methodClassNameCP  CP))
         (OperandArgList1 (methodArgListCP CP))
         (OperandArgList  (translate-types OperandArgList1))
         (ReturnType1     (methodReturnTypeCP CP))
         (returnType  (translate-type returnType1))
         (StackArgList (reverse (cons (prefix-class MethodClassName) 
                                      OperandArgList)))
         (target (top (popMatchingList1 (reverse OperandArgList) (frameStack curFrame)))))
    (and (not (equal methodName "<clinit>"))
         (not (equal methodName "<init>"))
         (passesProtectedMethodCheck env methodClassName methodName 
                                     Returntype1 OperandArgList1 target)
         ;; use untranslated types to look up 
         ;; but treat them as int during type checking 
         ;; byte, char, short and  boolean to int
         (validTypeTransition env StackArgList ReturnType curFrame))))


(defun execute-invokevirtual (inst env curFrame)
  (let* ((CP (arg1 inst))
         (methodClassName (methodClassNameCP  CP))
         (OperandArgList1  (methodArgListCP CP))
         (OperandArgList  (translate-types OperandArgList1))
         (ReturnType1      (methodReturnTypeCP CP))
         (returnType  (translate-type returnType1))
         (StackArgList (reverse (cons (prefix-class MethodClassName) 
                                      OperandArgList))))
    (mv (TypeTransition env StackArgList ReturnType
                        curFrame)
        (exceptionStackFrame curFrame))))

;--
(defun check-ireturn (inst env curFrame)
  (declare (ignore inst))
  (let* ((method (methodEnvironment env))
         (returnType1 (methodReturnType method))
         (returnType  (translate-type returnType1)))
    (and (equal returntype 'int)
         (canPop env curFrame '(int)))))

(defun execute-ireturn (inst env curFrame)
  (declare (ignore inst env))
  (mv 'aftergoto 
      (exceptionStackFrame curFrame)))
;--
(defun check-istore (inst env curFrame)
  (let ((index (arg1 inst)))
    (storeIsTypeSafe env index 'int curFrame)))

(defun execute-istore (inst env curFrame)
  (let ((index (arg1 inst)))
    (mv (do-store env index 'int curFrame)
        (exceptionStackFrame curFrame))))
;--

;---
(defun check-l2d (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(long) 'double curFrame))

(defun execute-l2d (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(long) 'double curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-l2f (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(long) 'float curFrame))

(defun execute-l2f (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(long) 'float curFrame)
      (exceptionStackFrame curFrame)))
;--

(defun check-l2i (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(long) 'int curFrame))

(defun execute-l2i (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(long) 'int curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-l2l (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(long) 'long curFrame))

(defun execute-l2l (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(long) 'long curFrame)
      (exceptionStackFrame curFrame)))
;--

(defun check-ladd (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(long long) 'long curFrame))

(defun execute-ladd (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(long long) 'long curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-laload (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(int (array long)) 'long curFrame))

(defun execute-laload (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(int (array long)) 'long curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-lastore (inst env curFrame)
  (declare (ignore inst))
  (canPop env curFrame '(long int (array long))))

(defun execute-lastore (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(long int (array long)) 'void curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-lcmp (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(long long) 'int curFrame))

(defun execute-lcmp (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(long long) 'int curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-lconst_0 (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env nil 'long curFrame))

(defun execute-lconst_0 (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env nil 'long curFrame)
      (exceptionStackFrame curFrame)))

;---
; ldc constant pool entry ( <tag> <value> ) 
; shall we just assume this already resolved 
;
; -- either by jvm2acl2 translator or by the top level routine that do
; some instruction preprocessing routine. 
; ldc, invokevirtual, branch instructions all need this kind of preprocessing.
;---

(defun tagCP (CP)
  (car CP))

(defun typeCP (CP)
  (cadr CP))

(defun check-ldc (inst env curFrame)
  (let* ((cp (arg1 inst))
         (tag (tagCP CP))
         (type (typeCP CP)))
    (and (mem (list tag type)
              '((int int)
                (float float)
                (string (class "java.lang.String"))))
         (validTypeTransition env nil type curFrame))))

(defun execute-ldc (inst env curFrame)
  (let* ((cp (arg1 inst))
         (type (typeCP CP)))
    (mv (TypeTransition env nil type curFrame)
        (exceptionStackFrame curFrame))))
;-- 
(defun check-ldc2_w (inst env curFrame)
  (let* ((cp (arg1 inst))
         (tag (tagCP CP)))
    (and (mem tag
              '(long double))
         (validTypeTransition env nil tag curFrame))))

(defun execute-ldc2_w (inst env curFrame)
  (let* ((cp (arg1 inst))
         (tag (tagCP cp)))
    (mv (TypeTransition env nil tag curFrame)
        (exceptionStackFrame curFrame))))

;;
;; need properties about ldc2_w is not changed during execution.
;;

;--
(defun check-lload (inst env curFrame)
  (let ((index (arg1 inst)))
    (loadIsTypeSafe env index 'long curFrame)))


(defun execute-lload (inst env curFrame)
  (let* ((index (arg1 inst)))
    (mv (do-load env index 'long curFrame)
        (exceptionStackFrame curFrame))))
;--
(defun check-lneg (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(long) 'long curFrame))

(defun execute-lneg (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(long) 'long curFrame)
      (exceptionStackFrame curFrame)))
;-- 
; rely on some preprocessing

(defun ordered (lst)
  (if (endp lst)
      t
    (if (endp (cdr lst))
        t
      (and (<= (car lst) (cadr lst))
           (ordered (cdr lst))))))
        
(defun checklist-targetIsTypeSafe (env frame targets)
  (if (endp targets)
      t
    (and (targetIsTypeSafe env frame (car targets))
         (checklist-targetIsTypeSafe env frame (cdr targets)))))

(defun make-inst2 (offset opcode arg1 arg2)
  (list offset (list opcode arg1 arg2)))

(defun lksdefault (lksinfo)
  (nth 1 lksinfo))

(defun paircount (lksinfo)
  (nth 2 lksinfo))

(defun pairs (lksinfo)
  (nth 3 lksinfo))


(defun collect-keys (npairs)
  (if (endp npairs)
      nil
    (cons (caar npairs) (collect-keys (cdr npairs)))))

(defun collect-targets (npairs)
  (if (endp npairs)
      nil
    (cons (cdar npairs) (collect-targets (cdr npairs)))))


(defun inst-trans-lookupswitch (inst) 
  (let* ((lookupswitchinfo (arg1 inst))
         (default     (lksdefault lookupswitchinfo))
         (npairs      (pairs     lookupswitchinfo))
         (keys        (collect-keys npairs))
         (targets     (collect-targets npairs)))
    (make-inst2 (instrOffset inst)
                (op-code inst)
                (cons default targets)
                keys)))



(defun check-lookupswitch (inst env curFrame)
  (let* ((Targets (arg1 inst))
         (Keys    (arg2 inst))
         (BranchStackFrame (popMatchingList '(int) curFrame)))
    (and (ordered Keys)
         (canPop env curFrame '(int))
         (checklist-targetIsTypeSafe env branchStackFrame targets))))


(defun execute-lookupswitch (inst env curFrame)
  (declare (ignore inst env))
  (mv 'aftergoto (exceptionStackFrame curFrame)))
;--

(defun check-lreturn (inst env curFrame)
  (declare (ignore inst))
  (let* ((method (methodEnvironment env))
         (returnType (methodReturnType method)))
    (and (equal returnType 'long)
         (canPop env curFrame '(long)))))

(defun execute-lreturn (inst env curFrame)
  (declare (ignore inst env))
  (mv 'aftergoto 
      (exceptionStackFrame curFrame)))
;--
(defun check-lshl (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(int long) 'long curFrame))

(defun execute-lshl (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(int long) 'long curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-lstore (inst env curFrame)
  (let ((index (arg1 inst)))
    (storeIsTypeSafe env index 'long curFrame)))

(defun execute-lstore (inst env curFrame)
  (let ((index (arg1 inst)))
    (mv (do-store env index 'long curFrame)
        (exceptionStackFrame curFrame))))
;--
(defun check-monitorenter (inst env curFrame)
  (declare (ignore inst))
  (canPop env curFrame '(reference)))

(defun execute-monitorenter (inst env curFrame)
  (declare (ignore inst env))
  (mv (PopMatchingList '(reference) curFrame)
      (exceptionStackFrame curFrame)))
;--

(defun classDimensionCP (class)
  (let ((X (component-type class)))
    (cond ((isClassType class) 0)
          ((isArrayType class)
           (+ 1 (classDimensionCP X)))
          (t 0))))
      
(defun intlist (n)
  (if (zp n)
      nil
    (cons 'int (intlist (- n 1)))))

(defun check-multianewarray (inst env curFrame)
  (let* ((CP (arg1 inst))
         (Dimension (classDimensionCP CP))
         (Dim (arg2 inst))
         (IntList (intlist Dim)))
    (and (isArrayType CP)
         (<= Dim Dimension)
         (< 0 Dim)
         (validTypeTransition env IntList CP curFrame))))

(defun execute-multianewarray (inst env curFrame)
  (let* ((CP (arg1 inst))
         (Dim (arg2 inst))
         (IntList (intlist Dim)))
    (mv (TypeTransition env IntList CP curFrame)
        (exceptionStackFrame curFrame))))
;--


(defun check-new (inst env curFrame)
  (let* ((CP (arg1 inst))
         (OperandStack (frameStack curFrame))
         (Locals       (frameLocals curFrame))
         (Flags        (frameFlags  curFrame))
         (offset (instrOffset inst))
         (newItem (list 'uninitialized offset)))
    (and (isClassType CP)
         (not (mem newItem OperandStack)) 
;;
;;         make sure we are not coming to this location, 
;;         without initialize the previous object that was created. 
;;
         (let ((NewLocals (replacex NewItem 'topx Locals)))
;;
;;  For safety, we clean out the NewItem that exists in LOCALS
;; ?? Why? Because we could have some old reference lying around? 
;;  We could have some uninitialized pointers lying around? Replacing them with
;;  'topx we prevent the future use of those uninitialized pointers. 
;; 
;;  We can eventually prove that defensive machine will never use an
;;  uninitialized pointer
;;
           (validTypeTransition env nil newItem 
                                (make-sig-frame newLocals 
                                                OperandStack
                                                Flags))))))


(defun execute-new (inst env curFrame)
  (let* ((OperandStack (frameStack curFrame))
         (Locals       (frameLocals curFrame))
         (Flags        (frameFlags  curFrame))
         (offset (instrOffset inst))
         (newItem (list 'uninitialized offset))
         (NewLocals (replacex NewItem 'topx Locals)))
    ;; make sure we can store such a reference somewhere in unoccupied slot but
    ;; nowhere else.
    (mv (TypeTransition env nil newItem 
                        (make-sig-frame newLocals 
                                        OperandStack
                                        Flags))
        (exceptionStackFrame curFrame))))
;--
(defun check-newarray (inst env curFrame)
  (let ((ElementType (arg1 inst)))
    (validTypeTransition env '(int) (list 'array ElementType)
                         curFrame)))

(defun execute-newarray (inst env curFrame)
  (let ((ElementType (arg1 inst)))
    (mv (TypeTransition env '(int) (list 'array ElementType)
                        curFrame)
        (exceptionStackFrame curFrame))))
;--

(defun check-nop (inst env curFrame)
  (declare (ignore inst env curFrame))
  t)

(defun execute-nop (inst env curFrame)
  (declare (ignore inst env))
  (mv curFrame 
      (exceptionStackFrame curFrame)))
;--
(defun check-pop (inst env curFrame)
  (declare (ignore inst env))
  (let* ((Stack  (frameStack  curFrame)))
    (and (nth1OperandStackExist 1 curFrame)
         (isTopCategory1 stack))))

(defun execute-pop (inst env curFrame)
  (declare (ignore inst  env))
  (let* ((Locals (frameLocals curFrame))
         (Stack  (frameStack  curFrame))
         (Flags  (frameFlags  curFrame))
         (Rest   (popCategory1 Stack)))
    (mv (make-sig-frame Locals
                        Rest
                        Flags)
        (exceptionStackFrame curFrame))))
;--
(defun is-pop2-form1 (inst env curFrame)
  (declare (ignore inst env))
  (and (isTopCategory1 (frameStack curFrame))
       (isTopCategory1 (popCategory1 (frameStack curFrame)))))

(defun do-pop2-form1 (inst env curFrame)
  (declare (ignore inst env))
  (mv (make-sig-frame 
       (framelocals curFrame)
       (popCategory1 (popCategory1 (frameStack curFrame)))
       (frameFlags curFrame))
      (exceptionStackFrame curFrame)))

(defun is-pop2-form2 (inst env curFrame)
  (declare (ignore inst env))
  (isTopCategory2 (frameStack curFrame)))

(defun do-pop2-form2 (inst env curFrame)
  (declare (ignore inst env))
  (mv (make-sig-frame 
       (framelocals curFrame)
       (popCategory2 (frameStack curFrame))
       (frameFlags curFrame))
      (exceptionStackFrame curFrame)))

(defun check-pop2 (inst env curFrame)
  (and (nth1operandStackExist 2 curFrame)
       (or (is-pop2-form1 inst env curFrame)
           (is-pop2-form2 inst env curFrame))))

(defun execute-pop2 (inst env curFrame)
  (cond ((is-pop2-form1 inst env curFrame)
         (do-pop2-form1 inst env curFrame))
        ((is-pop2-form2 inst env curFrame)
         (do-pop2-form2 inst env curFrame))
        (t (mv nil nil))))
;--
; assume the field is well formed.
(defun check-putfield (inst env curFrame)
  (let* ((CP (arg1 inst))
         (fieldClassName (fieldClassNameCP cp))
         (fieldName      (fieldNameCP cp))
         (fieldType1      (fieldTypeCP  cp))
         (fieldType       (translate-type fieldType1))
         (target (top (popMatchingType fieldType (frameStack curFrame)))))
    (and (passesProtectedFieldCheck env fieldClassName fieldName fieldType target)
         (canPop  env curFrame (list fieldtype (prefix-class
                                                     fieldClassName))))))

(defun execute-putfield (inst env curFrame)
  (declare (ignore env))
  (let* ((CP (arg1 inst))
         (fieldClassName  (fieldClassNameCP cp))
         (fieldType1      (fieldTypeCP  cp))
         (fieldType       (translate-type fieldType1)))
    (mv (PopMatchingList (list fieldtype (prefix-class
                                               fieldClassName))
                         curFrame)
        (exceptionStackFrame curFrame))))
;--
(defun check-putstatic (inst env curFrame)
  (let* ((CP (arg1 inst))
         (fieldType1      (fieldTypeCP  cp))
         (fieldType       (translate-type fieldType1)))
    (canPop  env curFrame (list fieldtype))))

(defun execute-putstatic (inst env curFrame)
  (declare (ignore env))
  (let* ((CP (arg1 inst))
         (fieldType1      (fieldTypeCP  cp))
         (fieldType       (translate-type fieldType1)))
    (mv (PopMatchingList (list fieldtype)
                         curFrame)
        (exceptionStackFrame curFrame))))
;--
(defun check-return (inst env curFrame)
  (declare (ignore inst))
  (let* ((curMethod (methodEnvironment env))
         (Flags (frameFlags curFrame))
         (returntype (methodReturnType curMethod)))
    (and (equal returntype 'void)
         (not (mem 'flagThisUninit Flags)))))

(defun execute-return (inst env curFrame)
  (declare (ignore inst env))
  (mv 'aftergoto
      (exceptionStackFrame curFrame)))
;--
(defun check-saload (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env '(int (array short)) 'int curFrame))

(defun execute-saload (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(int (array short)) 'int curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-sastore (inst env curFrame)
  (declare (ignore inst))
  (canPop env curFrame '(int int (array short))))

(defun execute-sastore (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env '(int int (array short)) 'void curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-sipush (inst env curFrame)
  (declare (ignore inst))
  (validTypeTransition env nil 'int curFrame))

(defun execute-sipush (inst env curFrame)
  (declare (ignore inst))
  (mv (TypeTransition env nil 'int curFrame)
      (exceptionStackFrame curFrame)))
;--
(defun check-swap (inst env curFrame)
  (declare (ignore inst env))
  (let ((Stack (frameStack curFrame)))
    (and (nth1operandStackExist 2 curFrame)
         (equal (sizeOf (top stack)) 1)
         (equal (sizeOf (top (pop stack))) 1))))

(defun execute-swap (inst env curFrame)
  (declare (ignore inst env))
  (let ((Stack (frameStack curFrame)))
    (mv (make-sig-frame 
         (frameLocals curFrame)
         (push (top (pop stack))
               (push (top stack)
                     (pop (pop stack))))
         (frameFlags curFrame))
        (exceptionStackFrame curFrame))))
;--

(defun tbldefault (tblinfo)
  (nth 1 tblinfo))

(defun tblrange (tblinfo)
  (nth 2 tblinfo))

(defun tbltargets (tblinfo)
  (nth 3 tblinfo))


(defun gen-list (low count)
  (if (zp count)
      nil
    (cons low (gen-list (+ 1 low) (- count 1)))))


(defun gen-keys (range)
  (gen-list (car range) (- (+ 1 (cdr range)) (car range))))


(defun inst-trans-tableswitch (inst)
  (let* ((tblinfo (arg1 inst))
         (default (tbldefault tblinfo))
         (range   (tblrange tblinfo))
         (keys    (gen-keys range))
         (targets  (tbltargets tblinfo)))
    (make-inst2 (instrOffset inst)
                (op-code inst)
                (cons default targets)
                keys)))





(defun check-tableswitch (inst env curFrame)
  (let* ((Targets (arg1 inst))
         (Keys    (arg2 inst))
         (BranchStackFrame (popMatchingList '(int) curFrame)))
    (and (ordered Keys)
         (canPop env curFrame '(int))
         (checklist-targetIsTypeSafe env branchStackFrame Targets))))

(defun execute-tableswitch (inst env curFrame)
  (declare (ignore inst env))
  (mv 'aftergoto (exceptionStackFrame curFrame)))



(defun cpEntry (index cpool)
  (nth index cpool))

(defun makeTagCP (tag type)
  (list tag type))

(defun inst-resolve-cp (inst env) 
  (let ((cpool (classConstantPool (classEnvironment env))))
    (cond ((or (equal (op-code inst) 'ldc)
               (equal (op-code inst) 'ldc2_w))
           (let* ((index (arg1 inst))
                  (entry (cpEntry index cpool))
                  (tag   (car entry)))
             (cond ((equal tag 'String) 
                    (make-inst1 (instrOffset inst)
                                (op-code inst)
                                (makeTagCP tag '(class "java.lang.String"))))
                   ((equal tag 'Long)
                    (make-inst1 (instrOffset inst)
                                (op-code inst)
                                (makeTagCP tag 'LONG)))
                   ((equal tag 'FLOAT)
                    (make-inst1 (instrOffset inst)
                                (op-code inst)
                                (makeTagCP tag 'FLOAT)))
                   ((equal tag 'DOUBLE)
                    (make-inst1 (instrOffset inst)
                                (op-code inst)
                                (makeTagCP tag 'DOUBLE)))
                   ((equal tag 'Int)
                    (make-inst1 (instrOffset inst)
                                (op-code inst)
                                (makeTagCP tag 'INT)))
                   (t nil))))
          (t nil))))



(defun instructionIsTypeSafe (instr env cur);; *9*
  (let* ((inst (instructionHasEquivalentTypeRule instr))
         (op   (op-code inst)))
    (cond ((equal op 'aaload)      (check-aaload  inst env cur))
          ((equal op 'aastore)     (check-aastore inst env cur))
          ((equal op 'aconst_null) (check-aconst_null   inst env cur))  
          ((equal op 'aload)       (check-aload   inst env cur))
          ((equal op 'anewarray)   (check-anewarray   inst env cur))  
          ((equal op 'areturn)     (check-areturn inst env cur))
          ((equal op 'arraylength) (check-arraylength   inst env cur))  
          ((equal op 'astore)      (check-astore inst env cur))
          ((equal op 'athrow)      (check-athrow   inst env cur))  
          ((equal op 'baload)      (check-baload inst env cur))
          ((equal op 'bastore)     (check-bastore   inst env cur))  
          ((equal op 'caload)      (check-caload inst env cur))
          ((equal op 'castore)     (check-castore  inst env cur))  
          ((equal op 'checkcast)   (check-checkcast inst env cur))
          ((equal op 'd2f)         (check-d2f   inst env cur))  
          ((equal op 'd2i)         (check-d2i inst env cur))
          ((equal op 'd2l)         (check-d2l   inst env cur))  
          ((equal op 'dadd)        (check-dadd inst env cur))
          ((equal op 'daload)      (check-daload   inst env cur))  
          ((equal op 'dastore)     (check-dastore inst env cur))
          ((equal op 'dcmpg)       (check-dcmpg   inst env cur))  
          ((equal op 'dconst_0)   (check-dconst_0 inst env cur))
          ((equal op 'dload)      (check-dload   inst env cur))  
          ((equal op 'dneg)       (check-dneg inst env cur))
          ((equal op 'dreturn)    (check-dreturn   inst env cur))  
          ((equal op 'dstore)     (check-dstore inst env cur))
          ((equal op 'dup)        (check-dup  inst env cur))  
          ((equal op 'dup_x1)     (check-dup_x1 inst env cur))
          ((equal op 'dup_x2)     (check-dup_x2   inst env cur))  
          ((equal op 'dup2)       (check-dup2 inst env cur))
          ((equal op 'dup2_x1)    (check-dup2_x1   inst env cur))  
          ((equal op 'dup2_x2)    (check-dup2_x2 inst env cur))
          ((equal op 'f2d)        (check-f2d   inst env cur))  
          ((equal op 'f2i)         (check-f2i inst env cur))
          ((equal op 'f2l)         (check-f2l   inst env cur))  
          ((equal op 'fadd)        (check-fadd inst env cur))
          ((equal op 'faload)      (check-faload   inst env cur))  
          ((equal op 'fastore)     (check-fastore inst env cur))
          ((equal op 'fcmpg)       (check-fcmpg   inst env cur))  
          ((equal op 'fconst_0)   (check-fconst_0 inst env cur))
          ((equal op 'fload)      (check-fload   inst env cur))  
          ((equal op 'fneg)       (check-fneg inst env cur))
          ((equal op 'freturn)    (check-freturn   inst env cur))  
          ((equal op 'fstore)     (check-fstore inst env cur))
          ((equal op 'getfield)   (check-getfield inst env cur))
          ((equal op 'getstatic)  (check-getstatic   inst env cur))  
          ((equal op 'goto)       (check-goto inst env cur))
          ((equal op 'i2f)        (check-i2f   inst env cur))  
          ((equal op 'i2d)        (check-i2d   inst env cur))  
          ((equal op 'i2l)        (check-i2l   inst env cur))  
          ((equal op 'iadd)       (check-iadd inst env cur))
          ((equal op 'saload)      (check-saload   inst env cur))  
          ((equal op 'sastore)     (check-sastore inst env cur))
          ((equal op 'iaload)      (check-iaload   inst env cur))  
          ((equal op 'iastore)     (check-iastore inst env cur))
          ((equal op 'if_acmpeq)   (check-if_acmpeq inst env cur))
          ((equal op 'if_icmpeq)   (check-if_icmpeq inst env cur))
          ((equal op 'ifeq)        (check-ifeq inst env cur))
          ((equal op 'ifnonnull)   (check-ifnonnull inst env cur))
          ((equal op 'iinc)        (check-iinc inst env cur))
          ((equal op 'iload)      (check-iload   inst env cur))  
          ((equal op 'ineg)       (check-ineg inst env cur))
          ((equal op 'instanceof) (check-instanceof inst env cur))
          ((equal op 'invokeinterface) (check-invokeinterface  inst env cur))  
          ((equal op 'invokespecial)  (check-invokespecial    inst env cur))
          ((equal op 'invokestatic)   (check-invokestatic    inst env cur))
          ((equal op 'invokevirtual)  (check-invokevirtual    inst env cur))
          ((equal op 'ireturn)    (check-ireturn   inst env cur))  
          ((equal op 'istore)     (check-istore inst env cur))
          ((equal op 'l2f)        (check-l2f   inst env cur))  
          ((equal op 'l2d)        (check-l2d   inst env cur))  
          ((equal op 'l2i)         (check-l2i inst env cur))
          ((equal op 'ladd)        (check-ladd inst env cur))
          ((equal op 'laload)      (check-laload   inst env cur))  
          ((equal op 'lastore)     (check-lastore inst env cur))
          ((equal op 'lcmp)       (check-lcmp   inst env cur))  
          ((equal op 'lconst_0)   (check-lconst_0 inst env cur))
          ((equal op 'ldc)        (check-ldc 
                                   (inst-resolve-cp inst env) env cur))
          ((equal op 'ldc2_w)        (check-ldc2_w 
                                      (inst-resolve-cp inst env) env cur))
          ((equal op 'lload)      (check-lload   inst env cur))  
          ((equal op 'lneg)         (check-lneg inst env cur))
          ((equal op 'lookupswitch) (check-lookupswitch (inst-trans-lookupswitch inst) env cur))
          ((equal op 'lreturn)    (check-lreturn   inst env cur))  
          ((equal op 'lshl)       (check-lshl   inst env cur))
          ((equal op 'lstore)       (check-lstore inst env cur))          
          ((equal op 'monitorenter)    (check-monitorenter   inst env cur))
          ((equal op 'multianewarray)  (check-multianewarray inst env cur))
          ((equal op 'new)       (check-new   inst env cur))  
          ((equal op 'newarray)   (check-newarray inst env cur))
          ((equal op 'nop)       (check-nop  inst env cur))  
          ((equal op 'pop)       (check-pop inst env cur))
          ((equal op 'pop2)      (check-pop2   inst env cur))  
          ((equal op 'putfield)  (check-putfield inst env cur))
          ((equal op 'putstatic)    (check-putstatic inst env cur))
          ((equal op 'return)       (check-return inst env cur))
          ((equal op 'saload)       (check-saload inst env cur))
          ((equal op 'sipush)       (check-sipush inst env cur))
          ((equal op 'swap)         (check-swap   inst env cur))
          ((equal op 'tableswitch)  (check-tableswitch (inst-trans-tableswitch inst) env cur))
          (t nil))))


; return boolean 


;; *9* Note: 
;;     This corresponds to M3-untagged-runtime's 
;;     sig-check-inst   
;;     in /u/hbl/m3-runtime/m3-untagged-runtime-machine.lisp
;;
;; this, together with following sig-do-inst is where we define the
;; semantics of individual instruction. 
;; model differently from Prolog, We want to sperate the Guard --> Action



(defun sig-do-inst  (instr Env cur);; *10* 
  (let* ((inst (instructionHasEquivalentTypeRule instr))
         (op   (op-code inst)))
    (cond ((equal op 'aaload)      (execute-aaload  inst env cur))
          ((equal op 'aastore)     (execute-aastore inst env cur))
          ((equal op 'aconst_null) (execute-aconst_null   inst env cur))  
          ((equal op 'aload)       (execute-aload   inst env cur))
          ((equal op 'anewarray)   (execute-anewarray   inst env cur))  
          ((equal op 'areturn)     (execute-areturn inst env cur))
          ((equal op 'arraylength) (execute-arraylength   inst env cur))  
          ((equal op 'astore)      (execute-astore inst env cur))
          ((equal op 'athrow)      (execute-athrow   inst env cur))  
          ((equal op 'baload)      (execute-baload inst env cur))
          ((equal op 'bastore)     (execute-bastore   inst env cur))  
          ((equal op 'caload)      (execute-caload inst env cur))
          ((equal op 'castore)     (execute-castore  inst env cur))  
          ((equal op 'checkcast)   (execute-checkcast inst env cur))
          ((equal op 'd2f)         (execute-d2f   inst env cur))  
          ((equal op 'd2i)         (execute-d2i inst env cur))
          ((equal op 'd2l)         (execute-d2l   inst env cur))  
          ((equal op 'dadd)        (execute-dadd inst env cur))
          ((equal op 'daload)      (execute-daload   inst env cur))  
          ((equal op 'dastore)     (execute-dastore inst env cur))
          ((equal op 'dcmpg)       (execute-dcmpg   inst env cur))  
          ((equal op 'dconst_0)   (execute-dconst_0 inst env cur))
          ((equal op 'dload)      (execute-dload   inst env cur))  
          ((equal op 'dneg)       (execute-dneg inst env cur))
          ((equal op 'dreturn)    (execute-dreturn   inst env cur))  
          ((equal op 'dstore)     (execute-dstore inst env cur))
          ((equal op 'dup)        (execute-dup  inst env cur))  
          ((equal op 'dup_x1)     (execute-dup_x1 inst env cur))
          ((equal op 'dup_x2)     (execute-dup_x2   inst env cur))  
          ((equal op 'dup2)       (execute-dup2 inst env cur))
          ((equal op 'dup2_x1)    (execute-dup2_x1   inst env cur))  
          ((equal op 'dup2_x2)    (execute-dup2_x2 inst env cur))
          ((equal op 'f2d)        (execute-f2d   inst env cur))  
          ((equal op 'f2i)         (execute-f2i inst env cur))
          ((equal op 'f2l)         (execute-f2l   inst env cur))  
          ((equal op 'fadd)        (execute-fadd inst env cur))
          ((equal op 'faload)      (execute-faload   inst env cur))  
          ((equal op 'fastore)     (execute-fastore inst env cur))
          ((equal op 'fcmpg)       (execute-fcmpg   inst env cur))  
          ((equal op 'fconst_0)   (execute-fconst_0 inst env cur))
          ((equal op 'fload)      (execute-fload   inst env cur))  
          ((equal op 'fneg)       (execute-fneg inst env cur))
          ((equal op 'freturn)    (execute-freturn   inst env cur))  
          ((equal op 'fstore)     (execute-fstore inst env cur))
          ((equal op 'getfield)   (execute-getfield inst env cur))
          ((equal op 'getstatic)  (execute-getstatic   inst env cur))  
          ((equal op 'goto)       (execute-goto inst env cur))
          ((equal op 'i2f)        (execute-i2f   inst env cur))  
          ((equal op 'i2d)        (execute-i2d   inst env cur))  
          ((equal op 'i2l)        (execute-i2l   inst env cur))  
          ((equal op 'iadd)       (execute-iadd inst env cur))
          ((equal op 'iaload)      (execute-iaload   inst env cur))  
          ((equal op 'iastore)     (execute-iastore inst env cur))
          ((equal op 'saload)      (execute-saload   inst env cur))  
          ((equal op 'sastore)     (execute-sastore inst env cur))
          ((equal op 'if_acmpeq)   (execute-if_acmpeq inst env cur))
          ((equal op 'if_icmpeq)   (execute-if_icmpeq inst env cur))
          ((equal op 'ifeq)        (execute-ifeq inst env cur))
          ((equal op 'ifnonnull)   (execute-ifnonnull inst env cur))
          ((equal op 'iinc)        (execute-iinc inst env cur))
          ((equal op 'iload)      (execute-iload   inst env cur))  
          ((equal op 'ineg)       (execute-ineg inst env cur))
          ((equal op 'instanceof) (execute-instanceof inst env cur))
          ((equal op 'invokeinterface) (execute-invokeinterface  inst env cur))  
          ((equal op 'invokespecial)  (execute-invokespecial    inst env cur))
          ((equal op 'invokestatic)   (execute-invokestatic    inst env cur))
          ((equal op 'invokevirtual)  (execute-invokevirtual    inst env cur))
          ((equal op 'ireturn)    (execute-ireturn   inst env cur))  
          ((equal op 'istore)     (execute-istore inst env cur))
          ((equal op 'l2f)        (execute-l2f   inst env cur))  
          ((equal op 'l2d)        (execute-l2d   inst env cur))  
          ((equal op 'l2i)         (execute-l2i inst env cur))
          ((equal op 'ladd)        (execute-ladd inst env cur))
          ((equal op 'laload)      (execute-laload   inst env cur))  
          ((equal op 'lastore)     (execute-lastore inst env cur))
          ((equal op 'lcmp)       (execute-lcmp   inst env cur))  
          ((equal op 'lconst_0)   (execute-lconst_0 inst env cur))
          ((equal op 'ldc)        (execute-ldc (inst-resolve-cp inst env) env cur))
          ((equal op 'ldc2_w)     (execute-ldc2_w (inst-resolve-cp inst env) env cur))
          ((equal op 'lload)      (execute-lload   inst env cur))  
          ((equal op 'lneg)         (execute-lneg inst env cur))
          ((equal op 'lookupswitch) (execute-lookupswitch inst env cur))
          ((equal op 'lreturn)    (execute-lreturn   inst env cur))  
          ((equal op 'lshl)       (execute-lshl   inst env cur))
          ((equal op 'lstore)       (execute-lstore inst env cur))          
          ((equal op 'monitorenter)    (execute-monitorenter   inst env cur))
          ((equal op 'multianewarray)  (execute-multianewarray inst env cur))
          ((equal op 'new)       (execute-new   inst env cur))  
          ((equal op 'newarray)   (execute-newarray inst env cur))
          ((equal op 'nop)       (execute-nop  inst env cur))  
          ((equal op 'pop)       (execute-pop inst env cur))
          ((equal op 'pop2)      (execute-pop2   inst env cur))  
          ((equal op 'putfield)  (execute-putfield inst env cur))
          ((equal op 'putstatic)    (execute-putstatic inst env cur))
          ((equal op 'return)       (execute-return inst env cur))
          ((equal op 'saload)       (execute-saload inst env cur))
          ((equal op 'sipush)       (execute-sipush inst env cur))
          ((equal op 'swap)         (execute-swap   inst env cur))
          ((equal op 'tableswitch)  (execute-tableswitch inst env cur))
          (t (mv nil nil)))))



 
; return (<frame> <frame>) 
; first one is a NextStackFrame      as in normal execution
; next  one is a ExceptionStackFrame as in event an exception is thrown.

;; *10* Note:
;;      In prolog version, typechecker.pl:351
;;      instructionIsTypeSafe  -- check instruction is TypeSafe 
;;      and compute the effect on SigState at the same time.
;;
;;      by returning a NextStackFrame and ExceptionStackFrame                 



;; --------------------------------------------------
;;
;; Exception Handler Helper functions
;;
;; --------------------------------------------------

;; <ExceptionHandler> ::= (handler <stack_pc> <end_pc> <hander_pc> <ExceptionType>)

(defun handlerStartPC (handler)
  (nth 1 handler))

(defun handlerEndPC (handler)
  (nth 2 handler))

(defun handlerHandlerPC (handler)
  (nth 3 handler))


(defun handlerExceptionClass (handler);; *11*
  (nth 4 handler))

;; *11* Note: 
;;   In JVM if handler type is O, translate into 
;;    (class "java.lang.Throwable")
;;
;;  jvm2acl2 tool translates the ExceptionInfo section type 0 into "All" -- old
;;  update: jvm2acl2 take the responsibility to translates this correctly

; --- Exception helper ----

;; assume well formed handlers
(defun isApplicableHandler (offset handler) 
  (let ((start (handlerStartPC handler))
        (end   (handlerEndPC   handler)))
    (and (>= offset start)
         (< offset end))))



;; well formed the predicate is seperated from this function.
(defun instructionSatisfiesHandler (Environment ExceptionStackFrame handler)
  (let ((ExceptionClass (handlerExceptionClass handler))
        (Target  (handlerHandlerPC handler))
        (Flags  (frameFlags ExceptionStackFrame))
        (Locals (frameLocals ExceptionStackFrame)))
    (targetIsTypeSafe Environment (make-sig-Frame Locals (list ExceptionClass)
                                                  Flags)
                      Target)))
                      

;; curMethod
(defun checklist-instructionSatisfiesHandler (env frame Handlers)
  (if (endp handlers)
      t
    (and (instructionSatisfiesHandler env frame (car Handlers))
         (checklist-instructionSatisfiesHandler env frame (cdr Handlers)))))

(defun sublist-isApplicableHandler (offset Handlers)
  (if (endp handlers)
      nil
    (if (isApplicableHandler offset (car Handlers))
        (cons (car Handlers) 
              (sublist-isApplicableHandler offset (cdr Handlers)))
      (sublist-isApplicableHandler offset (cdr Handlers)))))


(defun instructionSatisfiesHandlers (Environment offset ExceptionStackFrame)
  (let* ((Handlers (exceptionHandlers Environment))
         (ApplicableHandlers (sublist-isApplicableHandler offset Handlers)))
    ;; collect all applicable handlers
    (checklist-instructionSatisfiesHandler 
     Environment ExceptionStackFrame  ApplicableHandlers)))


(defun mergedCodeIsTypeSafe(Environment MergedCode StackFrame)
  (if (endp MergedCode)  nil
    (if (endp (cdr MergedCode))
        (and (isEnd (car mergedcode))
             (equal stackframe 'aftergoto))
      (if (equal StackFrame 'afterGoto)
          (cond  ((isStackMap (car MergedCode))
                  (prog2$ 
                   (acl2::debug-print "saw a stack frame as ~p0~%" (getMap (car MergedCode)))
                   (let ((MapFrame (mapFrame (getMap (car MergedCode)))))
                     (mergedCodeIsTypeSafe Environment (cdr MergedCode)
                                           mapFrame))))
                 ((isInstruction (car MergedCode))
                  (prog2$
                   (acl2::debug-print "Missing StackFrame aftergoto at offset ~p0~%"
                                      (instrOffset (car MergedCode)))
                   nil))
                 (t nil))
        ;; is after unconditional branch, there must be a mapFrame  
        (cond  ((isStackMap (car MergedCode))
                (prog2$ 
                 (acl2::debug-print "saw a stack frame as ~p0~%" (getMap (car MergedCode)))
                 (let ((MapFrame (mapFrame (getMap (car MergedCode)))))
                   (and (frameIsAssignable StackFrame MapFrame
                                           Environment)
                        (mergedCodeIsTypeSafe Environment (cdr MergedCode)
                                              MapFrame)))))
          ;; must be an instruction (in a basic block)
               ((isInstruction (car MergedCode))
                (prog2$
                 (acl2::debug-print "~%check inst ~p0~%---~p1~%" (car MergedCode) StackFrame)
                 (let ((offset     (instrOffset (car MergedCode)))
                       (instr      (car MergedCode)))
                   (if (instructionIsTypeSafe instr Environment StackFrame)
                       (prog2$ (acl2::debug-print "here")
                               (mv-let (NextStackFrame ExceptionStackFrame)
                                       (sig-do-inst instr Environment StackFrame)
                                       (and (instructionSatisfiesHandlers Environment offset
                                                                          ExceptionStackFrame)
                                            (prog2$
                                             (acl2::debug-print "" (car (cdr MergedCode)))
                                             (mergedCodeIsTypeSafe Environment (cdr MergedCode)
                                                                   NextStackFrame)))))
                     (prog2$ 
                      (acl2::debug-print "check inst ~p0 failed! ~%~p1~%~p2~%" 
                                         instr  stackFrame (stackFrameAtOffset
                                                            Environment (arg1 instr))) 
                      nil)))))
               (t nil))))))



;; (defun mergedCodeIsTypeSafe(Environment MergedCode StackFrame)
;;   (if (endp MergedCode) 
;;       (equal StackFrame 'afterGoto)
;;     (if (equal StackFrame 'afterGoto)
;;         (if (isStackMap (car MergedCode))
;;             (prog2$ 
;;              (acl2::debug-print "saw a stack frame as ~p0~%" (getMap (car MergedCode)))
;;              (let ((MapFrame (mapFrame (getMap (car MergedCode)))))
;;                (mergedCodeIsTypeSafe Environment (cdr MergedCode)
;;                                      mapFrame)))
;;           (if (isInstruction (car MergedCode))
;;               (prog2$
;;                (acl2::debug-print "Missing StackFrame aftergoto at offset ~p0~%"
;;                          (instrOffset (car MergedCode)))
;;                nil)
;;             (isEnd (car MergedCode))))
;;       ;; is after unconditional branch, there must be a mapFrame  
;;       (if (isStackMap (car MergedCode))
;;           (prog2$ 
;;            (acl2::debug-print "saw a stack frame as ~p0~%" (getMap (car MergedCode)))
;;            (let ((MapFrame (mapFrame (getMap (car MergedCode)))))
;;              (and (frameIsAssignable StackFrame MapFrame
;;                                      Environment)
;;                   (mergedCodeIsTypeSafe Environment (cdr MergedCode)
;;                                         MapFrame))))
;;         ;; must be an instruction (in a basic block)
;;         (if (isInstruction (car MergedCode))
;;             (prog2$
;;              (acl2::debug-print "~%check inst ~p0~%---~p1~%" (car MergedCode) StackFrame)
;;              (let ((offset     (instrOffset (car MergedCode)))
;;                    (instr      (car MergedCode)))
;;                (if (instructionIsTypeSafe instr Environment StackFrame)
;;                    (prog2$ (acl2::debug-print "here")
;;                            (mv-let (NextStackFrame ExceptionStackFrame)
;;                                    (sig-do-inst instr Environment StackFrame)
;;                                    (and (instructionSatisfiesHandlers Environment offset
;;                                                                       ExceptionStackFrame)
;;                                         (prog2$
;;                                          (acl2::debug-print "" (car (cdr MergedCode)))
;;                                          (mergedCodeIsTypeSafe Environment (cdr MergedCode)
;;                                                                NextStackFrame)))))
;;                  (prog2$ 
;;                   (acl2::debug-print "check inst ~p0 failed! ~%~p1~%~p2~%" 
;;                             instr  stackFrame (stackFrameAtOffset
;;                                                Environment (arg1 instr))) 
;;                   nil))))
;;             (if (isEnd (car MergedCode)) t nil))))));; if reach an end


;;;; Sat Dec 24 13:45:39 2005. Wrong!!! 

;; (defun mergedCodeIsTypeSafe(Environment MergedCode StackFrame)
;;   (if (endp MergedCode) 
;;       (equal StackFrame 'afterGoto)
;;     (if (equal StackFrame 'afterGoto)
;;         (if (isStackMap (car MergedCode))
;;             (prog2$ 
;;              (acl2::debug-print "saw a stack frame as ~p0~%" (getMap (car MergedCode)))
;;              (let ((MapFrame (mapFrame (getMap (car MergedCode)))))
;;                (mergedCodeIsTypeSafe Environment (cdr MergedCode)
;;                                      mapFrame)))
;;           (if (isInstruction (car MergedCode))
;;               (prog2$
;;                (acl2::debug-print "Missing StackFrame aftergoto at offset ~p0~%"
;;                          (instrOffset (car MergedCode)))
;;                nil)
;;             (isEnd (car MergedCode))))
;;       ;; is after unconditional branch, there must be a mapFrame  
;;       (if (isStackMap (car MergedCode))
;;           (prog2$ 
;;            (acl2::debug-print "saw a stack frame as ~p0~%" (getMap (car MergedCode)))
;;            (let ((MapFrame (mapFrame (getMap (car MergedCode)))))
;;              (and (frameIsAssignable StackFrame MapFrame
;;                                      Environment)
;;                   (mergedCodeIsTypeSafe Environment (cdr MergedCode)
;;                                         MapFrame))))
;;         ;; must be an instruction (in a basic block)
;;         (if (isInstruction (car MergedCode))
;;             (prog2$
;;              (acl2::debug-print "~%check inst ~p0~%---~p1~%" (car MergedCode) StackFrame)
;;              (let ((offset     (instrOffset (car MergedCode)))
;;                    (instr      (car MergedCode)))
;;                (if (instructionIsTypeSafe instr Environment StackFrame)
;;                    (prog2$ (acl2::debug-print "here")
;;                            (mv-let (NextStackFrame ExceptionStackFrame)
;;                                    (sig-do-inst instr Environment StackFrame)
;;                                    (and (instructionSatisfiesHandlers Environment offset
;;                                                                       ExceptionStackFrame)
;;                                         (prog2$
;;                                          (acl2::debug-print "" (car (cdr MergedCode)))
;;                                          (mergedCodeIsTypeSafe Environment (cdr MergedCode)
;;                                                                NextStackFrame)))))
;;                  (prog2$ 
;;                   (acl2::debug-print "check inst ~p0 failed! ~%~p1~%~p2~%" 
;;                             instr  stackFrame (stackFrameAtOffset
;;                                                Environment (arg1 instr))) 
;;                   nil))))
;;           (if (isEnd (car MergedCode)) t nil))))));; if reach an end


;; and not
;; afterGoto. fail. 


(defun instrExists (offset Instructions)
  (assoc-equal offset Instructions))

(defun isEndofcode (end Instructions)
  (if (assoc-equal 'endofcode Instructions)
      (equal (cadr (assoc-equal 'endofcode Instructions))
             end)
    nil))
  

(defun instrIncludedEnd (Instructions End) 
  (or (instrExists End Instructions);; do we want to insert an (endofcode
      ;; offset) into the parsed instruction? 
      (isEndofCode End Instructions)))

;; (defun isStackFrame (stackFrame)
;;   (and (consp stackFrame)
;;        (equal (car stackFrame) 'frame)))

(defun handlerIsLegal (Environment Handler)
  (let* ((Start (handlerStartPC Handler))
         (End   (handlerEndPC   Handler))
         (Target (handlerHandlerPC Handler))
         (StackFrame (StackFrameAtOffset Environment Target))
         (ExceptionClass (handlerExceptionClass Handler))
         (Instructions (AllInstructions Environment)))
    (and (< Start End)
         (instrExists Start Instructions)
         (isStackFrame stackframe)
         (instrIncludedEnd Instructions End)
         (isAssignable ExceptionClass '(class "java.lang.Throwable") environment))))
         
(defun checklist-handlerIsLegal (env handlers)
  (if (endp handlers)
      t
    (and (handlerIsLegal env (car handlers))
         (checklist-handlerIsLegal env (cdr handlers)))))


(defun handlersAreLegal (Environment) 
  (let ((Handlers (Handlers (methodEnvironment Environment)
                            (classEnvironment Environment))))
    (checklist-handlerIsLegal Environment Handlers)))

(defun methodWithCodeIsTypeSafe (Class Method CL)
  ;; change parseCodeAttribute to consistentCodeAttribute
  (and (isWellFormedCodeAttribute Class Method) 
       ;; will this be important?
       (let* ((FrameSize  (FrameSize method Class)) 
              (MaxStack   (MaxStack   Method Class))
              ;;(ByteCodeLength (ByteCodeLength Method Class))
              (ParsedCode (ParsedCode Method Class))
              (Handlers   (Handlers    Method Class))
              (StackMap   (StackMap   Method Class)))
         (and;; (mem '(endofCode *any*) ParsedCode) 
          ;; temp, doubt whether it
          ;; will work this way.
          (let* ((MergedCode (mergeStackMapAndCode StackMap ParsedCode))
                 (StackFrame (methodInitialStackFrame Class Method FrameSize))
                 (ReturnType  (methodReturnType Method))
                 (Environment (makeEnvironment Class Method ReturnType
                                               MergedCode MaxStack
                                               Handlers
                                               CL)))
            (and (handlersAreLegal Environment)
                 (mergedCodeIsTypeSafe Environment MergedCode
                                       StackFrame)))))))

;--------------
(defun sigMatch (m1 m2)
  (and (equal (methodName m1) (methodName m2))
       (equal (methodParameters m1) (methodParameters m2))
       (equal (methodReturnType m1) (methodReturnType m2))))


(defun matchMethodNameSig (method methods)
  (if (endp methods) 
      nil
    (if (sigMatch method (car methods))
        (car methods)
      (matchMethodNameSig method (cdr methods)))))

(defun isFinal (method)
  (member '*final* (methodAccessFlags method)))


#|        
(defun doesNotOverrideFinalMethod (Class Method CL)
  (let ((classname (classClassName Class)))
    (or (equal classname "java.lang.Object")
        (let* ((supername (classSuperClassName Class))
               (superClass (class-by-name supername CL))
               (methods (classMethods superClass))
               (matched (matchMethodNameSig method methods)))
               (if matched 
                   (not (isFinal matched))
                 (doesNotOverrideFinalMethod superClass Method CL))))))
|# ;; This is hard to terminate. Write a different one. 

(defun doesNotOverrideFinalMethodInClasses (supers Method cl)
  (if (endp supers) t
    (let* ((supername (car supers))
           (superClass (class-by-name supername CL))
           (methods (classMethods superClass))
           (matched (matchMethodNameSig method methods)))
      (if ;; matched ;;; Fri Jan 28 16:38:20 2005. Same problem as lookupFieldInClasses
          (sigMatch method matched)
          (not (isFinal matched))
        (doesNotOverrideFinalMethodInClasses (cdr supers) Method cl)))))

(defun doesNotOverrideFinalMethod (Class Method CL)
    (let* ((classname (classClassName Class))
           (superclasses (superClassChain classname cl)))
      (or (equal classname "java.lang.Object")
          (doesNotOverrideFinalMethodInClasses superclasses Method CL))))


(defun methodIsTypeSafe (Class CL Method)
  (let* ((AccessFlags (methodAccessFlags Method))
         (code  (methodCodeAttribute Method)))
    (and (doesNotOverrideFinalMethod Class Method CL)
         (or (mem '*abstract*  AccessFlags);; rule 1
             (mem '*native*  AccessFlags);; rule 2  
             (and (not (mem '*native*  AccessFlags));; rule 3
                  (not (mem '*abstract* AccessFlags))
                  (not (equal code nil))
                  (methodWithCodeIsTypeSafe Class Method CL))))))

   
   
(defun checklist-methodIsTypeSafe (class cl methods)
  (if (endp methods)
      t
    (and (prog2$ 
          (acl2::debug-print "Checking Method ~p0 in Class ~p1~%" 
                    (methodName (car methods)) (classClassName  class))
          (methodIsTypeSafe class cl (car methods)))
         (prog2$
          (acl2::debug-print "Check Method ~p0 Passed!~%~%" (methodName (car methods)))
          (checklist-methodIsTypeSafe class cl (cdr methods))))))
    
(defun classIsFinal (Class)
  (member '*final* (classAccessFlags Class)))

(defun classIsNotFinal (Class)
  (not (classIsFinal Class)))


(defun classIsTypeSafe (Class CL)
  (let ((Methods (classMethods Class))
        (Name    (classClassName class)))
    (prog2$
     (acl2::debug-print  "Checking class ~p0 ~%" (classClassName class))
     (and (isClassTerm Class)
          (or (equal Name "java.lang.Object")
              (let* ((superClassName (classSuperClassName Class))
                     (superClass (class-by-name superClassName CL)))
                (classIsNotFinal superClass)))
          (checklist-methodIsTypeSafe Class Cl Methods)))))


(defun bcv-sim (mcode env curframe n)
  (if (zp n)
      curframe
    (if (endp mcode)
        curframe
      (if (isStackMapFrame (car mcode))
          (prog2$
           (acl2::debug-print "saw a mapframe ~p0 ~%"(getMap (car mcode)))
           (if (equal curFrame 'aftergoto) 
               (bcv-sim (cdr mcode) env (mapFrame (getMap (car mCode))) (- n 1))
             (if (FrameIsAssignable curFrame (mapFrame (getMap (car mcode))) env)
                 (bcv-sim (cdr mcode) env (mapFrame (getMap (car mCode))) (- n 1))
               (acl2::debug-print "incompatible mapframe ~p0 ~% ~p1~%" curFrame (mapFrame (getMap (car mcode)))))))
        (if (isInstruction (car mcode))
            (if (instructionIsTypeSafe (car mcode) env curFrame)
                (prog2$ 
                 (acl2::debug-print "inst ~p0 OK~%----~%~p1~%===~%" (car mcode) curFrame)
                 (mv-let (nextframe exceptionframe)
                         (sig-do-inst (car mcode) env curframe)
                         (declare (ignore exceptionFrame))
                         (bcv-sim (cdr mcode) env nextframe  (- n 1))))
              (acl2::debug-print "inst ~p0 failed on ~p1~%" (car mcode) curframe))
          (if (isEnd (car mcode)) 
              (acl2::debug-print "Verification Succeed!~%")
            (acl2::debug-print "unknown sequence ~p0~%" mcode)))))))

(defun bcv-sim2 (method class cl n) 
  (let* ((FrameSize  (FrameSize method Class)) 
         (MaxStack   (MaxStack   Method Class))
         ;;(ByteCodeLength (ByteCodeLength Method Class))
         (ParsedCode (ParsedCode Method Class))
         (Handlers   (Handlers    Method Class))
         (StackMap   (StackMap   Method Class)))
    (let* ((MergedCode (mergeStackMapAndCode StackMap ParsedCode))
           (StackFrame (methodInitialStackFrame Class Method FrameSize))
           (ReturnType  (methodReturnType Method))
           (Environment (makeEnvironment Class Method ReturnType
                                         MergedCode MaxStack
                                         Handlers
                                         CL)))
      (bcv-sim mergedcode environment stackframe n))))
                


                    
   
;; (defun make-class-def (class)
;;   class)

;; I changed the file format of the output of jvm2acl2
;; to include better support for accessflags 
;; The classIsInterface field disappeared.
;;
;; either change the definition of make-class-def 
;; or make change to this typechecker.
;; 
;; chose to change this typechecker to reflect the change.
;; because to allow expansion, we need the better support for accessflag.
;; is this true??? -- no
;;
;; let's change make-class-def

(defun classname-s (scd)          (nth 1 scd))
(defun super-s     (scd)          (nth 2 scd))
(defun constantpool-s   (scd)     (cdr (nth 3 scd)))
(defun fields-s         (scd)     (cdr (nth 4 scd)))
(defun methods-s        (scd)     (cdr (nth 5 scd)))
(defun interfaces-s     (scd)     (cdr (nth 6 scd)))
(defun accessflags-s    (scd)     (cdr (nth 7 scd)))
(defun attributes-s     (scd)     (cdr (nth 8 scd)))

(defun make-class-def (raw-class)
  (make-class-term 
   (classname-s raw-class)
   (mem '*interface* (accessflags-s raw-class))
   (super-s     raw-class)
   (constantpool-s  raw-class)
   (interfaces-s    raw-class)
   (fields-s        raw-class)
   (methods-s       raw-class)
   (accessflags-s   raw-class)))


(defmacro make-static-class-decls (&rest cl)
  (cons 'list cl))


(defun verifyAll (l cl)
  (if (endp l)
      t
    (and (classIsTypeSafe (car l) cl)
         (verifyAll (cdr l) cl))))
                
                
(defun collectAllFailedClass (l cl)
  (if (endp l)
      nil
    (if (classIsTypeSafe (car l) cl)
        (collectAllFailedClass (cdr l) cl)
      (cons (classClassName (car l)) (collectAllFailedClass (cdr l) cl)))))
           
(defun abstract-parsedCode (c)
  (declare (ignore c))
  nil)

(defun abstract-methodCodeAttribute (m)
  (make-code-attribute-term
   (MaxStack1 m)
   (FrameSize1 m)
   (ByteCodeLength1 m)
   (abstract-parsedCode (ParsedCode1 m))
   (Handlers1   m)
   (StackMap1   m)))

(defun abstract-method-def (m)
  (make-method-term 
   (methodName m)
   (methodParameters m)
   (methodReturnType m)
   (methodAccessFlags m)
   (abstract-methodCodeAttribute 
    (methodCodeAttribute m))))
   


(defun abstract-method-defs (methods)
  (if (endp methods)
      nil
    (cons (abstract-method-def (car methods))
          (abstract-method-defs (cdr methods)))))


(defun abstract-class-def (c)
  (make-class-term 
   (classClassName c)
   (classIsInterface c)
   (classSuperClassName c)
   (classConstantPool c)
   (classInterfaces c)
   (classFields     c)
   (abstract-method-defs
    (classMethods    c))
   (classAccessFlags c)))

;; (defun abstract-class-def (c)
;;   (make-class-term 
;;    (classClassName c)
;;    (classIsInterface c)
;;    (classSuperClassName c)
;;    (classConstantPool c)
;;    (classInterfaces c)
;;    (classFields     c)
;;    (abstract-method-defs
;;     (classMethods    c))
;;    (classAccessFlags c)
;;    (classAttributes c)))

(defun abstract-class-defs (cl) 
  (if (endp cl) 
      nil
    (cons (abstract-class-def (car cl))
          (abstract-class-defs (cdr cl)))))


(defun abstract-class-table (ct)
  (abstract-class-defs ct))



#|
(defthm bcv-abs-bcv-concrete-equal 
  (iff (classIsTypeSafe c concrete-ct)
       (classIsTypeSafe c (abstract-class-table concrete-ct))))
|#

                
;----------------------------------------------------------------------

; Wed Aug 17 20:16:18 2005. 

(defun good-stack-maps (maps program)
  (if (endp maps) t
    (if (endp program) nil
      (let ((mpc (mapoffset (car maps)))
            (pc (instroffset (car program))))
        (if (equal mpc pc)
            (good-stack-maps (cdr maps) (cdr program))
          (if (< pc mpc)
              (good-stack-maps maps (cdr program))
            nil))))))


;----------------------------------------------------------------------





































