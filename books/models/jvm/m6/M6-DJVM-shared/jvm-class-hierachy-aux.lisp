(in-package "JVM")
(include-book "../M6-DJVM-shared/jvm-class-table")
(include-book "../M6-DJVM-shared/jvm-type-value")

(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

(acl2::set-verify-guards-eagerness 2)

;;; Tue Jan 13 15:43:53 2004 WE need some major fix of this. We need to reuse
;;; consistent-state's definition. 
;;; 
;;;; I don't think this will affect much. (It can) 
;;;;
;;;;; Major dependency in in jvm-linker!! 
;;;;; jvm-object-manipulation-primitives!!

;;;;; NOTE: isAssignableTo is the dynamic checking which is not using
;;;;; isSubclassOf at ALL!!



;; always need to think about whether we need to do guard verification for
;; this. 

;;; we need to use djvm-class-hierachy-aux.lisp instead of this one
;;;; We keep the folllowing because jvm-linker seems to be using those
;;;; definitions quite extensively.
;;;; We just prove under he consistent-class-hierachy-hyp. those two
;;;; definitions are the same. 

;;; Tue Jan 13 17:31:54 2004

(defun classClassName (class) 
  (declare (xargs :guard (wff-class-rep class)))
  (classname class))
    
(defun classSuperClassName (class)
  (declare (xargs :guard (wff-class-rep class)))
  (super class))


;; (defun all-class-names (cl)
;;   (declare (xargs :guard (wff-instance-class-table cl)))
;;   (if (endp cl)
;;       nil
;;     (cons (classClassName (car cl))
;;           (all-class-names (cdr cl)))))
;;; defined in jvm-class-table


(defun unseen-class-measure (seen cl)
  (declare (xargs :guard (and  (wff-instance-class-table cl)
                               (true-listp seen))))
  (len (set-diff (all-class-names cl) seen)))

(defun superclass-no-loop1-measure (seen cl)
  (declare (xargs :guard (and  (wff-instance-class-table cl)
                               (true-listp seen))))
  (len (set-diff (all-class-names cl) seen)))

(defthm class-by-name-all-class-names
  (implies (isClassTerm (class-by-name n1 cl)) 
           (mem n1 (all-class-names cl))))

(local (in-theory (disable isClassTerm class-by-name)))


;; (defthm mem-all-classname
;;   (implies (consp (class-by-name n1 cl))
;;            (mem n1 (all-class-names cl))))

(defun superclass-no-loop1 (n1 cl seen)
   (declare (xargs :guard (and (wff-instance-class-table cl)
                               (true-listp seen))
             :measure (superclass-no-loop1-measure seen cl)))
   (mylet* ((theClass (class-by-name n1 cl))
            (n2 (classSuperClassName theClass)))
           (if  (not (isClassTerm theClass)) t
             (if (mem n1 seen)
                 nil
               (superclass-no-loop1 n2 cl (cons n1 seen))))))


(defun superclass-no-loop (n1 cl)
   (declare (xargs :guard (wff-instance-class-table cl)))
  (superclass-no-loop1 n1 cl nil))




(defun collect-superclass-list1 (n1 cl ss)
  (declare (xargs :guard (and (wff-instance-class-table cl)
                              (true-listp ss))
            :measure (superclass-no-loop1-measure ss cl)))
  (mylet* ((theClass (class-by-name n1 cl))
           (n2 (classSuperClassName theClass)))
          (if (isClassTerm theClass)
              (if (mem n1 ss)
                  nil
                (cons n1 (collect-superclass-list1 n2 cl (cons n1 ss))))
            nil)))
          
(defun collect-superclass-list (n1 cl)
   (declare (xargs :guard (wff-instance-class-table cl)))
  (collect-superclass-list1 n1 cl nil))


(defun isSubClassOf1 (c1 c2 cl seen)
  (declare (xargs :guard (and (wff-instance-class-table cl)
                               (true-listp seen))
                  :measure (superclass-no-loop1-measure seen cl)))
  (mylet* ((theClass (class-by-name c1 cl))
         (n1 (classSuperClassName theClass)))
    (if  (not (isClassTerm theClass)) nil
      (if (mem c1 seen) nil
        (if (equal c1 c2)
            t
          (isSubClassOf1 n1
                         c2 
                         cl (cons c1 seen)))))))


(defun isJavaSubclassOf-guard (c1 c2 cl)
  (declare (xargs :verify-guards t))
  (and (consistent-class-hierachy cl)
       (isClassTerm (class-by-name c1 cl))
       (isClassTerm (class-by-name c2 cl))))
       

;; I would add isJavaSuclassOf with an extra seen parameter.  We need to prove
;; that under no loop hypothesis, with seen and without seen it is the
;; same. Basically, we proved it for bytecode verifier's isAssignable check.

(defun isJavaSubClassOf-measure (cl seen)
  (declare (xargs :guard (and (wff-instance-class-table cl)
                              (true-listp seen))))
  (unseen-classes cl seen))

;; 

;; (defthm consistent-class-hierachy-implies-wff-instance-class-table
;;   (implies (consistent-class-hierachy cl)
;;            (wff-instance-class-table cl)))


(defun isJavaSubclassof1 (c1 c2 cl seen)
  (declare (xargs :guard (and (consistent-class-hierachy cl)
                              (true-listp seen))
                  :measure (isJavasubclassOf-measure cl seen)))
  ;; I need to wff-instance-class-table assert this class-rep

  ;; I think for Defensive Machine I have the liberty to define
  ;; isJavaSubclassof with an extra parameter of seen

  ;;
  ;; 09/08/03 This is the test of the defensive machine's Class Hierachy!!
  ;; need special handling of termination ... 
  ;;
  ;; isJavaSubclassOf should be different from BCV's isJavaSubclassOf 
  ;; because class table are different (can we reuse it??)
  ;; We can define as long as two class table are equivalent in some
  ;; sense. isJavaSubclassOf will return the same value.
  ;; 
  ;; What do I want? 
  ;;
  ;; Decision reuses BCV's definition. We will need to the use static
  ;; class-table? 
  ;;
  ;;
  ;; redefining it is painful. 
  ;;
  ;; We need to prove current CL has some relation with BCV's SCL --- The
  ;; portion of class hierachy cl describes matches what is in scl which relies
  ;; on the correctness of class loader (relies on something we have proved)
  ;; 
  ;; The issue is whether I need to write a second class loader? should
  ;; defensive machine's loader check for more things? Can I reuse? Class
  ;; loader does not change opstack and locals, only change class table and
  ;; heap. and we decided to keep the heap and class table the same with
  ;; non-defensive version. So Good. we could reuse class-loader. (However, we
  ;; do we need to extend the current class loader to check class implement
  ;; what it declare to implement? NO. We don't. Runtime resolution will catch
  ;; that!!! So far so good. 
  ;; 
  ;; 
  ;; All superclass of c1 appears in cl 
  ;; 
  ;; Reuse BCV's version (however we need to make sure BCV's class table is in
  ;; some sense matches with non-defensive machine's class table (which add a
  ;; few extra fields.) 
  ;;
  (if (not (consistent-class-hierachy cl)) nil
    ;;; cheat??  ;; this for termination!! ;;; 
    ;;; Guard verification will allow get rid of it. 
    ;;;
  (and (class-exists? c1 cl) ;; 
       (class-exists? c2 cl) ;; this is for termination!!
       (not (mem c1 seen)) 
       (or (equal c1 c2)
           (let* ((SubClass (class-by-name c1 cl))
                  (c3 (super SubClass)))
             (isJavaSubclassOf1 c3 c2 cl (cons c1 seen)))))))

;; how guard works?? 

;; this function is easy to admit. 
;; Shall I use this definition? 
;; I could prove under the consistent-class-hierachy hyp. 
;; without test on seen it is admissible 
;; 
;; This proof is done for "typechecker.lisp"
;; SKIP.
;;
;; 
;; basically a collect-super cons subclass to seen does not matter. 
;;
;; What's the point of defining consistent-class-hierachy if it is not used to
;; justify the termination? It is used elsewhere...

(defun isJavaSubclassOf (c1 c2 cl)
  (declare (xargs :guard (and (consistent-class-hierachy cl)
                              (wff-class-rep c1) 
                              (wff-class-rep c2))))  ;;  10/28/03 
  ;; The parameter is class-rep instead of class name. 
  (isJavaSubclassOf1 (classname c1) (classname c2) cl nil))


(defun isJavaClassAssignmentCompatible (rtype type cl)
  (declare (xargs :guard (and (consistent-class-hierachy cl)
                              (class-exists? rtype cl)
                              (class-exists? type cl))))
  ;; make sure this function is only called when we know class-exists.
  ;;  09/09/03 
  
  ;; Assuming that rtype and type are both class names 
  ;; the most straightforward and precise result.
  ;; should I return a pair as a result? (complicated), return nil if not
  ;; valid.
  ;; 
  ;; invariant that rtype and type are bounded types. 
  ;;
  ;; here rtype and type are expect to be classnames.
  ;;
  ;; This function is only used in consistent-state predicate. We don't check
  ;; whether interface slots have correctly labeled value. (We can't guarantee
  ;; that in CLDC. In J2SE, maybe we could.
  ;;
  ;; Checking implementation relation in CLDC BCV and Defensive JVM is
  ;; weak. and delayed to runtime. 
  ;;
  (let ((SlotType  (class-by-name type cl))
        (ValueType (class-by-name rtype cl))) ;; BUG  10/28/03 
    (cond  ; ((or (class-exists? rtype cl)
           ;     (class-exists? type  cl)) nil)
           ;; make it explicit that above cause is nil
           ;;
           ;; Moved it to Guard. We are sure that this method is not even
           ;; called.        
           ;;

           ((isInterface SlotType)  t)
            ;; check for a marker in class description
            ;; if yes. Return t
            ;;
           (t (isJavaSubclassOf ValueType SlotType cl)))))

            ;;This needs an invariant that ValueType's supers all exists in cl
            ;; Because this is used in consistent-state. This should be
            ;; guaranteed. 
            ;;
            ;; Otherwise, the isSubclassOf's return value will not be accurate.

;; In consistent-state, it does not matter that we have an interface variable
;; that hold an value does not implement that interface. Check is done at the
;; runtime. BCV does not guarantee anything in that case. 

;; 


(defun isJavaAssignmentCompatible (rtype type cl)
  (declare (xargs :guard (consistent-class-hierachy cl)))
  ;; in this, we won't expect to see Oneword, or Twoword, or top
  ;; We don't even see rtype being byte, short, boolean
  ;; Because there are operations that implicit convert values.
  ;; Do we allow to assign an int to a long? no.
  ;; we have explicit instructions that does the convertion. (i2l, i2d)
  ;; however i2b, b2i doesn't change the type of value on the OPSTACK

  ;; FIX. rtype and type could be just a string. not always (class <something>)
  ;;  10/28/03.  

  (cond ((primitive-type? rtype) ;;; Thu Oct 21 18:07:53 2004
           (and 
            ;;(primitive-opvalue-type rtype)
            ;; Mon Oct 25 11:13:02 2004. fixed to match isAssignableTo
                (equal rtype type)))
          ((equal rtype 'NULL)
           ;; Do I want to write the most specific rule possible?
           ;; which means if type is not valid, I return nil
           ;; Decision, relaxing a bit. 
           ;; We can expect that type are valid type 
           ;;
           ;; reference-type-s ??
           ;;
           ;; let me check it at level of isAssignable level.
           ;;
           (or (isClassType type)
               (isArrayType type)))
          ;; this only assert that the synatx is
          ;; correct. To check whether something is really a class type, we may
          ;; need to check reference-type-s and array-type-s.
        
          ;; if I see NULL is type, still return nil
          ;; SlotType must be a valid type. 
          ((isClassType rtype)
           (and (isClassType type)
                (class-exists? (classname-classtype rtype) cl) 
                (class-exists? (classname-classtype type) cl)
                ;; added to make sure the guard of isJavaAssignmentCompatible is satisfied. 
                (isJavaClassAssignmentCompatible (classname-classtype rtype)
                                                 (classname-classtype type)
                                                 cl)))
          ((isArrayType rtype)
           (cond ((isClassType type)
                  (or (and 
                       (class-exists?  (classname-classtype type) cl)
                       (isInterface (class-by-name
                                         (classname-classtype type) cl)))
                      ;; treat differently as long as type is an interface, it
                      ;; will be assignable.
                      ;;
                      ;; IN BCV this is tested as whether rtype implement Array
                      ;; interface. 
                      ;;
                      (isJavaLangObject type)))
                 (t (and (isArrayType type)
                         (let ((x (component-type rtype))
                               (y (component-type type)))
                           (or (and (primitive-type? x)
                                    (primitive-type? y)
                                    (equal x y))
                               (and ;;(compound x)
                                    ;;(compound y) 
                                ;;; Mon Oct 25 10:52:40 2004. We fixed it 
                                ;;; so that class type does not have a "(class
                                ;;; prefix)"
                                (isJavaAssignmentCompatible x y cl))))))))))
               

(defun assignmentCompatible (rtype type cl)
  (declare (xargs :guard (consistent-class-hierachy cl)))

  ;; this assignmentCompable has to deal with interface proported to be
  ;; implemented actually get implemented?  No. We only use the information
  ;; from the class hierachy's tree.
  ;;
  ;; 
  ;; Maybe I should skip proof something to avoid the problem while still stick
  ;; with the dynamic loading in both defensive and non-defensive JVM?
  ;; 
  ;; THIS VERSION WILL WORK LIKE ISASSIGNABLE in BCV. 
  ;; WE NEED TO WRITE/REUSE THE VERSION IN THE NON-DEFENSIVE MACHINE
  ;; 
  ;; WE WILL MAKE SURE THIS VERSION DOES NOT CAUSE CLASS LOADING.
  ;; BECAUSE WE USE THIS TO EXPRESS THE CONSISTENT STATE concept.
  ;;
  ;; WE still need another version for test InstanceOf, AASTORE etc
  ;; (reuse non-defensive version)
  ;; 
  ;;
  ;; There are several ways to write AssignmentCompatible.  

  ;; One is copy BCV's
  ;; check (which is efficient, but it is not straight forward.
  (and (or (primitive-type? rtype) ;; Thu Oct 21 18:05:17 2004
           (reference-type-s rtype cl))
       (or (primitive-type? type)  ;; Thu Oct 21 18:05:20 2004
           (reference-type-s type cl))
       (isJavaAssignmentCompatible rtype type cl)))

;;;; Thu Oct 21 18:03:03 2004
;;;; The problem of primitive-type vs primitive-type?!! 


;; (defun assignmentCompatible (rtype type cl)
;;   (declare (xargs :guard (consistent-class-hierachy cl)))

;;   ;; this assignmentCompable has to deal with interface proported to be
;;   ;; implemented actually get implemented?  No. We only use the information
;;   ;; from the class hierachy's tree.
;;   ;;
;;   ;; 
;;   ;; Maybe I should skip proof something to avoid the problem while still stick
;;   ;; with the dynamic loading in both defensive and non-defensive JVM?
;;   ;; 
;;   ;; THIS VERSION WILL WORK LIKE ISASSIGNABLE in BCV. 
;;   ;; WE NEED TO WRITE/REUSE THE VERSION IN THE NON-DEFENSIVE MACHINE
;;   ;; 
;;   ;; WE WILL MAKE SURE THIS VERSION DOES NOT CAUSE CLASS LOADING.
;;   ;; BECAUSE WE USE THIS TO EXPRESS THE CONSISTENT STATE concept.
;;   ;;
;;   ;; WE still need another version for test InstanceOf, AASTORE etc
;;   ;; (reuse non-defensive version)
;;   ;; 
;;   ;;
;;   ;; There are several ways to write AssignmentCompatible.  

;;   ;; One is copy BCV's
;;   ;; check (which is efficient, but it is not straight forward.
;;   (and (or (primitive-type rtype)
;;            (reference-type-s rtype cl))
;;        (or (primitive-type type)
;;            (reference-type-s type cl))
;;        (isJavaAssignmentCompatible rtype type cl)))




;  The obligation of assignmentCompatible is 
; 
;  value of rtype is assignable to of "type" type
;
;  A PROOF needs to be ESTABLISHED 
;  
;  isAssignable? in the BCV is equal to assignmentCompatible
;  when type are well formed and  satisfy reference-type-s or primitive-type
;
; We need to prove assignmentCompatible is BCV's isAssignable 
; When class table is correctly loaded from env's class table and type refered
; is in side the system.
;
; However isAssignable uses the full spec of type (class "java.lang.Object")
; etc. assignmentCompatible in M3 use abbreviated "java.lang.Object" instead of
; (class "java.lang.Object")
;
;
; need to get the package name right!! 
;


;;; expecting some problem with the proofs in jvm-linker.... 
;;;; maybe we should keep it and prove these two definition will be same...

;; (defun isSubClassOf1 (c1 c2 cl seen)
;;   (declare (xargs :measure (superclass-no-loop1-measure seen cl)))
;;   (mylet* ((theClass (class-by-name c1 cl))
;;          (n1 (classSuperClassName theClass)))
;;     (if  (not (isClassTerm theClass)) nil
;;       (if (mem c1 seen) nil
;;         (if (equal c1 c2)
;;             t
;;           (isSubClassOf1 n1
;;                          c2 
;;                          cl (cons c1 seen)))))))


(defthm consistent-class-hierachy-implies-isSubClassOf1-is-isJavaSubclassOf1
  (implies (consistent-class-hierachy cl)
           (equal (isSubClassOf1 c1 c2 cl seen)
                  (isJavaSubclassOf1 c1 c2 cl seen))))


;--------------------------------------------------------------------
;
;  collect superclass with respect to ENV classtable 
;

;(i-am-here)

(defun all-class-names-s (cl)
  (declare (xargs :guard (wff-static-class-table cl)))
    (IF (not (consp CL))
        NIL
        (CONS (classname-s (CAR CL))
              (ALL-CLASS-NAMES-s (CDR CL)))))



(defun collect-superclassname1-measure (env-cl seen)
  (declare (xargs :guard (and (wff-static-class-table env-cl)
                              (true-listp seen))))
  (len (set-diff (all-class-names-s env-cl) seen)))

                          

(defthm found-implies-mem
  (mv-let (found class-desc)
          (class-by-name-s n1 env-cl)
          (declare (ignore class-desc))
          (implies found 
                   (mem n1 (all-class-names-s env-cl)))))
          

;; collect super class from env-class-table
(defun collect-superclassname1 (n1 env-cl seen)
  (declare (xargs :measure (collect-superclassname1-measure env-cl seen)
                  :guard (and (wff-static-class-table env-cl)
                              (true-listp seen))))
  (mv-let (found class-desc)
          (class-by-name-s n1 env-cl)
          (if found
              (if (mem n1 seen)
                  nil
                (cons n1 (collect-superclassname1 
                          (super-s class-desc) env-cl (cons n1 seen))))
            nil)))


(defun collect-superinterface1-measure (env-cl seen mode)
  (declare (xargs :guard (and (wff-static-class-table env-cl)
                              (true-listp seen))))
  (cons (cons (+ 1 (collect-superclassname1-measure env-cl seen) 1)
              0)
        mode))

(defun collect-interface-x-env-measusre (ns env-cl seen mode)
  (declare (xargs :guard (and (wff-static-class-table env-cl)
                              (true-listp seen))))
  (cond ((equal mode 1)
         (collect-superinterface1-measure env-cl seen 0))
        ((equal mode 2)
         (collect-superinterface1-measure env-cl seen (len ns)))
        (t 0)))
         


; ;;not good for proving propeties
; ;;
; ;; (mutual-recursion 
; ;;  (defun collect-superinterface1 (n1 env-cl seen)
; ;;    (declare (xargs :measure (collect-superinterface1-measure env-cl seen 0)))
; ;;   (mv-let (found class-desc)
;            (class-by-name-s n1 env-cl)
;            (let ((interfaces (interfaces-s class-desc))
;                  (super      (super-s      class-desc)))
;              (if (not found)
;                  nil
;                 (if (mem n1 seen)
;                     nil
;                   (app (cons n1 interfaces)
;                        (app (collect-superinterface1 super env-cl
;                                                      (cons n1 seen))
;                             (collect-superinterface2 interfaces env-cl 
;                                                      (cons n1 seen)))))))))
;  (defun collect-superinterface2 (ns env-cl seen)
;    (declare (xargs :measure (collect-superinterface1-measure env-cl seen 
;                                                              (len ns))))
;    (if (endp ns)
;        nil
;      (app (collect-superinterface1 (car ns) env-cl seen)
;           (collect-superinterface2 (cdr ns) env-cl seen)))))



(defun collect-interface-x-env (n1-or-ns env-cl seen mode)
  (declare (xargs :measure 
                  (collect-interface-x-env-measusre n1-or-ns env-cl
                                                    seen mode)
                  :guard (and (wff-static-class-table env-cl)
                              (true-listp seen))))
  (let ((n1 n1-or-ns)
        (ns n1-or-ns))
    (cond ((equal mode 1) ;; collect-superinterface1 
           (mv-let (found class-desc)
                   (class-by-name-s n1 env-cl)
                   (mylet* ((interfaces (interfaces-s class-desc))
                            (super      (super-s      class-desc)))
                     (if (not found)
                         nil
                       (if (mem n1 seen)
                           nil
                         (app (cons n1 interfaces)
                              (app (collect-interface-x-env  super env-cl
                                                             (cons n1 seen) 1)
                                   (collect-interface-x-env  interfaces env-cl 
                                                             (cons n1 seen)
                                                             2))))))))
          ((equal  mode 2) ;; collect-superinterface2
           (if (not (consp ns))
               nil
             (app (collect-interface-x-env (car ns) env-cl seen 1)
                  (collect-interface-x-env (cdr ns) env-cl seen 2))))
          (t nil))))
          
(defun collect-superinterface1 (n env-cl seen)
  (declare (xargs :guard (and (wff-static-class-table env-cl)
                              (true-listp seen))))
  (collect-interface-x-env n env-cl seen 1))

(defun collect-superinterface2 (ns env-cl seen)
  (declare (xargs :guard (and (wff-static-class-table env-cl)
                              (true-listp seen))))
  (collect-interface-x-env ns env-cl seen 2))


(defun collect-superclassname (classname env-cl)
  (declare (xargs :guard (wff-static-class-table env-cl)))
  (collect-superclassname1 classname env-cl nil))

(defun collect-superinterface (classname env-cl)
  (declare (xargs :guard (wff-static-class-table env-cl)))
  (collect-superinterface1 classname env-cl nil))
  


(defun collect-assignableToName (classname env-cl)
  (declare (xargs :guard (wff-static-class-table env-cl)))
  (cons classname 
        (app (collect-superclassname     classname env-cl)
             (collect-superinterface classname env-cl))))
  

;---------------------------------------------------------------------------

