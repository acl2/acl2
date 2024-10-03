;; Mon Dec 22 21:39:11 2003. This file defines WFF predicate and
;; consistent-state predicate. 
;;; Mon Dec 19 21:08:10 2005


(in-package "DJVM")
(include-book "../DJVM/djvm-state")
(include-book "../DJVM/djvm-env")
(include-book "../DJVM/djvm-class-table")
(include-book "../DJVM/djvm-thread")
(include-book "../DJVM/djvm-obj")
(include-book "../DJVM/djvm-type-value")
(include-book "../DJVM/djvm-linker")

(acl2::set-verify-guards-eagerness 2)

;; WFF predicate. Used as guard for accessors 
;; tagged-value is of form (tag . value)
;
;
;  First we define wff-tagged-value

; consistent-state for DJVM 


;; ;----------------------------------------------------------------------
;; ;
;; ;  TAG and VALUE


;; (defun wff-tagged-value (tagged-value)
;;   (declare (xargs :verify-guards t))
;;   (and (consp tagged-value)
;;        (equal (len tagged-value) 1))) 


;; (defun tag-of (tagged-value)
;;   (declare (xargs :guard (wff-tagged-value tagged-value)))
;;   (car tagged-value)) 

;; (defun value-of (tagged-value)
;;   (declare (xargs :guard (wff-tagged-value tagged-value)))
;;   (cdr tagged-value)) value-sig


;; ;----------------------------------------------------------------------

;; ;; Need a reference type predicate: 
;; (defun wff-REFp (ref)
;;   (declare (xargs :verify-guards t))
;;   ;; when we assert globally syntax correct.  we need assert wff-tagged-value
;;   ;; and appropriate wff-REFp like predicate.
;;   (and (wff-tagged-value ref)
;;        (equal (tag-of ref) 'REF)
;;        (integerp (value-of ref))))
;;        ;; we probably do not to assert (integerp (value-of ref))
;;        ;; because we never only use those as key into heap. 


;; (defun rREF (ref)
;;   (declare (xargs :guard (wff-REFp ref)))
;;   ;; make sure it is only called after we can establish ref is a wff-REFp
;;   (cdr ref))

;; ;; only called on wff-REFp

;; (defun NULLp (ref)
;;   (declare (xargs :verify-guards t))
;;   (and (wff-REFp ref)
;;        (equal (rREF ref) -1)))

;; ;----------------------------------------------------------------------

;; (defun wff-Heap (hp)
;;   (declare (xargs :verify-guards t))
;;   (alistp hp)) ;; minium requirement 


;; (defun Valid-REFp (ref hp)
;;   ;; somethin about consistency
;;   (declare (xargs :guard (wff-Heap hp)))
;;   (and (wff-REFp ref)
;;        (bound? (rREF ref) hp)))

;; ;; Note: We do not assert objected at (rREF ref) is a valid object. 
;; ;; Because that would cause mutual recurision. 
;; ;; We will be relying on the fact that every object in the heap is a
;; ;; valid-object (valid-object means its reference valued fields are REFp)

;; (defun REFp (ref hp)
;;   (declare (xargs :guard (wff-Heap hp)))
;;   ;; more semantic REF bounded! 
;;   (or (NULLp ref)
;;       (Valid-REFp ref hp)))

;; ;----------------------------------------------------------------------

;;; moved djvm-type-value
;;; should should

;; (defun deref2 (ref hp)
;;   (declare (xargs :guard (and (wff-Heap hp)
;;                               (Valid-REFp ref hp))))
;;   ;; never deref2 a non pointer. 
;;   ;; ensure our owm implementation is right. 
              
;;   (binding (rREF ref) hp))

;; We keep the represetation of Heap in M6 and DJVM to be the same! 

;----------------------------------------------------------------------


;; (defun wff-INT (tagged-value)
;;   (and (wff-tagged-value tagged-value)
;;        (equal  (tag-of tagged-value) 'INT)
;;        (integerp (value-of tagged-value)))) 


;; (defun Valid-INTp (tagged-value)
;;   (and (wff-INT tagged-value)
;;        (int32p (value-of tagged-value))))

;; ;;  int32p defined in primitive.lisp



;----------------------------------------------------------------------

;; (defun wff-class-table (cl)
;;   (declare (xargs :verify-guards t))
;;   (and (equal (len cl) 3)
;;        (true-listp cl)
;;        (consp (nth 1 cl))
;;        (consp (nth 2 cl))
;;        (equal (car (nth 1 cl)) 'instance-class-table)
;;        (equal (car (nth 2 cl)) 'array-class-table)))

;; moved to jvm-class-table.lisp in M6-DJVM-shared/
;; Tue Dec 23 01:20:31 2003

;;;;
;;
;; From jvm-class-table 
;;

;; does this depends on DJVM?? 
;; M6 does not check for this. 


;; (defun wff-array-type (arraytype)
;;   (declare (xargs :verify-guards t))
;;   (and (consp arraytype)
;;        (equal (car arraytype) 'ARRAY)
;;        (equal (len arraytype) 2)))

;; (defun array-component-type (arraytype)
;;   (declare (xargs :guard (wff-array-type arraytype)))
;;   (cadr arraytype))

;; (defun primitive-type (type)
;;   (declare (xargs :verify-guards t))
;;   (or (equal type 'INT)
;;       (equal type 'ADDR) ;; different from jvm's definition.
;;       (equal type 'BYTE)
;;       (equal type 'LONG)
;;       (equal type 'SHORT)
;;       (equal type 'CHAR)));; ARRAY-type MAY NEED THIS
;;                              ;; need to deal with LONG, etc.  

;; (defun primitive-opvalue-type (type) 
;;   (declare (xargs :verify-guards t))
;;    (or (equal type 'INT)
;;        (equal type 'ADDR)
;;        (equal type 'LONG)))


;;
;; Notice BYTE SHORT CHAR etc will not appear on the OPSTACK
;; they could only appear in ARRAY OBJECT's SPEC.
;;
;; For example: baload, bastore will convert byte into/back from integer.
;;

;; (mutual-recursion 
;;  (defun reference-type-s (type cl)
;;    ;; why reference-type-s should it just be reference-type
;;    ;; this recursive.
;;    (declare (xargs :guard (wff-instance-class-table cl)
;;                    :measure (cons (+ (acl2-count type) 1) 1)))
;;    (or (equal type 'NULL) ;; never used. ;; we represent NULL with (REF . -1)
;;        (array-type-s type cl)
;;        (class-exists? type cl)))
 
;;  (defun array-type-s (type cl)
;;    (declare (xargs :guard (wff-instance-class-table cl)
;;                    :measure (cons (+ (acl2-count type) 1) 0)))
;;    (and (wff-array-type type)
;;         (or (primitive-type (array-component-type type))
;;             (reference-type-s (array-component-type type) cl)))))


;; How to deal with isArrayType does it recursively check for component type
;; being a either a primitive type or reference-type

;; We need to able to say, all values in a consistent-state have proper type.
;;
;; The difference with M3, is handling of NULL type and ARRAY 
;;
;; Can we have an array of NULL in the defensive machine? 

;----------------------------------------------------------------------
;
; The question is now do we want to write a completely different set of
; class-exists? class-by-name primitives. (because the domain of their
; application will be different. Will it be different?? (Can we keep the class
; table and heap the same? (in Defensive and non defensive machine?)
; 
;  Only on OPSTACK and LOCALS, we need TAG information to distinguish INT from
;  FLOAT or RETURN ADDRESS and HEAP REFERENCE (since we only support int, so
;  only need to distinguish. Since we put a (REF . pointer) around a ref value,
;  we may as well put an (INT . value) around an int value. to make it more
;  uniform. 
;
;  We could keep heap and class table, thread table the same (even ref doesn't
;  has (REF . pointer) around a pointer. (because from the class table we know
;  the type!! SAVE some work of untagging. We need to implement getfield and
;  putfield correctly to deal with what type of object it is putting out. 
;  
;  Decision: keep the heap and class table the same. Special care about
;  consistent-heap and consistent-class-table predicate (need fix)
;  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;(ld "../M6/no-dup-set-facts.lisp")

;;; the following is consistent-class-hierachy!! move to djvm-class-table!!


;; (defun all-class-names (cl)
;;   (declare (xargs :guard (wff-instance-class-table cl)))
;;   (if (not (consp cl)) nil
;;     (cons (classname (car cl))
;;           (all-class-names (cdr cl)))))


;; (defun unseen-classes (cl seen)
;;   (declare (xargs :measure (wff-instance-class-table cl)
;;                   :guard (and (wff-instance-class-table cl)
;;                               (true-listp seen))))
;;   (len (set-diff (all-class-names cl) seen)))

;; (defun unseen-classes-x (ns cl seen mode)
;;   (declare (xargs :guard (and (wff-instance-class-table cl)
;;                               (true-listp seen))))
;;   (cond ((equal mode 'NODE) (cons (cons (+ 1 (unseen-classes cl seen)) 0) 0))
;;         ((equal mode 'LIST) (cons (cons (+ 1 (unseen-classes cl seen)) 0) 
;;                                   (len ns)))
;;         (t 0)))

;; ;; 
;; ;;



;; ;; (defun isInterfaceType (class-decl)
;; ;;   (declare (xargs :guard (wff-class-rep class-decl)))
;; ;;   (mem '*interface* (class-accessflags class-decl)))


;; (defun all-interfaces-bounded? (interfaces cl)
;;   (declare (xargs :guard (wff-instance-class-table cl)))
;;   (if (not (consp interfaces)) t
;;     (and (class-exists? (car interfaces) cl)
;;          (isInterface (class-by-name (car interfaces) cl))
;;          (all-interfaces-bounded? (cdr interfaces) cl))))




;; (defun class-hierachy-consistent1-class-n (n cl)
;;   ;; 
;;   ;; 1. super ends with "java.lang.Object" 
;;   ;; 2. interfaces all bounded and are in fact interfaces.
;;   ;; 3. Somewhere we need to assert no loop
;;   ;;
;;   ;;
;;   (declare (xargs :guard (wff-instance-class-table cl)))
;;   (and (class-exists? n cl)
;;        (if (equal n "java.lang.Object")
;;            (let ((class-rep (class-by-name n cl)))
;;              (and (not (class-exists? (super class-rep) cl))
;;                   (all-interfaces-bounded? (interfaces class-rep) cl)))
;;          (let ((class-rep (class-by-name n cl)))
;;            (and (class-exists? (super class-rep) cl)
;;                 (all-interfaces-bounded? (interfaces class-rep) cl))))))


;; ; (defun subseqx (l1 l2)
;; ;   (declare (xargs :verify-guards t))
;; ;   (if (equal l1 l2) t
;; ;     (if (not (consp l2)) nil
;; ;         (subseqx l1 (cdr l2)))))



;; ; (defthm wff-instance-class-table-hireachy-wff-class-rep
;; ;   (implies (and (class-exists? n cl)
;; ;                 (wff-instance-class-table cl))
;; ;            (wff-class-rep (class-by-name n cl))))


;; (defun class-hierachy-consistent1-aux (classes cl)
;;   (declare (xargs :guard (and (wff-instance-class-table cl)
;;                               (wff-instance-class-table classes))))
;;   (if (not (consp classes)) t
;;     (and (class-hierachy-consistent1-class-n (classname (car classes)) cl)
;;          ;;; NOTE: Here using (class (car classes)) is different from testing
;;          ;;; (car classes). Current usage allows some invalid description in
;;          ;;; class-table. Otherwise we need to assert no-dups explicitly
;;          ;;; We are using the same interface to assert property then it is
;;          ;;; good. 
;;          (class-hierachy-consistent1-aux (cdr classes) cl))))


;; (defun class-hierachy-consistent1 (cl)
;;   (declare (xargs :guard (wff-instance-class-table cl)))
;;   (class-hierachy-consistent1-aux cl cl)) 
;;   ;;
;;   ;; this only assert the fact that no class-rep refers an undefined 
;;   ;; entity in super field and interfaces field
;;   ;;
;;   ;; Thus self contained. 


;; (defthm class-exists?-implies-mem-all-class-names 
;;   (implies (and (class-exists? n cl)
;;                 (wff-instance-class-table cl))
;;            (mem n (all-class-names cl))))


;; ;;  
;; (defun superclass-chain-no-loop-class-n (n1 cl seen)
;;   (declare (xargs :guard (and (wff-instance-class-table cl)
;;                               (true-listp seen))
;;                   :measure (unseen-classes cl seen)))
;;   ;;
;;   ;; for termination, I also need cl is wff-instance-class-table we need to be
;;   ;; able to show n1 if bounded, then it is a member of all classes
;;   ;;
;;   (if (not (wff-instance-class-table cl)) nil
;;     (if (not (class-exists? n1 cl)) t
;;       (if (mem n1 seen) nil
;;         (let ((n2 (super (class-by-name n1 cl))))
;;           ;; this definition is a trickier. 
;;           ;; termination should be ok.
;;           (superclass-chain-no-loop-class-n n2 cl (cons n1 seen)))))))


;; ;; I could merge this with the above one.  09/08/03 
;; (defun interfaces-chains-no-loop-class-n (n-or-ns cl seen mode)
;;   (declare (xargs :guard (and (wff-instance-class-table cl)
;;                               (true-listp seen))
;;                   ;; I could assert stronger guard such as 
;;                   ;; all n, ns are also bounded. 
;;                   :measure (unseen-classes-x n-or-ns cl seen mode)))
;;   (let ((n  n-or-ns)
;;         (ns n-or-ns)) 
;;     (if (not (wff-instance-class-table cl)) nil 
;;       ;; need for termintation!!
;;       (cond ((equal mode 'NODE)
;;              (if (not (class-exists? n cl)) t
;;                (if (mem n seen) nil
;;                    (let ((ns (interfaces (class-by-name n cl))))
;;                      (interfaces-chains-no-loop-class-n
;;                       ns cl (cons n seen) 'LIST)))))
;;             ((equal mode 'LIST)
;;              (if (not (consp ns)) t
;;                (and (interfaces-chains-no-loop-class-n (car ns) cl seen 'NODE)
;;                     (interfaces-chains-no-loop-class-n (cdr ns) cl seen 'LIST))))))))



;; (defun class-hierachy-consistent2-class-n (n cl)
;;   (declare (xargs :guard (wff-instance-class-table cl)))
;;   ;; this one I want to assert no loop through superclass chain and super
;;   ;; interface chain.
;;   ;;
;;   ;; The problem is shall I mix this part with the other part?   
;;   ;; 
;;   ;; Shall I assert all interface's super must be java.lang.Object?
;;   (and (superclass-chain-no-loop-class-n n cl nil)
;;        (interfaces-chains-no-loop-class-n n cl nil 'NODE)))


;; (defun class-hierachy-consistent2-aux (classes cl)
;;   (declare (xargs :guard (and (wff-instance-class-table classes)
;;                               (wff-instance-class-table cl))))
;;   (if (not (consp classes)) t
;;     (and (class-hierachy-consistent2-class-n (classname (car classes)) cl)
;;          (class-hierachy-consistent2-aux  (cdr classes) cl))))

;; (defun class-hierachy-consistent2 (cl)
;;   (declare (xargs :guard (wff-instance-class-table cl)))
;;   (class-hierachy-consistent2-aux cl cl))


;; ;; The third thing we need to assert about the internal class table is 
;; ;; it is in fact loaded from the external class table. 
;; ;; We only need to assert, class hierachy is not changed! tags of value in the
;; ;; consistent pool is not changed. 
;; ;; 
;; ;; We also need to assert that static field's type all right? No we don't 
;; ;; if Static field doesn't exist, we could just thrown an error in both
;; ;; machine. However a sensible JVM implementation of loader should load that
;; ;; field correctly. (part of the correctness of loader then) 
;; ;;
;; ;; WE DON'T EVEN NEED TO ASSERT FIELDS ARE ALL RIGHT. BECAUSE EVERYTHING IS
;; ;; ENCODED IN THE FIELD CP.  09/09/03 ??? REALLY???  THE ASSIGNMENT COMPATIBLE
;; ;; TEST IS DONE AFTER RESOLUTION. RESOLUTION IS GUARANTEED TO FIND THE RIGHT
;; ;; TYPE. IN BCV, NO RESOLUTION IS DONE. BCV JUST TRUST AT RUNTIME RESOLUTION
;; ;; PROCEDURE WILL FIND THE FIELD OF RIGHT TYPE.

;; (defun consistent-class-hierachy (cl)
;;   (declare (xargs :verify-guards t))
;;   ;; although 
;;   (and (wff-instance-class-table cl)
;;        (class-hierachy-consistent1 cl)
;;        (class-hierachy-consistent2 cl)))


;----------------------------------------------------------------------


;----------------------------------------------------------------------


;; (defun constantpool-loaded-from (cpentries cpentries-s)
;;   (declare (xargs :guard (and (wff-constant-pool cpentries)
;;                               (wff-constant-pool-s cpentries-s))))
;;   (cond ((not (consp cpentries)) (not (consp cpentries-s)))
;;         ((not (consp cpentries-s)) nil)
;;         (t (and (equal (cpentry-type (car cpentries))
;;                        (cpentry-type-s (car cpentries-s)))
;;                 (constantpool-loaded-from (cdr cpentries)
;;                                           (cdr cpentries-s))))))

;; ;; (defun wff-class-rep-static (class-rep)
;; ;;   (declare (xargs :verify-guards t))
;; ;;   (and (true-listp class-rep)
;; ;;        (equal (len class-rep) 8)
;; ;;        (equal (car class-rep) 'class) 
;; ;;        (consp (nth 3 class-rep))
;; ;;        (consp (nth 4 class-rep))
;; ;;        (consp (nth 5 class-rep))
;; ;;        (consp (nth 6 class-rep))
;; ;;        (consp (nth 7 class-rep))
;; ;;        (true-listp (cdr (nth 3 class-rep)))
;; ;;        (true-listp (cdr (nth 4 class-rep)))
;; ;;        (true-listp (cdr (nth 5 class-rep)))
;; ;;        (true-listp (cdr (nth 6 class-rep)))
;; ;;        (true-listp (cdr (nth 7 class-rep)))))

;; ;; moved to jvm-env


;; (defun wff-class-rep-strong (class-rep)
;;   (and (wff-class-rep class-rep)
;;        (wff-constant-pool (constantpool class-rep))))


;; (defun wff-class-rep-static-strong (class-rep)
;;   (and (wff-class-rep-static class-rep)
;;        (wff-constant-pool-s (constantpool-s class-rep))))


;; (defun class-is-loaded-from-helper (class-rep class-rep-static)
;;   (declare (xargs :guard (and (wff-class-rep-strong class-rep) 
;;                               (wff-class-rep-static-strong class-rep-static))))
;;   (and (equal (classname  class-rep) (classname-s  class-rep-static))
;;        (equal (super      class-rep) (super-s      class-rep-static))
;;        (equal (interfaces class-rep) (interfaces-s class-rep-static))
;;        ;; we also need the access flags are preserved 
;;        (equal (class-accessflags class-rep) (accessflags-s class-rep-static))
;;        (constantpool-loaded-from (constantpool class-rep)
;;                                  (constantpool-s class-rep-static))))
;;        ;; this also stipulated whether is it an interface type or not.


;; (defun wff-static-class-table (scl)
;;   (declare (xargs :verify-guards t))
;;   (if (not (consp scl)) t
;;     (and (wff-class-rep-static (car scl))
;;          (wff-static-class-table (cdr scl)))))

;; (defun wff-instance-class-table-strong (icl)
;;   (declare (xargs :verify-guards t))
;;   (if (not (consp icl)) t 
;;     (and (wff-class-rep-strong (car icl))
;;          (wff-instance-class-table-strong (cdr icl)))))



;; (defun wff-static-class-table-strong (scl)
;;   (declare (xargs :verify-guards t))
;;   (if (not (consp scl)) t
;;     (and (wff-class-rep-static-strong (car scl))
;;          (wff-static-class-table-strong (cdr scl)))))


;; ;; (defun class-by-name-s (name scl)
;; ;;   (declare (xargs :guard (wff-static-class-table scl)))
;; ;;   (if (not (consp scl))
;; ;;       (mv nil nil)
;; ;;     (if (equal (classname-s (car scl))
;; ;;                name)
;; ;;         (mv t (car scl))
;; ;;       (class-by-name-s name (cdr scl)))))


;; (defun class-exists-s? (n scl)
;;   (declare (xargs :guard (wff-static-class-table scl)))
;;   (mv-let (found rep)
;;           (class-by-name-s n scl)
;;           (declare (ignore rep))
;;           found))

;; (defthm class-exists-s-implies-wff-static-rep
;;    (implies (and (class-exists-s? n scl)
;;                  (wff-static-class-table-strong scl))
;;             (wff-class-rep-static-strong (mv-let (found rep)
;;                                                  (class-by-name-s n scl)
;;                                                  (declare (ignore found))
;;                                                  rep))))


;; (defthm class-exists-implies-wff-rep-strong
;;    (implies (and (class-exists? n cl)
;;                  (wff-instance-class-table-strong cl))
;;             (wff-class-rep-strong (class-by-name n cl))))


;; (defthm wff-class-rep-strong-is-strong
;;   (implies (wff-class-rep-strong rep)
;;            (wff-class-rep rep))
;;   :rule-classes :forward-chaining)

;; (defthm wff-instance-class-table-strong-is-strong
;;   (implies (wff-instance-class-table-strong cl)
;;            (wff-instance-class-table cl))
;;   :rule-classes :forward-chaining)


;; (defthm wff-static-class-table-strong-is-strong
;;   (implies (wff-static-class-table-strong scl)
;;            (wff-static-class-table scl))
;;   :rule-classes :forward-chaining)


;; ;; (defthm wff-static-class-table-strong-is-strong-tmp
;; ;;   (implies (wff-static-class-table-strong scl)
;; ;;            (jvm::wff-static-class-table scl))
;; ;;   :rule-classes :forward-chaining)


;; (defthm wff-class-static-rep-strong-is-strong
;;   (implies (wff-class-rep-static-strong rep)
;;            (wff-class-rep-static rep))
;;   :rule-classes :forward-chaining)



;; ;(in-theory (disable wff-class-rep-static-strong wff-class-rep-strong
;; ;                    wff-class-rep
;; ;                    class-exists? class-by-name class-by-name-s class-exists-s?))

;; ;; These are too general!!

;; (defthm wff-class-rep-if-exists-in-wff-instance-table
;;   (implies (and (class-exists? n cl)
;;                 (wff-instance-class-table cl))
;;            (wff-class-rep (class-by-name n cl))))



;; (defun class-table-is-loaded-from (cl scl)
;;   (declare (xargs :guard (and (wff-instance-class-table-strong cl)
;;                               (wff-static-class-table-strong scl))))
;;   (if (not (consp cl)) t
;;     (and (class-exists? (classname (car cl)) cl)
;;          (class-exists-s? (classname (car cl)) scl)
;;          (mv-let (def-found rep)
;;                  (class-by-name-s (classname (car cl)) scl)
;;                  (declare (ignore def-found))
;;                  (class-is-loaded-from-helper (class-by-name (classname (car cl)) cl)
;;                                               rep))
;;          (class-table-is-loaded-from (cdr cl) scl))))

;; ;; we chose not to disable those functions. ACL2 will get it anyway!

;;;; moved to djvm-class-table


;;
;; If we know class-hierachy-consistent 
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; We need to move this to 

;; (defun isJavaSubclassOf-guard (c1 c2 cl)
;;   (declare (xargs :verify-guards t))
;;   (and (consistent-class-hierachy cl)
;;        (isClassTerm (class-by-name c1 cl))
;;        (isClassTerm (class-by-name c2 cl))))
       

;; ;; I would add isJavaSuclassOf with an extra seen parameter.  We need to prove
;; ;; that under no loop hypothesis, with seen and without seen it is the
;; ;; same. Basically, we proved it for bytecode verifier's isAssignable check.

;; (defun isJavaSubClassOf-measure (cl seen)
;;   (declare (xargs :guard (and (wff-instance-class-table cl)
;;                               (true-listp seen))))
;;   (unseen-classes cl seen))


;; (defun isJavaSubclassof1 (c1 c2 cl seen)
;;   (declare (xargs :guard (and (consistent-class-hierachy cl)
;;                               (true-listp seen))
;;                   :measure (isJavasubclassOf-measure cl seen)))
;;   ;; I need to wff-instance-class-table assert this class-rep

;;   ;; I think for Defensive Machine I have the liberty to define
;;   ;; isJavaSubclassof with an extra parameter of seen

;;   ;;
;;   ;; 09/08/03 This is the test of the defensive machine's Class Hierachy!!
;;   ;; need special handling of termination ... 
;;   ;;
;;   ;; isJavaSubclassOf should be different from BCV's isJavaSubclassOf 
;;   ;; because class table are different (can we reuse it??)
;;   ;; We can define as long as two class table are equivalent in some
;;   ;; sense. isJavaSubclassOf will return the same value.
;;   ;; 
;;   ;; What do I want? 
;;   ;;
;;   ;; Decision reuses BCV's definition. We will need to the use static
;;   ;; class-table? 
;;   ;;
;;   ;;
;;   ;; redefining it is painful. 
;;   ;;
;;   ;; We need to prove current CL has some relation with BCV's SCL --- The
;;   ;; portion of class hierachy cl describes matches what is in scl which relies
;;   ;; on the correctness of class loader (relies on something we have proved)
;;   ;; 
;;   ;; The issue is whether I need to write a second class loader? should
;;   ;; defensive machine's loader check for more things? Can I reuse? Class
;;   ;; loader does not change opstack and locals, only change class table and
;;   ;; heap. and we decided to keep the heap and class table the same with
;;   ;; non-defensive version. So Good. we could reuse class-loader. (However, we
;;   ;; do we need to extend the current class loader to check class implement
;;   ;; what it declare to implement? NO. We don't. Runtime resolution will catch
;;   ;; that!!! So far so good. 
;;   ;; 
;;   ;; 
;;   ;; All superclass of c1 appears in cl 
;;   ;; 
;;   ;; Reuse BCV's version (however we need to make sure BCV's class table is in
;;   ;; some sense matches with non-defensive machine's class table (which add a
;;   ;; few extra fields.) 
;;   ;;
;;   (if (not (consistent-class-hierachy cl)) nil
;;     (and (class-exists? c1 cl)
;;          (class-exists? c2 cl)
;;          (not (mem c1 seen))
;;          (or (equal c1 c2)
;;              (let* ((SubClass (class-by-name c1 cl))
;;                     (c3 (super SubClass)))
;;                (isJavaSubclassOf1 c3 c2 cl (cons c1 seen)))))))

;; ;; how guard works?? 

;; ;; this function is easy to admit. 
;; ;; Shall I use this definition? 
;; ;; I could prove under the consistent-class-hierachy hyp. 
;; ;; without test on seen it is admissible 
;; ;; 
;; ;; This proof is done for "typechecker.lisp"
;; ;; SKIP.
;; ;;
;; ;; 
;; ;; basically a collect-super cons subclass to seen does not matter. 
;; ;;
;; ;; What's the point of defining consistent-class-hierachy if it is not used to
;; ;; justify the termination? It is used elsewhere...

;; (defun isJavaSubclassOf (c1 c2 cl)
;;   (declare (xargs :guard (and (consistent-class-hierachy cl)
;;                               (wff-class-rep c1) 
;;                               (wff-class-rep c2))))  ;;  10/28/03 
;;   ;; The parameter is class-rep instead of class name. 
;;   (isJavaSubclassOf1 (classname c1) (classname c2) cl nil))


;; (defun isJavaClassAssignmentCompatible (rtype type cl)
;;   (declare (xargs :guard (and (consistent-class-hierachy cl)
;;                               (class-exists? rtype cl)
;;                               (class-exists? type cl))))
;;   ;; make sure this function is only called when we know class-exists.
;;   ;;  09/09/03 
  
;;   ;; Assuming that rtype and type are both class names 
;;   ;; the most straightforward and precise result.
;;   ;; should I return a pair as a result? (complicated), return nil if not
;;   ;; valid.
;;   ;; 
;;   ;; invariant that rtype and type are bounded types. 
;;   ;;
;;   ;; here rtype and type are expect to be classnames.
;;   ;;
;;   ;; This function is only used in consistent-state predicate. We don't check
;;   ;; whether interface slots have correctly labeled value. (We can't guarantee
;;   ;; that in CLDC. In J2SE, maybe we could.
;;   ;;
;;   ;; Checking implementation relation in CLDC BCV and Defensive JVM is
;;   ;; weak. and delayed to runtime. 
;;   ;;
;;   (let ((SlotType  (class-by-name type cl))
;;         (ValueType (class-by-name rtype cl))) ;; BUG  10/28/03 
;;     (cond  ; ((or (class-exists? rtype cl)
;;            ;     (class-exists? type  cl)) nil)
;;            ;; make it explicit that above cause is nil
;;            ;;
;;            ;; Moved it to Guard. We are sure that this method is not even
;;            ;; called.        
;;            ;;

;;            ((isInterface SlotType)  t)
;;             ;; check for a marker in class description
;;             ;; if yes. Return t
;;             ;;
;;            (t (isJavaSubclassOf ValueType SlotType cl)))))

;;             ;;This needs an invariant that ValueType's supers all exists in cl
;;             ;; Because this is used in consistent-state. This should be
;;             ;; guaranteed. 
;;             ;;
;;             ;; Otherwise, the isSubclassOf's return value will not be accurate.

;; ;; In consistent-state, it does not matter that we have an interface variable
;; ;; that hold an value does not implement that interface. Check is done at the
;; ;; runtime. BCV does not guarantee anything in that case. 

;; ;; 

;; Tue Jan 13 01:17:04 2004 moved to djvm-class-hierachy-aux.lisp

;; (defun isClassType (t1)
;;   (stringp t1)) 
;; ;; FIXED  10/28/03 for the wrong assumption in isJavaAssignmentCompatible
;; ;; originally t1 was expected to be (class <something>)
;; ;; 

;; (defun isArrayType (t1)
;;   (and (consp t1)
;;        (equal (len t1) 2)
;;        (equal (car t1) 'array)))


;; (defun wff-type-desc (type-desc)
;;   (or (primitive-type type-desc)
;;       (isClassType type-desc)
;;       (isArrayType type-desc)))
;; ;;

;; (defun classname-classtype (ctype)
;;   (declare (xargs :guard (isClassType ctype)))
;;   ctype) ;; FIXED  10/28/03. see above fix for isClassType

;; (defun compound (x)
;;   (consp x))

;; (defun isJavaLangObject (type)
;;   (equal type '(class  "java.lang.Object")))

;; ; -- used only on arrayType
;; (defun component-type (aArrayType)
;;   (declare (xargs :guard (isArrayType aArrayType)))
;;   (cadr aArrayType))

;; Need to decide whether to write use the same set of functions and (prove
;; class tables are in some sense equivalent in BCV and 
;;
;;; DJVM's test!!

;; (defun isJavaAssignmentCompatible (rtype type cl)
;;   (declare (xargs :guard (consistent-class-hierachy cl)))
;;   ;; in this, we won't expect to see Oneword, or Twoword, or top
;;   ;; We don't even see rtype being byte, short, boolean
;;   ;; Because there are operations that implicit convert values.
;;   ;; Do we allow to assign an int to a long? no.
;;   ;; we have explicit instructions that does the convertion. (i2l, i2d)
;;   ;; however i2b, b2i doesn't change the type of value on the OPSTACK

;;   ;; FIX. rtype and type could be just a string. not always (class <something>)
;;   ;;  10/28/03.  

;;   (cond ((primitive-type rtype)
;;            (and (primitive-opvalue-type rtype)
;;                 (equal rtype type)))
;;           ((equal rtype 'NULL)
;;            ;; Do I want to write the most specific rule possible?
;;            ;; which means if type is not valid, I return nil
;;            ;; Decision, relaxing a bit. 
;;            ;; We can expect that type are valid type 
;;            ;;
;;            ;; reference-type-s ??
;;            ;;
;;            ;; let me check it at level of isAssignable level.
;;            ;;
;;            (or (isClassType type)
;;                (isArrayType type)))
;;           ;; this only assert that the synatx is
;;           ;; correct. To check whether something is really a class type, we may
;;           ;; need to check reference-type-s and array-type-s.
        
;;           ;; if I see NULL is type, still return nil
;;           ;; SlotType must be a valid type. 
;;           ((isClassType rtype)
;;            (and (isClassType type)
;;                 (class-exists? (classname-classtype rtype) cl) 
;;                 (class-exists? (classname-classtype type) cl)
;;                 ;; added to make sure the guard of isJavaAssignmentCompatible is satisfied. 
;;                 (isJavaClassAssignmentCompatible (classname-classtype rtype)
;;                                                  (classname-classtype type)
;;                                                  cl)))
;;           ((isArrayType rtype)
;;            (cond ((isClassType type)
;;                   (or (and 
;;                        (class-exists?  (classname-classtype type) cl)
;;                        (isInterface (class-by-name
;;                                          (classname-classtype type) cl)))
;;                       ;; treat differently as long as type is an interface, it
;;                       ;; will be assignable.
;;                       ;;
;;                       ;; IN BCV this is tested as whether rtype implement Array
;;                       ;; interface. 
;;                       ;;
;;                       (isJavaLangObject type)))
;;                  (t (and (isArrayType type)
;;                          (let ((x (component-type rtype))
;;                                (y (component-type type)))
;;                            (or (and (primitive-type x)
;;                                     (primitive-type y)
;;                                     (equal x y))
;;                                (and (compound x)
;;                                     (compound y)
;;                                     (isJavaAssignmentCompatible x y cl))))))))))
               

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


;; ;  The obligation of assignmentCompatible is 
;; ; 
;; ;  value of rtype is assignable to of "type" type
;; ;
;; ;  A PROOF needs to be ESTABLISHED 
;; ;  
;; ;  isAssignable? in the BCV is equal to assignmentCompatible
;; ;  when type are well formed and  satisfy reference-type-s or primitive-type
;; ;
;; ; We need to prove assignmentCompatible is BCV's isAssignable 
;; ; When class table is correctly loaded from env's class table and type refered
;; ; is in side the system.
;; ;
;; ; However isAssignable uses the full spec of type (class "java.lang.Object")
;; ; etc. assignmentCompatible in M3 use abbreviated "java.lang.Object" instead of
;; ; (class "java.lang.Object")
;; ;
;; ;
;; ; need to get the package name right!! 
;; ;


; (defun correctly-loaded? (classname class-table env-class-table)
;   (mv-let (found class-rep-static)
;           (class-by-name-s classname env-class-table)
;           (declare (ignore found))
;           (and (class-is-loaded? classname class-table)
;                (class-is-loaded-from 
;                                  (class-by-name classname class-table) 
;                                  class-rep-static))))
;
; (defun all-correctly-loaded? (supers class-table env-class-table)
;   (if (endp supers)
;       t
;     (and (correctly-loaded? (car supers) class-table env-class-table)
;          (all-correctly-loaded? (cdr supers) class-table env-class-table))))
;
; (defun loader-inv-helper1 (class-rep class-table env-class-table)
;   (let* ((classname (classname class-rep))
;          (supers    (collect-assignableToName classname env-class-table)))
;     (all-correctly-loaded? supers class-table env-class-table))) 
;
;
; (defun loader-inv-helper (classes class-table env-class-table)
;   (if (endp classes)
;       t
;     (and (loader-inv-helper1 (car classes) class-table env-class-table)
;          (loader-inv-helper (cdr classes) class-table env-class-table))))


; (defun class-is-loaded-from (cl scl)
;   (m6::loader-inv-helper cl cl scl))


; (defun class-is-loaded-from (cl scl)

;   (m6::loader-inv-helper cl cl scl))


;; SKIP-PROOFS

; (skip-proofs 
;  (defthm isAssignable-and-valid-class-table-implies-assignmentCompatible
;    (implies (and (bcv::isAssignable from to env)
;                  (equal (bcv::classtableEnvironment env) scl)
;                  (class-table-loaded-from cl scl)
;                  (class-exists? from cl)
;                  (class-exists? to cl))
;             ;; however from, to must be the full type spec.
;             ;; need to tweak assignmentCompatible.
;             ;; however concept class-is-defined has not been defined.
;             ;; nor class-table-loaded-from is defined so far. August 12, 2003
;             (assignmentCompatible from to cl))))

;;; 
;;; WE PROBABLY WANT TO DEFINE THIS ASSIGNMENT COMPATIBLE with respect to SCL
;;; instead of the RUNTIME cl.  08/27/03 
;;; 
;;; HOWEVER MY CURRENT IMPLEMENTATION USE RUNTIME CLASS TABLE SO ABOVE THEOREM
;;; ARE USEFULL.
;;;
;;; Runtime checking really talks about the cl instead of the static cl
;;;
;;; cl here could be an array-class need to deal with array types. 
;;; 

;;
;; THIS IS NOT TRUE because of handling of INTERFACE CLASS SHOULD
;; consistent-state also ignore interface issue as BCV does?  for example, an
;; array of type certain interfaces, contains some aribtary object, should it
;; be considered to be consistent? 
;;
;; BECAUSE INVOKEINTERFACE etc will be checked at RUNTIME anyway. 
;;
;; THIS MAY BE TRUE, if we copy from BCV's isAssignableTo
;; 
;; So the conclusion is AssignmentCompatible copy from BCV, 
;; isAssignableTo copy from Non-defensive machine. 
;;
;; WE FOLLOWED A DIFFERENT PATH.  09/09/03 
;;
;; HOWEVER, our consistent-state is becoming weaker!! NOT SO GOOD.
;;

;;(in-theory (disable assignmentCompatible))

;;         
;; consistency is not the only requirement 
;; 


; (defun make-common-info (hashcode monitor class-ptr) 
;   (list 'common-info hashcode monitor class-ptr)) 

; (defun hashcode  (cminfo)   (nth 1 cminfo)) ;; a number 
; (defun monitor   (cminfo)   (nth 2 cminfo))
; (defun class-ptr (cminfo)   (nth 3 cminfo))

; (defun obj-hashcode  (object)   (hashcode  (common-info object))) ;; a number 
; (defun obj-monitor   (object)   (monitor   (common-info object))) ;; a composite structure
; (defun obj-class-ptr (object)   (class-ptr (common-info object))) ;; a number 

; (defun obj-type (obj)  ;; object's runtime type.
;   (obj-class-ptr obj))  


;; (defun wff-internal-heap-obj (obj)
;;   (and (true-listp obj)
;;        (equal (len obj) 4)
;;        (equal (car obj) 'object)))

;; ; (defun wff-internal-array (array-obj)
;; ;    (and (wff-internal-heap-obj array-obj)
;; ;         (wff-ARRAY-specific-info (specific-info array-obj))))


;; (defun wff-class-ptr (class-ptr)
;;   (or ;; (isClassType class-ptr)
;;       ;; (stringp class-ptr) ;;  FIX: 10/27/03 to comply with M6's
;;       ;;  usage. cf. consistent-test.lisp  
;;       (isClassType class-ptr) ;;  10/28/03 FIX. changed the definition of
;; 			      ;;  isClassType
;;       (isArrayType class-ptr)))


;; (defun wff-common-info-strong (common-info)
;;   (and (true-listp common-info)
;;        (equal (len common-info) 4)
;;        (wff-class-ptr (nth 3 common-info))))


;; (defun wff-jvp (jvp)
;;    (alistp jvp))

;; (defun wff-specific-info (specific-info)
;;   (and (true-listp specific-info)
;;        (consp specific-info)
;;        (equal (car specific-info) 'specific-info)
;;        (cond ((equal (nth 1 specific-info) 'ARRAY) 
;;               (and (equal (len specific-info) 4)
;;                    (integerp (nth 3 specific-info))
;;                    (equal (len (nth 2 specific-info)) (nth 3 specific-info))))
;;              (t t))))


;; ; (defun make-object (commoninfo specific-info java-visible-part)
;; ;   (list 'object commoninfo specific-info java-visible-part))

;; ; (defun common-info   (object)     (nth 1 object))
;; ; (defun specific-info (object)     (nth 2 object))    ;; the format depends on types
;; ; (defun java-visible-portion (object) (nth 3 object))


;; ;; (defun common-info (obj)
;; ;;   (declare (xargs :guard (wff-internal-heap-obj obj)))
;; ;;   (nth 1 obj))

;; ;; (defun specific-info (obj)
;; ;;   (declare (xargs :guard (wff-internal-heap-obj obj)))
;; ;;   (nth 2 obj))

;; ;; (defun java-visible-portion (obj)
;; ;;   (declare (xargs :guard (wff-internal-heap-obj obj)))
;; ;;   (nth 3 obj))


;; (defun wff-obj-strong (obj)
;;   (and (wff-internal-heap-obj obj)
;;        (wff-common-info-strong (common-info obj))
;;        (wff-specific-info (specific-info obj))
;;        (wff-jvp (java-visible-portion obj))))

;;;
;;; Tue Jan 13 01:20:29 2004: moved to djvm-obj
;;;



;; (defun class-ptr (common-info)
;;   (declare (xargs :guard (wff-common-info-strong common-info)))
;;   (nth 3 common-info))

;; (defun obj-class-ptr (object)   
;;   (declare (xargs :guard (wff-obj-strong object)))
;;   (class-ptr (common-info object))) ;; a number 



;; (defun obj-type (obj)  ;; object's runtime type.
;;   (declare (xargs :guard (wff-obj-strong obj)))
;;   (obj-class-ptr obj))


;; (defun wff-heap-strong (hp)
;;   (and (wff-heap hp)
;;        (if (not (consp hp)) t  
;;          (and (wff-obj-strong (cdar hp))
;;               (wff-heap-strong (cdr hp))))))


;; (in-theory (disable wff-obj-strong))
;; ;; I could disable more functions to really restrict how ACL2 will prove it.
;; ;; for now. just disable wff-obj,

;;; moved to djvm-heap.lisp


;; (defun ADDRp (v) 
;;   (integerp v))

;; (defun CHARp (v)
;;   ;; temp implementation
;;   ;; should be 16 bit unsigned integer.
;;   ;;
;;   (integerp v))

;;
;; moved to djvm-type-value.lisp
;; Tue Jan 13 01:30:41 2004
;;


;; (defthm wff-obj-strong-implies-wff-obj
;;   (implies (wff-obj-strong obj)
;;            (wff-obj obj))
;;   :hints (("Goal" :in-theory (enable wff-obj-strong))))

;; (defthm wff-obj-strong-implies-wff-common-info
;;   (implies (wff-obj-strong obj)
;;            (wff-common-info (common-info obj)))
;;   :hints (("Goal" :in-theory (enable wff-obj-strong))))


;; (in-theory (disable wff-obj wff-common-info common-info))

;;;; moved to djvm-obj

;;;; consistent value!!


(defun consistent-value (tagged-value type cl hp)
  ;; consistent-value with respect to the interal class table it will be
  (declare (xargs :guard (and (consistent-class-hierachy cl)
                              (wff-heap-strong hp))))
  ;; the guard here is not very perfect.
  (if (not (wff-tagged-value tagged-value)) nil
    (let ((vtype (tag-of  tagged-value))
          (value (value-of tagged-value)))
      (cond ((primitive-type? type)
             (and (equal vtype type)
                  (cond ((equal type 'INT)  (INT32p value))
                        ((equal type 'ADDR) (ADDRp value))
                        ((equal type 'CHAR) (CHARp value)) ;; caught by
                                                           ;; consistent-state
                        ;; Mon May 30 14:29:42 2005
                        ((equal type 'BOOLEAN) (jvmBOOLEANp value))
                        ((equal type 'SHORT)   (SHORTp value))
                        ((equal type 'BYTE)    (BYTEp value))
                        ((equal type 'FLOAT)   (jvmFLOATp value))
                        ((equal type 'DOUBLE)  (DOUBLEp value))

                        ;; 10/27/03 
                        ((equal type 'LONG) (INT64p value))
                        ;; not adequate to handle it.
                        (t nil))))
            ((NULLp tagged-value) t)
            ((REFp tagged-value hp)
             (let* ((ref tagged-value)
                    (obj (deref2 ref hp)) 
                    (rtype (obj-type obj)))
               (assignmentCompatible rtype type cl)))
            (t nil)))))

;----------------------------------------------------------------------
;
; Mon May 30 14:41:42 2005

(defthm default-value-is-consistent-value
  (implies (or (primitive-type? type)
               (reference-type type)
               (Array-type? type))
           (consistent-value (tag (default-value type) type) type cl hp)))

;----------------------------------------------------------------------


;; assignmentCompatible is used in consistent-state.  We need have an invariant
;; that if in the system there is a value appear to have a certain type, then
;; all type that it is assignableTo is also loaded. Thus assignmentCompatible
;; does not change state!! in a consistent state. IsAssignableTo in fact does
;; not change state!! (NO. it changes) Because class loading has a certain
;; invariant .. (unless in the case of testing of instanceOf (and assign object
;; to array!!)
;; 
;; However all testing that appears in the consistent-state testing won't
;; change state!!
;;
;; Sun Oct 24 19:44:22 2004
;;
;; REFER to CLDC BCV SPEC' class hierachy graph Remember to get the assignment
;; relation to be transitive.
;;
;;; 
;;; Deviation from BCV's SPEC!!
;;;
 
;; If type is an interface type, every reference type can assign to it
;;

;;
;; Do we want a straightforward assignmentCompatible definition or a definition
;; looks exactly like isAssignableTo in the JVM (and the bytecode verifier
;; (NOTE: BCV's isAssignableTo is different from the one in JVM)
;; 
;; We can have a straightforward definition of assignmentCompatible, to prove
;; it is in some sense the same with isAssignableTo is hard. 
;; 
;;
;; Basically, we would prove that invariant in other part of the bcv
;; implementation + bcv implementation for isAssignable ensures the
;; straightforward assignableTo succeed. 
;;
;; Is this comment really true? we need some invariant about class table is
;; correctly loaded. It is true, because, the isAssignable in typechecker
;; assume the types are well formed. (because (isAssignable X X env), however,
;; a straightforward assignmentCompatible would first assert the type are valid
;; type and use the transitivity relation...
;; 
;; Thus proving isAssignable equal to assignmentCompatible (if defined
;; straightforwardly), we need to prove the invariant that all types are
;; consistent types. 
;;
;; In essense, we are proving two descriptions of tree are really describing
;; the same tree, when the type involves are from a certain domain.
;; 
;; Basically, BCV's isAssignable is more ready to return true. for cases
;; outside the domain of assignmentCompatible. 
;; 
;; As theorem would SKIP-PROOFs
;; 
;;   If both types are valid types in the system, isAssignableTo returns the
;;   same value as assignmentCompatible.  
;;


;; One problem is this consistency check does not match well with 
;; jvp-set-field , jvp-getfield. Need to prove theorems about setfield valid
;; data does not change consistency, get existing field returns valid data.
;; 
;;
;; Not a big problem. But we could define a consistency check that uses only
;; set-get interface?? maybe possible. That may make proof of maintaining
;; consistency being simpler. Instead of treating object as a list of alist, we
;; first defines an iterator or collector that collect the fields from class
;; defintion, we should using set-get with valid value, we get valid value
;; back. 
;; 

;; (defun wff-field (field)
;;   (and (consp field)
;;        (equal (len field) 1)))


;; (defun fieldname (field) 
;;   (declare (xargs :guard (wff-field field)))
;;   ;; as in a object rep
;;   (car field))

;; (defun fieldvalue (field)
;;   (declare (xargs :guard (wff-field field)))
;;   (cdr field))

;;;;; moved to djvm-obj.lisp. maybe we should move it to jvm-obj!!
 

;; 09/09/03 we DECIDED THAT WE SHOULD KEEP HEAP AND CLASS TABLE THE SAME FOR M6
;; and Defensive M6.


;; (defun tag (untagged-value field-type)
;;   (if (primitive-type? field-type)
;;       (cons field-type untagged-value)
;;     (cons 'REF untagged-value)))


;; 09/09/03 we DECIDED THAT WE SHOULD KEEP HEAP AND CLASS TABLE THE SAME FOR M6
;; and Defensive M6.

; (defun make-field (classname fieldname fieldtype accessflags)
;   (list 'field classname fieldname fieldtype 
;         (cons 'accessflags accessflags)))

; (defun field-classname (field)  (nth 1 field))
; (defun field-fieldname (field)  (nth 2 field))
; (defun field-fieldtype (field)  (nth 3 field))
; (defun field-fieldaccessflags (field)  (cdr (nth 4 field)))


(defun wff-field-decl (field-decl)
  (and (true-listp field-decl)
       (equal (len field-decl) 5)
       (consp (nth 4 field-decl))
       (true-listp (cdr (nth 4 field-decl)))))


;; (defun field-classname (field-decl)  
;;   (declare (xargs :guard (wff-field-decl field-decl)))
;;   (nth 1 field-decl))


;; (defun field-fieldname (field-decl)  
;;   (declare (xargs :guard (wff-field-decl field-decl)))
;;   (nth 2 field-decl))


;; (defun field-fieldtype (field-decl) 
;;   (declare (xargs :guard (wff-field-decl field-decl)))
;;   (nth 3 field-decl))

;; (defun field-fieldaccessflags (field-decl)  
;;   (declare (xargs :guard (wff-field-decl field-decl)))
;;   (cdr (nth 4 field-decl)))

;;; Mon Jul 18 17:40:15 2005
;;; Now we need to assert that 
;;; field is properly initialized! 
;;;

;;;
;;; However the current definition of consistent-field could not 
;;; easily incorporate this extra assertion!!! 
;;; We need a new set of consistent-field-init
;;;

(defun wff-immediate-instance (immediate-instance)
  (consp immediate-instance))


(defun consistent-field (field field-decl cl hp)
  (declare (xargs :guard (and (consistent-class-hierachy cl)
                              (wff-heap-strong hp))))
  (and (wff-data-field field)
       (wff-field-decl field-decl)
       (equal (fieldname field) (field-fieldname field-decl))
       (consistent-value (tag (fieldvalue field) (field-fieldtype field-decl)) 
                         (field-fieldtype field-decl) cl hp)))


;; (defun consistent-field (field field-decl cl hp)
;;   (declare (xargs :guard (and (consistent-class-hierachy cl)
;;                               (wff-heap-strong hp))))
;;   (and (wff-data-field field)
;;        (wff-field-decl field-decl)
;;        (equal (fieldname field) (field-fieldname field-decl))
;;        (consistent-value (tag (fieldvalue field) (field-fieldtype field-decl)) 
;;                          (field-fieldtype field-decl) cl hp)))


;;; maintain that heap being the same with non-defensive machine. 


(defun consistent-fields (fields field-decls cl hp)
  (declare (xargs :guard (and (consistent-class-hierachy cl)
                              (wff-heap-strong hp))))
  (cond ((not (consp fields)) (not (consp field-decls)))
        ((not (consp field-decls)) nil)
        (t (and (consistent-field (car fields) (car field-decls) cl hp)
                (consistent-fields (cdr fields) (cdr field-decls) cl hp)))))


      
(defun consistent-immedidate-instance (obj-type immediate-instance cl hp)
  (declare (xargs :guard (and (consistent-class-hierachy cl)
                              (consp immediate-instance)
                              (wff-heap-strong hp))))
  (and (wff-immediate-instance immediate-instance)
       (equal obj-type (car immediate-instance))  
       ;; this is not right
       (class-exists? obj-type cl)
       ;; does not handle array object well. 
       (let ((fields (cdr immediate-instance))
             (field-decls (fields (class-by-name obj-type cl))))
         (and (alistp fields) ;; Thu Jun  9 13:30:08 2005.
              ;; added because GETFIELD. 
              (consistent-fields fields field-decls cl hp)))))


;;
;; Where I should check for java.lang.Object, or check for the superclass of
;; obj-type is nil? if I check for java.lang.Object, the termination relies on
;; an invariant that super of each eventually ends in java.lang.Object
;;
;;
;; should I use the internal class table as the "cl"??  Then I need invariant
;; about internal class table with respect to external class-table
;;
;; Prove some property of class loader, class loader preserve the consistency. 
;; consistency is important. (However if model is not accurate such proof is
;; not so meaningful


(defun consistent-jvp (obj-type jvp cl hp)
  (declare (xargs   :guard (and (consistent-class-hierachy cl)
                                (wff-heap-strong hp))
                    :measure (len jvp)))
  (and (alistp jvp)
       (cond ((< (len jvp) 1) nil)
             ((equal (len jvp) 1) 
              (and (equal obj-type "java.lang.Object")
                   (consistent-immedidate-instance obj-type (car jvp) cl hp)))
             (t (and (consistent-immedidate-instance obj-type (car jvp) cl hp)
                     (let* ((class-decl (class-by-name obj-type cl))
                            (super (super class-decl)))
                       (and (class-exists? super cl)
                            (consistent-jvp super (cdr jvp) cl hp))))))))




(defthm wff-obj-implies-wff-internal-heap-obj 
  (implies (wff-obj-strong obj)
           (wff-internal-heap-obj obj))
  :hints (("Goal" :in-theory (enable wff-obj)))
  :rule-classes :forward-chaining)

(in-theory (enable wff-obj-strong))

(defun consistent-object (obj hp cl) 
  (declare (xargs :guard (and (consistent-class-hierachy cl)
                              (wff-heap-strong hp))))
                  
  ;; assumping cl is consistent and is instance-class-table 
  ;; need to check the monitor consistency? Maybe just wff is good enough
  ;; execution of interpreter can handle it well. 
  (and (wff-obj-strong obj)
       (reference-type (obj-type obj))       ;; more assertions.
       (not (primitive-type? (obj-type obj))) ;; not necessary once we have above!
       (if (isArrayType (obj-type obj))
           t;; we will check the array-consistent in a different predicated 
         ;; here!! we could not avoid the mutural recursion in the array-object +
         ;; instance object.!! 
         ;; NO we can avoid it because we only eventually every pointer in an array
         ;; has to be bound to some consistent-object or some consistent-array-object.
         ;; by virtual of referring to an object in a consistent heap which only
         ;; assert that one level dereference is consistent,  we can show infiniti
         ;; level of dereference is consistent. 
         ;; 
         (and;;(wff-obj-strong obj) ;; top level syntatically ok, 3 components 
          ;; wff-obj-strong allow us to use obj-type without causing an error
          (class-exists? (obj-type obj) cl) 
          (consistent-jvp (obj-type obj) (java-visible-portion obj) cl hp)))))




;; (in-theory (disable consistent-class-hierachy)) 
;; seem to be a nice concept that many thing depends on it no need to open its
;; definition

;;;
;;; MAYBE I SHOULD WORD ON THE GUARD OF CONSISTENT-STATE
;;;

(defun consistent-heap1 (hp1 hp cl id)
  (declare (xargs :guard (and (consistent-class-hierachy cl)
                              (wff-heap-strong hp))))
  (and (integerp id)
       (alistp hp1)
       (if (endp hp1) t
	 (and (equal (caar hp1) id)
              (consistent-object (cdar hp1) hp cl) ;; consistent object or
                                                   ;; array object 
	      (consistent-heap1 (cdr hp1) hp cl (+ 1 id))))))

;;
;; Thinking about using record book for implemention the heap ...  what
;; benefit? record book still has not got an iterator?? so that we can say for
;; all fields, value type consistent?
;;
;; currently we are traverse the object in a "particular" order and assert
;; consistency. Our way is quite "white" box. We know the order of fields in
;; the memory layout in some sense. 
;;
;; We can't say set of all without giving away to construct such a set. And
;; proofs depend on how we construct the set.  Maybe it is necessary, because
;; we need to able to tell the membership with the set. Implicitly (high-order)
;; we can claim an object "comes" from  a consistent-heap, thus we can derive
;; many properties of the "object". We have to be very explicit in how we get
;; the "object". We may be able to benefit from the record book, which hide
;; from the representation of the objects.
;; 

;; (i-am-here) ;; Sun Nov  7 19:44:38 2004

;; (defun array-class-exists? (array-type acl)
;;   (declare (xargs :guard (and (alistp acl)
;;                               (wff-array-type array-type))))
;;   (bound? (array-component-type array-type) acl))

;;; Sun Nov  7 22:17:25 2004

(defun array-class-exists? (array-type acl)
  (declare (xargs :guard (and (alistp acl)
                              (wff-array-type array-type))))
  (bound? array-type acl))


(defun array-obj-consistent1 (data-array component-type hp cl)
  (declare (xargs :guard (and (true-listp data-array)
                              (wff-heap-strong hp)
                              (consistent-class-hierachy cl))))
  (if (endp data-array) t
    (and (consistent-value (tag (car data-array) component-type) component-type cl hp)
         (array-obj-consistent1 (cdr data-array) component-type hp cl))))

;;
;; we could chose to write consistent-state in such a way, that we always check
;; synatx before doing anything. Thus we don't need seperate wff-XXX concept. 
;;


;; (defun wff-INSTANCE_CLASS-specific-info (specific-info)
;;   (and (true-listp specific-info)
;;        (equal (len specific-info) 4)
;;        (equal (car specific-info) 'specific-info)
;;        (equal (nth 1 specific-info) 'INSTANCE_CLASS)
;;        (wff-type-desc (nth 2 specific-info))))

;; (defun wff-ARRAY_CLASS-specific-info (specific-info)
;;   (and (true-listp specific-info)
;;        (equal (len specific-info) 3)
;;        (equal (car specific-info) 'specific-info)
;;        (equal (nth 1 specific-info) 'ARRAY_CLASS)
;;        (wff-type-desc (nth 2 specific-info))))


;; (defun wff-ARRAY-specific-info (specific-info)
;;    (and (true-listp specific-info)
;;         (equal (len specific-info) 4)
;;         (equal (car specific-info) 'specific-info)
;;         (equal (nth 1 specific-info) 'ARRAY)
;;         (integerp (nth 3 specific-info))
;;         (true-listp (nth 2 specific-info))
;;         (equal (len (nth 2 specific-info)) (nth 3 specific-info))))

;; (defun wff-STRING-specific-info (specific-info)
;;    (and (true-listp specific-info)
;;         (equal (len specific-info) 4)
;;         (equal (car specific-info) 'specific-info)
;;         (equal (nth 1 specific-info) 'STRING)
;;         (or (stringp (nth 3 specific-info))
;;             (equal (nth 3 specific-info) -1))))
;; ;;           (nullp (nth 3 specific-info)))))
;; ;;          ^^^^^^^           

;; ; (defun wff-specific-info (specific-info)
;; ;   (or (wff-INSTANCE_CLASS-specific-info specific-info)
;; ;       (wff-ARRAY_CLASS-specific-info specific-info)
;; ;       (wff-ARRAY-specific-info specific-info)
;; ;       (wff-STRING-specific-info specific-info)
;; ;       (wff-GENERIC_OBJECT-specific-info specific-info)))


;; (defun wff-internal-array (array-obj)
;;    (and (wff-obj-strong array-obj)
;;         (wff-array-type (obj-type array-obj))
;;         (wff-ARRAY-specific-info (specific-info array-obj))))


;;; this is in conflict with shared' part's definition. 


;; (defun array-bound (array-obj) 
;;   (declare (xargs :guard (wff-internal-array array-obj)))
;;   (let ((array-specific-info (specific-info array-obj)))
;;     (nth 3 array-specific-info)))


;; (defun array-data (array-obj)
;;   (declare (xargs :guard (wff-internal-array array-obj)))
;;   (let ((array-specific-info (specific-info array-obj)))
;;     (nth 2 array-specific-info)))

;;;;; moved to jvm-object-manipulation-primitives.lisp


;;;
;;; should move those around to the shared part. Tue Jan 13 14:23:04 2004
;;;
;;;; moved to 


; (defun element-at (index array)
;   (nth index (array-data array)))


; (defun init-array (type count)
;   (if (zp count)
;       nil
;       (cons (default-value type) (init-array type (- count 1)))))

(defun array-obj-consistent (array-type array-obj hp cl)
  (declare (xargs :guard (and (wff-internal-array array-obj)
                              (wff-heap-strong hp)
                              (wff-array-type array-type)
                              (consistent-class-hierachy cl))))
  (let* ((component-type (array-component-type array-type))
         (bound (array-bound array-obj))
         (data-array (array-data array-obj)))
    (and (equal (len data-array) bound)
         (array-obj-consistent1 data-array component-type hp cl))))


;; (defun wff-array-class-table (acl)
;;   (alistp acl))

(defthm wff-array-class-table-implies-alistp
  (implies (wff-array-class-table acl)
           (alistp acl))
  :rule-classes :forward-chaining)



(defun valid-array-type (arraytype cl acl)
  ;; Sat Oct 30 00:25:04 2004
  (declare (xargs :guard (and (wff-instance-class-table cl)
                              (wff-array-class-table acl))))
  (and (array-type-s arraytype cl)
       (let ((basetype (array-component-type arraytype)))
         (and (ArrayClassLoaded1? (make-array-type basetype) acl)
              (if (isArrayType basetype)
                  (valid-array-type basetype cl acl)
                (or (primitive-type? basetype)
                    (isClassTerm (class-by-name basetype cl))))))))

       


(defun consistent-array-object (obj hp cl acl)
  (declare (xargs :guard (and (consistent-class-hierachy cl)
                              (wff-array-class-table acl)
                              (wff-obj-strong obj)
                              (wff-heap-strong hp))))
  (let ((obj-type (obj-type obj)))
    (and (wff-internal-array obj)
         (valid-array-type obj-type cl acl) ;; 
         (array-type-s obj-type cl)
         (array-class-exists? obj-type acl)
         (array-obj-consistent obj-type obj hp cl)
         (consistent-jvp "java.lang.Object" 
                         (java-visible-portion obj) cl hp))))
                         

;;
;; basically we need to prove in a consistent-state, build a new obj, the new
;; object is consistent, etc. build an new array, the array is consistent. 
;; 
;; Does defensive machine also need to record information about whether an
;; object is initialized? check any operation before initialization?? 
;; 
;; YES!! we need to do that. object of class java.lang.Object is by default
;; initialized, other objects need an explicit call to some <init> method to
;; correctly mark it. We also want to show init is not called twice? YES. 
;;
;; BCV guarantees this by expecting <init> is invoked with (uninitialized ...) 
;; or 'uninitializedThis
;; 
;; How could be sure that constructor actually call all super's constructors??
;; Suppose A ...  B  ... C. create a raw object of A, we only call C's
;; constructor to initialize the C part and skipping B part.
;; HOWEVER this is programmer's responsibility. The constructor of A must be
;; called and called only once. This is what BCV guarantees.
;;
;; As long as programmer write correct code for A, people have not corrupted
;; the system yet, this won't cause someone create a improperly initialized
;; object.

(defun consistent-heap2 (hp1 hp cl acl id)
  (declare (xargs :guard (and (consistent-class-hierachy cl)
                              (wff-array-class-table acl)
                              (integerp id)
                              (wff-heap-strong hp1)
                              (wff-heap-strong hp))))
  (and (integerp id)
       (alistp hp1)
       (if (endp hp1) t
         (and (equal (caar hp1) id)
              (wff-obj-strong (cdar hp1))
              (if (isArrayType (obj-type (cdar hp1)))
                  (consistent-array-object (cdar hp1) hp cl acl)
                t)
              ;; either not array-type or a consistent-array-obj
              (consistent-heap2 (cdr hp1) hp cl acl (+ 1 id ))))))



(defun consistent-heap (hp cl acl)
  (declare (xargs :guard (and (consistent-class-hierachy cl)
                              (wff-array-class-table acl))))
  (and (wff-heap-strong hp)
       (consistent-heap1 hp hp cl 0)
       (consistent-heap2 hp hp cl acl 0)))

;; WITHOUT CONSISTENT-HEAP THIS ONLY ASSERT THAT Java visible part are
;; consistent with types.
;;
;;    
;; We need some properties about operations that maintain the consistency of
;; heap
;; 

;; How strong we want this is consistent-state predict We want each value in
;; the state is meaningful?  thread ref really point to a real object that
;; represent the thread.
;; 
;; Only with that we could prove from a consistent state we always reach a
;; consistent state, using a defensive machine or a non-defensive machine that
;; use a bytecode verifier. 
;;
;; However safety is more than maintaining the consistency of the JVM state.
;; some policy like protected access permission must also be honored (in the
;; defensive machine they are checked at runtime) Our proof effort can be
;; considered as justifing the correctness of implementations that rely on a
;; bytecode verifier to remove certain check at runtime.
;;
;; In any execution, object is initialized before being used. 
;;
;; access control is respected (dynamic check + protected access control check)
;;

;;
;; In the first step, showing consistency is low level security. 
;; 

;; Our consistency of value is defined using instance-class-table, which itself
;; is created by. We need(?) to define a consistency between
;; instance-class-table. correctly-loaded? predicate? 

;;
;; need something from the fourth proof.  all classes in the class table are
;; correctedly loaded from the ...
;; 
;; An interface  method is invoked with invokeinterface, the class of the
;; actual object really declared to implement the interface. This is not
;; checked by the class loader. It needs to be checked at runtime by both
;; defensive and non-defensive machines.
;;


;; WHY? I need to go into this much details to define those consistent-...
;; because otherwise the leaf proofs does not make sense. Proving a trivial
;; consistent-state does not say a lot.

;; That loading invariant only talked about class hierachy?  it has not talked
;; about the fields and methods matches...  Do consistent-value need this fact
;; that fields matches??  maybe the hierachy info encoded in the internal
;; class-table is same with static class table are good enough. That is encoded
;; by the loader-inv. 

;; notice we have two class table now. (instance-class-table, array-class-table)



; (defun make-static-field (classname fieldname fieldtype accessflags value)
;   (list 'static-field 
;         classname 
;         fieldname 
;         fieldtype 
;         (cons 'accessflags accessflags)
;         value))

; (defun static-field-classname  (field)  (nth 1 field))
; (defun static-field-fieldname  (field)  (nth 2 field))
; (defun static-field-fieldtype  (field)  (nth 3 field))
; (defun static-field-accessflags (field)  (cdr (nth 4 field))) ;; don't need cpindex
; (defun static-field-fieldvalue (field)  (nth 5 fields))


;; (defun wff-static-field (static-field)
;;   (and (true-listp static-field)
;;        (equal (len static-field) 6)
;;        (consp (nth 4 static-field))
;;        (true-listp (cdr (nth 4 static-field)))))

;; (defun static-field-classname  (field)  
;;   (declare (xargs :guard (wff-static-field field)))
;;   (nth 1 field))
;; (defun static-field-fieldname  (field)  
;;   (declare (xargs :guard (wff-static-field field)))
;;   (nth 2 field))
;; (defun static-field-fieldtype  (field)  
;;   (declare (xargs :guard (wff-static-field field)))
;;   (nth 3 field))
;; (defun static-field-accessflags (field) 
;;     (declare (xargs :guard (wff-static-field field)))
;;     (cdr (nth 4 field))) ;; don't need cpindex
;; (defun static-field-fieldvalue (field)  
;;   (declare (xargs :guard (wff-static-field field)))  
;;   (nth 5 field))

       


(defun consistent-static-field (classname static-field cl hp)
  (declare (xargs :guard (and (wff-static-field static-field)
                              (consistent-class-hierachy cl)
                              (wff-heap-strong hp))))
    (let  ((cname (static-field-classname static-field))
           (ftype (static-field-fieldtype static-field))
           (fvalue (static-field-fieldvalue static-field)))
      (and (equal classname cname)
           (consistent-value (tag fvalue ftype) ftype cl hp))))

(defun wff-static-fields-strong (fields)
  (if (not (consp fields)) t
    (and (wff-static-field (car fields))
         (wff-static-fields-strong (cdr fields)))))

(defun consistent-static-fields (classname static-fields cl hp)
    (declare (xargs :guard (and (wff-static-fields-strong static-fields)
                                (consistent-class-hierachy cl)
                                (wff-heap-strong hp))))
  ;; we will check that static-fields matches the fields that have static flags
  ;; in the .class file representation
  (if (not (consp static-fields)) t ;; return t here.
    (and (consistent-static-field classname (car static-fields) cl hp)
         (consistent-static-fields classname (cdr static-fields) cl hp))))


(defun tag-REF (v)
  (cons 'REF v))



;;; Fri Nov  5 12:05:30 2004
;;; 
;;;   consistent-constantpool defined!! 
;;; 

;;; So far, we only support three kinds of cpentry-type

(defthm wff-common-info-wff-obj-strong
  (implies (wff-obj-strong obj)
           (wff-common-info (common-info obj)))
  :rule-classes :forward-chaining)

(defun consistent-constantpool-entry (cp hp cl)
  (declare (ignore cl))
  (declare (xargs :guard (and (wff-constant-pool-entry cp)
                              (wff-heap-strong hp)
                              (wff-instance-class-table cl))
                  :guard-hints (("Goal" :in-theory (enable
                                                    wff-constant-pool-entry
                                                    binding
                                                    bound?)))))
  (cond ((equal (cpentry-type cp) 'INT)  (INT32p (cpentry-value cp)))
        ((equal (cpentry-type cp) 'LONG) (INT64p (cpentry-value cp)))
        ((equal (cpentry-type cp) 'STRING) 
         (and (bound? (cpentry-value cp) hp)
              (equal  (obj-type (deref (cpentry-value cp) hp))
                      "java.lang.String")))))

;;; Fri Nov  5 12:11:54 2004. We will need to make it clear
;;; in wff-constant-pool-entry-s!! 
;;; it is already clear there. Fri Nov  5 12:18:24 2004 

(defun consistent-constantpool (cps hp cl)
  (declare (xargs :guard (and (wff-constant-pool cps)
                              (wff-heap-strong hp)
                              (wff-instance-class-table cl))))
  ;; (declare (ignore cps hp cl))
  (if (not (consp cps)) t
    ;; we only allow certain fields in the cps
    (and (consistent-constantpool-entry (car cps) hp cl)
         (consistent-constantpool (cdr cps) hp cl)))) 


(defun wff-class-rep-strongx (class-decl)
  (and (wff-class-rep-strong class-decl)
       (wff-static-fields-strong (static-fields class-decl))))



;; Mon Mar 29 21:30:47 2004
(defun consistent-handlers (handlers)
  (declare (ignore handlers))
  t)


(defun consistent-instructions (instrs)
  (declare (ignore instrs))
  t)

;; Mon Mar 29 21:32:16 2004 Temp implementation

(defun consistent-code (code) 
  (and (wff-code code)
       (integerp (code-max-Stack code))
       (integerp (code-max-local code))
       (consistent-handlers (code-handlers code))
       (consistent-instructions (code-instrs code))))


(defun consistent-method-decl (method-decl)
  (and (wff-method-decl method-decl)
       (true-listp (method-accessflags method-decl))
       (if (or (mem '*abstract* (method-accessflags method-decl))
               (mem '*native* (method-accessflags method-decl)))
           ;; (not (method-code method-decl))
           t ;; replace with it a T ;; Mon Nov  8 19:13:03 2004
         (consistent-code (method-code method-decl)))))
           

(defun consistent-method-decls (method-decls)
  (if (not (consp method-decls))
      t
    (and (consistent-method-decl (car method-decls))
         (consistent-method-decls (cdr method-decls)))))


(defun consistent-class-decl (class-decl cl hp)
  (declare (xargs :guard (and (consistent-class-hierachy cl)
                              (wff-class-rep-strongx class-decl)
                              (wff-heap-strong hp))))
  ;; this one only talks about value are consistent however it does not talk
  ;; about fields, method matches. in context of dynamic loading ... intend to
  ;; skip prove the matches.  also need to check static variables. any value
  ;; that could show up on the op stack or local variables
  (and ;; need ASSERTION ABOUT CONSTANT POOL be consistent, well-formed. 
       ;; need to assert the classname being a string. Wed Nov 19 02:23:43 2003
       ;; because we don't want a class of name 
       ;; (array (class "java.lang.Object")) be treated as an array. 
       (stringp (classname class-decl)) ;; need to modify loader to ensure
                                        ;; this.
       ;; Wed Nov 19 02:25:22 2003
       ;; 
       ;; Mon Mar 29 21:16:55 2004. Add assertions that method are well formed
       ;;

       ;; Thu Jun  9 15:19:06 2005. need to add assertions about
       ;; interface-class does not have fields. 
       (or (not (isInterface class-decl))
           (equal (fields class-decl) nil))
       ;; Thu Jun  9 15:20:34 2005. 
       (consistent-method-decls (methods class-decl))
       (consistent-constantpool (constantpool class-decl) hp cl)
       (consistent-value (tag-REF (class-ref class-decl)) "java.lang.Class" cl hp)
       (Valid-REFp (tag-REF (class-ref class-decl)) hp)
       (consistent-static-fields (classname class-decl) (static-fields class-decl) cl hp)))
  ;; assumption this ref-value is in form (REF . value)

;;  09/09/03  ALL THESE DOES NOT MATTER for AALOAD PROOF.

;;; Mon Mar 29 21:34:14 2004. modified consistent-class-decl to assert
;;; well-formedness of method-code
;;;

(defun consistent-class-decls (cl1 cl hp)
    (declare (xargs :guard (and (consistent-class-hierachy cl)
                                (wff-heap-strong hp))))
  ;; this version only talks about the static field values, class-ref etc.
  ;; with respect to the instance class-table 
  ;; loader-inv will talk about class hierachy matches. 
  (if (not (consp cl1)) t
    (and (wff-class-rep-strongx (car cl1))
         (consistent-class-decl  (car cl1) cl hp)
         (consistent-class-decls (cdr cl1) cl hp))))

;; (defun class-hierachy-match (cl scl)
;;;  (m6::loader-inv-helper cl cl scl))

; (defun fields-declaration-match (cl scl)
;   ;; tmp implementation
;   (declare (ignore cl scl))
;   t)

; (defun consistent-class-decls2 (cl scl)
;   ;; assert the class hierachy matches 
;   ;; We also need to assert that class and field matches? Do we? 
;   ;; However IN REAL JVM, BCV use the cl to do the type checking!!
;   (and (class-hierachy-match cl scl)
;        (fields-delcaration-match cl scl)))

;;
;; NEED to write this out. We can skip prove it but the spec need to be
;; there. 
;;

(defun consistent-class-table (cl scl hp)
  (declare (xargs :guard (and (wff-heap-strong hp)
                              (wff-static-class-table-strong scl))))
  (and (wff-instance-class-table-strong cl)
       (consistent-class-hierachy cl)
       ;; all symbolic reference to super and interfaces are actually present
       ;; not loops in supers, and interfaces. 
       (class-table-is-loaded-from cl scl)
       ;; loaded correctly from the class-table 
       ;;
       (consistent-class-decls cl cl hp)))
       ;; in fact bcv also use cl. However in bcv spec, bcv use scl. N ext form
       ;; is say cl and scl is consistent with each other
       ;; check fields declaration match? Guaranteed by class loader.
       ;; So far we only proved that class-hierachy-match


;; this does not check the class hierachy is correct
;; runtime error? 

; (defun classImplementInterface2 (rtype interfacetype cl)
;   (declare (ignore rtype interfacetype cl))
;   t)


;; we need a skip proof that 
;; 
;; bytecode from from a dereferencing a valid method-ptr is one of bytecode
;; verifier have looked at. 
;; 
;(skip-proofs 
; (defthm BCV-valid-method-ptr-code-verified 
;   t)

;; ;   Methods 
;; (defun make-method (classname methodname args returntype accessflags code)
;;   (list 'method 
;;         classname 
;;         methodname 
;;         (cons 'parameters args)
;;         (cons 'returntype returntype)
;;         (cons 'accessflags accessflags)
;;         code))


; A typical method 
;
; (METHOD
;  "java.lang.Class" "<init>" (PARAMETERS)
;  (RETURNTYPE . VOID)
;  (ACCESSFLAGS *CLASS* *PRIVATE*)
;  (CODE
;      (MAX_STACK . 1)
;      (MAX_LOCAL . 1)
;      (CODE_LENGTH . 5)
;      (PARSEDCODE
;           (0 (ALOAD_0))
;           (1 (INVOKESPECIAL (METHODCP "<init>" "java.lang.Object" NIL VOID)))
;           (4 (RETURN))
;           (ENDOFCODE 5))
;      (EXCEPTIONS)
;      (STACKMAP)))


(defun abstract-method (method-rep)
  (declare (xargs :guard (wff-method-decl method-rep)))
  (mem '*abstract* (method-accessflags method-rep)))



;; methods is a list of method



;; ;; method-ptr is a ACL2 object that can be used to locate the method.
;; (defun make-method-ptr (classname methodname args-type return-type)
;;   (list 'method-ptr classname methodname args-type return-type))

;; (defun wff-method-ptr (method-ptr)
;;   (and (true-listp method-ptr)
;;        (equal (len method-ptr) 5)
;; ;;     (consp (nth 3 method-ptr)) this is not necessary. in conflict with
;; ;; functions with no parameter. FIXED 10/28/03
;;        (true-listp (nth 3 method-ptr))))
       


;; (defun method-ptr-classname   (method-ptr) 
;;   (declare (xargs :guard (wff-method-ptr method-ptr)))
;;   (nth 1 method-ptr))

;; (defun method-ptr-methodname  (method-ptr)  
;;   (declare (xargs :guard (wff-method-ptr method-ptr)))
;;   (nth 2 method-ptr))

;; (defun method-ptr-args-type   (method-ptr) 
;;   (declare (xargs :guard (wff-method-ptr method-ptr)))
;;   (nth 3 method-ptr))

;; (defun method-ptr-returntype  (method-ptr)  
;;   (declare (xargs :guard (wff-method-ptr method-ptr)))
;;   (nth 4 method-ptr))

;;
;; this needed because we need to assert that in consistent-state the
;; method-ptr points to correct location!!
;;

;; (defun wff-method-decls (methods)
;;   (if (not (consp methods)) t
;;     (and (wff-method-decl (car methods))
;;          (wff-method-decls (cdr methods)))))


;; (defun searchMethod (method-ptr methods)
;;   (declare (xargs :guard (and (true-listp methods)
;;                               (wff-method-decls methods)
;;                               (wff-method-ptr method-ptr))))
;;   (if (endp methods)
;;       nil
;;     (let* ((methodname (method-ptr-methodname method-ptr))
;;            (args       (method-ptr-args-type  method-ptr))
;;            (returntype (method-ptr-returntype method-ptr))
;;            (thisMethod (car methods)))
;;       (if (and (equal (method-methodname thisMethod) methodname)
;;                (equal (method-args       thisMethod) args)
;;                (equal (method-returntype thisMethod) returntype))
;;           thisMethod
;;         (searchMethod method-ptr (cdr methods))))))




;; (defun deref-method (method-ptr class-table)
;;   (declare (xargs :guard (and (wff-method-ptr method-ptr)
;;                               (wff-instance-class-table class-table))))
;;   (and (class-exists? (method-ptr-classname method-ptr) class-table)
;;        (let* ((classname (method-ptr-classname method-ptr))
;;               (class-rep (class-by-name classname class-table))
;;               (methods   (methods class-rep)))
;;          (and  (wff-method-decls methods)
;;                (searchMethod method-ptr methods)))))


(defun method-exists? (method-ptr cl)
     (declare (xargs :guard (and (wff-method-ptr method-ptr)
                                 (wff-instance-class-table cl))))
     (deref-method method-ptr cl))


(defthm search-method-mem-l
  (implies (searchMethod any-ptr l)
           (mem (searchMethod any-ptr l) l))
  :rule-classes :forward-chaining)
  

(defthm mem-wff-method-decls-wff-method-decl
  (implies (and (mem m methods)
                (wff-method-decls methods))
           (wff-method-decl m))
  :rule-classes :forward-chaining)


(defthm dereef-method-if-found-then-well-formed
  (implies (deref-method any-ptr cl)
           (wff-method-decl (deref-method any-ptr cl)))
  :hints (("Goal" :in-theory (disable wff-method-decl)))
  :rule-classes :forward-chaining)



(in-theory (disable deref-method))
;; enought theorem about deref-method on
;; wff-method-ptr return wff-method
;; if deref-method returns, it returns well formed one. 


(defun valid-method-ptr (method-ptr cl)
  (declare (xargs :guard (and (wff-method-ptr method-ptr)
                              (wff-instance-class-table cl))))
  (and (method-exists? method-ptr cl)
       (not (abstract-method (deref-method method-ptr cl)))))

; (defun valid-sync-obj (obj-ref hp)
;   (declare (xargs :guard (wff-heap hp)))
;   (bound? obj-ref hp)) ;; WRONG 


(defun valid-sync-obj (obj-ref hp)
  (declare (xargs :guard (wff-heap hp)))
  (or (equal obj-ref -1)
      (bound? obj-ref hp))) ;; fixed  10/28/03 
;;
;; Wed Jan 14 01:36:50 2004

(defun Category1 (tvalue)
  (and (wff-tagged-value tvalue)
       (not (equal (tag-of tvalue) 'LONG))
       (not (equal (tag-of tvalue) 'DOUBLE))))

(defun Category2 (tvalue)
  (and (wff-tagged-value tvalue)
       (or (equal (tag-of tvalue) 'LONG)
           (equal (tag-of tvalue) 'DOUBLE))))

(defun top (stack)
  (declare (xargs :guard (consp stack)))
  (car stack))

(defun pop (stack)
  (declare (xargs :guard (consp stack)))
  (cdr stack))

(defun canPopCategory1 (stack)
  (and (>= (len stack) 1)
       (Category1 (top stack))))

(defun canPopCategory2 (stack)
  (and (>= (len stack) 2)
       (Category2 (top stack))
       (equal (top (pop stack)) '(topx . topx))))

(defun topCategory1 (stack)
  (declare (xargs :guard (canPopCategory1 stack)))
  (top stack))

(defun topCategory2 (stack)
  (declare (xargs :guard (canPopCategory2 stack)))
  (top stack))


(defun popCategory2 (stack)
  (declare (xargs :guard (canPopCategory2 stack)))
  (pop (pop stack)))

(defun popCategory1 (stack)
  (declare (xargs :guard (canPopCategory1 stack)))
  (pop stack))


(defun consistent-value-x (tagged-value cl hp)
  (declare (xargs  :guard (and (wff-tagged-value tagged-value)
                               (consistent-class-hierachy cl)
                               (wff-heap-strong hp))))
  (let ((type  (tag-of tagged-value)))
    (if (REFp tagged-value hp) t
      (consistent-value tagged-value type cl hp))))
  


(defun consistent-opstack (stack cl hp)
  (declare (xargs :guard (and (consistent-class-hierachy cl)
                              (wff-heap-strong hp))))
 (if (not (consp stack)) (equal stack nil)
    (cond ((canPopCategory1 stack)
           (and (consistent-value-x (topCategory1 stack) cl hp)
                (consistent-opstack (popCategory1 stack) cl hp)))
          ((canPopCategory2 stack)
           (and (consistent-value-x (topCategory2 stack) cl hp)
                (consistent-opstack (popCategory2 stack) cl hp))))))

;; how do I check for return address being valid?? 


(defun category1Loc (locals)
  (and (consp locals)
       (wff-tagged-value (car locals))
       (Category1 (car locals))))

(defun category2Loc (locals)
  (and (consp locals)
       (consp (cdr locals))
       (wff-tagged-value (car locals))
       (Category2 (car locals))
       (wff-tagged-value (cadr locals))
       (equal (tag-of (cadr locals)) 'topx)))

;; (defun category2Loc (locals)
;;   (and (consp locals)
;;        (consp (cdr locals))
;;        (wff-tagged-value (car locals))
;;        (Category2 (car locals))
;;        (equal (tag-of (car locals)) 'topx)))

(defun shift1slot (locals)
  (declare (xargs :guard (and (not (category2Loc locals))
                              (consp locals))))
  (cdr locals))

(defun shift2slot (locals)
  (declare (xargs :guard (category2Loc locals)))
  (cddr locals))

(defun category1Value (locals)
    (declare (xargs :guard (category1Loc locals)))
    (car locals))

(defun category2Value (locals)
    (declare (xargs :guard (category2Loc locals)))
    (car locals))


;;
;; one different between local and opstack is that value TOP can appear in the
;; locals (representing uninitialized value)
;;


(defun consistent-locals (locals cl hp)
  ;; this one only assert a valid list of types. or top element.
  (declare (xargs :guard (and (consistent-class-hierachy cl)
                              (wff-heap-strong hp))))
  (if (not (consp locals)) (equal locals nil)
    (cond ((category1Loc locals)
           (and (or (equal (tag-of (car locals)) 'topx)
                    (consistent-value-x  (category1Value locals) cl hp))
                (consistent-locals (shift1slot locals) cl hp)))
          ((category2Loc locals)
           (and (consistent-value-x (category2Value locals) cl hp)
                (consistent-locals (shift2slot locals) cl hp))))))


;; ;; (defun consistent-locals (locals cl hp)
;; ;;   ;; this one only assert a valid list of types. or top element.
;; ;;   (declare (xargs :guard (and (consistent-class-hierachy cl)
;; ;;                               (wff-heap-strong hp))))
;; ;;   (if (not (consp locals)) (equal locals nil)
;; ;;     (cond ((category1Loc locals)
;; ;;            (and (consistent-value-x  (category1Value locals) cl hp)
;; ;;                 (consistent-locals (shift1slot locals) cl hp)))
;; ;;           ((category2Loc locals)
;; ;;            (and (consistent-value-x (category2Value locals) cl hp)
;; ;;                 (consistent-locals (shift2slot locals) cl hp))))))

;; Tue Aug 10 14:22:28 2004
;; category1 or category2 
;; some may not be initialized TOP element.
;;

;;
;; need to assert the size of the local for a consistent-state.
;;

;; (defun wff-call-frame (frame)
;;   (and (true-listp frame)
;;        (equal (len frame) 6)
;;        (equal (car frame) 'frame)
;;        (consp (nth 1 frame))
;;        (consp (nth 2 frame))
;;        (consp (nth 3 frame))
;;        (wff-method-ptr (nth 4 frame))
;;        (consp (nth 5 frame))))


;; ; (defun make-frame (return-pc operant-stack locals method-ptr sync-obj-ref)
;; ;   (list 'frame 
;; ;         (cons 'return_pc return-pc)
;; ;         (cons 'operand-stack operant-stack)
;; ;         (cons 'locals locals)
;; ;         method-ptr
;; ;         (cons 'sync-obj-ref sync-obj-ref)))

;; (defun return-pc     (frame)    
;;   (declare (xargs :guard (wff-call-frame frame)))
;;   (cdr (nth 1 frame)))

;; (defun operand-stack (frame)  
;;   (declare (xargs :guard (wff-call-frame frame)))
;;   (cdr (nth 2 frame)))

;; (defun locals        (frame)   
;;   (declare (xargs :guard (wff-call-frame frame)))
;;   (cdr (nth 3 frame)))

;; (defun method-ptr    (frame)  
;;   (declare (xargs :guard (wff-call-frame frame)))
;;   (nth 4 frame))

;; (defun sync-obj-ref  (frame) 
;;   (declare (xargs :guard (wff-call-frame frame)))
;;   (cdr (nth 5 frame)))


;;; moved to jvm-thread.lisp

;;;;;;;;;;;;;;;;;; Wed Jan 14 02:00:21 2004 I AM HERE!!!!  ;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable wff-heap))

;; (acl2::set-verify-guards-eagerness 2)

(defun consistent-frame-max-local (frame cl)
  (mylet* ((method (deref-method (method-ptr frame) cl)))
          (and (wff-call-frame frame)
               (wff-method-ptr (method-ptr frame))
               (wff-instance-class-table cl)
               (wff-method-decl method)
               (or (mem '*abstract* (method-accessflags method))
                   (mem '*native*   (method-accessflags method))
                   (and (wff-code (method-code method))
                        (integerp (method-maxlocals method))
                        (<= (len (locals frame))
                            (method-maxlocals method)))))))
  
;(i-am-here)

;;
;; We need to add a new assertion to say that all method code are well formed!! 
;;

;; (defun wff-method-codes (methods)
;;   (if (not (consp methods)) t
;;     (and (wff-method-decl (car methods))
;;          (wff-code (method-code (car methods)))
;;          (integerp (method-maxlocals (car methods)))
;;          (integerp (method-maxstack  (car methods)))
;;          (wff-method-codes (cdr methods)))))


;; (defun wff-methods-instance-class-rep (class-decl)
;;   (and (wff-class-rep class-decl)
;;        (wff-method-codes (methods class-decl))))


;; (defun wff-methods-instance-class-table-strong (classes)
;;   (if (not (consp classes)) t
;;     (and (wff-methods-instance-class-rep (car classes))
;;          (wff-methods-instance-class-table-strong (cdr classes)))))


;;; Sun May 16 21:07:10 2004. Note. class constructed by static class table may
;;; not be consistent-state using above definition. For example: Native
;;; methods!!. Need to fix class loader to normalize the method
;;; representation!! or fix jvm2acl2!! Fix jvm2acl2, to always generated
;;; correctly formed methods. so that class loader just copying will be good
;;; enough!  
;;;                     Sun Oct 17 15:51:44 2004. already fixed!! 
;;; 
;;; 
;;; Sun Oct 17 15:48:01 2004. We need to assert that there is no frame that
;;; corresponds to some abstract method!! 
;;; 

; (i-am-here) ;; Sun Oct 17 15:55:21 2004

(defun consistent-frame (frame cl hp)
  (declare (xargs :guard (and (consistent-class-hierachy cl)
                              (wff-heap-strong hp))))

  (mylet* ((method (deref-method (method-ptr frame) cl)))
          (and (wff-call-frame frame)
               (consistent-opstack (operand-stack frame) cl hp)
               (consistent-locals  (locals frame) cl hp)
               (consistent-frame-max-local frame cl)
               ;; return-pc' validity check could not be checked at frame level 
               ;; we need caller frame to decide whether it is consistent
               ;; 
               ;; Tue Mar 30 16:10:14 2004 we did not check that len of locals is less
               ;; than max-local. check at runtime
               (wff-method-ptr (method-ptr frame))
               (valid-method-ptr (method-ptr frame) cl)
               (valid-sync-obj   (sync-obj-ref frame) hp)
               
               ;; Mon May 17 11:59:18 2004
               ;; fixed to add assertions about max-stack!! 

               ;; Sun Oct 17 15:47:41 2004
               (wff-method-decl method)
               ;; (not (mem '*abstract* (method-accessflags method)))
               ;; Mon Oct 18 10:34:47 2004. It appears that valid-method-ptr
               ;; already asserted that not abstract!! 
               (not (mem '*abstract* (method-accessflags method)))
               (or (mem '*native* (method-accessflags method))
                   (and (wff-code (method-code method))
                        (integerp (method-maxlocals method))
                        (integerp (method-maxstack method))
                        (<= (len (operand-stack frame))
                            (method-maxstack method)))))))


;; seems to cause an infinite loop! 

(defun consistent-call-stack (callstack cl hp)
  (declare (xargs :guard (and (consistent-class-hierachy cl)
                              (wff-heap-strong hp))))
  ;; tmp implementation 
  ;;
  ;; should assert that each method pointer point to valid place, saved-pc
  ;; within bound? values on op stack and locals and sync obj are valid.
  ;; 
  ;; sync object is pointing to a valid object.
  ;;
  ;; What else? 
  ;;
  ;; Should I assert the last frame must be a frame of particular form
  ;;
  ;; At least one frame? Let me leave this thing out in a different assertion 
  ;; I will not try assert that return addresses are right in this consistent-call-stack

  (if (not (consp callstack)) t
    (and (consistent-frame (car callstack) cl hp)
         (consistent-call-stack (cdr callstack) cl hp))))

;;(i-am-here)

(defun wff-invocation-frame (frame cl)
  (declare (xargs :guard (wff-instance-class-table cl)))
  (mylet* ((method (deref-method (method-ptr frame) cl)))
  (and (wff-call-frame frame)
       (wff-method-ptr (method-ptr frame))
       (valid-method-ptr (method-ptr frame) cl)
       (wff-method-decl method)
       (OR (MEM '*NATIVE*
                (METHOD-ACCESSFLAGS METHOD))
           (AND (WFF-CODE (METHOD-CODE METHOD))
                (INTEGERP (METHOD-MAXLOCALS METHOD))
                (INTEGERP (METHOD-MAXSTACK METHOD))
                (<= (LEN (OPERAND-STACK FRAME))
                    (method-maxstack method)))))))


(defun consistent-adjacent-frame-guard (caller callee cl)
  (and (wff-instance-class-table cl)
       (wff-invocation-frame caller cl)
       (wff-invocation-frame callee cl)
       (not (mem '*native* 
                 (method-accessflags 
                  (deref-method (method-ptr caller) cl))))))

                                    
(defun valid-offset-into (pc instrs)
  (if (not (consp instrs)) nil
    (and (wff-inst (car instrs))
         (or (equal (inst-offset (car instrs)) pc)
             (valid-offset-into pc (cdr instrs))))))
  
                  

(defun consistent-adjacent-frame (caller callee cl)
  (declare (xargs :guard (consistent-adjacent-frame-guard caller callee cl)))
  (and (equal (return-pc callee)
              (resume-pc caller))
       ;; awkward of fact of
       ;; introducing now symbols. 
       (valid-offset-into (return-pc callee) 
                          (method-code (deref-method (method-ptr caller) cl)))
       (<= (+ (len (operand-stack caller))
              (type-size (method-ptr-returntype (method-ptr callee))))
           (method-maxstack (deref-method (method-ptr caller) cl)))))
                                          
                                          

(defun consistent-call-stack-linkage (callstack cl)
  (declare (xargs :guard (wff-instance-class-table cl)))
  (if (not (consp callstack)) t
    (if (not (consp (pop callstack)))
        ;;; the first frame of a thread. 
        (and (wff-invocation-frame (top callstack) cl)
             (equal (return-pc (top callstack)) 'KILL_THREAD)) 
      ;; may need fix
      ;; later!! 
      ;; not very necessary to asser this. 
      (let* ((caller (top (pop callstack)))
             (callee (top callstack)))
        (and (wff-invocation-frame caller cl)
             (wff-invocation-frame callee cl)
             (or (mem '*native* 
                      (method-accessflags (deref-method (method-ptr caller)
                                                        cl)))
                 (consistent-adjacent-frame caller callee cl))
             (consistent-call-stack-linkage (pop callstack) cl))))))





;; (defun make-thread (id pc call-stack s m-ref mdepth thread-ref)
;;   (list 'thread id 
;;      (cons 'saved-pc pc)
;;      (cons 'call-stack call-stack)
;;      (cons 'status s)         ;; 
;;      (cons 'monitor  m-ref)
;;      (cons 'mdepth   mdepth)
;;      (cons 'thread-obj thread-ref)))

;; (defun make-thread (id pc call-stack s m-ref mdepth thread-ref)
;;   (list 'thread id 
;;      (cons 'saved-pc pc)
;;      (cons 'call-stack call-stack)
;;      (cons 'status s)         ;; 
;;      (cons 'monitor  m-ref)
;;      (cons 'mdepth   mdepth)
;;      (cons 'thread-obj thread-ref)))

;; status is a list of 
;; flags 
;; thread_just_born thread_active thread_suspended thread_dead
;; thread_monitor_wait thread_convar_wait 


;; (defun wff-thread (thread) 
;;   (and (true-listp thread)
;;        (equal (len thread) 8)
;;        (consp (nth 2 thread))
;;        (consp (nth 3 thread))
;;        (consp (nth 4 thread))
;;        (consp (nth 5 thread))
;;        (consp (nth 6 thread))
;;        (consp (nth 7 thread))))


;; (defun thread-id (thread)
;;   (declare (xargs :guard (wff-thread thread)))
;;   (nth 1 thread))
  

;; (defun thread-saved-pc    (thread) 
;;   (declare (xargs :guard (wff-thread thread)))
;;   (cdr (nth 2 thread)))

;; (defun thread-call-stack  (thread) 
;;   (declare (xargs :guard (wff-thread thread)))
;;   (cdr (nth 3 thread)))

;; (defun thread-state       (thread) 
;;   (declare (xargs :guard (wff-thread thread)))
;;   (cdr (nth 4 thread))) ;; thread-state is a list

;; (defun thread-mref       (thread)
;;   (declare (xargs :guard (wff-thread thread)))
;;   (cdr (nth 5 thread)))

;; (defun thread-mdepth     (thread) 
;;   (declare (xargs :guard (wff-thread thread)))
;;   (cdr (nth 6 thread)))

;; (defun thread-ref         (thread) 
;;   (declare (xargs :guard (wff-thread thread)))
;;   (cdr (nth 7 thread)))

;;; tmp implementation !! Wed Jan 14 14:23:28 2004


(defun classImplementInterface (rtype interface cl)
  (declare (ignore rtype interface cl))
  t)  ;; temp implementation!! 

#|
(defthm valid-refp-is-implied-by-bounded-in-wff-heap-strong
  (implies (and (wff-heap-strong hp)
                (bound? x hp))
           (valid-refp (tag-ref x) hp)))
|#

(in-theory (disable wff-obj))

(defthm wff-heap-strong-bound-wff-obj
  (implies (and (wff-heap-strong hp)
                (assoc-equal x hp))
           (wff-obj-strong (cdr (assoc-equal x hp))))
  :hints (("Goal" :in-theory (disable wff-heap wff-obj-strong))))

(in-theory (disable wff-obj-strong consistent-class-hierachy wff-heap))

(defthm wff-heap-strong-implies-alistp
  (implies (wff-heap-strong hp)
           (alistp hp))
  :hints (("Goal" :in-theory (enable wff-heap))))



(defun consistent-thread-entry (th cl hp)
  (declare (xargs :guard  (and (consistent-class-hierachy cl)
                               (wff-heap-strong hp))))
  (and (wff-thread th) ;;  10/10/03 
       (Valid-REFp (tag-REF (thread-ref th)) hp)
       ;; make sure that thread-ref is bounded. 
       ;; Not recording the type.  09/14/03 
       ;; 
       (consp (thread-call-stack th)) ;; at list one frame
       (consistent-call-stack (thread-call-stack th) cl hp)
       ;; we could add the next check to see that obj is really a thread or
       ;; some class that implement the java.lang.Runnable interface We need
       ;; this property to prove native method currentThread always return a
       ;; thread obj. We can add this spec on the currentThread instead of
       ;; here. 
       ;; 
       ;; That's add the check at native method, let the defensive
       ;; machine detect that and set the "FATAL error".
       ;; 
       ;; However we can prove M6's native implementation maintain the
       ;; consistent state. 
       ;; 
       (consistent-call-stack-linkage (thread-call-stack th) cl)
       ;; A bunch of invariant!! 
       (let* ((obj (deref2 (tag-REF (thread-ref th)) hp))
              (rtype (obj-type obj)))
         (or (assignmentCompatible rtype "java.lang.Thread" cl)
             (classImplementInterface rtype "java.lang.Runnable" cl)))
       (or (equal (thread-mref th) -1)
           ;; (NULLp (thread-mref th))
           (bound? (thread-mref th) hp))))
           ;;(Valid-REFp (thread-mref th) hp))))
;;
;; In consistent-value, we need also to check no value is of a "interface type"
;; or an "abstract" type. (UPDATE to consistent-value needed!! NEED FIX. 
;; fix in CONSISTENT HEAP?? what could be the problem if we allow such a instance
;; exists in our consistent-state? can some bad thing happen?
;;

(defun consistent-thread-entries (ths cl hp)
  (declare (xargs :guard  (and (consistent-class-hierachy cl)
                               (wff-heap-strong hp))))
  ;; This does not specific the correct locking state
  ;; if some thread locks on non-existing object? 
  ;; what would happen? We only need the object exists
  ;; and we don't check whether thread hold the lock at the same time 
  ;; nor we check that monitor queues are compatibles with thread state
  ;;
  ;; Locking exceptions could happen, because the underlying machine has the
  ;; problem. We want to prove that JVM would fail gracefully, by first
  ;; checking for something. How important is modeling a particular monitor
  ;; implementation?? If we want to study the fairness execution and some
  ;; program's correctness depends on that, we may have to model it then.
  ;;
  ;; However, without a monitor implementation, we could not reason about
  ;; locking count, notify, wait etc. 
  ;;
  ;; In principle we can prove that certain error won't happen because of the 
  ;; native implementation. is THIS true?? We have no control about how user use
  ;; monitors. 
  ;;
  ;; Anyway, we don't restrict this aspect (monitor init state) in a "valid" state.
  ;; Because those inconsistency can be handled correct in JVM with exception
  ;; etc. AGREED  08/15/03 
  ;;
  ;; Defensive machine will check every dereference in fact bounded. 
  ;; We can show this property as corrollory of it preserve the consistency. 
  ;; every pointer in the system is valid. 
  ;;
  (if (not (consp ths)) t
    (and (consistent-thread-entry (car ths) cl hp)
         (consistent-thread-entries (cdr ths) cl hp))))


(defun consistent-thread-table (ths cl hp)
  (declare (xargs :guard  (and (consistent-class-hierachy cl)
                               (wff-heap-strong hp))))
  (consistent-thread-entries ths cl hp))

;----------------------------------------------------------------------

;; (defun wff-aux (aux)
;;   (and (true-listp aux)
;;        (> (len aux) 1)))


;; (defun wff-aux (aux)
;;   (declare (ignore aux))
;;   t)


;; (defun heap-init-map (aux)
;;   (declare (xargs :guard (wff-aux aux)))
;;   (acl2::g 'heap-init-map aux))


;;; moved to jvm-loader.lisp ;; Fri Oct 29 17:54:15 2004


(defun wff-heap-init-map (heap-init-map)
  (alistp heap-init-map))


;; the format of tag is 
;;
;;  nil
;; or 
;;
;; (offset . a-method-ptr)
;;
;; we do not assert that method-exists our deref-method is checking for it
;; explicitly (however in real jvm, certain checking is avoided by caching and
;; shortening the pointers) 
;; 

(defun wff-obj-init-tag (tag)
  (or (equal tag nil)
      (and (consp tag)
           (equal (integerp (car tag))
                  (wff-method-ptr (cdr tag))))))



(defun wff-heap-init-map-strong (heap-init-map)
  (if (not (consp heap-init-map))
      (equal heap-init-map nil)
    (and (consp (car heap-init-map))
         (wff-obj-init-tag (cdar heap-init-map))
         (wff-heap-init-map-strong (cdr heap-init-map)))))



(defun consistent-heap-init-obj-with-heap-obj (obj obj-init)
  (declare (ignore obj obj-init))
  ;; temp implementation 
 t)



(defun consistent-heap-with-heap-init-map (hp hp-init)
  (declare (xargs :guard (and (wff-heap-strong hp)
                              (wff-heap-init-map-strong hp-init))))
  (if (not (consp hp)) (not (consp  hp-init))
    (if (not (consp  hp-init)) nil
      (and (consistent-heap-init-obj-with-heap-obj (car hp) (car hp-init))
           ;; when we assert heap consistent with obj tagging that records
           ;; initialization status 
           (consp (car hp))
           (consp (car hp-init))
           (equal (caar hp) (caar hp-init))
           (consistent-heap-with-heap-init-map (cdr hp) (cdr hp-init))))))

;; these two is not used?? Thu Dec  4 16:15:57 2003
;; No. this is used in the opstack-sig's guard. 
;; 
;; The problem is I probably don't want to verify the guards for those
;; frame-sig functions!!






;; (defun instance-class-table (S)
;;   (declare (xargs :guard (and (wff-state s)
;;                               (wff-class-table (class-table s)))))
;;   (cdr (nth 1 (class-table s))))


;; (defun array-class-table (s)
;;   (declare (xargs :guard (and (wff-state s)
;;                               (wff-class-table (class-table s)))))
;;   (cdr (nth 2 (class-table s))))



; (defun make-env (scl) ;; temp version
;    (list 'env 
;         (cons 'external-class-table
;               scl)))


;; (defun env (s)   
;;   (declare (xargs :guard (wff-state s)))
;;   (nth 6 s)) ;; only loader read from env


; (defun make-env (scl) ;; temp version
;    (list 'env 
;         (cons 'external-class-table
;               scl)))

;; (defun wff-env (env)
;;   (and (true-listp env)
;;        (equal (len env) 2)
;;        (consp (nth 1 env))))


;; (defun env-class-table (env)
;;   (declare (xargs :guard (wff-env env)))
;;   (cdr (nth 1 env)))

;; (defun external-class-table (s)
;;    (declare (xargs :guard (and (wff-state s)
;;                                (wff-env (env s)))))
;;    (env-class-table (env s)))


; (defthm consistent-thread-table-implies-alistp
;   (implies (consistent-thread-table ths cl hp)
;            (alistp ths))
;   :rule-classes :forward-chaining)


;; ; ** from jvm-thread.lisp **
;; (defun wff-thread-table (thread-table)
;;   (if (not (consp thread-table)) t
;;     (and (wff-thread (car thread-table))
;;          (wff-thread-table (cdr thread-table)))))


;; (defun thread-by-id (id thread-table)
;;   (declare (xargs :guard (wff-thread-table thread-table)))
;;   (if (not (consp thread-table))
;;       nil
;;     (if (equal (thread-id (car thread-table)) id)
;;         (car thread-table)
;;       (thread-by-id id (cdr thread-table)))))

;; (defun thread-exists (id tt)
;;   (declare (xargs :guard (wff-thread-table tt)))
;;   (thread-by-id id tt))

(in-theory (enable wff-thread-table))
(defthm consistent-thread-table-implies-wff-thread-table
  (implies (consistent-thread-entries ths cl hp)
           (wff-thread-table ths))
  :rule-classes :forward-chaining)


;; (defun valid-array-type (arraytype cl acl)
;;   (declare (ignore arraytype cl acl))
;;   t) ;; TEMP implementation Thu Dec  4 16:12:54 2003


;; (defun valid-array-type (arraytype cl acl)
;;   ;; Sat Oct 30 00:25:04 2004
;;   (declare (xargs :guard (and (wff-instance-class-table cl)
;;                               (wff-array-class-table acl))))
;;   (and (array-type-s arraytype cl)
;;        (let ((basetype (array-component-type arraytype)))
;;          (and (ArrayClassLoaded1? basetype acl)
;;               (if (isArrayType basetype)
;;                   (valid-array-type basetype cl acl)
;;                 (isClassTerm (class-by-name basetype cl)))))))

       


(in-theory (disable valid-array-type))
;;; Wed Jan 14 14:39:22 2004
;;; Lots of things to do. 

;; We need to assert array object is always initialized!!
;; Sun Oct 31 14:45:33 2004


(defun consistent-heap-array-init-state1 (hp cl acl hp-init)
  (declare (xargs :guard (and (wff-heap-strong hp)
                              (wff-array-class-table acl)
                              (wff-instance-class-table cl)
                              (alistp hp-init))))
  (if (not (consp hp)) t
    (and (or (not (isArrayType (obj-type (cdar hp)))) 
             ;; either it is not array type object
             (and (valid-array-type (obj-type (cdar hp)) cl acl)
                  ;; we need this to assert if array-type, the component type are
                  ;; valid. 
                  (not (assoc-equal (caar hp) hp-init))))
                  ;; Mon Feb 23 18:14:19 2004. This and is added later!!
                  ;; During proof!!
         ;; we need to remember to update hp-init when we create a new array
         ;; object 
         (consistent-heap-array-init-state1 (cdr hp) cl acl hp-init))))

(defun consistent-heap-array-init-state2 (hp hp-init)
  (declare (xargs :guard (and (alistp hp)
                              (alistp hp-init))))
  (if (not (consp hp-init)) t
      (and (assoc-equal (caar hp-init) hp)
           (consistent-heap-array-init-state2 hp (cdr hp-init)))))



;; >V            (DEFUN
;;                ARRAY-OBJ-CONSISTENT1
;;                (DATA-ARRAY COMPONENT-TYPE HP CL)
;;                (DECLARE (XARGS :GUARD
;;                                (AND (TRUE-LISTP DATA-ARRAY)
;;                                     (WFF-HEAP-STRONG HP)
;;                                     (CONSISTENT-CLASS-HIERACHY CL))))
;;                (IF
;;                  (ENDP DATA-ARRAY)
;;                  T
;;                  (AND (CONSISTENT-VALUE (TAG (CAR DATA-ARRAY) COMPONENT-TYPE)
;;                                         COMPONENT-TYPE CL HP)
;;                       (ARRAY-OBJ-CONSISTENT1 (CDR DATA-ARRAY)
;;                                              COMPONENT-TYPE HP CL))))
;;(i-am-here)

(defun array-content-initialized (data-array hp-init)
  (declare (xargs :guard (and (true-listp data-array)
                              (alistp hp-init))))
  (if (endp data-array) t
    (and (or (equal (car data-array) -1)
             (or  (not (bound? (car data-array) hp-init)) 
                  ;; Mon Jun  6 17:35:23 2005
                  ;; either not bound, if it were bound,
                  ;; then it is not consp ..
                  (not (consp (binding (car data-array) hp-init)))))
         (array-content-initialized (cdr data-array) hp-init))))


;; Mon May  2 12:35:41 2005 new addition to assert that 
;; all object refered by some element in the array correctly 
;; initialized. 

(defun consistent-heap-array-init-state3 (hp hp-init)
  (declare (xargs :guard (and (wff-heap-strong hp)
                              (alistp hp-init))))
  (if (not (consp hp)) t
    (and (or (not (isArrayType (obj-type (cdar hp))))
             (and (WFF-INTERNAL-ARRAY (cdar hp)) ;; get pass the guard!! 
                  (or (primitive-type? (array-component-type (obj-type (cdar hp))))
                      (array-content-initialized (array-data (cdar hp)) hp-init))))
         (consistent-heap-array-init-state3 (cdr hp) hp-init))))



(defun consistent-heap-array-init-state (hp cl acl hp-init)
  (declare (xargs :guard (and (wff-heap-strong hp)
                              (wff-array-class-table acl)
                              (wff-instance-class-table cl)
                              (alistp hp-init))))
  (and (wff-heap-init-map-strong hp-init)
       (consistent-heap-array-init-state2 hp hp-init)
       (consistent-heap-array-init-state1 hp cl acl hp-init)
       (consistent-heap-array-init-state3 hp hp-init)))



;;----------------------------------------------------------------------
;;
;; Mon Jul 18 17:49:12 2005
;;
;; Need to assert that consistent-object all the reference-type fields 
;; are properly initialized (or NULL pointer!)
;;
;; Before an object is propertly initialized, reference to it can be stored in
;; an array nor an object!! 
;;
;; BCV make sure that verified code maintains this property.
;;
;;
;; similiar to consistent-heap-array-init-state3 !!
;;

;; (i-am-here) ;; Mon Jul 18 18:01:20 2005

;;   (and (wff-immediate-instance immediate-instance)
;;        (equal obj-type (car immediate-instance))  
;;        ;; this is not right
;;        (class-exists? obj-type cl)
;;        ;; does not handle array object well. 
;;        (let ((fields (cdr immediate-instance))
;;              (field-decls (fields (class-by-name obj-type cl))))
;;          (and (alistp fields) ;; Thu Jun  9 13:30:08 2005.
;;               ;; added because GETFIELD. 
;;               (consistent-fields fields field-decls cl hp)))))


(defun consistent-field-init-state (field field-decl hp-init)
  (declare (xargs :guard (alistp hp-init)))
  (and (wff-data-field field)
       (wff-field-decl field-decl)
       (equal (fieldname field)
              (field-fieldname field-decl))
       (or (primitive-type? (field-fieldtype field-decl))
           ;; reference type!! 
           (or (equal (fieldvalue field) -1) ;; NULLp
               (not (bound? (fieldvalue field) hp-init))))))


(defun consistent-fields-init-state (fields field-decls hp-init)
  (declare (xargs :guard (alistp hp-init)))
  (if (not (consp fields)) (not (consp field-decls))
    (if (not (consp field-decls)) nil
      (and (consistent-field-init-state (car fields) (car field-decls)
                                        hp-init)
           (consistent-fields-init-state (cdr fields) (cdr field-decls)
                                         hp-init)))))



(defun consistent-immedidate-instance-init-state (instance cl hp-init)
  (declare (xargs :guard (and (alistp hp-init)
                              (wff-instance-class-table cl))))
  (and (wff-immediate-instance instance)
       (class-exists? (car instance) cl)
       (let ((fields (cdr instance))
             (field-decls (fields (class-by-name (car instance) cl))))
         (consistent-fields-init-state fields field-decls hp-init))))
                     


(defun consistent-jvp-init-state (jvp cl hp-init)
  (declare (xargs :guard (and (alistp hp-init)
                              (wff-instance-class-table cl))))
  (if (not (consp jvp)) t
    (and (consistent-immedidate-instance-init-state
          (car jvp) cl hp-init)
         (consistent-jvp-init-state (cdr jvp) cl hp-init))))
                                    

(defun consistent-object-init-state (obj cl hp-init)
  (declare (xargs :guard (and (alistp hp-init)
                              (wff-instance-class-table cl)
                              (wff-obj-strong obj))))
  (if (isArrayType (obj-type obj))
      t ;; if array, it will be checked in 
        ;; consistent-heap-array-init-state3 !!! 
    (consistent-jvp-init-state (java-visible-portion obj) cl hp-init)))

(defthm wff-obj-strong-implies-wff-obj
  (implies (wff-obj-strong obj)
           (wff-obj obj))
  :rule-classes :forward-chaining)

(defun consistent-heap-init-state (hp cl hp-init)
  (declare (xargs :guard (and (alistp hp-init)
                              (wff-instance-class-table cl)
                              (wff-heap-strong hp))))
  (if (not (consp hp)) t
    (and (consistent-object-init-state (cdar hp) cl hp-init)
         (consistent-heap-init-state (cdr hp) cl hp-init))))

      













































;;
;;
;;
;;
;;----------------------------------------------------------------------




















;; (defun consistent-heap-array-init-state (hp cl acl hp-init)
;;   (declare (xargs :guard (wff-heap-strong hp)))
;;   (if (not (consp hp)) t
;;     (and (or (not (isArrayType (obj-type (cdar hp)))) 
;;              ;; either it is not array type object
;;              (valid-array-type (obj-type (cdar hp)) cl acl)
;;                   ;; we need this to assert if array-type, the component type are
;;                   ;; valid. 
;;              (not (binding (caar hp) hp-init)))
;;                   ;; Mon Feb 23 18:14:19 2004. This and is added later!!
;;                   ;; During proof!!
;;          ;; we need to remember to update hp-init when we create a new array
;;          ;; object 
;;          (consistent-heap-array-init-state (cdr hp) cl acl hp-init))))

;;; Sun May 16 20:57:43 2004. In order to prove 


;; (skip-proofs 
;;  (defthm consistent-state-implies-max-stack-guard-true
;;    (implies (consistent-state s)
;;             (max-stack-guard s))
;;    :rule-classes :forward-chaining))


;; (skip-proofs 
;;  (defthm consistent-state-implies-max-stack-integerp
;;    (implies (consistent-state s)
;;             (integerp (max-stack s)))
;;    :rule-classes :forward-chaining))

;; in consistent-state-properties.lisp

;; ;;
;; ;; We need to add a new assertion to say that all method code are well formed!! 
;; ;;

(defun wff-method-codes (methods)
  (if (not (consp methods)) t
    (and (wff-method-decl (car methods))
         (wff-code (method-code (car methods)))
         (integerp (method-maxlocals (car methods)))
         (integerp (method-maxstack  (car methods)))
         (wff-method-codes (cdr methods)))))


(defun wff-methods-instance-class-rep (class-decl)
  (and (wff-class-rep class-decl)
       (wff-method-codes (methods class-decl))))


(defun wff-methods-instance-class-table-strong (classes)
  (if (not (consp classes)) t
    (and (wff-methods-instance-class-rep (car classes))
         (wff-methods-instance-class-table-strong (cdr classes)))))


;;; Sun May 16 21:07:10 2004. Note. class constructed by static class table may
;;; not be consistent-state using above definition. For example: Native
;;; methods!!. Need to fix class loader to normalize the method
;;; representation!! or fix jvm2acl2!! Fix jvm2acl2, to always generated
;;; correctly formed methods. so that class loader just copying will be good
;;; enough! 

(defun array-class-table-inv (s)
  (jvm::load_array_class_guard s))

;; Sun Aug  8 15:33:38 2004. At any point, we can load an array class
;; Basically it assert that all array-base types are loaded. 
;;

(defun instance-class-table-inv (s)
  (jvm::load_class-guard s))


;(i-am-here) ;; Sun Oct 17 15:43:51 2004

;;; Tue Oct 19 17:38:45 2004. need to assert some basic properties of
;;; loaded classes

;;(i-am-here) ;; Thu Jun 16 19:57:02 2005
(defun boot-strap-class-okp (s)
  (declare (xargs :guard (and (wff-state s)
                              (wff-class-table (class-table s))
                              (wff-heap-strong (heap s))
                              (wff-env (env s))
                              (wff-static-class-table-strong
                               (external-class-table s))
                              (wff-instance-class-table-strong
                               (instance-class-table s))
                              (CONSISTENT-CLASS-HIERACHY (INSTANCE-CLASS-TABLE S))
                              (wff-array-class-table (array-class-table s)))))
  (and (class-loaded? "java.lang.Object" s)
       (class-loaded? "java.lang.Class" s)
       (class-loaded? "java.lang.String" s)
;;        (null (super 
;;               (class-by-name "java.lang.Object" 
;;                              (instance-class-table s))))
       (equal (super 
               (class-by-name "java.lang.Object" 
                              (instance-class-table s))) "")
       (equal (fields (class-by-name "java.lang.Object"  (instance-class-table s))) nil)
       (JVM::correctly-loaded? "java.lang.Object" (instance-class-table s)
                               (external-class-table s))
       (JVM::correctly-loaded? "java.lang.Class" (instance-class-table s)
                               (external-class-table s))
       (JVM::correctly-loaded? "java.lang.String" (instance-class-table s)
                               (external-class-table s))
       (build-a-java-visible-instance-guard "java.lang.Object" s)
       (build-a-java-visible-instance-guard "java.lang.Class" s)
       (build-a-java-visible-instance-guard "java.lang.String" s)
       (CONSISTENT-JVP "java.lang.Object"
                       '(("java.lang.Object"))
                       (INSTANCE-CLASS-TABLE S)
                       (HEAP S)) ;; 
       ;; Thu Jun 16 19:53:48 2005 new addition!! 

       ;; Sun Oct 31 19:44:54 2004. in order to prove load_cp_entry preserves
       ;; the consistent-state we need to add assertions to say that (array
       ;; char) is already defined!
       ;; 
       ;; (not (class-by-name "" (instance-class-table s))) 
       ;; Wed Jun 22 22:04:49 2005 
       ;; no need to assert this just yet!! 
       ;; this may break a few proofs!! 
       (array-class-exists? '(array char) (array-class-table s))
       (mv-let (found rep)
               (class-by-name-s "" (external-class-table s))
               (declare (ignore rep))
               (not found))))

;;; Tue Oct 19 17:46:23 2004
;;;
;;; overly strong/explicit. build-a-java-visible-instance-guard is probably
;;; provable from loader-inv + boot-strap-class-okp
;;;
       

(defthm consistent-heap-implies-wff-heap-strong
  (implies (consistent-heap hp cl acl)
           (wff-heap-strong hp))
  :hints (("Goal" :in-theory (enable consistent-heap)))
  :rule-classes :forward-chaining)


;----------------------------------------------------------------------

;; Wed May  4 22:14:38 2005
;; 
;; Redefined here to 

(include-book "../BCV/bcv-functions-basic")
(include-book "../BCV/bcv-functions-basic-verify-guard")

;; (defun collect-thread-id (tt)
;;   (declare (xargs :guard (wff-thread-table tt)))
;;   (if (consp tt)
;;       (cons (thread-id (car tt)) 
;;             (collect-thread-id (cdr tt)))
;;     nil))

;; (defun unique-thread-id (tt)
;;   (unique (collect-thread-id tt)))

;;Tue Dec 23 14:45:43 2003
(defun consistent-state (s) 
  ;; this s is a tagged state 
  ;; the purpose is that consistent-state is strong enough
  ;; safe machine will guarantee to from a consistent-state to a next
  ;; consistent-state
  ;;
  ;; We will prove that bytecode verified program also provide such guarantee. 
  ;; so the definition of this state is essential
  (and (wff-state s) ;; syntatically correct
       (wff-env (env s))
       (wff-aux (aux s)) ;; Tue Dec 23 14:47:51 2003 aux structurally correct.
       (alistp (heap-init-map (aux s))) ;; Mon Feb 23 18:40:46 2004. 
       (WFF-HEAP-INIT-MAP-STRONG (HEAP-INIT-MAP (AUX S)))
       ;; (wff-heap-init-map-strong (heap-init-map (aux s))) ;; Wed Mar 17 00:23:17 2004
       (wff-class-table (class-table s))
       (wff-instance-class-table-strong (instance-class-table s))
       (wff-array-class-table (array-class-table s))
       (wff-static-class-table-strong (external-class-table s))
       (wff-methods-instance-class-table-strong (instance-class-table s))
       ;; Mon May 17 11:57:08 2004. Added to show max-stack-guard is true. 
       ;;
       ;; Sun Apr 30 19:34:17 2006. these above assertion is problematic
       ;; because it incorrectly assume none of the methods are native,
       ;; abstract!
       ;; 
       ;; (wff-thread-table (thread-table s))
       (consistent-class-hierachy (instance-class-table s))
       ;; Have to assert this
       ;; So that consistent-value's guard could be met
       (consistent-heap (heap s) 
                        (instance-class-table s) 
                        (array-class-table s))

       ;; Tue Jul 19 11:17:21 2005 ;; Tue Jul 19 11:17:28 2005
       (consistent-heap-init-state (heap s)
                                   (instance-class-table s)
                                   (heap-init-map (aux s))) 
       ;; Tue Jul 19 11:17:49 2005 
       ;;
       ;; ADDED for GETFIELD TO ASSUME GETTING FROM 
       ;; 
       
       ;; the following is new addition Thu Dec  4 16:19:49 2003
       (consistent-heap-array-init-state (heap s)
                                         (instance-class-table s)
                                         (array-class-table s)
                                         (heap-init-map (aux s)))
       ;; Haven't Need to rerun consistent-state preserving proof
       ;; check in for now. Thu Dec  4 16:25:28 2003
       ;;
       ;; We need to add assertions to say methods are well formed!!
       ;; Mon Mar 29 21:38:05 2004. 
       ;; 
       (consistent-class-table (instance-class-table s) 
                                (external-class-table s) (heap s))
        ;;
        ;; ASSERT consistent-class-hierachy
        ;;        the relation between CL and SCL
        ;;        the values contained in CL are of right type.
        ;;
        ;; Mon Mar 29 21:14:10 2004. 
        ;; 
        ;; To deal max stack. We need to assert that each call frame contains
        ;; valid method-pointer method-pointer points to valid
        ;; methods.. (valid-method-ptr . added a while ago) 
        ;;
       (consistent-thread-table (thread-table s) 
                                 (instance-class-table s)
                                 (heap s))
        ;; ASSERT call-stack contains propertly typed value.
        ;;(consp (thread-table s))
        ;; (bound? (current-thread s) (thread-table s))
       ;;(wff-thread-table (thread-table s))
       (unique-id-thread-table (thread-table s))
       (thread-exists? (current-thread s) (thread-table s))
       ;; something about pc, status flag?? 
       (instance-class-table-inv s)
       (array-class-table-inv s)
       (boot-strap-class-okp s)

       ;;; Sun Oct 17 15:43:57 2004 added. after 
       ;;; a proof that consistent-state implies max-stack-guard!! 
       ;;;
       
       ;;  (not (MEM '*ABSTRACT* (METHOD-ACCESSFLAGS 
       ;;                        (deref-method (method-ptr (current-frame s))
       ;;                                      (instance-class-table s)))))

       ;;; We need to assert that this is true on every call stack
       ;;;
       ;;; actual method in execution!! 
       ;;; 
       ;;;

       ;;(class-loaded? "java.lang.Object" s)
       ;;(class-loaded? "java.lang.Class" s)
       ;;(jvm::loader-inv s) ;; Sun Aug  8 14:57:37 2004
       ;;(jvm::load_array_class_guard s)
       ;; we need now to reason about changing something else does not modify
       ;; loader-inv!! 

       
       (equal (bcv::scl-bcv2jvm (bcv::scl-jvm2bcv (external-class-table s)))
              (external-class-table s))
       ;;; Wed May  4 22:18:47 2005
       (bcv::good-scl (bcv::scl-jvm2bcv (external-class-table s)))
       ;; Fri Jul 15 18:16:20 2005
       ;; in order to do proofs in base-consistent-state-good-icl-etc.lisp
       ;;
       ;;; The problematic!! Guard verification!! I didn't verify guards
       ;;; of primitives of BCV!!. 
       ;;; chain of requirements!! 
       ))

;----------------------------------------------------------------------
;
;
; used for base-object-field-always-initialized.lisp
;
; Wed Jul 20 23:24:27 2005
;

(acl2::set-verify-guards-eagerness 0)

(defun get-field-type1 (fieldname fields) 
  (if (not (consp fields)) nil
    (if (equal (field-fieldname (car fields))
               fieldname)
        (field-fieldtype (car fields))
      (get-field-type1 fieldname (cdr fields)))))


(defun get-field-type (classname fieldname cl)
  (mylet* ((class-rep (class-by-name classname cl))
           (fields    (fields class-rep)))
          (get-field-type1 fieldname fields)))

;----------------------------------------------------------------------
