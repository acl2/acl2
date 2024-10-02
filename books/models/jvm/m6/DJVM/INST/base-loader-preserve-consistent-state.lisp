(in-package "DJVM")
(include-book "../../DJVM/consistent-state")
(include-book "../../DJVM/consistent-state-properties")
(include-book "../../M6-DJVM-shared/jvm-loader-guard-verification")


(encapsulate ()
  (local (include-book "base-consistent-state-step-definition"))
  (defun consistent-state-step (s)
    (and
     (wff-state s)
     (wff-env (env s))
     (wff-aux (aux s))
     (alistp (heap-init-map (aux s)))
     (wff-heap-init-map-strong (heap-init-map (aux s)))
     (wff-class-table (class-table s))
     (wff-instance-class-table-strong (instance-class-table s))
     (wff-array-class-table (array-class-table s))
     (wff-static-class-table-strong (external-class-table s))
     (wff-methods-instance-class-table-strong
      (instance-class-table s))
     (consistent-class-hierachy (instance-class-table s))
     (consistent-heap (heap s)
                      (instance-class-table s)
                      (array-class-table s))
     (consistent-heap-init-state (heap s)
                               (instance-class-table s)
                               (heap-init-map (aux s)))
     (consistent-heap-array-init-state (heap s)
                                       (instance-class-table s)
                                       (array-class-table s)
                                       (heap-init-map (aux s)))
     (consistent-class-table (instance-class-table s)
                             (external-class-table s)
                             (heap s))
     (consistent-thread-table (thread-table s)
                              (instance-class-table s)
                              (heap s))
     (unique-id-thread-table (thread-table s))
     (thread-exists? (current-thread s)
                     (thread-table s))
     (instance-class-table-inv s)
     (array-class-table-inv s)
     (boot-strap-class-okp s)
     (equal (bcv::scl-bcv2jvm
             (bcv::scl-jvm2bcv (external-class-table s)))
            (external-class-table s))
     (bcv::good-scl (bcv::scl-jvm2bcv (external-class-table s))))))



;; (defun consistent-state-step (s) 
;;   (and (wff-state s) ;; syntatically correct
;;        (wff-env (env s))
;;        (wff-aux (aux s)) ;; Tue Dec 23 14:47:51 2003 aux structurally correct.
;;        (alistp (heap-init-map (aux s))) ;; Mon Feb 23 18:40:46 2004. 
;;        ;; (wff-heap-init-map-strong (heap-init-map (aux s))) ;; Wed Mar 17 00:23:17 2004
;;        (wff-class-table (class-table s))
;;        (wff-instance-class-table-strong (instance-class-table s))
;;        (wff-array-class-table (array-class-table s))
;;        (wff-static-class-table-strong (external-class-table s))
;;        (wff-methods-instance-class-table-strong (instance-class-table s))
;;        (consistent-class-hierachy (instance-class-table s))
;;        (consistent-heap (heap s) 
;;                         (instance-class-table s) 
;;                         (array-class-table s))
;;        (consistent-heap-array-init-state (heap s)
;;                                          (instance-class-table s)
;;                                          (array-class-table s)
;;                                          (heap-init-map (aux s)))
;;        (consistent-class-table (instance-class-table s) 
;;                                 (external-class-table s) (heap s))
;;        (consistent-thread-table (thread-table s) 
;;                                  (instance-class-table s)
;;                                  (heap s))
;;        (unique-id-thread-table (thread-table s))
;;        (thread-exists? (current-thread s) (thread-table s))
;;        (instance-class-table-inv s)
;;        (array-class-table-inv s)
;;        (boot-strap-class-okp s)
;;        ))



; Introducing consistent-state-step trick
;
;;; In order to establish a consistate-state preserving
;;; operation. We want to enable the "goal" term, but we do not
;;; want ACL2 rewriter to open up the consistent-state term in
;;; the hypothesis. Instead we just prove necessary properties of
;;; consistent-state.

;  In order to prove: 
;
; (defthm load_class2-preserve-consistency
;   (implies 
;    (consistent-state s)
;    (consistent-state (load_class2 any s))))
;
; We prove 
;
; (defthm load_class2-preserve-consistency-lemma
;   (implies 
;    (consistent-state s)
;    (consistent-state-step (load_class2 any s))))
;
; with consistent-state disabled. 
; and consistent-state-step enabled. 
;
; The we prove 
;
;  (defthm consistent-state-step-consistent-state-load_class2
;    (implies (consistent-state-step (load_class2 any s))
;             (consistent-state (load_class2 any s))))
;

(in-theory (disable heap-init-map))

(defthm heap-init-map-alistp-1
  (implies (alistp (heap-init-map (aux s)))
           (alistp (heap-init-map (aux (mv-nth 1 (load_cp_entry cp s))))))
  :hints (("Goal" :in-theory (enable load_cp_entry))))


(defthm heap-init-map-alistp-2
  (implies (alistp (heap-init-map (aux s)))
           (alistp (heap-init-map (aux (mv-nth 1 (load_cp_entries cps s)))))))


(defthm make-trace-alistp
  (implies (alistp list)
           (alistp (make-trace any list))))


(defthm add-obj-th-count-alistp
  (implies (alistp list)
           (alistp (add-obj-th-count any th list))))


(defthm trace-alistp-1
  (implies (alistp (acl2::G 'trace (aux s)))
           (alistp (acl2::G 'trace (aux (mv-nth 1 (load_cp_entry cp s))))))
  :hints (("Goal" :in-theory (e/d (load_cp_entry aux-set-trace)
                                  (add-obj-th-count)))))


(defthm trace-alistp-2
  (implies (alistp (acl2::G 'trace (aux s)))
           (alistp (acl2::G 'trace (aux (mv-nth 1 (load_cp_entries cps s)))))))

  
;;; Sat Oct 30 00:06:06 2004
;;;
;;; In ACL2 it is hard to say 
;;;
;;;  The effect of an operation is to add something to some other
;;;  things.  And adding something does not affect a certain
;;;  property.  So any composition of the operations preserve the
;;;  property
;;; 
;;; We need to go via an equivalence relation!! 
;;; 
;;;    equivalence vs. existential qualifier. 



(defthm consistent-heap-array-init-state2-array-bind
  (implies (consistent-heap-array-init-state2 hp hp-init)
           (consistent-heap-array-init-state2 (bind ref obj hp) hp-init)))


(defthm bound?-hp-implies
  (implies (bound? ref hp)
           (bound? ref (cons (cons any1 any2) hp)))
  :hints (("Goal" :in-theory (enable bound?))))


(defthm consp-len-equal
  (implies (consp hp)
           (equal (+ 1 (len (cdr hp)))
                  (len hp)))
  :rule-classes :linear)


(defthm consistent-array-object-implies-valid-array-type
  (implies (consistent-array-object obj hp cl acl)
           (valid-array-type (obj-type obj) cl acl))
  :hints (("Goal" :in-theory (enable consistent-array-object))))

(defthm consistent-heap-array-init-state1-bind-new-array
  (implies (and (not (bound? ref hp-init))
                (valid-array-type (obj-type obj) cl acl)
                (consistent-heap-array-init-state1 hp cl acl hp-init))
           (consistent-heap-array-init-state1 (bind ref obj hp) cl acl
                                              hp-init))
  :hints (("Goal" :in-theory (enable bound?)
           :do-not '(generalize))))


(defthm consistent-heap-array-init-state2-bound-bound
  (implies (and (consistent-heap-array-init-state2 hp hp-init)
                (not (bound? ref hp)))
           (not (bound? ref hp-init)))
  :hints (("Goal" :in-theory (enable bound?)))
  :rule-classes :forward-chaining)

(defthm consistent-heap-array-init-state2-bound-bound-b
  (implies (and (consistent-heap-array-init-state2 hp hp-init)
                (not (bound? ref hp)))
           (not (bound? ref hp-init)))
  :hints (("Goal" :in-theory (enable bound?))))

(defthm consistent-heap-array-init-state1-bind-not-array
  (implies (and (not (bound? ref hp-init))
                (not (isArrayType (obj-type obj)))
                (consistent-heap-array-init-state1 hp cl acl hp-init))
           (consistent-heap-array-init-state1 (bind ref obj hp) cl acl
                                              hp-init))
  :hints (("Goal" :in-theory (enable bound?)
           :do-not '(generalize))))


(defthm consistent-heap-array-init-state3-bind-not-array
  (implies (and (not (bound? ref hp-init))
                (not (isArrayType (obj-type obj)))
                (consistent-heap-array-init-state3 hp  hp-init))
           (consistent-heap-array-init-state3 (bind ref obj hp) hp-init))
  :hints (("Goal" :in-theory (enable bound?)
           :do-not '(generalize))))



(defthm consistent-heap-array-init-state-if-new-object-is-not-array
  (implies (and (consistent-heap-array-init-state hp cl acl hp-init)
                (not (isArrayType (obj-type obj)))
                (not (bound? ref hp)))
           (consistent-heap-array-init-state (bind ref obj hp)
                                             cl acl hp-init)))


;;; Thu May 26 23:06:45 2005 
;;; added!! 
;;;

(defthm consistent-heap-array-init-state3-bind-new-array
  (implies (and (not (bound? ref hp-init))
                (WFF-INTERNAL-ARRAY obj)  ;;; 
                (or (primitive-type? (ARRAY-COMPONENT-TYPE (OBJ-TYPE obj)))
                    (ARRAY-CONTENT-INITIALIZED (ARRAY-DATA obj)
                                               HP-INIT))
                (consistent-heap-array-init-state3 hp hp-init))
           (consistent-heap-array-init-state3 (bind ref obj hp) hp-init))
  :hints (("Goal" :in-theory (e/d (bound?) 
                                  (primitive-type? 
                                   wff-internal-array
                                   array-component-type
                                   array-data))
           :do-not '(generalize))))

;;; because we added that consistent-heap-array-init-state to assert all
;;; array's component contained in the consistent-state are initialized!!
;;;



(defthm consistent-heap-array-init-state-if-new-object-is-new-array
  (implies (and (consistent-heap-array-init-state hp cl acl hp-init)
                (valid-array-type (obj-type obj) cl acl)
                (WFF-INTERNAL-ARRAY obj)
                (or (primitive-type? (ARRAY-COMPONENT-TYPE (OBJ-TYPE obj)))
                    (ARRAY-CONTENT-INITIALIZED (ARRAY-DATA obj)
                                               HP-INIT))                
                (not (bound? ref hp)))
           (consistent-heap-array-init-state (bind ref obj hp)
                                             cl acl hp-init)))




(defthm isClassTerm-add-class-decl
  (implies (and (ISCLASSTERM (CLASS-BY-NAME BASETYPE CL))
                (isclassterm class-rep))
           (isclassterm (class-by-name basetype (add-instance-class-entry
                                                 class-rep cl))))
  :hints (("Goal" :in-theory (enable add-instance-class-entry))))

(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

(local (include-book "arithmetic-2/meta/top" :dir :system))


(defun fix-zp-mode (mode)
  (declare (xargs :guard (and (integerp mode)
                              (<= 0 mode))))
  (if (zp mode) 0
    1))

; valid-type-s 
;
; reference-type-s is mutual recursive with array-type-s
; 
; This makes it is difficult to do current induction
; and harder to prove properties of functions.
;
; valid-type-s is defined to merge array-type-s and
; reference-type-s


(defun valid-type-s (type cl mode)
    (DECLARE (XARGS :GUARD
                    (WFF-INSTANCE-CLASS-TABLE CL)
                    :hints (("Goal" :in-theory (enable array-component-type)))
                    :MEASURE
                    (CONS (+ (ACL2-COUNT TYPE) 1) (fix-zp-mode mode))))
    (cond ((equal mode 1)
           (OR (EQUAL TYPE 'NULL)
               (valid-type-s TYPE  CL 0)
               (CLASS-EXISTS? TYPE cl)))
          ((equal mode 0) 
           (AND (WFF-ARRAY-TYPE TYPE)
                (OR (PRIMITIVE-TYPE? (ARRAY-COMPONENT-TYPE TYPE))
                    (AND (valid-TYPE-S (ARRAY-COMPONENT-TYPE TYPE) cl 1)
                         (NOT (EQUAL (ARRAY-COMPONENT-TYPE TYPE)
                                     'NULL))))))))

(defthm valid-type-s-add-class-decl
  (implies (and (valid-type-s type cl mode)
                (isclassterm class-rep))
           (valid-type-s type (add-instance-class-entry class-rep cl) mode)))


;;; basically copy from the definition of the reference-type-s, array-type-s

(defun induct-valid-type-is-m (type1 type2 mode)
  (cond ((equal mode 1)
         (cons (cons (+ 1 (acl2-count type1)) 0) 1))
        ((equal mode 0)
         (cons (cons (+ 1 (acl2-count type2)) 0) 0))
        (t 0)))


(acl2::set-verify-guards-eagerness 0)
(defun induct-valid-type-is (type1 cl1 type2 cl2 mode)
  (declare (xargs :measure (induct-valid-type-is-m type1 type2 mode)
                  :hints (("Goal" :do-not '(generalize)
                           :in-theory (enable array-component-type)))))
  (cond ((equal mode 1)
         (induct-valid-type-is type1 cl1 type1 cl1 0))
        ((equal mode 0)
         (if (wff-array-type type2)
             (induct-valid-type-is (array-component-type type2) cl2 
                                   type2 cl2 1)
           (list type1 cl1 type2 cl2 mode)))))
(acl2::set-verify-guards-eagerness 2)



(defthm valid-type-s-is-lemma
  (cond ((equal mode 1)
         (equal (valid-type-s type1 cl1 1)
                (reference-type-s type1 cl1)))
        ((equal mode 0)
         (equal (valid-type-s type2 cl2 0)
                (array-type-s type2 cl2)))
        (t t))
  :hints (("Goal" :in-theory (disable isclassterm)
           :induct (induct-valid-type-is type1 cl1 type2 cl2 mode)))
  :rule-classes nil)




(defthm valid-type-s-is
  (and (equal (valid-type-s type cl 1)
              (reference-type-s type cl))
        (equal (valid-type-s type cl 0)
               (array-type-s type cl)))
  :hints (("Goal" :use ((:instance 
                         valid-type-s-is-lemma
                         (cl1 cl) (type1 type) (mode 1))
                        (:instance 
                         valid-type-s-is-lemma
                         (cl2 cl) (type2 type) (mode 0)))))
  :rule-classes nil)



;; (defthm array-type-add-class-decl
;;   (implies (and (array-type-s type cl)
;;                 (isclassterm class-rep))
;;            (ARRAY-TYPE-S TYPE
;;                          (ADD-INSTANCE-CLASS-ENTRY CLASS-REP CL)))
;;   :hints (("Goal" :in-theory (e/d (add-instance-class-entry array-type-s)
;;                                   (isclassterm))
;;            :use ((:instance 
;;                   valid-type-s-is 
;;                   (type2 type)
;;                   (cl2 (add-instance-class-entry class-rep cl)))))))


(defthm array-type-add-class-decl
  (implies (and (array-type-s type cl)
                (isclassterm class-rep))
           (ARRAY-TYPE-S TYPE
                         (ADD-INSTANCE-CLASS-ENTRY CLASS-REP CL)))
  :hints (("Goal" :in-theory (e/d (add-instance-class-entry array-type-s)
                                  (isclassterm))
           :use ((:instance valid-type-s-is)
                 (:instance valid-type-s-is
                            (cl (add-instance-class-entry class-rep cl)))
                 (:instance valid-type-s-add-class-decl
                            (mode 0))))))
                           
                           

(defthm reference-type-s-add-class-decl
  (implies (and (reference-type-s  type cl)
                (isclassterm class-rep))
           (reference-type-s  TYPE
                         (ADD-INSTANCE-CLASS-ENTRY CLASS-REP CL)))
  :hints (("Goal" :in-theory (e/d (add-instance-class-entry array-type-s)
                                  (isclassterm))
           :use ((:instance valid-type-s-is)
                 (:instance valid-type-s-is
                            (cl (add-instance-class-entry class-rep cl)))
                 (:instance valid-type-s-add-class-decl
                            (mode 1))))))
                           


(defthm array-type-add-class-decl-loose
  (implies (and (array-type-s type cl)
                (isclassterm class-rep))
           (ARRAY-TYPE-S TYPE
                         (cons CLASS-REP CL)))
  :hints (("Goal" :in-theory (e/d (array-type-s add-instance-class-entry)
                                  (isclassterm))
           :use array-type-add-class-decl)))

                           

(defthm reference-type-s-add-class-decl-loose
  (implies (and (reference-type-s  type cl)
                (isclassterm class-rep))
           (reference-type-s  TYPE
                         (cons CLASS-REP CL)))
  :hints (("Goal" :in-theory (e/d (array-type-s add-instance-class-entry)
                                  (isclassterm))
           :use reference-type-s-add-class-decl)))
                           




(defthm valid-array-type-add-class-decl
  (implies (and (valid-array-type type cl acl)
                (isclassterm class-rep))
           (valid-array-type type (add-instance-class-entry class-rep cl) acl))
  :hints (("Goal" :in-theory (e/d (valid-array-type ;;add-instance-class-entry
                                                    array-type-s)
                                  (isclassterm))
           :do-not '(generalize))))


(defthm valid-array-type-add-class-decl-loose
  (implies (and (valid-array-type type cl acl)
                (isclassterm class-rep))
           (valid-array-type type (cons class-rep cl) acl))
  :hints (("Goal" :in-theory (e/d (array-type-s add-instance-class-entry)
                                  (isclassterm))
           :use valid-array-type-add-class-decl)))


(defthm consistent-heap-array-init-state1-add-class-decl
  (implies (and (consistent-heap-array-init-state1 hp cl acl hp-init)
                (isclassterm class-rep))
           (CONSISTENT-HEAP-ARRAY-INIT-STATE1 HP
                                     (add-instance-class-entry class-rep cl)
                                     ACL HP-INIT))
  :hints (("Goal" :in-theory (disable isclassterm))))

(defthm consistent-heap-array-init-state1-add-class-decl-loose
  (implies (and (consistent-heap-array-init-state1 hp cl acl hp-init)
                (isclassterm class-rep))
           (CONSISTENT-HEAP-ARRAY-INIT-STATE1 HP
                                     (cons class-rep cl)
                                     ACL HP-INIT))
  :hints (("Goal" :in-theory (disable isclassterm)
           :use consistent-heap-array-init-state1-add-class-decl)))

(defthm consistent-heap-array-init-state-extending-class-table
  (implies (and (consistent-heap-array-init-state hp cl acl hp-init)
                (isClassTerm class-rep))
           (consistent-heap-array-init-state hp (add-instance-class-entry 
                                                   class-rep cl) acl hp-init))
  :hints (("Goal" :in-theory (disable isclassterm))))


(defthm consistent-heap-array-init-state-extending-class-table-loose
  (implies (and (consistent-heap-array-init-state hp cl acl hp-init)
                (isClassTerm class-rep))
           (consistent-heap-array-init-state hp (cons
                                                   class-rep cl) acl hp-init))
  :hints (("Goal" :in-theory (e/d (add-instance-class-entry)
                                  (isclassterm consistent-heap-array-init-state))
           :use consistent-heap-array-init-state-extending-class-table)))


(local (include-book "arithmetic-2/meta/top" :dir :system))

(defthm consistent-heap1-implies-not-bound?-len
  (implies (consistent-heap1 hp1 hp cl id)
           (not (bound? (+ id (len hp1))
                        hp1)))
  :hints (("Goal" :in-theory (enable bound?)
           :do-not '(generalize))))

(in-theory (disable bound? consistent-heap consistent-object))

(defthm consistent-heap-implies-not-bound?-len
  (implies (consistent-heap hp cl acl)
           (not (bound? (len hp) hp)))
  :hints (("Goal" :in-theory (enable consistent-heap)
           :use ((:instance consistent-heap1-implies-not-bound?-len
                            (id 0) (hp1 hp)))
           :do-not-induct t)))


(defthm consistent-heap-implies-not-bound?-len-f
  (implies (consistent-heap hp cl acl)
           (not (bound? (len hp) hp)))
  :rule-classes :forward-chaining)


(defthm consistent-heap-array-init-state2-bound-bound-b-specific
  (implies (and (consistent-heap-array-init-state2 hp (heap-init-map aux))
                (not (bound? (len hp) hp)))
           (not (bound? (len hp) (heap-init-map aux))))
  :hints (("Goal" :in-theory (enable bound?))))


(defthm consistent-heap1-implies-not-bound?-len-specific
  (implies (consistent-heap1 hp1 hp cl 0)
           (not (bound? (len hp1) hp1)))
  :hints (("Goal" :in-theory (enable bound?)
           :use ((:instance consistent-heap1-implies-not-bound?-len
                            (id 0)))
           :do-not '(generalize))))



(defthm consistent-heap1-consistent-heap1
  (implies (and (consistent-heap1 hp1 hp cl id)
                (consistent-object obj hp cl))
           (consistent-heap1 (bind (+ id (len hp1)) obj hp1) hp cl id))
  :hints (("Goal" :in-theory (disable consistent-object)
           :do-not '(generalize))))


(defthm consistent-heap1-consistent-heap1-specific
  (implies (and (consistent-heap1 hp1 hp cl 0)
                (consistent-object obj hp cl))
           (consistent-heap1 (bind (len hp1) obj hp1) hp cl 0))
  :hints (("Goal" :use ((:instance consistent-heap1-consistent-heap1
                                   (id 0))))))



(defthm deref2-v-in-extended-heap-is-not-changed
  (implies (and (not (bound? new-addr hp))
                (bound? (rREF v) hp)
                (alistp hp))
           (equal (deref2 v (bind new-addr any hp))
                  (deref2 v hp)))
  :hints (("Goal" :in-theory (e/d (bound? deref2 binding) ()))))


(defthm REFp-extend-heap
  (implies (and (REFp v hp)
                (alistp hp))
           (REFp v (bind new-addr any hp)))
  :hints (("Goal" :in-theory (enable bound? bind))))



(defthm consistent-value-bind-new-object-1
  (implies (and (consistent-value v type cl hp)
                (alistp hp)
                (not (bound? new-addr  hp)))
           (consistent-value v type cl (bind new-addr any hp)))
  :hints (("Goal" :in-theory (e/d (consistent-value) ()))))

(defthm consistent-fields-bind-new-object-1
  (implies (and (consistent-fields fields field-decls cl hp)
                (alistp hp)
                (not (bound? new-addr  hp)))
           (consistent-fields fields field-decls cl (bind new-addr any hp)))
  :hints (("Goal" :in-theory (disable bind))))

(defthm consistent-jvp-bind-new-object-1
  (implies (and (consistent-jvp type jvps cl hp)
                (alistp hp)
                (not (bound? new-addr hp)))
           (consistent-jvp type jvps cl (bind new-addr any hp)))
  :hints (("Goal" :in-theory (disable consistent-fields bind))))

(defthm consistent-object-bind-new-object-1
  (implies (and (consistent-object obj hp cl)
                (alistp hp)
                (not (bound? new-addr hp)))
           (consistent-object obj (bind new-addr any hp) cl))
  :hints (("Goal" :in-theory (enable consistent-object))))


(defthm consistent-heap-bind-new-object-1
  (implies (and (consistent-heap1 hp1 hp cl id)
                (alistp hp)
                (not (bound? new-addr hp)))
           (consistent-heap1 hp1 (bind new-addr any hp) cl id)))

;; (i-am-here) ;; Tue Jul 12 16:21:36 2005
;; spent over 20 minutes!! 

(defthm consistent-heap1-consistent-heap1-2
  (implies (and (consistent-heap1 hp1 hp cl id)
                (alistp hp)
                (not (bound? ref hp)))
           (consistent-heap1 hp1 (bind ref obj hp) cl id))
  :hints (("Goal" :in-theory (e/d (bound?)
                                  (consistent-object)))))


(in-theory (disable isArrayType obj-type wff-obj-strong consistent-array-object))

(defthm consistent-heap2-consistent-heap2
  (implies (and (consistent-heap2 hp1 hp cl acl id)
                (wff-obj-strong obj)
                (consistent-array-object obj hp cl acl))
           (consistent-heap2 (bind (+ id (len hp1)) obj hp1) hp cl acl id)))



(defthm consistent-heap2-consistent-heap2-none-array
  (implies (and (consistent-heap2 hp1 hp cl acl id)
                (wff-obj-strong obj)
                (not (isArrayType (obj-type obj))))
           (consistent-heap2 (bind (+ id (len hp1)) obj hp1) hp cl acl id)))




(defthm consistent-heap2-consistent-heap2-specific
  (implies (and (consistent-heap2 hp1 hp cl acl 0)
                (wff-obj-strong obj)
                (consistent-array-object obj hp cl acl))
           (consistent-heap2 (bind (len hp1) obj hp1) hp cl acl 0))
  :hints (("Goal" :use ((:instance consistent-heap2-consistent-heap2
                                   (id 0))))))

(defthm consistent-heap2-consistent-heap2-specific-none-array
  (implies (and (consistent-heap2 hp1 hp cl acl 0)
                (wff-obj-strong obj)
                (not (isArrayType (obj-type obj))))
           (consistent-heap2 (bind (len hp1) obj hp1) hp cl acl 0))
  :hints (("Goal" :use ((:instance consistent-heap2-consistent-heap2-none-array
                                   (id 0))))))


(in-theory (disable consistent-value))

(defthm array-obj-consistent1-bind-new-object-2
  (implies (and (array-obj-consistent1 array type hp cl)
                (alistp hp)
                (not (bound? ref hp)))
           (array-obj-consistent1 array type (bind ref obj hp) cl)))


(defthm consistent-object-bind-new-object-2
  (implies (and (consistent-array-object obj hp cl acl)
                (alistp hp)
                (not (bound? new-addr hp)))
           (consistent-array-object obj (bind new-addr any hp) cl acl))
  :hints (("Goal" :in-theory (enable consistent-array-object))))


(defthm consistent-heap2-consistent-heap2-2
  (implies (and (consistent-heap2 hp1 hp cl acl id)
                (alistp hp)
                (not (bound? ref hp)))
           (consistent-heap2 hp1 (bind ref obj hp) cl acl id))
  :hints (("Goal" :in-theory (e/d (bound?)
                                  (consistent-array-object)))))



(defthm wff-heap-strong-bind-new
  (implies (and (wff-heap-strong hp)
                (wff-obj-strong obj))
           (WFF-HEAP-STRONG (BIND ref obj hp)))
  :hints (("Goal" :in-theory (enable wff-heap))))

(defthm consistent-heap1-implies-alistp
  (implies (consistent-heap1 hp hp cl id)
           (alistp hp))
  :rule-classes :forward-chaining)



(defthm consistent-heap1-consistent-heap1-final
  (implies (and (consistent-heap1 hp hp cl 0)
                (consistent-object obj hp cl))
           (consistent-heap1 (bind (len hp) obj hp)
                             (bind (len hp) obj hp) cl 0))
  :hints (("Goal" :in-theory (disable consistent-object consistent-heap1)
           :use ((:instance consistent-heap1-consistent-heap1-specific
                            (hp1 hp) (hp (bind (len hp) obj hp)))
                 (:instance consistent-heap-bind-new-object-1
                            (hp1 hp) 
                            (new-addr (len hp))
                            (id 0)))
           :do-not-induct t)))
                        
(defthm consistent-object-implies-wff-obj-strong
  (implies (consistent-object obj hp cl)
           (wff-obj-strong obj))
  :hints (("Goal" :in-theory (enable consistent-object)))
  :rule-classes :forward-chaining)


(defthm consistent-heap2-consistent-heap2-final-none-array
  (implies (and (consistent-heap2 hp hp cl acl 0)
                (consistent-heap1 hp cl acl 0)
                (consistent-object obj hp cl)
                (not (isArrayType (obj-type obj))))
           (consistent-heap2 (bind (len hp) obj hp)
                             (bind (len hp) obj hp) cl acl 0))
  :hints (("Goal" :in-theory (disable consistent-object consistent-heap1)
           :use ((:instance consistent-heap2-consistent-heap2-specific-none-array
                            (hp1 hp) (hp (bind (len hp) obj hp)))
                 (:instance consistent-heap2-consistent-heap2-2
                            (hp1 hp) 
                            (ref (len hp))
                            (id 0)))
           :do-not-induct t)))


(defthm consistent-heap2-consistent-heap2-final-array
  (implies (and (consistent-heap1 hp hp cl 0)
                (consistent-heap2 hp hp cl acl 0)
                (consistent-object obj hp cl)
                (consistent-array-object obj hp cl acl))
           (consistent-heap2 (bind (len hp) obj hp)
                             (bind (len hp) obj hp) cl acl 0))
  :hints (("Goal" :in-theory (disable consistent-object consistent-heap1)
           :use ((:instance consistent-heap2-consistent-heap2-specific
                            (hp1 hp) (hp (bind (len hp) obj hp)))
                 (:instance consistent-heap2-consistent-heap2-2
                            (hp1 hp) 
                            (ref (len hp))
                            (id 0)))
           :do-not-induct t)))


(defthm consistent-heap-consistent-heap-none-array
  (implies (and (consistent-heap hp cl acl)
                (consistent-object obj hp cl)
                (not (isArrayType (obj-type obj))))
           (consistent-heap (bind (len hp) obj hp) cl acl))
  :hints (("Goal" :in-theory (e/d (consistent-heap)
                                  (consistent-object))
                                   
           :do-not-induct t)))


(defthm consistent-heap-consistent-heap-new-array
  (implies (and (consistent-heap hp cl acl)
                (consistent-object obj hp cl)
                (consistent-array-object obj hp cl acl))
           (consistent-heap (bind (len hp) obj hp) cl acl))
  :hints (("Goal" :in-theory (e/d (consistent-heap)
                                  (consistent-object))
                                   
           :do-not-induct t)))


(defthm consistent-object-fact-1
  (implies (boot-strap-class-okp s)
           (CONSISTENT-OBJECT '(OBJECT (COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                                                    (ARRAY CHAR))
                                       (SPECIFIC-INFO ARRAY NIL 0)
                                       (("java.lang.Object")))
                              (HEAP S)
                              (INSTANCE-CLASS-TABLE S)))
  :hints (("Goal" :in-theory (enable consistent-object))))

(defthm implies-assoc-equal-array-class-by-name
  (implies (assoc-equal name l)
           (array-class-by-name name l)))

(defthm implies-bound?-equal-array-class-by-name
  (implies (bound? name l)
           (array-class-by-name name l))
  :hints (("Goal" :in-theory (enable bound?))))


;;; (i-am-here) ;; Thu Jun 16 19:50:32 2005

;; (defthm consistent-state-consistent-jvp
;;   (implies (consistent-state s)
;;            (CONSISTENT-JVP "java.lang.Object"
;;                            '(("java.lang.Object"))
;;                            (INSTANCE-CLASS-TABLE S)
;;                            (HEAP S))))

(defthm consistent-array-obj-fact-1
  (implies (boot-strap-class-okp s)
           (CONSISTENT-ARRAY-OBJECT '(OBJECT (COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                                                          (ARRAY CHAR))
                                             (SPECIFIC-INFO ARRAY NIL 0)
                                             (("java.lang.Object")))
                                    (HEAP S)
                                    (INSTANCE-CLASS-TABLE S)
                                    (ARRAY-CLASS-TABLE S)))
  :hints (("Goal" :in-theory (e/d (consistent-array-object 
                                   valid-array-type
                                   array-class-by-name bound?)
                                  (consistent-state
                                   consistent-jvp)))))



(defthm consistent-value-char-code
  (CONSISTENT-VALUE (TAG (CHAR-CODE any)
                         'CHAR)
                    'CHAR
                    cl hp)
  :hints (("Goal" :in-theory (enable consistent-value tag tag-of
                                     wff-tagged-value value-of))))

(defthm consistent-value-fact
  (CONSISTENT-VALUE '(CHAR . 0)
                    'CHAR
                    CL HP)
  :hints (("Goal" :in-theory (enable consistent-value))))


(defthm array-obj-consistent-fact
  (ARRAY-OBJ-CONSISTENT1
   (STR-TO-ARRAY-CHAR-DATA str any len)
   'CHAR
   hp cl)
  :hints (("Goal" :in-theory (e/d (array-obj-consistent1 consistent-value) ()))))
                                  
                                  

(defthm consistent-array-object-fact-2
  (implies (boot-strap-class-okp s)
           (consistent-array-object 
            (LIST*
             'OBJECT
             '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                           (ARRAY CHAR))
             (LIST
              'SPECIFIC-INFO
              'ARRAY
              (CONS (CHAR-CODE (CAR (COERCE CP3 'LIST)))
                    (STR-TO-ARRAY-CHAR-DATA CP3 1 (LEN (COERCE CP3 'LIST))))
              (+ 1
                 (LEN (STR-TO-ARRAY-CHAR-DATA CP3 1 (LEN (COERCE CP3 'LIST))))))
             '((("java.lang.Object"))))
            (heap s) 
            (instance-class-table s)
            (array-class-table s)))
  :hints (("Goal" :in-theory (enable consistent-array-object
                                     consistent-value
                                     valid-array-type
                                     wff-internal-array
                                     wff-obj-strong
                                     common-info
                                     obj-type
                                     array-bound))))


(defthm consistent-object-fact-2
  (implies (boot-strap-class-okp s)
           (consistent-object 
            (LIST*
             'OBJECT
             '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                           (ARRAY CHAR))
             (LIST
              'SPECIFIC-INFO
              'ARRAY
              (CONS (CHAR-CODE (CAR (COERCE CP3 'LIST)))
                    (STR-TO-ARRAY-CHAR-DATA CP3 1 (LEN (COERCE CP3 'LIST))))
              (+ 1
                 (LEN (STR-TO-ARRAY-CHAR-DATA CP3 1 (LEN (COERCE CP3 'LIST))))))
             '((("java.lang.Object"))))
            (heap s) 
            (instance-class-table s)))
  :hints (("Goal" :in-theory (enable consistent-array-object
                                     consistent-object
                                     wff-internal-array
                                     wff-obj-strong
                                     common-info
                                     obj-type
                                     array-bound))))




(defthm consistent-object-fact-3
  (implies (boot-strap-class-okp s)
           (CONSISTENT-OBJECT
            (CONS
             'OBJECT
             (CONS
              '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                            (ARRAY CHAR))
              (CONS
               (CONS
                'SPECIFIC-INFO
                (CONS
                 'ARRAY
                 (CONS
                  (CONS '0
                        (STR-TO-ARRAY-CHAR-DATA (CAR (CDR CP))
                                                '1
                                                (LEN (CAR (CDR CP)))))
                  (CONS (BINARY-+ '1
                                  (LEN (STR-TO-ARRAY-CHAR-DATA (CAR (CDR CP))
                                                               '1
                                                               (LEN (CAR (CDR CP))))))
                        'NIL))))
               '((("java.lang.Object"))))))
            (HEAP S)
            (INSTANCE-CLASS-TABLE S)))
  :hints (("Goal" :in-theory (enable consistent-array-object
                                     consistent-object
                                     wff-internal-array
                                     wff-obj-strong
                                     common-info
                                     obj-type
                                     array-bound))))



(defthm consistent-array-object-fact-3
  (implies (boot-strap-class-okp s)
           (CONSISTENT-array-object
             (CONS
              'OBJECT
              (CONS
               '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                             (ARRAY CHAR))
               (CONS
                (CONS
                 'SPECIFIC-INFO
                 (CONS
                  'ARRAY
                  (CONS
                   (CONS '0
                         (STR-TO-ARRAY-CHAR-DATA (CAR (CDR CP))
                                                 '1
                                                 (LEN (CAR (CDR CP)))))
                   (CONS (BINARY-+ '1
                                   (LEN (STR-TO-ARRAY-CHAR-DATA (CAR (CDR CP))
                                                                '1
                                                                (LEN (CAR (CDR CP))))))
                         'NIL))))
                '((("java.lang.Object"))))))
             (HEAP S)
             (INSTANCE-CLASS-TABLE S)
             (array-class-table s)))
  :hints (("Goal" :in-theory (enable consistent-array-object
                                     consistent-value
                                     wff-internal-array
                                     wff-obj-strong
                                     valid-array-type
                                     common-info
                                     obj-type
                                     array-bound))))


(defthm consistent-state-implies-bootstrap-class-ok-f
  (implies (consistent-state s)
           (boot-strap-class-okp s))
  :hints (("Goal" :in-theory (e/d (consistent-state)
                                  (boot-strap-class-okp))))
  :rule-classes :forward-chaining)


(defthm consistent-state-implies-consistent-heap-f
  (implies (consistent-state s)
           (consistent-heap (heap s) (instance-class-table s)
                            (array-class-table s)))
  :hints (("Goal" :in-theory (enable consistent-state)))
  :rule-classes :forward-chaining)


(in-theory (disable valid-array-type))



(defthm boot-strap-class-okp-implies-valid-array-type
  (implies (boot-strap-class-okp s)
           (valid-array-type '(array char) (instance-class-table s)
                             (array-class-table s)))
  :hints (("Goal" :in-theory (enable valid-array-type))))



(defthm not-isArray-fact
  (NOT
   (ISARRAYTYPE
    (OBJ-TYPE
     (CONS
      'OBJECT
      (CONS '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                          "java.lang.String")
            any)))))
  :hints (("Goal" :in-theory (enable isarraytype obj-type common-info))))



(in-theory (disable consistent-object))

;;; This is a result of not disable build-an-string ....
;;; 
;;; Thu Mar 10 17:11:26 2005. Don't know what I am talking about


(defthm consistent-state-implies-string-class-loaded
  (implies (consistent-state s)
           (isClassTerm (class-by-name "java.lang.String" (instance-class-table
                                                           s))))
  :hints (("Goal" :in-theory (enable class-loaded? consistent-state boot-strap-class-okp)))
  :rule-classes :forward-chaining)


(defthm isClassTerm-implies-consp
  (implies (isClassTerm class-rep)
           (consp class-rep))
  :rule-classes :forward-chaining)


(defthm correctly-loaded-implies-class-exists?
  (implies (correctly-loaded? x cl env-cl)
           (class-exists? x cl))
  :hints (("Goal" :in-theory (e/d (class-exists? correctly-loaded?
                                                 jvm::class-is-loaded?)
                                  (isClassTerm))))
  :rule-classes :forward-chaining)

(defthm consistent-state-fact-java.lang.String-loaded?
  (implies (consistent-state s)
           (class-exists? "java.lang.String" (instance-class-table s)))
  :hints (("Goal" :in-theory (e/d (consistent-state)
                                  (class-exists?)))))
  

(defthm object-fact-1
  (WFF-OBJ-STRONG (LIST 'OBJECT
                        '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                                      "java.lang.String")
                        '(SPECIFIC-INFO STRING)
                        (CONS (LIST* "java.lang.String"
                                     (CONS "value" (LEN (HEAP S)))
                                     '(("offset" . 0) ("count" . 0)))
                              '(("java.lang.Object")))))
  :hints (("Goal" :in-theory (e/d (wff-obj-strong common-info) ()))))



(skip-proofs 
 (defthm consistent-object-fact-4
  (implies (consistent-state s)
           (CONSISTENT-OBJECT
            (CONS 'OBJECT
                   (CONS '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                                       "java.lang.String")
                         (CONS '(SPECIFIC-INFO STRING)
                               (CONS (CONS (CONS '"java.lang.String"
                                                 (CONS (CONS '"value" (LEN (HEAP S)))
                                                       '(("offset" . 0) ("count" . 0))))
                                           '(("java.lang.Object")))
                                     'NIL))))
             (BIND (LEN (HEAP S))
                   '(OBJECT (COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                                         (ARRAY CHAR))
                            (SPECIFIC-INFO ARRAY NIL 0)
                            (("java.lang.Object")))
                   (HEAP S))
             (INSTANCE-CLASS-TABLE S)))
  :hints (("Goal" :in-theory (e/d (consistent-object 
                                   common-info obj-type)
                                  (class-exists? isClassTerm
                                                 fields
                                                 reference-type))))))

;;; a few consistent-object-facts


(skip-proofs 
 (defthm consistent-object-fact-5
   (implies (consistent-state s)
            (CONSISTENT-OBJECT
             (CONS
              'OBJECT
              (CONS
               '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                             "java.lang.String")
               (CONS
                '(SPECIFIC-INFO STRING)
                (CONS
                 (CONS (CONS '"java.lang.String"
                             (CONS (CONS '"value" (LEN (HEAP S)))
                                   (CONS '("offset" . 0)
                                         (CONS (CONS '"count"
                                                     (LEN (COERCE (CAR (CDR CP)) 'LIST)))
                                               'NIL))))
                       '(("java.lang.Object")))
                 'NIL))))
             (BIND
              (LEN (HEAP S))
              (CONS
               'OBJECT
               (CONS
                '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                              (ARRAY CHAR))
                (CONS
                 (CONS
                  'SPECIFIC-INFO
                  (CONS
                   'ARRAY
                   (CONS
                    (CONS (CHAR-CODE (CAR (COERCE (CAR (CDR CP)) 'LIST)))
                          (STR-TO-ARRAY-CHAR-DATA (CAR (CDR CP))
                                                  '1
                                                  (LEN (COERCE (CAR (CDR CP)) 'LIST))))
                    (CONS
                     (BINARY-+
                      '1
                      (LEN (STR-TO-ARRAY-CHAR-DATA (CAR (CDR CP))
                                                   '1
                                                   (LEN (COERCE (CAR (CDR CP)) 'LIST)))))
                     'NIL))))
                 '((("java.lang.Object"))))))
              (HEAP S))
             (INSTANCE-CLASS-TABLE S)))))

(skip-proofs 
 (defthm consistent-object-fact-6
   (implies (consistent-state s)
            (CONSISTENT-OBJECT
             (CONS
              'OBJECT
              (CONS
               '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                             "java.lang.String")
               (CONS
                '(SPECIFIC-INFO STRING)
                (CONS (CONS (CONS '"java.lang.String"
                                  (CONS (CONS '"value" (LEN (HEAP S)))
                                        (CONS '("offset" . 0)
                                              (CONS (CONS '"count" (LEN (CAR (CDR CP))))
                                                    'NIL))))
                            '(("java.lang.Object")))
                      'NIL))))
             (BIND
              (LEN (HEAP S))
              (CONS
               'OBJECT
               (CONS
                '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                              (ARRAY CHAR))
                (CONS
                 (CONS
                  'SPECIFIC-INFO
                  (CONS
                   'ARRAY
                   (CONS
                    (CONS '0
                          (STR-TO-ARRAY-CHAR-DATA (CAR (CDR CP))
                                                  '1
                                                  (LEN (CAR (CDR CP)))))
                    (CONS (BINARY-+ '1
                                    (LEN (STR-TO-ARRAY-CHAR-DATA (CAR (CDR CP))
                                                                 '1
                                                                 (LEN (CAR (CDR CP))))))
                          'NIL))))
                 '((("java.lang.Object"))))))
              (HEAP S))
             (INSTANCE-CLASS-TABLE S)))))



(defthm obj-type-is-array-char
  (equal (OBJ-TYPE
          (CONS
           'OBJECT
           (CONS
            '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                          (ARRAY CHAR))
            any)))
         '(array char))
  :hints (("Goal" :in-theory (enable obj-type common-info))))

(in-theory (disable primitive-type? wff-internal-array array-data))


(defthm wff-internal-array-fact-1
  (wff-internal-array
              (CONS
               'OBJECT
               (CONS
                '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                              (ARRAY CHAR))
                (CONS
                 (CONS
                  'SPECIFIC-INFO
                  (CONS
                   'ARRAY
                   (CONS
                    (CONS any
                          (STR-TO-ARRAY-CHAR-DATA data
                                                  '1
                                                  (LEN data)))
                    (CONS
                     (BINARY-+
                      '1
                      (LEN (STR-TO-ARRAY-CHAR-DATA data
                                                   '1
                                                   (LEN data))))
                     'NIL))))
                 '((("java.lang.Object")))))))
  :hints (("Goal" :in-theory (enable wff-internal-array common-info wff-obj-strong))))


(defthm wff-internal-array-fact-2
  (wff-internal-array
     (LIST*
      'OBJECT
      '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                    (ARRAY CHAR))
      (LIST
           'SPECIFIC-INFO
           'ARRAY
           (CONS (CHAR-CODE (CAR (COERCE CP3 'LIST)))
                 (STR-TO-ARRAY-CHAR-DATA CP3 1 (LEN (COERCE CP3 'LIST))))
           (+ 1
              (LEN (STR-TO-ARRAY-CHAR-DATA CP3 1 (LEN (COERCE CP3 'LIST))))))
      '((("java.lang.Object")))))
  :hints (("Goal" :in-theory (enable wff-internal-array common-info wff-obj-strong))))



;; (defthm consistent-array-object-implies-wff-internal-array
;;   (implies (consistent-array-object obj hp cl acl)
;;            (wff-internal-array obj))
;;   :hints (("Goal" :in-theory (enable consistent-array-object))))


(defthm consistent-heap-array-init-state-load-cp-entry
  (implies (and (consistent-state s) 
                (consistent-heap-array-init-state (heap s)
                                                  (instance-class-table s)
                                                  (array-class-table s) 
                                                  (heap-init-map (aux s))))
           (consistent-heap-array-init-state (heap (mv-nth 1 (load_cp_entry cp s)))
                                             (instance-class-table s)
                                             (array-class-table s)
                                             (heap-init-map (aux s))))
  :hints (("Goal" :in-theory (e/d (load_cp_entry) 
                                  (consistent-object
                                   consistent-state
                                   consistent-heap-array-init-state))
           :restrict ((consistent-heap-implies-not-bound?-len
                       ((cl (instance-class-table s))
                        (acl (array-class-table s))))))))
 

(defthm consistent-heap-load-cp-entry
  (implies (and (consistent-state s)
                (consistent-heap (heap s) cl acl)
                (equal (instance-class-table s) cl)
                (equal (array-class-table s) acl))
           (consistent-heap (heap (mv-nth 1 (load_cp_entry cp s))) cl acl))
  :hints (("Goal" :in-theory (e/d (load_cp_entry)
                                  (consistent-state)))))

(local (in-theory (enable consistent-state)))

(defthm consistent-state-implies-wff-env
  (implies (consistent-state s)
           (wff-env (env s)))
  :rule-classes :forward-chaining)



(defthm consistent-state-implies-wff-array-class-table
  (implies (consistent-state s)
           (wff-array-class-table (array-class-table s)))
  :rule-classes :forward-chaining)



(defthm consistent-state-implies-wff-static-class-table-strong
  (implies (consistent-state s)
           (wff-static-class-table-strong (env-class-table (env s))))
  :rule-classes :forward-chaining)



(defthm consistent-state-implies-wff-methods-instance-class-table
  (implies (consistent-state s)
           (WFF-METHODS-INSTANCE-CLASS-TABLE-STRONG (INSTANCE-CLASS-TABLE S)))
  :rule-classes :forward-chaining)


(defthm heap-init-map-equal-load_cp_entry
  (equal (heap-init-map (aux (mv-nth 1 (load_cp_entry cp s))))
         (heap-init-map (aux s)))
  :hints (("Goal" :in-theory (enable load_cp_entry))))
                        
(defthm consistent-state-implies-wff-instance-class-table-strong
  (IMPLIES (CONSISTENT-STATE S)
           (WFF-INSTANCE-CLASS-TABLE-STRONG (INSTANCE-CLASS-TABLE S)))
  :rule-classes :forward-chaining)

(defthm consistent-state-implies-class-table-loaded-from
  (IMPLIES (CONSISTENT-STATE S)
           (CLASS-TABLE-IS-LOADED-FROM (INSTANCE-CLASS-TABLE S)
                                       (ENV-CLASS-TABLE (ENV S))))
  :rule-classes :forward-chaining)


(defthm valid-ref-bind-new-object
  (implies (and (not (bound? ref hp))
                (valid-refp v hp))
           (valid-refp v (bind ref obj hp)))
  :hints (("Goal" :in-theory (enable valid-refp bound? bind binding wff-REFp))))


(local (in-theory (disable consistent-state)))


(defthm consistent-static-fields-bind-new-object-1
  (implies (and (consistent-static-fields classname field-decls cl hp)
                (alistp hp)
                (not (bound? new-addr  hp)))
           (consistent-static-fields classname field-decls cl (bind new-addr any hp)))
  :hints (("Goal" :in-theory (disable bind))))

;; COPIED for reference
;; (defthm binding-bind-is
;;   (equal (binding x (bind y v hp))
;;          (if (equal x y) 
;;              v
;;            (binding x hp))))

(defthm consistent-constantpool-entry-bind-new-object
  (implies (and (consistent-constantpool-entry cp hp cl)
                (alistp hp)
                (not (bound? ref hp)))
           (consistent-constantpool-entry cp (bind ref obj hp) cl))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (enable bound? bind binding))))


(defthm consistent-constantpool-bind-new-object
  (implies (and (consistent-constantpool cps hp cl)
                (alistp hp)
                (not (bound? ref hp)))
           (consistent-constantpool cps (bind ref obj hp) cl))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable consistent-constantpool-entry))))


(defthm consistent-class-decl-bind-new-object
  (implies (and (consistent-class-decl class-rep cl hp)
                (alistp hp)
                (not (bound? ref hp)))
           (consistent-class-decl class-rep cl 
                                  (bind ref obj hp)))
  :hints (("Goal" :do-not '(generalize))))


(defthm consistent-class-decl-load-cp-entry
  (implies (and (consistent-class-decl decl (instance-class-table s) (heap s))
                (consistent-state s))
           (consistent-class-decl decl (instance-class-table s) (heap (mv-nth 1 (load_cp_entry cp s)))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d (load_cp_entry) (consistent-class-decl))
           :restrict ((consistent-heap-implies-not-bound?-len
                       ((cl (instance-class-table s))
                        (acl (array-class-table s))))))))


(defthm consistent-class-decls-load-cp-entry
  (implies (and (consistent-class-decls decls (instance-class-table s) (heap s))
                (consistent-state s))
           (consistent-class-decls decls (instance-class-table s) (heap (mv-nth 1 (load_cp_entry cp s)))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d () (consistent-class-decl consistent-state)))))



;; (defthm consistent-class-decl-load-cp-entry
;;   (implies (and (consistent-class-decl class-rep cl hp)
;;                 (alistp hp)
;;                 (not (bound? ref hp)))
;;            (consistent-class-decl class-rep cl 
;;                                   (bind ref obj hp)))
;;   :hints (("Goal" :do-not '(generalize))))


;; (defthm consistent-class-decls-bind-new-object
;;   (implies (and (consistent-class-decls decls cl hp)
;;                 (alistp hp)
;;                 (not (bound? ref hp)))
;;            (consistent-class-decls decls  cl 
;;                                   (bind ref obj hp)))
;;   :hints (("Goal" :do-not '(generalize))))

;; Thu Mar 10 17:23:51 2005. Proved earlier?? 

(defthm consistent-value-x-bind-new-object-1
  (implies (and (consistent-value-x v cl hp)
                (alistp hp)
                (not (bound? new-addr  hp)))
           (consistent-value-x  v cl (bind new-addr any hp)))
  :hints (("Goal" :in-theory (e/d (consistent-value-x) ()))))


;; (defthm conistent-value-fact-1
;;   (implies (bound? v hp)
;;            (CONSISTENT-VALUE (CONS 'REF v)
;;                              'REF
;;                              CL (BIND REF OBJ HP)))
;;   :hints (("Goal" :in-theory (enable consistent-value primitive-type?))))

(defthm bound-still-bound-after-bind
  (implies (bound? v hp)
           (bound? v (bind x obj hp)))
  :hints (("Goal" :in-theory (enable bound? bind))))


(defthm consistent-opstack-bind-new-object
  (implies (and (consistent-opstack opstack cl hp)
                (alistp hp)
                (not (bound? ref hp)))
           (consistent-opstack opstack cl (bind ref obj hp)))
  :hints (("Goal" :do-not '(generalize))))

(defthm consistent-locals-bind-new-object
  (implies (and (consistent-locals locals cl hp)
                (alistp hp)
                (not (bound? ref hp)))
           (consistent-locals locals cl (bind ref obj hp)))
  :hints (("Goal" :do-not '(generalize))))


(defthm consistent-frame-bind-new-object
  (implies (and (consistent-frame frame cl hp)
                (alistp hp)
                (not (bound? ref hp)))
           (consistent-frame frame cl (bind ref obj hp)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable WFF-CALL-FRAME 
                               consistent-opstack
                               consistent-locals))))

(defthm consistent-call-stack-bind-new-object
  (implies (and (consistent-call-stack cs cl hp)
                (alistp hp)
                (not (bound? ref hp)))
           (consistent-call-stack cs cl (bind ref obj hp)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable consistent-frame))))


  
(defthm consistent-thread-entry-bind-new-object
  (implies (and (consistent-thread-entry th cl hp)
                (alistp hp)
                (not (bound? ref hp)))
           (consistent-thread-entry th cl (bind ref obj hp)))
  :hints (("Goal" :do-not '(generalize))))


(defthm consistent-thread-entry-load-cp
  (implies (and (consistent-thread-entry th (instance-class-table s) (heap s))
                (consistent-state s))
           (consistent-thread-entry th (instance-class-table s)
                                    (heap (mv-nth 1 (load_cp_entry cp s)))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d (load_cp_entry) (consistent-thread-entry))
           :restrict ((consistent-heap-implies-not-bound?-len
                       ((cl (instance-class-table s))
                        (acl (array-class-table s))))))))

(defthm consistent-thread-entries-load-cp
  (implies (and (consistent-thread-entries tt (instance-class-table s) (heap s))
                (consistent-state s))
           (consistent-thread-entries tt (instance-class-table s)
                                    (heap (mv-nth 1 (load_cp_entry cp s)))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d () (consistent-thread-entry consistent-state)))))


(defthm consistent-state-consistent-thread-entries
  (implies (consistent-state s)
           (consistent-thread-entries (thread-table s) (instance-class-table s)
                                      (heap s)))
  :hints (("Goal" :in-theory (enable consistent-state)))
  :rule-classes :forward-chaining)


;; ======================================================================


(defthm load-cp-entry-perserve-fatal-error
  (implies (not (no-fatal-error? s))
           (not (no-fatal-error? (mv-nth 1 (load_cp_entry cp s)))))
  :hints (("Goal" :in-theory (enable load_cp_entry no-fatal-error?))))

(defthm loader-inv-load-cp
  (implies (loader-inv s)
           (loader-inv (mv-nth 1 (load_cp_entry cp s))))
  :hints (("Goal" :in-theory (enable loader-inv))))

(defthm consistent-state-loader-inv
  (implies (consistent-state s)
           (loader-inv s))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable consistent-state))))

(in-theory (disable boot-strap-class-okp))

(defthm consistent-state-boot-strap-inv
  (implies (consistent-state s)
           (boot-strap-class-okp s))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable consistent-state))))

(defthm array-class-table-load-cp
  (equal (array-class-table (mv-nth 1 (load_cp_entry cp s)))
         (array-class-table s)))

(defthm boot-strap-class-okp-load-cp
  (implies (boot-strap-class-okp s)
           (boot-strap-class-okp (mv-nth 1 (load_cp_entry cp s))))
  :hints (("Goal" :in-theory (e/d (boot-strap-class-okp
                                                 class-loaded? 
                                                 build-a-java-visible-instance-guard)
                                  (isClassTerm
                                   wff-static-class-table-strong
                                   wff-state
                                   build-a-java-visible-instance-data-guard)))))

(local (in-theory (enable BUILD-A-JAVA-VISIBLE-INSTANCE-GUARD)))

(defthm consistent-state-implies-instance-table-env-table
  (IMPLIES (CONSISTENT-STATE S)
           (EQUAL (COLLECT-SUPERCLASS-LIST1 "java.lang.Class"
                                            (INSTANCE-CLASS-TABLE S)
                                            NIL)
                  (JVM::COLLECT-SUPERCLASSNAME1 "java.lang.Class"
                                                (ENV-CLASS-TABLE (ENV S))
                                                NIL)))
  :hints (("Goal" :in-theory (enable consistent-state)))
  :rule-classes :forward-chaining)


(defthm consistent-state-implies-java-lang-Object-exists
  (IMPLIES (CONSISTENT-STATE S)
           (isClassTerm (CLASS-BY-NAME "java.lang.Object"
                                       (INSTANCE-CLASS-TABLE S))))
  :hints (("Goal" :in-theory (enable consistent-state class-loaded?))))

(defthm consistent-state-implies-java-lang-Class-exists
  (IMPLIES (CONSISTENT-STATE S)
           (isClassTerm (CLASS-BY-NAME "java.lang.Class"
                                       (INSTANCE-CLASS-TABLE S))))
  :hints (("Goal" :in-theory (enable consistent-state class-loaded?))))


(defthm array-class-correctly-loaded-types-load-cp
  (implies (JVM::array-class-correctly-loaded? types s)
           (JVM::array-class-correctly-loaded? types (mv-nth 1 (load_cp_entry
                                                                cp s))))
  :hints (("Goal" :in-theory (enable class-loaded? aux-set-trace 
                                     array-base-type
                                     arrayclassloaded?))))


(defthm array-class-table-inv-load-cp
  (IMPLIES  (JVM::ARRAY-CLASS-TABLE-INV-HELPER array-sigs s)
            (JVM::ARRAY-CLASS-TABLE-INV-HELPER  array-sigs (MV-NTH 1 (LOAD_CP_ENTRY CP S)))))



(defthm consistent-state-implies-array-class-table-inv
  (implies (consistent-state s)
           (jvm::array-class-table-inv-helper 
                    (JVM::ALL-ARRAY-SIGS (ARRAY-CLASS-TABLE S))
                    s))
  :hints (("Goal" :in-theory (enable consistent-state))))


(defthm consistent-state-implies-unique-thread-id
  (IMPLIES (CONSISTENT-STATE S)
           (NODUP-SET (COLLECT-THREAD-ID (THREAD-TABLE S))))
  :hints (("Goal" :in-theory (enable consistent-state)))
  :rule-classes :forward-chaining)


(defthm consistent-state-alistp-heap-init-state
  (IMPLIES (CONSISTENT-STATE S)
           (ALISTP (HEAP-INIT-MAP (AUX S))))
  :hints (("Goal" :in-theory (enable consistent-state))))

(defthm consistent-state-consistent-class-hierachy
  (IMPLIES (CONSISTENT-STATE S)
           (CONSISTENT-CLASS-HIERACHY (INSTANCE-CLASS-TABLE S)))
  :hints (("Goal" :in-theory (enable consistent-state))))


(defthm consistent-state-consistent-heap-init-array
  (IMPLIES (CONSISTENT-STATE S)
           (consistent-heap-array-init-state (heap s)
                                             (instance-class-table s)
                                             (array-class-table s)
                                             (heap-init-map (aux s))))
  :hints (("Goal" :in-theory (enable consistent-state))))


(defthm consistent-state-consistent-class-decls
  (IMPLIES (CONSISTENT-STATE S)
           (CONSISTENT-CLASS-DECLS (INSTANCE-CLASS-TABLE S)
                                   (INSTANCE-CLASS-TABLE S)
                                   (heap s)))
  :hints (("Goal" :in-theory (enable consistent-state))))


(defthm consistent-state-current-thread-exists
  (IMPLIES (CONSISTENT-STATE S)
           (THREAD-BY-ID (CURRENT-THREAD S)
                         (THREAD-TABLE S)))
  :hints (("Goal" :in-theory (enable consistent-state))))


(defthm consistent-state-wff-heap-init-map-strong
  (IMPLIES (CONSISTENT-STATE S)
           (WFF-HEAP-INIT-MAP-STRONG (HEAP-INIT-MAP (AUX S))))
  :hints (("Goal" :in-theory (enable consistent-state))))


(defthm consistent-state-wff-heap
  (IMPLIES (CONSISTENT-STATE S)
           (WFF-HEAP (HEAP s)))
  :hints (("Goal" :in-theory (enable consistent-state))))

(defthm consistent-state-env-class-table
  (IMPLIES
   (CONSISTENT-STATE S)
   (EQUAL (BCV::SCL-BCV2JVM (BCV::SCL-JVM2BCV (ENV-CLASS-TABLE (ENV S))))
          (ENV-CLASS-TABLE (ENV S))))
  :hints (("Goal" :in-theory (enable consistent-state))))

(in-theory (disable consistent-heap-array-init-state))


;;; 

(defthm consistent-state-implies-good-scl
  (implies (consistent-state s)
           (bcv::good-scl (bcv::scl-jvm2bcv (env-class-table (env s)))))
  :hints (("Goal" :in-theory (e/d (consistent-state)
                                  (bcv::good-scl))))
  :rule-classes :forward-chaining)


(defthm bcv-good-scl-implies-not-isClassTerm-nil
  (implies (bcv::good-scl scl)
           (NOT
            (BCV::ISCLASSTERM
             (BCV::CLASS-BY-NAME NIL scl))))
  :hints (("Goal" :in-theory (enable bcv::good-scl)))
  :rule-classes :forward-chaining)

(local (in-theory (disable bcv::good-scl)))


;; (i-am-here) ;; after modifying consistent-state
;; we invariablely ends up here
;;
;; Tue Jul 19 13:39:13 2005

(skip-proofs 
 (defthm consistent-state-load_cp_entry_implies
   (IMPLIES (consistent-state s)
            (CONSISTENT-HEAP-INIT-STATE (HEAP (MV-NTH 1 (LOAD_CP_ENTRY CP S)))
                                        (INSTANCE-CLASS-TABLE S)
                                        (HEAP-INIT-MAP (AUX S))))))


;; skip proof it for now.
;; we know that load_cp_entry only creates initialized objects!! 
;; and object created refers only to initialized objects!!




(defthm consistent-state-preserved-by-load-cp-entry
  (implies (consistent-state s)
           (consistent-state-step (mv-nth 1 (load_cp_entry cp s))))
  :hints (("Goal" :in-theory (e/d (build-a-java-visible-instance-guard
                                   class-loaded?)
                                  (isClassTerm)))))


;;(i-am-here) ;;;  Fri Jul 15 21:23:12 2005

; Matt K. mod: Avoid raw Lisp error in tau; see similar disable in
; BCV/bcv-isAssignable-transitive.lisp.
(local (in-theory (disable (:e tau-system))))

(defthm consistent-state-step-implies-consistent-state
  (implies (consistent-state-step s)
           (consistent-state s))
  :hints (("Goal" :in-theory (enable consistent-state)))
  :rule-classes nil)


(defthm consistent-state-implies-consistent-state-1
  (implies (consistent-state s)
           (consistent-state (mv-nth 1 (load_cp_entry cp s))))
  :hints (("Goal" :use ((:instance
                         consistent-state-step-implies-consistent-state
                         (s (mv-nth  1 (load_cp_entry cp s))))))))


(defthm consistent-state-preserved-by-load-cp-entries
  (implies (consistent-state s)
           (consistent-state (mv-nth 1 (load_cp_entries cps s)))))


; -------------------------------------------------------------



(defthm consistent-state-implies
  (IMPLIES (wff-state s)
           (WFF-STATE (MV-NTH 1 (LOAD_CP_ENTRY CP S))))
  :hints (("Goal" :in-theory (enable load_cp_entry))))

(defthm consistent-state-implies-wff-state
  (implies (consistent-state s)
           (wff-state s))
  :hints (("Goal" :in-theory (enable consistent-state)))
  :rule-classes :forward-chaining)

(defthm consistent-state-implies-heap-init-map
  (IMPLIES (CONSISTENT-STATE S)
           (ALISTP (HEAP-INIT-MAP (AUX S))))
  :hints (("Goal" :in-theory (enable consistent-state)))
  :rule-classes :forward-chaining)

(defthm consistent-state-implies-wff-class-table
  (IMPLIES (CONSISTENT-STATE S)
           (WFF-CLASS-TABLE (CLASS-TABLE S)))
  :hints (("Goal" :in-theory (enable consistent-state)))
  :rule-classes :forward-chaining)


(defthm consistent-state-implies-class-hierachy
  (IMPLIES (CONSISTENT-STATE S)
           (CONSISTENT-CLASS-HIERACHY (INSTANCE-CLASS-TABLE S)))
  :hints (("Goal" :in-theory (enable consistent-state)))
  :rule-classes :forward-chaining)


(defthm consistent-state-implies-consistent-heap-array-init
   (IMPLIES (CONSISTENT-STATE S)
            (CONSISTENT-HEAP-ARRAY-INIT-STATE (HEAP s)
                                              (INSTANCE-CLASS-TABLE S)
                                              (ARRAY-CLASS-TABLE S)
                                              (HEAP-INIT-MAP (AUX S))))
   :hints (("Goal" :in-theory (enable consistent-state)))
   :rule-classes :forward-chaining)

(defthm consistent-state-implies-consistent-class-decls
   (IMPLIES (CONSISTENT-STATE S)
            (CONSISTENT-CLASS-DECLS (INSTANCE-CLASS-TABLE S)
                                    (INSTANCE-CLASS-TABLE S)
                                    (HEAP s)))
   :hints (("Goal" :in-theory (enable consistent-state)))
   :rule-classes :forward-chaining)

(defthm consistent-state-implies-thread-by-id
   (IMPLIES (CONSISTENT-STATE S)
            (thread-by-id (current-thread s) (thread-table s)))
   :hints (("Goal" :in-theory (enable consistent-state)))
   :rule-classes :forward-chaining)


(defthm build-a-java-visible-instance-guard-make-state
  (implies (build-a-java-visible-instance-data-guard any s)
           (build-a-java-visible-instance-data-guard any
                                                     (MAKE-STATE (PC S)
                                                                 (CURRENT-THREAD S)
                                                                 (HEAP S)
                                                                 (THREAD-TABLE S)
                                                                 (CLASS-TABLE S)
                                                                 (ENV S)
                                                                 anyerror
                                                                 (AUX S)))))



(defthm boot-strap-class-okp-implies-bound?-array-class
  (implies (boot-strap-class-okp s)
           (bound? '(array char) (array-class-table s)))
  :hints (("Goal" :in-theory (enable boot-strap-class-okp)))
  :rule-classes :forward-chaining)


(defthm boot-strap-class-okp-make-state
  (implies (and (boot-strap-class-okp s)
                (equal (pc s) pc)
                (equal (current-thread s) cid)
                (equal (thread-table s) tt)
                (equal (env s) env))
           (boot-strap-class-okp (MAKE-STATE pc 
                                         cid
                                         (HEAP S)
                                         tt
                                         (CLASS-TABLE S)
                                         env
                                         anyerror
                                         (AUX S))))
  :hints (("Goal" :in-theory (enable boot-strap-class-okp class-loaded?))))


(defthm jvm-array-class-correctly-loaded
  (implies (JVM::array-class-correctly-loaded? types s)
           (JVM::ARRAY-CLASS-CORRECTLY-LOADED? types 
                                               (MAKE-STATE PC CID (HEAP S)
                                                           TT (CLASS-TABLE S)
                                                           ENV ANYERROR (AUX
                                                                         S))))
  :hints (("Goal" :in-theory (enable class-loaded? array-base-type)
           :do-not '(generalize))))

(defthm jvm-array-class-table-inv-helper
  (implies (JVM::array-class-table-inv-helper l s)
           (JVM::array-class-table-inv-helper l (MAKE-STATE pc 
                                                            cid
                                                            (HEAP S)
                                                            tt
                                                            (CLASS-TABLE S)
                                                            env
                                                            anyerror
                                                            (AUX S)))))

(defthm consistent-state-implies-bootstrap-class-ok-b
  (implies (consistent-state s)
           (boot-strap-class-okp s)))


;; (i-am-here) ;; Thu Jul 21 00:38:59 2005 
;; Thu Jul 21 00:39:02 2005

(defthm consistent-state-implies-consistent-heap-init-state
  (implies (CONSISTENT-STATE S)
           (CONSISTENT-HEAP-INIT-STATE (HEAP S)
                                       (INSTANCE-CLASS-TABLE S)
                                       (HEAP-INIT-MAP (AUX S))))
  :hints (("Goal" :in-theory (e/d (consistent-state)
                                  (consistent-heap-init-state)))))

(defthm consistent-state-implies-make-state-general
  (implies (and (consistent-state s)
                (equal (pc s) pc)
                (equal (current-thread s) cid)
                (equal (thread-table s) tt)
                (equal (env s) env)
                (not (null anyerror)))
           (CONSISTENT-STATE-step (MAKE-STATE pc 
                                         cid
                                         (HEAP S)
                                         tt
                                         (CLASS-TABLE S)
                                         env
                                         anyerror
                                         (AUX S))))
  :hints (("Goal" :in-theory (enable consistent-state-step 
                                     class-loaded?
                                     JVM::ARRAY-CLASS-TABLE-INV-HELPER))))

(in-theory (disable consistent-heap-array-init-state)) 

(in-theory (disable instance-class-table-inv array-class-table-inv))
(in-theory (disable wff-methods-instance-class-table-strong
                    wff-static-class-table-strong
                    consistent-class-hierachy))
                    
;;;
;;; Maybe I should just prove 
;;;
;;;    loader-inv-helper 
;;;
;;; implies 
;;;
;;;    consistent-class-hierachy
;;;
;;; Well this is not true!! Tue Nov  2 21:24:24 2004. 


;;; loader-inv-helper + consistent-class-hierachy => next
;;; consistent-class-hierachy 




(defthm all-interfaces-bounded?-all-interface-bounded?
  (implies (and (ALL-INTERFACES-BOUNDED? classnames cl)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (ALL-INTERFACES-BOUNDED? classnames (CONS CLASS-REP cl))))


(defthm super-interface-implies-loaded-implies-consistent-1-class-n
  (implies (and (isClassTerm (class-by-name (super class-rep) cl))
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl)))
                (isClassTerm (class-by-name "java.lang.Object" cl))
                (all-interfaces-bounded? (interfaces class-rep) cl))
           (class-hierachy-consistent1-class-n (classname class-rep)
                                               (cons class-rep cl)))
  :hints (("Goal" :in-theory (e/d ()
                                  (isClassTerm)))))

(defthm class-hierachy-consistent1-aux-add-new-class
  (implies (and (class-hierachy-consistent1-class-n name cl)
                (isClassTerm class-rep)
                (not (equal (classname class-rep) (super (class-by-name
                                                          "java.lang.Object" cl))))
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (class-hierachy-consistent1-class-n name (cons class-rep cl)))
  :hints (("Goal" :in-theory (disable isClassTerm)
           :do-not '(generalize))))


(defthm class-hierachy-consistent1-aux-add-new-class-2
  (implies (and (class-hierachy-consistent1-aux cl1 cl)
                (isClassTerm class-rep)
                (not (equal (classname class-rep) (super (class-by-name
                                                          "java.lang.Object" cl))))
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (class-hierachy-consistent1-aux cl1 (cons class-rep cl)))
  :hints (("Goal" :in-theory (disable isClassTerm
                                      class-hierachy-consistent1-class-n)
           :do-not '(generalize))))

(defthm class-hierachy-consistent1-aux-add-new-class-1
  (implies (and (class-hierachy-consistent1-aux cl1 cl)
                (class-hierachy-consistent1-class-n (classname class-rep) cl))
           (class-hierachy-consistent1-aux (cons class-rep cl1) cl))
  :hints (("Goal" :in-theory (disable class-hierachy-consistent1-class-n))))


(defthm class-hierachy-consistent1-aux-add-new-class-final
  (implies (and (class-hierachy-consistent1 cl)
                (isClassTerm class-rep)
                (ISCLASSTERM (CLASS-BY-NAME (SUPER CLASS-REP) CL))
                (ISCLASSTERM (CLASS-BY-NAME '"java.lang.Object" CL))
                (ALL-INTERFACES-BOUNDED? (INTERFACES CLASS-REP) CL)
                (not (equal (classname class-rep) (super (class-by-name
                                                          "java.lang.Object" cl))))
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (class-hierachy-consistent1 (cons class-rep cl)))
  :hints (("Goal" :in-theory (disable isClassTerm
                                      class-hierachy-consistent1-class-n)
           :do-not '(generalize)
           :do-not-induct t)))


;;; (defun all-super-loaded? (names cl)
;;;   (declare (xargs :guard (wff-instance-class-table cl)))
;;;   (if (not (consp names)) t
;;;     (and (isClassTerm (class-by-name (car names) cl))
;;;          (all-super-loaded? (cdr names) cl))))


;;; (defthm superclass-chain-no-loop-class-n-add-new-class
;;;   (implies (and (superclass-chain-no-loop-class-n n cl seen)
;;;                 (not (isClassTerm (class-by-name (classname class-rep) cl)))
;;;                 (not (equal (classname class-rep) n))
;;;                 (wff-class-rep class-rep)
;;;                 (all-super-loaded? (collect-superclass-list1 n cl seen) cl)
;;;                 (not (mem (classname class-rep) (collect-superclass-list1 n cl seen))))
;;;            (superclass-chain-no-loop-class-n n (cons class-rep cl) seen))
;;;   :hints (("Goal" :in-theory (disable isClassTerm)
;;;            :do-not '(generalize))))

;;;
;;; Mon Nov  1 21:48:14 2004. this is more difficult!! 
;;;
;;; why this is no loop for loading a class? 
;;;
;;; Because all super classes are already loaded!! 
;;; 

(defthm class-loaded-from-class-table-implies-same
  (implies (and (class-table-is-loaded-from cl scl)
                (isClassTerm (class-by-name name cl))
                (class-is-loaded-from-helper class-rep
                                             (mv-nth 1 (class-by-name-s name
                                                                        scl))))
           (equal (super (class-by-name name cl))
                  (super class-rep))))


(defthm class-loaded-from-class-table-implies-same-specific
  (implies (and (class-table-is-loaded-from cl scl)
                (isClassTerm (class-by-name (classname class-rep) cl))
                (class-is-loaded-from-helper class-rep
                                             (mv-nth 1 (class-by-name-s 
                                                        (classname class-rep)
                                                        scl))))
           (equal (super (class-by-name (classname class-rep) cl))
                  (super class-rep))))


(defthm superclass-chain-no-loop-class-n-no-change-if-cons
  (implies (and (superclass-chain-no-loop-class-n n cl seen)
                (isClassTerm (class-by-name name cl))
                (wff-class-rep class-rep)
                (equal (classname class-rep) name)
                (equal (super class-rep) (super (class-by-name
                                                 name cl))))
           (superclass-chain-no-loop-class-n 
              n (cons class-rep cl) seen))
  :hints (("Goal" :in-theory (disable isClassTerm)
           :do-not '(generalize))
          ("Subgoal *1/5" :expand  
           (SUPERCLASS-CHAIN-NO-LOOP-CLASS-N N (CONS CLASS-REP CL) seen))
          ("Subgoal *1/2" :expand  
           (SUPERCLASS-CHAIN-NO-LOOP-CLASS-N N (CONS CLASS-REP CL) seen))))



(defthm superclass-chain-no-loop-class-n-no-change-if-cons-specific
  (implies (and (superclass-chain-no-loop-class-n n cl seen)
                (isClassTerm (class-by-name n cl))
                (wff-class-rep class-rep)
                (equal (classname class-rep) n)
                (equal (super class-rep) (super (class-by-name
                                                 n cl))))
           (superclass-chain-no-loop-class-n 
              n (cons class-rep cl) seen))
  :hints (("Goal" :in-theory (disable isClassTerm)
           :do-not '(generalize))))


(defthm super-s-is-mem-of-collect-superclassnames
  (implies (and (car (class-by-name-s (super-s (mv-nth 1 (class-by-name-s n scl)))
                                      scl))
                (car (class-by-name-s n scl)))
           (mem (super-s (mv-nth 1 (class-by-name-s n scl)))
                (jvm::collect-superclassname1 n scl nil)))
  :hints (("Goal" :expand (jvm::collect-superclassname1 n scl nil)
           :do-not-induct t)))


(defthm super-s-is-mem-of-collect-superclassnames-specific
  (implies (and (car (class-by-name-s (super (class-by-name n cl)) scl))
                (correctly-loaded? n cl scl))
           (mem (super (class-by-name n cl))
                (jvm::collect-superclassname1 n scl nil)))
  :hints (("Goal" :use super-s-is-mem-of-collect-superclassnames
           :in-theory (enable correctly-loaded?)
           :do-not-induct t)))


(defthm correctly-loaded-lemma
   (implies (and (jvm::all-correctly-loaded? l cl scl)
                 (mem x l))
            (correctly-loaded? x cl scl))
   :hints (("Goal" :in-theory (disable correctly-loaded?))))


(defthm mem-collect-superclass-mem-assignable
  (implies (mem x (jvm::collect-superclassname1 n scl nil))
           (mem x (jvm::collect-assignabletoname n scl)))
  :hints (("Goal" :in-theory (enable jvm::collect-assignabletoname))))

(in-theory (disable super-s super))


(defthm loader-inv-helper1-implies-if-super-exists-super-defined
  (implies (and (JVM::loader-inv-helper1 (class-by-name n cl) cl scl)
                (car (class-by-name-s (super (class-by-name n cl)) scl))
                (correctly-loaded? n cl scl))
           (correctly-loaded? (super (class-by-name n cl)) cl scl))
  :hints (("Goal" :do-not-induct t)))

;;; The problematic part is the loader-inv-helper1 is expressed in class-rep
;;; while other are expressed in classname

(defthm loader-inv-helper1-implies-if-super-exists-super-defined-weak
  (implies (and (JVM::loader-inv-helper1 (class-by-name n cl) cl scl)
                (isClassTerm (class-by-name n cl))
                (car (class-by-name-s (super (class-by-name n cl)) scl)))
           (correctly-loaded? (super (class-by-name n cl)) cl scl))
  :hints (("Goal" :do-not-induct t
           :cases ((correctly-loaded? n cl scl)))))


(defthm correctly-loaded?-implies-isClassTerm
  (implies (correctly-loaded? n cl scl)
           (isClassTerm (class-by-name n cl)))
  :hints (("Goal" :in-theory (enable correctly-loaded?)))
  :rule-classes :forward-chaining)

(defthm correctly-loaded?-implies-isClassTerm-b
  (implies (correctly-loaded? n cl scl)
           (isClassTerm (class-by-name n cl)))
  :hints (("Goal" :in-theory (enable correctly-loaded?))))


(defthm loader-inv-helper1-implies-if-super-exists-super-defined-isClassTerm
  (implies (and (JVM::loader-inv-helper1 (class-by-name n cl) cl scl)
                (isClassTerm (class-by-name n cl))
                (car (class-by-name-s (super (class-by-name n cl)) scl)))
           (isClassTerm (class-by-name (super (class-by-name n cl)) cl)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable jvm::loader-inv-helper1 isClassTerm)
           :restrict ((correctly-loaded?-implies-isClassTerm-b
                       ((scl scl)))))))



(in-theory (disable correctly-loaded?-implies-isClassTerm-b
                    correctly-loaded?-implies-isClassTerm
                    loader-inv-helper1-implies-if-super-exists-super-defined-weak
                    correctly-loaded-lemma))



(defthm loader-inv-helper1-implies-all-correctly-loaded
  (implies (and (JVM::loader-inv-helper1 (class-by-name n cl) cl scl)
                (isClassTerm (class-by-name n cl))
                (not (isclassterm (class-by-name (super (class-by-name n cl)) cl))))
           (not (car (class-by-name-s (super (class-by-name n cl)) scl))))
  :hints (("Goal" :in-theory (disable isclassterm jvm::loader-inv-helper1)
           :do-not-induct t)))


(defthm loader-inv-helper-loader-inv-helper
  (implies (and (JVM::loader-inv-helper cl cl scl)
                (isclassterm (class-by-name n cl)))
           (JVM::loader-inv-helper1 (class-by-name n cl) cl scl))
  :hints (("Goal" :in-theory (disable JVM::loader-inv-helper1))))


(defthm loader-inv-helper-loader-inv-helper-f
  (implies (and (JVM::loader-inv-helper cl cl scl)
                (isclassterm (class-by-name n cl)))
           (JVM::loader-inv-helper1 (class-by-name n cl) cl scl))
  :hints (("Goal" :in-theory (disable JVM::loader-inv-helper1)))
  :rule-classes :forward-chaining)


(defthm loader-inv-helper1-implies-all-correctly-loaded-f
  (implies (and (JVM::loader-inv-helper1 (class-by-name n cl) cl scl)
                (isClassTerm (class-by-name n cl))
                (not (isclassterm (class-by-name (super (class-by-name n cl)) cl))))
           (not (car (class-by-name-s (super (class-by-name n cl)) scl))))
  :rule-classes :forward-chaining)


;----------------------------------------------------------------------
;

(defthm superclass-chain-no-loop-class-n-add-new-class-lemma
  (implies (and (superclass-chain-no-loop-class-n n cl seen)
                (isClassTerm (class-by-name n cl))
                (JVM::loader-inv-helper cl cl scl)
                (car (class-by-name-s (classname class-rep) scl))
                (class-table-is-loaded-from cl scl)
                (wff-class-rep class-rep)
                (class-is-loaded-from-helper class-rep
                                             (mv-nth 1 
                                                     (class-by-name-s
                                                      (classname class-rep) scl))))
           (superclass-chain-no-loop-class-n n (cons class-rep cl) seen))
  :hints (("Goal" :in-theory (disable isClassTerm class-is-loaded-from-helper) 
           :do-not '(generalize))
          ("Subgoal *1/6" :expand  
           (SUPERCLASS-CHAIN-NO-LOOP-CLASS-N N (CONS CLASS-REP CL) SEEN))
          ("Subgoal *1/5" :expand 
           (SUPERCLASS-CHAIN-NO-LOOP-CLASS-N N (CONS CLASS-REP CL) seen))
          ("Subgoal *1/5.2" :cases ((equal (super (class-by-name n cl))
                                           (classname class-rep))))))


; The above theorem says: 
;
; add new a class-decl does not introduce loops in the superclass chain!! 
;
;----------------------------------------------------------------------

;; COPIED HERE FOR REFERERENCE
;;
;; >V            (DEFUN
;;                SUPERCLASS-CHAIN-NO-LOOP-CLASS-N
;;                (JVM::N1 JVM::CL JVM::SEEN)
;;                (DECLARE (XARGS :GUARD
;;                                (AND (WFF-INSTANCE-CLASS-TABLE JVM::CL)
;;                                     (TRUE-LISTP JVM::SEEN))
;;                                :MEASURE
;;                                (UNSEEN-CLASSES JVM::CL JVM::SEEN)))
;;                (IF
;;                 (NOT (WFF-INSTANCE-CLASS-TABLE JVM::CL))
;;                 NIL
;;                 (IF
;;                  (NOT (CLASS-EXISTS? JVM::N1 JVM::CL))
;;                  T
;;                  (IF (MEM JVM::N1 JVM::SEEN)
;;                      NIL
;;                      (LET ((JVM::N2 (SUPER (CLASS-BY-NAME JVM::N1 JVM::CL))))
;;                           (SUPERCLASS-CHAIN-NO-LOOP-CLASS-N
;;                                JVM::N2
;;                                JVM::CL (CONS JVM::N1 JVM::SEEN)))))))
;;

(acl2::set-verify-guards-eagerness 0)

(defun superclass-chain-no-loop-induct (n cl sub super)
  (declare (xargs :measure (unseen-classes cl super)))
  (IF
   (NOT (WFF-INSTANCE-CLASS-TABLE CL))
   NIL
   (IF
    (NOT (CLASS-EXISTS? N CL))
    T
    (if (mem n super)
        (list n cl sub super)
      (superclass-chain-no-loop-induct
       (super (class-by-name n cl)) cl 
       (cons n sub)
       (cons n super))))))

(acl2::set-verify-guards-eagerness 2)       
      
(defthm superclass-chain-no-loop-subset
  (implies (and (subset sub super)
                (superclass-chain-no-loop-class-n n cl super))
           (superclass-chain-no-loop-class-n n cl sub))
  :hints (("Goal" :in-theory (disable isClassTerm)
           :induct (superclass-chain-no-loop-induct n cl sub super)
           :do-not '(generalize))))



(defthm subset-cons
  (subset (cons n (cons any seen))
          (cons any (cons n seen))))

(defthm superclass-chain-no-loop-cons-not-name
  (implies (and (superclass-chain-no-loop-class-n n cl seen)
                (not (mem any (jvm::collect-superclass-list1 n cl seen))))
           (superclass-chain-no-loop-class-n n cl (cons any seen)))
  :hints (("Goal" :in-theory (disable isClassTerm)
           :restrict ((superclass-chain-no-loop-subset
                       ((super (cons any (cons n seen))))))
           :do-not '(generalize))
          ("Subgoal *1/6" :expand (SUPERCLASS-CHAIN-NO-LOOP-CLASS-N N CL (CONS ANY SEEN)))))



(defthm not-loaded-implies-not-mem
  (implies (not (isClassTerm (class-by-name name  cl)))
           (not (mem name (jvm::collect-superclass-list1 any cl seen)))))



(defthm superclass-chain-no-loop-class-n-add-new-class-lemma2
  (implies (and (isClassTerm (class-by-name (super class-rep) cl))
                (superclass-chain-no-loop-class-n (super class-rep) cl seen)
                (JVM::loader-inv-helper cl cl scl)
                (not (isClassTerm (class-by-name (classname class-rep) cl)))
                (car (class-by-name-s (classname class-rep) scl))
                (class-table-is-loaded-from cl scl)
                (wff-class-rep class-rep)
                (not (MEM (CLASSNAME CLASS-REP) SEEN))
                (class-is-loaded-from-helper class-rep
                                             (mv-nth 1 
                                                     (class-by-name-s
                                                      (classname class-rep) scl))))
           (superclass-chain-no-loop-class-n (classname class-rep) (cons class-rep cl) seen))
  :hints (("Goal" :in-theory (disable isClassTerm class-is-loaded-from-helper)
           :do-not-induct t
           :expand  (superclass-chain-no-loop-class-n (classname class-rep) (cons class-rep cl) seen))))
          
;------------------------------------------------------------


(acl2::set-verify-guards-eagerness 0)
(defun interfaces-loaded? (n-or-ns cl mode)
  (cond ((equal mode 'JVM::NODE)
         (isClassTerm (class-by-name n-or-ns cl)))
        ((equal mode 'JVM::LIST)
         (if (not (consp n-or-ns)) t
           (and (interfaces-loaded? (car n-or-ns) cl 'JVM::NODE)
                (interfaces-loaded? (cdr n-or-ns) cl 'JVM::LIST))))))
(acl2::set-verify-guards-eagerness 2)
        


(defthm class-loaded-from-class-table-implies-same-interfaces
  (implies (and (class-table-is-loaded-from cl scl)
                (class-is-loaded-from-helper class-rep
                                             (mv-nth 1 (class-by-name-s name
                                                                        scl)))
                (isClassTerm (class-by-name name cl)))
           (equal (interfaces (class-by-name name cl))
                  (interfaces class-rep))))


(defthm class-loaded-from-class-table-implies-same-interfaces-specific
  (implies (and (class-table-is-loaded-from cl scl)
                (isClassTerm (class-by-name (classname class-rep) cl))
                (class-is-loaded-from-helper class-rep
                                             (mv-nth 1 (class-by-name-s 
                                                        (classname class-rep)
                                                        scl))))
           (equal (interfaces (class-by-name (classname class-rep) cl))
                  (interfaces class-rep))))




(defthm loader-inv-helper-loader-inv-helper
   (implies (and (JVM::loader-inv-helper cl cl scl)
                 (isclassterm (class-by-name n cl)))
            (JVM::loader-inv-helper1 (class-by-name n cl) cl scl))
   :hints (("Goal" :in-theory (disable JVM::loader-inv-helper1))))




(defthm class-table-is-loaded-from-interface-loaded
   (implies (and (class-table-is-loaded-from cl scl)
                 (interfaces-loaded? n cl 'JVM::NODE))
            (class-is-loaded-from-helper 
             (class-by-name n cl)
             (mv-nth 1 (class-by-name-s n scl))))
   :hints (("Goal" :in-theory (disable class-is-loaded-from-helper))))



; We are using loader-inv to prove class-hierachy consistency is preserved.
;
; the key points here is that we introduce a class-rep for some class that
; exists in the external class table, and we know loader-inv-helper1, we can
; show adding it does not create loops! 
;



;; COPIED FOR REFERENCE
;;
;; (defthm |Subgoal *1/5-lemma|
;;   (IMPLIES
;;    (AND
;;     (WFF-INSTANCE-CLASS-TABLE CL)
;;     (EQUAL MODE 'JVM::NODE)
;;     (ISCLASSTERM (CLASS-BY-NAME N-OR-NS CL))
;;     (NOT (MEM N-OR-NS SEEN))
;;     (NOT (INTERFACES-LOADED? (INTERFACES (CLASS-BY-NAME N-OR-NS CL))
;;                              CL 'LIST))
;;     (INTERFACES-CHAINS-NO-LOOP-CLASS-N N-OR-NS CL SEEN MODE)
;;     (INTERFACES-LOADED? N-OR-NS CL MODE)
;;     (CLASS-TABLE-IS-LOADED-FROM CL SCL)
;;     (JVM::LOADER-INV-HELPER CL CL SCL)
;;     (CAR (CLASS-BY-NAME-S (CLASSNAME CLASS-REP)
;;                           SCL))
;;     (WFF-CLASS-REP CLASS-REP)
;;     (CLASS-IS-LOADED-FROM-HELPER CLASS-REP
;;                                  (MV-NTH 1
;;                                          (CLASS-BY-NAME-S (CLASSNAME CLASS-REP)
;;                                                           SCL))))
;;    (INTERFACES-CHAINS-NO-LOOP-CLASS-N N-OR-NS (CONS CLASS-REP CL)
;;                                       SEEN MODE)))


(defun all-not-mem (l seen)
  (if (not (consp l)) t
    (and (not (mem (car l) seen))
         (all-not-mem (cdr l) seen))))
  




(defun not-mem (n-or-ns seen mode)
  (cond ((equal mode 'JVM::NODE) 
         (not (mem n-or-ns seen)))
        ((equal mode 'JVM::LIST)
         (all-not-mem n-or-ns seen))))
        

(defthm interfaces-chains-no-loop-class-n-nil
  (implies (NOT (ALL-NOT-MEM l seen))
           (not (INTERFACES-CHAINS-NO-LOOP-CLASS-N l  CL seen 'LIST))))

(defthm wff-class-rep-implies-isClassTerm
  (implies (wff-class-rep class-rep)
           (isclassterm class-rep))
  :hints (("Goal" :in-theory (enable wff-class-rep isclassterm)))
  :rule-classes :forward-chaining)


(local (in-theory (enable class-loaded?)))
(in-theory (disable interfaces))


(defthm interfaces-chains-no-loop-class-n-add-new-class-lemma
  (implies (and (interfaces-chains-no-loop-class-n n-or-ns cl seen mode)
                (class-table-is-loaded-from cl scl)
                (not-mem n-or-ns seen mode)
                (JVM::loader-inv-helper cl cl scl)
                (car (class-by-name-s (classname class-rep) scl))
                (wff-class-rep class-rep)
                (class-is-loaded-from-helper 
                   class-rep
                   (mv-nth 1 (class-by-name-s 
                              (classname class-rep) scl))))
           (interfaces-chains-no-loop-class-n n-or-ns (cons class-rep cl) seen
                                              mode))
  :hints (("Goal" :in-theory (disable isClassTerm
                                      interfaces
                                      JVM::loader-inv-helper1
                                      class-is-loaded-from-helper)
           :restrict
           ((class-loaded-from-class-table-implies-same-interfaces-specific
             ((scl scl))))
           :do-not '(generalize))
          ("Subgoal *1/4" :expand 
           (INTERFACES-CHAINS-NO-LOOP-CLASS-N N-OR-NS (CONS CLASS-REP CL)
                                              SEEN 'JVM::NODE))))


(defthm interfaces-chains-no-loop-class-n-no-change-if-cons
  (implies (and (interfaces-chains-no-loop-class-n n cl seen mode)
                (not-mem n seen mode)
                (isClassTerm (class-by-name name cl))
                (wff-class-rep class-rep)
                (equal (classname class-rep) name)
                (equal (interfaces class-rep) (interfaces (class-by-name
                                                           name cl))))
           (interfaces-chains-no-loop-class-n n (cons class-rep cl) seen mode))
  :hints (("Goal" :in-theory (disable isClassTerm)
           :do-not '(generalize))
          ("Subgoal *1/4" :expand 
               (INTERFACES-CHAINS-NO-LOOP-CLASS-N N (CONS CLASS-REP CL)
                                                  SEEN 'JVM::NODE))))


(defun collect-superinterface-list1 (n-or-ns cl seen mode)
 (declare  (xargs :guard (and (wff-instance-class-table cl)
                              (true-listp seen))
                  :measure (unseen-classes-x n-or-ns  cl seen mode)))
 (let ((n n-or-ns)
       (ns n-or-ns))
   (if (not (wff-instance-class-table cl))  nil
     (cond ((equal mode 'jvm::node)
            (if (not (class-exists? n cl))
                nil
              (if (mem n seen) nil
                (let ((ns (interfaces (class-by-name n cl))))
                  (app (list n)
                       (collect-superinterface-list1 ns cl (cons n seen) 'JVM::LIST))))))
           ((equal mode 'JVM::LIST)
            (if (not (consp ns))
                t
              (app (collect-superinterface-list1 (car ns) cl seen 'JVM::NODE)
                   (collect-superinterface-list1 (cdr ns) cl seen 'JVM::LIST))))))))


(defun interfaces-chains-no-loop-class-n-induct (n-or-ns cl sub super mode)
 (declare  (xargs :guard (and (wff-instance-class-table cl)
                              (true-listp sub)
                              (true-listp super))
                  :measure (unseen-classes-x n-or-ns  cl super mode)))
 (let ((n n-or-ns)
       (ns n-or-ns))
   (if (not (wff-instance-class-table cl))  (list n cl sub super mode)
     (cond ((equal mode 'jvm::node)
            (if (mem n super) nil
              (if (not (class-exists? n cl))
                  nil
                (let ((ns (interfaces (class-by-name n cl))))
                  (interfaces-chains-no-loop-class-n-induct ns cl (cons n sub)
                                                            (cons n super) 'JVM::LIST)))))
           ((equal mode 'JVM::LIST)
            (if (not (consp ns))
                t
              (list (interfaces-chains-no-loop-class-n-induct 
                     (car ns) cl sub super 'JVM::NODE)
                    (interfaces-chains-no-loop-class-n-induct 
                     (cdr ns) cl sub super 'JVM::LIST))))))))

(defthm interfaces-chains-no-loop-subset
  (implies (and (subset sub super)
                (interfaces-chains-no-loop-class-n n cl super mode))
           (interfaces-chains-no-loop-class-n n cl sub mode))
  :hints (("Goal" :in-theory (disable isClassTerm)
           :induct (interfaces-chains-no-loop-class-n-induct 
                    n cl sub super mode)
           :do-not '(generalize))))


(defthm interfaces-chains-no-loop-class-n-cons-not-name
  (implies (and (interfaces-chains-no-loop-class-n n cl seen mode)
                (not (mem any (collect-superinterface-list1 n cl seen mode))))
           (interfaces-chains-no-loop-class-n n cl (cons any seen) mode))
  :hints (("Goal" :in-theory (disable isClassTerm)
           :restrict ((interfaces-chains-no-loop-subset
                       ((super (cons any (cons n seen))))))
           :do-not '(generalize))))


;;; We need to show 
;;;
;;; (NOT (MEM (CLASSNAME CLASS-REP)
;;;           (COLLECT-SUPERINTERFACE-LIST1 (INTERFACES CLASS-REP)
;;;                                         (CONS CLASS-REP CL)
;;;                                         SEEN 'LIST))).

(defthm mem-app-lemma
  (implies (mem a l1)
           (mem a (app l1 l2))))

(defthm mem-app-lemma2
  (implies (mem a l2)
           (mem a (app l1 l2))))

(defthm mem-app-lemma3
  (implies (and (not (mem x b))
                (not (mem x a)))
           (not (mem x (app a b)))))

(defthm not-loaded-implies-not-mem-interface
  (implies (not (isClassTerm (class-by-name name  cl)))
           (not (mem name (collect-superinterface-list1 n cl seen mode))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable isClassTerm))))


(defthm all-not-mem-if-interface-no-loop-class-n
  (implies (interfaces-chains-no-loop-class-n l cl seen 'JVM::LIST)
           (all-not-mem l seen))
  :rule-classes :forward-chaining)

(defthm interfaces-chains-no-loop-class-n-add-new-class-lemma2
  (implies (and (interfaces-chains-no-loop-class-n 
                 (interfaces class-rep) cl seen 'JVM::LIST)
                (JVM::loader-inv-helper cl cl scl)
                (ALL-NOT-MEM (INTERFACES CLASS-REP) (CONS (CLASSNAME CLASS-REP) SEEN))
                (not (isClassTerm (class-by-name (classname class-rep) cl)))
                (car (class-by-name-s (classname class-rep) scl))
                (class-table-is-loaded-from cl scl)
                (wff-class-rep class-rep)
                (not (MEM (CLASSNAME CLASS-REP) SEEN))
                (class-is-loaded-from-helper class-rep
                                             (mv-nth 1 
                                                     (class-by-name-s
                                                      (classname class-rep) scl))))
           (interfaces-chains-no-loop-class-n (classname class-rep) (cons
                                                                     class-rep
                                                                     cl) seen 'JVM::NODE))
  :hints (("Goal" :in-theory (disable isClassTerm 
                                      JVM::loader-inv-helper1
                                      class-is-loaded-from-helper)
           :restrict ((interfaces-chains-no-loop-class-n-add-new-class-lemma
                       ((scl scl))))
           :do-not-induct t)))

; What's the use of this one? Adding a new class introduces no
; loop.



(defthm correctly-loaded-implies-loaded
  (implies (correctly-loaded? any cl scl)       
           (isClassTerm (class-by-name any cl)))
  :hints (("Goal" :in-theory (enable correctly-loaded?))))


(defthm correctly-loaded-implies-loaded-f
  (implies (correctly-loaded? any cl scl)       
           (isClassTerm (class-by-name any cl)))
  :hints (("Goal" :in-theory (enable correctly-loaded?)))
  :rule-classes :forward-chaining)


(defthm mem-all-correctly-loaded-loaded?
  (implies (and  (jvm::all-correctly-loaded? classes cl scl)
                 (mem n classes))
           (correctly-loaded? n cl scl)))


(defthm mem-all-correctly-loaded-loaded?-f  (implies (and  (jvm::all-correctly-loaded? classes cl scl)
                 (mem n classes))
           (correctly-loaded? n cl scl))
  :rule-classes :forward-chaining)

(defthm mem-collect-assignableTo
  (mem n (jvm::collect-assignabletoname n scl))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((jvm::collect-assignabletoname
                                     n scl)))))
  

(defthm jvm-loader-inv-helper-implies-loaded
  (implies (JVM::loader-inv-helper1 class-rep cl scl)
           (correctly-loaded? (classname class-rep) cl scl)))



(defthm jvm-loader-inv-helper-implies-loaded-f
  (implies (JVM::loader-inv-helper1 class-rep cl scl)
           (correctly-loaded? (classname class-rep) cl scl))
  :rule-classes :forward-chaining)




(defthm class-hierachy-consistent2-aux-implies-element
  (implies (and (jvm::loader-inv-helper cl1 cl scl)
                (consp cl1))
           (isClassTerm (class-by-name (classname (car cl1)) cl)))
  :hints (("Goal" :in-theory (e/d (jvm::loader-inv-helper)
                                  (isClassTerm)))))


(defthm class-hierachy-consistent2-aux-add-new-class-lemma
  (implies (and (class-hierachy-consistent2-aux cl1 cl)
                (class-table-is-loaded-from cl scl)
                (JVM::loader-inv-helper cl1 cl scl)
                (JVM::loader-inv-helper cl cl scl)
                (car (class-by-name-s (classname class-rep) scl))
                (wff-class-rep class-rep)
                (class-is-loaded-from-helper 
                   class-rep
                   (mv-nth 1 (class-by-name-s 
                              (classname class-rep) scl))))
           (class-hierachy-consistent2-aux cl1 (cons class-rep cl)))
  :hints (("Goal" :in-theory (e/d (add-instance-class-entry
                                   jvm::loader-inv-helper)
                                  (class-is-loaded-from-helper
                                   superclass-chain-no-loop-class-n
                                   interfaces-chains-no-loop-class-n
                                   isClassTerm)))))

(defthm all-not-mem-cons
  (equal (all-not-mem l (cons x nil))
         (not (mem x l))))

(defthm class-name-interfaces-l
  (implies (and (interfaces-chains-no-loop-class-n l cl nil 'JVM::LIST)
                (mem x l))
           (isClassTerm (class-by-name x cl)))
  :rule-classes :forward-chaining)



(defthm class-hierachy-consistent-aux-loaded-implies-super-no-loop
  (implies (and (class-hierachy-consistent2-aux cl1 cl)
                (isClassTerm (class-by-name name cl1)))
           (superclass-chain-no-loop-class-n name cl nil)))


(defthm class-hierachy-consistent2-aux-add-new-class-step
  (implies (and (class-hierachy-consistent2 cl)
                (class-table-is-loaded-from cl scl)
                (interfaces-chains-no-loop-class-n 
                 (interfaces class-rep) cl nil 'JVM::LIST)
                (JVM::loader-inv-helper cl cl scl)
                (isClassTerm (class-by-name (super class-rep) cl))
                (not (isClassTerm (class-by-name (classname class-rep) cl)))
                (car (class-by-name-s (classname class-rep) scl))
                (wff-class-rep class-rep)
                (class-is-loaded-from-helper 
                   class-rep
                   (mv-nth 1 (class-by-name-s 
                              (classname class-rep) scl))))
           (class-hierachy-consistent2  (add-instance-class-entry 
                                         class-rep cl)))
  :hints (("Goal" :in-theory (e/d (add-instance-class-entry)
                                  (class-is-loaded-from-helper
                                   superclass-chain-no-loop-class-n
                                   interfaces-chains-no-loop-class-n
                                   isClassTerm))
           :restrict ((superclass-chain-no-loop-class-n-add-new-class-lemma2
                       ((scl scl)))
                      (interfaces-chains-no-loop-class-n-add-new-class-lemma2
                       ((scl scl))))
           :cases ((mem (classname class-rep) (interfaces class-rep)))
           :do-not-induct t)))
                

(defthm class-hierachy-consistent-aux-loaded-implies-super-no-loop
  (implies (and (class-hierachy-consistent2-aux cl1 cl)
                (isClassTerm (class-by-name name cl1)))
           (superclass-chain-no-loop-class-n name cl nil)))



(defthm class-hierachy-consistent-aux-loaded-implies-interfaces-no-loop
  (implies (and (class-hierachy-consistent2-aux cl1 cl)
                (isClassTerm (class-by-name n cl1)))
           (interfaces-chains-no-loop-class-n n cl nil 'JVM::NODE)))


(defthm class-hierachy-consistent-aux-loaded-implies-interfaces-no-loop-all
  (implies (and (class-hierachy-consistent2-aux cl1 cl)
                (wff-instance-class-table cl)
                (interfaces-loaded? l cl1 'JVM::LIST))
           (interfaces-chains-no-loop-class-n l cl nil 'JVM::LIST)))

; Add a new class will preserve the consistency of class
; hierachy. We rely on the loader-inv properties that we proved
; in jvm-dynamic-class-loading-property.lisp.

(defthm class-hierachy-consistent2-add-new-class
  (implies (and (class-hierachy-consistent2 cl)
                (wff-instance-class-table cl)
                (class-table-is-loaded-from cl scl)
                (JVM::loader-inv-helper cl cl scl)
                (interfaces-loaded? (interfaces class-rep) cl 'JVM::LIST)
                (isClassTerm (class-by-name (super class-rep) cl))
                (not (isClassTerm (class-by-name (classname class-rep) cl)))
                (car (class-by-name-s (classname class-rep) scl))
                (wff-class-rep class-rep)
                (class-is-loaded-from-helper 
                   class-rep
                   (mv-nth 1 (class-by-name-s 
                              (classname class-rep) scl))))
           (class-hierachy-consistent2  (cons class-rep cl)))
  :hints (("Goal" :in-theory (e/d (add-instance-class-entry
                                   class-hierachy-consistent2)
                                  (class-is-loaded-from-helper
                                   superclass-chain-no-loop-class-n
                                   interfaces-chains-no-loop-class-n
                                   isClassTerm))
           :use class-hierachy-consistent2-aux-add-new-class-step
           :do-not-induct t)))


;----------------------------------------------------------------------
;  
;   Goal is to prove the following.
;
;   class-hierachy-consistent1 asserts that if a class is loaded,
;   its direct super class and direct super interfaces are also loaded.
;   
;   class-hierachy-consistent2 asserts that there is no loops in
;   the super class chains and super interface chains.
;  
;   We want to prove that adding a new class definition, these
;   two properties still holds on the new class table. 
;

;; (defthm class-hierachy-consistent1-aux-add-new-class-final
;;   (implies (and (class-hierachy-consistent1 cl)
;;                 (isClassTerm class-rep)
;;                 (ISCLASSTERM (CLASS-BY-NAME (SUPER CLASS-REP) CL))
;;                 (ISCLASSTERM (CLASS-BY-NAME '"java.lang.Object" CL))
;;                 (ALL-INTERFACES-BOUNDED? (INTERFACES CLASS-REP) CL)
;;                 (not (equal (classname class-rep) (super (class-by-name
;;                                                           "java.lang.Object" cl))))
;;                 (not (isClassTerm (class-by-name (classname class-rep) cl))))
;;            (class-hierachy-consistent1 (cons class-rep cl)))
;;   :hints (("Goal" :in-theory (disable isClassTerm
;;                                       class-hierachy-consistent1-class-n)
;;            :do-not '(generalize)
;;            :do-not-induct t)))


;; (defthm class-hierachy-consistent1-aux-add-new-class-final-x
;;   (implies (and (class-hierachy-consistent1 cl)
;;                 (isClassTerm class-rep)
;;                 (ISCLASSTERM (CLASS-BY-NAME (SUPER CLASS-REP) CL))
;;                 (ISCLASSTERM (CLASS-BY-NAME '"java.lang.Object" CL))
;;                 (ALL-INTERFACES-BOUNDED? (INTERFACES CLASS-REP) CL)
;;                 (not (equal (classname class-rep) (super (class-by-name
;;                                                           "java.lang.Object" cl)))))
;;                 ;;(not (isClassTerm (class-by-name (classname class-rep) cl))))
;;            (class-hierachy-consistent1 (cons class-rep cl)))
;;   :hints (("Goal" :in-theory (disable isClassTerm
;;                                       class-hierachy-consistent1-class-n)
;;            :do-not '(generalize)
;;            :cases ((isClassTerm (class-by-name (classname class-rep) cl)))
;;            :do-not-induct t)))



(defthm consistent-state-consistent-hierachy1
  (implies (consistent-state s)
           (class-hierachy-consistent1 (instance-class-table s)))
  :hints (("Goal" :in-theory (enable consistent-state
                                     consistent-class-hierachy))))

(defthm consistent-state-consistent-hierachy2
  (implies (consistent-state s)
           (class-hierachy-consistent2  (instance-class-table s)))
  :hints (("Goal" :in-theory (enable consistent-state consistent-class-hierachy))))

  
(defthm wff-class-rep-implies-isClassTerm
  (implies (wff-class-rep class-rep)
           (isClassTerm class-rep))
  :hints (("Goal" :in-theory (enable wff-class-rep)))
  :rule-classes :forward-chaining)


(defthm consistent-and-found-implies-not-equal-empty-string
  (implies (boot-strap-class-okp s)
           (not (car (class-by-name-s "" (env-class-table (env s))))))
  :hints (("Goal" :in-theory (enable boot-strap-class-okp)))
  :rule-classes :forward-chaining)



(defthm consistent-state-not-bound
  (implies (consistent-state s)
           (not (car (class-by-name-s "" (env-class-table (env s))))))
  :hints (("Goal" :in-theory (enable consistent-state 
                                     boot-strap-class-okp))))

(defthm consistent-state-not-bound-f
  (implies (consistent-state s)
           (not (car (class-by-name-s "" (env-class-table (env s))))))
  :rule-classes :forward-chaining)


(defthm consistent-state-super-java-lang-object
  (implies (consistent-state s)
           (equal (super (class-by-name "java.lang.Object"
                                        (instance-class-table s)))
                  ""))
  :hints (("Goal" :in-theory (enable consistent-state 
                                     boot-strap-class-okp))))
                      

(defthm all-interface-bounded?-implies-interface-loaded
  (implies (all-interfaces-bounded? l cl)
           (interfaces-loaded? l cl 'JVM::LIST)))


(defthm consistent-hierachy-perserved-lemma
  (implies (and (consistent-state s)
                (no-fatal-error? s)
                (wff-class-rep class-rep)
                (class-loaded? (super class-rep) s)
                (all-interfaces-bounded? (interfaces class-rep) 
                                         (instance-class-table s))
                (not (equal (classname class-rep) ""))
                (not (isClassTerm (class-by-name (classname class-rep) 
                                                 (instance-class-table s))))
                (car (class-by-name-s (classname class-rep) 
                                      (env-class-table (env s))))
                (class-is-loaded-from-helper
                 class-rep
                 (mv-nth '1
                         (class-by-name-s (classname class-rep)
                                          (env-class-table (env s))))))
           (consistent-class-hierachy (add-instance-class-entry
                                       class-rep (instance-class-table s))))
  :hints (("Goal" :in-theory (e/d (consistent-class-hierachy
                                   class-loaded?
                                   add-instance-class-entry)
                                  (isClassTerm
                                   class-is-loaded-from-helper
                                   class-hierachy-consistent2
                                   class-hierachy-consistent1))
           :restrict ((class-hierachy-consistent2-add-new-class
                       ((scl (env-class-table (env s)))))))))

(in-theory (disable consistent-class-table instance-class-table-inv boot-strap-class-okp))


(in-theory (enable wff-methods-instance-class-table-strong))

;; (defthm consistent-hierachy-perserved-lemma
;;   (implies (and (consistent-state s)
;;                 (no-fatal-error? s)
;;                 (wff-class-rep class-rep)
;;                 (class-loaded? (super class-rep) s)
;;                 (all-interfaces-bounded? (interfaces class-rep) 
;;                                          (instance-class-table s))
;;                 (not (equal (classname class-rep) ""))
;;                 (not (isClassTerm (class-by-name (classname class-rep) 
;;                                                  (instance-class-table s))))
;;                 (car (class-by-name-s (classname class-rep) 
;;                                       (env-class-table (env s))))
;;                 (class-is-loaded-from-helper
;;                  class-rep
;;                  (mv-nth '1
;;                          (class-by-name-s (classname class-rep)
;;                                           (env-class-table (env s))))))
;;            (consistent-class-hierachy (add-instance-class-entry
;;                                        class-rep (instance-class-table s))))
;;   :hints (("Goal" :in-theory (e/d (consistent-class-hierachy
;;                                    class-loaded?
;;                                    add-instance-class-entry)
;;                                   (isClassTerm
;;                                    class-is-loaded-from-helper
;;                                    class-hierachy-consistent2
;;                                    class-hierachy-consistent1))
;;            :restrict ((class-hierachy-consistent2-add-new-class
;;                        ((scl (env-class-table (env s)))))))))

;
; consistent-hierachy-perserved is step towards proving that when
; load_class2's guard is met, load_class2 will preserve the class
; hierachy.

(defthm consistent-hierachy-perserved
  (implies (and (consistent-state s)
                (no-fatal-error? s)
                (wff-class-rep class-rep)
                (class-loaded? (super class-rep) s)
                (all-interfaces-bounded? (interfaces class-rep) 
                                         (instance-class-table s))
                (not (equal (classname class-rep) ""))
                (not (isClassTerm (class-by-name (classname class-rep) 
                                                 (instance-class-table s))))
                (car (class-by-name-s (classname class-rep) 
                                      (env-class-table (env s))))
                (class-is-loaded-from-helper
                 class-rep
                 (mv-nth '1
                         (class-by-name-s (classname class-rep)
                                          (env-class-table (env s))))))
           (consistent-class-hierachy (cons 
                                       class-rep (instance-class-table s))))
  :hints (("Goal" :in-theory (e/d (consistent-class-hierachy
                                   class-loaded?
                                   add-instance-class-entry)
                                  (isClassTerm
                                   class-is-loaded-from-helper
                                   class-hierachy-consistent2
                                   class-hierachy-consistent1))
           :restrict ((class-hierachy-consistent2-add-new-class
                       ((scl (env-class-table (env s)))))))))


(defthm consistent-and-found-implies-not-equal-empty-string-l
  (implies (and (boot-strap-class-okp s)
                (car (class-by-name-s any (env-class-table (env s)))))
           (not (equal any "")))
  :hints (("Goal" :in-theory (enable boot-strap-class-okp)))
  :rule-classes :forward-chaining)


;; (i-am-here) ;;









(defthm class-is-loaded-from-helper-make-runtime-class-rep
  (implies (and (constantpool-loaded-from cps (constantpool-s jvm::class-desc))
                (equal (classname-s jvm::class-desc) any))
           (class-is-loaded-from-helper
            (MAKE-RUNTIME-CLASS-REP
             any
             (SUPER-S JVM::CLASS-DESC)
             cps
             (RUNTIME-INSTANCE-FIELDS-REP1
              (FIELDS-S JVM::CLASS-DESC)
              any)
             (RUNTIME-METHODS-REP1 (METHODS-S JVM::CLASS-DESC)
                                   any)
             (INTERFACES-S JVM::CLASS-DESC)
             (RUNTIME-STATIC-FIELDS-REP1
              (FIELDS-S JVM::CLASS-DESC)
              any  cps)
             JVM::*CLASS_LOADED*
             (ACCESSFLAGS-S JVM::CLASS-DESC)
             -1 JVM::NEW-ADDRESS)  JVM::CLASS-DESC))
  :hints (("Goal" :in-theory (enable super-s super interfaces-s interfaces
                                     classname classname-s))))
            

(defthm constant-pool-is-loaded-from
  (constantpool-loaded-from
   (car (load_cp_entries static-cps s))
   static-cps))


(defthm isJavaSubclass1-cons-new-class
  (implies (and (isJavaSubclassOf1 new1 new2 cl seen)
                (consistent-class-hierachy (cons class-rep cl))
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (isJavaSubclassOf1 new1 new2 (cons class-rep cl) seen))
  :hints (("Goal" :in-theory (e/d (isJavaSubClassOf1) (isClassTerm))
           :do-not '(generalize))
          ("Subgoal *1/4" :expand 
           (ISJAVASUBCLASSOF1 NEW1 NEW2 (CONS CLASS-REP CL) SEEN))))
;;;
;;;  There is some usage patterns. In the following theorem we
;;;  use isClassTerm ..., in later part of the proof, we use
;;;  (class-loaded?  ....) 
;;;

(defthm isJavaClassAssignmentcompatible-cons-new-class
  (implies (and (isJavaClassAssignmentcompatible new1 new2 cl)
                (isClassTerm (class-by-name new2 cl)) 
                (isClassTerm (class-by-name new1 cl))
                ;;; we need these assertions!! 
                ;;; Mon Nov  8 14:34:07 2004
                ;;; 
                ;;; Our pick of isClassTerm and class-loaded is
                ;;; quite arbitrary. It is not very good. 
                ;;;
                (consistent-class-hierachy (cons class-rep cl))
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (isJavaClassAssignmentcompatible new1 new2 (cons class-rep cl)))
  :hints (("Goal" :in-theory (e/d (isJavaClassAssignmentcompatible)
                                  (isClassTerm))
           :do-not-induct t)))


(defthm isJavaAssignmentcompatible-cons-new-class
  (implies (and (isJavaAssignmentcompatible new1 new2 cl)
                (isClassTerm class-rep)
                (consistent-class-hierachy (cons class-rep cl))
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (isJavaAssignmentcompatible new1 new2 (cons class-rep cl)))
  :hints (("Goal" :in-theory (e/d () (isJavaClassAssignmentcompatible isClassTerm)))))



(defthm assignmentcompatible-cons-new-class
  (implies (and (assignmentcompatible new1 new2 cl)
                (isClassTerm class-rep)
                (consistent-class-hierachy (cons class-rep cl))
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (assignmentcompatible new1 new2 (cons class-rep cl)))
  :hints (("Goal" :in-theory (e/d (assignmentcompatible) (isClassTerm
                                                          array-type-s
                                                          reference-type-s
                                                          primitive-type?
                                                          isJavaAssignmentcompatible))
           :do-not '(generalize))))

(defthm consistent-value-cons-new-class
  (implies (and (consistent-value v type cl hp)
                (consistent-class-hierachy (cons class-rep cl))
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-value v type (cons class-rep cl) hp))
  :hints (("Goal" :in-theory (enable consistent-value))))


(defthm consistent-field-cons-new-class
  (implies (and (consistent-field field field-decl cl hp)
                (consistent-class-hierachy (cons class-rep cl))
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-field field field-decl (cons class-rep cl) hp)))


(defthm consistent-fields-cons-new-class
  (implies (and (consistent-fields fields field-decls cl hp)
                (consistent-class-hierachy (cons class-rep cl))
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-fields fields field-decls (cons class-rep cl) hp)))

(defthm consistent-immediate-instance-cons-new-class
  (implies (and (consistent-immedidate-instance obj-type fields cl hp)
                (consistent-class-hierachy (cons class-rep cl))
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-immedidate-instance obj-type fields (cons class-rep cl) hp)))


(defthm consistent-jvp-cons-new-class
  (implies (and (consistent-jvp obj-type jvp cl hp)
                (consistent-class-hierachy (cons class-rep cl))
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-jvp obj-type jvp (cons class-rep cl) hp)))


(defthm consistent-object-cons-new-class
  (implies (and (consistent-object obj hp cl)
                (consistent-class-hierachy (cons class-rep cl))
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-object obj hp (cons class-rep cl)))
  :hints (("Goal" :in-theory (e/d (consistent-object) 
                                  (isClassTerm)))))


(defthm consistent-heap1-implies-consistent-heap-add-new-class
  (implies (and (consistent-heap1 hp1 hp cl id)
                (consistent-class-hierachy (cons class-rep cl))
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-heap1 hp1 hp (cons class-rep cl) id))
  :hints (("Goal" :in-theory (disable isClassTerm))))



(defthm array-consistent-cons-new-class
  (implies (and (array-obj-consistent1 array basetype hp cl)
                (consistent-class-hierachy (cons class-rep cl))
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (array-obj-consistent1 array basetype hp (cons class-rep cl))))


(defthm consistent-array-object-cons-new-class
  (implies (and (consistent-array-object obj hp cl acl)
                (consistent-class-hierachy (cons class-rep cl))
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-array-object obj hp (cons class-rep cl) acl))
  :hints (("Goal" :in-theory (e/d (consistent-array-object)
                                  (isClassTerm)))))




(defthm consistent-heap2-implies-consistent-heap-add-new-class
  (implies (and (consistent-heap2 hp1 hp cl acl id)
                (consistent-class-hierachy (cons class-rep cl))
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-heap2 hp1 hp (cons class-rep cl) acl id))
  :hints (("Goal" :in-theory (disable isClassTerm))))


(defthm consistent-heap-implies-consistent-heap-add-new-class
  (implies (and (consistent-heap hp cl acl)
                (consistent-class-hierachy (cons class-rep cl))
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-heap hp (cons class-rep cl) acl))
  :hints (("Goal" :in-theory (e/d (consistent-heap) (isClassTerm)))))
  

(defthm consistent-state-consistent-heap
  (implies (and (consistent-state s)
                (equal (instance-class-table s) cl)
                (equal (array-class-table s) acl))
           (consistent-heap 
            (heap s) cl acl)))

;;; we proved the load_cp_entries preserves the consistency!! 
;;; 
;;; Now we need to prove load_cp_entry preserves consistency! 
;;; in some sense, this is reversed. 
;;; Go up then down! Thu Nov  4 11:19:38 2004


(defthm load_cp_entry_no_change_instance_class_table
  (equal (instance-class-table (mv-nth 1 (load_cp_entry cp s)))
         (instance-class-table s))
  :hints (("Goal" :in-theory (enable load_cp_entry))))

(defthm load_cp_entries_no_change_instance_class_table
  (equal (instance-class-table (mv-nth 1 (load_cp_entries cp s)))
         (instance-class-table s)))

(defthm load_cp_entry_no_change_array_class_table
  (equal (array-class-table (mv-nth 1 (load_cp_entry cp s)))
         (array-class-table s))
  :hints (("Goal" :in-theory (enable load_cp_entry))))

(defthm load_cp_entries_no_change_array_class_table
  (equal (array-class-table (mv-nth 1 (load_cp_entries cp s)))
         (array-class-table s)))

;;; (i-am-here) ;; Mon Feb 28 20:51:42 2005

;;; TO FIX LATER
(skip-proofs 
 (defthm consistent-object-fact-7
   (implies (and (consistent-state s)
                 (equal (instance-class-table s) cl))
            (consistent-object
              (CONS 'OBJECT
                    (CONS '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                                        "java.lang.Class")
                          (CONS (CONS 'SPECIFIC-INFO
                                      (CONS 'INSTANCE_CLASS (CONS ANY 'NIL)))
                                '((("java.lang.Class")
                                   ("java.lang.Object"))))))
              (heap s)
              cl))))
    
(defthm not-array-type-fact
  (NOT
   (ISARRAYTYPE
    (OBJ-TYPE (CONS 'OBJECT
                    (CONS '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                                        "java.lang.Class")
                          any)))))
  :hints (("Goal" :in-theory (enable isarraytype common-info obj-type))))



(defthm consistent-state-consistent-heap-array-init-state
  (implies (and (consistent-state s)
                (equal (instance-class-table s) cl)
                (equal (array-class-table s) acl)
                (equal (heap-init-map (aux s)) hp-init))
           (consistent-heap-array-init-state
            (heap s) cl acl hp-init)))



(defthm consistent-state-implies-not-bound-len-heap
  (implies (consistent-state s)
           (not (bound? (len (heap s)) (heap s)))))

(defthm alist-get-heap-init-map
   (implies (consistent-state s)
            (alistp (acl2::g 'heap-init-map (nth 8 s))))
   :hints (("Goal" :use consistent-state-alistp-heap-init-state
            :in-theory (enable heap-init-map aux))))


(skip-proofs 
 (defthm alist-get-trace
   (implies (consistent-state s)
            (alistp (acl2::g 'trace (nth 8 s))))))


(skip-proofs 
 (defthm true-list-get-trace
   (implies (consistent-state s)
            (true-listp (acl2::g 'trace (nth 8 s))))))


(defthm wff-class-fields-runtime-fields
  (wff-class-fields
   (runtime-instance-fields-rep1 somefields any)))

(defthm wff-static-fields-runtime-fields
  (wff-static-fields-x
   (runtime-static-fields-rep1 somefields any anycps)))

(defthm wff-static-fields-strong-runtime-fields
  (wff-static-fields-strong
   (runtime-static-fields-rep1 somefields any anycps)))

(defthm wff-methods-runtime-methods
  (implies (JVM::RUNTIME-METHOD-REP-GUARDS somemethods)
           (jvm::wff-class-method-decls
            (runtime-methods-rep1 somemethods any)))
  :hints (("Goal" :in-theory (enable wff-method-decl))))
  

(defthm wff-instance-class-rep-strong
  (implies (and (wff-class-rep-static-strong static-class-desc)
                (wff-constant-pool cps)
                (true-listp cps)
                (integerp class-ref))
           (wff-class-rep-strong
            (make-runtime-class-rep
             any
             super
             cps 
             (RUNTIME-INSTANCE-FIELDS-REP1 somefields ANY)
             (RUNTIME-METHODS-REP1 (methods-s static-class-desc) any)
             (INTERFACES-S static-class-desc)
             (RUNTIME-STATIC-FIELDS-REP1 somestaticfields any cps)
             status 
             (ACCESSFLAGS-S static-class-desc)
             -1
             class-ref)))
  :hints (("Goal" :in-theory (enable interfaces-s accessflags-s
                                     wff-class-rep wff-class-rep-static)
           :do-not '(generalize))))



;;; COPIED FOR REFERENCE
;;; (defthm consistent-hierachy-perserved
;;;   (implies (and (consistent-state s)
;;;                 (no-fatal-error? s)
;;;                 (wff-class-rep class-rep)
;;;                 (class-loaded? (super class-rep) s)
;;;                 (all-interfaces-bounded? (interfaces class-rep) 
;;;                                          (instance-class-table s))
;;;                 (not (equal (classname class-rep) ""))
;;;                 (not (isClassTerm (class-by-name (classname class-rep) 
;;;                                                  (instance-class-table s))))
;;;                 (car (class-by-name-s (classname class-rep) 
;;;                                       (env-class-table (env s))))
;;;                 (class-is-loaded-from-helper
;;;                  class-rep
;;;                  (mv-nth '1
;;;                          (class-by-name-s (classname class-rep)
;;;                                           (env-class-table (env s))))))
;;;            (consistent-class-hierachy (cons 
;;;                                        class-rep (instance-class-table s))))
;;;   :hints (("Goal" :in-theory (e/d (consistent-class-hierachy
;;;                                    class-loaded?
;;;                                    add-instance-class-entry)
;;;                                   (isClassTerm
;;;                                    class-is-loaded-from-helper
;;;                                    class-hierachy-consistent2
;;;                                    class-hierachy-consistent1))
;;;            :restrict ((class-hierachy-consistent2-add-new-class
;;;                        ((scl (env-class-table (env s)))))))))


(defthm wff-class-static-rep-implies-stringp-if-found-lemma
  (implies (wff-class-rep-static static-rep)
           (stringp (classname-s static-rep)))
  :hints (("Goal" :in-theory (enable wff-class-rep-static classname-s)))
  :rule-classes :forward-chaining)


(defthm consistent-state-implies-stringp-if-found-lemma
  (implies (and (wff-static-class-table-strong scl)
                (car (class-by-name-s name scl)))
           (stringp name))
  :hints (("Goal" :in-theory (enable wff-static-class-table-strong)))
  :rule-classes :forward-chaining)



(defthm consistent-state-implies-stringp-if-found
  (implies (and (consistent-state s)
                (car (class-by-name-s name (env-class-table (env s)))))
           (stringp name))
  :rule-classes :forward-chaining)



(defthm consistent-method-decl-if-wff-method-decl
  (implies (JVM::RUNTIME-METHOD-REP-GUARD method-s)
           (consistent-method-decl (runtime-method-rep
                                    method-s any)))
  :hints (("Goal" :in-theory (enable consistent-method-decl 
                                     method-code
                                     wff-method-decl
                                     code-max-local
                                     wff-code
                                     code-max-stack
                                     consistent-code
                                     method-accessflags))))

(defthm consistent-method-decls-if-wff-method-decls
  (implies (JVM::RUNTIME-METHOD-REP-GUARDS methods-s)
           (consistent-method-decls (runtime-methods-rep1 
                                     methods-s any)))
  :hints (("Goal" :in-theory (disable runtime-method-rep))))

  

(defthm wff-static-class-rep-strong-implies-runtime-method-guards
  (implies (wff-class-rep-static-strong  static-class-rep)
           (JVM::RUNTIME-METHOD-REP-GUARDS (methods-s static-class-rep))))


(defthm wff-static-class-rep-strong-implies-runtime-method-guards-f
  (implies (wff-class-rep-static-strong  static-class-rep)
           (JVM::RUNTIME-METHOD-REP-GUARDS (methods-s static-class-rep)))
  :rule-classes :forward-chaining)


(defthm wff-static-class-table-strong-implies-bounded?-class-strong-f
  (implies (and (car (class-by-name-s name scl))
                (wff-static-class-table-strong scl))
           (wff-class-rep-static-strong (mv-nth 1 (class-by-name-s name scl))))
  :rule-classes :forward-chaining)



(defthm wff-static-class-table-strong-implies-bounded?-class-strong-b
  (implies (and (car (class-by-name-s name scl))
                (wff-static-class-table-strong scl))
           (wff-class-rep-static-strong (mv-nth 1 (class-by-name-s name scl)))))



(defthm wff-class-rep-static-strong-implie-wff-static-fields-strong-f
  (implies (wff-class-rep-static-strong class-rep)
           (jvm::wff-fields-s (fields-s class-rep)))
  :rule-classes :forward-chaining)


(defthm consistent-static-field-add-new-class
  (implies (and (consistent-static-field any field cl hp)
                (consistent-class-hierachy (cons class-rep cl))
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-static-field any field (cons class-rep cl) hp))
  :hints (("Goal" :in-theory (e/d () (isClassTerm)))))


(defthm consistent-static-fields-add-new-class
  (implies (and (consistent-static-fields any fields cl hp)
                (consistent-class-hierachy (cons class-rep cl))
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-static-fields any fields (cons class-rep cl) hp))
  :hints (("Goal" :in-theory (e/d () (isClassTerm consistent-static-field)))))


(defthm consistent-constantpool-entry-add-new-class
  (implies (and (consistent-constantpool-entry cp hp cl)
                (consistent-class-hierachy (cons class-rep cl))
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-constantpool-entry cp hp (cons class-rep cl)))
  :hints (("Goal" :in-theory (e/d () (isClassTerm)))))


(defthm consistent-constantpool-add-new-class
  (implies (and (consistent-constantpool cps hp cl)
                (consistent-class-hierachy (cons class-rep cl))
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-constantpool cps hp (cons class-rep cl)))
  :hints (("Goal" :in-theory (e/d () (isClassTerm)))))



(defthm consistent-class-decl-add-new-class
  (implies (and (consistent-class-decl class-decl cl hp)
                (consistent-class-hierachy (cons class-rep cl))
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-class-decl class-decl (cons class-rep cl) hp))
  :hints (("Goal" :in-theory (e/d () (isClassTerm)))))


(defthm consistent-class-decls-add-new-class
  (implies (and (consistent-class-decls cl1 cl hp)
                (consistent-class-hierachy (cons class-rep cl))
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-class-decls cl1 (cons class-rep cl) hp))
  :hints (("Goal" :in-theory (e/d () (isClassTerm consistent-class-decl)))))

;;;
;;; Thu Jun  9 22:49:04 2005
;;; Thu Jun  9 22:49:05 2005
;;;
;;; Need to add the assertion that if isInterfaceType, then it has no fields!!
;;;

;; (i-am-here)

(defthm consistent-state-consistent-class-decl-add-new-class-decl-lemma
  (implies (and  (consistent-state s)
                 (consistent-class-hierachy (cons class-rep
                                                  (instance-class-table s)))
                 (isClassTerm class-rep)
                 (car (class-by-name-s (classname class-rep) 
                                       (env-class-table (env s))))
                 (class-is-loaded-from-helper class-rep
                                              (mv-nth 1
                                                      (class-by-name-s 
                                                       (classname class-rep) 
                                                       (env-class-table (env
                                                                         s)))))
                 (JVM::wff-static-cp-ok 
                         (fields-s (mv-nth 1 (class-by-name-s 
                                              (classname class-rep)
                                              (env-class-table (env s)))))
                         (constantpool class-rep))
                 (equal (fields class-rep)
                        (runtime-instance-fields-rep1 
                         (fields-s (mv-nth 1 (class-by-name-s 
                                              (classname class-rep)
                                              (env-class-table (env s)))))
                         (classname class-rep)))
                 (or (not (isInterface class-rep)) ;; 
                     (equal (fields class-rep) nil))  ;; no instance field if interface.
                 
                 (equal (static-fields class-rep)
                        (runtime-static-fields-rep1 
                         (fields-s (mv-nth 1 (class-by-name-s 
                                              (classname class-rep)
                                              (env-class-table (env s)))))
                         (classname class-rep)
                         (constantpool class-rep)))
                 (consistent-static-fields (classname class-rep)
                                           (runtime-static-fields-rep1 
                                                (fields-s (mv-nth 1 (class-by-name-s 
                                                                     (classname class-rep)
                                                                     (env-class-table (env s)))))
                                                (classname class-rep)
                                                (constantpool class-rep))
                                           (instance-class-table s)
                                           (heap s))
                 (CONSISTENT-VALUE (TAG-REF (CLASS-REF CLASS-REP))
                                   "java.lang.Class"
                                   (INSTANCE-CLASS-TABLE S)
                                   (HEAP S))
                 (CONSISTENT-CONSTANTPOOL (CONSTANTPOOL CLASS-REP)
                                          (HEAP S)
                                          (INSTANCE-CLASS-TABLE S))
                 (VALID-REFP (TAG-REF (CLASS-REF CLASS-REP))
                             (HEAP S))
                 (equal (methods class-rep)
                        (RUNTIME-METHODS-REP 
                         (methods-s 
                          (mv-nth 1
                                  (class-by-name-s 
                                   (classname class-rep) 
                                   (env-class-table (env s)))))
                         (classname class-rep)))
                 (valid-refp (tag-ref (class-ref class-rep)) hp))
           (consistent-class-decl class-rep
                                  (instance-class-table s)
                                  (heap s)))
  :hints (("Goal" :in-theory (e/d () (isClassTerm static-fields 
                                                  fields-s
                                                  fields
                                                  methods
                                                  constantpool
                                                  methods-s
                                                  class-ref
                                                  wff-class-rep-static-strong)))))

;
;
;  Lemmas (in this section) here are needed to prove  
; 
;    load_class2 preserves consistent-class-table
;
;  We work from ground up, and prove load_cp_entry preserves it. 
;  .... 
; 

(defthm heap-init-map-aux-load_cp_entries
  (equal (heap-init-map (aux (mv-nth 1 (load_cp_entries cps s))))
         (heap-init-map (aux s))))



(defthm heap-init-map-aux-is
  (equal (heap-init-map (aux (load_class2 any s)))
         (heap-init-map (aux s)))
  :hints (("Goal" :in-theory (enable load_class2))))


(defthm consistent-heap1-bind-len-heap
  (implies (and (consistent-heap1 hp1 hp cl id)
                (integerp id))
           (equal (len (bind (+ id (len hp1)) any hp1))
                  (+ 1 (len hp1)))))


(defthm consistent-heap-len-bind-len-heap
  (implies (consistent-heap hp cl acl)
           (equal (len (bind (len hp) any hp))
                  (+ 1 (len hp))))
  :hints (("Goal" :in-theory (enable consistent-heap)
           :use ((:instance consistent-heap1-bind-len-heap
                            (id 0) (hp1 hp))))))


(defthm consistent-heap1-not-bound?
  (implies (consistent-heap1 hp1 hp cl id)
           (not (bound? (+ 1 (+ id (len hp1))) hp1)))
  :hints (("Goal" :in-theory (enable bound?))))


(defthm consistent-heap-not-bound?
  (implies (consistent-heap hp cl acl)
           (not (bound? (+ 1 (len hp)) hp)))
  :hints (("Goal" :in-theory (enable consistent-heap)
           :use ((:instance consistent-heap1-not-bound?
                            (id 0) (hp1 hp))))))


(defthm bound?-after-bind
  (bound? ref (bind ref any hp))
  :hints (("Goal" :in-theory (enable bind bound?))))

(in-theory (disable binding))

(defthm binding-of-bind
  (equal (binding x (bind x obj hp))
         obj)
  :hints (("Goal" :in-theory (enable binding bind))))

(defthm consistent-constantpool-entry-load-cp-entry
  (implies (and (wff-constant-pool-entry-s cp)
                (consistent-state s))
           (consistent-constantpool-entry (car (load_cp_entry cp s))
                                          (heap (mv-nth 1 (load_cp_entry cp s)))
                                          (instance-class-table s)))
  :hints (("Goal" :in-theory (enable load_cp_entry obj-type common-info))))



(defthm consistent-constantpool-entry-load-cp-entry-generalize
  (implies (and (wff-constant-pool-entry-s cp)
                (equal (instance-class-table s) cl)
                (consistent-state s))
           (consistent-constantpool-entry (car (load_cp_entry cp s))
                                          (heap (mv-nth 1 (load_cp_entry cp s)))
                                          cl)) 
  :hints (("Goal" :in-theory (enable load_cp_entry obj-type common-info))))


(defthm bound?-bound?-bind
  (implies (bound? ref hp)
           (bound? ref (bind ref2 any hp)))
  :hints (("Goal" :in-theory (enable bind bound?))))

(defthm bound?-bound?-load-cp
  (implies (bound? ref (heap s))
           (bound? ref (heap (mv-nth 1 (load_cp_entry cp s)))))
  :hints (("Goal" :in-theory (enable load_cp_entry))))

(defthm bound?-bound?-load-cps
  (implies (bound? ref (heap s))
           (bound? ref (heap (mv-nth 1 (load_cp_entries cps s))))))



(defthm consistent-state-implies-not-bound-len-plus-one
  (implies (consistent-state s)
           (not (bound? (+ 1 (len (heap s))) (heap s)))))

(defthm binding-bind-diff
  (equal (binding x (bind y obj hp))
         (if (equal x y) 
             obj
           (binding x hp)))
  :hints (("Goal" :in-theory (enable binding bind))))


(defthm consistent-state-load_cp_entry_only_add_new_objects
  (implies (and (consistent-state s)
                (bound? ref (heap s)))
           (equal (binding ref (heap (mv-nth 1 (load_cp_entry cp s))))
                  (binding ref (heap s))))
  :hints (("Goal" :in-theory (enable load_cp_entry))))


(defthm consistent-constantpool-entry-load-cp-entry-generalize2
  (implies (and (consistent-constantpool-entry cp (heap s) cl)
                (consistent-state s))
           (consistent-constantpool-entry cp (heap (mv-nth 1 (load_cp_entries
                                                              cps s))) cl))
  :hints (("Goal" :do-not '(generalize))))



(defthm consistent-constantpool-load-cp-entries
  (implies (and (wff-constant-pool-s cps)
                (consistent-state s))
           (consistent-constantpool 
            (car (load_cp_entries cps s))
            (heap (mv-nth 1 (load_cp_entries cps s)))
            (instance-class-table s)))
  :hints (("Goal" :in-theory (disable wff-constant-pool-entry-s
                                      consistent-constantpool-entry)
           :do-not '(generalize))))
                                      
;; Proved earlier. Copied here for reference.
;;
;; (defthm consistent-value-cons-new-class
;;   (implies (and (consistent-value v type cl hp)
;;                 (consistent-class-hierachy (cons class-rep cl))
;;                 (isClassTerm class-rep)
;;                 (not (isClassTerm (class-by-name (classname class-rep) cl))))
;;            (consistent-value v type (cons class-rep cl) hp))
;;   :hints (("Goal" :in-theory (enable consistent-value))))

(defthm consistent-state-implies-assignment-compatible
  (implies (consistent-state s)
           (ASSIGNMENTCOMPATIBLE "java.lang.Class" "java.lang.Class"
                                 (INSTANCE-CLASS-TABLE S)))
  :hints (("Goal" :in-theory (enable assignmentcompatible))))


(defthm valid-refp-tag-ref
  (implies (integerp ref)
           (valid-refp (tag-ref ref)
                       (bind ref 
                             (CONS 'OBJECT
                                   (CONS '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                                                       "java.lang.Class")
                                         (CONS (CONS 'SPECIFIC-INFO
                                                     (CONS 'INSTANCE_CLASS (CONS ANY 'NIL)))
                                               '((("java.lang.Class")
                                                  ("java.lang.Object"))))))
                             anyhp)))
  :hints (("Goal" :in-theory (enable valid-refp wff-tagged-value
                                     bound? tag-of
                                     wff-refp tag-ref rREF obj-type common-info))))


(defthm consistent-value-build-an-new-class-object
  (implies (and (consistent-state s)
                (equal (instance-class-table s) cl)
                (integerp ref))
           (CONSISTENT-VALUE
            (TAG-REF ref)
            '"java.lang.Class"
            cl 
            (BIND ref (CONS 'OBJECT
                            (CONS '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                                                "java.lang.Class")
                                  (CONS (CONS 'SPECIFIC-INFO
                                              (CONS 'INSTANCE_CLASS (CONS ANY 'NIL)))
                                        '((("java.lang.Class")
                                           ("java.lang.Object"))))))
                  (heap s))))
  :hints (("Goal" :in-theory (enable consistent-value valid-refp
                                     wff-tagged-value
                                     wff-refp tag-ref RREF deref2
                                     bind binding obj-type
                                     tag-of
                                     common-info))))

; we need to show when you add one new class, consistent-value
; judgement does not change.

(defthm consistent-value-tag-1-fact
   (CONSISTENT-VALUE (TAG -1 'INT) 'INT CL HP)
   :hints (("Goal" :in-theory (enable consistent-value tag-of
                                      wff-tagged-value
                                      tag
                                      primitive-type?))))

(defthm consistent-value-tag-1-fact-2
   (CONSISTENT-VALUE (TAG -1 'LONG) 'LONG CL HP)
   :hints (("Goal" :in-theory (enable consistent-value tag-of
                                      wff-tagged-value
                                      tag
                                      primitive-type?))))

(defthm consistent-value-tag-1-fact-3
   (CONSISTENT-VALUE (TAG -1 '"java.lang.String") '"java.lang.String" CL HP)
   :hints (("Goal" :in-theory (enable consistent-value tag-of
                                      wff-tagged-value
                                      tag
                                      primitive-type?))))

                              
(defthm consistent-value-tag-consistent-constant-pool
  (implies (and (consistent-constantpool-entry cp hp cl)
                (primitive-type? (cpentry-type cp)))
           (consistent-value (tag (cpentry-value cp)
                                  (cpentry-type cp))
                             (cpentry-type cp)
                             cl hp))
  :hints (("Goal" :in-theory (enable tag-of tag consistent-value
                                     int32p tag-ref 
                                     
                                     primitive-type? value-of
                                     wff-tagged-value)
           :do-not-induct t))) 
           


(defthm consistent-constantpool-consistent-entry
  (implies (and (consistent-constantpool cps hp cl)
                (<= 0 i)
                (< i (len cps)))
           (consistent-constantpool-entry (nth i cps) hp cl)))
                

(defthm consistent-value-tag-consistent-constant-pool-x
  (implies (and (consistent-constantpool cps hp cl)
                (<= 0 i)
                (< i (len cps))
                (primitive-type? (cpentry-type (nth i cps))))
           (consistent-value (tag (cpentry-value (nth i cps))
                                  (cpentry-type (nth i cps)))
                             (cpentry-type (nth i cps))
                             cl hp))
  :hints (("Goal" :do-not-induct t
           :use ((:instance consistent-value-tag-consistent-constant-pool
                            (cp (nth i cps)))))))
           


(defthm consistent-value-fact-1
  (CONSISTENT-VALUE '(INT . 0)
                    'INT
                    CL HP)
  :hints (("Goal" :in-theory (enable consistent-value))))

(defthm consistent-value-fact-2
  (CONSISTENT-VALUE '(LONG . 0)
                    'LONG
                    CL HP)
  :hints (("Goal" :in-theory (enable consistent-value))))


(defthm consistent-value-fact-3
  (implies (reference-type type)
           (CONSISTENT-VALUE (tag -1 type)
                             type 
                             CL HP))
  :hints (("Goal" :in-theory (enable consistent-value primitive-type?))))

(defthm consistent-value-fact-4
  (CONSISTENT-VALUE '(BOOLEAN . 0)
                    'BOOLEAN
                    CL HP)
  :hints (("Goal" :in-theory (enable consistent-value))))


(defthm consistent-value-fact-5
  (CONSISTENT-VALUE '(BYTE . 0)
                    'BYTE
                    CL HP)
  :hints (("Goal" :in-theory (enable consistent-value))))


(defthm consistent-value-fact-6
  (CONSISTENT-VALUE '(CHAR . 0)
                    'CHAR
                    CL HP)
  :hints (("Goal" :in-theory (enable consistent-value))))

(defthm consistent-value-fact-7
  (CONSISTENT-VALUE '(SHORT . 0)
                    'SHORT
                    CL HP)
  :hints (("Goal" :in-theory (enable consistent-value))))




(local (in-theory (disable tag)))


;; (i-am-here) ;; Thu Jan  5 19:56:22 2006 
;; Thu Jan  5 19:56:25 2006
;;

;;; Thu Jan  5 20:02:52 2006
;;; 
;;; problem: we need to assert that 
;;; wff-static-cp-entry-s implies 
;;; that values are in suitable range!!! 
;;; 
;;; Thu Jan  5 20:03:26 2006

;;; we updated that. It should prove!! 

;; (i-am-here) ;; Thu Jan  5 22:06:12 2006

(defthm if-type-primitive-type-lemma-1
  (implies (and (jvm::wff-static-cp-entry-ok field dynamic-cp)
                (consistent-constantpool dynamic-cp hp cl)
                (primitive-type? type)
                (equal (cpentry-type (nth (field-cpindex-s field) dynamic-cp)) type))
           (consistent-value (tag (cpentry-value (nth (field-cpindex-s field) dynamic-cp))
                                  type)
                             type
                             cl hp))
  :hints (("Goal" :in-theory (enable primitive-type?
                                     tag normalize-type-rep
                                     consistent-value))))


(defthm if-type-primitive-type-lemma-2
  (implies (and (jvm::wff-static-cp-entry-ok field dynamic-cp)
                (consistent-constantpool dynamic-cp hp cl)
                (primitive-type? type)
                (equal (cpentry-type (nth (field-cpindex-s field) dynamic-cp)) 'INT)
                (EQUAL (FIELD-FIELDTYPE-S field) type))
           (consistent-value (tag (cpentry-value (nth (field-cpindex-s field) dynamic-cp))
                                  type)
                             type
                             cl hp))
  :hints (("Goal" :in-theory (enable primitive-type?
                                     tag normalize-type-rep
                                     consistent-value))))



(defthm consistent-static-fields-runtime-static-fields
  (implies (and (JVM::wff-static-cp-ok fields dynamic-cp)
                (consistent-constantpool dynamic-cp hp cl)
                (wff-constant-pool dynamic-cp)
                (JVM::wff-fields-s fields))
           (consistent-static-fields any (runtime-static-fields-rep1 fields any
                                                                     dynamic-cp) cl
                                                                     hp))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d ()
                           (cpentry-type 
                            cpentry-value
                            field-fieldtype-s
                            field-cpindex-s)))))

;
;  We also need to show that adding a new object into heap does
;  not change judgement on consistent-class-decl, which in term
;  asserts consistency on static-fields etc. 
; 
; (Defthm consistent-class-decl-bind-new-object
;   (implies (and (consistent-class-decl class-rep cl hp)
;                 (alistp hp)
;                 (not (bound? ref hp)))
;            (consistent-class-decl class-rep cl 
;                                   (bind ref obj hp)))
;   :hints (("Goal" :do-not '(generalize))))

(defthm consistent-class-decls-bind-new-object
   (implies (and (consistent-class-decls cl1 cl hp)
                 (alistp hp)
                 (not (bound? ref hp)))
            (consistent-class-decls cl1 cl 
                                   (bind ref obj hp)))
   :hints (("Goal" :do-not '(generalize))))


(defthm consistent-class-decls-load-cp-entries
  (implies (and (consistent-class-decls decls (instance-class-table s) (heap s))
                (consistent-state s))
           (consistent-class-decls decls (instance-class-table s) (heap (mv-nth 1 (load_cp_entries cps s)))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d () (consistent-class-decl consistent-state)))))

(in-theory (disable consistent-class-decl))

(local (defthm cons-ref-is-tag-ref
         (equal (cons 'ref (len hp))
                (tag-ref (len hp)))))


(defthm all-fields-static-final-implies-runtime-instance-fields-nil
  (implies (jvm::all-fields-static-final fields)
           (equal (runtime-instance-fields-rep1 fields any)  nil)))

(defthm if-interface-then-no-instance-fields
  (implies (and (wff-class-rep-static-strong class-desc)
                (mem '*interface* (accessflags-s class-desc)))
           (equal (runtime-instance-fields-rep1 
                   (fields-s class-desc) any)
                  nil)))
  
;;; (i-am-here) ;; Thu Jul 21 01:25:28 2005

(defthm consistent-state-implies-consistent-class-decls-load-class2-strong
  (implies (and (consistent-state s)
                (class-loaded? (super-s 
                                (mv-nth 1 (class-by-name-s any
                                             (env-class-table (env s))))) s)
                (all-interfaces-bounded? (interfaces-s 
                                          (mv-nth 1 (class-by-name-s any 
                                                                     (env-class-table (env s)))))
                                         (instance-class-table s))
                (car (class-by-name-s any (env-class-table (env s))))
                (not (class-loaded? any s))
                (no-fatal-error? s))
           (consistent-class-table (instance-class-table  (load_class2 any s))
                                   (env-class-table (env s))
                                   (heap (load_class2 any s))))
  :hints (("Goal" :in-theory (e/d (add-instance-class-entry
                                   consistent-class-table 
                                   consistent-class-decl
                                   isInterface
                                   class-loaded?
                                   load_class2)
                                   ;;instance-class-table-inv
                                   ;;class-loaded?)
                                  (make-runtime-class-rep isClassTerm
                                                          ;;
                                                          tag-ref
                                                          ;;build-an-instanceclass
                                                          class-is-loaded-from-helper)))))




;; Often, what to disable and enable becomes important. 

; wff-methods-instance-class-rep-make-wff-methods
; TO FIX LATER by asserting more in the wff-env!  or make sure
; runtime-static-fields-rep1 always return a wff-one if it does
; not, returns a default one and some error flag? 

(skip-proofs 
 (defthm wff-methods-instance-class-rep-make-wff-methods
   (wff-methods-instance-class-rep
    (make-runtime-class-rep
     any super cp fields 
     (runtime-methods-rep1 smethods any)
    interfaces
    static-fields status access-flags init-thread class-ref))
   :hints (("Goal" :in-theory (enable wff-class-rep)))))

; prove load_class2 preserves consistent-state.

;;; Fri May 27 01:26:57 2005. TO FIX !!!

(defthm |loader-consistent-state-Subgoal 8|
  (IMPLIES
   (AND
    (CONSISTENT-STATE S)
    (CLASS-LOADED?
     (SUPER-S (MV-NTH 1
                      (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S)))))
     S)
    (ALL-INTERFACES-BOUNDED?
     (INTERFACES-S (MV-NTH 1
                           (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S)))))
     (INSTANCE-CLASS-TABLE S))
    (CAR (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S))))
    (NOT (CLASS-LOADED? ANY S))
    (NO-FATAL-ERROR? S))
   (WFF-METHODS-INSTANCE-CLASS-TABLE-STRONG
    (INSTANCE-CLASS-TABLE (LOAD_CLASS2 ANY S))))
  :hints (("Goal" :in-theory (e/d (add-instance-class-entry
                                   load_class2
                                   )
                                  (make-runtime-class-rep isClassTerm
                                                          class-is-loaded-from-helper)))))

(defthm |loader-consistent-state-Subgoal 7|
  (IMPLIES
   (AND
    (CONSISTENT-STATE S)
    (CLASS-LOADED?
     (SUPER-S (MV-NTH 1
                      (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S)))))
     S)
    (ALL-INTERFACES-BOUNDED?
     (INTERFACES-S (MV-NTH 1
                           (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S)))))
     (INSTANCE-CLASS-TABLE S))
    (CAR (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S))))
    (NOT (CLASS-LOADED? ANY S))
    (NO-FATAL-ERROR? S))
   (CONSISTENT-CLASS-HIERACHY (INSTANCE-CLASS-TABLE (LOAD_CLASS2 ANY S))))
  :hints (("Goal" :in-theory (e/d (add-instance-class-entry
                                   class-loaded?
                                   load_class2)
                                  (make-runtime-class-rep 
                                   isClassTerm
                                   class-is-loaded-from-helper)))))




(defthm |loader-consistent-state-Subgoal 6|
  (IMPLIES
   (AND
    (CONSISTENT-STATE S)
    (CLASS-LOADED?
     (SUPER-S (MV-NTH 1
                      (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S)))))
     S)
    (ALL-INTERFACES-BOUNDED?
     (INTERFACES-S (MV-NTH 1
                           (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S)))))
     (INSTANCE-CLASS-TABLE S))
    (CAR (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S))))
    (NOT (CLASS-LOADED? ANY S))
    (NO-FATAL-ERROR? S))
   (CONSISTENT-HEAP (HEAP (LOAD_CLASS2 ANY S))
                    (INSTANCE-CLASS-TABLE (LOAD_CLASS2 ANY S))
                    (ARRAY-CLASS-TABLE S)))
  :hints (("Goal" :in-theory (e/d (add-instance-class-entry
                                   class-loaded?
                                   load_class2)
                                  (make-runtime-class-rep 
                                   isClassTerm
                                   class-is-loaded-from-helper)))))



(defthm |loader-consistent-state-Subgoal 5|
  (IMPLIES
   (AND
    (CONSISTENT-STATE S)
    (CLASS-LOADED?
     (SUPER-S (MV-NTH 1
                      (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S)))))
     S)
    (ALL-INTERFACES-BOUNDED?
     (INTERFACES-S (MV-NTH 1
                           (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S)))))
     (INSTANCE-CLASS-TABLE S))
    (CAR (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S))))
    (NOT (CLASS-LOADED? ANY S))
    (NO-FATAL-ERROR? S))
   (CONSISTENT-HEAP-ARRAY-INIT-STATE (HEAP (LOAD_CLASS2 ANY S))
                                     (INSTANCE-CLASS-TABLE (LOAD_CLASS2 ANY S))
                                     (ARRAY-CLASS-TABLE S)
                                     (HEAP-INIT-MAP (AUX S))))
  :hints (("Goal" :in-theory (e/d (add-instance-class-entry
                                   class-loaded?
                                   load_class2)
                                  (make-runtime-class-rep 
                                   isClassTerm
                                   class-is-loaded-from-helper)))))

;; COPIED FOR REFERENCE
;;
;; (defthm consistent-class-decls-add-new-class
;;   (implies (and (consistent-class-decls cl1 cl hp)
;;                 (consistent-class-hierachy (cons class-rep cl))
;;                 (isClassTerm class-rep)
;;                 (not (isClassTerm (class-by-name (classname class-rep) cl))))
;;            (consistent-class-decls cl1 (cons class-rep cl) hp))
;;   :hints (("Goal" :in-theory (e/d () (isClassTerm consistent-class-decl)))))

(defthm consistent-value-x-add-new-class
  (implies (and (consistent-value-x v  cl hp)
                (consistent-class-hierachy (cons class-rep cl))
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-value-x v (cons class-rep cl) hp))
  :hints (("Goal" :in-theory (e/d (consistent-value-x) (isClassTerm)))))


(defthm consistent-opstack-add-new-class
  (implies (and (consistent-opstack opstack cl hp)
                (consistent-class-hierachy (cons class-rep cl))
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-opstack opstack (cons class-rep cl) hp))
  :hints (("Goal" :in-theory (e/d () (isClassTerm)))))


(defthm consistent-locals-add-new-class
  (implies (and (consistent-locals locals cl hp)
                (consistent-class-hierachy (cons class-rep cl))
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-locals locals (cons class-rep cl) hp))
  :hints (("Goal" :in-theory (e/d () (isClassTerm)))))


;;; >V            (DEFUN
;;;                    CONSISTENT-FRAME-MAX-LOCAL (FRAME CL)
;;;                    (MYLET* ((METHOD (DEREF-METHOD (METHOD-PTR FRAME) CL)))
;;;                            (AND (WFF-CALL-FRAME FRAME)
;;;                                 (WFF-METHOD-PTR (METHOD-PTR FRAME))
;;;                                 (WFF-INSTANCE-CLASS-TABLE CL)
;;;                                 (WFF-METHOD-DECL METHOD)
;;;                                 (OR (MEM '*ABSTRACT*
;;;                                          (METHOD-ACCESSFLAGS METHOD))
;;;                                     (MEM '*NATIVE*
;;;                                          (METHOD-ACCESSFLAGS METHOD))
;;;                                     (AND (WFF-CODE (METHOD-CODE METHOD))
;;;                                          (INTEGERP (METHOD-MAXLOCALS METHOD))
;;;                                          (<= (LEN (LOCALS FRAME))
;;;                                              (METHOD-MAXLOCALS METHOD)))))))
;;;
;;; additional checks in force me to add more hyps into ....


(defthm deref-method-equal-add-new-class
  (implies (and (deref-method method-ptr cl)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (equal (deref-method method-ptr (cons class-rep cl))
                  (deref-method method-ptr cl)))
  :hints (("Goal" :in-theory (enable deref-method))))


(defthm consistent-call-frame-add-new-class
  (implies (and (consistent-frame frame cl hp)
                (consistent-class-hierachy (cons class-rep cl))
                (wff-class-rep class-rep)
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-frame frame (cons class-rep cl) hp))
  :hints (("Goal" :in-theory (e/d () (isClassTerm consistent-opstack
                                                  consistent-locals)))))

(in-theory (disable consistent-frame))

(defthm consistent-call-stack-add-new-class
  (implies (and (consistent-call-stack cs cl hp)
                (consistent-class-hierachy (cons class-rep cl))
                (wff-class-rep class-rep)
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-call-stack cs (cons class-rep cl) hp))
  :hints (("Goal" :in-theory (e/d () (isClassTerm)))))

;; (i-am-here) 
;; Mon Mar 21 12:23:02 2005. After adding linkage requirement
;; between frames. 


(defthm consistent-adjacent-frame-add-new-class
  (implies (and (consistent-adjacent-frame caller callee cl)
                (deref-method (method-ptr caller) cl)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-adjacent-frame caller callee (cons class-rep cl)))
  :hints (("Goal" :in-theory (enable consistent-adjacent-frame))))


(defthm wff-invocation-frame-implies-deref-method
  (implies (wff-invocation-frame frame cl)
           (deref-method (method-ptr frame) cl))
  :hints (("Goal" :in-theory (enable wff-invocation-frame)))
  :rule-classes :forward-chaining)


(in-theory (disable wff-invocation-frame consistent-adjacent-frame))

;; (i-am-here) ;; Fri May 27 21:55:19 2005

(defthm wff-invocation-frame-add-new-class
  (implies (and (wff-invocation-frame frame cl)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (wff-invocation-frame frame (cons class-rep cl)))
  :hints (("Goal" :in-theory (enable wff-invocation-frame))))


(defthm deref-method-no-change-add-new-class
  (implies (and (not (isClassTerm (class-by-name (classname class-rep) cl)))
                (deref-method method-ptr cl))
           (equal (deref-method method-ptr (cons class-rep cl))
                  (deref-method method-ptr cl)))
  :hints (("Goal" :in-theory (enable deref-method))))
 

(defthm wff-invocation-frame-implies-deref-method-b
  (implies (wff-invocation-frame frame cl)
           (deref-method (method-ptr frame) cl))
  :hints (("Goal" :in-theory (enable wff-invocation-frame))))

(in-theory (disable method-ptr))


  

(defthm consistent-call-stack-linkage-add-new-class
  (implies (and (consistent-call-stack-linkage cs cl)
                (consistent-class-hierachy (cons class-rep cl))
                (wff-class-rep class-rep)
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-call-stack-linkage cs (cons class-rep cl)))
  :hints (("Goal" :in-theory (e/d (top pop) (isClassTerm))
           :do-not '(generalize))))


(defthm consistent-thread-entry-add-new-class
  (implies (and (consistent-thread-entry thread cl hp)
                (consistent-class-hierachy (cons class-rep cl))
                (wff-class-rep class-rep)
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-thread-entry thread (cons class-rep cl) hp))
  :hints (("Goal" :in-theory (e/d () (isClassTerm consistent-call-stack))
           :do-not-induct t)))


(defthm consistent-thread-entries-add-new-class
  (implies (and (consistent-thread-entries ths cl hp)
                (consistent-class-hierachy (cons class-rep cl))
                (wff-class-rep class-rep)
                (isClassTerm class-rep)
                (not (isClassTerm (class-by-name (classname class-rep) cl))))
           (consistent-thread-entries ths (cons class-rep cl) hp))
  :hints (("Goal" :in-theory (e/d () (isClassTerm consistent-class-decl)))))


;; (defthm consistent-thread-entry-bind-new-object
;;   (implies (and (consistent-thread-entry th cl hp)
;;                 (alistp hp)
;;                 (not (bound? ref hp)))
;;            (consistent-thread-entry th cl (bind ref obj hp)))
;;   :hints (("Goal" :do-not '(generalize))))


(defthm consistent-thread-entries-bind-new-object
   (implies (and (consistent-thread-entries ths cl hp)
                 (alistp hp)
                 (not (bound? ref hp)))
            (consistent-thread-entries ths cl (bind ref obj hp)))
   :hints (("Goal" :do-not '(generalize))))

(defthm consistent-thread-entries-load-cp-entries
  (implies (and (consistent-thread-entries tt (instance-class-table s) (heap s))
                (consistent-state s))
           (consistent-thread-entries tt (instance-class-table s)
                                    (heap (mv-nth 1 (load_cp_entries cps s)))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d () (consistent-thread-entry consistent-state)))))

(defthm |loader-consistent-state-Subgoal 4|
  (IMPLIES
   (AND
    (CONSISTENT-STATE S)
    (CLASS-LOADED?
     (SUPER-S (MV-NTH 1
                      (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S)))))
     S)
    (ALL-INTERFACES-BOUNDED?
     (INTERFACES-S (MV-NTH 1
                           (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S)))))
     (INSTANCE-CLASS-TABLE S))
    (CAR (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S))))
    (NOT (CLASS-LOADED? ANY S))
    (NO-FATAL-ERROR? S))
   (CONSISTENT-THREAD-ENTRIES (THREAD-TABLE S)
                              (INSTANCE-CLASS-TABLE (LOAD_CLASS2 ANY S))
                              (HEAP (LOAD_CLASS2 ANY S))))
  :hints (("Goal" :in-theory (e/d (add-instance-class-entry
                                   class-loaded?
                                   load_class2)
                                  (make-runtime-class-rep 
                                   isClassTerm
                                   class-is-loaded-from-helper)))))



(defthm all-interfaces-bounded?-implies-all-correctly-loaded
  (implies (all-interfaces-bounded? l (instance-class-table s))
           (all-loaded? l s))
  :hints (("Goal" :in-theory (enable class-loaded?)))
  :rule-classes :forward-chaining)


(defthm jvm-loader-inv-helper-implies-loader-helper1
  (implies (and (JVM::loader-inv-helper cl1 cl scl)
                (class-by-name name cl1))
           (jvm::loader-inv-helper1 (class-by-name name cl1) cl scl))
  :hints (("Goal" :in-theory (e/d () (jvm::loader-inv-helper1)))))

(defthm loader-inv-implies-loader-inv-helper1
  (implies (and (loader-inv s)
                (no-fatal-error? s)
                (class-by-name name (instance-class-table s)))
           (jvm::loader-inv-helper1 (class-by-name name (instance-class-table
                                                         s))
                                    (instance-class-table s)
                                    (env-class-table (env s))))
  :hints (("Goal" :in-theory (e/d (loader-inv) (jvm::loader-inv-helper1))))
  :rule-classes :forward-chaining)


;; jvm-loader-inv-helper-implies-loaded-f


(defthm classname-class-by-name-is
  (implies (class-by-name name cl)
           (equal (classname (class-by-name name cl))
                  name)))


(defthm loader-inv-loaded-correctly-loaded
  (implies (and (loader-inv s)
                (no-fatal-error? s)
                (class-by-name name (instance-class-table s)))
           (correctly-loaded? name (instance-class-table s)
                              (env-class-table (env s))))
  :hints (("Goal" :in-theory (e/d (loader-inv) (jvm::loader-inv-helper1))
           :use ((:instance jvm-loader-inv-helper-implies-loaded-f
                            (class-rep (class-by-name name
                                                      (instance-class-table
                                                       s)))
                            (cl (instance-class-table s))
                            (scl (env-class-table (env s))))))))


(defthm consistent-state-loaded-correctly-loaded
  (implies (and (class-by-name name (instance-class-table s))
                (consistent-state s)
                (no-fatal-error? s))
           (correctly-loaded? name (instance-class-table s)
                              (env-class-table (env s))))
  :rule-classes :forward-chaining)


(defthm consistent-state-all-loaded-implies-all-correctly-loaded
  (implies (and (consistent-state s)
                (no-fatal-error? s)
                (all-loaded? l s))
           (jvm::all-correctly-loaded? l (instance-class-table s)
                                       (env-class-table (env s))))
  :hints (("Goal" :in-theory (enable class-loaded?))))


;;; Wed Nov 10 12:18:49 2004

(defthm |loader-consistent-state-Subgoal 3|
  (IMPLIES
   (AND
    (CONSISTENT-STATE S)
    (ISCLASSTERM
     (CLASS-BY-NAME
       (SUPER-S (MV-NTH 1
                        (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S)))))
       (INSTANCE-CLASS-TABLE S)))
     (ALL-INTERFACES-BOUNDED?
      (INTERFACES-S (MV-NTH 1
                            (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S)))))
      (INSTANCE-CLASS-TABLE S))
     (CAR (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S))))
     (NOT (ISCLASSTERM (CLASS-BY-NAME ANY (INSTANCE-CLASS-TABLE S))))
     (NO-FATAL-ERROR? S))
   (LOADER-INV (LOAD_CLASS2 ANY S)))
  :hints (("Goal" :in-theory (e/d (add-instance-class-entry
                                   instance-class-table-inv
                                   loader-inv)
                                   (make-runtime-class-rep 
                                    isClassTerm
                                    class-is-loaded-from-helper)))))


;;; we proved something like this!! 
;;; in jvm-loader-guard-verification-support-load-cp-guard.lisp
;;;

;;;      (defthm loaded-in-a-loader-inv-state-superchain-is-fixed
;;;        (implies (and (class-loaded? any s)
;;;                      (no-fatal-error? s)
;;;                      (loader-inv s))
;;;                 (equal (collect-superclass-list1 any (instance-class-table s) nil)
;;;                        (collect-superclassname1 any (external-class-table s) nil)))
;;;        :hints (("Goal" :restrict
;;;                 ((all-correctly-loaded-implies-collect-superclass-list
;;;                   ((env-cl (external-class-table s))))
;;;                  (loader-inv-helper-implies-all-found?
;;;                   ((cl (instance-class-table s)))))
;;;                 :do-not-induct t
;;;                 :in-theory (disable external-class-table))))

(defthm no-fatal-error-if-found
  (implies (and (no-fatal-error? s)
                (car (class-by-name-s any (env-class-table (env s)))))
           (no-fatal-error? (load_class2 any s)))
  :hints (("Goal" :in-theory (enable load_class2 no-fatal-error? fatalError))))


(defthm collect-superclass-list1-not-changed-if-loader-inv
  (implies (and (loader-inv s)
                (loader-inv (load_class2 any s))
                (no-fatal-error? s)
                (NOT (ISCLASSTERM (CLASS-BY-NAME ANY (INSTANCE-CLASS-TABLE
                                                      S))))
                (car (class-by-name-s any (env-class-table (env s))))
                (isclassterm (class-by-name any2 (instance-class-table s))))
           (equal (collect-superclass-list1 any2 (instance-class-table 
                                                   (load_class2 any s)) nil)
                  (collect-superclass-list1 any2 (instance-class-table s)
                                            nil)))
  :hints (("Goal" :cases ((not (no-fatal-error? (load_class2 any s))))
           :in-theory (e/d (add-instance-class-entry)
                           (make-runtime-class-rep 
                            isClassTerm
                            class-is-loaded-from-helper))
           :do-not-induct t)))

(defthm class-by-name-no-change-if-loader-inv
   (implies (and (isClassTerm (class-by-name any2 (instance-class-table s)))
                 (not (isClassTerm (class-by-name any (instance-class-table s)))))
            (equal (class-by-name any2 (instance-class-table (load_class2 any
                                                                          s)))
                   (class-by-name any2 (instance-class-table s))))
   :hints (("Goal" :in-theory (e/d (load_class2 add-instance-class-entry
                                                classname)
                                   (isClassTerm)))))


;;; Wed Nov 10 11:09:05 2004 We may introduce a weaker form of the
;;; consistent-state


(defthm build-immediate-instance-data-guard-load_class2
  (implies (and (loader-inv s)
                 (no-fatal-error? s)
                 (not (isclassterm 
                       (class-by-name any 
                                      (instance-class-table s))))
                 (car (class-by-name-s any (env-class-table (env s))))
                 (build-immediate-instance-data-guard n s)
                 (isclassterm (class-by-name n (instance-class-table s))))
          (build-immediate-instance-data-guard n (load_class2 any s))))



(defthm build-an-instance-data-guard-load_class2
  (implies (and (loader-inv s)
                 (no-fatal-error? s)
                 (not (isclassterm 
                       (class-by-name any 
                                      (instance-class-table s))))
                 (car (class-by-name-s any (env-class-table (env s))))
                 (build-a-java-visible-instance-data-guard l s)
                 (all-loaded? l s))
          (build-a-java-visible-instance-data-guard l (load_class2 any s)))
  :hints (("Goal" :in-theory (e/d (class-loaded?) (isclassterm 
                                                   build-immediate-instance-data-guard)))))


(in-theory (disable isclassterm))


(defthm array-correctly-loaded-loaded
  (implies (class-loaded? any2 s)
           (class-loaded? any2 (load_class2 any s)))
  :hints (("Goal" :cases ((class-loaded? any s)))
          ("Subgoal 1" :cases ((equal any2 any)))
          ("Subgoal 1.1" :in-theory (e/d (load_class2
                                          add-instance-class-entry)
                                         (make-runtime-class-rep)))))



(defthm arrayclass-loaded-loaded-after-loadclass2
  (implies (ARRAYCLASSLOADED? any s)
           (arrayclassloaded? any (load_class2 any2 s))))


(defthm array-class-correctly-loaded-loaded
  (implies (jvm::array-class-correctly-loaded? l s)
           (jvm::array-class-correctly-loaded? l (load_class2 any s)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable arrayclassloaded? class-loaded?))))


(defthm array-class-table-inv-helper-loaded
  (implies (jvm::array-class-table-inv-helper l s)
           (jvm::array-class-table-inv-helper l (load_class2 any s)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable arrayclassloaded?))))


(local (in-theory (disable class-loaded?)))


(defthm |loader-consistent-state-Subgoal 2|
 (IMPLIES
 (AND
  (CONSISTENT-STATE S)
  (CLASS-LOADED?
       (SUPER-S (MV-NTH 1
                        (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S)))))
       S)
  (ALL-INTERFACES-BOUNDED?
      (INTERFACES-S (MV-NTH 1
                            (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S)))))
      (INSTANCE-CLASS-TABLE S))
  (CAR (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S))))
  (NOT (CLASS-LOADED? ANY S))
  (NO-FATAL-ERROR? S))
 (ARRAY-CLASS-TABLE-INV (LOAD_CLASS2 ANY S)))
  :hints (("Goal" :in-theory (e/d (add-instance-class-entry
                                   instance-class-table-inv
                                   class-loaded?
                                   JVM::LOAD_ARRAY_CLASS_GUARD
                                   array-class-table-inv
                                   ;;BUILD-A-JAVA-VISIBLE-INSTANCE-DATA-GUARD
                                   ;;build-immediate-instance-data-guard
                                   ;;load_class2
                                   )
                                  (make-runtime-class-rep 
                                   isClassTerm
                                   class-is-loaded-from-helper)))))


(defthm consistent-java-lang-Object-not-afffected
  (implies (and (not (isClassTerm (class-by-name any (instance-class-table
                                                      s))))
                (isClassTerm (class-by-name "java.lang.Object" (instance-class-table s))))
           (equal (class-by-name "java.lang.Object" 
                                 (instance-class-table 
                                  (load_class2 any s)))
                  (class-by-name "java.lang.Object" (instance-class-table
                                                     s)))))

(defthm consistent-jvp-implies-fields-class-by-name-is
  (implies (CONSISTENT-JVP "java.lang.Object"
                           '(("java.lang.Object"))
                           cl hp)
           (not  (consp (fields (class-by-name "java.lang.Object" cl)))))
  :hints (("Goal" :in-theory (e/d (isClassTerm classname)
                                  (fields)))))


(defthm consistent-jvp-if-not-consp-fields
  (implies (and (isClassTerm (class-by-name "java.lang.Object" cl))
                (not (consp (fields (class-by-name "java.lang.Object" cl)))))
           (consistent-jvp "java.lang.Object"
                           '(("java.lang.Object"))
                           cl hp)))



(defthm consistent-jvp-implies-fields-class-by-name-is-specific
  (implies (CONSISTENT-JVP "java.lang.Object"
                           '(("java.lang.Object"))
                           (instance-class-table s) (heap s))
           (not  (consp (fields (class-by-name "java.lang.Object"
                                               (instance-class-table s))))))
  :hints (("Goal" :in-theory (e/d (isClassTerm classname)
                                  (fields)))))

(defthm consistent-state-implies-consistent-jvp
  (implies (consistent-state s)
           (CONSISTENT-JVP "java.lang.Object"
                           '(("java.lang.Object"))
                           (instance-class-table s) (heap s)))
  :hints (("Goal" :in-theory (e/d (consistent-state boot-strap-class-okp)
                                  (consistent-jvp)))))
                                     

;; (i-am-here) ;; Mon Jun 20 16:38:42 2005

(defthm consistent-state-implies-fields-java-lang-Object-nil
  (implies (consistent-state s)
           (not (fields (class-by-name "java.lang.Object"
                                       (instance-class-table s)))))
  :hints (("Goal" :in-theory (e/d (consistent-state boot-strap-class-okp) ()))))





(defthm |loader-consistent-state-Subgoal 1|
  (IMPLIES
   (AND
    (CONSISTENT-STATE S)
    (ISCLASSTERM
     (CLASS-BY-NAME
      (SUPER-S (MV-NTH 1
                       (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S)))))
      (INSTANCE-CLASS-TABLE S)))
    (ALL-INTERFACES-BOUNDED?
     (INTERFACES-S (MV-NTH 1
                           (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S)))))
     (INSTANCE-CLASS-TABLE S))
    (CAR (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S))))
    (NOT (ISCLASSTERM (CLASS-BY-NAME ANY (INSTANCE-CLASS-TABLE S))))
    (NO-FATAL-ERROR? S))
   (BOOT-STRAP-CLASS-OKP (LOAD_CLASS2 ANY S)))
  :hints (("Goal" :in-theory (e/d (add-instance-class-entry
                                   instance-class-table-inv
                                   class-loaded?
                                   JVM::LOAD_ARRAY_CLASS_GUARD
                                   boot-strap-class-okp
                                   ;;BUILD-A-JAVA-VISIBLE-INSTANCE-DATA-GUARD
                                   ;;build-immediate-instance-data-guard
                                   ;;load_class2
                                   )
                                  (make-runtime-class-rep 
                                   isClassTerm
                                   fields
                                   consistent-jvp
                                   class-is-loaded-from-helper)))))


;;; (i-am-here) ;; Thu Jul 21 01:29:05 2005


;;; modified the consistent-state need to prove additional property of
;;; load-class2

(skip-proofs 
 (defthm consistent-state-load-class2-consistent-heap-init-state
   (implies (consistent-state s)
            (CONSISTENT-HEAP-INIT-STATE (HEAP (LOAD_CLASS2 ANY S))
                                        (INSTANCE-CLASS-TABLE (LOAD_CLASS2 ANY S))
                                        (HEAP-INIT-MAP (AUX S))))
   :hints (("Goal" :in-theory (enable load_class2)))))


;;; Thu Jul 21 01:31:32 2005!!! 


(defthm consistent-state-implies-consistent-state-load-class2-strong
  (implies (and (consistent-state s)
                (class-loaded? (super-s 
                                (mv-nth 1 (class-by-name-s any
                                             (env-class-table (env s))))) s)
                (all-interfaces-bounded? (interfaces-s 
                                          (mv-nth 1 (class-by-name-s any 
                                                                     (env-class-table (env s)))))
                                         (instance-class-table s))
                (car (class-by-name-s any (env-class-table (env s))))
                (not (class-loaded? any s))
                (no-fatal-error? s))
           (consistent-state-step (load_class2 any s)))
  :hints (("Goal" :in-theory (e/d (add-instance-class-entry
                                   instance-class-table-inv
                                   class-loaded?)
                                  (make-runtime-class-rep isClassTerm
                                                          class-is-loaded-from-helper)))))




(defthm consistent-state-implies-consistent-table
  (IMPLIES (CONSISTENT-STATE S)
           (CONSISTENT-CLASS-TABLE (INSTANCE-CLASS-TABLE S)
                                   (ENV-CLASS-TABLE (ENV S))
                                   (HEAP S)))
  :hints (("Goal" :in-theory (enable consistent-state))))

(defthm consistent-state-load-class2
  (implies (consistent-state-step (load_class2 any s))
           (consistent-state (load_class2 any s)))
  :hints (("Goal" :use ((:instance
                         consistent-state-step-implies-consistent-state
                         (s (load_class2 any s)))))))

; At last we get this proof. consistent-state is preserved by
; load_class2 when it is invoked when its guards are in some
; sense met.
;
; consistent-state-implies-consistent-state-load-class2-strong
;
; Now we also need to prove that if there is no fatal error
; during loading, the class is also loaded! 
;

(defthm consistent-state-loader-inv-helper
  (implies (and (consistent-state s)
                (no-fatal-error? s))
           (JVM::LOADER-INV-HELPER (INSTANCE-CLASS-TABLE S)
                                   (INSTANCE-CLASS-TABLE S)
                                   (ENV-CLASS-TABLE (ENV S))))
  :hints (("Goal" :in-theory (enable consistent-state
                                     instance-class-table-inv
                                     loader-inv))))


(defthm consistent-state-fatalError
  (implies (and (consistent-state s)
                any)
           (consistent-state-step (fatalError any s)))
  :hints (("Goal" :in-theory (e/d (instance-class-table-inv
                                   array-class-table-inv
                                   no-fatal-error?
                                   loader-inv) 
                                  ()))))

(defthm consistent-state-fatalError-1
  (implies (consistent-state-step (fatalError any s))
           (consistent-state (fatalError any s)))
  :hints (("Goal" :use ((:instance 
                         consistent-state-step-implies-consistent-state
                         (s (fatalError any s)))))))


                   
(defthm correctly-loaded-implies-loaded-f-2
  (implies (correctly-loaded? n (instance-class-table s)
                              (env-class-table (env s)))
           (class-loaded? n s))
  :hints (("Goal" :in-theory (e/d (class-loaded? correctly-loaded?)
                                  (isClassTerm))))
  :rule-classes :forward-chaining)
           

(defthm no-fatal-error?-load_class_x-loaded
  (implies (and (no-fatal-error? (load_class_x n s seen 2))
                (not (class-loaded? n s))
                (jvm::loader-inv-helper (instance-class-table s)
                                        (instance-class-table s)
                                        (env-class-table (env s)))
                (car (class-by-name-s n (env-class-table (env s)))))
           (class-loaded? (super-s (mv-nth 1 (class-by-name-s n
                                                              (env-class-table
                                                               (env s)))))
                          (load_class_x n s seen 2)))
  :hints (("Goal" :in-theory (e/d (class-loaded?) (JVM::load_class_x_establish_post_given_pre))
           :use ((:instance 
                  JVM::load_class_x_establish_post_given_pre
                  (JVM::p n) 
                  (JVM::seen seen)
                  (JVM::s s)
                  (JVM::mode 2))))))


(defthm no-fatal-error?-load_class_x-all-loaded-3
  (implies (and (no-fatal-error? (load_class_x n s seen 3))
                (jvm::loader-inv-helper (instance-class-table s)
                                        (instance-class-table s)
                                        (env-class-table (env s)))
                (car (class-by-name-s n (env-class-table (env s))))
                (equal (env-class-table (env s)) scl))
           (correctly-loaded? n  (INSTANCE-CLASS-TABLE (LOAD_CLASS_X n s  SEEN 3))
                              scl))
  :hints (("Goal" :in-theory (disable JVM::load_class_x_establish_post_given_pre)
           :use ((:instance 
                  JVM::load_class_x_establish_post_given_pre
                  (JVM::p n) 
                  (JVM::seen seen)
                  (JVM::s s)
                  (JVM::mode 3))))))


(acl2::set-verify-guards-eagerness 0)
(defun load_class_x_induct_0 (l s seen)
  (if (not (consp l))
      (list l s seen)
    (load_class_x_induct_0 (cdr l)
                           (load_class_x (car l) s seen 3) seen)))
(acl2::set-verify-guards-eagerness 2)    


(defthm load_class_x_still_loaded
  (implies (and (no-fatal-error? (load_class_x l s seen mode))
                (isClassTerm (class-by-name a (instance-class-table s))))
           (equal (class-by-name a (instance-class-table (load_class_x l s seen
                                                                       mode)))
                  (class-by-name a (instance-class-table s))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d (class-loaded?) (isClassTerm)))))



(defthm correctloaded-implies-isClassTerm
  (implies (correctly-loaded? n cl scl)
           (isClassTerm (class-by-name n cl)))
  :rule-classes :forward-chaining)


(defthm no-fatal-error?-load_class_x-all-loaded-3-f
  (implies (and (no-fatal-error? (load_class_x n s seen 3))
                (jvm::loader-inv-helper (instance-class-table s)
                                        (instance-class-table s)
                                        (env-class-table (env s)))
                (car (class-by-name-s n (env-class-table (env s))))
                (equal (env-class-table (env s)) scl))
           (correctly-loaded? n  (INSTANCE-CLASS-TABLE (LOAD_CLASS_X n s  SEEN 3))
                              scl))
  :rule-classes :forward-chaining)
  


(defthm load_class_x_still_loaded-interface
  (implies (and (no-fatal-error? (load_class_x l s seen mode))
                (isinterface (class-by-name a (instance-class-table s)))
                (isClassTerm (class-by-name a (instance-class-table s))))
           (isinterface (class-by-name a (instance-class-table (load_class_x l s seen mode)))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d (class-loaded?) (isClassTerm)))))


(defthm load_class_x_still_loaded-isClassTerm
  (implies (and (no-fatal-error? (load_class_x l s seen mode))
                (isClassTerm (class-by-name a (instance-class-table s))))
           (isClassTerm (class-by-name a (instance-class-table (load_class_x l s seen
                                                                       mode)))))
  :hints (("Goal" :do-not '(generalize))))



(defthm no-fatal-error?-load_class_x-all-loaded-3-collorary
  (implies (and (no-fatal-error? (load_class_x n s seen 3))
                (jvm::loader-inv-helper (instance-class-table s)
                                        (instance-class-table s)
                                        (env-class-table (env s)))
                (not (isClassTerm (class-by-name n (instance-class-table s)))))
           (isClassTerm (class-by-name n  (INSTANCE-CLASS-TABLE (LOAD_CLASS_X n
                                                                              s
                                                                              SEEN 3)))))
  :hints (("Goal" :in-theory (disable isClassTerm)
           :cases ((car (class-by-name-s n (env-class-table (env s))))))
          ("Subgoal 2" :in-theory (e/d (class-loaded? no-fatal-error?)
                                       (isClassTerm)))
          ("Subgoal 1" :in-theory (disable isClassTerm)
           :use ((:instance correctloaded-implies-isClassTerm
                            (cl (instance-class-table (load_class_x n s seen
                                                                    3)))
                            (scl (env-class-table (env s))))))))
;; COPIED FOR REFERENCE
;;
;; (defthm load-class-x-prop-implies
;;   (implies (loader-inv s)
;;            (loader-inv (load_class_x classname s seen 3)))
;;   :hints (("Goal" :use ((:instance load_class_x_establish_post_given_pre
;;                                    (p classname)
;;                                    (mode 3)))
;;            :in-theory (disable wff-state wff-class-table))))

(defthm load-class-x-prop-implies-expanded
   (implies (and (loader-inv s)
                 (no-fatal-error? (load_class_x classname s seen 3)))
            (jvm::loader-inv-helper (instance-class-table (load_class_x
                                                           classname 
                                                           s seen 3))
                                    (instance-class-table 
                                     (load_class_x classname 
                                                   s seen 3))
                                    (env-class-table (env s))))
   :hints (("Goal" :use ((:instance jvm::load-class-x-prop-implies))
            :in-theory (enable loader-inv))))



(defthm no-fatal-error?-load_class_x-all-loaded-0
  (implies (and (no-fatal-error? (load_class_x l s seen 0))
                (loader-inv s)
                (jvm::loader-inv-helper (instance-class-table s)
                                        (instance-class-table s)
                                        (env-class-table (env s))))
           (all-interfaces-bounded? l (instance-class-table (load_class_x l s
                                                                          seen
                                                                          0))))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d (class-loaded?) (no-fatal-error? fatalError isClassTerm))
           :induct (load_class_x_induct_0 l s seen))))



(defthm loader-mode-0-mode-1
  (implies 
   (and (equal (env-class-table (env s)) scl)
        (car (class-by-name-s any scl))
        (not (mem any seen))
        (all-interfaces-bounded? 
         (interfaces-s (mv-nth 1 (class-by-name-s any scl)))
         (instance-class-table (load_class_x 
                                (interfaces-s 
                                 (mv-nth 1
                                  (class-by-name-s any scl)))
                                s
                                (cons any seen) 0))))
   (all-interfaces-bounded? 
    (interfaces-s (mv-nth 1 (class-by-name-s any scl)))
    (INSTANCE-CLASS-TABLE (LOAD_CLASS_X ANY S SEEN '1))))
  :hints (("Goal" :expand   (LOAD_CLASS_X ANY S SEEN '1)
           :do-not-induct t)))


(defthm no-fatal-error?-no-fatal-error?-specific
  (implies (NO-FATAL-ERROR? (LOAD_CLASS_X ANY (LOAD_CLASS_X ANY S SEEN 2)
                                          SEEN 1))
           (NO-FATAL-ERROR?
            (LOAD_CLASS_X
             (INTERFACES-S (MV-NTH '1
                                   (CLASS-BY-NAME-S ANY (ENV-CLASS-TABLE (ENV S)))))
             (LOAD_CLASS_X ANY S SEEN '2)
             (CONS ANY SEEN)
             '0)))
  :hints (("Goal" :expand (LOAD_CLASS_X ANY (LOAD_CLASS_X ANY S SEEN 2)
                                          SEEN 1)
           :in-theory (enable no-fatal-error?))))


(defthm not-loaded-no-loaded-after-load-class-x
   (implies (and (not (class-loaded? n s))
                 (mem n seen))
            (not (class-loaded? n (load_class_x any s seen mode))))
   :hints (("Goal" :in-theory (e/d (class-loaded? no-fatal-error?)
                                   (isClassTerm))
            :do-not '(generalize)
            :induct (load_class_x any s seen mode))))



(defthm instance-class-table-make-state
  (equal (INSTANCE-CLASS-TABLE (MAKE-STATE pc 
                                           cid 
                                           hp
                                           tt
                                           (CLASS-TABLE S)
                                           env
                                           any
                                           aux))
         (instance-class-table s))
  :hints (("Goal" :in-theory (enable instance-class-table))))

(defthm class-loaded-make-state
  (equal (class-loaded? any (MAKE-STATE pc 
                                        cid
                                        hp
                                        tt
                                        (CLASS-TABLE S)
                                        env
                                        ef
                                        aux))
         (class-loaded? any s))
  :hints (("Goal" :in-theory (enable class-loaded?))))



(defthm not-loaded-notloaded-after-load-class-x-specific
  (implies (not (class-loaded? any s))
           (NOT (CLASS-LOADED? ANY
                               (LOAD_CLASS_X ANY (LOAD_CLASS_X ANY S SEEN '2)
                                             SEEN '1))))
  :hints (("Goal" :in-theory (e/d (no-fatal-error?)
                                  (isClassTerm))
           :do-not '(preprocess)
           :expand (load_class_x any (load_class_x any s seen '2) seen
                                 '1))
          ("Subgoal 4" :expand (load_class_x any s seen '2))
          ("Subgoal 2" :expand (load_class_x any s seen '2))))
          




(defthm consistent-state-load-class_x
  (implies (consistent-state s)
           (consistent-state (load_class_x any s seen mode)))
  :hints (("Goal" :in-theory (e/d (instance-class-table-inv)
                                  (fatalError
                                   consistent-state-step))
           :do-not '(generalize))
          ("Subgoal *1/6" :expand (LOAD_CLASS_X ANY (LOAD_CLASS_X ANY S SEEN '2)
                                         SEEN '1))))

;;; (defthm consistent-state-implies-consistent-state-load-class2-strong-strong
;;;   (implies (and (consistent-state s)
;;;                 (class-loaded? (super-s 
;;;                                 (mv-nth 1 (class-by-name-s any
;;;                                              (env-class-table (env s))))) s)
;;;                 (all-interfaces-bounded? (interfaces-s 
;;;                                           (mv-nth 1 (class-by-name-s any 
;;;                                                                      (env-class-table (env s)))))
;;;                                          (instance-class-table s))
;;;                 (car (class-by-name-s any (env-class-table (env s))))
;;;                 ;; (not (class-loaded? any s))
;;;                 (no-fatal-error? s))
;;;            (consistent-state-step (load_class2 any s)))
;;;   :hints (("Goal" :cases ((class-loaded? any s)))))


;;;
;;; I can either show that loading a loaded class twice is fine. as long as the 
;;; initial state is ok. 
;;;
;;; I can resolve to show that it is not possible to try to load
;;; loaded class with load_class2
;;;
;;; Wed Nov 10 18:54:12 2004. I would chose the latter!! 
;;;  


;;; (defthm reference-type-not-affected-by-addition-of-new-class
;;;   (implies (reference-type-s type cl)
;;;            (reference-type-s type (cons class-rep cl))))

;;; ;; (defthm valid-type-s-not-affected-by-addition-of-new-class
;;; ;;   (implies (and (valid-type-s type cl mode)
;;; ;;                 (not (isClassTerm (class-by-name (classname class-rep) cl))))
;;; ;;            (valid-type-s type (cons class-rep cl) mode)))


;;; ;; (skip-proofs 
;;; ;;  (local 
;;; ;;   (defthm valid-type-s-normalization
;;; ;;     (and (equal (reference-type-s type1 cl)
;;; ;;                 (valid-type-s type1 cl 1))
;;; ;;          (equal (array-type-s type2 cl)
;;; ;;                 (valid-type-s type2 cl 0))))))


;;; ;; (defthm reference-type-not-affected-by-addition-of-new-class
;;; ;;    (implies (and (reference-type-s type cl)
;;; ;;                  (not (isClassTerm (class-by-name (classname class-rep) cl))))
;;; ;;             (reference-type-s type (cons class-rep cl))))

;;; ;; (defthm array-type-not-affected-by-addition-of-new-class
;;; ;;    (implies (and (array-type-s type cl)
;;; ;;                  (not (isClassTerm (class-by-name (classname class-rep) cl))))
;;; ;;             (array-type-s type (cons class-rep cl))))


;;; ;; (local (in-theory (disable valid-type-s-normalization)))


;;; ;; (defthm isjavasubclass1-not-affected-by-addition-of-new-class
;;; ;;   (implies (and (isJavaSubclassof1 rtype type cl seen)
;;; ;;                 (not (isclassterm (class-by-name (classname class-rep)
;;; ;;                                                  cl)))
;;; ;;                 (consistent-class-hierachy (cons class-rep cl)))
;;; ;;            (isjavasubclassof1 rtype type (cons class-rep cl) seen))
;;; ;;   :hints (("Goal" :do-not '(generalize)
;;; ;;            :in-theory (disable isclassterm))
;;; ;;           ("Subgoal *1/4" :expand 
;;; ;;            (ISJAVASUBCLASSOF1 RTYPE TYPE (CONS CLASS-REP CL) seen))))


;;; ;; (defthm isJavaAssignmentcompatible-not-affected-by-addition-of-new-class
;;; ;;   (implies (and (isJavaAssignmentCompatible rtype type cl)
;;; ;;                 (consistent-class-hierachy (cons class-rep cl))
;;; ;;                 (not (isClassTerm (class-by-name (classname class-rep) cl))))
;;; ;;            (isJavaAssignmentcompatible rtype type (cons class-rep cl)))
;;; ;;   :hints (("Goal" :in-theory (e/d (isJavaAssignmentcompatible)
;;; ;;                                   (isClassTerm))
;;; ;;            :do-not '(generalize))))


;;; ;; (defthm Assignmentcompatible-not-affected-by-addition-of-new-class
;;; ;;   (implies (and (AssignmentCompatible rtype type cl)
;;; ;;                 (consistent-class-hierachy (cons class-rep cl))
;;; ;;                 (not (isClassTerm (class-by-name (classname class-rep) cl))))
;;; ;;            (Assignmentcompatible rtype type (cons class-rep cl)))
;;; ;;   :hints (("Goal" :in-theory (enable Assignmentcompatible))))


;;; ;; (defthm consistent-value-not-affected-addition-of-new-class
;;; ;;   (implies (and (consistent-class-hierachy (cons class-rep cl))
;;; ;;                 (consistent-value tagged-value type cl hp)
;;; ;;                 (not (isClassTerm (class-by-name (classname class-rep) cl))))
;;; ;;            (consistent-value tagged-value type (cons class-rep cl) hp))
;;; ;;   :hints (("Goal" :in-theory (enable consistent-value))))





;;; ;; ;;;
;;; ;; ;;; judgment about consistent-value does not change after introducing a new
;;; ;; ;;; class definition!! 
;;; ;; ;;; 
;;; ;; ;;; Dynamic class loading is fine. Mon Nov  1 19:20:47 2004
;;; ;; ;;;


;;; ;; (defthm consistent-state-add-instance-class-table
;;; ;;   (implies (and (consistent-state s)
;;; ;;                 (equal (pc s) pc)
;;; ;;                 (equal (current-thread s) cid)
;;; ;;                 (equal (thread-table s) tt)
;;; ;;                 (equal (instance-class-table s) cl)
;;; ;;                 (equal (array-class-table s) acl)
;;; ;;                 (equal (env s) env)
;;; ;;                 (equal (error-flag s) ef)
;;; ;;                 (equal (aux s) aux)
;;; ;;                 (not (class-loaded? (classname class-rep) s))
;;; ;;                 (class-loaded? (super class-rep) s)
;;; ;;                 (WFF-METHODS-INSTANCE-CLASS-REP class-rep)
;;; ;;                 (jvm::all-loaded? (interfaces class-rep) s)
;;; ;;                 (consistent-class-decl class-rep cl (heap s)))
;;; ;;            (consistent-state-step
;;; ;;                              (MAKE-STATE
;;; ;;                                 pc cid (heap s)
;;; ;;                                 tt (make-class-table 
;;; ;;                                     (add-instance-class-entry class-rep
;;; ;;                                                               cl)
;;; ;;                                     acl)
;;; ;;                                 env
;;; ;;                                 ef
;;; ;;                                 aux)))
;;; ;;   :hints (("Goal" :in-theory (enable 
;;; ;;                               wff-methods-instance-class-table-strong
;;; ;;                               add-instance-class-entry))))
                              
                              


;;; ;; (defthm consistent-state-weak-implies-consistent-state-weak-load-class2
;;; ;;   (implies (consistent-state s)
;;; ;;            (consistent-state-step (load_class2 any s)))
;;; ;;   :hints (("Goal" :in-theory (e/d (load_class2 aux-set-trace)
;;; ;;                                   (consistent-state-step)))))




;;; (defthm consistent-heap-array-init-state-load-cp-entry
;;;   (implies (and ;; (consistent-state s) 
;;;                 ;; we do not need such a strong
;;;                 ;; to use the theorem, we need then to 
;;;                 ;; prove consistent-state!! 
;;;                 ;;
;;;                 ;; load_cp_entries!!
;;;                 ;; Sun Oct 31 20:15:40 2004?? 
;;;                 ;; Shall we weaken the hyps? 
;;;                 (boot-strap-class-okp s)
;;;                 (consistent-heap (heap s) 
;;;                 (consistent-heap-array-init-state (heap s)
;;;                                                   (instance-class-table s)
;;;                                                   (array-class-table s) 
;;;                                                   (heap-init-map (aux s))))
;;;            (consistent-heap-array-init-state (heap (mv-nth 1 (load_cp_entry cp s)))
;;;                                              (instance-class-table s)
;;;                                              (array-class-table s)
;;;                                              (heap-init-map (aux s))))
;;;   :hints (("Goal" :in-theory (e/d (load_cp_entry) (consistent-object))
;;;            :restrict ((consistent-heap-implies-not-bound?-len
;;;                        ((cl (instance-class-table s))
;;;                         (acl (array-class-table s))))))))
 

;;; the above is not true, we will need to assert that the keys in heap-init,
;;; are always keys in heap.
;;; 

;;; (defthm consistent-heap-array-init-state-if-new-object-is-not-array
;;;   (implies (and (consistent-heap-array-init-state hp cl acl hp-init)
;;;                 (not (isArrayType (obj-type obj))))
;;;            (consistent-heap-array-init-state (bind ref obj hp)
;;;                                              cl acl hp-init)))


;;; (defthm consistent-heap-array-init-state-extending-class-table
;;;   (implies (and (consistent-heap-array-init-state hp cl acl hp-init)
;;;                 (isClassTerm class-rep))
;;;            (consistent-heap-array-init-state hp (add-instance-class-entry 
;;;                                                    class-rep cl) acl hp-init)))



;;; ;; (defthm consistent-thread-entry-if-new-object
;;; ;;   (implies (and (consistent-thread-entry th cl hp)
;;; ;;                 (not (bound? ref hp)))
;;; ;;            (consistent-thread-entry th cl (bind ref obj hp))))
                                                   


;;; ;; ;; (defthm load_class2-preserve-consistency-weak
;;; ;; ;;   (implies (consistent-state-step s)
;;; ;; ;;            (consistent-state-step  (load_class2 any s)))
;;; ;; ;;   :hints (("Goal" :in-theory (e/d (load_class2)
;;; ;; ;;                                   (make-runtime-class-rep)))))








;;; ;; (skip-proofs 
;;; ;;  (defthm class-loaded-implies-collect-super-no-change
;;; ;;    (implies (class-loaded? any s)
;;; ;;             (equal (collect-superclass-list1 any (instance-class-table (load_class_x anyx s seen mode))
;;; ;;                                              seen2)
;;; ;;                    (collect-superclass-list1 any (instance-class-table s)
;;; ;;                                              seen2)))))

;;; ;; (skip-proofs 
;;; ;;  (defthm class-loaded-implies-super-no-change
;;; ;;    (implies (class-loaded? any s)
;;; ;;             (equal (class-by-name any (instance-class-table (load_class_x anyx s seen mode)))
;;; ;;                    (class-by-name any (instance-class-table s))))))


;;; ;; (defthm load_class_x-preserve-consistentcy
;;; ;;   (IMPLIES
;;; ;;    (CONSISTENT-STATE S)
;;; ;;    (CONSISTENT-STATE 
;;; ;;     (load_class_x any s seen 3)))
;;; ;;   :hints (("Goal" :do-not '(generalize)
;;; ;;            :in-theory (e/d (consistent-state
;;; ;;                             build-a-java-visible-instance-guard)
;;; ;;                            (loader-inv)))))
 


;;; may need to update the definition of
;;; jvm::equiv-state-except-thread-and-trace to assert (heap-init-map (aux ...))
;;; being equal
;;;
;;;      JVM::EQUIV-STATE-EXCEPT-THREAD-AND-TRACE-IMPLIES-EQUIV-STATE-EXCEPT-THREAD-AND-TRACE-LOAD_CLASS_X-2)
;;; 

;;;; 

;;; (defthm equal-heap-init-map-aux-load_cp_entry
;;;   (equal (heap-init-map (aux (mv-nth 1 (load_cp_entry any (state-set-current-thread anyx s)))))
;;;          (heap-init-map (aux (mv-nth 1 (load_cp_entry any s)))))
;;;   :hints (("Goal" :in-theory (enable load_cp_entry heap-init-map))))



;;; (defthm load_cp_entry_implies-equiv-state-lemma
;;;   (implies (JVM::equiv-state-except-thread-and-trace s2 s1)
;;;            (JVM::EQUIV-STATE-EXCEPT-THREAD-AND-TRACE
;;;             (slot (LOAD_CP_ENTRY ANY1 S2))
;;;             (MV-NTH 1 (LOAD_CP_ENTRY ANY1 S1)))))


;;; (defthm equal-heap-init-map-aux-load_cp_entries-lemma
;;;   (implies (and (JVM::equiv-state-except-thread-and-trace s2 s1)
;;;                 (equal (heap-init-map (aux s2))
;;;                        (heap-init-map (aux s1))))
;;;            (equal (heap-init-map (aux (mv-nth 1 (load_cp_entries any s2))))
;;;                   (heap-init-map (aux (mv-nth 1 (load_cp_entries any s1))))))
;;;   :hints (("Goal" :do-not '(generalize))))


;;; (defthm equal-heap-init-map-aux
;;;   (equal (heap-init-map (aux (load_class2 any (state-set-current-thread any s))))
;;;          (heap-init-map (aux (load_class2 any s))))
;;;   :hints (("Goal" :in-theory (enable load_class2))))


(defthm load_class_x-state-set-current-thread-equal
  (and (equal (heap (load_class_x any (state-set-current-thread anyth s) seen
                                  mode))
              (heap (load_class_x any s seen mode)))
       (equal (instance-class-table (load_class_x any 
                                                  (state-set-current-thread
                                                   anyth s) seen mode))
              (instance-class-table (load_class_x any s seen mode)))
       (equal (class-table (load_class_x any 
                                                  (state-set-current-thread
                                                   anyth s) seen mode))
              (class-table (load_class_x any s seen mode)))
       (equal (array-class-table (load_class_x any 
                                                  (state-set-current-thread
                                                   anyth s) seen mode))
              (array-class-table (load_class_x any s seen mode)))
       (equal (thread-table (load_class_x any 
                                                  (state-set-current-thread
                                                   anyth s) seen mode))
              (thread-table (load_class_x any s seen mode)))
       (equal (env (load_class_x any (state-set-current-thread
                                                  anyth s) seen mode))
              (env (load_class_x any s seen mode)))
       (equal (heap-init-map (aux (load_class_x any (state-set-current-thread
                                                     anyth s) seen mode)))
              (heap-init-map (aux (load_class_x any s seen mode))))))
                                    
(defthm consistent-state-implies-alist-heap-init-map
  (IMPLIES (CONSISTENT-STATE S)
           (ALISTP (HEAP-INIT-MAP (AUX s)))))

(defthm consistent-state-wff-methods
  (IMPLIES (CONSISTENT-STATE S)
           (WFF-METHODS-INSTANCE-CLASS-TABLE-STRONG
            (INSTANCE-CLASS-TABLE s))))

(defthm consistent-state-class-hierachy
  (IMPLIES (CONSISTENT-STATE S)
           (CONSISTENT-CLASS-HIERACHY
              (INSTANCE-CLASS-TABLE s))))


(defthm consistent-class-consistent-class-table
  (implies (and (CONSISTENT-STATE S)
                (equal (env-class-table (env s)) scl))
           (CONSISTENT-CLASS-TABLE (INSTANCE-CLASS-TABLE s)
                                   scl
                                   (HEAP s))))


(defthm consistent-class-consistent-threads
  (implies (and (CONSISTENT-STATE S)
                (equal (thread-table s) tt))
           (consistent-thread-entries tt
                                      (INSTANCE-CLASS-TABLE s)
                                      (HEAP s))))



(defthm array-class-table-inv-set-thread-id
  (implies (array-class-table-inv s)
           (array-class-table-inv (state-set-current-thread any s)))
  :hints (("Goal" :in-theory (enable array-class-table-inv))))


(defthm boot-strap-class-okp-set-thread-id
  (implies (boot-strap-class-okp s)
           (boot-strap-class-okp (state-set-current-thread any s)))
  :hints (("Goal" :in-theory (enable boot-strap-class-okp))))


(defthm pc-does-not-change
  (equal (pc (load_class_x any s seen mode))
         (pc s)))

(defthm wff-state-load-independent-of-thread-x
  (implies (wff-state s)
           (wff-state (LOAD_CLASS_X any s seen mode))))


(defthm build-immediate-instance-data-guard-load-independent-of-thread
  (implies (and (wff-state s)
                (build-immediate-instance-data-guard l (LOAD_CLASS_X ANY s SEEN
                                                                     MODE)))
                (build-immediate-instance-data-guard l (LOAD_CLASS_X ANY 
                                                                     (state-set-current-thread anyid s)
                                                                     seen mode)))
  :hints (("Goal" :in-theory (e/d (build-a-java-visible-instance-data-guard)
                                  (load_class_x)))))



(defthm build-a-java-visible-instance-guard-load-independent-of-thread
  (implies (and (wff-state s)
                (BUILD-A-JAVA-VISIBLE-INSTANCE-DATA-GUARD l (LOAD_CLASS_X ANY s SEEN
                                                                          MODE)))
           (BUILD-A-JAVA-VISIBLE-INSTANCE-DATA-GUARD l (LOAD_CLASS_X ANY 
                                                                     (state-set-current-thread anyid s)
                                                                     seen mode)))
  :hints (("Goal" :in-theory (e/d (build-a-java-visible-instance-data-guard)
                                  (load_class_x
                                   build-immediate-instance-data-guard)))))



(defthm boot-strap-class-okp-load-independent-of-thread
  (implies (and (boot-strap-class-okp (load_class_x any s seen mode))
                (wff-state s))
           (boot-strap-class-okp (load_class_x any (state-set-current-thread
                                                    anyid s) seen mode)))
  :hints (("Goal" :in-theory (e/d (boot-strap-class-okp)
                                  (load_class_x)))))


(defthm arrayclassloaded?-loaded-independent-of-current-thread
  (implies (JVM::ARRAYCLASSLOADED? l (LOAD_CLASS_X ANY s SEEN MODE))
           (JVM::ARRAYCLASSLOADED? l (LOAD_CLASS_X ANY
                                                   (state-set-current-thread cid S) SEEN MODE)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (disable load_class_x))))


(defthm class-loaded?-loaded-independent-of-current-thread
  (implies (class-loaded? any (LOAD_CLASS_X ANY s SEEN MODE))
           (class-loaded? any (LOAD_CLASS_X ANY
                                            (state-set-current-thread cid S) SEEN MODE)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d (class-loaded?) (load_class_x)))))




(defthm array-correctly-loaded-loaded-independent-of-current-thread
  (implies (JVM::ARRAY-CLASS-CORRECTLY-LOADED? l (LOAD_CLASS_X ANY s SEEN MODE))
           (JVM::ARRAY-CLASS-CORRECTLY-LOADED? l
                                               (LOAD_CLASS_X ANY
                                                             (state-set-current-thread cid S) SEEN MODE)))
  :hints (("Goal" :do-not '(generalize)
           :in-theory (e/d () (jvm::arrayclassloaded?
                               class-loaded?
                               load_class_x)))))

(defthm array-class-table-inv-helper-load-independent-of-thread
  (implies (jvm::array-class-table-inv-helper l (load_class_x any s seen mode))
           (jvm::array-class-table-inv-helper l (load_class_x any
                                                              (state-set-current-thread cid s) seen mode)))
  :hints (("Goal" :in-theory (e/d (jvm::array-class-table-inv-helper
                                   loader-inv)
                                  (load_class_x))
           :do-not '(generalize))))


(defthm array-class-table-inv-load-independent-of-thread
  (implies (and (wff-state s)
                (array-class-table-inv (load_class_x any s seen mode)))
           (array-class-table-inv (load_class_x any (state-set-current-thread
                                                     anyid s) seen mode)))
  :hints (("Goal" :in-theory (e/d (array-class-table-inv
                                   loader-inv)
                                  (load_class_x)))))



(defthm consistent-state-implies-array-class-table-inv-b
  (implies (consistent-state s)
           (array-class-table-inv s))
  :hints (("Goal" :in-theory (e/d (consistent-state)
                                  (array-class-table-inv)))))

(defthm consistent-state-implies-bootstrap-class-ok
  (implies (consistent-state s)
           (boot-strap-class-okp s))
  :hints (("Goal" :in-theory (e/d (consistent-state)
                                  (boot-strap-class-okp)))))
  

(defthm consistent-state-java-lang-Object-correctly-loaded
  (IMPLIES (boot-strap-class-okp s)
           (CLASS-LOADED? "java.lang.Object" s))
  :hints (("Goal" :in-theory (enable boot-strap-class-okp))))

(defthm load_class-preserve-consistency
  (implies (consistent-state s)
           (consistent-state-step (load_class any s)))
  :hints (("Goal" :in-theory (enable load_class class-loaded? 
                                     instance-class-table-inv))))



(defthm load_class-preserve-consistency-1
  (implies (consistent-state-step (load_class any s))
           (consistent-state (load_class any s)))
  :hints (("Goal" :use ((:instance
                         consistent-state-step-implies-consistent-state
                         (s (load_class any s)))))))


; At last we proved that load_class preserve consistent-state
; However class loader also loads array classes!! 
; we move on to prove that. 

(defthm consistent-heap-array-init1-bind-non-array
  (implies (consistent-heap-array-init-state1 hp cl acl hp-init)
           (consistent-heap-array-init-state1 (bind any
                                                   (LIST* 'OBJECT
                                                          '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                                                                        "java.lang.Class")
                                                          (LIST 'SPECIFIC-INFO
                                                                'ARRAY_CLASS
                                                                (LIST 'ARRAY ANYX))
                                                          '((("java.lang.Class")
                                                             ("java.lang.Object"))))
                                                   hp)
                                             cl 
                                             acl hp-init)))



(defthm consistent-heap-array-init2-bind-non-array
  (implies (consistent-heap-array-init-state2 hp hp-init)
           (consistent-heap-array-init-state2 (bind any
                                                   (LIST* 'OBJECT
                                                          '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                                                                        "java.lang.Class")
                                                          (LIST 'SPECIFIC-INFO
                                                                'ARRAY_CLASS
                                                                (LIST 'ARRAY ANYX))
                                                          '((("java.lang.Class")
                                                             ("java.lang.Object"))))
                                                   hp)
                                             hp-init)))



(defthm consistent-heap-array-init3-bind-non-array
  (implies (consistent-heap-array-init-state3 hp hp-init)
           (consistent-heap-array-init-state3 (bind any
                                                   (LIST* 'OBJECT
                                                          '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                                                                        "java.lang.Class")
                                                          (LIST 'SPECIFIC-INFO
                                                                'ARRAY_CLASS
                                                                (LIST 'ARRAY ANYX))
                                                          '((("java.lang.Class")
                                                             ("java.lang.Object"))))
                                                   hp)
                                             hp-init)))







(defthm consistent-heap-array-init-bind-non-array
  (implies (consistent-heap-array-init-state hp cl acl hp-init)
           (consistent-heap-array-init-state (bind any
                                                   (LIST* 'OBJECT
                                                          '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                                                                        "java.lang.Class")
                                                          (LIST 'SPECIFIC-INFO
                                                                'ARRAY_CLASS
                                                                (LIST 'ARRAY ANYX))
                                                          '((("java.lang.Class")
                                                             ("java.lang.Object"))))
                                                   hp)
                                             cl 
                                             acl hp-init))
  :hints (("Goal" :in-theory (enable consistent-heap-array-init-state))))



(defthm heap-init-map-aux-set-trace
  (equal (heap-init-map (aux-set-trace any aux))
         (heap-init-map aux)))




(defthm valid-array-type-valid-array-type
  (implies    (VALID-ARRAY-TYPE obj CL ACL)
              (VALID-ARRAY-TYPE obj CL
                                (CONS (LIST (LIST 'ARRAY ANY)
                                            anyaccessflag
                                            ANYX)
                                      ACL)))
  :hints (("Goal" :in-theory (enable valid-array-type))))



(defthm consistent-heap-array-init-bind-non-array-2-1
  (implies (consistent-heap-array-init-state1 hp cl acl hp-init)
           (consistent-heap-array-init-state1 hp cl
                                              (CONS (LIST (LIST 'ARRAY ANY)
                                                          anyaccessflag
                                                          anyx) 
                                                    acl)
                                              hp-init))
  :hints (("Goal" :in-theory (enable consistent-heap-array-init-state)
           :do-not '(generalize))))


(defthm consistent-heap-array-init-bind-non-array-2
  (implies (consistent-heap-array-init-state hp cl acl hp-init)
           (consistent-heap-array-init-state hp cl
                                             (CONS (LIST (LIST 'ARRAY ANY)
                                                         anyaccessflag
                                                         anyx) 
                                                   acl)
                                             hp-init))
  :hints (("Goal" :in-theory (enable consistent-heap-array-init-state))))


(defthm load_array_class2-preserve-consistency-subgoal-10
  (implies (consistent-state s)
           (ALISTP (HEAP-INIT-MAP (AUX (LOAD_ARRAY_CLASS2 ANY S)))))
  :hints (("Goal" :in-theory (enable load_array_class2))))


(defthm equal-instance-class-table-load_array_class2
  (equal (instance-class-table (load_array_class2 any s))
         (instance-class-table s))
  :hints (("Goal" :in-theory (enable load_array_class2))))


;----------------------------------------------------------------------
; FIX LATER. This is not a small skip proof

(skip-proofs 
  (defthm consistent-heap-change-array-class-table
    (implies (and (consistent-heap hp cl (array-class-table s))
                  (not (arrayclassloaded? any s)))
             (consistent-heap hp cl (cons (cons (list 'array any) anyx)
                                          (array-class-table s))))))

;----------------------------------------------------------------------



(skip-proofs 
 (defthm consistent-object-is-created-by-load-array-class2
   (implies (consistent-state s)
            (CONSISTENT-OBJECT
             (CONS 'OBJECT
                   (CONS '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
                                       "java.lang.Class")
                         (CONS (CONS 'SPECIFIC-INFO
                                     (CONS 'ARRAY_CLASS
                                           (CONS (CONS 'ARRAY (CONS ANY 'NIL))
                                                 'NIL)))
                               '((("java.lang.Class")
                                  ("java.lang.Object"))))))
             (HEAP S)
             (INSTANCE-CLASS-TABLE S)))))


(defthm load_array_class2-preserve-consisteny-subgoal-heap
  (IMPLIES (and (CONSISTENT-STATE S)
                (not (arrayclassloaded? any s)))
           (CONSISTENT-HEAP (HEAP (LOAD_ARRAY_CLASS2 ANY S))
                            (INSTANCE-CLASS-TABLE s)
                            (ARRAY-CLASS-TABLE (LOAD_ARRAY_CLASS2 ANY S))))
  :hints (("Goal" :in-theory (enable load_array_class2))))



(defthm load_array_class2-preserve-consisteny-subgoal-heap-init
  (IMPLIES (CONSISTENT-STATE S)
           (CONSISTENT-HEAP-ARRAY-INIT-STATE
            (HEAP (LOAD_ARRAY_CLASS2 ANY S))
            (INSTANCE-CLASS-TABLE s)
            (ARRAY-CLASS-TABLE (LOAD_ARRAY_CLASS2 ANY S))
            (HEAP-INIT-MAP (AUX (LOAD_ARRAY_CLASS2 ANY S)))))
   :hints (("Goal" :in-theory (enable load_array_class2))))


(defthm load_array_class2-preserve-consisteny-subgoal-consistent-class-table
  (IMPLIES
   (CONSISTENT-STATE S)
   (CONSISTENT-CLASS-TABLE (INSTANCE-CLASS-TABLE s)
                           (ENV-CLASS-TABLE (ENV S))
                           (HEAP (LOAD_ARRAY_CLASS2 ANY S))))
   :hints (("Goal" :in-theory (enable load_array_class2
                                      consistent-class-table))))


(defthm load_array_class2-preserve-consisteny-subgoal-thread-entry
  (IMPLIES
   (CONSISTENT-STATE S)
   (CONSISTENT-THREAD-ENTRIES (THREAD-TABLE S)
                              (INSTANCE-CLASS-TABLE s)
                              (HEAP (LOAD_ARRAY_CLASS2 ANY S))))
   :hints (("Goal" :in-theory (enable load_array_class2))))



(defthm boot-strap-class-okp-bootstrap-class-ok
  (IMPLIES
   (boot-strap-class-okp s)
   (boot-strap-class-okp (LOAD_ARRAY_CLASS2 ANY S)))
   :hints (("Goal" :in-theory (enable load_array_class2 class-loaded?
                                      boot-strap-class-okp))))




(defthm load_array_class2-preserve-consisteny-subgoal-bootstrap-class-ok
  (IMPLIES
   (CONSISTENT-STATE S)
   (boot-strap-class-okp (LOAD_ARRAY_CLASS2 ANY S)))
  :hints (("Goal" :in-theory (disable load_array_class2))))

(skip-proofs 
 (defthm load_array_class2-preserve-consisteny-heap-init-state
   (IMPLIES (AND (CONSISTENT-STATE S)
                 (JVM::LOAD_ARRAY_CLASS2-GUARD ANY S))
            (CONSISTENT-HEAP-INIT-STATE (HEAP (LOAD_ARRAY_CLASS2 ANY S))
                                        (INSTANCE-CLASS-TABLE S)
                                        (HEAP-INIT-MAP (AUX S))))))


(defthm class-loaded-class-loaded
  (implies (class-loaded? any s)
           (class-loaded? any (load_array_class2 anyx s)))
  :hints (("Goal" :in-theory (enable load_array_class2 class-loaded?))))


(in-theory (disable load_array_class2))


;; (defthm array-class-correctly-loaded-make-state-reduce
;;   (equal (JVM::ARRAY-CLASS-CORRECTLY-LOADED? l 
;;                                              (MAKE-STATE
;;                                               anypc 
;;                                               anythread
;;                                               heap
;;        (PC S)
;;        (CURRENT-THREAD S)
;;        (BIND (LEN (HEAP S))
;;              (LIST* 'OBJECT
;;                     '(COMMON-INFO 0 (MONITOR -1 0 NIL NIL)
;;                                   "java.lang.Class")
;;                     (LIST 'SPECIFIC-INFO
;;                           'ARRAY_CLASS
;;                           (LIST 'ARRAY ANY))
;;                     '((("java.lang.Class")
;;                        ("java.lang.Object"))))
;;              (HEAP S))
;;        (THREAD-TABLE S)
;;        (MAKE-CLASS-TABLE
;;             (INSTANCE-CLASS-TABLE S)
;;             (CONS (LIST (LIST 'ARRAY ANY)
;;                         '(ACCESSFLAGS *FINAL*
;;                                       *ABSTRACT* JVM::*ARRAY_CLASS* *PUBLIC*)
;;                         (LEN (HEAP S)))
;;                   (ARRAY-CLASS-TABLE S)))
;;        (ENV S)
;;        (ERROR-FLAG S)
;;        (AUX-SET-TRACE (ACL2::G 'TRACE (AUX S))
;;                       (AUX S))))).

;;; skip for now. Fri May 27 16:07:40 2005. should work
;;; 
;;; Fri May 27 17:09:14 2005


(skip-proofs 
 (defthm load_array_class2-preserve-consisteny-subgoal-array-table-inv
   (IMPLIES
    (and (CONSISTENT-STATE S)
         (jvm::load_array_class2-guard any s))
    (array-class-table-inv (LOAD_ARRAY_CLASS2 ANY S)))
   :hints (("Goal" :in-theory (e/d (class-loaded? 
                                    load_array_class2
                                    array-class-table-inv)
                                   (array-type?
                                    primitive-type?
                                    arrayclassloaded?
                                    ))))))


;; (skip-proofs 
;;  (defthm load_array_class2-preserve-consisteny-subgoal-array-table-inv
;;    (IMPLIES
;;     (and (CONSISTENT-STATE S)
;;          (jvm::load_array_class2-guard any s))
;;     (array-class-table-inv (LOAD_ARRAY_CLASS2 ANY S)))
;;    :hints (("Goal" :in-theory (enable load_array_class2
;;                                       array-class-table-inv)))))


(defthm load_array_class2-change-no-env
  (equal (ENV (LOAD_ARRAY_CLASS2 ANY S))
         (env s))
  :hints (("Goal" :in-theory (enable load_array_class2))))

(defthm load_array_class2-change-no-heap-init-map
  (equal (HEAP-INIT-MAP (AUX (LOAD_ARRAY_CLASS2 ANY S)))
         (heap-init-map (aux s)))
  :hints (("Goal" :in-theory (enable load_array_class2))))



(defthm load_array_class2-preserve-consisteny-subgoal-heap-init-specific
  (IMPLIES (CONSISTENT-STATE S)
           (CONSISTENT-HEAP-ARRAY-INIT-STATE
            (HEAP (LOAD_ARRAY_CLASS2 ANY S))
            (INSTANCE-CLASS-TABLE s)
            (ARRAY-CLASS-TABLE (LOAD_ARRAY_CLASS2 ANY S))
            (HEAP-INIT-MAP (AUX s))))
   :hints (("Goal" :in-theory (enable load_array_class2))))


(defthm load_array_class2-implies-not-arrayclassloaded?
  (implies (jvm::load_array_class2-guard any s)
           (not (arrayclassloaded? any s))))


;; (i-am-here) ;; Thu Jul 21 12:57:02 2005

;;;
;;; need to add a skip proof that 
;;; load class preserve consistent-heap-init-state



(defthm load_array_class2-preserve-consistency
  (implies (and (consistent-state s)
                (JVM::load_array_class2-guard any s))
           (consistent-state-step (load_array_class2 any s)))
  :hints (("Goal" :in-theory (e/d (instance-class-table-inv 
                                   class-loaded?
                                   ) (jvm::load_array_class2-guard)))))

(defthm consistent-state-load_array_class2
  (implies (consistent-state-step (load_array_class2 any s))
           (consistent-state (load_array_class2 any s)))
  :hints (("Goal" :use ((:instance 
                         consistent-state-step-implies-consistent-state
                         (s (load_array_class2 any s)))))))

(defthm load_array_class2-preserve-consistency-actual
  (implies (and (consistent-state s)
                (JVM::load_array_class2-guard any s))
           (consistent-state (load_array_class2 any s)))
  :hints (("Goal" :use load_array_class2-preserve-consistency
           :in-theory (disable consistent-state-step 
                               jvm::load_array_class2-guard
                               load_array_class2))))


;; (defthm instance-class-table-inv-preserved
;;   (implies (instance-class-table-inv s)
;;            (INSTANCE-CLASS-TABLE-INV
;;             (STATE-SET-CURRENT-THREAD (CURRENT-THREAD S) s)))
;;   :hints (("Goal" :in-theory (enable instance-class-table-inv
;;                                      state-set-current-thread
;;                                      loader-inv))))
                                     
                                    

;; (defthm consistent-state-state-set-current-thread
;;   (implies (and (consistent-state s)
;;                 (thread-exists? id (thread-table s)))
;;            (consistent-state 
;;             (state-set-current-thread id s)))
;;   :hints (("Goal" :in-theory (enable consistent-state
;;                                      instance-class-table-inv
;;                                      ))))


(defthm load_class-preserve-consistency-general
  (implies (consistent-state s)
           (consistent-state (load_class any s)))
  :hints (("Goal" :in-theory (disable load_class consistent-state-step))))


(defthm wff-state-consistent-state
  (implies (consistent-state s)
           (wff-state s)))

(defthm alistp-heap-consistent-state
  (implies (consistent-state s)
           (alistp (heap s))))

(defthm alistp-heap-consistent-state
  (implies (consistent-state s)
           (alistp (heap s))))

(defthm wff-class-table-consistent-state
  (implies (consistent-state s)
           (wff-class-table (class-table s))))

(defthm wff-instance-class-table-consistent-state
  (implies (consistent-state s)
           (wff-instance-class-table (instance-class-table s))))

(defthm wff-array-class-table-consistent-state
  (implies (consistent-state s)
           (WFF-ARRAY-CLASS-TABLE (ARRAY-CLASS-TABLE s))))

(defthm array-class-table-load-class-no-change
  (equal (array-class-table (load_class any s))
         (array-class-table s))
  :hints (("Goal" :in-theory (enable load_class))))

(defthm array-class-table-inv-array-class-table-inv
  (implies (JVM::ARRAY-CLASS-TABLE-INV-HELPER
            (JVM::ALL-ARRAY-SIGS (ARRAY-CLASS-TABLE s)) s)
           (jvm::array-class-table-inv-helper
            (jvm::all-array-sigs (array-class-table s))
            (load_class any s)))
  :hints (("Goal" :in-theory (enable jvm::array-class-table-inv-helper load_class))))



(defthm no-fatal-error?-load-class-load
  (implies (no-fatal-error? (load_class any s))
           (class-loaded? any (load_class any s)))
  :hints (("Goal" :in-theory (enable load_class))))




(defthm array-class-table-state-set-array-class-table
  (equal (array-class-table (state-set-array-class-table acl s))
         acl))

(defthm wff-array-class-rep-load-array-class2
  (WFF-ARRAY-CLASS-TABLE-REP
   (ARRAY-CLASS-BY-NAME (make-array-type any)
                        (ARRAY-CLASS-TABLE (LOAD_ARRAY_CLASS2 any S))))
  :hints (("Goal" :expand (load_array_class2 any s))))



(defthm wff-array-class-rep-load-array-class2-specific
  (implies (array-type? any)
           (WFF-ARRAY-CLASS-TABLE-REP
            (ARRAY-CLASS-BY-NAME any
                                 (ARRAY-CLASS-TABLE 
                                  (LOAD_ARRAY_CLASS2
                                   (array-base-type any) S)))))
  :hints (("Goal" :use ((:instance wff-array-class-rep-load-array-class2
                                   (any (array-base-type any))))
           :in-theory (e/d (array-base-type) (wff-array-class-table-rep)))))



(defthm load_array_class-loaded-if-no-error-loaded-1
  (implies (and (consistent-state s)
                (no-fatal-error? s)
                (no-fatal-error? (load_array_class (array-base-type any) s))
                (array-type? any))
           (WFF-ARRAY-CLASS-TABLE-REP
            (ARRAY-CLASS-BY-NAME any
                                 (ARRAY-CLASS-TABLE 
                                  (LOAD_ARRAY_CLASS
                                   (array-base-type any) s)))))
  :hints (("Goal" :in-theory (e/d (load_array_class)
                                  (wff-array-class-table-rep
                                   array-type?))
           :expand (load_array_class (array-base-type any) s))))


; (skip-proofs  
;  (defthm load_array_class-loaded-if-no-error-loaded
;   (implies (and (consistent-state s)
;                 (array-type? any)
;                 ;; (not (arrayclassloaded? any s))
;                 (no-fatal-error? (load_array_class any s)))
;            (WFF-ARRAY-CLASS-TABLE-REP
;             (ARRAY-CLASS-BY-NAME any
;                                  (ARRAY-CLASS-TABLE (LOAD_ARRAY_CLASS any s)))))
;   :hints (("Goal" :in-theory (enable load_array_class 
;                                      make-array-type
;                                      wff-array-class-table-rep)))))

; ;;; this is true:
; ;;;; because: 
; ;;;;
; ;;;; 1) if (array any) already loaded, must have been loaded correctly
; ;;;  2) if not. 
; ;;;       load_array_class2 should have been called to any
; ;;;       then (array-class-by-name '(array any) should have been loaded
; ;;;  Because load_array_class preserve invariant helper
; ;;;  so all the subclass are loaded!! 

; The following lemmas are the justifications. The proof is a bit
; involved. 
;

(defthm mem-sig-all-sig
  (implies  (wff-array-class-table-rep (array-class-by-name any acl))
            (mem any (jvm::all-array-sigs acl))))

(defthm array-class-table-inv-helper-array-class-loaded
  (implies (and (jvm::array-class-table-inv-helper l s)
                (array-type? any)
                (mem any l))
           (jvm::array-class-correctly-loaded? (jvm::base-types any) s)))


(defthm array-base-type-member-base-types
  (implies (array-type? any)
           (mem (array-base-type any) (jvm::base-types any))))


(defthm array-class-correctly-loaded-implies-base-type-loaded-1
  (implies (and (jvm::array-class-correctly-loaded? l s)
                (mem any l)
                (array-type? any))
           (array-class-by-name any (array-class-table s))))


(defthm consistent-state-bounded-implies-wff
  (implies (and (consistent-state s)
                (array-class-by-name any (array-class-table s)))
           (wff-array-class-table-rep 
            (array-class-by-name any (array-class-table s)))))


(defthm consistent-state-bounded-implies-wff-specific
  (implies (and (consistent-state s)
                (array-type? any)
                (wff-array-class-table-rep (array-class-by-name any
                                                                (array-class-table s)))
                (array-type? (array-base-type any)))
           (wff-array-class-table-rep 
            (array-class-by-name (array-base-type any) (array-class-table s))))
  :hints (("Goal" :in-theory (e/d (array-class-table-inv) 
                                  (array-type? wff-array-class-table-rep))
           :use ((:instance array-class-correctly-loaded-implies-base-type-loaded-1
                            (any (array-base-type any))
                            (l (jvm::base-types any)))
                 (:instance array-class-table-inv-helper-array-class-loaded
                            (l (jvm::all-array-sigs (array-class-table s))))))))
                            
;;; All this should be local events! 
;; 
;; (defthm consistent-state-implies-build-a-java-visible-instance-guard
;;   (implies (consistent-state s)
;;            (BUILD-A-JAVA-VISIBLE-INSTANCE-GUARD "java.lang.Class" s))
;;   :hints (("Goal" :in-theory (e/d (consistent-state boot-strap-class-okp)
;;                                   (build-a-java-visible-instance-guard)))))
;;
;; name conflict!! 

(defthm consistent-state-implies-build-a-java-visible-instance-guard-x
  (implies (consistent-state s)
           (BUILD-A-JAVA-VISIBLE-INSTANCE-GUARD "java.lang.Class" s))
  :hints (("Goal" :in-theory (e/d (consistent-state boot-strap-class-okp)
                                  (build-a-java-visible-instance-guard)))))



(defthm load-array-class-no-fatal-error-implies-load-array-class2-guard
   (implies (and (consistent-state s)
                 (no-fatal-error? s)
                 (NOT (ARRAYCLASSLOADED? ANY S))
                 (array-type? any)
                 (consistent-state (load_array_class (array-base-type any) s))
                 (no-fatal-error? (load_array_class (array-base-type any) s)))
            (jvm::load_array_class2-guard any 
                                          (load_array_class (array-base-type
                                                             any) s)))
   :hints (("Goal" :in-theory (e/d (load_array_class)
                                   (class-loaded?
                                    load_class
                                    array-type?
                                    wff-array-class-table-rep
                                    BUILD-A-JAVA-VISIBLE-INSTANCE-GUARD                                    
                                    load_array_class2-preserve-consistency-actual                                   
                                    )))))


;; (defthm load_array_class2-state-set-current-thread
;;   (implies (consistent-state (load_array_class2 any s))
;;            (consistent-state (load_array_class2 any (state-set-current-thread
;;                                                      any -1 
                             


(defthm |Subgoal *1/8'|
  (IMPLIES (AND (NOT (ERROR-FLAG S))
                (NOT (ARRAYCLASSLOADED? ANY S))
                (NOT (ARRAY-TYPE? ANY))
                (NOT (PRIMITIVE-TYPE? ANY))
                (NOT (CLASS-LOADED? ANY S))
                (NOT (ERROR-FLAG (LOAD_CLASS ANY S)))
                (CONSISTENT-STATE S))
           (CONSISTENT-STATE (LOAD_ARRAY_CLASS2 ANY (load_class any S))))
  :hints (("Goal" :in-theory (e/d (load_array_class)
                                  (load_class)))))


(defthm load_array_class-preserve-consistency
  (implies (consistent-state s)
           (consistent-state (load_array_class any s)))
  :hints (("Goal" :in-theory (e/d (load_array_class)
                                  (;;jvm::load_array_class2-guard 
                                   Arrayclassloaded?
                                   load_class))
           :do-not '(generalize))))



;;; Mon Mar  7 16:09:59 2005. At last!! Still have skip proofs about basic
;;; operation that introduce new objects into heap! 

;;;
;;; prove one subgoal needs jvm::load_array_class2-guard opens.
;;; prove 1/4 needs the jvm::load_array_class2-guard closed. 
;;;



;;; (skip-proofs
;;;  (defthm load_array_class-preserve-consistency
;;;    (implies (consistent-state s)
;;;             (consistent-state (load_array_class any s)))))
;;;
;;;; these may need to be proved earlier!!! 


(defthm resolveClassReference-preserve-consistency
  (implies (consistent-state s)
           (consistent-state (resolveClassReference any s)))
  :hints (("Goal" :in-theory (e/d (resolveClassReference) (load_array_class load_class)))))

(defthm getArrayClass-preserve-consistency
   (implies (consistent-state s)
            (consistent-state (getArrayClass any s))))

(defthm build-an-array-instance-does-not-affect-s
  (equal (mv-nth 1 (build-an-array-instance base-type  bound s))
         s))




;----------------------------------------------------------------------



