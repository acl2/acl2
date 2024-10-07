(in-package "JVM")
(acl2::set-verify-guards-eagerness 2)
(include-book "../M6-DJVM-shared/jvm-env")
(include-book "../M6-DJVM-shared/jvm-class-table-test-data")
;----------------------------------------------------------------------

(include-book "ordinals/e0-ordinal" :dir :system)
(set-well-founded-relation e0-ord-<)

(defun make-class-table (instance-class-table array-class-table)
  (list 'class-table 
        (cons 'instance-class-table instance-class-table)
        (cons 'array-class-table array-class-table)))

(defun wff-class-table (cl)
  (declare (xargs :verify-guards t))
  (and (equal (len cl) 3)
       (true-listp cl)
       (consp (nth 1 cl))
       (consp (nth 2 cl))
       (equal (car (nth 1 cl)) 'instance-class-table)
       (equal (car (nth 2 cl)) 'array-class-table)))


(local 
 (defthm wff-class-table-test
   (wff-class-table *test.classtable*)))

;----------------------------------------------------------------------

(defun make-runtime-class-rep (classname super constpool fields methods
                               interfaces static-fields status accessflags
                               init-thread-id class-ref)
  (list 'class classname  ;; just names 
               super      ;; name of the super
               (cons 'constant_pool constpool)  ;; runtime representation
               (cons 'fields  fields)           ;; non static fields 
               (cons 'methods methods)          ;; list of methods 
               (cons 'interfaces interfaces)    ;; interfaces 
               (cons 'static-fields static-fields)   
               (cons 'status status)            ;; 'LOADED, 'INITIALIZED, not worry about
               (cons 'access-flags accessflags)    ;;
               (cons 'init-thread init-thread-id)  ;;
               (cons 'class-ref class-ref)))


#| KVM status bit
 #define CLASS_RAW       0 /* this value must be 0 */ ;; implicit in our STATE REP
 #define CLASS_LOADING   1                            ;;    
 #define CLASS_LOADED    2
 #define CLASS_LINKED    3
 #define CLASS_VERIFIED  4
 #define CLASS_READY     5
 #define CLASS_ERROR    -1
|#

(defconst *class_raw*        0) ;; not neccessary
(defconst *class_loading*    1) ;; not necessary
(defconst *class_loaded*     2) ;;
(defconst *class_linked*     3) ;;
(defconst *class_verified*   4) ;;
(defconst *class_ready*      5) ;;
(defconst *class_error*     -1)



(defun wff-class-rep (class-rep)
  (declare (xargs :verify-guards t))
  (and (true-listp class-rep)
       (equal (len class-rep) 12)
       (equal (car class-rep) 'class) 
       (consp (nth 3 class-rep))
       (consp (nth 4 class-rep))
       (consp (nth 5 class-rep))
       (consp (nth 6 class-rep))
       (consp (nth 7 class-rep))
       (consp (nth 8 class-rep))
       (consp (nth 9 class-rep))
       (consp (nth 10 class-rep))
       (consp (nth 11 class-rep))
       ;; may need to be strengthened.  09/08/03 
       (integerp (cdr (nth 11 class-rep)))
       (true-listp (cdr (nth 3 class-rep)))
       (true-listp (cdr (nth 4 class-rep)))
       (true-listp (cdr (nth 5 class-rep)))
       (true-listp (cdr (nth 6 class-rep)))
       (true-listp (cdr (nth 7 class-rep)))
     ; (true-listp (cdr (nth 8 class-rep))) 
       ;; 10/27/03  fixed after having a concrete state.
       (true-listp (cdr (nth 9 class-rep)))))




(defun wff-instance-class-table (icl)
  (declare (xargs :verify-guards t))
  (if (not (consp icl)) t
    (and (wff-class-rep (car icl))
         (wff-instance-class-table (cdr icl)))))

(local 
 (defthm wff-instance-class-table-test
   (wff-instance-class-table (cdr (nth 1 *test.classtable*)))))

;----------------------------------------------------------------------



(defun classname (crep)
  (declare (xargs :guard (wff-class-rep crep)))
  (nth 1 crep))

(defun class-ref (crep)
  (declare (xargs :guard (wff-class-rep crep)))
  (cdr (nth 11 crep)))

(defun class-accessflags (crep)
  (declare (xargs :guard (wff-class-rep crep)))
  (cdr (nth 9 crep)))

(defun constantpool (crep)
  (declare (xargs :guard (wff-class-rep crep)))
  (cdr (nth 3 crep)))

(defun super (crep)
  (declare (xargs :guard (wff-class-rep crep)))
  (nth 2 crep))

(defun interfaces (crep)
  (declare (xargs :guard (wff-class-rep crep)))
  (cdr (nth 6 crep)))


(defun fields  (crep)    
  (declare (xargs :guard (wff-class-rep crep)))
  (cdr (nth 4 crep)))

(defun methods  (crep)    
  (declare (xargs :guard (wff-class-rep crep)))
  (cdr (nth 5 crep)))

(defun static-fields  (crep)    
  (declare (xargs :guard (wff-class-rep crep)))
  (cdr (nth 7 crep)))


(defun class-status (crep)
  (declare (xargs :guard (wff-class-rep crep)))
  (cdr (nth 8 crep)))


(defun init-thread-id (crep)
  (declare (xargs :guard (wff-class-rep crep)))
  (cdr (nth 10 crep)))

;----------------------------------------------------------------------


(defun class-rep-set-classname (n crep)
  (declare (xargs :guard (wff-class-rep crep)))
  (make-runtime-class-rep 
      n
      (super     crep)
      (constantpool crep)
      (fields       crep)
      (methods      crep)
      (interfaces   crep)
      (static-fields crep)
      (class-status  crep)
      (class-accessflags crep)
      (init-thread-id    crep)
      (class-ref         crep)))

(defun class-rep-set-super (super crep)
  (declare (xargs :guard (wff-class-rep crep)))
  (make-runtime-class-rep 
      (classname crep)
      super
      (constantpool crep)
      (fields       crep)
      (methods      crep)
      (interfaces   crep)
      (static-fields crep)
      (class-status  crep)
      (class-accessflags crep)
      (init-thread-id    crep)
      (class-ref         crep)))

(defun class-rep-set-constantpool (cp crep)
  (declare (xargs :guard (wff-class-rep crep)))
  (make-runtime-class-rep 
      (classname crep)
      (super     crep)
      cp
      (fields       crep)
      (methods      crep)
      (interfaces   crep)
      (static-fields crep)
      (class-status  crep)
      (class-accessflags crep)
      (init-thread-id    crep)
      (class-ref         crep)))

(defun class-rep-set-fields (fs crep)
  (declare (xargs :guard (wff-class-rep crep)))
  (make-runtime-class-rep 
      (classname crep)
      (super     crep)
      (constantpool crep)
      fs
      (methods      crep)
      (interfaces   crep)
      (static-fields crep)
      (class-status  crep)
      (class-accessflags crep)
      (init-thread-id    crep)
      (class-ref         crep)))

(defun class-rep-set-methods (ms crep)
  (declare (xargs :guard (wff-class-rep crep)))
  (make-runtime-class-rep 
      (classname crep)
      (super     crep)
      (constantpool crep)
      (fields       crep)
      ms
      (interfaces   crep)
      (static-fields crep)
      (class-status  crep)
      (class-accessflags crep)
      (init-thread-id    crep)
      (class-ref         crep)))

(defun class-rep-set-interfaces (is crep)
  (declare (xargs :guard (wff-class-rep crep)))
  (make-runtime-class-rep 
      (classname crep)
      (super     crep)
      (constantpool crep)
      (fields       crep)
      (methods      crep)
      is
      (static-fields crep)
      (class-status  crep)
      (class-accessflags crep)
      (init-thread-id    crep)
      (class-ref         crep)))

(defun class-rep-set-static-fields (sfs crep)
  (declare (xargs :guard (wff-class-rep crep)))
  (make-runtime-class-rep 
      (classname crep)
      (super     crep)
      (constantpool crep)
      (fields       crep)
      (methods      crep)
      (interfaces   crep)
      sfs
      (class-status  crep)
      (class-accessflags crep)
      (init-thread-id    crep)
      (class-ref         crep)))

(defun class-rep-set-class-status (cs crep)
  (declare (xargs :guard (wff-class-rep crep)))
  (make-runtime-class-rep 
      (classname crep)
      (super     crep)
      (constantpool crep)
      (fields       crep)
      (methods      crep)
      (interfaces   crep)
      (static-fields crep)
      cs
      (class-accessflags crep)
      (init-thread-id    crep)
      (class-ref         crep)))

(defun class-rep-set-accessflags (afs crep)
  (declare (xargs :guard (wff-class-rep crep)))
  (make-runtime-class-rep 
      (classname crep)
      (super     crep)
      (constantpool crep)
      (fields       crep)
      (methods      crep)
      (interfaces   crep)
      (static-fields crep)
      (class-status  crep)
      afs
      (init-thread-id    crep)
      (class-ref         crep)))

(defun class-rep-set-init-thread-id (id crep)
  (declare (xargs :guard (wff-class-rep crep)))
  (make-runtime-class-rep 
      (classname crep)
      (super     crep)
      (constantpool crep)
      (fields       crep)
      (methods      crep)
      (interfaces   crep)
      (static-fields crep)
      (class-status  crep)
      (class-accessflags crep)
      id
      (class-ref         crep)))

(defun class-rep-set-class-ref (cref crep)
  (declare (xargs :guard (wff-class-rep crep)))
  (make-runtime-class-rep 
      (classname crep)
      (super     crep)
      (constantpool crep)
      (fields       crep)
      (methods      crep)
      (interfaces   crep)
      (static-fields crep)
      (class-status  crep)
      (class-accessflags crep)
      (init-thread-id    crep)
      cref))

;----------------------------------------------------------------------



(defthm make-runtime-class-rep-accessor 
  (mylet* ((s (make-runtime-class-rep cn sn cp fs ms ifs sfs cs ac id crf)))
  (and (equal (classname s) cn)
       (equal (super s) sn)
       (equal (constantpool s) cp)
       (equal (fields s) fs)
       (equal (methods s) ms)
       (equal (interfaces s) ifs)
       (equal (static-fields s) sfs)
       (equal (class-status s) cs)
       (equal (class-accessflags s) ac)
       (equal (init-thread-id s) id)
       (equal (class-ref s) crf)))
  :hints (("Goal" :in-theory (enable make-runtime-class-rep))))



;----------------------------------------------------------------------

(defun replace-class-table-entry (old-class-rep new-class-rep old-class-table)
  (declare (xargs :guard t))
  (if (not (consp old-class-table))
      nil
    (if (equal (car old-class-table) old-class-rep)
        (cons new-class-rep (cdr old-class-table))
      (cons (car old-class-table)
            (replace-class-table-entry old-class-rep new-class-rep (cdr
                                                                    old-class-table))))))


;----------------------------------------------------------------------

(defun wff-string-cp-entry (cp-entry)
  (declare (xargs :verify-guards t))
  (and (consp cp-entry)
       (equal (len cp-entry) 2)
       (equal (car cp-entry) 'STRING)
       (integerp (cadr cp-entry))))


(defun wff-int-cp-entry (cp-entry)
  (declare (xargs :verify-guards t))
  (and (consp cp-entry)
       (equal (len cp-entry) 2)
       (equal (car cp-entry) 'INT)
       (int32p (cadr cp-entry))))

(defun wff-long-cp-entry (cp-entry)
  (declare (xargs :verify-guards t))
  (and (consp cp-entry)
       (equal (len cp-entry) 2)
       (equal (car cp-entry) 'LONG)
       (int64p (cadr cp-entry))))

(defun wff-constant-pool-entry (cp-entry)
  (declare (xargs :verify-guards t))
  (and (consp cp-entry)
       (equal (len cp-entry) 2)
       (or (wff-string-cp-entry cp-entry)
           (wff-int-cp-entry cp-entry)
           (wff-long-cp-entry cp-entry)
           ;;(wff-float-cp-entry cp-entry)
           ;;(wff-double-cp-entry cp-entry)
           ;; temp implementation
           )))

(defun wff-constant-pool (cps)
  (declare (xargs :verify-guards t))
  (if (not (consp cps)) t
    (and (wff-constant-pool-entry (car cps))
         (wff-constant-pool (cdr cps)))))


(local
 (defun all-constant-pools (class-reps)
   (declare (xargs :guard (wff-instance-class-table class-reps)))
   (if (not (consp class-reps)) t
     (cons (constantpool (car class-reps))
           (all-constant-pools (cdr class-reps))))))

(local 
 (defun all-wff-constant-pools (cps)
  (if (not (consp cps)) t
    (and (wff-constant-pool (car cps))
         (all-wff-constant-pools (cdr cps))))))

(local 
 (defthm all-wff-constant-pools-test
   (all-wff-constant-pools (all-constant-pools  (cdr (nth 1 *test.classtable*))))))

;----------------------------------------------------------------------

(defun cpentry-type (cpentry)
  (declare (xargs :guard (wff-constant-pool-entry cpentry)))
  (car cpentry))

(defun cpentry-value (cpentry)
  (declare (xargs :guard (wff-constant-pool-entry cpentry)))
  (cadr cpentry))


(defun make-string-cp-entry (obj-ref)
  (list 'STRING obj-ref))

(defun string-value-cp-entry (cpentry)
  (declare (xargs :guard (wff-constant-pool-entry cpentry)))
  (cadr cpentry))

(defun make-int-cp-entry (int-value)
  (list 'INT int-value))

(defun int-value-cpentry (cpentry)
  (declare (xargs :guard (wff-constant-pool-entry cpentry)))
  (cadr cpentry))

(defun make-long-cp-entry (long-value)
  (list 'LONG long-value))

(defun long-value-cpentry (cpentry)
  (declare (xargs :guard (wff-constant-pool-entry cpentry)))
  (cadr cpentry))

(defun make-float-cp-entry (float-value)
  (list 'FLOAT float-value))
(defun float-value-cpentry (cpentry)
  (declare (xargs :guard (wff-constant-pool-entry cpentry)))
  (cadr cpentry))

(defun make-double-cp-entry (double-value)
  (list 'double double-value))

;----------------------------------------------------------------------


;----------------------------------------------------------------------
;
;  this are instance fields, what don't mention any constant value.
;

(defun make-field (classname fieldname fieldtype accessflags)
  (list 'field classname fieldname fieldtype 
        (cons 'accessflags accessflags)))

(defun wff-field (field)
  (and (equal (len field) 5)
       (true-listp field)
       (consp (nth 4 field))))

(defun wff-fields-x (fields)
  (if (not (consp fields)) 
      (equal fields nil)
    (and (wff-field (car fields))
         (wff-fields-x (cdr fields)))))

;----------------------------------------------------------------------

(defun field-classname (field)
  (declare (xargs :guard (wff-field field)))
  (nth 1 field))

(defun field-fieldname (field)  
  (declare (xargs :guard (wff-field field)))
  (nth 2 field))

(defun field-fieldtype (field)  
  (declare (xargs :guard (wff-field field)))
  (nth 3 field))

(defun field-fieldaccessflags (field)  
 (declare (xargs :guard (wff-field field)))
 (cdr (nth 4 field)))

;----------------------------------------------------------------------

;; these are static fields, what may refer to constant value in the constantpool

(defun make-static-fields (fields) 
  (cons 'static-fields fields))


(defun wff-static-fields (fields)
  (and (true-listp fields)
       (consp fields)))

(defun static-fields-fields (fields)
  (declare (xargs :guard (wff-static-fields fields)))
  (cdr fields))

;----------------------------------------------------------------------


(defun make-static-field (classname fieldname fieldtype accessflags value)
  (list 'static-field 
        classname 
        fieldname 
        fieldtype 
        (cons 'accessflags accessflags)
        value))


(defun wff-static-field (field)
  (and (equal (len field) 6)
       (true-listp field)
       (consp (nth 4 field))))

(defun static-field-classname  (field) 
  (declare (xargs :guard (wff-static-field field)))
  (nth 1 field))
(defun static-field-fieldname  (field) 
  (declare (xargs :guard (wff-static-field field)))
  (nth 2 field))
(defun static-field-fieldtype  (field) 
  (declare (xargs :guard (wff-static-field field)))
  (nth 3 field))
(defun static-field-accessflags (field) 
  (declare (xargs :guard (wff-static-field field)))
  (cdr (nth 4 field))) ;; don't need cpindex

(defun static-field-fieldvalue (field)   
 (declare (xargs :guard (wff-static-field field)))
 (nth 5 field))

(defun wff-static-fields-x (fields)
  (if (not (consp fields)) t
    (and (wff-static-field (car fields))
         (wff-static-fields-x (cdr fields)))))
                           


;----------------------------------------------------------------------
;
;  since we only modify static fields value field
;

(defun static-field-set-value (value field)
 (declare (xargs :guard (wff-static-field field)))
  (make-static-field (static-field-classname field)
                     (static-field-fieldname field)
                     (static-field-fieldtype field)
                     (static-field-accessflags field)
                     value))


;----------------------------------------------------------------------
;
;   Methods 
;

(defun make-method (classname methodname args returntype accessflags code)
  (list 'method 
        classname 
        methodname 
        (cons 'parameters args)
        (cons 'returntype returntype) 
        ;; Sun Apr 30 20:37:57 2006.  The cldc-class-table's format changed!! 
        (cons 'accessflags accessflags)
        code))

(defun wff-method-decl (method-decl)
  (and (true-listp method-decl)
       (equal (len method-decl) 7)
       (consp (nth 3 method-decl))
       (consp (nth 4 method-decl))
       (consp (nth 5 method-decl))
       (true-listp (cdr (nth 3 method-decl)))
       (true-listp (cdr (nth 5 method-decl)))
       (true-listp (nth 6 method-decl))))

;----------------------------------------------------------------------

(defun method-classname  (method)      
  (declare (xargs :guard (wff-method-decl method)))
  (nth 1 method))


(defun method-methodname (method)     
  (declare (xargs :guard (wff-method-decl method)))
  (nth 2 method))

(defun method-args       (method)      
  (declare (xargs :guard (wff-method-decl method)))
  (cdr (nth 3 method))) ;; FIXED  10/28/03. Originally missing a cdr 

(defun method-returntype (method)      
  (declare (xargs :guard (wff-method-decl method)))
  (cdr (nth 4 method))) ;; Sun Apr 30 20:34:21 2006. fixed after
;; cldc-class-table format changed!! 
;; Mon May  1 01:37:14 2006

(defun method-accessflags(method)    
  (declare (xargs :guard (wff-method-decl method)))
  (cdr (nth 5 method)))
(defun method-code       (method)  
  (declare (xargs :guard (wff-method-decl method)))
  (nth 6 method))

;----------------------------------------------------------------------

(defun make-code (max-stack max-local code-length instrs exceptions stackmaps)
  (list 'code 
        (cons 'max_stack max-stack)
        (cons 'max_local max-local)
        (cons 'code_length code-length)
        (cons 'parsedcode instrs)
        (cons 'Exceptions exceptions)
        (cons 'StackMap   stackmaps)))


(defun wff-code (code)
  (and (equal (len code) 7)
       (true-listp code)
       (consp (nth 1 code))
       (consp (nth 2 code))
       (consp (nth 3 code))
       (consp (nth 4 code))
       (consp (nth 5 code))
       (consp (nth 6 code))))



(defun code-max-stack (code) 
  (declare (xargs :guard (wff-code code)))
  (cdr (nth 1 code)))

(defun code-max-local (code) 
  (declare (xargs :guard (wff-code code)))
  (cdr (nth 2 code)))

(defun code-code-lenght (code)
  (declare (xargs :guard (wff-code code)))
  (cdr (nth 3 code)))

(defun code-instrs (code)
  (declare (xargs :guard (wff-code code)))
  (cdr (nth 4 code)))

(defun code-handlers (code)
  (declare (xargs :guard (wff-code code)))
  (cdr (nth 5 code)))

(defun code-stackmaps (code)
  (declare (xargs :guard (wff-code code)))
  (cdr (nth 6 code)))


;----------------------------------------------------------------------

(defun make-accessflags (flags)
  flags)

;----------------------------------------------------------------------

(defun wff-inst (inst)
  (and (true-listp inst)
       (equal (len inst) 2)
       (integerp (car inst))
       (consp (nth 1 inst))
       (true-listp (nth 1 inst))))

(defun  wff-insts (code)
  (if (not (consp code)) t
    (and (wff-inst (car code))
         (wff-insts (cdr code)))))

;; Tue Mar 30 09:52:41 2004. updated 

;; (defun wff-inst (instr)
;;   (and (true-listp instr)
;;        (equal (length instr) 2)
;;        (true-listp (NTH 1 instr))))
;; ;;     (equal (length (nth 1 instr)) 2)))

(defun inst-offset (instr)
  (declare (xargs :guard (wff-inst instr)))
  (car instr))

(defun inst-inst (instr) 
  (declare (xargs :guard (wff-inst instr)))
  (nth 1 instr))

(defun inst-opcode (instr)
  (declare (xargs :guard (wff-inst instr)))
  (car (inst-inst instr)))

(defun inst-arg    (instr)
  (declare (xargs :guard (and (wff-inst instr)
                              (equal (len (nth 1 instr)) 2))))
  (cadr (inst-inst instr)))


;----------------------------------------------------------------------


;; OLD comment: Mon Dec 22 23:40:31 2003

;; the only way to create a runtime-class-rep is through the class_loader in
;; JVM. 

;; maybe we should allow classname to be a class-descriptor, so that any Array
;; Class has an entry in this table, to really compare whether two array is
;; assignable, we could go through the descriptor or the object on the Java
;; heap.  another representation is to create a seperated table to record the
;; array-classes. We need a ...

;; should we introduce another table to record those array-classes?? In that
;; way, we could keep internal-class-table in a uniform format.
;;
;; yes. that's what we did not.
;;

;----------------------------------------------------------------------

(defun make-array-type (base-type)
  (list 'ARRAY base-type))


(defun make-array-class-table-entry (base-type accessflags new-addr)
  (list (make-array-type base-type) 
        (cons 'accessflags accessflags) new-addr))

(defun wff-array-class-table-rep (array-class-rep)
  (and (true-listp array-class-rep)
       (equal (len array-class-rep) 3)
       (consp (nth 1 array-class-rep))))

(defun wff-array-class-table (array-class-table)
  (and (true-listp array-class-table)
       (if (not (consp array-class-table))
           t
         (and (wff-array-class-table-rep (car array-class-table))
              (wff-array-class-table (cdr array-class-table))))))

;----------------------------------------------------------------------

(defun array-sig (array-class-rep) 
  (declare (xargs :guard (wff-array-class-table-rep array-class-rep)))
  (nth 0 array-class-rep))

(defun array-access-flags (array-class-rep) 
  (declare (xargs :guard (wff-array-class-table-rep array-class-rep)))
  (cdr (nth 1 array-class-rep)))

(defun array-class-ref    (array-class-rep) 
  (declare (xargs :guard (wff-array-class-table-rep array-class-rep)))
  (nth 2 array-class-rep))

;; once loaded this array-class-table doesn't change.

(defun add-array-class-table-entry (ent table)
  (cons ent table))

;----------------------------------------------------------------------


;; for provide array-class-table is to provide a translation to a unique
;; class-ref, so that someone may call Class.forName() return a unique
;; references.

;----------------------------------------------

;----------------------------------------------------------------------

(defun class-by-name (class-name dcl)
  (declare (xargs :guard (wff-instance-class-table dcl)))
  (if (not (consp dcl))
      nil
   (if (equal (classname (car dcl)) class-name)
      (car dcl)
      (class-by-name class-name (cdr dcl)))))


(defun isClassTerm (Class)
  (and (consp Class)
       (equal (len (cdr Class)) 11)))  ;; not an accurate definition here 



(defun class-exists? (cn icl)
  (declare (xargs :guard (wff-instance-class-table icl)))
  (isClassTerm (class-by-name cn icl))) ;; not nil

;; 1. base type could be a loaded array-class 
;; 2. base type could be a loaded instance-class
;; 3. base type could be a primitive type.

(defun array-class-by-name (array-type array-class-table)
  (declare (xargs :guard (wff-array-class-table array-class-table)))
  (if (not (consp array-class-table))
      nil
    (if (equal (array-sig (car array-class-table)) array-type)
        (car array-class-table)
      (array-class-by-name array-type (cdr array-class-table)))))

;----------------------------------------------------------------------

(defun isInterface (class-rep)
  (declare (xargs :guard (wff-class-rep class-rep)))
  (mem '*interface* (class-accessflags class-rep)))

;; assuming when class-rep is loaded, the super is also loaded. 
(defun super-exists (class-rep) 
  (declare (xargs :guard (wff-class-rep class-rep)))
  (not (equal (super class-rep) "")))

(defun class-rep-in-error-state? (class-rep) 
  (declare (xargs :guard (wff-class-rep class-rep)))
  (equal (class-status class-rep) *CLASS_ERROR*))

;----------------------------------------------------------------------



;----------------------------------------------------------------------
;----------------------------------------------------------------------

;; From consistent-state.lisp Tue Jan 13 15:35:05 2004



;----------------------------------------------------------------------
;
; defining concepts of wff class-table and consistent-class-hierachy!!
;
; We need this to define properly-guarded isSubclassOf?? 
; 
; Tue Jan 13 15:18:13 2004. The purpose is to reuse the same definition in DJVM
; and the actual JVM. We want JVM's operations being guarded, but we don't
; check for them.. We want to "guard verify" them. As long as top level guard
; satisfy (and we should they satisfy) then. execution will not causing guard
; failuring in any point of program execution!!
;
;


(defun all-class-names (cl)
  (declare (xargs :guard (wff-instance-class-table cl)))
  (if (not (consp cl)) nil
    (cons (classname (car cl))
          (all-class-names (cdr cl)))))


(defun unseen-classes (cl seen)
  (declare (xargs ; :measure (wff-instance-class-table cl) ; Matt K. commented out
                  :guard (and (wff-instance-class-table cl)
                              (true-listp seen))))
  (len (set-diff (all-class-names cl) seen)))

(defun unseen-classes-x (ns cl seen mode)
  (declare (xargs :guard (and (wff-instance-class-table cl)
                              (true-listp seen))))
  (cond ((equal mode 'NODE) (cons (cons (+ 1 (unseen-classes cl seen)) 0) 0))
        ((equal mode 'LIST) (cons (cons (+ 1 (unseen-classes cl seen)) 0) 
                                  (len ns)))
        (t 0)))


(defun all-interfaces-bounded? (interfaces cl)
  (declare (xargs :guard (wff-instance-class-table cl)))
  (if (not (consp interfaces)) t
    (and (class-exists? (car interfaces) cl)
         (isInterface (class-by-name (car interfaces) cl))
         (all-interfaces-bounded? (cdr interfaces) cl))))




(defun class-hierachy-consistent1-class-n (n cl)
  ;; 
  ;; 1. super ends with "java.lang.Object" 
  ;; 2. interfaces all bounded and are in fact interfaces.
  ;; 3. Somewhere we need to assert no loop
  ;;
  ;;
  (declare (xargs :guard (wff-instance-class-table cl)))
  (and (class-exists? n cl)
       (if (equal n "java.lang.Object")
           (let ((class-rep (class-by-name n cl)))
             (and (not (class-exists? (super class-rep) cl))
                  (all-interfaces-bounded? (interfaces class-rep) cl)))
         (let ((class-rep (class-by-name n cl)))
           (and (class-exists? (super class-rep) cl)
                (all-interfaces-bounded? (interfaces class-rep) cl))))))


(defun class-hierachy-consistent1-aux (classes cl)
  (declare (xargs :guard (and (wff-instance-class-table cl)
                              (wff-instance-class-table classes))))
  (if (not (consp classes)) t
    (and (class-hierachy-consistent1-class-n (classname (car classes)) cl)
         ;;; NOTE: Here using (class (car classes)) is different from testing
         ;;; (car classes). Current usage allows some invalid description in
         ;;; class-table. Otherwise we need to assert no-dups explicitly
         ;;; We are using the same interface to assert property then it is
         ;;; good. 
         (class-hierachy-consistent1-aux (cdr classes) cl))))


(defun class-hierachy-consistent1 (cl)
  (declare (xargs :guard (wff-instance-class-table cl)))
  (class-hierachy-consistent1-aux cl cl)) 
  ;;
  ;; this only assert the fact that no class-rep refers an undefined 
  ;; entity in super field and interfaces field
  ;;
  ;; Thus self contained. 
  ;; 

(defthm class-exists?-implies-mem-all-class-names 
  (implies (and (class-exists? n cl)
                (wff-instance-class-table cl))
           (mem n (all-class-names cl))))


;;  
(defun superclass-chain-no-loop-class-n (n1 cl seen)
  (declare (xargs :guard (and (wff-instance-class-table cl)
                              (true-listp seen))
                  :measure (unseen-classes cl seen)))
  ;;
  ;; for termination, I also need cl is wff-instance-class-table we need to be
  ;; able to show n1 if bounded, then it is a member of all classes
  ;;
  (if (not (wff-instance-class-table cl)) nil
    (if (not (class-exists? n1 cl)) t
      (if (mem n1 seen) nil
        (let ((n2 (super (class-by-name n1 cl))))
          ;; this definition is a trickier. 
          ;; termination should be ok.
          (superclass-chain-no-loop-class-n n2 cl (cons n1 seen)))))))


;; I could merge this with the above one.  09/08/03 

;;  Mon Nov 15 18:25:44 2004
(defun interfaces-chains-no-loop-class-n (n-or-ns cl seen mode)
  (declare (xargs :guard (and (wff-instance-class-table cl)
                              (true-listp seen))
                  ;; I could assert stronger guard such as 
                  ;; all n, ns are also bounded. 
                  :measure (unseen-classes-x n-or-ns cl seen mode)))
  (let ((n  n-or-ns)
        (ns n-or-ns)) 
    (if (not (wff-instance-class-table cl)) nil 
      ;; need for termintation!!
      (cond ((equal mode 'NODE)
             (if (mem n seen) nil
               (if (not (class-exists? n cl)) nil 
                 ;; if super interface is not bound then fail!!
                   (let ((ns (interfaces (class-by-name n cl))))
                     (interfaces-chains-no-loop-class-n
                      ns cl (cons n seen) 'LIST)))))
            ((equal mode 'LIST)
             (if (not (consp ns)) t
               (and (interfaces-chains-no-loop-class-n (car ns) cl seen 'NODE)
                    (interfaces-chains-no-loop-class-n (cdr ns) cl seen 'LIST))))))))

;; ;; Mon Nov 15 18:25:08 2004
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
;;              (if (mem n seen) nil
;;                (if (not (class-exists? n cl)) t
;;                    (let ((ns (interfaces (class-by-name n cl))))
;;                      (interfaces-chains-no-loop-class-n
;;                       ns cl (cons n seen) 'LIST)))))
;;             ((equal mode 'LIST)
;;              (if (not (consp ns)) t
;;                (and (interfaces-chains-no-loop-class-n (car ns) cl seen 'NODE)
;;                     (interfaces-chains-no-loop-class-n (cdr ns) cl seen 'LIST))))))))


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
;;              (if (not (class-exists? n cl)) t  ;;; !!!!!!!!!!!!!!
;;                (if (mem n seen) nil            ;;; !!!!!!!!!!!!!! 
;;                                                ;;; Need to reverse these two
;;                                                ;;; lines!! 
;;                    (let ((ns (interfaces (class-by-name n cl))))
;;                      (interfaces-chains-no-loop-class-n
;;                       ns cl (cons n seen) 'LIST)))))
;;             ((equal mode 'LIST)
;;              (if (not (consp ns)) t
;;                (and (interfaces-chains-no-loop-class-n (car ns) cl seen 'NODE)
;;                     (interfaces-chains-no-loop-class-n (cdr ns) cl seen 'LIST))))))))


(defun class-hierachy-consistent2-class-n (n cl)
  (declare (xargs :guard (wff-instance-class-table cl)))
  ;; this one I want to assert no loop through superclass chain and super
  ;; interface chain.
  ;;
  ;; The problem is shall I mix this part with the other part?   
  ;; 
  ;; Shall I assert all interface's super must be java.lang.Object?
  (and (superclass-chain-no-loop-class-n n cl nil)
       (interfaces-chains-no-loop-class-n n cl nil 'NODE)))


(defun class-hierachy-consistent2-aux (classes cl)
  (declare (xargs :guard (and (wff-instance-class-table classes)
                              (wff-instance-class-table cl))))
  (if (not (consp classes)) t
    (and (class-hierachy-consistent2-class-n (classname (car classes)) cl)
         (class-hierachy-consistent2-aux  (cdr classes) cl))))

(defun class-hierachy-consistent2 (cl)
  (declare (xargs :guard (wff-instance-class-table cl)))
  (class-hierachy-consistent2-aux cl cl))



(defun consistent-class-hierachy (cl)
  (declare (xargs :verify-guards t))
  ;; although 
  (and (wff-instance-class-table cl)
       (class-hierachy-consistent1 cl)
       (class-hierachy-consistent2 cl)))


;----------------------------------------------------------------------


;; The third thing we need to assert about the internal class table is 
;; it is in fact loaded from the external class table. 
;; We only need to assert, class hierachy is not changed! tags of value in the
;; consistent pool is not changed. 
;; 
;; We also need to assert that static field's type all right? No we don't 
;; if Static field doesn't exist, we could just thrown an error in both
;; machine. However a sensible JVM implementation of loader should load that
;; field correctly. (part of the correctness of loader then) 
;;
;; WE DON'T EVEN NEED TO ASSERT FIELDS ARE ALL RIGHT. BECAUSE EVERYTHING IS
;; ENCODED IN THE FIELD CP.  09/09/03 ??? REALLY???  THE ASSIGNMENT COMPATIBLE
;; TEST IS DONE AFTER RESOLUTION. RESOLUTION IS GUARANTEED TO FIND THE RIGHT
;; TYPE. IN BCV, NO RESOLUTION IS DONE. BCV JUST TRUST AT RUNTIME RESOLUTION
;; PROCEDURE WILL FIND THE FIELD OF RIGHT TYPE.



(defun constantpool-loaded-from (cpentries cpentries-s)
  (declare (xargs :guard (and (wff-constant-pool cpentries)
                              (wff-constant-pool-s cpentries-s))))
  (cond ((not (consp cpentries)) (not (consp cpentries-s)))
        ((not (consp cpentries-s)) nil)
        (t (and (equal (cpentry-type (car cpentries))
                       (cpentry-type-s (car cpentries-s)))
                (constantpool-loaded-from (cdr cpentries)
                                          (cdr cpentries-s))))))

;; (defun wff-class-rep-static (class-rep)
;;   (declare (xargs :verify-guards t))
;;   (and (true-listp class-rep)
;;        (equal (len class-rep) 8)
;;        (equal (car class-rep) 'class) 
;;        (consp (nth 3 class-rep))
;;        (consp (nth 4 class-rep))
;;        (consp (nth 5 class-rep))
;;        (consp (nth 6 class-rep))
;;        (consp (nth 7 class-rep))
;;        (true-listp (cdr (nth 3 class-rep)))
;;        (true-listp (cdr (nth 4 class-rep)))
;;        (true-listp (cdr (nth 5 class-rep)))
;;        (true-listp (cdr (nth 6 class-rep)))
;;        (true-listp (cdr (nth 7 class-rep)))))

;; moved to jvm-env

(defun wff-class-fields (class-fields)
  (if (not (consp class-fields)) 
      (equal class-fields nil)
    (and (wff-field (car class-fields))
         (wff-class-fields (cdr class-fields)))))

(defun wff-class-method-decls (method-decls)
  (if (not (consp method-decls))
      (equal method-decls nil)
    (and (wff-method-decl (car method-decls))
         (wff-class-method-decls (cdr method-decls)))))

(defthm wff-class-rep-implies-true-listp-constant-pool
  (implies (wff-class-rep class-rep)
           (true-listp (constantpool class-rep)))
  :hints (("Goal" :in-theory (enable wff-class-rep
                                     constantpool)))
  :rule-classes :forward-chaining)


(defun wff-class-rep-strong (class-rep)
  (and (wff-class-rep class-rep)
       (wff-class-fields (fields class-rep))
       (wff-static-fields-x (static-fields class-rep))
       (wff-class-method-decls (methods class-rep))
       (wff-constant-pool (constantpool class-rep))))
                         

;; Note. still need to add assertions about methods etc. Fri Jul 2 17:03:49
;; 2004

;; Fri Aug  6 16:02:26 2004. Now we come to jvm-linker.lisp.
;; we add wff-method-decls
;; 
;; We will need to prove loader produce such wff-class-rep
;; we will need to add assertions to the wff-class-static!! 
;; 
;; Fri Aug 6 16:55:21 2004. It seems that it has already been incorporated.
;; 
;;
;; let it be now.
;; 

;------------------------------------------------------------

(defconst *primitive-types* '(char short int float double long boolean byte))

(defun primitive-type? (type)
  (mem type *primitive-types*))


(defun array-type? (type-sig)
  (and (true-listp type-sig)
       (equal (len type-sig) 2)
       (equal (car type-sig) 'ARRAY)))


(defun reference-type (type)
  (or (stringp type)
      (array-type? type)))


(defun default-value (type)
  (cond ((equal type 'BYTE)  0)
        ((equal type 'SHORT) 0)
        ((equal type 'INT)   0)
        ((equal type 'LONG)  0)
        ((equal type 'FLOAT) "0.0")
        ((equal type 'DOUBLE) "0.0");
        ((equal type 'CHAR)   0)
        ((equal type 'BOOLEAN)  0)
        ((reference-type type) -1) ;; use -1 as null pointer.
        ((array-type? type) -1)    ;;
        (t 'NOT-DEFINED))) 

;----------------------------------------------------------------------

(defun array-base-type (array-type)
  (declare (xargs :guard (array-type? array-type)))
  (nth 1 array-type))


(defun type-size (type-desc)
  (if (or (equal type-desc 'LONG)
          (equal type-desc 'DOUBLE))
      2
    1))

;----------------------------------------------------------------------
;; (acl2::set-verify-guards-eagerness 0)


(defun wff-type-rep (type-rep)
  (or (primitive-type? type-rep)
      (and (consp type-rep)
           (or (and (true-listp type-rep) ;; Wed Jun  1 19:27:07 2005
                    (equal (car type-rep) 'class)
                    (equal (len type-rep) 2)
                    (stringp (cadr type-rep))) 
               ;; Tue Apr  6 18:33:46 2004. Modified to 
               ;; prevent (class 'uninitializedThis. 
               (and (array-type? type-rep)
                    (wff-type-rep (array-base-type type-rep)))))))
              


;; (defun wff-type-rep (type-rep)
;;   (or (primitive-type? type-rep)
;;       (and (consp type-rep)
;;            (or (and (equal (car type-rep) 'class)
;;                     (equal (len type-rep) 2)
;;                     (stringp (cadr type-rep))) 
;;                ;; Tue Apr  6 18:33:46 2004. Modified to 
;;                ;; prevent (class 'uninitializedThis. 
;;                (and (array-type? type-rep)
;;                     (wff-type-rep (array-base-type type-rep)))))))
              



;;; we also need to assert that it is true-listp
;;; so that we can prove 
;;;
;;; (fix-sig (normalize-type-rep type)) equal type
 

(defun normalize-type-rep (type-rep)
  (declare (xargs :guard (wff-type-rep type-rep)))
  (if (primitive-type? type-rep)
      type-rep
    (if (consp type-rep)
        (cond ((equal (car type-rep) 'class)
               (cadr type-rep))
              ((Array-Type? type-rep) 
               (make-array-type (normalize-type-rep 
                                 (array-base-type type-rep))))
              (t type-rep))
      type-rep)))

(defun wff-type-reps (type-reps)
  (if (not (consp type-reps)) t
    (and (wff-type-rep (car type-reps))
         (wff-type-reps (cdr type-reps)))))

(defun normalize-type-reps (types)
  (declare (xargs :guard (wff-type-reps types)))
  (if (not (consp types))
      nil
    (cons (normalize-type-rep (car types))
          (cdr types))))

;------------------------------------------------------------


(defun wff-fields-s (static-fields)
  (if (not (consp static-fields)) t
    (and (wff-field-s (car static-fields))
         (wff-type-rep (field-fieldtype-s (car static-fields)))
         (wff-fields-s (cdr static-fields)))))


;-----------------------------------

(defun runtime-instance-field-rep (sfield classname)
  (declare (xargs :guard (and (wff-field-s sfield)
                              (wff-type-rep (field-fieldtype-s sfield)))))
  (make-field classname 
              (field-fieldname-s sfield) 
              (normalize-type-rep (field-fieldtype-s sfield))
              (field-fieldaccessflags-s sfield)))  ;; throw away the cpindex
                                                   ;; fields in the sfield


(defun runtime-instance-fields-rep1 (static-fields classname)
  (declare (xargs :guard (wff-fields-s static-fields)))
  (if (not (consp static-fields))
      nil
    (if (static-field?-s (car static-fields))
          (runtime-instance-fields-rep1 (cdr static-fields) classname)
    (cons (runtime-instance-field-rep (car static-fields) classname)
          (runtime-instance-fields-rep1 (cdr static-fields) classname)))))

(defun runtime-instance-fields-rep (static-field-table classname)
  (declare (xargs :guard (wff-fields-s static-field-table)))
  (runtime-instance-fields-rep1 static-field-table classname))

(defun getCPvalue (i dynamic-cp) 
  (declare (xargs :guard (and (wff-constant-pool dynamic-cp)
                              (true-listp dynamic-cp)
                              (integerp i)
                              (<= 0 i)
                              (< i (len dynamic-cp)))))
  (cpentry-value (nth i dynamic-cp)))

;;; Thu Nov  4 18:27:33 2004
;;; Revised to correct the problem
;;; Misuses the cp entry as the static field's initial value!! 
;;;



(defun runtime-static-field-rep (sfield classname dynamic-cp)
  (declare (xargs :guard (and (wff-field-s sfield)
                              (wff-type-rep (field-fieldtype-s sfield))
                              (wff-constant-pool dynamic-cp)
                              (true-listp dynamic-cp)
                              (or (equal (field-cpindex-s sfield) -1)
                                  (and  (integerp (field-cpindex-s sfield))
                                        (<= 0 (field-cpindex-s sfield))
                                        (< (field-cpindex-s sfield) (len dynamic-cp)))))))
  (make-static-field classname 
              (field-fieldname-s sfield) 
              (normalize-type-rep (field-fieldtype-s sfield))
              (field-fieldaccessflags-s sfield)
              (if (equal (field-cpindex-s sfield) -1)  
                  (default-value (normalize-type-rep (field-fieldtype-s sfield)))
                (getCPvalue (field-cpindex-s sfield) dynamic-cp))))
      

;; ;;; Thu Jan  5 18:40:04 2006

;; (defun value-type-ok (type1 type2)
;;   (and (primitive-type? type1)
;;        (equal type1 type2)))


(defun value-type-ok (cp-type1 field-type2)
   (and (primitive-type? cp-type1)
        (or (and (not (equal cp-type1 'INT))
                 (equal cp-type1 field-type2))
            (and (equal cp-type1 'INT)
                 (or (equal field-type2 'BOOLEAN)
                     (equal field-type2 'BYTE)
                     (equal field-type2 'CHAR)
                     (equal field-type2 'SHORT)
                     (equal field-type2 'INT))))))


(defun value-type-ok-2 (type value)
  (and (primitive-type? type)
       (cond ((equal type 'BOOLEAN) (jvmBOOLEANp value))
             ((equal type 'BYTE)    (BYTEp value))
             ((equal type 'CHAR)    (CHARp value))
             ((equal type 'SHORT)   (SHORTp value))
             ((equal type 'INT)     (INT32p value))
             ((equal type 'LONG)    (INT64p value))
             ((equal type 'FLOAT)   (jvmFloatp value))
             ((equal type 'DOUBLE)  (Doublep value)))))




(local (in-theory (disable wff-constant-pool-entry)))

(defthm nth-in-bound-wff-constant-pool-entry
  (implies (and (<= 0 i) 
                (< i (len cps))
                (wff-constant-pool cps))
           (wff-constant-pool-entry (nth i cps))))

;; (i-am-here) ;; Thu Jan  5 20:29:27 2006

;; (defun wff-static-cp-entry-ok (static-field dynamic-cp)
;;   (declare (xargs :guard (and (wff-field-s static-field)
;;                               (static-field?-s static-field)
;;                               (wff-constant-pool dynamic-cp)
;;                               (true-listp dynamic-cp))))
;;   (or (and (equal (field-cpindex-s static-field) -1)
;;            (equal (field-fieldtype-s static-field) '"java.lang.String"))
;;       (and (integerp (field-cpindex-s static-field))
;;            (<= 0 (field-cpindex-s static-field))
;;            (< (field-cpindex-s static-field) (len dynamic-cp))
;;            (value-type-ok (cpentry-type (nth (field-cpindex-s static-field)
;;                                              dynamic-cp))
;;                           (field-fieldtype-s static-field)))))
;;;
;;; Wed Nov 10 20:51:44 2004 Why? 



(defun wff-static-cp-entry-ok (static-field dynamic-cp)
  (declare (xargs :guard (and (wff-field-s static-field)
                              (static-field?-s static-field)
                              (wff-constant-pool dynamic-cp)
                              (true-listp dynamic-cp)
                              (wff-type-rep (field-fieldtype-s static-field)))))
  (or (and (equal (field-cpindex-s static-field) -1)
           (or (equal (field-fieldtype-s static-field) 'BOOLEAN)
               (equal (field-fieldtype-s static-field) 'BYTE)
               (equal (field-fieldtype-s static-field) 'CHAR)
               (equal (field-fieldtype-s static-field) 'SHORT)
               (equal (field-fieldtype-s static-field) 'INT)
               (equal (field-fieldtype-s static-field) 'LONG)
               (reference-type (normalize-type-rep (field-fieldtype-s static-field)))))
      ;; note. only this two type are currently supported!! 
           ;; Wed Nov 10 21:56:33 2004
           ;;
           ;; should have moved this into wff-class-rep-static!! 
           ;;
           (and (integerp (field-cpindex-s static-field))
                (<= 0 (field-cpindex-s static-field))
                (< (field-cpindex-s static-field) (len dynamic-cp))
                (value-type-ok (cpentry-type (nth (field-cpindex-s static-field)
                                                  dynamic-cp))
                               (field-fieldtype-s static-field))
                (value-type-ok-2 (field-fieldtype-s static-field)
                                 (cpentry-value (nth (field-cpindex-s
                                                      static-field)
                                                     dynamic-cp))))))


;;
;; >V            (DEFUN STATIC-FIELD?-S (FIELD)
;;                      (DECLARE (XARGS :GUARD (WFF-FIELD-S FIELD)))
;;                      (MEM '*STATIC*
;;                           (FIELD-FIELDACCESSFLAGS-S FIELD)))

;; (i-am-here) ;; Thu Jan  5 20:24:52 2006

(defun wff-static-cp-ok (static-fields dynamic-cp)
  (declare (xargs :guard (and (wff-fields-s static-fields)
                              (true-listp dynamic-cp)
                              (wff-constant-pool dynamic-cp))))
  (if (not (consp static-fields)) t
    (if (not (static-field?-s (car static-fields)))
        (wff-static-cp-ok (cdr static-fields) dynamic-cp)
      (and (wff-static-cp-entry-ok (car static-fields) dynamic-cp)
           (wff-static-cp-ok (cdr static-fields) dynamic-cp)))))


(defun runtime-static-fields-rep1 (static-fields classname dynamic-cp)
  (declare (xargs :guard (and (wff-fields-s static-fields)
                              (true-listp dynamic-cp)
                              (wff-constant-pool dynamic-cp)
                              (wff-static-cp-ok static-fields dynamic-cp))))
  (if (not (consp static-fields))
      nil
    (if (not (static-field?-s (car static-fields)))
          (runtime-static-fields-rep1 (cdr static-fields) classname dynamic-cp)
    (cons (runtime-static-field-rep (car static-fields) classname dynamic-cp)
          (runtime-static-fields-rep1 (cdr static-fields) classname dynamic-cp)))))


(defun runtime-static-fields-rep (static-field-table classname dynamic-cp)
  (declare (xargs :guard (and (wff-fields-s static-field-table)
                              (true-listp dynamic-cp)
                              (wff-constant-pool dynamic-cp)
                              (wff-static-cp-ok static-field-table dynamic-cp))))
  (runtime-static-fields-rep1 static-field-table classname dynamic-cp))



(defun runtime-code-rep0 (scode)
  (declare (xargs :guard (wff-code-s scode)))
  (make-code 
   (code-max-stack-s scode)
   (code-max-local-s scode)
   (code-code-length-s scode)
   (code-instrs-s    scode)
   (code-handlers-s  scode)
   (code-stackmaps-s scode)))

(defun runtime-code-rep (scode accessflag)
  (declare (xargs :guard (or (mem '*native* accessflag)
                             (mem '*abstract* accessflag)
                             (wff-code-s scode))))
  (cond ((mem '*native* accessflag)   (make-code 0 0 0 nil nil nil))
        ((mem '*abstract* accessflag) (make-code 0 0 0 nil nil nil))
        (t (runtime-code-rep0 scode)))) 

(defun runtime-method-rep-guard (amethod)
  (and (wff-method-decl-s amethod)
       (wff-type-reps (method-args-s amethod))
       (or (equal (method-returntype-s amethod) 'VOID)
           (wff-type-rep (method-returntype-s amethod)))
       ;; Sat Oct 23 18:55:58 2004
       (or (mem '*native* (method-accessflags-s amethod))
           (mem '*abstract* (method-accessflags-s amethod))
           (and (wff-code-s (method-code-s amethod))
                (integerp (code-max-local-s (method-code-s amethod)))
                (integerp (code-max-stack-s (method-code-s amethod)))))))
;;; Mon Nov  8 19:16:03 2004. 
;;;
;;; fixed from consistent-class-decl requirement!! 
;;;

(defun runtime-method-rep (amethod classname)
  (declare (xargs :guard (runtime-method-rep-guard  amethod)))
  (make-method classname 
              (method-methodname-s  amethod) 
              (normalize-type-reps (method-args-s        amethod))
              (if (equal (method-returntype-s amethod) 'VOID)
                  'VOID
                (normalize-type-rep  (method-returntype-s  amethod)))
              (method-accessflags-s amethod)
              (runtime-code-rep 
               (method-code-s  amethod) (method-accessflags-s amethod))))

(defun runtime-method-rep-guards (methods)
  (if (not (consp methods)) t
      (and (runtime-method-rep-guard (car methods))
           (runtime-method-rep-guards (cdr methods)))))

(defun runtime-methods-rep1 (methods classname)
  (declare (xargs :guard (runtime-method-rep-guards methods)))
  (if (not (consp methods))
      nil
    (cons (runtime-method-rep (car methods) classname)
          (runtime-methods-rep1 (cdr methods) classname))))

;(i-am-here)

(defun runtime-methods-rep (static-method-table classname)
  (declare (xargs :guard (runtime-method-rep-guards static-method-table)))
  (runtime-methods-rep1 static-method-table classname))



;----------------------------------------------------------------------

(defun wff-fields-s-x (fields)
  (if (not (consp fields)) t
    (and (wff-field-s (car fields))
         (wff-fields-s-x (cdr fields)))))


;; (defun wff-class-rep-static-strong (class-rep)
;;   (and (wff-class-rep-static class-rep)
;;        (wff-fields-s (fields-s class-rep))
;;        ;; missing assertions about fields being wff. 
;;        (wff-fields-s-x (fields-s class-rep))
;;        (runtime-method-rep-guards (methods-s class-rep))
;;        (wff-constant-pool-s (constantpool-s class-rep))))


(defthm nth-in-bound-wff-constant-pool-entry-s
  (implies (and (<= 0 i) 
                (< i (len cps))
                (wff-constant-pool-s cps))
           (wff-constant-pool-entry-s (nth i cps))))




(defun wff-static-cp-entry-ok-s (static-field static-cp)
  (declare (xargs :guard (and (wff-field-s static-field)
                              (static-field?-s static-field)
                              (wff-constant-pool-s static-cp)
                              (true-listp static-cp)
                              (wff-type-rep (field-fieldtype-s static-field)))))
  (or (and (equal (field-cpindex-s static-field) -1)
           (or (equal (field-fieldtype-s static-field) 'BOOLEAN)
               (equal (field-fieldtype-s static-field) 'BYTE)
               (equal (field-fieldtype-s static-field) 'CHAR)
               (equal (field-fieldtype-s static-field) 'SHORT)
               (equal (field-fieldtype-s static-field) 'INT)
               (equal (field-fieldtype-s static-field) 'LONG)
               (reference-type (normalize-type-rep (field-fieldtype-s static-field)))))
      (and (integerp (field-cpindex-s static-field))
           (<= 0 (field-cpindex-s static-field))
           (< (field-cpindex-s static-field) (len static-cp))
           (value-type-ok (cpentry-type-s (nth (field-cpindex-s static-field)
                                               static-cp))
                          (field-fieldtype-s static-field))
           (value-type-ok-2 (field-fieldtype-s static-field)
                            (cpentry-value-s (nth (field-cpindex-s static-field)
                                                  static-cp))))))



(defun wff-static-cp-ok-s (static-fields static-cp)
  (declare (xargs :guard (and (wff-fields-s static-fields)
                              (true-listp static-cp)
                              (wff-constant-pool-s static-cp))))
  (if (not (consp static-fields)) t
    (if (not (static-field?-s (car static-fields)))
        (wff-static-cp-ok-s (cdr static-fields) static-cp)
      (and (wff-static-cp-entry-ok-s (car static-fields) static-cp)
           (wff-static-cp-ok-s (cdr static-fields) static-cp)))))


(defthm wff-class-rep-static-implies-true-listp
  (implies (wff-class-rep-static class-rep)
           (true-listp (constantpool-s class-rep)))
  :hints (("Goal" :in-theory (enable wff-class-rep-static constantpool-s)))
  :rule-classes :forward-chaining)


(defun all-fields-static-final (fields)
  (declare (xargs :guard (and (wff-fields-s fields))))
  (if (not (consp fields)) t
    (and (MEM '*STATIC*
              (FIELD-FIELDACCESSFLAGS-S (car FIELDs)))
         (MEM '*FINAL*
              (field-fieldaccessflags-s (car fields)))
         (all-fields-static-final (cdr fields)))))
      

(defun wff-interface-class-static (class-rep)
  (declare (xargs :guard (and (wff-class-rep-static class-rep)
                              (wff-fields-s (fields-s class-rep)))))
  (and (equal (super-s class-rep) "java.lang.Object")
       (all-fields-static-final (fields-s class-rep))))
  

(defun collect-static-field-names (fields)
  (declare (xargs :guard (wff-fields-s fields)))
  (if (not (consp fields)) nil
    (cons (field-fieldname-s (car fields))
          (collect-static-field-names (cdr fields)))))


(defun wff-class-rep-static-strong (class-rep)
  (and (wff-class-rep-static class-rep)
       (wff-fields-s (fields-s class-rep))
       (nodup-set (collect-static-field-names (fields-s class-rep)))
       (or (not (mem '*interface*  (accessflags-s class-rep)))
           (wff-interface-class-static class-rep))
       (wff-fields-s-x (fields-s class-rep))
       (runtime-method-rep-guards (methods-s class-rep))
       (wff-constant-pool-s (constantpool-s class-rep))
       (wff-static-cp-ok-s (fields-s class-rep)
                           (constantpool-s class-rep))))


;; (defun constantpool-loaded-from (cpentries cpentries-s)
;;   (declare (xargs :guard (and (wff-constant-pool cpentries)
;;                               (wff-constant-pool-s cpentries-s))))
;;   (cond ((not (consp cpentries)) (not (consp cpentries-s)))
;;         ((not (consp cpentries-s)) nil)
;;         (t (and (equal (cpentry-type (car cpentries))
;;                        (cpentry-type-s (car cpentries-s)))
;;                 (constantpool-loaded-from (cdr cpentries)
;;                                           (cdr cpentries-s))))))


(defun fields-loaded-from (fields sfields classname)
  (declare (xargs :guard (wff-fields-s  sfields)))
  (equal (runtime-instance-fields-rep sfields classname)
         fields))

;;; Mon Jun 13 17:29:08 2005 
;;; worry about static variable later!!! 
;;;
;;
;;                              (RUNTIME-INSTANCE-FIELDS-REP
;;                                   (FIELDS-S JVM::CLASS-DESC)

;;(i-am-here)

(defun collect-field-names (field-decls)
  (declare (xargs :guard (wff-class-fields field-decls)))
  (if (not (consp field-decls)) nil
    (cons (field-fieldname (car field-decls))
          (collect-field-names (cdr field-decls)))))


(defthm nodup-set-fields-s-nodup-set-fields
  (implies (nodup-set (collect-static-field-names fields-s))
           (nodup-set (collect-field-names 
                       (runtime-instance-fields-rep
                        fields-s classname))))
  :hints (("Goal" :do-not '(generalize))))


(defun methods-loaded-from (methods static-methods classname)
  (declare (xargs :guard (RUNTIME-METHOD-REP-GUARDS static-methods)))
  (equal (runtime-methods-rep static-methods classname)
         methods))

(defun class-is-loaded-from-helper (class-rep class-rep-static)
  (declare (xargs :guard (and (wff-class-rep-strong class-rep) 
                              (wff-class-rep-static-strong class-rep-static))))
  (and (equal (classname  class-rep) (classname-s  class-rep-static))
       (equal (super      class-rep) (super-s      class-rep-static))
       (equal (interfaces class-rep) (interfaces-s class-rep-static))
       ;; Mon Jun 13 17:20:05 2005 new additions. 
       (fields-loaded-from (fields class-rep) (fields-s class-rep-static)
                           (classname class-rep))
       ;; Thu Jan  5 13:27:18 2006
       (methods-loaded-from (methods class-rep) (methods-s class-rep-static)
                            (classname-s class-rep-static))
       ;; we also need the access flags are preserved 
       (equal (class-accessflags class-rep) (accessflags-s class-rep-static))
       (constantpool-loaded-from (constantpool class-rep)
                                 (constantpool-s class-rep-static))))
       ;; this also stipulated whether is it an interface type or not.



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




(defun wff-static-class-table (scl)
  (declare (xargs :verify-guards t))
  (if (not (consp scl)) t
    (and (wff-class-rep-static (car scl))
         (wff-static-class-table (cdr scl)))))

(defun wff-instance-class-table-strong (icl)
  (declare (xargs :verify-guards t))
  (if (not (consp icl)) t 
    (and (wff-class-rep-strong (car icl))
         (wff-instance-class-table-strong (cdr icl)))))



(defun wff-static-class-table-strong (scl)
  (declare (xargs :verify-guards t))
  (if (not (consp scl)) t
    (and (wff-class-rep-static-strong (car scl))
         (wff-static-class-table-strong (cdr scl)))))


;; (defun class-by-name-s (name scl)
;;   (declare (xargs :guard (wff-static-class-table scl)))
;;   (if (not (consp scl))
;;       (mv nil nil)
;;     (if (equal (classname-s (car scl))
;;                name)
;;         (mv t (car scl))
;;       (class-by-name-s name (cdr scl)))))


(defun class-exists-s? (n scl)
  (declare (xargs :guard (wff-static-class-table scl)))
  (mv-let (found rep)
          (class-by-name-s n scl)
          (declare (ignore rep))
          found))

(defthm class-exists-s-implies-wff-static-rep
   (implies (and (class-exists-s? n scl)
                 (wff-static-class-table-strong scl))
            (wff-class-rep-static-strong (mv-let (found rep)
                                                 (class-by-name-s n scl)
                                                 (declare (ignore found))
                                                 rep))))


(defthm class-exists-implies-wff-rep-strong
   (implies (and (class-exists? n cl)
                 (wff-instance-class-table-strong cl))
            (wff-class-rep-strong (class-by-name n cl))))


(defthm wff-class-rep-strong-is-strong
  (implies (wff-class-rep-strong rep)
           (wff-class-rep rep))
  :rule-classes :forward-chaining)

(defthm wff-instance-class-table-strong-is-strong
  (implies (wff-instance-class-table-strong cl)
           (wff-instance-class-table cl))
  :rule-classes :forward-chaining)


(defthm wff-static-class-table-strong-is-strong
  (implies (wff-static-class-table-strong scl)
           (wff-static-class-table scl))
  :rule-classes :forward-chaining)


;; (defthm wff-static-class-table-strong-is-strong-tmp
;;   (implies (wff-static-class-table-strong scl)
;;            (jvm::wff-static-class-table scl))
;;   :rule-classes :forward-chaining)


(defthm wff-class-static-rep-strong-is-strong
  (implies (wff-class-rep-static-strong rep)
           (wff-class-rep-static rep))
  :rule-classes :forward-chaining)



;(in-theory (disable wff-class-rep-static-strong wff-class-rep-strong
;                    wff-class-rep
;                    class-exists? class-by-name class-by-name-s class-exists-s?))

;; These are too general!!

(defthm wff-class-rep-if-exists-in-wff-instance-table
  (implies (and (class-exists? n cl)
                (wff-instance-class-table cl))
           (wff-class-rep (class-by-name n cl))))



(defun class-table-is-loaded-from (cl scl)
  (declare (xargs :guard (and (wff-instance-class-table-strong cl)
                              (wff-static-class-table-strong scl))))
  (if (not (consp cl)) t
    (and (class-exists? (classname (car cl)) cl)
         (class-exists-s? (classname (car cl)) scl)
         (mv-let (def-found rep)
                 (class-by-name-s (classname (car cl)) scl)
                 (declare (ignore def-found))
                 (class-is-loaded-from-helper (class-by-name (classname (car cl)) cl)
                                              rep))
         (class-table-is-loaded-from (cdr cl) scl))))

;; we chose not to disable those functions. ACL2 will get it anyway!

;; Thu Jan  5 15:50:23 2006
;;
 

(local 
 (defthm class-table-is-loaded-from-test
   (class-table-is-loaded-from (cdr (nth 1 *test.classtable*))
                               (env-class-table *test.env*))))


;----------------------------------------------------------------------
;; Thu Jan  5 15:01:26 2006

(acl2::set-verify-guards-eagerness 0)


;; (defpredicate method-static-match-guard (method-s)
;;   (and (wff-method-decl-s method-s)
;;        (wff-type-reps (method-args-s method-s))
;;        (or (equal (method-returntype-s method-s) 'VOID)
;;            (wff-type-rep (method-returntype-s method-s)))))


;; (defun method-static-match (name args returntype method-s)
;;   (declare (xargs :guard (method-static-match-guard method-s)))
;;   (and (equal (method-methodname-s method-s) name)
;;        (equal (normalize-type-reps (method-args-s method-s)) args)
;;        (if (equal returntype 'VOID)
;;            (equal (method-returntype-s method-s) 'VOID)
;;          (equal (normalize-type-rep (method-returntype-s method-s))
;;                 returntype))))



(defun method-static-match (name args returntype method-s)
  (and (equal (method-methodname-s method-s) name)
       (equal (normalize-type-reps (method-args-s method-s)) args)
       (if (equal returntype 'VOID)
           (equal (method-returntype-s method-s) 'VOID)
         (equal (normalize-type-rep (method-returntype-s method-s))
                returntype))))



;; (defpredicate method-by-name-s-guard (methods-s)
;;   (if (not (consp methods-s)) t
;;     (and (method-static-match-guard (car methods-s))
;;          (method-by-name-s-guard (cdr methods-s)))))



(defun method-by-name-s (name args returntype methods-s)
  (if (not (consp methods-s))
      (mv nil nil)
    (if (method-static-match name args returntype (car methods-s))
        (mv t (car methods-s))
      (method-by-name-s name args returntype (cdr methods-s)))))


;; (defun method-by-name-s (name args returntype methods-s)
;;   (declare (xargs :guard (method-by-name-s-guard methods-s)))
;;   (if (not (consp methods-s))
;;       (mv nil nil)
;;     (if (method-static-match name args returntype (car methods-s))
;;         (mv t (car methods-s))
;;       (method-by-name-s name args returntype (cdr methods-s)))))


;; (in-theory (disable method-static-match-guard
;;                     method-by-name-s-guard))


;----------------------------------------------------------------------
