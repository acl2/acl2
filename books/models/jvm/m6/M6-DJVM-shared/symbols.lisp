(in-package "JVM")

(defconst *jvm-class-table-symbols*
  '(make-class-table-wff ;;??
    wff-class-table
    make-runtime-class-rep
    wff-class-rep
    classname
    class-ref
    class-accessflags
    constantpool
    super
    interfaces
    fields
    methods
    static-fields
    class-status
    init-thread-id
    class-rep-set-classname
    class-rep-set-super
    class-rep-set-constantpool
    class-rep-set-fields
    class-rep-set-methods
    class-rep-set-interfaces
    class-rep-set-static-fields
    class-rep-set-class-status
    class-rep-set-accessflags
    class-rep-set-init-thread-id
    class-rep-set-class-ref
    replace-class-table-entry
    wff-string-cp-entry
    wff-int-cp-entry
    wff-long-cp-entry
    wff-constant-pool-entry
    wff-constant-pool
    cpentry-type
    cpentry-value
    make-string-cp-entry
    string-value-cp-entry
    make-int-cp-entry
    int-value-cpentry
    make-long-cp-entry
    long-value-cpentry
    make-float-cp-entry
    float-value-cpentry
    make-double-cp-entry
    make-field
    wff-field
    wff-fields-x
    field-classname
    field-fieldname
    field-fieldtype
    field-fieldaccessflags
    make-static-fields
    wff-static-fields
    static-fields-fields
    make-static-field
    wff-static-field
    wff-static-fields-x
    static-field-classname
    static-field-fieldname
    static-field-fieldtype
    static-field-accessflags
    static-field-fieldvalue
    static-field-set-value
    make-method
    wff-method-decl
    method-classname
    method-methodname
    method-args
    method-returntype
    method-accessflags
    method-code
    make-code
    wff-code
    code-max-stack
    code-max-local
    code-code-lenght
    code-instrs
    code-handlers
    code-stackmaps
    make-accessflags
    wff-inst
    wff-insts 
    inst-offset
    inst-inst
    inst-opcode
    inst-arg
    make-array-type
    make-array-class-table-entry
    wff-array-class-table-rep
    wff-array-class-table
    array-sig
    array-access-flags
    array-class-ref
    add-array-class-table-entry
    wff-instance-class-table
    class-by-name
    isClassTerm
    class-exists?
    array-class-by-name
    isInterface
    super-exists
    class-rep-in-error-state?
    all-class-names
    unseen-classes
    unseen-classes-x
    all-interfaces-bounded?
    class-hierachy-consistent1-class-n
    class-hierachy-consistent1-aux
    class-hierachy-consistent1
    superclass-chain-no-loop-class-n
    interfaces-chains-no-loop-class-n
    class-hierachy-consistent2-class-n
    class-hierachy-consistent2-aux
    class-hierachy-consistent2
    consistent-class-hierachy
    constantpool-loaded-from
    wff-class-rep-strong
    wff-class-rep-static-strong
    collect-field-names
    collect-static-field-names
    NODUP-SET-FIELDS-S-NODUP-SET-FIELDS
    class-is-loaded-from-helper
    wff-static-class-table
    wff-instance-class-table-strong
    wff-static-class-table-strong
    class-exists-s?
    class-table-is-loaded-from
    ))



(defconst *jvm-internal-primitives*
  '(push 
    pop 
    top 
    deref 
    alloc  
    sub-list 
    setChars 
    make-acl2-string 
    code-to-chars 
    make-trace 
    th-counters 
    rtrace 
    init-trace 
    add-obj-th-count))
  

(defconst *jvm-env-symbols* 
  '(make-env
    wff-env
    env-class-table
    make-static-class-table
    make-static-class-desc
    wff-class-rep-static
    classname-s
    super-s
    constantpool-s
    fields-s
    methods-s
    interfaces-s
    accessflags-s
    wff-string-cp-entry-s
    wff-int-cp-entry-s
    wff-long-cp-entry-s
    wff-constant-pool-entry-s
    wff-constant-pool-s
    cpentry-type-s
    make-string-cp-entry-s
    string-value-cp-entry-s
    make-int-cp-entry-s
    int-value-cpentry-s
    make-long-cp-entry-s
    long-value-cpentry-s
    make-float-cp-entry-s
    float-value-cpentry-s
    make-double-cp-entry-s
    double-value-cpentry-s
    make-field-s
    wff-field-s
    field-fieldname-s
    field-fieldtype-s
    field-fieldaccessflags-s
    field-cpindex-s
    static-field?-s
    make-method-s
    wff-method-decl-s
    method-methodname-s
    method-args-s
    method-returntype-s
    method-accessflags-s
    method-code-s
    make-code-s
    wff-code-s
    code-max-stack-s
    code-max-local-s
    code-code-length-s
    code-instrs-s
    code-handlers-s
    code-stackmaps-s
    wff-static-class-table
    class-by-name-s
    make-class-def
    make-class-table
    ))

(defconst *jvm-thread-symobls* 
  '(make-thread-table
    make-thread
    wff-thread
    thread-id
    thread-saved-pc
    thread-call-stack
    thread-state
    thread-mref
    thread-mdepth
    thread-ref
    thread-set-id
    thread-set-saved-pc
    thread-set-call-stack
    thread-set-state
    thread-set-mref
    thread-set-mdepth
    thread-set-ref
    make-method-ptr
    wff-method-ptr
    method-ptr-classname
    method-ptr-methodname
    method-ptr-args-type
    method-ptr-returntype
    make-frame
    wff-call-frame
    return-pc
    resume-pc
    operand-stack
    locals
    method-ptr
    sync-obj-ref
    frame-aux
    frame-set-return-pc
    frame-set-operand-stack
    frame-set-locals
    frame-set-method-ptr
    frame-set-sync-obj-ref
    frame-set-aux
    wff-thread-table
    thread-by-id
    thread-id-by-ref
    replace-thread-table-entry
    add-thread-entry
    make-init-operand-stack
    new-thread-id
    add-no-dup
    set-thread-state-flag
    remove-all
    remove-thread-state-flag
    set-thread-state-by-id
    buildThread
    getVMthread
    thread-exists?
    current-thread-exists?
    collect-thread-id
    unique-id-thread-table
    method-stackMap
    method-maxStack
    method-maxLocals  
    method-handlers))


(defconst *jvm-frame-manipulation-primitives-symbols* 
  '(wff-call-stack
    current-frame-guard
    current-frame
    current-method-ptr
    localx
    current-class
    alert
    push-stack-of-thread
    pushStack
    popStack-of-thread
    popStack
    set-local-at-of-thread
    state-set-local-at
    topStack-guard
    topStack
    secondStack
    pushFrame0
    pushFrame
    popFrame
    make-method-ptr
    wff-method-ptr
    ))

(defconst *jvm-object-manipluation-primitives-symbols*
  '(make-field-value-pair
    make-immediate-field-bindings
    wff-class-fields
    build-class-fields-bindings
    build-immediate-instance-data-guard
    build-immediate-instance-data
    build-a-java-visible-instance-data-guard
    build-a-java-visible-instance-data
    make-java-lang-Object-java-visible-part
    build-a-java-visible-instance-guard
    build-a-java-visible-instance
    jvp-setfield
    jvp-getfield
    build-common-info
    build-INSTANCE-specific-info
    build-an-instance
    build-ARRAY-specific-info
    array-type
    array-bound
    array-data
    element-at-guard
    element-at
    init-array
    make-array
    set-element-at-guard
    set-element-at
    build-an-array-instance
    new-array
    set-element-at-array-guard
    set-element-at-array
    set-array-content-guard
    set-array-content1
    set-array-content
    build-a-javaString
    build-instanceClass-info
    isInstanceClass?
    specific-info-classname
    build-java-lang-Class-java-visible-part
    build-an-instanceClass
    build-instanceClassArrayClass-info
    isArrayClass?
    specific-info-array-desc
    build-instanceClassArrayClass
    build-throwable-specific-info
    specific-info-throwable-instance-message
    isSubClassOf
    build-a-Throwable-instance
    instantiate
    new-instance
    type-by-class-ref
    m6-putfield
    m6-getfield
    field-access-guard
    ))


(defconst *jvm-state-symbols* 
  '(make-state
    wff-state
    pc
    current-thread
    heap
    thread-table
    class-table
    env
    error-flag
    aux
    state-set-pc
    state-set-current-thread
    state-set-heap
    state-set-thread-table
    state-set-class-table
    state-set-env
    state-set-error-flag
    state-set-aux
    instance-class-table
    array-class-table
    trace-aux
    aux-set-trace
    ptable-aux
    set-ptable-aux
    mtrace
    pname
    state-set-trace
    pending-exception-aux
    set-pending-exception-aux-safe
    set-pending-exception-aux
    pending-exception
    state-set-pending-exception-safe
    state-set-instance-class-table
    state-set-array-class-table
    add-instance-class-entry
    setClassInitialThread
    setClassStatus
    class-initialized?
    external-class-table
    update-trace
    m6-internal-error
    fatalError
    no-fatal-error?
    alertUser
    class-ref-by-name
    wff-aux
    heap-init-map
    ))

(defconst *jvm-type-value-symbols* 
  '(primitive-type?
    array-type?
    reference-type
    default-value
    array-base-type
    type-size
    wff-type-rep
    wff-type-reps
    normalize-type-rep
    normalize-type-reps
    primitive-array?
    isClassType
    isArrayType
    wff-array-type
    array-component-type
    primitive-type
    primitive-opvalue-type
    reference-type-s
    array-type-s
    wff-type-desc
    classname-classtype
    compound
    isJavaLangObject
    component-type
    ADDRp
    CHARp
    jvmBOOLEANp
    SHORTp
    BYTEp
    jvmFLOATp
    DOUBLEp
    ))


(defconst *jvm-class-hierachy-symbols* 
  '(classClassName
    classSuperClassName
    all-class-names
    unseen-class-measure
    superclass-no-loop1-measure
    superclass-no-loop1
    superclass-no-loop
    collect-superclass-list1
    collect-superclass-list
    isSubClassOf1
    isJavaSubclassOf-guard
    isJavaSubClassOf-measure
    isJavaSubclassof1
    isJavaSubclassOf
    isJavaClassAssignmentCompatible
    isJavaAssignmentCompatible
    assignmentCompatible
    ))


(defconst *jvm-obj-symbols* 
  '(
    make-object
    wff-obj
    common-info
    specific-info
    java-visible-portion
    obj-set-common-info
    obj-set-specific-info
    obj-set-java-visible-portion
    make-common-info
    wff-common-info
    hashcode
    monitor
    class-ptr
    obj-hashcode
    obj-monitor
    obj-class-ptr
    obj-type
    common-info-set-hashcode
    common-info-set-monitor
    common-info-set-class-ptr
    make-monitor
    wff-monitor
    new-monitor
    owner
    depth
    mqueue
    cqueue
    monitor-set-owner
    monitor-set-depth
    monitor-set-mqueue
    monitor-set-cqueue
    make-INSTANCE_CLASS-specific-info
    make-ARRAY_CLASS-specific-info
    make-ARRAY-specific-info
    make-STRING-specific-info
    make-INSTANCE-specific-info
    make-INSTANCECLASS-specific-info
    make-instanceclassarrayclass-info
    make-THROWABLE-specific-info
    wff-internal-heap-obj
    wff-class-ptr
    wff-common-info-strong
    wff-jvp
    wff-INSTANCE_CLASS-specific-info
    wff-ARRAY_CLASS-specific-info
    wff-ARRAY-specific-info
    wff-STRING-specific-info
    wff-THROWABLE-specific-info
    wff-GENERIC_OBJECT-specific-info
    wff-specific-info
    wff-obj-strong
    wff-data-field
    fieldname
    fieldvalue
    wff-internal-array
    wff-heap
    wff-heap-strong
    ))
(defconst *jvm-thread-primitives-symbols* 
  '(signalTimeToReschedule
    dismantleThread
    resumeThread-inv
    resumeThread
    storeExecutionEnvironment
    loadExecutionEnvironment
    suspendThread1
    suspendThread
    startThread
    stopThread))


(defconst *jvm-monitor-primitives-symbols* 
  '(removePendingAlarm
    registerAlarm
    dequeue-h
    dequeue-r
    obj-monitor-by-ref
    update-obj-monitor
    removeMonitorWait-inv
    removeMonitorWait
    add-to-queue-end
    addMonitorWait
    removeCondvarWait2
    removeCondvarWait1
    removeCondvarWait
    addCondvarWait
    MonitorStatusOwn
    MonitorStatusError
    MonitorStatusWaiting
    MonitorStatusRelease
    class_ready
    ALL
    ))

(defconst *jvm-loader-primitives-symbols* 
  '(countdown-measure
    str-to-array-char-data
    str-to-array-obj
    make-immediate-string-part
    make-java-lang-string-visible-part
    ACL2-str-to-JavaString
    ACL2-str-to-JavaString-ref))

(defconst *jvm-loader-constant-pool-primitivies-symbols* 
  '(load_CP_entry
    load_CP_entries
    load_CP
    runtime-instance-field-rep
    runtime-static-field-rep
    runtime-instance-fields-rep1
    runtime-instance-fields-rep
    runtime-static-fields-rep1
    runtime-static-fields-rep
    runtime-code-rep
    runtime-method-rep
    runtime-methods-rep1
    runtime-methods-rep))


(defconst *jvm-loader-symbols* 
  '(class-loaded?
    ArrayClassLoaded1?
    ArrayClassLoaded?
    load_class2
    all-class-names-s
    unloaded-class-count
    loader-measure
    load_class_1-inv
    load_class_2-inv
    trivial-inv-env-do-not-change
    induct-measure
    load_class_x
    load_class
    gen-access-flags
    load_array_class2
    load_array_class
    load_primitive_array_classes
    getClass
    getArrayClass11
    getArrayClass
    load-JavaSystemClasses
    load_classes
    class-exists-externally?
    classes-exists-externally?
    all-not-loaded?
    correctly-loaded?
    loader-inv
    all-loaded?
    ))


(defconst *jvm-linker-symbols* 
  '(resolveClassReference1
    hasAccessToClass
    resolveClassReference
    methodCP-classname
    methodCP-methodname
    methodCP-args-type
    methodCP-returntype
    methodCP-to-method-ptr
    searchMethod
    deref-method
    lookupMethod-measure
    lookupMethod-inv
    lookupMethod
    hasAccessToMethod
    resolveMethodReference
    getSpecialMethod1
    getSpecialMethod
    static-field-size
    fieldCP-classname
    fieldCP-fieldname
    fieldCP-fieldtype
    make-field-ptr
    field-ptr-classname
    field-ptr-fieldname
    field-ptr-type
    fieldCP-to-field-ptr
    searchStaticFields
    deref-static-field
    lookupStaticField-measure
    lookupStaticField-inv
    lookupStaticField
    hasAccessToField
    resolveStaticFieldReference
    static-field-class-rep
    searchFields
    deref-field
    lookupField-measure
    lookupField-inv
    lookupField
    resolveFieldReference
    make-callback-func-ptr
    callback-funcname
    callback-func-ptr?
    clinitMethod-ptr
    initMethod-ptr
    RunCustomCode-method-ptr
    wff-method-decls
    method-exists?
    wff-fieldCP
    resolveClassReference-guard))

(defconst *jvm-verifier-symbols*
  '(class-rep-verified?
    verify-class1
    check-super-class-isnt-final
    check-interface-super-class-is-JavaLangObject
    verify-class))


(defconst *jvm-monitor-failure-as-fatalError-symbols*
  '(monitorNotifyX
    classMonitorNotifyX
    monitorExitX
    classMonitorExitX
    monitorEnterX
    classMonitorEnterX
    monitorWait1X
    monitorWaitX
    classMonitorWaitX))


(defconst *jvm-object-type-hierachy-symbols*
  '(superClass1-measure
    isSuperClass1-invariant
    isSuperClass1
    isSuperClass
    unseen-class-count
    classImplements-measure
    classImplementsInterface1-invariant
    classImplementsInterface1-aux-invariant
    interfacesImplementsInterface1-inv
    simple-inv1
    implementInterface-x-measure
    implementInterface-x
    interfacesImplementsInterface
    classImplementsInterface
    isAssignableTo
    ))


(defconst *jvm-semantic-primitives-2-symbols* 
  '(set-curframe-sync-obj
    set-top-frame-return-pc))

(defconst *jvm-exceptions-symbols* 
  '(ERROR_THROW
    handler-start
    handler-end
    handler-entry-point
    handler-exception-type
    JavaString-to-ACL2-str
    throw-exception2
    find-handler
    getExceptionMessage
    monitorExit
    call-stack-depth
    locked-stage
    exception-measure
    invariant-exception-handling-1
    invariant-exception-handling-2
    release-lock-invariant
    release-lock-on-sync-obj
    throw-exception1
    throw-exception
    raise-exception1
    ;; raise-exception 
    ;; Fri Apr  9 19:30:22 2004
    ;; Take out. So that m6::raise-exception 
    ;; is different from djvm::raise-excecption
    ))



(defconst *jvm-monitor-failure-as-java-Exception* 
  '(monitorNotify
    classMonitorNotify
    monitorExit
    classMonitorExit
    monitorEnter
    classMonitorEnter
    monitorWait1
    monitorWait
    classMonitorWait
    ))

(defconst *jvm-bytecode-symbols* 
  '(;; ADVANCE-PC
    wff-inst
    wff-one-arg
    arg 
    local-at
    ;; LP
    inst-by-offset1
    inst-by-offset
    next-inst
    inst-size
    field-size
    fatalSlotError))

(defconst *other-symbols* 
  '(INSTANCE_CLASS
    ARRAY_CLASS
    OBJECT
    ;; FRAME
    *public* 
    *static* 
    *private*
    *native*
    *abstract*
    *class*
    *super*
    *protected*
    *synchronized*
    *final*
    *runClinit*
    *initInitialThreadBehavior*
    *newInstanceReturnObject*
    *initThreadBehaviorFromThread*
    *interruptedGetOutput1Behavior*
    thread_just_born
    thread_suspended
    thread_active
    thread_dead
    thread_monitor_wait 
    thread_convar_wait
    generic_object
    parameters
    return-type
    code
    max_stack
    max_local
    code_length
    parsedcode
    exceptions
    stackmap
    return_pc
    returntype
    endofcode
    methodcp
    SHORT
    ADDR
    CLASS
    CONSTANT_POOL
    FIELDS
    METHODS
    INTERFACES
    ACCESSFLAGS
    ATTRIBUTES))

(defconst *opcode-symbols* 
  '(CUSTOMCODE    

    ICONST_0      
    ICONST_1      
    ICONST_2      
    ICONST_3      
    ICONST_4      
    ICONST_5      
    ICONST_M1     

    ACONST_NULL   


    ISTORE        
    ISTORE_0      
    ISTORE_1      
    ISTORE_2         
    ISTORE_3         

    ILOAD         
    ILOAD_0       
    ILOAD_1       
    ILOAD_2       
    ILOAD_3       

    ANEWARRAY ;; Fri Aug 19 22:36:07 2005 failed proof found this. 

    ASTORE        
    ASTORE_0      
    ASTORE_1      
    ASTORE_2         
    ASTORE_3         

    ALOAD         
    ALOAD_0       
    ALOAD_1       
    ALOAD_2       
    ALOAD_3       

    AALOAD        
    AASTORE       

    IALOAD        
    IASTORE       

    LCONST_0      
    LCONST_1      
    LCMP

    LALOAD        
    LASTORE       

    BALOAD        
    BASTORE       

    CALOAD        
    CASTORE       

    SALOAD        
    SASTORE       

    IADD          
    IINC          
    INEG          

    IMUL          
    IDIV          
    IREM          


    ISUB          

    POP           
    POP2          

    NEWARRAY      
    ARRAYLENGTH   


    MONITORENTER  
    MONITOREXIT   

    CHECKCAST     


    RETURN        
    NEW           
    DUP           
    DUP_X1        
    DUP_X2        
    DUP2          
    DUP2_X1       
    DUP2_X2       


    INVOKESPECIAL 
    INVOKESTATIC  
    INVOKEVIRTUAL 
    INVOKEINTERFACE
    PUTFIELD      

    GETFIELD      
    GETSTATIC     

    PUTSTATIC     
    BIPUSH        

    LDC           
    IFNULL        
    IFNONNULL     
    IFEQ          
    IFNE          
    IFLT          
    IFGE          
    IFGT          
    IFLE          
    IF_ICMPEQ     
    IF_ICMPNE     
    IF_ICMPLT     
    IF_ICMPGE     
    IF_ICMPGT     
    IF_ICMPLE     
    GOTO          
    IRETURN       
    RETURN        
    ARETURN       
    ATHROW        
    JSR           
    RET 
    
    HALT 
))


;;
;; needed for the program proof!!
;; such as (popStack (pushStack any s)) == s
;; 
;; We need such wff-ness. 

(defconst *wff-data-structure-symobls* 
  '(wff-method-ptr-regular
    wff-call-frame-regular
    wff-call-stack-regular
    wff-thread-regular
    wff-thread-table-regular
    wff-state-regular))


(defconst *m6-djvm-shared-symbols* 
  (remove-duplicates ; Matt K. mod: replacement for remove-duplicates-eql
   (union-eq *other-symbols*
            (union-eq *wff-data-structure-symobls*
            (union-eq *opcode-symbols*
            (union-eq *jvm-env-symbols*
                      (union-eq *jvm-class-table-symbols* 
                                (union-eq *jvm-thread-symobls*
                                          (union-eq *jvm-frame-manipulation-primitives-symbols*        
                                                    (union-eq *jvm-object-manipluation-primitives-symbols*
                                                              (union-eq
                                                               *jvm-state-symbols*
      (union-eq *jvm-type-value-symbols*
            (union-eq *jvm-class-hierachy-symbols* 
                      (union-eq *jvm-obj-symbols*
                                (union-eq *jvm-thread-primitives-symbols*
                                          (union-eq *jvm-loader-primitives-symbols*
                                                    (union-eq *jvm-loader-constant-pool-primitivies-symbols*
                                                              (union-eq *jvm-loader-symbols*
                                                                        (union-eq *jvm-linker-symbols*
                                                                                  (union-eq *jvm-verifier-symbols*
         (union-eq *jvm-monitor-primitives-symbols*        
            (union-eq  *jvm-monitor-failure-as-fatalError-symbols*
                       (union-eq  *jvm-object-type-hierachy-symbols*
                                  (union-eq *jvm-semantic-primitives-2-symbols*
                                            (union-eq *jvm-exceptions-symbols*
                                                      (union-eq *jvm-monitor-failure-as-java-Exception*
                                                                (union-eq *jvm-bytecode-symbols*
                                                                          *jvm-internal-primitives*)))))))))))))))))))))))))))
