(in-package "M6")
(include-book "../M6/m6-interpreter")

(defun load-parameters1 (params s0)
  (if (endp params) 
      (mv nil s0)
    (mv-let (str-ref s1)
            (ACL2-str-to-JavaString-ref (car params) s0)
            (mv-let (str-refs sn)
                    (load-parameters1 (cdr params) s1)
                    (mv (cons str-ref str-refs)
                        sn)))))

(defun load-command-line-parameters (params s0)
  (mv-let (string-refs s1)
          (load-parameters1 params s0)
          (let ((len (len string-refs)))
            (mv-let  (array-obj s2)
                     (make-array 
                      (make-array-type "java.lang.String")
                      len string-refs  s1)
                     (let* ((heap (heap s2))
                            (new-addr (alloc heap))
                            (new-heap (bind new-addr array-obj heap)))
                       (mv new-addr 
                           (update-trace new-addr (state-set-heap new-heap s2))))))))


;;; until now, there is not invocation of any <init> methods
;;; we need to fake the initialization for the first few objects, 
;;; such as the initial Thread objects.

;;; we also need to the fake/make the invocation of the <clinit> 
;;; on java.lang.Thread, java.lang.String, java.lang.Class, java.lang.Object
;;;
;;; Because those classes doesn't have static fields, trivial, easy.

;;; as for faking the result of the call to init of java.lang.Thread, we just
;;; change fake the object's field target = null and priority=5.

;;; a lot need to be done.  depends on how we going to detect the termination
;;; of a thread.  we can introduce a special instruction or a special internal
;;; implementation of return.

;; fake the effects/behaviors of calling the <init> method with interpreter.  
(defun fakeThreadObjectDefaultInit (thread-obj-ref s)
  (m6-putfield "java.lang.Thread" "target" -1 thread-obj-ref 
               (m6-putfield "java.lang.Thread" "priority" 5 thread-obj-ref s)))
;; return a m6 state.
  

;; add one special instruction to RunCustomCode
;; change max_stack 

(defconst *runCustomCode-maxStack* 4)

(defun new-runCustomCode () 
  (make-method "java.lang.Class"
               "runCustomCode"
               nil
               'void
               '(*CLASS* *PRIVATE* *STATIC*)
               (make-code *runCustomCode-maxStack* 
                          0 2 
                          '((0 (customcode))
                            (1 (return))
                            (endofcode 2))
                          nil
                          nil)))

(defun patch-JavaLangClass-RunCustomCode3 (methods)
  (if (endp methods) 
      nil
    (if (equal (method-methodname (car methods)) "runCustomCode")
        (cons (new-runCustomCode) 
              (cdr methods))
      (cons (car methods) (patch-JavaLangClass-RunCustomCode3 (cdr methods))))))


(defun patch-JavaLangClass-RunCustomCode2 (class-rep)
  (make-runtime-class-rep 
   (classname class-rep)
   (super     class-rep)
   (constantpool class-rep)
   (fields       class-rep)
   (patch-JavaLangClass-RunCustomCode3 
        (methods class-rep))
   (interfaces    class-rep)
   (static-fields class-rep)
   (class-status  class-rep)
   (class-accessflags class-rep)
   (init-thread-id    class-rep)
   (class-ref         class-rep)))

(defun patch-JavaLangClass-RunCustomCode1 (class-reps)
  (if (endp class-reps)
      nil
    (if (equal (classname (car class-reps)) "java.lang.Class")
        (cons (patch-JavaLangClass-RunCustomCode2 (car class-reps))
              (cdr class-reps))
      (cons (car class-reps) (patch-JavaLangClass-RunCustomCode1 (cdr class-reps))))))


(defun patch-JavaLangClass-RunCustomCode (s)
  (state-set-class-table 
   (make-class-table (patch-JavaLangClass-RunCustomCode1
                      (instance-class-table s))
                     (array-class-table s))
   s))

;; assume system classes are loaded already. 


(defun setup-initial-state1 (classname parameters sx)
  (let* ((s (state-set-current-thread -1 sx))
         (s0 (getArrayClass "java.lang.String" s)))
    (mv-let (string-array-ref s1)
            (load-command-line-parameters parameters s0)
            (let* ((init-method-ptr (RunCustomCode-Method-ptr)))
                (mv-let (thread-obj-ref s2)
                      (new-instance "java.lang.Thread" s1)
                      (let ((s3 (fakeThreadObjectDefaultInit thread-obj-ref s2)))
                        (mv-let (thread-id s4)
                                (buildThread thread-obj-ref s3)
                                (let* ((s5 (set-thread-state-by-id thread-id 'thread_active s4))
                                       (s6 (state-set-current-thread thread-id s5))
                                       (s7 (pushFrame init-method-ptr nil s6))
                                       (s8 (pushStack (make-callback-func-ptr
                                                       '*initInitialThreadBehavior*) s7))
                                       (s9 (pushStack classname s8))
                                       (s10 (pushStack string-array-ref s9)))
                                  (initializeClass classname s10)))))))))



;; load a few system classes patch the java.lang.Class so that RunCustomCode
;; has a special instruction "RunCustomCode" so that Interpreter know when to
;; do call backs. 
(defun setup-initial-state (classname parameters s0)
  (let* ((s1 (load-JavaSystemClasses s0))
         (s2 (patch-JavaLangClass-RunCustomCode s1)))
    (setup-initial-state1 classname parameters s2)))












