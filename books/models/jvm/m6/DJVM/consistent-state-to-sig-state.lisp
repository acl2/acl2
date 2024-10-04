(in-package "DJVM")
(include-book "../DJVM/consistent-state")
(include-book "../BCV/typechecker")
(include-book "../DJVM/djvm-class-table")
(include-book "../DJVM/djvm-heap")

(acl2::set-verify-guards-eagerness 0) 
;; not going to say anything about guard. We did not assert anything about
;; guard 

(defun fix-sig (sig)
  "fix-sig need to transform java.lang.String into (class java.lang.String)"
  (if (primitive-type? sig) 
      sig
    (if (isArrayType sig)
        (list 'ARRAY (fix-sig (component-type sig)))
      (list 'class sig))))




(acl2::set-ignore-ok t)

(defun djvm-translate-int-type (type)
  (COND ((EQUAL TYPE 'BOOLEAN) 'INT)
        ((EQUAL TYPE 'BYTE) 'INT)
        ((EQUAL TYPE 'SHORT) 'INT)
        ((EQUAL TYPE 'CHAR) 'INT)
        (T TYPE)))

(verify-guards djvm-translate-int-type)

(defun value-sig (v cl hp hp-init curMethodPtr)
 (declare (xargs :guard (and (consistent-class-hierachy cl)
                             (wff-heap-strong hp)
                             (wff-heap-init-map-strong hp-init)
                             (wff-tagged-value v)
                             (consistent-heap-with-heap-init-map hp hp-init)
                             (consistent-value-x v cl hp))))
   (if (REFp v hp)
      (if (NULLp v)
          'null
        ;; need to deal with different package issue later
        (let ((obj-init-tag (deref2-init v hp-init))
              (obj (deref2 v hp)))
          (if (not (consp obj-init-tag)) 
              ;; if not consp obj-init-tag means initialized. Fri Nov 21
              ;; 16:30:24 2003
              (fix-sig (obj-type obj))
            (if (equal (cdr obj-init-tag) curMethodPtr)
                ;; if the object is created in this method
                ;; then translate into an uninitialized(Offset)
                (cons 'uninitialized (car obj-init-tag))
              ;; else translate it into a 'uninitializedThis because one could
              ;; never pass a 'uninitialized object to a different method,
              ;; without being the this pointer in calling the constructor.
              ;; AASTORE and putfield etc guarantee, an uninitialized object
              ;; reference will not be stored somewhere. 
              'uninitializedThis))))
              ;; at any point of program execution, at the give frame.
              ;; multiple of uninitialized object created in this call, there
              ;; is at most one uninitialized object not created from this
              ;; frame.
              ;; 
              ;; the invariant involves that all the object reachable from the
              ;; references in this frame, no object is uninitialized besides
              ;; one object. 'uninitializedThis.
              ;; 
              ;; pretty hard!! We want to defensive maintain this property
              ;; we want BCV guarantee the check succeeds. 
     (djvm-translate-int-type (tag-of v))))

      
;; how to deal with the long and 
;; (defun opstack-sig (opstack cl hp hp-init curMethodPtr)
;;   (declare (xargs :guard (and (consistent-class-hierachy cl)
;;                               (wff-heap-strong hp)
;;                               (wff-heap-init-map-strong hp-init)
;;                               (consistent-heap-with-heap-init-map hp hp-init)
;;                               (consistent-opstack opstack cl hp))))
;;   (if (not (consp opstack))
;;       nil
;;     (cond ((canPopCategory1 opstack)
;;            (push (value-sig (topCategory1 opstack) cl hp hp-init curMethodPtr)
;;                  (opstack-sig (popCategory1 opstack) cl hp hp-init curMethodPtr)))
;;           ((canPopCategory2 opstack)
;;            (push (value-sig (topCategory2 opstack) cl hp hp-init curMethodPtr)
;;                  (push 'topx
;;                        (opstack-sig (popCategory2 opstack) cl hp hp-init curMethodPtr)))))))

(defun opstack-sig (opstack cl hp hp-init curMethodPtr)
  (declare (xargs :guard (and (consistent-class-hierachy cl)
                              (wff-heap-strong hp)
                              (wff-heap-init-map-strong hp-init)
                              (consistent-heap-with-heap-init-map hp hp-init)
                              (consistent-opstack opstack cl hp))))
  (if (not (consp opstack))
      nil
    (cond ((canPopCategory1 opstack)
           (push (value-sig (topCategory1 opstack) cl hp hp-init curMethodPtr)
                 (opstack-sig (popCategory1 opstack) cl hp hp-init curMethodPtr)))
          ((canPopCategory2 opstack)
           (push 'topx ;; fixed a bug. Mon May 16 19:32:52 2005;; changed
                 ;; 'topx into 'topx
                 (push (value-sig (topCategory2 opstack) cl hp hp-init curMethodPtr)
                       (opstack-sig (popCategory2 opstack) cl hp hp-init curMethodPtr)))))))

;;; notice Sun May 22 17:15:28 2005 that on opstack-sig: we have topx on the top
;;; the actual value on the BCV's sig stack, 
;;; on locals-sig we have the topx after the actual type !! 
;;; Sun May 22 17:16:35 2005

;;; Thu Dec 16 23:20:47 2004. 
;;; We fix this to match with the BCV
;;; BCV demands this because this is the order for the StackMap is given. by
;;; the preverifier!! 
;;; Thu Dec 16 23:22:14 2004

;;;; Mon Jan 31 15:44:03 2005. OK. Seem to be fixed already. 

;; Tue Mar 30 18:36:17 2004
;; problem. locals-sig assume all slot is initialized!!
;; which is not true!! some slot may have 'topx
;;
;; locals-sig is different rom opstack-sig

(defun locals-sig (locals cl hp hp-init curMethodPtr)
  (declare (xargs :guard (and (consistent-class-hierachy cl)
                              (wff-heap-strong hp)
                              (wff-heap-init-map-strong hp-init)            
                              (consistent-heap-with-heap-init-map hp hp-init)                  
                              (consistent-locals locals cl hp))))
  (if (not (consp locals))
      nil
    (cond ((Category1Loc locals)
           (cons (value-sig (category1value locals) cl hp hp-init curMethodPtr)
                 (locals-sig (shift1slot locals) cl hp hp-init curMethodPtr)))
          ((Category2Loc locals)
           (cons (value-sig (category2value locals) cl hp hp-init curMethodPtr)
                 (cons 'topx 
                       (locals-sig (shift2slot locals) cl hp hp-init
                                   curMethodPtr))))
          (t (cons 'topx (locals-sig (shift1slot locals) cl hp hp-init curMethodPtr))))))


;; To get a frame with proper flags, we also need the flag about it. 
;;
;; This is becoming more interesting. 

;; The flag together with return's check make sure it called the initializer at
;; least once.


;; (defun gen-flags (values)
;;   (if (not (consp values)) nil
;;     (if (equal (car values) 'uninitializedThis)
;;         (list 'flagThisUninit)
;;       (gen-flags (cdr values)))))

;; (defun gen-frame-flags (local-sig stack-sig)
;;   (or (gen-flags local-sig)
;;       (gen-flags stack-sig)))


;;;
;;; It appears that I have to add a new field into the make-frame We need to
;;; modify the DJVM's make-frame to keep track of the current this pointer in a
;;; method.
;;; 

;;; Sat Jul 30 23:37:11 2005. !!

;;(i-am-here) ;; Sun Jul 31 01:22:50 2005

(defun gen-frame-flags (frame hp-init)
  (declare (xargs :guard (wff-call-frame frame)))
  (if (not (acl2::g 'this (jvm::frame-aux frame))) 
      nil
    (if (not (bound? (acl2::g 'this (jvm::frame-aux frame)) hp-init)) nil
      (if (not (binding (acl2::g 'this (jvm::frame-aux frame)) hp-init)) 
          '(flagThisUninit)
        nil))))



(defun make-sig-frame (Locals Stack Flags) 
  (list 'frame (cons 'locals locals) (cons 'stack stack) Flags))


(defun frame-sig (frame cl hp hp-init)
  (declare (xargs :guard (and (consistent-class-hierachy cl)
                              (wff-heap-strong hp)
                              (wff-heap-init-map-strong hp-init)            
                              (consistent-heap-with-heap-init-map hp hp-init)                  
                              (consistent-frame frame cl hp))))
  (let* ((locals-sig (locals-sig (locals frame)  cl hp hp-init (method-ptr frame)))
         (stack-sig  (opstack-sig (operand-stack frame) cl hp hp-init (method-ptr frame)))
         (flags (gen-frame-flags frame hp-init)))
    (make-sig-frame  locals-sig stack-sig flags)))


(defun makeEnvironment (Class Method ReturnType MergedCode MaxStack Handlers CL)  
  (list Class Method ReturnType MergedCode MaxStack Handlers CL))


(include-book "../BCV/bcv-functions-basic") ;; Wed May  4 22:25:50 2005
;; The static class table format is differnet between BCV and DJVM

(defun env-sig (s)
  (declare (xargs :guard (consistent-state s)))
  (let* ((scl (external-class-table s))
         (cid (current-thread s))
         (curThread (thread-by-id cid (thread-table s)))
         (callstack (thread-call-stack curThread))
         (curFrame  (top callstack))
         (curmethodptr (method-ptr curFrame))
         (classname (method-ptr-classname curmethodptr))
         (curClass (class-by-name classname (instance-class-table s)))
         (returnType (method-ptr-returntype curmethodptr))
         (curMethod (deref-method curmethodptr (instance-class-table s)))
         (parsedCode (method-code curMethod))
         (stackMaps  (method-stackmap curMethod))
         (mergedCode (bcv::mergeStackMapAndCode stackMaps parsedCode))
         (maxStack (method-maxStack curMethod))
         (handlers (method-handlers curMethod)))
    ;; those pieces all need some fixs to transform into BCV's format. 
    (makeEnvironment curClass curMethod returnType mergedCode maxStack handlers
                     (bcv::scl-jvm2bcv scl))));; 11/14/03 pass in scl!!


;; we probably don't need to define and verify guard for those conversion
;; functions. 




