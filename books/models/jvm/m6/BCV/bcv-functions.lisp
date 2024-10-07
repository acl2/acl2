(in-package "BCV")
(include-book "../BCV/typechecker")
(include-book "../DJVM/consistent-state")

(defun good-java-type (typ icl)
  (declare (xargs :hints (("Goal" :in-theory (enable isArrayType)))))
  (or (JVM::PRIMITIVE-TYPE? typ)
      (and (isclasstype typ)
           (JVM::CLASS-EXISTS? (name-of typ) icl))
      (and (isArrayType typ)
           (not (equal (component-type typ) 'NULL))
           (good-java-type (component-type typ) icl))))


(defun wff-icl (icl)
  (if (not (consp icl)) t
    (and (stringp (jvm::classname (car icl)))
         (wff-icl (cdr icl)))))


(defun all-subclass-of-java-lang-Object (nl icl)
  (if (endp nl)
      t
    (and (mem "java.lang.Object"
              (djvm::collect-superclass-list (car nl) icl))
         (all-subclass-of-java-lang-Object (cdr nl) icl))))
      

(defun good-icl (icl)
  (and (wff-icl icl)
       (djvm::class-exists? "java.lang.Object" icl)
       (not (djvm::class-exists? 
             (djvm::super (class-by-name "java.lang.Object" icl))
             icl))
       ;; add an extra assertion that all classes has a super class of
       ;; "java.lang.Object"!! Thu Jul 14 12:29:12 2005
       ;; which, we will try to prove it later from consistent-state!! 
       (all-subclass-of-java-lang-Object 
        (djvm::all-class-names icl) icl)
       (djvm::consistent-class-hierachy icl)))


(defun good-bcv-type (typ icl)
  (or (equal typ 'ONEWORD)
      (equal typ 'TWOWORD)
      (equal typ 'topx)
      (equal typ 'REFERENCE)
      (equal typ 'UNINITIALIZED)
      (equal typ 'UNINITIALIZEDTHIS)
      (equal typ 'NULL)
      (good-java-type typ icl)))



(defun consistent-sig-type (type icl)
  (and (not (equal type 'TWOWORD))
       (not (equal type 'ONEWORD))
       (not (equal type 'VOID))
       (not (equal type 'SHORT)) ;; these should not be seen 
       (not (equal type 'BYTE))  ;; assuming translate-type!! 
       (not (equal type 'CHAR))  ;;
       (not (equal type 'BOOLEAN))
       ;; (not (equal type 'uninitialized))
       ;; (not (equal type 'reference))
       (good-bcv-type type icl)))


;; (defun consistent-sig-stack (stack icl)
;;   (if (endp stack) t
;;     (if (endp (cdr stack)) 
;;         (and (equal (sizeof (car stack)) 1)
;;              (consistent-sig-type (car stack) icl)
;;              (consistent-sig-stack (cdr stack) icl))
;;       (if (equal (sizeof (cadr stack)) 2)
;;           (and (consistent-sig-type (cadr stack) icl)
;;                (equal (car stack) 'topx)
;;                (consistent-sig-stack (cddr stack) icl))
;;         nil)))) ;; this nil is not reachable!! Thu Jul 28 00:52:23 2005


(defun consistent-sig-stack (stack icl)
  (if (endp stack) t
    (if (endp (cdr stack)) 
        (and (equal (sizeof (car stack)) 1)
             (consistent-sig-type (car stack) icl)
             (consistent-sig-stack (cdr stack) icl))
      (if (equal (sizeof (cadr stack)) 2)
          (and (consistent-sig-type (cadr stack) icl)
               (equal (car stack) 'topx)
               (consistent-sig-stack (cddr stack) icl))
        (and (equal (sizeof (car stack)) 1)
             (consistent-sig-type (car stack) icl)
             (consistent-sig-stack (cdr stack) icl))))))


;;;; We shall prove that opstack-sig from a consistent-opstack will produce 
;;;; a consistent-sig-stack
;;;;
;;;; Sun May 22 17:19:06 2005
;;;;
;;;; Notice that our consistent-sig-stack allow a sequence of topx 
;;;; on the opstack!! which will not happen. 
;;;; 
;;;; Sun May 22 17:21:11 2005

(defun consistent-sig-locals (locals icl)
  (if (endp locals) t
    (if (equal (sizeof (car locals)) 1)
        (and (consistent-sig-type (car locals) icl)
             (consistent-sig-locals (cdr locals) icl))
      (if (equal (sizeof (car locals)) 2)
          (if (endp (cdr locals)) nil
            (and (consistent-sig-type (car locals) icl)
                 (equal (cadr locals) 'topx)
                 (consistent-sig-locals (cddr locals) icl)))
        nil))))




(defun sig-frame-more-general (gframe sframe env)
  (FrameIsAssignable sframe gframe env))

(include-book "bcv-functions-basic")

;; (defun make-static-class-decl (cn super cp fs ms is as ats)
;;   (LIST 'CLASS cn super
;;         (CONS 'CONSTANT_POOL CP)
;;         (CONS 'FIELDS fs)
;;         (CONS 'METHODS ms)
;;         (CONS 'INTERFACES is)
;;         (CONS 'ACCESSFLAGS as)
;;         (CONS 'ATTRIBUTES ats)))


;; (defun scl-decl-bcv2jvm (scl-decl)
;;   (make-static-class-decl 
;;     (classClassName scl-decl)
;;     (classSuperClassName scl-decl)
;;     (classConstantPool scl-decl)
;;     (classFields scl-decl)
;;     (classMethods scl-decl)
;;     (classInterfaces scl-decl)
;;     (classAccessFlags scl-decl)
;;     (classAttributes scl-decl)))




;; (defun scl-bcv2jvm (scl)
;;   (if (endp scl) nil
;;     (cons (scl-decl-bcv2jvm (car scl))
;;           (scl-bcv2jvm (cdr scl)))))

;; (defun scl-jvm2bcv (raw-scl)
;;   (if (endp raw-scl) nil
;;     (cons (make-class-def (car raw-scl))
;;           (scl-jvm2bcv (cdr raw-scl)))))


;; (defun good-scl (scl)
;;   (equal (scl-jvm2bcv (scl-bcv2jvm scl)) scl))


(defun icl-scl-compatible (icl scl)
  (and (good-scl scl)
       (JVM::WFF-STATIC-CLASS-TABLE-STRONG (scl-bcv2jvm scl))
       (djvm::class-table-is-loaded-from icl (scl-bcv2jvm scl))))




(defun normal-frame (frame-pair)
  (mv-nth 0 frame-pair))

;----------------------------------------------------------------------

(acl2::set-verify-guards-eagerness 0)

;;;
;;; useful in proof of bcv-check general implies bcv-check specific
;;; 
(defun sig-pop-opstack (type sig-frame)
  (make-sig-frame
    (frameLocals sig-frame)
    (popMatchingType type (frameStack sig-frame))
    (frameFlags sig-frame)))



(defun sig-push-opstack (v sig-frame)
  (make-sig-frame
    (frameLocals sig-frame)
    (pushOperandStack v (frameStack sig-frame))
    (frameFlags sig-frame)))
;;;
;;; need these to express some generic rules. 
;;; base-bcv-fact-isMatchingType-consistent-sig-type!! 
;;;
