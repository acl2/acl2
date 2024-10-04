(in-package "JVM")

(include-book "jvm-env-test-data")
;;; importing *test.env*
;;;

;-- ENV ------
; temp -- consider no IO
;-------------

;; static class representation. 

(acl2::set-verify-guards-eagerness 2)

(defun make-env (scl) ;; temp version
  "Create an object that represents the 'Environment'"
   (list 'env 
        (cons 'external-class-table
              scl)))

;; Mon Jan 12 23:59:43 2004 from consistent-class.lisp

(defun wff-env (env)
  "Shallow wff of ENV"
  (and (true-listp env)
       (equal (len env) 2)
       (consp (nth 1 env))))

(local 
 (defthm wff-env-test 
   (wff-env *test.env*)))


(defun env-class-table (env) 
  "Extract the external class table from the environment"
  (declare (xargs :guard (wff-env env)))
  (cdr (nth 1 env)))


(defun make-static-class-table (static-class-descs)
    static-class-descs)


(defun make-static-class-desc (classname super constantpool
                                         fields methods
                                         interfaces
                                         accessflags)
  (list 'class classname                   ;; just names 
        super                              ;; name of the super
        (cons 'constant_pool constantpool)  ;; runtime representation
        (cons 'fields fields)               ;; fields 
        (cons 'methods methods)             ;; list of methods 
        (cons 'interfaces interfaces)       ;; interfaces 
        (cons 'accessflags accessflags)))   ;; access flags

;;(i-am-here) ;; Tue Jul 12 21:30:24 2005

(defun wff-class-rep-static (class-rep)
  "One level Wff assertions on static class representation"
  (declare (xargs :verify-guards t))
  (and (true-listp class-rep)
       (equal (len class-rep) 8)
       (equal (car class-rep) 'class) 
       (stringp (nth 1 class-rep))
       (stringp (nth 2 class-rep)) ;; Wed Jul 13 12:21:51 2005
       (consp (nth 3 class-rep))
       (consp (nth 4 class-rep))
       (consp (nth 5 class-rep))
       (consp (nth 6 class-rep))
       (consp (nth 7 class-rep))
       (true-listp (cdr (nth 3 class-rep)))
       (true-listp (cdr (nth 4 class-rep)))
       (true-listp (cdr (nth 5 class-rep)))
       (true-listp (cdr (nth 6 class-rep)))
       (true-listp (cdr (nth 7 class-rep)))
       (true-listp (cdr (nth 7 class-rep)))
       (EQUAL (LIST 'CLASS
                    (NTH 1 class-rep)
                    (NTH 2 class-rep)
                    (CONS 'CONSTANT_POOL
                          (CDR (NTH 3 class-rep)))
                    (CONS 'FIELDS (CDR (NTH 4 class-rep)))
                    (CONS 'METHODS (CDR (NTH 5 class-rep)))
                    (CONS 'INTERFACES
                          (CDR (NTH 6 class-rep)))
                    (CONS 'ACCESSFLAGS
                          (CDR (NTH 7 class-rep))))
              class-rep)))
 
;;;
;;; Tue Jul 12 21:27:08 2005. We need to strengthen it. 
;;; so that we can prove the 

;; (defthm equal-make-class-def-scl-decl-bcv2jvm
;;   (implies (jvm::wff-class-rep-static raw-class)
;;            (equal (scl-decl-bcv2jvm 
;;                    (make-class-def raw-class))
;;                   raw-class))
;;   :hints (("Goal" :in-theory (enable jvm::wff-class-rep-static))))

;; scl-decl-bcv2jvm is not defined until 


;;          (EQUAL (LIST (CAR class-rep)
;;                       (NTH 1 class-rep)
;;                       (CONS 'CONSTANT_POOL
;;                             (CDR (NTH 2 class-rep)))
;;                       (CONS 'FIELDS (CDR (NTH 3 class-rep)))
;;                       (CONS 'METHODS (CDR (NTH 4 class-rep)))
;;                       (CONS 'INTERFACES
;;                             (CDR (NTH 5 class-rep)))
;;                       (CONS 'ACCESSFLAGS
;;                             (CDR (NTH 6 class-rep)))
;;                       (CONS 'ATTRIBUTES
;;                             (CDR (NTH 7 class-rep))))
;;                 class-rep)).


(local 
 (defun all-wff-class-rep-static (class-reps)
   (if (not (consp class-reps)) t
     (and (wff-class-rep-static (car class-reps))
          (all-wff-class-rep-static (cdr class-reps))))))
       

;; (i-am-here) ;; 

(local 
  (defthm wff-class-rep-static-test
    (all-wff-class-rep-static  (env-class-table *test.env*))))

;; ;;; this failed!! 
;; ;;; to be investigated!! 


(defun classname-s (sclass-rep)
  (declare (xargs :guard (wff-class-rep-static sclass-rep)))
  (nth 1 sclass-rep))

(defun super-s (sclass-rep)
  (declare (xargs :guard (wff-class-rep-static sclass-rep)))
  (nth 2 sclass-rep))

(defun constantpool-s (sclass-rep)
  (declare (xargs :guard (wff-class-rep-static sclass-rep)))
  (cdr (nth 3 sclass-rep)))

(defun fields-s (sclass-rep)
  (declare (xargs :guard (wff-class-rep-static sclass-rep)))
  (cdr (nth 4 sclass-rep)))

(defun methods-s (sclass-rep)
  (declare (xargs :guard (wff-class-rep-static sclass-rep)))
  (cdr (nth 5 sclass-rep)))

(defun interfaces-s (sclass-rep)
  (declare (xargs :guard (wff-class-rep-static sclass-rep)))
  (cdr (nth 6 sclass-rep)))

(defun accessflags-s (sclass-rep)
  (declare (xargs :guard (wff-class-rep-static sclass-rep)))
  (cdr (nth 7 sclass-rep)))


;----------------------------------------------------------------------


;----------------------------------------------------------------------

(defun wff-string-cp-entry-s (cp-entry)
  "Static cp-entry representing a String"
  (declare (xargs :verify-guards t))
  (and (consp cp-entry)
       (equal (len cp-entry) 2)
       (equal (car cp-entry) 'STRING)
       (stringp (cadr cp-entry))))


(defun wff-int-cp-entry-s (cp-entry)
  "Static cp-entry representing a INT"
  (declare (xargs :verify-guards t))
  (and (consp cp-entry)
       (equal (len cp-entry) 2)
       (equal (car cp-entry) 'INT)
       (int32p (cadr cp-entry))))



(defun wff-long-cp-entry-s (cp-entry)
  "Static cp-entry representing a LONG"
  (declare (xargs :verify-guards t))
  (and (consp cp-entry)
       (equal (len cp-entry) 2)
       (equal (car cp-entry) 'LONG)
       (int64p (cadr cp-entry))))


(defun wff-constant-pool-entry-s (cp-entry)
  "wff static cp-entry"
  (declare (xargs :verify-guards t))
  (and (consp cp-entry)
       (equal (len cp-entry) 2)
       (or (wff-string-cp-entry-s cp-entry)
           (wff-int-cp-entry-s cp-entry)
           (wff-long-cp-entry-s cp-entry)
           ;;(wff-float-cp-entry cp-entry)
           ;;(wff-double-cp-entry cp-entry)
           ;; temp implementation
           )))



(defun wff-constant-pool-s (cps)
  "Constant pool being wff"
  (declare (xargs :verify-guards t))
  (if (not (consp cps)) t
    (and (wff-constant-pool-entry-s (car cps))
         (wff-constant-pool-s (cdr cps)))))

(local 
 (defun all-constant-pools-s (class-reps)
   (declare (xargs :guard (all-wff-class-rep-static class-reps)))
   (if (not (consp class-reps)) nil
     (cons (constantpool-s (car class-reps))
           (all-constant-pools-s (cdr class-reps))))))


(local 
 (defun all-wff-constant-pool-s (constantpools)
   (if (not (consp constantpools)) t
     (and (wff-constant-pool-s (car constantpools))
          (all-wff-constant-pool-s (cdr constantpools))))))

(local 
 (defthm all-wff-constant-pool-s-test 
   (all-wff-constant-pool-s (all-constant-pools-s (env-class-table *test.env*)))))

;; cpentry : type + value 
(defun cpentry-type-s (cpentry)
  "Return the type of the cpentry"
  (declare (xargs :guard (wff-constant-pool-entry-s cpentry)))
  (car cpentry))


(defun cpentry-value-s (cpentry)
  "Return the value of the cpentry"
  (declare (xargs :guard (wff-constant-pool-entry-s cpentry)))
  (cadr cpentry))

(defun make-string-cp-entry-s (string-value)
  (list 'STRING string-value))

(defun string-value-cp-entry-s (cpentry)
  (declare (xargs :guard (wff-constant-pool-entry-s cpentry)))
  (cadr cpentry))

(defun make-int-cp-entry-s (int-value)
  (list 'INT int-value))

(defun int-value-cpentry-s (cpentry)
  (declare (xargs :guard (wff-constant-pool-entry-s cpentry)))
  (cadr cpentry))


(defun make-long-cp-entry-s (long-value)
  (list 'LONG long-value))

(defun long-value-cpentry-s (cpentry)
  (declare (xargs :guard (wff-constant-pool-entry-s cpentry)))
  (cadr cpentry))


(defun make-float-cp-entry-s (float-value)
  (list 'FLOAT float-value))

(defun float-value-cpentry-s (cpentry)
  (declare (xargs :guard (wff-constant-pool-entry-s cpentry)))
  (cadr cpentry))

(defun make-double-cp-entry-s (double-value)
  (list 'double double-value))

(defun double-value-cpentry-s (cpentry)
  (declare (xargs :guard (wff-constant-pool-entry-s cpentry)))
  (cadr cpentry))

;----------------------------------------------------------------------

(defun make-field-s (fieldname fieldtype accessflags cpindex)
  (list 'field fieldname fieldtype 
        (cons 'accessflags accessflags)
        cpindex))

(defun wff-field-s (field)
  "Field being wff. shallow"
  (and (equal (len field) 5)
       (true-listp field)
       (consp (nth 3 field))))


(local 
 (defun all-fields-s (class-reps)
   (declare (xargs :guard (all-wff-class-rep-static class-reps)))
   (if (not (consp class-reps)) nil
     (app (fields-s (car class-reps))
          (all-fields-s (cdr class-reps))))))


;; (local 
;;  (defun all-wff-fields-s (class-reps)
;;    (declare (xargs :guard (all-wff-class-rep-static class-reps)))
;;    (if (not (consp class-reps)) t
;;      (and (wff-fields-s (fields-s (car class-reps)))
;;           (all-wff-fields-s (cdr class-reps))))))


(local 
 (defun all-wff-fields-s (fields)
   (if (not (consp fields)) t
     (and (wff-field-s (car fields))
          (all-wff-fields-s (cdr fields))))))


(local 
 (defthm all-wff-fields-s-test 
   (all-wff-fields-s (all-fields-s (env-class-table *test.env*)))))

(defun field-fieldname-s (field)  
  (declare (xargs :guard (wff-field-s field)))
  (nth 1 field))

(defun field-fieldtype-s (field) 
  (declare (xargs :guard (wff-field-s field)))
  (nth 2 field))

(defun field-fieldaccessflags-s (field) 
  (declare (xargs :guard (wff-field-s field)))
  (cdr (nth 3 field)))

(defun field-cpindex-s (field)   
  (declare (xargs :guard (wff-field-s field)))
  (nth 4 field))

(defun static-field?-s (field)
  (declare (xargs :guard (wff-field-s field)))
  (mem '*static* (field-fieldaccessflags-s field)))

;; in the jvm-class-table
; methods 

(defun make-method-s (methodname args returntype accessflags code)
  (list 'method 
        methodname 
        (list 'parameters args)
        (list 'returntype returntype)
        (list 'accessflags accessflags)
        code))


(defun wff-method-decl-s (method-decl)
  (and (true-listp method-decl)
       (equal (len method-decl) 6)
       (consp (nth 2 method-decl))
       (consp (nth 3 method-decl))
       (consp (nth 4 method-decl))
       ;; (consp (cdr (nth 3 method-decl))) ;; Thu Jan  5 17:55:19 2006
       ;; Thu Jan  5 17:54:40 2006. updated jvm2acl2. 
       (true-listp (cdr (nth 2 method-decl)))
       (true-listp (cdr (nth 4 method-decl)))
       (true-listp (nth 5 method-decl))))


(defun method-methodname-s  (method) 
  (declare (xargs :guard (wff-method-decl-s method)))
  (nth 1 method))

(defun method-args-s        (method)  
  (declare (xargs :guard (wff-method-decl-s method)))
  (cdr  (nth 2 method)))

(defun method-returntype-s  (method)   
  (declare (xargs :guard (wff-method-decl-s method)))
  (cdr (nth 3 method)))


(defun method-accessflags-s (method)  
  (declare (xargs :guard (wff-method-decl-s method)))
  (cdr (nth 4 method)))

(defun method-code-s        (method) 
  (declare (xargs :guard (wff-method-decl-s method)))
  (nth 5 method))



(defun wff-method-decls-s (method-decls)
  (if (not (consp method-decls)) t
    (and (wff-method-decl-s (car method-decls))
         (wff-method-decls-s (cdr method-decls)))))


(local
 (defun all-method-decls-s (class-reps)
   (declare (xargs :guard (all-wff-class-rep-static class-reps)))
   (if (not (consp class-reps)) nil
     (app (methods-s (car class-reps))
          (all-method-decls-s (cdr class-reps))))))
      
(local 
 (defun all-wff-method-decls-s (methods)
   (if (not (consp methods)) t
     (and (wff-method-decl-s (car methods))
          (all-wff-method-decls-s (cdr methods))))))


(local 
 (defthm all-wff-method-decls-s-test 
   (all-wff-method-decls-s (all-method-decls-s (env-class-table *test.env*)))))

;; the following are the same with their dynamic counterpart

(defun make-code-s (max-stack max-local code-length instrs exceptions stackmaps)
  (list 'code 
        (list 'max_stack max-stack)  ;; different from dynamic version.
        (list 'max_local max-local)  ;; the format generated by jvm2acl2-m6
        (list 'code_length code-length)
        (cons 'parsedcode instrs)
        (cons 'Exceptions exceptions)
        (cons 'StackMap   stackmaps)))


(defun wff-code-s (code)
  (and (equal (len code) 7)
       (true-listp code)
       (consp (nth 1 code))
       (integerp (cdr (nth 1 code)))
       (consp (nth 2 code))
       (integerp (cdr (nth 2 code)))
       (consp (nth 3 code))
       (integerp (cdr (nth 3 code)))
       (consp (nth 4 code))
       (consp (nth 5 code))
       (consp (nth 6 code))))


(defun code-max-stack-s (code)
  (declare (xargs :guard (wff-code-s code)))
  (cdr (nth 1 code)))

(defun code-max-local-s (code)
  (declare (xargs :guard (wff-code-s code)))
  (cdr (nth 2 code)))

(defun code-code-length-s (code)
  (declare (xargs :guard (wff-code-s code)))
  (cdr (nth 3 code)))

(defun code-instrs-s (code)
  (declare (xargs :guard (wff-code-s code)))
  (cdr (nth 4 code)))

(defun code-handlers-s (code)
  (declare (xargs :guard (wff-code-s code)))
  (cdr (nth 5 code)))

(defun code-stackmaps-s (code)
  (declare (xargs :guard (wff-code-s code)))
  (cdr (nth 6 code)))


(local 
 (defun all-code-s (methods)
   (declare (xargs :guard (wff-method-decls-s methods)))
   (if (not (consp methods)) t
     (if (and (not (mem '*native*   (method-accessflags-s (car methods))))
              (not (mem '*abstract* (method-accessflags-s (car methods)))))
         (cons (method-code-s (car methods))
               (all-code-s (cdr methods)))
       (all-code-s (cdr methods))))))

;; it is possible that some 

(local 
 (defun all-wff-code-s (codes)
   (if (not (consp codes)) t
     (and (wff-code-s (car codes))
          (all-wff-code-s (cdr codes))))))
       
(local 
 (defthm all-wff-code-s-test 
   (all-wff-code-s (all-code-s (all-method-decls-s (env-class-table *test.env*))))))

;---
;---

(defun wff-static-class-table (scl)
  (declare (xargs :verify-guards t))
  (if (not (consp scl)) t
    (and (wff-class-rep-static (car scl))
         (wff-static-class-table (cdr scl)))))

(defun class-by-name-s (name scl)
  (declare (xargs :guard (wff-static-class-table scl)))
  (if (not (consp scl))
      (mv nil nil)
    (if (equal (classname-s (car scl))
               name)
        (mv t (car scl))
      (class-by-name-s name (cdr scl)))))


;-------
(defun make-class-def (raw-class) 
  (declare (xargs :guard (wff-class-rep-static raw-class)))
  (make-static-class-desc 
     (classname-s raw-class)
     (super-s     raw-class)
     (constantpool-s raw-class)
     (fields-s       raw-class)
     (methods-s      raw-class)
     (interfaces-s   raw-class)
     (accessflags-s  raw-class)))
       
(defmacro make-static-class-decls (&rest cl)
  (cons 'list cl))


;; (defconst *jvm-env-symbols* 
;;   '(make-env
;; env-class-table
;; make-static-class-table
;; make-static-class-desc
;; classname-s
;; super-s
;; constantpool-s
;; fields-s
;; methods-s
;; interfaces-s
;; accessflags-s
;; cpentry-type-s
;; make-string-cp-entry-s
;; string-value-cp-entry-s
;; make-int-cp-entry-s
;; int-value-cpentry-s
;; make-long-cp-entry-s
;; long-value-cpentry-s
;; make-float-cp-entry-s
;; float-value-cpentry-s
;; make-double-cp-entry-s
;; make-field-s
;; field-fieldname-s
;; field-fieldtype-s
;; field-fieldaccessflags-s
;; field-cpindex-s
;; static-field?-s
;; make-method-s
;; method-methodname-s
;; method-args-s
;; method-returntype-s
;; method-accessflags-s
;; method-code-s
;; make-code-s
;; code-max-stack-s
;; code-max-local-s
;; code-code-length-s
;; code-instrs-s
;; code-handlers-s
;; code-stackmaps-s
;; class-by-name-s
;; make-class-def))
