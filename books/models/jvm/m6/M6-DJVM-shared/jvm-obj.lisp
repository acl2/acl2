(in-package "JVM")
(acl2::set-verify-guards-eagerness 2)
(include-book "../M6-DJVM-shared/jvm-type-value")

;; 
;; Internal representation of the object 
;;
;; (object  (commoninfo <hashcode> <monitor> <of-class>)
;;          (type-specific-info ) 
;;          <java-visible portion>)
;;
;; specific-type :: INSTANCE_CLASS ARRAY_CLASS STRING ARRAY GENERIC_OBJECT
;; 
;; Java-visible portion just like what it has been in M5
;; except some tags is removed from data values.       
;;
;;


(defun make-object (commoninfo specific-info java-visible-part)
  (list 'object commoninfo specific-info java-visible-part))

(defun wff-obj (obj)
  (and (true-listp obj)
       (equal (length obj) 4)))

(defun common-info   (object)  
  (declare (xargs :guard (wff-obj object)))
  (nth 1 object))

(defun specific-info (object)  
  (declare (xargs :guard (wff-obj object)))
  (nth 2 object))    ;; the format depends on types

(defun java-visible-portion (object)
  (declare (xargs :guard (wff-obj object)))
  (nth 3 object))


(defun obj-set-common-info (cminfo obj) 
  (declare (xargs :guard (wff-obj obj)))
  (make-object cminfo
               (specific-info obj)
               (java-visible-portion obj)))


(defun obj-set-specific-info (spinfo obj) 
  (declare (xargs :guard (wff-obj obj)))
  (make-object (common-info   obj)
               spinfo
               (java-visible-portion obj)))

(defun obj-set-java-visible-portion (jvp obj) 
  (declare (xargs :guard (wff-obj obj)))
  (make-object (common-info   obj)
               (specific-info obj)
               jvp))

(defun make-common-info (hashcode monitor class-ptr) 
  (list 'common-info hashcode monitor class-ptr)) 

(defun wff-common-info (cminfo)
  (and (true-listp cminfo)
       (equal (length cminfo) 4)))

(defun hashcode  (cminfo)  
  (declare (xargs :guard (wff-common-info cminfo)))
  (nth 1 cminfo)) ;; a number. 

(defun monitor   (cminfo)
  (declare (xargs :guard (wff-common-info cminfo)))
  (nth 2 cminfo))

(defun class-ptr (cminfo)  
  (declare (xargs :guard (wff-common-info cminfo)))
  (nth 3 cminfo))

(defun obj-hashcode  (object) 
  (declare (xargs :guard (and (wff-obj object)
                              (wff-common-info (common-info object)))))
  (hashcode  (common-info object))) ;; a number 

(defun obj-monitor   (object) 
  (declare (xargs :guard (and (wff-obj object)
                              (wff-common-info (common-info object)))))
  (monitor   (common-info object))) ;; a composite structure

(defun obj-class-ptr (object)  
  (declare (xargs :guard (and (wff-obj object)
                              (wff-common-info (common-info object)))))
  (class-ptr (common-info object))) ;; a number 

(defun obj-type (obj)  ;; object's runtime type.
  (declare (xargs :guard (and (wff-obj obj)
                              (wff-common-info (common-info obj)))))
  (obj-class-ptr obj))

;;
;; 08/27/03: Do we want to assert that hashcode is a number? (it could show up
;; on the operand stack) We need some properties about native
;; methods. asserting native method preserve the type and consistent-state!
;;

;;
;; In the common info section of the Object representation: 
;;
;;     three fields -- hashcode, monitor, and class-ptr.
;;
;;     current class-ptr is a symbolic reference in our M6. We assume all the
;;     symbolic reference recorded here are already loaded.  
;;  
;;     In real KVM this ptr is a pointer to the the obj of type java.lang.Class
;;     that represent the type of this Object
;;


(defun common-info-set-hashcode (h cminfo)
  (declare (xargs :guard (wff-common-info cminfo)))
  (make-common-info h (monitor cminfo) (class-ptr cminfo)))

(defun common-info-set-monitor (m cminfo)
  (declare (xargs :guard (wff-common-info cminfo)))
  (make-common-info (hashcode cminfo) m (class-ptr cminfo)))

(defun common-info-set-class-ptr (p cminfo)
  (declare (xargs :guard (wff-common-info cminfo)))
  (make-common-info (hashcode cminfo) (monitor cminfo) p))

;---------------------

(defun make-monitor (th mcount mqueue cqueue)
  (list 'monitor th mcount mqueue cqueue))

(defun wff-monitor (monitor)
  (and (true-listp monitor)
       (equal (length monitor) 5)))

(defun new-monitor () 
  (make-monitor -1 0 nil nil))

(defun owner (monitor)
  (declare (xargs :guard (wff-monitor monitor)))
  (nth 1 monitor))

(defun depth (monitor) 
  (declare (xargs :guard (wff-monitor monitor)))
  (nth 2 monitor))


(defun mqueue (monitor) 
  (declare (xargs :guard (wff-monitor monitor)))
  (nth 3 monitor)) ;; monitor     queue
(defun cqueue (monitor) 
  (declare (xargs :guard (wff-monitor monitor)))
  (nth 4 monitor)) ;; conditional variable queue


(defun monitor-set-owner (owner monitor)
  (declare (xargs :guard (wff-monitor monitor)))
  (make-monitor owner
                (depth monitor)
                (mqueue monitor)
                (cqueue monitor)))


(defun monitor-set-depth (d monitor)
  (declare (xargs :guard (wff-monitor monitor)))
  (make-monitor (owner monitor)
                d
                (mqueue monitor)
                (cqueue monitor)))


(defun monitor-set-mqueue (mqueue monitor)
  (declare (xargs :guard (wff-monitor monitor)))
  (make-monitor (owner monitor)
                (depth monitor)
                mqueue
                (cqueue monitor)))


(defun monitor-set-cqueue (cqueue monitor)
  (declare (xargs :guard (wff-monitor monitor)))
  (make-monitor (owner monitor)
                (depth monitor)
                (mqueue monitor)
                cqueue))

;---

(defun make-INSTANCE_CLASS-specific-info (class-desc)
  (list 'specific-info 'INSTANCE_CLASS class-desc))

;;
;; class-ptr is something we can used to find the class-desc in the internal
;; class-table. (class-name)
;; 
;; This class-desc here is different from the class-ptr in the 
;; common-info section of the obj repesentation.
;;
;; class-desc record what is the class this object of "java.lang.Class" representing
;; while the class-ptr records what is the type of the object itself.
;;
 


(defun make-ARRAY_CLASS-specific-info (element-type)
  (list 'specific-info 'ARRAY_CLASS  element-type))

;; Object of class "java.lang.Class" that represents Array Class that represent
;; element-type.



;;(defun make-ARRAY-specific-info (element-type length)
;;  (list 'specific-info 'ARRAY  element-type length))

;; THIS IS NOT USED!!!
(defun make-ARRAY-specific-info (internal-array length)
  (list 'specific-info 'ARRAY  internal-array length))
;; this is right!

(defun make-STRING-specific-info ()
  (list 'specific-info 'STRING))   


;; Comments: ;; how could we find out the java.lang.Class object that
	     ;; represents the STRING class adding entries to the internal
             ;; class-table?  same is true for array...  we need special
             ;; handling for finding the reference for a particular type. Need
             ;; some work in internal-class-table. don't worry about it now.

             ;; we have an internal class-table which is used for lookup from
             ;; classname/array sig to class-obj ref.  8-27-2002

;;
;; although it is not necessary that there exists an java object representing
;; Java array? Class.forName() have to return such an reference. 
;;


(defun make-INSTANCE-specific-info () 
  (list 'specific-info 'GENERIC_OBJECT))

(defun make-INSTANCECLASS-specific-info (class-ptr)
  (list 'specific-info class-ptr))

(defun make-instanceclassarrayclass-info (type-desc)
  (list 'specific-info 'ARRAY_CLASS type-desc))


;;
;; message is a reference to a Java String Object, backtrace is an list of ?? 
;;

(defun make-THROWABLE-specific-info (message backtrace) 
  (list 'specific-info 'THROWABLE_OBJECT message backtrace))

;;
;; Special specific-info
;; 
;;           INSTANCE-CLASS
;;           ARRAY-CLASS
;;           STRING
;;           THROWABLE_OBJECT
;;           ARRAY
;;           GENERIC_OBJECT        
;;

;---------------------------------------------------------------------------
; 
; Tue Jan 13 14:41:23 2004 Define a set of wff predicated which will be used 
;
; in jvm-object-manipulation-primitives.lisp
;
; Originally from consistent-state.lisp

(defun wff-internal-heap-obj (obj)
  (and (true-listp obj)
       (equal (len obj) 4)
       (equal (car obj) 'object)))

; (defun wff-internal-array (array-obj)
;    (and (wff-internal-heap-obj array-obj)
;         (wff-ARRAY-specific-info (specific-info array-obj))))


;; (defun wff-class-ptr (class-ptr)
;;   (and  (true-listp class-ptr)
;;        (or ;; (isoClassType class-ptr)
;;         ;; (stringp class-ptr) ;;  FIX: 10/27/03 to comply with M6's
;;         ;;  usage. cf. consistent-test.lisp  
;;         (isClassType class-ptr) ;;  10/28/03 FIX. changed the definition of
;;         ;;  isClassType
;;         (isArrayType class-ptr))))

(defun wff-class-ptr (class-ptr)
  (or ;; (isoClassType class-ptr)
   ;; (stringp class-ptr) ;;  FIX: 10/27/03 to comply with M6's
   ;;  usage. cf. consistent-test.lisp  
   (isClassType class-ptr) ;;  10/28/03 FIX. changed the definition of
   ;;  isClassType
   (isArrayType class-ptr)))
;;; change the definition of wff-class-ptr
;;; 


(defun wff-common-info-strong (common-info)
  (and (true-listp common-info)
       (equal (len common-info) 4)
       (wff-class-ptr (nth 3 common-info))))


(defun wff-jvp (jvp)
   (alistp jvp))



;----------------------------------------------------------------------

(defun wff-INSTANCE_CLASS-specific-info (specific-info)
  (and (true-listp specific-info)
       (equal (len specific-info) 3)
       (equal (car specific-info) 'specific-info)
       (equal (nth 1 specific-info) 'INSTANCE_CLASS)
       (wff-type-desc (nth 2 specific-info))))

(defun wff-ARRAY_CLASS-specific-info (specific-info)
  (and (true-listp specific-info)
       (equal (len specific-info) 3)
       (equal (car specific-info) 'specific-info)
       (equal (nth 1 specific-info) 'ARRAY_CLASS)
       (wff-type-desc (nth 2 specific-info))))


(defun wff-ARRAY-specific-info (specific-info)
   (and (true-listp specific-info)
        (equal (len specific-info) 4)
        (equal (car specific-info) 'specific-info)
        (equal (nth 1 specific-info) 'ARRAY)
        (integerp (nth 3 specific-info))
        (true-listp (nth 2 specific-info))
        (equal (len (nth 2 specific-info)) (nth 3 specific-info))))

(defun wff-STRING-specific-info (specific-info)
   (and (true-listp specific-info)
        (equal (len specific-info) 2)
        (equal (car specific-info) 'specific-info)
        (equal (nth 1 specific-info) 'STRING)))
        ;;(stringp (nth 3 specific-info))))
;;            (equal (nth 3 specific-info) -1))
;;            (nullp (nth 3 specific-info)))))


;; (defun wff-STRING-specific-info (specific-info)
;;    (and (true-listp specific-info)
;;         (equal (len specific-info) 4)
;;         (equal (car specific-info) 'specific-info)
;;         (equal (nth 1 specific-info) 'STRING)
;;         (stringp (nth 3 specific-info))))
;; ;;            (equal (nth 3 specific-info) -1))
;; ;;            (nullp (nth 3 specific-info)))))


;; (defun make-THROWABLE-specific-info (message backtrace) 
;;   (list 'specific-info 'THROWABLE_OBJECT message backtrace))

(defun wff-THROWABLE-specific-info (specific-info)
   (and (true-listp specific-info)
        (equal (len specific-info) 4)
        (equal (car specific-info) 'specific-info)
        (equal (nth 1 specific-info) 'THROWABLE_OBJECT)
        (stringp (nth 2 specific-info))
        (true-listp (nth 3 specific-info))))

;; (defun make-INSTANCE-specific-info () 
;;   (list 'specific-info 'GENERIC_OBJECT))

(defun wff-GENERIC_OBJECT-specific-info (specific-info)
  (equal specific-info 
         (make-INSTANCE-specific-info)))

(defun wff-specific-info (specific-info)
  (or (wff-INSTANCE_CLASS-specific-info specific-info)
      (wff-ARRAY_CLASS-specific-info specific-info)
      (wff-ARRAY-specific-info specific-info)
      (wff-STRING-specific-info specific-info)
      (wff-THROWABLE-specific-info specific-info)
      (wff-GENERIC_OBJECT-specific-info specific-info)))


;; (defun wff-specific-info (specific-info)
;;   (and (true-listp specific-info)
;;        (consp specific-info)
;;        (equal (car specific-info) 'specific-info)
;;        (cond ((equal (nth 1 specific-info) 'ARRAY) 
;;               (and (equal (len specific-info) 4)
;;                    (integerp (nth 3 specific-info))
;;                    (equal (len (nth 2 specific-info)) (nth 3 specific-info))))
;;              (t t))))


; (defun make-object (commoninfo specific-info java-visible-part)
;   (list 'object commoninfo specific-info java-visible-part))

; (defun common-info   (object)     (nth 1 object))
; (defun specific-info (object)     (nth 2 object))    ;; the format depends on types
; (defun java-visible-portion (object) (nth 3 object))


;; (defun common-info (obj)
;;   (declare (xargs :guard (wff-internal-heap-obj obj)))
;;   (nth 1 obj))

;; (defun specific-info (obj)
;;   (declare (xargs :guard (wff-internal-heap-obj obj)))
;;   (nth 2 obj))

;; (defun java-visible-portion (obj)
;;   (declare (xargs :guard (wff-internal-heap-obj obj)))
;;   (nth 3 obj))


(defun wff-obj-strong (obj)
  (and (wff-internal-heap-obj obj)
       (wff-common-info-strong (common-info obj))
       (wff-specific-info (specific-info obj))
       (wff-jvp (java-visible-portion obj))))


;;; WFF data structure. 

;----------------------------------------------------------------------

;;; some properties of wff-obj-strong

(defthm wff-obj-strong-implies-wff-obj
  (implies (wff-obj-strong obj)
           (wff-obj obj))
  :hints (("Goal" :in-theory (enable wff-obj-strong))))

(defthm wff-obj-strong-implies-wff-common-info
  (implies (wff-obj-strong obj)
           (wff-common-info (common-info obj)))
  :hints (("Goal" :in-theory (enable wff-obj-strong))))


(in-theory (disable wff-obj wff-common-info common-info))


;----------------------------------------------------------------------

;;; Note this wff-field NEED FIX!!! Tue Jan 13 01:33:56 2004

(defun wff-data-field (field)
  (and (consp field)
       (equal (len field) 1)))

(defun fieldname (data-field) 
  (declare (xargs :guard (wff-data-field data-field)))
  ;; as in a object rep
  (car data-field))

(defun fieldvalue (data-field)
  (declare (xargs :guard (wff-data-field data-field)))
  (cdr data-field))

;; this is part of OBJECT representation!
;;
;;---------------------------------------------------------------------


(defun wff-internal-array (array-obj)
   (and (wff-obj-strong array-obj)
        (wff-array-type (obj-type array-obj))
        (wff-ARRAY-specific-info (specific-info array-obj))))

;----------------------------------------------------------------------

(defun wff-heap (hp)
  (alistp hp))

;----------------------------------------------------------------------



(defun wff-heap-strong (hp)
  (and (wff-heap hp)
       (if (not (consp hp)) t  
         (and (wff-obj-strong (cdar hp))
              (wff-heap-strong (cdr hp))))))


