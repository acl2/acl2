; The class-table structure
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

(include-book "classes")
(include-book "kestrel/maps/maps" :dir :system)
(include-book "kestrel/lists-light/memberp" :dir :system)
(local (include-book "kestrel/jvm/utilities" :dir :system))
(local (include-book "std/lists/union" :dir :system))

; The class-table of a JVM state is a map, where the keys are class
; names (strings) and the values are class-infos.

;fixme theorems should go in the same package as the forall function's name
;fixme the defforall could add -list or just -s to the names of the list params?
(defforall all-keys-bound-to-class-infosp (key class-table)
  (class-infop (g key class-table) key)
  :declares ((xargs :guard (all-class-namesp key)))
  :fixed class-table)

;todo: make this an alist instead?
(defund class-tablep0 (class-table)
  (declare (xargs :guard t))
  (let* (;call mapp here?
         (dom (acl2::rkeys class-table))
         (key-list (SET::2LIST dom))) ;call key-list?
    (and (all-class-namesp key-list) ;;fixme abstract into something like deffoldmap:
         (all-keys-bound-to-class-infosp key-list class-table))))

(defund bound-in-class-tablep (class-name class-table)
  (declare (xargs :guard (and (class-namep class-name)
                              (class-tablep0 class-table))))
  (set::in class-name (acl2::rkeys class-table)))

;; Logically just g but has a guard.  Requires that the class be bound in the table.
;todo: use this more
(defund get-class-info (class-name class-table)
  (declare (xargs :guard (and (class-namep class-name)
                              (class-tablep0 class-table)
                              (bound-in-class-tablep class-name class-table))))
  (g class-name class-table))

(defthm field-info-alistp-of-class-decl-non-static-fields-of-get-class-info ;no free var
  (implies (class-infop (get-class-info class-name class-table) class-name)
           (field-info-alistp (class-decl-non-static-fields (get-class-info class-name class-table))))
  :hints (("Goal" :use (:instance field-info-alistp-of-class-decl-non-static-fields (class-info (get-class-info class-name class-table)))
           :in-theory (disable field-info-alistp-of-class-decl-non-static-fields))))

(defthm field-info-alistp-of-class-decl-static-fields-of-get-class-info ;no free var
  (implies (class-infop (get-class-info class-name class-table) class-name)
           (field-info-alistp (class-decl-static-fields (get-class-info class-name class-table))))
  :hints (("Goal" :use (:instance field-info-alistp-of-class-decl-static-fields (class-info (get-class-info class-name class-table)))
           :in-theory (disable field-info-alistp-of-class-decl-static-fields))))

;no free var
(defthm true-listp-of-class-decl-interfaces-of-get-class-info
  (implies (class-infop (get-class-info class-name class-table) class-name)
           (true-listp (class-decl-interfaces (get-class-info class-name class-table))))
  :hints (("Goal" :use (:instance true-listp-of-class-decl-interfaces (class-info (get-class-info class-name class-table)))
           :in-theory (disable true-listp-of-class-decl-interfaces))))

;no free var
(defthm all-class-namesp-of-class-decl-interfaces-of-get-class-info
  (implies (class-infop (get-class-info class-name class-table) class-name)
           (all-class-namesp (class-decl-interfaces (get-class-info class-name class-table))))
  :hints (("Goal" :use (:instance all-class-namesp-of-class-decl-interfaces (class-info (get-class-info class-name class-table)))
           :in-theory (disable all-class-namesp-of-class-decl-interfaces))))


;; (defun all-keys-bound-to-class-infosp (key-list class-table)
;;   (declare (xargs :guard (string-listp key-list)))
;;   (if (endp key-list)
;;       t
;;     (and (let* ((key (first key-list))
;;                 (val (get-class-info key class-table)))
;;            (class-infop val key))
;;          (all-keys-bound-to-class-infosp (rest key-list) class-table))))

;; (defcong perm equal (all-keys-bound-to-class-infosp key-list class-table) 1
;;   :hints (("Goal" :in-theory (enable PERM)))
;;   )

;not used
;; (defun map-fold-class-infop (class-table)
;;   (let ((key-list (acl2::key-list class-table)))
;;     (all-keys-bound-to-class-infosp key-list class-table)))

(defthm use-all-keys-bound-to-class-infosp
  (implies (and (all-keys-bound-to-class-infosp keys class-table)
                (memberp key keys))
           (class-infop (get-class-info key class-table) key))
  :hints (("Goal" :in-theory (enable get-class-info))))

(defthm bound-in-class-tablep-when-all-keys-bound-to-class-infosp
  (implies (and (all-keys-bound-to-class-infosp keys class-table)
                (memberp key keys))
           (bound-in-class-tablep key class-table))
  :hints (("Goal" :in-theory (enable all-keys-bound-to-class-infosp
                                     bound-in-class-tablep))))

(defthm class-infop0-of-get-class-info
  (implies (and (all-keys-bound-to-class-infosp keys class-table)
                (memberp key keys))
           (class-infop0 (get-class-info key class-table)))
  :hints (("Goal" :use (:instance use-all-keys-bound-to-class-infosp)
           :in-theory (disable use-all-keys-bound-to-class-infosp
                               acl2::use-all-keys-bound-to-class-infosp-2
                               acl2::use-all-keys-bound-to-class-infosp))))

;equivalent to subsetp-equal but also prints a message
;todo: add a version of defforall that prints a message if any element fails to satisfy the predicate, then use that here
(defun all-interfaces-present (interface-names all-class-names)
  (declare (xargs :guard (and (true-listp interface-names)
                              (true-listp all-class-names))))
  (if (endp interface-names)
      t
    (if (member-equal (first interface-names) all-class-names) ;fixme also test that it is bound to an interface?! will require passing in the class-table here
        (all-interfaces-present (rest interface-names) all-class-names)
      (prog2$ (cw "Note: Missing interface: ~s0!~%" (first interface-names))
              nil))))

(defthm all-interfaces-present-become-subsetp-equal
  (equal (all-interfaces-present interface-names all-class-names)
         (acl2::subsetp-equal interface-names all-class-names)))

;the last param is just an optimization, to avoid recomputing the domain of the class-table over and over.
(defforall all-super-interfaces-bound (class-name class-table all-class-names)
    (all-interfaces-present (class-decl-interfaces (get-class-info class-name class-table)) all-class-names)
    ;alternative syntax: (lambda (class-name) (subsetp-eq (class-decl-interfaces (get-class-info class-name class-table)) all-class-names))
    :fixed (class-table all-class-names)
    :declares ((xargs :guard (and (all-class-namesp class-name)
                                  (all-class-namesp all-class-names)
                                  (true-listp all-class-names)
                                  (CLASS-TABLEP0 CLASS-TABLE)
                                  (all-keys-bound-to-class-infosp class-name class-table)))))



;justifies including this as a known-predicate
(defthm booleanp-of-bound-in-class-tablep
  (booleanp (bound-in-class-tablep class-name class-table)))

(defthm bound-in-class-tablep-when-equal-of-get-class-info
  (implies (and (equal (get-class-info class-name class-table) val)
                (not (equal nil val))) ;can axe handle just "val" here?
           (bound-in-class-tablep class-name class-table))
  :hints (("Goal" :in-theory (enable bound-in-class-tablep get-class-info))))

;use a forall?
(defund all-bound-in-class-tablep (class-names class-table)
  (declare (xargs :guard (and (true-listp class-names)
                              (all-class-namesp class-names)
                              (class-tablep0 class-table)
                              )))
  (if (endp class-names)
      t
    (and (bound-in-class-tablep (first class-names) class-table)
         (all-bound-in-class-tablep (rest class-names) class-table))))

(defthmd all-bound-in-class-tablep-alt
  (equal (all-bound-in-class-tablep class-names class-table)
         (acl2::subsetp-equal class-names (set::2list (acl2::rkeys class-table))))
  :hints (("Goal" :in-theory (enable all-bound-in-class-tablep bound-in-class-tablep acl2::subsetp-equal))))

(defthm all-bound-in-class-tablep-of-cdr
  (implies (all-bound-in-class-tablep names class-table)
           (all-bound-in-class-tablep (cdr names) class-table))
  :hints (("Goal" :in-theory (enable all-bound-in-class-tablep))))

(defthm all-bound-in-class-tablep-of-append
  (equal (all-bound-in-class-tablep (append names names2) class-table)
         (and (all-bound-in-class-tablep names class-table)
              (all-bound-in-class-tablep names2 class-table)))
  :hints (("Goal" :in-theory (enable all-bound-in-class-tablep))))

(defthm all-bound-in-class-tablep-of-cons
  (equal (all-bound-in-class-tablep (cons name names) class-table)
         (and (bound-in-class-tablep name class-table)
              (all-bound-in-class-tablep names class-table)))
  :hints (("Goal" :in-theory (enable all-bound-in-class-tablep))))

(defthm all-bound-in-class-tablep-of-nil
  (equal (all-bound-in-class-tablep nil class-table)
         t)
  :hints (("Goal" :in-theory (enable all-bound-in-class-tablep))))

(defthm use-all-bound-in-class-tablep
  (implies (and (all-bound-in-class-tablep class-names class-table) ;class-names is a free var
                (memberp class-name class-names))
           (bound-in-class-tablep class-name class-table))
  :hints (("Goal" :in-theory (enable all-bound-in-class-tablep))))

(defthm use-all-super-interfaces-bound-alt
  (implies (and (all-super-interfaces-bound class-names class-table (set::2list (acl2::rkeys class-table)))
                (memberp class-name class-names))
           (all-bound-in-class-tablep (class-decl-interfaces (get-class-info class-name class-table)) class-table))
  :hints (("Goal" :use (:instance acl2::use-all-super-interfaces-bound (acl2::free-class-name class-names)
                                  (all-class-names (set::2list (acl2::rkeys class-table)))
                                  (acl2::x class-name))
           :in-theory (e/d (all-bound-in-class-tablep-alt) ( acl2::use-all-super-interfaces-bound)))))


(defthm class-namep-of-class-decl-superclass-of-get-class-info
  (implies (and (class-infop (get-class-info class-name class-table) class-name)
                (not (equal class-name "java.lang.Object"))
;                (not (class-decl-interfacep class-info))
                )
           (class-namep (class-decl-superclass (get-class-info class-name class-table))))
  :hints (("Goal" :use (:instance class-namep-of-class-decl-superclass (class-info (get-class-info class-name class-table)))
           :in-theory (disable class-namep-of-class-decl-superclass))))

;; TODO: Compare this to what we say in class-infop
(defund super-class-okayp (class-name class-table)
  (declare (xargs :guard (and (class-namep class-name)
                              (class-tablep0 class-table)
                              (bound-in-class-tablep class-name class-table)
                              (class-infop (get-class-info class-name class-table) class-name))))
  (let* ((class-info (get-class-info class-name class-table))
         (super-class-name (class-decl-superclass class-info)))
    (if (equal class-name "java.lang.Object")
        ;;java.lang.object has no superclass:
        (equal :none super-class-name)
      ;; (if (class-decl-interfacep class-info)
      ;;     ;; if it's an interface, it's super-class must be java.lang.Object:
      ;;     (equal super-class-name ;Note: class-tablep checks that object is bound in the class file.
      ;;            "java.lang.Object")
      ;;otherwise, it's a normal class:
      (and (bound-in-class-tablep super-class-name class-table)
           (let* ((super-class-info (get-class-info super-class-name class-table)))
             (and (if super-class-info
                      t
                    (prog2$ (cw "Note: Missing super-class: ~s0!~%" super-class-name)
                            nil))
                  ;; the super-class must be a class, not an interface:
                  (and (class-namep super-class-name)
                       (class-infop super-class-info super-class-name)
                       (not (class-decl-interfacep super-class-info))))))
;)
      )))

;class-name is really class-or-interface-name
(defforall all-super-classes-okayp (class-name class-table)
  (super-class-okayp class-name class-table)
  :fixed (class-table)
  :declares ((xargs :guard (and (true-listp class-name)
                                (all-class-namesp class-name)
                                (class-tablep0 class-table)
                                (all-keys-bound-to-class-infosp class-name class-table)))))

;;Logically equivalent to (boolfix of) b, but prints a MSG when b is false:
(defun check-bool (b msg)
  (declare (xargs :guard (and (booleanp b) (stringp msg))))
  (if b
      t
    (prog2$ (cw msg)
            nil)))

;; array classes:

;; In general, a class or interface is either:
;; 1) An array class.
;; 2) An ordinary (non-array) class.
;; 3) An interface.

;; ;assumes the name is in the class-table (unless it is an array class). change that?
;; (defun non-array-classp (class-or-interface-name class-table)
;;   (declare (xargs :guard t))
;;   (and (not (array-classp class-or-interface-name)) ;must test this first, since we can't currently look up an array class in the class-table
;;        (let* ((class-info (get-class-info class-or-interface-name class-table))
;;               (access-flags (class-decl-access-flags class-info)))
;;          (and (true-listp access-flags) ;for guards, could instead assume the class-table is well-formed
;;               (not (member-eq :acc_interface access-flags))))))

;; ;fixme call this more?
;; ;assumes the name is in the class-table (unless it is an array class). change that?
;; (defun bound-to-an-interfacep (class-or-interface-name class-table)
;;   (declare (xargs :guard t))
;;   (and (not (array-classp class-or-interface-name)) ;must test this first, since we can't currently look up an array class in the class-table
;;        (let* ((class-info (get-class-info class-or-interface-name class-table))
;;               (access-flags (class-decl-access-flags class-info)))
;;          (and (true-listp access-flags) ;for guards, could instead assume the class-table is well-formed
;;               (member-eq :acc_interface access-flags)))))

;; ;assumes the name is in the class-table (unless it is an array class). change that?
;; (defun classp (class-or-interface-name class-table)
;;   (declare (xargs :guard t))
;;   (or (array-classp class-or-interface-name)
;;       (non-array-classp class-or-interface-name class-table)))

(defthm class-infop0-of-get-class-info-2
  (implies (and (class-tablep0 class-table)
                (bound-in-class-tablep class-name class-table))
           (class-infop0 (get-class-info class-name class-table)))
  :hints (("Goal" :in-theory (enable class-tablep0 bound-in-class-tablep))))

;this is called by class-tablep, so it can't use class-tablep in its guard
(defun bound-to-a-non-interfacep (class-name class-table)
  (declare (xargs :guard (and (class-namep class-name)
                              (class-tablep0 class-table))))
  (if (and (bound-in-class-tablep class-name class-table)
           (not (class-decl-interfacep (get-class-info class-name class-table))))
      t
    (mbe :exec (prog2$ (cw "Note: ~s0 must be bound to a non-interface in the class table.~%" class-name)
                       nil)
         :logic nil)))

;These constants help ensure that we don't mistype the name of the
;exception classes anywhere:
(defconst *ArithmeticException*            "java.lang.ArithmeticException")
(defconst *ArrayIndexOutOfBoundsException* "java.lang.ArrayIndexOutOfBoundsException")
(defconst *ArrayStoreException*            "java.lang.ArrayStoreException")
(defconst *ClassCastException*             "java.lang.ClassCastException")
(defconst *IllegalMonitorStateException*   "java.lang.IllegalMonitorStateException")
(defconst *NegativeArraySizeException*     "java.lang.NegativeArraySizeException")
(defconst *NullPointerException*           "java.lang.NullPointerException")
(defconst *WrongMethodTypeException*       "java.lang.invoke.WrongMethodTypeException")
(defconst *IncompatibleClassChangeError*   "java.lang.IncompatibleClassChangeError")
(defconst *NoSuchFieldError*               "java.lang.NoSuchFieldError")
(defconst *IllegalAccessError*             "java.lang.IllegalAccessError")

;todo: does this contain everything it needs to?
(defconst *built-in-exception-classes*
  (list *NullPointerException*
        *NegativeArraySizeException*
        *ArrayIndexOutOfBoundsException*
        *ArrayStoreException*
        *IllegalMonitorStateException*
        *ClassCastException*
        *ArithmeticException*
        *WrongMethodTypeException*
        *IncompatibleClassChangeError*
        *NoSuchFieldError*
        *IllegalAccessError*))

;use defforall
(defund all-bound-to-a-non-interfacep (items class-table)
  (declare (xargs :guard (and (true-listp items)
                              (all-class-namesp items)
                              (class-tablep0 class-table))))
  (if (endp items)
      t
    (and (bound-to-a-non-interfacep (first items) class-table)
         (all-bound-to-a-non-interfacep (rest items) class-table))))

(defthm all-bound-to-a-non-interfacep-of-cdr
  (implies (all-bound-to-a-non-interfacep names class-table)
           (all-bound-to-a-non-interfacep (cdr names) class-table))
  :hints (("Goal" :in-theory (enable all-bound-to-a-non-interfacep))))

(defthm all-bound-to-a-non-interfacep-of-cons
  (equal (all-bound-to-a-non-interfacep (cons name names) class-table)
         (and (bound-to-a-non-interfacep name class-table)
              (all-bound-to-a-non-interfacep names class-table)))
  :hints (("Goal" :in-theory (enable all-bound-to-a-non-interfacep))))

(defthm bound-in-class-tablep-when-all-bound-to-a-non-interfacep
  (implies (and (all-bound-to-a-non-interfacep names class-table)
                (member-equal name names))
           (bound-in-class-tablep name class-table))
  :hints (("Goal" :in-theory (enable all-bound-to-a-non-interfacep))))


;TODO: call this well-formed-class-tablep and then rename class-tablep0 to class-tablep?
;fixme better way to recur through maps
(defund class-tablep (class-table)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable class-tablep0)))))
  (and (class-tablep0 class-table)
       (let* ( ;call mapp here?
              (dom (acl2::rkeys class-table))
              (key-list (SET::2LIST dom))) ;call key-list?
         (and (all-bound-to-a-non-interfacep *built-in-exception-classes* class-table)
              (bound-to-a-non-interfacep "java.lang.String" class-table) ;new!
              (bound-in-class-tablep "java.lang.Object" class-table)
              (let ((object-class-info (get-class-info "java.lang.Object" class-table)))
                (and object-class-info ;Object is bound, and it's bound to a class
                     (true-listp (class-decl-access-flags object-class-info)) ;for guards (todo: drop?)
                     (not (class-decl-interfacep object-class-info))))
              (check-bool (all-super-interfaces-bound key-list class-table key-list) ;All superinterfaces of any class/interface must also be in dom.
                          "ERROR: interfaces are wrong in class table!~%")
              (check-bool (all-super-classes-okayp key-list class-table) ;The super-class of every class must also be in dom.
                          "ERROR: super-classes are wrong in class table!~%")))))

(defthm class-tablep0-forward-to-class-tablep0
  (implies (class-tablep class-table)
           (class-tablep0 class-table))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable class-tablep))))



(defun set-all-to-empty-class (class-names)
  (if (endp class-names)
      nil
    (s (first class-names) (empty-class) (set-all-to-empty-class (rest class-names)))))

(defun empty-class-table ()
  (s "java.lang.Object"
     (make-class-info :none nil nil nil nil nil) ;this is fake
     (set-all-to-empty-class (cons "java.lang.String" *built-in-exception-classes*))))

(defthm class-tablep-of-empty-class-table
  (class-tablep (empty-class-table)))

;no longer using this because now every class table must include the exception classes
;(defund empty-class-table () (declare (xargs :guard t)) (acl2::empty-map))

;; (defthm class-tablep-of-empty-empty-class-table
;;   (class-tablep (empty-class-table)))

(defun add-class (class-name class-info class-table)
  (declare (xargs :guard (and (class-namep class-name)
                              (class-infop class-info class-name)
                              (class-tablep class-table))))
  (s class-name class-info class-table))

;; ;fixme prove - not true if you bind a special class to a bad value (e.g., you bind an exception class to an interface?)
;; (defthm class-tablep-of-add-class
;;   (implies (and (class-infop class-info class-name)
;;                 (class-tablep class-table)
;;                 (stringp class-name)
;;                 )
;;            (class-tablep (add-class class-name class-info class-table)))
;;   :hints (("Goal" :in-theory (enable class-tablep))))

(encapsulate (((error-looking-up-class * *) => *))
             (local (defun error-looking-up-class (class-name class-table) (declare (ignore class-name class-table)) nil))
             (defthm all-class-namesp-of-error-looking-up-class
               (all-class-namesp (error-looking-up-class class-name class-table)))
             (defthm true-listp-of-error-looking-up-class
               (true-listp (error-looking-up-class class-name class-table))))

;; (defthm true-listp-of-error-looking-up-class
;;   (true-listp (error-looking-up-class class-name class-table))
;;   :hints (("Goal" :use (:instance all-class-namesp-of-error-looking-up-class)
;;            :in-theory (disable all-class-namesp-of-error-looking-up-class))))

(defthm class-infop-of-get-class-info
  (implies (and (class-tablep0 class-table)
                (bound-in-class-tablep class-name class-table))
           (class-infop (get-class-info class-name class-table) class-name))
  :hints (("Goal" :in-theory (enable class-tablep0 bound-in-class-tablep))))

;; Shows that we can distinguish a string from a valid class-info (e.g., in resolve-field).
(defthm not-stringp-of-get-class-info-when-class-tablep
  (implies (class-tablep class-table)
           (not (stringp (get-class-info class-name class-table))))
  :hints (("Goal" :use (:instance class-infop-of-get-class-info)
           :in-theory (e/d (bound-in-class-tablep get-class-info)
                           (class-infop-of-get-class-info)))))

(defund get-super-class (class-name class-table)
  (declare (xargs :guard (and (class-namep class-name)
                              (class-tablep class-table)
                              (bound-in-class-tablep class-name CLASS-TABLE))
                  :guard-hints (("Goal" :in-theory (enable class-tablep)))))
  (class-decl-superclass (get-class-info class-name class-table)))

(defthm class-namep-of-get-super-class-none-1
  (implies (super-class-okayp class-name class-table)
           (equal (class-namep (get-super-class class-name class-table))
                  (not (equal "java.lang.Object" class-name))))
  :hints (("Goal" :in-theory (enable super-class-okayp  get-super-class))))

(defthm class-namep-of-get-super-class-none-2
  (implies (and (all-super-classes-okayp class-names class-table) ;class-names is a free var
                (memberp class-name class-names))
           (equal (class-namep (get-super-class class-name class-table))
                  (not (equal "java.lang.Object" class-name)))))

(defthm class-namep-of-get-super-class-none-3
  (implies (and (class-tablep class-table)
                (bound-in-class-tablep class-name CLASS-TABLE))
           (equal (class-namep (get-super-class class-name class-table))
                  (not (equal "java.lang.Object" class-name))))
  :hints (("Goal" :in-theory (enable class-tablep bound-in-class-tablep))))

;count ensures termination
(defun get-super-classes-aux (class-name class-table count)
  (declare (xargs :measure (nfix (+ 1 count))
                  :guard (and (class-namep class-name)
                              (class-tablep class-table))
                  :guard-hints (("Goal" :in-theory (enable class-tablep))))
           (type (integer 0 *) count))
  (if (zp count) ;forces termination
      nil
    (if (equal class-name "java.lang.Object")
        nil ;no super classes for Object!
      (if (not (bound-in-class-tablep class-name class-table))
          (prog2$ (er hard? 'get-super-classes-aux "Class not found: ~x0." class-name)
                  (error-looking-up-class class-name class-table) ;will cause an error instead of being evaluated
                  )
        (let* ((super-class (get-super-class class-name class-table)))
          (cons super-class
                (get-super-classes-aux super-class class-table (+ -1 count))))))))

(defthm true-listp-of-get-super-classes-aux
  (true-listp (get-super-classes-aux class-name class-table count)))

;fixme use defopener?
(defthm get-super-classes-aux-opener
  (implies (and (not (equal class-name "java.lang.Object"))
                (not (zp count)))
           (equal (get-super-classes-aux class-name class-table count)
                  (if (not (bound-in-class-tablep class-name class-table))
                      (error-looking-up-class class-name class-table) ;will cause an error instead of being evaluated
                    (let* ((super-class (get-super-class class-name class-table)))
                      (cons super-class
                            (get-super-classes-aux super-class class-table (+ -1 count))))))))

(defthm get-super-classes-aux-base
  (equal (get-super-classes-aux "java.lang.Object" class-table count)
         nil))

;; ;rename to allow for none
;now has a free var... (almost want to backchain when trying to match free vars...)
;fixme what is x is the info for an interface?
;; (defthm class-namep-of-class-decl-superclass2
;;   (implies (and (class-infop x class-name)
;;                 (not (equal class-name "java.lang.Object")))
;;            (class-namep (class-decl-superclass x)))
;;   :hints (("Goal" :in-theory (enable class-infop))))

(defthm class-namep-of-get-super-class-special-case
  (implies (and (class-infop (get-class-info class-name class-table) class-name)
                (not (equal class-name "java.lang.Object"))
                ;(not (class-decl-interfacep (get-class-info class-name class-table)))
                )
           (class-namep (get-super-class class-name class-table)))
  :hints (("Goal" :use (:instance class-namep-of-class-decl-superclass (class-info (get-class-info class-name class-table)))
           :in-theory (e/d (GET-SUPER-CLASS) (class-namep-of-class-decl-superclass)))))

(defthm super-class-is-not-an-interface
  (implies (and (not (equal class-name "java.lang.Object"))
                (memberp class-name keys) ; keys is a free var
                (all-super-classes-okayp keys class-table)
                (not (class-decl-interfacep (get-class-info class-name class-table))))
           (not (class-decl-interfacep (get-class-info (get-super-class class-name class-table)
                                          class-table))))
  :hints (("Goal" :in-theory (enable get-super-class all-super-classes-okayp super-class-okayp memberp))))

(defthm super-class-is-not-an-interface2
  (implies (and (not (equal class-name "java.lang.Object"))
                (bound-in-class-tablep class-name class-table)
                (class-tablep class-table)
                (not (class-decl-interfacep (get-class-info class-name class-table))))
           (not (class-decl-interfacep (get-class-info (get-super-class class-name class-table) class-table))))
  :hints (("Goal" :use (:instance super-class-is-not-an-interface (keys (set::2list (acl2::rkeys class-table))))
           :in-theory (e/d (get-super-class class-tablep bound-in-class-tablep) (super-class-is-not-an-interface)))))

(defthm all-class-namesp-of-get-super-classes-aux
  (implies (and (class-tablep class-table)
;                (not (class-decl-interfacep (get-class-info class-name class-table)))
                )
           (all-class-namesp (get-super-classes-aux class-name class-table n)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (get-super-classes-aux ;class-tablep
                            bound-in-class-tablep) ()))))

;returns the (proper) super-classes of class-name from most to least specific (ending with java.lang.Object)
;fixme really this should be called get-super-class-names
(defun acl2::get-super-classes (class-name class-table)
  (declare (xargs :guard (and (class-tablep class-table)
                              (class-namep class-name))))
  (get-super-classes-aux class-name class-table 1000000 ;fixme use (len (dom class-table)) instead, but that can cause problems for rewriting?
                         ))

;fixme uncomment
;; (defthm string-listp-of-get-super-classes
;;   (implies (class-tablep class-table)
;;            (string-listp (acl2::get-super-classes class-name class-table))))

;; (defthm all-keys-bound-to-class-infosp-when-subset-of-dom
;;   (implies  (and (class-tablep class-table)
;;                  (all-bound-in-class-tablep names class-table))
;;             (all-keys-bound-to-class-infosp names class-table))
;;   :hints (("Goal" :in-theory (enable ALL-KEYS-BOUND-TO-CLASS-INFOSP all-bound-in-class-tablep BOUND-IN-CLASS-TABLEP))))

(defthm all-bound-in-class-tablep-of-class-decl-interfaces
  (implies (and (class-tablep class-table)
                (bound-in-class-tablep class-name class-table))
           (all-bound-in-class-tablep (class-decl-interfaces (get-class-info class-name class-table)) class-table))
  :hints (("Goal" :in-theory (enable class-tablep BOUND-IN-CLASS-TABLEP))))

;; (thm
;;  (IMPLIES
;;   (AND (ALL-KEYS-BOUND-TO-CLASS-INFOSP keys CLASS-TABLE)
;;        (memberp name keys))
;;   (CLASS-INFOP (get-class-info NAME CLASS-TABLE)
;;                CLASS-NAME))
;;  :hints (("Goal" :in-theory (enable ALL-KEYS-BOUND-TO-CLASS-INFOSP MEMBERP))))

;; (thm
;;  (equal (ACL2::SUBSETP-EQUAL x (SET::2LIST set))
;;         (set::subset (list::2set x) set)))

;a workset algorithm
;note: this does not look up superclasses!
(defun acl2::get-super-interfaces-aux (class-or-interface-names class-table count acc)
  (declare (xargs :measure (nfix (+ 1 count))
                  :guard (and (class-tablep class-table)
                              (all-class-namesp class-or-interface-names)
                              (true-listp class-or-interface-names)
                              (true-listp acc)
                              (all-bound-in-class-tablep class-or-interface-names class-table))
                  :guard-hints (("Goal" :in-theory (enable class-tablep))))
           (type (integer 0 *) count))
  (if (zp count) ; to ensure termination
      acc
    (if (endp class-or-interface-names)
        acc
      (let* ((class-or-interface0-name (first class-or-interface-names))
             (class-info (get-class-info class-or-interface0-name class-table))
             (direct-super-interfaces (class-decl-interfaces class-info)))
        (acl2::get-super-interfaces-aux (append direct-super-interfaces
                                                (rest class-or-interface-names))
                                        class-table
                                        (+ -1 count)
                                        (union-equal direct-super-interfaces acc))))))

(defthm get-super-interfaces-aux-base
  (implies (endp class-or-interface-names)
           (equal (acl2::get-super-interfaces-aux class-or-interface-names class-table count acc)
                  acc)))

(defthm get-super-interfaces-aux-opener
  (implies (and (not (zp count))
                (not (endp class-or-interface-names)))
           (equal (acl2::get-super-interfaces-aux class-or-interface-names class-table count acc)
                  (let* ((class-or-interface0-name (first class-or-interface-names))
                         (class-info (get-class-info class-or-interface0-name class-table))
                         (direct-super-interfaces (class-decl-interfaces class-info)))
                    (acl2::get-super-interfaces-aux (append direct-super-interfaces
                                                            (rest class-or-interface-names))
                                                    class-table
                                                    (+ -1 count)
                                                    (union-equal direct-super-interfaces acc))))))

;write a tool to automate stuff like this?
(defthm true-listp-of-get-super-interfaces-aux
  (implies (true-listp acc)
           (true-listp (acl2::get-super-interfaces-aux class-or-interface-names class-table count acc))))

(defun acl2::get-super-interfaces (class-or-interface-names class-table)
  (declare (xargs :guard (and (all-class-namesp class-or-interface-names)
                              (true-listp class-or-interface-names)
                              (class-tablep class-table)
                              (all-bound-in-class-tablep class-or-interface-names class-table))
                  :guard-hints (("Goal" :in-theory (enable class-tablep)))))
  (acl2::get-super-interfaces-aux class-or-interface-names class-table 100000 nil))

;BOZO is this up to date?
; Note that the definition below of the Thread class includes a 'run' method,
;  which most applications will override.  The definition is consistent
;  with the default run method provided by the Thread class [O'Reily]

;dup - this and related stuff should go in a separate state book?
;(defun class-table (s) (declare (xargs :guard (true-listp s))) (nth 2 s))


;; Test whether CLASS-NAME is a proper superclass of CLASS-NAME2.
;todo: remove hyphen from name
(defund super-classp (class-name class-name2 class-table)
  (declare (xargs :guard (and (class-tablep class-table)
                              (class-namep class-name)
                              (class-namep class-name2))))
  (member-equal class-name (acl2::get-super-classes class-name2 class-table)))

;; Test whether CLASS-NAME is a proper subclass of CLASS-NAME2.
;todo: remove hyphen from name
(defund sub-classp (class-name class-name2 class-table)
  (declare (xargs :guard (and (class-tablep class-table)
                              (class-namep class-name)
                              (class-namep class-name2))))
  (super-classp class-name2 class-name class-table))

;; Test whether CLASS-NAME is a proper subclass of CLASS-NAME2 or is the same class as CLASS-NAME2.
(defund sub-class-or-same-classp (class-name class-name2 class-table)
  (declare (xargs :guard (and (class-tablep class-table)
                              (class-namep class-name)
                              (class-namep class-name2))))
  (or (equal class-name class-name2)
      (sub-classp class-name class-name2 class-table)))

;; (thm
;;  (implies (and (All-Super-Classes-Okayp (SET::2LIST (ACL2::RKEYS CLASS-TABLE))
;;                                         CLASS-TABLE
;;                                         (SET::2LIST (ACL2::RKEYS CLASS-TABLE)))
;;                (set::in class-or-interface-name (acl2::rkeys class-table))
;;                (not (equal "java.lang.Object" class-or-interface-name)))
;;           (set::in (class-decl-super-class (get-class-info class-or-interface-name class-table))
;;                    (acl2::rkeys class-table)))
;;  :hints (("Goal" :in-theory (enable class-tablep))))

;move
(defthm member-when-not-memberp-of-cdr-cheap
  (implies (not (memberp a (cdr x)))
           (equal (memberp a x)
                  (if (consp x)
                      (equal a (car x))
                    nil)))
  :hints (("Goal" :in-theory (enable memberp)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm in-get-super-class-and-rkeys-helper
  (implies (and (all-super-classes-okayp keys class-table)
                ;; (class-tablep class-table)
                (memberp class-name keys)
                (not (equal class-name "java.lang.Object"))
                ;; (not (class-decl-interfacep (get-class-info class-name class-table)))
                )
           (set::in (get-super-class class-name class-table) (acl2::rkeys class-table)))
  :hints (("Goal" :in-theory (enable ALL-SUPER-CLASSES-OKAYP
                                     get-super-class
                                     bound-in-class-tablep
                                     all-super-classes-okayp
                                     SUPER-CLASS-OKAYP;memberp
                                     class-decl-superclass class-tablep))))

;rename
(defthm bound-in-class-tablep-of-get-super-class-helper
  (implies (and (all-super-classes-okayp keys class-table)
                ;; (class-tablep class-table)
                (memberp class-name keys)
                (not (equal class-name "java.lang.Object"))
                ;; (not (class-decl-interfacep (get-class-info class-name class-table)))
                )
           (bound-in-class-tablep (get-super-class class-name class-table) class-table))
  :hints (("Goal" :in-theory (enable ALL-SUPER-CLASSES-OKAYP
                                     get-super-class
                                     bound-in-class-tablep
                                     all-super-classes-okayp
                                     SUPER-CLASS-OKAYP;memberp
                                     class-decl-superclass class-tablep))))

(defthm bound-in-class-tablep-of-get-super-class
  (implies (and (class-tablep class-table)
                (bound-in-class-tablep class-name class-table)
                (not (equal class-name "java.lang.Object"))
                ;; (not (class-decl-interfacep (get-class-info class-name class-table)))
                )
           (bound-in-class-tablep (get-super-class class-name class-table) class-table))
  :hints (("Goal"
           :use (:instance bound-in-class-tablep-of-get-super-class-helper (keys (set::2list (acl2::rkeys class-table))))
           :in-theory (enable class-tablep bound-in-class-tablep))))

(defthm not-class-decl-interfacep-of-get-class-info-of-get-super-class-helper
  (implies (and (all-super-classes-okayp keys class-table)
                ;; (class-tablep class-table)
                (memberp class-name keys)
                (not (equal class-name "java.lang.Object"))
                ;; (not (class-decl-interfacep (get-class-info class-name class-table)))
                )
           (not (class-decl-interfacep (get-class-info (get-super-class class-name class-table) class-table))))
  :hints (("Goal" :in-theory (enable all-super-classes-okayp
                                     get-super-class
                                     bound-in-class-tablep
                                     all-super-classes-okayp
                                     super-class-okayp;memberp
                                     class-decl-superclass class-tablep))))

(defthm not-class-decl-interfacep-of-get-class-info-of-get-super-class
  (implies (and (class-tablep class-table)
                (bound-in-class-tablep class-name class-table)
                (not (equal class-name "java.lang.Object"))
                ;; (not (class-decl-interfacep (get-class-info class-name class-table)))
                )
           (not (class-decl-interfacep (get-class-info (get-super-class class-name class-table) class-table))))
  :hints (("Goal"
           :use (:instance not-class-decl-interfacep-of-get-class-info-of-get-super-class-helper (keys (set::2list (acl2::rkeys class-table))))
           :in-theory (enable class-tablep bound-in-class-tablep))))

;; (defthm in-of-class-decl-superclass-lemma-special-case
;;   (implies (and (class-tablep class-table)
;;                 (bound-in-class-tablep CLASS-NAME CLASS-TABLE)
;;                 (not (equal class-name "java.lang.Object"))
;;                 (not (class-decl-interfacep (get-class-info class-name class-table)))
;;                 )
;;            (bound-in-class-tablep (CLASS-DECL-SUPER-CLASS (get-class-info CLASS-NAME CLASS-TABLE)) ;(class-decl-superclass (get-class-info class-name class-table))
;;                     class-table
;;                     ))
;;   :hints (("Goal" :use (:instance in-of-class-decl-superclass-lemma (keys (acl2::rkeys class-table)) (all-keys (acl2::rkeys class-table)))
;;            :in-theory (e/d (CLASS-TABLEP) (in-of-class-decl-superclass-lemma)))))

(defthm super-class-is-not-interface
  (implies (and  (class-tablep class-table)
                (not (equal "java.lang.Object" class-name))
                ;(not (CLASS-DECL-interfacep (get-class-info CLASS-NAME CLASS-TABLE))) ;fixme
                (super-class-okayp class-name class-table))
           (not (class-decl-interfacep (get-class-info (class-decl-superclass (get-class-info class-name class-table)) class-table))))
  :hints (("Goal" :in-theory (enable super-class-okayp CLASS-TABLEP))))

(defthm super-class-okayp-when-bound-in-class-table
  (implies (and (class-tablep class-table)
                (not (equal "java.lang.Object" class-name))
                (bound-in-class-tablep class-name class-table))
           (super-class-okayp class-name class-table))
  :hints (("Goal" :in-theory (enable class-tablep bound-in-class-tablep))))

;; (defthm super-class-is-not-interface2
;;   (implies (and (class-tablep class-table)
;;                 (not (equal "java.lang.Object" class-name))
;;                 (bound-in-class-tablep class-name class-table))
;;            (not (class-decl-interfacep (get-class-info (class-decl-superclass (get-class-info class-name class-table)) class-table)))))

(defthm subset-of-get-super-classes-aux
  (implies (and (class-tablep class-table)
                (bound-in-class-tablep class-name class-table)
;                (not (class-decl-interfacep (get-class-info class-name class-table))) ;fixme?
                )
           (all-bound-in-class-tablep (get-super-classes-aux class-name class-table n) class-table))
  :hints (("Goal"
    ;          :expand ((BOUND-IN-CLASS-TABLEP CLASS-NAME CLASS-TABLE))
           :in-theory (e/d (get-super-classes-aux ;class-tablep ;class-decl-superclass
                            ;;    BOUND-IN-CLASS-TABLEP
                            ALL-SUPER-CLASSES-OKAYP
                            acl2::SUBSETP-EQ
                            ) (CLASS-DECL-SUPERCLASS)))))

(defthm object-bound-in-class-table
  (implies (class-tablep class-table)
           (bound-in-class-tablep "java.lang.Object" class-table))
  :hints (("Goal" :in-theory (enable class-tablep BOUND-IN-CLASS-TABLEP))))

;; (defthm super-class-bound-helper
;;   (implies (and (class-tablep class-table)
;;                 (not (equal "java.lang.Object" class-name))
;;                 (not (class-decl-interfacep (get-class-info class-name class-table))) ;fixme
;;                 (super-class-okayp class-name class-table))
;;            (bound-in-class-tablep (get-super-class class-name class-table) class-table))
;;   :hints (("Goal" :in-theory (enable super-class-okayp BOUND-IN-CLASS-TABLEP))))

;; (defthm super-class-bound-helper2
;;   (implies (and (class-tablep class-table)
;;                 (not (equal "java.lang.Object" class-name))
;; ;                (not (class-decl-interfacep (get-class-info class-name class-table))) ;fixme
;;                 (super-class-okayp class-name class-table))
;;            (bound-in-class-tablep (get-super-class class-name class-table) class-table))
;;   :hints (("Goal" :in-theory (enable get-super-class))))

;; (defthm super-class-bound
;;   (implies (and (class-tablep class-table)
;;                 (not (equal "java.lang.Object" class-name))
;;                 (bound-in-class-tablep CLASS-NAME CLASS-TABLE))
;;            (bound-in-class-tablep (get-super-class class-name class-table) class-table))
;;   :hints (("Goal" :in-theory (enable class-tablep))))

;; (defthm super-class-bound2
;;   (implies (and (class-tablep class-table)
;;                 (not (equal "java.lang.Object" class-name))
;;                 (bound-in-class-tablep CLASS-NAME CLASS-TABLE))
;;            (bound-in-class-tablep (get-super-class class-name class-table) class-table))
;;   :hints (("Goal" :in-theory (enable class-tablep))))

(defthm super-class-equal-none-1
  (implies (super-class-okayp class-name class-table)
           (equal (equal :none (get-super-class class-name class-table))
                  (equal "java.lang.Object" class-name)))
  :hints (("Goal" :in-theory (enable super-class-okayp  get-super-class))))

(defthm super-class-equal-none-2
  (implies (and (all-super-classes-okayp class-names class-table) ;class-names is a free var
                (memberp class-name class-names))
           (equal (equal :none (get-super-class class-name class-table))
                  (equal "java.lang.Object" class-name))))

(defthm super-class-equal-none-3
  (implies (and (class-tablep class-table)
                (bound-in-class-tablep class-name class-table))
           (equal (equal :none (get-super-class class-name class-table))
                  (equal "java.lang.Object" class-name)))
  :hints (("Goal" :in-theory (enable class-tablep bound-in-class-tablep))))

(defthm method-info-alistp-of-class-decl-methods-of-get-class-info
  (implies (and (class-tablep class-table)
                (bound-in-class-tablep CLASS-NAME CLASS-TABLE))
           (method-info-alistp (class-decl-methods (get-class-info class-name class-table))))
  :hints (("Goal" :use (:instance method-info-alistp-of-class-decl-methods (class-info (get-class-info class-name class-table)))
           :in-theory (e/d (class-tablep) (method-info-alistp-of-class-decl-methods)))))

;special case with no free var:
(defthm alistp-of-class-decl-methods-of-get-class-info
  (implies (class-infop (get-class-info class-name class-table) class-name)
           (alistp (class-decl-methods (get-class-info class-name class-table))))
  :hints (("Goal" :in-theory (disable alistp-of-class-decl-methods)
           :use (:instance alistp-of-class-decl-methods (class-info (get-class-info class-name class-table))))))

(defthm alistp-of-class-decl-methods-of-get-class-info-alt
  (implies (and (class-tablep class-table)
                (bound-in-class-tablep class-name class-table))
           (alistp (class-decl-methods (get-class-info class-name class-table))))
  :hints (("Goal" :in-theory (enable class-tablep))))

(defthm bound-in-class-tablep-when-bound-to-a-non-interfacep
  (implies (bound-to-a-non-interfacep class-name class-table)
           (bound-in-class-tablep class-name class-table))
  :hints (("Goal" :in-theory (enable bound-in-class-tablep BOUND-TO-A-NON-INTERFACEP))))

(defthm bound-in-class-tablep-of-s
  (implies class-info ;prove that a class-infop is always non-nil
           (equal (bound-in-class-tablep class-name (s class-name2 class-info class-table))
                  (if (equal class-name class-name2)
                      t
                    (bound-in-class-tablep class-name class-table))))
  :hints (("Goal" :in-theory (enable bound-in-class-tablep))))

;; ;fixme better way to recur down a record?
;; (defun acl2::initialize-class-table (term class-table-map)
;;   (if (endp class-table-map)
;;       term
;;     (let* ((entry (car class-table-map))
;;            (class-name (car entry))
;;            (class-info (cdr entry)))
;;       `(s ',class-name ',class-info ,(acl2::initialize-class-table term (cdr class-table-map))))))

;; (defmacro acl2::setup-class-table (var)
;;   `(acl2::initialize-class-table ,var (acl2::global-class-map state)))

;; to work around an issue with a free var
(defthm true-listp-of-class-decl-access-flags-of-get-class-info
  (implies (and (class-tablep class-table)
                (bound-in-class-tablep class-name class-table))
           (true-listp (class-decl-access-flags (get-class-info class-name class-table))))
  :hints (("Goal" :use (:instance true-listp-of-class-decl-access-flags (class-info (get-class-info class-name class-table)))
           :in-theory (disable true-listp-of-class-decl-access-flags))))

(defthm string-in-class-table
  (implies (class-tablep class-table)
           (bound-in-class-tablep "java.lang.String" class-table))
  :hints (("Goal" :in-theory (e/d (class-tablep bound-to-a-non-interfacep)
                                  ()))))

(defthm string-not-interface-in-class-table
  (implies (class-tablep class-table)
           (not (class-decl-interfacep (get-class-info "java.lang.String" class-table))))
  :hints (("Goal" :in-theory (e/d (class-tablep bound-to-a-non-interfacep)
                                  (true-listp-of-class-decl-access-flags-of-get-class-info))
           :use (:instance true-listp-of-class-decl-access-flags-of-get-class-info (class-name "java.lang.String")))))

(defthm all-bound-in-class-tablep-of-get-super-classes
  (implies (and (class-tablep class-table)
                (bound-in-class-tablep class-name class-table)
;                (not (class-decl-interfacep (get-class-info class-name class-table))) ;fixme?
                )
           (all-bound-in-class-tablep (acl2::get-super-classes class-name class-table) class-table)))

(defun bound-to-a-classp (class-or-interface-name class-table)
  (declare (xargs :guard (and (class-namep class-or-interface-name)
                              (class-tablep class-table)
                              (bound-in-class-tablep class-or-interface-name class-table))
                  :guard-hints (("Goal" :in-theory (enable class-tablep)))))
  (not (class-decl-interfacep (get-class-info class-or-interface-name class-table))))

;fixme call this more?
(defun bound-to-an-interfacep (class-or-interface-name class-table)
  (declare (xargs :guard (and (class-namep class-or-interface-name)
                              (class-tablep class-table)
                              (bound-in-class-tablep class-or-interface-name class-table))))
  (class-decl-interfacep (get-class-info class-or-interface-name class-table)))

;; ;gen?
;; ;delete?
;; (defthm ALL-CLASS-NAMESP-of-CLASS-DECL-INTERFACES-of-g-alt
;;   (implies (and (SET::IN C (ACL2::RKEYS CLASS-TABLE))
;;                 (CLASS-TABLEp class-table)
;;                 (CLASS-NAMEP C))
;;            (ALL-CLASS-NAMESP (CLASS-DECL-INTERFACES (get-class-info C CLASS-TABLE))))
;;   :hints (("Goal" :in-theory (e/d (CLASS-TABLEP) (all-class-namesp-of-class-decl-interfaces))
;;            :use (:instance all-class-namesp-of-class-decl-interfaces (class-name c) (class-info (get-class-info c class-table))))))

;; ;move
;; ;todo: compare to the other
;; (defthm all-class-namesp-of-class-decl-interfaces-of-g-alt2
;;   (implies (and (bound-in-class-tablep class-name class-table)
;;                 (class-tablep class-table))
;;            (all-class-namesp (class-decl-interfaces (get-class-info class-name class-table))))
;;   :hints (("Goal" :use (:instance ALL-CLASS-NAMESP-OF-CLASS-DECL-INTERFACES (class-info (get-class-info class-name class-table)))
;;            :in-theory (disable ALL-CLASS-NAMESP-OF-CLASS-DECL-INTERFACES))))

;; Note that JLS says "A class necessarily implements all the interfaces that
;; its direct superclasses and direct superinterfaces do" so we have to check
;; the superclasses and the superinterfaces.
(defun class-implements-interfacep (class-name interface-name class-table)
  (declare (xargs :guard (and (class-namep class-name)
                              (class-namep interface-name)
                              (class-tablep class-table)
                              (bound-in-class-tablep class-name class-table))))
  (let* ((super-class-names (acl2::get-super-classes class-name class-table))
         (implemented-interfaces (acl2::get-super-interfaces super-class-names class-table)))
    (if (member-equal interface-name implemented-interfaces)
        t
      nil)))



;;todo:
(defthm all-bound-to-a-non-interfacep-of-get-super-classes-aux-helper
  (implies (and ;(not (class-decl-interfacep (get-class-info class-name class-table)))
            (bound-in-class-tablep class-name class-table)
            (all-super-classes-okayp (SET::2LIST (ACL2::RKEYS CLASS-TABLE)) class-table)
            (member-equal class-name (SET::2LIST (ACL2::RKEYS CLASS-TABLE)))
            ;(class-namep class-name)
            (CLASS-TABLEP CLASS-TABLE))
           (all-bound-to-a-non-interfacep (get-super-classes-aux class-name class-table count) class-table))
  :hints (("Goal" :in-theory (e/d (GET-SUPER-CLASSES-AUX ALL-BOUND-TO-A-NON-INTERFACEP)
                                  ( ;ACL2::MEMBERP-OF-SET2LIST ;introduces set::in
                                   )))))

(defthm all-bound-to-a-non-interfacep-of-get-super-classes-aux
  (implies (and ;(not (class-decl-interfacep (get-class-info class-name class-table)))
            (bound-in-class-tablep class-name class-table)
            (class-tablep class-table)
     ;(class-namep class-name)
            )
           (all-bound-to-a-non-interfacep (get-super-classes-aux class-name class-table 1000000) class-table))
  :hints (("Goal" :in-theory (enable CLASS-TABLEP BOUND-IN-CLASS-TABLEP))))

(defthm class-namep-when-bound-in-class-tablep
  (implies (and (bound-in-class-tablep class-name class-table) ;; class-table is a free var
                (class-tablep0 class-table))
           (class-namep class-name))
  :hints (("Goal" :in-theory (enable bound-in-class-tablep class-tablep0))))


;; ;in case bound-in-class-tablep is opened up
;; (defthm class-namep-when-in-of-rkeys
;;   (implies (and (SET::IN class-name (ACL2::RKEYS CLASS-TABLE))
;;                 (class-tablep class-table))
;;            (class-namep class-name))
;;   :hints (("Goal" :in-theory (enable class-tablep))))

;move
;; (defthm not-bound-in-class-tablep-when-not-class-namep
;;   (implies (and (not (class-namep class-name))
;;                 (class-tablep class-table))
;;            (not (bound-in-class-tablep class-name class-table))))

;; The global-class-table maps class names to class-infops.
(defund acl2::global-class-alist (state)
  (declare (xargs :stobjs (state)))
  (table-alist 'acl2::global-class-table (w state)))
