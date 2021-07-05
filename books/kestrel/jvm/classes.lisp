; Classes in the JV, including the class-info structure
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

;; This book deals with the class-table of the JVM.  These structures
;; are usually built up in the books created by the class-file-parser.

(include-book "methods")
;(include-book "kestrel/utilities/mydefconst" :dir :system) ;for the translated classes (TODO: have them include less?)
(include-book "kestrel/utilities/string-contains-charp" :dir :system)
(include-book "kestrel/utilities/string-utilities" :dir :system) ; for substring-before-last-occurrence
;(include-book "method-designator-strings") ;drop or reduce?
(include-book "kestrel/sequences/defforall" :dir :system)

;move
(defthm keyword-listp-forward-to-true-listp
  (implies (acl2::keyword-listp x)
           (true-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable acl2::keyword-listp))))

;FIXME Should each class correspond to a some "class object" in the
;heap?  When should those objects be created? Also, where should the
;mapping from classes to heap objects be stored?  I don't want it to
;be in the class-table, because I want that to be read-only.  Maybe it
;could be a special entry in the static-field-map?

;; ;could call this field-infosp ?
;; (defforall string-descriptor-pairsp (pair)
;;   (and (consp pair)
;;        (stringp (car pair))
;;        (descriptorp (cdr pair))))

;; (verify-guards string-descriptor-pairsp)

(defforall all-class-namesp (item) (class-namep item))
(verify-guards all-class-namesp)

(defforall all-field-idp (item) (field-idp item))
(verify-guards all-field-idp)

;; A method-id is a pair of two strings: a name and a descriptor.
(defun method-idp (item)
  (declare (xargs :guard t))
  (and (consp item)
       (method-namep (car item))
       (method-descriptorp (cdr item))))

(defund method-id-name (method-id)
  (declare (xargs :guard (method-idp method-id)))
  (car method-id))

(defthm method-namep-of-method-id-name
  (implies (method-idp method-id)
           (method-namep (method-id-name method-id)))
  :hints (("Goal" :in-theory (enable method-id-name method-idp))))

(defthm stringp-of-method-id-name
  (implies (method-idp method-id)
           (stringp (method-id-name method-id)))
  :hints (("Goal" :in-theory (enable method-id-name method-idp method-namep))))

(defund method-id-descriptor (method-id)
  (declare (xargs :guard (method-idp method-id)))
  (cdr method-id))

(defthm method-descriptorp-of-method-id-descriptor
  (implies (method-idp method-id)
           (method-descriptorp (method-id-descriptor method-id)))
  :hints (("Goal" :in-theory (enable method-id-descriptor method-idp))))

(defthm stringp-of-method-id-descriptor
  (implies (method-idp method-id)
           (stringp (method-id-descriptor method-id)))
  :hints (("Goal" :in-theory (enable method-id-descriptor method-idp method-descriptorp))))

(defund make-method-id (name desc)
  (declare (xargs :guard (and (method-namep name)
                              (method-descriptorp desc))))
  (cons name desc))

(defthm method-idp-of-make-method-id
  (equal (method-idp (make-method-id name desc))
         (and (method-namep name)
              (method-descriptorp desc)))
  :hints (("Goal" :in-theory (enable method-idp make-method-id))))

(defforall all-method-idp (item) (method-idp item))
(verify-guards all-method-idp)

(defun all-keys-bound-to-field-infosp (field-info-alist)
  (declare (xargs :guard (acl2::alistp field-info-alist)))
  (if (endp field-info-alist)
      t
    (let* ((entry (first field-info-alist))
           (field-info (cdr entry)))
      (and (field-infop field-info)
           (all-keys-bound-to-field-infosp (rest field-info-alist))))))

;an alist from field-ids to their field-infos
(defund field-info-alistp (field-info-alist)
  (declare (xargs :guard t))
  (and (acl2::alistp field-info-alist)
       (all-field-idp (acl2::strip-cars field-info-alist)) ;combine these steps?
       (all-keys-bound-to-field-infosp field-info-alist)))

(defthm field-info-alistp-forward-to-true-listp
  (implies (field-info-alistp item)
           (true-listp item))
  :rule-classes ((:forward-chaining))
  :hints (("Goal" :in-theory (enable field-info-alistp))))

(defthm field-info-alistp-of-cdr
  (implies (field-info-alistp item)
           (field-info-alistp (cdr item)))
  :hints (("Goal" :in-theory (enable field-info-alistp))))

(defthm field-infop-of-cdr-of-car
  (implies (and (field-info-alistp field-info-alist)
                (consp field-info-alist))
           (field-infop (cdr (car field-info-alist))))
  :hints (("Goal" :in-theory (enable field-info-alistp))))

(defthm field-idp-of-caar-when-field-info-alistp
  (implies (and (field-info-alistp field-info-alist)
                (consp field-info-alist))
           (field-idp (caar field-info-alist)))
  :hints (("Goal" :in-theory (enable field-info-alistp))))

(defthm consp-of-car-when-field-info-alistp
  (implies (field-info-alistp field-info-alist)
           (equal (consp (car field-info-alist))
                  (consp field-info-alist)))
  :hints (("Goal" :in-theory (enable field-info-alistp))))

(defun all-keys-bound-to-method-infosp (method-info-alist)
  (declare (xargs :guard (acl2::alistp method-info-alist)))
  (if (endp method-info-alist)
      t
    (let* ((entry (first method-info-alist))
           (method-info (cdr entry)))
      (and (method-infop method-info)
           (all-keys-bound-to-method-infosp (rest method-info-alist))))))

(defund method-info-alistp (method-info-alist)
  (declare (xargs :guard t))
  (and (acl2::alistp method-info-alist)
       (all-method-idp (acl2::strip-cars method-info-alist)) ;combine these steps?
       (all-keys-bound-to-method-infosp method-info-alist)))

(defthm method-info-alistp-forward-to-alistp
  (implies (method-info-alistp method-info-alist)
           (alistp method-info-alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable method-info-alistp))))

(defthm method-info-alistp-of-acons
  (equal (method-info-alistp (acons method-id method-info method-info-alist))
         (and (method-info-alistp method-info-alist)
              (method-idp method-id)
              (method-infop method-info)))
  :hints (("Goal" :in-theory (e/d (method-info-alistp)
                                  (METHOD-IDP)))))

;; The class-info structure:

;; A class-info structure contains the information for a single Java
;; class (or interface?).  The most interesting value in the
;; class-info is the :methods alist which associates method-ids
;; with method-info structures.

(defund class-infop0 (class-info)
  (declare (xargs :guard t))
  (and (alistp class-info)
       (equal (strip-cars class-info)
              '(:super-class :interfaces :access-flags :fields :static-fields :methods))
       (let ((super-class (acl2::lookup-eq :super-class class-info))
             (interfaces (acl2::lookup-eq :interfaces class-info))
             (access-flags (acl2::lookup-eq :access-flags class-info))
             (fields (acl2::lookup-eq :fields class-info))
             (static-fields (acl2::lookup-eq :static-fields class-info))
             (methods (acl2::lookup-eq :methods class-info)))
         (and (or (eq :none super-class)
                  (class-namep super-class))
              (true-listp interfaces)
              (all-class-namesp interfaces)
              (acl2::keyword-listp access-flags)
              (acl2::no-duplicatesp access-flags)
              (acl2::subsetp-eq access-flags '(:ACC_PUBLIC
                                               :ACC_FINAL
                                               :ACC_SUPER
                                               :ACC_INTERFACE
                                               :ACC_ABSTRACT
                                               :ACC_SYNTHETIC
                                               :ACC_ANNOTATION
                                               :ACC_ENUM))
              (field-info-alistp fields)
              (field-info-alistp static-fields)
              (method-info-alistp methods)))))

;This must take the class-name as an argument because java.lang.Object
;is treated specially (e.g., it has a superclass of :none).

;; TODO: rename class-or-interface-infop?
(defund class-infop (class-info class-name)
  (declare (xargs :guard (class-namep class-name)
                  :guard-hints (("Goal" :in-theory (enable class-infop0)))))
  (and
   (class-infop0 class-info)
   ;; Check the super class:
   (let ((super-class (acl2::lookup-eq :super-class class-info)))
     (if (equal class-name "java.lang.Object")
         (eq :none super-class)
       (if  (member-eq :acc_interface (acl2::lookup-eq :access-flags class-info))
           ;; The superclass of an interface is java.lang.Object (see JVMS: The ClassFile Structure)
           (equal "java.lang.Object" super-class)
         (class-namep super-class))))
   ;;... fixme add more tests
   ))

(defthm class-infop0-when-class-infop
  (implies (class-infop class-info class-name) ;free var
           (class-infop0 class-info))
  :hints (("Goal" :in-theory (enable class-infop))))

;;todo: should class-infop imply this?
;; (defthmd object-is-not-an-interface
;;   (implies (class-infop class-info "java.lang.Object")
;;            (not (class-decl-interfacep class-info)))
;;   :hints (("Goal" :in-theory (enable CLASS-INFOP))))

;fixme these apply to interfaces too, not just classes, despite their names
;fixme these should be macros?
;a list of the direct superinterfaces implemented by the class (i.e., a list of strings):
(defund class-decl-interfaces        (class-info) (declare (xargs :guard (class-infop0 class-info) :guard-hints (("Goal" :in-theory (enable CLASS-INFOP0))))) (acl2::lookup-eq :interfaces    class-info))
;just the name of the class (a string), or :none for java.lang.Object's superclass:
;fixme standardize whether super-class is hyphenated
(defund class-decl-superclass        (class-info) (declare (xargs :guard (class-infop0 class-info) :guard-hints (("Goal" :in-theory (enable CLASS-INFOP0))))) (acl2::lookup-eq :super-class   class-info))
(defund class-decl-non-static-fields (class-info) (declare (xargs :guard (class-infop0 class-info) :guard-hints (("Goal" :in-theory (enable CLASS-INFOP0))))) (acl2::lookup-eq :fields        class-info))
(defund class-decl-static-fields     (class-info) (declare (xargs :guard (class-infop0 class-info) :guard-hints (("Goal" :in-theory (enable CLASS-INFOP0))))) (acl2::lookup-eq :static-fields class-info))
;format?
(defund class-decl-methods           (class-info) (declare (xargs :guard (class-infop0 class-info) :guard-hints (("Goal" :in-theory (enable CLASS-INFOP0))))) (acl2::lookup-eq :methods       class-info))
(defund class-decl-access-flags      (class-info) (declare (xargs :guard (class-infop0 class-info) :guard-hints (("Goal" :in-theory (enable CLASS-INFOP0))))) (acl2::lookup-eq :access-flags  class-info))

(defund class-decl-interfacep (class-info)
  (declare (xargs :guard (class-infop0 class-info)
                  :guard-hints (("Goal" :in-theory (enable class-infop0)))))
  (member-eq :acc_interface (acl2::lookup-eq :access-flags class-info)))


;; A "normal" class is one that is not java.lang.Object
(defund normal-class-infop (class-info)
  (declare (xargs :guard t
                  :guard-hints (("Goal" :in-theory (enable class-infop0)))))
  (and
   (class-infop0 class-info)
   ;; the super-class is a class name (if there is a super-class):
   (let ((super-class (acl2::lookup-eq :super-class class-info)))
     (if (class-decl-interfacep class-info)
         ;; The superclass of an interface is java.lang.Object (see JVMS: The ClassFile Structure)
         (equal "java.lang.Object" super-class)
       (class-namep super-class)))
   ;;... fixme add more tests
   ))

(defthm class-infop-when-normal-class-infop
  (implies (and (normal-class-infop class-info)
                (not (equal "java.lang.Object" class-name)))
            (class-infop class-info class-name))
  :hints (("Goal" :in-theory (enable normal-class-infop class-infop class-decl-interfacep))))

(defthm normal-class-infop-forward-to-class-infop0
  (implies (normal-class-infop class-info)
           (class-infop0 class-info))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable normal-class-infop))))

(defthm class-infop-forward-to-consp
  (implies (class-infop class-info class-name)
           (consp class-info))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable class-infop))))

(defthm field-info-alistp-of-class-decl-non-static-fields
  (implies (class-infop class-info class-name) ;yuck: class-name is a free variable
           (field-info-alistp (class-decl-non-static-fields class-info)))
  :hints (("Goal" :in-theory (enable class-decl-non-static-fields class-infop class-infop0))))

(defthm field-info-alistp-of-class-decl-non-static-fields-2
  (implies (class-infop0 class-info)
           (field-info-alistp (class-decl-non-static-fields class-info)))
  :hints (("Goal" :in-theory (enable class-decl-non-static-fields class-infop class-infop0))))

(defthm field-info-alistp-of-class-decl-static-fields
  (implies (class-infop class-info class-name) ;yuck: class-name is a free variable
           (field-info-alistp (class-decl-static-fields class-info)))
  :hints (("Goal" :in-theory (enable class-decl-static-fields class-infop class-infop0))))

(defthm field-info-alistp-of-class-decl-static-fields-2
  (implies (class-infop0 class-info)
           (field-info-alistp (class-decl-static-fields class-info)))
  :hints (("Goal" :in-theory (enable class-decl-static-fields class-infop class-infop0))))

(defthm field-info-alistp-of-class-decl-static-fields-when-normal-class-infop
  (implies (normal-class-infop class-info)
           (field-info-alistp (class-decl-static-fields class-info)))
  :hints (("Goal" :in-theory (enable normal-class-infop class-infop0 CLASS-DECL-STATIC-FIELDS))))

;; ;This version (in the ACL2 package) is used in the translated class files (so that the package need not be in the portcullis):
;; (defmacro acl2::class-infop (class-info class-name)
;;   `(class-infop ,class-info ,class-name))

;this may be a good example of not using general purpose functions but rather special purpose versions
;rules about this function can be hung on get-field-ids rather than the general strip-cars
;and this will induce better (more specific) guard obligations when this is used...
(defund get-field-ids (field-info-alist)
  (declare (xargs :guard (field-info-alistp field-info-alist)
                  :guard-hints (("Goal" :in-theory (enable field-info-alistp)))))
  (strip-cars field-info-alist))

(defthm true-listp-of-class-decl-interfaces
  (implies (class-infop class-info class-name) ;darn class-name is a free var
           (true-listp (class-decl-interfaces class-info)))
  :hints (("Goal" :in-theory (enable class-infop class-infop0 class-decl-interfaces))))

(defthm all-class-namesp-of-class-decl-interfaces
  (implies (class-infop class-info class-name) ;darn class-name is a free var
           (all-class-namesp (class-decl-interfaces class-info)))
  :hints (("Goal" :in-theory (enable class-infop class-infop0 class-decl-interfaces))))

(defthm class-namep-of-class-decl-superclass
  (implies (and (class-infop class-info class-name)
                (not (equal class-name "java.lang.Object"))
                ;; (not (class-decl-interfacep class-info))
                )
           (class-namep (class-decl-superclass class-info)))
  :hints (("Goal" :in-theory (enable class-infop class-infop0 class-decl-superclass))))

(defthm true-listp-of-class-decl-access-flags
  (implies (class-infop class-info class-name)
           (true-listp (class-decl-access-flags class-info)))
  :hints (("Goal" :in-theory (enable class-infop class-infop0 class-decl-access-flags))))

(defun make-class-info (super-class interfaces non-static-field-info-alist static-field-info-alist method-info-alist access-flags)
  (declare (xargs :guard t)) ;todo: strengthen?
  (acons :super-class super-class
         (acons :interfaces interfaces
                (acons :access-flags access-flags
                       (acons :fields non-static-field-info-alist
                              (acons :static-fields static-field-info-alist
                                     (acons :methods method-info-alist
                                            nil)))))))

(defthm class-infop-of-make-class-info
  (implies (and (acl2::keyword-listp access-flags)
                (acl2::no-duplicatesp access-flags)
                (acl2::subsetp-eq access-flags '(:ACC_PUBLIC
                                                 :ACC_FINAL
                                                 :ACC_SUPER
                                                 :ACC_INTERFACE
                                                 :ACC_ABSTRACT
                                                 :ACC_SYNTHETIC
                                                 :ACC_ANNOTATION
                                                 :ACC_ENUM))
                (true-listp interfaces)
                (all-class-namesp interfaces)
                (field-info-alistp static-field-info-alist)
                (field-info-alistp non-static-field-info-alist)
                (method-info-alistp method-info-alist)
                (implies (equal "java.lang.Object" class-name)
                         (equal :none super-class))
                (implies (member-equal :acc_interface access-flags)
                         (equal "java.lang.Object" super-class))
                (implies (and (not (member-equal :acc_interface access-flags))
                              (not (equal "java.lang.Object" class-name)))
                         (class-namep super-class)))
           (class-infop (make-class-info super-class interfaces non-static-field-info-alist static-field-info-alist method-info-alist access-flags)
                        class-name))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable class-infop
                              class-infop0
                              class-decl-access-flags
                              class-decl-static-fields
                              class-decl-non-static-fields
                              class-decl-methods
                              class-decl-interfaces
                              class-decl-superclass))))

(defun empty-class ()
  (make-class-info "java.lang.Object" nil nil nil nil
                   nil ;todo: may need at least one access flag?
                   ))

(defthm class-infop-of-empty-class
  (implies (and (class-namep class-name)
                (not (equal "java.lang.Object" class-name)))
           (class-infop (empty-class) class-name))
  :hints (("Goal" :in-theory (enable class-infop))))

;move
(defthm method-info-alistp-of-class-decl-methods
  (implies (class-infop class-info class-name) ;class-name is a free-var
           (method-info-alistp (class-decl-methods class-info)))
  :hints (("Goal" :in-theory (enable class-infop class-infop0 class-decl-methods))))

(defthm alistp-of-class-decl-methods
  (implies (class-infop class-info class-name) ;class-name is a free var
           (alistp (class-decl-methods class-info)))
  :hints (("Goal" :in-theory (enable class-infop class-infop0 method-info-alistp class-decl-methods))))

;move?
;; Returns a string or :unnamed-package
(defun extract-package-name-from-class-name (class-name)
  (declare (xargs :guard (class-namep class-name)))
  (if (acl2::string-contains-charp class-name #\.)
      (acl2::substring-before-last-occurrence class-name #\.)
    :unnamed-package))

(defthm not-class-infop-of-nil
  (not (class-infop nil class-name))
  :hints (("Goal" :in-theory (enable class-infop))))
