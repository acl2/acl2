; Fields (names, ids, attributes, etc) and the field-info structure
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

(include-book "types")
(include-book "kestrel/alists-light/lookup-eq" :dir :system)

(local
 (defthm keyword-listp-forward-to-true-listp
   (implies (acl2::keyword-listp x)
            (true-listp x))
   :hints (("Goal" :in-theory (enable acl2::keyword-listp)))))

(local
 (defthm keyword-listp-forward-to-eqlable-listp
   (implies (acl2::keyword-listp x)
            (eqlable-listp x))
   :hints (("Goal" :in-theory (enable acl2::keyword-listp)))))

;; The name of a field is a string.
(defund field-namep (name)
  (declare (xargs :guard t))
  (stringp name))

(defthm field-namep-forward-to-stringp
  (implies (field-namep name)
           (stringp name))
  :rule-classes :forward-chaining)

;; A field-id contains the field name and its type (a parsed descriptor).
(defund field-idp (item)
  (declare (xargs :guard t))
  (and (consp item)
       (field-namep (car item))
       (typep (cdr item))))

(defund make-field-id (field-name type)
  (declare (xargs :guard (and (field-namep field-name)
                              (typep type))))
  (cons field-name type))

(defthm field-idp-of-make-field-id
  (implies (and (field-namep field-name)
                (typep type))
           (field-idp (make-field-id field-name type)))
  :hints (("Goal" :in-theory (enable field-idp make-field-id))))

;; Extract the name from a field-id.  This is just car but note the guard.
(defund field-id-name (field-id)
  (declare (xargs :guard (field-idp field-id)
                  :guard-hints (("Goal" :in-theory (enable field-idp)))))
  (car field-id))

;; Extract the type from a field-id.  This is just cdr but note the guard.
(defund field-id-type (field-id)
  (declare (xargs :guard (field-idp field-id)
                  :guard-hints (("Goal" :in-theory (enable field-idp)))))
  (cdr field-id))

;;;
;;; the field-info structure
;;;

;really, this can contain duplicate bindings for the same key?!
(defund attributesp (attributes)
  (declare (xargs :guard t))
  (alistp attributes))

(defun get-ConstantValue-attribute (attributes)
  (declare (xargs :guard (attributesp attributes)))
  (acl2::lookup-equal "ConstantValue" attributes))

;;These are the only keys allowed in the field-info alist:
(defconst *field-info-keys*
  '(:access-flags :attributes))

;an alist specifying various properties about a field
(defund field-infop (field-info)
  (declare (xargs :guard t))
  (and (alistp field-info)
       (acl2::subsetp-eq (strip-cars field-info) *field-info-keys*)
       (attributesp (acl2::lookup-eq :attributes field-info))
       (let ((access-flags (acl2::lookup-eq :access-flags field-info)))
         (and (acl2::keyword-listp access-flags)
              (acl2::no-duplicatesp access-flags)
              (acl2::subsetp-eq access-flags
                                '(:ACC_PUBLIC
                                  :ACC_PRIVATE
                                  :ACC_PROTECTED
                                  :ACC_STATIC
                                  :ACC_FINAL
                                  :ACC_VOLATILE
                                  :ACC_TRANSIENT
                                  :ACC_SYNTHETIC
                                  :ACC_ENUM))))))

(defthm field-infop-forward-to-true-listp
  (implies (field-infop field-info)
           (true-listp field-info))
  :rule-classes ((:forward-chaining))
  :hints (("Goal" :in-theory (enable field-infop))))

(defthm field-infop-forward-to-alistp
  (implies (field-infop field-info)
           (alistp field-info))
  :rule-classes ((:forward-chaining))
  :hints (("Goal" :in-theory (enable field-infop))))

(defund field-attributes (field-info)
  (declare (xargs :guard (field-infop field-info)))
  (acl2::lookup-eq :attributes field-info))

(defthm attributesp-of-field-attributes
  (implies (field-infop field-info)
           (attributesp (field-attributes field-info)))
  :hints (("Goal" :in-theory (enable field-infop field-attributes))))

(defund field-access-flags (field-info)
  (declare (xargs :guard (field-infop field-info)))
  (acl2::lookup-eq :access-flags field-info))

(defthm true-listp-of-field-access-flags-forward
  (implies (field-infop field-info)
           (true-listp (field-access-flags field-info)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable field-infop field-access-flags))))

(defund field-publicp (field-info)
  (declare (xargs :guard (field-infop field-info)))
  (acl2::member-eq :acc_public (field-access-flags field-info)))

(defund field-privatep (field-info)
  (declare (xargs :guard (field-infop field-info)))
  (acl2::member-eq :acc_private (field-access-flags field-info)))

(defund field-protectedp (field-info)
  (declare (xargs :guard (field-infop field-info)))
  (acl2::member-eq :acc_protected (field-access-flags field-info)))

(defund field-staticp (field-info)
  (declare (xargs :guard (field-infop field-info)))
  (acl2::member-eq :acc_static (field-access-flags field-info)))
