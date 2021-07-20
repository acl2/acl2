; Creating ACL2 events to represent a Java classs
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "classes")

(defun class-info-constant-name (class-name  ;fully qualified?
                                 )
  (declare (xargs :guard (jvm::class-namep class-name)))
  (packn (list '* class-name '-class-info*)))

;; Returns a list events that load and register the given class.
(defun events-to-load-class (class-name class-info)
  (declare (xargs :guard (and (jvm::class-namep class-name)
                              ;(jvm::class-infop class-info class-name)
                              (jvm::class-infop0 class-info))))
  (let ((class-info-constant-name (class-info-constant-name class-name)))
    `((mydefconst ,class-info-constant-name ',class-info)

      ;; Register the class in the global-class-table (used in lifting):
      (table global-class-table ,class-name ,class-info-constant-name))))

;; Returns a list of event forms.
(defun events-for-class (class-name
                         class-info
                         field-defconsts ; do we always want these?
                         )
  (declare (xargs :guard (and (jvm::class-namep class-name)
                              (jvm::class-infop0 class-info)
                              (true-listp field-defconsts))))
  (append field-defconsts ;;TODO: Do we always want these?
          ;; method-defconsts ;(defconsts-for-methods raw-method-infos class-name)
          ;;          ;; we are associating each class with an object in the heap,
          ;;          ;; whose class is java.lang.Class, and which has fields for the static fields of the class.
          ;;          (equal (get-class (heapref-for-class ,class-name s)
          ;;                            (jvm::heap s))
          ;;                 "java.lang.Class")
          (events-to-load-class class-name class-info)))


;; ;; Returns a list of event forms.
;; (defun parsed-class-events (;class-name ;fully qualified?
;;                             raw-parsed-class)
;;   (declare (xargs :guard (and ;(stringp class-name)
;;                               (raw-parsed-classp raw-parsed-class))))
;;   (b* (((mv class-info field-defconsts) (make-class-info-from-raw-parsed-class raw-parsed-class))
;;        (class-name (acl2::lookup-eq :this_class raw-parsed-class)))
;;     (if nil ;(not (jvm::class-infop class-info class-name)) ;todo: drop this check
;;         ;; Should not happen:
;;         nil ;(er hard? 'parsed-class-events "Error: Invalid class-info created for ~x0: ~X12" class-name class-info nil)

;;       (append field-defconsts ;;TODO: Do we always want these?
;;               ;; method-defconsts ;(defconsts-for-methods raw-method-infos class-name)
;;               ;;          ;; we are associating each class with an object in the heap,
;;               ;;          ;; whose class is java.lang.Class, and which has fields for the static fields of the class.
;;               ;;          (equal (get-class (heapref-for-class ,class-name s)
;;               ;;                            (jvm::heap s))
;;               ;;                 "java.lang.Class")
;;               (events-to-load-class class-name class-info)))))
