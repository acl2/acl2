; The string intern-table of the JVM
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

;; Support for establishing that the intern-table only contains addresses of String objects

(include-book "classes")
(include-book "heap")

(local (in-theory (disable strip-cdrs))) ;make unlocal?

;; The intern table maps strings to their corresponding heap objects:

;see also the version in android/layouts
(defun all-stringp (x)
  (declare (xargs :guard t))
  (if (atom x)
      t
      (and (stringp (first x))
           (all-stringp (rest x)))))

;todo: optimize this to make a single pass?:
(defund intern-tablep (intern-table)
  (declare (xargs :guard t))
  (and (alistp intern-table)
       (all-stringp (strip-cars intern-table))
       (acl2::all-addressp (strip-cdrs intern-table)) ;;the elements are addresses (intern-table-okp requires them to be addresses of string objects)
       ))

(defund empty-intern-table ()
  (declare (xargs :guard t))
  nil ;an empty alist
  )

(defthm intern-tablep-of-empty-intern-table
  (intern-tablep (empty-intern-table)))

;; Check that all addresses to which strings are bound in the intern table are
;; in fact addresses of string objects.
(defund intern-table-okp (intern-table heap)
  (declare (xargs :guard (and (intern-tablep intern-table)
                              (heapp heap))
                  :guard-hints (("Goal" :in-theory (enable intern-tablep strip-cdrs)))))
  (if (endp intern-table)
      t
    (let* ((entry (first intern-table))
           (address (cdr entry)))
      (and (equal "java.lang.String" (acl2::get-class address heap))
           (intern-table-okp (rest intern-table) heap)))))

(defthm intern-table-okp-of-set-field-irrel-pair
  (implies (not (equal pair (acl2::class-pair)))
           (equal (intern-table-okp intern-table (acl2::set-field ad pair val heap))
                  (intern-table-okp intern-table heap)))
  :hints (("Goal" :in-theory (enable intern-table-okp))))

;I think this can be useful in some cases
(defthm intern-table-okp-of-set-field-irrel-pair-alt
  (implies (or (not (equal (car pair) :special-data))
               (not (equal (cdr pair) :class)))
           (equal (intern-table-okp intern-table (acl2::set-field ad pair val heap))
                  (intern-table-okp intern-table heap)))
  :hints (("Goal" :in-theory (enable intern-table-okp))))

(defthm intern-table-okp-of-set-field-irrel-ad
  (implies (not (member-equal ad (strip-cdrs intern-table)))
           (equal (intern-table-okp intern-table (acl2::set-field ad pair val heap))
                  (intern-table-okp intern-table heap)))
  :hints (("Goal" :in-theory (enable intern-table-okp strip-cdrs))))

;drop?
(defthm intern-table-okp-of-set-field-irrel-when-bound
  (implies (and (intern-table-okp intern-table heap2)
                (not (set::in ad (acl2::rkeys heap2))))
           (equal (intern-table-okp intern-table (acl2::set-field ad pair val heap))
                  (intern-table-okp intern-table heap)))
  :hints (("Goal" :in-theory (enable intern-table-okp acl2::get-class))))

(defthm intern-table-okp-of-set-field-irrel-when-bound-same-heap
  (implies (and (intern-table-okp intern-table heap)
                (not (set::in ad (acl2::rkeys heap))))
           (equal (intern-table-okp intern-table (acl2::set-field ad pair val heap))
                  (intern-table-okp intern-table heap))))

;; Setting some field of some object to "java.lang.String" can only make the intern table more correct
(defthm intern-table-okp-of-set-field-2
  (implies (intern-table-okp intern-table heap)
           (intern-table-okp intern-table (acl2::set-field ad pair "java.lang.String" heap)))
  :hints (("Goal" :in-theory (enable intern-table-okp))))

;really this is true for any f, not just cdr
(defthm not-equal-constant-when-cdr-wrong
  (implies (and (syntaxp (quotep k))
                (not (equal (cdr x) free))
                (syntaxp (quotep free))
                (equal free (cdr k)))
           (not (equal x k))))

;really this is true for any f, not just car
(defthm not-equal-constant-when-car-wrong
  (implies (and (syntaxp (quotep k))
                (not (equal (car x) free))
                (syntaxp (quotep free))
                (equal free (car k)))
           (not (equal x k))))

(defthm intern-table-okp-of-set-fields-irrel-bindings
  (implies (not (member-equal '(:special-data . :class) (strip-cars bindings)))
           (equal (intern-table-okp intern-table (acl2::set-fields ad bindings heap))
                  (intern-table-okp intern-table heap)))
  :hints (("Goal" :in-theory (e/d (acl2::set-fields strip-cdrs)
                                  (intern-table-okp)))))

(defthm intern-table-okp-of-set-fields-irrel-ad
  (implies (not (member-equal ad (strip-cdrs intern-table)))
           (equal (intern-table-okp intern-table (acl2::set-fields ad bindings heap))
                  (intern-table-okp intern-table heap)))
  :hints (("Goal" :in-theory (enable ACL2::SET-FIELDS))))

(defthm intern-table-okp-of-set-fields-irrel-when-bound
  (implies (and (intern-table-okp intern-table heap2)
                (not (set::in ad (acl2::rkeys heap2))))
           (equal (intern-table-okp intern-table (acl2::set-fields ad bindings heap))
                  (intern-table-okp intern-table heap))))

(defthm intern-table-okp-of-set-fields-irrel-when-bound-same-heap
  (implies (and (intern-table-okp intern-table heap)
                (not (set::in ad (acl2::rkeys heap))))
           (equal (intern-table-okp intern-table (acl2::set-fields ad bindings heap))
                  (intern-table-okp intern-table heap))))

(defun string-has-been-internedp (string intern-table)
  (declare (xargs :guard (and (stringp string)
                              (intern-tablep intern-table))
                  :guard-hints (("Goal" :in-theory (enable INTERN-TABLEP)))))
  (let* ((looked-up-string (acl2::lookup-equal string intern-table)) ;will be a heap reference (a natural) or nil if the string isn't in the table
         )
    (not (equal looked-up-string nil))))

(defthm booleanp-of-string-has-been-internedp
  (booleanp (string-has-been-internedp string intern-table)))

;; (defthm string-has-been-internedp-of-nil
;;   (equal (string-has-been-internedp string nil)
;;          nil))

(defthm string-has-been-internedp-of-empty-intern-table
  (equal (string-has-been-internedp string (empty-intern-table))
         nil))

;assumes that the string has been interned??
;returns a heap address, or nil if the string isn't in the intern table
(defun get-interned-string (string intern-table)
  (declare (xargs :guard (and (stringp string)
                              (intern-tablep intern-table))
                  :guard-hints (("Goal" :in-theory (enable INTERN-TABLEP)))))
  (let* ((looked-up-string (acl2::lookup-equal string intern-table)))
    looked-up-string))

;; (defthm get-interned-string-of-nil
;;   (equal (get-interned-string string nil)
;;          nil))

(defthm get-interned-string-of-empty-intern-table
  (equal (get-interned-string string (empty-intern-table))
         nil))

(defun set-interned-string (string ad intern-table)
  (declare (xargs :guard (and (stringp string)
                              (addressp ad)
                              (intern-tablep intern-table))
                  :guard-hints (("Goal" :in-theory (enable INTERN-TABLEP)))))
  (acons string ad intern-table))

(defthm get-interned-string-of-set-interned-string-same
  (equal (get-interned-string string (set-interned-string string ad intern-table))
         ad))

(defthm string-has-been-internedp-of-set-interned-string-same
  (equal (string-has-been-internedp string (set-interned-string string ad intern-table))
         (not (equal nil ad))))

(defthm string-has-been-internedp-of-set-interned-string-diff
  (implies (not (equal string1 string2))
           (equal (string-has-been-internedp string1 (set-interned-string string2 ad intern-table))
                  (string-has-been-internedp string1 intern-table))))

(defthm not-memberp-of-strip-cdrs-when-intern-table-okp
  (implies (and (intern-table-okp intern-table heap)
                (not (set::in ad (acl2::rkeys heap))))
           (not (memberp ad (strip-cdrs intern-table))))
  :hints (("Goal" :in-theory (enable acl2::get-class ;todo
                                     intern-table-okp
                                     strip-cdrs))))

(defthm intern-table-okp-of-init-ref-in-heap
  (implies (and (intern-tablep intern-table)
                (intern-table-okp intern-table heap)
                (not (set::in ad (acl2::rkeys heap)))
                )
           (equal (intern-table-okp intern-table (acl2::init-ref-in-heap ad class-name class-table heap))
                  (intern-table-okp intern-table heap)))
  :hints (("Goal" :in-theory (enable ACL2::INIT-REF-IN-HEAP))))

;; (defthm intern-table-okp-of-init-ref-in-heap-2
;;   (implies (and (intern-tablep intern-table)
;;                 (intern-table-okp intern-table heap)
;; ;(not (set::in ad (acl2::rkeys heap)))
;;                 )
;;            (implies (intern-table-okp intern-table heap)
;;                     (intern-table-okp intern-table (acl2::init-ref-in-heap ad "java.lang.String" class-table heap))))
;;   :hints (("Goal" :in-theory (enable ACL2::INIT-REF-IN-HEAP))))

;TODO: maybe rename string-has-been-internedp?  does not really mean it's been interned..

;; (defthm assoc-equal-when-not-consp
;;   (implies (not (consp alist))
;;            (equal (assoc-equal key alist)
;;                   nil))
;;   :hints (("Goal" :in-theory (enable assoc-equal))))

;; (defthm lookup-equal-when-not-consp
;;   (implies (not (consp alist))
;;            (equal (acl2::lookup-equal key alist)
;;                   nil))
;;   :hints (("Goal" :in-theory (enable acl2::lookup-equal))))

;drop, if we keep get-class diabled?
(defthm get-field-of-get-interned-string-and-class-pair
  (implies (and (string-has-been-internedp string intern-table)
                (intern-table-okp intern-table heap))
           (equal (acl2::get-field (get-interned-string string intern-table) '(:special-data . :class) heap)
                  "java.lang.String"))
  :hints (("Goal" :in-theory (enable acl2::lookup-equal intern-table-okp intern-table-okp acl2::get-class))))

(defthm intern-table-okp-of-acons
  (implies (and (jvm::intern-table-okp intern-table heap)
                (equal (acl2::get-field ad '(:special-data . :class) heap)
                       "java.lang.String"))
           (jvm::intern-table-okp (acons string ad intern-table) heap))
  :hints (("Goal" :in-theory (enable jvm::intern-table-okp acl2::get-class))))

(defthm not-member-equal-of-new-ad-of-rkeys-and-strip-cdrs-when-intern-table-okp
  (implies (jvm::intern-table-okp intern-table heap)
           (not (member-equal (acl2::new-ad (acl2::rkeys heap)) (acl2::strip-cdrs intern-table)))))

(defthm not-null-refp-of-get-interned-string
  (implies (jvm::intern-tablep intern-table)
           (not (null-refp (jvm::get-interned-string string intern-table))))
  :hints (("Goal" :in-theory (enable jvm::intern-tablep strip-cdrs))))
