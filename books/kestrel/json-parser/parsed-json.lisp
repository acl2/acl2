; Recognizers for parsed JSON objects, arrays, and values
;
; Copyright (C) 2019-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also kestrel/json/abstract-syntax.lisp.

;; JSON arrays are represented as lists, tagged with :array.
;; JSON objects (maps) are represented as alists, tagged with :object.

(mutual-recursion
 ;; Recognize a parsed JSON array, of the form (:array <values>)
 (defund parsed-json-arrayp (val)
   (declare (xargs :guard t
                   :measure (make-ord 1 (+ 1 (acl2-count val)) 0)))
   (and (true-listp val)
        (= 2 (len val))
        (eq :array (car val))
        (parsed-json-valuesp (cadr val))))

 ;; Recognize a sequence of name/value pairs that appears in the parsed form of
 ;; a JSON object.
 (defund parsed-json-object-pairsp (val)
   (declare (xargs :guard t
                   :measure (make-ord 1 (+ 1 (acl2-count val)) 0)))
   (if (atom val)
       (null val)
     (let ((entry (first val)))
       (and (consp entry)
            (stringp (car entry))
            (parsed-json-valuep (cdr entry))
            (parsed-json-object-pairsp (rest val))))))

 ;; Recognize a parsed JSON object (in JSON parlance, an "object" is a map
 ;; from keys to values).
 (defund parsed-json-objectp (val)
   (declare (xargs :guard t
                   :measure (make-ord 1 (+ 1 (acl2-count val)) 0)))
   (and (true-listp val)
        (= 2 (len val))
        (eq :object (car val))
        (parsed-json-object-pairsp (cadr val))))

 ;; Recogize a true-list of parsed JSON values.
 (defund parsed-json-valuesp (vals)
   (declare (xargs :guard t
                   :measure (make-ord 1 (+ 1 (acl2-count vals)) 0)))
   (if (atom vals)
       (null vals)
     (and (parsed-json-valuep (first vals))
          (parsed-json-valuesp (rest vals)))))

 ;; Recogize a parsed JSON value (in JSON parlance, a "value" can be a scalar,
 ;; an array, or an object).
 (defund parsed-json-valuep (val)
   (declare (xargs :guard t
                   :measure (make-ord 1 (+ 1 (acl2-count val)) 1)))
   (or (if (member-eq val '(:true :false :null)) t nil) ; coerce to boolean
       (rationalp val)
       (stringp val)
       (parsed-json-arrayp val)
       (parsed-json-objectp val))))

(defthm parsed-json-object-pairsp-of-cons
  (equal (parsed-json-object-pairsp (cons pair pairs))
         (and (consp pair)
              (stringp (car pair))
              (parsed-json-valuep (cdr pair))
              (parsed-json-object-pairsp pairs)))
  :hints (("Goal" :in-theory (enable parsed-json-object-pairsp))))

(defthm parsed-json-object-pairsp-forward-to-alistp
  (implies (parsed-json-object-pairsp pairs)
           (alistp pairs))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable parsed-json-object-pairsp))))

(defthm string-listp-of-strip-cars-when-parsed-json-object-pairsp
  (implies (parsed-json-object-pairsp pairs)
           (string-listp (strip-cars pairs)))
  :hints (("Goal" :induct (len pairs)
           :in-theory (enable parsed-json-valuesp strip-cdrs))))

(defthm parsed-json-valuesp-of-strip-cdrs-when-parsed-json-object-pairsp
  (implies (parsed-json-object-pairsp pairs)
           (parsed-json-valuesp (strip-cdrs pairs)))
  :hints (("Goal" :induct (len pairs)
           :in-theory (enable parsed-json-valuesp strip-cdrs))))

(defthm parsed-json-valuesp-forward-to-true-listp
  (implies (parsed-json-valuesp values)
           (true-listp values))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable parsed-json-valuesp))))

(defthm parsed-json-object-pairsp-of-revappend
  (implies (and (parsed-json-object-pairsp x)
                (parsed-json-object-pairsp acc))
           (parsed-json-object-pairsp (revappend x acc)))
  :hints (("Goal" :in-theory (enable parsed-json-object-pairsp revappend))))

(defthm parsed-json-valuep-of-car-when-parsed-json-valuesp
  (implies (parsed-json-valuesp vals)
           (equal (parsed-json-valuep (car vals))
                  (consp vals)))
  :hints (("Goal" :in-theory (enable parsed-json-valuesp))))

(defthm parsed-json-valuesp-of-cdr
  (implies (parsed-json-valuesp array-vals)
           (parsed-json-valuesp (cdr array-vals)))
  :hints (("Goal" :in-theory (enable parsed-json-valuesp))))

(defthm parsed-json-valuesp-of-revappend
  (implies (and (parsed-json-valuesp x)
                (parsed-json-valuesp acc))
           (parsed-json-valuesp (revappend x acc)))
  :hints (("Goal" :in-theory (enable parsed-json-valuesp revappend))))

(defthmd parsed-json-valuesp-when-string-listp
  (implies (string-listp strings)
           (parsed-json-valuesp strings))
  :hints (("Goal" :in-theory (enable parsed-json-valuesp string-listp parsed-json-valuep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Access the values in a parsed-json-array
(defund parsed-json-array->values (array)
  (declare (xargs :guard (parsed-json-arrayp array)
                  :guard-hints (("Goal" :in-theory (enable parsed-json-arrayp)))))
  (cadr array) ; strip the :array
  )

(defthm parsed-json-valuesp-of-parsed-json-array->values
  (implies (parsed-json-arrayp array)
           (parsed-json-valuesp (parsed-json-array->values array)))
  :hints (("Goal" :in-theory (enable parsed-json-array->values
                                     parsed-json-arrayp))))

(defthm true-listp-of-parsed-json-array->values
  (implies (parsed-json-arrayp array)
           (true-listp (parsed-json-array->values array)))
  :hints (("Goal" :in-theory (enable parsed-json-array->values
                                     parsed-json-arrayp))))

(defthm <-of-acl2-count-of-parsed-json-array->values-linear
  (implies (parsed-json-arrayp val)
           (< (acl2-count (parsed-json-array->values val))
              (acl2-count val)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable parsed-json-array->values
                                     parsed-json-arrayp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Access the name/value pairs (an alist) in a parsed-json-object
(defund parsed-json-object->pairs (object)
  (declare (xargs :guard (parsed-json-objectp object)
                  :guard-hints (("Goal" :in-theory (enable parsed-json-objectp)))))
  (cadr object) ; strip the :object
  )

(defthm parsed-json-object-pairsp-of-parsed-json-object->pairs
  (implies (parsed-json-objectp object)
           (parsed-json-object-pairsp (parsed-json-object->pairs object)))
  :hints (("Goal" :in-theory (enable parsed-json-object->pairs
                                     parsed-json-objectp))))

(defthm alistp-of-parsed-json-object->pairs
  (implies (parsed-json-objectp object)
           (alistp (parsed-json-object->pairs object)))
  :hints (("Goal" :in-theory (enable parsed-json-object->pairs
                                     parsed-json-objectp))))

(defthm <-of-acl2-count-of-parsed-json-object->pairs-linear
  (implies (parsed-json-objectp val)
           (< (acl2-count (parsed-json-object->pairs val))
              (acl2-count val)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable parsed-json-object->pairs
                                     parsed-json-objectp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognize a list of parsed json-arrays.
(defun parsed-json-array-listp (x)
  (declare (xargs :guard t))
  (if (not (consp x))
      (null x)
    (and (parsed-json-arrayp (first x))
         (parsed-json-array-listp (rest x)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
