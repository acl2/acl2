; Recognizers for parsed JSON objects, arrays, and values
;
; Copyright (C) 2019-2022 Kestrel Institute
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
 ;; Recognize the parsed form of a JSON array
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
   (or (member-eq val '(:true :false :null))
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

(defthm parsed-json-object-pairsp-of-revappend
  (implies (and (parsed-json-object-pairsp x)
                (parsed-json-object-pairsp acc))
           (parsed-json-object-pairsp (revappend x acc)))
  :hints (("Goal" :in-theory (enable parsed-json-object-pairsp revappend))))

(defthm parsed-json-valuesp-of-revappend
  (implies (and (parsed-json-valuesp x)
                (parsed-json-valuesp acc))
           (parsed-json-valuesp (revappend x acc)))
  :hints (("Goal" :in-theory (enable parsed-json-valuesp revappend))))
