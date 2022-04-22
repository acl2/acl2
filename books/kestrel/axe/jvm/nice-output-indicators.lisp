; Utilities supporting the lifter(s)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "output-indicators")
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))

;; todo: allow the param name to be deep in the structure, once the output-indicator stuff is cleaned up
(defun nice-output-indicatorp (x)
  (declare (xargs :guard t))
  (or (output-indicatorp x)
      (eq :rv x) ; "return value"
      ;; a param-name
      (and (symbolp x)
           (not (keywordp x)))))

(defund slot-to-parameter-type-alist-aux (slot parameter-types)
  (declare (xargs :guard (and (natp slot)
                              (true-listp parameter-types)
                              (jvm::all-typep parameter-types))
                  :verify-guards nil ; done below
                  ))
  (if (endp parameter-types)
      nil
    (acons slot (first parameter-types)
           (slot-to-parameter-type-alist-aux (+ slot (jvm::type-slot-count (first parameter-types)))
                                             (rest parameter-types)))))

(defthm alistp-of-slot-to-parameter-type-alist-aux
  (alistp (slot-to-parameter-type-alist-aux slot parameter-types))
  :hints (("Goal" :in-theory (enable slot-to-parameter-type-alist-aux))))

(verify-guards slot-to-parameter-type-alist-aux)

;; (slot-to-parameter-type-alist '(:int :int :long :short))
(defund slot-to-parameter-type-alist (parameter-types)
  (declare (xargs :guard (and (true-listp parameter-types)
                              (jvm::all-typep parameter-types))))
  (slot-to-parameter-type-alist-aux 0 parameter-types))

(defthm alistp-of-slot-to-parameter-type-alist
  (alistp (slot-to-parameter-type-alist parameter-types))
  :hints (("Goal" :in-theory (enable slot-to-parameter-type-alist))))

;; (desugar-nice-output-indicatorp 'y '((y . 4)) (list :int :int :long (jvm::make-array-type 1 :short)) :short)
(defun desugar-nice-output-indicatorp (x param-slot-to-name-alist parameter-types return-type)
  (declare (xargs :guard (and (nice-output-indicatorp x)
                              (true-listp parameter-types)
                              (jvm::all-typep parameter-types)
                              (alistp param-slot-to-name-alist))))
  (if (output-indicatorp x)
      x
    (if (eq :rv x)
        (if (eq :void return-type)
            (er hard? 'desugar-nice-output-indicatorp "Output indicator is :rv but method is void.")
          (if (jvm::primitive-typep return-type)
              (if (member-eq return-type jvm::*one-slot-types*)
                  :return-value
                :return-value-long)
            (if (jvm::array-typep return-type)
                :array-return-value
              (er hard? 'desugar-nice-output-indicatorp "Output indicator is :rv but method returns an object."))))
      ;; must be a param name:
      (let* ((res (rassoc-eq x param-slot-to-name-alist)))
        (if (not res)
            (er hard? 'desugar-nice-output-indicatorp "Can't find a slot for param ~x0." x)
          (let* ((param-slot (car res))
                 (slot-to-parameter-type-alist (slot-to-parameter-type-alist parameter-types))
                 (res (assoc-equal param-slot slot-to-parameter-type-alist)))
            (if (not res)
                (er hard? 'desugar-nice-output-indicatorp "Can't find a type for param ~x0 (slot ~x1)." x param-slot)
              (let ((type (cdr res)))
                (if (not (jvm::array-typep type))
                    (er hard? 'desugar-nice-output-indicatorp "Output indicator is ~x0 but that param is not an array." x)
                  `(:array-local ,param-slot))))))))))
