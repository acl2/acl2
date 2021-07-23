; Supporting tools for x86 lifters
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X86ISA") ;todo: use X package

(include-book "kestrel/axe/util2" :dir :system) ;for make-cons-nest
(include-book "kestrel/alists-light/lookup-equal" :dir :system)

(mutual-recursion
 (defun normal-output-indicatorp (x)
   (declare (xargs :guard t))
   (or (and (true-listp x) ;; (:register <N>)
            (eq (first x) :register)
            (eql 2 (len x))
            (natp (second x)) ;todo: what is the max allowed?
            )
       ;; TODO: Add other sizes of :memXXX
       (and (true-listp x) ;; (:mem32 <ADDR-TERM>)
            (eq (first x) :mem32)
            (eql 2 (len x))
            (pseudo-termp (second x)); argument should be a term (should we translate it)
            )
       (and (true-listp x)
            (eq (first x) :tuple)
            (normal-output-indicatorsp (rest x)))))
 (defun normal-output-indicatorsp (x)
   (declare (xargs :guard t))
   (if (atom x)
       (null x)
     (and (normal-output-indicatorp (first x))
          (normal-output-indicatorsp (rest x))))))

(defun x::output-indicatorp (x)
  (declare (xargs :guard t))
  (or (eq x :all)
      (normal-output-indicatorp x)))

(mutual-recursion
 (defun wrap-in-normal-output-extractor (output-indicator term-to-simulate)
   (declare (xargs :guard (normal-output-indicatorp output-indicator)))
   (if (and (consp output-indicator)
            (eq :register (first output-indicator)))
       `(xr ':rgf ',(second output-indicator) ,term-to-simulate)
     (if (and (consp output-indicator)
              (eq :mem32 (first output-indicator)))
         `(x::read '4 ,(second output-indicator) ,term-to-simulate)
       (if (and (consp output-indicator)
                (eq :tuple (first output-indicator)))
           (acl2::make-cons-nest (wrap-in-normal-output-extractors (rest output-indicator) term-to-simulate))
         (er hard 'wrap-in-output-extractor "Invalid output indicator: ~x0" output-indicator)))))

 (defun wrap-in-normal-output-extractors (output-indicators term-to-simulate)
   (declare (xargs :guard (normal-output-indicatorsp output-indicators)))
   (if (endp output-indicators)
       nil
     (cons (wrap-in-normal-output-extractor (first output-indicators) term-to-simulate)
           (wrap-in-normal-output-extractors (rest output-indicators) term-to-simulate)))))

(defun x::wrap-in-output-extractor (output-indicator term-to-simulate)
  (declare (xargs :guard (x::output-indicatorp output-indicator)))
  (if (eq :all output-indicator)
      term-to-simulate
    (wrap-in-normal-output-extractor output-indicator term-to-simulate)))

(defun x::get-x86-lifter-table (state)
  (declare (xargs :stobjs state))
  (table-alist 'x86-lifter-table (w state)))

;TODO: Use the generic utility for redundancy checking
;WHOLE-FORM is a call to the lifter
(defun x::previous-lifter-result (whole-form state)
  (declare (xargs :stobjs state))
  (let* ((table-alist (x::get-x86-lifter-table state)))
    (if (not (alistp table-alist))
        (hard-error 'x::previous-lifter-result "Invalid table alist for x86-lifter-table: ~x0."
                    (acons #\0 table-alist nil))
      (let ((previous-result (acl2::lookup-equal whole-form table-alist)))
        (if previous-result
            (prog2$ (cw "NOTE: The call to the lifter ~x0 is redundant.~%" whole-form)
                    previous-result)
          nil)))))
