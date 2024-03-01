; Supporting tools for x86 lifters
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "kestrel/utilities/make-cons-nest" :dir :system)
(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "kestrel/bv/bvchop-def" :dir :system) ; mentioned below

(mutual-recursion
 (defun normal-output-indicatorp (x)
   (declare (xargs :guard t))
   (or ;; TODO: Deprecate this case:
    (member-equal x '(:rax
                      :eax
                      ;; todo: more
                      :zmm0 :ymm0 :xmm0
                      ))
       (and (true-listp x) ;; (:register <N>) or (:register-bool <N>)
            (member-eq (first x) '(:register :register-bool))
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

;; Indicates the desired result of lifting, either :all or some component of the state
(defun output-indicatorp (x)
  (declare (xargs :guard t))
  (or (eq x :all)
      (normal-output-indicatorp x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(mutual-recursion
 (defun wrap-in-normal-output-extractor (output-indicator term)
   (declare (xargs :guard (normal-output-indicatorp output-indicator)))
   (if (symbolp output-indicator)
       (case output-indicator
         (:rax `(bvchop '64 (rax ,term)))
         (:eax `(bvchop '32 (xr ':rgf '0 ,term))) ; for now, or do something different depending on 32/64 bit mode since eax is not really well supported in 32-bit mode?
         ;; (:eax (rax ,term))
         (:zmm0 `(xr ':zmm '0 ,term)) ; seems to already be unsigned
         (:ymm0 `(bvchop '256 (xr ':zmm '0 ,term)))
         (:xmm0 `(bvchop '128 (xr ':zmm '0 ,term)))
         (t (er hard 'wrap-in-normal-output-extractor "Unsupported output-indicator: ~x0." output-indicator)))
     (if (and (consp output-indicator)
              (eq :register (first output-indicator)))
         `(xr ':rgf ',(second output-indicator) ,term)
       (if (and (consp output-indicator)
                (eq :register-bool (first output-indicator)))
         ;; On Linux with gcc, a C function that returns a boolean has been observed to only set the low byte of RAX
         ;; TODO: Should we chop to a single bit?
           `(acl2::bvchop '8 (xr ':rgf ',(second output-indicator) ,term))
         (if (and (consp output-indicator)
                  (eq :mem32 (first output-indicator)))
             `(read '4 ,(second output-indicator) ,term)
           (if (and (consp output-indicator)
                    (eq :tuple (first output-indicator)))
               (acl2::make-cons-nest (wrap-in-normal-output-extractors (rest output-indicator) term))
             (er hard 'wrap-in-output-extractor "Invalid output indicator: ~x0" output-indicator)))))))

 (defun wrap-in-normal-output-extractors (output-indicators term)
   (declare (xargs :guard (normal-output-indicatorsp output-indicators)))
   (if (endp output-indicators)
       nil
     (cons (wrap-in-normal-output-extractor (first output-indicators) term)
           (wrap-in-normal-output-extractors (rest output-indicators) term)))))

(defun wrap-in-output-extractor (output-indicator term)
  (declare (xargs :guard (output-indicatorp output-indicator)))
  (if (eq :all output-indicator)
      term
    (wrap-in-normal-output-extractor output-indicator term)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun get-x86-lifter-table (state)
  (declare (xargs :stobjs state))
  (table-alist 'x86-lifter-table (w state)))

;TODO: Use the generic utility for redundancy checking
;WHOLE-FORM is a call to the lifter
(defun previous-lifter-result (whole-form state)
  (declare (xargs :stobjs state))
  (let* ((table-alist (get-x86-lifter-table state)))
    (if (not (alistp table-alist))
        (hard-error 'previous-lifter-result "Invalid table alist for x86-lifter-table: ~x0."
                    (acons #\0 table-alist nil))
      (let ((previous-result (acl2::lookup-equal whole-form table-alist)))
        (if previous-result
            (prog2$ (cw "NOTE: The call to the lifter ~x0 is redundant.~%" whole-form)
                    previous-result)
          nil)))))
