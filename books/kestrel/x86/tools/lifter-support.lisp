; Supporting tools for x86 lifters
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "kestrel/utilities/make-cons-nest" :dir :system)
(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "kestrel/bv-lists/bv-array-conversions" :dir :system)
(include-book "kestrel/bv/bvchop-def" :dir :system) ; mentioned below
(include-book "kestrel/utilities/translate" :dir :system)

;; An "output-indicator" indicates the desired result of lifting, either :all or some component of the state.

(mutual-recursion
  ;; Create a term representing the extraction of the indicated output from TERM.
  ;; why "normal"?  maybe "component" ?  or non-trivial?
  ;; This can translate some parts of the output-indicator.
  (defun wrap-in-normal-output-extractor (output-indicator term wrld)
    (declare (xargs :guard (plist-worldp wrld)
                    :mode :program ; because of translate-term
                    ))
    (if (symbolp output-indicator)
        (case output-indicator
          (:rax `(bvchop '64 (rax ,term)))
          ;; todo: call eax or use choped rax here?
          (:eax `(bvchop '32 (xr ':rgf '0 ,term))) ; for now, or do something different depending on 32/64 bit mode since eax is not really well supported in 32-bit mode?
          ;; (:eax (rax ,term))
          (:xmm0 `(bvchop '128 (xr ':zmm '0 ,term)))
          (:ymm0 `(bvchop '256 (xr ':zmm '0 ,term)))
          (:zmm0 `(xr ':zmm '0 ,term)) ; seems to already be unsigned
          (t (er hard? 'wrap-in-normal-output-extractor "Unsupported output-indicator: ~x0." output-indicator)))
      (if (not (and (consp output-indicator)
                    (true-listp output-indicator)))
          (er hard? 'wrap-in-normal-output-extractor "Bad output-indicator: ~x0." output-indicator)
        (case (ffn-symb output-indicator)
          ;; (:register <N>)
          (:register (if (and (eql 1 (len (fargs output-indicator)))
                              (natp (farg1 output-indicator)) ;todo: what is the max allowed?
                              )
                         `(xr ':rgf ',(farg1 output-indicator) ,term)
                       (er hard? 'wrap-in-normal-output-extractor "Bad output-indicator: ~x0." output-indicator)))
          ;;  (:register-bool <N>)
          ;; TODO: Deprecate this case but the tester uses :register-bool
          ;; On Linux with gcc, a C function that returns a boolean has been observed to only set the low byte of RAX
          ;; TODO: Should we chop to a single bit?
          (:register-bool (if (and (eql 1 (len (fargs output-indicator)))
                                   (natp (farg1 output-indicator)) ;todo: what is the max allowed?
                                   )
                              `(bvchop '8 (xr ':rgf ',(farg1 output-indicator) ,term))
                            (er hard? 'wrap-in-normal-output-extractor "Bad output-indicator: ~x0." output-indicator)))
          ;; (:mem32 <ADDR-TERM>)
          ;; TODO: Add other sizes of :memXXX
          (:mem32 (if (eql 1 (len (fargs output-indicator)))
                      `(read '4 ,(translate-term (farg1 output-indicator) 'wrap-in-normal-output-extractor wrld) ,term)
                    (er hard? 'wrap-in-normal-output-extractor "Bad output-indicator: ~x0." output-indicator)))
          ;; (:byte-array <ADDR-TERM> <LEN>)
          (:byte-array (if (and (eql 2 (len (fargs output-indicator)))
                                (posp (farg2 output-indicator)) ; number of bytes to read
                                )
                           `(acl2::list-to-byte-array (read-bytes ,(translate-term (farg1 output-indicator) 'wrap-in-normal-output-extractor wrld)
                                                                  ',(farg2 output-indicator)
                                                                  ,term))
                         (er hard? 'wrap-in-normal-output-extractor "Bad output-indicator: ~x0." output-indicator)))
          ;; (:tuple ... output-indicators ...)
          ;; todo: what if no args?
          (:tuple (acl2::make-cons-nest (wrap-in-normal-output-extractors (fargs output-indicator) term wrld)))
          (otherwise (er hard? 'wrap-in-output-extractor "Bad output indicator: ~x0" output-indicator))))))

  (defun wrap-in-normal-output-extractors (output-indicators term wrld)
    (declare (xargs :guard (and (true-listp output-indicators)
                                (plist-worldp wrld))
                    :mode :program ; because of translate-term
                    ))
    (if (endp output-indicators)
        nil
      (cons (wrap-in-normal-output-extractor (first output-indicators) term wrld)
            (wrap-in-normal-output-extractors (rest output-indicators) term wrld)))))

;; Wraps TERM as indicated by OUTPUT-INDICATOR.
;; todo: reorder args?
(defun wrap-in-output-extractor (output-indicator term wrld)
  (declare (xargs :guard (plist-worldp wrld)
                  :mode :program ; because of translate-term
                  ))
  (if (eq :all output-indicator)
      term
    (wrap-in-normal-output-extractor output-indicator term wrld)))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *executable-types32* '(:pe-32 :mach-o-32 :elf-32))
(defconst *executable-types64* '(:pe-64 :mach-o-64 :elf-64))
(defconst *executable-types* (append *executable-types32* *executable-types64*))

;; The type of an x86 executable
(defun executable-typep (type)
  (declare (xargs :guard t))
  (member-eq type *executable-types*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a symbol-list.
(defund maybe-add-debug-rules (debug-rules monitor)
  (declare (xargs :guard (and (or (eq :debug monitor)
                                  (symbol-listp monitor))
                              (symbol-listp debug-rules))))
  (if (eq :debug monitor)
      debug-rules
    (if (member-eq :debug monitor)
        ;; replace :debug in the list with all the debug-rules:
        (union-eq debug-rules (remove-eq :debug monitor))
      ;; no special treatment:
      monitor)))
