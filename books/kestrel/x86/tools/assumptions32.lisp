; Assumptions for 32-bit x86 proofs
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "assumptions")
(include-book "support32")
(include-book "../parsers/parsed-executable-tools")

;; TODO: Add assumptions about segments
(defun standard-state-assumption-32 (x86)
  (declare (xargs :stobjs x86))
  (and (standard-state-assumption x86)
       ;; 32-bit mode (compatibility or protected mode, which are the only modeled
       ;; modes other than 64-bit):
       (equal (64-bit-modep x86) nil) ;try: (not (64-bit-modep x86)) here

       ;; Alignment checking is turned off:
       (not (alignment-checking-enabled-p x86)) ;todo: think about this
       ;; ;; The stack pointer is 4-byte aligned (TODO: check with Shilpi):
       ;; ;; This may not be respected by malware.
       ;; ;; TODO: Try without this
       ;; (equal 0 (mod (xr :rgf *rsp* ,x86) 4))
       (code-segment-well-formedp x86)
       ))

;; The 32-bit address at the top of the stack when a call is made (which is
;; jumped to when the all returns), which is an effective address in the code
;; segment, must be less than the limit of the code
(defund return-address-okp (x86)
  (declare (xargs :stobjs x86))
  (not (< (seg-hidden-limiti *cs* x86)
          (read-from-segment 4 (esp x86) *ss* x86))))

;;for axe
(defthm booleanp-of-return-address-okp
  (booleanp (return-address-okp x86)))

(defthm return-address-okp-intro
  (equal (< (xr :seg-hidden-limit *cs* x86)
            (read-from-segment 4 (esp x86) *ss* x86))
         (not (return-address-okp x86)))
  :hints (("Goal" :in-theory (enable return-address-okp))))

(acl2::add-known-boolean return-address-okp)

;;todo: add more checking
(defun gen-section-assumptions-pe-32 (entry base-of-code)
  (declare (xargs :guard (consp entry)
                  :verify-guards nil))
  (let* ( ;; (name (car entry))
         (section-info (cdr entry))
         (header (acl2::lookup-eq-safe :header section-info))
         (section-rva (acl2::lookup-eq-safe :virtual-address header))
         (characteristics (acl2::lookup-eq-safe :characteristics header))
         (raw-data (acl2::lookup-eq-safe :raw-data section-info))
         (code-sectionp (and (member-eq :IMAGE_SCN_CNT_CODE characteristics)
                             (consp raw-data))) ;todo: check also that the rva is between base of code and base of data?
         (offset-to-section (- section-rva base-of-code)) ;relative to the base of the code segment
         )
    (if code-sectionp
        (list `(code-segment-assumptions32-for-code ',raw-data ',offset-to-section x86))
      nil)))

;; TODO: Check for contradictions from overlapping segments
(defun gen-sections-assumptions-pe-32 (sections base-of-code)
  (declare (xargs :guard (alistp sections)
                  :verify-guards nil))
  (if (endp sections)
      nil
    (append (gen-section-assumptions-pe-32 (first sections) base-of-code)
            (gen-sections-assumptions-pe-32 (rest sections) base-of-code))))

;; If TARGET is :entry-point or a numeric offset, we take whatever section
;; contains that entry point as the .text section, regardless of its actual
;; name.  Otherwise, TARGET is the name of a subroutine (a string), which we
;; look up in the symbol table, which must exist.  We then start execution at
;; the resulting offset for that symbol, relative to the section named ".text"
;; (TODO: Use whatever section name includes the offset?).
(defun gen-standard-assumptions-pe-32 (target
                                       parsed-pe
                                       stack-slots)
  (declare (xargs :guard (and (lifter-targetp target)
                              (natp stack-slots))
                  :verify-guards nil ;todo
                  ))
  (b* ((sections (acl2::get-pe-sections parsed-pe))
       (base-of-code (acl2::get-pe-base-of-code parsed-pe)) ; relative to the base of the image
       (- (cw "Base of the code segment is: ~x0.~%" base-of-code))
       (subroutine-rva    ;relative to the base of the image
        (if (natp target) ; relative to the base of the image
            target
          (if (eq :entry-point target)
              (acl2::get-pe-entry-point parsed-pe) ; relative to the base of the image
            (b* ((symbol-table (acl2::lookup-eq-safe :symbol-table parsed-pe))
                 ((when (eq :none symbol-table))
                  (er hard 'gen-standard-assumption-pe-32 "No symbol table present."))
                 (symbol-record (acl2::lookup-pe-symbol target symbol-table))
                 (offset-to-subroutine (acl2::lookup-eq-safe :value symbol-record)) ;relative to the base of the section?
                 (section-number (acl2::lookup-eq-safe :section-number symbol-record))
                 (- (cw "Offset to ~x0 in symbol table (for section ~x1) is ~x2.~%" target section-number offset-to-subroutine))
                 (section-entry (nth (- section-number 1) sections)) ;numbering starts at 1?
                 (section-info (cdr section-entry))
                 (header (acl2::lookup-eq-safe :header section-info))
                 (section-rva (acl2::lookup-eq-safe :virtual-address header)))
              (+ offset-to-subroutine section-rva)))))
       (- (cw "Subroutine RVA is: ~x0.~%" subroutine-rva))
       (offset-to-subroutine (- subroutine-rva base-of-code))
       (- (cw "Offset to subroutine from the base of the code segment is: ~x0.~%" offset-to-subroutine)))
    (append `((standard-state-assumption-32 x86)
              ;; The program counter is at the start of the routine to lift (this is
              ;; relative to the base of the code segment):
              (equal (eip x86) ',offset-to-subroutine)
              (stack-segment-assumptions32 ',stack-slots x86)
              (code-and-stack-segments-separate x86) ;todo: allow this and other assumptions to be replaced by assumptions about a flat segmentation model
              (return-address-okp x86))
            (gen-sections-assumptions-pe-32 sections base-of-code))))

;; TODO: Add assumptions about the content of sections!
(defun gen-standard-assumptions-mach-o-32 (target
                                           parsed-pe
                                           stack-slots)
  (declare (xargs :guard (and (lifter-targetp target)
                              (natp stack-slots))
                  :verify-guards nil ;todo
                  )
           (ignore target parsed-pe) ;for now
           )
  `((standard-state-assumption-32 x86)
    ;; The program counter is at the start of the routine to lift (this is
    ;; relative to the base of the code segment):
    ;(equal (eip x86) ',offset-to-subroutine)
    (stack-segment-assumptions32 ',stack-slots x86)
    (code-and-stack-segments-separate x86) ;todo: allow this and other assumptions to be replaced by assumptions about a flat segmentation model
    (return-address-okp x86)))
  ;; (let ((text-section-bytes (acl2::get-mach-o-code parsed-mach-o)) ;all the code, not just the given method
  ;;       (text-section-address (acl2::get-mach-o-code-address parsed-mach-o))
  ;;       (subroutine-address (acl2::subroutine-address-mach-o subroutine-name parsed-mach-o)))
  ;;   (standard-assumption-32 text-section-bytes
  ;;                           text-offset
  ;;                           (- subroutine-address text-section-address)
  ;;                           stack-slots
  ;;                           x86)))
