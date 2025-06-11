; New method of generating assumptions for x86 lifting
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "regions") ; since this book knows about disjoint-regions48p
(include-book "canonical-unsigned")
(include-book "assumptions") ; todo: for lifter-targetp
(include-book "assumptions-for-inputs")
(include-book "assumptions64")  ; reduce?
(include-book "parsers/elf-tools")
(include-book "read-bytes-and-write-bytes") ; since this book knows about read-bytes
(include-book "kestrel/utilities/quote" :dir :system)
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/bv-lists/all-unsigned-byte-p2" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/reverse" :dir :system))

(local (in-theory (disable acl2::reverse-becomes-reverse-list-gen
                           acl2::reverse-becomes-reverse-list
                           acl2::reverse-removal
                           acl2::revappend-removal
                           assoc-equal
                           symbol-alistp
                           ))) ; todo

(local (in-theory (disable x86isa::byte-listp-becomes-all-unsigned-byte-p ; todo
                           )))
(local
  (defthm true-listp-when-byte-listp
    (implies (acl2::byte-listp x)
             (true-listp x))))

(local
  (defthm all-unsigned-byte-p-when-byte-listp
    (implies (acl2::byte-listp x)
             (acl2::all-unsigned-byte-p 8 x))
    :hints (("Goal" :in-theory (enable acl2::byte-listp acl2::all-unsigned-byte-p)))))

(local
  (defthm byte-listp-of-repeat ;move
    (equal (acl2::byte-listp (acl2::repeat n x))
           (if (posp n)
               (acl2::bytep x)
             t))
    :hints (("Goal" :in-theory (enable acl2::byte-listp acl2::repeat)))))

;; Result is untranslated
(defund symbolic-add-constant (constant term)
  (declare (xargs :guard (integerp constant)))
  (if (= 0 constant)
      term
    `(+ ',constant ,term)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp assumptions).
;; Generates assumptions asserting that a chunk of data has been loaded into memory (e.g., a section or segment of the executable).
(defund assumptions-for-memory-chunk (addr bytes relp state-var base-var stack-slots-needed bvp)
  (declare (xargs :guard (and (natp addr)
                              (acl2::byte-listp bytes)
                              (booleanp relp)
                              (symbolp state-var)
                              (symbolp base-var) ; rename base-address-var?
                              (natp stack-slots-needed)
                              (booleanp bvp))))
  (let ((numbytes (len bytes)))
    (if relp
        ;; Relative addresses make everything relative to the base-var:
        (let* ((first-addr-term (symbolic-add-constant addr base-var)) ; todo: use bvplus?
               (last-addr-term (symbolic-add-constant (+ 1 ; todo: why is this needed?  I have code that ends in RET and checks whether the address after the RET is canonical.  however, making this change elsewhere broke other proofs.
                                                         (+ -1 addr numbytes)) base-var)) ; todo: use bvplus?
               )
          (mv nil ; no error
              (append (if bvp
                          `((integerp ,base-var) ; needed for things like turning + into bvplus
                            (canonical-regionp ,(+ 1 numbytes)  ; todo: why the +1? (see above)
                                               ,(if (= addr 0) base-var `(bvplus 64 ,addr ,base-var))))
                        `((canonical-address-p ,first-addr-term)
                          (canonical-address-p ,last-addr-term)))
                      ;; Assert that the chunk is loaded into memory:
                      ;; TODO: "program-at" is not a great name since the bytes may not represent a program:
                      (if bvp
                          ;; alternate formulation for bv/smt proofs:
                          `((equal (read-bytes ,first-addr-term ',(len bytes) ,state-var) ',bytes))
                        `((program-at ,first-addr-term ; todo: use something better that includes the length, for speed
                                      ',bytes
                                      ,state-var)))
                      ;; Assert that the chunk is disjoint from the saved return address (so writing to the chunk doesn't change it)
                      ;; TODO: Do this only for writable chunks?
                      (if bvp
                          `((disjoint-regions48p ',(len bytes) ,first-addr-term
                                                 '8 (rsp ,state-var)))
                        `((separate ':r ',(len bytes) ,first-addr-term
                                    ':r '8 (rsp ,state-var))))
                      ;; Assert that the chunk is disjoint from the part of the stack that will be written:
                      (if (posp stack-slots-needed)
                          ;; todo: make a better version of separate that doesn't require the Ns to be positive (and that doesn't have the useless rwx params):
                          (if bvp
                              `((disjoint-regions48p ',(len bytes) ,first-addr-term
                                                     ',(* 8 stack-slots-needed) (binary-+ ',(* '-8 stack-slots-needed) (rsp ,state-var))))
                            `((separate ':r ',(len bytes) ,first-addr-term
                                        ':r ',(* 8 stack-slots-needed) (binary-+ ',(* '-8 stack-slots-needed) (rsp ,state-var)))))
                        ;; Can't call separate here because (* 8 stack-slots-needed) = 0:
                        nil))))
      ;; Absolute addresses are just numbers:
      (let* ((first-addr addr)
             (last-addr (+ -1 addr numbytes)) ; todo: use bvplus? ; don't need to add 1 here for that RET issue, because the number should be clearly canonical
             (first-addr-term `',first-addr))
        (if (not (and (canonical-address-p first-addr) ; we can test these here instead of adding them as assumptions
                      (canonical-address-p last-addr)))
            (mv :bad-address nil)
          (mv nil ; no error
              `(;; In the absolute case, the start and end addresses are just numbers, so we don't need canonical claims for them:
                ;; Assert that the chunk is loaded into memory:
                ,(if bvp
                     ;; alternate formulation for bv/smt proofs:
                     `(equal (read-bytes ,first-addr-term ',(len bytes) ,state-var) ',bytes)
                   `(program-at ,first-addr-term ; todo: use something better that includes the length, for speed
                                ',bytes
                                ,state-var))
                ;; Assert that the chunk is disjoint from the saved return address (so writing to the chunk doesn't change it)
                ;; TODO: Do this only for writable chunks?
                ,(if bvp
                     `(disjoint-regions48p ',(len bytes) ,first-addr-term
                                         '8 (rsp ,state-var))
                   `(separate ':r ',(len bytes) ,first-addr-term
                              ':r '8 (rsp ,state-var)))
                ;; Assert that the chunk is disjoint from the part of the stack that will be written:
                ,@(if (posp stack-slots-needed)
                      ;; todo: make a better version of separate that doesn't require the Ns to be positive (and that doesn't have the useless rwx params):
                      (if bvp
                          `((disjoint-regions48p ',(len bytes) ,first-addr-term
                                               ',(* 8 stack-slots-needed) (binary-+ ',(* '-8 stack-slots-needed) (rsp ,state-var))))
                        `((separate ':r ',(len bytes) ,first-addr-term
                                    ':r ',(* 8 stack-slots-needed) (binary-+ ',(* '-8 stack-slots-needed) (rsp ,state-var)))))
                    ;; Can't call separate here because (* 8 stack-slots-needed) = 0:
                    nil))))))))

(defthm true-listp-of-mv-nth-1-of-assumptions-for-memory-chunk
  (true-listp (mv-nth 1 (assumptions-for-memory-chunk addr bytes relp state-var base-var stack-slots-needed bvp)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable assumptions-for-memory-chunk))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp assumptions)
(defund assumptions-for-elf64-segment (program-header-table-entry relp state-var base-var stack-slots-needed bytes bytes-len bvp)
  (declare (xargs :guard (and (alistp program-header-table-entry)
                              (booleanp relp)
                              (symbolp state-var)
                              (symbolp base-var)
                              (natp stack-slots-needed)
                              (acl2::byte-listp bytes)
                              (equal bytes-len (len bytes))
                              (booleanp bvp))
                  :guard-hints (("Goal" :in-theory (enable acl2::elf-program-header-tablep)))))
  (b* ((type (lookup-eq :type program-header-table-entry))
       ((when (not (eq type :pt_load)))
        ;; We skip any segment that is not a LOAD segment:
        (mv nil nil))
       (offset (lookup-eq :offset program-header-table-entry))
       (filesz (lookup-eq :filesz program-header-table-entry))
       (vaddr (lookup-eq :vaddr program-header-table-entry)) ; we don't use the paddr for anything
       (memsz (lookup-eq :memsz program-header-table-entry)) ; todo: do anything with flags or align?
       ((when (not (and (natp offset)
                        (natp filesz)
                        (natp vaddr)
                        (natp memsz))))
        (mv :bad-program-header-table-entry-value nil))
       (last-byte-num (+ -1 offset filesz)))
    (if (not (< last-byte-num bytes-len))
        (mv :bad-byte-range nil)
      (if (< memsz filesz)
          (mv :too-many-bytes-in-file nil)
        (b* ((bytes (take filesz (nthcdr offset bytes)))
             (numzeros (- memsz filesz))
             ;; Zero bytes at the end of the segment may not be stored in the file:
             (bytes (if (posp numzeros)
                        (append bytes (acl2::repeat numzeros 0)) ; optimize?
                      bytes)))
          (assumptions-for-memory-chunk vaddr bytes relp state-var base-var stack-slots-needed bvp))))))

(defthm true-listp-of-mv-nth-1-of-assumptions-for-elf64-segment
  (true-listp (mv-nth 1 (assumptions-for-elf64-segment program-header-table-entry relp state-var base-var stack-slots-needed bytes bytes-len bvp)))
  :hints (("Goal" :in-theory (enable assumptions-for-elf64-segment))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp assumptions).
;; TODO: Check for contradiction due to overlap of segments (after perhaps adding zeros at the end)
(defund assumptions-for-elf64-segments (program-header-table relp state-var base-var stack-slots-needed bytes bytes-len bvp acc)
  (declare (xargs :guard (and (acl2::elf-program-header-tablep program-header-table)
                              (booleanp relp)
                              (symbolp state-var)
                              (symbolp base-var)
                              (natp stack-slots-needed)
                              (acl2::byte-listp bytes)
                              (equal bytes-len (len bytes))
                              (booleanp bvp)
                              (true-listp acc))
                  :guard-hints (("Goal" :in-theory (enable acl2::elf-program-header-tablep
                                                           acl2::true-listp-when-pseudo-term-listp-2)))))
  (if (endp program-header-table)
      (mv nil (reverse acc))
    (b* ((program-header-table-entry (first program-header-table))
         ((mv erp assumptions)
          (assumptions-for-elf64-segment program-header-table-entry relp state-var base-var stack-slots-needed bytes bytes-len bvp))
         ((when erp) (mv erp nil)))
      (assumptions-for-elf64-segments (rest program-header-table) relp state-var base-var stack-slots-needed bytes bytes-len
                                      bvp
                                      (revappend assumptions acc) ; since they will be reversed again at the end
                                      ))))

(defthm true-listp-of-mv-nth-1-of-assumptions-for-elf64-segments
  (implies (true-listp acc)
           (true-listp (mv-nth 1 (assumptions-for-elf64-segments program-header-table relp state-var base-var stack-slots-needed bytes bytes-len bvp acc))))
  :hints (("Goal" :in-theory (enable assumptions-for-elf64-segments))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp ASSUMPTIONS), where ASSUMPTIONS is a list of terms over the variables STATE-VAR and (perhaps BASE-VAR).
(defund assumptions-for-elf64-sections-new (section-names position-independentp stack-slots-needed state-var base-var parsed-elf bvp acc)
  (declare (xargs :guard (and (string-listp section-names)
                              (booleanp position-independentp)
                              (natp stack-slots-needed)
                              (symbolp state-var)
                              (symbolp base-var)
                              (parsed-elfp parsed-elf)
                              (booleanp bvp)
                              (true-listp acc))))
  (if (endp section-names)
      (mv nil (reverse acc))
    (let* ((section-name (first section-names)))
      (if (acl2::elf-section-presentp section-name parsed-elf)
          (b* ((- (cw "(~s0 section detected.)~%" section-name))
               (addr (acl2::get-elf-section-address section-name parsed-elf))
               ((when (not (natp addr)))
                (mv (cons :bad-addr addr) nil))
               (bytes (acl2::get-elf-section-bytes section-name parsed-elf))
               ((when (not bytes)) ; the call to separate would be ill-guarded if there are no bytes?
                (cw "(NOTE: section ~s0 is empty.)~%" section-name)
                (assumptions-for-elf64-sections-new (rest section-names) position-independentp stack-slots-needed state-var base-var parsed-elf bvp acc))
               ((mv erp assumptions)
                (assumptions-for-memory-chunk addr
                                              bytes
                                              position-independentp
                                              state-var base-var stack-slots-needed bvp))
               ((when erp) (mv erp nil)))
            (assumptions-for-elf64-sections-new (rest section-names) position-independentp stack-slots-needed state-var base-var parsed-elf bvp
                                                ;; will be reversed again, as part of the ACC, when this function finishes:
                                                (append (reverse assumptions) acc)))
        (assumptions-for-elf64-sections-new (rest section-names) position-independentp stack-slots-needed state-var base-var parsed-elf bvp acc)))))

(defthm true-listp-of-mv-nth-1-of-assumptions-for-elf64-sections-new
  (implies (true-listp acc)
           (true-listp (mv-nth 1 (assumptions-for-elf64-sections-new section-names position-independentp stack-slots-needed state-var base-var parsed-elf bvp acc))))
  :hints (("Goal" :in-theory (enable assumptions-for-elf64-sections-new))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: eventually remove make- from the names
;; TODO: Deprecate the bvp=nil cae
(defund make-standard-assumptions64-new (stack-slots-needed state-var target-address-term bvp)
  (declare (xargs :guard (and (natp stack-slots-needed)
                              (symbolp state-var)
                              ;; target-address-term may be untranslated
                              (booleanp bvp))))
  (append (make-standard-state-assumptions-fn state-var)
          `((equal (64-bit-modep ,state-var) t) ; can we call make-standard-state-assumptions-64-fn?
            ;; Alignment checking is turned off:
            (not (alignment-checking-enabled-p ,state-var))
            ;; The RSP is 8-byte aligned (TODO: check with Shilpi):
            ;; This may not be respected by malware.
            ;; TODO: Try without this
            (equal 0 (bvchop 3 (rsp ,state-var)))
            ;; The program counter is at the start of the code to lift:
            (equal (rip ,state-var) ,target-address-term)
            )
          ;; The return address must be canonical because we will transfer
          ;; control to that address when doing the return:
          (if bvp
              `((unsigned-canonical-address-p (read 8 (rsp ,state-var) ,state-var)))
            `((canonical-address-p (logext 64 (read 8 (rsp ,state-var) ,state-var)))))
          ;; The stack must be canonical:
          (if bvp
              ;; todo: think about this:
              `((canonical-regionp ,(+ 16 (* 8 stack-slots-needed))
                                   ,(if (= 0 stack-slots-needed)
                                        `(rsp ,state-var)
                                      `(bvplus 64 ',(* -8 stack-slots-needed) (rsp ,state-var)))))
            ;; old-style
            (append `(;; The stack slot contaning the return address must be canonical
                      ;; because the stack pointer returns here when we pop the saved
                      ;; RBP:
                      (canonical-address-p (rsp ,state-var))

                      ;; The stack slot 'below' the return address must be canonical
                      ;; because the stack pointer returns here when we do the return:
                      (canonical-address-p (+ 8 (rsp ,state-var))))
                    (if (posp stack-slots-needed)
                        `(;;add to make-standard-state-assumptions-64-fn?
                          (x86isa::canonical-address-p (+ -8 (rsp ,state-var)))
                          (x86isa::canonical-address-p (binary-+ ',(* -8 stack-slots-needed) (rsp ,state-var))) ; todo: drop if same as above
                          )
                      nil)))))

(defthm true-listp-of-make-standard-assumptions64-new
  (true-listp (make-standard-assumptions64-new stack-slots-needed state-var target-address-term bvp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Generate all the assumptions for an ELF64 file, whether relative or
;; absolute.  Returns (mv erp assumptions assumption-vars) where assumptions is
;; a list of (untranslated) terms.
(defund assumptions-elf64-new (target
                               relp ; rename position-independentp?
                               stack-slots-needed
                               state-var
                               base-var ; only used if relp
                               inputs
                               type-assumptions-for-array-varsp
                               disjoint-chunk-addresses-and-lens
                               bvp
                               parsed-elf)
  (declare (xargs :guard (and (lifter-targetp target)
                              (booleanp relp)
                              (natp stack-slots-needed)
                              (symbolp state-var) ; todo: too strict?
                              (symbolp base-var)
                              (names-and-typesp inputs)
                              (booleanp type-assumptions-for-array-varsp)
                              (alistp disjoint-chunk-addresses-and-lens) ; cars are terms
                              (nat-listp (strip-cdrs disjoint-chunk-addresses-and-lens))
                              (booleanp bvp)
                              (acl2::parsed-elfp parsed-elf))
                  :guard-hints (("Goal" :in-theory (enable acl2::parsed-elfp acl2::true-listp-when-pseudo-term-listp-2)))))
  (b* ((file-type (acl2::parsed-elf-type parsed-elf))
       ((when (not (member-eq file-type '(:rel :dyn :exec))))
        (mv (cons :unknown-file-type file-type) nil nil))
       ;; Decide whether to treat addresses as relative or absolute:
       ;; (relp (if (eq :auto relp)
       ;;           (if (member-eq file-type '(:rel :dyn)) t nil) ; :exec means absolute
       ;;         ;; use the explicitly given relp:
       ;;         relp))
       ;; Decide where to start lifting:
       (target-address (if (eq :entry-point target)
                           (acl2::parsed-elf-entry-point parsed-elf)
                         (if (natp target)
                             target ; explicit address given (relative iff relp)
                           ;; target is the name of a function:
                           (acl2::subroutine-address-elf target parsed-elf))))
       ((when (not (natp target-address)))
        (er hard? 'assumptions-elf64-new "Bad or missing lift target address: ~x0." target-address)
        (mv :bad-or-missing-subroutine-address nil nil))
       (target-address-term (if relp
                                (if bvp
                                    (if (= 0 target-address)
                                        `(logext 64 ,base-var)
                                      `(logext 64 (bvplus 64 ',target-address ,base-var)))
                                  (if (= 0 target-address)
                                      base-var
                                    `(binary-+ ',target-address ,base-var)))
                              (acl2::enquote target-address)))
       (bytes (acl2::parsed-elf-bytes parsed-elf))
       (program-header-table (acl2::parsed-elf-program-header-table parsed-elf))
       ;; Generate assumptions for the segments/sections:
       ((mv erp segment-or-section-assumptions)
        (if (null program-header-table)
            ;; There are no segments, so we have to use the sections (TODO: WHICH ONES?):
            (assumptions-for-elf64-sections-new '(".text" ".data" ".rodata") ; todo: .bss, etc
                                                relp stack-slots-needed state-var base-var parsed-elf bvp nil)
          ;;todo: check that there is at least one LOAD section:
          (assumptions-for-elf64-segments program-header-table relp state-var base-var stack-slots-needed bytes (len bytes) bvp nil)))
       ((when erp) (mv erp nil nil))
       ;; currently, we only assume the inputs are disjoint from the text section (an input to the function being lifted may very well be in a data section or in the stack!):
       (code-address (acl2::get-elf-code-address parsed-elf)) ; todo: what if there are segments but no sections?!
       ((when (not (natp code-address))) ; impossible
        (mv :bad-code-addres nil nil))
       ;; (text-offset (if relp
       ;;                  (symbolic-add-constant code-address base-var) ; todo clean up base-var handling -- done?
       ;;                code-address))
       ((mv input-assumptions input-assumption-vars)
        (if (equal inputs :skip)
            (mv nil nil)
          (input-assumptions-and-vars inputs
                                      ;; todo: handle zmm regs and values passed on the stack?!:
                                      ;; handle structs that fit in 2 registers?
                                      ;; See the System V AMD64 ABI
                                      '((rdi x86) (rsi x86) (rdx x86) (rcx x86) (r8 x86) (r9 x86))
                                      stack-slots-needed
                                      disjoint-chunk-addresses-and-lens ; (acons text-offset (len (acl2::get-elf-code parsed-elf)) nil) ; todo: could there be extra zeros?
                                      type-assumptions-for-array-varsp
                                      nil nil
                                      t ; new-canonicalp
                                      ))))
    (mv nil ; no error
        (append ;; can't use this: not in normal form: (make-standard-state-assumptions-64-fn state-var) ; todo: put back, but these are untranslated!  should all the assumptions be generated untranslated (for presentation) and then translated?
          (make-standard-assumptions64-new stack-slots-needed state-var target-address-term bvp)

          ;; Assumptions about the BASE-VAR:
          (if relp
              (if bvp
                  `((unsigned-canonical-address-p ,base-var)) ; do we need this?
                `(;(integerp ,base-var)
                  (canonical-address-p$inline ,base-var) ; todo: do we need this, given that we have assumptions for all the segments?
                  ))
            nil)
          segment-or-section-assumptions
          input-assumptions)
        input-assumption-vars)))

(defthm true-list-of-mv-nth-1-of-assumptions-elf64-new
  (true-listp (mv-nth 1 (assumptions-elf64-new target relp stack-slots-needed state-var base-var inputs type-assumptions-for-array-varsp disjoint-chunk-addresses-and-lens bvp parsed-elf)))
  :hints (("Goal" :in-theory (enable assumptions-elf64-new))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;move this stuff?

;; Returns (mv erp maybe-extended-acc).
(defun elf64-segment-address-and-len (program-header-table-entry relp base-var bytes-len acc)
  (declare (xargs :guard (and (alistp program-header-table-entry)
                              (booleanp relp)
                              (symbolp base-var)
                              (natp bytes-len)
                              (true-listp acc))
                  :guard-hints (("Goal" :in-theory (enable acl2::elf-program-header-tablep)))))
  (b* ((type (lookup-eq :type program-header-table-entry))
       ((when (not (eq type :pt_load)))
        ;; We skip any segment that is not a LOAD segment:
        (mv nil acc))
       (offset (lookup-eq :offset program-header-table-entry))
       (filesz (lookup-eq :filesz program-header-table-entry))
       (vaddr (lookup-eq :vaddr program-header-table-entry)) ; we don't use the paddr for anything
       (memsz (lookup-eq :memsz program-header-table-entry)) ; todo: do anything with flags or align?
       ((when (not (and (natp offset)
                        (natp filesz)
                        (natp vaddr)
                        (natp memsz))))
        (mv :bad-program-header-table-entry-value nil))
       (last-byte-num (+ -1 offset filesz)))
    (if (not (< last-byte-num bytes-len))
        (mv :not-enough-bytes nil)
      (if (< memsz filesz)
          (mv :too-many-bytes-in-file nil)
        (b* ((address-term (if relp (symbolic-add-constant vaddr base-var) `,vaddr)))
          (mv nil
              (cons (cons address-term memsz)
                    acc)))))))

;; Returns (mv erp bases-and-lens).
(defund elf64-segment-addresses-and-lens (program-header-table relp base-var bytes-len acc)
  (declare (xargs :guard (and (acl2::elf-program-header-tablep program-header-table)
                              (booleanp relp)
                              (symbolp base-var)
                              (natp bytes-len)
                              (true-listp acc))
                  :guard-hints (("Goal" :in-theory (enable acl2::elf-program-header-tablep
                                                           acl2::true-listp-when-pseudo-term-listp-2)))))
  (if (endp program-header-table)
      (mv nil (reverse acc))
    (b* ((program-header-table-entry (first program-header-table))
         ((mv erp acc)
          (elf64-segment-address-and-len program-header-table-entry relp base-var bytes-len acc))
         ((when erp) (mv erp nil)))
      (elf64-segment-addresses-and-lens (rest program-header-table) relp base-var bytes-len acc))))

(local (include-book "kestrel/alists-light/alistp" :dir :system))

;todo: nested induction
(defthm elf64-segment-addresses-and-lens-type
  (implies (and (alistp acc) ; cars are terms
                (nat-listp (strip-cdrs acc)))
           (mv-let (erp bases-and-lens)
             (elf64-segment-addresses-and-lens program-header-table relp base-var bytes-len acc)
             (declare (ignore erp))
             (and (alistp bases-and-lens) ; cars are terms
                  (nat-listp (strip-cdrs bases-and-lens)))))
  :hints (("Goal" :in-theory (enable elf64-segment-addresses-and-lens elf64-segment-address-and-len))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
