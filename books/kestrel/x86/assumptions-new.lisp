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

(include-book "kestrel/memory/memory48" :dir :system) ; since this book knows about disjoint-regions48p
(include-book "canonical-unsigned")
(include-book "assumptions") ; todo: for lifter-targetp
(include-book "assumptions-for-inputs")
;(include-book "assumptions64")  ; reduce?
(include-book "parsers/parsed-executable-tools")
(include-book "parsers/elf-tools")
(include-book "read-bytes-and-write-bytes") ; since this book knows about read-bytes
(include-book "kestrel/utilities/quote" :dir :system)
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/nat-listp" :dir :system))
;(local (include-book "kestrel/bv-lists/all-unsigned-byte-p2" :dir :system))
;(include-book "kestrel/bv-lists/unsigned-byte-listp" :dir :system) ; todo: reduce
(local (include-book "kestrel/bv-lists/byte-listp" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
;; (local (include-book "kestrel/lists-light/reverse" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/alists-light/strip-cdrs" :dir :system))

(local (in-theory (disable acl2::reverse-removal
                           acl2::revappend-removal
                           assoc-equal
                           symbol-alistp
                           x86isa::byte-listp-becomes-all-unsigned-byte-p ; todo
                           ))) ; todo

(set-induction-depth-limit 1)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Result is untranslated
(defund symbolic-add-constant (constant term)
  (declare (xargs :guard (integerp constant)))
  (if (= 0 constant)
      term
    `(+ ,constant ,term)))

;; Result is untranslated
(defund symbolic-bvplus-constant (size constant term)
  (declare (xargs :guard (integerp constant)))
  (if (= 0 constant)
      term ; could chop
    `(bvplus ,size ,constant ,term)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;move this stuff?

;; ;; Usually extends ACC with a pair (cons <address-term> <size>) for the memory that will be occupied by the segment.
;; ;; Returns (mv erp maybe-extended-acc).
;; (defun elf64-segment-address-and-len (program-header-table-entry relp bvp base-var bytes-len acc)
;;   (declare (xargs :guard (and (alistp program-header-table-entry)
;;                               (booleanp relp)
;;                               (symbolp base-var)
;;                               (natp bytes-len)
;;                               (true-listp acc))
;;                   :guard-hints (("Goal" :in-theory (enable acl2::elf-program-header-tablep)))))
;;   (b* ((type (lookup-eq :type program-header-table-entry))
;;        ((when (not (eq type :pt_load)))
;;         ;; We skip any segment that is not a LOAD segment:
;;         (mv nil acc))
;;        (offset (lookup-eq :offset program-header-table-entry))
;;        (filesz (lookup-eq :filesz program-header-table-entry))
;;        (vaddr (lookup-eq :vaddr program-header-table-entry)) ; we don't use the paddr for anything
;;        (memsz (lookup-eq :memsz program-header-table-entry)) ; todo: do anything with flags or align?
;;        ((when (not (and (natp offset)
;;                         (natp filesz)
;;                         (natp vaddr)
;;                         (natp memsz))))
;;         (mv :bad-program-header-table-entry-value nil))
;;        (last-byte-num (+ -1 offset filesz)))
;;     (if (not (< last-byte-num bytes-len))
;;         (mv :not-enough-bytes nil)
;;       (if (< memsz filesz)
;;           (mv :too-many-bytes-in-file nil)
;;         (b* ((address-term (if relp
;;                                (if bvp
;;                                    (symbolic-bvplus-constant 48 vaddr base-var)
;;                                  (symbolic-add-constant vaddr base-var))
;;                              vaddr)))
;;           (mv nil
;;               (cons (cons address-term memsz)
;;                     acc)))))))

;; ;; Returns (mv erp bases-and-lens).
;; ;drop?
;; (defund elf64-segment-addresses-and-lens (program-header-table relp bvp base-var bytes-len acc)
;;   (declare (xargs :guard (and (acl2::elf-program-header-tablep program-header-table)
;;                               (booleanp relp)
;;                               (symbolp base-var)
;;                               (natp bytes-len)
;;                               (true-listp acc))
;;                   :guard-hints (("Goal" :in-theory (enable acl2::elf-program-header-tablep
;;                                                            acl2::elf-program-header-table-entryp
;;                                                            acl2::true-listp-when-pseudo-term-listp-2)))))
;;   (if (endp program-header-table)
;;       (mv nil (reverse acc))
;;     (b* ((program-header-table-entry (first program-header-table))
;;          ((mv erp acc)
;;           (elf64-segment-address-and-len program-header-table-entry relp bvp base-var bytes-len acc))
;;          ((when erp) (mv erp nil)))
;;       (elf64-segment-addresses-and-lens (rest program-header-table) relp bvp base-var bytes-len acc))))

;; ;todo: nested induction
;; (defthm elf64-segment-addresses-and-lens-type
;;   (implies (and (alistp acc) ; cars are terms
;;                 (nat-listp (strip-cdrs acc)))
;;            (mv-let (erp bases-and-lens)
;;              (elf64-segment-addresses-and-lens program-header-table relp bvp base-var bytes-len acc)
;;              (declare (ignore erp))
;;              (and (alistp bases-and-lens) ; cars are terms
;;                   (nat-listp (strip-cdrs bases-and-lens)))))
;;   :hints (("Goal" :in-theory (enable elf64-segment-addresses-and-lens elf64-segment-address-and-len))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp assumptions).
;; Generates assumptions asserting that a chunk of data has been loaded into memory (e.g., a section or segment of the executable).
;; Also generated assumptions that the addresses are canonical and that the chunk is disjoint from the saved return address and future stack words.
(defund assumptions-for-memory-chunk (offset bytes relp state-var base-var stack-slots-needed bvp new-canonicalp)
  (declare (xargs :guard (and (natp offset)
                              (acl2::byte-listp bytes)
                              (booleanp relp)
                              (symbolp state-var)
                              (symbolp base-var) ; rename base-address-var? ; only used if relp
                              (natp stack-slots-needed)
                              (booleanp bvp)
                              (booleanp new-canonicalp))))
  (let ((numbytes (len bytes)))
    (if relp
        ;; Relative addresses make everything relative to the base-var:
        (let* ((first-addr-term (if bvp (symbolic-bvplus-constant 48 offset base-var) (symbolic-add-constant offset base-var)))
               (last-addr-term (if bvp
                                   (symbolic-bvplus-constant 48 (+ 1 ; todo: why is this needed?  I have code that ends in RET and checks whether the address after the RET is canonical.  however, making this change elsewhere broke other proofs.
                                                                   (+ -1 offset numbytes))
                                                             base-var)
                                 (symbolic-add-constant (+ 1 ; todo: why is this needed?  I have code that ends in RET and checks whether the address after the RET is canonical.  however, making this change elsewhere broke other proofs.
                                                           (+ -1 offset numbytes))
                                                        base-var))) ; todo: use bvplus?
               )
          (mv nil ; no error
              (append
                ;; Assert that the addresses are canonical:
                (if new-canonicalp
                    `((integerp ,base-var) ; needed for things like turning + into bvplus
                      (canonical-regionp ,(+ 1 numbytes)  ; todo: why the +1? (see above)
                                         ,(if (= offset 0) base-var `(bvplus 64 ,offset ,base-var))))
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
                                               ',(* 8 stack-slots-needed) (bvplus 48 ',(* '-8 stack-slots-needed) (rsp ,state-var))))
                      `((separate ':r ',(len bytes) ,first-addr-term
                                  ':r ',(* 8 stack-slots-needed) (bvplus 48 ',(* '-8 stack-slots-needed) (rsp ,state-var)))))
                  ;; Can't call separate here because (* 8 stack-slots-needed) = 0:
                  nil))))
      ;; Absolute addresses are just numbers:
      (let* ((first-addr offset)
             (last-addr (+ -1 offset numbytes)) ; todo: use bvplus? ; don't need to add 1 here for that RET issue, because the number should be clearly canonical
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
                                               ',(* 8 stack-slots-needed) (bvplus 48 ',(* '-8 stack-slots-needed) (rsp ,state-var))))
                        `((separate ':r ',(len bytes) ,first-addr-term
                                    ':r ',(* 8 stack-slots-needed) (bvplus 48 ',(* '-8 stack-slots-needed) (rsp ,state-var)))))
                    ;; Can't call separate here because (* 8 stack-slots-needed) = 0:
                    nil))))))))

(defthm true-listp-of-mv-nth-1-of-assumptions-for-memory-chunk
  (true-listp (mv-nth 1 (assumptions-for-memory-chunk offset bytes relp state-var base-var stack-slots-needed bvp new-canonicalp)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable assumptions-for-memory-chunk))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; Returns (mv erp assumptions)
;; (defund assumptions-for-elf64-segment (program-header-table-entry relp state-var base-var stack-slots-needed bytes bytes-len bvp new-canonicalp)
;;   (declare (xargs :guard (and (alistp program-header-table-entry)
;;                               (booleanp relp)
;;                               (symbolp state-var)
;;                               (symbolp base-var)
;;                               (natp stack-slots-needed)
;;                               (acl2::byte-listp bytes)
;;                               (equal bytes-len (len bytes))
;;                               (booleanp bvp)
;;                               (booleanp new-canonicalp))
;;                   :guard-hints (("Goal" :in-theory (enable acl2::elf-program-header-tablep)))))
;;   (b* ((type (lookup-eq :type program-header-table-entry))
;;        ((when (not (eq type :pt_load)))
;;         ;; We skip any segment that is not a LOAD segment:
;;         (mv nil nil))
;;        (offset (lookup-eq :offset program-header-table-entry))
;;        (filesz (lookup-eq :filesz program-header-table-entry))
;;        (vaddr (lookup-eq :vaddr program-header-table-entry)) ; we don't use the paddr for anything
;;        (memsz (lookup-eq :memsz program-header-table-entry)) ; todo: do anything with flags or align?
;;        ((when (not (and (natp offset)
;;                         (natp filesz)
;;                         (natp vaddr)
;;                         (natp memsz))))
;;         (mv :bad-program-header-table-entry-value nil))
;;        (last-byte-num (+ -1 offset filesz)))
;;     (if (not (< last-byte-num bytes-len))
;;         (mv :bad-byte-range nil)
;;       (if (< memsz filesz)
;;           (mv :too-many-bytes-in-file nil)
;;         (b* ((bytes (take filesz (nthcdr offset bytes)))
;;              (numzeros (- memsz filesz))
;;              ;; Zero bytes at the end of the segment may not be stored in the file:
;;              (bytes (if (posp numzeros)
;;                         (append bytes (acl2::repeat numzeros 0)) ; optimize?
;;                       bytes)))
;;           (assumptions-for-memory-chunk vaddr bytes relp state-var base-var stack-slots-needed bvp new-canonicalp))))))

;; (defthm true-listp-of-mv-nth-1-of-assumptions-for-elf64-segment
;;   (true-listp (mv-nth 1 (assumptions-for-elf64-segment program-header-table-entry relp state-var base-var stack-slots-needed bytes bytes-len bvp new-canonicalp)))
;;   :hints (("Goal" :in-theory (enable assumptions-for-elf64-segment))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; Returns (mv erp assumptions).
;; ;; TODO: Check for contradiction due to overlap of segments (after perhaps adding zeros at the end)
;; (defund assumptions-for-elf64-segments (program-header-table relp state-var base-var stack-slots-needed bytes bytes-len bvp new-canonicalp acc)
;;   (declare (xargs :guard (and (acl2::elf-program-header-tablep program-header-table)
;;                               (booleanp relp)
;;                               (symbolp state-var)
;;                               (symbolp base-var)
;;                               (natp stack-slots-needed)
;;                               (acl2::byte-listp bytes)
;;                               (equal bytes-len (len bytes))
;;                               (booleanp bvp)
;;                               (booleanp new-canonicalp)
;;                               (true-listp acc))
;;                   :guard-hints (("Goal" :in-theory (enable acl2::elf-program-header-tablep
;;                                                            acl2::elf-program-header-table-entryp
;;                                                            acl2::true-listp-when-pseudo-term-listp-2)))))
;;   (if (endp program-header-table)
;;       (mv nil (reverse acc))
;;     (b* ((program-header-table-entry (first program-header-table))
;;          ((mv erp assumptions)
;;           (assumptions-for-elf64-segment program-header-table-entry relp state-var base-var stack-slots-needed bytes bytes-len bvp new-canonicalp))
;;          ((when erp) (mv erp nil)))
;;       (assumptions-for-elf64-segments (rest program-header-table) relp state-var base-var stack-slots-needed bytes bytes-len
;;                                       bvp new-canonicalp
;;                                       (revappend assumptions acc) ; since they will be reversed again at the end
;;                                       ))))

;; (defthm true-listp-of-mv-nth-1-of-assumptions-for-elf64-segments
;;   (implies (true-listp acc)
;;            (true-listp (mv-nth 1 (assumptions-for-elf64-segments program-header-table relp state-var base-var stack-slots-needed bytes bytes-len bvp new-canonicalp acc))))
;;   :hints (("Goal" :in-theory (enable assumptions-for-elf64-segments))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; Returns (mv erp ASSUMPTIONS), where ASSUMPTIONS is a list of terms over the variables STATE-VAR and (perhaps BASE-VAR).
;; (defund assumptions-for-elf64-sections-new (section-names position-independentp stack-slots-needed state-var base-var parsed-elf bvp new-canonicalp acc)
;;   (declare (xargs :guard (and (string-listp section-names)
;;                               (booleanp position-independentp)
;;                               (natp stack-slots-needed)
;;                               (symbolp state-var)
;;                               (symbolp base-var)
;;                               (parsed-elfp parsed-elf)
;;                               (booleanp bvp)
;;                               (booleanp new-canonicalp)
;;                               (true-listp acc))))
;;   (if (endp section-names)
;;       (mv nil (reverse acc))
;;     (let* ((section-name (first section-names)))
;;       (if (acl2::elf-section-presentp section-name parsed-elf)
;;           (b* ((- (cw "(~s0 section detected.)~%" section-name))
;;                (addr (acl2::get-elf-section-address section-name parsed-elf))
;;                ((when (not (natp addr)))
;;                 (mv (cons :bad-addr addr) nil))
;;                (bytes (acl2::get-elf-section-bytes section-name parsed-elf))
;;                ((when (not bytes)) ; the call to separate would be ill-guarded if there are no bytes?
;;                 (cw "(NOTE: section ~s0 is empty.)~%" section-name)
;;                 (assumptions-for-elf64-sections-new (rest section-names) position-independentp stack-slots-needed state-var base-var parsed-elf bvp new-canonicalp acc))
;;                ((mv erp assumptions)
;;                 (assumptions-for-memory-chunk addr
;;                                               bytes
;;                                               position-independentp
;;                                               state-var base-var stack-slots-needed bvp new-canonicalp))
;;                ((when erp) (mv erp nil)))
;;             (assumptions-for-elf64-sections-new (rest section-names) position-independentp stack-slots-needed state-var base-var parsed-elf bvp new-canonicalp
;;                                                 ;; will be reversed again, as part of the ACC, when this function finishes:
;;                                                 (append (reverse assumptions) acc)))
;;         (assumptions-for-elf64-sections-new (rest section-names) position-independentp stack-slots-needed state-var base-var parsed-elf bvp new-canonicalp acc)))))

;; (defthm true-listp-of-mv-nth-1-of-assumptions-for-elf64-sections-new
;;   (implies (true-listp acc)
;;            (true-listp (mv-nth 1 (assumptions-for-elf64-sections-new section-names position-independentp stack-slots-needed state-var base-var parsed-elf bvp new-canonicalp acc))))
;;   :hints (("Goal" :in-theory (enable assumptions-for-elf64-sections-new))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: eventually remove make- from the names
;; TODO: Deprecate the bvp=nil case
;; Not ELF-specific
(defund make-standard-assumptions64-new (stack-slots-needed
                                         state-var
                                         base-var ; only needed if position-independentp
                                         target-offset
                                         position-independentp
                                         bvp
                                         new-canonicalp)
  (declare (xargs :guard (and (natp stack-slots-needed)
                              (symbolp state-var)
                              (symbolp base-var)
                              (natp target-offset)
                              (booleanp position-independentp)
                              (booleanp bvp)
                              (booleanp new-canonicalp))))
  (let ((target-address-term (if position-independentp
                                 ;; Position-independent, so the target is the base-var plus the target-offset:
                                 (if bvp
                                     (if (= 0 target-offset)
                                         `(logext 64 ,base-var) ; avoids adding 0
                                       `(logext 64 (bvplus 64 ',target-offset ,base-var)))
                                   (if (= 0 target-offset)
                                       base-var ; avoids adding 0
                                     `(binary-+ ',target-offset ,base-var)))
                               ;; Not position-independent, so the target is a concrete address:
                               (acl2::enquote target-offset))))
    (append (make-standard-state-assumptions-fn state-var)
            ;; Assumptions about the BASE-VAR:
            (if position-independentp
                (if new-canonicalp
                    `((unsigned-canonical-address-p ,base-var)) ; do we need this?
                  `(;(integerp ,base-var)
                    (canonical-address-p$inline ,base-var) ; todo: do we need this, given that we have assumptions for all the segments?
                    ))
              nil)
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
            (if new-canonicalp
                `((unsigned-canonical-address-p (read 8 (rsp ,state-var) ,state-var)))
              `((canonical-address-p (logext 64 (read 8 (rsp ,state-var) ,state-var)))))
            ;; The stack must be canonical:
            (if new-canonicalp
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
                        nil))))))

(defthm true-listp-of-make-standard-assumptions64-new
  (true-listp (make-standard-assumptions64-new stack-slots-needed state-var base-var target-offset position-independentp bvp new-canonicalp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognizes a representation of a memory region, of the form:
;; (<len> <addr> <bytes>)
;; todo: consider adding support for zero-fill (or partial zero-fill) regions
(defund memory-regionp (reg)
  (declare (xargs :guard t))
  (and (true-listp reg)
       (= 3 (len reg))
       (natp (first reg)) ; length
       ;; The address can be absolute (a natp) or relative (a term representing some base-var plus the addr):
       (natp (second reg)) ; addr (agnostic on the size of the memory space, for now)
       (acl2::byte-listp (third reg))
       ;; the length must be correct, at least for now:
       (= (first reg) (len (third reg)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognizes a true-list of memory regions
(defund memory-regionsp (regions)
  (declare (xargs :guard t))
  (if (not (consp regions))
      (null regions)
    (and (memory-regionp (first regions))
         (memory-regionsp (rest regions)))))

(local
  (defthm memory-regionsp-of-revappend
    (implies (and (memory-regionsp x)
                  (memory-regionsp y))
             (memory-regionsp (revappend x y)))
    :hints (("Goal" :in-theory (enable revappend memory-regionsp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Strips out just the addresses and lens
(defund memory-region-addresses-and-lens (regions acc)
  (declare (xargs :guard (and (memory-regionsp regions)
                              (alistp acc))
                  :guard-hints (("Goal" :in-theory (enable memory-regionsp
                                                           memory-regionp)))))
  (if (endp regions)
      (reverse acc)
    (b* ((region (first regions))
         (length (first region))
         (addr (second region))
         ;;(bytes (third region))
         )
      (memory-region-addresses-and-lens (rest regions)
                                        (acons addr length acc)))))

(local
  (defthm alistp-of-memory-region-addresses-and-lens
    (implies (alistp acc)
             (alistp (memory-region-addresses-and-lens regions acc)))
    :hints (("Goal" :in-theory (enable memory-region-addresses-and-lens)))))

(local
  (defthm nat-listp-of-strip-cdrs-of-memory-region-addresses-and-lens
    (implies (and (memory-regionsp regions)
;                  (true-listp acc)
                  (nat-listp (strip-cdrs acc)))
             (nat-listp (strip-cdrs (memory-region-addresses-and-lens regions acc))))
    :hints (("Goal" :in-theory (enable memory-region-addresses-and-lens
                                       memory-regionsp
                                       memory-regionp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp assumptions).
(defund assumptions-for-memory-regions (regions base-var state-var stack-slots-needed bvp position-independentp new-canonicalp acc)
  (declare (xargs :guard (and (memory-regionsp regions)
                              (symbolp base-var) ; only used if position-independentp
                              (symbolp state-var)
                              (natp stack-slots-needed)
                              (booleanp bvp)
                              (booleanp position-independentp)
                              (booleanp new-canonicalp)
                              (true-listp acc))
                  :guard-hints (("Goal" :in-theory (e/d (memory-regionsp
                                                         memory-regionp)
                                                        (acl2::acl2-numberp-of-car-when-acl2-number-listp ; todo, for speed
                                                         rationalp-implies-acl2-numberp
                                                         ))))))
  (if (endp regions)
      (mv nil (reverse acc))
    (b* ((region (first regions))
         (length (first region))
         (addr (second region))
         (bytes (third region))
         ((mv erp assumptions-for-region)
          (if position-independentp
              ;; Relative addresses make everything relative to the base-var:
              (let* ((first-addr-term (if bvp (symbolic-bvplus-constant 48 addr base-var) (symbolic-add-constant addr base-var)))
                     (last-addr-term (if bvp
                                         (symbolic-bvplus-constant 48 (+ 1 ; todo: why is this needed?  I have code that ends in RET and checks whether the address after the RET is canonical.  however, making this change elsewhere broke other proofs.
                                                                         (+ -1 addr length))
                                                                   base-var)
                                       (symbolic-add-constant (+ 1 ; todo: why is this needed?  I have code that ends in RET and checks whether the address after the RET is canonical.  however, making this change elsewhere broke other proofs.
                                                                 (+ -1 addr length))
                                                              base-var))) ; todo: use bvplus?
                     )
                (mv nil ; no error
                    (append
                      ;; Assert that the addresses are canonical:
                      (if new-canonicalp
                          `((integerp ,base-var) ; needed for things like turning + into bvplus
                            (canonical-regionp ,(+ 1 length)  ; todo: why the +1? (see above)
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
                                                     ',(* 8 stack-slots-needed) (bvplus 48 ',(* '-8 stack-slots-needed) (rsp ,state-var))))
                            `((separate ':r ',(len bytes) ,first-addr-term
                                        ':r ',(* 8 stack-slots-needed) (bvplus 48 ',(* '-8 stack-slots-needed) (rsp ,state-var)))))
                        ;; Can't call separate here because (* 8 stack-slots-needed) = 0:
                        nil))))
            ;; Absolute addresses are just numbers:
            (let* ((first-addr addr)
                   (last-addr (+ -1 addr length)) ; todo: use bvplus? ; don't need to add 1 here for that RET issue, because the number should be clearly canonical
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
                                                       ',(* 8 stack-slots-needed) (bvplus 48 ',(* '-8 stack-slots-needed) (rsp ,state-var))))
                              `((separate ':r ',(len bytes) ,first-addr-term
                                          ':r ',(* 8 stack-slots-needed) (bvplus 48 ',(* '-8 stack-slots-needed) (rsp ,state-var)))))
                          ;; Can't call separate here because (* 8 stack-slots-needed) = 0:
                          nil)))))))
         ((when erp)
          (mv erp nil)))
      (assumptions-for-memory-regions (rest regions)
                                      base-var state-var stack-slots-needed bvp position-independentp new-canonicalp
                                      ;; todo: think about the order:
                                      (append assumptions-for-region acc)))))

(local
  (defthm true-list-of-mv-nth-1-of-assumptions-for-memory-regions
    (implies (true-listp acc)
             (true-listp (mv-nth 1 (assumptions-for-memory-regions regions base-var state-var stack-slots-needed bvp position-independentp new-canonicalp acc))))
    :hints (("Goal" :in-theory (enable assumptions-for-memory-regions)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp regions).
(defund elf64-regions-to-load-aux (program-header-table all-bytes-len all-bytes acc)
  (declare (xargs :guard (and (acl2::elf-program-header-tablep program-header-table)
                              (acl2::byte-listp all-bytes)
                              (equal all-bytes-len (len all-bytes))
                              (true-listp acc))
                  :guard-hints (("Goal" :in-theory (enable acl2::elf-program-header-tablep
                                                           acl2::elf-program-header-table-entryp)))))
  (if (endp program-header-table)
      (mv nil (reverse acc))
    (b* ((program-header-table-entry (first program-header-table))
         (type (lookup-eq :type program-header-table-entry))
         ;; We skip any segment that is not a LOAD segment:
         ((when (not (eq type :pt_load)))
          (elf64-regions-to-load-aux (rest program-header-table) all-bytes-len all-bytes acc))
         ;; It is a LOAD segment:
         (offset (lookup-eq :offset program-header-table-entry))
         (filesz (lookup-eq :filesz program-header-table-entry))
         (vaddr (lookup-eq :vaddr program-header-table-entry)) ; we don't use the paddr for anything
         (memsz (lookup-eq :memsz program-header-table-entry)) ; todo: do anything with flags or align?
         ((when (not (and (natp offset)
                          (natp filesz)
                          (natp vaddr)
                          (natp memsz)
                          ;; The file size can't be larger than the memory size:
                          (<= filesz memsz))))
          (mv :bad-program-header-table-entry-value nil))
         (last-byte-num (+ -1 offset filesz))
         ((when (not (< last-byte-num all-bytes-len)))
          (mv :not-enough-bytes nil))
         ;; If the file size is smaller than the memory size, we fill with zeros (todo: what if there are too many?):
         (numzeros (- memsz filesz))
         (bytes (take filesz (nthcdr offset all-bytes)))
         ;; Zero bytes at the end of the segment may not be stored in the file:
         (bytes (if (posp numzeros)
                    (append bytes (acl2::repeat numzeros 0)) ; optimize?
                  bytes))
         ;; ((when (not (= memsz filesz))) ; todo
         ;;  (cw "Warning: filesz is ~x0 but memsz is ~x1.~%" filesz memsz)
         ;;  (mv :filesz-memsz-mismatch nil))
         )
      (elf64-regions-to-load-aux (rest program-header-table)
                                 all-bytes-len all-bytes
                                 (cons (list memsz vaddr bytes)
                                       acc)))))

(local
  (defthm memory-regionsp-of-mv-nth-1-of-elf64-regions-to-load-aux
    (implies (and (memory-regionsp acc)
                  (acl2::byte-listp all-bytes)
                  (equal all-bytes-len (len all-bytes)))
             (memory-regionsp (mv-nth 1 (elf64-regions-to-load-aux program-header-table all-bytes-len all-bytes acc))))
    :hints (("Goal" :in-theory (enable elf64-regions-to-load-aux memory-regionsp memory-regionp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp regions).
(defund elf64-regions-to-load (parsed-elf)
  (declare (xargs :guard (acl2::parsed-elfp parsed-elf)))
  (b* ((program-header-table (acl2::parsed-elf-program-header-table parsed-elf))
       (all-bytes (acl2::parsed-elf-bytes parsed-elf))
       ;; For now, we only look at the segments, not the sections, as the segments
       ;; are what is actually loaded into memory when the program runs.
       ;; TODO: Consider implementing some sort of dynamic loading using the
       ;; sections (but call instructions (and others?) may need to be fixed up):
       ((when (not (consp program-header-table)))
        (er hard? 'assumptions-elf64-new "Program header table is empty. Please link the executable") ; todo: print the name
        (mv :empty-program-header-table nil))
       ;; (if (null program-header-table) ; todo: simplify this:
       ;;     (prog2$ (er hard? 'assumptions-elf64-new "No program-header-table.  Please link the executbable.")
       ;;             ;; There are no segments, so we have to use the sections (TODO: WHICH ONES?):
       ;;             (assumptions-for-elf64-sections-new '(".text" ".data" ".rodata") ; todo: .bss, etc
       ;;                                                 position-independentp stack-slots-needed state-var base-var parsed-elf bvp new-canonicalp nil))
       )
    (elf64-regions-to-load-aux program-header-table (len all-bytes) all-bytes nil)))

;; Returns (mv erp regions).
(local
  (defthm memory-regionsp-of-mv-nth-1-of-elf64-regions-to-load
    (implies (acl2::parsed-elfp parsed-elf)
             (memory-regionsp (mv-nth 1 (elf64-regions-to-load parsed-elf))))
    :hints (("Goal" :in-theory (enable elf64-regions-to-load)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun macho64-regions-to-load-aux (commands all-bytes-len all-bytes acc)
  (declare (xargs :guard (and (acl2::mach-o-command-listp commands)
                              (acl2::byte-listp all-bytes)
                              (equal all-bytes-len (len all-bytes))
                              (true-listp acc))
                  :guard-hints (("Goal" :in-theory (enable acl2::mach-o-command-listp
                                                           acl2::mach-o-commandp)))))
  (if (endp commands)
      (mv nil (reverse acc))
    (let* ((command (first commands))
           (cmd-type (lookup-eq :cmd command)))
      (if (not (member-eq cmd-type '(:LC_SEGMENT :LC_SEGMENT_64)))
          ;; not a load command, so skip:
          (macho64-regions-to-load-aux (rest commands) all-bytes-len all-bytes acc)
        (b* ((vaddr (lookup-eq :vmaddr command)) ; var names here match what we do for ELF
             (memsz (lookup-eq :vmsize command))
             (offset (lookup-eq :fileoff command))
             (filesz (lookup-eq :filesize command))
             ((when (not (and (natp offset)
                              (natp filesz)
                              (natp vaddr)
                              (natp memsz)
                              ;; The file size can't be larger than the memory size:
                              (<= filesz memsz))))
              (er hard? 'macho64-regions-to-load-aux "Bad load command: vaddr=~x0, memsz=~x1, offset=~x2, filesz=~x3." vaddr memsz offset filesz)
              (mv :bad-load-command nil))
             (last-byte-num (+ -1 offset filesz))
             ((when (not (< last-byte-num all-bytes-len)))
              (mv :not-enough-bytes nil))
             ;; If the file size is smaller than the memory size, we fill with zeros (todo: what if there are too many?):
             (numzeros (- memsz filesz))
             ((when (> numzeros 10000)) ; allows padding with zeros up a multiple of 4k
              (cw "Too many zeros (~x0)!  Skipping this segment!~%" numzeros) ; ttodo!
              (macho64-regions-to-load-aux (rest commands) all-bytes-len all-bytes acc))
             (bytes (take filesz (nthcdr offset all-bytes)))
             ;; Zero bytes at the end of the segment may not be stored in the file:
             (bytes (if (posp numzeros)
                        (append bytes (acl2::repeat numzeros 0)) ; optimize?
                      bytes)))
          (macho64-regions-to-load-aux (rest commands)
                                       all-bytes-len all-bytes
                                       (cons (list memsz vaddr bytes)
                                             acc)))))))

(local
  (defthm memory-regionsp-of-mv-nth-1-of-macho64-regions-to-load-aux
    (implies (and (memory-regionsp acc)
                  (acl2::byte-listp all-bytes)
                  (equal all-bytes-len (len all-bytes)))
             (memory-regionsp (mv-nth 1 (macho64-regions-to-load-aux command all-bytes-len all-bytes acc))))
    :hints (("Goal" :in-theory (enable macho64-regions-to-load-aux memory-regionsp memory-regionp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp regions).
(defund macho64-regions-to-load (parsed-macho)
  (declare (xargs :guard (acl2::parsed-mach-o-p parsed-macho)
                  :guard-hints (("Goal" :in-theory (enable acl2::parsed-mach-o-p)))))
  (b* ((commands (lookup-eq :cmds parsed-macho))
       (all-bytes (lookup-eq :bytes parsed-macho)))
    (macho64-regions-to-load-aux commands (len all-bytes) all-bytes nil)))

(local
  (defthm memory-regionsp-of-mv-nth-1-of-macho64-regions-to-load
    (implies (acl2::parsed-mach-o-p parsed-macho)
             (memory-regionsp (mv-nth 1 (macho64-regions-to-load parsed-macho))))
    :hints (("Goal" :in-theory (enable macho64-regions-to-load acl2::parsed-mach-o-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun acl2::pe-sectionp (section)
  (declare (xargs :guard t))
  (and (consp section)
       (let ((name (first section))
             (info (rest section)))
         (and (stringp name)
              (symbol-alistp info)
              (let ((header (lookup-eq :header info))
                    (bytes (lookup-eq :raw-data info)))
                (and (symbol-alistp header)
                     (acl2::byte-listp bytes)))))))


(defun acl2::pe-section-listp (sections)
  (declare (xargs :guard t))
  (if (not (consp sections))
      (null sections)
    (and (acl2::pe-sectionp (first sections))
         (acl2::pe-section-listp (rest sections)))))

;move
(defun acl2::parsed-pe-p (pe)
  (declare (xargs :guard t))
  (and (symbol-alistp pe)
       (acl2::pe-section-listp (lookup-eq :sections pe))))

(defun pe64-regions-to-load-aux (sections acc)
  (declare (xargs :guard (and (acl2::pe-section-listp sections)
;                              (acl2::byte-listp all-bytes)
;                              (equal all-bytes-len (len all-bytes))
                              (true-listp acc))
                  :guard-hints (("Goal" :in-theory (enable acl2::pe-section-listp
                                                           acl2::pe-sectionp)))))
  (if (endp sections)
      (mv nil (reverse acc))
    (b* ((section (first sections)) ; todo: do all section types get loaded?
         ;; (name (first section))
         (info (rest section))
         (header (lookup-eq :header info))
         (vaddr (lookup-eq :virtual-address header)) ; var names here match what we do for ELF
         (memsz (lookup-eq :virtual-size header))
         ;; (offset (lookup-eq :pointer-to-raw-data section)) ; todo: this is rel to what?
         ;; (filesz (lookup-eq :filesize section))
         (bytes (lookup-eq :raw-data info))
         (len-bytes (len bytes))
         ((when (not (and ;; (natp offset)
                       ;; (natp filesz)
                       (natp vaddr)
                       (natp memsz)
                       ;; The data length can't be larger than the memory size:
                       (<= len-bytes memsz) ;; the size of the raw data may be rounded up, but that should all be handled by the parser
                       )))
          (er hard? 'pe64-regions-to-load-aux "Bad section: vaddr=~x0, memsz=~x1, len-bytes=~x2." vaddr memsz len-bytes)
          (mv :bad-load-section nil))
         ((when (not (equal memsz len-bytes)))
          (er hard? 'pe64-regions-to-load-aux "Bad section length: memsz=~x0, bytes=~x1." memsz bytes)
          (mv :bad-load-section nil))
         ;; ttodo: do we ever need to pad with zeros?
         ;; (last-byte-num (+ -1 filesz))
         ;; ((when (not (< last-byte-num len-bytes)))
         ;;  (mv :not-enough-bytes nil))
         ;; ;; If the file size is smaller than the memory size, we fill with zeros (todo: what if there are too many?):
         ;; (numzeros (- memsz filesz))
         ;; ((when (> numzeros 10000)) ; allows padding with zeros up a multiple of 4k
         ;;  (cw "Too many zeros (~x0)!  Skipping this segment!~%" numzeros) ; ttodo!
         ;;  (pe64-regions-to-load-aux (rest sections) all-bytes-len all-bytes acc))
         ;; (bytes (take filesz (nthcdr offset all-bytes)))
         ;; ;; Zero bytes at the end of the segment may not be stored in the file:
         ;; (bytes (if (posp numzeros)
         ;;            (append bytes (acl2::repeat numzeros 0)) ; optimize?
         ;;          bytes))
         )
      (pe64-regions-to-load-aux (rest sections)
                                ;all-bytes-len all-bytes
                                (cons (list memsz vaddr bytes)
                                      acc)))))

(local
  (defthm memory-regionsp-of-mv-nth-1-of-pe64-regions-to-load-aux
    (implies (and ;(not (mv-nth 0 (pe64-regions-to-load-aux sections acc))) ; no error
                  (acl2::pe-section-listp sections)
                  (memory-regionsp acc)
                  ;;(acl2::byte-listp all-bytes)
                  ;;(equal all-bytes-len (len all-bytes))
                  )
             (memory-regionsp (mv-nth 1 (pe64-regions-to-load-aux sections acc))))
    :hints (("Goal" :in-theory (enable pe64-regions-to-load-aux memory-regionsp memory-regionp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund pe64-regions-to-load (parsed-pe)
  (declare (xargs :guard (acl2::parsed-pe-p parsed-pe)
                  :guard-hints (("Goal" :in-theory (enable acl2::parsed-pe-p)))))
  (b* ((sections (lookup-eq :sections parsed-pe))
       ;; (all-bytes (lookup-eq :bytes parsed-pe)) ; currently, each section stores its :raw-data
       )
    (pe64-regions-to-load-aux sections nil)))

(local
  (defthm memory-regionsp-of-mv-nth-1-of-pe64-regions-to-load
    (implies (acl2::parsed-pe-p parsed-pe)
             (memory-regionsp (mv-nth 1 (pe64-regions-to-load parsed-pe))))
    :hints (("Goal" :in-theory (enable pe64-regions-to-load acl2::parsed-pe-p)))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Generate all the assumptions for an ELF64 file, whether relative or
;; absolute.  Returns (mv erp assumptions assumption-vars) where assumptions is
;; a list of (untranslated) terms and the assumption-vars are the variables
;; introduced by the assumptions to represent various state components.
(defund assumptions-elf64-new (target
                               position-independentp
                               stack-slots-needed
                               state-var
                               inputs
                               type-assumptions-for-array-varsp
                               inputs-disjoint-from
                               bvp
                               new-canonicalp
                               parsed-elf)
  (declare (xargs :guard (and (lifter-targetp target)
                              (booleanp position-independentp)
                              (natp stack-slots-needed)
                              (symbolp state-var) ; todo: too strict?
                              (names-and-typesp inputs)
                              (booleanp type-assumptions-for-array-varsp)
                              (member-eq inputs-disjoint-from '(nil :code :all))
                              (booleanp bvp)
                              (booleanp new-canonicalp)
                              (acl2::parsed-elfp parsed-elf))
                  :guard-hints (("Goal" :in-theory (enable acl2::parsed-elfp acl2::true-listp-when-pseudo-term-listp-2)))))
  (b* ((base-var 'base-address) ; arbitrary base address, only used if position-independentp
       ;; Decide where to start lifting:
       (target-offset (if (eq :entry-point target)
                          (acl2::parsed-elf-entry-point parsed-elf)
                        (if (natp target)
                            target ; explicit address given (relative iff position-independentp)
                          ;; target is the name of a function:
                          (acl2::subroutine-address-elf target parsed-elf))))
       ((when (not (natp target-offset)))
        (er hard? 'assumptions-elf64-new "Bad or missing lift target offset: ~x0." target-offset)
        (mv :bad-or-missing-subroutine-address nil nil))
       ;; Make the standard assumptions:
       (standard-assumptions (make-standard-assumptions64-new stack-slots-needed state-var base-var target-offset position-independentp bvp new-canonicalp))
       ;; Gather memory-regions to assume loaded:
       ((mv erp regions-to-load) (elf64-regions-to-load parsed-elf)) ; these use absolute addresses
       ((when erp) (mv erp nil nil))
       ;; Checks that there is at least one load segment:
       ((when (not (consp regions-to-load)))
        (mv :no-memory-regions-found-in-executable nil nil))
       ;; Generate assumptions for the regions (bytes are loaded, addresses are canonical, regions are disjoint from future stack words):
       ((mv erp memory-region-assumptions)
        (assumptions-for-memory-regions regions-to-load base-var state-var stack-slots-needed bvp position-independentp new-canonicalp nil))
       ((when erp) (mv erp nil nil))
       ;; Decide which memory regions to assume disjoint from the inputs:
       ((mv erp addresses-and-lens-of-chunks-disjoint-from-inputs)
        (if (eq nil inputs-disjoint-from)
            ;; Don't assume the inputs are disjoint from anything:
            (mv nil nil)
          (if (eq :all inputs-disjoint-from)
              ;; Assume the inputs are disjoint from all the sections/segments in the executable::
              ;; Warning: This is quite strong: an input to the function being lifted may very well be in a data section or in the stack!):
              (mv nil (memory-region-addresses-and-lens regions-to-load nil))
            ;; inputs-disjoint-from must be :code, so assume the inputs are disjoint from the code bytes only:
            ;; todo: what if there are segments but no sections?  could use the segment that contains the text section, if we can find it, or throw an error.
            ;; could allow the user to specify exactly which regions to assume disjoint from the assumptions.
            (b* ((code-address (acl2::get-elf-text-section-address parsed-elf))
                 ((when (not (natp code-address))) ; impossible?
                  (mv :bad-code-addres nil))
                 (text-offset-term (if position-independentp
                                       (if bvp
                                           (symbolic-bvplus-constant 48 code-address base-var)
                                         (symbolic-add-constant code-address base-var))
                                     code-address)))
              ; todo: could there be extra zeros?:
              (mv nil (acons text-offset-term (len (acl2::get-elf-code parsed-elf)) nil))))))
       ((when erp) (mv erp nil nil))
       ;; Generate assumptions for the inputs (introduce vars, canonical, disjointness from future stack space, disjointness from bytes loaded from the executable, disjointness from saved return address):
       ((mv input-assumptions input-assumption-vars)
        (if (equal inputs :skip)
            (mv nil nil)
          (assumptions-and-vars-for-inputs inputs ; tttodo: do we assume inputs disjoint from the stack?
                                           ;; todo: handle zmm regs and values passed on the stack?!:
                                           ;; handle structs that fit in 2 registers?
                                           ;; See the System V AMD64 ABI
                                           '((rdi x86) (rsi x86) (rdx x86) (rcx x86) (r8 x86) (r9 x86))
                                           stack-slots-needed
                                           addresses-and-lens-of-chunks-disjoint-from-inputs
                                           type-assumptions-for-array-varsp
                                           nil nil
                                           new-canonicalp))))
    (mv nil ; no error
        (append standard-assumptions
                memory-region-assumptions
                input-assumptions)
        input-assumption-vars)))

(defthm true-list-of-mv-nth-1-of-assumptions-elf64-new
  (true-listp (mv-nth 1 (assumptions-elf64-new target position-independentp stack-slots-needed state-var inputs type-assumptions-for-array-varsp inputs-disjoint-from bvp new-canonicalp parsed-elf)))
  :hints (("Goal" :in-theory (enable assumptions-elf64-new))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Generate all the assumptions for a MACHO64 file, whether relative or
;; absolute.  Returns (mv erp assumptions assumption-vars) where assumptions is
;; a list of (untranslated) terms and the assumption-vars are the variables
;; introduced by the assumptions to represent various state components.
(defund assumptions-macho64-new (target
                                 position-independentp
                                 stack-slots-needed
                                 state-var
                                 inputs
                                 type-assumptions-for-array-varsp
                                 inputs-disjoint-from
                                 bvp
                                 new-canonicalp
                                 parsed-macho)
  (declare (xargs :guard (and (lifter-targetp target)
                              (booleanp position-independentp)
                              (natp stack-slots-needed)
                              (symbolp state-var) ; todo: too strict?
                              (names-and-typesp inputs)
                              (booleanp type-assumptions-for-array-varsp)
                              (member-eq inputs-disjoint-from '(nil :code :all))
                              (booleanp bvp)
                              (booleanp new-canonicalp)
                              (acl2::parsed-mach-o-p parsed-macho))
                  :guard-hints (("Goal" :in-theory (enable acl2::parsed-mach-o-p acl2::true-listp-when-pseudo-term-listp-2)))))
  (b* ((base-var 'base-address) ; arbitrary base address, only used if position-independentp
       ;; Decide where to start lifting:
       (target-offset (if (eq :entry-point target)
                          (er hard? 'assumptions-macho64-new ":entry-point is not yet supported for MACH-O files.") ;; (acl2::parsed-elf-entry-point parsed-elf) ; todo
                        (if (natp target)
                            target ; explicit address given (relative iff position-independentp)
                          ;; target is the name of a function:
                          (ec-call (acl2::subroutine-address-mach-o target parsed-macho)) ; todo on the ec-call
                          )))
       ((when (not (natp target-offset)))
        (er hard? 'assumptions-macho64-new "Bad or missing lift target offset: ~x0." target-offset)
        (mv :bad-or-missing-subroutine-address nil nil))
       ;; Make the standard assumptions:
       (standard-assumptions (make-standard-assumptions64-new stack-slots-needed state-var base-var target-offset position-independentp bvp new-canonicalp))
       ;; Gather memory-regions to assume loaded:
       ((mv erp regions-to-load) (macho64-regions-to-load parsed-macho)) ; these use absolute addresses
       ((when erp) (mv erp nil nil))
       ;; Checks that there is at least one load segment:
       ((when (not (consp regions-to-load)))
        (mv :no-memory-regions-found-in-executable nil nil))
       ;; Generate assumptions for the regions (bytes are loaded, addresses are canonical, regions are disjoint from future stack words):
       ((mv erp memory-region-assumptions)
        (assumptions-for-memory-regions regions-to-load base-var state-var stack-slots-needed bvp position-independentp new-canonicalp nil))
       ((when erp) (mv erp nil nil))
       ;; Decide which memory regions to assume disjoint from the inputs:
       ((mv erp addresses-and-lens-of-chunks-disjoint-from-inputs)
        (if (eq nil inputs-disjoint-from)
            ;; Don't assume the inputs are disjoint from anything:
            (mv nil nil)
          (if (eq :all inputs-disjoint-from)
              ;; Assume the inputs are disjoint from all the sections/segments in the executable::
              ;; Warning: This is quite strong: an input to the function being lifted may very well be in a data section or in the stack!):
              (mv nil (memory-region-addresses-and-lens regions-to-load nil))
            ;; inputs-disjoint-from must be :code, so assume the inputs are disjoint from the code bytes only:
            ;; todo: what if there are segments but no sections?  could use the segment that contains the text section, if we can find it, or throw an error.
            ;; could allow the user to specify exactly which regions to assume disjoint from the assumptions.
            (b* ((code-address (acl2::ec-call (acl2::get-mach-o-code-address parsed-macho))) ;todo on the ec-call
                 ((when (not (natp code-address))) ; impossible?
                  (mv :bad-code-addres nil))
                 (text-offset-term (if position-independentp
                                       (if bvp
                                           (symbolic-bvplus-constant 48 code-address base-var)
                                         (symbolic-add-constant code-address base-var))
                                     code-address)))
              ; todo: could there be extra zeros?:
              (mv nil (acons text-offset-term (len (acl2::ec-call (acl2::get-mach-o-code parsed-macho))) nil)))))) ; todo on the ec-call
       ((when erp) (mv erp nil nil))
       ;; Generate assumptions for the inputs (introduce vars, canonical, disjointness from future stack space, disjointness from bytes loaded from the executable, disjointness from saved return address):
       ((mv input-assumptions input-assumption-vars)
        (if (equal inputs :skip)
            (mv nil nil)
          (assumptions-and-vars-for-inputs inputs ; tttodo: do we assume inputs disjoint from the stack?
                                           ;; todo: handle zmm regs and values passed on the stack?!:
                                           ;; handle structs that fit in 2 registers?
                                           ;; See the System V AMD64 ABI
                                           '((rdi x86) (rsi x86) (rdx x86) (rcx x86) (r8 x86) (r9 x86))
                                           stack-slots-needed
                                           addresses-and-lens-of-chunks-disjoint-from-inputs
                                           type-assumptions-for-array-varsp
                                           nil nil
                                           new-canonicalp))))
    (mv nil ; no error
        (append standard-assumptions
                memory-region-assumptions
                input-assumptions)
        input-assumption-vars)))

(defthm true-list-of-mv-nth-1-of-assumptions-macho64-new
  (true-listp (mv-nth 1 (assumptions-macho64-new target position-independentp stack-slots-needed state-var inputs type-assumptions-for-array-varsp inputs-disjoint-from bvp new-canonicalp parsed-macho)))
  :hints (("Goal" :in-theory (enable assumptions-macho64-new))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund assumptions-pe64-new (target
                              position-independentp
                              stack-slots-needed
                              state-var
                              inputs
                              type-assumptions-for-array-varsp
                              inputs-disjoint-from
                              bvp
                              new-canonicalp
                              parsed-pe)
  (declare (xargs :guard (and (lifter-targetp target)
                              (booleanp position-independentp)
                              (natp stack-slots-needed)
                              (symbolp state-var) ; todo: too strict?
                              (names-and-typesp inputs)
                              (booleanp type-assumptions-for-array-varsp)
                              (member-eq inputs-disjoint-from '(nil :code :all))
                              (booleanp bvp)
                              (booleanp new-canonicalp)
                              (acl2::parsed-pe-p parsed-pe))
                  :verify-guards nil ; todo
                  :guard-hints (("Goal" :in-theory (enable acl2::parsed-pep acl2::true-listp-when-pseudo-term-listp-2)))))
  (b* ((base-var 'base-address) ; arbitrary base address, only used if position-independentp
       ;; Decide where to start lifting:
       (target-offset (if (eq :entry-point target)
                          (acl2::get-pe-entry-point parsed-pe)
                        (if (natp target)
                            target ; explicit address given (relative iff position-independentp)
                          ;; target is the name of a function:
                          (acl2::subroutine-address-pe-64 target parsed-pe))))
       ((when (not (natp target-offset)))
        (er hard? 'assumptions-pe64-new "Bad or missing lift target offset: ~x0." target-offset)
        (mv :bad-or-missing-subroutine-address nil nil))
       ;; Make the standard assumptions:
       (standard-assumptions (make-standard-assumptions64-new stack-slots-needed state-var base-var target-offset position-independentp bvp new-canonicalp))
       ;; Gather memory-regions to assume loaded:
       ((mv erp regions-to-load) (pe64-regions-to-load parsed-pe)) ; these use absolute addresses
       ((when erp) (mv erp nil nil))
       ;; Checks that there is at least one section to be loaded:
       ((when (not (consp regions-to-load)))
        (mv :no-memory-regions-found-in-executable nil nil))
       ;; Generate assumptions for the regions (bytes are loaded, addresses are canonical, regions are disjoint from future stack words):
       ((mv erp memory-region-assumptions)
        (assumptions-for-memory-regions regions-to-load base-var state-var stack-slots-needed bvp position-independentp new-canonicalp nil))
       ((when erp) (mv erp nil nil))
       ;; Decide which memory regions to assume disjoint from the inputs:
       ((mv erp addresses-and-lens-of-chunks-disjoint-from-inputs)
        (if (eq nil inputs-disjoint-from)
            ;; Don't assume the inputs are disjoint from anything:
            (mv nil nil)
          (if (eq :all inputs-disjoint-from)
              ;; Assume the inputs are disjoint from all the sections/segments in the executable::
              ;; Warning: This is quite strong: an input to the function being lifted may very well be in a data section or in the stack!):
              (mv nil (memory-region-addresses-and-lens regions-to-load nil))
            ;; inputs-disjoint-from must be :code, so assume the inputs are disjoint from the code bytes only:
            ;; todo: what if there are segments but no sections?  could use the segment that contains the text section, if we can find it, or throw an error.
            ;; could allow the user to specify exactly which regions to assume disjoint from the assumptions.
            (b* ((code-address (acl2::get-pe-section-rva ".text" parsed-pe))
                 ((when (not (natp code-address))) ; impossible?
                  (mv :bad-code-addres nil))
                 (text-offset-term (if position-independentp
                                       (if bvp
                                           (symbolic-bvplus-constant 48 code-address base-var)
                                         (symbolic-add-constant code-address base-var))
                                     code-address)))
              ; todo: could there be extra zeros?:
              (mv nil (acons text-offset-term (len (acl2::get-pe-text-section-bytes parsed-pe)) nil))))))
       ((when erp) (mv erp nil nil))
       ;; Generate assumptions for the inputs (introduce vars, canonical, disjointness from future stack space, disjointness from bytes loaded from the executable, disjointness from saved return address):
       ((mv input-assumptions input-assumption-vars)
        (if (equal inputs :skip)
            (mv nil nil)
          (assumptions-and-vars-for-inputs inputs ; tttodo: do we assume inputs disjoint from the stack?
                                           ;; todo: handle zmm regs and values passed on the stack?!:
                                           ;; handle structs that fit in 2 registers?
                                           ;; See the System V AMD64 ABI
                                           '((rdi x86) (rsi x86) (rdx x86) (rcx x86) (r8 x86) (r9 x86))
                                           stack-slots-needed
                                           addresses-and-lens-of-chunks-disjoint-from-inputs
                                           type-assumptions-for-array-varsp
                                           nil nil
                                           new-canonicalp))))
    (mv nil ; no error
        (append standard-assumptions
                memory-region-assumptions
                input-assumptions)
        input-assumption-vars)))

(defthm true-list-of-mv-nth-1-of-assumptions-pe64-new
  (true-listp (mv-nth 1 (assumptions-pe64-new target position-independentp stack-slots-needed state-var inputs type-assumptions-for-array-varsp inputs-disjoint-from bvp new-canonicalp parsed-pe)))
  :hints (("Goal" :in-theory (enable assumptions-pe64-new))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: redo this like elf64-section-loadedp. ??
;; Returns (mv erp assumptions).
(defun make-section-assumptions-mach-o-64 (segment-name
                                           section-name
                                           parsed-mach-o
                                           relp
                                           stack-slots-needed
                                           bvp
                                           base-var
                                           state-var)
  (declare (xargs :guard (and (stringp segment-name)
                              (stringp section-name)
                              ;; parsed-mach-o
                              (booleanp relp)
                              (natp stack-slots-needed)
                              (booleanp bvp)
                              (symbolp base-var)
                              (symbolp state-var))
                  :verify-guards nil ;todo
                  ))
  (if (acl2::mach-o-section-presentp segment-name section-name parsed-mach-o)
      (let* ((segment (acl2::get-mach-o-segment segment-name (acl2::lookup-eq-safe :cmds parsed-mach-o)))
             (section (acl2::get-mach-o-section section-name (acl2::lookup-eq-safe :SECTIONS segment)))
             (section-bytes (acl2::lookup-eq-safe :contents section))
             (section-offset (acl2::lookup-eq-safe :addr section))
             ;(text-section-address (acl2::get-mach-o-code-address parsed-mach-o))
             ;; todo: can this be negative?:
             ;(section-offset-from-text (- section-address text-section-address))
             ;; (section-start (+ section-offset
             ;;                   base-address))
             )
        ;; (and (bytes-loaded-at-address-64 section-bytes section-start bvp x86)
        ;;      ;; (canonical-address-p$inline const-section-start)
        ;;      ;; (canonical-address-p$inline (+ -1 (len const-section-bytes) const-section-start))
        ;;      ;; The constant data is disjoint from the part of the stack that is written:
        ;;      (if bvp
        ;;          (disjoint-regions48p (len section-bytes) section-start
        ;;                               ;; Only a single stack slot is written
        ;;                               ;;old: (create-canonical-address-list 8 (+ -8 (rgfi *rsp* x86)))
        ;;                               (* 8 stack-slots-needed) (+ (* -8 stack-slots-needed) (rsp x86)))
        ;;        (separate :r (len section-bytes) section-start
        ;;                  ;; Only a single stack slot is written
        ;;                  ;;old: (create-canonical-address-list 8 (+ -8 (rgfi *rsp* x86)))
        ;;                  :r (* 8 stack-slots-needed) (+ (* -8 stack-slots-needed) (rsp x86))))))
        (assumptions-for-memory-chunk section-offset section-bytes relp state-var base-var stack-slots-needed bvp t ;new-canonicalp
                                      ))
    ;; no assumptions if section not present: ; todo: print a warning
    (mv nil
        nil)))
