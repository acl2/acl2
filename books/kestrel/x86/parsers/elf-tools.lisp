; Tools for processing the alists that represent parsed ELF files.
;
; Copyright (C) 2022-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/x86/portcullis" :dir :system) ; for the package
(include-book "parse-elf-file") ; overkill?  brings in get-elf-section-header.  really that book should include this one?
(include-book "kestrel/utilities/file-existsp" :dir :system)
(include-book "kestrel/file-io-light/read-file-into-byte-list" :dir :system)
;(include-book "kestrel/utilities/defopeners" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/alists-light/lookup-equal-safe" :dir :system)
(include-book "kestrel/memory/memory-regions" :dir :system)
(include-book "kestrel/lists-light/repeat-def" :dir :system)
(local (include-book "kestrel/bv-lists/byte-listp" :dir :system))
(local (include-book "kestrel/bv-lists/byte-listp2" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/repeat" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

;; todo: use the section-header-table?
(defund elf-section-presentp (section-name parsed-elf)
  (declare (xargs :guard (and (stringp section-name)
                              (parsed-elfp parsed-elf))
                  :guard-hints (("Goal" :in-theory (enable parsed-elfp)))))
  (if (assoc-equal section-name (lookup-eq :sections parsed-elf)) t nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund get-elf-section-bytes (section-name parsed-elf)
  (declare (xargs :guard (and (stringp section-name)
                              (parsed-elfp parsed-elf))
                  :guard-hints (("Goal" :in-theory (enable parsed-elfp)))))
  (let ((res (lookup-equal-safe section-name (lookup-eq-safe :sections parsed-elf))))
    (if (not (byte-listp res))
        (er hard? 'get-elf-section-bytes "Non-bytes found.") ; todo: prove that this doesn't happen.  maybe redo the sections to not have their bytes stored?
      res)))

(defthm byte-listp-of-get-elf-section-bytes
  (implies (parsed-elfp parsed-elf)
           (byte-listp (get-elf-section-bytes section-name parsed-elf)))
  :hints (("Goal" :in-theory (enable get-elf-section-bytes parsed-elfp))))


;; Get the code from the .text section:
(defund get-elf-code (parsed-elf)
  (declare (xargs :guard (parsed-elfp parsed-elf)))
  (get-elf-section-bytes ".text" parsed-elf))

;; Returns the :addr field of the header with the give SECTION-NAME, or :none
(defund get-elf-section-address (section-name parsed-elf)
  (declare (xargs :guard (and (stringp section-name)
                              (parsed-elfp parsed-elf))
                  :guard-hints (("Goal" :in-theory (enable parsed-elfp)))))
  (let ((header (get-elf-section-header section-name (lookup-eq-safe :section-header-table parsed-elf))))
    (if (eq :none header)
        :none
      (lookup-eq-safe :addr header))))

;; Returns the :addr field of the ".text" section, or :none.
(defund get-elf-text-section-address (parsed-elf)
  (declare (xargs :guard (parsed-elfp parsed-elf)
                  :guard-hints (("Goal" :in-theory (enable parsed-elfp)))))
  (let ((addr (get-elf-section-address ".text" parsed-elf)))
    (if (eq :none addr)
        (er hard? 'get-elf-text-section-address "No .text section.") ;; todo: instead, return :none
      addr)))

;; Throws an error if the symbol has multiple matches
(defund get-elf-symbol-address-aux (name symbol-table)
  (declare (xargs :guard (and (stringp name)
                              (elf-symbol-tablep symbol-table))
                  :guard-hints (("Goal" :in-theory (enable elf-symbol-tablep)))))
  (if (endp symbol-table)
      nil ; not found
    (let* ((entry (first symbol-table))
           (this-name (lookup-eq-safe :name entry)))
      (if (equal this-name name)
          (if (get-elf-symbol-address-aux name (rest symbol-table))
              (er hard? 'get-elf-symbol-address-aux "Multiple matches in symbol table for ~s0." name)
            (lookup-eq-safe :value entry) ; assumes it is not a relocatable file
            )
        (get-elf-symbol-address-aux name (rest symbol-table))))))

;; Throws an error if the symbol is not found or has multiple matches
(defund get-elf-symbol-address (name symbol-table)
  (declare (xargs :guard (and (stringp name)
                              (elf-symbol-tablep symbol-table))))
  (let ((result (get-elf-symbol-address-aux name symbol-table)))
    (if (not result)
        (er hard? 'get-elf-symbol-address "Can't find ~s0 in symbol table." name)
      result)))

(defund get-names-from-elf-symbol-table (symbol-table acc)
  (declare (xargs :guard (and (elf-symbol-tablep symbol-table)
                              (true-listp acc))
                  :guard-hints (("Goal" :in-theory (enable elf-symbol-tablep)))))
  (if (endp symbol-table)
      (reverse acc)
    (let* ((entry (first symbol-table))
           (name (lookup-eq-safe :name entry)))
      (get-names-from-elf-symbol-table (rest symbol-table)
                                       (if (stringp name) ; skips :no-name
                                           (cons name acc)
                                         acc)))))

(defopeners get-elf-symbol-address-aux)

(defund parsed-elf-symbol-table (parsed-elf)
  (declare (xargs :guard (parsed-elfp parsed-elf)))
  (lookup-eq-safe :symbol-table parsed-elf))

;; Throws an error if not found
(defund subroutine-address-elf (name parsed-elf)
  (declare (xargs :guard (and (stringp name)
                              (parsed-elfp parsed-elf))
                  :guard-hints (("Goal" :in-theory (enable parsed-elf-symbol-table
                                                           parsed-elfp)))))
  (get-elf-symbol-address name (parsed-elf-symbol-table parsed-elf)))

(defund parsed-elf-symbols (parsed-elf)
  (declare (xargs :guard (parsed-elfp parsed-elf)
                  :guard-hints (("Goal" :in-theory (enable parsed-elfp parsed-elf-symbol-table)))))
  (get-names-from-elf-symbol-table (parsed-elf-symbol-table parsed-elf) nil))

;; :rel or :exec or :dyn, etc.
(defund parsed-elf-type (parsed-elf)
  (declare (xargs :guard (parsed-elfp parsed-elf)))
  (lookup-eq :type parsed-elf))

(defund parsed-elf-cpu-type (parsed-elf)
  (declare (xargs :guard (parsed-elfp parsed-elf)))
  (lookup-eq :machine parsed-elf))

(defund parsed-elf-entry-point (parsed-elf)
  (declare (xargs :guard (parsed-elfp parsed-elf)))
  (lookup-eq :entry parsed-elf))

;; all the bytes in the file, for looking up the bytes of the segments
(defund parsed-elf-bytes (parsed-elf)
  (declare (xargs :guard (parsed-elfp parsed-elf)))
  (lookup-eq :bytes parsed-elf))

(defthm byte-listp-of-parsed-elf-bytes
  (implies (parsed-elfp parsed-elf)
           (byte-listp (parsed-elf-bytes parsed-elf)))
  :hints (("Goal" :in-theory (enable parsed-elf-bytes parsed-elfp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Only checks segments whose :type is :pt_load.
(defund elf-program-header-table-entries-disjoint-fromp (start size pht)
  (declare (xargs :guard (and (natp start)
                              (natp size)
                              (elf-program-header-tablep pht))
                  :guard-hints (("Goal" :in-theory (enable elf-program-header-tablep
                                                           elf-program-header-table-entryp)))))
  (if (endp pht)
      t
    (let* ((entry (first pht))
           (entry-start (lookup-eq :vaddr entry))
           (entry-size (lookup-eq :memsz entry))
           (type (lookup-eq :memsz entry)))
      ;; we checked elsewhere that these calculations don't wrap:
      (if (or (not (eq :pt_load type)) ; only check for disjointness of load segments
              (<= (+ start size) entry-start)
              (<= (+ entry-start entry-size) start))
          (elf-program-header-table-entries-disjoint-fromp start size (rest pht))
        (prog2$ (cw "Overlapping entries in program-header-table.  First start/size: ~x0/~x1.  Second start/size: ~x2/~x3." start size entry-start entry-size)
                nil)))))

(defund elf-program-header-table-okp (pht)
  (declare (xargs :guard (elf-program-header-tablep pht)
                  :guard-hints (("Goal" :in-theory (enable elf-program-header-tablep
                                                           elf-program-header-table-entryp)))))
  (if (endp pht)
      t
    (let* ((entry (first pht))
           (start (lookup-eq :vaddr entry))
           (size (lookup-eq :memsz entry))
           (type (lookup-eq :memsz entry)))
      (and (if (eq :pt_load type) ; only check for disjointness of load segments
               (elf-program-header-table-entries-disjoint-fromp start size (rest pht))
             t)
           (elf-program-header-table-okp (rest pht))))))

;; Extracts the program-header-table from the parsed ELF file.
;; Also checks that no segments overlap
(defund parsed-elf-program-header-table (parsed-elf)
  (declare (xargs :guard (parsed-elfp parsed-elf)
                  :guard-hints (("Goal" :in-theory (enable parsed-elfp)))))
  (let ((pht (lookup-eq :program-header-table parsed-elf)))
    (if (not (elf-program-header-table-okp pht)) ; todo: move this check?
        (er hard? 'parsed-elf-program-header-table "Bad program-header-table (some entries overlap): ~X01." pht nil)
      pht)))

(defthm program-header-tablep-of-parsed-elf-program-header-table
  (implies (parsed-elfp parsed-elf)
           (elf-program-header-tablep (parsed-elf-program-header-table parsed-elf)))
  :hints (("Goal" :in-theory (enable parsed-elf-program-header-table parsed-elfp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Parses an ELF executable.
;; Returns (mv erp contents state) where contents in an alist representing
;; the contents of the executable.
(defund parse-elf (filename state)
  (declare (xargs :guard (stringp filename)
                  :stobjs state))
  (b* (((mv existsp state) (file-existsp filename state))
       ((when (not existsp))
        (progn$ (er hard? 'parse-elf "File ~x0 does not exist." filename)
                (mv t nil state)))
       ((mv erp bytes state) (read-file-into-byte-list filename state))
       ((when erp) (mv erp nil state))
       ((mv erp magic-number) (parse-executable-magic-number bytes filename))
       ((when erp) (mv erp nil state))
       ((when (not (= magic-number *elf-magic-number*)))
        (er hard? 'parse-elf "File ~x0 does not appear to be an ELF file." filename)
        (mv t nil state))
       ((mv erp parsed-elf)
        (parse-elf-file-bytes bytes)))
    (mv erp parsed-elf state)))

(defthm parsed-elfp-of-mv-nth-1-of-parse-elf
  (implies (not (mv-nth 0 (parse-elf filename state))) ; no error
           (parsed-elfp (mv-nth 1 (parse-elf filename state))))
  :hints (("Goal" :in-theory (enable parse-elf))))

;; Reads the given ELF file and returns some info about it, or returns an error.
;; Returns an error triple (mv erp info state).
(defund elf-info-fn (filename state)
  (declare (xargs :guard (stringp filename)
                  :stobjs state
                  :guard-hints (("Goal" :in-theory (enable alistp-when-parsed-elfp)))))
  (b* (((mv erp parsed-elf state) (parse-elf filename state))
       ((when erp) (mv erp nil state))
       ;; (sections (lookup-eq-safe :sections parsed-elf))
       ;; (section-names (strip-cars sections))
       (info nil) ; to be extended below
       ;; TODO: Or just clear out the :bytes and :sections (which might be huge)
       (info (acons :type (lookup-eq-safe :type parsed-elf) info))
       (info (acons :machine (lookup-eq-safe :machine parsed-elf) info))
       (info (acons :entry (lookup-eq-safe :entry parsed-elf) info))
       (info (acons :section-header-table (lookup-eq-safe :section-header-table parsed-elf) info))
       (info (acons :program-header-table (lookup-eq-safe :program-header-table parsed-elf) info))
       (info (acons :symbol-table (lookup-eq-safe :symbol-table parsed-elf) info))
       ;(info (acons :sections sections info))
       ;; todo: extract more info, like section sizes
       (info (reverse info)))
    (mv nil info state)))

(defmacro elf-info (filename)
  `(elf-info-fn ,filename state))

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
    (implies (and (x::memory-regionsp acc)
                  (acl2::byte-listp all-bytes)
                  (equal all-bytes-len (len all-bytes)))
             (x::memory-regionsp (mv-nth 1 (elf64-regions-to-load-aux program-header-table all-bytes-len all-bytes acc))))
    :hints (("Goal" :in-theory (enable elf64-regions-to-load-aux x::memory-regionsp x::memory-regionp)))))

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

(defthm memory-regionsp-of-mv-nth-1-of-elf64-regions-to-load
  (implies (acl2::parsed-elfp parsed-elf)
           (x::memory-regionsp (mv-nth 1 (elf64-regions-to-load parsed-elf))))
  :hints (("Goal" :in-theory (enable elf64-regions-to-load))))
