; A parser for ELF executables
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See https://refspecs.linuxfoundation.org/elf/elf.pdf
;; and
;; https://www.uclibc.org/docs/elf-64-gen.pdf

(include-book "parser-utils")
(include-book "kestrel/alists-light/lookup-equal-safe" :dir :system)
(include-book "kestrel/alists-light/lookup" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(include-book "kestrel/alists-light/lookup-safe" :dir :system)
(include-book "kestrel/bv-lists/byte-listp" :dir :system)
(include-book "kestrel/utilities/defopeners" :dir :system)
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))

(defconst *elf-magic-number* #x464C457F) ; 7F"ELF" (but note the byte order)

(defconst *classes*
  `(;; (0 . :invalid)
    (1 . :elfclass32)
    (2 . :elfclass64)))

(defconst *data-encodings*
  `(;; (0 . :invalid)
    (1 . :elfdata2lsb)
    (2 . :elfdata2msb)))

(defconst *osabis*
  `((0 . :elfosabi_sysv)
    (1 . :elfosabi_hpux)
    (255 . :elfosabi_standalone)))

(defconst *elf-file-types* ; acl2::*file-types* is already defined
  `((0 . :none)
    (1 . :rel)
    (2 . :exec)
    (3 . :dyn)
    (4 . :core)
    (#xfe00 . :loos)
    (#xfeff . :hios)
    (#xff00 . :loproc)
    (#xffff . :hiproc)))

;; Returns (mv item bytes).
(defun parse-half (bytes)
  (declare (xargs :guard (byte-listp bytes)
                  :verify-guards nil
                  ))
  (parse-u16 bytes))

;; Returns (mv item bytes).
(defun parse-word (bytes)
  (declare (xargs :guard (byte-listp bytes)
                  :verify-guards nil
                  ))
  (parse-u32 bytes))

;; Returns (mv item bytes).
(defun parse-addr (64bitp bytes)
  (declare (xargs :guard (and (booleanp 64bitp)
                              (byte-listp bytes))
                  :verify-guards nil
                  ))
  (if 64bitp (parse-u64 bytes) (parse-u32 bytes)))

;; Returns (mv item bytes).
(defun parse-offset (64bitp bytes)
  (declare (xargs :guard (and (booleanp 64bitp)
                              (byte-listp bytes))
                  :verify-guards nil
                  ))
  (parse-addr 64bitp bytes))

;; Returns (mv item bytes).
(defun parse-xword (bytes)
  (declare (xargs :guard (byte-listp bytes)
                  :verify-guards nil
                  ))
  (parse-u64 bytes))

(defun parse-string-chars (bytes acc)
  (if (endp bytes)
      (er hard? 'parse-string-chars "Ran out of bytes.")
    (let ((byte (first bytes)))
      (if (= 0 byte)
          (reverse acc)
        (parse-string-chars (rest bytes) (cons (code-char byte) acc))))))

(defun parse-string (bytes)
  (coerce (parse-string-chars bytes nil) 'string))

(defconst *sh-types*
  '((0 . :sht-null)
    (1 . :sht-progbits)
    (2 . :sht-symtab)
    (3 . :sht-strtab)
    (4 . :sht-rela)
    (5 . :sht-hash)
    (6 . :sht-dynamic)
    (7 . :sht-note)
    (8 . :sht-nobits)
    (9 . :sht-rel)
    (10 . :sht-shlib)
    (11 . :sht-dynsym)
    ;; todo: handle the ranges
    ))

;; Returns (mv section-header bytes).
(defun parse-elf-section-header (64-bitp bytes)
  (b* ((result nil)
       ((mv sh_name bytes) (parse-word bytes))
       (result (acons :name-offset sh_name result))
       ((mv sh_type bytes) (parse-word bytes))
       (type (let ((res (lookup sh_type *sh-types*)))
               (or res :unknown)))
       (result (acons :type type result))
       ((mv sh_flags bytes) (parse-xword bytes))
       (result (acons :flags sh_flags result))
       ((mv sh_addr bytes) (parse-addr 64-bitp bytes))
       (result (acons :addr sh_addr result))
       ((mv sh_offset bytes) (parse-offset 64-bitp bytes))
       (result (acons :offset sh_offset result))
       ((mv sh_size bytes) (if 64-bitp (parse-xword bytes) (parse-word bytes)))
       (result (acons :size sh_size result))
       ((mv sh_link bytes) (parse-word bytes))
       (result (acons :link sh_link result))
       ((mv sh_info bytes) (parse-word bytes))
       (result (acons :info sh_info result))
       ((mv sh_addralign bytes) (if 64-bitp (parse-xword bytes) (parse-word bytes)))
       (result (acons :addralign sh_addralign result))
       ((mv sh_entsize bytes) (if 64-bitp (parse-xword bytes) (parse-word bytes)))
       (result (acons :entsize sh_entsize result)))
    (mv (reverse result) bytes)))

;; Returns the section headers
(defun parse-elf-section-headers (index count 64-bitp acc bytes)
  (declare (xargs :measure (nfix (- count index))))
  (if (or (<= count index)
          (not (natp index))
          (not (natp count)))
      (reverse acc)
    (mv-let (section-header bytes)
      (parse-elf-section-header 64-bitp bytes)
      (parse-elf-section-headers (+ 1 index)
                             count
                             64-bitp
                             (acons index section-header acc)
                             bytes))))

(defun assign-section-header-names (section-header-table string-table-bytes acc)
  (if (endp section-header-table)
      (reverse acc)
    (let* ((entry (first section-header-table))
           (index (car entry))
           (section-header (cdr entry))
           (name-offset (lookup-eq-safe :name-offset section-header))
           (name (parse-string (nthcdr name-offset string-table-bytes)))
           (section-header (acons :name name section-header)))
      (assign-section-header-names (rest section-header-table)
                                   string-table-bytes
                                   (acons index section-header acc)))))


(defun symtab-offset-and-size (section-header-table)
  (if (endp section-header-table)
      (prog2$ (er hard? 'symtab-offset-and-size "No symbol table found.") ; todo: what about a stripped binary?
              (mv 0 0))
    (let* ((entry (first section-header-table))
           (section-header (cdr entry))
           (type (lookup-eq-safe :type section-header)))
      (if (eq type :sht-symtab)
          (mv (lookup-eq-safe :offset section-header)
              (lookup-eq-safe :size section-header))
        (symtab-offset-and-size (rest section-header-table))))))

(defun get-elf-section-header (name section-header-table)
  (if (endp section-header-table)
      (er hard? 'get-elf-section-header "No section header found for ~x0." name)
    (let* ((entry (first section-header-table))
           ;; (index (car entry))
           (section-header (cdr entry))
           (this-name (lookup-eq-safe :name section-header)))
      (if (equal this-name name)
          section-header
        (get-elf-section-header name (rest section-header-table))))))

(defopeners get-elf-section-header) ; move?

(defun strtab-offset (section-header-table)
  (lookup-eq-safe :offset (get-elf-section-header ".strtab" section-header-table)))

(defun parse-elf-symbol-table-entry (64-bitp string-table-bytes-etc bytes)
  (b* ((result nil)
       ((mv st_name bytes) (parse-word bytes)) ; actually an offset
       (result (acons :name-offset st_name result))
       (name (if (= 0 st_name)
                 :no-name
               (parse-string (nthcdr st_name string-table-bytes-etc))))
       (result (acons :name name result))
       ((mv st_info bytes) (parse-u8 bytes))
       (result (acons :info st_info result))
       ((mv st_other bytes) (parse-u8 bytes))
       (result (acons :other st_other result))
       ((mv st_shndx bytes) (parse-half bytes))
       (result (acons :shndx st_shndx result))
       ((mv st_value bytes) (parse-addr 64-bitp bytes))
       (result (acons :value st_value result))
       ((mv st_size bytes) (parse-xword bytes))
       (result (acons :size st_size result)))
    (mv (reverse result) bytes)))

(defun parse-elf-symbol-table (symbol-table-size 64-bitp string-table-bytes-etc acc bytes)
  (declare (xargs :measure (len bytes)))
  (if (zp symbol-table-size)
      (reverse acc)
    (if (< (len bytes) 24) ; todo: optimize
        (er hard? 'parse-elf-symbol-table "Not enough bytes.")
      (mv-let (symbol-table-entry bytes)
        (parse-elf-symbol-table-entry 64-bitp string-table-bytes-etc bytes)
        (parse-elf-symbol-table (- symbol-table-size 24)
                                64-bitp
                                string-table-bytes-etc
                                (cons symbol-table-entry acc)
                                bytes)))))

(defun extract-elf-sections (section-header-table all-bytes acc)
  (if (endp section-header-table)
      (reverse acc)
    (let* ((entry (first section-header-table))
           ;; (index (car entry))
           (section-header (cdr entry))
           (name (lookup-eq-safe :name section-header))
           (offset (lookup-eq-safe :offset section-header))
           (size (lookup-eq-safe :size section-header))
           (bytes (take-safe size (nthcdr offset all-bytes))))
      (extract-elf-sections (rest section-header-table) all-bytes
                            (acons name bytes acc)))))

(defun parse-elf-file-bytes (bytes)
  (b* ((all-bytes bytes) ;capture for later looking up things at given offsets
       (result nil) ; empty alist
       ((mv e_ident bytes) (parse-n-bytes 16 bytes))
       (elfmag0 (nth 0 e_ident))
       (elfmag1 (nth 1 e_ident))
       (elfmag2 (nth 2 e_ident))
       (elfmag3 (nth 3 e_ident))
       ((when (not (and (= #x7F elfmag0)
                        (= (char-code #\E) elfmag1)
                        (= (char-code #\L) elfmag2)
                        (= (char-code #\F) elfmag3))))
        (er hard? 'parse-elf-file-bytes "Bad magic number: ~x0." (take 4 e_ident)))
       (ei_class (nth 4 e_ident))
       (class (lookup-safe ei_class *classes*))
       (64-bitp (eq :elfclass64 class))
       (result (acons :class class result))
       ;; Now we can set the magic number:
       (result (acons :magic (if :elfclass64 :elf-64 :elf-32) result)) ; for use by parsed-executable-type
       (ei_data (nth 5 e_ident))
       (data (lookup-safe ei_data *data-encodings*))
       (result (acons :data data result))
       (ei_version (nth 6 e_ident))
       (result (acons :version ei_version result))
       (ei_osabi (nth 7 e_ident))
       (osabi (lookup-safe ei_osabi *osabis*))
       (result (acons :osabi osabi result))
       (ei_abiversion (nth 8 e_ident))
       (result (acons :abiversion ei_abiversion result))
       ((mv e_type bytes) (parse-half bytes)) ; todo: consider endianness for these values
       (type (lookup-safe e_type *elf-file-types*))
       (result (acons :type type result))
       ((mv e_machine bytes) (parse-half bytes)) ; todo: decode
       (result (acons :machine e_machine result))
       ((mv e_version bytes) (parse-word bytes))
       (result (acons :version e_version result))
       ((mv e_entry bytes) (parse-addr 64-bitp bytes))
       (result (acons :entry e_entry result))
       ((mv e_phoff bytes) (parse-offset 64-bitp bytes))
       (result (acons :phoff e_phoff result))
       ((mv e_shoff bytes) (parse-offset 64-bitp bytes))
       (result (acons :shoff e_shoff result))
       ((mv e_flags bytes) (parse-word bytes))
       (result (acons :flags e_flags result))
       ((mv e_ehsize bytes) (parse-half bytes))
       (result (acons :ehsize e_ehsize result))
       ((mv e_phentsize bytes) (parse-half bytes))
       (result (acons :phentsize e_phentsize result))
       ((mv e_phnum bytes) (parse-half bytes))
       (result (acons :phnum e_phnum result))
       ((mv e_shentsize bytes) (parse-half bytes))
       (result (acons :shentsize e_shentsize result))
       ((mv e_shnum bytes) (parse-half bytes))
       (result (acons :shnum e_shnum result))
       ((mv e_shstrndx & ;bytes
            ) (parse-half bytes))
       (result (acons :shstrndx e_shstrndx result))
       ;; Parse the section header table:
       (section-header-table-without-names (parse-elf-section-headers 0 e_shnum 64-bitp nil (nthcdr e_shoff all-bytes)))
       ;; Add the names to the section headers:
       (section-name-string-table-header (lookup-safe e_shstrndx section-header-table-without-names))
       (section-name-string-table-header-offset (lookup-eq-safe :offset section-name-string-table-header))
       (section-header-table (assign-section-header-names section-header-table-without-names
                                                          (nthcdr section-name-string-table-header-offset all-bytes)
                                                          nil))
       (result (acons :section-header-table section-header-table result))
       ((mv symbol-table-offset symbol-table-size) (symtab-offset-and-size section-header-table))
       (string-table-offset (strtab-offset section-header-table))
       (string-table-bytes-etc (nthcdr string-table-offset all-bytes))
       (symbol-table (parse-elf-symbol-table symbol-table-size 64-bitp string-table-bytes-etc nil (nthcdr symbol-table-offset all-bytes)))
       (result (acons :symbol-table symbol-table result))
       (sections (extract-elf-sections section-header-table all-bytes nil))
       (result (acons :sections sections result))
       )
    (reverse result)))

;; todo: move this stuff?:

;; Get the code from the .text section:
(defun get-elf-code (parsed-elf)
  (lookup-equal-safe ".text" (lookup-eq-safe :sections parsed-elf)))

(defun get-elf-code-address (parsed-elf)
  (lookup-eq-safe :addr (get-elf-section-header ".text" (lookup-eq-safe :section-header-table parsed-elf))))

(defun get-elf-symbol-address (name symbol-table)
  (if (endp symbol-table)
      (er hard? 'get-elf-symbol-address "Can't find ~s0 in symbol table." name)
    (let* ((entry (first symbol-table))
           (this-name (lookup-eq-safe :name entry)))
      (if (equal this-name name)
          (lookup-eq-safe :value entry) ; assumes it is not a relocatable file
        (get-elf-symbol-address name (rest symbol-table))))))

(defopeners get-elf-symbol-address)

;; Throws an error if not found
(defun subroutine-address-elf (name parsed-elf)
  (get-elf-symbol-address name (lookup-eq-safe :symbol-table parsed-elf)))
