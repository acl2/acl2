; EXLD (execloader) Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2020, Shilpi Goel
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Shilpi Goel         <shigoel@gmail.com>

(in-package "EXLD")

(include-book "std/strings/pad" :dir :system)
(include-book "kestrel/fty/byte-list" :dir :system)
(include-book "centaur/fty/bitstruct" :dir :system)
(include-book "centaur/fty/top" :dir :system)

(local (xdoc::set-default-parents elf-reader))

;; ----------------------------------------------------------------------

;; ELF segments:

(defprod elf64-segment-header
  ((type natp :default 0)
   (flags natp :default 0)
   (offset natp :default 0)
   (vaddr  natp :default 0)
   (paddr  natp :default 0)
   (filesz natp :default 0)
   (memsz  natp :default 0)
   (align  natp :default 0)))
(fty::deflist elf64-segment-headers
              :elt-type elf64-segment-header
              :true-listp t)

(defprod elf32-segment-header
  ((type   natp :default 0)
   (flags  natp :default 0)
   (offset natp :default 0)
   (vaddr  natp :default 0)
   (paddr  natp :default 0)
   (filesz natp :default 0)
   (memsz  natp :default 0)
   (align  natp :default 0)))
(fty::deflist elf32-segment-headers
              :elt-type elf32-segment-header
              :true-listp t)

;; ----------------------------------------------------------------------

;; ELF sections:

(defprod elf-section-header
  ((name-str  stringp :default "")
   (name      natp :default 0)
   (type      natp :default 0)
   (flags     natp :default 0)
   (addr      natp :default 0
              "The address where this section should be laid in memory")
   (offset    natp :default 0
              "The offset in the binary file where this section is located")
   (size      natp :default 0
              "The size of the section in terms of number of bytes it occupies")
   (link      natp :default 0)
   (info      natp :default 0)
   (addralign natp :default 0)
   (entsize   natp :default 0)))
(fty::deflist elf-section-headers
              :elt-type elf-section-header
              :true-listp t)

(defprod section-info
  :short "Relevant information about a section of an ELF or Mach-O binary file"
  ((header elf-section-header-p :default (make-elf-section-header))
   (bytes byte-listp :default 'nil
          "The content of this section (least-significant byte first)")))
(fty::deflist section-info-list :elt-type section-info-p :true-listp t)

(define section-names ((section-info-list section-info-list-p))
  :short "Get all names from sections in @('section-info-list')"
  :returns (sec-names string-listp :hyp :guard)
  (b* (((when (atom section-info-list))
        nil)
       ((section-info section-info) (car section-info-list))
       ((elf-section-header section-info.header)))
    (cons section-info.header.name-str (section-names (cdr section-info-list)))))

(define get-section-info ((name stringp "Name of a section header; e.g., \".symtab\"")
                          (section-info-list section-info-list-p))
  :short "Get a @(tsee section-info-p) in @('section-info-list-p') corresponding to @('name')"
  :returns (section-info section-info-p :hyp (section-info-list-p section-info-list))
  (b* (((when (atom section-info-list))
        (prog2$
         (raise "Section ~s0 not found! List of sections found: ~x1."
                name (section-names section-info-list))
         (make-section-info)))
       ((section-info section-info) (car section-info-list))
       ((elf-section-header section-info.header))
       ((when (equal (str::trim section-info.header.name-str) (str::trim name)))
        section-info))
    (get-section-info name (cdr section-info-list))))

;; ----------------------------------------------------------------------

;; ELF header:

(defprod elf-header
  ((magic     byte-listp :default 'nil)
   (class     natp :default 0)
   (dataenc   natp :default 0)
   (identver  natp :default 0)
   (osabi     natp :default 0)
   (abiver    natp :default 0)
   (padding   byte-listp :default 'nil)
   (type      natp :default 0)
   (machine   natp :default 0)
   (version   natp :default 0)
   (entry     natp :default 0)
   (phoff     natp :default 0)
   (shoff     natp :default 0)
   (flags     natp :default 0)
   (ehsize    natp :default 0)
   (phentsize natp :default 0)
   (phnum     natp :default 0)
   (shentsize natp :default 0)
   (shnum     natp :default 0)
   (shstrndx  natp :default 0)))

;; ----------------------------------------------------------------------

;; Symbol table entries:

(fty::defbitstruct elf_bits8   8)
(fty::defbitstruct elf_bits16 16)
(fty::defbitstruct elf_bits32 32)
(fty::defbitstruct elf_bits64 64)
(fty::defbitstruct elf64_sym ;; LSB first                   
  ;; typedef struct {
  ;;     uint32_t      st_name;
  ;;     unsigned char st_info;
  ;;     unsigned char st_other;
  ;;     uint16_t      st_shndx;
  ;;     Elf64_Addr    st_value;
  ;;     uint64_t      st_size;
  ;; } Elf64_Sym;
  ((name     elf_bits32 :default 0)
   (info     elf_bits8  :default 0)
   (other    elf_bits8  :default 0)
   (shndx    elf_bits16 :default 0)
   (value    elf_bits64 :default 0)
   (size     elf_bits64 :default 0))
  :msb-first nil)

(defprod elf64_sym-info
  ((name-str stringp        :default "") ;; Obtained from strtab.
   (entry    elf64_sym-p    :default 0)))
(fty::deflist elf64_sym-info-list
              :elt-type elf64_sym-info
              :true-listp t)

(fty::defbitstruct elf32_sym
  ;; typedef struct {
  ;;     uint32_t      st_name;
  ;;     Elf32_Addr    st_value;
  ;;     uint32_t      st_size;
  ;;     unsigned char st_info;
  ;;     unsigned char st_other;
  ;;     uint16_t      st_shndx;
  ;; } Elf32_Sym;
  ((name  elf_bits32 :default 0)
   (value elf_bits32 :default 0)
   (size  elf_bits32 :default 0)
   (info  elf_bits8  :default 0)
   (other elf_bits8  :default 0)
   (shndx elf_bits16 :default 0)))
(defprod elf32_sym-info
  ((name-str stringp        :default "") ;; Obtained from strtab.
   (entry    elf32_sym      :default 0)))
(fty::deflist elf32_sym-info-list
              :elt-type elf32_sym-info
              :true-listp t)

;; ----------------------------------------------------------------------
