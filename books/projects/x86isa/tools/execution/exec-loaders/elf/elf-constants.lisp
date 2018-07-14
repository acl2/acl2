; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
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
; Shilpi Goel         <shigoel@cs.utexas.edu>
; Soumava Ghosh       <soumava@cs.utexas.edu>
;;
;; ==================================================================

(in-package "X86ISA")

(include-book "std/io/read-file-bytes" :dir :system)
(include-book "../sdlf-utils"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

;; ==================================================================

(defconst *note_abi_tag*       (combine-bytes (string-to-bytes ".note.ABI-tag")))
(defconst *note_gnu_build_id*  (combine-bytes (string-to-bytes ".note.gnu.build-id")))
(defconst *rela_plt*           (combine-bytes (string-to-bytes ".rela.plt")))
(defconst *init*               (combine-bytes (string-to-bytes ".init")))
(defconst *plt*                (combine-bytes (string-to-bytes ".plt")))
(defconst *elf-text*               (combine-bytes (string-to-bytes ".text")))
(defconst *fini*               (combine-bytes (string-to-bytes ".fini")))
(defconst *rodata*             (combine-bytes (string-to-bytes ".rodata")))
(defconst *eh_frame*           (combine-bytes (string-to-bytes ".eh_frame")))
(defconst *gcc_except_table*   (combine-bytes (string-to-bytes ".gcc_except_table")))
(defconst *init_array*         (combine-bytes (string-to-bytes ".init_array")))
(defconst *fini_array*         (combine-bytes (string-to-bytes ".fini_array")))
(defconst *ctors*              (combine-bytes (string-to-bytes ".ctors")))
(defconst *dtors*              (combine-bytes (string-to-bytes ".dtors")))
(defconst *jcr*                (combine-bytes (string-to-bytes ".jcr")))
(defconst *data_rel_ro*        (combine-bytes (string-to-bytes ".data.rel.ro")))
(defconst *got*                (combine-bytes (string-to-bytes ".got")))
(defconst *got_plt*            (combine-bytes (string-to-bytes ".got.plt")))
(defconst *elf-data*               (combine-bytes (string-to-bytes ".data")))
(defconst *tdata*              (combine-bytes (string-to-bytes ".tdata")))
(defconst *bss*                (combine-bytes (string-to-bytes ".bss")))
(defconst *tbss*               (combine-bytes (string-to-bytes ".tbss")))
;; /* the ELF magic number */
(defconst *ELFMAG*             (combine-bytes (append '(127) (string-to-bytes "ELF"))))
