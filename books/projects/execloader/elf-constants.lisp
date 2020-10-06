; EL Library

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

; [Shilpi Goel] This book used to live in
; [books]/projects/x86isa/tools/execution/exec-loaders, but now it's
; in a stand-alone library of its own.

;; ----------------------------------------------------------------------

(in-package "EL")

(include-book "base")

(local (xdoc::set-default-parents elf-reader))

;; ----------------------------------------------------------------------

(defconst *note_abi_tag*       (merge-bytes (string->bytes ".note.ABI-tag")))
(defconst *note_gnu_build_id*  (merge-bytes (string->bytes ".note.gnu.build-id")))
(defconst *rela_plt*           (merge-bytes (string->bytes ".rela.plt")))
(defconst *init*               (merge-bytes (string->bytes ".init")))
(defconst *plt*                (merge-bytes (string->bytes ".plt")))
(defconst *elf-text*           (merge-bytes (string->bytes ".text")))
(defconst *fini*               (merge-bytes (string->bytes ".fini")))
(defconst *rodata*             (merge-bytes (string->bytes ".rodata")))
(defconst *eh_frame*           (merge-bytes (string->bytes ".eh_frame")))
(defconst *gcc_except_table*   (merge-bytes (string->bytes ".gcc_except_table")))
(defconst *init_array*         (merge-bytes (string->bytes ".init_array")))
(defconst *fini_array*         (merge-bytes (string->bytes ".fini_array")))
(defconst *ctors*              (merge-bytes (string->bytes ".ctors")))
(defconst *dtors*              (merge-bytes (string->bytes ".dtors")))
(defconst *jcr*                (merge-bytes (string->bytes ".jcr")))
(defconst *data_rel_ro*        (merge-bytes (string->bytes ".data.rel.ro")))
(defconst *got*                (merge-bytes (string->bytes ".got")))
(defconst *got_plt*            (merge-bytes (string->bytes ".got.plt")))
(defconst *elf-data*           (merge-bytes (string->bytes ".data")))
(defconst *tdata*              (merge-bytes (string->bytes ".tdata")))
(defconst *bss*                (merge-bytes (string->bytes ".bss")))
(defconst *tbss*               (merge-bytes (string->bytes ".tbss")))
(defconst *symtab*             (merge-bytes (string->bytes ".symtab")))
(defconst *strtab*             (merge-bytes (string->bytes ".strtab")))
;; /* the ELF magic number */
(defconst *ELFMAG*             (merge-bytes (append '(127) (string->bytes "ELF"))))

;; ----------------------------------------------------------------------
