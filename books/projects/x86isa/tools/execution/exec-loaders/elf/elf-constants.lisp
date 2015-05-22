;; ORIGINAL AUTHORS:
;; Soumava Ghosh       <soumava@cs.utexas.edu>
;; Shilpi Goel         <shigoel@cs.utexas.edu>
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
