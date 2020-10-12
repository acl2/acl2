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
; Soumava Ghosh       <soumava@cs.utexas.edu>

; [Shilpi Goel] This book is a modified version of the one that used
; to live in [books]/projects/x86isa/tools/execution/exec-loaders.

(in-package "EL")

(include-book "elf-constants")
(include-book "centaur/defrstobj2/defrstobj" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (in-theory (disable unsigned-byte-p loghead logtail)))

(local (xdoc::set-default-parents elf-reader))

;; ========================================================

(defconst *elf-body*
  `((elf-file-size                  :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (sections-num                   :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (elf-header-size                :type (integer 0 *)
                                    :initially 0 :fix (nfix x))

    ;; note-ABI-tag section
    (note-ABI-tag-addr              :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (note-ABI-tag-size              :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (note-ABI-tag-offset            :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (note-ABI-tag-bytes             :type (satisfies byte-listp)
                                    :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; note-gnu-build-id section
    (note-gnu-buildid-addr          :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (note-gnu-buildid-size          :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (note-gnu-buildid-offset        :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (note-gnu-buildid-bytes         :type (satisfies byte-listp)
                                    :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; rela-plt section
    (rela-plt-addr                  :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (rela-plt-size                  :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (rela-plt-offset                :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (rela-plt-bytes                 :type (satisfies byte-listp)
                                    :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; init section
    (init-addr                      :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (init-size                      :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (init-offset                    :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (init-bytes                     :type (satisfies byte-listp)
                                    :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; plt section
    (plt-addr                       :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (plt-size                       :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (plt-offset                     :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (plt-bytes                      :type (satisfies byte-listp)
                                    :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; text section
    (text-addr                      :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (text-size                      :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (text-offset                    :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (text-bytes                     :type (satisfies byte-listp)
                                    :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; fini section
    (fini-addr                      :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (fini-size                      :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (fini-offset                    :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (fini-bytes                     :type (satisfies byte-listp)
                                    :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; rodata section
    (rodata-addr                    :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (rodata-size                    :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (rodata-offset                  :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (rodata-bytes                   :type (satisfies byte-listp)
                                    :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; eh-frame section
    (eh-frame-addr                  :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (eh-frame-size                  :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (eh-frame-offset                :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (eh-frame-bytes                 :type (satisfies byte-listp)
                                    :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; gcc-except-table section
    (gcc-except-table-addr          :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (gcc-except-table-size          :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (gcc-except-table-offset        :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (gcc-except-table-bytes         :type (satisfies byte-listp)
                                    :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; init-array section
    (init-array-addr                :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (init-array-size                :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (init-array-offset              :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (init-array-bytes               :type (satisfies byte-listp)
                                    :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; fini-array section
    (fini-array-addr                :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (fini-array-size                :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (fini-array-offset              :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (fini-array-bytes               :type (satisfies byte-listp)
                                    :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; ctors section
    (ctors-addr                     :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (ctors-size                     :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (ctors-offset                   :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (ctors-bytes                    :type (satisfies byte-listp)
                                    :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; dtors section
    (dtors-addr                     :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (dtors-size                     :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (dtors-offset                   :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (dtors-bytes                    :type (satisfies byte-listp)
                                    :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; jcr section
    (jcr-addr                       :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (jcr-size                       :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (jcr-offset                     :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (jcr-bytes                      :type (satisfies byte-listp)
                                    :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; data-rel-ro section
    (data-rel-ro-addr               :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (data-rel-ro-size               :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (data-rel-ro-offset             :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (data-rel-ro-bytes              :type (satisfies byte-listp)
                                    :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; got section
    (got-addr                       :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (got-size                       :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (got-offset                     :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (got-bytes                      :type (satisfies byte-listp)
                                    :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; got-plt section
    (got-plt-addr                   :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (got-plt-size                   :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (got-plt-offset                 :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (got-plt-bytes                  :type (satisfies byte-listp)
                                    :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; data section
    (data-addr                      :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (data-size                      :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (data-offset                    :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (data-bytes                     :type (satisfies byte-listp)
                                    :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; tdata section
    (tdata-addr                     :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (tdata-size                     :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (tdata-offset                   :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (tdata-bytes                    :type (satisfies byte-listp)
                                    :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; bss section
    (bss-addr                       :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (bss-size                       :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (bss-offset                     :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (bss-bytes                      :type (satisfies byte-listp)
                                    :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; tbss section
    (tbss-addr                      :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (tbss-size                      :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (tbss-offset                    :type (integer 0 *)
                                    :initially 0 :fix (nfix x))
    (tbss-bytes                     :type (satisfies byte-listp)
                                    :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; symtab section
    (symtab-addr                     :type (integer 0 *)
                                     :initially 0 :fix (nfix x))
    (symtab-size                     :type (integer 0 *)
                                     :initially 0 :fix (nfix x))
    (symtab-offset                   :type (integer 0 *)
                                     :initially 0 :fix (nfix x))
    (symtab-bytes                    :type (satisfies byte-listp)
                                     :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; strtab section
    (strtab-addr                     :type (integer 0 *)
                                     :initially 0 :fix (nfix x))
    (strtab-size                     :type (integer 0 *)
                                     :initially 0 :fix (nfix x))
    (strtab-offset                   :type (integer 0 *)
                                     :initially 0 :fix (nfix x))
    (strtab-bytes                    :type (satisfies byte-listp)
                                     :initially nil :fix (ec-call (acl2::byte-list-fix x)))))

(with-output :off (prove event)
  :summary #!acl2 (errors form time)
  (make-event
   `(rstobj2::defrstobj elf
      ,@*elf-body*
      :accessor-template (@ x)
      :updater-template (! x))))

(defsection good-elf-p
  :short "The preferred recognizer for the @('elf') stobj"
  (defun good-elf-p (elf)
    (declare (xargs :stobjs elf)
             (ignore elf))
    t))

;; ----------------------------------------------------------------------
