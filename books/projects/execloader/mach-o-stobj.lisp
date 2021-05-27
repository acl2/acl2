; EXLD Library

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

; [Shilpi Goel] This book used to live in
; [books]/projects/x86isa/tools/execution/exec-loaders, but now it's
; in a stand-alone library of its own.

(in-package "EXLD")

(include-book "mach-o-constants")
(include-book "centaur/defrstobj2/defrstobj" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (in-theory (disable unsigned-byte-p loghead logtail)))

(local (xdoc::set-default-parents mach-o-reader))

;; ======================================================================

(defconst *mach-o-body*
  `(
    (mach-o-file-size             :type (integer 0 *)
                                  :initially   0 :fix (nfix x))
    (load-cmds-size               :type (unsigned-byte 64)
                                  :initially   0 :fix (ec-call (loghead 64 x)))
    (mach-o-header-size           :type (unsigned-byte 64)
                                  :initially   0 :fix (ec-call (loghead 64 x)))
    ;; TEXT Segment

    ;; text section:
    (TEXT-text-section-addr       :type (unsigned-byte 64)
                                  :initially   0 :fix (ec-call (loghead 64 x)))
    (TEXT-text-section-size       :type (unsigned-byte 64)
                                  :initially   0 :fix (ec-call (loghead 64 x)))
    (TEXT-text-section-offset     :type (unsigned-byte 64)
                                  :initially   0 :fix (ec-call (loghead 64 x)))
    (TEXT-text-section-bytes      :type (satisfies byte-listp)
                                  :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; cstring section:
    (TEXT-cstring-section-addr    :type (unsigned-byte 64)
                                  :initially   0 :fix (ec-call (loghead 64 x)))
    (TEXT-cstring-section-size    :type (unsigned-byte 64)
                                  :initially   0 :fix (ec-call (loghead 64 x)))
    (TEXT-cstring-section-offset  :type (unsigned-byte 64)
                                  :initially   0 :fix (ec-call (loghead 64 x)))
    (TEXT-cstring-section-bytes   :type (satisfies byte-listp)
                                  :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; const section:
    (TEXT-const-section-addr      :type (unsigned-byte 64)
                                  :initially   0 :fix (ec-call (loghead 64 x)))
    (TEXT-const-section-size      :type (unsigned-byte 64)
                                  :initially   0 :fix (ec-call (loghead 64 x)))
    (TEXT-const-section-offset    :type (unsigned-byte 64)
                                  :initially   0 :fix (ec-call (loghead 64 x)))
    (TEXT-const-section-bytes     :type (satisfies byte-listp)
                                  :initially nil :fix (ec-call (acl2::byte-list-fix x)))
    ;; DATA Segment

    ;; data section:
    (DATA-data-section-addr      :type (unsigned-byte 64)
                                 :initially   0 :fix (ec-call (loghead 64 x)))
    (DATA-data-section-size      :type (unsigned-byte 64)
                                 :initially   0 :fix (ec-call (loghead 64 x)))
    (DATA-data-section-offset    :type (unsigned-byte 64)
                                 :initially   0 :fix (ec-call (loghead 64 x)))
    (DATA-data-section-bytes     :type (satisfies byte-listp)
                                 :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; dyld section:
    (DATA-dyld-section-addr      :type (unsigned-byte 64)
                                 :initially   0 :fix (ec-call (loghead 64 x)))
    (DATA-dyld-section-size      :type (unsigned-byte 64)
                                 :initially   0 :fix (ec-call (loghead 64 x)))
    (DATA-dyld-section-offset    :type (unsigned-byte 64)
                                 :initially   0 :fix (ec-call (loghead 64 x)))
    (DATA-dyld-section-bytes     :type (satisfies byte-listp)
                                 :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; const section:
    (DATA-const-section-addr     :type (unsigned-byte 64)
                                 :initially   0 :fix (ec-call (loghead 64 x)))
    (DATA-const-section-size     :type (unsigned-byte 64)
                                 :initially   0 :fix (ec-call (loghead 64 x)))
    (DATA-const-section-offset   :type (unsigned-byte 64)
                                 :initially   0 :fix (ec-call (loghead 64 x)))
    (DATA-const-section-bytes    :type (satisfies byte-listp)
                                 :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; bss section:
    (DATA-bss-section-addr       :type (unsigned-byte 64)
                                 :initially   0 :fix (ec-call (loghead 64 x)))
    (DATA-bss-section-size       :type (unsigned-byte 64)
                                 :initially   0 :fix (ec-call (loghead 64 x)))
    (DATA-bss-section-offset     :type (unsigned-byte 64)
                                 :initially   0 :fix (ec-call (loghead 64 x)))
    (DATA-bss-section-bytes      :type (satisfies byte-listp)
                                 :initially nil :fix (ec-call (acl2::byte-list-fix x)))

    ;; common section:
    (DATA-common-section-addr    :type (unsigned-byte 64)
                                 :initially   0 :fix (ec-call (loghead 64 x)))
    (DATA-common-section-size    :type (unsigned-byte 64)
                                 :initially   0 :fix (ec-call (loghead 64 x)))
    (DATA-common-section-offset  :type (unsigned-byte 64)
                                 :initially   0 :fix (ec-call (loghead 64 x)))
    (DATA-common-section-bytes   :type (satisfies byte-listp)
                                 :initially nil :fix (ec-call (acl2::byte-list-fix x)))
    ))

(with-output :off (prove event)
  :summary-off #!acl2 (:other-than errors form time)
  (make-event
   `(rstobj2::defrstobj mach-o
      ,@*mach-o-body*
      :accessor-template (@ x)
      :updater-template (! x))))

(defsection good-mach-o-p
  :short "The preferred recognizer for the @('mach-o') stobj"
  (defun good-mach-o-p (mach-o)
    (declare (xargs :stobjs mach-o)
             (ignore mach-o))
    t))

;; ==================================================================-
