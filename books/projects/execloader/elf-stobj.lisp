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
; Soumava Ghosh       <soumava@cs.utexas.edu>

; [Shilpi Goel] This book is a modified version of the one that used
; to live in [books]/projects/x86isa/tools/execution/exec-loaders.

(in-package "EXLD")

(include-book "elf-structs")
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

    (elf-header                     :type (satisfies elf-header-p)
                                    :initially ,(make-elf-header)
                                    :fix (ec-call (elf-header-fix x)))

    (sections                       :type (satisfies section-info-list-p)
                                    :initially nil :fix (ec-call (section-info-list-fix x)))))

(with-output :off (prove event)
  :summary-off #!acl2 (:other-than errors form time)
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
