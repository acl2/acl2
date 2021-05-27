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
(include-book "kestrel/fty/byte-list" :dir :system)
(include-book "centaur/fty/top" :dir :system)

(local (xdoc::set-default-parents mach-o-reader))

;; ----------------------------------------------------------------------

(defprod mach-o-section-header
  ((sectname  stringp :default "")
   (segname   stringp :default "")
   (addr      natp :default 0)
   (size      natp :default 0)
   (offset    natp :default 0)
   (align     natp :default 0)
   (reloff    natp :default 0)
   (nreloc    natp :default 0)
   (flags     natp :default 0)
   (reserved1 natp :default 0)
   (reserved2 natp :default 0)
   (reserved3 natp :default 0)))
(fty::deflist mach-o-section-headers
              :elt-type mach-o-section-header
              :true-listp t)

(defprod mach-o-header
  ((magic      natp :default 0)
   (cputype    natp :default 0)
   (cpusubtype natp :default 0)
   (filetype   natp :default 0)
   (ncmds      natp :default 0)
   (sizeofcmds natp :default 0)
   (flags      natp :default 0)
   (reserved   acl2::maybe-natp :default 'nil)))

;; ----------------------------------------------------------------------
