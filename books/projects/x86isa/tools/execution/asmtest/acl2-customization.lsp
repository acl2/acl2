; x86isa assembly snippet testing framework
;
; X86ISA Library
; Copyright (C) 2024 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Sol Swords (sswords@gmail.com)

(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)
(set-deferred-ttag-notes t state)

(ld "cert.acl2" :ld-missing-input-ok t)
(in-package "X86ISA")

(reset-prehistory)
