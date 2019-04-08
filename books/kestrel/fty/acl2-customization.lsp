; FTY -- Kestrel Extensions -- Customization
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)

(include-book "centaur/fty/portcullis" :dir :system)

(reset-prehistory)

(in-package "FTY")
