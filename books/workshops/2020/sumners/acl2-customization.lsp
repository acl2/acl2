; Copyright (C) 2020, Rob Sumners
; Written by Rob Sumners
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(include-book "portcullis")
(set-deferred-ttag-notes t state)
(break-on-error nil)
(ld "~/acl2-customization.lsp" :ld-missing-input-ok t)
(in-package "GL")
(set-inhibit-warnings "theory")
