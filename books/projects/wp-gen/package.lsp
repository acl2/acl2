; This file is not part of the original "wp-gen" project.  We added it to
; resolve a name conflict by wrapping the project in its own package.

(in-package "ACL2")

(include-book "system/acl2-system-exports" :dir :system)

(defpkg "WP-GEN"
  (append *acl2-system-exports*
          '(ALL-FNNAMES
            DEFXDOC)))
