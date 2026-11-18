; This file is not part of the original "avr-isa" project.  We added it to
; resolve a name conflict by wrapping the project in its own package.

(in-package "ACL2")

(defpkg "AVR-ISA"
  (append *acl2-exports*
          '(loghead
            logtail
            logapp
            ashu)))
