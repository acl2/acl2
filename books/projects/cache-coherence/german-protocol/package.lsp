; This file is not part of the original "cache-coherence/german-protocol"
; project.  We added it to resolve a name conflict by wrapping the project in
; its own package.

(in-package "ACL2")

(defpkg "CACHE-COHERENCE/GERMAN-PROTOCOL"
  (append *acl2-exports*
          '(s g)))
