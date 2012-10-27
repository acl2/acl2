(in-package "ACL2")

(include-book "sublis-var")

(verify-termination meta-extract-rw+-term)

(verify-termination meta-extract-contextual-fact)

(verify-termination meta-extract-global-fact)
