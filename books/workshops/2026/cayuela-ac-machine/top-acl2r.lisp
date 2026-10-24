; top-acl2r.lisp
;
; Includes the ACL2(r)-only extensions to this verification (staged
; separately from top.lisp's plain-ACL2 chain, as described in the
; paper's Availability section). Certifying this book certifies, from
; a clean state:
;   - 06-generic-omega-collapse-acl2r.lisp (the concrete real
;     omega=e^{j2pi/3}, Section 4.4's existence witness)
;   - 08-inductance-integral.lisp (the inductance-integral progress
;     report, Section 5.1)
;
;   ACL2=/path/to/saved_acl2r cert.pl --acl2 "$ACL2" top-acl2r
;
; Requires the ACL2(r) executable and the nonstd/nsa and
; nonstd/workshops/2011/reid-gamboa-differentiator community books.
; Each book below is self-contained (neither includes the other, nor
; the plain-ACL2 chain), since they are independent pieces of work.

; cert_param: (uses-acl2r)

(in-package "ACL2")

(include-book "06-generic-omega-collapse-acl2r")
(include-book "08-inductance-integral")
