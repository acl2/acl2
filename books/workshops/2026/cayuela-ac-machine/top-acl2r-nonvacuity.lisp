; top-acl2r-nonvacuity.lisp
;
; ACL2(r)-only. Certifies 09-nonvacuity-acl2r.lisp, which shows that
; the (equal (* s3 s3) 3) hypothesis used throughout books 02-05 is
; satisfiable in ACL2(r) (s3 = (acl2-sqrt 3)), using REALP instead of
; RATIONALP. It includes books 00-05, so those must be certified with
; the ACL2(r) executable. It is a separate top book because
; 06-generic-omega-collapse-acl2r.lisp re-declares the names CPLX,
; CPLXP, RE... and therefore cannot coexist with books 00-05.
;
;   ACL2=/path/to/saved_acl2r cert.pl --acl2 "$ACL2" top-acl2r-nonvacuity

; cert_param: (uses-acl2r)

(in-package "ACL2")

(include-book "09-nonvacuity-acl2r")
