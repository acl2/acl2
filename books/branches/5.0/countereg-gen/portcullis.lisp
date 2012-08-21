#|$ACL2s-Preamble$;

(ld ;; Newline to fool dependency scanner for ACL2 Makefiles/cert.pl
 "portcullis.acl2")

(acl2::begin-book t);$ACL2s-Preamble$|#


; portcullis.lisp
;
; This is an empty book in the DEFDATA package.  Note that in cert.acl2 we
; (include-book "portcullis") instead of (ld "pkg.lsp").  This ensures that as
; we load several books from this directory, their portcullises just have
; redundant (include-book "portcullis") commands instead of redundant defpkg
; commands.  It is a very minor efficienty tweak that adds up over multiple
; libraries.

(in-package "DEFDATA")