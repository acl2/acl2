(in-package "ACL2")

(include-book "fix-cert")

(defttag :test-fix-cert)

(progn!
; The following assign was added by Matt K. after the addition of bookdata in
; 10/2013 (see :DOC bookdata).  It seemed necessary; apparently some defpkg
; forms were placed into the top level of the world, but bookdata processing
; assumes that defpkg forms do not appear in a book.
 (assign write-bookdata nil)
 ;(trace$ fix-cert-fn)     ; for debugging
 ;(trace$ parse-book-name) ; for debugging
 (fix-cert ("moved/test1bb" "moved/test1bp"))
 (fix-cert '("moved/test1pp" "moved/test1pb"))
 (fix-cert "moved/test1b")
 (fix-cert "moved/test1p")
 (fix-cert "moved/test1")
 (fix-cert "moved/test2"))
