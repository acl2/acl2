(in-package "ACL2")

(include-book "fix-cert")

(defttag :test-fix-cert)

(progn!
 ;(trace$ fix-cert-fn)     ; for debugging
 ;(trace$ parse-book-name) ; for debugging
 (fix-cert ("moved/test1bb" "moved/test1bp"))
 (fix-cert '("moved/test1pp" "moved/test1pb"))
 (fix-cert "moved/test1b")
 (fix-cert "moved/test1p")
 (fix-cert "moved/test1")
 (fix-cert "moved/test2"))
