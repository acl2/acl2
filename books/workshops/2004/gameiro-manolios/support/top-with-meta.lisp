(in-package "ACL2")

#-non-standard-analysis
(include-book "../../../../arithmetic/top-with-meta")

; The linebreak below, after include-book, is there in order to avoid picking
; up this dependency when using books/cert.pl.
#+non-standard-analysis
(include-book
 "../../../../nonstd/arithmetic/top-with-meta")
