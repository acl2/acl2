; HTCLIENT -- HTTP/HTTPS Client Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "HTCLIENT")

(include-book "post-logic")
(include-book "post")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc htclient
  :parents (acl2::kestrel-books)
  :short "HTTP/HTTPS client library"
  :long
  (xdoc::topstring
   (xdoc::p
    "Currently we wrap selected functions from the "
    (xdoc::ahref "https://github.com/fukamachi/dexador/"
                 "Dexador HTTP Client Library")
    "."))
  )
