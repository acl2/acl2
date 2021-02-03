; Bitcoin Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BITCOIN")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "base58")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Example from steps 8 and 9 in Section 'How to create Bitcoin Address'
; of Page 'Technical background of version 1 Bitcoin addresses' of [Wiki]
; (https://en.bitcoin.it/wiki/Technical_background_of_version_1_Bitcoin_addresses#How_to_create_Bitcoin_Address):

(acl2::assert-equal
 (base58-encode
  (nat=>bebytes 25 #x00f54a5851e9372b87810a8e60cdd2e7cfd80b6e31c7f18fe8))
 (explode "1PMycacnJaSqwwJqjawXBErnLsZ7RkXUAs"))

(acl2::assert-equal
 (bebytes=>nat (base58-decode (explode "1PMycacnJaSqwwJqjawXBErnLsZ7RkXUAs")))
 #x00f54a5851e9372b87810a8e60cdd2e7cfd80b6e31c7f18fe8)
