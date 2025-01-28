See `books/acl2s/aspf` for the ACL2s Systems Programming Framework
library, which used to exist in this directory. We provide
`books/acl2s/interface/top` and
`books/acl2s/interface/acl2s-utils/top` to retain backwards
compatibility for now, but we will eliminate them at some point in the
future. Any users of the library should update any include-books to
point to `books/acl2s/aspf/top` and `books/acl2s/aspf/acl2s-utils/top`
respectively.
