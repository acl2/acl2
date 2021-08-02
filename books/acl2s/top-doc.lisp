(in-package "ACL2")

(include-book "xdoc/top" :dir :system)
(include-book "kestrel/utilities/xdoc-archiving" :dir :system)
(local (include-book "doc")) ; no_port
(xdoc::archive-topics-for-books-tree "acl2s")
