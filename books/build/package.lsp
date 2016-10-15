(include-book "std/portcullis" :dir :system)

(defpkg "BUILD"
  (union-eq '(books)
            *std-pkg-symbols*))
