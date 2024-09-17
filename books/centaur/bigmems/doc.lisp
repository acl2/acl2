(in-package "BIGMEMS")

(include-book "xdoc/topics" :dir :system)

(defxdoc bigmems
  :pkg "BIGMEMS"
  :parents (acl2::projects)
  :short "@('2^64')-byte memory models that are logically a record."

  :long "<p>The @('bigmems') library implements multiple memory models with
  @('2^64') bytes of space as abstract stobjs. These models use different
  techniques to lazily allocate the space as you use it. Logically they are
  equivalent, sharing the same logical definitions, but they may have different
  performance characteristics because they have different executable
  definitions.</p>

  <p>If you're writing a book, you should use @(tsee bigmem::bigmem). This
  stobj is \"attachable,\" so users of your book can attach other bigmem
  implementations to it if they so chooose. See the topics for the individual
  bigmem implementations below for more information about particular memory
  models.</p>")
