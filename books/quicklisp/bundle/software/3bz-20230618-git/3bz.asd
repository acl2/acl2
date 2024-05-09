(defsystem :3bz
  :description "deflate decompressor"
  :depends-on (alexandria
               (:feature (:and (:not :mezzano) (:not :abcl)) cffi)
               (:feature (:and (:not :mezzano) (:not :abcl)) mmap)
               trivial-features
               nibbles
               babel)
  :serial t
  :license "MIT"
  :author "Bart Botta <00003b at gmail.com>"
  :components
  ((:file "package")
   (:file "tuning")
   (:file "util")
   (:file "constants")
   (:file "types")
   (:file "huffman-tree")
   (:file "ht-constants")
   (:file "io-common")
   (:file "io-nommap" :if-feature (:or :mezzano :abcl))
   (:file "io-mmap" :if-feature (:and (:not :mezzano) (:not :abcl)))
   (:file "io")
   (:file "deflate")
   (:file "checksums")
   (:file "zlib")
   (:file "gzip")
   (:file "api")))

