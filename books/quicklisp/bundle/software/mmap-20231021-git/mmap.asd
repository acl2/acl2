(asdf:defsystem mmap
  :version "1.1.0"
  :license "zlib"
  :author "Yukari Hafner <shinmera@tymoon.eu>"
  :maintainer "Yukari Hafner <shinmera@tymoon.eu>"
  :description "Portable mmap (file memory mapping) utility library."
  :homepage "https://shinmera.github.io/mmap/"
  :bug-tracker "https://github.com/Shinmera/mmap/issues"
  :source-control (:git "https://github.com/Shinmera/mmap.git")
  :serial T
  :components ((:file "package")
               (:file "generic")
               (:file "posix" :if-feature :unix)
               (:file "windows" :if-feature :windows)
               (:file "documentation"))
  :defsystem-depends-on (:trivial-features)
  :depends-on (:documentation-utils
               :cffi)
  :in-order-to ((asdf:test-op (asdf:test-op :mmap-test))))
