#|
 This file is a part of mmap
 (c) 2017 Shirakumo http://tymoon.eu (shinmera@tymoon .eu)
 Author: Nicolas Hafner <shinmera@tymoon.eu>
|#

(asdf:defsystem mmap
  :version "1.0.0"
  :license "zlib"
  :author "Nicolas Hafner <shinmera@tymoon.eu>"
  :maintainer "Nicolas Hafner <shinmera@tymoon.eu>"
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
