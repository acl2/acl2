(asdf:defsystem file-attributes
  :version "1.0.0"
  :license "zlib"
  :author "Yukari Hafner <shinmera@tymoon.eu>"
  :maintainer "Yukari Hafner <shinmera@tymoon.eu>"
  :description "Access to file attributes (uid, gid, atime, mtime, mod)"
  :homepage "https://shinmera.github.io/file-attributes"
  :bug-tracker "https://github.com/Shinmera/file-attributes/issues"
  :source-control (:git "https://github.com/Shinmera/file-attributes.git")
  :serial T
  :defsystem-depends-on (:trivial-features)
  :components ((:file "package")
               (:file "protocol")
               (:file "posix" :if-feature :unix)
               (:file "linux" :if-feature :linux)
               (:file "windows" :if-feature :windows)
               (:file "mezzano" :if-feature :mezzano)
               (:file "documentation"))
  :depends-on (:documentation-utils
               :cffi))
