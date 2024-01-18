(asdf:defsystem mmap-test
  :version "1.0.0"
  :license "zlib"
  :author "Yukari Hafner <shinmera@tymoon.eu>"
  :maintainer "Yukari Hafner <shinmera@tymoon.eu>"
  :description "Tests for the mmap system."
  :homepage "https://shinmera.github.io/mmap/"
  :bug-tracker "https://github.com/Shinmera/mmap/issues"
  :source-control (:git "https://github.com/Shinmera/mmap.git")
  :serial T
  :components ((:file "test"))
  :depends-on (:mmap :cffi :alexandria :parachute)
  :perform (asdf:test-op (op c) (uiop:symbol-call :parachute :test :mmap-test)))
