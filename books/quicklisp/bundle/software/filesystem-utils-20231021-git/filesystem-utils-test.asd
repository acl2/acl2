(asdf:defsystem filesystem-utils-test
  :version "1.0.0"
  :license "zlib"
  :author "Yukari Hafner <shinmera@tymoon.eu>"
  :maintainer "Yukari Hafner <shinmera@tymoon.eu>"
  :description "Tests for the filesystem-utils system."
  :homepage "https://Shinmera.github.io/filesystem-utils/"
  :bug-tracker "https://github.com/Shinmera/filesystem-utils/issues"
  :source-control (:git "https://github.com/Shinmera/filesystem-utils.git")
  :serial T
  :components ((:file "test"))
  :depends-on (:filesystem-utils :parachute)
  :perform (asdf:test-op (op c) (uiop:symbol-call :parachute :test :filesystem-utils-test)))
