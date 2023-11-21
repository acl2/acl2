(asdf:defsystem pathname-utils-test
  :version "1.0.0"
  :license "zlib"
  :author "Yukari Hafner <shinmera@tymoon.eu>"
  :maintainer "Yukari Hafner <shinmera@tymoon.eu>"
  :description "Tests for the pathname-utils system."
  :homepage "https://Shinmera.github.io/pathname-utils/"
  :bug-tracker "https://github.com/Shinmera/pathname-utils/issues"
  :source-control (:git "https://github.com/Shinmera/pathname-utils.git")
  :serial T
  :components ((:file "test"))
  :depends-on (:pathname-utils :parachute)
  :perform (asdf:test-op (op c) (uiop:symbol-call :parachute :test :pathname-utils-test)))
