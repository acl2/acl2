#|
 This file is a part of Trivial-Mimes
 (c) 2014 Shirakumo http://tymoon.eu (shinmera@tymoon.eu)
 Author: Nicolas Hafner <shinmera@tymoon.eu>
|#

(defsystem trivial-mimes
  :name "Trivial-Mimes"
  :version "1.1.0"
  :license "zlib"
  :author "Nicolas Hafner <shinmera@tymoon.eu>"
  :maintainer "Nicolas Hafner <shinmera@tymoon.eu>"
  :description "Tiny library to detect mime types in files."
  :homepage "https://Shinmera.github.io/trivial-mimes/"
  :bug-tracker "https://github.com/Shinmera/trivial-mimes/issues"
  :source-control (:git "https://github.com/Shinmera/trivial-mimes.git")
  :serial T
  :components ((:file "mime-types"))
  :depends-on ())
