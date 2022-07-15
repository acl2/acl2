#|
 This file is a part of Trivial-Indent
 (c) 2014 Shirakumo http://tymoon.eu (shinmera@tymoon.eu)
 Author: Nicolas Hafner <shinmera@tymoon.eu>
|#

(defsystem trivial-indent
  :name "Trivial-Indent"
  :version "1.0.0"
  :license "zlib"
  :author "Nicolas Hafner <shinmera@tymoon.eu>"
  :maintainer "Nicolas Hafner <shinmera@tymoon.eu>"
  :description "A very simple library to allow indentation hints for SWANK."
  :homepage "https://shinmera.github.io/trivial-indent/"
  :bug-tracker "https://github.com/Shinmera/trivial-indent/issues"
  :source-control (:git "https://github.com/Shinmera/trivial-indent.git")
  :serial T
  :components ((:file "indent"))
  :depends-on ())
