#|
 This file is a part of documentation-utils
 (c) 2016 Shirakumo http://tymoon.eu (shinmera@tymoon.eu)
 Author: Nicolas Hafner <shinmera@tymoon.eu>
|#

(asdf:defsystem documentation-utils
  :version "1.2.0"
  :license "zlib"
  :author "Nicolas Hafner <shinmera@tymoon.eu>"
  :maintainer "Nicolas Hafner <shinmera@tymoon.eu>"
  :description "A few simple tools to help you with documenting your library."
  :homepage "https://Shinmera.github.io/documentation-utils/"
  :bug-tracker "https://github.com/Shinmera/documentation-utils/issues"
  :source-control (:git "https://github.com/Shinmera/documentation-utils.git")
  :serial T
  :components ((:file "package")
               (:file "toolkit")
               (:file "documentation"))
  :depends-on (:trivial-indent))
