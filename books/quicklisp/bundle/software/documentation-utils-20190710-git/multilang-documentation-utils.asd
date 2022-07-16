#|
 This file is a part of documentation-utils
 (c) 2016 Shirakumo http://tymoon.eu (shinmera@tymoon.eu)
 Author: Nicolas Hafner <shinmera@tymoon.eu>
|#

(asdf:defsystem multilang-documentation-utils
  :version "1.1.0"
  :license "zlib"
  :author "Nicolas Hafner <shinmera@tymoon.eu>"
  :maintainer "Nicolas Hafner <shinmera@tymoon.eu>"
  :description "Multiple-languages support for documentation-utils."
  :homepage "https://Shinmera.github.io/documentation-utils/"
  :bug-tracker "https://github.com/Shinmera/documentation-utils/issues"
  :source-control (:git "https://github.com/Shinmera/documentation-utils.git")
  :serial T
  :components ((:file "multilang"))
  :depends-on (:documentation-utils
               :multilang-documentation))
