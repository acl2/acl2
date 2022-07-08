#|
 This file is a part of Colleen
 (c) 2016 Shirakumo http://tymoon.eu (shinmera@tymoon.eu)
 Author: Nicolas Hafner <shinmera@tymoon.eu>
|#

(asdf:defsystem pathname-utils
  :version "1.1.0"
  :license "zlib"
  :author "Nicolas Hafner <shinmera@tymoon.eu>"
  :maintainer "Nicolas Hafner <shinmera@tymoon.eu>"
  :description "A collection of utilities for pathname manipulation."
  :homepage "https://Shinmera.github.io/pathname-utils/"
  :bug-tracker "https://github.com/Shinmera/pathname-utils/issues"
  :source-control (:git "https://github.com/Shinmera/pathname-utils.git")
  :serial T
  :components ((:file "package")
               (:file "toolkit")
               (:file "documentation"))
  :depends-on ()
  :in-order-to ((asdf:test-op (asdf:test-op :pathname-utils-test))))
