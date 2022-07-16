#|
 This file is a part of file-attributes
 (c) 2020 Shirakumo http://tymoon.eu (shinmera@tymoon.eu)
 Author: Nicolas Hafner <shinmera@tymoon.eu>
|#

(defpackage #:org.shirakumo.file-attributes
  (:use #:cl)
  (:shadow #:byte)
  ;; protocol.lisp
  (:export
   #:access-time
   #:modification-time
   #:creation-time
   #:group
   #:owner
   #:attributes
   #:*system*
   #:encode-attributes
   #:decode-attributes))
