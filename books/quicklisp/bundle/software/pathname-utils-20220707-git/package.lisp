#|
 This file is a part of Colleen
 (c) 2016 Shirakumo http://tymoon.eu (shinmera@tymoon.eu)
 Author: Nicolas Hafner <shinmera@tymoon.eu>
|#

(in-package #:cl-user)
(defpackage #:pathname-utils
  (:nicknames #:org.shirakumo.pathname-utils)
  (:use #:cl)
  (:export
   #:*wild-component*
   #:*wild-inferiors-component*
   #:*wild-file*
   #:*wild-directory*
   #:*wild-inferiors*
   #:*wild-path*
   #:clean-directory-spec
   #:normalize-directory-spec
   #:normalize-pathname
   #:pathname*
   #:unspecific-p
   #:relative-p
   #:absolute-p
   #:logical-p
   #:physical-p
   #:root-p
   #:directory-p
   #:file-p
   #:subpath-p
   #:pathname=
   #:pathname-equal
   #:to-root
   #:to-physical
   #:to-directory
   #:to-file
   #:subdirectory
   #:pop-directory
   #:parent
   #:upwards
   #:downwards
   #:enough-pathname
   #:relative-pathname
   #:file-in
   #:file-type
   #:file-name
   #:directory-name
   #:directory-separator
   #:components))
