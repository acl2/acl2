(in-package #:cl-user)
(defpackage #:org.shirakumo.filesystem-utils
  (:use #:cl)
  (:local-nicknames (#:pathname-utils #:org.shirakumo.pathname-utils))
  (:export
   #:runtime-directory
   #:temporary-directory
   #:make-temporary-file
   #:with-temporary-file
   #:current-directory
   #:with-current-directory
   #:ensure-deleted
   #:truename*
   #:file-exists-p
   #:directory*
   #:list-contents
   #:list-files
   #:list-directories
   #:list-hosts
   #:list-devices
   #:resolve-symbolic-links
   #:directory-p
   #:file-p
   #:symbolic-link-p
   #:create-symbolic-link
   #:rename-file*
   #:copy-file
   #:delete-directory
   #:delete-file*))
