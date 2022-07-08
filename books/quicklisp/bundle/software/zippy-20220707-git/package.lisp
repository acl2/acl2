#|
 This file is a part of zippy
 (c) 2020 Shirakumo http://tymoon.eu (shinmera@tymoon.eu)
 Author: Nicolas Hafner <shinmera@tymoon.eu>
|#

(defpackage #:org.shirakumo.zippy
  (:use #:cl)
  (:local-nicknames
   (#:file-attributes #:org.shirakumo.file-attributes))
  ;; compression.lisp
  (:export
   #:make-decompression-state
   #:call-with-decompressed-buffer
   #:make-compression-state
   #:call-with-compressed-buffer
   #:call-with-completed-compressed-buffer)
  ;; decode.lisp
  (:export
   #:archive-file-required
   #:disk
   #:decode-file
   #:with-zip-file
   #:open-zip-file
   #:decode-entry)
  ;; encode.lisp
  (:export
   #:*version*
   #:*compatibility*
   #:encode-file)
  ;; encryption.lisp
  (:export
   #:make-decryption-state
   #:call-with-decrypted-buffer
   #:make-encryption-state
   #:call-with-encrypted-buffer
   #:call-with-completed-encrypted-buffer)
  ;; io.lisp
  (:export
   #:io
   #:vector-input
   #:vector-input-vector
   #:vector-input-index
   #:vector-input-start
   #:vector-input-end
   #:seek
   #:has-more
   #:index
   #:size
   #:start
   #:end
   #:ub32
   #:output
   #:parse-structure*
   #:write-structure*
   #:parse-structure
   #:with-io)
  ;; parser.lisp
  (:export
   #:decode-structure
   #:read-structure
   #:encode-structure
   #:write-structure
   #:define-byte-structure)
  ;; structures.lisp
  (:export
   #:zip64-extended-information
   #:os/2
   #:ntfs
   #:openvms
   #:unix
   #:patch-descriptor
   #:pkcs7-store
   #:x509-file
   #:x509-central-directory
   #:encryption-header
   #:record-management-controls
   #:pkcs7-encryption-recipient-certificate-list
   #:mvs
   #:policy-decryption-key-record
   #:key-provider-record
   #:policy-key-data-record
   #:zipit-macintosh-long
   #:zipit-macintosh-short-file
   #:zipit-macintosh-short-dir
   #:infozip-unicode-comment
   #:infozip-unicode-path
   #:data-stream-alignment
   #:microsoft-open-packaging-growth-hint
   #:aes-extra-data)
  ;; tables.lisp
  (:export
   #:file-attribute-name
   #:file-attribute-id
   #:compression-method-name
   #:compression-method-id
   #:encryption-method-name
   #:encryption-method-id)
  ;; toolkit.lisp
  (:export)
  ;; zippy.lisp
  (:export
   #:zip-file
   #:entries
   #:disks
   #:comment
   #:move-in-memory
   #:zip-entry
   #:zip-file
   #:version
   #:attributes
   #:encryption-method
   #:compression-method
   #:crc-32
   #:disk
   #:offset
   #:size
   #:uncompressed-size
   #:extra-fields
   #:last-modified
   #:file-name
   #:comment
   #:content
   #:entry-to-file
   #:entry-to-stream
   #:entry-to-vector
   #:extract-zip
   #:compress-zip))
