; Decompression Utility Raw Lisp Code
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)
; Supporting Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;(include-book "quicklisp/zippy" :dir :system :ttags :all)
;(include-book "kestrel/bv-lists/byte-listp" :dir :system)

; If the arguments are the wrong type, gets a hard error.
; If it gets an error when decompressing, it writes an error message
;   to the comment window and returns the empty list.
(defun decompress-bytes (byte-list format)
  (if (not (byte-listp byte-list))
      (error "DECOMPRESS-BYTES can only be called on a list of 8-bit bytes")
   (if (not (member format '(:deflate :zlib :gzip)))
       (error "DECOMPRESS-BYTES second argument must be one of :deflate :zlib :gzip")
     (handler-case
      (let ((input-vector (coerce byte-list '(simple-array (unsigned-byte 8) (*)))))
        (let ((output-array (3bz:decompress-vector input-vector :format format)))
          (coerce output-array 'list)))
      (error (condition)
             (let ((condition-str (format nil "~a" condition)))
               (cw "DECOMPRESS-BYTES error: ~s0." condition-str)))))))

; simpler form without any error checking
;(defun decompress-bytes (byte-list format)
;  (let ((input-vector (coerce byte-list '(simple-array (unsigned-byte 8) (*)))))
;    (let ((output-array (3bz:decompress-vector input-vector :format format)))
;      (coerce output-array 'list))))
