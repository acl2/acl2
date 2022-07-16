(in-package :cl-utilities)

(defun rotate-byte (count bytespec integer)
  "Rotates a field of bits within INTEGER; specifically, returns an
integer that contains the bits of INTEGER rotated COUNT times
leftwards within the byte specified by BYTESPEC, and elsewhere
contains the bits of INTEGER. See http://www.cliki.net/ROTATE-BYTE"
  (declare (optimize (speed 3) (safety 0) (space 0) (debug 1)))
  #-sbcl
  (let ((size (byte-size bytespec)))
    (when (= size 0)
      (return-from rotate-byte integer))
    (let ((count (mod count size)))
      (labels ((rotate-byte-from-0 (count size integer)
                 (let ((bytespec (byte size 0)))
                   (if (> count 0)
                       (logior (ldb bytespec (ash integer count))
                               (ldb bytespec (ash integer (- count size))))
                       (logior (ldb bytespec (ash integer count))
                               (ldb bytespec (ash integer (+ count size))))))))
        (dpb (rotate-byte-from-0 count size (ldb bytespec integer))
             bytespec
             integer))))
  ;; On SBCL, we use the SB-ROTATE-BYTE extension.
  #+sbcl-uses-sb-rotate-byte (sb-rotate-byte:rotate-byte count bytespec integer))

;; If we're using the SB-ROTATE-BYTE extension, we should inline our
;; call and let SBCL handle optimization from there.
#+sbcl-uses-sb-rotate-byte (declaim (inline rotate-byte))