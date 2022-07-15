(in-package 3bz)

(defun decompress (context state)
  (etypecase state
    (gzip-state
     (decompress-gzip context state))
    (zlib-state
     (decompress-zlib context state))
    (deflate-state
     (decompress-deflate context state))))

(defun replace-output-buffer (state buffer)
  (unless (or (zerop (ds-output-offset state))
              (ds-output-overflow state))
    ;; we don't create/fill window until output buffer overflows, so
    ;; would need to do that here. error for now until someone needs
    ;; that ability...
    (error "can't switch buffers without filling old one yet."))
  (setf (ds-output-buffer state) buffer)
  (setf (ds-output-offset state) 0)
  (setf (ds-output-overflow state) nil))

(defun decompress-vector (compressed &key (format :zlib) (start 0) (end (length compressed)) output)
  "decompress octet-vector COMPRESSED using
FORMAT (:deflate,:zlib,:gzip). If output is supplied, it should be an
octet-vector large enough to hold entire uncompressed output.

Returns buffer containing decompressed data (OUTPUT if supplied) and #
of octets decompressed."
  (let ((parts nil)
        (state (ecase format
                 (:gzip (make-gzip-state))
                 (:zlib (make-zlib-state))
                 (:deflate (make-deflate-state))))
        (rc (make-octet-vector-context compressed :start start :end end)))
    (if output
        (progn
          (setf (ds-output-buffer state) output)
          (setf (ds-output-offset state) 0)
          (let ((c (decompress rc state)))
            (unless (ds-finished state)
              (cond
                ((ds-input-underrun state)
                 (error "incomplete ~a stream" format))
                ((ds-output-overflow state)
                 (error "not enough space to decompress ~a stream" format))
                (t (error "?"))))
            (values output c)))
        (progn
          (loop for out = (make-array (min (- end start) 32768)
                                      :element-type 'octet)
                  then (make-array (* 2 (length out)) :element-type 'octet)
                do (replace-output-buffer state out)
                   (let ((c (decompress rc state)))
                     (push (cons out c) parts))
                   (assert (not (ds-input-underrun state)))
                until (ds-finished state))
          (let* ((s (reduce '+ parts :key 'cdr))
                 (b (make-array s :element-type 'octet)))
            (loop for start = 0 then (+ start c)
                  for (p . c) in (nreverse parts)
                  do (replace b p :start1 start :end2 c))
            (values b (length b)))))))

(defun finished (state)
  (ds-finished state))
(defun input-underrun (state)
  (ds-input-underrun state))
(defun output-overflow (state)
  (ds-output-overflow state))

