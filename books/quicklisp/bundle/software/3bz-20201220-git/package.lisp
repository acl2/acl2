(defpackage 3bz
  (:use :cl)
  (:import-from :alexandria
                #:with-gensyms
                #:once-only
                #:ensure-list)

  (:import-from #+mezzano #:mezzano.internals
                #-mezzano #:nibbles
                #:ub16ref/le
                #:ub32ref/le
                #:ub64ref/le)
  (:export
   #:decompress
   #:decompress-vector
   #:with-octet-pointer
   #:make-octet-vector-context
   #:make-octet-stream-context
   #:make-octet-pointer-context
   #:make-deflate-state
   #:make-zlib-state
   #:make-gzip-state
   #:finished
   #:input-underrun
   #:output-overflow
   #:%resync-file-stream
   #:replace-output-buffer))

