(defpackage #:mmap
  (:nicknames #:org.shirakumo.fraf.trial.mmap)
  (:use #:cl)
  (:export
   #:mmap-error
   #:code
   #:message
   #:mmap
   #:munmap
   #:msync
   #:mprotect
   #:madvise
   #:with-mmap))
