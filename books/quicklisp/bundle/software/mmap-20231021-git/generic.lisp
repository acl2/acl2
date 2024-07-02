(in-package #:org.shirakumo.fraf.trial.mmap)

(define-condition mmap-error (simple-error)
  ((code :initarg :code :reader code)
   (message :initarg :message :reader message))
  (:report (lambda (c s) (format s "Failed to mmap file (E~d):~%  ~a"
                                 (code c) (message c)))))

(defun error-mmap (code message)
  (error 'mmap-error :code code :message message))

(defun cfold (env form &rest vars)
  (if (loop for var in vars
            always (constantp var env))
      `(load-time-value ,form)
      form))

(defun translate-path (path)
  (etypecase path
    #+unix
    ((unsigned-byte #+64-bit 64 #-64-bit 32) path)
    (string path)
    (pathname (uiop:native-namestring path))
    (null)))

#-(or unix windows)
(defun mmap (path &key open protection mmap)
  (error "Platform not supported."))

#-(or unix windows)
(defun munmap (addr fd size)
  (error "Platform not supported."))

#-(or unix windows)
(defun msync (addr size &key flags)
  (error "Platform not supported."))

#-(or unix windows)
(defun mprotect (addr size protection)
  (error "Platform not supported."))

#-(or unix windows)
(defun madvise (addr size advice)
  (error "Platform not supported."))

(defmacro with-mmap ((addr fd size path &rest args &key dont-close &allow-other-keys) &body body)
  (let ((addrg (gensym "ADDR"))
        (fdg (gensym "FD"))
        (sizeg (gensym "SIZE"))
        (args (copy-list args)))
    (remf args :dont-close)
    `(multiple-value-bind (,addrg ,fdg ,sizeg) (mmap ,path ,@args)
       (unwind-protect
            (let ((,addr ,addrg)
                  (,fd ,fdg)
                  (,size ,sizeg))
              (declare (ignorable ,fd ,size))
              ,@body)
         (munmap ,addrg ,(unless dont-close fdg) ,sizeg)))))
