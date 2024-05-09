(in-package #:org.shirakumo.fraf.trial.mmap)

(pushnew :mmap *features*)

(cffi:defbitfield protection-flag
  (:none          #x0)
  (:read          #x1)
  (:write         #x2)
  (:exec          #x4)
  (:atomic        #x8))

(cffi:defbitfield mmap-flag
  (:shared        #x0000001)
  (:private       #x0000002)
  (:fixed         #x0000010)
  (:anonymous     #x0000020)
  (:grows-down    #x0000100)
  (:locked        #x0002000)
  (:no-reserve    #x0004000)
  (:populate      #x0008000)
  (:non-block     #x0010000)
  (:stack         #x0020000)
  (:huge-table    #x0040000)
  (:sync          #x0080000)
  (:no-replace    #x0100000)
  (:uninitialized #x4000000))

(cffi:defbitfield msync-flag
  (:async         #x1)
  (:invalidate    #x2)
  (:sync          #x4))

(cffi:defcenum madvise-flag
  (:normal            0)
  (:random            1)
  (:sequential        2)
  (:will-need         3)
  (:dont-need         4)
  (:free              8)
  (:remove            9)
  (:dont-fork        10)
  (:do-fork          11)
  (:mergeable        12)
  (:unmergeable      13)
  (:huge-page        14)
  (:no-huge-page     15)
  (:dont-dump        16)
  (:do-dump          17)
  (:wipe-on-fork     18)
  (:keep-on-fork     19)
  (:cold             20)
  (:pageout          21))

(cffi:defbitfield open-flag
  (:read          #o0000000)
  (:write         #o0000002)
  (:create        #o0000100)
  (:ensure-create #o0000200)
  (:dont-claim-tty#o0000400)
  (:truncate      #o0001000)
  (:non-block     #o0004000)
  (:data-sync     #o0010000)
  (:async         #o0020000)
  (:direct        #o0040000)
  (:large-file    #o0100000)
  (:directory     #o0200000)
  (:no-follow     #o0400000)
  (:file-sync     #o4010000))

(cffi:defctype size-t
  #+64-bit :uint64
  #+32-bit :uint32)

(cffi:defctype offset-t
  #+(or 64-bit bsd) :int64
  #-(or 64-bit bsd) :int32)

(cffi:defcfun strerror :string
  (errnum :int))

(cffi:defcvar errno :int)

(cffi:defcfun (u-open "open") :int
  (pathname :string)
  (mode open-flag))

(cffi:defcfun (u-close "close") :int
  (fd :int))

;; (cffi:defcfun (u-fstat "fstat") :int
;;   (fd :int)
;;   (buffer :pointer))

;; (cffi:defcstruct stat
;;   (device ))

(cffi:defcfun (u-mmap "mmap") :pointer
  (address :pointer)
  (length size-t)
  (protection protection-flag)
  (flags mmap-flag)
  (fd :int)
  (offset offset-t))

(cffi:defcfun (u-munmap "munmap") :int
  (address :pointer)
  (length size-t))

(cffi:defcfun (u-msync "msync") :int
  (address :pointer)
  (length size-t)
  (flags msync-flag))

(cffi:defcfun (u-mprotect "mprotect") :int
  (address :pointer)
  (length size-t)
  (flags protection-flag))

(cffi:defcfun (u-madvise "madvise") :int
  (address :pointer)
  (length size-t)
  (advice madvise-flag))

(defun check-posix (result)
  (unless result
    (error-mmap errno (strerror errno))))

(declaim (notinline %mmap))
(defun %mmap (path size offset open protection mmap)
  (declare (type fixnum open protection mmap))
  (declare (optimize speed))
  (let ((fd -1)
        (error-handler (constantly nil)))
    (etypecase path
      ((and fixnum unsigned-byte)
        (setf fd path)
        ;; If an fd is provided, the burden ought to be on the caller to
        ;; provide the size as well
        (check-type size unsigned-byte))
      (string
       (setf fd (u-open path open)
             error-handler (lambda (e)
                            (declare (ignore e))
                            (check-posix (= 0 (u-close fd)))))
       (check-posix (<= 0 fd))
       (unless size
         (with-open-file (stream path :direction :input :element-type '(unsigned-byte 8))
           (setf size (- (file-length stream) offset)))))
      (null))
    (handler-bind ((error error-handler))
      (let ((addr (u-mmap (cffi:null-pointer)
                          size
                          protection
                          mmap
                          fd
                          offset)))
        (check-posix (/= (1- (ash 1 64)) (cffi:pointer-address addr)))
        (values addr fd size)))))

(defun mmap (path &key (open '(:read)) (protection '(:read)) (mmap '(:private)) size (offset 0))
  (%mmap (translate-path path)
         size offset
         (cffi:foreign-bitfield-value 'open-flag open)
         (cffi:foreign-bitfield-value 'protection-flag protection)
         (cffi:foreign-bitfield-value 'mmap-flag mmap)))

(define-compiler-macro mmap (&environment env path &key (open ''(:read)) (protection ''(:read)) (mmap ''(:private)) size (offset 0))
  `(%mmap ,(cfold env `(translate-path ,path) path)
          ,size ,offset
          ,(cfold env `(cffi:foreign-bitfield-value 'open-flag ,open) open)
          ,(cfold env `(cffi:foreign-bitfield-value 'protection-flag ,protection) protection)
          ,(cfold env `(cffi:foreign-bitfield-value 'mmap-flag ,mmap) mmap)))

(defun munmap (addr fd size)
  (check-posix (= 0 (u-munmap addr size)))
  (when fd (u-close fd))
  NIL)

(defun msync (addr fd size &key (flags '(:sync)))
  (declare (ignore fd))
  (check-posix (= 0 (u-msync addr size (cffi:foreign-bitfield-value 'msync-flag flags))))
  NIL)

(define-compiler-macro msync (&environment env addr fd size &key (flags ''(:sync)))
  (declare (ignore fd))
  `(progn
     (check-posix (= 0 (u-msync ,addr ,size ,(cfold env `(cffi:foreign-bitfield-value 'msync-flag ,flags) flags))))
     NIL))

(defun mprotect (addr size protection)
  (check-posix (= 0 (u-mprotect addr size (cffi:foreign-bitfield-value 'protection-flag protection))))
  NIL)

(define-compiler-macro mprotect (&environment env addr size protection)
  `(progn
     (check-posix (= 0 (u-mprotect ,addr ,size ,(cfold env `(cffi:foreign-bitfield-value 'protection-flag ,protection) protection))))
     NIL))

(defun madvise (addr size advice)
  (check-posix (= 0 (u-madvise addr size advice)))
  NIL)

(define-compiler-macro madvise (&environment env addr size advice)
  `(progn
     (check-posix (= 0 (u-madvise ,addr ,size ,(cfold env `(cffi:foreign-enum-value 'madvise-flag ,advice) advice))))
     NIL))
