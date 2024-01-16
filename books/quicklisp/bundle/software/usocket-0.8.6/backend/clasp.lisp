(in-package :usocket)

#-clasp
(progn
  #-:wsock
  (ffi:clines
   "#include <errno.h>"
   "#include <sys/socket.h>"
   "#include <unistd.h>")
  #+:wsock
  (ffi:clines
   "#ifndef FD_SETSIZE"
   "#define FD_SETSIZE 1024"
   "#endif"
   "#include <winsock2.h>")
  (ffi:clines
   #+:msvc "#include <time.h>"
   #-:msvc "#include <sys/time.h>"
   "#include <ecl/ecl-inl.h>"))
(progn
  #-clasp
  (defun cerrno ()
    (ffi:c-inline () () :int
		  "errno" :one-liner t))
  #+clasp
  (defun cerrno ()
    (sockets-internal:errno))
  
  #-clasp
  (defun fd-setsize ()
    (ffi:c-inline () () :fixnum
		  "FD_SETSIZE" :one-liner t))
  #+clasp
  (defun fd-setsize () (sockets-internal:fd-setsize))

  #-clasp
  (defun fdset-alloc ()
    (ffi:c-inline () () :pointer-void
		  "ecl_alloc_atomic(sizeof(fd_set))" :one-liner t))
  #+clasp (defun fdset-alloc () (sockets-internal::alloc-atomic-sizeof-fd-set))

  #-clasp
  (defun fdset-zero (fdset)
    (ffi:c-inline (fdset) (:pointer-void) :void
		  "FD_ZERO((fd_set*)#0)" :one-liner t))
  #+clasp(defun fdset-zero (fdset) (sockets-internal:fdset-zero fdset))

  #-clasp
  (defun fdset-set (fdset fd)
    (ffi:c-inline (fdset fd) (:pointer-void :fixnum) :void
		  "FD_SET(#1,(fd_set*)#0)" :one-liner t))
  #+clasp(defun fdset-set (fdset fd) (sockets-internal:fdset-set fd fdset))

  #-clasp
  (defun fdset-clr (fdset fd)
    (ffi:c-inline (fdset fd) (:pointer-void :fixnum) :void
		  "FD_CLR(#1,(fd_set*)#0)" :one-liner t))
  #+clasp(defun fdset-clr (fdset fd) (sockets-internal:fdset-clr fd fdset))

  #-clasp
  (defun fdset-fd-isset (fdset fd)
    (ffi:c-inline (fdset fd) (:pointer-void :fixnum) :bool
		  "FD_ISSET(#1,(fd_set*)#0)" :one-liner t))
  #+clasp(defun fdset-fd-isset (fdset fd) (sockets-internal:fdset-isset fd fdset))

  (declaim (inline cerrno
                   fd-setsize
                   fdset-alloc
                   fdset-zero
                   fdset-set
                   fdset-clr
                   fdset-fd-isset))
  #-clasp
  (defun get-host-name ()
    (ffi:c-inline
     () () :object
     "{ char *buf = (char *) ecl_alloc_atomic(257);

        if (gethostname(buf,256) == 0)
          @(return) = make_simple_base_string(buf);
        else
          @(return) = Cnil;
      }" :one-liner nil :side-effects nil))

  #+clasp
  (defun get-host-name ()
    (sockets-internal:get-host-name))

  #-clasp
  (defun read-select (wl to-secs &optional (to-musecs 0))
    (let* ((sockets (wait-list-waiters wl))
           (rfds (wait-list-%wait wl))
           (max-fd (reduce #'(lambda (x y)
                               (let ((sy (sb-bsd-sockets:socket-file-descriptor
                                          (socket y))))
                                 (if (< x sy) sy x)))
                           (cdr sockets)
                           :initial-value (sb-bsd-sockets:socket-file-descriptor
                                           (socket (car sockets))))))
      (fdset-zero rfds)
      (dolist (sock sockets)
        (fdset-set rfds (sb-bsd-sockets:socket-file-descriptor
                         (socket sock))))
      (let ((count
             (ffi:c-inline (to-secs to-musecs rfds max-fd)
                           (t :unsigned-int :pointer-void :int)
                           :int
			   "
          int count;
          struct timeval tv;

          if (#0 != Cnil) {
            tv.tv_sec = fixnnint(#0);
            tv.tv_usec = #1;
          }
        @(return) = select(#3 + 1, (fd_set*)#2, NULL, NULL,
                           (#0 != Cnil) ? &tv : NULL);
" :one-liner nil)))
        (cond
          ((= 0 count)
           (values nil nil))
          ((< count 0)
           ;; check for EINTR and EAGAIN; these should not err
           (values nil (cerrno)))
          (t
           (dolist (sock sockets)
             (when (fdset-fd-isset rfds (sb-bsd-sockets:socket-file-descriptor
                                         (socket sock)))
               (setf (state sock) :READ))))))))

  #+clasp
  (defun read-select (wl to-secs &optional (to-musecs 0))
    (let* ((sockets (wait-list-waiters wl))
           (rfds (wait-list-%wait wl))
           (max-fd (reduce #'(lambda (x y)
                               (let ((sy (sb-bsd-sockets:socket-file-descriptor
                                          (socket y))))
                                 (if (< x sy) sy x)))
                           (cdr sockets)
                           :initial-value (sb-bsd-sockets:socket-file-descriptor
                                           (socket (car sockets))))))
      (fdset-zero rfds)
      (dolist (sock sockets)
        (fdset-set rfds (sb-bsd-sockets:socket-file-descriptor
                         (socket sock))))
      (let ((count (sockets-internal:do-select to-secs to-musecs rfds max-fd)))
        (cond
          ((= 0 count)
           (values nil nil))
          ((< count 0)
           ;; check for EINTR and EAGAIN; these should not err
           (values nil (cerrno)))
          (t
           (dolist (sock sockets)
             (when (fdset-fd-isset rfds (sb-bsd-sockets:socket-file-descriptor
                                         (socket sock)))
               (setf (state sock) :READ))))))))
  )
