# usocket-timeout-sbcl-ccl
Changes to lisp usocket to provide better timeout for SOCKET-CONNECT in USOCKET for ECL and SBCL

Changes:

   * in package.lisp, added   exports `#:already-shutdown-error` and `#:out-of-memory-error` to avoid problem with package reload in sbcl
   
   * in sbcl.lisp 
   
     * added unexported variable `*socket-connect-nonblock-wait*` to activate new method of doing timeouts for SBCL and CCL
     * added functions `%socket-operation-condition-not-connected-p` and `%socket-operation-condition-in-progress-p` to test state of socket
     * in `socket-connect` perform a timeout by 
       1. putting socket into nonblocking mode
       2. connecting, and testing for EINPROGRESS (otherwise, error)
       3. looping with increasing `(SLEEP)` until testing for `(sb-bsd-sockets:socket-peername socket)` doesn't throw error `ENOTCONN`
       
       
Comments:

  * this isn't as proper a solution as using a `poll` but I think it is better than what is there, and it leverages `SB-BSD-SOCKET` so less low level stuff has to be added
  * for SBCL, `%socket-operation-condition-not-connected-p` and `%socket-operation-condition-in-progress-p` is handled by SB-BSD-SOCKET condition type.  This *should* be right, everywhere, and it works on RPi Linux and x64 Mac.
  * for ECL, `%socket-operation-condition-not-connected-p` and `%socket-operation-condition-in-progress-p` assume BSD errno codes except if Linux is in `*features*`.    This is probably wrong for WIN32 and uncommon Unixes.  It works on RPi Linux and x64 Mac.
  
  
  It is enabled only on platforms where it is tested (or likely) to work:
  
  ```
  (defparameter *socket-connect-nonblock-wait*
        ;; trust SBCL errno to be handled correctly in SB-BSD-SOCKETS on all platforms
        #+sbcl
        t
        ;; trust that errno is done correctly above - how are BSD flavors marked in *features*?
        #+(and (or ecl mkcl) (or darwin linux openbsd freebsd netbsd bsd))
        t
        ;; for all other cases, we have no reason to think we handle errno correctly in
        ;; functions %socket-operation-condition-*
        #+(or clasp
      	      (and (or ecl mkcl) (not (or darwin linux openbsd freebsd netbsd bsd))))
        nil)
  
  ```
