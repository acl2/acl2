(in-package "ACL2")

(defparameter *shared-libs-list* nil)

(defun disconnect-shared-libs ()
  (cw "Disconnecting shared libraries.~%")
  (when *shared-libs-list*
    (error "Already have disconnected shared libs?"))
  (let ((state acl2::*the-live-state*)
        (info (loop for lib in ccl::*shared-libraries* collect
                    (cons (ccl::shlib.soname lib)
                          (ccl::shlib.opencount lib)))))
    (loop for (soname . count) in info do
          (b* (((unless (and (stringp soname)
                             (not (equal soname ""))
                             (eql (char soname 0) #\/)))
                (cw "Skipping ~f0.~%" soname))
               ((unless (equal count 1))
                ;; Probably just paranoia
                (er hard? 'magically-grab-abs-shared-libs
                    "Don't know what to do with ~f0 since its count is ~x1.~%"
                    soname count))
               (filename (filename-part soname))
               (- (cw "Copying ~f0 to ~f1.~%" soname filename))
               ((mv erp ?val ?state)
                (sys-call+ "cp" (list soname filename) state))
               ((when erp)
                (er hard? 'magically-grab-abs-shared-libs
                    "Failed to copy ~f0 to ~f1.~%" soname filename)))
            (cw "Closing old shared library.~%")
            (ccl::close-shared-library soname)
            (push filename *shared-libs-list*))))
  (cw "Disconnected shared libraries: ~x0." *shared-libs-list*))

(defun reconnect-shared-libs ()
  (cw "Reconnecting shared libraries.~%")
  (loop for lib in *shared-libs-list* do
        (cw "Opening ~s0.~%" lib)
        (ccl::open-shared-library lib))
  (cw "Done reconnecting shared libraries.~%"))
