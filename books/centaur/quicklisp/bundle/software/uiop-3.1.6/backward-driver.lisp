;;;; -------------------------------------------------------------------------
;;; Hacks for backward-compatibility of the driver

(uiop/package:define-package :uiop/backward-driver
  (:nicknames :asdf/backward-driver)
  (:recycle :uiop/backward-driver :asdf/backward-driver :asdf)
  (:use :uiop/common-lisp :uiop/package :uiop/utility
   :uiop/pathname :uiop/stream :uiop/os :uiop/image
   :uiop/run-program :uiop/lisp-build :uiop/configuration)
  (:export
   #:coerce-pathname #:component-name-to-pathname-components
   #+(or clasp ecl mkcl) #:compile-file-keeping-object
   #:user-configuration-directories #:system-configuration-directories
   #:in-first-directory #:in-user-configuration-directory #:in-system-configuration-directory
   ))
(in-package :uiop/backward-driver)

;;;; Backward compatibility with various pathname functions.

(with-upgradability ()
  (defun coerce-pathname (name &key type defaults)
    ;; For backward-compatibility only, for people using internals
    ;; Reported users in quicklisp: hu.dwim.asdf, asdf-utils, xcvb
    ;; Will be removed after 2014-01-16.
    ;;(warn "Please don't use ASDF::COERCE-PATHNAME. Use ASDF/PATHNAME:PARSE-UNIX-NAMESTRING.")
    (parse-unix-namestring name :type type :defaults defaults))

  (defun component-name-to-pathname-components (unix-style-namestring
                                                 &key force-directory force-relative)
    ;; Will be removed after 2014-01-16.
    ;; (warn "Please don't use ASDF::COMPONENT-NAME-TO-PATHNAME-COMPONENTS, use SPLIT-UNIX-NAMESTRING-DIRECTORY-COMPONENTS")
    (multiple-value-bind (relabs path filename file-only)
        (split-unix-namestring-directory-components
         unix-style-namestring :ensure-directory force-directory)
      (declare (ignore file-only))
      (when (and force-relative (not (eq relabs :relative)))
        (error (compatfmt "~@<Absolute pathname designator not allowed: ~3i~_~S~@:>")
               unix-style-namestring))
      (values relabs path filename)))

  #+(or clasp ecl mkcl)
  (defun compile-file-keeping-object (&rest args) (apply #'compile-file* args))

  ;; Backward compatibility for ASDF 2.27 to 3.1.4
  (defun user-configuration-directories ()
    "Return the current user's list of user configuration directories
for configuring common-lisp.
    DEPRECATED. Use uiop:xdg-config-pathnames instead."
    (xdg-config-pathnames "common-lisp"))
  (defun system-configuration-directories ()
    "Return the list of system configuration directories for common-lisp.
    DEPRECATED. Use uiop:config-system-pathnames instead."
    (system-config-pathnames "common-lisp"))
  (defun in-first-directory (dirs x &key (direction :input))
    "Finds the first appropriate file named X in the list of DIRS for I/O
in DIRECTION \(which may be :INPUT, :OUTPUT, :IO, or :PROBE).
   If direction is :INPUT or :PROBE, will return the first extant file named
X in one of the DIRS.
   If direction is :OUTPUT or :IO, will simply return the file named X in the
first element of DIRS that exists. DEPRECATED."
    (find-preferred-file
     (mapcar #'(lambda (dir) (subpathname (ensure-directory-pathname dir) x)) dirs)
     :direction direction))
  (defun in-user-configuration-directory (x &key (direction :input))
    "Return the file named X in the user configuration directory for common-lisp.
DEPRECATED."
    (xdg-config-pathname `("common-lisp" ,x) direction))
  (defun in-system-configuration-directory (x &key (direction :input))
    "Return the pathname for the file named X under the system configuration directory
for common-lisp. DEPRECATED."
    (find-preferred-file (system-config-pathnames "common-lisp" x) :direction direction)))
