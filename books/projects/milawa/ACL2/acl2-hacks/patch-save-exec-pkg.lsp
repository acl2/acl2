;; Patch by Matt Kaufmann to permit ACL2 to save the :q package when save-exec
;; is called.

(in-package "ACL2")

(defvar *startup-package-name* "ACL2")

(defun save-exec (exec-filename extra-startup-string)

  ":Doc-Section Other

  save an executable image and (for most Common Lisps) a wrapper script~/

  ~l[saving-and-restoring] for an explanation of why one might want to use this
  function.
  ~bv[]
  Examples:
  ; Save an executable named my-saved_acl2:
  (save-exec \"my-saved_acl2\"
             \"This saved image includes Version 7 of Project Foo.\")

  ; Same as above, but with a generic comment instead:
  (save-exec \"my-saved_acl2\" nil)~/
  General Form:
  (save-exec exec-filename extra-startup-string)
  ~ev[]
  where ~c[exec-filename] is the filename of the proposed executable and
  ~c[extra-startup-string] is a non-empty string to be printed after the normal
  ACL2 startup message when you start up the saved image.  However,
  ~c[extra-startup-string] is allowed to be ~c[nil], in which case a generic
  string will be printed instead.

  ~st[Note]: For technical reasons, we require that you first execute ~c[:q], to
  exit the ACL2 read-eval-print loop, before evaluating a ~c[save-exec] call.

  For most Common Lisps, the specified file (e.g., ~c[\"my-saved_acl2\"] in the
  examples above) will be written as a small script, which in turn invokes a
  saved image to which an extension has been appended (e.g.,
  ~c[my-saved_acl2.gcl] for the examples above, when the underlying Common Lisp
  is GCL on a non-Windows system).~/"

  #-acl2-loop-only
  (progn
    (if (not (eql *ld-level* 0))
        (er hard 'save-exec
            "Please type :q to exit the ACL2 read-eval-print loop and then try ~
             again."))
    (if (equal extra-startup-string "")
        (er hard 'save-exec
            "The extra-startup-string argument of save-exec must be ~x0 or ~
             else a non-empty string."
            nil)
      (setq *saved-string*
            (format
             nil
             "~a~%MODIFICATION NOTICE:~%~%~a~%"
             *saved-string*
             (cond ((null extra-startup-string)
                    "This ACL2 executable was created by saving a session.")
                   (t extra-startup-string)))))
    #-(or gcl cmu sbcl allegro clisp openmcl)
    (er hard 'save-exec
        "Sorry, but save-exec is not implemented for this Common Lisp.~a0"
        #+lispworks "  If you care to investigate, see the comment in ~
                     acl2-init.lisp starting with: ``The definition of ~
                     save-exec-raw for lispworks (below) did not work.''"
        #-lispworks "")

; The forms just below, before the call of save-exec-raw, are there so that the
; initial (lp) will set the :cbd correctly.

    (f-put-global 'connected-book-directory nil *the-live-state*)
    (setq *initial-cbd* nil)
    (setq *lp-ever-entered-p* nil)
    (setq *startup-package-name* (package-name *package*))
    (setq *saved-build-date*

; By using setq here for *saved-build-date* instead of a let-binding for
; save-exec-raw, it happens that saving more than once in the same session (for
; Lisps that allow this, such as Allegro CL but not GCL) would result in extra
; "; then ..." strings.  But that seems a minor problem, and avoids having to
; think about the effect of having a let-binding in force above a save of an
; image.

          (concatenate 'string
                       *saved-build-date*
                       "; then "
                       (saved-build-date-string)))
    (save-exec-raw exec-filename))
  #+acl2-loop-only
  (declare (ignore exec-filename extra-startup-string))
  nil ; Won't get to here in GCL and perhaps other lisps
  )

(defun acl2-default-restart ()
  (if *acl2-default-restart-complete*
      (return-from acl2-default-restart nil))

  #+openmcl
  (progn

; In OpenMCL, print greeting now, rather than upon first re-entry to ACL2 loop.
; Here we follow a suggestion from Gary Byers.

    (format t "~&Welcome to ~A ~A!~%"
            (lisp-implementation-type)
            (lisp-implementation-version))
    (setq ccl::*inhibit-greeting* t))
  #+hons (funcall 'hons-init)
  (format t *saved-string*
          (acl2-version+)
          *saved-build-date*)
  (maybe-load-acl2-init)
  (eval `(in-package ,*startup-package-name*))

; The following two lines follow the recommendation in Allegro CL's
; documentation file doc/delivery.htm.

  #+allegro (tpl:setq-default *package* (find-package "ACL2"))
  #+allegro (rplacd (assoc 'tpl::*saved-package*
                           tpl:*default-lisp-listener-bindings*)
                    'common-lisp:*package*)

  #+allegro (lp)
  #+openmcl (eval '(lp)) ; using eval to avoid compiler warning

; See the comment in save-acl2-in-lispworks for why we need the following call.

  #+lispworks (mp:initialize-multiprocessing)

  ;;Lispworks 4.2.0 no longer recognizes the following:
  ;;#+lispworks (lw::extend-current-stack 1000)

  (setq *acl2-default-restart-complete* t)
  nil)

#+openmcl
(defun save-acl2-in-openmcl (sysout-name &optional mode core-name)
  (declare (ignore mode))
  (eval `(in-package ,*startup-package-name*))
  #-acl2-mv-as-values (proclaim-files)
; We do the following load when *suppress-compile* in save-acl2, but it's
; harmless enough to do it again here in case *suppress-compile* is set to t.
  #+acl2-mv-as-values (load "acl2-proclaims.lisp")
  (load "openmcl-acl2-trace.lisp")
  (save-acl2-in-openmcl-aux sysout-name core-name))

(defun lp (&rest args)

; This function can only be called from within raw lisp, because no
; ACL2 function mentions it.  Thus, we assume we are in raw lisp.
; This is the top-level entry to ACL2.  Note that truename can cause an error
; in some Common Lisps when the given file or directory does not exist.  Hence,
; we sometimes call truename on "" rather than on a file name.

  (let ((state *the-live-state*)
        #+(and gcl (not ansi-cl)) (lisp::*break-enable*
                                   (eq (debugger-enable *the-live-state*) t))
        (raw-p
         (cond
          ((null args) nil)
          ((equal args '(raw)) 'raw)
          (t (error "LP either takes no args or a single argument, 'raw.")))))
    (cond
     ((> *ld-level* 0)
      (when (raw-mode-p *the-live-state*)
        (fms "You have attempted to enter the ACL2 read-eval-print loop from ~
              within raw mode.  However, you appear already to be in that ~
              loop.  If your intention is to leave raw mode, then execute:  ~
              :set-raw-mode nil.~|"
             nil (standard-co *the-live-state*) *the-live-state* nil))
      (return-from lp nil))
     (*lp-ever-entered-p*
      (f-put-global 'standard-oi
                    (if (and raw-p (not (raw-mode-p state)))
                        (cons '(set-raw-mode t)
                              *standard-oi*)
                      *standard-oi*)
                    *the-live-state*)
      (with-warnings-suppressed
       (ld-fn (f-get-ld-specials *the-live-state*)
              *the-live-state*
              nil)))
     (t (eval `(in-package ,*startup-package-name*))

; Acl2-default-restart isn't enough in Allegro, at least, to get the new prompt
; when we start up:

        (let* ((system-dir (getenv$-raw "ACL2_SYSTEM_BOOKS"))
               (user-home-dir-path (user-homedir-pathname))
               (user-home-dir0 (and user-home-dir-path
                                    (namestring user-home-dir-path)))
               (user-home-dir (if (eql (char user-home-dir0
                                             (1- (length user-home-dir0)))
                                       *directory-separator*)
                                  (subseq user-home-dir0
                                          0
                                          (1- (length user-home-dir0)))
                                user-home-dir0)))
          (when system-dir
            (f-put-global 'distributed-books-dir system-dir *the-live-state*))
          (when user-home-dir
            (f-put-global 'user-home-dir user-home-dir *the-live-state*)))
        #-hons
; Hons users are presumably advanced enough to tolerate the lack of a
; "[RAW LISP]" prompt.
        (install-new-raw-prompt)
        (setq *lp-ever-entered-p* t)
        #+(and (not acl2-loop-only) acl2-rewrite-meter)
        (setq *rewrite-depth-alist* nil)

; Without the following call, it was impossible to read and write with ACL2 I/O
; functions to *standard-co* in CLISP 2.30.  Apparently the appropriate Lisp
; streams at the time of the build were closed when the ACL2 image was brought
; up.  So we "refresh" the appropriate property lists with the current such
; Lisp streams.

        (setup-standard-io)

; The following applies to CLISP 2.30, where charset:iso-8859-1 is defined, not to
; CLISP 2.27, where charset:utf-8 is not defined.  It apparently has to be
; executed in the current Lisp session.  We tried executing the following form
; before saving an image, but the value of custom:*default-file-encoding* at
; startup was #<ENCODING CHARSET:ASCII :UNIX>.

        #+(and clisp unicode)
        (setq custom:*default-file-encoding* charset:iso-8859-1)
        #+mswindows
        (cond
         ((null (f-get-global 'mswindows-drive *the-live-state*))
          (let* ((str (namestring (truename "")))
                 (posn (position #\: str)))
            (cond
             ((null posn)
              (er soft 'LP
                  "We are unable to determine the drive using ~
                   (namestring (truename \"\")), which evaluates to ~p0."
                  str)
              (return-from lp nil)))
            (f-put-global 'mswindows-drive
                          (subseq str 0 (1+ posn))
                          *the-live-state*))))
        (cond ((f-get-global 'connected-book-directory *the-live-state*) nil)
              ((null *initial-cbd*)
               (setq *initial-cbd*
                     (pathname-os-to-unix
                      (namestring (truename

; See the comment in save-acl2-in-allegro, which mentions a comment present
; before Version_2.5 that was present here as well.

                                   ""))
                      *the-live-state*))

; In openmcl, it seems that *initial-cbd* as computed above could give a string
; not ending in "/".  We fix that here.

               (cond ((and (stringp *initial-cbd*)
                           (not (equal *initial-cbd* ""))
                           (not (eql (char *initial-cbd*
                                           (1- (length *initial-cbd*)))
                                     #\/)))
                      (setq *initial-cbd*
                            (concatenate 'string *initial-cbd* "/"))))
               (cond ((not (absolute-pathname-string-p
                            *initial-cbd*
                            t
                            (os (w *the-live-state*))))
                      (er soft 'LP
                          "Our guess for the initial setting of cbd, ~x0, ~
                           which was generated by (pathname-os-to-unix ~
                           (namestring (truename \"\")) *the-live-state*), ~
                           is not a legal directory!  Before entering ACL2, ~
                           please setq *initial-cbd* to a nonempty string ~
                           that represents an absolute ACL2 (i.e., ~
                           Unix-style) pathname.  Sorry for the inconvenience."
                          *initial-cbd*)
                      (return-from lp nil)))
               (f-put-global 'connected-book-directory *initial-cbd*
                             *the-live-state*))
              ((not (absolute-pathname-string-p *initial-cbd*
                                                t
                                                (os (w *the-live-state*))))
               (er soft 'LP
                   "The current setting of *initial-cbd*, ~x0, is ~
                    not a directory.  Before entering ACL2, please ~
                    setq *initial-cbd* to a nonempty string that ~
                    represents the absolute ACL2 (i.e., Unix-style) ~
                    pathname of a directory. See :DOC cbd."
                   *initial-cbd*
                   *directory-separator*)
               (return-from lp nil))
              (t
               (f-put-global 'connected-book-directory *initial-cbd*
                             *the-live-state*)))
        (let ((customization-full-file-name
               (let* ((cb1 (our-merge-pathnames
                            (f-get-global 'connected-book-directory
                                          *the-live-state*)
                            "acl2-customization"))
                      (cfb1 (string-append cb1 ".lisp")))
                 (if (probe-file (pathname-unix-to-os cfb1 *the-live-state*))
                     cfb1
                   (let* ((cb2

; There is not a true notion of home directory for Windows systems, as far as
; we know.  We may provide one at a future point, but for now, we simply act as
; though ~/acl2-customization.lisp does not exist on such systems.

                           #+mswindows
                           nil
                           #-mswindows
                           (our-merge-pathnames

; The call of pathname-os-to-unix below may seem awkward, since later we apply
; pathname-unix-to-os before calling probe-file.  However, our-merge-pathnames
; requires Unix-style pathname arguments, and we prefer not to write an
; analogous function that takes pathnames for the host operating system.

                            (pathname-os-to-unix
                             (namestring

; MCL does not seem to handle calls of truename correctly on logical pathnames.
; We should think some more about this, but for now, let's solve this problem
; by brute force.

                              #+(and mcl (not openmcl))
                              (truename
                               (common-lisp::translate-logical-pathname
                                (user-homedir-pathname)))
                              #-(and mcl (not openmcl))
                              (truename (user-homedir-pathname)))
                             *the-live-state*)
                            "acl2-customization"))
                          (cfb2 (and cb2 (string-append cb2 ".lisp"))))
                     (if (and cfb2
                              (probe-file (pathname-unix-to-os
                                           cfb2 *the-live-state*)))
                         cfb2
                       nil))))))
          (cond
           ((and customization-full-file-name
                 (not (global-val 'boot-strap-flg (w state))))

; If the file "acl2-customization.lisp" on the current directory exists (and we
; are not booting) and it hasn't been included yet, we include it first.  If it
; does not exist, but it exists on the user's home directory, then we include
; that.  Because of the ld-skip-proofsp setting we use, no warning is printed
; if "acl2-customization.lisp" is uncertified.  But it will prevent the
; production of truly certified books in any session in which it has been
; included, so we check it explicitly below and warn the user.

            (fms "Customizing with ~x0.~%"
                 (list (cons #\0 customization-full-file-name))
                 *standard-co*
                 state
                 nil)
            (let ((old-infixp (f-get-global 'infixp *the-live-state*)))
              (f-put-global 'infixp nil *the-live-state*)
              (with-warnings-suppressed
               (ld-fn (put-assoc-eq
                       'standard-oi
                       (if (and raw-p (not (raw-mode-p state)))
                           (cons '(set-raw-mode t)
                                 customization-full-file-name)
                         customization-full-file-name)
                       (put-assoc-eq
                        'ld-error-action :return
                        (f-get-ld-specials *the-live-state*)))
                      *the-live-state*
                      nil))
              (f-put-global 'infixp old-infixp *the-live-state*))))
          (f-put-global 'standard-oi
                        (if (and raw-p (not (raw-mode-p state)))
                            (cons '(set-raw-mode t)
                                  *standard-oi*)
                          *standard-oi*)
                        *the-live-state*)
          (f-put-global 'ld-error-action :continue *the-live-state*)
          (with-warnings-suppressed
           (ld-fn (f-get-ld-specials state)
                  *the-live-state*
                  nil)))))
    (fms "Exiting the ACL2 read-eval-print loop.  To re-enter, execute (LP)."
         nil *standard-co* *the-live-state* nil)
    (values)))
