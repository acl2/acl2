; NOTE: An Allegro CL dynamic runtime license is needed in order for this to
; create an Allegro CL ACL2 application acl2.exe in the bin/ directory.
; See target allegro-app in GNUmakefile.

#|

Execute the following form from the ACL2 sources directory, setting the
variable *acl2-application-distributed-books-dir* if necessary as shown below
(probably not necessary).

echo '(generate-application "acl2.exe" (or (sys::getenv "ACL2_BIN_DIR") "app/") (quote ("../build-image.cl")) :runtime :dynamic :include-compiler t)' \
| lisp >& generate-application.log&

Then look at generate-application.log and see if it's OK, especially near the end.

|# ; |

; The file our-develenv.cl will not be distributed with ACL2.  It is obtained
; from a path such as <path-to-allegro>/AllegroCL-7.0/acl70/develenv.cl, then
; commenting out those not allowed in runtime images, as suggested in the above
; file.
(load "our-develenv.cl")

(load "init.lisp")

(in-package "ACL2")

; The sources had better already be compiled!  The following form just informs
; ACL2 of that fact.
(note-compile-ok)

; We are attempting to replicate the effects of this form from the Makefile:
; (acl2::save-acl2 (quote (acl2::initialize-acl2 (quote acl2::include-book) acl2::*acl2-pass-2-files* t)) "${PREFIXsaved_acl2}")

; From save-acl2
(load-acl2)
(setq *saved-build-date* (saved-build-date-string))
; It is legal to replace nil below by, e.g., "/u/acl2/v2-9/acl2-sources/books/".
(defconstant *acl2-application-distributed-books-dir* nil)
(initialize-acl2 (quote include-book) *acl2-pass-2-files* *acl2-application-distributed-books-dir*)

; Adapted from save-acl2-in-allegro
	 (setq *saved-mode*
	       (quote (initialize-acl2 (quote include-book)
				       *acl2-pass-2-files*
                                       *acl2-application-distributed-books-dir*)))
	 (tpl:setq-default *PACKAGE* (find-package "ACL2"))
	 (setq EXCL:*RESTART-INIT-FUNCTION* 'acl2-default-restart)
         (load "allegro-acl2-trace.lisp")

; Copied exactly from acl2-init.lisp:
(defvar *acl2-default-restart-complete* nil)

; Copied exactly from acl2-init.lisp:
(defun acl2-default-restart ()
  (if *acl2-default-restart-complete*
      (return-from acl2-default-restart nil))
  (format t *saved-string*
          *copy-of-acl2-version*
          *saved-build-date*
          (cond (*saved-mode*
                 (format nil "~% Initialized with ~a." *saved-mode*))
                (t ""))
          (eval '(latest-release-note-string)) ; avoid possible warning
          )
  (maybe-load-acl2-init)
  (in-package "ACL2")

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

; Now optionally include some books.

;(load "/home/kaufmann/foo.fasl")
