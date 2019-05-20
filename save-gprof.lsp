; ACL2 Version 8.2 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2019, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

; This is a file for building a profiling ACL2/GCL image.  It also allows
; functions in specified books to be profiled.  We thank Camm Maguire for
; providing an initial version of the code below, to which we have made
; relatively small modifications, and for considerable expert advice.  We also
; thank David Hardin for inspiring this effort and for his help.

;;; TABLE OF CONTENTS
;;; -----------------
;;; Preconditions.
;;; How to use a profiling ACL2/GCL executable.
;;; How to build a profiling ACL2/GCL executable.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Preconditions.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (1) You will need a profiling GCL image. In a Debian GCL installation, it
; should suffice to execute

; setenv GCL_PROF t

; before invoking GCL.  You have started up a profiling GCL image if and only
; if the word "profiling" appears in the GCL startup banner.  On non-Debian
; systems you may need to build gcl by hand by adding the --enable-gprof option
; to ./configure.  You might also find that you need to increase the default
; maxpages.

; (2) Rename init.lisp as follows:

; mv init.lisp init.lisp.ori

; (3) Follow the steps in "How to build a profiling ACL2/GCL executable" below,
; with book-name-list set to nil.

; NOTE: If you only want to profile ACL2 system functions, not functions
; defined in books, skip steps (4) through (6).

; (4) Put the form

; (setq compiler::*default-system-p* t)

; into a file ~/acl2-init.lsp.  This will cause GCL to create .o files that are
; suitable for profiling.

; (5) Certify all books of interest using the ACL2 executable you built in (3).
; These are the books containing functions that you want to profile.  Be sure
; first to remove any existing .cert files for these books if you are using
; "make certify-books" (or any method that avoids recertification of books that
; are already certified).  Example:

; make certify-books-fresh ACL2=/u/acl2/rel/gcl-gprof-saved_acl2

; (6) Optionally start up the ACL2 executable you built in (3), if you want
; user-defined *1* functions (executable counterparts) to be compiled too.
; Then in the ACL2 loop, include books with functions that you want to profile,
; which should have been certified in step (5), and then execute the following
; forms, which will create and compile file TMP2.lisp.

; (comp-fn :exec nil "2" state)

; Then exit ACL2 with (good-bye).

;;; End of "Preconditions."

; Now, follow the steps in "How to build a profiling ACL2/GCL executable" below
; (a second time, since you already executed (3) above), using the "books of
; interest" in (5) above for step (A) below.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; How to build a profiling ACL2/GCL executable.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (A) Load this file in a profiling GCL and evaluate the function it defines,
; as follows.

; (load "save-gprof.lsp")
; (save-profiling-image book-name-list)

; where book-name-list is a list of book names (without .lisp extensions),
; where both relative and absolute pathnames are allowed.

; If this is your initial build (from step (3) above), use book-name-list =
; nil:

; (save-profiling-image nil)

; Otherwise, for example:

; (save-profiling-image
;   '("books/arithmetic/top-with-meta"
;     "books/data-structures/number-list-theory")
;   :tmp2 t)

; There are keyword arguments you may optionally supply (including :tmp2 above,
; which is also optional), as explained in the following example that shows
; their defaults.

; (save-profiling-image
;  '("books/arithmetic/top-with-meta"
;    "books/data-structures/number-list-theory")
;  :clean t ; Default behavior, if :clean is not supplied, is to recompile ACL2
;           ; source files exactly when axioms.o does not exist or
;           ; book-name-list is nil.  Specify :clean nil to recompile exactly
;           ; when axioms.o does not exist.  Specify :clean t to recompile
;           ; unconditionally.
;  :dir nil ; If not nil then this is a directory string, ending in slash, to
;           ; which "books/" should be appended to find the distributed books.
;  :tmp2 nll; When t, a TMP2.o file should exist (see step (6) above) to be
;           ; included for profiling.
;  )

; (B) Quit out of GCL, (good-bye).

; (C) Rename the resulting executable as desired.  For example:

; mv nsaved_acl2.gcl gcl-gprof-saved_acl2

; or, in a later pass,

; mv nsaved_acl2.gcl gcl-gprof-books-saved_acl2

; (D) Delete the wrapper script.

; rm nsaved_acl2

; (E) When all use of save-gprof.lsp is completed, optionally restore init.lisp:

; mv init.lisp.ori init.lisp

; (F) Delete the file ~/acl2-init.lsp if it was created in step (4).

;;; End of "How to build a profiling ACL2/GCL executable."

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; How to use a profiling ACL2/GCL executable.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here is an example.  Start up a profiling ACL2/GCL executable that was built
; as described above.  Then submit the following forms.  Profiling information
; should appear after the last one, showing information about ACL2 source
; functions and also numeric-sort.

; (include-book "books/data-structures/number-list-theory")
; :q
; ; ONLY if you provided :tmp2 t with save-profiling-image above, in which
; ; case, include all books that were included when TMP2.o was created.
; ; NOTE that this does not seem to work if an absolute pathname is used, so if
; ; you are in a different directory from TMP2.o, you will need to create a
; ; soft link.
; (load "TMP2.o")
; ; If GCL aborts with the following, then next time try preceding the
; ; following with (si::sgc-on nil) and then optionally following it with
; ; (si::sgc-on t).
; (si::gprof-start)
; (lp)
; (length (numeric-sort (reverse (fromto 0 5000))))
; :q
; (si::gprof-quit)

; Note: temporary files, for example produced by calls of COMP, are not deleted
; in profiling images.  Nor is the process id used in their names, so two
; processes should not run with profiling in the same directory, or their
; temporary files could step on each other.  If this is a problem for you,
; please contact the ACL2 developers and we will see if we can improve the
; situation.

;;; End of "How to use a profiling ACL2/GCL executable."

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun save-profiling-image (my-books &key dir (clean t clean-p) tmp2)

; Clean by default, except if books are supplied since in that case we
; presumably already built a profiling image without books and can re-use the
; object files.

  (if (and my-books (not clean-p))
      (setq clean nil))
  (let ((si::*collect-binary-modules*

; Collect a list of names of each object file loaded

         t)
        si::*binary-modules*
        (compiler::*default-system-p*

; The .o files are to be linked in via ld; must be compiled with :system-p t.

         t))

    (let ((com

; This is a command to build acl2 which will be run twice -- once in stock gcl,
; compiling files, loading and recording same once in an image which is linked
; via ld from the results of the above redirecting each load to an
; initialization of the .o file already linked into the image by ld.

           `(let ((my-books ',my-books)
                  (tmp2 ',tmp2)
                  (save-dir ,(or dir
                                 (concatenate 'string
                                              (namestring (truename ""))
                                              "books/")))
                  (clean ,clean))
              (load "init.lisp.ori")

; Note that acl2::load-acl2 doesn't exist at read-time; similarly for other
; acl2 package symbols.

              (let* ((la (find-symbol "LOAD-ACL2" "ACL2"))
                     (sym-status-file (find-symbol "*ACL2-STATUS-FILE*"
                                                   "ACL2"))
                     (olf (symbol-function la))
                     (si::*collect-binary-modules*

; Make sure the second pass watches for .o loads, for the purpose of triggering
; an error.

                      t))
                (unless (probe-file "axioms.o") ; no sense in compiling twice
                  (funcall (symbol-function (find-symbol "COMPILE-ACL2" "ACL2")))

; Prevent package error when loading after compiling:

                  (delete-package "ACL2-PC"))
                (funcall olf) ; must load-acl2 to establish the symbols below
                (defparameter user::*fast-acl2-gcl-build* t)

; Keep temp files around, and do not use process id in their names.

                (defparameter user::*acl2-keep-tmp-files* :no-pid)
                (let ((sa (find-symbol "SAVE-ACL2" "ACL2"))
                      (ia (find-symbol "INITIALIZE-ACL2" "ACL2"))
                      (ib (find-symbol "INCLUDE-BOOK" "ACL2"))
                      (ap2f (find-symbol "*ACL2-PASS-2-FILES*" "ACL2"))
                      (osf (symbol-function 'si::save-system))
                      (sym-initial-cbd (find-symbol "*INITIAL-CBD*" "ACL2"))
                      (sym-pathname-os-to-unix (find-symbol
                                                "PATHNAME-OS-TO-UNIX"
                                                "ACL2"))
                      (sym-state (find-symbol "*THE-LIVE-STATE*" "ACL2"))
                      (sym-f-put-global (find-symbol "F-PUT-GLOBAL" "ACL2"))
                      (sym-ld (find-symbol "LD" "ACL2"))
                      (sym-cbd (find-symbol "CONNECTED-BOOK-DIRECTORY"
                                            "ACL2")))
                  (setf (symbol-function la)

; Save-acl2 calls load-acl2, but we can't load twice when initializing in reality.

                        (lambda () nil))

; Restore all moved functions on save-system.

                  (setf (symbol-function 'si::save-system)
                        (lambda (x)
                          (setf (symbol-function la) olf)
                          (setf (symbol-function 'si::save-system) osf)
                          (when si::*binary-modules*

; Saving when a .o has been loaded is a no-no.

                            (error "Loading binary modules prior to image save ~
                                    in save-gprof.lsp:~%  si::*binary-modules* ~
                                    = ~%~S~%"
                                   si::*binary-modules*))
                          (funcall osf x)))
                  (let ((no-save

; Don't call save-system on first pass.

                         si::*binary-modules*))
                    (funcall (symbol-function sa) ; save-acl2
                             (list ia (list 'quote ib) ap2f save-dir)
                             nil
                             no-save)
                    (if no-save ; first pass
                        (eval (list 'progn

; The following setq form comes from ACL2::LP.  We should probably separate
; this out as a new ACL2 function and just call that function both here and in
; ACL2::LP.

                                    `(setq ,sym-initial-cbd
                                           (,sym-pathname-os-to-unix
                                            (namestring (truename ""))
                                            (os (w ,sym-state))
                                            ,sym-state))
                                    `(,sym-f-put-global
                                      ',sym-cbd
                                      ,sym-initial-cbd
                                      ,sym-state)
                                    (if my-books
                                        (list sym-ld
                                              (list 'quote
                                                    (append
                                                     (loop for x in my-books
                                                           collect
                                                           (list ib x))))))
                                    (if tmp2
                                        '(load "TMP2.o")))))))))))
      (if (and clean (probe-file "axioms.o"))
          (delete-file "axioms.o")) ; will trigger a compile
      (format t "** STARTING FIRST PASS. **~%")
      (eval com) ; First evaluate the command in gcl.
      (format t "** STARTING SECOND (FINAL) PASS. **~%")

; Link in the .o files collected in si::*binary-modules* with ld.

      (compiler::link
       (remove-duplicates si::*binary-modules* :test (function equal))
       "saved_acl2" ; new image (ignored)

; Run the build sequence again in this image with load redirected to initialize.

       (format nil "~S" com)
       ""
       nil))))
