; ACL2 Version 8.3 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2020, Regents of the University of Texas

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

; Acknowledgments:  Bob Boyer contributed crucially to the design and
; implementation of early versions of ACL2.  Many others, largely at CLI, have
; also contributed to the design of certain features.  We especially thank
; Bishop Brock and John Cowles for their contributions.  See the documentation
; topic ACKNOWLEDGMENTS for more information.

; This research was supported in part at Computational Logic, Inc. by the
; Defense Advanced Research Projects Agency (DARPA), ARPA Orders #6082, 9151
; and 7406 and by the Office of Naval Research, contracts numbers
; N00014-88-C-0454, N00014-91-C-0130, and N00014-94-C-0193.  The views and
; conclusions contained in this document are those of the author(s) and should
; not be interpreted as representing the official policies, either expressed or
; implied, of Computational Logic, Inc., Office of Naval Research, DARPA or the
; U.S. Government.

; This file cannot be compiled because it changes packages in the middle.

; This file, acl2.lisp, (a) builds the packages for the ACL2 system, (b)
; defines the functions for loading and compiling ACL2 and for running code
; verified using ACL2, and (c) makes a couple of checks concerning minor,
; non-CLTL, assumptions that we make about Common Lisps in which ACL2 is to
; run.

; Other programs may want a compile-time check for whether ACL2 is running, so
; we push this feature.

(push :ACL2 *features*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                            CLTL1/CLTL2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; For the most part, we program in a subset both of CLTL1 and CLTL2.
; However, there are a few places, notably the name of the main
; package for Lisp symbols, where this is impossible.  So we use the
; read conditional #+CLTL2.  If one wishes to run ACL2 under CLTL2,
; execute the following form before commencing compiling or loading:

;        (push :CLTL2 *features*)

; For example, for Allegro and lispworks (respectively) we have the following.

#+(or ansi-cl draft-ansi-cl-2 lispworks clisp ccl)
(push :CLTL2 *features*)

; We use IN-PACKAGE in a way that is consistent with both CLTL1 and
; CLTL2, namely as a macro (i.e., whose argument is not evaluated) for
; switching *package* to an existing package, value ignored.

(in-package #-CLTL2 "USER" #+CLTL2 "COMMON-LISP-USER")

; Avoid warning, at least in Allegro CL, for use of this variable below.  Note
; that it is set to nil using GNUmakefile when ACL2_COMPILER_DISABLED is set.
(defvar *acl2-compiler-enabled*)

; Changes Made in Support of CMU Lisp

; (0) (The following issue with Cmulisp no longer seems to be true, at least
;     as of Version 19e on Linux.)
;     Cmulisp doesn't support EVAL-WHEN.  This meant that in the #+cmu case
;     I had to put down special code to try to do what other lisps do.
;     Generally, this involved just not checking for certain errors (compiling
;     files that weren't supposed to be compiled) in #+cmu that were checked
;     in other lisps.  In one case, namely the initialization of
;     current-acl2-world, it involved a little more.

; (1) cmulisp switches from *standard-input* to *terminal-io* when the input
;     stream reaches eof; our other lisps all exit to the operating system.
;     This means all the batch jobs we submit via make have to be arranged to
;     exit from cmulisp before eof.  This required changing the top-level
;     makefile and the makefiles of all the community books.  I generally put a
;     `:q #+cmu (lisp::quit)' at the end of each workxxx.
;     These could be replaced simply by `:q (acl2::exit-lisp)'.

; (2) Cmulisp checks type assertions at runtime.  I found two of our assertions
;     violated by actual use.  In fmt-char we mistakenly claimed the string's
;     length was less than 101.  This was a typo -- elsewhere in the same
;     function we claimed it was just a fixnum -- apparently caused by
;     copying a type-declaration and failing to edit it thoroughly.  (Another
;     variable was correctly limited to 101.)

;     In maximal-elements1, used in the selection of induction candidates,
;     we claimed (by using int=) that the scores for an induction candidate
;     are integers when in fact they are rationals.

; (3) Evidently, all functions in cmulisp pass the compiled-function-p test.
;     If you defun foo and immediately get its symbol-function you get
;     an object like #<Interpreted function ...>.  If you ask whether
;     this object is a compiled-function-p you get t.  If you compile
;     foo the symbol-function changes to an object like #<Function
;     ...>, which also passes the test.

;     The fact that everything in a symbol-function field looks like a compiled
;     function killed us in an interesting way.  Most locally, it made
;     compile-uncompiled-*1*-defuns write out an empty file of functions to
;     compile, because everything looked compiled already.  But where that
;     really got us was that we use that function to create TMP1.lisp during
;     the bootstrapping.  TMP1.lisp, recall, contains the mechanically
;     generated executable-counterparts of logic mode functions defined in
;     axioms.lisp.  By not generating these we built an image in which the
;     relevant functions were undefined.  Because of the rugged way we invoke
;     them, catching errors and producing a HIDE term if we can't eval them,
;     we survived the certification of many books before we finally got to a
;     proof that couldn't be done without running one of those functions.
;     The proof, in the bdd community books, required evaling (nth -1 nil), which
;     according to the axioms is nil but which we couldn't deduce because
;     ACL2_*1*_COMMON-LISP::NTH was undefined.

;     My fix was to define and use compiled-function-p! instead of the standard
;     compiled-function-p.  The new function has a #+/-cmu split in it.  In the
;     cmu case I ask

;     (not (eq (type-of (symbol-function fn)) 'eval:interpreted-function))

;     So I say fn is compiled if its symbol-function is not an object like
;     #<Interpreted function ...>.

; (4) CMU Lisp does not allow us to "undefine" a macro-function.  That is,
;     one is not permitted to store a nil into the macro-function
;     field because nil is not a function.  We do this when we
;     implement undo.  We handle it by storing a dummy function
;     instead, and change the notion of when a symbol is virgin to
;     recognize the case that its symbol-function or macro-function is
;     the dummy.

; (5) We made a few fixes and cleanups in order to avoid compiler warnings.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                               SAFETY AND PROCLAIMING
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar *acl2-optimize-form*
  `(optimize #+cltl2 (compilation-speed 0)

; The user is welcome to modify this proclaim form.  For example, in CCL and
; SBCL, where the "full" target does essentially nothing other than note in
; file acl2-status.txt that the system has allegedly been compiled, the
; following procedure works.

;   # Write :COMPILED to acl2-status.txt.
;   make full LISP=ccl

;   # Next, edit acl2r.lisp with the desired variant of *acl2-optimize-form*,
;   # for example as follows.
;   #   (defparameter cl-user::*acl2-optimize-form*
;   #     '(OPTIMIZE (COMPILATION-SPEED 0) (DEBUG 0) (SPEED 0) (SPACE 0)
;   #                (SAFETY 3)))
;   #

;   # Now start CCL and evaluate:

;   (load "init.lisp") ; loads acl2r.lisp
;   (in-package "ACL2")
;   (save-acl2 (quote (initialize-acl2 (quote include-book)
;                                      acl2::*acl2-pass-2-files*))
;              "saved_acl2")
;   (exit-lisp)

; The following may allow more tail recursion elimination (from "Lisp
; Knowledgebase" at lispworks.com); might consider for Allegro CL too.

             #+(or lispworks ccl) (debug 0)
             #+cmu (extensions:inhibit-warnings 3)
             #+sbcl (sb-ext:inhibit-warnings 3)
             (speed 3)

; Consider replacing cmu on the next line with (or cmu sbcl).  The SBCL manual
; says the following, but a quick test with (or cmu sbcl) yielded no smaller
; .core file size and no quicker (mini-proveall).

;   The value of space mostly influences the compiler's decision whether to
;   inline operations, which tend to increase the size of programs. Use the
;   value 0 with caution, since it can cause the compiler to inline operations
;   so indiscriminately that the net effect is to slow the program by causing
;   cache misses or even swapping.

             (space #+cmu 1 #-cmu 0)

; WARNING:  Do not proclaim (cl-user::fixnum-safety 0) for LispWorks.  Any
; fixnum-safety less than 3 expects all integers to be fixnums!

             (safety

; Consider using (safety 3) if there is a problem with LispWorks.  It should
; allow stack overflows to report an error, rather than simply to hang.

; Safety 1 for CCL has avoided the kernel debugger, e.g. for compiled calls
; of car on a non-nil atom.  The following results for CCL show why we have
; decided to keep the safety at 0 by default and why safety 3 is not too bad.
;
; Safety 0:
; 12955.537u 542.877s 3:46:24.68 99.3%  0+0k 0+0io 0pf+0w
;
; Safety 1:
; 15343.578u 562.207s 4:27:03.67 99.2%  0+0k 0+0io 0pf+0w

; Try safety 2 or 3 to find violations with Allegro CL like the car of a
; non-nil atom.  (Note: safety 3 has failed in GCL due to a stack overflow.)
; Here are some numbers with Allegro CL, 8 processors with make -j 8:

; Safety 0:
; 11262.699u 291.730s 38:23.72 501.5%   0+0k 0+0io 16pf+0w

; Safety 2:
; 15588.206u 285.249s 54:19.72 486.9%   0+0k 0+0io 0pf+0w

; Safety 3:
; 16450.508u 284.473s 57:46.03 482.8%   0+0k 0+0io 0pf+0w

; Here are GCL numbers, again with make -j 8 (and using "fast builds").

; Safety 0:
; 10013.573u 566.983s 33:33.80 525.4%   0+0k 0+0io 0pf+0w

; Safety 2:
; [Note: community book
; books/clause-processors/SULFA/books/sat-tests/test-incremental.lisp
; ran out of space, saving perhaps a minute]
; 15637.669u 511.811s 52:02.78 517.1%   0+0k 0+0io 0pf+0w

              ,(let ((our-safety
                      #-CLTL2
                      (if (boundp 'user::*acl2-safety*)
                          (symbol-value 'user::*acl2-safety*)
                        nil)
                      #+CLTL2
                      (if (boundp 'common-lisp-user::*acl2-safety*)
                          (symbol-value 'common-lisp-user::*acl2-safety*)
                        nil)))
                 (if our-safety
                     (progn (format t "Note: Setting SAFETY to ~s."
                                    our-safety)
                            our-safety)
                   0))
              )
             #+ccl
             ,@(let ((our-stack-access
                      (if (boundp 'common-lisp-user::*acl2-stack-access*)
                          (symbol-value 'common-lisp-user::*acl2-stack-access*)
                        nil)))
                 (if our-stack-access
                     (progn (format t "Note: Setting :STACK-ACCESS to ~s."
                                    our-stack-access)
                            `((:stack-access ,our-stack-access)))
                   nil))
              ))

(proclaim *acl2-optimize-form*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                               FILES
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This is the file acl2.lisp, the first source file for ACL2.  The names of the
; other ACL2 source files are listed under *acl2-files*.

; All of ACL2 is written in Common Lisp and we expect that ACL2 will run in any
; Common Lisp except for those Common Lisps which fail the tests we execute
; upon loading this file, acl2.lisp.  With the exception of this and other
; initialization files, files *-raw.lisp, and those constructs after the
; #-acl2-loop-only readtime conditional, ACL2 is written in the applicative
; Common Lisp for which ACL2 is a verification system.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                       READING CHARACTERS FROM FILES
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Files may be viewed as sequences of bytes.  But Lisp can interpret these byte
; sequences as sequences of characters, depending on so-called character
; encodings.

; For example, through about March 2012 the default character encoding in CCL
; was ISO-8859-1, sometimes known as LATIN-1.  When this changed to UTF-8 a
; failure was reported when attempting to certify community book
; books/workshops/2006/cowles-gamboa-euclid/Euclid/fld-u-poly/coe-fld.lisp,
; apparently because of the following line, where the next-to-last character is
; actually an accented `o' sometimes known as
; #\LATIN_SMALL_LETTER_O_WITH_ACUTE, having code 243.  (The CLISP build fails
; if we use that character here, because at this point we have not yet made the
; adjustments to the character encoding that are done below!)

  ;;; Inverso de la primera operacion

; The accented `o' above is encoded as a single byte in LATIN-1 but as two
; bytes in UTF-8.

; Jared Davis then suggested that we explicitly specify ISO-8859-1, which might
; be slightly more efficient for reading files.  Note that GCL (non-Ansi, circa
; 2010 but probably later) only supports ISO-8859-1 as far as we can tell.  We
; follow Jared's suggestion below.  It seems that character encoding for
; reading from files is controlled differently from character encoding for ACL2
; reading from the terminal.  Jared also suggested setting the terminal
; encoding to ISO-8859-1 as well, and showed us how to do that in CCL.  We have
; been unable to figure out how to do that in some other host Lisps, but since
; files are typically shared between users and (of course) ACL2 reading from
; the terminal is not, the encoding for the terminal seems less important than
; for files.

; Even for files, we assert there is no soundness issue, in the sense that for
; maximum trust we expect each user to certify all books from scratch in a
; single environment.  But in practice, users share books (in particular,
; via the community books); so it is desirable to enforce uniform character
; encodings for files.

; The use of latin-1 could in principle cause problems for those whose default
; Emacs buffer encoding is utf-8.  That's in fact the case for us at UT CS, but
; not on one of our Mac laptops as of this writing (April 2012), probably
; because environment variable LANG is en_US.UTF-8 at UT CS.  But ACL2 users
; don't often save Lisp files with nonstandard characters.  If they have
; occasion to do so, they can evaluate

; (setq save-buffer-coding-system 'iso-8859-1)

; in Emacs buffers before saving into files.  This will happen automatically
; for users who load file emacs/emacs-acl2.el into their emacs sessions.

; At any rate, it seems best to standardize file encodings and leave it to
; individuals to cope with editing issues.

; Without further ado, we set the default encoding for files.  Below, we make
; some attempt to do so for the terminal.  We wrap all this into a function,
; because we have found that for sbcl, upon restart we lose the effect of the
; assignment below.  It seems safest then to do these same assignments at
; startup; see the call of the following function in acl2-default-restart.

(defun acl2-set-character-encoding ()

; We set the character encoding (see discussion above).

  #+allegro
; Alternatively, we could set the locale on the command line using -locale C:
; see http://www.franz.com/support/documentation/6.1/doc/iacl.htm#locales-1
; Note that (setq *default-external-format* :ISO-8859-1) is obsolete:
; http://www.franz.com/support/documentation/6.1/doc/iacl.htm#older-ef-compatibility-2
  (setq *locale* (find-locale "C"))

  #+ccl
  (setq ccl:*default-file-character-encoding* :iso-8859-1)

; #+clisp
; Set using -E ISO-8859-1 command-line option from save-exec.
; Note that the setting below for custom:*default-file-encoding* works for
; files, but we were unable to do the analogous thing successfully for
; custom:*terminal-encoding*, even when restricting that assignment to
; (interactive-stream-p *terminal-io*).

  #+cmu
  (setq *default-external-format* :iso-8859-1)

; #+gcl -- already iso-8859-1, it seems, and nothing we can do to change
;          the encoding anyhow

  #+lispworks
; This the default on our linux system, at least on both 32- and 64-bit,
; version 6.1.0.  But it doesn't seem to suffice; see
; our-lispworks-file-encoding below.
  (setq stream::*default-external-format* '(:LATIN-1 :EOL-STYLE :LF))

; The following two symbols are external symbols of the "SB-EXT" package, but
; that wasn't always the case.  We use the packages below so that these
; assignments work back through at least SBCL 1.4.14.
  #+sbcl
  (setq sb-impl::*default-external-format* :iso-8859-1)
  #+sbcl
  (setq sb-alien::*default-c-string-external-format* :iso-8859-1)

; ;;;
; We have made only limited attempts to set the character encoding at the
; terminal, as discussed above.
; ;;;

; #+allegro
; Handled by *locale* setting above.  Formerly the following was later in
; this file; now we include it only as a comment.
;  #+(and allegro allegro-version>= (version>= 6 0))
;  (setf (stream-external-format *terminal-io*)
;        (excl::find-external-format
;         #+unix :latin1-base
;         #-unix :latin1))

; #+ccl
; For terminal, set using -K ISO-8859-1 command-line option from save-exec.

; #+cmucl -- Probably no setting is necessary.

; #+clisp -- Set using command-line option (see above).

; #+gcl -- There seems to be nothing we can do.

; #+lispworks -- No support seems to be available.

; #+sbcl
; We found that "unsetenv LANG" results in (stream-external-format
; *terminal-io*) being ascii at the terminal instead of utf-8; or, just start
; up sbcl like this to get ascii:

;   LANG=C ; XTERM_LOCALE=C ; sbcl

; But we don't know how to get latin-1.  We even tried each of these, but got
; ascii:

;   LANG=en_US.LATIN-1 ; XTERM_LOCALE=en_US.LATIN-1
;   LANG=en_US.ISO-8859-1 ; XTERM_LOCALE=en_US.ISO-8859-1

  )

; Here, we invoke the function defined above, so that a suitable character
; encoding is used during the build, not only when starting up a built image
; (which is why we call acl2-set-character-encoding in acl2-default-restart).
(acl2-set-character-encoding)

; We also do the following for clisp, since we set the encoding on the command
; line (see comment above) but we want to be able to read our own source files
; during the build.  See the comment in (defxdoc character-encoding ...) in
; community book books/system/doc/acl2-doc.lisp.
#+clisp
(setq custom:*default-file-encoding*
      (ext:make-encoding :charset 'charset:iso-8859-1

; The following is consistent with what we used to do in acl2-init.lisp; see
; the commented-out call there that sets custom:*default-file-encoding*.
; Unfortunately, according to http://www.clisp.org/impnotes/clhs-newline.html,
; this doesn't treat CR/LF as two characters when reading files -- for example,
; the file "foo.lisp" defined in a comment below for dealing with LispWorks
; provides (len *c*) = 3, not 4.

                         :line-terminator :unix))

; We seem to need to do more for LispWorks.  To see why, create a book
; "foo.lisp" as follows.
;
;   (in-package "ACL2")
;  (defconst *c*
;    "x
;  y")
;
; Next, if you have arranged in emacs to set save-buffer-coding-system
; 'iso-8859-1, as in emacs/emacs-acl2.el, turn that off and bring foo.lisp into
; a buffer; then add control-M at the end of every line; and finally, save the
; buffer, which will save the control-M at the end of every line and, in
; particular, in the middle of the string.  (And now restore your handling of
; save-buffer-coding-system.)  In a Lispworks image of ACL2, execute (ld
; "foo.lisp"), and you can evaluate (length *c*) to get 3, where 4 is expected
; because of the control-M.  We adopt here a solution found on the web at:
; http://www.lispworks.com/documentation/lw60/LW/html/lw-470.htm

#+lispworks
(defun our-file-encoding (pathname ef-spec buffer length)
  (system:merge-ef-specs ef-spec '(:LATIN-1 :EOL-STYLE :LF)))

#+lispworks
(setq system::*file-encoding-detection-algorithm*
      '(our-file-encoding))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                          LISP BUGS AND QUIRKS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; See acl2-fns.lisp for a fix to user-homedir-pathname for some versions of
; GCL.

; See the function print-number-base-16-upcase-digits for an explanation of the
; following code, which pushes a feature when that function can be needed.
(let ((*print-base* 16) (*print-case* :downcase))
  (let ((tmp (with-output-to-string (s) (princ 10 s))))
    (cond ((equal tmp "A"))
          ((equal tmp "a")
           (format t
                   "~%Note: Numbers in base 16 will be printed using a ~
                    special-purpose~%      ACL2 function, ~s."
                   'print-number-base-16-upcase-digits)
           (push :acl2-print-number-base-16-upcase-digits *features*))
          (t (error "Surprising result for (princ 10 s) in base 16: ~s"
                    tmp)))))

; To use ACL2 under LispWorks 3.2.0, execute the following to work around a
; bug.

; #+lispworks
; (setf (svref ccl::*funny-symbol-char-table* (char-code #\.)) t)

; Next, we correct *features* for Windows.

#+(and (or winnt win32 windows) (not mswindows))
(setq *features*
      (cons :mswindows *features*))

#+(and (or mswindows winnt) unix)
(setq *features*
      (delete :unix *features*
              :test
              (function (lambda (x y)
                          (equal (symbol-name x) (symbol-name y))))))

; Turn off automatic declaration of special variables, in particular since we
; do not want state declared special; see the comment above
; (eval '(setq state *the-live-state*)) in load-acl2.
#+cmu
(setq ext:*top-level-auto-declare* nil)

; Turn off compiler verbosity.  This is important for CMUCL and SBCL because,
; apparently, even >& does not seem to redirect the error stream to a file
; during regressions.  For GCL it is useful simply to reduce rather a lot of
; output on compilation, even for top-level forms (as opposed to file), which
; doesn't seem necessary for Allegro CL or LispWorks.
#+(or cmu sbcl gcl)
(setq *compile-verbose* nil)
#+(or cmu sbcl)
(setq *compile-print* nil)
#+gcl
(setq *load-verbose* nil)

; Turn off gc verbosity (same reason as above).
#+cmu
(setq ext:*gc-verbose* nil)

#+ccl
(when (fboundp 'ccl::gc-verbose) ; not in OpenMCL 1.0 (CCL)

; This gets overridden for ACL2(h) in acl2h-init.

  (apply 'ccl::gc-verbose nil nil))

; See later in this file for with-warnings-suppressed (after we introduce and
; enter the ACL2 package).

; Avoid saving source file information, which could cause some slowdown and
; isn't typically exploited by ACL2 users.
#+ccl
(setq ccl::*record-source-file* nil)

; The following avoids errors from extra right parentheses, but we leave it
; commented out since it doesn't seem important enough to merit messing around
; at this low level, and for just one Lisp.
; #+ccl
; (setq ccl::*ignore-extra-close-parenthesis* t)

; We have tried to build under ECL (Embeddable Common-Lisp), and with some
; modifications, we made progress -- except there appears (as of Sept. 2011) to
; be no good way for us to save an executable image.  Specifically, it appears
; that c:build-program not will suffice for saving state (properties etc.) --
; it's just for saving specified .o files.  (This impression seems to be
; confirmed at http://stackoverflow.com/questions/7686246/saving-lisp-state .)

; Here we document steps to take towards possibly porting to ECL in the future.

; If state-global-let* expansion causes an error due to excessive code blow-up,
; then consider replacing its definition by placing the following after
; state-free-global-let*.  HOWEVER, first think about whether this is right; we
; haven't thought through the effect of mixing a stack of let*-bindings of
; state global variables with the acl2-unwind-protect mechanism.  Also,
; comments are omitted here; be sure to restore them.

;;; (defmacro state-global-let*-logical (bindings body)
;;;   (declare (xargs :guard (and (state-global-let*-bindings-p bindings)
;;;                               (no-duplicatesp-equal (strip-cars bindings)))))
;;;
;;;   `(let ((state-global-let*-cleanup-lst
;;;           (list ,@(state-global-let*-get-globals bindings))))
;;;      ,@(and (null bindings)
;;;             '((declare (ignore state-global-let*-cleanup-lst))))
;;;      (acl2-unwind-protect
;;;       "state-global-let*"
;;;       (pprogn ,@(state-global-let*-put-globals bindings)
;;;               (check-vars-not-free (state-global-let*-cleanup-lst) ,body))
;;;       (pprogn
;;;        ,@(state-global-let*-cleanup bindings 0)
;;;        state)
;;;       (pprogn
;;;        ,@(state-global-let*-cleanup bindings 0)
;;;        state))))
;;;
;;; #-acl2-loop-only
;;; (defmacro enforce-live-state-p (form)
;;;
;;; ; Note that STATE is intended to be lexically bound at the point where this
;;; ; macro is called.
;;;
;;;   `(progn (when (not (live-state-p state)) ; (er hard! ...)
;;;             (let ((*hard-error-returns-nilp* nil))
;;;               (illegal 'enforce-live-state-p
;;;                        "The state was expected to be live in the context of ~
;;;                         an evaluation of the form:~|~x0"
;;;                        (list (cons #\0 ',form)))))
;;;           ,form))
;;;
;;; (defmacro state-global-let* (bindings body)
;;;   (cond #-acl2-loop-only
;;;         ((and (symbol-doublet-listp bindings)
;;;               (not (assoc-eq 'acl2-raw-mode-p bindings)))
;;;
;;; ; The test above guarantees that we merely have bindings of state globals.  A
;;; ; triple requires cleanup using a setter function.  Also we avoid giving this
;;; ; simple treatment to 'acl2-raw-mode-p because the semantics of
;;; ; state-global-let* are to call f-put-global, which has side effects in the
;;; ; case of 'acl2-raw-mode-p.
;;;
;;;          `(enforce-live-state-p
;;;            (warn-about-parallelism-hazard
;;;             '(state-global-let* ,bindings ,body)
;;;             (state-free-global-let* ,bindings ,body))))
;;;         (t `(state-global-let*-logical ,bindings ,body))))

; Also, place the following forms in file acl2-fns.lisp, just above qfuncall
; (but there may be better ways to do this).

;;; ; The following is in acl2.lisp, but seems to be needed here as well.
;;; #+ecl
;;; (ext:package-lock "COMMON-LISP" nil)
;;;
;;; Similarly in acl2.lisp, just before handling of package-lock on
;;; "COMMON-LISP" for clisp:
;;;
;;; #+ecl
;;; (ext:package-lock "COMMON-LISP" nil)

; Finally, consider these additional notes.

;;; We need (require "cmp") if we're to use c:build-program.

;;; Special-form-or-op-p: treat ecl like sbcl.

;;; System-call: treat ecl like akcl (actually replace #+akcl by #+(or akcl
;;; ecl)).

;;; Initialize-state-globals: treat ecl just like lispworks.

;;; Where we have the binding (compiler:*suppress-compiler-notes* t) for akcl,
;;; perhaps include the binding (*compile-verbose* t) for ecl.

;;; Modify exit-lisp to treat ecl like akcl, except using ext::quit instead of
;;; si::bye.

#+ccl
(defvar *acl2-egc-on* ; in "CL-USER" package; see second paragraph below

; This variable provides the initial garbage collection strategy, by way of the
; call of set-gc-strategy in acl2h-init.

; This variable is in the "CL-USER" package (see comment above) because users
; are welcome to set its value, for example by writing the form (defparameter
; cl-user::*acl2-egc-on* nil) to acl2r.lisp before doing the build by using
; ACL2_EGC_ON; see GNUmakefile.

; We formerly turned off EGC in CCL because it didn't seem to work well with
; memoizing worse-than-builtin and sometimes seemed buggy.  But Gary Byers made
; changes to improve EGC, in particular its interaction with static conses,
; starting in version 16378 (with the feature below introduced in 16384).  It
; seems best not to mess with GC heuristics such as post-gc hooks (see
; set-gc-strategy-builtin-delay), and instead rely on EGC.

  #+static-conses-should-work-with-egc-in-ccl
  t
  #-static-conses-should-work-with-egc-in-ccl
  nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                              PACKAGES
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We never intend that this file should be compiled, and hence we do
; not need to obey the CLTL1 strictures about putting all IN-PACKAGE
; forms near the front.

(let ((lisp-pkg (find-package "LISP")))
  (if lisp-pkg
      (let ((cl-pkg (find-package "COMMON-LISP")))
        (cond
         ((and cl-pkg (eq cl-pkg lisp-pkg))

; Then all is well.

          )
         #+(or cmu (and gcl cltl2))

; Starting with CMUCL 19a, lisp-pkg and cl-pkg are no longer the same.  We view
; CMUCL as CLTL2; see (push :CLTL2 *features*) above, noting that :ANSI-CL is
; in *features*.  So in this case, we simply ignore lisp-pkg.  Probably we can
; do the same for most other lisps, and in fact we do so for ANSI GCL as well.
; However, non-ANSI GCL is handled differently, since the "LISP" package is
; populated there but the "COMMON-LISP" appears to be largely irrelevant.

         (t nil)
         #-(or cmu (and gcl cltl2))
         (t
          (when cl-pkg ; but by the test above, cl-pkg is not lisp-pkg
            #-gcl ; not non-ANSI GCL

; Perhaps we can just add the present lisp to the case for #+(or cmu (and gcl
; cltl2)), above.

            (error "This Lisp is unsuitable for ACL2, because the ~
                    COMMON-LISP~% package is defined but is not the LISP ~
                    package.")
            #+gcl ; non-ANSI GCL

; Early versions of GCL 2.4.3/2.5.0 had a "COMMON-LISP" package that was
; initially populated only with LISP::T and LISP::NIL.  It seems safe to move
; any GCL COMMON-LISP package out of the way before we make "COMMON-LISP" a
; nickname for "LISP".

            (rename-package "COMMON-LISP" "COMMON-LISP-renamed"))
          (let ((old-name (package-name lisp-pkg)) ; reuse old name, nicknames
                (old-nicknames (package-nicknames lisp-pkg)))
            (rename-package "LISP"
                            old-name
                            (cons "COMMON-LISP" old-nicknames))))))))

(eval-when #-cltl2 (compile)
           #+cltl2 (:compile-toplevel)
           (error "The file acl2.lisp should never be compiled."))

(dolist
 (p (list-all-packages))
 (cond ((equal 4 (string< "ACL2" (package-name p)))
        (format t
                "~%~%Warning:  There is already a package with the ~
                 name ~a. ~%The ACL2 implementation depends upon ~
                 having complete knowledge of ~%and control over any ~
                 package whose name begins with the ~%four letters ``ACL2'', ~
                 so ACL2 may not work in this Lisp." (package-name p))
        (cond ((package-use-list p)
               (format t "~%~%Warning:  The package with name ~a ~
                   USES the packages in the list ~a.  ACL2 will not work ~
                   in state of affairs."
                       (package-name p) (package-use-list p)))))))

(or (find-package "ACL2")
    (make-package "ACL2" :use nil))

; The definition of defconst appears just below because we use it
; early in axioms.lisp.  But first, we define the constant
; *the-live-state* because it is used below in the definition of
; defconst and cmulisp warns if we use it before it has been defined.

; And, in order to define *the-live-state* we need the ACL2_INVISIBLE
; package, which we define here.  This package is used for a few odd
; objects that are to be hidden from the ACL2 user.  Symbols in this
; package having names that start with "HONS" are reserved for the
; hons/memoization implementation.

(let ((inv "ACL2_INVISIBLE"))
  (or (find-package inv)
      (make-package inv :use nil)))

; LispWorks has a package named "DEF", and that name conflicts with an ACL2
; package of that name introduced in community book books/coi/.  We deal with
; that issue here.  Thanks to Martin Simmons for providing this code in place
; of the original code, which instead invoked (rename-package "DEF"
; "DEF-FROM-LW-RENAMED").
#+lispworks
(when (find-package "DEF")
  (unless (equal (package-name "DEF") "DSPEC")
    (error "Expected LispWorks DEF package to be called DSPEC"))
  (rename-package "DSPEC" "DSPEC"
                  (remove "DEF" (package-nicknames "DSPEC") :test 'equal)))

; The value of the constant *the-live-state* is actually just a
; symbol, but that symbol is the unique representative of the one
; single active, global, real-time state of ACL2, which is represented
; both in real-time (e.g., characters not yet typed) and also rather
; efficiently, using typical von Neumann storage techniques.
; Functions that wish to access the global state must have received
; *the-live-state* as an arg.  Functions that modify this global state
; must receive it as an arg and return it.

(defconstant acl2::*the-live-state* 'acl2_invisible::|The Live State Itself|)

; (Defconst *var* term) is essentially just (defparameter *var* term).  But
; things are made complicated by the desire not to evaluate term unnecessarily.
; Suppose (defconst *var* term) appears in a certified book, say "book.lisp".
; Then when the events in "book.lisp" are processed, a CLTL-COMMAND is executed
; which causes (defconst *var* term) to be evaluated in the underlying raw
; lisp, assigning a value to *var* in Lisp.  But now suppose that the compiled
; file for another book, say "book2.o", is loaded on behalf of include-book.
; If defconst were just defparameter, term would be evaluated again (yielding a
; presumably EQUAL value), which is an unfortunate waste of computation.

; We avoid this in the code below by saving, on the raw Lisp property list of
; *var*, under the key 'REDUNDANT-RAW-LISP-DISCRIMINATOR, a triple, (DEFCONST
; term . val), giving the term we evaluated to produce the setting of the var
; and the value, val, produced.  When a defconst (defconst *var* term) is
; evaluated, we ask whether *var* has a value.  If not, we just proceed
; normally.  But if it has a value, we insist that the discriminator be present
; and appropriate or else we cause a hard error.  By appropriate in this case
; we mean that it be a DEFCONST such that the value produced last time is EQ to
; the current setting of *var*, and moreover, either the old and new DEFCONST
; have the same (EQUAL) term to evaluate or else the new value is EQUAL to the
; old.  The EQ check is meant to provide some safety if the user has manually
; set *var* in raw lisp, as with setq, since the last defconst to it.

; We anticipate that redundant-raw-lisp-discriminator may be used by the
; support functions for other events, e.g., defstobj.  So the value of that
; property is not necessarily (DEFCONST term . val) but may depend on the kind
; of event that stored it.  The reason we put the discriminator on the raw lisp
; property list of *var* rather than looking in the world of *the-live-state*,
; where we could in principle find an event-landmark, is that we execute many
; defconsts in axioms.lisp, before the world processing functions, like
; getprop, are defined and so the defmacro below must expand to code that can
; be executed in a partially booted ACL2.

(defvar acl2::*compiling-certified-file* nil)

(defun acl2::defconst-redeclare-error (name)
  (let ((stk (symbol-value 'acl2::*load-compiled-stack*)))
    (cond (stk
           (error
            "Illegal attempt to redeclare the constant ~s.~%~
             The problem appears to be that you are including a book,~%~
             ~2T~a,~%~
             that attempts to give a definition of this constant that~%~
             is incompatible with its existing definition.  The ~%~
             discrepancy is being discovered while loading that book's~%~
             compiled (or expansion) file~:[, as the last such load for~%~
             the following nested sequence of included books (outermost~%~
             to innermost):~%~{  ~a~%~}~;.~]"
            name
            (caar stk)
            (null (cdr stk))
            (reverse (loop for x in stk collect (car x)))))
          (t
           (error "Illegal attempt to redeclare the constant ~s."
                  name)))))

(defparameter acl2::*safe-mode-verified-p*

; This global may be bound to t when we are evaluating a form that we know will
; not lead to an ill-guarded call in raw Lisp (say, because the form was
; previously evaluated by ACL2 in safe-mode).  See also the comment in
; ec-call1-raw.

  nil)

(declaim (ftype (function (t)
                          (values t))
                acl2::large-consp))

(defmacro acl2::defconst (name term &rest rst)
  (declare (ignore rst))
  (let ((disc (gensym)))
    `(defparameter ,name
       (let ((acl2::*safe-mode-verified-p* t))
         (cond
          ((boundp ',name)
           (cond
            (acl2::*compiling-certified-file*

; We avoid the potentially expensive redundancy check done below, which is
; legitimate since we are simply loading a compiled file at the end of
; certify-book.  To see how important this optimization can be, try removing it
; before certifying the following book (thanks to Sol Swords for this
; example).

; (in-package "ACL2")
; (defun tree (n)
;    (if (zp n)
;        nil
;      (let ((sub (tree (1- n))))
;        (cons sub sub))))
; (defmacro deftree (name n)
;    `(defconst ,name ',(tree n)))
; (deftree *big* 35)

             (symbol-value ',name))
            (t

; Even though ',name is bound, we refer to its value with
; (symbol-value ',name) rather than simply an in-line ,name, to avoid
; compiler warnings.

             (let ((,disc (get ',name
                               'acl2::redundant-raw-lisp-discriminator)))
               (cond
                ((and (consp ,disc)
                      (eq (car ,disc) 'acl2::defconst))
                 (assert (consp (cdr ,disc)))
                 (cond
                  ((and (eq (cdr (cdr ,disc)) (symbol-value ',name))

; Here, as in defconst-fn, we skip the check just below (which is merely an
; optimization, as explained in defconst-fn) if it seems expensive but the
; second check (below) -- against the term -- could be cheap.  Without this
; check, if two books each contain a form (defconst *a* (hons-copy
; '<large_cons_tree>)) then when the compiled file for the second book is
; loaded, the check against the term (i.e. the first check below, as opposed to
; the second check, which uses that term's value) could be intractable.  For a
; concrete example, see :doc note-7-2.

                        (or (let ((disc ,disc)
                                  (qterm ',term))

; We check that acl2::large-consp to avoid a boot-strapping problem in GCL.

                              (and (not (and (fboundp 'acl2::large-consp)
                                             (acl2::large-consp qterm)))
                                   (equal (car (cdr disc)) qterm)))
                            (equal (cdr (cdr ,disc)) ,term)))
                   (symbol-value ',name))
                  (t (acl2::defconst-redeclare-error ',name))))
                ((acl2::raw-mode-p acl2::*the-live-state*)

; In this case we allow redeclaration of the constant; this is, after all, raw
; mode, where there are no guarantees.

                 ,term)
                (t
                 (acl2::defconst-redeclare-error ',name)))))))

; If ',name is not bound, we must evaluate ,term.  Note that we do so
; outside of all local bindings, so as not to disturb variables in
; term.  (There should be none -- this is supposed to be a constant,
; but you never know!)  We may want to enforce that this code is only executed
; during the boot-strap; see the Essay on Guard Checking.

          (t (let* ((val ,term)
                    (d (list* 'acl2::defconst ',term val)))
               (setf (get ',name 'acl2::redundant-raw-lisp-discriminator)
                     d)
               (cdr (cdr d)))))))))

; We now get our imports for package ACL2, putting them into the
; variable acl2::*common-lisp-symbols-from-main-lisp-package*.

; We use different variables for common-lisp-symbols-from-main-lisp-package*,
; *acl2-version*, and *acl2-files*, in order to avoid compiler warnings for
; redefined variables.  Actually, *acl2-version* no longer exists starting with
; Version_2.9.1, but we keep the name below nonetheless.

(defvar acl2::*copy-of-common-lisp-symbols-from-main-lisp-package*)
(defvar acl2::*copy-of-common-lisp-specials-and-constants*)
(defvar acl2::*copy-of-acl2-version*)

(defconstant acl2::*acl2-files*

; The order of these files determines compilation order.

; Note regarding backups at UT CS:

; Even though it's convenient to refer to our UT CS development directory as
; /projects/acl2/devel/, we'll need to get backups from
; /v/filer4b/v11q002/acl2space/acl2/.snapshot/*/devel, not from
; /projects/acl2/.snapshot/*/devel.  The latter is just a soft link to
; /projects/acl2/devel, i.e., to /v/filer4b/v11q002/acl2space/acl2/devel.

  '(
    #+acl2-par "multi-threading-raw"
    #+hons "serialize-raw"
    "axioms"
    "hons"      ; but only get special under-the-hood treatment with #+hons
    #+hons "hons-raw" ; avoid possible inlining of hons fns in later sources
    "basis-a"   ; to be included in any "toothbrush"
    "memoize"   ; but only get special under-the-hood treatment with #+hons
    "serialize" ; but only get special under-the-hood treatment with #+hons
    "basis-b"   ; not to be included in any "toothbrush"
    "parallel" ; but only get special under-the-hood treatment with #+acl2-par
    #+acl2-par "futures-raw"
    #+acl2-par "parallel-raw"
    #+hons "memoize-raw"
    "translate"
    "type-set-a"
    "linear-a"
    "type-set-b"
    "linear-b"
    "non-linear"
    "tau"
    "rewrite"
    "simplify"
    "bdd"
    "other-processes"
    "induct"
    "proof-builder-pkg"
    "doc"
    "history-management"
    "prove"
    "defuns"
    "proof-builder-a"
    "defthm"
    "other-events"
    "ld"
    "proof-builder-b"
    "apply-raw"
    "interface-raw"
    "defpkgs"
    "boot-strap-pass-2-a"
    "apply-prim"
    "apply-constraints"
    "apply"
    "boot-strap-pass-2-b"
    )
  "*acl2-files* is the list of all the files necessary to build
ACL2 from scratch.")

; CLISP version 2.30 (along with perhaps other versions) locks the LISP
; package.  That causes problems when we try to read the second form in
; axioms.lisp, which defines
; acl2::*common-lisp-symbols-from-main-lisp-package*, when CLISP tries to read
; some of the symbols in that list (e.g., CALL-METHOD) into the COMMON-LISP
; package.  (Specifically, INTERN breaks.)  We use eval below to avoid any
; chance (we hope) of getting an "undefined function" warning with earlier
; CLISP versions.

#+clisp
(if (fboundp 'package-lock)
    (eval '(setf (package-lock "LISP") nil)))

; CLISP version 2.33 defines the symbol custom::*suppress-check-redefinition*,
; but version 2.30 does not.  We temporarily unlock that package if necessary
; in order to define this variable.  While we are at it we make the variable
; special, in order to avoid potential compiler warnings in 2.30 when we bind
; it but never use it.

#+clisp
(if (not (find-symbol "*SUPPRESS-CHECK-REDEFINITION*" "CUSTOM"))
    (if (fboundp 'package-lock)
        (let ((old-lock (package-lock "CUSTOM")))
          (eval '(setf (package-lock "CUSTOM") nil))
          (let ((sym (intern "*SUPPRESS-CHECK-REDEFINITION*" "CUSTOM")))
            (eval `(defvar ,sym nil)))
          (eval `(setf (package-lock "CUSTOM") ',old-lock)))
      (let ((sym (intern "*SUPPRESS-CHECK-REDEFINITION*" "CUSTOM")))
        (eval `(defvar ,sym nil)))))

(with-open-file
 (fl "axioms.lisp" :direction :input)

;  Get into the main lisp package in order to read in
;  *common-lisp-symbols-from-main-lisp-package*.

 (let ((*package* (find-package #-CLTL2 "LISP" #+CLTL2 "COMMON-LISP")))

;  Skip the in-package

   (read fl)

;  Do the defconst for *common-lisp-symbols-from-main-lisp-package*.

   (setq acl2::*copy-of-common-lisp-symbols-from-main-lisp-package*
         (eval (caddr (read fl))))
   (import acl2::*copy-of-common-lisp-symbols-from-main-lisp-package* "ACL2")

   (setq acl2::*copy-of-acl2-version*
;  Keep this in sync with the value of acl2-version in *initial-global-table*.
         (concatenate 'string
                      "ACL2 Version 8.3"
                      #+non-standard-analysis
                      "(r)"
                      #+(and mcl (not ccl))
                      "(mcl)"))

;  Do the defconst for *common-lisp-specials-and-constants*.

   (setq acl2::*copy-of-common-lisp-specials-and-constants*
         (eval (caddr (read fl))))))

(in-package "ACL2")

(defun proclaim-optimize ()

; With SBCL 1.2.10, we have seen a saved_acl2 start up without the compiler
; optimizations that we had installed during the build.  Perhaps that has been
; true for other SBCL versions or even other Lisps.  The problem appears to be
; that (in SBCL 1.2.10 at least), proclaim forms can be local to the file in
; which they appear, even if the file isn't explicitly compiled.  So we call
; this function in acl2-default-restart, and also at the top level when
; building ACL2, to ensure that our compiler optimizations are in force, and we

  (proclaim #+cltl2 common-lisp-user::*acl2-optimize-form*
            #-cltl2 user::*acl2-optimize-form*))

(defparameter *compiled-file-extension*

; Note that for the community books, files books/Makefile-generic,
; books/Makefile-subdirs, and books/Makefile-psubdirs all deal with compiled
; file extensions.  Thanks to Gary Byers for suggested the following approach
; for #+ansi-cl, which however appears to work for all Lisps supported as of
; early 2006.

  (pathname-type (compile-file-pathname "foo.lisp")))

(defmacro initialize-state-globals ()
  (let ((acl2-compiler-enabled-var
         #+cltl2 'common-lisp-user::*acl2-compiler-enabled*
         #-cltl2 'user::*acl2-compiler-enabled*))
    `(let ((state *the-live-state*))
       (dolist (pair *initial-global-table*)
         (f-put-global (car pair) (cdr pair) state))
       (f-put-global 'acl2-sources-dir (our-pwd) state)
       (f-put-global 'iprint-ar
                     (compress1 'iprint-ar
                                (f-get-global 'iprint-ar state))
                     state)
       (f-put-global 'compiler-enabled

; Either t, nil, or :books is fine here.  For example, it might be reasonable
; to initialize to (not *suppress-compile-build-time*).  But for now we enable
; compilation of books for all Lisps.

                     (cond ((boundp ',acl2-compiler-enabled-var)
                            (or (member ,acl2-compiler-enabled-var
                                        '(t nil :books))
                                (error "Illegal value for ~
                                        user::*acl2-compiler-enabled*, ~s"
                                       ,acl2-compiler-enabled-var))
                            ,acl2-compiler-enabled-var)
                           (t

; Warning: Keep the following "compile on the fly" readtime conditional in sync
; with the one in acl2-compile-file.

                            #+(or ccl sbcl)
                            :books
                            #-(or ccl sbcl)
                            t))
                     state)
       (f-put-global
        'host-lisp
        ,(let () ; such empty binding has avoided errors in  GCL 2.6.7
           #+gcl :gcl
           #+ccl :ccl
           #+sbcl :sbcl
           #+allegro :allegro
           #+clisp :clisp
           #+cmu :cmu
           #+lispworks :lispworks
           #-(or gcl ccl sbcl allegro clisp cmu lispworks)
           (error
            "Error detected in initialize-state-globals: ~%The underlying ~
             host Lisp appears not to support ACL2. ~%Contact the ACL2 ~
             implementors to request such support."))
        state)
       (f-put-global
        'compiled-file-extension
        ,*compiled-file-extension*
        state)
       #+unix
       (f-put-global 'tmp-dir "/tmp" state)
       #+gcl ; for every OS, including Windows (thanks to Camm Maguire)
       (when (boundp 'si::*tmp-dir*)
         (f-put-global 'tmp-dir si::*tmp-dir* state))
       #-acl2-mv-as-values
       (f-put-global 'raw-arity-alist *initial-raw-arity-alist*
                     state)
       nil)))

(defconstant *suppress-compile-build-time*

; This flag controls whether explicit calls to the compiler during the build,
; that is via compile and compile-file, are suppressed.  The "interpreters" of
; SBCL and CCL compile on-the-fly, so a nice optimization is for us to
; avoid calling the compiler ourselves.

  #+(or sbcl ccl) ; these compile on-the-fly
  t
  #-(or sbcl ccl)
  nil)

(defparameter *global-package-prefix* "ACL2_GLOBAL_")

(defparameter *1*-package-prefix* "ACL2_*1*_")

(defun make-global-package (x)
  (let* ((n (concatenate 'string *global-package-prefix* x))
         (p (find-package n)))
    (cond (p
           (do-symbols (sym p)
                       (makunbound sym)))
          (t (make-package n :use nil)))))

(defun make-*1*-package (x)
  (let* ((n (concatenate 'string *1*-package-prefix* x)))

; Unlike make-global-package, here we really don't have to worry about bound
; (or fbound) symbols.  Presumably ``bound'' is irrelevant, and ``fbound'' is
; taken care of by our undoing mechanisms.

    (make-package n :use nil)))

(or (find-package "ACL2-INPUT-CHANNEL")
    (make-package "ACL2-INPUT-CHANNEL" :use nil))

(or (find-package "ACL2-OUTPUT-CHANNEL")
    (make-package "ACL2-OUTPUT-CHANNEL" :use nil))


; Next we define the initial global and *1* packages.

(defconstant *main-lisp-package*
  (find-package "COMMON-LISP"))

(defconstant *main-lisp-package-name-raw*
; Keep this in sync with *main-lisp-package-name*.
  "COMMON-LISP")

; Keep the following in sync with *main-lisp-package-name*.
(make-global-package *main-lisp-package-name-raw*)
(make-global-package "KEYWORD")
(make-global-package "ACL2")
(make-global-package "ACL2-INPUT-CHANNEL")
(make-global-package "ACL2-OUTPUT-CHANNEL")

; Keep the following in sync with *main-lisp-package-name*.
(make-*1*-package *main-lisp-package-name-raw*)
; Functions cannot be defined in the keyword package, so we do not do so.
;  (make-*1*-package "KEYWORD")
(make-*1*-package "ACL2")
(make-*1*-package "ACL2-INPUT-CHANNEL")
(make-*1*-package "ACL2-OUTPUT-CHANNEL")

; Common Lisp does not require that the symbol-package of the basic
; Lisp symbols be the basic LISP or COMMON-LISP package, but merely
; that those symbols be exported from that package.

(defparameter acl2::*initial-lisp-symbol-mark*
  'acl2_invisible::initial-lisp-symbol-mark)

(let ((cl-pkg-name *main-lisp-package-name-raw*))
  (dolist (sym *copy-of-common-lisp-symbols-from-main-lisp-package*)

; We support the Invariant on Symbols in the Common Lisp Package.  See the long
; comment about this invariant in the symbolp case of bad-lisp-objectp.

    (setf (get sym *initial-lisp-symbol-mark*) cl-pkg-name)))

(defconstant *acl2-package* (find-package "ACL2"))

(dolist (x *features*)
        (cond ((or (equal "AKCL-SET-MV"
                          (symbol-name x))
                   (equal "ACL2-LOOP-ONLY"
                          (symbol-name x))
                   (equal "ACL2-METERING"
                          (symbol-name x)))
               (format t "~%~%Warning:  This Common Lisp may be ~
                          unsuitable for ACL2 because a symbol with~
                          ~%the name \"ACL2-LOOP-ONLY\", ~
                          \"AKCL-SET-MV\" or \"ACL2-METERING\" is ~
                          a member of *FEATURES*."))))

#+akcl
(if (fboundp 'si::set-mv)
    (push :akcl-set-mv *features*)
  (error "Use a version of ACKL after 206"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                            EXITING LISP
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *acl2-panic-exit-status* nil)

#+ccl
(defun common-lisp-user::acl2-exit-lisp-ccl-report (status)

; Gary Byers says (email, 1/12/2016) that he believes that the first of 5
; values returned by (GCTIME) is the sum of the other four, which are full and
; then 3 levels of ephemeral/generational.  He also says that these are
; reported in internal-time-units, which are microseconds on x8664.

  (declare (ignore status))
  (format t
          "~%(ccl::total-bytes-allocated) = ~s~%(ccl::gctime) ~
           = ~s~%(ccl::gccounts) = ~s~%~%"
          (ccl::total-bytes-allocated)
          (multiple-value-list (ccl::gctime))
          (multiple-value-list (ccl::gccounts))))

#+cltl2
(defvar common-lisp-user::*acl2-exit-lisp-hook*
  nil)

(defun exit-lisp (&optional (status '0 status-p))

; Parallelism blemish: In ACL2(p), LispWorks 6.0.1 hasn't always successfully
; exited when exit-lisp was called.  The call below of stop-multiprocessing is
; an attempt to improve the chance of a successful exit.  In practice, the call
; does not fix the problem.  However, we leave it for now since we don't think
; it can hurt.  If exit-lisp starts working reliably without the following
; calls to send-die-to-worker-threads and stop-multiprocessing, they should be
; removed.

  #+cltl2
  (when (fboundp common-lisp-user::*acl2-exit-lisp-hook*)
    (funcall common-lisp-user::*acl2-exit-lisp-hook* status)
    (setq common-lisp-user::*acl2-exit-lisp-hook* nil))
  #+(and acl2-par lispworks)
  (when mp::*multiprocessing*
    (send-die-to-worker-threads)
    (mp::stop-multiprocessing))

; The status (an integer) will be returned as the exit status (shell variable
; $?).  We avoid passing the status argument when it is 0, in case Windows or
; other operating systems get confused by it.  However, this function is a
; no-op if we are already in the process of quitting via this function; see the
; comment below the occurrence below of *acl2-panic-exit-status*.

; It appeared at one point that (ccl::quit 0) is more reliable than
; (ccl::quit), but that's no longer clear.  Still, it seems reasonable to pass
; the status explicitly to the individual Lisp's exit function if that status
; is passed explicitly here -- hence the use of status-p.

  (cond
   ((null status) ; shouldn't happen
    (error "Passed null status to exit-lisp!"))
   (*acl2-panic-exit-status*

; We have seen various type errors and bus errors when attempting to quit in
; CCL.  Gary Byers pointed out that this may be caused by attempting to quit
; while in the process of quitting.  So, we avoid doing a quit if already in
; the process of quitting.

    (return-from exit-lisp nil)))
  (setq *acl2-panic-exit-status* status)
  #+clisp
  (if status-p (user::exit status) (user::exit))
  #+lispworks ; Version 4.2.0; older versions have used bye
  (if status-p (lispworks:quit :status status) (lispworks:quit))
  #+akcl
  (if status-p (si::bye status) (si::bye))
  #+lucid
  (lisp::exit) ; don't know how to handle status, but don't support lucid
  #+ccl
  (if status-p (ccl::quit status) (ccl::quit))
  #+cmu
  (cond ((null status-p)
         (common-lisp-user::quit t))
        (t ; quit does not take an exit status as of CMUCL version 19e
         (unix:unix-exit status)))
  #+allegro
  (user::exit status :no-unwind t)
  #+(and mcl (not ccl))
  (cl-user::quit) ; mcl support is deprecated, so we don't worry about status
  #+sbcl
  (let ((sym (or (find-symbol "EXIT" 'sb-ext)
                 (find-symbol "QUIT" 'sb-ext))))

; Quoting http://www.sbcl.org/manual/#Exit, regarding sb-ext:quit:

;   Deprecated in favor of sb-ext:exit as of 1.0.56.55 in May 2012. Expected to
;   move into late deprecation in May 2013.

    (cond ((or (null sym)
               (not (fboundp sym)))
           (error "No function named \"EXIT\" or \"QUIT\" is defined in the ~%~
                   \"SB-EXT\" package.  Perhaps you are using a very old or ~%~
                   very new version of SBCL.  If you are surprised by this ~%~
                   message, feel free to contact the ACL2 implementors."))
          ((equal (symbol-name sym) "EXIT")
           (if status-p
               (funcall sym :code status)
             (funcall sym)))
          (t ; (equal (symbol-name sym) "QUIT")
           (if status-p
               (funcall sym :unix-status status)
             (funcall sym)))))

; Return status (to avoid an ignore declaration) if we cannot exit lisp.  The
; caller of this function should complain if Lisp survives the call.  The panic
; flag may help though.

  (progn status-p status))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                CHECKS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; See acl2-check.lisp for more checks.

; We allow ACL2(h) code to take advantage of Ansi CL features.  It's
; conceivable that we don't need this restriction (which only applies to GCL),
; but it doesn't currently seem worth the trouble to figure that out.
#+(and hons (not cltl2))
(progn
; ACL2(c) deprecated: no longer says "build a hons-enabled version of ACL2".
  (format t "~%ERROR: It is illegal to build ACL2 in this non-ANSI Common ~
             Lisp.~%~%")
  (acl2::exit-lisp))

; The following macro turns off some style warnings.  It is defined here
; instead of the "LISP BUGS AND QUIRKS" section because we want to define this
; in the ACL2 package.

(defmacro with-redefinition-suppressed (&rest forms)

; This macro is equivalent to progn for SBCL and CMUCL, where we typically
; suppress more warnings anyhow; see with-warnings-suppressed.

  `(let (#+lispworks
         (compiler::*redefinition-action* :QUIET)
         #+allegro
         (excl:*redefinition-warnings* nil)
         #+clisp
         (custom::*suppress-check-redefinition*

; This binding may not suffice during the build.  Below is a comment that is
; probably old as of this writing (Oct. 9, 2011).

; Unfortunately, the above binding seems to be ignored when in the scope of
; with-compilation-unit, so we get redefinition warnings from clisp during the
; build.  Here is an example that exhibits that behavior CLISP 2.44.1 (even
; without ACL2); and the same problem occurs if we switch the order of
; with-compilation-unit and the binding of *suppress-check-redefinition*.

;   (common-lisp::with-compilation-unit
;    ()
;    (let ((custom::*suppress-check-redefinition* t))
;      (dolist (name '("foo" "bar"))
;        (let ((source (make-pathname :name name :type "lisp")))
;          (load source)
;          (progn
;            (compile-file source)
;            (load (make-pathname :name name :type "fas")))))))

          t)
         #+ccl
         (ccl::*compiler-warn-on-duplicate-definitions* nil)
         #+gcl
         (compiler::*warn-on-multiple-fn-definitions* nil))
     #+gcl ; We believe that this variable was introduced in GCL 2.6.12.
     (declare (special ; being safe; seems autoloaded via compiler::emit-fn
               compiler::*warn-on-multiple-fn-definitions*))
     ,@forms))

(defmacro with-warnings-suppressed (&rest forms)

; See also the handler-bind call in init.lisp.  Thanks to Juho Snellman for his
; assistance with handler-bind.

; We are happy to turn off redefinition warnings because we trust that
; functions such as add-trip know what they are doing.  Without this code, for
; example, :oops can cause many screens of such warnings.

  #+sbcl

; Warning: We turn off all warnings in SBCL because they are so noisy.  We
; eliminate most of them in the proclaim form earlier in this file, using
; (sb-ext:inhibit-warnings 3), because without that the following doesn't work;
; just start up sbcl and submit the following form without the leading
; backquote and replacing ,@forms by (defun f (x y) x).

; `(handler-bind
;   ((warning       (lambda (c)
;                     (declare (ignore c))
;                     (invoke-restart 'muffle-warning)))
;    (style-warning (lambda (c)
;                     (declare (ignore c))
;                     (invoke-restart 'muffle-warning))))
;   ,@forms)

; However, even with the above proclaim form we still get redefinition
; warnings.  So we wrap the following handler-bind around forms in order to
; eliminate redefinition warnings as well.

  `(handler-bind
    ((warning (lambda (c)
                (declare (ignore c))
                (invoke-restart 'muffle-warning))))
    ,@forms)

  #+cmu
  `(progn (setq ext:*gc-verbose* nil)
          (handler-bind
           ((warning (lambda (c)
                       (declare (ignore c))
                       (invoke-restart 'muffle-warning))))
           ,@forms))

; We include allegro below to avoid "unreachable" warnings from the compiler,
; as would otherwise appear when compiling function FROM-TO-BY-AC during the
; build.
  #+(or lispworks allegro)
  `(with-redefinition-suppressed
    (handler-bind
     ((style-warning (lambda (c)
                       (declare (ignore c))
                       (invoke-restart 'muffle-warning))))
     ,@forms))

  #-(or sbcl cmu lispworks allegro)
  `(with-redefinition-suppressed ,@forms))

(defmacro with-more-warnings-suppressed (&rest forms)

; We add additional warning suppression beyond what is provided by
; with-warnings-suppressed.  Warning: We do not necessarily suppress all
; warnings that are suppressed by with-warnings-suppressed, so you will
; probably want to call this macro in a context underneath
; with-warnings-suppressed.

; The handler-bind form given in with-warnings-suppressed for sbcl and cmucl is
; sufficient; we do not need anything further here.  But even with the addition
; of style-warnings (as commented there), that form doesn't seem to work for
; CCL, Allegro CL, or CLISP.  So we bind some globals instead.

; Through Version_8.3 we dealt with style-warning here when #+allegro, but that
; is now done in with-warnings-suppressed.

  #+clisp
  `(let ((*compile-verbose* nil))
     ,@forms)

  #+ccl
  `(let ((ccl::*suppress-compiler-warnings* t))
     ,@forms)

  #-(or clisp ccl)
  (if (cdr forms) `(progn ,@forms) (car forms)))

(defmacro with-suppression (&rest forms)

; Since "COMMON-LISP" is a package known to ACL2, a user should have permission
; to type 'common-lisp::foo (say) and not get a reader error due to a package
; lock.  This macro suppresses the package lock on "COMMON-LISP" for Lisps
; where we know this is necessary, and also inhibits some warnings.

  #-(or sbcl clisp) `(with-warnings-suppressed ,@forms)
  #+sbcl `(sb-ext:with-unlocked-packages
           ("COMMON-LISP")
           (with-warnings-suppressed ,@forms))
  #+clisp `(ext:without-package-lock
            ("COMMON-LISP")
            (with-warnings-suppressed ,@forms)))

; The following may prevent an error when SBCL compiles ec-calls in the
; definition of apply$-lambda.  We may do something more principled in the
; future.  The names could be obtained with (add-suffix name *inline-suffix*),
; except that add-suffix and inline-suffix* are not yet defined here.  We could
; wait until they are, but then we'd need to teach note-fns-in-form about
; with-suppression.
#-acl2-loop-only
(with-suppression
 (intern "CAR$INLINE" "COMMON-LISP")
 (intern "CDR$INLINE" "COMMON-LISP"))

(defconstant acl2::*acl2-status-file*
  (make-pathname :name "acl2-status"
                 :type "txt"))

(defun acl2::check-suitability-for-acl2 ()

; As of version 18a, cmulisp spews gc messages to the terminal even when
; standard and error output are redirected.  So we turn them off.

  (with-warnings-suppressed
   (or (not (probe-file *acl2-status-file*))
       (delete-file *acl2-status-file*))
   (load "acl2-check.lisp")

; At one time we wrote ":CHECKED" to the file *acl2-status-file*, in order to
; avoid both running this check here and then later, running this check again
; in compile-acl2.  But as of 2/2017 we timed the load above at about 1/5
; second; that seemed sufficiently negligible that it seemed fine to
; run the check twice in return for being able to avoid having "make full"
; needlessly recompile when *acl2-status-file* is up-to-date.

   t))

(defun note-compile-ok ()
  (progn (or (not (probe-file *acl2-status-file*))
             (delete-file *acl2-status-file*))
         (with-open-file (str *acl2-status-file*
                              :direction :output)
                         (format str
                                 "~s"
                                 :compiled))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                       COMPILING and LOADING, PART 1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; To compile ACL2, invoke (load "acl2.lisp") and then invoke
; (acl2::compile-acl2).  Having compiled ACL2, to build ACL2, invoke
; (load "acl2.lisp") and then invoke (acl2::load-acl2).  To run ACL2
; verified code, one may either load all of ACL2 as above, or
; alternatively, having complied ACL2, invoke (load "acl2.lisp") and
; invoke (acl2::load-acl2-execution-environment).  The top-level user
; functions for ACL2 are in package "ACL2", so invoke (in-package
; "ACL2") to obviate typing package names.

; NOTE: In order to compile ACL2, checks must first be run on the suitability
; of the underlying Common Lisp implementation, by executing
; (check-suitability-for-acl2).  Successful compilation should write out file
; *acl2-status* with the symbol :COMPILED.

; Compiling is a no-op if *suppress-compile-build-time* is non-nil, but we
; still write :COMPILED as indicated above.

(defvar *lisp-extension* "lisp")

#+sbcl ; turn off compiler notes (noisy)
(declaim (sb-ext:muffle-conditions sb-ext:compiler-note))

; The Allegro CL documentation tells us that the following variable is
; "Initially true only if speed is 3 and safety is 0", and that it allows the
; compiler to assume that the sum of two declared fixnums is a fixnum, etc.  We
; hope that by setting this variable to nil we avoid seeing occasional checksum
; errors during include-book when certifying the regression suite.
#+allegro
(setf comp:declared-fixnums-remain-fixnums-switch nil)

; Previous value for the above:
; (eval (read-from-string "
;   (SETQ COMPILER::DECLARED-FIXNUMS-REMAIN-FIXNUMS-SWITCH
;         #'(LAMBDA (X Y Z #+(VERSION>= 4 1) D) NIL)) "))

; The following appears to allow tail recursion elimination for functions
; locally defined using LABELS.  This is important for efficiency since we
; use LABELS in defining executable-counterparts (see e.g. oneify-cltl-code).
#+allegro
(setq compiler:tail-call-non-self-merge-switch t)

; LispWorks Version 4.2.0 has issued the following complaint during compilation
; until the next form was executed:
; **++++ Error in NTH-UPDATE-REWRITER1:
;   Function size 73824 is too large.
; But even with the next form, we have seen the following:
; **++++ Error in XTRANS-EVAL:
;   Function size 67910 is too large.
; This problem has disappeared with LispWorks 6.0.  But it seems reasonable to
; leave the following in place.
#+lispworks
(cl-user::toggle-source-debugging nil)

(defmacro our-with-compilation-unit (form)

; In fact, with-compilation-unit is only defined in dpANS, not CLtL2.  But MCL
; and CCL do seem to support it, so we allow it with #+cltl2 and #+ccl.
; We also have noticed that while :CLTL2 belongs to *features* in Version
; :CMU17 (presumably 17f), it does not belong in a cmucl version 18d that we
; obtained for Linux, even though with-compilation-unit continues to be
; defined.

  #+cltl2
  `(common-lisp::with-compilation-unit
    ()
    ,form)
  #-cltl2
  form)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                           BASIC FUNCTIONS TO BE COMPILED
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;  Functions for proclaiming and for defining ACL2's Implementation of the
;  Backquote Readmacro are to be compiled, so we do not include them in the
;  present file.  Instead we put them in acl2-fns.lisp, after defining the
;  following constant.  (We could put this defconstant in acl2-fns.lisp, but
;  CLISP would warn unless we made it conditional on a (not (boundp ..))
;  check.  That sort of fix has gotten us into trouble with Allegro, so we take
;  the simpler solution of putting the defconstant in this file, which is
;  loaded only once (there is no compiled version of this file to load).

(defconstant *acl2-read-character-terminators*
  '(#\Tab #\Newline #\Page #\Space #\" #\' #\( #\) #\; #\` #\,))

(our-with-compilation-unit

; At one time we avoided recompiling and had the following code inside a COND:

;    ((and (probe-file object-file)
;          (<= (file-write-date "acl2-fns.lisp")
;              (file-write-date object-file)))
;     (load object-file))

; But for example, if we compile with Allegro under SunOS and then later build
; the system with Allegro under Linux, the same ".fasl" extension could fool us
; into thinking that recompilation is not necessary.

 (progn
   (load "acl2-fns.lisp") ;we like to load before compiling
   (let ((acl2-fns-compiled
          (make-pathname :name "acl2-fns"
                         :type *compiled-file-extension*)))
     (when (probe-file acl2-fns-compiled)
       (delete-file acl2-fns-compiled))
     (when (not *suppress-compile-build-time*)
       (compile-file "acl2-fns.lisp")

; Note that load-compiled is not used below, but on the other hand we are still
; using the original readtable here so that's not a problem.

       (load acl2-fns-compiled)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                           ACL2-READTABLE
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defparameter *acl2-readtable*
  (copy-readtable nil)
  "*acl2-readtable* is the readtable we use (a) to restrict the use of
#. to cause evaluation during READing (b) and to define our own version
of backquote.")

(defparameter *host-readtable*
  (copy-readtable)
  "*host-readtable* is the original readtable provided by the host Lisp,
which is saved just in case it's needed later.")

(defun set-new-dispatch-macro-character (char subchar fn)

; This function currently causes an error when attempting to build ACL2(h) on
; top of CLISP, where (get-dispatch-macro-character #\# #\Y) evaluates to
; #<SYSTEM-FUNCTION SYSTEM::CLOSURE-READER>.  Here is a discussion of that
; issue.

; With some thought we might be able to avoid the special cases below for which
; char is #\# and subchar is, for example, #\Y -- i.e., smashing (in that
; example) which reader is invoked by #\Y.  We certainly have in mind our own
; semantics for ACL2 source files, to be read using *acl2-readtable*, while the
; host Lisp's semantics are expected for compiled files.  But consider files
; like .cert and @expansion.lsp files, i.e., files that may be written by the
; host Lisp (see the call of prin1 in print-object$-ser) but are read by ACL2.
; Perhaps the issue goes away if we are using the serialize reader and writer,
; as must be the case when we install a reader for #\Y.  We may think all this
; through when there is sufficient reason to do so.  For now, the only problem
; pertaining to our handling of dispatch macro characters is in the case of
; CLISP and ACL2(h), since #\Y is already defined in CLISP -- this function
; causes an error when attempting to build ACL2(h) on CLISP.  Since CLISP is
; much slower than the other six host Lisps that we support, and since ACL2(h)
; is optimized for CCL such that it is really only intended for CCL at this
; point (June 2013), we can live without CLISP support for ACL2(h).

  (let ((old (get-dispatch-macro-character char subchar)))
    (cond ((or (null old)
               (eql fn old)
               #+cmu

; This is really just a guess, but it's a pretty good one, as several values of
; subchar (for char equal to #\#) give this function, at least in our copies of
; CMU CL 19e and CMU CL 20D.

               (eq old (symbol-function 'LISP::DISPATCH-CHAR-ERROR))
               #+gcl

; For GCL, Camm Maguire has told us that he believes that it's safe for us to
; make this redefinition for these characters.

               (and (eql char #\#)
                    (member subchar '(#\@ #\! #\u #\Y #\Z)))
               #+allegro

; The #u reader has been defined in Allegro CL to invoke parse-uri.  It seems
; harmless to overwrite it (especially since we only smash #u in
; *acl2-readtable*).  David Margolies of Franz Inc. has kindly pointed us to
; the web page
; http://www.franz.com/support/documentation/8.1/doc/uri.htm#acl-implementation-1
; where we find this:

;   4. #u"..." is shorthand for (parse-uri "...") but if an existing #u
;   dispatch macro definition exists, it will not be overridden.

               (and (eql char #\#)
                    (member subchar '(#\u))))
           (set-dispatch-macro-character char subchar fn))
          (t (error "ACL2 cannot be built in this host Lisp, because ~%~
                     ~s is already defined, to be: ~s"
                    `(get-dispatch-macro-character ,char ,subchar)
                    old)))))

(defun define-sharp-dot ()
  (set-dispatch-macro-character
   #\#
   #\.
   #'sharp-dot-read))

; Define-sharp-atsign is defined in interface-raw.lisp.

(defun define-sharp-bang ()
  (set-new-dispatch-macro-character
   #\#
   #\!
   #'sharp-bang-read))

(defun define-sharp-u ()
  (set-new-dispatch-macro-character
   #\#
   #\u
   #'sharp-u-read))

(defun define-sharp-f ()
  (set-new-dispatch-macro-character
   #\#
   #\f
   #'sharp-f-read))

(defvar *old-character-reader*
  (get-dispatch-macro-character #\# #\\))

(defun modify-acl2-readtable (do-all-changes)
  (let ((*readtable* *acl2-readtable*))

; Jared's new fancy string reader

    (set-new-dispatch-macro-character
     #\#
     #\{
     'fancy-string-reader-macro)

; Thanks to Jared Davis for contributing the code for #\Y and #\Z (see
; serialize-raw.lisp).  Note that Section 2.4.8 Sharpsign of the Common Lisp
; Hyperspec (also Table 22-4, p. 531 of CLtL2) specifies that #\Y and #\Z may
; be available to us (though we check this by using
; set-new-dispatch-macro-character).  Keep these two settings in sync with
; *reckless-acl2-readtable*.

    #+hons ; SBCL requires #+hons (same restriction as ser-hons-reader-macro)
    (set-new-dispatch-macro-character
     #\#
     #\Z
     'ser-hons-reader-macro)

    #+hons ; SBCL requires #+hons (same restriction as ser-cons-reader-macro)
    (set-new-dispatch-macro-character
     #\#
     #\Y
     'ser-cons-reader-macro)

; Backquote

    (set-macro-character
     #\`
     #'(lambda (stream char)
         (declare (ignore char))
         (let ((*backquote-counter* (1+ *backquote-counter*)))
           (backquote (read stream t nil t)))))

; Comma

    (set-macro-character
     #\,
     #'(lambda (stream char)
         (declare (ignore char))
         (let ((*backquote-counter* (1- *backquote-counter*)))
           (acl2-comma-reader stream))))

;  Restrict #.

    (when do-all-changes
      (define-sharp-dot)
;     (define-sharp-atsign) ; see interface-raw.lisp
      (define-sharp-bang)
      (define-sharp-u)
      (define-sharp-f))

;  Keep control of character reader.  However, we do not need to keep such
;  control when reading in a .fas file for CLISP, and in fact, the set-theory
;  book's use of (code-char 255) generates
;  #\LATIN_SMALL_LETTER_Y_WITH_DIAERESIS in set-theory.fas.  We see no reason
;  to restrict reading of such characters in .fas files.

    (when do-all-changes
      (set-dispatch-macro-character
       #\#
       #\\
       #'acl2-character-reader))))

(eval-when
 #-cltl2
 (load eval compile)
 #+cltl2
 (:load-toplevel :execute :compile-toplevel)
 #-clisp
 (modify-acl2-readtable t)
 #+clisp
 (progn (modify-acl2-readtable nil)
        (defparameter *acl2-readtable-clisp-fas*
          (copy-readtable *acl2-readtable*))
        (let ((*readtable* *acl2-readtable*))
          (define-sharp-dot)
;         (define-sharp-atsign) ; see interface-raw.lisp
          (define-sharp-bang)
          (define-sharp-u)
          (define-sharp-f)
          (set-dispatch-macro-character
           #\#
           #\\
           #'acl2-character-reader))))

(defvar *reckless-acl2-readtable*

; See "SUPPORT FOR FAST #n= and #n#" in acl2-fns.lisp.

  (let ((*readtable* (copy-readtable *acl2-readtable*)))
    (set-dispatch-macro-character #\#
                                  #\#
                                  #'reckless-sharp-sharp-read)
    (set-dispatch-macro-character #\#
                                  #\=
                                  #'reckless-sharp-equal-read)
    (set-dispatch-macro-character
     #\#
     #\\
     *old-character-reader*)
    *readtable*))

;                       Remarks on *acl2-readtable*
;
;
; Because read-object calls the Common Lisp function read, read-object
; is a function of the values of the Common Lisp symbols (a)
; *readtable*, (b) *package*, and (c) *features*.  In ACL2, the user can
; specify the package to use, via in-package, which sets the global
; current-package.  The user of ACL2 has no (legitimate) control over the
; readtable, which is set above and discussed below.
;
; As for *features*, we currently permit full use of the *features*
; facility of the Common Lisp reader, with this caveat: it is an
; official part of the ACL2 story that *features* should have the same
; setting throughout all phases of ACL2 usage.  That is, the user must
; set up *features* at the beginning, before starting to use ACL2 and
; the user must then leave *features* alone (even though the
; implementors of ACL2 put :acl2-loop-only onto *features* during
; boot-strapping).  One bad consequence of our *features* policy is that
; verified files will not in general be verifiable or usable in other
; Lisp implementations or installations unless the settings of
; *features* relevant to one's usages of the #+ and #- are the same in
; the two Lisp implementations.  One simple way to obtain peace of mind
; on this topic is for the user not to use #+ or #- at all!  It might be
; cleaner for us simply to prohibit the use of the #+ and #- readmacros
; all together in ACL2.  This could be done at the cost of replacing the
; many uses of #+ and #- in axioms.lisp, and a few other places, with
; some sort of regular macro.
;
; Below is a detailed examination of the default Common Lisp readtable
; from the perspective of ACL2.  We want to make sure that when we read,
; we do not have side effects (e.g. via #.) of ACL2 but will merely
; either (a) cause an error or (b) generate a Lisp object, which we then
; will check with bad-lisp-object before handing it to ACL2 functions.
;
; All of the standard Common Lisp characters are either white space or
; constituent, with the following exceptions, which are read macros:
;
;   "  quote
;   #  number sign
;   '  quote
;   () parentheses
;   ,  comma
;   ;  comment
;   \  single escape
;   `  backquote
;   |  multiple escape
;
; With the exception of number sign, backquote and comma, we certainly
; want all of these readmacros to have their usual Common Lisp
; semantics.
;
; We have defined our own backquote and discussed it above.
;
; We now review the # situation:
;
;   ## and #= are for reading possibly circular stuff
;          bad-lisp-object may run forever
;   #'  reads as function
;          won't hurt anything
;   #(  vector
;          will be rejected by bad-lisp-object
;   #)  signals an error
;          enough said
;   #*  bit vector
;          will be rejected by bad-lisp-object
;   #,  load-time evaluation
;          we shut it off
;   #0-#9 used for infix arguments
;          ok
;   #:  uninterned symbol
;          will be rejected by bad-lisp-object
;   #<  signals an error
;          enough said
;   #\  character object
;          will be checked by bad-lisp-object; see also below
;   #|  start comment, ended by |#
;          ok
;   #<backspace | tab | newline | linefeed | page | return | space>
;       signals an error -- ok
;   #+  and #-
;       see the discussion of *features* above
;   #.  read time evaluation
;          we restrict it
;   #A, #a  arrays
;          will be checked by bad-lisp-object
;   #B, #b  binary rational
;          ok
;   #C, #c complex
;          ok (rejected by bad-lisp-object except for rational components)
;   #O, #o octal
;          ok
;   #P, #p pathname
;          will be checked by bad-lisp-object
;   #R, #r radix-n
;          fine
;   #S, #s structure
;          will be rejected by bad-lisp-object
;   #X, #x hex
;          ok
;
; Eventually, it will be best to define a read function for ACL2 solely in terms
; of ACL2 character reading primitives.  Common Lisp read is ambiguous.  There is
; the ambiguity of backquote described above.  There is the ambiguity of which
; tokens get read as numbers.  To make matters a little more scary, there is
; nothing that prevents a Common Lisp implementation from adding, for example, a
; new # readmacro option that would provide something as potentially catastrophic
; as full-blown sharp-dot.  One obstacle to doing a read within ACL2 this is
; efficiency.  For example, ACL2 does not now support unread-char.  And given the
; requirement that whatever is specified in a guard must be checkable, it is
; unclear now how best to add unread-char since Common Lisp does permit one to
; detect whether a stream is in a ``just unread'' state.  ACL2 could enable one
; to answer such a question, but at the cost of having to store the information
; every time that a character was unread.


;          ACL2's Implementation of the character reader

; We have decided to take full charge of everything that # reader
; does, which is just a part of the way towards writing READ totally
; from scratch.  And we are pretty conservative about what #\ does
; accept; one can always get the characters one wants by using
; code-char.  Notice for example that if we're not careful, then ACL2
; could be potentially unsound when we have 8-bit characters, because
; it's conceivable that
;
; (equal (char-code "#\fifth-control-character") 5)
;
; is a theorem in one Common Lisp and yet
;
; (equal (char-code "#\fifth-control-character") 6)
;
; is a theorem in another.  Bizarre, but apparently not ruled out by
; dpANS.
;
; So, we manage this simply by modifying the character reader so that
; the #\ notation only works for single characters and for Space, Tab,
; Newline, Page, Rubout, and Return; an error is caused otherwise.

; Our algorithm for reading character objects starting with #\ is
; quite simple.  We accumulate characters until encountering a
; whitespace character or a terminating macro character, from the list
; *acl2-read-character-terminators*.  The result must be either a
; single standard character or else one of the names (up to case,
; which we ignore in the multiple-character case) SPACE, TAB, NEWLINE,
; PAGE, RUBOUT, and RETURN.  Otherwise we cause an error.  Note that
; if we do NOT cause an error, then any dpANS-compliant Common Lisp
; implementation's character reader would behave the same way, because
; dpANS says (in the section ``Sharpsign Backslash'') the following.

;    .....  After #\ is read, the reader backs up
;    over the slash and then reads a token, treating the initial slash
;    as a single escape character (whether it really is or not in the
;    current readtable).

; The rather involved description from dpANS in the section ``Reader
; Algorithm'' implies that when a token is terminated without error,
; it must be upon first encountering a whitespace character or a
; terminating macro character.

; Finally, here is an argument that we cannot reasonably allow ACL2 to
; accept character notations of the sort akcl allows, such as #\\112
; for #\J for example.  (By the way, 112 is octal for 74, which is
; (char-code #\J).)  This is sad, because it would have been nice to
; provide a way of reading arbitrary 8-bit characters in ACL2.

; In the following, we refer to documentation from Bill Schelter's
; info version of dpANS.

; So, assume that #\J parses the same as #\\112 (and we'll derive a
; ``contradiction'' of sorts).  The documentation from ``Sharpsign
; Backslash'' below implies that #\\112 parses as the character whose
; name is [STRING-UPCASE applied to] the 4-character string \112.  So
; if #\\112 parses as #\J, then the name of the character #\J is
; "\\112".  Then, the documentation for ``char-name'' (part of which
; is also below) implies that CHAR-NAME returns the character name,
; and hence (CHAR-NAME #\J) must be "\\112".  But probably this isn't
; true of the implementation (it's not true for akcl or allegro, for
; example).  And, it seems really dangerous for us to redefine
; CHAR-NAME in ACL2.

; What's worse, if we apply the first part of this argument to
; #\Newline, we see that the name of the character #\Newline is
; "\\12", which directly contradicts the final passage below from
; dpANS.

; In what follows we'll quote from dpANS (an emacs Info version).  We
; quote here from three sections, separated by ++++++++++++++++++.

;
; Sharpsign Backslash
; ...................
;
; Syntax: #\<<x>>
;
; [[[ text omitted ]]]
;
; When the token x is more than one character long, the x must have the
; syntax of a symbol with no embedded package markers.  In this case, the
; sharpsign backslash notation parses as the character whose name is
; (string-upcase x); see *See Character Names::.
;
; ++++++++++++++++++
;
; char-name                                                        [Function]
; ---------------------------------------------------------------------------
;
; `char-name'  character =>  name
;
; Arguments and Values::
; ......................
;
; character--a character.
;
; name--a string or nil.
;
; Description::
; .............
;
; Returns a string that is the name of the character, or nil if the
; character has no name.
;
; ++++++++++++++++++
;
; Character Names
; ---------------
;
; The following character names must be present in all conforming
; implementations:
;
; Newline


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                       COMPILING and LOADING, PART 2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun non-trivial-acl2-proclaims-file-p ()
  (with-open-file (str "acl2-proclaims.lisp"
                       :direction :input
                       :if-does-not-exist nil)
                  (and str
                       (let* ((new-cons (cons nil nil))
                              (val (read str nil new-cons)))
                         (and (not (eq new-cons val))

; We might not need the following, but just in case we decide always to print
; an in-package form into the file, we require that the file have at least two
; forms.

                              (not (eq new-cons
                                       (read str nil new-cons))))))))

(defun compile-acl2 (&optional use-acl2-proclaims)

; When use-acl2-proclaims is true, we are recompiling to take advantage of
; acl2-proclaims.lisp.  But if *do-proclaims* is false, then there shouldn't be
; such a file (or, it consists only of a comment), so there is no point in
; recompiling, and we return immediately.

  #+gcl
  (unless (gcl-version->= 2 6 12)
    (error "Versions of GCL before 2.6.12 are no longer supported.
You are using version ~s.~s.~s."
           si::*gcl-major-version*
           si::*gcl-minor-version*
           si::*gcl-extra-version*))

  (when (and use-acl2-proclaims
             (not *do-proclaims*)) ; see comment above
    (return-from compile-acl2 nil))

; Juho Snellman points out that SBCL resets the compiler policy on entry to
; LOAD / COMPILE-FILE, and restores the old value once the file has been loaded
; / compiled; thus the global proclaim is no longer in effect once COMPILE-ACL2
; gets called.  So we proclaim here even though for other Lisps besides SBCL it
; might be redundant with the global proclaim above.

  (proclaim-optimize)

  (with-warnings-suppressed

; Note on Illegal Instructions:  If ACL2 causes an illegal instruction
; trap it is difficult to figure out what is happening.  Here is a
; brute force way to do it.
; (0) create an events file or book that will recreate the
;     the state up to the event that causes the illegal instruction.
; (1) Copy saved_acl2 to old_saved_acl2
; (2) replace the declaim above with
;     (declaim (optimize (safety 3) (space 0) (speed 0)));
; (3) make full init
;     this will fail because of stack overflows during booting.
; (4) fire up old_saved_acl2
; (5) load the saved events file or book, recreating the state.
; (6) :q from (LP)
; (7) (progn (setq old-world-pair (get 'current-acl2-world 'acl2-world-pair))
;            t)
; (8) (dolist (name *acl2-files*)
;           (or (equal name "defpkgs")
;               (load source)))   ; load the (safety 3) .o files
;     Actually, the last time I did this I loaded each file manually
;     and I did not load ld or interface-raw.  I think they can be
;     loaded here though.
; (9) (progn (f-put-global 'current-acl2-world
;                          (car old-world-pair) *the-live-state*)
;            t)
;(10) (si::use-fast-links nil)
;(11) enter (LP) and execute the offending event.
;(12) once the bug is fixed, be sure to change the declaim
;     back to (safety 0) (speed 3) before recompiling.

; Note on loading before compiling.  We load each ACL2 source file before
; compiling it to make sure that the functions needed to execute macros have
; been defun-ed before they are called.  Normal Common Lisp compilation does
; not do this.  So we cause all forms to be executed before we start the
; compilation.  This guarantees that when macros run, the functions they call
; have been defined.

; In general, and for the same reason, all ACL2 user checked files are also
; loaded before they are compiled.

; As of version 18a, cmulisp spews gc messages to the terminal even when
; standard and error output are redirected.  So we turn them off.

   (cond
    (use-acl2-proclaims
     (cond ((non-trivial-acl2-proclaims-file-p)
            (load "acl2-proclaims.lisp"))
           (t
            (error "Note: For the call ~s, generated file ~
                         \"acl2-proclaims.lisp\" is missing or has no forms ~
                         in it."
                   `(compile-acl2 ,use-acl2-proclaims)))))
    #+gcl
    ((eq *do-proclaims* :gcl) ; and (not use-acl2-proclaims)
     (loop for f in (directory "*.fn")
           do
           (delete-file f))
     (compiler::emit-fn t)))
   (unless (and (probe-file *acl2-status-file*)
                (with-open-file (str *acl2-status-file*
                                     :direction :input)
                                (eq (read str nil)

; This check is insufficient to avoid running the check twice, but that's OK.
; See the comment about ":CHECKED" in check-suitability-for-acl2.

                                    :compiled)))
     (check-suitability-for-acl2))
   (when (not *suppress-compile-build-time*)
     (our-with-compilation-unit
      (let ((*readtable* *acl2-readtable*)
            #+akcl

; AKCL compiler note stuff.  We have so many tail recursive functions
; that the notes about tail recursion optimization are just too much
; to take.

            (compiler:*suppress-compiler-notes* t))
        (dolist (name *acl2-files*)
          (or (equal name "defpkgs")
              (let ((source (make-pathname :name name
                                           :type *lisp-extension*)))
                (load source)
                (or (equal name "proof-builder-pkg")
                    (progn
                      (compile-file source)
                      (load-compiled
                       (make-pathname :name name
                                      :type *compiled-file-extension*))))))))))
   #+gcl
   (when (and (not use-acl2-proclaims)
              (eq *do-proclaims* :gcl))
     (compiler::make-all-proclaims "*.fn"))
   (note-compile-ok)))

#+gcl
(defvar user::*fast-acl2-gcl-build* nil)

(defun load-acl2 (&key fast load-acl2-proclaims)

; If fast is true, then we are welcome to avoid optimizations that might make
; for a better saved image.  For example, we use fast = t when building simply
; to write proclaim forms into acl2-proclaims.lisp.

  (declare (ignorable fast))

  (proclaim-optimize)

  (our-with-compilation-unit ; only needed when *suppress-compile-build-time*
   (with-warnings-suppressed

    (when load-acl2-proclaims
      (cond ((non-trivial-acl2-proclaims-file-p)
             (load "acl2-proclaims.lisp"))
            (t (error "Expected non-trivial file acl2-proclaims.lisp!"))))

; If we are in the first pass of two passes, then don't waste time doing the
; slow build for GCL (where we compile all *1* functions as we go through
; initialization).

    #+(and gcl acl2-mv-as-values)
    (when fast
      (setq user::*fast-acl2-gcl-build* t))

    #+akcl

; We grow the image slowly, since we now do allocation on start-up.  We are
; assuming that people will be using load-acl2 only as part of the process of
; building a saved image, and hence that this slow growth policy will be undone
; by the function save-acl2-in-akcl.  If we are

    (when (not fast)
      (loop
       for type in
       '(cons fixnum symbol array string cfun sfun

; In akcl, at least some versions of it, we cannot call allocate-growth on the
; following two types.

              #+gcl contiguous
              #+gcl relocatable
              )
       do
       (si::allocate-growth type 1 10 50 2)))
    (cond
     ((or (not (probe-file *acl2-status-file*))
          (with-open-file (str *acl2-status-file*
                               :direction :input)
                          (not (member (read str nil)
                                       '(:compiled :initialized)))))
      (error "Please compile ACL2 using ~s, which will write~%~
              the token :COMPILED to the file acl2-status.txt."
             '(compile-acl2))))
    (let ((*readtable* *acl2-readtable*)
          (extension (if *suppress-compile-build-time*
                         *lisp-extension*
                       *compiled-file-extension*)))
      (dolist (name *acl2-files*)
        (or (equal name "defpkgs")
            (if (equal name "proof-builder-pkg")
                (load "proof-builder-pkg.lisp")
              (load-compiled (make-pathname :name name
                                            :type extension)))))
      (load "defpkgs.lisp")
      (in-package "ACL2")

; Do not make state special, as that can interfere with tail recursion removal.
; The following form is provided merely as a convenience to the user, who may
; want to execute ACL2 forms in raw Lisp.  The use of set instead of setq is to
; avoid getting a warning in cmulisp that state is undefined.

      (set 'state *the-live-state*)
      "ACL2"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                            DECLARATIONS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We use XARGS and IRRELEVANT in DECLARE forms.  By making this proclamation,
; we suppress compiler warnings.

(declaim (declaration xargs))
(declaim (declaration irrelevant))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                            CONSTANTS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Allegro 6.0 (and probably later versions) warns when the following two (at
; least) constants are in axioms.lisp, even with boundp checks (as in ACL2
; Version_2.5).  The warning is a result of evaluating the defconstant twice:
; when loading the source file and when subsequently loading the compiled file.
; So starting with Version_2.6 we put the constants here, since this file
; (acl2.lisp) is not compiled and hence is only loaded once.

(defconstant *slashable-array*

; The list below comes from evaluating the following form in the supported
; Lisps (Allegro CL, CCL, CMUCL, GCL, LispWorks, SBCL) and taking the union.
; A similar form is found in check-slashable.

;   (loop for i from 0 to 255
;         when (let ((str (coerce (list (code-char i)
;                                       #\A #\B
;                                       (code-char i)
;                                       #\U #\V
;                                       (code-char i))
;                                 'string)))
;                (not (eq (ignore-errors (read-from-string str))
;                         (intern str "CL-USER"))))
;         collect i)

; Our use of the form above is justified by the following paragraph from the
; ANSI standard (also quoted in may-need-slashes-fn).

;    When printing a symbol, the printer inserts enough single escape and/or
;    multiple escape characters (backslashes and/or vertical-bars) so that if
;    read were called with the same *readtable* and with *read-base* bound to
;    the current output base, it would return the same symbol (if it is not
;    apparently uninterned) or an uninterned symbol with the same print name
;    (otherwise).

  (let ((ar (make-array 256 :initial-element nil)))
    (loop for i in
          '(0 1 2 3 4 5 6 7
              8 9 10 11 12 13 14 15 16 17 18 19 20 21
              22 23 24 25 26 27 28 29 30 31 32 34 35
              39 40 41 44 58 59 92 96 97 98 99 100 101
              102 103 104 105 106 107 108 109 110 111
              112 113 114 115 116 117 118 119 120 121
              122 124 127 128 129 130 131 132 133 134
              135 136 137 138 139 140 141 142 143 144
              145 146 147 148 149 150 151 152 153 154
              155 156 157 158 159 160 168 170 175 178
              179 180 181 184 185 186 188 189 190 224
              225 226 227 228 229 230 231 232 233 234
              235 236 237 238 239 240 241 242 243 244
              245 246 248 249 250 251 252 253 254 255)
          do
          (setf (aref ar i)
                t))
    ar))

(defconstant *suspiciously-first-numeric-array*
  (let ((ar (make-array 256 :initial-element nil)))
    (dolist (x

; Inline *suspiciously-first-numeric-chars*; see the comment above.

             '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9 #\+ #\- #\. #\^ #\_))
            (setf (aref ar (char-code x))
                  t))
    ar))

(defconstant *suspiciously-first-hex-array*
  (let ((ar (make-array 256 :initial-element nil)))
    (dolist (x

; Inline *suspiciously-first-hex-chars*; see the comment above.

             '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9
               #\A #\B #\C #\D #\E #\F
               #\a #\b #\c #\d #\e #\f
               #\+ #\- #\. #\^ #\_))
            (setf (aref ar (char-code x))
                  t))
    ar))

(defconstant *base-10-array*
  (let ((ar (make-array 256 :initial-element nil)))
    (dolist (x

; Inline *base-10-chars*; see the comment above.

             '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))
            (setf (aref ar (char-code x))
                  t))
    ar))

(defconstant *hex-array*
  (let ((ar (make-array 256 :initial-element nil)))
    (dolist (x

; Inline *hex-digits*; see the comment above.

             '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9
               #\A #\B #\C #\D #\E #\F
               #\a #\b #\c #\d #\e #\f))
            (setf (aref ar (char-code x))
                  t))
    ar))

(defconstant *letter-array*
  (let ((ar (make-array 256 :initial-element nil)))
    (dolist (ch

; Inline *letter-array*; see the comment above.

             '(#\A #\B #\C #\D #\E #\F #\G #\H #\I #\J #\K #\L #\M #\N #\O #\P
               #\Q #\R #\S #\T #\U #\V #\W #\X #\Y #\Z
               #\a #\b #\c #\d #\e #\f #\g #\h #\i #\j #\k #\l #\m #\n #\o #\p
               #\q #\r #\s #\t #\u #\v #\w #\x #\y #\z))
      (setf (aref ar (char-code ch))
            t))
    ar))

(defmacro suspiciously-first-numeric-array (print-base)
  `(if (eql ,print-base 16)
       *suspiciously-first-hex-array*
     *suspiciously-first-numeric-array*))

(defmacro numeric-array (print-base)
  `(if (eql ,print-base 16)
       *hex-array*
     *base-10-array*))

(defconstant *char-code-backslash* (char-code #\\))

(defconstant *char-code-slash* (char-code #\/))

(defconstant *char-code-double-gritch* (char-code #\"))

; The following constant was originally in translate.lisp, but CLISP warned
; that it was being redefined.  This seems to be the same problem as mentioned
; above for Allegro, so we define it here.

(defconstant *big-n-special-object* '(nil . nil))

(defconstant *number-of-return-values*

; Keep this in sync with related code in translate11.

  32)

(defconstant *boole-array*

; Keep this in sync with the defconst forms just above the definition of
; boole$.

  (let ((ar (make-array 16 :element-type 'fixnum))
        (i 0))
    (declare (type (simple-array fixnum (*)) ar))
    (dolist (x `((boole-1     . ,boole-1)
                 (boole-2     . ,boole-2)
                 (boole-and   . ,boole-and)
                 (boole-andc1 . ,boole-andc1)
                 (boole-andc2 . ,boole-andc2)
                 (boole-c1    . ,boole-c1)
                 (boole-c2    . ,boole-c2)
                 (boole-clr   . ,boole-clr)
                 (boole-eqv   . ,boole-eqv)
                 (boole-ior   . ,boole-ior)
                 (boole-nand  . ,boole-nand)
                 (boole-nor   . ,boole-nor)
                 (boole-orc1  . ,boole-orc1)
                 (boole-orc2  . ,boole-orc2)
                 (boole-set   . ,boole-set)
                 (boole-xor   . ,boole-xor)))
      (or (typep (cdr x) 'fixnum)
          (error "We expected the value of ~s to be a fixnum, but it is ~s!"
                 (car x) (cdr x)))
      (setf (aref ar i) (cdr x))
      (incf i))
    ar))

; The following constants were originally in memoize-raw.lisp, but CMUCL caused
; a redefinition error.  This may be the same problem as mentioned above for
; Allegro.
#+hons
(progn

; locals used in functions generated by memoize-fn

(defconstant *mf-old-caller* (make-symbol "OLD-CALLER"))
(defconstant *mf-start-pons* (make-symbol "START-PONS"))
(defconstant *mf-start-bytes* (make-symbol "START-BYTES"))
(defconstant *mf-ans* (make-symbol "ANS"))
(defconstant *mf-ans-p* (make-symbol "ANS-P"))
(defconstant *mf-ma* (make-symbol "MA"))
(defconstant *mf-args* (make-symbol "ARGS"))
(defconstant *mf-2mmf* (make-symbol "MF-2MMF"))
(defconstant *mf-2mmf-fnn* (make-symbol "MF-2MMF-FNN"))
(defconstant *mf-count-loc* (make-symbol "MF-COUNT-LOC"))
(defconstant *attached-fn-temp* (make-symbol "ATTACHED-FN-TEMP"))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                            STATISTICS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; See the comment in *rewrite-depth-max* about rewrite stack depth:
; (push :acl2-rewrite-meter *features*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                            PROMPTS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; New ACL2 users sometimes do not notice that they are outside the ACL2
; read-eval-print loop when in a break.  See the discussion of "PROMPTS" in
; interface-raw.lisp for how we deal with this.  For GCL CLtL1, we currently
; (as of GCL version 2.6.6, and still at GCL version 2.6.12) need a patch for
; built-in function si::break-level in order to avoid going into raw Lisp in
; the default state, i.e., without having executed (set-debugger-enable t).
; This requires a package change, so we put that patch in a file that is not
; compiled; the present file serves nicely.  (Perhaps there's a better way?)

; However, we abandon this prompts mess for ANSI GCL, where it is not necessary
; in order to stay out of the debugger.

#+(and gcl (not cltl2)) ; Let's avoid this mess for the more recent ANSI GCL
(in-package "SYSTEM")
#+(and gcl (not cltl2))
(progn
(defvar *debug-prompt-suffix* "")
; See comment about ACL2 for how the following is patched from si::break-level.
(defun break-level-for-acl2 (at &optional env)
  (eval '(acl2::print-proof-tree-finish acl2::*the-live-state*))
  (let* ((*break-message* (if (stringp at) at *break-message*))
         (*quit-tags* (cons (cons *break-level* *quit-tag*) *quit-tags*))
         (*quit-tag* (cons nil nil))
         (*break-level* (if (not at) *break-level* (cons t *break-level*)))
         (*ihs-base* (1+ *ihs-top*))
         (*ihs-top* (1- (ihs-top)))
         (*current-ihs* *ihs-top*)
         (*frs-base* (or (sch-frs-base *frs-top* *ihs-base*) (1+ (frs-top))))
         (*frs-top* (frs-top))
         (*break-env* nil)
         (be *break-enable*)
         (*break-enable*
          (progn
            (if (stringp at) nil be)))
                                        ;(*standard-input* *terminal-io*)
         (*readtable* (or *break-readtable* *readtable*))
         (*read-suppress* nil)
         (+ +) (++ ++) (+++ +++)
         (- -)
         (* *) (** **) (*** ***)
         (/ /) (// //) (/// ///)
         )
                                        ; (terpri *error-output*)
    (unless (or be (not (stringp at)))
      (simple-backtrace)
      (break-quit (length (cdr *break-level*))))
    (catch-fatal 1)
    (setq *interrupt-enable* t)
    (cond ((stringp at) (set-current)(terpri *error-output*)
           (setq *no-prompt* nil)
           )
          (t (set-back at env)))
      (loop
       (setq +++ ++ ++ + + -)
       (cond (*no-prompt* (setq *no-prompt* nil))
             (t ; ACL2 patch is in the following form, only
              (format *debug-io* "~&~a~a~a>~{~*>~}"
                      (if (stringp at) "" "dbl:")
                      (if (eq *package* (find-package 'user)) ""
                        (package-name *package*))
                      *debug-prompt-suffix*
                      *break-level*)))
       (force-output *error-output*)
       (when
        (catch 'step-continue
        (catch *quit-tag*
          (setq - (locally (declare (notinline read))
                           (dbl-read *debug-io* nil *top-eof*)))
          (when (eq - *top-eof*) (si::bye -1))
          (let* ( break-command
                 (values
                  (multiple-value-list
                  (LOCALLY (declare (notinline break-call evalhook))
                           (if (keywordp -)(setq - (cons - nil)))
                           (cond ((and (consp -) (keywordp (car -)))
                                  (setq break-command t)
                                  (break-call (car -) (cdr -) 'si::break-command))
                                 (t (evalhook - nil nil *break-env*)))))))
            (and break-command (eq (car values) :resume )(return))
            (setq /// // // / / values *** ** ** * * (car /))
            (fresh-line *debug-io*)
            (dolist (val /)
                    (locally (declare (notinline prin1)) (prin1 val *debug-io*))
                    (terpri *debug-io*)))
          nil))
        (terpri *debug-io*)
        (break-current))))))
#+(and gcl (not cltl2))
(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                        Additional hacks for CCL
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Also see the acl2h-init code.

; Bob Boyer uses the following at times.

; #+ccl
; (in-package "CCL")
; #+ccl
; (flet ((go-slow
;         ()
;         (set-current-compiler-policy (new-compiler-policy :inline-self-calls #'false))
;         (set-current-file-compiler-policy (new-compiler-policy :inline-self-calls #'false))
;         (proclaim '(optimize (debug 3) (compilation-speed 0)
;                              (safety 3) (speed 0) (space 0)))))
;   (go-slow))

; The following two assignments seemed to speed up regression runs by about
; 7.7% as opposed to only the second, which seemed to have little effect.
; Binding these variables in LP, instead of this, didn't seem to provide any
; of that speed-up.
; NOTE: If you don't like these defaults, try Bob Boyer's approach: put these
; same forms in your ~/ccl-init.lisp file, but replacing nil with t.
; NOTE: The first of these seemed to be necessary even in 32-bit CCL r13193,
; where one might have expected that not to be the case.
#+ccl
(when (boundp 'ccl::*save-interactive-source-locations*)
  (setq ccl::*save-interactive-source-locations* nil))
#+ccl
(when (boundp 'ccl::*save-source-locations*)
  (setq ccl::*save-source-locations* nil))

; As of CCL revision 15972 (and probably many earlier revisions), CCL treats
; "~user/" as "~/".  (See CCL bug 1121,
; http://trac.clozure.com/ccl/ticket/1121.)  The following workaround was
; suggested by Gary Byers.  We modify it by avoiding this setting once the
; version exceeds 1.10 (as the bug was fixed in a 1.10 svn version).
#+ccl
(unless (or (> ccl::*openmcl-major-version* 1)
            (and (eql ccl::*openmcl-major-version* 1)
                 (> ccl::*openmcl-minor-version* 10)))
  (setq ccl:*trust-paths-from-environment* nil))

#+ccl ; originally for ACL2(h), but let's make behavior the same for ACL2
(setq ccl::*quit-on-eof* t)
