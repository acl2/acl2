; Include raw Lisp files in ACL2 books
; Copyright (C) 2010 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original authors: Jared Davis and Sol Swords <{jared,sswords}@centtech.com>

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(defxdoc include-raw
  :parents (set-raw-mode progn! defttag)
  :short "A better way to load raw Lisp code than directly using @(see progn!)
or @(see set-raw-mode)."

  :long "<p>Sometimes you want to include raw Lisp code in an ACL2 book to
achieve better performance or do fancy things like connect to external
programs.  With <see topic='@(url defttag)'>trust tags</see>, you can do this.
Unfortunately, the built-in mechanisms (@(see progn!) and @(see set-raw-mode))
have some portability problems related to compilation, file paths, read tables,
non-ACL2 objects, and so on; see below for some examples.</p>

<h3>Using Include-Raw</h3>

<p>Using @('include-raw') solves some of these problems.  Here are some
examples of how to use it:</p>

@({
 (include-book \"tools/include-raw\" :dir :system)

 (defttag :my-ttag) ; required before calling include-raw

 (include-raw \"my-raw-lisp-file.lsp\")

 (include-raw \"another-raw-lisp-file.lsp\"
              :do-not-compile t)
})

<p>When you use @('include-raw'), your raw Lisp code goes into a separate file.
If your book is named @('foo.lisp'), then this file should typically be named
@('foo-raw.lsp').  Why?</p>

<ul>

<li>The @('.lsp') extension helps build systems realize that the raw file is
not a proper ACL2 book and should not be certified.</li>

<li>The @('-raw') part helps to avoid running into a problem: on most Lisps,
compiling @('foo.lisp') or @('foo.lsp') results in the same compiled file,
e.g., @('foo.fasl') or similar.  So it is a mistake to use the same base name
for a raw Lisp file with a @('.lsp') extension and an ACL2 book with @('.lisp')
extension.</li>

</ul>

<p>The path of the raw Lisp file must be given relative to the book containing
the @('include-raw') form.  Typically we put the raw Lisp file in the same
directory as its book.</p>

<p>By default, the raw Lisp file will be compiled and loaded when the
containing book is certified.  When including the book, the compiled file will
be loaded if possible, otherwise the original file will be loaded instead.  By
default, if either compilation or loading fails, an error will occur.</p>


<h3>Benefits</h3>

<p>Keeping raw Lisp code in a separate file means you can use various kinds of
Lisp syntax that are not allowed in ACL2.  Otherwise you have to jump through
awful hoops like having to @(see intern)ing the names of functions like
@('ccl::static-cons') that you want to call.  It's also nice to be able to use
floats, etc.</p>

<p>Using @('include-raw') instead of something like @('load') after a
@('set-raw-mode') means you get predictable path behavior.  Otherwise, unless
you go out of your way to save the @(see cbd) with a @(see make-event), you can
end up with @(see include-book) failing when you try to load your book from
other directories.</p>

<p>Using @('include-raw') means that by default your definitions get compiled,
which can help to avoid stack overflows on some Lisps that don't compile
definitions automatically.  This isn't the case for definitions submitted
inside a @(see progn!).  It also helps defend against the @(see comp) command
undoing your raw Lisp definitions.</p>


<h3>Optional Arguments</h3>

<p>The optional keywords @(':on-compile-fail') and/or @(':on-load-fail') may be
used to suppress the error for failed compilation or loading, respectively;
their argument is a term which will be evaluated in lieu of producing an error.
When evaluating this term, the variable @('condition') is bound to a value
describing the failure; see Common Lisp documentation on @('handler-case').
Note: for non-ansi-compliant Common Lisp implementations, such as GCL 2.6.*, no
such error handling is provided.  Here is an example:</p>

@({
 (include-raw \"a-raw-lisp-file.lsp\"
              :on-compile-fail
              (format t \"Compilation failed with message ~a~%\"
                      condition)
              :on-load-fail
              (cw \"Oh well, the load failed~%\")
              :host-readtable t)
})


<p>The optional keyword @(':do-not-compile') may be used to suppress
compilation.  In this case, during book certification the file will just be
loaded using @('load').  Similarly, during @('include-book') we will only load
the lisp file, and not try to load a compiled file.</p>

<p>The optional keyword @(':host-readtable') may be used to make sure that the
original @('*readtable*') for this Lisp is being used, instead of the ACL2
readtable, while reading the file.  This may sometimes be necessary to avoid
differences between ACL2's reader and what raw Lisp code is expecting.</p>")

(defmacro include-raw (fname &key
                             (do-not-compile 'nil)
                             (on-compile-fail 'nil on-compile-fail-p)
                             (on-load-fail 'nil on-load-fail-p)
                             (host-readtable 'nil))
  `(progn

     (progn!
      ;; [Jared] We originally defined these supporting functions above, but
      ;; that meant that just including the include-raw book required a ttag.
      ;; By putting these things into the macro itself, we get away from that.

      (set-raw-mode t)

      (defun raw-compile (name error-on-fail on-fail state)
        ;; Matt K., 3/1/2013: We avoid the use of #+cltl2/#-cltl2 below.  Otherwise, if
        ;; we certify this book with (non-ANSI) GCL, then the book will be uncertified
        ;; when included it with another Lisp -- and, vice-versa.  Worse yet is the
        ;; handling of expansion files on behalf of include-book option
        ;; :load-compiled-file :comp (see :DOC book-compiled-file).  We have seen a hard
        ;; lisp error when certifying the book with (non-ANSI) GCL and then trying to
        ;; use it with Allegro CL.  In that case, this book is included as uncertified,
        ;; but worse yet, the expansion file has saved the #-cltl2 definition, so
        ;; Allegro CL caused an error when a .fasl file was missing under the call just
        ;; below of load-compiled.
        (cond
         ((not (member :cltl2 *features*)) ; #-cltl2
          (compile-file (extend-pathname (cbd) name state)))
         (t ; #+cltl2
          (handler-case
           (compile-file (extend-pathname (cbd) name state))
           (error (condition)
                  (if error-on-fail
                      (let ((condition-str (format nil "~a" condition)))
                        (er hard 'include-raw
                            "Compilation of ~x0 failed with the following message:~%~@1~%"
                            name condition-str))
                    (eval `(let ((condition ',condition))
                             (declare (ignorable condition))
                             ,on-fail)))))
          nil)))

      (defun raw-load-uncompiled (name error-on-fail on-fail state)
        ;; See comment in raw-compile, above, for why we avoid #+cltl2/#-cltl2.
        (cond
         ((not (member :cltl2 *features*)) ; #-cltl2
          (load (extend-pathname (cbd) name state)))
         (t ; #+cltl2
          (handler-case
           (load (extend-pathname (cbd) name state))
           (error (condition)
                  (if error-on-fail
                      (let ((condition-str (format nil "~a" condition)))
                        (er hard 'include-raw
                            "Load of ~x0 failed with the following message:~%~@1~%"
                            name condition-str))
                    (eval `(let ((condition ',condition))
                             (declare (ignorable condition))
                             ,on-fail)))))
          nil)))

      (defun raw-load (name error-on-fail on-fail state)
        ;; See comment in raw-compile, above, for why we avoid #+cltl2/#-cltl2.
        (let* ((fname (extend-pathname (cbd) name state))
               (compiled-fname (compile-file-pathname fname)))
          (cond
           ((not (member :cltl2 *features*)) ; #-cltl2
            (cond ((probe-file compiled-fname)
                   (load-compiled compiled-fname))
                  (t (format t "Compiled file ~a does not exist; loading uncompiled ~a~%"
                             (namestring compiled-fname)
                             fname)
                     (raw-load-uncompiled name error-on-fail on-fail state))))
           (t ; #+cltl2
            (handler-case
             (load-compiled compiled-fname)
             (error (condition)
                    (progn
                      (format t "Compiled file ~a did not load; loading uncompiled ~a.~%Message: ~a~%"
                              (namestring compiled-fname)
                              fname condition)
                      (raw-load-uncompiled name error-on-fail on-fail state))))))
          nil)))

     (make-event
      (mv-let (erp val state)
        ;; This progn!, including the compilation of the file to be loaded,
        ;; will only happen during make-event expansion; that is, during
        ;; certification, top-level evaluation, or uncertified inclusion.
        ;; Furthermore, we check that ACL2 is currently certifying a book and
        ;; only perform the compilation if this is the case.  Why?
        ;;  - Book certification seems like a good time to compile files
        ;; associated with the book being certified; in particular, hopefully
        ;; the same book is not being certified multiple times simultaneously,
        ;; and no other book includes the same raw file.
        ;;  - It is intentional that this does _not_ happen during
        ;; certified inclusion, because this may interfere with parallel
        ;; certification: certifications of several files may simultaneously
        ;; include the containing book and try to compile the file, stomping
        ;; over each other's output.  Furthermore, if the book is certified,
        ;; then the compiled file should already exist.
        ;;  - In top-level evaluation/uncertified inclusion, the situation is a
        ;; bit more nuanced; it would be nice to load a compiled version of the
        ;; file.  However, we do not compile in these situations because
        ;; writing to the filesystem seems likely to be an unintended
        ;; consequence of including a book or running an "include-raw" command
        ;; at the top level.  Perhaps in the future we might allow the user to
        ;; customize what happens in each of these situations.
        (progn!
         (set-raw-mode t)
         (let ((*readtable* (if ,host-readtable
                                *host-readtable*
                              *acl2-readtable*)))
           (if (or (not (f-get-global 'certify-book-info state))
                   ,do-not-compile)
               (mv nil nil state)
             (raw-compile ,fname ,(not on-compile-fail-p)
                          ',on-compile-fail state))))
        (declare (ignore erp val))
        (value '(value-triple :invisible))))

     (progn!
      (set-raw-mode t)
      (let ((*readtable* (if ,host-readtable
                             *host-readtable*
                           *acl2-readtable*)))
        ;; According to Matt K., *hcomp-fn-macro-restore-ht* is nonnil only
        ;; when loading a book's compiled file.  We want to wait until the
        ;; events of the include-book are being processed to run this, so that
        ;; our compiled file isn't loaded twice.
        (when (null *hcomp-fn-macro-restore-ht*)
          (,(if do-not-compile 'raw-load-uncompiled 'raw-load)
           ,fname ,(not on-load-fail-p) ',on-load-fail state)))
      (value-triple ,fname))))

