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

(defttag include-raw)

(progn!
 (set-raw-mode t)

 (defun raw-compile (name error-on-fail on-fail state)
   #-cltl2
   (compile-file (extend-pathname (cbd) name state))
   #+cltl2
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
   nil)

 (defun raw-load-uncompiled (name error-on-fail on-fail state)
   #-cltl2
   (load (extend-pathname (cbd) name state))
   #+cltl2
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
   nil)

 (defun raw-load (name error-on-fail on-fail state)
   (let* ((fname (extend-pathname (cbd) name state))
          (compiled-fname (compile-file-pathname fname)))
     #-cltl2
     (load-compiled compiled-fname)
     #+cltl2
     (handler-case
      (load-compiled compiled-fname)
      (error (condition)
             (progn
               (format t "Compiled file ~a did not load; loading uncompiled ~a.~%Message: ~a~%"
                       (namestring compiled-fname)
                       fname condition)
               (raw-load-uncompiled name error-on-fail on-fail state)))))
   nil))


(defmacro include-raw (fname &key
                             (do-not-compile 'nil)
                             (on-compile-fail 'nil on-compile-fail-p)
                             (on-load-fail 'nil on-load-fail-p))
  ":doc-section miscellaneous
Include a raw Lisp file in an ACL2 book, with compilation~/

Note:  You must have a TTAG defined in order to use this macro.

Usage:
~bv[]
 (include-raw \"my-raw-lisp-file.lsp\")
 (include-raw \"a-raw-lisp-file.lsp\"
              :on-compile-fail
              (format t \"Compilation failed with message ~a~%\"
                      condition)
              :on-load-fail
              (cw \"Oh well, the load failed~%\"))
 (include-raw \"another-raw-lisp-file.lsp\"
              :do-not-compile t)
~ev[]

The path of the raw Lisp file must be given relative to the book containing the
include-raw form.

By default, the raw Lisp file will be compiled and loaded when the containing
book is certified.  When including the book, the compiled file will be loaded
if possible, otherwise the original file will be loaded instead.  By default,
if either compilation or loading fails, an error will occur.

The optional keywords ~c[:on-compile-fail] and/or ~c[:on-load-fail] may be used
to suppress the error for failed compilation or loading, respectively; their
argument is a term which will be evaluated in lieu of producing an error.  When
evaluating this term, the variable ~c[CONDITION] is bound to a value describing
the failure; see Common Lisp documentation on ~c[HANDLER-CASE].  (Note: for
non-ansi-compliant Common Lisp implementations, such as GCL 2.6.*, no such
error handling is provided.)

The optional keyword ~c[:do-not-compile] may be used to suppress compilation.
In this case, during book certification the file will just be loaded using
~c[load].  Similarly, during include-book we will only load the lisp file, and
not try to load a compiled file.

One further note:  In most or all Lisps, compiling foo.lisp and foo.lsp results
in the same compiled file (named foo.fasl, or something similar depending on
the Lisp.)  Therefore, it is a mistake to use the same base name for a raw Lisp
file with .lsp extension and an ACL2 book with .lisp extension, at least when
using this tool and depending on compilation.~/~/"
  `(progn
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
         (if (or (not (f-get-global 'certify-book-info state))
                 ,do-not-compile)
             (mv nil nil state)
           (raw-compile ,fname ,(not on-compile-fail-p)
                        ',on-compile-fail state)))
        (declare (ignore erp val))
        (value '(value-triple :invisible))))

     (progn!
      (set-raw-mode t)
      ;; According to Matt K., *hcomp-fn-macro-restore-ht* is nonnil only when
      ;; loading a book's compiled file.  We want to wait until the events of
      ;; the include-book are being processed to run this, so that our compiled
      ;; file isn't loaded twice.
      (when (null *hcomp-fn-macro-restore-ht*)
        (,(if do-not-compile 'raw-load-uncompiled 'raw-load)
         ,fname ,(not on-load-fail-p) ',on-load-fail state))
      (value-triple ,fname))))

