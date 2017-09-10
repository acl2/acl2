; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

; pcert.lisp -- provisional certification mechanism

(in-package "ACL2")



;; We implement our own provisional certification scheme for bootstrapping.
;; This predates ACL2's notion of provisional certificates.  We might
;; eventually switch to ACL2's new pcert mechanism, but at present it is not
;; very mature and our scheme doesn't require the extra acl2x pass.
;;
;; Basic instructions for using this scheme:
;;
;;   (provisionally-certify "foo")
;;
;; This is ordinarily done by the pcert.pl script.
;;
;; For earlier versions of ACL2 (up through at least 4.1) the certify-book-info
;; state global was just a string naming the book, and I did something here to
;; emulate certify-book.  But with the new ACL2 pcert mechanism, this is now
;; some complicated stupid defrec with very complicated semantics.  I don't
;; know how to properly fake it, and keep hitting problems with uncertified-okp
;; not being allowed no matter what mode I try.  Worse, I suspect this is all
;; going to get overhauled again soon and so I'll have to update whatever I do
;; to solve it.
;;
;; Well, fortunately the only function I was taking advantage of this was the
;; current-book-info macro from acl2-hacks/io.lisp, and it seems that this
;; macro was not even being used at all, so it doesn't really matter.
;;
;; So, now our pcert mechanism involves very little.  We basically just try to
;; ld the file, and see if it was successful.  If we successfully load the
;; file, we write out a .pcert file with its checksum.

(defun check-sum-file (filename state)
  (declare (xargs :guard (stringp filename) :mode :program :stobjs state))
  (mv-let (channel state)
          (open-input-channel filename :object state)
          (mv-let (sum state)
                  (check-sum channel state)
                  (let ((state (close-input-channel channel state)))
                    (mv sum state)))))

;; This is very basic.  It doesn't do any embeddable event checks
;; but does fail for incorrect theorems, at least.

(defun provisionally-certify-fn (filename state)
  (declare (xargs :guard (stringp filename)
                  :mode :program
                  :stobjs state))
  (let ((lisp-file  (concatenate 'string filename ".lisp"))
        (pcert-file (concatenate 'string filename ".mpcert")))
    (ld `((cw "Provisionally certifying ~x0.~%" ,filename)
          (ld ,lisp-file :ld-error-action :error)
          (mv-let (channel state) (open-output-channel ,pcert-file :object state)
            (mv-let (sum state) (check-sum-file ,lisp-file state)
              (let* ((state (fms! "~f0 check-sum ~f1~|"
                                  (list (cons #\0 ,lisp-file)
                                        (cons #\1 sum))
                                  channel state nil)))
                (close-output-channel channel state))))
          (cw "Provisional certification successful.~%")
          (exit 44))
        :ld-user-stobjs-modified-warning

; Matt K. mod: ACL2 now requires keyword :ld-user-stobjs-modified-warning in
; code.  If this macro is only to be evaluated at the top level, that keyword
; isn't needed.  But I'm including it, with value :same to preserve existing
; behavior, just in case someone uses it in code.  Perhaps more thought should
; be given to whether or not we want a warning here when a user stobj is
; modified.

        :same)))

(defmacro provisionally-certify (filename)
  `(provisionally-certify-fn ,filename state))

