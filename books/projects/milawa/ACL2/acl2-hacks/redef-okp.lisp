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

(in-package "ACL2")

(defttag redef-okp)

;; We allow certify-book even if redef has been set previously.  This is
;; obviously unsound!

(progn!
 (set-raw-mode t)

;;; Matt K. comment 10/2022: The following definition was already out of date
;;; as of ACL2 Version 8.5 (maybe sooner): its argument list isn't even of the
;;; same length as the original.  That didn't seem to interfere with
;;; pre-release testing, so I'm not going to fix it now.  If this needs to be
;;; fixed then I suggest that someone copy the current definition of
;;; chk-acceptable-certify-book and show, with comments, exactly what has been
;;; changed.
 (defun chk-acceptable-certify-book (book-name full-book-name k ctx state
                                               suspect-book-action-alist)

; This function determines that it is ok to run certify-book on
; full-book-name and k.  Unless an error is caused we return a pair
; (cmds . pre-alist) that contains the two parts of the portcullis.
; If k is t it means that the existing certificate file specifies the
; intended portcullis.  It also means that there must be such a file
; and that we are in the ground zero state.  If all those things check
; out, we will actually carry out the portcullis to get into the right
; state by the time we return.

   (let ((names

; Warning: If you change the list of names below, be sure to change it
; in the call of note-certification-world in certify-book-fn.

          (cons 'defpkg *primitive-event-macros*))
         (wrld (w state)))
     (er-progn
      (cond ((ld-skip-proofsp state)
             (er soft ctx
                 "Certify-book must be called with ld-skip-proofsp set to nil."))
            ((f-get-global 'in-local-flg state)
             (er soft ctx
                 "Certify-book may not be called inside a LOCAL command."))
            ((global-val 'skip-proofs-seen wrld)
             (er soft ctx
                 "At least one command in the current ACL2 world was executed ~
                 while the value of state global variable '~x0 was not ~
                 nil:~|~%  ~y1~%(If you did not explicitly use ~
                 set-ld-skip-proofsp or call ld with :ld-skip-proofsp not ~
                 nil, then some other function did so, for example, rebuild.) ~
                 Certification is therefore not allowed in this world.  If ~
                 the intention was for proofs to be skipped for one or more ~
                 events in the certification world, consider wrapping those ~
                 events explicitly in skip-proofs forms.  See :DOC ~
                 skip-proofs."
                 'ld-skip-proofsp
                 (global-val 'skip-proofs-seen wrld)))
            ((ttag wrld)

; We disallow active ttag at certification time because we don't want to think
; about certain oddly redundant defttag events.  Consider for example executing
; (defttag foo), and then certifying a book containing the following forms,
; (certify-book "foo" 1 nil :ttags ((foo nil))), indicating that ttag foo is
; only active at the top level, not inside a book.

; (defttag foo)

; (defun f ()
;   (declare (xargs :mode :program))
;   (sys-call "ls" nil))

; The defttag expands to a redundant table event, hence would be allowed.
; Perhaps this is OK, but it is rather scary since we then have a case of a
; book containing a defttag of which there is no evidence of this in any "TTAG
; NOTE" string or in the book's certificate.  While we see no real problem
; here, since the defttag really is ignored, still it's very easy for the user
; to work around this situation by executing (defttag nil) before
; certification; so we take this conservative approach.

             (er soft ctx
                 "It is illegal to certify a book while there is an active ~
                 ttag, in this case, ~x0.  Consider undoing the corresponding ~
                 defttag event (see :DOC ubt) or else executing ~x1.  See ~
                 :DOC defttag."
                 (ttag wrld)
                 '(defttag nil)))
            (t (value nil)))
      (chk-book-name book-name full-book-name ctx state)
      (er-let*
       ((certp (certificate-filep full-book-name state)))
       (mv-let
        (erp cmds wrld-segs wrld-list state)
        (get-portcullis-cmds wrld nil nil nil names ctx state)
        (cond
         (erp (silent-error state))
         ((eq k t)
          (cond
           (cmds
            (er soft ctx
                "When you tell certify-book to recover the certification world ~
                from the old certificate, you must call certify-book in the ~
                initial ACL2 logical world -- so we don't have to worry about ~
                the certification world  clashing with the existing logical ~
                world.  But you are not in the initial logical world.  Use ~
                :pbt 1 to see the world."))
           ((not certp)
            (er soft ctx
                "There is no certificate on file for ~x0.  But you told ~
                certify-book to recover the certi~-fication world from the ~
                old certificate.  You will have to construct the ~
                certi~-fication world by hand (by executing the desired ~
                commands in the current logical world) and then call ~
                certify-book again."
                full-book-name))
           (t

; So k is t, we are in the initial world, and there is a certificate file
; from which we can recover the portcullis.  Do it.

            (er-let*
             ((cert-obj
               (chk-certificate-file full-book-name t ctx state
                                     (cons '(:uncertified-okp . nil)
                                           suspect-book-action-alist)
                                     t))
              (cert-obj-cmds (value (and cert-obj
                                         (access cert-obj cert-obj :cmds)))))
             (chk-acceptable-certify-book1 full-book-name
                                           (length cert-obj-cmds) ;; k
                                           cert-obj-cmds ;; cmds
                                           :omitted ;; wrld-segs
                                           wrld-list
                                           names
                                           (w state)
                                           ctx state)))))
         (t (chk-acceptable-certify-book1 full-book-name k cmds wrld-segs
                                          wrld-list names wrld ctx
                                          state)))))))))
