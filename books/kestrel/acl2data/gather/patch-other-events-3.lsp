; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; ...
; Also Copyright (C) 2023, Regents of the University of Texas
; Written by Matt Kaufmann and J Strother Moore
; as this is derived from ACL2 source file other-events.lisp.

; Last updated for git commit: 8ef94c04ca9a3c7b9d7708696479d609944db454

(defun chk-acceptable-certify-book (book-name full-book-string full-book-name
                                              dir suspect-book-action-alist
                                              cert-op k ctx state)

; This function determines that it is ok to run certify-book on
; full-book-name/full-book-string, cert-op, and k.  Unless an error is caused
; we return a cert-obj that contains, at least, the two parts of the
; portcullis, where the commands are adjusted to include make-event expansions
; of commands in the certification world.  If cert-op is :convert-pcert then we
; check that the portcullis commands from the certification world agree with
; those in the .pcert0 file, and we fill in fields of the cert-obj based on the
; contents of the .pcert0 file.

; Dir is either nil or the directory of full-book-string.

; patch file: ignore k and bind k locally to '?
  (declare (ignore k)) ;patch;
  (let ((names (cons 'defpkg (primitive-event-macros)))
        (k '?) ;patch;
        (wrld (w state))
        (dir (or dir
                 (directory-of-absolute-pathname full-book-string))))
    (er-progn
     (cond ((and (ld-skip-proofsp state)
                 (not (eq cert-op ':write-acl2xu)))
            (er soft ctx
                "Certify-book must be called with ld-skip-proofsp set to nil ~
                 (except when writing .acl2x files in the case that ~
                 set-write-acl2x has specified skipping proofs)."))
           ((f-get-global 'in-local-flg state)
            (er soft ctx
                "Certify-book may not be called inside a LOCAL command."))
           ((and (global-val 'skip-proofs-seen wrld)
                 (not (cdr (assoc-eq :skip-proofs-okp
                                     suspect-book-action-alist))))
            (er soft ctx
                "At least one event in the current ACL2 world was executed ~
                 with proofs skipped, either with a call of skip-proofs or by ~
                 setting ``LD special'' variable '~x0 to a non-nil value.  ~
                 ~@1(If you did not explicitly use ~
                 skip-proofs or set-ld-skip-proofsp, or call ld with ~
                 :ld-skip-proofsp not nil, then some other function did so, ~
                 for example, rebuild or :puff.)  Certification is therefore ~
                 not allowed in this world unless you supply certify-book ~
                 with :skip-proofs-okp t.  See :DOC certify-book."
                'ld-skip-proofsp
                (let ((x (global-val 'skip-proofs-seen wrld)))
                  (if (and (consp x) ; always true?
                           (eq (car x) :include-book))
                      (msg "Such an event was introduced via the ~
                            included book, ~x0.  "
                           (book-name-to-filename (cadr x) wrld ctx))
                    (msg "Such an event was:~|~%  ~y0~%"
                         x)))))
           #+skip ; patch file: always skip, not just when doing book-runes ;patch;
           ((global-val 'redef-seen wrld)
            (er soft ctx
                "At least one command in the current ACL2 world was executed ~
                 while the value of state global variable '~x0 was not ~
                 nil:~|~%  ~y1~%Certification is therefore not allowed in ~
                 this world.  You can use :ubt to undo back through this ~
                 command; see :DOC ubt."
                'ld-redefinition-action
                (global-val 'redef-seen wrld)))
           ((and (not (pcert-op-p cert-op))
                 (global-val 'pcert-books wrld))
            (let ((books (global-val 'pcert-books wrld)))
              (er soft ctx
                  "Certify-book has been invoked in an ACL2 world that ~
                   includes the book~#0~[ below, which is~/s below, each of ~
                   which is~] only provisionally certified: there is a ~
                   certificate file with extension .pcert0 or .pcert1, but ~
                   not with extension .cert.~|~%~@1~|~%A certify-book command ~
                   is thus illegal in this world unless a :pcert keyword ~
                   argument is specified to be :create or :convert."

; This error message may be printed with sysfiles.  It is of a sufficiently low
; level that this seems reasonable: good information is more important than a
; pleasant shape.

                books
                (print-indented-list-msg books 2 ""))))
           #+skip ; patch file: always skip, not just when doing book-runes ;patch;
           ((ttag wrld)

; We disallow an active ttag at certification time because we don't want to
; think about certain oddly redundant defttag events.  Consider for example
; executing (defttag foo), and then certifying a book containing the following
; forms, (certify-book "foo" 1 nil :ttags ((foo nil))), indicating that ttag
; foo is only active at the top level, not inside a book.

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
     (illegal-to-certify-check t ctx state)
     (cond ((eq cert-op :convert-pcert)
; Cause early error now if certificate file is missing.
            (check-certificate-file-exists full-book-string cert-op ctx state))
           (t (value nil)))
     (mv-let
      (erp cmds cbds state)
      (get-portcullis-cmds wrld nil nil names ctx state)
      (cond
       (erp (silent-error state))
       (t (chk-acceptable-certify-book1 book-name
                                        full-book-string full-book-name
                                        dir k cmds
                                        cbds names cert-op
                                        suspect-book-action-alist wrld ctx
                                        state)))))))

