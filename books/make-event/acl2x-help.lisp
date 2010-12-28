; Utilities to help in producing useful .acl2x files.  Also see :DOC
; set-write-acl2x.

(in-package "ACL2")

; We try to do right by users of the HONS version of ACL2.
(include-book "misc/hons-help" :dir :system)

; There are times when one does proofs during the expansion phase of a
; make-event, but one prefers not to redo proofs on behalf of the generated
; event.  Here we provide a utility, make-event-skip-proofs, that skips such
; proofs by default at the top level and when writing a .acl2x file (though
; this can be changed), but never causes the proofs to be skipped during book
; certification (at which time one presumably does not want to skip proofs).

; An example appears in acl2x-help-test.lisp.

(defmacro set-skip-proofs? (val)

; Use (set-skip-proofs? t) to cause skip-proofs? to skip proofs except when
; certifying a book; this is the default.  Use (set-skip-proofs? nil) if you
; want skip-proofs? to act like the identity macro.

; Note that if you do two-step certification with a generated .acl2x file as
; described in :DOC set-write-acl2x, and if you only use skip-proofs?
; indirectly by way of make-event-skip-proofs, then the certification step will
; not encounter any skip-proofs? form, as skip-proofs? calls will already have
; been removed.

  `(local (table skip-proofs?-table :the-key ,val)))

(table skip-proofs?-table :the-key t)

(defmacro make-event-skip-proofs (form
                                  &key
                                  (check-expansion 'nil check-expansion-p)
                                  (on-behalf-of 'nil on-behalf-of-p))
  `(make-event
    (er-let* ((ev ,form))
      (value (list 'skip-proofs? ev)))
    ,@(and check-expansion-p
           `(:check-expansion ,check-expansion))
    ,@(and on-behalf-of-p
           `(:on-behalf-of ,on-behalf-of))))

(defmacro skip-proofs? (form)
  `(make-event
    (cond ((or (and (f-get-global 'certify-book-info state)
                    (not (f-get-global 'write-acl2x state)))
               (not
                (cdr (assoc-eq :the-key
                               (table-alist 'skip-proofs?-table (w state))))))
           ',form)
          (t '(skip-proofs ,form)))))

(defmacro with-guard1 (guard form)

; Wart: This macro only works if form returns a single, non-stobj value (hence
; the "1" suffix in the name of this macro).

  `(cond (,guard ,form)
         (t (er hard? 'with-guard1
                "Unexpected with-guard1 failure, ~x0"
                ',guard))))

(mutual-recursion

(defun acl2x-expansion-alist-with-skip-proofs?2 (form)
  (declare (xargs :guard t))
  (case-match form
    (('record-expansion ('make-event-skip-proofs . &)
                        ('skip-proofs y))
     (acl2x-expansion-alist-with-skip-proofs?2 y))
    (('progn . x)
     (with-guard1
      (true-listp x)
      (hons 'progn
            (acl2x-expansion-alist-with-skip-proofs?2-lst x))))
    (('encapsulate sigs . x)
     (with-guard1
      (true-listp x)
      (hons 'encapsulate
            (hons sigs
                  (acl2x-expansion-alist-with-skip-proofs?2-lst x)))))
    (('local x)
     (hons-list 'local
                (acl2x-expansion-alist-with-skip-proofs?2 x)))
    (('skip-proofs x)
     (hons-list 'skip-proofs
                (acl2x-expansion-alist-with-skip-proofs?2 x)))
    (('with-output . x)
     (with-guard1
      (true-listp x)
      (hons 'with-output
            (hons-append (butlast x 1)
                         (hons-list
                          (acl2x-expansion-alist-with-skip-proofs?2
                           (car (last x))))))))
    (& form)))

(defun acl2x-expansion-alist-with-skip-proofs?2-lst (x)
  (declare (xargs :guard (true-listp x)))
  (cond ((endp x) nil)
        (t (hons (acl2x-expansion-alist-with-skip-proofs?2 (car x))
                 (acl2x-expansion-alist-with-skip-proofs?2-lst (cdr x))))))

)

(defun acl2x-expansion-alist-with-skip-proofs?1 (alist acc)
  (declare (xargs :guard (and (alistp alist)
                              (alistp acc))))
  (cond ((endp alist)
         (hons-copy (reverse acc)))
        (t (acl2x-expansion-alist-with-skip-proofs?1
            (cdr alist)
            (acons (caar alist)
                   (acl2x-expansion-alist-with-skip-proofs?2 (cdar alist))
                   acc)))))

(defun acl2x-expansion-alist-with-skip-proofs? (alist)
  (declare (xargs :guard t))
  (with-guard1 (alistp alist)
               (acl2x-expansion-alist-with-skip-proofs?1 alist nil)))

(defattach acl2x-expansion-alist acl2x-expansion-alist-with-skip-proofs?)
