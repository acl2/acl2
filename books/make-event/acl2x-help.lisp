; Utilities to help in producing useful .acl2x files.  Also see :DOC
; set-write-acl2x.

; Our first (and only, so far) utility is
; acl2x-expansion-alist-removing-maybe-skip-proofs.  Here is how things work
; when that utility is attached to the built-in stub acl2x-expansion-alist, as
; with the defattach form below.

; This utility is useful for cases that one does proofs during the expansion
; phase of a make-event, but prefers not to redo proofs for the generated
; event.  An example appears in acl2x-help-test.lisp.

; The key idea is that when writing out a .acl2x file, each call
; (maybe-skip-proofs x) is replaced by x.  Thus, if you do two-step
; certification with a generated .acl2x file as described in :DOC
; set-write-acl2x, then the certification step will not encounter any
; maybe-skip-proofs form occurring in a make-event expansion, as its calls will
; already have been removed.  It is convenient, in fact, to eliminate all
; record-expansion forms from the top level; and that is done as well.

; As a minor extra we arrange that if maybe-skip-proofs is encountered during
; book certification -- though this would generally only happen if a .acl2x
; file is not written out first, which would presumably not be typical -- then
; maybe-skip-proofs does not cause proofs to be skipped.  So if you use
; maybe-skip-proofs, then you can certify books without skipping proofs, even
; if you don't do the two-step process of first writing out a .acl2x file.

(in-package "ACL2")

; We try to do right by users of the HONS version of ACL2.
(include-book "misc/hons-help" :dir :system)

(defmacro maybe-skip-proofs (form)
  `(make-event
    (cond ((and (f-get-global 'certify-book-info state)
                (not (f-get-global 'write-acl2x state)))
           ',form)
          (t '(skip-proofs (progn (value-triple :maybe-skip-proofs) ,form))))))

(defmacro with-guard1 (guard form)

; Wart: This macro only works if form returns a single, non-stobj value (hence
; the "1" suffix in the name of this macro).

  `(cond (,guard ,form)
         (t (er hard? 'with-guard1
                "Unexpected with-guard1 failure, ~x0"
                ',guard))))

(mutual-recursion

(defun acl2x-expansion-alist-removing-maybe-skip-proofs2 (form)
  (declare (xargs :guard t))
  (case-match form
    (('record-expansion & y)
     (acl2x-expansion-alist-removing-maybe-skip-proofs2 y))
    (('progn . x)
     (with-guard1
      (true-listp x)
      (hons 'progn
            (acl2x-expansion-alist-removing-maybe-skip-proofs2-lst x))))
    (('encapsulate sigs . x)
     (with-guard1
      (true-listp x)
      (hons 'encapsulate
            (hons sigs
                  (acl2x-expansion-alist-removing-maybe-skip-proofs2-lst x)))))
    (('local x)
     (hons-list 'local
                (acl2x-expansion-alist-removing-maybe-skip-proofs2 x)))
    (('skip-proofs x)
     (case-match x
       (('progn '(value-triple :maybe-skip-proofs) y)
        (acl2x-expansion-alist-removing-maybe-skip-proofs2 y))
       (& (hons-list 'skip-proofs
                     (acl2x-expansion-alist-removing-maybe-skip-proofs2 x)))))
    (('with-output . x)
     (with-guard1
      (true-listp x)
      (hons 'with-output
            (hons-append (butlast x 1)
                         (hons-list
                          (acl2x-expansion-alist-removing-maybe-skip-proofs2
                           (car (last x))))))))
    (& form)))

(defun acl2x-expansion-alist-removing-maybe-skip-proofs2-lst (x)
  (declare (xargs :guard (true-listp x)))
  (cond ((endp x) nil)
        (t (hons (acl2x-expansion-alist-removing-maybe-skip-proofs2 (car x))
                 (acl2x-expansion-alist-removing-maybe-skip-proofs2-lst (cdr x))))))

)

(defun acl2x-expansion-alist-removing-maybe-skip-proofs1 (alist acc)
  (declare (xargs :guard (and (alistp alist)
                              (alistp acc))))
  (cond ((endp alist)
         (hons-copy (reverse acc)))
        (t (acl2x-expansion-alist-removing-maybe-skip-proofs1
            (cdr alist)
            (acons (caar alist)
                   (acl2x-expansion-alist-removing-maybe-skip-proofs2 (cdar alist))
                   acc)))))

(defun acl2x-expansion-alist-removing-maybe-skip-proofs (alist)
  (declare (xargs :guard t))
  (with-guard1 (alistp alist)
               (acl2x-expansion-alist-removing-maybe-skip-proofs1 alist nil)))

(defattach acl2x-expansion-alist acl2x-expansion-alist-removing-maybe-skip-proofs)
