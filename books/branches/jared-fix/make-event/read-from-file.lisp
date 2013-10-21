; The following example shows how to create events by reading a file.  It was
; constructed in response to a potential application suggested by David Rager
; and Sandip Ray.

; File read-from-file-data.lsp has the following three forms.

#|
3
a
(x y)
|# ;|

(in-package "ACL2")

; Notice that this inclue-book can be local, even though the make-event just
; after it refers to read-list.  That's because this make-event had a default
; :check-expansion field of nil, so expansion is suppressed during subsequent
; include-books.
(local (include-book "misc/file-io" :dir :system))

(make-event
 (er-let* ((file-contents (read-list (our-merge-pathnames
                                      (cbd)
                                      "read-from-file-data.lsp")
                                     'top-level
                                     state)))
          (value `(defconst *obtained-from-file*
                    ',file-contents))))

(defthm got-it-right
  (equal *obtained-from-file*
         '(3
           a
           (x y)))
  :rule-classes nil)

; The following two succeed even though misc/file-io is included locally,
; because there is a local around the make-event, so that the make-event is
; skipped entirely on the second pass.

(local
 (make-event
  (er-let* ((file-contents (read-list (our-merge-pathnames
                                       (cbd)
                                       "read-from-file-data.lsp")
                                      'top-level
                                      state)))
           (value `(defconst *obtained-from-file-again*
                     ',file-contents)))
  :check-expansion
  (defconst *obtained-from-file-again*
    '(3
      a
      (x y))))
 )

(local
 (make-event
  (er-let* ((file-contents (read-list (our-merge-pathnames
                                       (cbd)
                                       "read-from-file-data.lsp")
                                      'top-level
                                      state)))
           (value `(defconst *obtained-from-file-again*
                     ',file-contents)))
  :check-expansion
  t)
 )

; We remedy the potential problem of local include-book, mentioned above, by
; doing a non-local include-book of "file-io".

(include-book "misc/file-io" :dir :system)

; Next, using :check-expansion t, we cause a check at include-book time that
; the data file hasn't changed since certify-book time.  A fun thing to do is
; to modify read-from-file-data-mod.lsp after the book is certified and then
; watch the include-book fail.

(encapsulate
 ()

; For the following expansion it is critical that proofs are enabled during
; evaluation of the expansion result when :check-expansion is not nil.

; Very Technical Remark: Otherwise, the second pass of this encapsulate will
; cause the :check-expansion to fail because chk-embedded-event-form returns
; nil for local events done under ld-skip-proofsp = 'include-book.  See call of
; do-proofs? in make-event-fn in the ACL2 sources.

 (make-event
  (er-let* ((file-contents (read-list (our-merge-pathnames
                                       (cbd)
                                       "read-from-file-data.lsp")
                                      'top-level
                                      state)))
           (value `(local (defun foo ()
                            ',file-contents))))
  :check-expansion
  t)
 )

(make-event
 (er-let* ((file-contents (read-list (our-merge-pathnames
                                      (cbd)
                                      "read-from-file-data.lsp")
                                     'top-level
                                     state)))
          (value `(defconst *obtained-from-file-again*
                    ',file-contents)))
 :check-expansion
 (defconst *obtained-from-file-again*
   '(3
     a
     (x y))))
