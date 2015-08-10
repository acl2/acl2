(in-package "ACL2")
#|

inline-book.lisp
----------------

Peter Dillinger, 22 July 2008

This book has two rough replacements for INCLUDE-BOOK that don't require the
referenced book to be certified separately.  Basically, we use make-event to
"inline" all the events from the referenced book into the current book.
This enables one to split a single ACL2 book across several files, which can
be in different packages.

We handle in-package clauses and the acl2-defaults-table properly, but we
assume the portcullis is already satisfied.  One version, "inline-book,"
does not respect LOCAL events in the referenced book, while the other,
"encapsulate-book," does.  Also, (local (inline-book ...)) is not supported
but (local (encapsulate-book ...)) should work.

;The syntax is to replace "include-book" with "inline-book" or
"encapsulate-book," except that only the book name and any :dir argument are
used by inline-book.  All the other parameters are ignored/irrelevant and the
effect is that they are inherited from the parent book.


In a feat of make-event foo, the inclusion of this book can itself be inlined:

;(make-event
; (er-progn (ld "inline-book.lisp")
;           (make-event (compute-inline-book-value "inline-book"))))

Explanation:
;  (ld "inline-book.lisp") loads the definitions in this file but they only
persist for computing the next result.
  (compute-inline-book-value "inline-book") is able to complete because we
temporarily loaded in the definitions, and this returns all the forms in
this file for inlining into the current book.

|#

;harshrc (July 1 2010)
;helper function
;removes a single (first) entry from the alist given the key
(defun remove-entry-by-key (key alist)
  (if (endp alist)
      nil
    (if (eq key (caar alist))
        (cdr alist)
      (cons (car alist)
            (remove-entry-by-key key (cdr alist))))))

(defun generate-add-include-book-dir-calls (dir-alist)
  (if (or (endp dir-alist) t)
      nil
    (cons `(add-include-book-dir ,(caar dir-alist);kwd
                                 ,(cdar dir-alist));dir
          (generate-add-include-book-dir-calls (cdr dir-alist)))))


; this is the guts of reading a book .lisp file and turning it into a progn or
; an encapsulate
(defun compute-inline-book-fn (user-book-name dir respect-localp state)
  (declare (xargs :mode :program
                  :stobjs state))
  (let* ((ctx 'inline-book)
         (wrld0 (w state))
         (saved-acl2-defaults-table
          (table-alist 'acl2-defaults-table wrld0))
         (saved-acl2-defaults-table-minus-book-dir-alist;hack
          (remove-entry-by-key :INCLUDE-BOOK-DIR-ALIST saved-acl2-defaults-table))
         (saved-book-dir-alist (cdr (assoc-eq :include-book-dir-alist
                                              saved-acl2-defaults-table)))
         )
    (er-let*
      ((dir-value
        (cond (dir (include-book-dir-with-chk soft ctx dir))
              (t (value (cbd))))))
      (mv-let
       (full-book-name directory-name familiar-name)
       (parse-book-name dir-value user-book-name ".lisp" ctx state)
       (declare (ignore directory-name familiar-name))
       (er-progn
        (chk-book-name user-book-name full-book-name ctx state)
        (chk-input-object-file full-book-name ctx state)
        (er-let* ((ev-lst (read-object-file full-book-name ctx state)))
          (value `(,@ (if respect-localp '(encapsulate ()) '(progn))
                      ,@ (if (eq :logic
                                 (cdr (assoc-eq :defun-mode saved-acl2-defaults-table)))
                             nil
                           '((logic))) ; put into defun-mode :logic, as include-book does
                         ,@ (cdr ev-lst) ; skip in-package
                            ,@ (if respect-localp
                                   '() ; acl2-defaults-table automatically reset by encapsulate
                                 (cons `(table acl2-defaults-table nil
                                               ',saved-acl2-defaults-table-minus-book-dir-alist;hack
                                               :clear)
                                       ;;now restore the include-book-dir-alist field
                                       (generate-add-include-book-dir-calls saved-book-dir-alist)))
                               (value-triple ',full-book-name)))))))))

; for inlining this book in other books (see intro)
(defmacro compute-inline-book-value (user-book-name
                               &key
                               dir)
  `(er-let* ((ev (compute-inline-book-fn ',user-book-name
                                         ',dir
                                         nil
                                         state)))
     (value `(value-triple ',ev))))


; rough replacement for include-book that does not respect LOCAL
(defmacro inline-book (user-book-name
                       &key
                       dir
                       ;; these are ignored, but included for easy transition
                       ;; to/from include-book
                       load-compiled-file uncertified-okp
                       defaxioms-okp skip-proofs-okp
                       ttags doc)
  (declare (ignore load-compiled-file uncertified-okp
                       defaxioms-okp skip-proofs-okp
                       ttags doc))
  `(make-event
    (compute-inline-book-fn ',user-book-name
                            ',dir
                            nil
                            state)))


; rough replacement for include-book that respects LOCAL
(defmacro encapsulate-book (user-book-name
                       &key
                       dir
                       ;; these are ignored, but included for easy transition
                       ;; to/from include-book
                       load-compiled-file uncertified-okp
                       defaxioms-okp skip-proofs-okp
                       ttags doc)
  (declare (ignore load-compiled-file uncertified-okp
                       defaxioms-okp skip-proofs-okp
                       ttags doc))
  `(make-event
    (compute-inline-book-fn ',user-book-name
                            ',dir
                            t
                            state)))

