(in-package "ACL2")

#|

require-book.lisp
-----------------

Peter Dillinger, 12 August 2008

When a book depends on another for "use" but not for certification, use this
to either require or recommend the other book at include-book time without
requiring (or recommending) at certify-book or interactive development time.

The common example is that a book of macros does not depend on the functions
that the macro expansions call.  The possible downsides of including the book
with the "used" functions include
 * Introduction of artificial dependencies on other books.  Maybe not all of
   the other books are required for some limited uses of the book of macros.
 * Longer certification time because of the inclusion.
 * Dependence on ttags when, strictly speaking, there might not be such a
   dependence.

Basically, instead of

(include-book <name> ...)

you can write

(require-book <name> ...)

and that will fail only in one of these cases:
 * An argument such as :dir is invalid.
 * The specified book does not exit.
 * We are inside an include-book, not inside certify-book, and the specified
   book has not been included.

You can also write

(recommend-book <name> ...)

to just print out a message without failing if the specified book has not been
included at include-book time.  Like require-book, recommend-book will fail if
the specified book does not exist.  You can also use

(recommend-book <name> :for "use of the MY-WHATEVER macro" ...)

to give more specific messages for each recommended book.

|#

(program)
(set-state-ok t)

(defun er-get-full-book-name (user-book-name dir ctx state)
  (er-let*
    ((dir-value
      (cond (dir (include-book-dir-with-chk soft ctx dir))
            (t (value (cbd))))))
    (mv-let
     (full-book-name directory-name familiar-name)
     (parse-book-name dir-value user-book-name ".lisp" ctx state)
     (declare (ignore directory-name familiar-name))
     (value full-book-name))))

(defun chk-for-included-book-fn (user-book-name dir errmsg no-err-if-existsp ctx state)
  (er-let*
    ((full-book-name
      (er-get-full-book-name user-book-name dir ctx state)))
    (let ((include-book-alist0 (global-val 'include-book-alist (w state))))
      (er-progn
       (chk-book-name user-book-name full-book-name ctx state)
       (chk-input-object-file full-book-name ctx state)
       (if (and full-book-name
                (assoc-equal full-book-name include-book-alist0))
         (value t) ; good; already included
         (if no-err-if-existsp
           (pprogn
            (cond ((null errmsg) ; no message
                   state)
                  ((stringp errmsg)
                   (observation1 ctx errmsg (list (cons #\b full-book-name)) nil state))
                  ((and (consp errmsg)
                        (stringp (car errmsg))
                        (alistp (cdr errmsg)))
                   (observation1 ctx
                                 (car errmsg)
                                 (cons (cons #\b full-book-name)
                                       (cdr errmsg))
                                 nil
                                 state))
                  (t ; a default message
                   (observation ctx "Book has not been included: ~x0" full-book-name)))
            (value nil))
           (cond ((stringp errmsg)
                  (error1 ctx errmsg (list (cons #\b full-book-name)) state))
                 ((and (consp errmsg)
                       (stringp (car errmsg))
                       (alistp (cdr errmsg)))
                  (error1 ctx
                          (car errmsg)
                          (cons (cons #\b full-book-name)
                                (cdr errmsg))
                          state))
                 ((null errmsg) ; no error message
                  (mv t nil state))
                 (t ; a default message
                  (er soft ctx "Book has not been included: ~x0" full-book-name)))))))))

(defun maybe-chk-for-included-book-fn (user-book-name dir errmsg no-err-if-existsp ctx state)
  (let ((behalf-of (cond ((or (@ certify-book-info)
                              (assoc-eq 'certify-book (global-val 'embedded-event-lst (w state))))
                          'certify-book)
                         ((assoc-eq 'include-book (global-val 'embedded-event-lst (w state)))
                          'include-book)
                         (t
                          'top-level))))
    (state-global-let*
     ((print-case ':downcase set-print-case)) ; probably better in this case
     (if (eq behalf-of 'include-book)
       (chk-for-included-book-fn user-book-name dir errmsg no-err-if-existsp ctx state)
       (mv-let
        (erp includedp state)
        (chk-for-included-book-fn user-book-name dir nil t ctx state)
        (if erp
          (mv t nil state)
          (pprogn
           (fms "NOTE: Book ~p0 ~#3~[:dir ~p4 ~/~]~
                 ~#1~[has been included.  Perhaps ~
                 you didn't want that to be the case during ~
                 ~#2~[interactive development~/certify-book~]?~/has ~
                 not been included, but you are stipulating that ~
                 should be OK since we are not inside an ~
                 include-book.~]~%~%"
                `((#\0 . ,user-book-name)
                  (#\1 . ,(if includedp 0 1))
                  (#\2 . ,(if (eq behalf-of 'certify-book) 1 0))
                  (#\3 . ,(if dir 0 1))
                  (#\4 . ,dir))
                *standard-co*
                state
                nil)
           (value :inivisible))))))))

(defmacro require-book (user-book-name
                       &key
                       dir
                       ;; these are mostly ignored, but included for easy
                       ;; transition to/from include-book:
                       load-compiled-file uncertified-okp
                       defaxioms-okp skip-proofs-okp
                       ttags doc)
  `(with-output
    :stack :push :off :all
    (make-event
     (er-progn
      (state-global-let*
       ((inhibit-output-lst (caar (@ inhibit-output-lst-stack))))
       (maybe-chk-for-included-book-fn
        ',user-book-name
        ',dir
        '("Please include the following book first, which has been marked as ~
           required for *use* of this book (but wasn't required for ~
           certification): ~%~%~p0~%~%"
          (#\0 include-book ,user-book-name
           ,@(and dir `(:dir ,dir))
           ,@(and load-compiled-file `(:load-compiled-file ,load-compiled-file))
           ,@(and uncertified-okp `(:uncertified-okp ,uncertified-okp))
           ,@(and defaxioms-okp `(:defaxioms-okp ,defaxioms-okp))
           ,@(and skip-proofs-okp `(:skip-proofs-okp ,skip-proofs-okp))
           ,@(and ttags `(:ttags ,ttags))
           ,@(and doc `(:doc ,doc))))
        nil
        'require-book
        state))
      (value '(value-triple ',user-book-name)))
     :check-expansion t)))

(defmacro recommend-book (user-book-name
                          &key
                          dir
                          ;; special for recommend-book:
                          for
                          ;; these are mostly ignored, but included for easy
                          ;; transition to/from include-book:
                          load-compiled-file uncertified-okp
                          defaxioms-okp skip-proofs-okp
                          ttags doc)
  `(with-output
    :stack :push :off :all
    (make-event
     (er-progn
      (state-global-let*
       ((inhibit-output-lst (caar (@ inhibit-output-lst-stack))))
       (maybe-chk-for-included-book-fn
        ',user-book-name
        ',dir
        '("The following book, which has not yet been included, is recommended ~
           for ~@1: ~%~%~p0~%~%"
          (#\0 include-book ,user-book-name
           ,@(and dir `(:dir ,dir))
           ,@(and load-compiled-file `(:load-compiled-file ,load-compiled-file))
           ,@(and uncertified-okp `(:uncertified-okp ,uncertified-okp))
           ,@(and defaxioms-okp `(:defaxioms-okp ,defaxioms-okp))
           ,@(and skip-proofs-okp `(:skip-proofs-okp ,skip-proofs-okp))
           ,@(and ttags `(:ttags ,ttags))
           ,@(and doc `(:doc ,doc)))
          (#\1 ,(if (stringp for) for "use of this book")))
        t
        'recommend-book
        state))
       (value '(value-triple ',user-book-name)))
     :check-expansion t)))#|ACL2s-ToDo-Line|#

