; Input file: ACL2 s-expressions.
; Tweaked by MJCG on 24.Oct.205 to update acl2_list_ref

; Output file: acl2_list_ref := [x1,x2,...,xk] 
; where each xi is the translation of the i-th input file expression.

; To do: If a2ml is run in other than the ACL2 package, then cons and nil could
; print out with package prefixes, which is not what is desired.  This may
; require some thought.

(in-package "ACL2")
(set-state-ok t)
(program)

(defconst *mksym*  'mksym)
(defconst *mk_chars_str*  'mk_chars_str)
(defconst *mkchr*  'mkchr)
(defconst *mknum*  'mknum)
(defconst *mkpair* 'mkpair)

(defun i2s (n)
  (coerce (explode-atom n 10) 'string))

(defun s2conses (s n result)
  (declare (xargs :guard (and (stringp s)
                              (natp n)
                              (< n (length s)))))
  (if (zp n)
      result
    (let ((k (1- n)))
      (s2conses s k (list 'cons (char-code (char s k)) result)))))

(defun sexp-to-ml (x)
  (cond ((characterp x)
         (list *mkchr* (char-code x)))
        ((stringp x)
         (list *mk_chars_str*
               (list 'chars_to_string
                     (s2conses x (length x) nil))))
        ((acl2-numberp x)
         (let ((rp (realpart x))
               (ip (imagpart x)))
           (list *mknum*
                 (i2s (numerator rp)) (i2s (denominator rp))
                 (i2s (numerator ip)) (i2s (denominator ip)))))
        ((symbolp x)
         (list *mksym* (symbol-package-name x) (symbol-name x)))
        ((atom x)
         (er hard 'sexp-to-ml
             "Unknown atom, ~x0"
             x))
        (t ; consp case
         (list *mkpair*
               (sexp-to-ml (car x))
               (sexp-to-ml (cdr x))))))

(defun pprint-object (obj channel state)
  (fms "~f0" (list (cons #\0 obj)) channel state nil))

(defun pprint-objects-to-ml (list sep channel state)
  (cond
   ((endp list)
      state)
   ((and (consp (car list))
         (eq (caar list) 'include-book))

; Include-book forms are not exported to ML.  See the comment about
; include-book in ../ISSUES (as of August 19, 2010).

    (pprint-objects-to-ml (cdr list) sep channel state))
   (t
    (prog2$
     (and (consp (car list))
          (eq (caar list) 'defpkg)
          (er hard 'pprint-objects-to-ml
              "Unexpected defpkg form, ~x0, in a book.  We had thought that ~
                defpkg forms would only be in the portcullis commands for a ~
                book."
              (car list)))
     (pprogn (pprint-object (sexp-to-ml (car list)) channel state)
             (newline channel state)
             (if (endp (cdr list)) state (princ$ sep channel state))
             (newline channel state)
             (pprint-objects-to-ml (cdr list) sep channel state))))))

(defun a2ml-read-eval-up-to-in-package1 (ch file ctx acc state)
  (mv-let (eofp val state)
          (read-object ch state)
          (cond (eofp
                 (er soft ctx
                     "Reached end of file ~x0 before finding in-package form."
                     file))
                (t (cond ((and (consp val)
                               (eq (car val) 'in-package))
                          (cond
                           ((and (true-listp val)
                                 (eql (length val) 2)
                                 (stringp (cadr val))
                                 (find-non-hidden-package-entry
                                  (cadr val)
                                  (known-package-alist state)))
                            (value (cons val acc)))
                           (t (er soft ctx
                                  "IN-PACKAGE must have a single argument, ~
                                    which is a known package name.  The form ~
                                    ~x0 in file ~x1 is thus illegal.  The ~
                                    known packages are~*2"
                                  val
                                  file
                                  (tilde-*-&v-strings
                                   '&
                                   (strip-non-hidden-package-names
                                    (known-package-alist state))
                                   #\.)))))
                         (t (er-progn
                             (trans-eval val ctx state t)
                             (a2ml-read-eval-up-to-in-package1
                              ch file ctx
                              (cond ((and (consp val)
                                          (member-eq (car val) '(include-book
                                                                 defpkg)))

; Include-book forms are not exported to ML.  See the comment about
; include-book in ../ISSUES (as of August 19, 2010).

; Defpkg forms are not exported to ML.  Instead, we check that packages are OK
; using the pkg-check.txt mechanism discussed in ../tests/README.

                                     acc)
                                    (t (cons val acc)))
                              state))))))))

(defun set-cbd-fn-state (str state)
  (mv-let (erp val state)
          (set-cbd-fn str state)
          (declare (ignore val))
          (prog2$ (and erp
                       (er hard 'set-cbd-fn-state
                           "Unable to set cbd with string ~x0."
                           str))
                  state)))

(defun a2ml-read-eval-up-to-in-package (ch file dir ctx acc state)
  (state-global-let*
   ((connected-book-directory
     (or dir
; The code below was adapted from remove-after-last-directory-separator.
         (let* ((file-rev (reverse file))
                (posn (position *directory-separator* file-rev)))
           (if posn
               (subseq file 0 (- (length file) posn))
             (f-get-global 'connected-book-directory state))))
     set-cbd-fn-state))
   (a2ml-read-eval-up-to-in-package1 ch file ctx acc state)))

(defun print-current-package (pkg-form channel state)
  (let ((pkg (if (and (true-listp pkg-form)
                      (eq (car pkg-form) 'in-package)
                      (stringp (cadr pkg-form)))
                 (cadr pkg-form)
               "ACL2")))
    (pprogn (fms "val package =~| implode(map chr ~x0);~|"
                 (list (cons #\0 (s2conses pkg (length pkg) nil)))
                 channel state nil))))

(defun acl2ml-write (lst pkg-form channel state)
  (state-global-let*
   ((write-for-read t)
    (current-package "ACL2" set-current-package-state)
    (print-case :downcase set-print-case))
   (pprogn (princ$ "open HolKernel Parse boolLib bossLib intSyntax pairSyntax listSyntax stringLib numLib sexp;"
                   channel state)
           (newline channel state)
           (print-current-package pkg-form channel state)
           (newline channel state)
           (princ$ "val events = [" channel state)
           (newline channel state)
           (let ((state (pprint-objects-to-ml lst "," channel state)))
             (pprogn (princ$ "];" channel state)
                     (newline channel state)
                     (close-output-channel channel state)
                     (value :invisible))))))

(defun a2ml-fn (infile outfile dir state)
  (declare (xargs :guard (and (stringp infile)
                              (stringp outfile))
                  :stobjs state))
  (state-global-let*
   ((current-package "ACL2" set-current-package-state))
   (let ((ctx 'a2ml))
     (er-let* ((ch (open-input-object-file infile ctx state))
               (lst1 (a2ml-read-eval-up-to-in-package ch infile dir ctx nil
                                                      state))
               (lst2 (read-object-file1 ch state (cdr lst1))))
       (let ((state (close-input-channel ch state)))
         (mv-let
          (channel state)
          (open-output-channel outfile :character state)
          (if (null channel)
              (er soft ctx
                  "Unable to open file ~s0 for :character output."
                  outfile)
            (mv-let
             (col state)
             (fmt1 "Writing ml file ~x0.~%" (list (cons #\0 outfile))
                   0 (standard-co state) state nil)
             (declare (ignore col))
             (acl2ml-write lst2 (car lst1) channel state)))))))))

(defun a2ml-filename (file)

; Convert hyphen (-) to underscore (_), but only for the filename part of the
; file, not the directory name.

  (let ((pos (search *directory-separator-string* file :from-end t)))
    (cond (pos (concatenate 'string
                            (subseq file 0 (1+ pos))
                            (substitute
                             #\_ #\-
                             (subseq file (1+ pos) (length file)))))
          (t (substitute #\_ #\- file)))))

(defmacro a2ml (infile outfile &optional infile-dir)

; We assume that infile consists of essential events from a book: first the
; portcullis commands, then the book proper.  Thus, the ambient package should
; be bound to "ACL2" before reading infile.

  (declare (xargs :guard (and (stringp infile)
                              (stringp outfile))))
  (let ((outfile (a2ml-filename outfile)))
    `(a2ml-fn ,infile ,outfile ,infile-dir state)))
