; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc run-script
  :parents (macro-libraries)
  :short "Run a script"
  :long "<p>@('Run-script') is a utility for testing evaluation of the forms in
 a given file, to check that the output is as expected.  The forms need not be
 embedded event forms (see @(see events)), and they need not all evaluate
 successfully; for example, a @(tsee thm) form may produce a failed proof
 attempt.</p>

 <p>General form:</p>

 @({
 (run-script NAME
             :inhibited-summary-types i-s-t  ; default '(time steps)
             :inhibit-output-lst      i-o-l  ; default '(proof-tree)
             :ld-error-action         action ; default ':continue
             )
 })

 <p>where the keyword arguments are evaluated.</p>

 <p>Example form:</p>

 @({
 (run-script \"mini-proveall\")
 })

 <p>In order to call @('(run-script NAME)') (with or without keyword
 arguments), you will need four files corresponding to @('NAME'), as described
 below.  For an example, see the files @('books/demos/mini-proveall-*.*') in
 the @(see community-books); there, @('NAME') is @('mini-proveall').</p>

 <ul>

 <li>@('NAME-input.lsp') &mdash; the file of forms to be evaluated</li>

 <li>@('NAME-book.acl2') &mdash; a file containing the following, where the
 indicated zero or more @(tsee include-book) forms are exactly those that are
 in @('NAME-input.lsp') (note that the form @('(ubu 1)') can perhaps be omitted
 but is needed in some cases, e.g., see
 @('books/projects/paco/books/proveall-book.acl2'))

 @({
 (include-book \"tools/run-script\" :dir :system)
 (run-script \"NAME\") ; optionally add keyword arguments
 (ubu 1)

 ; Help dependency scanner.
 #||
 (depends-on \"NAME-log.txt\")
 (include-book ...)
 (include-book ...)
 ...
 ||#
 })</li>

 <li>@('NAME-book.lisp') &mdash; a small file containing only these two forms:

 @({
 (in-package \"ACL2\")
 (assert-event
  (identical-files-p \"NAME-log.txt\" \"NAME-log.out\"))
 })</li>

 <li>@('NAME-log.txt') &mdash; the expected result from evaluating the forms in
 @('NAME-input.lsp')</li>

 </ul>

 <p>To create @('NAME-log.txt'), initially create it as the empty file (or,
 actually, create any file with that name).  Then run the test, for example
 using @('cert.pl') (see @(see build::cert.pl)) as follows.</p>

 @({
 <PATH_TO_books/build>/cert.pl -j 8 NAME-book
 })

 <p>Now inspect the generated file @('NAME-log.out').  When you are satisfied
 that it is as expected, move it to @('NAME-log.txt').  The @('cert.pl')
 command displayed above should now succeed.</p>

 <p>NOTE: If you fail to create file @('NAME-log.txt'), you will likely see an
 error message of the following form when you run @('cert.pl').</p>

 @({
 make: *** No rule to make target `NAME-log.txt', needed by `NAME-book.cert'.
 })

 <p>The solution is to create the missing file @('NAME-log.txt'), for example
 with the following shell command.</p>

 @({
 touch NAME-log.txt
 })")

(include-book "xdoc/top" :dir :system)

(defun identical-files-p-fn (file1 file2 state)
  (declare (xargs :stobjs state
                  :guard (and (stringp file1)
                              (stringp file2))))
  (let ((str1 (read-file-into-string file1))
        (str2 (read-file-into-string file2))
        (ctx 'identical-files-p))
    (cond
     ((null str1)
      (er hard? ctx
          "File ~x0 is missing or unreadable."
          file1))
     ((null str2)
      (er hard? ctx
          "File ~x0 is missing or unreadable."
          file2))
     ((equal str1 str2)
      t)
     (t
      (er hard? ctx
          "Files ~x0 and ~x1 differ."
          file1 file2)))))

(defmacro identical-files-p (file1 file2)
  `(identical-files-p-fn ,file1 ,file2 state))

(defmacro run-script (name &key
                           (inhibited-summary-types ''(time steps))
                           (inhibit-output-lst ''(proof-tree))
                           (ld-error-action ':continue))

; Input file should be NAME-input.lsp.  Then (run-script NAME) writes the
; standard and proofs output from LD of that input file to NAME-log.out.

  (let ((input-file (concatenate 'string name "-input.lsp"))
        (output-file (concatenate 'string name "-log.out")))
    `(ld '((set-inhibited-summary-types ,inhibited-summary-types)
           (set-inhibit-output-lst ,inhibit-output-lst)
           (assign script-mode t)
           .
           ,input-file)
         :ld-verbose nil ; avoid absolute pathname printed for cbd
         :ld-pre-eval-print t :ld-error-action ,ld-error-action 
         :standard-co ,output-file :proofs-co ,output-file)))
