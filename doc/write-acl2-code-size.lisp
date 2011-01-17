(in-package "ACL2")

; We compute information below to help in the reporting of ACL2 code size.

; We assume that the commands in file create-acl2-code-size have already been
; run that create the infile argument for write-acl2-code-size, which in this
; case is acl2-wc.txt.  That file records output from the wc (Linux) command.
; Why not just use our Lisp approach for everything, instead of only for
; counting lines and characters in :doc strings as we do below?  We could, by
; first reading each source file into a string (say, by reading a character and
; then writing it with princ$ into a channel to a string, finally calling
; get-output-stream-string$).  But we started with the wc command, so we simply
; proceeded by taking advantage of that.  If it becomes critical somehow to do
; this task entirely within ACL2, say because of problems with grep, then we
; may reconsider.

(program)
(set-state-ok t)

;;; We have considered using fixnums.  According to the Essay on Fixnum
;;; Declarations, only CLISP and Lispworks have bounds close to our current
;;; total size of about 10.6MB.  However, even GCL seems to handle this
;;; easily, without fixnum declarations.

(defabbrev inc-for-char (c count)
  (cond ((eql c #\") (+ 2 count))
        (t (1+ count))))

(defun doc-sizes1 (str name i max nlp
                       lines-code chars-code lines-comm chars-comm
                       lines-blank chars-blank lines-total chars-total)
  
; Nlp is, as the name suggests, related to newlines.  But really, it represents
; the following state of our accumulation.  When we hit a newline, nlp becomes
; 1, and it increments for each succeeding space.  Thus, a positive integer
; value of newline, k, is the number of characters since the most recent
; newline (inclusive), and indicates that we have seen only spaces since that
; newline.  (We do not like tabs in our sources, so if we see a tab we cause an
; error.)  Once we have hit a non-whitespace character after a newline, we set
; nlp to 'comm if that character is #\;, else to 'code.

; We compute lines-total and chars-total simplistically, without considering
; nlp but instead just accumulating immediately.  This way we can check totals
; against the parts at the end if we like, to gain extra confidence.

  (cond ((int= i max)
         (cond ((integerp nlp)

; If nlp is an integer then the final " would cause the last line of the string
; to be counted as code by our use of wc.  So we should count it as code here.

                (mv (1+ lines-code) (+ nlp chars-code)
                    lines-comm chars-comm
                    lines-blank chars-blank
                    lines-total chars-total))
               (t
                (mv lines-code chars-code
                    lines-comm chars-comm
                    lines-blank chars-blank
                    lines-total chars-total))))
        (t (let* ((c (char str i))
                  (chars-total (inc-for-char c chars-total)))
             (cond
              ((eql c #\Newline)
               (let ((lines-total (1+ lines-total)))
                 (cond ((integerp nlp)
                        (doc-sizes1 str name (1+ i) max 1
                                    lines-code chars-code
                                    lines-comm chars-comm
                                    (1+ lines-blank) (+ nlp chars-blank)
                                    lines-total chars-total))
                       (t
                        (doc-sizes1 str name (1+ i) max 1
                                    lines-code chars-code
                                    lines-comm chars-comm
                                    lines-blank chars-blank
                                    lines-total chars-total)))))
              ((eql c #\Tab)
               (mv (er hard 'doc-sizes1
                       "Found Tab at position ~x0 of the doc string for ~x1."
                       i name)
                   0 0 0 0 0 0 0)) ; don't-care
              ((eq nlp 'comm)
               (doc-sizes1 str name (1+ i) max 'comm
                           lines-code chars-code
                           lines-comm (inc-for-char c chars-comm)
                           lines-blank chars-blank
                           lines-total chars-total))
              ((eq nlp 'code)
               (doc-sizes1 str name (1+ i) max 'code
                           lines-code (inc-for-char c chars-code)
                           lines-comm chars-comm
                           lines-blank chars-blank
                           lines-total chars-total))
              (t
               (assert$
                (integerp nlp)
                (cond ((eql c #\Space)
                       (doc-sizes1 str name (1+ i) max (1+ nlp)
                                   lines-code chars-code
                                   lines-comm chars-comm
                                   lines-blank chars-blank
                                   lines-total chars-total))
                      ((eql c #\;)
                       (doc-sizes1 str name (1+ i) max 'comm
                                   lines-code chars-code
                                   (1+ lines-comm) (+ 1 nlp chars-comm)
                                   lines-blank chars-blank
                                   lines-total chars-total))
                      (t
                       (doc-sizes1 str name (1+ i) max 'code
                                   (1+ lines-code)
                                   (inc-for-char c (+ nlp chars-code))
                                   lines-comm chars-comm
                                   lines-blank chars-blank
                                   lines-total chars-total))))))))))

(defun doc-sizes (doc-alist lines-code chars-code
                            lines-comm chars-comm
                            lines-blank chars-blank
                            lines-total chars-total)

; We accumulate into lines-total and chars-total the number of lines and
; characters in the :doc strings in doc-alist, as they would appear in the
; source files.  Thus, since the " character is written in a :doc string as \",
; a it contributes 2 to chars-total.

; We also accumulate into lines-code through chars-blank the counts that :doc
; strings contribute to the output of wc on the source code, so that we can
; subtract away the effect of :doc strings when counting source code.  If we
; think of a deflabel, which is concluded by a :doc string, or a defun, which
; is not, we arrive at the same conclusion: we should add 1 to the number of
; newlines in the code and total line counts for the string.  Consider for
; example:

; (deflabel foo
;   "..
;    ..")

; Without the :doc string, this would have been written as:

; (deflabel foo)

; So the :doc string is responsible for two more newlines of code and two more
; newlines total.  Similarly for defun:

; (defun foo (x)
;   "..
;    .."
;  ...)

; Wart: We should perhaps subtract the entirety of a defdoc, not just its
; string; perhaps similarly for deflabel.  But maybe it's not unreasonable to
; consider those events as infrastructure for managing documentation.

  (cond ((endp doc-alist)
         (prog2$
          (cond ((not (equal lines-total (+ lines-code lines-comm lines-blank)))
                 (er hard 'doc-sizes
                     "Something is wrong with the doc-sizes algorithm: ~
                     expected ~x0 but got ~x1."
                     '(equal lines-total
                             (+ lines-code lines-comm lines-blank))
                     `(not (equal ,lines-total
                                  (+ ,lines-code ,lines-comm ,lines-blank)))))
                ((not (equal chars-total (+ chars-code chars-comm chars-blank)))
                 (er hard 'doc-sizes
                     "Something is wrong with the doc-sizes algorithm: ~
                     expected ~x0 but got ~x1."
                     '(equal chars-total
                             (+ chars-code chars-comm chars-blank))
                     `(not (equal ,chars-total
                                  (+ ,chars-code ,chars-comm ,chars-blank)))))
                (t nil))
          (mv lines-code chars-code lines-comm chars-comm
              lines-blank chars-blank lines-total chars-total)))
        (t (mv-let (lines-code chars-code lines-comm chars-comm
                               lines-blank chars-blank lines-total chars-total)
                   (let ((str (nth 3 (car doc-alist)))
                         (name (nth 0 (car doc-alist))))
                     (doc-sizes1 str name 0 (length str) 'code
                                 (1+ lines-code) chars-code
                                 lines-comm chars-comm
                                 lines-blank chars-blank
                                 (1+ lines-total) chars-total))
                   (doc-sizes (cdr doc-alist)
                              lines-code chars-code
                              lines-comm chars-comm
                              lines-blank chars-blank
                              lines-total chars-total)))))

(defun write-acl2-code-size-fn (infile outfile ctx state)
  (mv-let
   (channel state)
   (open-input-channel infile :object state)
   (cond
    ((null channel)
     (pprogn (warning$ ctx nil
                       "Unable to open file ~x0 for input.  Skipping ~
                        computation of code size."
                       infile)
             (value nil)))
    (t
     (er-let* ((lines-code  (read-object channel state))
               (chars-code  (read-object channel state))
               (lines-comm  (read-object channel state))
               (chars-comm  (read-object channel state))
               (lines-blank (read-object channel state))
               (chars-blank (read-object channel state))
               (lines-total (read-object channel state))
               (chars-total (read-object channel state)))
       (let ((state (close-input-channel channel state)))
         (mv-let
          (ch state)
          (open-output-channel outfile :character state)
          (cond
           ((null ch)
            (er soft ctx
                "Unable to open file ~x0 for output."
                outfile))
           (t (mv-let
               (lines-doc-code chars-doc-code
                               lines-doc-comm chars-doc-comm
                               lines-doc-blank chars-doc-blank
                               lines-doc-total chars-doc-total)
               (doc-sizes (global-val 'documentation-alist (w state))
                          0 0 0 0 0 0 0 0)
               (pprogn
                (fms "CODE:~| ~c0 lines, ~c1 characters"
                     (list (cons #\0 (cons (- lines-code lines-doc-code)
                                           7))
                           (cons #\1 (cons (- chars-code chars-doc-code)
                                           9)))
                     ch state nil)
                (fms "COMMENTS:~| ~c0 lines, ~c1 characters"
                     (list (cons #\0 (cons (- lines-comm lines-doc-comm)
                                           7))
                           (cons #\1 (cons (- chars-comm chars-doc-comm)
                                           9)))
                     ch state nil)
                (fms "BLANK (excluding documentation):~| ~c0 lines, ~c1 ~
                      characters"
                     (list (cons #\0 (cons (- lines-blank lines-doc-blank)
                                           7))
                           (cons #\1 (cons (- chars-blank chars-doc-blank)
                                           9)))
                     ch state nil)
                (fms "DOCUMENTATION:~| ~c0 lines, ~c1 characters"
                     (list (cons #\0 (cons lines-doc-total 7))
                           (cons #\1 (cons chars-doc-total 9)))
                     ch state nil)
                (fms "TOTAL:~| ~c0 lines, ~c1 characters"
                     (list (cons #\0 (cons lines-total 7))
                           (cons #\1 (cons chars-total 9)))
                     ch state nil)
                (newline ch state)
                (close-output-channel ch state)
                (value t))))))))))))

(defmacro write-acl2-code-size (infile outfile)

; See comments at the top of the file.  This macro is called in shell script
; create-acl2-code-size.

  `(time$ (write-acl2-code-size-fn ,infile ,outfile 'write-acl2-code-size
                                   state)
          :msg "~%The execution of WRITE-ACL2-CODE-SIZE took ~st seconds of ~
                real time and ~sc seconds of run time (cpu time), and ~
                allocated ~sa bytes.~%"))
