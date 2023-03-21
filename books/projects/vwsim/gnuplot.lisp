
; gnuplot.lisp                                    Vivek & Warren

; Simple interface to use ``gnuplot''.

(in-package "ACL2")

; (defttag :quicklisp)
; (defttag :quicklisp.shellpool)
; (defttag :tshell)

; If the trust tags above are defined, then parentheses are required around
; the "ttags arguments.

; (certify-book "gnuplot" ? t :ttags ((:quicklisp) (:quicklisp.shellpool) (:tshell)))

; However, if the trust tags above are note defined, then this will work:

; (certify-book "gnuplot" ? t :ttags (:quicklisp :quicklisp.shellpool :tshell))


;; Includes B* as well -- but from where?
(include-book "centaur/misc/tshell" :dir :system)

;; Launches a shell instance. If "gnuplot.lisp" is used with
;; "include-book", then the following form needs to be evaluated after
;; the include-book. If used with "ld", nothing further needs to be
;; done.
(value-triple (tshell-ensure) :on-skip-proofs t)

(defun concat-with-space (l)
  (declare (xargs :guard (string-listp l)))
  (if (atom l)
      ""
    (let ((str (car l)))
      (if (atom (cdr l))
          str
        (concatenate 'string
                     str
                     " "
                     (concat-with-space (cdr l)))))))

(defthm stringp-concat-with-space
  (implies (string-listp l)
           (stringp (concat-with-space l))))

(defun standard-char-stringp (str)
  (declare (xargs :guard (stringp str)))
  (standard-char-listp (coerce str 'list)))

(defun standard-char-string-listp (lst-of-str)
  (declare (xargs :guard (string-listp lst-of-str)))
  (if (atom lst-of-str)
      (null lst-of-str)
    (let ((str (car lst-of-str))
          (rst (cdr lst-of-str)))
      (and (standard-char-stringp str)
           (standard-char-string-listp rst)))))

(defthm standard-char-listp-of-strings
  (implies (standard-char-string-listp vars)
           (standard-char-listp (coerce (concat-with-space vars)
                                        'list)))
  :hints
  (("Goal" :in-theory (enable standard-char-listp))))

(defun run-gnuplot (csv-file vars)
  (declare (xargs :guard (and (stringp csv-file)
                              (string-listp vars)
                              (standard-char-string-listp vars))))
  ;; csv-file is a string, which is the path to the CSV file
  ;; vars is a list of strings of the requested variables to plot.
  (declare (ignorable vars))
  (b* ((plot-cmd "gnuplot -e ")
       ;; Create sh command to run JoSIM
       (sh-command
        (concatenate 'string
                     plot-cmd
                     "\"filename=\'"
                     csv-file
                     "\'; "
                     "vars = \'"
                     ;; We expect all column headers in the CSV file
                     ;; to be in uppercase
                     (string-upcase (concat-with-space vars))
                     "\'\""
                     " csv-plot.gnuplot"))
       ;; Run gnuplot in background so we get the ACL2 loop back. This
       ;; also lets us create multiple plots by running "run-gnuplot"
       ;; multiple times.
       (- (tshell-run-background sh-command)))
    sh-command))

#||

;; alternative approach using syscall:

;; NOTE: if you use this approach, you will not get control of the
;; loop back

(defttag t)

(defun run-gnuplot (csv-file vars)
  ;; csv-file is a string, which is the path to the CSV file
  ;; vars is a list of string of the requested variables to plot.
  (declare (ignorable vars))
  (b* ((plot-cmd "gnuplot -e ")
       ;; Create sh command to run JoSIM
       (sh-command
        (concatenate 'string
                     plot-cmd
                     "\"filename=\'"
                     csv-file
                     "\'; "
                     "vars = \'"
                     (concat-with-space vars)
                     "\'\""
                     " csv-plot.gnuplot"))
       ;; Run gnuplot
       (- (sys-call "sh" (list "-c" sh-command))))
    nil))

||#
