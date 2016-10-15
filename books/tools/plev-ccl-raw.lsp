(in-package "ACL2")


#-Clozure
(defun plev-info ()
  (format t "Sorry, (plev-info) is only implemented on CCL.")
  nil)

#+Clozure
(defn plev-info ()
  (loop for trip in
        (list (list '*package* :none *package*)
              (list 'lisp-variable 'arg-to-plev 'current-value)
              (list '*print-length* :length *print-length*)
              (list '*print-level* :level *print-level*)
              (list '*print-circle* :circle *print-circle*)
              (list '*print-lines* :lines *print-lines*)
              (list '*print-pretty* :pretty *print-pretty*)
              (list '*print-readably* :readably *print-readably*)
              (list 'ccl::*backtrace-print-length* :length
                    ccl::*backtrace-print-length*)
              (list 'ccl::*backtrace-print-level* :level
                    ccl::*backtrace-print-level*)
              (list 'ccl::*trace-print-length* :length
                    ccl::*trace-print-length*)
              (list 'ccl::*trace-print-level* :level
                    ccl::*trace-print-level*)
              (list 'ccl::*error-print-circle* :circle
                    ccl::*error-print-circle*)
              (list 'ccl::*error-print-length* :length
                    ccl::*error-print-length*)
              (list 'ccl::*error-print-level* :level
                    ccl::*error-print-level*)
              (list '*print-array*  :none *print-array*)
              (list '*print-base*  :none *print-base*)
              (list '*print-radix*  :none *print-radix*)
              (list '*print-case*  :none *print-case*)
              (list '*print-escape*  :none *print-escape*)
              (list '*print-miser-width*  :none *print-miser-width*)
              (list '*print-right-margin*  :none *print-right-margin*)
              (list '*read-base*  :none *read-base*)
              (list '*read-default-float-format*  :none
                    *read-default-float-format*)
              (list '*read-eval* :none *read-eval*)
              (list '*read-suppress* :none *read-suppress*)
              (list 'ccl::*print-abbreviate-quote* :none
                    ccl::*print-abbreviate-quote*)
              (list 'ccl::*print-structure* :none
                    ccl::*print-structure*)
              (list 'ccl::*print-simple-vector* :none
                    ccl::*print-simple-vector*)
              (list 'ccl::*print-simple-bit-vector* :none
                    ccl::*print-simple-vector*)
              (list 'ccl::*print-string-length* :none
                    ccl::*print-string-length*)
              )
        do
        (format t "~%~s~30t~s~50t~s" (car trip) (cadr trip) (caddr trip)))
  (format t "~%")
  nil)


(defn plev-fn (length level lines circle pretty readably state)

; Redefined here to deal with Clozure related things that the ACL2
; plev-fn cannot access.

  (setq *print-length* length)

  (setq *print-level* level)

  (setq *print-circle* circle)

  (setq *print-lines* lines)

  (setq *print-pretty* pretty)

  (setq *print-readably* readably)

  #+Clozure
  (setq ccl::*print-array* t)

  #+Clozure
  (setq ccl::*backtrace-print-level* level)

  #+Clozure
  (setq ccl::*backtrace-print-length* length)

  #+Clozure
  (setq ccl::*trace-print-level* level)

  #+Clozure
  (setq ccl::*trace-print-length* length)

  #+Clozure
  (setq ccl::*error-print-circle* circle)

  #+Clozure
  (setq ccl::*error-print-level* level)

  #+Clozure
  (setq ccl::*error-print-length* length)

  #+Clozure
  (setq ccl::*print-string-length* (and (integerp length)
                                        ;; Jared increased this to 3000 because
                                        ;; 300 is way too small.
                                        (max length 3000)))

  #+Clozure
  (setq ccl::*print-simple-vector* (and (integerp length)
                                        (max length 300)))

  #+Clozure
  (setq ccl::*print-simple-bit-vector* (and (integerp length)
                                                    (max length 300)))

  #+Clozure
  (setq ccl::*print-abbreviate-quote* t)

  #+Clozure
  (setq ccl::*print-structure* t)

  (let* ((old-tuple (abbrev-evisc-tuple state))
         (new-tuple (list (car old-tuple) level length
                          (cadddr old-tuple))))
    (mv-let (flg val state)
      (set-evisc-tuple new-tuple
                       :iprint t
                       :sites :all)
      (declare (ignore val))
      (mv flg
          (list :length length
                :level level
                :lines lines
                :circle circle
                :readably readably
                :pretty pretty)
          state))))
