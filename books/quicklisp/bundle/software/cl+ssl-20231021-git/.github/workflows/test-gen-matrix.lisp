;; TODO: enable CLISP after # https://github.com/cl-plus-ssl/cl-plus-ssl/issues/163 is fixed
(flet ((format-test-step (lisp openssl lib-load-mode &optional other-vars)
         (format t "      - run: |~%")
         (format t "           ~@[~A ~]LISP=~A OPENSSL=~A BITS=64 LIB_LOAD_MODE=~A docker-home/cl-plus-ssl/.github/workflows/test.sh~%"
                 other-vars lisp openssl lib-load-mode)
         ;; Is 2 mins enough?
         (format t "        timeout-minutes: 2~%")
         (format t "        if: success() || failure()~%")
         )
       (format-retrying-test-step (lisp openssl lib-load-mode &optional other-vars)
         ;; Note the `<  /dev/null` at the end of the cmd-line.
         ;; This is needed to prevent CCL to hang waiting
         ;; for user input when CCL Kernel Debugger is entered
         ;; upon unhandled exception.
         ;; The standard Guthub Actions `run` step closes the
         ;; stdin of the child shell process automatically.
         ;; But the nick-fields/retry step keeps it open,
         ;; so we need this workaround.
         ;; Reported this as a bug: https://github.com/nick-fields/retry/issues/98
         (let ((cmd-line (format nil "~@[~A ~]LISP=~A OPENSSL=~A BITS=64 LIB_LOAD_MODE=~A docker-home/cl-plus-ssl/.github/workflows/test.sh < /dev/null"
                                 other-vars lisp openssl lib-load-mode)))
           (format t "      - uses: nick-fields/retry@v2.8.2~%")
           (format t "        name: Run with retries ~A~%" cmd-line)
           (format t "        with:~%")
           (format t "          command: |~%")
           (format t "             ~A~%" cmd-line)
           ;; Is 2 mins enough? Usually the first execution, which is the longest
           ;; due to Quicklisp download of dependencies and compilation,
           ;; takes around 55 sec.
           (format t "          timeout_minutes: 2~%")
           (format t "          max_attempts: 3~%")
           ;; don't hide timeouts
           (format t "          retry_on: error~%")
           ;; don't hide error situations other than the known crashes
           (format t "          retry_on_exit_code: 137~%")
           (format t "        if: success() || failure()~%"))))
  (dolist (lib-load-mode '("new" "old"))
    (dolist (openssl '(
                       ;; newest releases
                       "openssl-3.0.4"
                       "openssl-1.1.1p"
                       "libressl-3.5.3"

                       ;; oldest releaes
                       "openssl-0.9.8zh"
                       "libressl-2.2.7"

                       ;; the rest
                       "openssl-1.1.0j"
                       "openssl-1.0.2q"
                       "openssl-1.0.0s"
                       "libressl-3.5.3"
                       "libressl-3.0.1"
                       "libressl-2.8.3"
                       "libressl-2.6.5"
                       "libressl-2.5.5"
                       ))
      (dolist (lisp '("sbcl" "ccl" "abcl"))
        (flet ((format-test-step-for-lisp (openssl lib-load-mode &optional other-vars)
                 (if (string= lisp "ccl")
                     ;; because of https://github.com/Clozure/ccl/issues/85
                     (format-retrying-test-step lisp openssl lib-load-mode other-vars)
                     (format-test-step lisp openssl lib-load-mode other-vars))))
          (unless (and (string= lisp "abcl")
                       (string= lib-load-mode "old"))

            (format-test-step-for-lisp openssl lib-load-mode)
            (when (and (string= openssl "openssl-3.0.4"))
              (format-test-step-for-lisp openssl lib-load-mode "KEEP_FASLS=1"))

            ;; TODO: repeat CCL test on the latest OpenSSL with READTABLE_CASE_INVERT=1

            ;; TODO: COVERALLS=true for SBCL on the laest version of OpenSSL and the latest LibreSSL
            ;;     after this cl-coveralls issue is fixed: https://github.com/fukamachi/cl-coveralls/issues/14

            ))))))

