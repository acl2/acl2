;; TODO: enable CLISP after # https://github.com/cl-plus-ssl/cl-plus-ssl/issues/163 is fixed
(dolist (lisp '("sbcl" "ccl" "abcl"))
  (dolist (openssl '(
                     "openssl-0.9.8zh"
                     "openssl-1.0.0s"
                     "openssl-1.0.2q"
                     "openssl-1.1.0j"
                     "openssl-1.1.1p"
                     "openssl-3.0.4"
                     "libressl-2.2.7"
                     "libressl-2.5.5"
                     "libressl-2.6.5"
                     "libressl-2.8.3"
                     "libressl-3.0.1"
                     "libressl-3.5.3"
                     ))
    (dolist (lib-load-mode '("new" "old"))
      (unless (and (string= lisp "abcl")
                   (string= lib-load-mode "old"))

        ;; TODO: COVERALLS=true for SBCL on the laest version of OpenSSL and the latest LibreSSL
        ;;     after this cl-coveralls issue is fixed: https://github.com/fukamachi/cl-coveralls/issues/14

        ;; TODO: repeat CCL test on the latest OpenSSL with READTABLE_CASE_INVERT=1

        (format t "      - if: always()~%")
        (format t "        run: |~%")
        (format t "           LISP=~A OPENSSL=~A BITS=64 LIB_LOAD_MODE=~A docker-home/cl-plus-ssl/.github/workflows/test.sh~%"
                lisp openssl lib-load-mode)
        ))))

