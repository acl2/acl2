(in-package "CPP")

;; Standalone lambda parsing branch, not in mutual recursion.
(define parse-cpp-primary-lambda ((tok-span spanp) (parstate parstatep))
  :returns (mv erp
               (expr cpp-expr-p)
               (span spanp)
               (new-parstate parstatep :hyp (parstatep parstate)))
  (b* (;; tok? = '[' was consumed — put it back for parse-cpp-capture-list
       (parstate (unread-token parstate))
       ;; Parse captures '[' ... ']'
       ((erp captures & parstate) (parse-cpp-capture-list-for-lambda parstate))
       ;; Parse parameter list '(' params ')'
       ((erp params & parstate) (parse-cpp-param-list parstate))
       ;; Record parsize before consuming '{'
       (psize-lambda (parsize parstate))
       ;; Read '{'
       ((erp lbrace? lbrace-span parstate) (read-token parstate))
       ((unless (token-punctuatorp lbrace? "{"))
        (reterr-msg :where (span->start lbrace-span)
                    :expected "'{' to begin lambda body"
                    :found lbrace?
                    :extra nil))
       ;; Strict parsize decrease after consuming '{'
       ((unless (mbt (< (parsize parstate) psize-lambda)))
        (reterr :impossible))
       ;; Parse body items (until '}')
       ((erp body & parstate) (parse-cpp-block-item-list-body parstate))
       ;; Read '}'
       ((erp rbrace? rbrace-span parstate) (read-token parstate))
       ((unless (token-punctuatorp rbrace? "}"))
        (reterr-msg :where (span->start rbrace-span)
                    :expected "'}' to close lambda body"
                    :found rbrace?
                    :extra nil))
       (span (make-span :start (span->start tok-span)
                        :end   (span->end rbrace-span))))
    (retok (make-cpp-expr-lambda
            :captures captures
            :params   params
            :body     body)
           span parstate)))