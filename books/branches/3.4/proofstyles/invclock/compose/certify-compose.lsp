#|

 certify-compose.lsp
 ~~~~~~~~~~~~~~~~~~~~

In this set of books we justify that clock functions can be composed. This
follows the traditional argument for composition of clock functions over run.

|#

(set-inhibit-output-lst '(proof-tree prove))
(ubt! 1)

(certify-book "compose-c-c-total")
(u)

(certify-book "compose-c-c-partial")
(u)

(set-inhibit-output-lst '(proof-tree))
