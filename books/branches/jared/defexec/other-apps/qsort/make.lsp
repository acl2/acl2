#|

  make.lisp
  ~~~~~~~~~

The collection of events below is a proof of an in-situ implementation of
quicksort. All the books should certify in ACL2 V2.6. We inhibit the proof in
the final run, just for the purpose of saving time as ACL2 whizzes past. To see
the proof, simply comment out the line that inhibits the proof. To see that the
proof goes thru, simply type (ld "make.lisp") in an ACL2 logic prompt. Make
sure that all the books specified in this file are actually present as well as
this file, in the current ACL2 book directory.

The final theorem is qsort-is-correct, that says it all. The theorem is in
final-theorem.lisp.

|#


(set-inhibit-output-lst '(proof-tree prove))

:ubt! 1

(certify-book "total-order")
:u

(certify-book "nth-update-nth")
:u

(certify-book "permutations")
:u

(certify-book "programs")
:u

(certify-book "intermediate-program")
:u

(certify-book "spec-properties")
:u

(certify-book "intermediate-to-spec")
:u

(certify-book "first-last")
:u

(certify-book "merge-intermediate")
:u

(certify-book "extraction")
:u

(certify-book "split-qs-properties")
:u

(certify-book "load-extract")
:u

(certify-book "sort-qs-properties")
:u

(certify-book "final-theorem")
:u

(set-inhibit-output-lst '(proof-tree))