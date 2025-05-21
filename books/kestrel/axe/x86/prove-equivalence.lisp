; Proving equivalence of two x86 binary functions.
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "unroll-x86-code") ; has skip-proofs
(include-book "../tactic-prover")
(include-book "kestrel/strings-light/upcase" :dir :system)
(include-book "../basic-rules") ; for equal-same
(local (include-book "kestrel/utilities/doublet-listp" :dir :system))

;; todo: add support for extra-proof-rules, and extra-lifting-rules?
;; todo: add support for print argument
;; todo: consider allowing the second inputs and outputs to be elided.  or maybe make all the input and output things keyword args (:inputs, :inputs1, :inputs2, etc.)
(defun prove-functions-equivalent-fn (executable1
                                      function1
                                      inputs1
                                      output1
                                      executable2
                                      function2
                                      inputs2
                                      output2
                                      extra-rules ; a form to be evaluated
                                      )
  (declare (xargs :guard (and (stringp executable1)
                              (stringp function1)
                              (names-and-typesp inputs1)
                              ;; (output-indicatorp output1)
                              (stringp executable2)
                              (stringp function2)
                              (names-and-typesp inputs2)
                              ;; (output-indicatorp output2)
                              )))
  (b* (((when (and (equal executable1 executable2)
                   (equal function1 function2)
                   (equal output1 output2)))
        (er hard? 'prove-functions-equivalent-fn "The two functions and executables (and the outputs of interest) are the same."))
       (name1 (acl2::pack-in-package "X" (acl2::string-upcase-gen executable1) "." (acl2::string-upcase-gen function1)))
       (name2 (acl2::pack-in-package "X" (acl2::string-upcase-gen executable2) "." (acl2::string-upcase-gen function2)))
       ((when (eq name1 name2))
        (er hard? 'prove-functions-equivalent-fn "Name clash on ~x0." name1))
       (params1 (strip-cars inputs1))
       (params2 (strip-cars inputs2))
       )
    `(progn
       ;; Lift the first function:
       (def-unrolled ,name1 ,executable1 ; no replacement of register with fresh vars (for now), so that the functions each just take a single param, x86
         :target ,function1
         :inputs ,inputs1
         :output ,output1)
       ;; Lift the second function:
       (def-unrolled ,name2 ,executable2
         :target ,function2
         :inputs ,inputs2
         :output ,output2)
       ;; TODO: Check for mismatch in the inputs
       ;; TODO: Check for output indicators that mean the proof will fail (e.g., checking a scalar against a state)
       ;; Prove that the 2 lifted representations are equivalent:
       ;; TODO: What we just get the DAGs, instead of their corresponding functions?  More generally, we could have this avoid submitting any events.
       (prove-equal-with-tactics '(,name1 ,@params1) ; todo: check the arities of the functions (will need to use make-event)
                                 '(,name2 ,@params2)
                                 :tactics '(:rewrite :stp)
                                 ;; todo: automatically add some rules here
                                 :rules (append '(,name1 ,name2)
                                                ;; in case there are embedded dags:
                                                '(acl2::lookup-equal-of-acons-same
                                                  acl2::lookup-equal-of-acons-diff
                                                  acl2::equal-same ; todo: what else?!
                                                  )
                                                ,extra-rules)))))

(defmacro prove-functions-equivalent (executable1
                                      function1
                                      inputs1
                                      output1
                                      executable2
                                      function2
                                      inputs2
                                      output2
                                      &key
                                      (extra-rules 'nil))
  (prove-functions-equivalent-fn executable1
                                 function1
                                 inputs1
                                 output1
                                 executable2
                                 function2
                                 inputs2
                                 output2
                                 extra-rules))
