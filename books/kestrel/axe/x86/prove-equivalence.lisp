; Proving equivalence of two x86 binary functions.
;
; Copyright (C) 2024-2025 Kestrel Institute
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
(defund prove-functions-equivalent-fn (executable1
                                      target1
                                      inputs1
                                      output1
                                      executable2
                                      target2
                                      inputs2
                                      output2
                                      extra-rules ; a form to be evaluated
                                      count-hits
                                      print)
  (declare (xargs :guard (and (stringp executable1)
                              (stringp target1)
                              (names-and-typesp inputs1)
                              ;; (output-indicatorp output1)
                              (stringp executable2)
                              (stringp target2)
                              (names-and-typesp inputs2)
                              ;; (output-indicatorp output2)
                              (or (eq :auto count-hits) (acl2::count-hits-argp count-hits))
                              (or (eq :auto count-hits) (acl2::print-levelp print)))))
  (b* (((when (and (equal executable1 executable2)
                   (equal target1 target2)
                   (equal output1 output2)))
        (er hard? 'prove-functions-equivalent-fn "The two functions and executables (and the outputs of interest) are the same."))
       (name1 (acl2::pack-in-package "X" (acl2::string-upcase-gen executable1) "." (acl2::string-upcase-gen target1)))
       (name2 (acl2::pack-in-package "X" (acl2::string-upcase-gen executable2) "." (acl2::string-upcase-gen target2)))
       ((when (eq name1 name2))
        (er hard? 'prove-functions-equivalent-fn "Name clash on ~x0." name1))
       (params1 (strip-cars inputs1))
       (params2 (strip-cars inputs2))
       )
    `(progn
       ;; Lift the first function:
       (def-unrolled ,name1 ,executable1 ; no replacement of register with fresh vars (for now), so that the functions each just take a single param, x86
         :target ,target1
         :inputs ,inputs1
         :output ,output1
         ;; For the :auto values, we insert nothing into the calls of
         ;; def-unrolled, thus arranging to get whatever that tool uses by
         ;; default for those options:
         ,@(if (eq :auto count-hits) nil `(:count-hits ,count-hits))
         ,@(if (eq :auto print) nil `(:print ,print)))
       ;; Lift the second function:
       (def-unrolled ,name2 ,executable2
         :target ,target2
         :inputs ,inputs2
         :output ,output2
         ,@(if (eq :auto count-hits) nil `(:count-hits ,count-hits))
         ,@(if (eq :auto print) nil `(:print ,print)))
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

(defmacrodoc prove-functions-equivalent (executable1
                                         target1
                                         inputs1
                                         output1
                                         executable2
                                         target2
                                         inputs2
                                         output2
                                         &key
                                         (extra-rules 'nil)
                                         (count-hits ':auto)
                                         (print ':auto))
  (prove-functions-equivalent-fn executable1
                                 target1
                                 inputs1
                                 output1
                                 executable2
                                 target2
                                 inputs2
                                 output2
                                 extra-rules
                                 count-hits
                                 print)
  :parents (acl2::axe-x86 acl2::axe-lifters)
  :short "A tool to prove two x86 binary functions equivalent."
  :description "This runs @(tsee def-unrolled) twice, once for each executable, and then tries to prove the two resulting lifted computations equal using rewriting and SMT solving."
  :args ((executable1 "The first executable.  Usually a string (a filename).")
         (target1 "The target to lift in the first executable.  See the @(':target') option of @(tsee def-unrolled).")
         (inputs1 "Information about the inputs of the first executable.  See the @(':inputs') option of @(tsee def-unrolled).  Corresponding inputs should have the same names in the @(':inputs2') below.")
         (output1 "Which output to extract from the first executable.  See the @(':output') option of @(tsee def-unrolled).")
         (executable2 "The second executable.  Usually a string (a filename).")
         (target2 "The target to lift in the second executable.  See the @(':target') option of @(tsee def-unrolled).")
         (inputs2 "Information about the inputs of the second executable.  See the @(':inputs') option of @(tsee def-unrolled).  Corresponding inputs should have the same names in the @(':inputs1') above.")
         (output2 "Which output to extract from the second executable.  See the @(':output') option of @(tsee def-unrolled).")
         (extra-rules "Extra rules to use during lifting.")
         (count-hits "Whether to count rewrite rule hits.")
         (print "Verbosity level.") ; todo values
         ))
