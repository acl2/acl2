(in-package "ACL2S-INTERFACE-EXTRAS")

#|

 The response from a call to itest? inside of acl2s-query should be of the form:
 (t nil) if an error occurred during itest? execution
         (i.e. trying to test something containing an undefined function)
 or
 (nil (cts-found? itest?-res)), where

 1. cts-found? is t if counterexamples were found and nil otherwise.

 2. if cts-found? is nil (no counterexamples) and itest?-fn proved
 the conjecture, then itest?-res is (nil nil wts), where wts is a
 list witnesses found (could be nil). A witness is an assignment of
 values to the variables appearing in the conjecture, which satisfies
 the hypotheses and the conclusion of the conjecture.

 3. if cts-found? is nil (no counterexamples) and itest?-fn did not
 prove the conjecture, then itest?-res is (:? nil wts), where wts is
 a list witnesses found (could be nil). 

 4. if cts-found? is t, then itest?-res is of the form
 (:falsifiable cts wts), where cts is a list of counterexamples and
 wts is a list of witnesses. A counterexample is an assignment of
 values to the variables appearing in the conjecture, which falsifies
 the conjecture.

 See itest-ithm.lisp, which also includes examples.  Keep the comments
 in the two files in sync.

|#

(defun itest?-query-res-ok? (res)
  (and (consp res)
       (= (length res) 2)
       (consp (second res))
       (= (length (second res)) 2)
       (consp (second (second res)))
       (= (length (second (second res))) 3)
       (booleanp (car (second res)))
       (true-listp (second (second (second res))))
       (true-listp (third (second (second res))))))

;; Returns a list where:
;; the first element indicates whether any counterexamples were found
;; the second element contains the counterexamples (which are just lists of variable assignments)
;; This will error if either the internal acl2s-query returns an unexpected response, or the query itself
;; errors out.
(defun itest?-query (q &key (num-counterexamples nil) (quiet t) (prover-step-limit (get-prover-step-limit)))
  "Attempts to find counterexamples to the given ACL2 statement.
Returns a list where:
- the first element indicates whether any counterexamples were found
- the second element contains the counterexamples (which are just lists of variable assignments)
This will error if either the internal acl2s-query returns an unexpected response, or the query itself
errors out."
  (when num-counterexamples
      (acl2s-event `(acl2s::acl2s-defaults :set acl2s::num-counterexamples ,num-counterexamples) :quiet t)
      (acl2s-event `(acl2s::acl2s-defaults :set acl2s::num-print-counterexamples ,num-counterexamples) :quiet t))
  (let* ((query `(acl2s::itest? ,q))
	 (res (acl2s-query query :quiet quiet :prover-step-limit prover-step-limit)))
    (cond ((acl2s-query-error? res)
	   (error 'acl2s-interface-error :query query
		  :desc "Error occurred running itest? query"
		  :err res))
	  ((not (itest?-query-res-ok? res))
	   (error 'unexpected-response-error :query query
		  :desc "Error occurred running itest? query"
		  :res res))
	  (t (second res))))) ;; the list (cts-found? itest?-res), see above
