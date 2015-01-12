

;; Common events (found in ACL2s session modes)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)
(set-well-founded-relation l<)
(make-event ; use ruler-extenders if available
 (if (member-eq 'ruler-extenders-lst
                (getprop 'put-induction-info 'formals nil
                         'current-acl2-world (w state)))
     (value '(set-ruler-extenders :all))
   (value '(value-triple :invisible))))


;; CCG settings

; dont be too verbose
 (set-ccg-print-proofs nil)     
 (set-ccg-inhibit-output-lst
  '(QUERY BASICS PERFORMANCE BUILD/REFINE SIZE-CHANGE))
;remove any time limit on ccg termination proofs
 (set-ccg-time-limit nil)



; Use CCG to do termination proofs.
(set-termination-method :ccg)
