; Tools to strengthen facts by rewriting
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "rewriter-alt") ; why this rewriter?
(include-book "dag-to-term")

;fixme combine with simplify-fact?  well, this one doesn't make a theorem..
;returns (mv result state)
;fixme use polarities and pass in the strengthen flag - use the new rewriter
(defun strengthen-fact (fact assumptions print rules state)
  (declare (xargs :mode :program :stobjs (state)))
  ;; now calls the new rewriter and passes a rewrite objective
  (rewrite-term fact
                :rewrite-objective nil ;;we want to strengthen
                :rules rules
                ;; :monitor '(bvlt-of-two-less-than-max-when-not-max)
                :print print
                :assumptions assumptions))

;returns (mv erp old-fact new-fact state), or (mv nil nil state) if nothing was strengthened
;facts are moved into acc
;fixme don't stop iterating after a change? keep a change flag?
(defun find-a-fact-to-strengthen (facts-to-strengthen print acc rules state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (endp facts-to-strengthen)
      (mv (erp-nil) nil nil state) ;failed to strengthen anything
    (let ((fact (first facts-to-strengthen)))
      (mv-let (erp result-dag-lst state)
        (strengthen-fact fact (append (rest facts-to-strengthen) acc) print rules state)
        (if erp
            (mv erp nil nil state)
          (let ((result (dag-to-term result-dag-lst))) ;fixme could this ever blow up?
            (if (equal result fact)
                ;;no change, so move fact to acc:
                (find-a-fact-to-strengthen (rest facts-to-strengthen) print (cons fact acc) rules state)
              ;;fact was strengthened:
              (mv (erp-nil) fact result state))))))))

;TODO: compare to improve-invars and simplify-terms-using-each-other-fn
;TODO: handle boolands?
;returns (mv erp new-facts state) where new-facts is a set of facts whose conjunction is equal to the conjunction of facts
;fixme handle contradictions (manifested as a single fact that rewrites to nil)?
(defun strengthen-facts (facts print rules state)
  (declare (xargs :mode :program :stobjs (state)))
  (mv-let (erp old-fact new-fact state)
    (find-a-fact-to-strengthen facts print nil rules state)
    (if erp
        (mv erp nil state)
      (if (not old-fact)
          (mv (erp-nil) facts state)
        (if (equal *t* new-fact)
; if the fact became t, drop it... (fixme would this ever happen if we are trying to strengthen? maybe we are doing more than just strengthening - also eliminating redundancy..)
            (strengthen-facts (remove-equal old-fact facts) print rules state)
          ;; fixme what if the fact gets rewritten to nil?
          (strengthen-facts (cons new-fact (remove-equal old-fact facts)) print rules state))))))
