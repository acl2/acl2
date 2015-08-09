;------------------------------------------------------------------------------------
;
;  File: consistency.lisp
;  April 2003
;  Authors: Toma Diana and Schmaltz Julien
;  TIMA - VDS, Grenoble, France
;  Functions checking the consistency of hypotheses
;
;------------------------------------------------------------------------------------


(in-package "ACL2")


; we use the expander book
(include-book "../../../../misc/expander")

(set-state-ok t)

(program)


; consistency returns nil in case of errors when calling tool1-fn
; normally returns the list of contradictory constraints of L
; Note that at call, L contains a contradiction

(defun consistency (L Ih i state)
     (if (and (true-listp L)
              (true-listp Ih)
              (integerp i)
              (< 0 i))
         (cond ((endp L) ; last step of the algorithm
		(value Ih)); L empty means that L is the minal set and now Ih = L
               ((< (length L) i) (value nil)) ;error: i out of L range
               ((endp Ih) ; first step(s) of the algorithm (at call Ih is empty)
                 (mv-let (erp val state)
                   (tool1-fn (subseq L 0 i) state nil t nil t t)
                   (if erp
                      (value nil)    ; tool1-fn error case
                      (if (nth 1 val) ; is either a list of consistent constraints or nil
                          (consistency L Ih (+ i 1) state)
          ; if no contradictions in L[0 .. i], proceed with L[0 .. i+1]
	  ; else the added constraint is removed from L and added to Ih
                          (consistency (remove (nth (- i 1) L) L)
                                       (cons (nth (- i 1) L) Ih) 1 state)))))
                (t (mv-let (erp val state)  ; one step of the algorithm
                    (tool1-fn Ih state nil t nil t t)
                    (if erp
                       (value nil)  ; tool1-fn error case
                       (if (nth 1 val)
                           (mv-let (erp1 val1 state)
                              (tool1-fn (append Ih (subseq L 0 i))
                                         state nil t nil t t)
           ; check of the consistency of the union of Ih and L[0 .. i]
                              (if erp1
                                  (value nil)  ; tool1-fn error case
                                  (if (nth 1 val1)
                                      (consistency L Ih (+ i 1) state)
                                      (consistency (remove (nth (- i 1) L) L)
                                                   (cons (nth (- i 1) L) Ih) 1 state))))
                           (value Ih))))))
        (value  nil)))



; check-consistency returns t if l is consistent
; else it calls consistency

(defun check-consistency (l state)
   (if (true-listp l)
       (cond ((endp l) (value  nil))
             (t (mv-let (erp val state)
                 (tool1-fn l state nil t nil t t)
                 (if erp
                    (value nil)  ; tool1-fn error case
                    (if (nth 1 val)
                        (value t) ; l contains no contradictions
                        (consistency l nil 1 state))))))
			; l is not consistent and
                        ; we call consistency to extract the set of contradictory hyps
       (value nil)))

(logic)


