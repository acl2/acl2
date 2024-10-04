(in-package "DJVM")
(include-book "../../DJVM/consistent-state")
(include-book "../../M6-DJVM-shared/jvm-bytecode")

(defconst *local-index-limit* 256)

(acl2::set-verify-guards-eagerness 2)

;; (defun wff-aload (inst)
;;   (and  (wff-one-arg inst)
;;         (integerp (arg inst))
;;         (<= 0 (arg inst))
;;         (< (arg inst) *local-index-limit*)))
;;;
;;; moved into ALOAD.lisp
;;;

(defthm wff-call-frame-implies-truelistp
  (implies (wff-call-frame frame)
           (true-listp (locals frame)))
  :hints (("Goal" :in-theory (enable wff-call-frame 
                                     locals)))
  :rule-classes :forward-chaining)



(defun valid_local_type (type)
  (or (equal type 'topx)
      (primitive-type? type)
      (equal type 'REF)))
      


;; (defun valid_local_type (type)
;;   (or (equal type 'topx)
;;       (equal type 'INT)    
;; ; BYTE, INT, CHAR, SHORT all appears as INT!! 
;; ; Thu Mar 10 15:31:30 2005 
;;       (equal type 'REF)
;;       (equal type 'FLOAT)  
;;       (equal type 'LONG)
;;       (equal type 'DOUBLE)  ; 
;; ;     (equal type 'RETADDR) ; We do not deal with it.
;; ;     (equal type 'CALLBACK) ; How about this?? Wed May 18 12:28:49 2005 Still
;; ;     need thinking!! 
;;       ))
      
;;
;; this define whether we are allow to read from that location
;;
;; Sat May 21 17:55:45 2005 
(defun valid-local-index (index locals)
  (declare (xargs :measure (len locals)
                  :guard (and (integerp index)
                              (< index (len locals)))
                  :guard-hints  (("Goal" :in-theory (enable category1 tag-of)))))
  (if (not (consp locals)) 
      nil
    (if (< index 0) nil
      (cond ((category1Loc locals)
             (and (valid_local_type (tag-of (car locals)))
                  (or (and (equal index 0)
                           (not (equal (tag-of (car locals)) 'topx)))
                      (valid-local-index (- index 1) (shift1slot locals)))))
            ((category2Loc locals)
             (and (valid_local_type (tag-of (car locals)))
                  (or (and (equal index 0)
                           (not (equal (tag-of (car locals)) 'topx)))
                      (valid-local-index (- index 2) (shift2slot locals)))))))))


;----------------------------------------------------------------------

(defun invalidate-category2-value (index s)
  (declare (xargs :guard (and (integerp index)
                              (current-frame-guard s)
                              (wff-call-frame (current-frame s))
                              (<= -1 index)
                              (< index (- (len (locals (current-frame s))) 1))
                              (or (< index 0)
                                  (wff-tagged-value (local-at index s))))))
  (if (< index 0) s
    (if (equal (type-size (tag-of (local-at index s))) 1) s
      (state-set-local-at index '(topx . topx) s))))

