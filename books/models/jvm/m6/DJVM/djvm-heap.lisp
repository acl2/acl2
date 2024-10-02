(in-package "DJVM")
(acl2::set-verify-guards-eagerness 2)
;;(include-book "../M6-DJVM-shared/jvm-heap")
(include-book "../DJVM/djvm-type-value")
(include-book "../DJVM/djvm-obj")
(include-book "../DJVM/consistent-state")


;; (defun deref2 (ref hp)
;;   (declare (xargs :guard (and (wff-Heap hp)
;;                               (Valid-REFp ref hp))))
;;   ;; never deref2 a non pointer. 
;;   ;; ensure our owm implementation is right. 
              
;;   (binding (rREF ref) hp))
;;
;; appeared in djvm-type-value.lisp

;; (defun wff-heap-strong (hp)
;;   (and (wff-heap hp)
;;        (if (not (consp hp)) t  
;;          (and (wff-obj-strong (cdar hp))
;;               (wff-heap-strong (cdr hp))))))


(defun deref2-init (v hp-init)
  (declare (xargs :guard (and (wff-Refp v)
                              (wff-heap-init-map-strong hp-init)
                              (bound? (rREF v) hp-init))))
                                                            
  (binding (rREF v) hp-init))
