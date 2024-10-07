(in-package "ACL2")
(include-book "bcv-model")
(include-book "bcv-simple-model")
(include-book "generic")


(defthm ordered-less-than-first-then-not-member
  (implies (and (ordered l)
                (< pc (car l)))
           (not (member pc l))))


(encapsulate () 
  (local (include-book "bcv-if-verified-then-pc-ordered"))
  (defthm merged-code-is-safe-implies-ordered
   (implies (and (merged-code-safe merged-code init-frame)
                 (wff-code1 (extract-code merged-code)
                            (g 'pc (car merged-code))))
            (ordered (collect-pc-merged-code merged-code))))

  (defthm merged-code-safe-implies-pc-less-than
    (implies (and (WFF-CODE1 (EXTRACT-CODE MERGED-CODE)
                             (+ 1 pc))
                  (consp (extract-code merged-code))
                  (merged-code-safe merged-code sig-frame))
             (< pc 
                (g 'pc (car merged-code))))
    :rule-classes :linear)

  (defthm merged-code-safe-stack-map-implies-consp-extract-code
    (implies (and (merged-code-safe merged-code init-frame)
                  (stack-map? init-frame))
             (consp (extract-code merged-code)))
    :rule-classes :forward-chaining))



(defthm car-collect-pc-merged-code-is
  (implies (consp (cdr merged-code))
           (equal (car (collect-pc-merged-code merged-code))
                  (g 'pc (car merged-code)))))


(defun collect-keys-from-witness (sig-vector)
  (if (endp sig-vector) nil
    (cons (car (car sig-vector))
          (collect-keys-from-witness (cdr sig-vector)))))


(defthm subsetp-collect-pc-collect-pc
  (implies (member x (collect-keys-from-witness 
                      (collect-witness-merged-code-safe merged-code init-frame)))
           (member x (collect-pc-merged-code merged-code)))
  :hints (("Goal" :in-theory (disable sig-frame-compatible
                                      bcv-check-step-pre
                                      bcv-execute-step
                                      inst? stack-map?)
           :do-not '(generalize fertilize))))


(defthm subsetp-collect-pc-collect-pc-1
  (implies  (not (member x (collect-pc-merged-code merged-code)))
            (not (member x (collect-keys-from-witness 
                            (collect-witness-merged-code-safe merged-code init-frame)))))
  :hints (("Goal" :in-theory (disable sig-frame-compatible
                                      bcv-check-step-pre
                                      bcv-execute-step
                                      inst? stack-map?)
           :do-not '(generalize fertilize))))


(defthm not-member-of-keys-not-bound
  (implies (not (member x (collect-keys-from-witness sig-vector)))
           (not (assoc-equal x sig-vector))))


;; (i-am-here) ;; Mon Nov  7 14:18:54 2005

(defthm not-consp-cdr-not-collect-witness
  (implies (not (consp (cdr merged-code)))
           (not (collect-witness-merged-code-safe merged-code init-frame))))


(defthm merged-code-is-safe-implies-not-bound-smaller
  (implies (and (merged-code-safe merged-code init-frame)
                (WFF-CODE1 (EXTRACT-CODE MERGED-CODE)
                           (g 'pc (car merged-code)))
                 (< pc1 (g 'pc (car merged-code))))
           (not (assoc-equal pc1 (collect-witness-merged-code-safe 
                                  merged-code init-frame))))
  :hints (("Goal" :in-theory (disable merged-code-safe
                                      wff-code1
                                      stack-map?
                                      collect-pc-merged-code
                                      extract-code
                                      collect-witness-merged-code-safe)
           :cases ((consp (cdr merged-code)))
           :do-not-induct t)))

