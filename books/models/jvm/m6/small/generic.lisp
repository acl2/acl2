(in-package "ACL2")
(include-book "jvm-model")
(include-book "bcv-simple-model")

(defthm g-pc-extract-sig-frame
  (equal (G 'PC
            (EXTRACT-SIG-FRAME frame method-table))
         (g 'pc frame))
  :hints (("Goal" :in-theory (enable extract-sig-frame))))


(defthm g-max-stack-extract-sig-frame
  (equal (G 'max-stack
            (EXTRACT-SIG-FRAME frame method-table))
         (g 'max-stack frame))
  :hints (("Goal" :in-theory (enable extract-sig-frame))))

(defthm g-opstack-stack-extract-sig-frame
  (equal (G 'op-stack
            (EXTRACT-SIG-FRAME frame method-table))
         (len (g 'op-stack frame)))
  :hints (("Goal" :in-theory (enable extract-sig-frame))))


(defthm g-method-table-extract-sig-frame
  (equal (G 'method-table
            (EXTRACT-SIG-FRAME frame method-table))
         method-table)
  :hints (("Goal" :in-theory (enable extract-sig-frame))))

(defthm g-method-name-extract-sig-frame
  (equal (G 'method-name
            (EXTRACT-SIG-FRAME frame method-table))
         (g 'method-name frame))
  :hints (("Goal" :in-theory (enable extract-sig-frame))))

;----------------------------------------------------------------------

(defthm integerp-implies-integper-plus-1
  (implies (integerp x)
           (integerp (+ 1 x))))

;----------------------------------------------------------------------

(defthm g-opstack-create-init-frame
  (equal (g 'op-stack (createinitframe anymethod anylocals st))
         nil))


(defthm g-max-stack-create-init-frame
  (equal (g 'max-stack (createinitframe anymethod anylocals st))
         (g 'max-stack (cdr (assoc-equal anymethod
                                         (g 'method-table st))))))


(defthm g-method-name-create-init-frame
  (equal (g 'method-name (createinitframe method-name anylocals st))
         method-name))

;----------------------------------------------------------------------

(defthm g-method-table-popStack-n
  (equal (g 'method-table (popStack-n st n))
         (g 'method-table st)))

;----------------------------------------------------------------------

;; (local 
;;  (defthm nth-out-of-bound-is-nil-1
;;    (implies (and (true-listp l)
;;                  (integerp x)
;;                  (>= x (len l)))
;;             (not (nth x l)))))

;; ;; nth is a strange. if x is not a number, 
;; ;; it returns (car l) ... 

;; (local 
;;  (defthm nth-out-of-bound-is-nil-2
;;    (implies (and (true-listp l)
;;                  (integerp x)
;;                  (< x 0))
;;             (not (nth x l)))))
            


;----------------------------------------------------------------------

(defthm g-max-stack-popStack-n
  (equal (g 'max-stack (car (g 'call-stack (popStack-n st n))))
         (g 'max-stack (car (g 'call-stack st)))))



(defthm g-method-name-popStack-n
  (equal (g 'method-name (car (g 'call-stack (popStack-n st n))))
         (g 'method-name (car (g 'call-stack st)))))


(defthm g-pc-sig-frame-pop-n
  (equal (G 'PC
            (SIG-FRAME-POP-N n pre))
         (g 'pc pre)))


(defthm g-max-stack-sig-frame-pop-n
  (equal (G 'max-stack
            (SIG-FRAME-POP-N n pre))
         (g 'max-stack pre)))

;----------------------------------------------------------------------


(defthm g-method-table-sig-frame-pop-n
  (equal (G 'METHOD-TABLE
            (SIG-FRAME-POP-N n  PRE))
         (g 'method-table pre)))

;----------------------------------------------------------------------

(defthm g-method-name-sig-frame-pop-n
  (equal (G 'METHOD-name
            (SIG-FRAME-POP-N n  PRE))
         (g 'method-name pre)))


;----------------------------------------------------------------------

(defthm inst?-implies-not-stackmap
  (implies (inst? inst)
           (not (stack-map? inst))))

