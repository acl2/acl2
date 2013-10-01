; (include-book "m1")
; (certify-book "defsys-utilities" 1)

(in-package "M1")

(defthm about-make-state
  (and (true-listp (make-state pc locs stk prog))
       (equal (len (make-state pc locs stk prog)) 4))
  :hints (("Goal" :in-theory (enable make-state))))

(defun name-locals (names locals i)
  (cond ((endp names) t)
        ((equal (car names) (nth i locals))
         (name-locals (cdr names) locals (+ i 1)))
        (t nil)))

(defthm name-locals-opener
  (and (equal (name-locals nil locals i) t)
       (equal (name-locals (cons name names) locals i)
              (and (equal name (nth i locals))
                   (name-locals names locals (+ 1 i))))))

(defun name-locals-locals-gen-hint (names junk)
  (if (endp names)
      junk
      (name-locals-locals-gen-hint (cdr names)
                                   (append junk (list (car names))))))

(defthm append-assoc
  (equal (append (append a b) c) (append a (append b c))))

(defthm len-append
  (equal (len (append a b)) (+ (len a) (len b))))

(defthm nth-len-append
  (equal (nth (len a) (append a b))
         (car b)))

(defthm name-locals-locals-gen
  (equal (name-locals names (append junk names) (len junk))
         t)
  :hints (("Goal" :induct (name-locals-locals-gen-hint names junk)))
  :rule-classes nil)

(defthm name-locals-locals
  (equal (name-locals names names 0) t)
  :hints (("Goal" :use (:instance name-locals-locals-gen
                                  (junk nil)))))

(defun update-nth* (i lst locals)
  (cond ((endp lst) locals)
        (t (update-nth i (car lst)
                       (update-nth* (+ i 1) (cdr lst) locals)))))

(defthm update-nth*-opener
  (and (equal (update-nth* i nil locals) locals)
       (equal (update-nth* i (cons x lst) locals)
              (update-nth i x (update-nth* (+ i 1) lst locals)))))

(defthm len-update-nth-nil
  (implies (natp i)
           (equal (len (update-nth i v nil))
                  (+ 1 i))))

(defthm len-update-nth-inequality
  (<= (len x) (len (update-nth i v x)))
  :rule-classes :linear)

; The :rewrite rule len-update-nth causes case splits that prevent us
; from establishing some of the READY-AT hypotheses.  It seems to be sufficient
; to know just the weaker :linear result, just proved.  So we disable the rewrite rule.

(in-theory (disable len-update-nth))

(defthm update-nth-noop
  (implies (and (natp i)
                (< i (len x)))
           (equal (update-nth i (nth i x) x) x)))

(defun number-of-explicit-elements (x)
  (cond ((atom x) 0)
        ((quotep x)
         (cond ((true-listp (car (cdr x)))
                (len (car (cdr x))))
               ((consp (car (cdr x)))
                (+ 1 (number-of-explicit-elements
                      (kwote (cdr (car (cdr x)))))))
               (t 0)))
        ((eq (acl2::ffn-symb x) 'cons)
         (+ 1 (number-of-explicit-elements (acl2::fargn x 2))))
        (t 0)))

(defthm nth-cons
  (and (equal (nth 0 (cons e x)) e)
       (implies (and (natp n)
                     (syntaxp
                      (and (quotep n)
                           (natp (car (cdr n)))
                           (<= (car (cdr n))
                               (number-of-explicit-elements x)))))
                (equal (nth (+ 1 n) (cons e x))
                       (nth n x)))))

(defthm true-listp-m1-update-nth-nil
  (true-listp (update-nth i v nil)))

(defthm true-listp-m1-update-nth
  (implies (true-listp x)
           (true-listp (update-nth i v x))))

(in-theory (disable nth-alt-def nth-add1! update-nth))

(defthm true-listp-locals-step
  (implies (true-listp (locals s))
           (true-listp (locals (step s))))
  :hints (("Goal" :in-theory (enable step))))

(defthm true-listp-locals-m1
  (implies (true-listp (locals s))
           (true-listp (locals (m1 s n))))
  :hints (("Goal" :in-theory (enable m1))))

(defthm len-locals-step
  (<= (len (locals s))
      (len (locals (step s))))
  :hints (("Goal" :in-theory (enable step)))
  :rule-classes :linear)

(defthm len-locals-m1
  (<= (len (locals s))
      (len (locals (m1 s n))))
  :hints (("Goal" :in-theory (enable m1)))
  :rule-classes :linear)

(defthm s-is-make-state-s
  (implies (and (true-listp s)
                (equal (len s) 4)
                (equal (pc s) pc)
                (equal (program s) program))
           (equal (equal s (make-state pc (locals s) (stack s) program))
                  t))
  :hints (("Goal" :in-theory (enable make-state))))