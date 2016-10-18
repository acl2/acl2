#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book);$ACL2s-Preamble$|#


(in-package "DEFDATA")

(set-verify-guards-eagerness 2)

(include-book "num-list-fns")

(local (include-book "num-list-thms"))

(local (in-theory (disable rem floor)))
(local (include-book "rem-and-floor"))

(include-book "mv-proof")

(defun weighted-switch-nat-find (rem-weights weights-idx rem-wchoice quotient-x)
  (declare (xargs :guard (and (pos-listp rem-weights)
                              (consp rem-weights) ; len >= 1
                              (natp weights-idx)
                              (integerp rem-wchoice)
                              (<= 0 rem-wchoice)
                              (< rem-wchoice (sum-list rem-weights))
                              (natp quotient-x))))
  (if (mbe :logic (or (endp rem-weights)
                      (endp (cdr rem-weights))
                      (< rem-wchoice (car rem-weights)))
           :exec (< rem-wchoice (car rem-weights)))
    (mv weights-idx (+ (* (car rem-weights) quotient-x) 
;changed from mv to list
;UPDATE: changed back to mv 9 July 2011
                       rem-wchoice))
    (weighted-switch-nat-find (cdr rem-weights) (1+ weights-idx)
                              (- rem-wchoice (car rem-weights))
                              quotient-x)))

(local
 (defthm weighted-switch-nat-find--car-integerp
   (implies (integerp weights-idx)
            (integerp (car (weighted-switch-nat-find rw weights-idx rwc qx))))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm weighted-switch-nat-find--car-non-neg
   (implies (<= 0 weights-idx)
            (<= 0 (car (weighted-switch-nat-find rw weights-idx rwc qx))))
   :rule-classes (:rewrite :linear)))

(local
 (defthm weighted-switch-nat-find--car-bound
   (<= (car (weighted-switch-nat-find rem-weights weights-idx rwc qx))
       (+ weights-idx (len (cdr rem-weights))))
   :rule-classes (:linear)))

(local
 (defthm weighted-switch-nat-find--car-bound2
   (implies (consp rem-weights)
            (< (car (weighted-switch-nat-find rem-weights weights-idx rwc qx))
               (+ weights-idx (len rem-weights))))
   :rule-classes (:linear)))

(local
 (defthm weighted-switch-nat-find--cadr-integerp
   (implies (and (integer-listp rem-weights)
                 (integerp rem-wchoice)
                 (integerp quotient-x))
            (integerp (cadr (weighted-switch-nat-find rem-weights weights-idx rem-wchoice quotient-x))))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm weighted-switch-nat-find--cadr-non-neg
   (implies (and (pos-listp rem-weights)
                 (<= 0 rem-wchoice)
                 (integerp quotient-x)
                 (<= 0 quotient-x))
            (<= 0 (cadr (weighted-switch-nat-find rem-weights weights-idx rem-wchoice quotient-x))))
   :rule-classes (:rewrite :linear)))

(local
 (encapsulate nil
   (local (include-book "arithmetic-5/top" :dir :system))
   
   (local (SET-DEFAULT-HINTS '((acl2::NONLINEARP-DEFAULT-HINT
                                acl2::STABLE-UNDER-SIMPLIFICATIONP
                                acl2::HIST acl2::PSPV))))
   
   (defthm weighted-switch-nat-find--cadr-loose-bound
     (implies (and (pos-listp rem-weights)
                   (<= 0 rem-wchoice)
                   (integerp quotient-x)
                   (<= 0 quotient-x)
                   (rationalp bound)
                   (<= (max-nat-list rem-weights) bound))
              (<= (cadr (weighted-switch-nat-find rem-weights weights-idx rem-wchoice quotient-x))
                  (+ rem-wchoice
                     (* quotient-x bound))))
     :rule-classes (:rewrite :linear))
   
   (defthm weighted-switch-nat-find--cadr-bound-pre
     (implies (and (pos-listp rem-weights)
                   (consp rem-weights)
                   (consp (cdr rem-weights))
                   (<= 0 rem-wchoice)
                   (integerp quotient-x)
                   (<= 0 quotient-x)
                   (implies (= 0 quotient-x)
                            (>= rem-wchoice (car rem-weights)))
                   (rationalp bound)
                   (<= (sum-list rem-weights) bound))
              (< (cadr (weighted-switch-nat-find rem-weights weights-idx rem-wchoice quotient-x))
                 (+ rem-wchoice
                    (* quotient-x bound)))))
   
   (defthm weighted-switch-nat-find--cadr-bound
     (implies (and (pos-listp rem-weights)
                   (consp rem-weights)
                   (consp (cdr rem-weights))
                   (<= 0 rem-wchoice)
                   (integerp quotient-x)
                   (<= 0 quotient-x)
                   (implies (= 0 quotient-x)
                            (>= rem-wchoice (car rem-weights))))
              (< (cadr (weighted-switch-nat-find rem-weights weights-idx rem-wchoice quotient-x))
                 (+ rem-wchoice
                    (* quotient-x (sum-list rem-weights)))))
     :rule-classes (:rewrite :linear))))
 
(defun weighted-switch-nat (weights x)
  (declare (xargs :guard (and (pos-listp weights)
                              (consp weights) ; len >= 1
                              (integerp x)
                              (<= 0 x))))
  (let* ((weights (mbe :logic (pos-list-fix weights)
                       :exec weights))
         (x (mbe :logic (nfix x)
                 :exec x))
         (wtot (sum-list weights))
         (wchoice (rem x wtot)))
    (weighted-switch-nat-find weights 0 wchoice (floor x wtot))))

(in-theory (disable weighted-switch-nat-find))

(defthm weighted-switch-nat--car-integerp
  (integerp (car (weighted-switch-nat weights x)))
  :rule-classes (:type-prescription :rewrite))

(defthm weighted-switch-nat--car-non-neg
  (<= 0 (car (weighted-switch-nat weights x)))
  :rule-classes (:linear :rewrite))

(defthm weighted-switch-nat--car-bound
  (<= (car (weighted-switch-nat weights x)) (len (cdr weights)))
  :rule-classes (:linear :rewrite))

(defthm weighted-switch-nat--car-bound2
  (implies (consp weights)
           (< (car (weighted-switch-nat weights x)) (len weights)))
  :rule-classes (:linear :rewrite))


(defthm weighted-switch-nat--cadr-integerp
  (integerp (cadr (weighted-switch-nat weights x)))
  :rule-classes (:type-prescription :rewrite))

(defthm weighted-switch-nat--cadr-non-neg
  (<= 0 (cadr (weighted-switch-nat weights x)))
  :rule-classes (:linear :rewrite))

(defthm weighted-switch-nat--cadr-<=
  (implies (and (integerp x)
                (<= 0 x))
           (<= (cadr (weighted-switch-nat weights x))
               x))
  :hints (("Goal" :use ((:instance weighted-switch-nat-find--cadr-loose-bound
                         (rem-weights (pos-list-fix weights))
                         (weights-idx 0)
                         (rem-wchoice (rem x (sum-list (pos-list-fix weights))))
                         (quotient-x (floor x (sum-list (pos-list-fix weights))))
                         (bound (sum-list (pos-list-fix weights)))))))
  :rule-classes (:linear :rewrite))

(encapsulate nil

  (local (in-theory (disable pos-listp sum-list)))
  (local (in-theory (enable weighted-switch-nat-find)))
  
  (defthm weighted-switch-nat--cadr-less1
    (implies (and (pos-listp weights)
                  (consp weights)
                  (consp (cdr weights))
                  (integerp x)
                  (<= (car weights) x))
             (< (cadr (weighted-switch-nat weights x))
                x))
    :hints (("Goal'" :use ((:instance weighted-switch-nat-find--cadr-bound
                            (rem-weights (pos-list-fix weights))
                            (weights-idx 0)
                            (rem-wchoice (rem x (sum-list (pos-list-fix weights))))
                            (quotient-x (floor x (sum-list (pos-list-fix weights))))))))
    :rule-classes (:linear :rewrite))

  (local (defthm weighted-switch-nat--cadr-less2-lemma
           (implies (and (pos-listp weights)
                         (consp weights)
                         (consp (cdr weights))
                         (integerp x)
                         (<= 0 x)
                         (< 0 (car (weighted-switch-nat weights x))))
                    (<= (car weights) x))
           :rule-classes :forward-chaining))
  
  (local (in-theory (union-theories '(weighted-switch-nat--cadr-less2-lemma
                                      weighted-switch-nat--cadr-less1)
                                    (theory 'minimal-theory))))
  
  (defthm weighted-switch-nat--cadr-less2
    (implies (and (pos-listp weights)
                  (consp weights)
                  (consp (cdr weights))
                  (integerp x)
                  (<= 0 x)
                  (< 0 (car (weighted-switch-nat weights x))))
             (< (cadr (weighted-switch-nat weights x))
                x))
    :rule-classes (:linear :rewrite)))

(in-theory (disable weighted-switch-nat))

(local
 (defthm make-list-ac--pos
   (implies (and (posp v)
                 (pos-listp ac))
            (pos-listp (make-list-ac n v ac)))
   :rule-classes (:rewrite)))

(defun switch-nat (nchoices x)
  (declare (xargs :guard (and (posp nchoices)
                              (natp x))))
  (weighted-switch-nat (make-list nchoices :initial-element 1) x))

(defun multiple-switch-nat (nchoices-lst x)
  (declare (xargs :guard (and (pos-listp nchoices-lst)
                              (consp nchoices-lst) ; len >= 1
                              (natp x))))
  (mv-let (choice x)
          (switch-nat (car nchoices-lst) x)
          (if (endp (cdr nchoices-lst))
              (mv (list choice) x)
            (mv-let (choice-lst x) 
                    (multiple-switch-nat (cdr nchoices-lst)
                                         (nfix x)) ; help guard verification
                    
                    (mv (cons choice choice-lst) x)))));switched back to mv

(defthm mv-nth--to--my-mv-nth--weighted-switch-nat
  (equal (mv-nth n (weighted-switch-nat y x))
         (my-mv-nth n (weighted-switch-nat y x)))
  :hints (("Goal" :in-theory (enable mv-nth--to--my-mv-nth))))




(defun nfixg (x)
  (declare (xargs :guard (natp x)))
  (mbe :logic (if (natp x) x 0)
       :exec x))#|ACL2s-ToDo-Line|#


#| test:
(defun nth-foo (x)
  (declare (xargs :measure (nfix x)
                  :guard (natp x)))
    (mv-let (sw v)
            (switch-nat 2 (nfixg x))
            (if (= sw 0)
              v
              (cons 'x (nth-foo v)))))
|#
