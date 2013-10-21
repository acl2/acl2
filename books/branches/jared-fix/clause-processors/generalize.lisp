
(in-package "ACL2")

(include-book "tools/flag" :dir :system)


(local (include-book "data-structures/list-theory" :dir :system))

(include-book "join-thms")


;; Collect up variables

(encapsulate
 ()
 (mutual-recursion 
  (defund term-vars (x)
    (declare (xargs :guard (pseudo-termp x)
                    :verify-guards nil))
    (cond ((atom x) (list x))
          ((eq (car x) 'quote) nil)
          (t
           (term-vars-list (cdr x)))))
  (defund term-vars-list (x)
    (declare (xargs :guard (pseudo-term-listp x)))
    (if (consp x)
        (append (term-vars (car x))
                (term-vars-list (cdr x)))
      nil)))

 (defthm term-vars-list-when-not-consp
   (implies (not (consp x))
            (equal (term-vars-list x)
                   nil))
   :hints(("Goal" :in-theory (enable term-vars-list))))

 (defthm term-vars-list-of-cons
   (equal (term-vars-list (cons a x))
          (append (term-vars a)
                  (term-vars-list x)))
   :hints(("Goal" :in-theory (enable term-vars-list))))

 (flag::make-flag flag-term-vars 
                  term-vars
                  :flag-mapping ((term-vars . term)
                                 (term-vars-list . list)))

 (defthm-flag-term-vars true-listp-of-flag-term-vars
   (term (true-listp (term-vars x))
         :rule-classes ((:type-prescription)))
   (list (true-listp (term-vars-list x))
         :rule-classes ((:type-prescription)))
   :hints(("Goal" :induct (flag-term-vars flag x))))
  
 (defthm-flag-term-vars symbol-listp-of-flag-term-vars
   (term (implies (force (pseudo-termp x))
                  (symbol-listp (term-vars x)))
         :rule-classes ((:type-prescription)))
   (list (implies (force (pseudo-term-listp x))
                  (symbol-listp (term-vars-list x)))
         :rule-classes ((:type-prescription)))
   :hints(("Goal" 
           :induct (flag-term-vars flag x)
           :expand (term-vars x))))

 (verify-guards term-vars))


(defevaluator gen-eval gen-eval-lst ((if x y z)))

(def-join-thms gen-eval)



(mutual-recursion
 (defun replace-subterms (x alist)
   (declare (xargs :guard (and (pseudo-termp x) (alistp alist))))
   (let ((lookup (assoc-equal x alist)))
     (if lookup
         (cdr lookup)
       (cond ((atom x) x)
             ((eq (car x) 'quote) x)
             (t (cons (car x) (replace-subterms-list (cdr x) alist)))))))

 (defun replace-subterms-list (x alist)
   (declare (xargs :guard (and (pseudo-term-listp x) (alistp alist))))
   (if (atom x)
       nil
     (cons (replace-subterms (car x) alist)
           (replace-subterms-list (cdr x) alist)))))



(flag::make-flag flag-replace-subterms replace-subterms
                 :flag-mapping ((replace-subterms . term)
                                (replace-subterms-list . list)))


(defthm lookup-is-a-pseudo-term
  (implies (pseudo-term-listp (strip-cdrs alist))
           (pseudo-termp (cdr (assoc-equal x alist)))))


(defthm len-replace-subterms-list
  (equal (len (replace-subterms-list x alist))
         (len x)))

(defthm-flag-replace-subterms pseudo-termp-replace-subterms
  (term (implies (and (pseudo-term-listp (strip-cdrs alist))
                      (pseudo-termp x))
                 (pseudo-termp (replace-subterms x alist))))
  (list (implies (and (pseudo-term-listp (strip-cdrs alist))
                      (pseudo-term-listp x))
                 (pseudo-term-listp (replace-subterms-list x alist))))
  :hints (("goal" :induct (flag-replace-subterms flag x alist)
           :expand ((PSEUDO-TERMP (CONS (CAR X)
                             (REPLACE-SUBTERMS-LIST (CDR X) ALIST)))))))


(defun replace-alist-to-bindings (alist bindings)
  (if (atom alist)
      nil
    (cons (cons (cdar alist) (gen-eval (caar alist) bindings))
          (replace-alist-to-bindings (cdr alist) bindings))))


(defthm intersectp-equal-of-components-of-term-vars-1
  (implies (and (not (intersectp-equal lst (term-vars-list x)))
                (consp x))
           (not (intersectp-equal lst (term-vars (car x))))))

(defthm intersectp-equal-of-components-of-term-vars-2
  (implies (and (not (intersectp-equal lst (term-vars-list x)))
                (consp x))
           (not (intersectp-equal lst (term-vars-list (cdr x))))))

(defthm intersectp-equal-of-components-of-term-vars-3
  (implies (and (consp x) (not (equal (car x) 'quote))
                (not (intersectp-equal lst (term-vars x))))
           (not (intersectp-equal lst (term-vars-list (cdr x)))))
:hints(("Goal" :in-theory (enable term-vars))))

(defthm term-vars-when-symbolp
  (implies (symbolp x)
           (equal (term-vars x) (list x)))
  :hints(("Goal" :in-theory (enable term-vars))))


(defthm intersectp-equal-with-singleton
  (iff (intersectp-equal lst (list x))
       (member-equal x lst)))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defthm assoc-eq-is-assoc-equal
;   (equal (assoc-eq x al) (assoc-equal x al)))

(defthm assoc-equal-of-append
  (implies (alistp a)
           (equal (assoc-equal x (append a b))
                  (or (assoc-equal x a)
                      (assoc-equal x b)))))

(defthm alistp-replace-alist-to-bindings
  (alistp (replace-alist-to-bindings alist env)))

(defthm assoc-equal-replace-alist-to-bindings
  (implies (not (member-equal x (strip-cdrs alist)))
           (not (assoc-equal x (replace-alist-to-bindings alist env)))))
         

(defthm symbolp-assoc-equal
  (implies (symbol-listp (strip-cdrs alist))
           (symbolp (cdr (assoc-equal x alist)))))


(defthm assoc-in-replace-alist-to-bindings
  (implies (and (assoc-equal x alist)
                (no-duplicatesp-equal (strip-cdrs alist)))
           (equal (assoc-equal (cdr (assoc-equal x alist))
                               (replace-alist-to-bindings alist env))
                  (cons (cdr (assoc-equal x alist))
                        (gen-eval x env))))
  :hints (("goal" :induct (assoc-equal x alist))))
                  

(defthm nonnil-values-implies-cdr
  (implies (and (assoc-equal x alist)
                (not (member-equal nil (strip-cdrs alist))))
           (cdr (assoc-equal x alist))))



(defthm-flag-replace-subterms replace-subterms-identity
  (term (implies (and (not (intersectp-equal (strip-cdrs alist)
                                             (term-vars x)))
                      (symbol-listp (strip-cdrs alist))
                      (not (member-equal nil (strip-cdrs alist)))
                      (no-duplicatesp-equal (strip-cdrs alist))
                      (pseudo-termp x))
                 (equal (gen-eval (replace-subterms x alist)
                                  (append
                                   (replace-alist-to-bindings alist env)
                                   env))
                        (gen-eval x env))))
  (list (implies (and (not (intersectp-equal (strip-cdrs alist)
                                             (term-vars-list x)))
                      (symbol-listp (strip-cdrs alist))
                      (not (member-equal nil (strip-cdrs alist)))
                      (no-duplicatesp-equal (strip-cdrs alist))
                      (pseudo-term-listp x))
                 (equal (gen-eval-lst (replace-subterms-list x alist)
                                      (append
                                       (replace-alist-to-bindings alist env)
                                       env))
                        (gen-eval-lst x env))))
  :hints (("goal" :induct (flag-replace-subterms flag x alist))
          ("Subgoal *1/3" :use ((:instance gen-eval-constraint-0
                                           (x (cons (car x)
                                                    (replace-subterms-list (cdr
                                                                            x)
                                                                           alist)))
                                           (a (append
                                               (replace-alist-to-bindings alist
                                                                          env)
                                               env)))
                                (:instance gen-eval-constraint-0
                                           (a env)))
           :in-theory (disable gen-eval-constraint-0))))




(defthm disjoin-replace-subterms-list
  (implies (and (not (intersectp-equal (strip-cdrs alist)
                                       (term-vars-list x)))
                (symbol-listp (strip-cdrs alist))
                (not (member-equal nil (strip-cdrs alist)))
                (no-duplicatesp-equal (strip-cdrs alist))
                (pseudo-term-listp x))
           (iff (gen-eval (disjoin (replace-subterms-list x alist))
                          (append (replace-alist-to-bindings alist env)
                                  env))
                (gen-eval (disjoin x) env)))
  :hints (("goal" :induct (len x))
          ("Subgoal *1/1" :in-theory
           (enable replace-subterms-list
                   term-vars-list
                   gen-eval-disjoin-when-consp))))





(defun simple-generalize-cp (clause alist)
  (let ((syms (strip-cdrs alist)))
    (if (and (not (intersectp-equal syms (term-vars-list clause)))
           (symbol-listp syms)
           (not (member-equal nil syms))
           (no-duplicatesp-equal syms))
        (list (replace-subterms-list clause alist))
      (list clause))))

(defun alist-for-simple-generalize-cp (clause alist env)
  (let ((syms (strip-cdrs alist)))
    (if (and (not (intersectp-equal syms (term-vars-list clause)))
             (symbol-listp syms)
             (not (member-equal nil syms))
             (no-duplicatesp-equal syms))
        (append (replace-alist-to-bindings alist env) env)
      env)))

(defthm consp-replace-subterms-list
  (equal (consp (replace-subterms-list clause alist))
         (consp clause))
  :hints (("goal" :induct (len clause))))

(defthm simple-generalize-cp-correct
  (implies (and (pseudo-term-listp clause)
                (alistp env)
                (gen-eval (conjoin-clauses (simple-generalize-cp clause alist))
                          (alist-for-simple-generalize-cp clause alist env)))
           (gen-eval (disjoin clause) env))
  :hints (("goal" :do-not-induct t))
  :rule-classes :clause-processor)















;; MAKE-N-VARS, below, makes N "fresh" symbols that are not members of a
;; given list and are nonnil.


(defun char-of-digit (n)
  (declare (xargs :guard (and (integerp n)
                              (<= 0 n)
                              (< n 10))))
  (code-char (+ (char-code #\0) n)))

(defthm characterp-char-of-digit
  (characterp (char-of-digit n)))

(in-theory (disable char-of-digit))

(defun char-of-digit-equal-fn (n m)
  (implies (and (integerp n) (integerp m)
                (<= 0 n) (<= 0 m)
                (< n 10) (< m 10))
           (equal (equal (char-of-digit n) (char-of-digit m))
                  (equal n m))))

(defun chars-of-digit-equal-n-fn (n m)
  (or (zp m)
      (and (char-of-digit-equal-fn n (1- m))
           (chars-of-digit-equal-n-fn n (1- m)))))


(local (include-book "arithmetic/top-with-meta" :dir :system))

(defthm chars-of-digit-equal-n-fn-implies
  (implies (and (chars-of-digit-equal-n-fn n m)
                (integerp k) (integerp n) (integerp m)
                (<= 0 k) (<= 0 n) (<= 0 m)
                (< k m) (< n 10) (<= m 10))
           (equal (equal (char-of-digit n) (char-of-digit k))
                  (equal n k))))

(defun chars-of-digit-equal-n-m-fn (n m)
  (or (zp n)
      (and (chars-of-digit-equal-n-fn (1- n) m)
           (chars-of-digit-equal-n-m-fn (1- n) m))))

(defthm chars-of-digit-equal-n-m-fn-implies
  (implies (and (chars-of-digit-equal-n-m-fn n 10)
                (integerp j) (integerp k) (integerp n)
                (<= 0 j) (<= 0 k) (<= 0 n)
                (< j n) (< k 10) (<= n 10))
           (equal (equal (char-of-digit j) (char-of-digit k))
                  (equal j k)))
  :hints (("goal" :in-theory (disable (char-of-digit)
                                      (chars-of-digit-equal-n-fn)
                                      (chars-of-digit-equal-n-m-fn)))))

(defthm chars-of-digit-unique
  (implies (and (integerp n) (integerp m)
                (<= 0 n) (<= 0 m)
                (< n 10) (< m 10))
           (equal (equal (char-of-digit n) (char-of-digit m))
                  (equal n m)))
  :hints (("goal" :use ((:instance chars-of-digit-equal-n-m-fn-implies
                                   (n 10) (j n) (k m)))
           :in-theory (disable chars-of-digit-equal-n-m-fn-implies))))

(defconst *digit-chars* '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))


(defun char-of-digit-members (n)
  (or (zp n)
      (and (member-equal (char-of-digit (1- n))
                         *digit-chars*)
           (char-of-digit-members (1- n)))))

(defthm char-of-digit-members-n
  (implies (and (integerp m) (<= 0 m) (< m n)
                (integerp n)
                (char-of-digit-members n))
           (member-equal (char-of-digit m) *digit-chars*)))

(defthm char-of-digit-member-of-digit-chars
  (implies (and (integerp n) (<= 0 n) (< n 10))
           (member-equal (char-of-digit n) *digit-chars*))
  :hints (("Goal" :in-theory (disable char-of-digit-members-n)
           :use ((:instance char-of-digit-members-n (n 10) (m n))))))


(defun char-of-digit-nonzeros (n)
  (or (zp n)
      (and (not (equal (char-of-digit n) #\0))
           (char-of-digit-nonzeros (1- n)))))

(defthm char-of-digit-nonzeros-n
  (implies (and (integerp m) (< 0 m) (< m n)
                (integerp n)
                (char-of-digit-nonzeros n))
           (not (equal (char-of-digit m) #\0))))

(defthm char-of-digit-nonzero
  (implies (and (integerp n) (< 0 n) (< n 10))
           (not (equal (char-of-digit n) #\0)))
  :hints (("Goal" :in-theory (disable char-of-digit-nonzeros-n)
           :use ((:instance char-of-digit-nonzeros-n (n 9) (m n))))))

(in-theory (disable char-of-digit (char-of-digit)))
           


(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (in-theory (disable floor)))
(defun nat-to-charlist1 (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      nil
    (cons (char-of-digit (mod n 10))
          (nat-to-charlist1 (floor n 10)))))


(local
 (defun n2cu-ind (n m)
   (if (or (zp n) (zp m))
       nil
     (n2cu-ind (floor n 10) (floor m 10)))))

(defthm nat-to-charlist1-unique
  (implies (and (natp n) (natp m))
           (equal (equal (nat-to-charlist1 n) (nat-to-charlist1 m))
                  (equal n m)))
  :hints (("goal" :induct (n2cu-ind n m))))

(defthm character-listp-nat-to-charlist1
  (character-listp (nat-to-charlist1 n)))


(defthm nat-to-charlist1-intersect-digit-chars
  (implies (not (zp n))
           (intersectp-equal (nat-to-charlist1 n) *digit-chars*)))


(defthm nat-to-charlist1-not-list-char-0
  (not (equal (nat-to-charlist1 n) '(#\0)))
  :hints (("goal" :cases ((and (natp n) (<= 10 n)) (zp n))))
  :otf-flg t)

(in-theory (disable nat-to-charlist1))

(defun nat-to-charlist (n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      (list #\0)
    (nat-to-charlist1 n)))

(defthm character-listp-nat-to-charlist
  (character-listp (nat-to-charlist n)))

(defthm intersectp-nat-to-charlist
  (intersectp-equal (nat-to-charlist n) *digit-chars*))

(defthm nat-to-charlist-unique
  (implies (and (natp n) (natp m))
           (equal (equal (nat-to-charlist n) (nat-to-charlist m))
                  (equal n m))))

(in-theory (disable nat-to-charlist))






(local
 (defun rcu-ind (x y xz yz)
   (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
   (if (and (atom x) (atom y))
       (list xz yz)
     (rcu-ind (cdr x) (cdr y)
              (if (consp x) (cons (car x) xz) xz)
              (if (consp y) (cons (car y) yz) yz)))))

(defthm revappend-charlists-unique
  (implies (and (character-listp x) (character-listp y)
                (equal (len xz) (len yz)))
           (equal (equal (revappend x xz) (revappend y yz))
                  (and (equal x y) (equal xz yz))))
  :hints (("goal" :induct (rcu-ind x y xz yz))))

(defthm reverse-charlists-unique
  (implies (and (character-listp x) (character-listp y))
           (equal (equal (reverse x) (reverse y))
                  (equal x y))))

(defthm character-listp-reverse
  (implies (character-listp x)
           (character-listp (reverse x))))

(defthm intersectp-revappend1
  (implies (intersectp-equal b c)
           (intersectp-equal (revappend a b) c)))

(defthm intersectp-revappend
  (equal (intersectp-equal (revappend a b) c)
         (or (intersectp-equal a c)
             (intersectp-equal b c))))

(defthm intersectp-reverse
  (equal (intersectp-equal (reverse a) b)
         (intersectp-equal a b)))

(local (in-theory (disable reverse)))

(defun nat-to-str (n)
  (declare (xargs :guard (natp n)))
  (coerce (reverse (nat-to-charlist n)) 'string))


(defthm coerce-unique
  (implies (and (character-listp x) (character-listp y))
           (equal (equal (coerce x 'string) (coerce y 'string))
                  (equal x y)))
  :hints (("goal" :in-theory (disable coerce-inverse-1)
           :use ((:instance coerce-inverse-1
                            (x y))
                 coerce-inverse-1))))

(defthm nat-to-str-unique
  (implies (and (natp n) (natp m))
           (equal (equal (nat-to-str n) (nat-to-str m))
                  (equal n m))))

(defthm stringp-nat-to-str
  (stringp (nat-to-str n)))

(defthm nat-to-str-coerce-intersectp
  (intersectp-equal (coerce (nat-to-str n) 'list)
                    *digit-chars*))

(in-theory (disable nat-to-str))

(defun symbol-n (base n)
  (declare (xargs :guard (and (symbolp base) (natp n))))
  (intern-in-package-of-symbol
   (concatenate 'string (symbol-name base) (nat-to-str n))
   base))

(defthm symbolp-symbol-n
  (symbolp (symbol-n base n)))

(defthm append-unique
  (equal (equal (append x y) (append x z))
         (equal y z)))
  
(defthm intersectp-equal-append
  (equal (intersectp-equal (append a b) c)
         (or (intersectp-equal a c)
             (intersectp-equal b c))))


(defthm intern-in-package-of-symbol-unique
  (implies (and (stringp a) (stringp b) (symbolp base))
           (equal (equal (intern-in-package-of-symbol a base)
                         (intern-in-package-of-symbol b base))
                  (equal a b)))
  :hints (("goal" :in-theory (disable symbol-name-intern-in-package-of-symbol)
           :use ((:instance symbol-name-intern-in-package-of-symbol
                            (s a) (any-symbol base))
                 (:instance symbol-name-intern-in-package-of-symbol
                            (s b) (any-symbol base))))))


(defthm symbol-n-unique-n
  (implies (and (symbolp base) (natp n) (natp m))
           (equal (equal (symbol-n base n) (symbol-n base m))
                  (equal n m)))
  :hints (("goal" :in-theory (enable nat-to-str))))

(defthm coerce-symbol-n-intersectp-equal
  (implies (symbolp base)
           (intersectp-equal (coerce (symbol-name (symbol-n base n)) 'list)
                             *digit-chars*)))

(in-theory (disable symbol-n))

(defthm symbol-n-nonnil
  (implies (symbolp base)
           (symbol-n base n))
  :hints (("goal" :in-theory (disable coerce-symbol-n-intersectp-equal)
           :use (coerce-symbol-n-intersectp-equal))))




(defun past-syms-in-avoid (base m avoid-lst)
  (if (zp m)
      0
    (if (member-eq (symbol-n base (1- m)) avoid-lst)
        (1+ (past-syms-in-avoid
             base (1- m) avoid-lst))
      (past-syms-in-avoid base (1- m) avoid-lst))))


(defthm past-syms-in-avoid-remove-equal
  (implies (and (natp m) (natp n) (<= m n) (symbolp base))
           (equal (past-syms-in-avoid base m (remove-equal (symbol-n base n) avoid))
                  (past-syms-in-avoid base m avoid))))

(defthm len-remove-equal-linear
  (implies (member-equal x lst)
           (< (len (remove-equal x lst)) (len lst)))
  :hints (("goal" :in-theory (disable len-remove-equal)))
  :rule-classes :linear)

(defun psia-redef (base m avoid-lst)
  (if (zp m)
      0
    (if (member-eq (symbol-n base (1- m)) avoid-lst)
        (1+ (psia-redef
             base (1- m)
             (remove-equal (symbol-n base (1- m)) avoid-lst)))
      (psia-redef base (1- m) avoid-lst))))

(encapsulate
 nil
 (local (defun psia-redef (base m avoid-lst)
         (if (zp m)
             0
           (if (member-eq (symbol-n base (1- m)) avoid-lst)
               (1+ (psia-redef
                    base (1- m)
                    (remove-equal (symbol-n base (1- m)) avoid-lst)))
             (psia-redef base (1- m) avoid-lst)))))

 (local (defthm psia-to-redef
          (implies (symbolp base)
                   (equal (past-syms-in-avoid base m avoid-lst)
                          (psia-redef base m avoid-lst)))
          :hints (("goal" :induct (psia-redef base m avoid-lst)))))

 (defthm past-syms-in-avoid-max
   (implies (symbolp base)
            (<= (past-syms-in-avoid base m avoid-lst)
                (len avoid-lst)))
  :hints (("goal" :in-theory (disable leq-position-equal-len len-remove-equal))
          ("Subgoal *1/2" :in-theory (disable leq-position-equal-len
                                              len-remove-equal)))
  :rule-classes :linear))


(defun make-n-vars (n base m avoid-lst)
  (declare (xargs :measure (make-ord 1 (if (symbolp base)
                                           (+ 1 (- (len avoid-lst)
                                                   (past-syms-in-avoid base (nfix m)
                                                                       avoid-lst)))
                                         1)
                                     (nfix n))
                  :guard (and (natp n) (natp m) (symbolp base)
                              (true-listp avoid-lst))))
  (if (or (zp n) (not (natp m)) (not (symbolp base)))
      nil
    (let ((new (symbol-n base m)))
      (if (member-eq new avoid-lst)
          (make-n-vars n base (1+ m) avoid-lst)
        (cons new (make-n-vars (1- n) base (1+ m) avoid-lst))))))



(defthm make-n-vars-len
  (implies (and (natp m) (symbolp base))
           (equal (len (make-n-vars n base m avoid-lst))
                  (nfix n))))

(defthm make-n-vars-not-in-avoid
  (not (intersectp-equal (make-n-vars n base m avoid-lst)
                         avoid-lst)))

(defthm make-n-vars-member-lemma
  (implies (and (natp j) (natp k) (< j k))
           (not (member-equal (symbol-n base j)
                              (make-n-vars n base k avoid-lst)))))

(defthm make-n-vars-no-dupsp
  (no-duplicatesp-equal (make-n-vars n base m avoid-lst)))

(defthm make-n-vars-not-nil
  (not (member-equal nil (make-n-vars n base m avoid-lst))))


(defthm symbol-listp-make-n-vars
  (symbol-listp (make-n-vars n base m avoid-lst)))
