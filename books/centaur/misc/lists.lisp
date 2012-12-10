
(in-package "ACL2")

;; Supplementing list-defthms, moving to a slightly different approach.

;; - For functions like take, etc that could have convenient
;; cdr-recursive definitions but don't, we make new definition rules and
;; corresponding induction rules.

;; - We try to avoid natp hyps and instead use nfix in RHSes where necessary.
;; We prove nat-equiv congruences where appropriate (and not already done in arith-equivs).

;; - For functions like SUBSEQ and BUTLAST which should have reasonable
;; recursive definitions and congruences but don't, we'll rewrite them to
;; functions suffixed with X that do, under appropriate constraints.

;; (future):
;; - For rewrite rules that cause case splits, we prove separate rules for all
;; the cases and leave the splitting rule disabled by default.  We add these to
;; a ruleset to keep track.

;; - We prove list-equiv congruences where appropriate.

(include-book "arith-equivs")
(include-book "data-structures/list-defthms" :dir :system)
(local (in-theory (enable* arith-equiv-forwarding)))
(local (include-book "arithmetic/top-with-meta" :dir :system))

;; ------------------- LIST-FIX, LIST-EQUIV -------------------------------
;; We may or may not be able to maintain compatibility with the unicode books,
;; but we'll try.
(defund list-fix (x)
  (declare (xargs :guard t))
  (if (consp x)
      (cons (car x)
            (list-fix (cdr x)))
    nil))

(local (in-theory (enable list-fix)))

(defthm true-listp-of-list-fix
  (true-listp (list-fix x)))

(defthm list-fix-when-true-listp
  (implies (true-listp x)
           (equal (list-fix x) x)))

(defthm list-fix-under-iff
  (iff (list-fix x)
       (consp x)))

(defun list-equiv (x y)
  (declare (xargs :guard t))
  (equal (list-fix x) (list-fix y)))

(defequiv list-equiv)

(defthm list-fix-under-list-equiv
  (list-equiv (list-fix x) x))

;; Various list-equiv congruences.
(defcong list-equiv equal      (list-fix x) 1)
(defcong list-equiv equal      (car x) 1)
(defcong list-equiv list-equiv (cdr x) 1)
(defcong list-equiv list-equiv (cons x y) 2)

(defcong list-equiv equal      (nth n x) 2)
(defcong list-equiv list-equiv (nthcdr n x) 2)
(defcong list-equiv list-equiv (update-nth n v x) 3)

(defun cdr-cdr-ind (x y)
  (declare (xargs :measure (+ (len x) (len y))))
  (if (and (atom x) (atom y))
      nil
    (cdr-cdr-ind (cdr x) (cdr y))))

(defcong list-equiv equal      (consp x) 1 :hints (("goal" :induct (cdr-cdr-ind x x-equiv))))
(defcong list-equiv equal      (len x) 1 :hints (("goal" :induct (cdr-cdr-ind x x-equiv))))
(defcong list-equiv equal      (append x y) 1 :hints (("goal" :induct (cdr-cdr-ind x x-equiv))))
(defcong list-equiv list-equiv (append x y) 2)
(defcong list-equiv list-equiv (member k x) 2 :hints (("goal" :induct (cdr-cdr-ind x x-equiv))))
(defcong list-equiv iff        (member k x) 2 :hints (("goal" :induct (cdr-cdr-ind x x-equiv))))
(defcong list-equiv equal      (remove k x) 2 :hints (("goal" :induct (cdr-cdr-ind x x-equiv))))
(defcong list-equiv equal      (resize-list lst n default) 1)

(defthm list-fix-equal-forward-to-list-equiv
  (implies (equal (list-fix x) (list-fix y))
           (list-equiv x y))
  :rule-classes :forward-chaining)


;; ------------------- REVAPPEND -------------------------------
;; Supposing we let REVERSE open into revappend -- this means we don't need
;; (not (stringp x)) hyps.

(defcong list-equiv equal (revappend x y) 1
  :hints (("goal" :induct (and (cdr-cdr-ind x x-equiv)
                               (revappend x y)))))

(defcong list-equiv list-equiv (revappend x y) 2)

(defthm revappend-to-append
  (implies (syntaxp (not (equal b ''nil)))
           (equal (revappend a b)
                  (append (revappend a nil) b))))

(in-theory (disable binary-append-revappend))

(theory-invariant (not (and (active-runep '(:rewrite revappend-to-append))
                            (active-runep '(:rewrite binary-append-revappend)))))


;; ------------------- TAKE redefinition --------------------------

(defthm take-rec
  (equal (take n x)
         (if (zp n)
             nil
           (cons (car x)
                 (take (1- n) (cdr x)))))
  :rule-classes ((:definition :controller-alist ((take t nil)))))

(defthm take-ind
  t
  :rule-classes ((:induction
                  :pattern (take n x)
                  :scheme (xfirstn n x))))

(in-theory (disable take-is-xfirstn take))

(defcong list-equiv equal (take n x) 2)

;; ------------------- SUBSEQ-LIST redefinition --------------------------

(defun subseqx (lst start end)
  (declare (xargs :guard (and (true-listp lst)
                              (natp start)
                              (integerp end)
                              (<= start end)
                              (<= end (length lst)))
                  :verify-guards nil))
  (mbe :logic (if (zp start)
                  (take end lst)
                (subseqx (cdr lst) (1- start) (1- (nfix end))))
       :exec (subseq lst start end)))

(defthm subseq-list-is-subseqx
  (implies (and (natp start)
                (integerp end)
                (<= start end))
           (equal (subseq-list lst start end)
                  (subseqx lst start end)))
  :hints (("goal" :induct (subseqx lst start end))))

(verify-guards subseqx)

(defun cdr-cdr-dec-dec-ind (x y n m)
  (declare (xargs :measure (+ (len x) (len y) (nfix n) (nfix m))
                  :hints(("Goal" :in-theory (enable nfix)))))
  (if (and (atom x) (atom y) (zp n) (zp m))
      nil
    (cdr-cdr-dec-dec-ind (cdr x) (cdr y) (1- (nfix n)) (1- (nfix m)))))

(defcong list-equiv equal (subseqx lst start end) 1
  :hints (("goal" :induct (cdr-cdr-dec-dec-ind lst lst-equiv start end)
           :expand ((:free (lst) (subseqx lst start end)))
           :in-theory (disable list-equiv))))

(defcong nat-equiv equal (subseqx list start end) 2)
(defcong nat-equiv equal (subseqx list start end) 3)

;; ------------------- BUTLAST redefinition --------------------------

(defun butlastx (lst n)
  (declare (xargs :guard (and (true-listp lst)
                              (natp n))
                  :verify-guards nil))
  (mbe :logic (if (<= (len lst) (nfix n))
                  nil
                (cons (car lst)
                      (butlastx (cdr lst) n)))
       :exec (butlast lst n)))

(defthm butlast-is-butlastx
  (implies (natp n)
           (equal (butlast lst n)
                  (butlastx lst n)))
  :hints(("Goal" :in-theory (enable butlast)
          :induct (butlastx lst n))))

(verify-guards butlastx)



(defcong list-equiv equal (butlastx lst n) 1
  :hints(("Goal" :in-theory (disable list-equiv)
          :induct (cdr-cdr-ind lst lst-equiv))))

(defcong nat-equiv equal (butlastx lst n) 2)

;; ------------------- MAKE-LIST-AC redefinition --------------------------

;; Note: this is now make-list-ac-redef in list-defthms.lisp
;; (defthm make-list-ac-rec
;;   (equal (make-list-ac n val ac)
;;          (if (zp n)
;;              ac
;;            (cons val (make-list-ac (1- n) val ac))))
;;   :rule-classes ((:definition :controller-alist ((make-list-ac t nil nil)))))

;; (defun make-list-ac-rec-ind (n val ac)
;;   (if (zp n)
;;       (list val ac)
;;     (make-list-ac-rec-ind (1- n) val ac)))

;; (defthm make-list-ac-induct
;;   t
;;   :rule-classes ((:induction
;;                   :pattern (make-list-ac n val ac)
;;                   :scheme (make-list-ac-rec-ind n val ac))))

(defcong list-equiv list-equiv (make-list-ac n val ac) 3)
(defcong nat-equiv equal (make-list-ac n val ac) 1)



(defun cdr-cdr-dec-ind (x y n)
  (declare (xargs :measure (+ (len x) (len y) (nfix n))
                  :hints(("Goal" :in-theory (enable nfix)))))
  (if (and (atom x) (atom y) (zp n))
      nil
    (cdr-cdr-dec-ind (cdr x) (cdr y) (1- (nfix n)))))

