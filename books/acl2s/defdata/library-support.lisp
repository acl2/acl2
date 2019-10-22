#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

;record implementation
(include-book "defexec/other-apps/records/records" :dir :system)
;(include-book "finite-set-theory/osets/sets" :dir :system)
;; (include-book "std/osets/top" :dir :system)
(include-book "make-event/defconst-fast" :dir :system)

;GETTING RECORDS TO behave nicely here are some
;;RECORDS THMS proven

(defthm records-lemma-acl2-count
  (implies (and (ifmp v)
                (well-formed-map v))
           (< (acl2-count (mget-wf x v))
              (acl2-count v)))
  :hints (("goal" :in-theory (enable mget-wf)))
  :rule-classes :linear)

(defun non-empty-good-map (x)
  (declare (xargs :guard t))
  (and (consp x)
       (good-map x)))

(defthm records-acl2-count-linear-arith-<=
  (<= (acl2-count (mget k v))
      (acl2-count v))
  :hints (("goal" :in-theory (enable mget acl2->map)))
  :rule-classes :linear)

(defthm records-acl2-count-linear-arith-<
  (implies (and (not (equal k (acl2::ill-formed-key)))
                (mget k v))
           (< (acl2-count (mget k v))
              (acl2-count v)))
  :hints (("goal" :in-theory (enable mget acl2->map)))
  :rule-classes :linear)

(defthm records-acl2-count
  (implies (and (consp v)
                (not (equal x (ill-formed-key))))
           (< (acl2-count (mget x v))
              (acl2-count v)))
  :hints (("goal" :induct (mget-wf x v)
           :in-theory (enable mget acl2->map)))
  :rule-classes :linear)


;shifted from base.lisp to here.

;; (defun map-identity (x) 
;;   "for map elim rules -- dummy destructor"
;;   x)

(defun map-identity2 (a x) 
  "for map elim rule -- dummy destructor"
  (declare (ignore a))
  x)

(defthmd map-elim-rule 
  ;(implies (good-map x)
           (equal (mset a (mget a x) (map-identity2 a x))
                  x)
  :rule-classes :elim)



(defun list-identity2 (a x) 
  "for list elim rule -- dummy destructor"
  (declare (ignore a))
  x)
#|
Rules: ((:COMPOUND-RECOGNIZER ZP-COMPOUND-RECOGNIZER)
        (:DEFINITION ENDP)
        (:DEFINITION LEN)
        (:DEFINITION LIST-IDENTITY2)
        (:DEFINITION NATP)
        (:DEFINITION NOT)
        (:DEFINITION NTH)
        (:DEFINITION UPDATE-NTH)
        (:EXECUTABLE-COUNTERPART <)
        (:EXECUTABLE-COUNTERPART INTEGERP)
        (:EXECUTABLE-COUNTERPART LEN)
        (:EXECUTABLE-COUNTERPART NOT)
        (:EXECUTABLE-COUNTERPART ZP)
        (:FAKE-RUNE-FOR-LINEAR NIL)
        (:FAKE-RUNE-FOR-TYPE-SET NIL)
        (:INDUCTION LEN)
        (:INDUCTION NTH)
        (:INDUCTION UPDATE-NTH)
        (:REWRITE CONS-CAR-CDR)
        (:TYPE-PRESCRIPTION LEN))
Time:  0.08 seconds (prove: 0.06, print: 0.00, other: 0.02)
|#
(defthmd list-elim-rule 
  (implies (and (true-listp x)
                (natp i)
                (< i (len x)))
           (equal (update-nth i (nth i x) (list-identity2 i x))
                  x))
  :hints (("Goal" :in-theory (e/d (update-nth len nth) (true-listp (tau-system)))))
  :rule-classes :elim)

(defun put-assoc-equal-elim-rule-version (e x)
  "put entry e=(key . value) in its rightful place in alist x"
  (put-assoc-equal (car e) (cdr e) x))

(defun alist-identity2 (a x) 
  "for alist elim rule -- dummy destructor"
  (declare (ignore a))
  x)

(defthm assoc-eq-answer-car 
  (implies (assoc-equal k x) 
           (equal (car (assoc-equal k x)) k)))

(defthmd alist-elim-rule 
  (implies (and (alistp x)
                (assoc-equal k x))
           (equal (put-assoc-equal-elim-rule-version (assoc-equal k x) (alist-identity2 k x))
                  x))
  :rule-classes :elim)

;Following lemmas are needed for record modifier theorems

(defthm mset-non-nil-val-is-consp
  (IMPLIES (AND (not (equal v nil))
                (good-map x)
                (wf-keyp a))
           (consp (MSET A V x)))
  :rule-classes :tau-system
  :hints (("goal" :in-theory (enable mset extensible-records))))


(local (defthm field-not-empty-implies-record-not-empty1
   (implies (and (mget a x)
                 (not (equal a (ill-formed-key))))
            (consp x))
   :hints (("goal" :in-theory (enable mset mget mget-wf mset-wf acl2->map)))
   :rule-classes (:forward-chaining))
   ;               (:rewrite :backchain-limit-lst 1)))
 )


(defthmd mset-diff-entry-non-empty-good-map-is-consp
  (implies (and ;(good-map r)
                (mget a r)
                (wf-keyp a)
                (not (equal a b))) 
           (consp (mset b v r)))
  :hints (("goal" ;:in-theory (disable good-map)
                  :use ((:instance field-not-empty-implies-record-not-empty1
                                   (x (mset b v r))))))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthmd mset-diff-entry-non-empty-good-map-is-non-nil
  (implies (and ;(good-map r)
                (mget a r)
                (wf-keyp a)
                (not (equal a b))) 
           (mset b v r))
  :hints (("goal" ;:in-theory (disable good-map)
                  :use ((:instance mset-diff-entry-non-empty-good-map-is-consp))))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))


(defthm non-empty-good-map-fc
  (implies (good-map v1)
           (and (implies v1 (consp v1))
                (implies  (car v1) (consp (car v1)))))
  :rule-classes :forward-chaining)

; In BAE books, Mitesh found that good-map is being opened up -- it shouldnt!
(in-theory (disable good-map))
