; Copyright (C) 2004, Regents of the University of Texas
; Written by Sol Swords
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.



(in-package "ACL2")

;; (include-book "equal-based-set")
;; (local (include-book "defset-encapsulates"))

(include-book "std/util/deflist" :dir :system)


(defun string-index-measure (idx str)
  (declare (xargs :guard t))
  (if (and (stringp str)
           (natp idx))
      (nfix (+ 1 (length str) (- idx)))
    0))

(defun string-index-end (idx str)
  (declare (xargs :guard (and (stringp str)
                              (natp idx))))
  (or (not (mbt (natp idx)))
      (not (mbt (stringp str)))
      (>= idx (length str))))

(defthm not-string-index-end-characterp
  (implies (not (string-index-end idx str))
           (characterp (char str idx))))


(in-theory (disable char))

(defun string-index-past-end (idx str)
  (declare (xargs :guard (and (stringp str)
                              (natp idx))))
  (or (not (mbt (natp idx)))
      (not (mbt (stringp str)))
      (> idx (length str))))


(defun length-equiv (a b)
  (declare (xargs :guard (and (or (stringp a)
                                  (true-listp a))
                              (or (stringp b)
                                  (true-listp b)))))
  (= (length a)
     (length b)))

(defequiv length-equiv
  :hints (("Goal" :in-theory (disable length))))


(defthm length-equiv-linear
  (implies (length-equiv a b)
           (= (length a)
              (length b)))
  :rule-classes :linear)

(defthm length-equiv-implies
  (implies (length-equiv a b)
           (equal (equal (length a)
                         (length b))
                  t)))

(defthm implies-length-equiv
  (implies (= (length a)
              (length b))
           (equal (length-equiv a b) t)))

(defun indexp (n str)
  (declare (xargs :guard (stringp str)))
  (and (natp n)
       (<= n (length str))))


(defthm indexp-characterp
  (implies (and (stringp str)
                (indexp n str)
                (not (= n (length str))))
           (characterp (char str n))))




(defcong length-equiv equal (indexp n str) 2
  :hints (("Goal" :in-theory (disable length))))



(defun backrefp (x str)
  (declare (xargs :guard (stringp str)))
  (and (consp x)
       (indexp (car x) str)
       (indexp (cdr x) str)
       (<= (car x) (cdr x))))

(defthm backref-ints
  (implies (backrefp x str)
           (and (integerp (car x))
                (integerp (cdr x)))))



(defcong length-equiv equal (backrefp x str) 2
  :hints (("Goal" :in-theory (disable length))))

(defun pseudo-backrefp (x)
  (declare (xargs :guard t))
  (and (consp x)
       (natp (car x))
       (natp (cdr x))))

(defthm backrefp-pseudo
  (implies (backrefp x str)
           (pseudo-backrefp x)))

(defun get-backref-string (br str)
  (declare (xargs :guard (and (stringp str)
                              (backrefp br str))))
  (subseq str (car br) (cdr br)))

(defthm backrefp-stringp
  (implies (and (stringp str)
                (backrefp br str))
           (stringp (get-backref-string br str))))


(defun backref-listp (l str)
  (declare (xargs :guard (stringp str)))
  (if (atom l)
      (equal l nil)
    (and (or (not (car l))
             (backrefp (car l) str))
         (backref-listp (cdr l) str))))


(defthm backref-listp-nth
  (implies (and (backref-listp l str)
                (nth n l))
           (and (consp (nth n l))
                (integerp (car (nth n l)))
                (integerp (cdr (nth n l))))))

(defthm backref-listp-nth-linear
  (implies (and (backref-listp l str)
                (nth n l))
           (and (<= (car (nth n l))
                    (cdr (nth n l)))
                (<= 0 (car (nth n l)))
                (<= 0 (cdr (nth n l)))
                (<= (cdr (nth n l)) (length str))))
  :rule-classes (:rewrite :linear))



(defcong length-equiv equal (backref-listp x str) 2
  :hints (("Goal" :in-theory (disable length length-equiv))))


(defun pseudo-backref-listp (l)
  (declare (xargs :guard t))
  (if (atom l)
      (null l)
    (and (or (not (car l))
             (pseudo-backrefp (car l)))
         (pseudo-backref-listp (cdr l)))))

(defthm pseudo-backref-listp-nth
  (implies (and (pseudo-backref-listp l)
                (nth n l))
           (and (consp (nth n l))
                (integerp (car (nth n l)))
                (integerp (cdr (nth n l))))))


(defthm backref-listp-pseudo
  (implies (backref-listp l str)
           (pseudo-backref-listp l)))

(defthm backref-listp-true-listp
  (implies (backref-listp l str)
           (true-listp l)))


(defun input-list-eltp (x str)
  (declare (xargs :guard (stringp str)))
  (and (consp x)
       (indexp (car x) str)
       (backref-listp (cdr x) str)))

(defthm input-list-eltp-thm
  (implies (input-list-eltp x str)
           (and (integerp (car x))
                (<= 0 (car x))
                (<= (car x) (length str))
                (backref-listp (cdr x) str))))

(defthm input-list-eltp-suffic
  (implies (and (consp x)
                (indexp (car x) str)
                (backref-listp (cdr x) str))
           (input-list-eltp x str)))


(defcong length-equiv equal (input-list-eltp x str) 2
  :hints (("Goal" :in-theory (disable length length-equiv))))

(defun pseudo-input-list-eltp (x)
  (declare (xargs :guard t))
  (and (consp x)
       (natp (car x))
       (pseudo-backref-listp (cdr x))))

(defthm input-list-eltp-pseudo
  (implies (input-list-eltp x str)
           (pseudo-input-list-eltp x)))





(std::deflist input-listp (x str)
              (input-list-eltp x str)
              :guard (stringp str))


(defcong length-equiv equal (input-listp l str) 2
  :hints (("Goal" :in-theory (e/d (input-listp)
                                  (length length-equiv)))))

(std::deflist pseudo-input-listp (x)
              (pseudo-input-list-eltp x))

(defthm input-listp-pseudo
  (implies (input-listp x str)
           (pseudo-input-listp x))
  :hints(("Goal" :in-theory (enable input-listp pseudo-input-listp))))





(defthm backref-listp-update-nth
  (implies (and (backrefp x str)
                (backref-listp brl str))
           (backref-listp (update-nth n x brl) str)))

(defthm pseudo-backref-listp-update-nth
  (implies (and (pseudo-backrefp x)
                (pseudo-backref-listp brl))
           (pseudo-backref-listp (update-nth n x brl))))



;; Functions on input lists

(defun min-idx-il (il str)
  (declare (xargs :guard (and (stringp str)
                              (input-listp il str))))
  (if (atom il)
      (length str)
    (min (caar il)
         (min-idx-il (cdr il) str))))

(defthm min-idx-il-type
  (implies (pseudo-input-listp il)
           (and (integerp (min-idx-il il str))
                (<= 0 (min-idx-il il str))))
  :rule-classes (:rewrite :type-prescription))


(defthm min-idx-il-lte-car
  (implies (and (pseudo-input-listp ilist)
                (consp ilist)
                (stringp str))
           (>= (caar ilist)
               (min-idx-il ilist str))))

(defthm min-idx-il-max
  (<= (min-idx-il l str) (length str))
  :rule-classes (:rewrite :linear))

(defthm member-min-idx
  (implies (member-equal x l)
           (<= (min-idx-il l str) (car x)))
  :rule-classes (:rewrite :linear))

;; (defthm insert-min-idx-il
;;   (<= (min-idx-il (set-insert-equal e l) str)
;;       (min-idx-il l str))
;;   :rule-classes (:rewrite :linear)
;;   :hints (("Goal" :in-theory (enable set-insert-equal))))

;; (defthm insert-min-idx
;;   (<= (min-idx-il (set-insert-equal e l) str)
;;       (car e))
;;   :rule-classes (:rewrite :linear)
;;   :hints (("Goal" :in-theory (enable set-insert-equal))))

;; (defthm insert-min-idx2
;;   (equal (min-idx-il (set-insert-equal e l) str)
;;          (min (car e) (min-idx-il l str)))
;;   :hints (("Goal" :in-theory (enable set-insert-equal))))


(defthm integerp-numberp
  (implies (integerp x)
           (acl2-numberp x)))

(defthm min-idx-append
  (implies (and (pseudo-input-listp a)
                (pseudo-input-listp b)
                (stringp str))
           (equal (min-idx-il (append a b) str)
                  (min (min-idx-il a str) (min-idx-il b str)))))




(defun longest-il (il)
  (declare (xargs :guard (and (consp il)
                              (pseudo-input-listp il))))
  (if (atom (cdr il))
      (car il)
    (let ((l-rest (longest-il (cdr il))))
      (if (>= (caar il) (car l-rest))
          (car il)
        l-rest))))

(defthm longest-il-type-weak
  (implies (and (pseudo-input-listp il)
                (consp il))
           (and (consp (longest-il il))
                (integerp (car (longest-il il)))
                (<= 0 (car (longest-il il)))
                (pseudo-backref-listp (cdr (longest-il il)))))
  :rule-classes (:rewrite :type-prescription))

(defthm longest-il-type-strong
  (implies (and (stringp str)
                (input-listp il str)
                (consp il))
           (and (<= (car (longest-il il)) (length str))
                (backref-listp (cdr (longest-il il)) str))))

(defthm longest-il-max-len
  (implies (and (stringp str)
                (input-listp il str)
                (consp il))
           (<= (car (longest-il il)) (length str)))
  :rule-classes (:rewrite :linear))

(defthm longest-il-min-len
  (implies (and (stringp str)
                (input-listp il str)
                (consp il))
           (<= (min-idx-il il str) (car (longest-il il))))
  :rule-classes (:rewrite :linear))

(defthm longest-il-greater-compare-to-min
  (implies (and (stringp str)
                (input-listp il str)
                (consp il)
                (<= idx (min-idx-il il str)))
           (<= idx (car (longest-il il))))
  :rule-classes (:rewrite :linear))


(defun remove-all-longer-equal-fn (x minidx)
  (declare (xargs :guard (and (integerp minidx)
                              (pseudo-input-list-eltp x))))
  (if (> (car x) minidx)
      (list x)
    nil))

(defun remove-all-longer-equal-il (s minidx)
  (declare (xargs :guard (and (pseudo-input-listp s)
                              (integerp minidx))))
  (if (atom s)
      nil
    (append (remove-all-longer-equal-fn (car s) minidx)
            (remove-all-longer-equal-il (cdr s) minidx))))

;; (prove-set-congruence-of-f remove-all-longer-equal-fn
;;                            :f-on-set remove-all-longer-equal-il
;;                            :equiv equal
;;                            :hard-guard nil
;;                            :additional-param t)


(defthm remove-all-longer-equal-shorter
  (implies (and (integerp minidx)
                (stringp str)
                (< minidx (length str)))
           (> (min-idx-il
               (remove-all-longer-equal-il il minidx) str)
              minidx))
  :rule-classes (:rewrite :linear))

(in-theory (disable length length-equiv))



;; Type theorems about input lists
(defthm remove-all-longer-equal-il-il
  (implies (input-listp l str)
           (input-listp (remove-all-longer-equal-il l maxlen) str)))

(defthm remove-all-longer-equal-il-pseudo
  (implies (pseudo-input-listp l)
           (pseudo-input-listp (remove-all-longer-equal-il l maxlen))))

