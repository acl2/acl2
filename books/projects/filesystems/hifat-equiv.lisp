(in-package "ACL2")

;  hifat-equiv.lisp                                    Mihir Mehta

; Some definitions and theorems for the equivalence relation hifat-equiv.

(include-book "hifat")

(defun
    hifat-subsetp
    (m1-file-alist1 m1-file-alist2)
  (declare
   (xargs
    :guard (and (m1-file-alist-p m1-file-alist1)
                (m1-file-alist-p m1-file-alist2))
    :hints (("goal" :in-theory (enable m1-file->contents
                                       m1-directory-file-p)))))
  (b*
      (((when (atom m1-file-alist1)) t)
       ((unless (mbt (and (consp (car m1-file-alist1))
                          (stringp (car (car m1-file-alist1))))))
        (and (member-equal (car m1-file-alist1)
                           m1-file-alist2)
             (hifat-subsetp (cdr m1-file-alist1)
                            m1-file-alist2)))
       (name (caar m1-file-alist1))
       (file1 (cdar m1-file-alist1))
       ((unless (consp (assoc-equal name m1-file-alist2)))
        nil)
       (file2 (cdr (assoc-equal name m1-file-alist2))))
    (if (not (m1-directory-file-p file1))
        (and (not (m1-directory-file-p file2))
             (hifat-subsetp (cdr m1-file-alist1)
                            m1-file-alist2)
             (equal (m1-file->contents file1)
                    (m1-file->contents file2)))
      (and (m1-directory-file-p file2)
           (hifat-subsetp (cdr m1-file-alist1)
                          m1-file-alist2)
           (hifat-subsetp (m1-file->contents file1)
                          (m1-file->contents file2))))))

(defthm hifat-subsetp-of-remove1-assoc-1
  (implies (and (m1-file-alist-p m1-file-alist1)
                (atom (assoc-equal key m1-file-alist1)))
           (equal (hifat-subsetp m1-file-alist1
                                 (remove1-assoc key m1-file-alist2))
                  (hifat-subsetp m1-file-alist1 m1-file-alist2))))

(defthm
  hifat-no-dups-p-of-remove1-assoc-equal
  (implies
   (hifat-no-dups-p m1-file-alist)
   (hifat-no-dups-p (remove1-assoc-equal key m1-file-alist)))
  :hints (("Goal" :in-theory (enable hifat-no-dups-p))))

(defthm hifat-subsetp-preserves-assoc-equal
  (implies (and (hifat-subsetp x y)
                (stringp file)
                (consp (assoc-equal file x)))
           (consp (assoc-equal file y))))

(defthm
  hifat-subsetp-transitive-lemma-1
  (implies
   (and (m1-file-alist-p y)
        (consp (assoc-equal key y))
        (hifat-subsetp y z))
   (iff (m1-directory-file-p (cdr (assoc-equal key z)))
        (m1-directory-file-p (cdr (assoc-equal key y)))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (m1-file-alist-p y)
          (consp (assoc-equal key y))
          (hifat-subsetp y z)
          (m1-directory-file-p (cdr (assoc-equal key y))))
     (m1-directory-file-p (cdr (assoc-equal key z)))))))

(local
 (defthm
   hifat-subsetp-transitive-lemma-2
   (implies
    (and (m1-file-alist-p y)
         (consp (assoc-equal key y))
         (not (m1-directory-file-p (cdr (assoc-equal key y))))
         (hifat-subsetp y z))
    (equal (m1-file->contents (cdr (assoc-equal key y)))
           (m1-file->contents (cdr (assoc-equal key z)))))))

(defthm
  hifat-subsetp-transitive-lemma-3
  (implies (and (m1-file-alist-p y)
                (m1-directory-file-p (cdr (assoc-equal key y)))
                (hifat-subsetp y z))
           (hifat-subsetp (m1-file->contents (cdr (assoc-equal key y)))
                          (m1-file->contents (cdr (assoc-equal key z))))))

(encapsulate
  () ;; start lemmas for hifat-subsetp-transitive

  (local
   (defthm
     hifat-subsetp-transitive-lemma-4
     (implies
      (and (not (m1-directory-file-p (cdr (assoc-equal (car (car x)) y))))
           (consp (assoc-equal (car (car x)) y))
           (hifat-subsetp y z)
           (m1-file-alist-p y))
      (not (m1-directory-file-p (cdr (assoc-equal (car (car x)) z)))))
     :hints (("goal" :in-theory (disable hifat-subsetp-transitive-lemma-1)
              :use (:instance hifat-subsetp-transitive-lemma-1
                              (key (car (car x))))))))

  (local
   (defthm
     hifat-subsetp-transitive-lemma-5
     (implies (and (m1-directory-file-p (cdr (assoc-equal (car (car x)) y)))
                   (hifat-subsetp y z)
                   (m1-file-alist-p y))
              (m1-directory-file-p (cdr (assoc-equal (car (car x)) z))))
     :hints (("goal" :in-theory (disable hifat-subsetp-transitive-lemma-1)
              :use (:instance hifat-subsetp-transitive-lemma-1
                              (key (car (car x))))))))

  (local
   (defthm
     hifat-subsetp-transitive-lemma-6
     (implies (and (not (stringp (car (car x))))
                   (m1-file-alist-p y))
              (not
               (member-equal (car x) y)))
     :hints (("goal" :in-theory (enable m1-file-alist-p)))))

 (defthm hifat-subsetp-transitive
   (implies (and (hifat-subsetp x y)
                 (hifat-subsetp y z)
                 (m1-file-alist-p y))
            (hifat-subsetp x z))))

(defthm
  hifat-subsetp-when-atom
  (implies (atom m1-file-alist2)
           (equal (hifat-subsetp m1-file-alist1 m1-file-alist2)
                  (atom m1-file-alist1))))

(defthm hifat-subsetp-reflexive-lemma-1
  (implies (and (m1-file-alist-p x)
                (hifat-no-dups-p (append x y)))
           (equal (assoc-equal (car (car y)) (append x y))
                  (car y)))
  :hints (("Goal" :in-theory (enable hifat-no-dups-p)) ))

(defthm hifat-subsetp-reflexive-lemma-2
  (implies (not (hifat-no-dups-p y))
           (not (hifat-no-dups-p (append x y))))
  :hints (("Goal" :in-theory (enable hifat-no-dups-p)) ))

(defthm hifat-subsetp-reflexive-lemma-3
  (implies (and (m1-file-alist-p y)
                (hifat-no-dups-p y)
                (m1-directory-file-p (cdr (car y))))
           (hifat-no-dups-p (m1-file->contents (cdr (car y)))))
  :hints (("Goal" :in-theory (enable hifat-no-dups-p)) ))

(encapsulate
  ()

  (local
   (defun
       induction-scheme (x y)
     (declare
      (xargs
       :hints
       (("goal" :in-theory (enable m1-file->contents
                                   m1-file-contents-fix)))))
     (if
         (atom y)
         x
       (append
        (induction-scheme nil (m1-file->contents (cdr (car y))))
        (induction-scheme (append x (list (car y)))
                          (cdr y))))))

  (defthm hifat-subsetp-reflexive-lemma-4
    (implies (and (m1-file-alist-p x)
                  (m1-file-alist-p y)
                  (hifat-no-dups-p (append x y)))
             (hifat-subsetp y (append x y)))
    :hints (("goal" :induct (induction-scheme x y)
             :in-theory (enable hifat-no-dups-p)))))

(defthm
  hifat-subsetp-reflexive-lemma-5
  (implies
   (m1-file-p file)
   (equal (m1-directory-file-p
           (m1-file dir-ent (m1-file->contents file)))
          (m1-directory-file-p file)))
  :hints (("goal" :in-theory (enable m1-directory-file-p))))

(defthm
  hifat-subsetp-reflexive
  (implies (and (m1-file-alist-p y)
                (hifat-no-dups-p y))
           (hifat-subsetp y y))
  :hints
  (("goal"
    :in-theory
    (disable hifat-subsetp-reflexive-lemma-4)
    :use (:instance hifat-subsetp-reflexive-lemma-4
                    (x nil)))))

(defund hifat-equiv (m1-file-alist1 m1-file-alist2)
  (declare (xargs :guard (and (m1-file-alist-p m1-file-alist1)
                              (hifat-no-dups-p m1-file-alist1)
                              (m1-file-alist-p m1-file-alist2)
                              (hifat-no-dups-p m1-file-alist2))))
  (b* ((m1-file-alist1 (hifat-file-alist-fix m1-file-alist1))
       (m1-file-alist2 (hifat-file-alist-fix m1-file-alist2)))
    (and (hifat-subsetp m1-file-alist1 m1-file-alist2)
         (hifat-subsetp m1-file-alist2 m1-file-alist1))))

;; A bug was here: after we changed the definition of hifat-equiv, we placed
;; this defequiv form somewhat later in the file, with the result that two
;; rules which should have rewritten in an hifat-equiv context instead began
;; to rewrite in an equal context. Moving this defequiv form up here fixed the
;; issue.
(defequiv hifat-equiv
  :hints (("goal" :in-theory (enable hifat-equiv))))

(defthm
  hifat-equiv-of-cons-lemma-1
  (implies
   (and (m1-file-alist-p fs)
        (hifat-no-dups-p fs)
        (m1-regular-file-p (cdar fs)))
   (hifat-equiv (cons (cons (caar fs)
                            (m1-file dir-ent (m1-file->contents (cdar fs))))
                      (cdr fs))
                fs))
  :hints
  (("goal"
    :expand
    (hifat-equiv (cons (cons (caar fs)
                             (m1-file dir-ent (m1-file->contents (cdar fs))))
                       (cdr fs))
                 fs)
    :in-theory (e/d (hifat-no-dups-p)
                    (hifat-subsetp-reflexive-lemma-4))
    :use
    ((:instance hifat-subsetp-reflexive-lemma-4
                (x (list (cons (car (car fs))
                               (m1-file dir-ent
                                        (m1-file->contents (cdr (car fs)))))))
                (y (cdr fs)))
     (:instance hifat-subsetp-reflexive-lemma-4
                (x (list (car fs)))
                (y (cdr fs)))))))

(defthm
  hifat-equiv-of-cons-lemma-2
  (implies (and (fat32-filename-p (car head))
                (m1-regular-file-p (cdr head))
                (equal contents (m1-file->contents (cdr head)))
                (m1-file-alist-p tail)
                (hifat-no-dups-p (cons head tail)))
           (hifat-equiv (cons (cons (car head)
                                    (m1-file dir-ent contents))
                              tail)
                        (cons head tail)))
  :hints
  (("goal"
    :in-theory
    (disable hifat-equiv-of-cons-lemma-1)
    :use (:instance hifat-equiv-of-cons-lemma-1
                    (fs (cons head tail))))))

(defthm
  hifat-equiv-of-cons-lemma-3
  (implies (and (m1-directory-file-p (cdr head))
                (m1-file-alist-p (cons head tail))
                (hifat-no-dups-p (cons head tail))
                (hifat-no-dups-p contents)
                (hifat-equiv (m1-file->contents (cdr head))
                             contents)
                (m1-file-alist-p contents))
           (hifat-equiv (cons (cons (car head)
                                    (m1-file dir-ent contents))
                              tail)
                        (cons head tail)))
  :hints
  (("goal"
    :expand ((hifat-equiv (cons (cons (car head)
                                      (m1-file dir-ent contents))
                                tail)
                          (cons head tail))
             (hifat-equiv (m1-file->contents (cdr head))
                          contents))
    :in-theory
    (e/d (hifat-no-dups-p)
         (hifat-subsetp-reflexive-lemma-4 m1-directory-file-p-of-m1-file))
    :use ((:instance hifat-subsetp-reflexive-lemma-4
                     (x (list head))
                     (y tail))
          (:instance hifat-subsetp-reflexive-lemma-4
                     (x (list (cons (car head)
                                    (m1-file dir-ent contents))))
                     (y tail))
          (:instance m1-directory-file-p-of-m1-file
                     (contents contents)
                     (dir-ent dir-ent))))))

(local
 (defthm hifat-equiv-of-cons-lemma-4
   (implies (and (not (assoc-equal (car head) tail1))
                 (hifat-subsetp tail2 tail1)
                 (fat32-filename-p (car head)))
            (not (assoc-equal (car head) tail2)))))

(defthm hifat-equiv-of-cons-lemma-5
  (implies (and (hifat-no-dups-p (cons head tail1))
                (hifat-subsetp tail2 tail1))
           (hifat-subsetp tail2 (cons head tail1)))
  :hints (("Goal" :in-theory (enable hifat-no-dups-p)) ))

;; This rule had a problem earlier - no loop-stopper could be defined on it,
;; because it was an hifat-equiv rule, not an equal rule. Without a
;; loop-stopper, we were going round and round in a big induction proof. By
;; explicitly stipulating equality as the equivalence relation, we get around
;; this.
(defthm
  hifat-equiv-of-cons
  (implies (hifat-equiv tail1 tail2)
           (equal (hifat-equiv (cons head tail1)
                               (cons head tail2))
                  t))
  :hints
  (("goal" :in-theory (e/d (hifat-equiv hifat-no-dups-p))
    :expand (hifat-file-alist-fix (cons head tail1)))))
