(in-package "ACL2")

;  m1-dir-equiv.lisp                                   Mihir Mehta

; Some definitions and theorems for the equivalence relation m1-dir-equiv.

(include-book "file-system-m1")

(defun
  m1-dir-subsetp
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
             (m1-dir-subsetp (cdr m1-file-alist1)
                             m1-file-alist2)))
       (name (caar m1-file-alist1))
       (file1 (cdar m1-file-alist1))
       ((unless (consp (assoc-equal name m1-file-alist2)))
        nil)
       (file2 (cdr (assoc-equal name m1-file-alist2))))
    (if (not (m1-directory-file-p file1))
        (and (not (m1-directory-file-p file2))
             (m1-dir-subsetp (cdr m1-file-alist1)
                             m1-file-alist2)
             (equal (m1-file->contents file1)
                    (m1-file->contents file2)))
        (and (m1-directory-file-p file2)
             (m1-dir-subsetp (cdr m1-file-alist1)
                             m1-file-alist2)
             (m1-dir-subsetp (m1-file->contents file1)
                             (m1-file->contents file2))))))

(defun
  m1-file-no-dups-p (m1-file-alist)
  (declare (xargs :guard (m1-file-alist-p m1-file-alist)))
  (cond ((atom m1-file-alist) t)
        ((not (m1-file-no-dups-p (cdr m1-file-alist)))
         nil)
        ((not (mbt (and (consp (car m1-file-alist))
                        (stringp (car (car m1-file-alist))))))
         (not (member-equal (car m1-file-alist)
                            (cdr m1-file-alist))))
        ((assoc-equal (caar m1-file-alist)
                      (cdr m1-file-alist))
         nil)
        ((m1-directory-file-p (cdar m1-file-alist))
         (m1-file-no-dups-p
          (m1-file->contents (cdar m1-file-alist))))
        (t t)))

(defthm m1-file-no-dups-p-correctness-1
  (implies (m1-file-no-dups-p fs)
           (m1-file-no-dups-p (cdr fs)))
  :hints (("goal" :do-not-induct t)))

(defthm m1-dir-subsetp-of-remove1-assoc-1
  (implies (and (m1-file-alist-p m1-file-alist1)
                (atom (assoc-equal key m1-file-alist1)))
           (equal (m1-dir-subsetp m1-file-alist1
                                  (remove1-assoc key m1-file-alist2))
                  (m1-dir-subsetp m1-file-alist1 m1-file-alist2))))

(defthm
  m1-file-no-dups-p-of-remove1-assoc-equal
  (implies
   (m1-file-no-dups-p m1-file-alist)
   (m1-file-no-dups-p (remove1-assoc-equal key m1-file-alist))))

(defthm m1-dir-subsetp-preserves-assoc-equal
  (implies (and (m1-dir-subsetp x y)
                (stringp file)
                (consp (assoc-equal file x)))
           (consp (assoc-equal file y))))

(defthm
  m1-dir-subsetp-transitive-lemma-1
  (implies
   (and (m1-file-alist-p y)
        (consp (assoc-equal key y))
        (m1-dir-subsetp y z))
   (iff (m1-directory-file-p (cdr (assoc-equal key z)))
        (m1-directory-file-p (cdr (assoc-equal key y)))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (m1-file-alist-p y)
          (consp (assoc-equal key y))
          (m1-dir-subsetp y z)
          (m1-directory-file-p (cdr (assoc-equal key y))))
     (m1-directory-file-p (cdr (assoc-equal key z)))))))

(defthm
  m1-dir-subsetp-transitive-lemma-2
  (implies (and (m1-file-alist-p z)
                (m1-file-no-dups-p z)
                (m1-directory-file-p (cdr (assoc-equal key z))))
           (m1-file-no-dups-p (m1-file->contents (cdr (assoc-equal key z))))))

(defthm
  m1-dir-subsetp-transitive-lemma-3
  (implies (and (m1-file-alist-p y)
                (m1-directory-file-p (cdr (assoc-equal key y)))
                (m1-dir-subsetp y z))
           (m1-dir-subsetp (m1-file->contents (cdr (assoc-equal key y)))
                           (m1-file->contents (cdr (assoc-equal key z))))))

(defthm
  m1-dir-subsetp-transitive-lemma-4
  (implies
   (and (m1-file-alist-p y)
        (consp (assoc-equal key y))
        (not (m1-directory-file-p (cdr (assoc-equal key y))))
        (m1-dir-subsetp y z))
   (equal (m1-file->contents (cdr (assoc-equal key y)))
          (m1-file->contents (cdr (assoc-equal key z))))))

(defthm
  m1-dir-subsetp-transitive
  (implies (and (m1-file-alist-p x)
                (m1-file-alist-p y)
                (m1-file-alist-p z)
                (m1-dir-subsetp x y)
                (m1-dir-subsetp y z))
           (m1-dir-subsetp x z))
  :hints
  (("Goal"
    :induct (mv (m1-dir-subsetp x z) (m1-dir-subsetp x y)))
   ("subgoal *1/5" :in-theory (disable m1-dir-subsetp-transitive-lemma-1)
    :use (:instance m1-dir-subsetp-transitive-lemma-1
                    (key (car (car x)))))
   ("subgoal *1/2" :in-theory (disable m1-dir-subsetp-transitive-lemma-1)
    :use (:instance m1-dir-subsetp-transitive-lemma-1
                    (key (car (car x)))))))

(defthm
  m1-dir-subsetp-when-atom
  (implies (atom m1-file-alist2)
           (equal (m1-dir-subsetp m1-file-alist1 m1-file-alist2)
                  (atom m1-file-alist1))))

(defthm m1-dir-subsetp-reflexive-lemma-1
  (implies (and (m1-file-alist-p x)
                (m1-file-no-dups-p (append x y)))
           (equal (assoc-equal (car (car y)) (append x y))
                  (car y))))

(defthm m1-dir-subsetp-reflexive-lemma-2
  (implies (not (m1-file-no-dups-p y))
           (not (m1-file-no-dups-p (append x y)))))

(defthm m1-dir-subsetp-reflexive-lemma-3
  (implies (and (m1-file-alist-p y)
                (m1-file-no-dups-p y)
                (m1-directory-file-p (cdr (car y))))
           (m1-file-no-dups-p (m1-file->contents (cdr (car y))))))

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

  (defthm m1-dir-subsetp-reflexive-lemma-4
    (implies (and (m1-file-alist-p x)
                  (m1-file-alist-p y)
                  (m1-file-no-dups-p (append x y)))
             (m1-dir-subsetp y (append x y)))
    :hints (("goal" :induct (induction-scheme x y)))))

(defthm
  m1-dir-subsetp-reflexive-lemma-5
  (implies
   (m1-file-p file)
   (equal (m1-directory-file-p
           (m1-file dir-ent (m1-file->contents file)))
          (m1-directory-file-p file)))
  :hints (("goal" :in-theory (enable m1-directory-file-p))))

(defthm
  m1-dir-subsetp-reflexive
  (implies (and (m1-file-alist-p y)
                (m1-file-no-dups-p y))
           (m1-dir-subsetp y y))
  :hints
  (("goal"
    :in-theory
    (disable m1-dir-subsetp-reflexive-lemma-4)
    :use (:instance m1-dir-subsetp-reflexive-lemma-4
                    (x nil)))))

(defund m1-dir-equiv (m1-file-alist1 m1-file-alist2)
  (declare (xargs :guard (and (m1-file-alist-p m1-file-alist1)
                              (m1-file-alist-p m1-file-alist2))))
  (b* ((good1 (and (mbt (m1-file-alist-p m1-file-alist1))
                   (m1-file-no-dups-p m1-file-alist1)))
       (good2 (and (mbt (m1-file-alist-p m1-file-alist2))
                   (m1-file-no-dups-p m1-file-alist2)))
       ((unless (and good1 good2)) (and (not good1) (not good2))))
    (and (m1-dir-subsetp m1-file-alist1 m1-file-alist2)
         (m1-dir-subsetp m1-file-alist2 m1-file-alist1))))

(defthm m1-dir-equiv-of-nil
  (and
   (equal (m1-dir-equiv m1-file-alist nil)
          (null m1-file-alist))
   (equal (m1-dir-equiv nil m1-file-alist)
          (null m1-file-alist)))
  :hints (("Goal" :in-theory (enable m1-dir-equiv))))

;; A bug was here: after we changed the definition of m1-dir-equiv, we placed
;; this defequiv form somewhat later in the file, with the result that two
;; rules which should have rewritten in an m1-dir-equiv context instead began
;; to rewrite in an equal context. Moving this defequiv form up here fixed the
;; issue.
(defequiv m1-dir-equiv
  :hints (("Goal" :in-theory (enable m1-dir-equiv))))

(defthm
  m1-dir-equiv-of-cons-lemma-1
  (implies
   (and (m1-file-alist-p fs)
        (m1-regular-file-p (cdar fs)))
   (m1-dir-equiv
    (cons (cons (caar fs)
                (m1-file dir-ent (m1-file->contents (cdar fs))))
          (cdr fs))
    fs))
  :hints
  (("goal"
    :expand
    (m1-dir-equiv
     (cons
      (cons (caar fs)
            (m1-file dir-ent (m1-file->contents (cdar fs))))
      (cdr fs))
     fs)
    :in-theory
    (disable m1-dir-subsetp-reflexive-lemma-4)
    :use
    ((:instance
      m1-dir-subsetp-reflexive-lemma-4
      (x
       (list
        (cons (car (car fs))
              (m1-file dir-ent
                       (m1-file->contents (cdr (car fs)))))))
      (y (cdr fs)))
     (:instance m1-dir-subsetp-reflexive-lemma-4
                (x (list (car fs)))
                (y (cdr fs)))))))

(defthm
  m1-dir-equiv-of-cons-lemma-2
  (implies (and (fat32-filename-p (car head))
                (m1-regular-file-p (cdr head))
                (equal contents (m1-file->contents (cdr head)))
                (m1-file-alist-p tail))
           (m1-dir-equiv (cons (cons (car head)
                                     (m1-file dir-ent contents))
                               tail)
                         (cons head tail)))
  :hints
  (("goal"
    :in-theory
    (disable m1-dir-equiv-of-cons-lemma-1)
    :use (:instance m1-dir-equiv-of-cons-lemma-1
                    (fs (cons head tail))))))

(local
 (defthm
   m1-dir-equiv-of-cons-lemma-3
   (implies (and (m1-file-alist-p contents1)
                 (m1-file-no-dups-p contents1)
                 (not (m1-file-no-dups-p (m1-file-contents-fix contents2))))
            (not (m1-dir-equiv contents1 contents2)))
   :hints (("goal" :expand (m1-dir-equiv contents1 contents2)))))

(local
 (defthm
   m1-dir-equiv-of-cons-lemma-4
   (implies (and (m1-file-alist-p contents1)
                 (m1-file-no-dups-p contents1)
                 (not (m1-dir-subsetp contents1
                                      (m1-file-contents-fix contents2))))
            (not (m1-dir-equiv contents1 contents2)))
   :hints (("goal" :expand (m1-dir-equiv contents1 contents2)))))

(local
 (defthm
   m1-dir-equiv-of-cons-lemma-5
   (implies
    (and (m1-file-alist-p contents1)
         (m1-file-no-dups-p contents1)
         (not (m1-dir-subsetp (m1-file-contents-fix contents2)
                              contents1)))
    (not (m1-dir-equiv contents1 contents2)))
   :hints (("goal" :expand (m1-dir-equiv contents1 contents2)))))

(local
 (defthm
   m1-dir-equiv-of-cons-lemma-6
   (implies (and (m1-file-alist-p contents1)
                 (m1-file-no-dups-p contents1)
                 (not (m1-file-alist-p contents2)))
            (not (m1-dir-equiv contents1 contents2)))
   :hints (("goal" :expand (m1-dir-equiv contents1 contents2)))))

(defthm
  m1-dir-equiv-of-cons-lemma-7
  (implies (and (m1-directory-file-p (cdr head))
                (m1-file-no-dups-p (m1-file->contents (cdr head)))
                (m1-dir-equiv (m1-file->contents (cdr head))
                              contents))
           (m1-dir-equiv (cons (cons (car head)
                                     (m1-file dir-ent contents))
                               tail)
                         (cons head tail)))
  :hints
  (("goal" :expand (m1-dir-equiv (cons (cons (car head)
                                             (m1-file dir-ent contents))
                                       tail)
                                 (cons head tail))
    :in-theory (disable m1-dir-subsetp-reflexive-lemma-4
                        m1-directory-file-p-of-m1-file)
    :use ((:instance m1-dir-subsetp-reflexive-lemma-4
                     (x (list head))
                     (y tail))
          (:instance m1-dir-subsetp-reflexive-lemma-4
                     (x (list (cons (car head)
                                    (m1-file dir-ent contents))))
                     (y tail))
          (:instance m1-directory-file-p-of-m1-file
                     (contents contents)
                     (dir-ent dir-ent))))))

(defthm m1-dir-equiv-of-cons-lemma-8
  (implies (and (not (assoc-equal (car head) tail1))
                (m1-dir-subsetp tail2 tail1)
                (fat32-filename-p (car head)))
           (not (assoc-equal (car head) tail2))))

(defthm m1-dir-equiv-of-cons-lemma-9
  (implies (and (m1-file-no-dups-p (cons head tail1))
                (m1-dir-subsetp tail2 tail1))
           (m1-dir-subsetp tail2 (cons head tail1))))

;; This rule had a problem earlier - no loop-stopper could be defined on it,
;; because it was an m1-dir-equiv rule, not an equal rule. Without a
;; loop-stopper, we were going round and round in a big induction proof. By
;; explicitly stipulating equality as the equivalence relation, we get around
;; this.
(defthm m1-dir-equiv-of-cons
  (implies (m1-dir-equiv tail1 tail2)
           (equal
            (m1-dir-equiv (cons head tail1)
                          (cons head tail2))
            t))
  :hints (("goal" :in-theory (e/d (m1-dir-equiv) (m1-file-no-dups-p))
           :expand ((m1-file-no-dups-p (cons head tail2))
                    (m1-file-no-dups-p (cons head tail1))))))
