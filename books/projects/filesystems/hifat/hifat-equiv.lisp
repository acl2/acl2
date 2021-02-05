(in-package "ACL2")

;  hifat-equiv.lisp                                    Mihir Mehta

; Some definitions and theorems for the equivalence relation hifat-equiv.

(include-book "../hifat")

(defund
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
                  (hifat-subsetp m1-file-alist1 m1-file-alist2)))
  :hints (("Goal" :in-theory (enable
                              hifat-subsetp))))

(defthm
  hifat-no-dups-p-of-remove1-assoc-equal
  (implies
   (hifat-no-dups-p m1-file-alist)
   (hifat-no-dups-p (remove1-assoc-equal key m1-file-alist)))
  :hints (("Goal" :in-theory (enable hifat-no-dups-p))))

(defthm hifat-subsetp-preserves-assoc
  (implies (and (hifat-subsetp x y)
                (stringp file)
                (consp (assoc-equal file x)))
           (consp (assoc-equal file y)))
  :hints (("Goal" :in-theory (enable
                              hifat-subsetp))))

;; This can't be made local.
(defthm
  hifat-subsetp-transitive-lemma-1
  (implies
   (and (m1-file-alist-p y)
        (consp (assoc-equal key y))
        (hifat-subsetp y z))
   (iff (m1-directory-file-p (cdr (assoc-equal key z)))
        (m1-directory-file-p (cdr (assoc-equal key y)))))
  :hints (("Goal" :in-theory (enable
                              hifat-subsetp)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (hifat-subsetp y z)
          (m1-file-alist-p y)
          (consp (assoc-equal key y))
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
           (m1-file->contents (cdr (assoc-equal key z)))))
  :hints (("Goal" :in-theory (enable
                              hifat-subsetp)))))

(defthm
  hifat-subsetp-transitive-lemma-3
  (implies (and (m1-file-alist-p y)
                (m1-directory-file-p (cdr (assoc-equal key y)))
                (hifat-subsetp y z))
           (hifat-subsetp (m1-file->contents (cdr (assoc-equal key y)))
                          (m1-file->contents (cdr (assoc-equal key z)))))
  :hints (("Goal" :in-theory (enable
                              hifat-subsetp))))

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
            (hifat-subsetp x z))
   :hints (("Goal" :in-theory (enable
                               hifat-subsetp)))))

(defthm
  hifat-subsetp-when-atom
  (implies (atom m1-file-alist2)
           (equal (hifat-subsetp m1-file-alist1 m1-file-alist2)
                  (atom m1-file-alist1)))
  :hints (("Goal" :in-theory (enable
                              hifat-subsetp))))

(local
 (defthm hifat-subsetp-reflexive-lemma-1
   (implies (and (m1-file-alist-p x)
                 (hifat-no-dups-p (append x y)))
            (equal (assoc-equal (car (car y)) (append x y))
                   (car y)))
   :hints (("Goal" :in-theory (enable hifat-no-dups-p)) )))

(local
 (defthm hifat-subsetp-reflexive-lemma-2
   (implies (not (hifat-no-dups-p y))
            (not (hifat-no-dups-p (append x y))))
   :hints (("Goal" :in-theory (enable hifat-no-dups-p)) )))

;; This can't be made local.
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
             :in-theory (enable hifat-no-dups-p hifat-subsetp)))))

(defthm
  hifat-subsetp-reflexive-lemma-5
  (implies
   (m1-file-p file)
   (equal (m1-directory-file-p
           (m1-file d-e (m1-file->contents file)))
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

(defund hifat-equiv (fs1 fs2)
  (declare (xargs :guard (and (m1-file-alist-p fs1)
                              (hifat-no-dups-p fs1)
                              (m1-file-alist-p fs2)
                              (hifat-no-dups-p fs2))))
  (let ((fs1 (hifat-file-alist-fix fs1))
        (fs2 (hifat-file-alist-fix fs2)))
    (and (hifat-subsetp fs1 fs2)
         (hifat-subsetp fs2 fs1))))

;; A bug was here: after we changed the definition of hifat-equiv, we placed
;; this defequiv form somewhat later in the file, with the result that two
;; rules which should have rewritten in an hifat-equiv context instead began
;; to rewrite in an equal context. Moving this defequiv form up here fixed the
;; issue.
(defequiv hifat-equiv
  :hints (("goal" :in-theory (enable hifat-equiv))))

(defthm consp-of-assoc-when-hifat-equiv-lemma-1
  (implies (and (not (consp (assoc-equal name m1-file-alist2)))
                (m1-file-alist-p m1-file-alist1)
                (hifat-subsetp m1-file-alist1 m1-file-alist2))
           (not (consp (assoc-equal name m1-file-alist1))))
  :hints (("goal" :in-theory (enable hifat-subsetp m1-file-alist-p))))

(defthm
  consp-of-assoc-when-hifat-equiv
  (implies (hifat-equiv x y)
           (equal (consp (assoc-equal (fat32-filename-fix name)
                                      (hifat-file-alist-fix x)))
                  (consp (assoc-equal (fat32-filename-fix name)
                                      (hifat-file-alist-fix y)))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (hifat-equiv)
                           (hifat-subsetp-preserves-assoc))
           :use ((:instance hifat-subsetp-preserves-assoc
                            (x (hifat-file-alist-fix x))
                            (y (hifat-file-alist-fix y))
                            (file (fat32-filename-p name)))
                 (:instance hifat-subsetp-preserves-assoc
                            (x (hifat-file-alist-fix y))
                            (y (hifat-file-alist-fix x))
                            (file (fat32-filename-p name))))
           :cases ((consp (assoc-equal (fat32-filename-fix name)
                                       (hifat-file-alist-fix x))))))
  :rule-classes
  :congruence)

(defthm
  hifat-equiv-of-cons-lemma-1
  (implies
   (and (m1-file-alist-p fs)
        (hifat-no-dups-p fs)
        (m1-regular-file-p (cdar fs)))
   (hifat-equiv (cons (cons (caar fs)
                            (m1-file d-e (m1-file->contents (cdar fs))))
                      (cdr fs))
                fs))
  :hints
  (("goal"
    :expand
    (hifat-equiv (cons (cons (caar fs)
                             (m1-file d-e (m1-file->contents (cdar fs))))
                       (cdr fs))
                 fs)
    :in-theory (e/d (hifat-no-dups-p hifat-subsetp)
                    (hifat-subsetp-reflexive-lemma-4 m1-directory-file-p-of-m1-file))
    :use
    ((:instance hifat-subsetp-reflexive-lemma-4
                (x (list (cons (car (car fs))
                               (m1-file d-e
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
                                    (m1-file d-e contents))
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
                                    (m1-file d-e contents))
                              tail)
                        (cons head tail)))
  :hints
  (("goal"
    :expand ((hifat-equiv (cons (cons (car head)
                                      (m1-file d-e contents))
                                tail)
                          (cons head tail))
             (hifat-equiv (m1-file->contents (cdr head))
                          contents))
    :in-theory
    (e/d (hifat-no-dups-p hifat-subsetp)
         (hifat-subsetp-reflexive-lemma-4 m1-directory-file-p-of-m1-file))
    :use ((:instance hifat-subsetp-reflexive-lemma-4
                     (x (list head))
                     (y tail))
          (:instance hifat-subsetp-reflexive-lemma-4
                     (x (list (cons (car head)
                                    (m1-file d-e contents))))
                     (y tail))
          (:instance m1-directory-file-p-of-m1-file
                     (contents contents)
                     (d-e d-e))))))

(defthmd hifat-equiv-of-cons-lemma-4
  (implies (and (hifat-no-dups-p (cons head tail1))
                (hifat-subsetp tail2 tail1))
           (hifat-subsetp tail2 (cons head tail1)))
  :hints (("Goal" :in-theory (enable hifat-no-dups-p hifat-subsetp)) ))

(local (in-theory (enable hifat-equiv-of-cons-lemma-4)))

;; This rule had a problem earlier - no loop-stopper could be defined on it,
;; because it was an hifat-equiv rule, not an equal rule. Without a
;; loop-stopper, we were going round and round in a big induction proof. By
;; explicitly stipulating equality as the equivalence relation, we get around
;; this.
;;
;; OK, another problem this rule had earlier - it was a rewrite rule instead of
;; a congruence, and therefore supremely unwieldy!
(defthm
  hifat-equiv-of-cons
  (implies (hifat-equiv tail1 tail2)
           (hifat-equiv (cons head tail1)
                        (cons head tail2)))
  :hints
  (("goal"
    :in-theory
    (e/d (hifat-equiv hifat-no-dups-p
                      hifat-file-alist-fix hifat-subsetp))
    :expand (hifat-file-alist-fix (cons head tail1))))
  :rule-classes :congruence)

(defthm hifat-equiv-implies-set-equiv-strip-cars-1-lemma-1
  (implies (and (member-equal a x) (null (car a)))
           (member-equal nil (strip-cars x))))

(defthm hifat-equiv-implies-set-equiv-strip-cars-1-lemma-2
  (implies (hifat-subsetp fs1 fs2)
           (subsetp-equal (strip-cars fs1)
                          (strip-cars fs2)))
  :hints (("goal" :in-theory (enable hifat-subsetp))))

(defthm
  hifat-equiv-implies-set-equiv-strip-cars-1
  (implies (hifat-equiv fs1 fs2)
           (set-equiv (fat32-filename-list-fix (strip-cars fs1))
                      (fat32-filename-list-fix (strip-cars fs2))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (hifat-equiv set-equiv)
                    (hifat-equiv-implies-set-equiv-strip-cars-1-lemma-2))
    :use ((:instance hifat-equiv-implies-set-equiv-strip-cars-1-lemma-2
                     (fs1 (hifat-file-alist-fix fs1))
                     (fs2 (hifat-file-alist-fix fs2)))
          (:instance hifat-equiv-implies-set-equiv-strip-cars-1-lemma-2
                     (fs2 (hifat-file-alist-fix fs1))
                     (fs1 (hifat-file-alist-fix fs2))))))
  :rule-classes :congruence)

(defthm
  put-assoc-under-hifat-equiv-1
  (implies (and (hifat-equiv (m1-file->contents file1)
                             (m1-file->contents file2))
                (syntaxp (not (term-order file1 file2)))
                (m1-directory-file-p (m1-file-fix file1))
                (m1-directory-file-p (m1-file-fix file2)))
           (hifat-equiv (put-assoc-equal name file1 fs)
                        (put-assoc-equal name file2 fs)))
  :hints
  (("goal"
    :induct (mv (put-assoc-equal name file1 fs)
                (put-assoc-equal name file2 fs))
    :in-theory
    (e/d (hifat-no-dups-p hifat-equiv hifat-file-alist-fix hifat-subsetp)
         (hifat-subsetp-reflexive-lemma-4
          (:rewrite hifat-file-alist-fix-when-hifat-no-dups-p))))
   ("subgoal *1/2"
    :use
    (:instance
     hifat-subsetp-reflexive-lemma-4
     (x
      (list
       (cons (fat32-filename-fix (car (car fs)))
             (m1-file (m1-file->d-e file1)
                      (hifat-file-alist-fix (m1-file->contents file1))))))
     (y (hifat-file-alist-fix (cdr fs)))))))

(defthm
  put-assoc-under-hifat-equiv-3
  (implies (and (equal (m1-file->contents file1)
                       (m1-file->contents file2))
                (syntaxp (not (term-order file1 file2)))
                (m1-regular-file-p (m1-file-fix file1))
                (m1-regular-file-p (m1-file-fix file2)))
           (hifat-equiv (put-assoc-equal name file1 fs)
                        (put-assoc-equal name file2 fs)))
  :hints
  (("goal"
    :induct (mv (put-assoc-equal name file1 fs)
                (put-assoc-equal name file2 fs))
    :in-theory
    (e/d (hifat-no-dups-p hifat-equiv hifat-file-alist-fix hifat-subsetp)
         (hifat-subsetp-reflexive-lemma-4
          (:rewrite hifat-file-alist-fix-when-hifat-no-dups-p))))
   ("subgoal *1/2"
    :use
    (:instance
     hifat-subsetp-reflexive-lemma-4
     (x
      (list
       (cons (fat32-filename-fix (car (car fs)))
             (m1-file (m1-file->d-e file1)
                      (hifat-file-alist-fix (m1-file->contents file1))))))
     (y (hifat-file-alist-fix (cdr fs)))))))

(defthm hifat-equiv-of-hifat-file-alist-fix-1
  (equal (hifat-equiv (hifat-file-alist-fix fs1)
                      fs2)
         (hifat-equiv fs1 fs2))
  :hints (("goal" :in-theory (enable hifat-equiv)
           :do-not-induct t)))

(defthm hifat-equiv-of-hifat-file-alist-fix-2
  (equal (hifat-equiv fs1
                      (hifat-file-alist-fix fs2))
         (hifat-equiv fs1 fs2))
  :hints (("goal" :in-theory (enable hifat-equiv)
           :do-not-induct t)))

(defthm
  hifat-subsetp-of-put-assoc-1
  (implies
   (and (m1-file-alist-p x)
        (hifat-no-dups-p x)
        (stringp name))
   (equal
    (hifat-subsetp (put-assoc-equal name val x)
                   y)
    (and
     (hifat-subsetp (remove-assoc-equal name x)
                    y)
     (consp (assoc-equal name y))
     (or
      (and (not (m1-directory-file-p (cdr (assoc-equal name y))))
           (not (m1-directory-file-p val))
           (equal (m1-file->contents val)
                  (m1-file->contents (cdr (assoc-equal name y)))))
      (and (m1-directory-file-p (cdr (assoc-equal name y)))
           (m1-directory-file-p val)
           (hifat-subsetp (m1-file->contents val)
                          (m1-file->contents (cdr (assoc-equal name y)))))))))
  :hints (("goal" :in-theory (enable hifat-subsetp hifat-no-dups-p)
           :induct (mv (put-assoc-equal name val x)
                       (remove-assoc-equal name x)))))

(defthm hifat-subsetp-of-put-assoc-2
  (implies (and (m1-file-alist-p x)
                (hifat-subsetp x (remove-assoc-equal name y)))
           (hifat-subsetp x (put-assoc-equal name val y)))
  :hints (("goal" :in-theory (enable hifat-subsetp))))

(defthm hifat-subsetp-of-remove-assoc-1
  (implies (and (m1-file-alist-p x)
                (atom (assoc-equal name x))
                (hifat-subsetp x y))
           (hifat-subsetp x (remove-assoc-equal name y)))
  :hints (("goal" :in-theory (enable hifat-subsetp))))

(defthm hifat-subsetp-of-remove-assoc-2
  (implies (hifat-subsetp x y)
           (hifat-subsetp (remove-assoc-equal name x)
                          y))
  :hints (("goal" :in-theory (enable hifat-subsetp))))

(defthm
  hifat-place-file-when-hifat-equiv-lemma-3
  (implies (and (hifat-equiv (m1-file->contents file1)
                             (m1-file->contents file2))
                (syntaxp (not (term-order file1 file2)))
                (m1-directory-file-p (m1-file-fix file1))
                (m1-directory-file-p (m1-file-fix file2)))
           (hifat-equiv (put-assoc-equal (fat32-filename-fix (car path))
                                         (m1-file-fix file1)
                                         (hifat-file-alist-fix fs))
                        (put-assoc-equal (fat32-filename-fix (car path))
                                         (m1-file-fix file2)
                                         (hifat-file-alist-fix fs))))
  :instructions (:promote (:dive 1)
                          (:rewrite put-assoc-under-hifat-equiv-1
                                    ((file2 (m1-file-fix file2))))
                          :top
                          :bash :bash
                          :bash :bash))

(defthm
  hifat-place-file-when-hifat-equiv-lemma-1
  (implies
   (and
    (hifat-equiv
     (mv-nth
      0
      (hifat-place-file
       (m1-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                            (hifat-file-alist-fix fs))))
       (cdr path)
       file1))
     (mv-nth
      0
      (hifat-place-file
       (m1-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                            (hifat-file-alist-fix fs))))
       (cdr path)
       file2)))
    (syntaxp (not (term-order file1 file2))))
   (hifat-equiv
    (put-assoc-equal
     (fat32-filename-fix (car path))
     (m1-file
      (m1-file->d-e (cdr (assoc-equal (fat32-filename-fix (car path))
                                          (hifat-file-alist-fix fs))))
      (mv-nth
       0
       (hifat-place-file
        (m1-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                             (hifat-file-alist-fix fs))))
        (cdr path)
        file1)))
     (hifat-file-alist-fix fs))
    (put-assoc-equal
     (fat32-filename-fix (car path))
     (m1-file
      (m1-file->d-e (cdr (assoc-equal (fat32-filename-fix (car path))
                                          (hifat-file-alist-fix fs))))
      (mv-nth
       0
       (hifat-place-file
        (m1-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                             (hifat-file-alist-fix fs))))
        (cdr path)
        file2)))
     (hifat-file-alist-fix fs))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite put-assoc-under-hifat-equiv-1))
    :use
    (:instance
     (:rewrite put-assoc-under-hifat-equiv-1)
     (fs (hifat-file-alist-fix fs))
     (file1
      (m1-file
       (m1-file->d-e (cdr (assoc-equal (fat32-filename-fix (car path))
                                           (hifat-file-alist-fix fs))))
       (mv-nth
        0
        (hifat-place-file
         (m1-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                              (hifat-file-alist-fix fs))))
         (cdr path)
         file1))))
     (file2
      (m1-file
       (m1-file->d-e (cdr (assoc-equal (fat32-filename-fix (car path))
                                           (hifat-file-alist-fix fs))))
       (mv-nth
        0
        (hifat-place-file
         (m1-file->contents (cdr (assoc-equal (fat32-filename-fix (car path))
                                              (hifat-file-alist-fix fs))))
         (cdr path)
         file2))))
     (name (fat32-filename-fix (car path)))))))

(defthm hifat-place-file-correctness-lemma-3
  (implies (and (fat32-filename-p name)
                (not (m1-regular-file-p (cdr (assoc-equal name x))))
                (m1-file-alist-p x)
                (hifat-subsetp y x))
           (not (m1-regular-file-p (cdr (assoc-equal name y)))))
  :hints (("goal" :in-theory (enable hifat-subsetp))))

(defthm hifat-find-file-correctness-lemma-1
  (and (equal (hifat-equiv (hifat-file-alist-fix fs1)
                           fs2)
              (hifat-equiv fs1 fs2))
       (equal (hifat-equiv fs1 (hifat-file-alist-fix fs2))
              (hifat-equiv fs1 fs2)))
  :hints (("goal" :in-theory (enable hifat-equiv))))

(defthm
  abs-pwrite-correctness-lemma-29
  (implies
   (and (fat32-filename-p name)
        (m1-directory-file-p (cdr (assoc-equal name y)))
        (hifat-subsetp y x))
   (m1-directory-file-p (cdr (assoc-equal name x))))
  :hints (("goal" :in-theory (enable hifat-subsetp))))

(defthm hifat-place-file-when-hifat-equiv-1
  (implies (and (hifat-equiv (m1-file->contents file1)
                             (m1-file->contents file2))
                (syntaxp (not (term-order file1 file2)))
                (m1-directory-file-p (m1-file-fix file1))
                (m1-directory-file-p (m1-file-fix file2)))
           (and
            (hifat-equiv (mv-nth 0 (hifat-place-file fs path file1))
                         (mv-nth 0 (hifat-place-file fs path file2)))
            (equal (mv-nth 1 (hifat-place-file fs path file1))
                   (mv-nth 1 (hifat-place-file fs path file2)))))
  :hints (("goal" :in-theory (enable hifat-place-file)
           :induct
           (mv (mv-nth 0 (hifat-place-file fs path file1))
               (mv-nth 0 (hifat-place-file fs path file2))))))
