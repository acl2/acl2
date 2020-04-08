;  abstract-separate.lisp                               Mihir Mehta

; This is a model of the FAT32 filesystem, related to HiFAT but with abstract
; variables.

(in-package "ACL2")

(include-book "hifat-equiv")
(local (include-book "std/lists/prefixp" :dir :system))

(local
 (in-theory (disable (:definition true-listp)
                     (:definition string-listp)
                     (:definition integer-listp)
                     (:definition acl2-number-listp)
                     (:rewrite nat-listp-of-remove)
                     (:definition rational-listp)
                     (:rewrite member-of-a-nat-list)
                     (:rewrite take-fewer-of-take-more)
                     (:rewrite assoc-equal-when-member-equal)
                     (:rewrite take-when-atom)
                     (:rewrite take-of-take-split)
                     (:rewrite take-more-of-take-fewer))))

(defthm abs-find-file-helper-of-collapse-lemma-3
  (implies (prefixp (fat32-filename-list-fix x) y)
           (prefixp (fat32-filename-list-fix x)
                    (fat32-filename-list-fix y)))
  :hints (("goal" :in-theory (e/d (fat32-filename-list-fix prefixp)
                                  ((:i fat32-filename-list-fix)))
           :induct (fat32-filename-list-prefixp x y)
           :expand ((fat32-filename-list-fix x)
                    (fat32-filename-list-fix y)))))

;; This is explicitly a replacement for assoc-equal with a vacuous guard.
(defund abs-assoc (x alist)
  (declare (xargs :guard t))
  (cond ((atom alist) nil)
        ((and (atom (car alist)) (null x))
         (car alist))
        ((and (consp (car alist)) (equal x (car (car alist))))
         (car alist))
        (t (abs-assoc x (cdr alist)))))

(defthm abs-assoc-definition
  (equal (abs-assoc x alist)
         (assoc-equal x alist))
  :hints (("goal" :in-theory (enable abs-assoc)))
  :rule-classes :definition)

;; This is explicitly a replacement for put-assoc-equal with a vacuous guard.
(defund abs-put-assoc (name val alist)
  (declare (xargs :guard t))
  (cond ((atom alist) (list (cons name val)))
        ((and (atom (car alist)) (null name))
         (cons (cons name val) (cdr alist)))
        ((and (consp (car alist)) (equal name (caar alist)))
         (cons (cons name val) (cdr alist)))
        (t (cons (car alist)
                 (abs-put-assoc name val (cdr alist))))))

(defthm abs-put-assoc-definition
  (equal (abs-put-assoc name val alist)
         (put-assoc-equal name val alist))
  :hints (("goal" :in-theory (enable abs-put-assoc)))
  :rule-classes :definition)

;; This is explicitly a replacement for remove-assoc-equal with a vacuous guard.
(defund abs-remove-assoc (x alist)
  (declare (xargs :guard t))
  (cond ((atom alist) nil)
        ((and (atom (car alist)) (null x))
         (abs-remove-assoc x (cdr alist)))
        ((and (consp (car alist)) (equal x (car (car alist))))
         (abs-remove-assoc x (cdr alist)))
        (t (cons (car alist)
                 (abs-remove-assoc x (cdr alist))))))

(defthm abs-remove-assoc-definition
  (equal (abs-remove-assoc x alist)
         (remove-assoc-equal x alist))
  :hints (("goal" :in-theory (enable abs-remove-assoc)))
  :rule-classes :definition)

;; We need to write this whole thing out - the same way we did it for
;; m1-file-alist-p - because the induction scheme has to be created by us,
;; without assistance from fty, just this once.
(defund
  abs-file-alist-p (x)
  (declare (xargs :guard t))
  (b* (((when (atom x)) (equal x nil))
       (head (car x))
       ;; The presence of abstract variables makes this data structure not
       ;; strictly an alist - because they have no names and therefore they
       ;; don't need a cons pair with the car for the name.
       ((when (atom head))
        (and (natp head) (abs-file-alist-p (cdr x))))
       (file (cdr head))
       ((unless (and (alistp file)
                     (equal (strip-cars file)
                            '(dir-ent contents))))
        nil)
       (dir-ent (cdr (std::da-nth 0 (cdr head))))
       (contents (cdr (std::da-nth 1 (cdr head)))))
    (and (fat32-filename-p (car head))
         (dir-ent-p dir-ent)
         (or (and (stringp contents)
                  (unsigned-byte-p 32 (length contents)))
             (abs-file-alist-p contents))
         (abs-file-alist-p (cdr x)))))

(defthm abs-file-alist-p-of-cdr
  (implies (abs-file-alist-p abs-file-alist1)
           (abs-file-alist-p (cdr abs-file-alist1)))
  :hints (("goal" :in-theory (enable abs-file-alist-p))))

(defthm
  abs-file-alist-p-when-m1-file-alist-p
  (implies (m1-file-alist-p x)
           (abs-file-alist-p x))
  :hints (("goal" :in-theory (enable abs-file-alist-p
                                     m1-file-alist-p))))

(defund abs-file-contents-p (contents)
  (declare (xargs :guard t))
  (or (and (stringp contents)
           (unsigned-byte-p 32 (length contents)))
      (abs-file-alist-p contents)))

(defund abs-file-contents-fix (contents)
  (declare (xargs :guard t))
  (if (abs-file-contents-p contents)
      contents
    ""))

(defthm
  abs-file-contents-p-correctness-1
  (implies (abs-file-alist-p contents)
           (abs-file-contents-p contents))
  :hints (("goal" :in-theory (enable abs-file-contents-p))))

(defthm abs-file-contents-p-of-abs-file-contents-fix
  (abs-file-contents-p (abs-file-contents-fix x))
  :hints (("goal" :in-theory (enable abs-file-contents-fix))))

(defthm abs-file-contents-fix-when-abs-file-contents-p
  (implies (abs-file-contents-p x)
           (equal (abs-file-contents-fix x) x))
  :hints (("goal" :in-theory (enable abs-file-contents-fix))))

(defthm
  abs-file-contents-p-when-stringp
  (implies (stringp contents)
           (equal (abs-file-contents-p contents)
                  (unsigned-byte-p 32 (length contents))))
  :hints (("goal" :in-theory (enable abs-file-contents-p abs-file-alist-p))))

(defthm
  abs-file-alist-p-of-abs-file-contents-fix
  (equal (abs-file-alist-p (abs-file-contents-fix contents))
         (abs-file-alist-p contents))
  :hints (("goal" :in-theory (enable abs-file-contents-fix))))

(fty::deffixtype abs-file-contents
                 :pred abs-file-contents-p
                 :fix abs-file-contents-fix
                 :equiv abs-file-contents-equiv
                 :define t)

(defthm
  abs-file-contents-p-when-m1-file-contents-p
  (implies (m1-file-contents-p contents)
           (abs-file-contents-p contents))
  :hints (("goal" :in-theory (enable m1-file-contents-p
                                     abs-file-contents-p))))

(fty::defprod
 abs-file
 ((dir-ent dir-ent-p :default (dir-ent-fix nil))
  (contents abs-file-contents-p :default (abs-file-contents-fix nil))))

(defthm
  acl2-count-of-abs-file->contents
  t
  :rule-classes
  ((:linear
    :corollary
    (implies (abs-file-p file)
             (< (acl2-count (abs-file->contents file))
                (acl2-count file)))
    :hints
    (("goal" :in-theory (enable abs-file-p abs-file->contents))))
   (:linear
    :corollary
    (<= (acl2-count (abs-file->contents file))
        (acl2-count file))
    :hints
    (("goal"
      :in-theory
      (enable abs-file-p abs-file->contents abs-file-contents-fix))))))

(defthm
  abs-file->contents-when-m1-file-p
  (implies (m1-file-p file)
           (equal (abs-file->contents file)
                  (m1-file->contents file)))
  :hints
  (("goal" :in-theory (enable m1-file->contents
                              abs-file->contents m1-file-p))))

(defund abs-directory-file-p (file)
  (declare (xargs :guard t))
  (and (abs-file-p file)
       (abs-file-alist-p (abs-file->contents file))))

(defthm
  abs-file-p-when-m1-regular-file-p
  (implies (m1-regular-file-p file)
           (abs-file-p file))
  :hints (("goal" :in-theory (enable m1-regular-file-p
                                     abs-file-p m1-file-p))))

;; Awful proof.
(defthm
  m1-regular-file-p-of-abs-file
  (equal
   (m1-regular-file-p (abs-file dir-ent contents))
   (and
    (stringp (abs-file-contents-fix contents))
    (unsigned-byte-p 32
                     (length (abs-file-contents-fix contents)))))
  :hints (("goal" :in-theory (enable m1-regular-file-p abs-file-contents-fix
                                     m1-file-p abs-file-contents-p abs-file
                                     m1-file->contents))))

(defthm
  abs-directory-file-p-correctness-1
  (implies (m1-directory-file-p file)
           (and (m1-file-p file)
                (not (stringp (m1-file->contents file)))))
  :hints (("goal"
           :in-theory (enable m1-directory-file-p m1-file-alist-p
                              m1-regular-file-p))))

(defthm
  abs-file-p-when-abs-directory-file-p
  (implies (abs-directory-file-p file)
           (abs-file-p file))
  :hints (("goal" :in-theory (enable abs-directory-file-p))))

(defthm
  abs-file-alist-p-of-abs-file->contents
  (equal (abs-file-alist-p (abs-file->contents file))
         (abs-directory-file-p (abs-file-fix file)))
  :hints (("goal" :in-theory (enable abs-file->contents
                                     abs-directory-file-p)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies (abs-directory-file-p file)
             (abs-file-alist-p (abs-file->contents file))))))

(defthm
  abs-directory-file-p-of-abs-file
  (implies (abs-file-alist-p contents)
           (abs-directory-file-p (abs-file dir-ent contents)))
  :hints (("goal" :in-theory (enable abs-directory-file-p))))

(defthm
  abs-directory-file-p-when-m1-file-p-lemma-1
  (implies (stringp x)
           (not (abs-file-alist-p x)))
  :hints (("goal" :in-theory (enable abs-file-alist-p)))
  :rule-classes :type-prescription)

(defthm
  abs-directory-file-p-when-m1-file-p
  (implies (m1-file-p file)
           (equal (abs-directory-file-p file)
                  (m1-directory-file-p file)))
  :hints (("goal" :in-theory (enable m1-file-p abs-file-p
                                     abs-directory-file-p m1-directory-file-p
                                     m1-file->contents abs-file->contents
                                     m1-file-contents-p))))

;; top-complete is known to match up with alistp
(defund abs-complete (x)
  (declare (xargs :guard t))
  (or (atom x)
      (and (consp (car x))
           (or (not (abs-directory-file-p (cdar x)))
               (abs-complete (abs-file->contents (cdar x))))
           (abs-complete (cdr x)))))

(defthm
  abs-file-alist-p-correctness-1-lemma-1
  (implies (and (or (and (consp (car x))
                         (m1-file-alist-p (abs-file->contents (cdr (car x)))))
                    (not
                     (and (abs-file-alist-p (abs-file->contents (cdr (car x))))
                          (or (abs-directory-file-p (cdr (car x)))
                              (abs-complete (abs-file->contents (cdr (car x))))))))
                (abs-file-alist-p x))
           (m1-file-p (cdr (car x))))
  :hints
  (("goal" :expand ((m1-file-p (cdr (car x)))
                    (abs-file-alist-p x)
                    (m1-file-alist-p (abs-file->contents (cdr (car x))))
                    (abs-file->contents (cdr (car x)))
                    (abs-directory-file-p (cdr (car x)))
                    (abs-file-p (cdr (car x)))))))

(defthmd
  abs-file-alist-p-correctness-1-lemma-2
  (implies (and (consp (car x))
                (m1-file-alist-p (abs-file->contents (cdr (car x))))
                (m1-file-alist-p (cdr x))
                (abs-file-alist-p x))
           (m1-file-alist-p x))
  :hints (("goal" :in-theory (disable (:rewrite m1-file-alist-p-of-cons))
           :use (:instance (:rewrite m1-file-alist-p-of-cons)
                           (x (cdr x))
                           (a (car x)))
           :expand (abs-file-alist-p x))))

(encapsulate
  ()

  (local
   (defthm
     abs-file-alist-p-correctness-1-lemma-3
     (implies (and (not (and (abs-file-alist-p (abs-file->contents (cdr (car x))))
                             (or (abs-directory-file-p (cdr (car x)))
                                 (abs-complete (abs-file->contents (cdr (car x)))))))
                   (m1-file-alist-p (cdr x))
                   (abs-file-alist-p x))
              (m1-file-alist-p x))
     :hints (("goal" :in-theory (disable (:rewrite m1-file-alist-p-of-cons))
              :use (:instance (:rewrite m1-file-alist-p-of-cons)
                              (x (cdr x))
                              (a (car x)))
              :expand (abs-file-alist-p x)))))

  ;; This theorem states that an abstract filesystem tree without any body
  ;; addresses is just a HiFAT instance.
  (defthm
    abs-file-alist-p-correctness-1
    (implies (and (abs-file-alist-p x)
                  (abs-complete x))
             (m1-file-alist-p x))
    :hints (("goal" :in-theory (enable abs-file-alist-p abs-complete
                                       abs-file-alist-p-correctness-1-lemma-2)
             :induct (abs-complete x)))))

(defthm abs-file-alist-p-of-put-assoc-equal
  (implies (abs-file-alist-p alist)
           (equal (abs-file-alist-p (put-assoc-equal name val alist))
                  (and (fat32-filename-p name)
                       (abs-file-p val))))
  :hints (("goal" :in-theory (enable abs-file-alist-p
                                     abs-file-p abs-file-contents-p))))

(defthm abs-file-alist-p-of-append
  (implies (and (abs-file-alist-p x)
                (abs-file-alist-p y))
           (abs-file-alist-p (append x y)))
  :hints (("goal" :in-theory (enable abs-file-alist-p))))

(defthm abs-file-alist-p-of-remove-equal
  (implies (abs-file-alist-p l)
           (abs-file-alist-p (remove-equal x l)))
  :hints (("goal" :in-theory (enable abs-file-alist-p))))

(defthm abs-file-alist-p-of-remove-assoc-equal
  (implies (abs-file-alist-p alist)
           (abs-file-alist-p (remove-assoc-equal x alist)))
  :hints (("goal" :in-theory (enable abs-file-alist-p))))

(defthm true-listp-when-abs-file-alist-p
  (implies (abs-file-alist-p fs)
           (true-listp fs))
  :hints (("goal" :in-theory (enable abs-file-alist-p))))

(defund
  abs-top-addrs (abs-file-alist)
  (declare
   (xargs :guard (abs-file-alist-p abs-file-alist)
          :guard-hints
          (("goal" :in-theory (enable abs-file-alist-p)))))
  (cond ((atom abs-file-alist) nil)
        ((natp (car abs-file-alist))
         (list* (car abs-file-alist)
                (abs-top-addrs (cdr abs-file-alist))))
        (t (abs-top-addrs (cdr abs-file-alist)))))

;; abs-fs-fix might seem to be a nice fixer for the first (only) argument, but
;; it's not because when you have the removal of duplicate elements, you end up
;; with some addresses disappearing. The same thing explains why abs-complete
;; does not neatly line up.
(defund
  abs-addrs (abs-file-alist)
  (declare
   (xargs :guard (abs-file-alist-p abs-file-alist)
          :guard-hints
          (("goal" :in-theory (enable abs-file-alist-p)))))
  (cond ((atom abs-file-alist) nil)
        ((atom (car abs-file-alist))
         (list* (mbe :logic (nfix (car abs-file-alist))
                     :exec (car abs-file-alist))
                (abs-addrs (cdr abs-file-alist))))
        ((abs-directory-file-p (cdar abs-file-alist))
         (append
          (abs-addrs (abs-file->contents (cdar abs-file-alist)))
          (abs-addrs (cdr abs-file-alist))))
        (t (abs-addrs (cdr abs-file-alist)))))

(defthm abs-addrs-when-m1-file-alist-p
  (implies (m1-file-alist-p x)
           (equal (abs-addrs x) nil))
  :hints (("goal" :in-theory (enable abs-addrs
                                     abs-file-alist-p-correctness-1-lemma-2)))
  :rule-classes :type-prescription)

(defthm abs-addrs-of-true-list-fix
  (equal (abs-addrs (true-list-fix abs-file-alist))
         (abs-addrs abs-file-alist))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  member-of-abs-addrs-when-natp
  (implies (and (natp x)
                (member-equal x abs-file-alist))
           (member-equal x (abs-addrs abs-file-alist)))
  :hints (("goal" :in-theory (enable abs-addrs abs-file-alist-p)))
  :rule-classes
  (:rewrite
   (:rewrite :corollary (implies (and (natp x)
                                      (equal (abs-addrs abs-file-alist) nil))
                                 (not (member-equal x abs-file-alist))))))

(defthm
  abs-addrs-of-remove-lemma-1
  (implies (and (member-equal x abs-file-alist1)
                (integerp x)
                (<= 0 x)
                (member-equal x (abs-addrs abs-file-alist2)))
           (intersectp-equal (abs-addrs abs-file-alist1)
                             (abs-addrs abs-file-alist2)))
  :hints (("goal" :use (:instance (:rewrite intersectp-member)
                                  (a x)
                                  (y (abs-addrs abs-file-alist2))
                                  (x (abs-addrs abs-file-alist1))))))

(defthm
  abs-addrs-of-remove-lemma-2
  (implies
   (and
    (natp x)
    (member-equal x (cdr abs-file-alist))
    (not (intersectp-equal
          (abs-addrs (cdr abs-file-alist))
          (abs-addrs (abs-file->contents (cdr (car abs-file-alist)))))))
   (not (member-equal
         x
         (abs-addrs (abs-file->contents (cdr (car abs-file-alist)))))))
  :hints
  (("goal"
    :use
    (:instance (:rewrite intersectp-member)
               (a x)
               (y (abs-addrs (abs-file->contents (cdr (car abs-file-alist)))))
               (x (abs-addrs (cdr abs-file-alist)))))))

(defthm abs-addrs-of-remove
  (implies (and (natp x)
                (member-equal x abs-file-alist)
                (no-duplicatesp-equal (abs-addrs abs-file-alist)))
           (equal (abs-addrs (remove-equal x abs-file-alist))
                  (remove-equal x (abs-addrs abs-file-alist))))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm abs-addrs-of-append
  (equal (abs-addrs (append x y))
         (append (abs-addrs x) (abs-addrs y)))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm abs-complete-definition
  (equal (abs-complete x)
         (atom (abs-addrs x)))
  :rule-classes :definition
  :hints (("goal" :in-theory (enable abs-complete abs-addrs))))

(defund
  abs-no-dups-p (fs)
  (declare
   (xargs
    :guard (abs-file-alist-p fs)
    :guard-hints (("goal" :expand (abs-file-alist-p fs)))))
  (cond ((atom fs) t)
        ((not (abs-no-dups-p (cdr fs))) nil)
        ((and (consp (car fs))
              (consp (abs-assoc (caar fs) (cdr fs))))
         nil)
        ((and (consp (car fs))
              (abs-directory-file-p (cdar fs)))
         (abs-no-dups-p (abs-file->contents (cdar fs))))
        (t t)))

(defthm abs-no-dups-p-of-cdr
  (implies (abs-no-dups-p abs-file-alist1)
           (abs-no-dups-p (cdr abs-file-alist1)))
  :hints (("goal" :in-theory (enable abs-no-dups-p))))

(defthm
  abs-no-dups-p-of-abs-file->contents-of-cdr-of-assoc
  (implies (and (abs-file-alist-p fs)
                (abs-no-dups-p fs)
                (abs-directory-file-p (cdr (assoc-equal name fs))))
           (abs-no-dups-p (abs-file->contents (cdr (assoc-equal name fs)))))
  :hints (("goal" :in-theory (enable abs-no-dups-p)
           :expand (abs-file-alist-p fs))))

(defthm
  abs-no-dups-p-when-m1-file-alist-p
  (implies (m1-file-alist-p fs)
           (equal (abs-no-dups-p fs)
                  (hifat-no-dups-p fs)))
  :hints (("goal" :induct (abs-no-dups-p fs)
           :in-theory (enable abs-no-dups-p abs-directory-file-p
                              m1-directory-file-p abs-file->contents
                              m1-file->contents abs-file-p)
           :expand ((hifat-no-dups-p fs)
                    (m1-file-alist-p fs)))))

(defthm
  abs-no-dups-p-of-remove-lemma-1
  (implies
   (and (not (consp (assoc-equal name abs-file-alist)))
        (abs-file-alist-p abs-file-alist))
   (not
    (consp (assoc-equal name (remove-equal x abs-file-alist)))))
  :hints (("goal" :in-theory (enable abs-file-alist-p))))

(defthm abs-no-dups-p-of-remove
  (implies (and (abs-no-dups-p abs-file-alist)
                (abs-file-alist-p abs-file-alist))
           (abs-no-dups-p (remove-equal x abs-file-alist)))
  :hints (("goal" :in-theory (enable abs-no-dups-p)
           :induct (mv (abs-no-dups-p abs-file-alist)
                       (remove-equal x abs-file-alist)))))

(defthm abs-no-dups-p-of-put-assoc-equal
  (equal (abs-no-dups-p (put-assoc-equal key val x))
         (and (atom (assoc-equal key (remove1-assoc-equal key x)))
              (abs-no-dups-p (remove1-assoc-equal key x))
              (or (not (abs-directory-file-p val))
                  (abs-no-dups-p (abs-file->contents val)))))
  :hints (("goal" :in-theory (enable abs-no-dups-p))))

(defthm
  abs-no-dups-p-of-remove1-assoc
  (implies
   (or
    (atom (assoc-equal name fs))
    (and
     (atom (assoc-equal name (remove1-assoc-equal name fs)))
     (or (not (abs-directory-file-p (cdr (assoc-equal name fs))))
         (abs-no-dups-p (abs-file->contents (cdr (assoc-equal name fs)))))))
   (equal (abs-no-dups-p (remove1-assoc-equal name fs))
          (abs-no-dups-p fs)))
  :hints (("goal" :in-theory (enable abs-no-dups-p))
          ("subgoal *1/3" :cases ((equal name (car (car fs)))))))

(defthmd abs-no-dups-p-of-append-lemma-1
  (implies (and (abs-file-alist-p alist)
                (not (fat32-filename-p x)))
           (not (consp (assoc-equal x alist))))
  :hints (("goal" :in-theory (enable abs-file-alist-p))))

;; I'm choosing to include a corollary which really is about hifat-no-dups-p,
;; because moving it to hifat.lisp would introduce a bunch of intersectp
;; forms which I don't know if I want in that file.
(defthm
  abs-no-dups-p-of-append
  (implies
   (and (abs-file-alist-p x)
	(abs-file-alist-p y))
   (equal (abs-no-dups-p (append x y))
	  (and (abs-no-dups-p x)
	       (abs-no-dups-p y)
	       (not (intersectp-equal (remove-equal nil (strip-cars x))
				      (remove-equal nil (strip-cars y)))))))
  :hints (("goal" :in-theory (e/d (abs-no-dups-p
                                   intersectp-equal
                                   abs-no-dups-p-of-append-lemma-1)
				  (intersectp-is-commutative))
	   :induct (append x y))
	  ("subgoal *1/2" :cases ((null (car (car x))))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (m1-file-alist-p x)
	  (m1-file-alist-p y))
     (equal (hifat-no-dups-p (append x y))
	    (and (hifat-no-dups-p x)
	         (hifat-no-dups-p y)
	         (not (intersectp-equal (remove-equal nil (strip-cars x))
				        (remove-equal nil (strip-cars y))))))))))

(defthm abs-no-dups-p-of-remove-assoc
  (implies (abs-no-dups-p fs)
           (abs-no-dups-p (remove-assoc-equal x fs)))
  :hints (("goal" :in-theory (enable abs-no-dups-p))))

(defund abs-fs-p (x)
  (declare (xargs :guard t))
  (and (abs-file-alist-p x)
       (abs-no-dups-p x)))

(defthm abs-fs-p-correctness-1
  (implies
   (abs-fs-p x)
   (and (abs-file-alist-p x)
        (abs-no-dups-p x)))
  :hints (("Goal" :in-theory (enable abs-fs-p)) ))

(defthm
  abs-fs-p-of-append
  (implies
   (and (abs-file-alist-p x)
        (abs-file-alist-p y))
   (equal (abs-fs-p (append x y))
          (and (abs-no-dups-p x)
               (abs-no-dups-p y)
               (not (intersectp-equal (remove-equal nil (strip-cars x))
                                      (remove-equal nil (strip-cars y)))))))
  :hints (("goal" :in-theory (enable abs-fs-p))))

(defthm abs-fs-p-of-remove
  (implies (abs-fs-p fs)
           (abs-fs-p (remove-equal x fs)))
  :hints (("Goal" :in-theory (enable abs-fs-p))))

(defthm
  abs-fs-p-of-put-assoc-equal
  (implies (abs-file-alist-p (put-assoc-equal key val x))
           (equal (abs-fs-p (put-assoc-equal key val x))
                  (and (atom (assoc-equal key (remove1-assoc-equal key x)))
                       (abs-no-dups-p (remove1-assoc-equal key x))
                       (or (not (abs-directory-file-p val))
                           (abs-no-dups-p (abs-file->contents val))))))
  :hints (("goal" :in-theory (enable abs-fs-p))))

(defund
  abs-fs-fix (x)
  (declare
   (xargs
    :guard (abs-file-alist-p x)
    :verify-guards nil))
  (b* (((when (atom x)) nil)
       (head (car x))
       (tail (abs-fs-fix (cdr x)))
       ((when (atom head))
        (cons (nfix head) tail))
       (head (cons
              (fat32-filename-fix (car head))
              (abs-file-fix (cdr head))))
       ((when (consp (abs-assoc (car head) tail)))
        tail))
    (if
        (abs-directory-file-p (cdr head))
        (cons (cons (car head)
                    (make-abs-file
                     :dir-ent (abs-file->dir-ent (cdr head))
                     :contents (abs-fs-fix (abs-file->contents (cdr head)))))
              (abs-fs-fix (cdr x)))
      (cons head
            (abs-fs-fix (cdr x))))))

(defthm
  abs-fs-fix-when-abs-fs-p
  (implies (abs-fs-p x)
           (equal (abs-fs-fix x) x))
  :hints
  (("goal"
    :in-theory (e/d (abs-fs-fix abs-file-alist-p m1-file->contents
                                abs-file-p abs-no-dups-p abs-fs-p
                                abs-file->contents abs-directory-file-p)
                    ((:rewrite abs-file-alist-p-correctness-1)
                     (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
                     (:rewrite abs-file-alist-p-when-m1-file-alist-p)
                     (:rewrite abs-file->contents$inline-of-abs-file-fix-x)
                     (:rewrite m1-file-contents-p-correctness-1)
                     (:rewrite abs-file-alist-p-of-abs-file-contents-fix)
                     (:rewrite abs-no-dups-p-when-m1-file-alist-p)))
    :induct (abs-file-alist-p x))))

(defthm abs-file-alist-p-of-abs-fs-fix
  (abs-file-alist-p (abs-fs-fix x))
  :hints (("goal" :in-theory (enable abs-fs-fix abs-file-alist-p
                                     abs-file-fix abs-file-contents-fix
                                     abs-file-contents-p abs-file))))

(defthm abs-no-dups-p-of-abs-fs-fix
  (abs-no-dups-p (abs-fs-fix x))
  :hints (("goal" :in-theory (enable abs-fs-fix abs-no-dups-p))))

(defthm abs-fs-p-of-abs-fs-fix
  (abs-fs-p (abs-fs-fix x))
  :hints (("goal" :in-theory (enable abs-fs-fix))))

(verify-guards
  abs-fs-fix
  :guard-debug t
  :hints (("goal" :expand (abs-file-alist-p x)
           :in-theory (enable abs-file-p))))

(defthmd
  member-of-abs-fs-fix-when-natp-lemma-1
  (implies (and (abs-file-alist-p abs-file-alist)
                (consp abs-file-alist))
           (or (consp (car abs-file-alist))
               (natp (car abs-file-alist))))
  :hints (("goal" :do-not-induct t
           :expand (abs-file-alist-p abs-file-alist)))
  :rule-classes :type-prescription)

(defthm member-of-abs-fs-fix-when-natp
  (implies (and (natp x) (abs-file-alist-p fs))
           (iff (member-equal x (abs-fs-fix fs))
                (member-equal x fs)))
  :hints (("goal" :in-theory (enable abs-fs-fix
                                     member-of-abs-fs-fix-when-natp-lemma-1))))

(defthm consp-of-assoc-of-abs-fs-fix
  (implies (abs-file-alist-p fs)
           (equal (consp (assoc-equal name (abs-fs-fix fs)))
                  (consp (assoc-equal name fs))))
  :hints (("goal" :in-theory (enable abs-fs-fix)
           :induct (mv (abs-fs-fix fs)
                       (assoc-equal name fs))
           :expand (abs-file-alist-p fs))))

;; Move later
(defthm
  abs-fs-fix-of-remove-equal
  (implies (and (natp x) (abs-file-alist-p fs))
           (equal (abs-fs-fix (remove-equal x fs))
                  (remove-equal x (abs-fs-fix fs))))
  :hints
  (("goal" :in-theory (enable abs-fs-fix abs-file-alist-p)
    :expand (:with (:rewrite assoc-of-remove)
                   (assoc-equal (fat32-filename-fix (car (car fs)))
                                (remove-equal x (cdr fs)))))))

;; I'm not sure what to do with abs-fs-equiv...
(fty::deffixtype abs-fs
                 :pred abs-fs-p
                 :fix abs-fs-fix
                 :equiv abs-fs-equiv
                 :define t
                 :forward t)

;; Where are the numbers going to come from? It's not going to work, the idea
;; of letting variables be represented by their index in the list. Under such a
;; scheme, we'll never be able to rewrite an (append ...) term, since that
;; would immediately cause all the indices to become wrong. It's probably best
;; to use the function find-new-index for this purpose.
;;
;; In a certain theoretical sense, we don't actually need to store abstract heap
;; cells as pairs - keeping the address in the table along with the
;; substructure isn't actually necessary, because we can just look in the
;; larger structure for occurrences of the body address. However, this process
;; would be grossly inefficient because we would have to look everywhere in the
;; directory tree. I suspect that's why the idea of an abstract heap cell as a
;; pair arose in the first place.
;;
;; One more thing: I'm not returning an error code from this function at the
;; moment, because I can't fathom where such an error code would be useful. It
;; would only arise from a programming error on our part, where we tried to
;; context-apply a nonexistent variable - not from any real filesystem
;; error. In such a case, it's OK to keep the no-change loser behaviour, even
;; if we don't immediately formalise it.
;;
;; Another thing: this function only works if there are no body addresses in
;; the way down the path... otherwise, we'd have to look up those body
;; addresses and look inside them. In terms of recursion, we'd have to recur as
;; many times as body addresses occur along the path. Also, each time we were
;; looking for something and failed to find a directory entry at a certain
;; level - but found at least one body address - we'd have to iterate over all
;; body addresses at that level.
;;
;; <sigh>
(defund
  context-apply
  (abs-file-alist1 abs-file-alist2 x x-path)
  (declare (xargs :guard (and (abs-fs-p abs-file-alist1)
                              (natp x)
                              (abs-fs-p abs-file-alist2)
                              (fat32-filename-list-p x-path))
                  :verify-guards nil
                  :measure (len x-path)))
  (b*
      ((abs-file-alist1 (mbe :logic (abs-fs-fix abs-file-alist1) :exec abs-file-alist1))
       (abs-file-alist2 (mbe :logic (abs-fs-fix abs-file-alist2) :exec abs-file-alist2))
       (x (mbe :logic (nfix x) :exec x))
       ((when (and (atom x-path)
                   (member x abs-file-alist1)))
        (append (remove x abs-file-alist1)
                abs-file-alist2))
       ((when (atom x-path)) abs-file-alist1)
       (head (mbe :exec (car x-path)
                  :logic (fat32-filename-fix (car x-path))))
       ((when (and (consp (abs-assoc head abs-file-alist1))
                   (abs-directory-file-p
                    (cdr (abs-assoc head abs-file-alist1)))))
        (abs-put-assoc
         head
         (abs-file
          (abs-file->dir-ent
           (cdr (abs-assoc head abs-file-alist1)))
          (context-apply
           (abs-file->contents
            (cdr (abs-assoc head abs-file-alist1)))
           abs-file-alist2 x (cdr x-path)))
         abs-file-alist1)))
    ;; This is actually an error condition.
    abs-file-alist1))

(defthm
  abs-file-alist-p-of-context-apply-lemma-1
  (implies
   (and (abs-directory-file-p (cdr (assoc-equal (car x-path)
                                                abs-file-alist1)))
        (abs-file-alist-p abs-file-alist1))
   (abs-file-alist-p
    (put-assoc-equal
     (car x-path)
     (abs-file (abs-file->dir-ent (cdr (assoc-equal (car x-path)
                                                    abs-file-alist1)))
               (context-apply
                (abs-file->contents (cdr (assoc-equal (car x-path)
                                                      abs-file-alist1)))
                abs-file-alist2 x (cdr x-path)))
     abs-file-alist1)))
  :hints
  (("goal"
    :use (:instance abs-no-dups-p-of-append-lemma-1
                    (alist abs-file-alist1)
                    (x (car x-path))))))

(defthm abs-file-alist-p-of-context-apply
  (abs-file-alist-p (context-apply abs-file-alist1
                                   abs-file-alist2 x x-path))
  :hints (("goal" :in-theory (enable context-apply))))

(defthm abs-fs-p-of-abs-file->contents-of-cdr-of-assoc
  (implies (and (abs-fs-p fs)
                (abs-directory-file-p (cdr (assoc-equal name fs))))
           (abs-fs-p (abs-file->contents (cdr (assoc-equal name fs)))))
  :hints (("goal" :in-theory (enable abs-fs-p))))

(verify-guards context-apply
  :guard-debug t
  :hints (("Goal" :in-theory (enable abs-file-alist-p)) ))

(defthm context-apply-of-fat32-filename-list-fix
  (equal (context-apply abs-file-alist1 abs-file-alist2
                        x (fat32-filename-list-fix x-path))
         (context-apply abs-file-alist1
                        abs-file-alist2 x x-path))
  :hints (("goal" :in-theory (enable context-apply))))

(defcong
  fat32-filename-list-equiv equal
  (context-apply abs-file-alist1
                 abs-file-alist2 x x-path)
  4
  :hints
  (("goal"
    :in-theory (e/d (fat32-filename-list-equiv)
                    (context-apply-of-fat32-filename-list-fix))
    :use
    (context-apply-of-fat32-filename-list-fix
     (:instance context-apply-of-fat32-filename-list-fix
                (x-path x-path-equiv))))))

(defthm context-apply-of-nfix
  (equal (context-apply abs-file-alist1 abs-file-alist2
                        (nfix x) x-path)
         (context-apply abs-file-alist1
                        abs-file-alist2 x x-path))
  :hints (("goal" :in-theory (enable context-apply))))

(defcong
  nat-equiv equal
  (context-apply abs-file-alist1
                 abs-file-alist2 x x-path)
  3
  :hints
  (("goal" :in-theory (disable (:rewrite context-apply-of-nfix))
    :use ((:instance (:rewrite context-apply-of-nfix)
                     (x x-equiv))
          (:rewrite context-apply-of-nfix)))))

(defthm context-apply-of-abs-fs-fix-1
  (equal (context-apply (abs-fs-fix abs-file-alist1)
                        abs-file-alist2 x x-path)
         (context-apply abs-file-alist1
                        abs-file-alist2 x x-path))
  :hints (("goal" :in-theory (enable context-apply))))

(defthm context-apply-of-abs-fs-fix-2
  (equal (context-apply abs-file-alist1
                        (abs-fs-fix abs-file-alist2)
                        x x-path)
         (context-apply abs-file-alist1
                        abs-file-alist2 x x-path))
  :hints (("goal" :in-theory (enable context-apply))))

(defund context-apply-ok
  (abs-file-alist1 abs-file-alist2 x x-path)
  (declare (xargs :guard (and (abs-fs-p abs-file-alist1)
                              (natp x)
                              (abs-fs-p abs-file-alist2)
                              (fat32-filename-list-p x-path))))
  (not
   (equal
    (context-apply
     abs-file-alist1 abs-file-alist2 x x-path)
    (abs-fs-fix abs-file-alist1))))

(defcong
  fat32-filename-list-equiv equal
  (context-apply-ok abs-file-alist1
                    abs-file-alist2 x x-path)
  4
  :hints
  (("goal"
    :in-theory (enable context-apply-ok))))

(defthm context-apply-ok-of-abs-fs-fix-1
  (equal (context-apply-ok (abs-fs-fix abs-file-alist1)
                           abs-file-alist2 x x-path)
         (context-apply-ok abs-file-alist1
                           abs-file-alist2 x x-path))
  :hints (("goal" :in-theory (enable context-apply-ok))))

(defthm context-apply-ok-of-abs-fs-fix-2
  (equal (context-apply-ok abs-file-alist1
                           (abs-fs-fix abs-file-alist2)
                           x x-path)
         (context-apply-ok abs-file-alist1
                           abs-file-alist2 x x-path))
  :hints (("goal" :in-theory (enable context-apply-ok))))

(defthm context-apply-ok-of-nfix
  (equal (context-apply-ok abs-file-alist1 abs-file-alist2
                           (nfix x) x-path)
         (context-apply-ok abs-file-alist1
                           abs-file-alist2 x x-path))
  :hints (("goal" :in-theory (e/d (context-apply-ok) (nfix)))))

(defcong
  nat-equiv equal
  (context-apply-ok abs-file-alist1
                    abs-file-alist2 x x-path)
  3
  :hints
  (("goal" :in-theory (disable (:rewrite context-apply-ok-of-nfix))
    :use ((:instance (:rewrite context-apply-ok-of-nfix)
                     (x x-equiv))
          (:rewrite context-apply-ok-of-nfix)))))

(defthm abs-addrs-of-context-apply-1-lemma-1
  (subsetp-equal (abs-addrs (remove-equal x abs-file-alist))
                 (abs-addrs abs-file-alist))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  abs-addrs-of-context-apply-1-lemma-3
  (implies (and (member-equal x abs-file-alist1)
                (integerp x)
                (<= 0 x)
                (no-duplicatesp-equal (abs-addrs abs-file-alist1)))
           (not (member-equal x
                              (abs-addrs (remove-equal x abs-file-alist1)))))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  abs-addrs-of-context-apply-1-lemma-4
  (implies
   (and (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
        (no-duplicatesp-equal (abs-addrs abs-file-alist1)))
   (no-duplicatesp-equal
    (abs-addrs
     (abs-file->contents (cdr (assoc-equal name abs-file-alist1))))))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  abs-addrs-of-context-apply-1-lemma-5
  (implies
   (and (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
        (not (intersectp-equal (abs-addrs abs-file-alist1)
                               y)))
   (not
    (intersectp-equal
     (abs-addrs (abs-file->contents (cdr (assoc-equal name abs-file-alist1))))
     y)))
  :hints (("goal" :in-theory (e/d (abs-addrs intersectp-equal)
                                  (intersectp-is-commutative)))))

(defthm
  abs-addrs-of-context-apply-1-lemma-6
  (implies
   (and (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
        (not (member-equal x (abs-addrs abs-file-alist1))))
   (not
    (member-equal
     x
     (abs-addrs
      (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))))))
  :hints (("goal" :in-theory (enable abs-addrs)))
  :rule-classes :type-prescription)

;; Important - says clearly that the variable's name (or number, whatever) must
;; exist for context application to go right.
(defthm
  abs-addrs-of-context-apply-1-lemma-7
  (implies (and (natp x)
                (not (member-equal x
                                   (abs-addrs (abs-fs-fix abs-file-alist1)))))
           (not (context-apply-ok abs-file-alist1
                                  abs-file-alist2 x x-path)))
  :hints (("goal" :in-theory (enable abs-addrs
                                     context-apply context-apply-ok)
           :induct (context-apply abs-file-alist1
                                  abs-file-alist2 x x-path)
           :do-not-induct t)))

(defthm
  abs-addrs-of-context-apply-1-lemma-8
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal name (cdr abs-file-alist1))))
    (member-equal
     x
     (abs-addrs
      (abs-file->contents (cdr (assoc-equal name (cdr abs-file-alist1))))))
    (member-equal
     x
     (abs-addrs (abs-file->contents (cdr (car abs-file-alist1))))))
   (intersectp-equal
    (abs-addrs (cdr abs-file-alist1))
    (abs-addrs (abs-file->contents (cdr (car abs-file-alist1))))))
  :hints
  (("goal"
    :use (:instance
          (:rewrite intersectp-member)
          (a x)
          (y (abs-addrs (abs-file->contents (cdr (car abs-file-alist1)))))
          (x (abs-addrs (cdr abs-file-alist1)))))))

(defthm
  abs-addrs-of-context-apply-1-lemma-9
  (implies
   (not (member-equal x (abs-addrs abs-file-alist)))
   (not (member-equal x
                      (abs-addrs (remove-assoc-equal name abs-file-alist)))))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  abs-addrs-of-context-apply-1-lemma-10
  (implies
   (and
    (member-equal
     x
     (abs-addrs (abs-file->contents (cdr (car abs-file-alist1)))))
    (member-equal x
                  (abs-addrs (remove-assoc-equal (car (car abs-file-alist1))
                                                 (cdr abs-file-alist1)))))
   (intersectp-equal
    (abs-addrs (cdr abs-file-alist1))
    (abs-addrs (abs-file->contents (cdr (car abs-file-alist1))))))
  :hints
  (("goal"
    :use (:instance
          (:rewrite intersectp-member)
          (a x)
          (y (abs-addrs (abs-file->contents (cdr (car abs-file-alist1)))))
          (x (abs-addrs (cdr abs-file-alist1)))))))

(defthmd
  abs-addrs-of-context-apply-1-lemma-11
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
    (member-equal
     x
     (abs-addrs
      (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))))
    (no-duplicatesp-equal (abs-addrs abs-file-alist1)))
   (not (member-equal x
                      (abs-addrs (remove-assoc-equal name abs-file-alist1)))))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm abs-addrs-of-context-apply-1-lemma-12
  (implies (and (fat32-filename-p (car (car abs-file-alist1)))
                (abs-file-alist-p (cdr abs-file-alist1))
                (not (consp (assoc-equal (car (car abs-file-alist1))
                                         (cdr abs-file-alist1)))))
           (equal (remove-assoc-equal (car (car abs-file-alist1))
                                      (cdr abs-file-alist1))
                  (cdr abs-file-alist1)))
  :hints (("goal" :cases ((equal (car (car abs-file-alist1))
                                 nil)))))

(defthm
  abs-addrs-of-context-apply-1-lemma-13
  (implies
   (and
    (not (member-equal x
                       (abs-addrs (remove-assoc-equal name abs-file-alist1))))
    (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
    (not (member-equal x (abs-addrs abs-file-alist2)))
    (abs-file-alist-p abs-file-alist2)
    (abs-file-alist-p abs-file-alist1)
    (abs-no-dups-p abs-file-alist1))
   (not
    (member-equal
     x
     (abs-addrs
      (put-assoc-equal
       name
       (abs-file (abs-file->dir-ent (cdr (assoc-equal name abs-file-alist1)))
                 abs-file-alist2)
       abs-file-alist1)))))
  :hints
  (("goal"
    :in-theory (e/d ((:definition abs-addrs)
                     intersectp-equal abs-no-dups-p)
                    (intersectp-is-commutative))
    :expand ((abs-no-dups-p abs-file-alist1)
             (abs-file-alist-p abs-file-alist1))
    :induct
    (put-assoc-equal
     name
     (abs-file (abs-file->dir-ent (cdr (assoc-equal name abs-file-alist1)))
               abs-file-alist2)
     abs-file-alist1))))

(defthm
  abs-addrs-of-context-apply-1-lemma-14
  (implies
   (not (context-apply-ok abs-file-alist1
                          abs-file-alist2 x x-path))
   (equal (context-apply abs-file-alist1
                         abs-file-alist2 x x-path)
          (abs-fs-fix abs-file-alist1)))
  :hints (("goal" :in-theory (enable context-apply-ok))))

(defthm
  abs-addrs-of-context-apply-1-lemma-15
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
    (not
     (member-equal
      x
      (abs-addrs
       (context-apply
        (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))
        abs-file-alist2 x x-path))))
    (integerp x)
    (<= 0 x)
    (no-duplicatesp-equal (abs-addrs abs-file-alist1))
    (not
     (equal
      (put-assoc-equal
       name
       (abs-file
        (abs-file->dir-ent (cdr (assoc-equal name abs-file-alist1)))
        (context-apply
         (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))
         abs-file-alist2 x x-path))
       abs-file-alist1)
      abs-file-alist1))
    (abs-fs-p abs-file-alist1)
    (abs-file-alist-p abs-file-alist2))
   (not
    (member-equal
     x
     (abs-addrs
      (put-assoc-equal
       name
       (abs-file
        (abs-file->dir-ent (cdr (assoc-equal name abs-file-alist1)))
        (context-apply
         (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))
         abs-file-alist2 x x-path))
       abs-file-alist1)))))
  :hints
  (("goal"
    :in-theory (disable put-assoc-equal-without-change
                        (:rewrite abs-addrs-of-context-apply-1-lemma-7))
    :use
    ((:instance
      put-assoc-equal-without-change
      (alist abs-file-alist1)
      (val
       (abs-file
        (abs-file->dir-ent (cdr (assoc-equal name abs-file-alist1)))
        (context-apply
         (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))
         abs-file-alist2 x x-path))))
     (:instance
      (:rewrite abs-addrs-of-context-apply-1-lemma-7)
      (abs-file-alist1
       (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))))
     (:rewrite abs-addrs-of-context-apply-1-lemma-11))
    :do-not-induct t)))

(defthmd
  abs-addrs-of-context-apply-1
  (implies
   (and (natp x)
        (no-duplicatesp-equal (abs-addrs abs-file-alist1))
        (context-apply-ok abs-file-alist1
                          abs-file-alist2 x x-path)
        (not (intersectp-equal (abs-addrs abs-file-alist1)
                               (abs-addrs (abs-fs-fix abs-file-alist2))))
        (abs-fs-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist2))
   (not (member-equal x
                      (abs-addrs (context-apply abs-file-alist1
                                                abs-file-alist2 x x-path)))))
  :hints (("goal" :in-theory (enable abs-addrs
                                     context-apply context-apply-ok)
           :induct (context-apply abs-file-alist1
                                  abs-file-alist2 x x-path))))

;; This just might be made obsolete soon...
(defthm
  abs-addrs-of-context-apply-2-lemma-1
  (implies (not (intersectp-equal (abs-addrs abs-file-alist1)
                                  y))
           (not (intersectp-equal (abs-addrs (remove-equal x abs-file-alist1))
                                  y)))
  :hints (("goal" :in-theory (e/d (abs-addrs intersectp-equal)
                                  (intersectp-is-commutative)))))

(defthm
  abs-addrs-of-context-apply-2-lemma-3
  (implies
   (and
    (abs-no-dups-p abs-file-alist1)
    (abs-file-alist-p abs-file-alist1)
    (abs-file-alist-p abs-file-alist2)
    (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
    (not
     (intersectp-equal (abs-addrs (remove-assoc-equal name abs-file-alist1))
                       y))
    (not (intersectp-equal (abs-addrs abs-file-alist2)
                           y)))
   (not
    (intersectp-equal
     (abs-addrs
      (put-assoc-equal
       name
       (abs-file (abs-file->dir-ent (cdr (assoc-equal name abs-file-alist1)))
                 abs-file-alist2)
       abs-file-alist1))
     y)))
  :hints (("goal" :in-theory (e/d ((:definition abs-addrs)
                                   intersectp-equal abs-file-alist-p)
                                  (intersectp-is-commutative))
           :expand (abs-no-dups-p abs-file-alist1))))

(defthm
  abs-addrs-of-context-apply-2-lemma-4
  (subsetp-equal (abs-addrs (remove-assoc-equal name abs-file-alist))
                 (abs-addrs abs-file-alist))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  abs-addrs-of-context-apply-2-lemma-6
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
    (not
     (intersectp-equal
      (abs-addrs
       (context-apply
        (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))
        abs-file-alist2 x x-path))
      y))
    (abs-file-alist-p abs-file-alist2)
    (not (intersectp-equal (abs-addrs abs-file-alist1)
                           y))
    (abs-fs-p abs-file-alist1))
   (not
    (intersectp-equal
     (abs-addrs
      (put-assoc-equal
       name
       (abs-file
        (abs-file->dir-ent (cdr (assoc-equal name abs-file-alist1)))
        (context-apply
         (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))
         abs-file-alist2 x x-path))
       abs-file-alist1))
     y)))
  :hints
  (("goal"
    :use
    (:instance (:rewrite intersect-with-subset)
               (z y)
               (y (abs-addrs abs-file-alist1))
               (x (abs-addrs (remove-assoc-equal name abs-file-alist1)))))))

(defthm
  abs-addrs-of-context-apply-2-lemma-11
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                            abs-file-alist1)))
    (not
     (intersectp-equal
      (abs-addrs
       (context-apply (abs-file->contents
                       (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                         abs-file-alist1)))
                      abs-file-alist2 x (cdr x-path)))
      y))
    (abs-file-alist-p abs-file-alist2)
    (not (intersectp-equal (abs-addrs abs-file-alist1)
                           y))
    (abs-fs-p abs-file-alist1)
    (not (natp x)))
   (not
    (intersectp-equal
     (abs-addrs
      (put-assoc-equal
       (fat32-filename-fix (car x-path))
       (abs-file
        (abs-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                             abs-file-alist1)))
        (context-apply
         (abs-file->contents
          (cdr (assoc-equal (fat32-filename-fix (car x-path))
                            abs-file-alist1)))
         abs-file-alist2 0 (cdr x-path)))
       abs-file-alist1))
     y)))
  :instructions (:promote (:dive 1)
                          (:rewrite abs-addrs-of-context-apply-2-lemma-6)
                          (:dive 1 1 1 3)
                          (:= (nfix x))
                          :top :bash))

(defthm
  abs-addrs-of-context-apply-2-lemma-7
  (implies
   (and (abs-file-alist-p abs-file-alist2)
        (not (intersectp-equal (abs-addrs abs-file-alist1)
                               y))
        (not (intersectp-equal (abs-addrs (abs-fs-fix abs-file-alist2))
                               y))
        (abs-fs-p abs-file-alist1))
   (not (intersectp-equal (abs-addrs (context-apply abs-file-alist1
                                                    abs-file-alist2 x x-path))
                          y)))
  :hints (("goal" :in-theory (e/d ((:definition abs-addrs) context-apply)
                                  (intersectp-is-commutative)))))

(defthm
  abs-addrs-of-context-apply-2-lemma-8
  (implies
   (not (intersectp-equal
         (abs-addrs (abs-file->contents (cdr (car abs-file-alist1))))
         (abs-addrs (cdr abs-file-alist1))))
   (not
    (intersectp-equal
     (abs-addrs (remove-assoc-equal name (cdr abs-file-alist1)))
     (abs-addrs (abs-file->contents$inline (cdr (car abs-file-alist1)))))))
  :hints
  (("goal"
    :use
    ((:instance
      (:rewrite intersect-with-subset)
      (z (abs-addrs (abs-file->contents (cdr (car abs-file-alist1)))))
      (x (abs-addrs (remove-assoc-equal name (cdr abs-file-alist1))))
      (y (abs-addrs (cdr abs-file-alist1))))))))

(defthm
  abs-addrs-of-context-apply-2-lemma-9
  (implies
   (and (abs-directory-file-p (cdr (assoc-equal name (cdr abs-file-alist1))))
        (not (intersectp-equal
              (abs-addrs (abs-file->contents (cdr (car abs-file-alist1))))
              (abs-addrs (cdr abs-file-alist1))))
        (not (intersectp-equal
              (abs-addrs (abs-file->contents (cdr (car abs-file-alist1))))
              (abs-addrs abs-file-alist2)))
        (abs-no-dups-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist2))
   (not
    (intersectp-equal
     (abs-addrs (abs-file->contents (cdr (car abs-file-alist1))))
     (abs-addrs
      (put-assoc-equal
       name
       (abs-file
        (abs-file->dir-ent (cdr (assoc-equal name (cdr abs-file-alist1))))
        abs-file-alist2)
       (cdr abs-file-alist1))))))
  :hints
  (("goal"
    :in-theory (disable intersectp-is-commutative)
    :expand
    ((:with
      intersectp-is-commutative
      (intersectp-equal
       (abs-addrs (abs-file->contents (cdr (car abs-file-alist1))))
       (abs-addrs
        (put-assoc-equal
         name
         (abs-file
          (abs-file->dir-ent (cdr (assoc-equal name (cdr abs-file-alist1))))
          abs-file-alist2)
         (cdr abs-file-alist1)))))
     (:with
      intersectp-is-commutative
      (intersectp-equal
       (abs-addrs abs-file-alist2)
       (abs-addrs
        (abs-file->contents$inline (cdr (car abs-file-alist1))))))))))

(defthm
  abs-addrs-of-context-apply-2-lemma-12
  (implies
   (and (abs-directory-file-p (cdr (car abs-file-alist1)))
        (not (intersectp-equal
              (abs-addrs (remove-assoc-equal (car (car abs-file-alist1))
                                             (cdr abs-file-alist1)))
              (abs-addrs abs-file-alist2)))
        (abs-no-dups-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist1))
   (not (intersectp-equal (abs-addrs abs-file-alist2)
                          (abs-addrs (cdr abs-file-alist1)))))
  :hints (("goal" :expand ((abs-no-dups-p abs-file-alist1)
                           (abs-file-alist-p abs-file-alist1)))))

(defthm
  abs-addrs-of-context-apply-2-lemma-2
  (implies
   (and
    (not
     (intersectp-equal
      (abs-addrs (remove-assoc-equal name (cdr abs-file-alist1)))
      (abs-addrs
       (abs-file->contents (cdr (assoc-equal name (cdr abs-file-alist1)))))))
    (abs-directory-file-p (cdr (assoc-equal name (cdr abs-file-alist1))))
    (not (member-equal (car abs-file-alist1)
                       (abs-addrs (cdr abs-file-alist1)))))
   (not
    (intersectp-equal
     (abs-addrs
      (abs-file->contents (cdr (assoc-equal name (cdr abs-file-alist1)))))
     (cons (car abs-file-alist1)
           (abs-addrs (remove-assoc-equal name (cdr abs-file-alist1)))))))
  :hints
  (("goal"
    :in-theory (e/d (intersectp-equal)
                    (intersectp-is-commutative))
    :expand
    (:with
     intersectp-is-commutative
     (intersectp-equal
      (abs-addrs
       (abs-file->contents (cdr (assoc-equal name (cdr abs-file-alist1)))))
      (cons (car abs-file-alist1)
            (abs-addrs (remove-assoc-equal name (cdr abs-file-alist1)))))))))

(defthm
  abs-addrs-of-context-apply-2-lemma-14
  (implies
   (and (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
        (no-duplicatesp-equal (abs-addrs abs-file-alist1))
        (abs-no-dups-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist1))
   (not
    (intersectp-equal
     (abs-addrs
      (abs-file->contents$inline (cdr (assoc-equal name abs-file-alist1))))
     (abs-addrs (remove-assoc-equal name abs-file-alist1)))))
  :hints (("goal" :in-theory (e/d (abs-addrs) nil)
           :expand ((abs-no-dups-p abs-file-alist1)
                    (abs-file-alist-p abs-file-alist1)))))

(defthm
  abs-addrs-of-context-apply-2-lemma-15
  (implies
   (not (intersectp-equal (abs-addrs abs-file-alist1)
                          (abs-addrs abs-file-alist2)))
   (not
    (intersectp-equal (abs-addrs abs-file-alist2)
                      (abs-addrs (remove-assoc-equal name abs-file-alist1)))))
  :hints
  (("goal"
    :use (:instance (:rewrite intersect-with-subset)
                    (z (abs-addrs abs-file-alist2))
                    (x (abs-addrs (remove-assoc-equal name abs-file-alist1)))
                    (y (abs-addrs abs-file-alist1))))))

(defthm
  abs-addrs-of-context-apply-2-lemma-10
  (implies
   (and (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
        (no-duplicatesp-equal (abs-addrs abs-file-alist1))
        (not (intersectp-equal (abs-addrs abs-file-alist1)
                               (abs-addrs (abs-fs-fix abs-file-alist2))))
        (abs-fs-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist2))
   (not
    (intersectp-equal
     (abs-addrs (remove-assoc-equal name abs-file-alist1))
     (abs-addrs
      (context-apply
       (abs-file->contents$inline (cdr (assoc-equal name abs-file-alist1)))
       abs-file-alist2 x (cdr x-path))))))
  :hints
  (("goal"
    :in-theory (disable intersectp-is-commutative)
    :do-not-induct t
    :expand
    (:with
     intersectp-is-commutative
     (intersectp-equal
      (abs-addrs (remove-assoc-equal name abs-file-alist1))
      (abs-addrs
       (context-apply
        (abs-file->contents$inline (cdr (assoc-equal name abs-file-alist1)))
        abs-file-alist2 x (cdr x-path))))))))

(defthm
  abs-addrs-of-context-apply-2-lemma-16
  (implies
   (and
    (no-duplicatesp-equal
     (abs-addrs
      (context-apply
       (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                             abs-file-alist1)))
       abs-file-alist2 x (cdr x-path))))
    (not (natp x)))
   (no-duplicatesp-equal
    (abs-addrs
     (context-apply (abs-file->contents$inline
                     (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                       abs-file-alist1)))
                    abs-file-alist2 '0
                    (cdr x-path)))))
  :instructions (:promote (:dive 1 1 3)
                          (:= (nfix x))
                          :top :bash))

(defthm
  abs-addrs-of-context-apply-3-lemma-1
  (implies
   (and
    (consp (assoc-equal (fat32-filename-fix (car x2-path))
                        abs-file-alist1))
    (abs-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                                            abs-file-alist1)))
    (not
     (equal
      (put-assoc-equal
       (fat32-filename-fix (car x2-path))
       (abs-file
        (abs-file->dir-ent
         (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                           abs-file-alist1)))
        (context-apply
         (abs-file->contents
          (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                            abs-file-alist1)))
         abs-file-alist2 x2 (cdr x2-path)))
       abs-file-alist1)
      abs-file-alist1)))
   (not
    (equal
     (abs-file->contents$inline
      (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                        abs-file-alist1)))
     (context-apply (abs-file->contents$inline
                     (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                                       abs-file-alist1)))
                    abs-file-alist2 x2 (cdr x2-path))))))

(defthm
  abs-addrs-of-context-apply-3-lemma-2
  (implies
   (and
    (member-equal
     x
     (abs-addrs (abs-file->contents (cdr (car abs-file-alist1)))))
    (not (intersectp-equal
          (abs-addrs (cdr abs-file-alist1))
          (abs-addrs (abs-file->contents (cdr (car abs-file-alist1)))))))
   (not (member-equal x (abs-addrs (cdr abs-file-alist1)))))
  :hints
  (("goal"
    :use (:instance
          (:rewrite intersectp-member)
          (a x)
          (y (abs-addrs (abs-file->contents (cdr (car abs-file-alist1)))))
          (x (abs-addrs (cdr abs-file-alist1)))))))

(defthm
  abs-addrs-of-context-apply-3-lemma-3
  (implies
   (and
    (member-equal
     x
     (abs-addrs
      (abs-file->contents (cdr (assoc-equal name (cdr abs-file-alist1))))))
    (abs-directory-file-p (cdr (assoc-equal name (cdr abs-file-alist1))))
    (not (intersectp-equal
          (abs-addrs (cdr abs-file-alist1))
          (abs-addrs (abs-file->contents (cdr (car abs-file-alist1)))))))
   (not
    (member-equal
     x
     (abs-addrs (abs-file->contents$inline (cdr (car abs-file-alist1)))))))
  :hints (("goal" :in-theory (enable intersectp-member))))

(defthm
  abs-addrs-of-context-apply-3-lemma-4
  (implies
   (and
    (member-equal
     x
     (abs-addrs
      (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))))
    (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
    (equal
     (abs-addrs
      (context-apply
       (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))
       abs-file-alist2 x (cdr x-path)))
     (remove-equal
      x
      (abs-addrs
       (abs-file->contents (cdr (assoc-equal name abs-file-alist1))))))
    (no-duplicatesp-equal (abs-addrs abs-file-alist1)))
   (equal
    (abs-addrs
     (put-assoc-equal
      name
      (abs-file
       (abs-file->dir-ent (cdr (assoc-equal name abs-file-alist1)))
       (context-apply
        (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))
        abs-file-alist2 x (cdr x-path)))
      abs-file-alist1))
    (remove-equal x (abs-addrs abs-file-alist1))))
  :hints
  (("goal"
    :in-theory (enable abs-addrs)
    :induct
    (mv
     (abs-addrs abs-file-alist1)
     (put-assoc-equal
      name
      (abs-file
       (abs-file->dir-ent (cdr (assoc-equal name abs-file-alist1)))
       (context-apply
        (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))
        abs-file-alist2 x (cdr x-path)))
      abs-file-alist1)))))

(defthm
  abs-addrs-of-context-apply-3-lemma-5
  (implies
   (and
    (abs-fs-p abs-file-alist1)
    (abs-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                            abs-file-alist1)))
    (natp x)
    (not
     (equal
      (put-assoc-equal
       (fat32-filename-fix (car x-path))
       (abs-file
        (abs-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                             abs-file-alist1)))
        (context-apply
         (abs-file->contents
          (cdr (assoc-equal (fat32-filename-fix (car x-path))
                            abs-file-alist1)))
         abs-file-alist2 x (cdr x-path)))
       abs-file-alist1)
      abs-file-alist1)))
   (member-equal
    x
    (abs-addrs (abs-file->contents$inline
                (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                  abs-file-alist1))))))
  :hints
  (("goal"
    :in-theory (disable put-assoc-equal-without-change)
    :use
    ((:instance
      put-assoc-equal-without-change
      (alist abs-file-alist1)
      (val
       (abs-file
        (abs-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                             abs-file-alist1)))
        (context-apply
         (abs-file->contents
          (cdr (assoc-equal (fat32-filename-fix (car x-path))
                            abs-file-alist1)))
         abs-file-alist2 x (cdr x-path))))
      (name (fat32-filename-fix (car x-path))))))))

(defthm
  abs-addrs-of-context-apply-3-lemma-6
  (implies (m1-file-alist-p abs-file-alist2)
           (equal (append (remove-equal x (abs-addrs abs-file-alist1))
                          (abs-addrs abs-file-alist2))
                  (remove-equal x (abs-addrs abs-file-alist1))))
  :hints
  (("goal"
    :in-theory (disable (:type-prescription abs-addrs-when-m1-file-alist-p))
    :use ((:instance (:type-prescription abs-addrs-when-m1-file-alist-p)
                     (x abs-file-alist2))))))

(encapsulate
  ()

  (local
   (defthmd
     abs-addrs-of-context-apply-3-lemma-7
     (implies
      (and (natp x)
           (no-duplicatesp-equal (abs-addrs (abs-fs-fix abs-file-alist1)))
           (abs-fs-p abs-file-alist2)
           (abs-complete abs-file-alist2)
           (context-apply-ok abs-file-alist1
                             abs-file-alist2 x x-path))
      (equal (abs-addrs (context-apply abs-file-alist1
                                       abs-file-alist2 x x-path))
             (remove-equal x
                           (abs-addrs (abs-fs-fix abs-file-alist1)))))
     :hints (("goal" :in-theory (e/d (context-apply context-apply-ok))
              :induct (context-apply abs-file-alist1
                                     abs-file-alist2 x x-path)))))

  (defthm
    abs-addrs-of-context-apply-3
    (implies
     (and (no-duplicatesp-equal (abs-addrs (abs-fs-fix abs-file-alist1)))
          (abs-complete (abs-fs-fix abs-file-alist2))
          (context-apply-ok abs-file-alist1
                            abs-file-alist2 x x-path))
     (equal (abs-addrs (context-apply abs-file-alist1
                                      abs-file-alist2 x x-path))
            (remove-equal (nfix x)
                          (abs-addrs (abs-fs-fix abs-file-alist1)))))
    :hints
    (("goal" :in-theory (disable nfix)
      :use (:instance abs-addrs-of-context-apply-3-lemma-7
                      (x (nfix x))
                      (abs-file-alist2 (abs-fs-fix abs-file-alist2)))))))

;; Both these names, below, merit some thought later...
(fty::defprod frame-val
              ((path fat32-filename-list-p)
               (dir abs-fs-p)
               (src natp)))

(fty::defalist frame
               :key-type nat
               :val-type frame-val
               :true-listp t)

(defthm nat-listp-of-strip-cars-when-frame-p
  (implies (frame-p frame)
           (nat-listp (strip-cars frame))))

;; That this lemma is needed is a reminder to get some list macros around
;; abs-file-alist-p...
(defthm
  unlink-abs-alloc-helper-1-guard-lemma-1
  (implies
   (and (integerp index)
        (<= 0 index)
        (abs-directory-file-p (cdr (assoc-equal path1 fs))))
   (abs-file-contents-p
    (cons
     index
     (remove-assoc-equal (car path2)
                         (abs-file->contents (cdr (assoc-equal path1 fs)))))))
  :hints (("goal" :in-theory (enable abs-file-contents-p abs-file-alist-p)
           :do-not-induct t)))

;; It's going to be incredibly hard to implement the thing which this helper
;; function is a part of, because in general when we're looking up a file we'll
;; have to go down many, many rabbit holes. We might want to look up
;; /usr/bin/busybox in an instrumented filesystem where /usr has 4 abstract
;; addresses in it, and one of them has /usr/bin, and that one has 8 abstract
;; addresses in it, and finally it turns out none of the 8 has busybox in
;; it. We'd have to process abstract addresses through a queue into which we
;; keep adding them, accompanied by relative paths, as we find ourselves
;; stymied and over and over again while looking for a file. It pretty much
;; goes without saying that reasoning about abstract allocations and
;; deallocations would get very hard. It might be possible to reason about
;; single steps of allocation and deallocation - respectively taking a
;; substructure out of a directory we know to exist and putting it back where
;; we know no duplicates to exist - but it's still going to be hard.
;;
;; Return 4 values - the abs-file-alist, potentially changed; the list of
;; abstract addresses to look into, potentially empty; the substructure we
;; pulled out, potentially the default abs-file-alist; and the path from where
;; the substructure was pulled out, potentially empty.
(defund
  unlink-abs-alloc-helper-1 (fs path index)
  (declare (xargs :guard (and (abs-file-alist-p fs)
                              (fat32-filename-list-p path)
                              (natp index))
                  :measure (len path)
                  :guard-debug t))
  (b*
      (;; This is an error condition.
       ((when (atom path)) (mv fs nil nil *empty-fat32-name*))
       (head (mbe :exec (car path)
                  :logic (fat32-filename-fix (car path))))
       ((when (atom (abs-assoc head fs)))
        (mv fs (abs-top-addrs fs) nil head))
       ((when (atom (cdr path)))
        (mv (list* (mbe :exec index :logic (nfix index))
                   (abs-remove-assoc head fs))
            nil (list (abs-assoc head fs))
            head))
       ;; This is an error condition.
       ((unless (abs-directory-file-p (cdr (abs-assoc head fs))))
        (mv fs nil nil *empty-fat32-name*))
       ((mv insert addr-list sub-fs final-head)
        (unlink-abs-alloc-helper-1
         (abs-file->contents (cdr (abs-assoc head fs)))
         (cdr path)
         index)))
    (mv
     (abs-put-assoc
      head
      (abs-file (abs-file->dir-ent (cdr (abs-assoc head fs)))
                insert)
      fs)
     addr-list sub-fs final-head)))

(defthm
  unlink-abs-alloc-helper-1-correctness-1-lemma-1
  (implies
   (and (abs-file-alist-p abs-file-alist)
        (integerp index)
        (<= 0 index))
   (abs-file-alist-p (cons index
                           (remove-assoc-equal (fat32-filename-fix (car path))
                                               abs-file-alist))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable abs-file-alist-p))))

(defthm
  unlink-abs-alloc-helper-1-correctness-1
  (implies (abs-file-alist-p abs-file-alist)
           (abs-file-alist-p
            (mv-nth 0
                    (unlink-abs-alloc-helper-1 abs-file-alist path index))))
  :hints (("goal" :in-theory (enable unlink-abs-alloc-helper-1))))

(assert-event
 (frame-p
  (list
   (cons
    0
    (frame-val
     nil
     (list
      (cons
       "INITRD  IMG"
       (abs-file (dir-ent-fix nil) ""))
      (cons
       "RUN        "
       (abs-file
        (dir-ent-fix nil)
        (list
         (cons
          "RSYSLOGDPID"
          (abs-file (dir-ent-fix nil) "")))))
      (cons
       "USR        "
       (abs-file (dir-ent-fix nil)
                 (list
                  (cons
                   "LOCAL      "
                   (abs-file (dir-ent-fix nil) ()))
                  (cons
                   "LIB        "
                   (abs-file (dir-ent-fix nil) ()))
                  1))))
     0))
   (cons
    1
    (frame-val
     (list "USR        ")
     (list
      (cons
       "SHARE      "
       (abs-file (dir-ent-fix nil) ()))
      (cons
       "BIN        "
       (abs-file (dir-ent-fix nil)
                 (list
                  (cons
                   "CAT        "
                   (abs-file (dir-ent-fix nil) ""))
                  2
                  (cons
                   "TAC        "
                   (abs-file (dir-ent-fix nil) ""))))))
     0))
   (cons
    2
    (frame-val
     (list "USR        " "BIN        ")
     (list
      (cons
       "COL        "
       (abs-file (dir-ent-fix nil) "")))
     1)))))

(assert-event
 (mv-let
   (fs addr-list sub-fs final-head)
   (unlink-abs-alloc-helper-1
    (list
     (cons
      "INITRD  IMG"
      (abs-file (dir-ent-fix nil) ""))
     (cons
      "RUN        "
      (abs-file
       (dir-ent-fix nil)
       (list
        (cons
         "RSYSLOGDPID"
         (abs-file (dir-ent-fix nil) "")))))
     (cons
      "USR        "
      (abs-file (dir-ent-fix nil)
                (list
                 (cons
                  "LOCAL      "
                  (abs-file (dir-ent-fix nil) ()))
                 (cons
                  "LIB        "
                  (abs-file (dir-ent-fix nil) ()))
                 1))))
    (list "INITRD  IMG")
    3)
   (and
    (equal
     fs
     (list
      3
      (cons
       "RUN        "
       (abs-file
        (dir-ent-fix nil)
        (list
         (cons
          "RSYSLOGDPID"
          (abs-file (dir-ent-fix nil) "")))))
      (cons
       "USR        "
       (abs-file (dir-ent-fix nil)
                 (list
                  (cons
                   "LOCAL      "
                   (abs-file (dir-ent-fix nil) ()))
                  (cons
                   "LIB        "
                   (abs-file (dir-ent-fix nil) ()))
                  1)))))
    (equal
     addr-list
     nil)
    (equal
     sub-fs
     (list
      (cons
       "INITRD  IMG"
       (abs-file (dir-ent-fix nil) ""))))
    (equal
     final-head
     "INITRD  IMG"))))

(assert-event
 (mv-let
   (fs addr-list sub-fs final-head)
   (unlink-abs-alloc-helper-1
    (list
     (cons
      "INITRD  IMG"
      (abs-file (dir-ent-fix nil) ""))
     (cons
      "RUN        "
      (abs-file
       (dir-ent-fix nil)
       (list
        (cons
         "RSYSLOGDPID"
         (abs-file (dir-ent-fix nil) "")))))
     (cons
      "USR        "
      (abs-file (dir-ent-fix nil)
                (list
                 (cons
                  "LOCAL      "
                  (abs-file (dir-ent-fix nil) ()))
                 (cons
                  "LIB        "
                  (abs-file (dir-ent-fix nil) ()))
                 1))))
    (list "RUN        " "RSYSLOGDPID")
    3)
   (and
    (equal
     fs
     (list
      (cons
       "INITRD  IMG"
       (abs-file (dir-ent-fix nil) ""))
      (cons
       "RUN        "
       (abs-file
        (dir-ent-fix nil)
        (list
         3)))
      (cons
       "USR        "
       (abs-file (dir-ent-fix nil)
                 (list
                  (cons
                   "LOCAL      "
                   (abs-file (dir-ent-fix nil) ()))
                  (cons
                   "LIB        "
                   (abs-file (dir-ent-fix nil) ()))
                  1)))))
    (equal
     addr-list
     nil)
    (equal
     sub-fs
     (list
      (cons
       "RSYSLOGDPID"
       (abs-file (dir-ent-fix nil) ""))))
    (equal
     final-head
     "RSYSLOGDPID"))))

(assert-event
 (mv-let
   (fs addr-list sub-fs final-head)
   (unlink-abs-alloc-helper-1
    (list
     (cons
      "INITRD  IMG"
      (abs-file (dir-ent-fix nil) ""))
     (cons
      "RUN        "
      (abs-file
       (dir-ent-fix nil)
       (list
        (cons
         "RSYSLOGDPID"
         (abs-file (dir-ent-fix nil) "")))))
     (cons
      "USR        "
      (abs-file (dir-ent-fix nil)
                (list
                 (cons
                  "LOCAL      "
                  (abs-file (dir-ent-fix nil) ()))
                 (cons
                  "LIB        "
                  (abs-file (dir-ent-fix nil) ()))
                 1))))
    (list "USR        " "BIN        " "COL        ")
    3)
   (and
    (equal
     fs
     (list
      (cons
       "INITRD  IMG"
       (abs-file (dir-ent-fix nil) ""))
      (cons
       "RUN        "
       (abs-file
        (dir-ent-fix nil)
        (list
         (cons
          "RSYSLOGDPID"
          (abs-file (dir-ent-fix nil) "")))))
      (cons
       "USR        "
       (abs-file (dir-ent-fix nil)
                 (list
                  (cons
                   "LOCAL      "
                   (abs-file (dir-ent-fix nil) ()))
                  (cons
                   "LIB        "
                   (abs-file (dir-ent-fix nil) ()))
                  1)))))
    (equal
     addr-list
     (list 1))
    (equal
     sub-fs
     nil)
    (equal
     final-head
     "BIN        "))))

;; Let's simplify this. We will have some prefix reasoning - that's pretty much
;; unavoidable. Still, we aren't going to claim that we're starting from the
;; root directory (i.e. \mathcal{F}) and following the precise sequence of
;; paths which will lead us to the file we want at the path we want. That will
;; require a queue, which is messy... Instead, we're going to look through
;; all the elements in the frame until we have ruled out the existence of an
;; abstract variable which has this file in it.
(defund
  stat-abs-lookup (frame path)
  (declare (xargs :guard (and (frame-p frame)
                              (fat32-filename-list-p path))
                  :guard-debug t))
  (b*
      (((when (atom frame)) nil)
       (head-frame-val (cdr (car frame)))
       ((when
            (and
             (equal (frame-val->path head-frame-val)
                    (butlast path 1))
             (consp
              (abs-assoc (car (last path))
                         (frame-val->dir head-frame-val)))))
        t))
    (stat-abs-lookup (cdr frame) path)))

(assert-event
 (equal
  (stat-abs-lookup
   (list
    (cons
     0
     (frame-val
      nil
      (list
       (cons
        "INITRD  IMG"
        (abs-file (dir-ent-fix nil) ""))
       (cons
        "RUN        "
        (abs-file
         (dir-ent-fix nil)
         (list
          (cons
           "RSYSLOGDPID"
           (abs-file (dir-ent-fix nil) "")))))
       (cons
        "USR        "
        (abs-file (dir-ent-fix nil)
                  (list
                   (cons
                    "LOCAL      "
                    (abs-file (dir-ent-fix nil) ()))
                   (cons
                    "LIB        "
                    (abs-file (dir-ent-fix nil) ()))
                   1))))
      0))
    (cons
     1
     (frame-val
      (list "USR        ")
      (list
       (cons
        "SHARE      "
        (abs-file (dir-ent-fix nil) ()))
       (cons
        "BIN        "
        (abs-file (dir-ent-fix nil)
                  (list
                   (cons
                    "CAT        "
                    (abs-file (dir-ent-fix nil) ""))
                   2
                   (cons
                    "TAC        "
                    (abs-file (dir-ent-fix nil) ""))))))
      0))
    (cons
     2
     (frame-val
      (list "USR        " "BIN        ")
      (list
       (cons
        "COL        "
        (abs-file (dir-ent-fix nil) "")))
      1)))
   (list "INITRD  IMG"))
  t))

(assert-event
 (equal
  (stat-abs-lookup
   (list
    (cons
     0
     (frame-val
      nil
      (list
       (cons
        "INITRD  IMG"
        (abs-file (dir-ent-fix nil) ""))
       (cons
        "RUN        "
        (abs-file
         (dir-ent-fix nil)
         (list
          (cons
           "RSYSLOGDPID"
           (abs-file (dir-ent-fix nil) "")))))
       (cons
        "USR        "
        (abs-file (dir-ent-fix nil)
                  (list
                   (cons
                    "LOCAL      "
                    (abs-file (dir-ent-fix nil) ()))
                   (cons
                    "LIB        "
                    (abs-file (dir-ent-fix nil) ()))
                   1))))
      0))
    (cons
     1
     (frame-val
      (list "USR        ")
      (list
       (cons
        "SHARE      "
        (abs-file (dir-ent-fix nil) ()))
       (cons
        "BIN        "
        (abs-file (dir-ent-fix nil)
                  (list
                   (cons
                    "CAT        "
                    (abs-file (dir-ent-fix nil) ""))
                   2
                   (cons
                    "TAC        "
                    (abs-file (dir-ent-fix nil) ""))))))
      0))
    (cons
     2
     (frame-val
      (list "USR        " "BIN        ")
      (list
       (cons
        "COL        "
        (abs-file (dir-ent-fix nil) "")))
      1)))
   (list "USR        " "BIN        " "COL        "))
  t))

(assert-event
 (equal
  (stat-abs-lookup
   (list
    (cons
     0
     (frame-val
      nil
      (list
       (cons
        "INITRD  IMG"
        (abs-file (dir-ent-fix nil) ""))
       (cons
        "RUN        "
        (abs-file
         (dir-ent-fix nil)
         (list
          (cons
           "RSYSLOGDPID"
           (abs-file (dir-ent-fix nil) "")))))
       (cons
        "USR        "
        (abs-file (dir-ent-fix nil)
                  (list
                   (cons
                    "LOCAL      "
                    (abs-file (dir-ent-fix nil) ()))
                   (cons
                    "LIB        "
                    (abs-file (dir-ent-fix nil) ()))
                   1))))
      0))
    (cons
     1
     (frame-val
      (list "USR        ")
      (list
       (cons
        "SHARE      "
        (abs-file (dir-ent-fix nil) ()))
       (cons
        "BIN        "
        (abs-file (dir-ent-fix nil)
                  (list
                   (cons
                    "CAT        "
                    (abs-file (dir-ent-fix nil) ""))
                   2
                   (cons
                    "TAC        "
                    (abs-file (dir-ent-fix nil) ""))))))
      0))
    (cons
     2
     (frame-val
      (list "USR        " "BIN        ")
      (list
       (cons
        "COL        "
        (abs-file (dir-ent-fix nil) "")))
      1)))
   (list "USR        " "BIN        " "FIREFOX    "))
  nil))

;; We didn't include it in the guard, but... 0 should not be among the indices.
(defund 1st-complete (frame)
  (declare (xargs :guard (frame-p frame)))
  (b* (((when (atom frame)) 0)
       (head-index (caar frame))
       (head-frame-val (cdar frame)))
    (if (abs-complete (frame-val->dir head-frame-val))
        (mbe :exec head-index :logic (nfix head-index))
      (1st-complete (cdr frame)))))

(defthm 1st-complete-correctness-1
  (implies (not (zp (1st-complete frame)))
           (consp (assoc-equal (1st-complete frame)
                               frame)))
  :hints (("goal" :in-theory (enable 1st-complete)))
  :rule-classes :type-prescription)

(defthm
  1st-complete-of-put-assoc-lemma-1
  (implies (and (frame-p frame)
                (not (member-equal (car (car frame))
                                   (strip-cars (cdr frame)))))
           (equal (remove-assoc-equal (car (car frame))
                                      (cdr frame))
                  (cdr frame)))
  :hints (("goal" :in-theory (disable (:rewrite len-of-remove-assoc-equal-2))
           :use (:instance (:rewrite len-of-remove-assoc-equal-2)
                           (alist (cdr frame))
                           (x (car (car frame)))))))

(defthm
  1st-complete-of-put-assoc-1
  (implies
   (and
    (frame-p frame)
    (not (equal name 0))
    (not (equal (1st-complete frame) 0))
    (or (atom (assoc-equal name frame))
        (subsetp-equal
         (abs-addrs (frame-val->dir val))
         (abs-addrs (frame-val->dir (cdr (assoc-equal name frame)))))))
   (not (equal (1st-complete (put-assoc-equal name val frame))
               0)))
  :hints (("goal" :in-theory (enable 1st-complete)))
  :rule-classes
  (:rewrite
   (:linear
    :corollary
    (implies
     (and
      (frame-p frame)
      (not (equal name 0))
      (not (equal (1st-complete frame) 0))
      (or (atom (assoc-equal name frame))
          (subsetp-equal
           (abs-addrs (frame-val->dir val))
           (abs-addrs (frame-val->dir (cdr (assoc-equal name frame)))))))
     (> (1st-complete (put-assoc-equal name val frame))
        0)))))

(defthm
  1st-complete-of-put-assoc-2
  (implies (and (frame-p frame)
                (no-duplicatesp-equal (strip-cars frame))
                (not (equal (1st-complete (put-assoc-equal name val frame))
                            name)))
           (equal (1st-complete (put-assoc-equal name val frame))
                  (1st-complete (remove-assoc-equal name frame))))
  :hints (("goal" :in-theory (enable 1st-complete))))

;; Perhaps this should be disabled or removed.
(defthm
  1st-complete-of-put-assoc-3
  (implies (and (frame-p frame)
                (no-duplicatesp-equal (strip-cars frame))
                (consp (abs-addrs (frame-val->dir val))))
           (equal (1st-complete (put-assoc-equal name val frame))
                  (1st-complete (remove-assoc-equal name frame))))
  :hints (("goal" :in-theory (enable 1st-complete))))

(defthm 1st-complete-of-remove-assoc-1
  (implies (and (not (zp x))
                (case-split (not (equal x (1st-complete frame)))))
           (equal (1st-complete (remove-assoc-equal x frame))
                  (1st-complete frame)))
  :hints (("goal" :in-theory (enable 1st-complete))))

(defthm
  1st-complete-of-remove-assoc-2
  (implies
   (and (not (zp y))
        (not (equal y
                    (1st-complete (remove-assoc-equal x frame)))))
   (equal (1st-complete (remove-assoc-equal x (remove-assoc-equal y frame)))
          (1st-complete (remove-assoc-equal x frame))))
  :hints (("goal" :in-theory (disable 1st-complete-of-remove-assoc-1)
           :use (:instance 1st-complete-of-remove-assoc-1
                           (frame (remove-assoc-equal x frame))
                           (x y)))))

(defthm frame-val-p-of-cdr-of-assoc-equal-when-frame-p
  (implies (frame-p x)
           (iff (frame-val-p (cdr (assoc-equal k x)))
                (or (consp (assoc-equal k x))
                    (frame-val-p nil))))
  :hints (("goal" :in-theory (enable frame-p))))

(defthm frame-p-of-put-assoc-equal
  (implies (frame-p alist)
           (equal (frame-p (put-assoc-equal name val alist))
                  (and (natp name) (frame-val-p val))))
  :hints (("goal" :in-theory (enable frame-p))))

(defthm frame-p-of-remove-assoc
  (implies (frame-p alist)
           (frame-p (remove-assoc-equal x alist)))
  :hints (("goal" :in-theory (enable frame-p))))

(defthm frame-p-of-remove1-assoc
  (implies (frame-p alist)
           (frame-p (remove1-assoc-equal x alist)))
  :hints (("goal" :in-theory (enable frame-p))))

(defund 1st-complete-src (frame)
  (declare (xargs :guard (and (frame-p frame)
                              (consp (assoc-equal (1st-complete frame)
                                                  frame)))))
  (frame-val->src (cdr (assoc-equal (1st-complete frame) frame))))

(defthm 1st-complete-src-of-remove-assoc-1
  (implies (and (not (zp x))
                (not (equal x (1st-complete frame))))
           (equal (1st-complete-src (remove-assoc-equal x frame))
                  (1st-complete-src frame)))
  :hints (("goal" :in-theory (enable 1st-complete-src))))

;; This is a "false" frame because the src value given to the root is 0, same
;; as its abstract variable. This is one of a few compromises in elegance
;; required for distinguishing the root, which is necessary to properly define
;; the collapse relation.
(defund frame-with-root (root frame)
  (declare (xargs :guard (and (abs-file-alist-p root)
                              (frame-p frame))))
  (list* (cons 0 (frame-val nil (abs-fs-fix root) 0))
         frame))

(defund frame->root (frame)
  (declare (xargs :guard (and (frame-p frame) (consp (assoc-equal 0 frame)))))
  (frame-val->dir (cdr (assoc-equal 0 frame))))

(defund frame->frame (frame)
  (declare (xargs :guard (frame-p frame)))
  (remove1-assoc-equal 0 frame))

(defthm frame->root-of-frame-with-root
  (equal (frame->root (frame-with-root root frame))
         (abs-fs-fix root))
  :hints (("Goal" :in-theory (enable frame-with-root frame->root)) ))

(defthm frame->frame-of-frame-with-root
  (equal (frame->frame (frame-with-root root frame))
         frame)
  :hints (("goal" :in-theory (enable frame-with-root frame->frame))))

(defthm frame-p-of-frame->frame
  (implies (frame-p frame)
           (frame-p (frame->frame frame)))
  :hints (("goal" :in-theory (enable frame->frame))))

(defthm abs-fs-p-of-frame->root
  (abs-fs-p (frame->root frame))
  :hints (("goal" :in-theory (enable frame->root))))

(defthm frame-with-root-correctness-1
  (consp (assoc-equal 0 (frame-with-root root frame)))
  :hints (("Goal" :in-theory (enable frame-with-root)))
  :rule-classes :type-prescription)

(defthm frame-with-root-of-abs-fs-fix
  (equal (frame-with-root (abs-fs-fix root)
                          frame)
         (frame-with-root root frame))
  :hints (("goal" :in-theory (enable frame-with-root))))

(defthmd no-duplicatesp-of-strip-cars-of-frame->frame
  (implies
   (no-duplicatesp-equal (strip-cars frame))
   (no-duplicatesp-equal (strip-cars (frame->frame frame))))
  :hints (("goal" :in-theory (enable frame->frame))))

;; This is because of fixing.
(defthm frame-p-of-frame-with-root
  (equal (frame-p (frame-with-root root frame))
         (frame-p frame))
  :hints (("goal" :in-theory (enable frame-with-root))))

(defund
  collapse (frame)
  (declare (xargs :guard (and (frame-p frame)
                              (consp (assoc-equal 0 frame)))
                  :guard-debug t
                  :measure (len (frame->frame frame))))
  (b*
      (((when (atom (frame->frame frame)))
        (mv (frame->root frame) t))
       (head-index (1st-complete (frame->frame frame)))
       ((when (zp head-index))
        (mv (frame->root frame) nil))
       (head-frame-val
        (cdr (assoc-equal head-index (frame->frame frame))))
       (src (1st-complete-src (frame->frame frame))))
    (if
        (zp src)
        (b*
            ((root-after-context-apply
              (context-apply (frame->root frame)
                             (frame-val->dir head-frame-val)
                             head-index
                             (frame-val->path head-frame-val)))
             ((when
                  (not
                   (context-apply-ok (frame->root frame)
                                     (frame-val->dir head-frame-val)
                                     head-index
                                     (frame-val->path head-frame-val))))
              (mv (frame->root frame) nil))
             (frame
              (frame-with-root
               root-after-context-apply
               (remove-assoc-equal head-index (frame->frame frame)))))
          (collapse frame))
      (b*
          ((path (frame-val->path head-frame-val))
           ((when
                (or
                 (equal src head-index)
                 (atom
                  (assoc-equal src
                               (remove-assoc-equal
                                head-index (frame->frame frame))))))
            (mv (frame->root frame) nil))
           (src-path
            (frame-val->path
             (cdr
              (assoc-equal src
                           (remove-assoc-equal
                            head-index (frame->frame frame))))))
           (src-dir
            (frame-val->dir
             (cdr
              (assoc-equal src
                           (remove-assoc-equal
                            head-index (frame->frame frame))))))
           ((unless (prefixp src-path path))
            (mv (frame->root frame) nil))
           (src-dir-after-context-apply
            (context-apply src-dir (frame-val->dir head-frame-val)
                           head-index
                           (nthcdr (len src-path) path)))
           ((when (not (context-apply-ok
                        src-dir (frame-val->dir head-frame-val)
                        head-index
                        (nthcdr (len src-path) path))))
            (mv (frame->root frame) nil))
           (frame
            (frame-with-root
             (frame->root frame)
             (put-assoc-equal
              src
              (frame-val
               (frame-val->path
                (cdr (assoc-equal src (frame->frame frame))))
               ;; This fixing function wasn't always there; we added it after we
               ;; realised we needed to maintain frame-p as an invariant. In one
               ;; sense, though, it doesn't really impose an additional
               ;; requirement, because abs-separate is a hypothesis in many of
               ;; our theorems and that does require all the values in the frame
               ;; to satisfy abs-no-dups-p.
               (abs-fs-fix src-dir-after-context-apply)
               (frame-val->src
                (cdr (assoc-equal src (frame->frame frame)))))
              (remove-assoc-equal
               head-index (frame->frame frame))))))
        (collapse frame)))))

(assert-event
 (b*
     (((mv root result)
       (collapse
        (frame-with-root
         (list
          (cons
           "INITRD  IMG"
           (abs-file (dir-ent-fix nil) ""))
          (cons
           "RUN        "
           (abs-file
            (dir-ent-fix nil)
            (list
             (cons
              "RSYSLOGDPID"
              (abs-file (dir-ent-fix nil) "")))))
          (cons
           "USR        "
           (abs-file (dir-ent-fix nil)
                     (list
                      (cons
                       "LOCAL      "
                       (abs-file (dir-ent-fix nil) ()))
                      (cons
                       "LIB        "
                       (abs-file (dir-ent-fix nil) ()))
                      1))))
         (list
          (cons
           1
           (frame-val
            (list "USR        ")
            (list
             (cons
              "SHARE      "
              (abs-file (dir-ent-fix nil) ()))
             (cons
              "BIN        "
              (abs-file (dir-ent-fix nil)
                        (list
                         (cons
                          "CAT        "
                          (abs-file (dir-ent-fix nil) ""))
                         2
                         (cons
                          "TAC        "
                          (abs-file (dir-ent-fix nil) ""))))))
            0))
          (cons
           2
           (frame-val
            (list "USR        " "BIN        ")
            (list
             (cons
              "COL        "
              (abs-file (dir-ent-fix nil) "")))
            1)))))))
   (and
    (equal
     root
     (list
      (cons
       "INITRD  IMG"
       (abs-file (dir-ent-fix nil) ""))
      (cons
       "RUN        "
       (abs-file (dir-ent-fix nil)
                 (list
                  (cons
                   "RSYSLOGDPID"
                   (abs-file (dir-ent-fix nil) "")))))
      (cons
       "USR        "
       (abs-file (dir-ent-fix nil)
                 (list
                  (cons
                   "LOCAL      "
                   (abs-file (dir-ent-fix nil) nil))
                  (cons
                   "LIB        "
                   (abs-file (dir-ent-fix nil) nil))
                  (cons
                   "SHARE      "
                   (abs-file (dir-ent-fix nil) nil))
                  (cons
                   "BIN        "
                   (abs-file (dir-ent-fix nil)
                             (list
                              (cons
                               "CAT        "
                               (abs-file (dir-ent-fix nil) ""))
                              (cons
                               "TAC        "
                               (abs-file (dir-ent-fix nil) ""))
                              (cons
                               "COL        "
                               (abs-file (dir-ent-fix nil) ""))))))))))
    (equal result t))))

;; This example used to behave differently earlier, before abs-no-dups-p was
;; changed to reflect that it's pointless to worry about the same variable
;; occurring twice in a directory when we really need it not to occur twice
;; anywhere.
(assert-event
 (equal
  (abs-no-dups-p
   (list
    (cons
     "INITRD  IMG"
     (abs-file (dir-ent-fix nil) ""))
    (cons
     "RUN        "
     (abs-file
      (dir-ent-fix nil)
      (list
       (cons
        "RSYSLOGDPID"
        (abs-file (dir-ent-fix nil) "")))))
    (cons
     "USR        "
     (abs-file (dir-ent-fix nil)
               (list
                1
                (cons
                 "LIB        "
                 (abs-file (dir-ent-fix nil) ()))
                1)))))
  t))

(assert-event
 (equal
  (abs-no-dups-p
   (list
    (cons
     "INITRD  IMG"
     (abs-file (dir-ent-fix nil) ""))
    (cons
     "RUN        "
     (abs-file
      (dir-ent-fix nil)
      (list
       (cons
        "RSYSLOGDPID"
        (abs-file (dir-ent-fix nil) "")))))
    (cons
     "USR        "
     (abs-file (dir-ent-fix nil)
               (list
                (cons
                 "LIB        "
                 (abs-file (dir-ent-fix nil) ()))
                1
                (cons
                 "LIB        "
                 (abs-file (dir-ent-fix nil) ())))))))
  nil))

(assert-event
 (equal
  (abs-no-dups-p
   (list
    (cons
     "INITRD  IMG"
     (abs-file (dir-ent-fix nil) ""))
    (cons
     "RUN        "
     (abs-file
      (dir-ent-fix nil)
      (list
       (cons
        "RSYSLOGDPID"
        (abs-file (dir-ent-fix nil) "")))))
    (cons
     "USR        "
     (abs-file (dir-ent-fix nil)
               (list
                (cons
                 "LIB        "
                 (abs-file (dir-ent-fix nil) ()))
                1)))))
  t))

(defthm abs-file-alist-p-of-collapse
  (abs-file-alist-p (mv-nth 0 (collapse frame)))
  :hints (("goal" :in-theory (enable collapse))))

(defthm abs-fs-p-of-collapse
  (abs-fs-p (mv-nth 0 (collapse frame)))
  :hints (("goal" :in-theory (enable collapse))))

(defthm booleanp-of-collapse
  (booleanp (mv-nth 1 (collapse frame)))
  :hints (("goal" :in-theory (enable collapse)))
  :rule-classes :type-prescription)

(defund abs-top-names (x)
  (declare (xargs :guard t))
  (cond ((atom x) nil)
        ((atom (car x)) (abs-top-names (cdr x)))
        ((equal (caar x) nil) (abs-top-names (cdr x)))
        (t (cons (car (car x))
                 (abs-top-names (cdr x))))))

(defthm abs-top-names-definition
  (equal (abs-top-names x)
         (remove nil (strip-cars x)))
  :rule-classes :definition
  :hints (("goal" :in-theory (enable abs-top-names))))

(defthm
  absfat-subsetp-guard-lemma-1
  (implies (and (abs-file-alist-p abs-file-alist)
                (consp (assoc-equal name abs-file-alist)))
           (abs-file-p (cdr (assoc-equal name abs-file-alist))))
  :hints
  (("goal" :expand ((abs-file-alist-p abs-file-alist)
                    (abs-file-p (cdr (car abs-file-alist)))))))

(defund
  absfat-subsetp
  (abs-file-alist1 abs-file-alist2)
  (declare
   (xargs
    :guard (and (abs-file-alist-p abs-file-alist1)
                (abs-file-alist-p abs-file-alist2))
    :guard-hints
    (("goal''"
      :expand ((abs-file-alist-p abs-file-alist1)
               (abs-file-p (cdr (car abs-file-alist1))))))
    :guard-debug t))
  (b* (((when (atom abs-file-alist1)) t)
       ((unless (and (consp (car abs-file-alist1))
                     (stringp (car (car abs-file-alist1)))))
        (and (member-equal (car abs-file-alist1)
                           abs-file-alist2)
             (absfat-subsetp (cdr abs-file-alist1)
                             abs-file-alist2)))
       (name (caar abs-file-alist1))
       (file1 (cdar abs-file-alist1))
       ((unless (consp (abs-assoc name abs-file-alist2)))
        nil)
       (file2 (cdr (abs-assoc name abs-file-alist2))))
    (if (not (abs-directory-file-p file1))
        (and (not (abs-directory-file-p file2))
             (absfat-subsetp (cdr abs-file-alist1)
                             abs-file-alist2)
             (equal (abs-file->contents file1)
                    (abs-file->contents file2)))
      (and (abs-directory-file-p file2)
           (absfat-subsetp (cdr abs-file-alist1)
                           abs-file-alist2)
           (absfat-subsetp (abs-file->contents file1)
                           (abs-file->contents file2))))))

(defthm
  absfat-subsetp-correctness-1
  (implies
   (and (m1-file-alist-p abs-file-alist1)
        (m1-file-alist-p abs-file-alist2))
   (equal (absfat-subsetp abs-file-alist1 abs-file-alist2)
          (hifat-subsetp abs-file-alist1 abs-file-alist2)))
  :hints
  (("goal" :in-theory (enable absfat-subsetp hifat-subsetp))))

(defthm absfat-subsetp-reflexivity-lemma-1
  (implies (and (abs-file-alist-p x)
                (consp (car x))
                (consp (assoc-equal (car (car x)) y)))
           (consp (assoc-equal (car (car x))
                               (append (cdr x) y))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable abs-file-p abs-file-alist-p)
           :cases ((null (car (car x)))))))

(defthm absfat-subsetp-reflexivity-lemma-3
  (implies (and (abs-file-alist-p x)
                (consp (assoc-equal name x))
                (consp (assoc-equal name y)))
           (not (abs-no-dups-p (append x y))))
  :hints (("goal" :in-theory (enable abs-no-dups-p))))

(defthm absfat-subsetp-reflexivity-lemma-4
  (implies (and (abs-file-alist-p x)
                (absfat-subsetp z y)
                (abs-no-dups-p (append x y)))
           (absfat-subsetp z (append x y)))
  :hints (("goal" :in-theory (enable absfat-subsetp))))

(defthm
  absfat-subsetp-reflexivity-lemma-5
  (implies (and (absfat-subsetp (cdr x)
                                (append (cdr x) y))
                (abs-file-alist-p x)
                (abs-no-dups-p (append (cdr x) y))
                (or
                 (not (abs-directory-file-p (cdr (car x))))
                 (abs-no-dups-p (abs-file->contents (cdr (car x)))))
                (or (and (stringp (car (car x)))
                         (not (consp (assoc-equal (car (car x)) (cdr x))))
                         (not (consp (assoc-equal (car (car x)) y))))
                    (and (consp x)
                         (or
                          (not (consp (car x)))
                          (not (consp (assoc-equal (car (car x))
                                                   (append (cdr x) y))))))))
           (absfat-subsetp (cdr x)
                           (cons (car x) (append (cdr x) y))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (abs-no-dups-p abs-file-alist-p)
                    ((:rewrite absfat-subsetp-reflexivity-lemma-4)))
    :use (:instance (:rewrite absfat-subsetp-reflexivity-lemma-4)
                    (y (append (cdr x) y))
                    (x (list (car x)))
                    (z (cdr x)))
    :expand (abs-file-alist-p (list (car x))))))

(encapsulate
  ()

  (local
   (defun induction-scheme (x y)
     (cond
      ((and (not (atom x))
            (and (consp (car x))
                 (stringp (car (car x))))
            (consp (abs-assoc (car (car x)) (append x y)))
            (abs-directory-file-p (cdr (car x)))
            (abs-directory-file-p (cdr (abs-assoc (car (car x)) (append x y))))
            (absfat-subsetp (cdr x) (append x y)))
       (append
        (induction-scheme (cdr x) y)
        (induction-scheme (abs-file->contents (cdr (car x))) nil)))
      ((and (not (atom x))
            (if
                (and (consp (car x))
                     (stringp (car (car x))))
                (and(consp (abs-assoc (car (car x)) (append x y)))
                    (or
                     (and
                      (abs-directory-file-p (cdr (car x)))
                      (abs-directory-file-p (cdr (abs-assoc (car (car x)) (append x y))))
                      (not (absfat-subsetp (cdr x) (append x y))))
                     (and
                      (not (abs-directory-file-p (cdr (car x))))
                      (not (abs-directory-file-p (cdr (abs-assoc (car (car x))
                                                                 (append x y))))))))
              (member-equal (car x) (append x y))))
       (induction-scheme (cdr x) y))
      (t (append x y)))))

  (defthmd
    absfat-subsetp-reflexivity-lemma-7
    (implies (and (abs-file-alist-p x)
                  (abs-no-dups-p (append x y)))
             (absfat-subsetp x (append x y)))
    :hints
    (("goal" :in-theory (enable absfat-subsetp abs-no-dups-p)
      :induct (induction-scheme x y)))))

(defthm
  absfat-subsetp-reflexivity
  (implies (and (abs-file-alist-p x)
                (abs-no-dups-p x))
           (absfat-subsetp x x))
  :hints (("goal"
           :use (:instance absfat-subsetp-reflexivity-lemma-7
                           (y nil)))))

(defthm absfat-subsetp-transitivity-lemma-1
  (implies (and (abs-file-alist-p y)
                (consp (car y)))
           (stringp (car (car y))))
  :hints (("goal" :expand (abs-file-alist-p y))))

(defthm absfat-subsetp-transitivity-lemma-2
  (implies (and (abs-file-alist-p y)
                (not (consp (assoc-equal (car (car x)) z)))
                (consp (assoc-equal (car (car x)) y)))
           (not (absfat-subsetp y z)))
  :hints (("goal" :in-theory (enable absfat-subsetp)
           :induct (absfat-subsetp y z))))

(defthm absfat-subsetp-transitivity-lemma-3
  (implies (and (abs-file-alist-p y)
                (not (abs-directory-file-p (cdr (assoc-equal name z))))
                (abs-directory-file-p (cdr (assoc-equal name y))))
           (not (absfat-subsetp y z)))
  :hints (("goal" :in-theory (enable absfat-subsetp))))

(defthm
  absfat-subsetp-transitivity-lemma-4
  (implies (and (abs-file-alist-p y)
                (abs-directory-file-p (cdr (assoc-equal name y)))
                (absfat-subsetp y z))
           (absfat-subsetp (abs-file->contents (cdr (assoc-equal name y)))
                           (abs-file->contents (cdr (assoc-equal name z)))))
  :hints (("goal" :in-theory (enable absfat-subsetp))))

(defthm
  absfat-subsetp-transitivity-lemma-5
  (implies (and (abs-directory-file-p (cdr (assoc-equal name z)))
                (abs-file-alist-p z)
                (consp (assoc-equal name y))
                (not (abs-directory-file-p (cdr (assoc-equal name y)))))
           (not (absfat-subsetp y z)))
  :hints (("goal" :in-theory (enable absfat-subsetp))))

(defthm absfat-subsetp-transitivity-lemma-6
  (implies (and (not (consp (car x)))
                (not (member-equal (car x) z))
                (member-equal (car x) y))
           (not (absfat-subsetp y z)))
  :hints (("goal" :in-theory (enable absfat-subsetp))))

(defthm
  absfat-subsetp-transitivity-lemma-7
  (implies (and (abs-file-alist-p fs)
                (consp (assoc-equal name fs))
                (not (abs-directory-file-p (cdr (assoc-equal name fs)))))
           (m1-regular-file-p (cdr (assoc-equal name fs))))
  :hints (("goal" :in-theory (e/d
                              (abs-file-alist-p abs-directory-file-p
                                                m1-regular-file-p m1-file-p abs-file-p
                                                abs-file->contents m1-file->contents)
                              (abs-file-alist-p-when-m1-file-alist-p)))))

(defthm
  absfat-subsetp-transitivity-lemma-8
  (implies
   (and (equal (m1-file->contents (cdr (assoc-equal (car (car y)) (cdr y))))
               (abs-file->contents (cdr (car y))))
        (consp (assoc-equal (car (car y)) z))
        (not (abs-directory-file-p (cdr (assoc-equal (car (car y)) z))))
        (abs-file-alist-p y)
        (abs-file-alist-p z)
        (equal (abs-file->contents (cdr (car y)))
               (m1-file->contents (cdr (assoc-equal (car (car y)) z)))))
   (m1-file-p (cdr (car y))))
  :hints (("goal" :in-theory (enable abs-file-alist-p
                                     abs-file-p m1-file-p abs-file->contents
                                     m1-file-contents-p abs-directory-file-p)
           :do-not-induct t)))

(encapsulate
  ()

  (local
   (defthm
     absfat-subsetp-transitivity-lemma-9
     (implies
      (and (not (consp (assoc-equal (car (car y)) (cdr y))))
           (consp (assoc-equal (car (car y)) z))
           (abs-file-alist-p y)
           (abs-file-alist-p z)
           (equal (abs-file->contents (cdr (car y)))
                  (m1-file->contents (cdr (assoc-equal (car (car y)) z)))))
      (m1-file-p (cdr (car y))))
     :hints (("goal" :in-theory (enable abs-file->contents
                                        m1-file-p abs-file-alist-p)
              :do-not-induct t))))

  (defthmd absfat-subsetp-transitivity-lemma-10
    (implies (and (abs-file-alist-p y)
                  (abs-file-alist-p z)
                  (consp (assoc-equal name y))
                  (not (abs-directory-file-p (cdr (assoc-equal name y))))
                  (absfat-subsetp y z))
             (equal (m1-file->contents (cdr (assoc-equal name y)))
                    (m1-file->contents (cdr (assoc-equal name z)))))
    :hints (("goal" :in-theory (enable absfat-subsetp)))))

(defthm
  absfat-subsetp-transitivity
  (implies (and (absfat-subsetp x y)
                (absfat-subsetp y z)
                (abs-file-alist-p x)
                (abs-file-alist-p y)
                (abs-file-alist-p z))
           (absfat-subsetp x z))
  :hints
  (("goal" :in-theory (enable absfat-subsetp)
    :induct t)
   ("subgoal *1/2''" :use (:instance absfat-subsetp-transitivity-lemma-10
                                     (name (car (car x)))))))

(defthm
  absfat-subsetp-of-put-assoc-1
  (implies
   (and (abs-file-alist-p abs-file-alist1)
        (abs-no-dups-p abs-file-alist1)
        (absfat-subsetp (remove-assoc name abs-file-alist1)
                        abs-file-alist2)
        (abs-directory-file-p (cdr (assoc-equal name abs-file-alist2)))
        (fat32-filename-p name)
        (abs-directory-file-p val)
        (absfat-subsetp
         (abs-file->contents val)
         (abs-file->contents (cdr (assoc-equal name abs-file-alist2)))))
   (absfat-subsetp (put-assoc-equal name val abs-file-alist1)
                   abs-file-alist2))
  :hints (("goal" :in-theory (e/d (absfat-subsetp abs-no-dups-p) nil)
           :induct (put-assoc-equal name val abs-file-alist1))
          ("subgoal *1/2" :expand (abs-no-dups-p abs-file-alist1))))

(defthm absfat-subsetp-of-put-assoc-2
  (implies (and (absfat-subsetp abs-file-alist1 abs-file-alist2)
                (fat32-filename-p name)
                (atom (assoc-equal name abs-file-alist1)))
           (absfat-subsetp abs-file-alist1
                           (put-assoc-equal name val abs-file-alist2)))
  :hints (("goal" :in-theory (e/d (absfat-subsetp) nil))))

(defthm absfat-subsetp-of-remove-assoc-1
  (implies (absfat-subsetp abs-file-alist1 abs-file-alist2)
           (absfat-subsetp (remove-assoc-equal name abs-file-alist1)
                           abs-file-alist2))
  :hints (("goal" :in-theory (enable absfat-subsetp))))

(defthm absfat-subsetp-of-append-1
  (equal (absfat-subsetp (append x y) z)
         (and (absfat-subsetp x z)
              (absfat-subsetp y z)))
  :hints (("goal" :in-theory (enable absfat-subsetp))))

(defthm absfat-subsetp-of-append-2
  (implies (and (abs-file-alist-p y)
                (or (absfat-subsetp x y)
                    (and (abs-no-dups-p (append y z))
                         (absfat-subsetp x z))))
           (absfat-subsetp x (append y z)))
  :hints (("goal" :in-theory (enable absfat-subsetp))))

(defthm absfat-subsetp-of-remove-1
  (implies (absfat-subsetp abs-file-alist1 abs-file-alist2)
           (absfat-subsetp (remove-equal x abs-file-alist1)
                           abs-file-alist2))
  :hints (("goal" :in-theory (enable absfat-subsetp))))

(defthm absfat-subsetp-of-remove-2
  (implies (and (natp x)
                (not (member-equal x abs-file-alist1))
                (absfat-subsetp abs-file-alist1 abs-file-alist2))
           (absfat-subsetp abs-file-alist1
                           (remove-equal x abs-file-alist2)))
  :hints (("goal" :in-theory (enable absfat-subsetp))))

(defund
  absfat-equiv
  (abs-file-alist1 abs-file-alist2)
  (declare
   (xargs :guard (and (abs-file-alist-p abs-file-alist1)
                      (abs-file-alist-p abs-file-alist2))))
  (b* ((abs-file-alist1 (abs-fs-fix abs-file-alist1))
       (abs-file-alist2 (abs-fs-fix abs-file-alist2)))
    (and (absfat-subsetp abs-file-alist1 abs-file-alist2)
         (absfat-subsetp abs-file-alist2 abs-file-alist1))))

(defequiv
  absfat-equiv
  :hints (("Goal" :in-theory (enable absfat-equiv))))

(defthm
  absfat-equiv-of-abs-fs-fix
  (absfat-equiv (abs-fs-fix fs) fs)
  :hints (("Goal" :in-theory (enable absfat-equiv))))

(defund
  names-at (fs relpath)
  (declare (xargs :guard (and (abs-fs-p fs)
                              (fat32-filename-list-p relpath))
                  :measure (len relpath)))
  (b*
      ((fs (mbe :logic (abs-fs-fix fs) :exec fs))
       ((when (atom relpath))
        (abs-top-names fs))
       (head (mbe :exec (car relpath)
                  :logic (fat32-filename-fix (car relpath))))
       ((unless
            (and (consp (abs-assoc head fs))
                 (abs-directory-file-p (cdr (abs-assoc head fs)))))
        nil))
    (names-at
     (abs-file->contents (cdr (abs-assoc head fs)))
     (cdr relpath))))

(defthm fat32-filename-list-p-of-names-at-lemma-1
  (implies (abs-file-alist-p fs)
           (fat32-filename-list-p (remove-equal nil (strip-cars fs))))
  :hints (("goal" :in-theory (enable abs-file-alist-p))))

(defthm fat32-filename-list-p-of-names-at
  (implies (abs-file-alist-p fs)
           (fat32-filename-list-p (names-at fs relpath)))
  :hints (("goal" :in-theory (enable names-at))))

(defthm names-at-of-fat32-filename-list-fix
  (equal (names-at fs (fat32-filename-list-fix relpath))
         (names-at fs relpath))
  :hints (("goal" :in-theory (enable names-at))))

(defcong
  fat32-filename-list-equiv
  equal (names-at fs relpath)
  2
  :hints
  (("goal"
    :in-theory
    (e/d (fat32-filename-list-equiv)
         (names-at-of-fat32-filename-list-fix))
    :use
    (names-at-of-fat32-filename-list-fix
     (:instance names-at-of-fat32-filename-list-fix
                (relpath relpath-equiv))))))

(defthm names-at-of-abs-fs-fix
  (equal (names-at (abs-fs-fix fs)
                   relpath)
         (names-at fs relpath))
  :hints (("goal" :in-theory (enable names-at))))

(defthm absfat-equiv-implies-set-equiv-names-at-1-lemma-1
  (implies (and (abs-file-alist-p abs-file-alist1)
                (absfat-subsetp abs-file-alist1 abs-file-alist2)
                (consp (assoc-equal x abs-file-alist1)))
           (consp (assoc-equal x abs-file-alist2)))
  :hints (("goal" :in-theory (enable absfat-subsetp))))

(defthm
  absfat-equiv-implies-set-equiv-names-at-1-lemma-2
  (implies (and (abs-file-alist-p abs-file-alist1)
                (absfat-subsetp abs-file-alist1 abs-file-alist2)
                (abs-directory-file-p (cdr (assoc-equal x abs-file-alist1))))
           (abs-directory-file-p (cdr (assoc-equal x abs-file-alist2))))
  :hints (("goal" :in-theory (enable absfat-subsetp))))

(defthmd
  absfat-equiv-implies-set-equiv-names-at-1-lemma-3
  (implies
   (and (abs-fs-p abs-file-alist1)
        (abs-fs-p abs-file-alist2)
        (absfat-equiv abs-file-alist1 abs-file-alist2))
   (equal (abs-directory-file-p (cdr (assoc-equal x abs-file-alist2)))
          (abs-directory-file-p (cdr (assoc-equal x abs-file-alist1)))))
  :hints
  (("goal" :in-theory (e/d (absfat-equiv)
                           (absfat-equiv-implies-set-equiv-names-at-1-lemma-2))
    :use (absfat-equiv-implies-set-equiv-names-at-1-lemma-2
          (:instance absfat-equiv-implies-set-equiv-names-at-1-lemma-2
                     (abs-file-alist2 abs-file-alist1)
                     (abs-file-alist1 abs-file-alist2)))
    :do-not-induct t)))

(defthm
  absfat-equiv-implies-set-equiv-names-at-1-lemma-4
  (implies
   (and
    (abs-fs-p abs-file-alist1)
    (abs-fs-p abs-file-alist2)
    (absfat-equiv abs-file-alist1 abs-file-alist2)
    (abs-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                            abs-file-alist1))))
   (abs-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                           abs-file-alist2))))
  :hints
  (("goal"
    :use (:instance (:rewrite absfat-equiv-implies-set-equiv-names-at-1-lemma-3)
                    (x (fat32-filename-fix (car x-path)))))))

;; The second rewrite rule of this defthm is needed...
(defthm
  absfat-equiv-implies-set-equiv-names-at-1-lemma-5
  (implies (and (absfat-subsetp abs-file-alist1 abs-file-alist2)
                (abs-file-alist-p abs-file-alist1))
           (subsetp-equal (remove-equal nil (strip-cars abs-file-alist1))
                          (remove-equal nil (strip-cars abs-file-alist2))))
  :hints
  (("goal"
    :in-theory
    (e/d (absfat-subsetp)
         (intersectp-is-commutative
          (:rewrite abs-file->contents-when-m1-file-p)
          (:rewrite member-equal-of-strip-cars-when-m1-file-alist-p)
          (:rewrite absfat-subsetp-correctness-1)
          (:rewrite absfat-subsetp-transitivity)))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (absfat-subsetp abs-file-alist1 abs-file-alist2)
          (abs-file-alist-p abs-file-alist1)
          (not (intersectp-equal (remove-equal nil (strip-cars abs-file-alist2))
                                 y)))
     (not (intersectp-equal (remove-equal nil (strip-cars abs-file-alist1))
                            y)))
    :hints
    (("goal"
      :use (:instance (:rewrite intersect-with-subset)
                      (z y)
                      (y (remove-equal nil (strip-cars abs-file-alist2)))
                      (x (remove-equal nil (strip-cars abs-file-alist1)))))))))

(defthm
  absfat-equiv-implies-set-equiv-names-at-1-lemma-6
  (implies (and (absfat-subsetp abs-file-alist1 abs-file-alist2)
                (abs-fs-p abs-file-alist1)
                (abs-fs-p abs-file-alist2))
           (subsetp-equal (names-at abs-file-alist1 relpath)
                          (names-at abs-file-alist2 relpath)))
  :hints
  (("goal"
    :in-theory (e/d (absfat-subsetp names-at)
                    ((:rewrite absfat-equiv-implies-set-equiv-names-at-1-lemma-1)))
    :induct (mv (names-at abs-file-alist1 relpath)
                (names-at abs-file-alist2 relpath)))
   ("subgoal *1/3.2"
    :use (:instance (:rewrite absfat-equiv-implies-set-equiv-names-at-1-lemma-1)
                    (abs-file-alist2 abs-file-alist2)
                    (x (fat32-filename-fix (car relpath)))
                    (abs-file-alist1 abs-file-alist1)))))

(defcong absfat-equiv set-equiv (names-at fs relpath) 1
  :hints
  (("goal"
    :in-theory (e/d (absfat-equiv set-equiv)
                    (absfat-equiv-implies-set-equiv-names-at-1-lemma-6))
    :use
    ((:instance absfat-equiv-implies-set-equiv-names-at-1-lemma-6
                (abs-file-alist1 (abs-fs-fix fs))
                (abs-file-alist2 (abs-fs-fix fs-equiv)))
     (:instance
      absfat-equiv-implies-set-equiv-names-at-1-lemma-6
      (abs-file-alist1 (abs-fs-fix fs-equiv))
      (abs-file-alist2 (abs-fs-fix fs)))))))

(defthm
  abs-no-dups-p-of-context-apply-lemma-1
  (implies
   (and (abs-file-alist-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist2))
   (abs-directory-file-p (abs-file dir-ent
                                   (context-apply abs-file-alist1
                                                  abs-file-alist2 x x-path))))
  :hints
  (("goal"
    :expand (abs-directory-file-p
             (abs-file dir-ent
                       (context-apply abs-file-alist1
                                      abs-file-alist2 x x-path))))))

(defthm
  abs-no-dups-p-of-context-apply-lemma-2
  (implies
   (and (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
        (abs-no-dups-p abs-file-alist2)
        (abs-file-alist-p abs-file-alist1)
        (abs-no-dups-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist2))
   (abs-no-dups-p
    (put-assoc-equal
     name
     (abs-file (abs-file->dir-ent (cdr (assoc-equal name abs-file-alist1)))
               abs-file-alist2)
     abs-file-alist1)))
  :hints
  (("goal"
    :in-theory (enable abs-no-dups-p)
    :induct
    (mv
     (abs-no-dups-p abs-file-alist1)
     (put-assoc-equal
      name
      (abs-file (abs-file->dir-ent (cdr (assoc-equal name abs-file-alist1)))
                abs-file-alist2)
      abs-file-alist1))
    :expand (abs-file-alist-p abs-file-alist1))))

(defthm
  abs-no-dups-p-of-context-apply-lemma-3
  (implies
   (and (abs-directory-file-p (cdr (assoc-equal (car x-path)
                                                abs-file-alist1)))
        (abs-file-alist-p abs-file-alist2))
   (equal
    (abs-file-contents-fix
     (context-apply
      (abs-file->contents$inline (cdr (assoc-equal (car x-path)
                                                   abs-file-alist1)))
      abs-file-alist2 x (cdr x-path)))
    (context-apply
     (abs-file->contents$inline (cdr (assoc-equal (car x-path)
                                                  abs-file-alist1)))
     abs-file-alist2 x (cdr x-path)))))

;; This doesn't work all the time as a type prescription rule, because
;; rewriting is sometimes needed to establish the hypotheses.
(defthm
  abs-no-dups-p-of-context-apply-lemma-4
  (implies (and (abs-no-dups-p abs-file-alist)
                (fat32-filename-p name))
           (atom (assoc-equal name
                              (remove1-assoc-equal name abs-file-alist))))
  :hints (("goal" :in-theory (enable abs-no-dups-p))))

(defthm
  abs-no-dups-p-of-context-apply
  (implies
   (context-apply-ok abs-file-alist1
                     abs-file-alist2 x x-path)
   (equal
    (abs-no-dups-p (context-apply abs-file-alist1
                                  abs-file-alist2 x x-path))
    (not (intersectp-equal (names-at abs-file-alist1
                                     x-path)
                           (names-at abs-file-alist2 nil)))))
  :hints
  (("goal" :in-theory (e/d (context-apply context-apply-ok
                                          names-at abs-no-dups-p)
                           (nfix))))
  :rule-classes
  ((:rewrite
    :corollary
    (equal
     (abs-no-dups-p (context-apply abs-file-alist1
                                   abs-file-alist2 x x-path))
     (not
      (and
       (context-apply-ok abs-file-alist1
                         abs-file-alist2 x x-path)
       (intersectp-equal (names-at abs-file-alist1
                                   x-path)
                         (names-at abs-file-alist2 nil))))))))

(defthm
  abs-fs-p-of-context-apply
  (equal
   (abs-fs-p (context-apply abs-file-alist1
                            abs-file-alist2 x x-path))
   (not
    (and (context-apply-ok abs-file-alist1
                           abs-file-alist2 x x-path)
         (intersectp-equal (names-at abs-file-alist1
                                     x-path)
                           (names-at abs-file-alist2 nil)))))
  :hints (("goal" :in-theory (enable abs-fs-p))))

;; Shorter name for distinguish names.
(defund
  dist-names (dir relpath frame)
  (declare (xargs :guard (and (abs-fs-p dir)
                              (fat32-filename-list-p relpath)
                              (frame-p frame))
                  :measure (len frame)))
  (b*
      (((when (atom frame)) t)
       (relpath (mbe :exec relpath :logic (fat32-filename-list-fix relpath)))
       (head-frame-val (cdar frame))
       ((when (prefixp relpath
                       (frame-val->path head-frame-val)))
        (and
         (not
          (intersectp-equal
           (names-at
            dir
            (nthcdr (len relpath)
                    (frame-val->path head-frame-val)))
           (names-at (frame-val->dir head-frame-val) nil)))
         (dist-names dir relpath (cdr frame))))
       ((when (prefixp (frame-val->path head-frame-val)
                       relpath))
        (and
         (not (intersectp-equal
               (names-at
                (frame-val->dir head-frame-val)
                (nthcdr (len (frame-val->path head-frame-val))
                        relpath))
               (names-at dir nil)))
         (dist-names dir relpath (cdr frame)))))
    (dist-names dir relpath (cdr frame))))

;; Move later.
(defthm fat32-filename-list-p-when-prefixp
  (implies (and (prefixp x y)
                (fat32-filename-list-p y))
           (fat32-filename-list-p (true-list-fix x)))
  :hints (("goal" :in-theory (enable prefixp fat32-filename-list-p))))

(defthm dist-names-of-fat32-filename-list-fix
  (equal (dist-names dir (fat32-filename-list-fix relpath)
                     frame)
         (dist-names dir relpath frame))
  :hints (("goal" :in-theory (enable dist-names))))

(defthm dist-names-of-abs-fs-fix
  (equal (dist-names (abs-fs-fix dir) relpath
                     frame)
         (dist-names dir relpath frame))
  :hints (("goal" :in-theory (enable dist-names))))

(defcong
  fat32-filename-list-equiv equal
  (dist-names dir relpath frame)
  2
  :hints
  (("goal"
    :in-theory
    (disable dist-names-of-fat32-filename-list-fix)
    :use
    (dist-names-of-fat32-filename-list-fix
     (:instance dist-names-of-fat32-filename-list-fix
                (relpath relpath-equiv))))))

(defthm dist-names-of-remove-assoc-1
  (implies (dist-names dir relpath frame)
           (dist-names dir
                       relpath (remove-assoc-equal x frame)))
  :hints (("goal" :in-theory (enable dist-names))))

(defthm
  dist-names-of-remove-assoc-2
  (implies (dist-names dir
                       relpath (remove-assoc-equal x frame))
           (dist-names dir relpath
                       (remove-assoc-equal x (remove-assoc-equal y frame))))
  :hints (("goal" :in-theory (disable dist-names-of-remove-assoc-1)
           :use (:instance dist-names-of-remove-assoc-1
                           (frame (remove-assoc-equal x frame))
                           (x y)))))

(defthm
  dist-names-of-put-assoc-equal
  (implies
   (and (frame-p frame)
        (no-duplicatesp-equal (strip-cars frame)))
   (equal
    (dist-names dir
                relpath (put-assoc-equal src val frame))
    (and
     (dist-names dir
                 relpath (remove-assoc-equal src frame))
     (cond
      ((prefixp (fat32-filename-list-fix relpath)
                (frame-val->path val))
       (not
        (intersectp-equal (names-at (frame-val->dir val) nil)
                          (names-at dir
                                    (nthcdr (len relpath)
                                            (frame-val->path val))))))
      ((prefixp (frame-val->path val)
                (fat32-filename-list-fix relpath))
       (not (intersectp-equal
             (names-at dir nil)
             (names-at (frame-val->dir val)
                       (nthcdr (len (frame-val->path val))
                               relpath)))))
      (t t)))))
  :hints (("goal" :in-theory (enable dist-names))))

(defcong absfat-equiv
  equal (dist-names dir relpath frame)
  1
  :hints (("goal" :in-theory (enable dist-names))))

(defthm
  names-at-of-context-apply-lemma-1
  (implies (and (consp (assoc-equal (fat32-filename-fix (car relpath))
                                    root))
                (consp (assoc-equal (fat32-filename-fix (car relpath))
                                    abs-file-alist)))
           (intersectp-equal (remove-equal nil (strip-cars abs-file-alist))
                             (remove-equal nil (strip-cars root))))
  :instructions
  (:promote
   (:bash
    ("goal"
     :use (:instance (:rewrite intersectp-member)
                     (a (fat32-filename-fix (car relpath)))
                     (y (remove-equal nil (strip-cars root)))
                     (x (remove-equal nil (strip-cars abs-file-alist))))))))

;; The change we're making to this theorem is going to potentially make us
;; regret having done this...
(defthm
  names-at-of-context-apply
  (implies
   (abs-fs-p (context-apply root abs-file-alist x x-path))
   (equal
    (names-at (context-apply root abs-file-alist x x-path)
              relpath)
    (cond ((and (context-apply-ok root abs-file-alist x x-path)
                (equal (fat32-filename-list-fix x-path)
                       (fat32-filename-list-fix relpath)))
           (append (names-at root relpath)
                   (names-at abs-file-alist nil)))
          ((and (context-apply-ok root abs-file-alist x x-path)
                (prefixp (fat32-filename-list-fix x-path)
                         (fat32-filename-list-fix relpath))
                (not (member-equal (nth (len x-path)
                                        (fat32-filename-list-fix relpath))
                                   (names-at root x-path))))
           (names-at abs-file-alist
                     (nthcdr (len x-path) relpath)))
          (t (names-at root relpath)))))
  :hints
  (("goal" :induct (mv (context-apply root abs-file-alist x x-path)
                       (fat32-filename-list-prefixp x-path relpath))
    :in-theory (e/d (prefixp names-at context-apply-ok
                             context-apply names-at
                             fat32-filename-list-fix)
                    (nfix)))
   ("subgoal *1/4" :expand (:free (abs-file-alist)
                                  (names-at abs-file-alist relpath))
    :cases ((null (fat32-filename-fix (car relpath)))))))

(defund
  abs-separate (frame)
  (declare (xargs :guard (frame-p frame)))
  (or
   (atom frame)
   (and
    (abs-no-dups-p (frame-val->dir (cdar frame)))
    (no-duplicatesp-equal (abs-addrs (frame-val->dir (cdar frame))))
    (dist-names
     (frame-val->dir (cdar frame))
     (frame-val->path (cdar frame))
     (cdr frame))
    (abs-separate (cdr frame)))))

(defthm abs-separate-of-remove-assoc
  (implies (abs-separate frame)
           (abs-separate (remove-assoc-equal x frame)))
  :hints (("goal" :in-theory (enable abs-separate))))

(defthm
  abs-separate-of-put-assoc-2
  (implies (and (no-duplicatesp-equal (strip-cars frame))
                (frame-p frame)
                (no-duplicatesp-equal (abs-addrs (frame-val->dir val))))
           (equal (abs-separate (put-assoc-equal src val frame))
                  (and (abs-separate (remove-assoc-equal src frame))
                       (dist-names (frame-val->dir val)
                                   (frame-val->path val)
                                   (remove-assoc-equal src frame)))))
  :hints (("goal" :in-theory (enable abs-separate
                                     dist-names names-at))))

(defthm
  abs-separate-of-put-assoc-lemma-1
  (implies
   (and
    (prefixp (fat32-filename-list-fix relpath)
             (frame-val->path (cdr (car frame))))
    (not
     (intersectp-equal
      (names-at (frame-val->dir (cdr (car frame))) nil)
      (names-at dir
                (nthcdr (len relpath)
                        (frame-val->path (cdr (car frame)))))))
    (prefixp (frame-val->path (cdr (car frame)))
             (fat32-filename-list-fix relpath)))
   (not
    (intersectp-equal
     (names-at dir nil)
     (names-at (frame-val->dir (cdr (car frame)))
               (nthcdr (len (frame-val->path (cdr (car frame))))
                       relpath)))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (list-equiv names-at)
                           ((:rewrite prefixp-when-equal-lengths)))
           :use (:instance (:rewrite prefixp-when-equal-lengths)
                           (y (fat32-filename-list-fix relpath))
                           (x (frame-val->path (cdr (car frame))))))))

(defthmd
  abs-separate-of-put-assoc-lemma-2
  (implies
   (prefixp (frame-val->path (cdr (assoc-equal src frame)))
            relpath)
   (not (< (+ (len relpath)
              (- (len (frame-val->path (cdr (assoc-equal src frame))))))
           0)))
  :rule-classes :linear)

(defthm
  abs-separate-of-put-assoc-lemma-3
  (implies
   (and (consp (assoc-equal x frame))
        (dist-names dir relpath frame)
        (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                 (fat32-filename-list-fix relpath)))
   (not (intersectp-equal
         (names-at dir nil)
         (names-at
          (frame-val->dir (cdr (assoc-equal x frame)))
          (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                  relpath)))))
  :hints (("goal" :in-theory (enable dist-names names-at))))

(defthm
  abs-separate-of-put-assoc-lemma-7
  (implies
   (context-apply-ok abs-file-alist1
                     abs-file-alist2 x x-path)
   (equal (strip-cars (context-apply abs-file-alist1
                                     abs-file-alist2 x x-path))
          (if (consp x-path)
              (strip-cars (abs-fs-fix abs-file-alist1))
            (append (strip-cars (remove-equal (nfix x)
                                              (abs-fs-fix abs-file-alist1)))
                    (strip-cars (abs-fs-fix abs-file-alist2))))))
  :hints (("goal" :in-theory (e/d (context-apply context-apply-ok)
                                  (nfix))))
  :rule-classes
  ((:rewrite
    :corollary
    (equal
     (strip-cars (context-apply abs-file-alist1
                                abs-file-alist2 x x-path))
     (if (or (not (context-apply-ok abs-file-alist1
                                    abs-file-alist2 x x-path))
             (consp x-path))
         (strip-cars (abs-fs-fix abs-file-alist1))
       (append (strip-cars (remove-equal (nfix x)
                                         (abs-fs-fix abs-file-alist1)))
               (strip-cars (abs-fs-fix abs-file-alist2))))))))

(defthmd
  abs-separate-of-put-assoc-lemma-4
  (implies
   (and
    (dist-names dir1 relpath1 frame)
    (not (prefixp (fat32-filename-list-fix relpath1)
                  (fat32-filename-list-fix relpath2)))
    (prefixp (frame-val->path (cdr (assoc-equal src frame)))
             (fat32-filename-list-fix relpath2))
    (not
     (intersectp-equal
      (names-at dir1 nil)
      (names-at
       (context-apply
        (frame-val->dir (cdr (assoc-equal src frame)))
        dir2 x2
        (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
                relpath2))
       (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
               relpath1))))
    (abs-fs-p
     (context-apply
      (frame-val->dir (cdr (assoc-equal src frame)))
      dir2 x2
      (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
              relpath2))))
   (dist-names
    dir1 relpath1
    (put-assoc-equal
     src
     (frame-val
      (frame-val->path (cdr (assoc-equal src frame)))
      (context-apply
       (frame-val->dir (cdr (assoc-equal src frame)))
       dir2 x2
       (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
               relpath2))
      (frame-val->src (cdr (assoc-equal src frame))))
     frame)))
  :hints (("goal" :in-theory (enable dist-names names-at
                                     intersectp-equal prefixp))))

(defthm
  abs-separate-of-put-assoc-lemma-5
  (implies
   (and
    (< 0 x)
    (context-apply-ok
     (frame-val->dir (cdr (assoc-equal src (cdr frame))))
     dir x
     (nthcdr (len (frame-val->path (cdr (assoc-equal src (cdr frame)))))
             relpath))
    (integerp x))
   (consp (assoc-equal src (cdr frame)))))

(defthm
  abs-separate-of-put-assoc-lemma-6
  (implies
   (and
    (not (prefixp (frame-val->path (cdr (car frame)))
                  (fat32-filename-list-fix relpath)))
    (dist-names (frame-val->dir (cdr (car frame)))
                (frame-val->path (cdr (car frame)))
                (cdr frame))
    (< 0 x)
    (prefixp (fat32-filename-list-fix relpath)
             (frame-val->path (cdr (car frame))))
    (not
     (intersectp-equal
      (names-at (frame-val->dir (cdr (car frame))) nil)
      (names-at dir
                (nthcdr (len relpath)
                        (frame-val->path (cdr (car frame)))))))
    (prefixp (frame-val->path (cdr (assoc-equal src (cdr frame))))
             (fat32-filename-list-fix relpath))
    (context-apply-ok
     (frame-val->dir (cdr (assoc-equal src (cdr frame))))
     dir x
     (nthcdr (len (frame-val->path (cdr (assoc-equal src (cdr frame)))))
             relpath))
    (integerp x)
    (abs-fs-p
     (context-apply
      (frame-val->dir (cdr (assoc-equal src (cdr frame))))
      dir x
      (nthcdr (len (frame-val->path (cdr (assoc-equal src (cdr frame)))))
              relpath))))
   (dist-names
    (frame-val->dir (cdr (car frame)))
    (frame-val->path (cdr (car frame)))
    (put-assoc-equal
     src
     (frame-val
      (frame-val->path (cdr (assoc-equal src (cdr frame))))
      (context-apply
       (frame-val->dir (cdr (assoc-equal src (cdr frame))))
       dir x
       (nthcdr (len (frame-val->path (cdr (assoc-equal src (cdr frame)))))
               relpath))
      (frame-val->src (cdr (assoc-equal src (cdr frame)))))
     (cdr frame))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable (:rewrite prefixp-nthcdr-nthcdr))
    :use
    ((:instance (:rewrite abs-separate-of-put-assoc-lemma-4)
                (relpath2 relpath)
                (x2 x)
                (dir2 dir)
                (frame (cdr frame))
                (src src)
                (relpath1 (frame-val->path (cdr (car frame))))
                (dir1 (frame-val->dir (cdr (car frame)))))
     (:instance
      (:rewrite prefixp-nthcdr-nthcdr)
      (l2 (fat32-filename-list-fix relpath))
      (l1 (frame-val->path (cdr (car frame))))
      (n (len (frame-val->path (cdr (assoc-equal src (cdr frame)))))))))))

(defthm
  abs-separate-of-put-assoc-lemma-8
  (implies
   (and
    (dist-names dir1 relpath1 frame)
    (prefixp (frame-val->path (cdr (assoc-equal src frame)))
             (fat32-filename-list-fix relpath2))
    (not (intersectp-equal
          (names-at dir2 nil)
          (names-at dir1 (nthcdr (len relpath1) relpath2))))
    (not
     (intersectp-equal
      (names-at dir1 nil)
      (names-at
       (context-apply
        (frame-val->dir (cdr (assoc-equal src frame)))
        dir2 x2
        (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
                relpath2))
       (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
               relpath1))))
    (abs-fs-p
     (context-apply
      (frame-val->dir (cdr (assoc-equal src frame)))
      dir2 x2
      (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
              relpath2))))
   (dist-names
    dir1 relpath1
    (put-assoc-equal
     src
     (frame-val
      (frame-val->path (cdr (assoc-equal src frame)))
      (context-apply
       (frame-val->dir (cdr (assoc-equal src frame)))
       dir2 x2
       (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
               relpath2))
      (frame-val->src (cdr (assoc-equal src frame))))
     frame)))
  :hints
  (("goal" :in-theory (e/d (dist-names names-at
                                       intersectp-equal prefixp)))))

(defthm abs-separate-of-put-assoc-lemma-9
  (implies (and (not (equal (len (frame-val->path (cdr (car frame))))
                            (len relpath)))
                (prefixp (fat32-filename-list-fix relpath)
                         (frame-val->path (cdr (car frame)))))
           (not (prefixp (frame-val->path$inline (cdr (car frame)))
                         (fat32-filename-list-fix$inline relpath)))))

(defthm abs-separate-of-put-assoc-lemma-19
  (equal (names-at fs (nthcdr (len relpath) relpath))
         (names-at fs nil))
  :hints (("goal" :in-theory (enable names-at))))

(defthm
  abs-separate-of-put-assoc-lemma-10
  (implies
   (and
    (dist-names (frame-val->dir (cdr (car frame)))
                (frame-val->path (cdr (car frame)))
                (cdr frame))
    (< 0 x)
    (prefixp (fat32-filename-list-fix relpath)
             (frame-val->path (cdr (car frame))))
    (not
     (intersectp-equal
      (names-at (frame-val->dir (cdr (car frame)))
                nil)
      (names-at dir
                (nthcdr (len relpath)
                        (frame-val->path (cdr (car frame)))))))
    (prefixp (frame-val->path (cdr (assoc-equal src (cdr frame))))
             (fat32-filename-list-fix relpath))
    (context-apply-ok
     (frame-val->dir (cdr (assoc-equal src (cdr frame))))
     dir x
     (nthcdr (len (frame-val->path (cdr (assoc-equal src (cdr frame)))))
             relpath))
    (integerp x)
    (abs-fs-p
     (context-apply
      (frame-val->dir (cdr (assoc-equal src (cdr frame))))
      dir x
      (nthcdr (len (frame-val->path (cdr (assoc-equal src (cdr frame)))))
              relpath))))
   (dist-names
    (frame-val->dir (cdr (car frame)))
    (frame-val->path (cdr (car frame)))
    (put-assoc-equal
     src
     (frame-val
      (frame-val->path (cdr (assoc-equal src (cdr frame))))
      (context-apply
       (frame-val->dir (cdr (assoc-equal src (cdr frame))))
       dir x
       (nthcdr (len (frame-val->path (cdr (assoc-equal src (cdr frame)))))
               relpath))
      (frame-val->src (cdr (assoc-equal src (cdr frame)))))
     (cdr frame))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d
     (list-equiv)
     (nthcdr-when->=-n-len-l (:rewrite prefixp-when-equal-lengths)
                             (:rewrite abs-separate-of-put-assoc-lemma-1)))
    :use ((:instance (:rewrite prefixp-when-equal-lengths)
                     (y (fat32-filename-list-fix relpath))
                     (x (frame-val->path (cdr (car frame)))))
          (:instance (:rewrite abs-separate-of-put-assoc-lemma-1)
                     (relpath (frame-val->path (cdr (car frame))))))
    :cases
    ((<
      (binary-+
       (len relpath)
       (unary--
        (len (frame-val->path$inline (cdr (assoc-equal src (cdr frame)))))))
      '0)))))

(defthm abs-separate-of-put-assoc-lemma-11
  (implies (prefixp (frame-val->path (cdr (car frame)))
                    relpath)
           (prefixp (frame-val->path (cdr (car frame)))
                    (append relpath x-path))))

(defthm
  abs-separate-of-put-assoc-lemma-13
  (implies (prefixp relpath
                    (frame-val->path (cdr (car frame))))
           (equal (prefixp (append relpath x-path)
                           (frame-val->path (cdr (car frame))))
                  (prefixp x-path
                           (nthcdr (len relpath)
                                   (frame-val->path (cdr (car frame)))))))
  :hints (("goal" :in-theory (disable (:rewrite binary-append-take-nthcdr)
                                      (:rewrite take-when-prefixp)
                                      (:rewrite prefixp-nthcdr-nthcdr))
           :use ((:instance (:rewrite binary-append-take-nthcdr)
                            (l (frame-val->path (cdr (car frame))))
                            (i (len relpath)))
                 (:instance (:rewrite take-when-prefixp)
                            (y (frame-val->path (cdr (car frame))))
                            (x relpath))
                 (:instance (:rewrite prefixp-nthcdr-nthcdr)
                            (l2 (frame-val->path (cdr (car frame))))
                            (l1 (append relpath x-path))
                            (n (len relpath)))))))

(defthm
  abs-separate-of-put-assoc-lemma-14
  (implies (and (abs-fs-p (context-apply abs-file-alist1
                                         abs-file-alist2 x x-path))
                (dist-names abs-file-alist1 relpath frame)
                (dist-names abs-file-alist2 (append relpath x-path)
                            frame))
           (dist-names (context-apply abs-file-alist1
                                      abs-file-alist2 x x-path)
                       relpath frame))
  :hints
  (("goal"
    :in-theory (e/d (dist-names names-at)
                    ((:rewrite remove-when-absent)
                     (:linear count-free-clusters-correctness-1)
                     (:rewrite abs-fs-p-correctness-1)
                     (:type-prescription abs-addrs-when-m1-file-alist-p)
                     )))
   ("subgoal *1/5.2''"
    :in-theory (e/d (names-at)
                    ((:rewrite nthcdr-of-nthcdr)
                     (:rewrite nthcdr-when->=-n-len-l)))
    :use ((:instance (:rewrite nthcdr-when->=-n-len-l)
                     (l (fat32-filename-list-fix x-path))
                     (n (len (fat32-filename-list-fix x-path))))
          (:instance (:rewrite nthcdr-of-nthcdr)
                     (x (frame-val->path (cdr (car frame))))
                     (b (len relpath))
                     (a (len (fat32-filename-list-fix x-path))))))
   ("subgoal *1/5.1''"
    :in-theory (e/d (names-at)
                    ((:rewrite nthcdr-of-nthcdr)
                     (:rewrite nthcdr-when->=-n-len-l)))
    :use ((:instance (:rewrite nthcdr-of-nthcdr)
                     (x (frame-val->path (cdr (car frame))))
                     (b (len relpath))
                     (a (len (fat32-filename-list-fix x-path))))
          (:instance (:rewrite nthcdr-when->=-n-len-l)
                     (l (fat32-filename-list-fix x-path))
                     (n (len (fat32-filename-list-fix x-path))))))))

(defthm
  abs-separate-of-put-assoc-lemma-12
  (implies
   (and
    (abs-fs-p (context-apply (frame-val->dir (cdr (car frame)))
                             dir x
                             (nthcdr (len (frame-val->path (cdr (car frame))))
                                     relpath)))
    (dist-names dir relpath (cdr frame))
    (prefixp (frame-val->path (cdr (car frame)))
             (fat32-filename-list-fix relpath))
    (dist-names (frame-val->dir (cdr (car frame)))
                (frame-val->path (cdr (car frame)))
                (cdr frame)))
   (dist-names
    (context-apply (frame-val->dir (cdr (car frame)))
                   dir x
                   (nthcdr (len (frame-val->path (cdr (car frame))))
                           relpath))
    (frame-val->path (cdr (car frame)))
    (cdr frame)))
  :hints
  (("goal" :in-theory (disable (:rewrite binary-append-take-nthcdr))
    :use ((:instance (:rewrite binary-append-take-nthcdr)
                     (l relpath)
                     (i (len (frame-val->path (cdr (car frame))))))))))

(defthm
  abs-separate-of-put-assoc-lemma-16
  (implies
   (and
    (abs-fs-p (context-apply (frame-val->dir (cdr (car frame)))
                             dir2 x2
                             (nthcdr (len (frame-val->path (cdr (car frame))))
                                     relpath2)))
    (not (prefixp (fat32-filename-list-fix relpath2)
                  (fat32-filename-list-fix relpath1)))
    (prefixp (frame-val->path (cdr (car frame)))
             (fat32-filename-list-fix relpath2))
    (prefixp (frame-val->path (cdr (car frame)))
             (fat32-filename-list-fix relpath1)))
   (equal
    (names-at
     (context-apply (frame-val->dir (cdr (car frame)))
                    dir2 x2
                    (nthcdr (len (frame-val->path (cdr (car frame))))
                            relpath2))
     (nthcdr (len (frame-val->path (cdr (car frame))))
             relpath1))
    (names-at (frame-val->dir (cdr (car frame)))
              (nthcdr (len (frame-val->path (cdr (car frame))))
                      relpath1))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable (:rewrite prefixp-nthcdr-nthcdr)
                        (:rewrite names-at-of-context-apply))
    :use
    ((:instance (:rewrite prefixp-nthcdr-nthcdr)
                (l2 (fat32-filename-list-fix relpath1))
                (l1 (fat32-filename-list-fix relpath2))
                (n (len (frame-val->path (cdr (car frame))))))
     (:instance (:rewrite names-at-of-context-apply)
                (relpath (nthcdr (len (frame-val->path (cdr (car frame))))
                                 relpath1))
                (x-path (nthcdr (len (frame-val->path (cdr (car frame))))
                                relpath2))
                (x x2)
                (abs-file-alist dir2)
                (root (frame-val->dir (cdr (car frame)))))))))

(defthm
  abs-separate-of-put-assoc-lemma-15
  (implies
   (and
    (dist-names dir1 relpath1 frame)
    (not (prefixp (fat32-filename-list-fix relpath1)
                  (fat32-filename-list-fix relpath2)))
    (not (prefixp (fat32-filename-list-fix relpath2)
                  (fat32-filename-list-fix relpath1)))
    (prefixp (frame-val->path (cdr (assoc-equal src frame)))
             (fat32-filename-list-fix relpath2))
    (abs-fs-p
     (context-apply
      (frame-val->dir (cdr (assoc-equal src frame)))
      dir2 x2
      (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
              relpath2))))
   (dist-names
    dir1 relpath1
    (put-assoc-equal
     src
     (frame-val
      (frame-val->path (cdr (assoc-equal src frame)))
      (context-apply
       (frame-val->dir (cdr (assoc-equal src frame)))
       dir2 x2
       (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
               relpath2))
      (frame-val->src (cdr (assoc-equal src frame))))
     frame)))
  :hints (("goal" :in-theory (enable dist-names
                                     names-at intersectp-equal))))

(defthm
  abs-separate-of-put-assoc-lemma-17
  (implies
   (and
    (dist-names dir1 relpath1 frame)
    (not (prefixp (fat32-filename-list-fix relpath2)
                  (fat32-filename-list-fix relpath1)))
    (prefixp (frame-val->path (cdr (assoc-equal src frame)))
             (fat32-filename-list-fix relpath2))
    (not (intersectp-equal
          (names-at dir2 nil)
          (names-at dir1 (nthcdr (len relpath1) relpath2))))
    (abs-fs-p
     (context-apply
      (frame-val->dir (cdr (assoc-equal src frame)))
      dir2 x2
      (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
              relpath2))))
   (dist-names
    dir1 relpath1
    (put-assoc-equal
     src
     (frame-val
      (frame-val->path (cdr (assoc-equal src frame)))
      (context-apply
       (frame-val->dir (cdr (assoc-equal src frame)))
       dir2 x2
       (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
               relpath2))
      (frame-val->src (cdr (assoc-equal src frame))))
     frame)))
  :hints
  (("goal" :in-theory (e/d (dist-names names-at
                                       intersectp-equal prefixp)))))

;; Taking a chance on changing this lemma's rewrite rule. We should have
;; something more general than we had before, let's see...
(defthm
  abs-separate-of-put-assoc-1
  (implies
   (and (< 0 x)
        (integerp x)
        (abs-complete (abs-fs-fix dir))
        (dist-names dir
                    relpath frame)
        (prefixp (frame-val->path (cdr (assoc-equal src frame)))
                 (fat32-filename-list-fix relpath))
        (context-apply-ok
         (frame-val->dir (cdr (assoc-equal src frame)))
         dir x
         (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
                 relpath))
        (abs-separate frame))
   (abs-separate
    (put-assoc-equal
     src
     (frame-val
      (frame-val->path (cdr (assoc-equal src frame)))
      (context-apply
       (frame-val->dir (cdr (assoc-equal src frame)))
       dir x
       (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
               relpath))
      (frame-val->src (cdr (assoc-equal src frame))))
     frame)))
  :hints
  (("goal"
    :in-theory (e/d (abs-separate dist-names prefixp)
                    (nthcdr-when->=-n-len-l))
    :induct
    (mv
     (abs-separate frame)
     (put-assoc-equal
      src
      (frame-val
       (frame-val->path (cdr (assoc-equal src frame)))
       (context-apply
        (frame-val->dir (cdr (assoc-equal src frame)))
        dir x
        (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
                relpath))
       (frame-val->src (cdr (assoc-equal src frame))))
      frame))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and
      (< 0 x)
      (integerp x)
      (abs-complete (abs-fs-fix dir))
      (dist-names dir
                  relpath frame)
      (prefixp (frame-val->path (cdr (assoc-equal src other-frame)))
               (fat32-filename-list-fix relpath))
      (context-apply-ok
       (frame-val->dir (cdr (assoc-equal src other-frame)))
       dir x
       (nthcdr (len (frame-val->path (cdr (assoc-equal src other-frame))))
               relpath))
      (abs-separate frame)
      (force (equal (assoc-equal src frame)
                    (assoc-equal src other-frame))))
     (abs-separate
      (put-assoc-equal
       src
       (frame-val
        (frame-val->path (cdr (assoc-equal src other-frame)))
        (context-apply
         (frame-val->dir (cdr (assoc-equal src other-frame)))
         dir x
         (nthcdr (len (frame-val->path (cdr (assoc-equal src other-frame))))
                 relpath))
        (frame-val->src (cdr (assoc-equal src other-frame))))
       frame))))))

(defund frame-addrs-root (frame)
  (declare (xargs :guard (frame-p frame)))
  (cond ((atom frame) nil)
        ((zp (frame-val->src (cdar frame)))
         (cons (caar frame) (frame-addrs-root (cdr frame))))
        (t (frame-addrs-root (cdr frame)))))

(defthm
  frame-addrs-root-correctness-1
  (implies (and (consp (assoc-equal name frame))
                (equal (frame-val->src frame-val)
                       (frame-val->src (cdr (assoc-equal name frame)))))
           (equal (frame-addrs-root (put-assoc-equal name frame-val frame))
                  (frame-addrs-root frame)))
  :hints (("goal" :in-theory (enable frame-addrs-root))))

(defthm frame-addrs-root-correctness-2
  (implies (not (member-equal x (strip-cars frame)))
           (not (member-equal x (frame-addrs-root frame))))
  :hints (("goal" :in-theory (enable frame-addrs-root))))

(defthm frame-addrs-root-correctness-3
  (implies (frame-p frame)
           (equal (frame-addrs-root (remove-assoc-equal name frame))
                  (remove-equal name (frame-addrs-root frame))))
  :hints (("goal" :in-theory (enable frame-addrs-root))))

(defthm
  frame-addrs-root-correctness-4
  (implies (and (not (null x))
                (no-duplicatesp-equal (strip-cars frame)))
           (iff (member-equal x (frame-addrs-root frame))
                (and (consp (assoc-equal x frame))
                     (zp (frame-val->src (cdr (assoc-equal x frame)))))))
  :hints (("goal" :in-theory (enable frame-addrs-root))))

(defthm
  abs-separate-correctness-1-lemma-1
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
    (abs-file-alist-p abs-file-alist2)
    (subsetp-equal
     (abs-addrs abs-file-alist2)
     (abs-addrs
      (abs-file->contents (cdr (assoc-equal name abs-file-alist1))))))
   (subsetp-equal
    (abs-addrs (put-assoc-equal name (abs-file dir-ent abs-file-alist2)
                                abs-file-alist1))
    (abs-addrs abs-file-alist1)))
  :hints (("goal" :in-theory (enable abs-addrs))))

;; This is important!
(defthm
  abs-separate-correctness-1-lemma-3
  (implies (atom (abs-addrs (abs-fs-fix abs-file-alist2)))
           (subsetp-equal (abs-addrs (context-apply abs-file-alist1
                                                    abs-file-alist2 x x-path))
                          (abs-addrs (abs-fs-fix abs-file-alist1))))
  :hints (("goal" :in-theory (e/d (context-apply) (nfix))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (abs-fs-p abs-file-alist1)
          (atom (abs-addrs (abs-fs-fix abs-file-alist2))))
     (subsetp-equal (abs-addrs (context-apply abs-file-alist1
                                              abs-file-alist2 x x-path))
                    (abs-addrs abs-file-alist1))))))

(defthm abs-separate-correctness-1-lemma-4
  (implies (and (frame-p frame)
                (not (zp (1st-complete frame)))
                (no-duplicatesp-equal (strip-cars frame)))
           (equal (abs-addrs (frame-val->dir (cdr (assoc-equal
                                                   (1st-complete frame) frame))))
                  nil))
  :hints (("Goal" :in-theory (enable 1st-complete)) ))

;; This is a hack...
(defthm
  abs-separate-correctness-1-lemma-2
  (implies (abs-file-alist-p abs-file-alist)
           (subsetp-equal (abs-addrs (abs-fs-fix abs-file-alist))
                          (abs-addrs abs-file-alist)))
  :hints
  (("goal"
    :in-theory (e/d (abs-addrs abs-fs-fix abs-file-alist-p
                               abs-file-fix abs-file->contents)
                    ((:rewrite abs-file-alist-p-correctness-1-lemma-1)
                     (:rewrite abs-file-alist-p-correctness-1)
                     (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
                     (:rewrite abs-file->contents-when-m1-file-p)
                     (:rewrite m1-file-contents-p-correctness-1)
                     (:rewrite abs-directory-file-p-when-m1-file-p)
                     (:rewrite abs-file-alist-p-when-m1-file-alist-p)
                     (:rewrite abs-file-alist-p-of-cdr))))
   ("subgoal *1/5''" :expand (abs-addrs abs-file-alist))))

(defthm
  abs-separate-correctness-1-lemma-27
  (implies
   (and
    (subsetp-equal
     (abs-addrs
      (mv-nth
       0
       (collapse
        (frame-with-root
         (context-apply
          root
          (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame)))
          (1st-complete frame)
          (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                             frame))))
         (remove-assoc-equal (1st-complete frame)
                             frame)))))
     (abs-addrs
      (abs-fs-fix
       (context-apply root
                      (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      (1st-complete frame)
                      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                         frame)))))))
    (< 0 (1st-complete frame))
    (context-apply-ok root
                      (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      (1st-complete frame)
                      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                         frame))))
    (abs-file-alist-p root)
    (abs-no-dups-p root)
    (frame-p frame)
    (no-duplicatesp-equal (abs-addrs root))
    (no-duplicatesp-equal (strip-cars frame)))
   (not
    (member-equal
     (1st-complete frame)
     (abs-addrs
      (mv-nth
       0
       (collapse
        (frame-with-root
         (context-apply
          root
          (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame)))
          (1st-complete frame)
          (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                             frame))))
         (remove-assoc-equal (1st-complete frame)
                             frame))))))))
  :hints
  (("goal"
    :in-theory (e/d (intersectp-equal)
                    ((:rewrite subsetp-member . 4)))
    :use
    ((:instance
      (:rewrite abs-addrs-of-context-apply-1)
      (x-path (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                 frame))))
      (abs-file-alist2 (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                         frame))))
      (abs-file-alist1 root)
      (x (1st-complete frame)))
     (:instance
      (:rewrite subsetp-member . 4)
      (x
       (abs-addrs
        (abs-fs-fix
         (context-apply
          root
          (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame)))
          (1st-complete frame)
          (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                             frame)))))))
      (a (1st-complete frame))
      (y
       (abs-addrs
        (context-apply
         root
         (frame-val->dir$inline (cdr (assoc-equal (1st-complete frame)
                                                  frame)))
         (1st-complete frame)
         (frame-val->path$inline (cdr (assoc-equal (1st-complete frame)
                                                   frame)))))))
     (:instance
      (:rewrite subsetp-member . 4)
      (y
       (abs-addrs
        (abs-fs-fix
         (context-apply
          root
          (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame)))
          (1st-complete frame)
          (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                             frame)))))))
      (x
       (abs-addrs
        (mv-nth
         0
         (collapse
          (frame-with-root
           (context-apply
            root
            (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                              frame)))
            (1st-complete frame)
            (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                               frame))))
           (remove-assoc-equal (1st-complete frame)
                               frame))))))
      (a (1st-complete frame)))))))

(defthm
  abs-separate-correctness-1-lemma-9
  (implies
   (dist-names root nil frame)
   (not
    (intersectp-equal
     (names-at (frame-val->dir$inline (cdr (assoc-equal x frame)))
               nil)
     (names-at
      root
      (frame-val->path$inline (cdr (assoc-equal x frame)))))))
  :hints (("goal" :in-theory (enable dist-names prefixp
                                     intersectp-equal names-at)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (dist-names root nil frame)
          (equal relpath
                 (frame-val->path$inline (cdr (assoc-equal x frame)))))
     (not
      (intersectp-equal
       (names-at (frame-val->dir$inline (cdr (assoc-equal x frame)))
                 nil)
       (names-at root relpath)))))
   (:rewrite
    :corollary
    (implies
     (and
      (set-equiv
       names
       (names-at
        (frame-val->dir$inline (cdr (assoc-equal x frame)))
        nil))
      (dist-names root nil frame))
     (not (intersectp-equal
           names
           (names-at
            root
            (frame-val->path$inline
             (cdr (assoc-equal x frame))))))))
   (:rewrite
    :corollary
    (implies
     (and (dist-names root nil frame)
          (equal relpath
                 (frame-val->path$inline (cdr (assoc-equal x frame)))))
     (not
      (intersectp-equal
       (names-at root relpath)
       (names-at (frame-val->dir$inline (cdr (assoc-equal x frame)))
                 nil)))))))

(defthm
  abs-separate-correctness-1-lemma-12
  (implies (and (not (consp x))
                (not (null (car relpath))))
           (equal (assoc-equal (car relpath)
                               (remove-equal x fs))
                  (assoc-equal (car relpath) fs))))

(defthm
  abs-separate-correctness-1-lemma-13
  (implies (and (natp x) (abs-file-alist-p fs))
           (equal (names-at (remove-equal x fs)
                            relpath)
                  (names-at fs relpath)))
  :hints
  (("goal" :in-theory (enable names-at fat32-filename-list-p)
    :induct (names-at fs relpath)
    :expand ((:with (:rewrite assoc-of-remove)
                    (assoc-equal (fat32-filename-fix (car relpath))
                                 (remove-equal x (abs-fs-fix fs))))
             (names-at (remove-equal x fs)
                       relpath)))))

(defthm abs-separate-correctness-1-lemma-11
  (implies (not (null name))
           (equal (assoc-equal name
                               (append (remove-equal x root)
                                       abs-file-alist))
                  (if (consp (assoc-equal name (remove-equal x root)))
                      (assoc-equal name (remove-equal x root))
                    (assoc-equal name abs-file-alist)))))

(defthm
  abs-separate-correctness-1-lemma-15
  (implies (and (dist-names root nil frame)
                (dist-names abs-file-alist x-path frame)
                (abs-fs-p (context-apply root abs-file-alist x x-path)))
           (dist-names (context-apply root abs-file-alist x x-path)
                       nil frame))
  :hints (("goal" :in-theory (enable dist-names prefixp))))

(defthm
  abs-separate-correctness-1-lemma-19
  (implies
   (and (dist-names dir relpath frame)
        (prefixp (fat32-filename-list-fix relpath)
                 (frame-val->path (cdr (assoc-equal x frame)))))
   (not
    (intersectp-equal
     (names-at (frame-val->dir (cdr (assoc-equal x frame)))
               nil)
     (names-at
      dir
      (nthcdr (len relpath)
              (frame-val->path (cdr (assoc-equal x frame))))))))
  :hints (("goal" :in-theory (enable dist-names
                                     prefixp intersectp-equal))))

;; The :with hint doesn't work, because of hiding.
(defthm
  abs-separate-correctness-1-lemma-22
  (implies (abs-separate frame)
           (dist-names (frame-val->dir (cdr (assoc-equal x frame)))
                       (frame-val->path (cdr (assoc-equal x frame)))
                       (remove-assoc-equal x frame)))
  :hints
  (("goal" :in-theory (e/d (abs-separate dist-names))
    :induct (remove-assoc-equal x frame)
    :expand
    ((names-at nil (frame-val->path (cdr (car frame))))
     (intersectp-equal nil
                       (names-at (frame-val->dir (cdr (car frame)))
                                 nil))))
   ("subgoal *1/3''" :cases ((consp (assoc-equal x (cdr frame))))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies (and (abs-separate frame)
                  (absfat-equiv dir
                                (frame-val->dir (cdr (assoc-equal x frame)))))
             (dist-names dir
                         (frame-val->path (cdr (assoc-equal x frame)))
                         (remove-assoc-equal x frame))))
   (:rewrite
    :corollary
    (implies
     (and
      (abs-separate frame)
      (fat32-filename-list-equiv relpath
                                 (frame-val->path (cdr (assoc-equal x frame)))))
     (dist-names (frame-val->dir (cdr (assoc-equal x frame)))
                 relpath (remove-assoc-equal x frame))))))

;; Obtained by replacing (1st-complete frame) with x in the proof-builder.
(defthm
  abs-separate-correctness-1-lemma-10
  (implies
   (and
    (dist-names root nil frame)
    (abs-separate frame)
    (abs-fs-p (context-apply root
                             (frame-val->dir (cdr (assoc-equal x frame)))
                             x
                             (frame-val->path (cdr (assoc-equal x frame))))))
   (dist-names
    (context-apply root
                   (frame-val->dir (cdr (assoc-equal x frame)))
                   x
                   (frame-val->path (cdr (assoc-equal x frame))))
    nil (remove-assoc-equal x frame)))
  :hints (("goal" :in-theory (enable dist-names prefixp abs-separate)
           :do-not-induct t)))

(defthm
  abs-separate-correctness-1-lemma-16
  (implies
   (and
    (< 0 (1st-complete frame))
    (frame-p frame)
    (abs-separate (frame-with-root root frame))
    (no-duplicatesp-equal (strip-cars frame))
    (abs-fs-p
     (context-apply root
                    (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                      frame)))
                    (1st-complete frame)
                    (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                       frame))))))
   (abs-separate
    (frame-with-root
     (context-apply root
                    (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                      frame)))
                    (1st-complete frame)
                    (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                       frame))))
     (remove-assoc-equal (1st-complete frame)
                         frame))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (frame-with-root abs-separate)
                    (abs-addrs-of-context-apply-3))
    :use
    (:instance
     (:rewrite abs-addrs-of-context-apply-3)
     (x-path (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame))))
     (x (1st-complete frame))
     (abs-file-alist2 (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                        frame))))
     (abs-file-alist1 root)))))

;; The second rewrite rule is used explicitly in one theorem.
(defthm
  abs-separate-correctness-1-lemma-8
  (implies (abs-file-alist-p x)
           (subsetp-equal (remove-equal nil (strip-cars (abs-fs-fix x)))
                          (remove-equal nil (strip-cars x))))
  :hints (("goal" :in-theory (enable abs-fs-fix abs-file-fix
                                     abs-file->contents abs-file-alist-p)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (abs-file-alist-p x)
          (not (intersectp-equal y (remove-equal nil (strip-cars x)))))
     (not (intersectp-equal y
                            (remove-equal nil (strip-cars (abs-fs-fix x))))))
    :hints
    (("goal"
      :use (:instance (:rewrite intersect-with-subset)
                      (x (remove-equal nil (strip-cars (abs-fs-fix x))))
                      (z y)
                      (y (remove-equal nil (strip-cars x)))))))))

(defthm
  abs-separate-correctness-1-lemma-28
  (implies
   (and
    (not (intersectp-equal
          (names-at (frame-val->dir (cdr (car frame)))
                    nil)
          (names-at root
                    (frame-val->path (cdr (car frame))))))
    (prefixp (frame-val->path (cdr (car frame)))
             (fat32-filename-list-fix relpath))
    (not (intersectp-equal (names-at dir nil)
                           (names-at root relpath)))
    (abs-fs-p (context-apply (frame-val->dir (cdr (car frame)))
                             dir x
                             (nthcdr (len (frame-val->path (cdr (car frame))))
                                     relpath))))
   (not
    (intersectp-equal
     (names-at root
               (frame-val->path (cdr (car frame))))
     (names-at
      (context-apply (frame-val->dir (cdr (car frame)))
                     dir x
                     (nthcdr (len (frame-val->path (cdr (car frame))))
                             relpath))
      nil))))
  :hints
  (("goal"
    :in-theory (e/d (names-at)
                    ((:rewrite abs-separate-correctness-1-lemma-8
                               . 2)))
    :use
    (:instance (:rewrite abs-separate-correctness-1-lemma-8 . 2)
               (x (frame-val->dir (cdr (car frame))))
               (y (names-at root
                            (frame-val->path (cdr (car frame)))))))))

(defthmd
  abs-separate-correctness-1-lemma-17
  (implies
   (and
    (consp (assoc-equal src frame))
    (prefixp (frame-val->path (cdr (assoc-equal src frame)))
             (fat32-filename-list-fix relpath))
    (dist-names root nil frame)
    (not (intersectp-equal (names-at dir nil)
                           (names-at root relpath)))
    (abs-fs-p
     (context-apply
      (frame-val->dir (cdr (assoc-equal src frame)))
      dir x
      (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
              relpath))))
   (dist-names
    root nil
    (put-assoc-equal
     src
     (frame-val
      (frame-val->path (cdr (assoc-equal src frame)))
      (context-apply
       (frame-val->dir (cdr (assoc-equal src frame)))
       dir x
       (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
               relpath))
      (frame-val->src (cdr (assoc-equal src frame))))
     frame)))
  :hints (("goal" :in-theory (enable dist-names prefixp))))

(defthm
  abs-separate-correctness-1-lemma-18
  (implies
   (and
    (abs-fs-p
     (context-apply
      (frame-val->dir
       (cdr (assoc-equal (frame-val->src (cdr (assoc-equal x frame)))
                         frame)))
      (frame-val->dir (cdr (assoc-equal x frame)))
      x
      (nthcdr
       (len
        (frame-val->path
         (cdr (assoc-equal (frame-val->src (cdr (assoc-equal x frame)))
                           frame))))
       (frame-val->path (cdr (assoc-equal x frame))))))
    (not (equal (frame-val->src (cdr (assoc-equal x frame)))
                x))
    (consp (assoc-equal (frame-val->src (cdr (assoc-equal x frame)))
                        frame))
    (prefixp
     (frame-val->path
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal x frame)))
                        frame)))
     (frame-val->path (cdr (assoc-equal x frame))))
    (dist-names root nil frame))
   (dist-names
    root nil
    (put-assoc-equal
     (frame-val->src (cdr (assoc-equal x frame)))
     (frame-val
      (frame-val->path
       (cdr (assoc-equal (frame-val->src (cdr (assoc-equal x frame)))
                         frame)))
      (context-apply
       (frame-val->dir
        (cdr (assoc-equal (frame-val->src (cdr (assoc-equal x frame)))
                          frame)))
       (frame-val->dir (cdr (assoc-equal x frame)))
       x
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal (frame-val->src (cdr (assoc-equal x frame)))
                            frame))))
        (frame-val->path (cdr (assoc-equal x frame)))))
      (frame-val->src
       (cdr (assoc-equal (frame-val->src (cdr (assoc-equal x frame)))
                         frame))))
     (remove-assoc-equal x frame))))
  :hints
  (("goal"
    :use (:instance abs-separate-correctness-1-lemma-17
                    (src (frame-val->src (cdr (assoc-equal x frame))))
                    (dir (frame-val->dir (cdr (assoc-equal x frame))))
                    (relpath (frame-val->path (cdr (assoc-equal x frame))))
                    (frame (remove-assoc-equal x frame))))))

(defthm
  abs-separate-correctness-1-lemma-20
  (implies
   (and (atom (abs-addrs (abs-fs-fix dir)))
        (no-duplicatesp-equal (abs-addrs (frame-val->dir (cdr (car frame))))))
   (no-duplicatesp-equal
    (abs-addrs
     (context-apply (frame-val->dir (cdr (car frame)))
                    dir x
                    (nthcdr (len (frame-val->path (cdr (car frame))))
                            relpath)))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite abs-addrs-of-context-apply-3))
    :use ((:instance (:rewrite abs-addrs-of-context-apply-3)
                     (x-path (nthcdr (len (frame-val->path (cdr (car frame))))
                                     relpath))
                     (x x)
                     (abs-file-alist2 dir)
                     (abs-file-alist1 (frame-val->dir (cdr (car frame)))))))))

(defthm
  abs-separate-correctness-1-lemma-21
  (implies
   (and
    (no-duplicatesp-equal (strip-cars frame))
    (< 0 (1st-complete frame))
    (not (equal (1st-complete-src frame)
                (1st-complete frame)))
    (consp (assoc-equal (1st-complete-src frame)
                        frame))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                frame)))
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame))))
    (context-apply-ok
     (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                       frame)))
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (1st-complete frame)
     (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                     frame))))
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))))
    (frame-p frame)
    (abs-separate (frame-with-root root frame))
    (abs-fs-p
     (context-apply
      (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                        frame)))
      (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                        frame)))
      (1st-complete frame)
      (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                      frame))))
              (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                 frame)))))))
   (abs-separate
    (frame-with-root
     root
     (put-assoc-equal
      (1st-complete-src frame)
      (frame-val
       (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                          frame)))
       (context-apply
        (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                          frame)))
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (1st-complete frame)
        (nthcdr
         (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                 frame))))
         (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                            frame)))))
       (frame-val->src (cdr (assoc-equal (1st-complete-src frame)
                                         frame))))
      (remove-assoc-equal (1st-complete frame)
                          frame)))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable frame-with-root
                              abs-separate 1st-complete-src))))

(defthm
  abs-separate-correctness-1-lemma-34
  (implies (and (< 0 (1st-complete frame))
                (frame-p frame)
                (no-duplicatesp-equal (strip-cars frame)))
           (hifat-no-dups-p
            (frame-val->dir$inline (cdr (assoc-equal (1st-complete frame)
                                                     frame)))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite abs-no-dups-p-when-m1-file-alist-p))
    :use
    ((:instance (:rewrite abs-no-dups-p-when-m1-file-alist-p)
                (fs (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                      frame)))))))))

(defthm
  abs-separate-correctness-1-lemma-51
  (implies
   (and (< 0 (1st-complete-src frame))
        (member-equal (1st-complete frame)
                      (abs-addrs root))
        (no-duplicatesp-equal (strip-cars frame))
        (subsetp-equal (abs-addrs root)
                       (frame-addrs-root frame)))
   (let
       ((fs
         (mv-nth
          0
          (collapse
           (frame-with-root
            root
            (put-assoc-equal
             (1st-complete-src frame)
             (frame-val
              (frame-val->path
               (cdr (assoc-equal (1st-complete-src frame)
                                 frame)))
              (context-apply
               (frame-val->dir
                (cdr (assoc-equal (1st-complete-src frame)
                                  frame)))
               (frame-val->dir
                (cdr (assoc-equal (1st-complete frame)
                                  frame)))
               (1st-complete frame)
               (nthcdr
                (len
                 (frame-val->path
                  (cdr (assoc-equal (1st-complete-src frame)
                                    frame))))
                (frame-val->path
                 (cdr (assoc-equal (1st-complete frame)
                                   frame)))))
              (frame-val->src
               (cdr (assoc-equal (1st-complete-src frame)
                                 frame))))
             (remove-assoc-equal (1st-complete frame)
                                 frame)))))))
     (and (hifat-no-dups-p fs)
          (m1-file-alist-p fs))))
  :hints (("goal" :in-theory (enable 1st-complete-src))))

;; This is interesting because it talks about two arbitrarily chosen abstract
;; variables. Somehow it's hard to use directly, though...
(defthm
  abs-separate-correctness-1-lemma-14
  (implies
   (and (abs-separate frame)
        (consp (assoc-equal y frame))
        (not (equal x y))
        (prefixp (frame-val->path (cdr (assoc-equal y frame)))
                 (frame-val->path (cdr (assoc-equal x frame)))))
   (not
    (intersectp-equal
     (names-at (frame-val->dir (cdr (assoc-equal x frame)))
               nil)
     (names-at
      (frame-val->dir (cdr (assoc-equal y frame)))
      (nthcdr (len (frame-val->path (cdr (assoc-equal y frame))))
              (frame-val->path (cdr (assoc-equal x frame))))))))
  :hints (("goal" :in-theory (enable abs-separate)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (abs-separate frame)
          (consp (assoc-equal y frame))
          (not (equal x y))
          (prefixp (frame-val->path (cdr (assoc-equal y frame)))
                   (frame-val->path (cdr (assoc-equal x frame))))
          (set-equiv
           names
           (names-at (frame-val->dir (cdr (assoc-equal x frame)))
                     nil)))
     (not
      (intersectp-equal
       names
       (names-at
        (frame-val->dir (cdr (assoc-equal y frame)))
        (nthcdr (len (frame-val->path (cdr (assoc-equal y frame))))
                (frame-val->path (cdr (assoc-equal x frame)))))))))
   (:rewrite
    :corollary
    (implies
     (and (abs-separate frame)
          (consp (assoc-equal y frame))
          (not (equal x y))
          (prefixp (frame-val->path (cdr (assoc-equal y frame)))
                   (frame-val->path (cdr (assoc-equal x frame))))
          (fat32-filename-list-equiv
           relpath
           (nthcdr (len (frame-val->path (cdr (assoc-equal y frame))))
                   (frame-val->path (cdr (assoc-equal x frame))))))
     (not
      (intersectp-equal
       (names-at (frame-val->dir (cdr (assoc-equal x frame)))
                 nil)
       (names-at
        (frame-val->dir (cdr (assoc-equal y frame)))
        relpath)))))))

(defthm abs-separate-correctness-1-lemma-24
  (equal (abs-separate (frame-with-root root frame))
         (and (no-duplicatesp-equal (abs-addrs (abs-fs-fix root)))
              (dist-names root
                          nil frame)
              (abs-separate frame)))
  :hints (("goal" :in-theory (enable frame-with-root abs-separate))))

(defthm
  abs-separate-correctness-1-lemma-29
  (implies (not (consp (abs-addrs (frame->root frame))))
           (hifat-no-dups-p (frame->root frame)))
  :hints
  (("goal" :in-theory (disable (:rewrite abs-no-dups-p-when-m1-file-alist-p))
    :use ((:instance (:rewrite abs-no-dups-p-when-m1-file-alist-p)
                     (fs (frame->root frame)))))))

(defthm
  abs-separate-correctness-1-lemma-5
  (implies
   (and
    (< 0 (1st-complete (frame->frame frame)))
    (subsetp-equal
     (abs-addrs
      (mv-nth
       0
       (collapse
        (frame-with-root
         (context-apply
          (frame->root frame)
          (frame-val->dir
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
          (1st-complete (frame->frame frame))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))))
         (remove-assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
     (abs-addrs
      (abs-fs-fix
       (context-apply
        (frame->root frame)
        (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (1st-complete (frame->frame frame))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))))))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (frame-p (frame->frame frame)))
   (subsetp-equal
    (abs-addrs
     (mv-nth
      0
      (collapse
       (frame-with-root
        (context-apply
         (frame->root frame)
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
        (remove-assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))))
    (abs-addrs (frame->root frame))))
  :hints
  (("goal"
    :in-theory (disable subsetp-trans)
    :use
    ((:instance
      (:rewrite subsetp-trans)
      (z (abs-addrs (frame->root frame)))
      (y
       (abs-addrs
        (abs-fs-fix
         (context-apply
          (frame->root frame)
          (frame-val->dir
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
          (1st-complete (frame->frame frame))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))))
      (x
       (abs-addrs
        (mv-nth
         0
         (collapse
          (frame-with-root
           (context-apply
            (frame->root frame)
            (frame-val->dir
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame))))
            (1st-complete (frame->frame frame))
            (frame-val->path
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame)))))
           (remove-assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame))))))))
     (:instance
      subsetp-trans
      (z (abs-addrs (frame->root frame)))
      (x
       (abs-addrs
        (abs-fs-fix
         (context-apply
          (frame->root frame)
          (frame-val->dir
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
          (1st-complete (frame->frame frame))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))))
      (y
       (abs-addrs
        (context-apply
         (frame->root frame)
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))))))))))

(defthmd
  abs-separate-correctness-1-lemma-6
  (implies
   (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (frame-p (frame->frame frame)))
   (subsetp-equal (abs-addrs (mv-nth 0 (collapse frame)))
                  (abs-addrs (frame->root frame))))
  :hints (("goal" :in-theory (enable collapse))))

(defthm
  abs-separate-correctness-1-lemma-7
  (implies
   (and
    (< 0 (1st-complete frame))
    (context-apply-ok
     root
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (1st-complete frame)
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame))))
    (abs-file-alist-p root)
    (abs-no-dups-p root)
    (frame-p frame)
    (no-duplicatesp-equal (abs-addrs root))
    (no-duplicatesp-equal (strip-cars frame)))
   (not
    (member-equal
     (1st-complete frame)
     (abs-addrs
      (mv-nth
       0
       (collapse
        (frame-with-root
         (context-apply
          root
          (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame)))
          (1st-complete frame)
          (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                             frame))))
         (remove-assoc-equal (1st-complete frame)
                             frame))))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (intersectp-equal)
                    (subsetp-member))
    :use
    ((:instance
      (:rewrite subsetp-member . 4)
      (y
       (abs-addrs
        (context-apply
         root
         (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                           frame)))
         (1st-complete frame)
         (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                            frame))))))
      (x
       (abs-addrs
        (mv-nth
         0
         (collapse
          (frame-with-root
           (context-apply
            root
            (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                              frame)))
            (1st-complete frame)
            (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                               frame))))
           (remove-assoc-equal (1st-complete frame)
                               frame))))))
      (a (1st-complete frame)))
     (:instance
      abs-separate-correctness-1-lemma-6
      (frame
       (frame-with-root
        (context-apply root
                       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       (1st-complete frame)
                       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                          frame))))
        (remove-assoc-equal (1st-complete frame)
                            frame))))))))

(defthm
  abs-separate-correctness-1-lemma-23
  (implies
   (and
    (< 0 (1st-complete frame))
    (context-apply-ok
     root
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (1st-complete frame)
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame))))
    (not
     (intersectp-equal
      (remove-equal (1st-complete frame)
                    (strip-cars frame))
      (abs-addrs
       (mv-nth
        0
        (collapse
         (frame-with-root
          (context-apply
           root
           (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                             frame)))
           (1st-complete frame)
           (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                              frame))))
          (remove-assoc-equal (1st-complete frame)
                              frame)))))))
    (abs-file-alist-p root)
    (abs-no-dups-p root)
    (frame-p frame)
    (no-duplicatesp-equal (abs-addrs root))
    (no-duplicatesp-equal (strip-cars frame)))
   (not
    (intersectp-equal
     (strip-cars frame)
     (abs-addrs
      (mv-nth
       0
       (collapse
        (frame-with-root
         (context-apply
          root
          (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame)))
          (1st-complete frame)
          (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                             frame))))
         (remove-assoc-equal (1st-complete frame)
                             frame))))))))
  :hints
  (("goal"
    :do-not-induct t
    :use
    (:instance
     (:rewrite intersectp-when-member)
     (x (1st-complete frame))
     (y
      (abs-addrs
       (mv-nth
        0
        (collapse
         (frame-with-root
          (context-apply
           root
           (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                             frame)))
           (1st-complete frame)
           (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                              frame))))
          (remove-assoc-equal (1st-complete frame)
                              frame))))))
     (l (strip-cars frame))))))

(defthm
  abs-separate-correctness-1
  (implies (and (frame-p (frame->frame frame))
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (subsetp (abs-addrs (frame->root frame))
                         (frame-addrs-root (frame->frame frame)))
                (abs-separate (frame-with-root (frame->root frame)
                                               (frame->frame frame))))
           (mv-let (fs result)
             (collapse frame)
             (implies (equal result t)
                      (and (m1-file-alist-p fs)
                           (hifat-no-dups-p fs)))))
  :hints
  (("goal" :in-theory (enable collapse intersectp-equal)
    :induct (collapse frame))))

(defthm dist-names-of-append
  (equal (dist-names dir relpath (append frame1 frame2))
         (and (dist-names dir relpath frame1)
              (dist-names dir relpath frame2)))
  :hints (("goal" :in-theory (enable dist-names))))

(defund
  mutual-dist-names (frame1 frame2)
  (declare (xargs :guard (and (frame-p frame1)
                              (frame-p frame2))))
  (or (atom frame1)
      (and (dist-names (frame-val->dir (cdar frame1))
                       (frame-val->path (cdar frame1))
                       frame2)
           (mutual-dist-names (cdr frame1)
                              frame2))))

(defthm abs-separate-of-append
  (equal (abs-separate (append frame1 frame2))
         (and (abs-separate frame1)
              (abs-separate frame2)
              (mutual-dist-names frame1 frame2)))
  :hints (("goal" :in-theory (enable abs-separate
                                     mutual-dist-names))))

(defund abs-find-file-helper (fs pathname)
  (declare (xargs :guard (and (abs-file-alist-p fs)
                              (fat32-filename-list-p pathname))
                  :measure (acl2-count pathname)))
  (b*
      ((fs (abs-fs-fix fs))
       ((unless (consp pathname))
        (mv (make-abs-file) *enoent*))
       (name (mbe :logic (fat32-filename-fix (car pathname))
                  :exec (car pathname)))
       (alist-elem (abs-assoc name fs))
       ((unless (consp alist-elem))
        (mv (make-abs-file) *enoent*))
       ((when (abs-directory-file-p (cdr alist-elem)))
        (if (atom (cdr pathname))
            (mv (cdr alist-elem) 0)
          (abs-find-file-helper (abs-file->contents (cdr alist-elem))
                                (cdr pathname))))
       ((unless (atom (cdr pathname)))
        (mv (make-abs-file) *enotdir*)))
    (mv (cdr alist-elem) 0)))

(defthm
  natp-of-abs-find-file-helper
  (natp (mv-nth 1 (abs-find-file-helper fs pathname)))
  :hints (("goal" :in-theory (enable abs-find-file-helper)))
  :rule-classes :type-prescription)

(defthm abs-find-file-helper-of-fat32-filename-list-fix
  (equal (abs-find-file-helper fs (fat32-filename-list-fix pathname))
         (abs-find-file-helper fs pathname))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defcong
  fat32-filename-list-equiv
  equal (abs-find-file-helper fs pathname)
  2
  :hints
  (("goal"
    :in-theory
    (disable abs-find-file-helper-of-fat32-filename-list-fix)
    :use
    ((:instance abs-find-file-helper-of-fat32-filename-list-fix
                (pathname pathname-equiv))
     abs-find-file-helper-of-fat32-filename-list-fix))))

(defthm abs-find-file-helper-of-abs-fs-fix
  (equal (abs-find-file-helper (abs-fs-fix fs)
                               pathname)
         (abs-find-file-helper fs pathname))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defund
  abs-find-file (frame pathname)
  (declare
   (xargs :guard (and (frame-p frame)
                      (fat32-filename-list-p pathname))))
  (b*
      (((when (atom frame))
        (mv (make-abs-file) *enoent*))
       (pathname (mbe :exec pathname
                      :logic (fat32-filename-list-fix pathname)))
       ((unless (prefixp (frame-val->path (cdar frame))
                         pathname))
        (abs-find-file (cdr frame) pathname))
       ((mv file error-code)
        (abs-find-file-helper
         (frame-val->dir (cdar frame))
         (nthcdr (len (frame-val->path (cdar frame)))
                 pathname)))
       ((when (not (equal error-code *enoent*)))
        (mv file error-code)))
    (abs-find-file (cdr frame) pathname)))

(defthm natp-of-abs-find-file
  (natp (mv-nth 1 (abs-find-file frame pathname)))
  :hints (("goal" :in-theory (enable abs-find-file)))
  :rule-classes :type-prescription)

(encapsulate
  ()

  (local
   (defthmd abs-find-file-of-fat32-filename-list-fix
     (equal (abs-find-file frame
                           (fat32-filename-list-fix pathname))
            (abs-find-file frame pathname))
     :hints (("goal" :in-theory (enable abs-find-file)))))

  (defcong
    fat32-filename-list-equiv
    equal (abs-find-file frame pathname)
    2
    :hints
    (("goal"
      :use ((:instance abs-find-file-of-fat32-filename-list-fix
                       (pathname pathname-equiv))
            abs-find-file-of-fat32-filename-list-fix)))))

(defthm
  abs-find-file-helper-when-m1-file-alist-p-lemma-1
  (implies (and (abs-fs-p fs) (abs-complete fs))
           (equal (hifat-file-alist-fix fs) fs))
  :hints
  (("goal" :in-theory (disable (:rewrite abs-no-dups-p-when-m1-file-alist-p))
    :use ((:rewrite abs-no-dups-p-when-m1-file-alist-p)))))

(defthm
  abs-find-file-helper-when-m1-file-alist-p-lemma-2
  (implies
   (and
    (m1-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car pathname))
                                           fs)))
    (abs-fs-p fs))
   (abs-fs-p
    (m1-file->contents (cdr (assoc-equal (fat32-filename-fix (car pathname))
                                         fs)))))
  :hints
  (("goal"
    :in-theory
    (disable (:rewrite abs-fs-p-of-abs-file->contents-of-cdr-of-assoc))
    :use (:instance (:rewrite abs-fs-p-of-abs-file->contents-of-cdr-of-assoc)
                    (name (fat32-filename-fix (car pathname)))))))

(defthm
  abs-find-file-helper-when-m1-file-alist-p
  (implies (abs-complete (abs-fs-fix fs))
           (equal (abs-find-file-helper fs pathname)
                  (hifat-find-file (abs-fs-fix fs)
                                   pathname)))
  :hints (("goal" :in-theory (enable abs-find-file-helper
                                     hifat-find-file m1-file-alist-p))))

(defthm
  abs-find-file-helper-of-context-apply-lemma-1
  (implies
   (and (abs-fs-p abs-file-alist1)
        (abs-fs-p (append (remove-equal x abs-file-alist1)
                          abs-file-alist2))
        (integerp x)
        (not (equal (mv-nth 1
                            (abs-find-file-helper abs-file-alist1 pathname))
                    *enoent*)))
   (equal (abs-find-file-helper (append (remove-equal x abs-file-alist1)
                                        abs-file-alist2)
                                pathname)
          (abs-find-file-helper abs-file-alist1 pathname)))
  :hints
  (("goal" :do-not-induct t
    :expand (:free (abs-file-alist)
                   (abs-find-file-helper abs-file-alist pathname))
    :cases ((null (car pathname))))))

(defthmd abs-find-file-helper-of-context-apply-lemma-4
  (implies (not (zp (mv-nth 1 (abs-find-file-helper fs pathname))))
           (equal (abs-find-file-helper fs pathname)
                  (mv (abs-file-fix nil)
                      (mv-nth 1 (abs-find-file-helper fs pathname)))))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  abs-find-file-helper-of-context-apply-lemma-6
  (implies
   (and
    (abs-fs-p abs-file-alist2)
    (abs-fs-p abs-file-alist1)
    (integerp x)
    (not (intersectp-equal (remove-equal nil (strip-cars abs-file-alist1))
                           (remove-equal nil (strip-cars abs-file-alist2))))
    (equal (mv-nth 1
                   (abs-find-file-helper abs-file-alist1 pathname))
           2))
   (equal (abs-find-file-helper (append (remove-equal x abs-file-alist1)
                                        abs-file-alist2)
                                pathname)
          (abs-find-file-helper abs-file-alist2 pathname)))
  :hints
  (("goal"
    :do-not-induct t
    :use
    (:instance (:rewrite abs-find-file-helper-of-context-apply-lemma-4)
               (pathname (cdr pathname))
               (fs (abs-file->contents
                    (cdr (assoc-equal (fat32-filename-fix (car pathname))
                                      abs-file-alist1)))))
    :expand ((:free (abs-file-alist)
                    (abs-find-file-helper abs-file-alist pathname))
             (:with (:rewrite assoc-equal-of-append-1)
                    (assoc-equal (fat32-filename-fix (car pathname))
                                 (append (remove-equal x abs-file-alist1)
                                         abs-file-alist2)))))))

(defthm
  abs-find-file-helper-of-context-apply
  (implies
   (and (not (intersectp-equal
              (names-at abs-file-alist2 nil)
              (names-at abs-file-alist1 x-path)))
        (context-apply-ok abs-file-alist1
                          abs-file-alist2 x x-path)
        (abs-fs-p
         (context-apply abs-file-alist1
                        abs-file-alist2 x x-path)))
   (equal
    (abs-find-file-helper (context-apply abs-file-alist1
                                         abs-file-alist2 x x-path)
                          pathname)
    (cond
     ((and (equal (mv-nth 1
                          (abs-find-file-helper abs-file-alist1 pathname))
                  0)
           (prefixp (fat32-filename-list-fix pathname)
                    (fat32-filename-list-fix x-path)))
      (mv
       (abs-file
        (abs-file->dir-ent
         (mv-nth 0
                 (abs-find-file-helper abs-file-alist1 pathname)))
        (context-apply
         (abs-file->contents
          (mv-nth 0
                  (abs-find-file-helper abs-file-alist1 pathname)))
         abs-file-alist2
         x (nthcdr (len pathname) x-path)))
       0))
     ((and (equal (mv-nth 1
                          (abs-find-file-helper abs-file-alist1 pathname))
                  *enoent*)
           (prefixp (fat32-filename-list-fix x-path)
                    (fat32-filename-list-fix pathname)))
      (abs-find-file-helper abs-file-alist2
                            (nthcdr (len x-path) pathname)))
     (t (abs-find-file-helper abs-file-alist1 pathname)))))
  :hints
  (("goal"
    :in-theory
    (e/d (prefixp abs-find-file-helper context-apply
                  context-apply-ok names-at)
         (nfix (:rewrite abs-addrs-of-context-apply-1-lemma-4)
               (:rewrite remove-when-absent)
               (:rewrite abs-find-file-helper-when-m1-file-alist-p)
               (:rewrite m1-file-contents-p-correctness-1)
               (:rewrite abs-file-contents-p-when-m1-file-contents-p)
               (:rewrite abs-addrs-of-context-apply-3)
               (:rewrite abs-file-alist-p-correctness-1)
               (:definition no-duplicatesp-equal)))
    :induct
    (mv (mv-nth 0
                (abs-find-file-helper (context-apply abs-file-alist1
                                                     abs-file-alist2 x x-path)
                                      pathname))
        (fat32-filename-list-prefixp x-path pathname)
        (context-apply abs-file-alist1
                       abs-file-alist2 x x-path))
    :expand
    (:with (:rewrite assoc-equal-of-append-1)
           (assoc-equal (fat32-filename-fix (car pathname))
                        (append (remove-equal (nfix x)
                                              (abs-fs-fix abs-file-alist1))
                                (abs-fs-fix abs-file-alist2)))))))

(defthm
  abs-find-file-of-remove-assoc-1
  (implies
   (and
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (or
     (not (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                   (fat32-filename-list-fix pathname)))
     (equal
      (mv-nth 1
              (abs-find-file-helper
               (frame-val->dir (cdr (assoc-equal x frame)))
               (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                       pathname)))
      *enoent*)))
   (equal (abs-find-file (remove-assoc-equal x frame)
                         pathname)
          (abs-find-file frame pathname)))
  :hints (("goal" :in-theory (enable abs-find-file))))

(defthm
  abs-find-file-of-remove-assoc-2
  (implies
   (and
    (frame-p (remove-assoc-equal x frame))
    (no-duplicatesp-equal (strip-cars (remove-assoc-equal x frame)))
    (or
     (not
      (prefixp
       (frame-val->path (cdr (assoc-equal y (remove-assoc-equal x frame))))
       (fat32-filename-list-fix pathname)))
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal y (remove-assoc-equal x frame))))
        (nthcdr (len (frame-val->path
                      (cdr (assoc-equal y (remove-assoc-equal x frame)))))
                pathname)))
      *enoent*)))
   (equal (abs-find-file (remove-assoc-equal x (remove-assoc-equal y frame))
                         pathname)
          (abs-find-file (remove-assoc-equal x frame)
                         pathname)))
  :hints (("goal" :in-theory (disable abs-find-file-of-remove-assoc-1)
           :use (:instance abs-find-file-of-remove-assoc-1 (x y)
                           (frame (remove-assoc-equal x frame))))))

(defthmd abs-find-file-of-put-assoc-lemma-1
  (equal (abs-find-file-helper fs pathname)
         (mv (mv-nth 0 (abs-find-file-helper fs pathname))
             (mv-nth 1 (abs-find-file-helper fs pathname))))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  abs-find-file-of-put-assoc-lemma-2
  (equal
   (list (mv-nth 0
                 (abs-find-file-helper (frame-val->dir val)
                                       (nthcdr (len (frame-val->path val))
                                               pathname)))
         (mv-nth 1
                 (abs-find-file-helper (frame-val->dir val)
                                       (nthcdr (len (frame-val->path val))
                                               pathname))))
   (abs-find-file-helper (frame-val->dir val)
                         (nthcdr (len (frame-val->path val))
                                 pathname)))
  :hints
  (("goal" :use (:instance (:rewrite abs-find-file-of-put-assoc-lemma-1)
                           (pathname (nthcdr (len (frame-val->path val))
                                             pathname))
                           (fs (frame-val->dir val))))))

(defthm
  abs-find-file-of-put-assoc-lemma-3
  (implies
   (and
    (equal
     (mv-nth
      1
      (abs-find-file-helper (frame-val->dir val)
                            (nthcdr (len (frame-val->path val))
                                    pathname)))
     2)
    (equal const (mv (abs-file-fix nil) *enoent*)))
   (iff
    (equal
     const
     (abs-find-file-helper (frame-val->dir val)
                           (nthcdr (len (frame-val->path val))
                                   pathname)))
    t))
  :hints
  (("goal"
    :use
    (:instance (:rewrite abs-find-file-helper-of-context-apply-lemma-4)
               (pathname (nthcdr (len (frame-val->path val))
                                 pathname))
               (fs (frame-val->dir val))))))

(defthmd
  abs-find-file-of-put-assoc-lemma-4
  (implies (not (zp (mv-nth 1 (abs-find-file frame pathname))))
           (equal (abs-find-file frame pathname)
                  (mv (abs-file-fix nil)
                      (mv-nth 1 (abs-find-file frame pathname)))))
  :hints
  (("goal" :in-theory (enable abs-find-file))
   ("subgoal *1/2"
    :use
    (:instance (:rewrite abs-find-file-helper-of-context-apply-lemma-4)
               (pathname (nthcdr (len (frame-val->path (cdr (car frame))))
                                 pathname))
               (fs (frame-val->dir (cdr (car frame))))))))

(defthm
  abs-find-file-of-put-assoc-lemma-5
  (implies (and (equal (mv-nth 1 (abs-find-file (cdr frame) pathname))
                       2)
                (equal const (mv (abs-file-fix nil) *enoent*)))
           (iff (equal (abs-find-file (cdr frame) pathname)
                       const)
                t))
  :hints
  (("goal" :use (:instance (:rewrite abs-find-file-of-put-assoc-lemma-4)
                           (frame (cdr frame))))))

;; Could be important...
(defthm
  abs-find-file-of-put-assoc-lemma-6
  (implies
   (and (frame-p frame)
        (no-duplicatesp-equal (strip-cars frame))
        (consp (assoc-equal x frame))
        (equal (mv-nth 1
                       (abs-find-file (remove-assoc-equal x frame)
                                      pathname))
               *enoent*))
   (equal (abs-find-file frame pathname)
          (if (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                       (fat32-filename-list-fix pathname))
              (abs-find-file-helper
               (frame-val->dir (cdr (assoc-equal x frame)))
               (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                       pathname))
            (mv (abs-file-fix nil) *enoent*))))
  :hints (("goal" :in-theory (enable abs-find-file))))

(defthm
  abs-find-file-of-put-assoc-1
  (implies
   (and (frame-p (put-assoc-equal name val frame))
        (no-duplicatesp-equal (strip-cars (put-assoc-equal name val frame)))
        (case-split
         (equal (mv-nth 1
                        (abs-find-file (remove-assoc-equal name frame)
                                       pathname))
                *enoent*)))
   (equal (abs-find-file (put-assoc-equal name val frame)
                         pathname)
          (if (prefixp (frame-val->path val) (fat32-filename-list-fix pathname))
              (abs-find-file-helper (frame-val->dir val)
                                    (nthcdr (len (frame-val->path val))
                                            pathname))
            (mv (abs-file-fix nil) *enoent*))))
  :hints (("goal" :in-theory (disable abs-find-file-of-put-assoc-lemma-6)
           :use (:instance abs-find-file-of-put-assoc-lemma-6
                           (frame (put-assoc-equal name val frame))
                           (x name)))))

(defthm
  abs-find-file-of-put-assoc-lemma-9
  (implies (and (frame-p (cdr frame))
                (not (member-equal (car (car frame))
                                   (strip-cars (cdr frame)))))
           (equal (abs-find-file (remove-assoc-equal (car (car frame))
                                                     (cdr frame))
                                 pathname)
                  (abs-find-file (cdr frame) pathname)))
  :hints (("goal" :in-theory (disable (:rewrite remove-assoc-when-absent))
           :use (:instance (:rewrite remove-assoc-when-absent)
                           (alist (cdr frame))
                           (x (car (car frame)))))))

(defthm
  abs-find-file-of-put-assoc-2
  (implies
   (and
    (frame-p (put-assoc-equal name val frame))
    (no-duplicatesp-equal
     (strip-cars (put-assoc-equal name val frame)))
    (not
     (equal
      (mv-nth 1
              (abs-find-file (remove-assoc-equal name frame)
                             pathname))
      2))
    (case-split
     (or
      (not (prefixp (frame-val->path val)
                    (fat32-filename-list-fix pathname)))
      (equal
       (mv-nth 1
               (abs-find-file-helper (frame-val->dir val)
                                     (nthcdr (len (frame-val->path val))
                                             pathname)))
       *enoent*))))
   (equal (abs-find-file (put-assoc-equal name val frame)
                         pathname)
          (abs-find-file (remove-assoc-equal name frame)
                         pathname)))
  :hints
  (("goal" :in-theory (enable abs-find-file))))

(defthm
  abs-find-file-of-frame-with-root
  (equal (abs-find-file (frame-with-root root frame)
                        pathname)
         (if (equal (mv-nth 1
                            (abs-find-file-helper (abs-fs-fix root)
                                                  pathname))
                    *enoent*)
             (abs-find-file frame pathname)
           (abs-find-file-helper (abs-fs-fix root)
                                 pathname)))
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (abs-find-file frame-with-root)
                    ((:rewrite abs-find-file-of-put-assoc-lemma-1)))
    :use (:instance (:rewrite abs-find-file-of-put-assoc-lemma-1)
                    (fs (abs-fs-fix root))))))

(defund abs-find-file-alt
  (frame indices pathname)
  (b* (((when (atom indices))
        (mv (make-abs-file) *enoent*))
       (pathname (fat32-filename-list-fix pathname))
       ((unless (prefixp (frame-val->path (cdr (assoc-equal (car indices) frame)))
                         pathname))
        (abs-find-file-alt frame (cdr indices) pathname))
       ((mv file error-code)
        (abs-find-file-helper
         (frame-val->dir (cdr (assoc-equal (car indices) frame)))
         (nthcdr (len (frame-val->path (cdr (assoc-equal (car indices) frame))))
                 pathname)))
       ((when (not (equal error-code *enoent*)))
        (mv file error-code)))
    (abs-find-file-alt frame (cdr indices) pathname)))

(defthm abs-find-file-alt-of-fat32-filename-list-fix
  (equal (abs-find-file-alt frame indices
                            (fat32-filename-list-fix pathname))
         (abs-find-file-alt frame indices pathname))
  :hints (("goal" :in-theory (enable abs-find-file-alt))))

(defcong
  fat32-filename-list-equiv equal
  (abs-find-file-alt frame indices pathname)
  3
  :hints
  (("goal"
    :in-theory
    (disable abs-find-file-alt-of-fat32-filename-list-fix)
    :use
    ((:instance abs-find-file-alt-of-fat32-filename-list-fix
                (pathname pathname-equiv))
     abs-find-file-alt-of-fat32-filename-list-fix))))

(defthm abs-find-file-alt-correctness-1-lemma-1
  (implies (not (member-equal (caar frame) indices))
           (equal (abs-find-file-alt (cdr frame)
                                     indices pathname)
                  (abs-find-file-alt frame indices pathname)))
  :hints (("goal" :in-theory (enable abs-find-file-alt))))

(defthm
  abs-find-file-alt-correctness-1
  (implies (no-duplicatesp-equal (strip-cars frame))
           (equal (abs-find-file-alt frame (strip-cars frame)
                                     pathname)
                  (abs-find-file frame pathname)))
  :hints (("goal" :in-theory (enable abs-find-file-alt abs-find-file))))

(defthm
  abs-find-file-alt-correctness-2
  (implies (no-duplicatesp-equal (strip-cars frame))
           (equal (abs-find-file-alt frame
                                     (remove-equal x (strip-cars frame))
                                     pathname)
                  (abs-find-file (remove-assoc-equal x frame)
                                 pathname)))
  :hints (("goal" :in-theory (enable abs-find-file-alt abs-find-file))))

(defund abs-enotdir-witness (fs pathname)
  (declare (xargs :measure (len pathname)))
  (b* (((when (atom pathname)) pathname)
       ((mv file errno)
        (abs-find-file-helper fs pathname))
       ((when (and (zp errno) (m1-regular-file-p file))) pathname))
    (abs-enotdir-witness fs (butlast pathname 1))))

(defthm true-listp-of-abs-enotdir-witness
  (implies (true-listp pathname)
           (true-listp (abs-enotdir-witness fs pathname)))
  :hints (("Goal" :in-theory (enable abs-enotdir-witness)))
  :rule-classes :type-prescription)

(defthm prefixp-of-abs-enotdir-witness
  (prefixp (abs-enotdir-witness fs pathname)
           pathname)
  :hints (("goal" :in-theory (enable abs-enotdir-witness))))

(defthm len-of-abs-enotdir-witness
  (<= (len (abs-enotdir-witness fs pathname))
      (len pathname))
  :hints (("goal" :in-theory (enable abs-enotdir-witness)))
  :rule-classes :linear)

(defthm
  abs-enotdir-witness-correctness-1-lemma-1
  (implies
   (< 1 (len pathname))
   (not (equal (abs-enotdir-witness fs
                                    (take (+ -1 (len pathname)) pathname))
               pathname)))
  :hints (("goal" :use (:instance len-of-abs-enotdir-witness
                                  (pathname (take (+ -1 (len pathname))
                                                  pathname))))))

(defthm
  abs-enotdir-witness-correctness-1
  (implies (equal (mv-nth 1 (abs-find-file-helper fs pathname))
                  *enotdir*)
           (not (equal (abs-enotdir-witness fs pathname)
                       pathname)))
  :hints (("goal" :in-theory (enable abs-enotdir-witness
                                     abs-find-file-helper))))

(defthm
  abs-enotdir-witness-correctness-2-lemma-1
  (implies
   (and
    (not
     (equal
      (mv-nth 1
              (abs-find-file-helper fs
                                    (take (+ -1 (len pathname)) pathname)))
      *enotdir*))
    (equal (mv-nth 1 (abs-find-file-helper fs pathname))
           *enotdir*))
   (and
    (m1-regular-file-p
     (mv-nth 0
             (abs-find-file-helper fs
                                   (take (+ -1 (len pathname)) pathname))))
    (equal
     (mv-nth 1
             (abs-find-file-helper fs
                                   (take (+ -1 (len pathname)) pathname)))
     0)))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  abs-enotdir-witness-correctness-2
  (implies
   (equal (mv-nth 1 (abs-find-file-helper fs pathname))
          *enotdir*)
   (and
    (m1-regular-file-p
     (mv-nth 0
             (abs-find-file-helper fs (abs-enotdir-witness fs pathname))))
    (equal
     (mv-nth 1
             (abs-find-file-helper fs (abs-enotdir-witness fs pathname)))
     0)
    (consp (abs-enotdir-witness fs pathname))))
  :hints (("goal" :in-theory (enable abs-enotdir-witness
                                     abs-find-file-helper))))

(defthm fat32-filename-list-p-of-abs-enotdir-witness
  (implies
   (fat32-filename-list-p pathname)
   (fat32-filename-list-p (abs-enotdir-witness fs pathname)))
  :hints (("goal" :in-theory (enable abs-enotdir-witness))))

(defthm
  abs-find-file-helper-of-collapse-lemma-1
  (implies (m1-regular-file-p (mv-nth 0 (abs-find-file-helper root pathname)))
           (not (equal (mv-nth 1 (abs-find-file-helper root pathname))
                       2)))
  :hints
  (("goal"
    :use (:instance (:rewrite abs-find-file-helper-of-context-apply-lemma-4)
                    (fs root)))))

;; Important!
;; It's a pain in the neck that we have to stipulate x-path has at least one
;; element in it... but it's unavoidable. This is really a fundamental
;; difference between abs-find-file-helper and context-apply.
(defthm
  abs-find-file-helper-of-collapse-lemma-2
  (implies (and (consp x-path)
                (context-apply-ok abs-file-alist1
                                  abs-file-alist2 x x-path))
           (and (equal (mv-nth 1
                               (abs-find-file-helper abs-file-alist1 x-path))
                       0)
                (abs-directory-file-p
                 (mv-nth 0
                         (abs-find-file-helper abs-file-alist1 x-path)))))
  :hints
  (("goal"
    :in-theory (e/d (abs-find-file-helper context-apply context-apply-ok)
                    (nfix))
    :induct (abs-find-file-helper abs-file-alist1 x-path))
   ("subgoal *1/2" :expand (context-apply abs-file-alist1
                                          abs-file-alist2 x x-path))))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies
      (and (consp pathname)
           (prefixp pathname x-path)
           (zp (mv-nth 1 (abs-find-file-helper fs x-path)))
           (fat32-filename-list-p x-path)
           (fat32-filename-list-p pathname))
      (and (equal (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs
                                                                        pathname)))
                  (or
                   (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs
                                                                         x-path)))
                   (not (equal pathname x-path))))
           (equal (mv-nth 1 (abs-find-file-helper fs pathname))
                  0)))
     :hints (("goal" :in-theory (enable abs-find-file-helper prefixp)
              :induct t
              :expand (abs-find-file-helper fs x-path)))))

  ;; Important theorem about prefixp and abs-find-file.
  (defthmd
    abs-find-file-helper-of-collapse-lemma-4
    (implies
     (and (consp pathname)
          (prefixp (fat32-filename-list-fix pathname)
                   (fat32-filename-list-fix x-path))
          (zp (mv-nth 1 (abs-find-file-helper fs x-path))))
     (and
      (equal
       (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs pathname)))
       (or (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs x-path)))
           (not (fat32-filename-list-equiv pathname x-path))))
      (equal (mv-nth 1 (abs-find-file-helper fs pathname))
             0)))
    :hints
    (("goal" :use (:instance lemma
                             (x-path (fat32-filename-list-fix x-path))
                             (pathname (fat32-filename-list-fix pathname)))))))

(defthm
  abs-find-file-helper-of-collapse-lemma-5
  (implies
   (and
    (context-apply-ok root
                      (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      (1st-complete frame)
                      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                         frame))))
    (abs-file-alist-p root)
    (prefixp (fat32-filename-list-fix pathname)
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))))
   (not (m1-regular-file-p (mv-nth 0
                                   (abs-find-file-helper root pathname)))))
  :hints
  (("goal"
    :in-theory (e/d (abs-find-file-helper)
                    ((:rewrite abs-find-file-helper-of-collapse-lemma-2)))
    :use
    ((:instance
      (:rewrite abs-find-file-helper-of-collapse-lemma-2)
      (x (1st-complete frame))
      (abs-file-alist2 (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                         frame))))
      (x-path (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                 frame))))
      (abs-file-alist1 root))
     (:instance
      (:rewrite abs-find-file-helper-of-collapse-lemma-4)
      (x-path (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                 frame))))
      (fs root))))))

(defthm
  abs-find-file-helper-of-collapse-lemma-6
  (implies
   (and
    (not (equal (1st-complete-src frame)
                (1st-complete frame)))
    (consp (assoc-equal (1st-complete-src frame)
                        frame))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                frame)))
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame))))
    (dist-names root nil frame)
    (abs-fs-p
     (context-apply
      (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                        frame)))
      (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                        frame)))
      (1st-complete frame)
      (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                      frame))))
              (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                 frame)))))))
   (dist-names
    root nil
    (put-assoc-equal
     (1st-complete-src frame)
     (frame-val
      (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                         frame)))
      (context-apply
       (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                         frame)))
       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                         frame)))
       (1st-complete frame)
       (nthcdr
        (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                frame))))
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame)))))
      (frame-val->src (cdr (assoc-equal (1st-complete-src frame)
                                        frame))))
     (remove-assoc-equal (1st-complete frame)
                         frame))))
  :hints
  (("goal" :in-theory (e/d (1st-complete-src)
                           ((:rewrite abs-separate-correctness-1-lemma-18)))
    :use (:instance (:rewrite abs-separate-correctness-1-lemma-18)
                    (x (1st-complete frame))))))

(defthm
  abs-find-file-helper-of-collapse-1
  (implies
   (and (frame-p (frame->frame frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (abs-separate (frame->frame frame))
        (dist-names (frame->root frame)
                    nil (frame->frame frame))
        (m1-regular-file-p (mv-nth 0
                                   (abs-find-file-helper (frame->root frame)
                                                         pathname))))
   (equal (abs-find-file-helper (mv-nth 0 (collapse frame))
                                pathname)
          (abs-find-file-helper (frame->root frame)
                                pathname)))
  :hints
  (("goal" :in-theory (enable collapse dist-names)
    :induct (collapse frame))
   ("subgoal *1/4"
    :use (:instance (:rewrite abs-find-file-helper-of-context-apply-lemma-4)
                    (fs (frame->root frame)))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (frame-p (frame->frame frame))
          (no-duplicatesp-equal (strip-cars (frame->frame frame)))
          (abs-separate (frame->frame frame))
          (dist-names (frame->root frame)
                      nil (frame->frame frame))
          (m1-regular-file-p (mv-nth 0
                                     (abs-find-file-helper (frame->root frame)
                                                           pathname)))
          (m1-file-alist-p (mv-nth 0 (collapse frame)))
          (hifat-no-dups-p (mv-nth 0 (collapse frame))))
     (equal (hifat-find-file (mv-nth 0 (collapse frame))
                             pathname)
            (abs-find-file-helper (frame->root frame)
                                  pathname))))))

(defthm
  abs-find-file-helper-of-collapse-2
  (implies (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (frame-p (frame->frame frame))
                (abs-separate (frame->frame frame))
                (dist-names (frame->root frame)
                            nil (frame->frame frame))
                (not (equal (mv-nth 1
                                    (abs-find-file-helper (frame->root frame)
                                                          pathname))
                            0))
                (not (equal (mv-nth 1
                                    (abs-find-file-helper (frame->root frame)
                                                          pathname))
                            *enoent*)))
           (equal (abs-find-file-helper (mv-nth 0 (collapse frame))
                                        pathname)
                  (abs-find-file-helper (frame->root frame)
                                        pathname)))
  :hints (("goal" :in-theory (enable collapse dist-names)
           :induct (collapse frame))))

;; The somewhat weaker conclusion, in terms of (mv-nth 1 (abs-find-file ...))
;; rather than (abs-find-file ...), is because of the possibility that the file
;; returned is a directory with holes, which gets filled in during collapse.
(defthm
  abs-find-file-helper-of-collapse-3
  (implies (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (frame-p (frame->frame frame))
                (abs-separate (frame->frame frame))
                (dist-names (frame->root frame)
                            nil (frame->frame frame))
                (not (equal (mv-nth 1
                                    (abs-find-file-helper (frame->root frame)
                                                          pathname))
                            *enoent*)))
           (equal (mv-nth 1
                          (abs-find-file-helper (mv-nth 0 (collapse frame))
                                                pathname))
                  (mv-nth 1
                          (abs-find-file-helper (frame->root frame)
                                                pathname))))
  :hints (("goal" :in-theory (enable collapse dist-names)
           :induct (collapse frame)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
          (frame-p (frame->frame frame))
          (abs-separate (frame->frame frame))
          (dist-names (frame->root frame)
                      nil (frame->frame frame))
          (not (equal (mv-nth 1
                              (abs-find-file-helper (frame->root frame)
                                                    pathname))
                      *enoent*))
          (m1-file-alist-p (mv-nth 0 (collapse frame)))
          (hifat-no-dups-p (mv-nth 0 (collapse frame))))
     (equal (mv-nth 1
                    (hifat-find-file (mv-nth 0 (collapse frame))
                                     pathname))
            (mv-nth 1
                    (abs-find-file-helper (frame->root frame)
                                          pathname)))))))

(defthm
  abs-find-file-correctness-1-lemma-1
  (implies
   (and (not (consp (abs-addrs (abs-fs-fix root))))
        (m1-regular-file-p (mv-nth 0
                                   (abs-find-file (frame-with-root root nil)
                                                  pathname))))
   (equal (mv-nth 0
                  (abs-find-file (frame-with-root root nil)
                                 pathname))
          (mv-nth 0
                  (hifat-find-file (abs-fs-fix root)
                                   pathname))))
  :hints (("goal" :in-theory (enable frame-with-root
                                     abs-find-file abs-separate))))

(defthmd
  abs-find-file-correctness-1-lemma-2
  (implies
   (and
    (not (intersectp-equal
          (abs-addrs (cdr abs-file-alist))
          (abs-addrs (abs-file->contents (cdr (car abs-file-alist))))))
    (member-equal x (abs-addrs (cdr abs-file-alist))))
   (not (member-equal
         x
         (abs-addrs (abs-file->contents (cdr (car abs-file-alist)))))))
  :hints (("goal" :in-theory (enable intersectp-member))))

;; It seems this is useless...
(defthmd
  abs-find-file-correctness-1-lemma-4
  (implies
   (and (abs-directory-file-p val)
        (abs-directory-file-p (cdr (assoc-equal name abs-file-alist)))
        (no-duplicatesp-equal (abs-addrs abs-file-alist)))
   (iff
    (member-equal x
                  (abs-addrs (put-assoc-equal name val abs-file-alist)))
    (or
     (member-equal x (abs-addrs (abs-file->contents val)))
     (and
      (member-equal x (abs-addrs abs-file-alist))
      (not
       (member-equal
        x
        (abs-addrs
         (abs-file->contents (cdr (assoc-equal name abs-file-alist))))))))))
  :hints (("goal" :induct (put-assoc-equal name val abs-file-alist)
           :in-theory (enable abs-addrs))))

(defthm
  abs-find-file-correctness-1-lemma-28
  (implies
   (and
    (equal
     (mv-nth 1
             (abs-find-file-helper (context-apply abs-file-alist1
                                                  abs-file-alist2 x x-path)
                                   pathname))
     *enoent*)
    (prefixp (fat32-filename-list-fix x-path)
             (fat32-filename-list-fix pathname))
    (context-apply-ok abs-file-alist1
                      abs-file-alist2 x x-path)
    (not (intersectp-equal (names-at abs-file-alist2 nil)
                           (names-at abs-file-alist1 x-path))))
   (and (equal (mv-nth 1
                       (abs-find-file-helper abs-file-alist1 pathname))
               *enoent*)
        (equal (mv-nth 1
                       (abs-find-file-helper abs-file-alist2
                                             (nthcdr (len x-path) pathname)))
               *enoent*))))

;; Should the corollary be a type-prescription?
(defthm
  abs-find-file-correctness-1-lemma-13
  (implies
   (and
    (not (consp (assoc-equal (fat32-filename-fix (car pathname))
                             abs-file-alist1)))
    (abs-fs-p (append (remove-equal x abs-file-alist1)
                      abs-file-alist2))
    (abs-fs-p abs-file-alist2)
    (equal
     (mv-nth 1
             (abs-find-file-helper (append (remove-equal x abs-file-alist1)
                                           abs-file-alist2)
                                   pathname))
     0))
   (equal (mv-nth 1
                  (abs-find-file-helper abs-file-alist2 pathname))
          0))
  :hints
  (("goal"
    :do-not-induct t
    :expand ((abs-find-file-helper abs-file-alist2 pathname)
             (abs-find-file-helper (append (remove-equal x abs-file-alist1)
                                           abs-file-alist2)
                                   pathname)
             (:with (:rewrite assoc-equal-of-append-1)
                    (assoc-equal (fat32-filename-fix (car pathname))
                                 (append (remove-equal x abs-file-alist1)
                                         abs-file-alist2))))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (not (consp (assoc-equal (fat32-filename-fix (car pathname))
                                   abs-file-alist1)))
          (abs-fs-p (append (remove-equal x abs-file-alist1)
                            abs-file-alist2))
          (abs-fs-p abs-file-alist2)
          (not (equal (mv-nth 1
                              (abs-find-file-helper abs-file-alist2 pathname))
                      0)))
     (not
      (equal
       (mv-nth 1
               (abs-find-file-helper (append (remove-equal x abs-file-alist1)
                                             abs-file-alist2)
                                     pathname))
       0))))))

(defthm
  abs-find-file-correctness-1-lemma-8
  (implies
   (and
    (abs-directory-file-p
     (cdr (assoc-equal (fat32-filename-fix (car pathname))
                       (abs-fs-fix abs-file-alist1))))
    (abs-fs-p (append (remove-equal x abs-file-alist1)
                      abs-file-alist2))
    (abs-fs-p abs-file-alist1)
    (integerp x)
    (equal
     (mv-nth 1
             (abs-find-file-helper abs-file-alist1 pathname))
     *enoent*))
   (equal (mv-nth 1
                  (abs-find-file-helper
                   (append (remove-equal x abs-file-alist1)
                           abs-file-alist2)
                   pathname))
          *enoent*))
  :hints
  (("goal"
    :do-not-induct t
    :expand
    ((abs-find-file-helper abs-file-alist1 pathname)
     (abs-find-file-helper
      (append (remove-equal x abs-file-alist1)
              abs-file-alist2)
      pathname)
     (:with
      (:rewrite assoc-equal-of-append-1)
      (assoc-equal (fat32-filename-fix (car pathname))
                   (append (remove-equal x abs-file-alist1)
                           abs-file-alist2)))))))

(defthm abs-find-file-correctness-1-lemma-6
  (implies (and (fat32-filename-list-p pathname)
                (< n (len pathname))
                (zp (mv-nth 1
                            (abs-find-file-helper (abs-fs-fix fs)
                                                  pathname))))
           (member-equal (nth n pathname)
                         (names-at fs (take n pathname))))
  :hints (("goal" :in-theory (enable names-at
                                     abs-find-file-helper))))

(defthm
  abs-find-file-correctness-1-lemma-9
  (implies
   (and
    (not (prefixp (fat32-filename-list-fix relpath)
                  (frame-val->path (cdr (assoc-equal x frame)))))
    (prefixp (fat32-filename-list-fix relpath)
             (fat32-filename-list-fix pathname))
    (equal (mv-nth 1
                   (abs-find-file-helper (abs-fs-fix dir)
                                         (nthcdr (len relpath) pathname)))
           0)
    (equal
     (mv-nth 1
             (abs-find-file-helper
              (frame-val->dir (cdr (assoc-equal x frame)))
              (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                      pathname)))
     0)
    (prefixp (frame-val->path (cdr (assoc-equal x frame)))
             (fat32-filename-list-fix pathname)))
   (intersectp-equal
    (names-at dir nil)
    (names-at
     (frame-val->dir (cdr (assoc-equal x frame)))
     (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
             relpath))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (names-at abs-find-file-helper take-of-nthcdr)
                    (abs-find-file-correctness-1-lemma-6
                     nth-of-fat32-filename-list-fix
                     (:rewrite member-of-remove)
                     (:rewrite car-of-nthcdr)
                     (:rewrite nth-of-nthcdr)
                     (:rewrite take-when-prefixp)))
    :use
    ((:instance
      (:rewrite intersectp-member)
      (y (names-at
          (frame-val->dir (cdr (assoc-equal x frame)))
          (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                  relpath)))
      (x (names-at dir nil))
      (a (nth (len relpath)
              (fat32-filename-list-fix pathname))))
     (:instance abs-find-file-correctness-1-lemma-6
                (fs (abs-fs-fix dir))
                (pathname (nthcdr (len relpath)
                                  (fat32-filename-list-fix pathname)))
                (n 0))
     (:instance
      abs-find-file-correctness-1-lemma-6
      (fs (frame-val->dir (cdr (assoc-equal x frame))))
      (pathname (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                        (fat32-filename-list-fix pathname)))
      (n (+ (len relpath)
            (- (len (frame-val->path (cdr (assoc-equal x frame))))))))
     (:instance abs-separate-of-put-assoc-lemma-2
                (src x)
                (relpath (fat32-filename-list-fix relpath)))
     (:instance (:rewrite car-of-nthcdr)
                (x (fat32-filename-list-fix pathname))
                (i (len relpath)))
     (:instance
      (:rewrite nth-of-nthcdr)
      (x (fat32-filename-list-fix pathname))
      (m (len (frame-val->path (cdr (assoc-equal x frame)))))
      (n (+ (len relpath)
            (- (len (frame-val->path (cdr (assoc-equal x frame))))))))
     (:instance (:rewrite take-when-prefixp)
                (y (fat32-filename-list-fix pathname))
                (x (fat32-filename-list-fix relpath)))))))

(defthm
  abs-find-file-correctness-1-lemma-33
  (implies (and (abs-fs-p fs)
                (fat32-filename-list-p pathname)
                (not (equal (mv-nth 1 (abs-find-file-helper fs pathname))
                            *enoent*)))
           (member-equal (car pathname)
                         (remove-equal nil (strip-cars fs))))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  abs-find-file-correctness-1-lemma-37
  (implies
   (and (abs-fs-p fs)
        (fat32-filename-list-p pathname)
        (not (equal (mv-nth 1
                            (abs-find-file-helper fs (nthcdr n pathname)))
                    *enoent*)))
   (member-equal (nth n pathname)
                 (remove-equal nil (strip-cars fs))))
  :hints (("goal" :do-not-induct t
           :in-theory (disable abs-find-file-correctness-1-lemma-33
                               nth-of-nthcdr)
           :use ((:instance abs-find-file-correctness-1-lemma-33
                            (pathname (nthcdr n pathname)))
                 (:instance nth-of-nthcdr (n 0)
                            (m n)
                            (x pathname))))))

(defthmd
  abs-find-file-correctness-1-lemma-20
  (implies (and (< (+ (- (len relpath))
                      (len (frame-val->path (cdr (assoc-equal x frame)))))
                   0)
                (prefixp relpath pathname)
                (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                         pathname))
           (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                    relpath))
  :hints
  (("goal"
    :in-theory
    (e/d (names-at take-of-nthcdr abs-find-file-helper)
         (abs-find-file-correctness-1-lemma-6 member-of-remove))
    :cases ((prefixp relpath
                     (frame-val->path (cdr (assoc-equal x frame))))))))

(defthm
  abs-find-file-correctness-1-lemma-21
  (implies
   (and
    (not (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                  (fat32-filename-list-fix relpath)))
    (prefixp (fat32-filename-list-fix relpath)
             (fat32-filename-list-fix pathname))
    (equal (mv-nth 1
                   (abs-find-file-helper dir (nthcdr (len relpath) pathname)))
           0)
    (equal
     (mv-nth 1
             (abs-find-file-helper
              (frame-val->dir (cdr (assoc-equal x frame)))
              (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                      pathname)))
     0)
    (prefixp (frame-val->path (cdr (assoc-equal x frame)))
             (fat32-filename-list-fix pathname)))
   (intersectp-equal
    (names-at (frame-val->dir (cdr (assoc-equal x frame)))
              nil)
    (names-at
     dir
     (nthcdr (len relpath)
             (frame-val->path (cdr (assoc-equal x frame)))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (names-at take-of-nthcdr abs-find-file-helper
                              abs-find-file-correctness-1-lemma-20)
                    (abs-find-file-correctness-1-lemma-6
                     member-of-remove
                     (:rewrite nth-of-fat32-filename-list-fix)
                     (:rewrite take-when-prefixp)
                     (:rewrite nth-of-nthcdr)))
    :use
    ((:instance
      abs-find-file-correctness-1-lemma-6
      (fs (frame-val->dir (cdr (assoc-equal x frame))))
      (pathname (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                        (fat32-filename-list-fix pathname)))
      (n 0))
     (:instance abs-find-file-correctness-1-lemma-6
                (fs (abs-fs-fix dir))
                (pathname (nthcdr (len relpath)
                                  (fat32-filename-list-fix pathname)))
                (n (+ (len (frame-val->path (cdr (assoc-equal x frame))))
                      (- (len relpath)))))
     (:theorem (equal (+ (len relpath)
                         (- (len relpath))
                         (len (frame-val->path (cdr (assoc-equal x frame)))))
                      (len (frame-val->path (cdr (assoc-equal x frame))))))
     (:instance
      intersectp-member
      (a (nth (len (frame-val->path (cdr (assoc-equal x frame))))
              (fat32-filename-list-fix pathname)))
      (y (names-at
          dir
          (nthcdr (len relpath)
                  (frame-val->path (cdr (assoc-equal x frame))))))
      (x (remove-equal
          nil
          (strip-cars (frame-val->dir (cdr (assoc-equal x frame)))))))
     (:instance (:rewrite nth-of-nthcdr)
                (x (fat32-filename-list-fix pathname))
                (m (len relpath))
                (n (+ (- (len relpath))
                      (len (frame-val->path (cdr (assoc-equal x frame)))))))
     (:instance (:rewrite take-when-prefixp)
                (y (fat32-filename-list-fix pathname))
                (x (frame-val->path (cdr (assoc-equal x frame)))))))))

(defthmd
  abs-find-file-correctness-1-lemma-29
  (implies
   (and
    (not (intersectp-equal
          (names-at (frame-val->dir (cdr (assoc-equal x frame)))
                    nil)
          (names-at
           dir
           (nthcdr (len relpath)
                   (frame-val->path (cdr (assoc-equal x frame)))))))
    (prefixp (fat32-filename-list-fix relpath)
             (fat32-filename-list-fix pathname))
    (equal (mv-nth 1
                   (abs-find-file-helper (abs-fs-fix dir)
                                         (nthcdr (len relpath) pathname)))
           0)
    (equal
     (mv-nth 1
             (abs-find-file-helper
              (frame-val->dir (cdr (assoc-equal x frame)))
              (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                      pathname)))
     0)
    (prefixp (frame-val->path (cdr (assoc-equal x frame)))
             (fat32-filename-list-fix pathname)))
   (intersectp-equal
    (names-at dir nil)
    (names-at
     (frame-val->dir (cdr (assoc-equal x frame)))
     (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
             relpath))))
  :hints
  (("goal"
    :do-not-induct t
    :cases ((and (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                          (fat32-filename-list-fix relpath))
                 (prefixp (fat32-filename-list-fix relpath)
                          (frame-val->path (cdr (assoc-equal x frame))))))
    :in-theory
    (e/d (list-equiv nthcdr-when->=-n-len-l)
         (nth-of-fat32-filename-list-fix (:rewrite prefixp-when-equal-lengths)
                                         member-of-remove))
    :use
    ((:instance (:rewrite prefixp-when-equal-lengths)
                (y (frame-val->path (cdr (assoc-equal x frame))))
                (x (fat32-filename-list-fix relpath)))
     (:instance
      (:rewrite intersectp-member)
      (a (nth (len (frame-val->path (cdr (assoc-equal x frame))))
              (fat32-filename-list-fix pathname)))
      (y (names-at
          dir
          (nthcdr (len relpath)
                  (frame-val->path (cdr (assoc-equal x frame))))))
      (x (names-at (frame-val->dir (cdr (assoc-equal x frame)))
                   nil)))))
   ("subgoal 1.2"
    :expand (names-at (frame-val->dir (cdr (assoc-equal x frame)))
                      nil))
   ("subgoal 1.1" :expand (names-at dir nil))))

;; This theorem is kinda inadequate. It would be better to prove that the
;; subterm of the LHS, which is proved to be non-zero, is actually
;; *enoent*. But that's not possible, because proving that it cannot be
;; *ENOTDIR* (necessary) can't be done without the additional knowledge of
;; collapsibility...
(defthm
  abs-find-file-correctness-1-lemma-22
  (implies
   (and
    (equal (mv-nth 1
                   (abs-find-file-helper dir (nthcdr (len relpath) pathname)))
           0)
    (dist-names dir
                relpath frame)
    (consp (assoc-equal x frame))
    (prefixp (fat32-filename-list-fix relpath)
             (fat32-filename-list-fix pathname))
    (prefixp (frame-val->path (cdr (assoc-equal x frame)))
             (fat32-filename-list-fix pathname)))
   (not
    (equal
     (mv-nth 1
             (abs-find-file-helper
              (frame-val->dir (cdr (assoc-equal x frame)))
              (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                      pathname)))
     0)))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d
                       (abs-find-file-correctness-1-lemma-29)
                       (abs-separate-correctness-1-lemma-19
                        abs-separate-of-put-assoc-lemma-3))
           :use ((:instance abs-separate-correctness-1-lemma-19
                            (dir (abs-fs-fix dir)))
                 (:instance abs-separate-of-put-assoc-lemma-3
                            (dir (abs-fs-fix dir))))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (equal (mv-nth 1
                     (abs-find-file-helper dir (nthcdr (len relpath) pathname)))
             0)
      (dist-names dir
                  relpath frame)
      (consp (assoc-equal x frame))
      (prefixp (fat32-filename-list-fix relpath)
               (fat32-filename-list-fix pathname))
      (prefixp (frame-val->path (cdr (assoc-equal x frame)))
               (fat32-filename-list-fix pathname))
      (equal (mv-nth 1 mv) 0))
     (not
      (equal
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal x frame)))
        (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                pathname))
       mv))))))

(defthm
  abs-find-file-correctness-1-lemma-24
  (implies
   (equal
    (mv-nth
     1
     (abs-find-file-helper (frame-val->dir (cdr (car frame)))
                           (nthcdr (len (frame-val->path (cdr (car frame))))
                                   pathname)))
    0)
   (equal
    (cons
     (mv-nth
      0
      (abs-find-file-helper (frame-val->dir (cdr (car frame)))
                            (nthcdr (len (frame-val->path (cdr (car frame))))
                                    pathname)))
     '(0))
    (abs-find-file-helper (frame-val->dir (cdr (car frame)))
                          (nthcdr (len (frame-val->path (cdr (car frame))))
                                  pathname))))
  :instructions (:promote (:dive 2)
                          (:rewrite abs-find-file-of-put-assoc-lemma-1)
                          :top (:dive 2 2 1)
                          :=
                          :top :s))

(defthmd
  abs-find-file-correctness-1-lemma-59
  (implies
   (and
    (consp (assoc-equal x frame))
    (equal (mv-nth 1 (abs-find-file frame pathname))
           0)
    (equal
     (mv-nth 1
             (abs-find-file-helper
              (frame-val->dir (cdr (assoc-equal x frame)))
              (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                      pathname)))
     0)
    (abs-separate frame)
    (prefixp (frame-val->path (cdr (assoc-equal x frame)))
             (fat32-filename-list-fix pathname)))
   (equal (abs-find-file-helper
           (frame-val->dir (cdr (assoc-equal x frame)))
           (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                   pathname))
          (abs-find-file frame pathname)))
  :hints (("goal" :in-theory (enable abs-find-file abs-separate)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (consp (assoc-equal x frame))
      (equal (mv-nth 1 (abs-find-file frame pathname))
             0)
      (equal
       (mv-nth
        1
        (hifat-find-file
         (frame-val->dir (cdr (assoc-equal x frame)))
         (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                 pathname)))
       0)
      (abs-separate frame)
      (prefixp (frame-val->path (cdr (assoc-equal x frame)))
               (fat32-filename-list-fix pathname))
      (m1-file-alist-p (frame-val->dir (cdr (assoc-equal x frame))))
      (hifat-no-dups-p (frame-val->dir (cdr (assoc-equal x frame)))))
     (equal (hifat-find-file
             (frame-val->dir (cdr (assoc-equal x frame)))
             (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                     pathname))
            (abs-find-file frame pathname))))))

(defthm
  abs-find-file-correctness-1-lemma-5
  (implies
   (and
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))
             (fat32-filename-list-fix pathname))
    (< 0 (1st-complete frame))
    (context-apply-ok root
                      (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      (1st-complete frame)
                      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                         frame))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (dist-names root nil frame)
    (equal
     (mv-nth
      1
      (abs-find-file-helper
       (context-apply root
                      (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      (1st-complete frame)
                      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                         frame))))
       pathname))
     2))
   (equal
    (mv-nth
     1
     (hifat-find-file
      (frame-val->dir$inline (cdr (assoc-equal (1st-complete frame)
                                               frame)))
      (nthcdr
       (len (frame-val->path$inline (cdr (assoc-equal (1st-complete frame)
                                                      frame))))
       pathname)))
    *enoent*))
  :hints (("goal" :do-not-induct t)))

(defthm
  abs-find-file-correctness-1-lemma-14
  (implies
   (and
    (equal (mv-nth 1
                   (abs-find-file (frame-with-root root frame)
                                  pathname))
           0)
    (< 0 (1st-complete frame))
    (context-apply-ok root
                      (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      (1st-complete frame)
                      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                         frame))))
    (equal
     (mv-nth
      1
      (abs-find-file
       (frame-with-root
        (context-apply root
                       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       (1st-complete frame)
                       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                          frame))))
        (remove-assoc-equal (1st-complete frame)
                            frame))
       pathname))
     0)
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-file-alist-p root)
    (abs-separate (frame-with-root root frame))
    (m1-regular-file-p (mv-nth 0
                               (abs-find-file (frame-with-root root frame)
                                              pathname))))
   (equal
    (mv-nth
     0
     (abs-find-file
      (frame-with-root
       (context-apply root
                      (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      (1st-complete frame)
                      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                         frame))))
       (remove-assoc-equal (1st-complete frame)
                           frame))
      pathname))
    (mv-nth 0
            (abs-find-file (frame-with-root root frame)
                           pathname))))
  :hints (("goal" :in-theory (enable abs-find-file
                                     (:rewrite abs-find-file-correctness-1-lemma-59
                                               . 2)
                                     frame-with-root abs-separate)
           :do-not-induct t)))

;; Kinda general
(defthm
  abs-find-file-correctness-1-lemma-40
  (implies
   (and (not (equal (mv-nth 1 (hifat-find-file fs pathname))
                    0))
        (not (equal (mv-nth 1 (hifat-find-file fs pathname))
                    *enoent*)))
   (equal (mv-nth 1 (hifat-find-file fs pathname))
          *enotdir*))
  :hints (("goal" :in-theory (enable hifat-find-file)))
  :rule-classes
  (:rewrite
   (:type-prescription
    :corollary
    (natp (mv-nth 1 (hifat-find-file fs pathname))))))

;; Kinda general
(defthm
  abs-find-file-correctness-1-lemma-18
  (implies
   (and (not (equal (mv-nth 1 (abs-find-file-helper fs pathname))
                    0))
        (not (equal (mv-nth 1 (abs-find-file-helper fs pathname))
                    *enoent*)))
   (equal (mv-nth 1 (abs-find-file-helper fs pathname))
          *enotdir*))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  abs-find-file-correctness-1-lemma-23
  (implies
   (and (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                    frame)))
                 (fat32-filename-list-fix pathname))
        (equal (mv-nth 1 (abs-find-file-helper root pathname))
               0)
        (dist-names root nil frame))
   (equal
    (mv-nth
     1
     (abs-find-file-helper
      (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                        frame)))
      (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                      frame))))
              pathname)))
    *enoent*))
  :hints
  (("goal"
    :in-theory (e/d (abs-find-file-helper)
                    (abs-find-file-correctness-1-lemma-6
                     (:rewrite abs-find-file-correctness-1-lemma-18)))
    :do-not-induct t
    :cases
    ((equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                        frame))))
                pathname)))
      0)
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                        frame))))
                pathname)))
      *enotdir*))
    :use
    ((:instance
      (:rewrite intersectp-member)
      (a
       (fat32-filename-fix
        (car
         (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                         frame))))
                 pathname))))
      (y (names-at
          (abs-fs-fix root)
          (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                             frame)))))
      (x (names-at
          (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame)))
          nil)))
     (:instance
      abs-find-file-correctness-1-lemma-6
      (fs (abs-fs-fix root))
      (n (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                 frame)))))
      (pathname (fat32-filename-list-fix pathname)))
     (:instance
      (:rewrite abs-find-file-correctness-1-lemma-18)
      (pathname
       (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                       frame))))
               pathname))
      (fs (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame))))))
    :expand
    (abs-find-file-helper
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                     frame))))
             pathname)))
   ("subgoal 2.2"
    :expand
    (names-at (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                frame)))
              nil))
   ("subgoal 2.1"
    :expand
    (names-at (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                frame)))
              nil))
   ("subgoal 1.2"
    :expand
    (names-at (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                frame)))
              nil))
   ("subgoal 1.1"
    :expand
    (names-at (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                frame)))
              nil))))

(defthm
  abs-find-file-correctness-1-lemma-30
  (implies
   (and (fat32-filename-list-p pathname2)
        (zp (mv-nth 1 (abs-find-file-helper fs pathname1)))
        (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs pathname1)))
        (equal (mv-nth 1 (abs-find-file-helper fs pathname2))
               *enotdir*)
        (prefixp pathname1 pathname2))
   (member-equal (nth (len pathname1) pathname2)
                 (names-at fs pathname1)))
  :hints (("goal" :in-theory (enable abs-find-file-helper
                                     names-at prefixp)
           :induct t
           :expand (names-at fs pathname1))))

(defthm
  abs-find-file-correctness-1-lemma-25
  (implies (and (fat32-filename-list-p pathname)
                (not (equal (mv-nth 1
                                    (abs-find-file-helper (abs-fs-fix fs)
                                                          pathname))
                            *enoent*)))
           (member-equal (car pathname)
                         (names-at fs nil)))
  :hints (("goal" :in-theory (e/d (names-at)
                                  (abs-find-file-correctness-1-lemma-33))
           :use (:instance abs-find-file-correctness-1-lemma-33
                           (fs (abs-fs-fix fs))))))

(defthmd
  abs-find-file-correctness-1-lemma-26
  (implies
   (and (fat32-filename-list-p pathname)
        (not (equal (mv-nth 1
                            (abs-find-file-helper (abs-fs-fix fs)
                                                  (nthcdr n pathname)))
                    *enoent*)))
   (member-equal (nth n pathname)
                 (names-at fs nil)))
  :hints (("goal" :in-theory (e/d (names-at)
                                  (abs-find-file-correctness-1-lemma-37))
           :use (:instance abs-find-file-correctness-1-lemma-37
                           (fs (abs-fs-fix fs))))))

(encapsulate
  ()

  (local
   (defthm
     lemma
     (implies
      (and
       (member-equal (car (fat32-filename-list-fix pathname))
                     (names-at root nil))
       (not (equal (mv-nth 1 (abs-find-file-helper root pathname))
                   0))
       (context-apply-ok root
                         (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                           frame)))
                         (1st-complete frame)
                         (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                            frame))))
       (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                (fat32-filename-list-fix pathname))
       (not (equal (mv-nth 1 (abs-find-file-helper root pathname))
                   2)))
      (member-equal
       (nth (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                    frame))))
            (fat32-filename-list-fix pathname))
       (names-at root
                 (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                    frame))))))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory (e/d (names-at abs-find-file-helper)
                       (nthcdr-of-fat32-filename-list-fix
                        nth-of-fat32-filename-list-fix
                        (:rewrite abs-find-file-correctness-1-lemma-33)))
       :cases ((consp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                         frame)))))))))

  (defthm
    abs-find-file-correctness-1-lemma-7
    (implies
     (and
      (context-apply-ok root
                        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        (1st-complete frame)
                        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                           frame))))
      (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                  frame)))
               (fat32-filename-list-fix pathname))
      (not (equal (mv-nth 1 (abs-find-file-helper (abs-fs-fix root) pathname))
                  2))
      (dist-names root nil frame))
     (equal
      (abs-find-file-helper
       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                         frame)))
       (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                       frame))))
               pathname))
      (mv (abs-file-fix nil) *enoent*)))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (e/d (abs-find-file-helper)
                      (nthcdr-of-fat32-filename-list-fix
                       nth-of-fat32-filename-list-fix
                       (:rewrite abs-find-file-correctness-1-lemma-25)))
      :use
      ((:instance
        (:rewrite abs-find-file-correctness-1-lemma-25)
        (fs (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                              frame))))
        (pathname
         (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                         frame))))
                 (fat32-filename-list-fix pathname))))
       (:instance (:rewrite abs-find-file-correctness-1-lemma-25)
                  (fs (abs-fs-fix root))
                  (pathname (fat32-filename-list-fix pathname)))
       (:instance
        (:rewrite intersectp-member)
        (a
         (car
          (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                          frame))))
                  (fat32-filename-list-fix pathname))))
        (y (names-at
            root
            (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                               frame)))))
        (x
         (names-at (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                     frame)))
                   nil))))
      :cases
      ((and
        (not
         (equal
          (mv-nth
           1
           (abs-find-file-helper
            (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                              frame)))
            (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                            frame))))
                    pathname)))
          2))
        (abs-file-alist-p (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                            frame))))
        (equal (mv-nth 1 (abs-find-file-helper root pathname))
               0))
       (and
        (not
         (equal
          (mv-nth
           1
           (abs-find-file-helper
            (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                              frame)))
            (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                            frame))))
                    pathname)))
          2))
        (abs-file-alist-p (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                            frame))))
        (not (equal (mv-nth 1 (abs-find-file-helper root pathname))
                    0))))))))

(defthm
  abs-find-file-correctness-1-lemma-49
  (implies
   (and
    (context-apply-ok
     root
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (1st-complete frame)
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame))))
    (prefixp
     (frame-val->path (cdr (assoc-equal x frame)))
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame))))
    (abs-file-alist-p root))
   (abs-directory-file-p
    (mv-nth
     0
     (abs-find-file-helper root
                           (frame-val->path (cdr (assoc-equal x frame)))))))
  :hints
  (("goal"
    :in-theory (e/d (abs-find-file-helper)
                    ((:rewrite abs-find-file-helper-of-collapse-lemma-2)
                     (:rewrite abs-find-file-helper-of-collapse-lemma-4)))
    :use
    ((:instance
      (:rewrite abs-find-file-helper-of-collapse-lemma-4)
      (pathname (frame-val->path (cdr (assoc-equal x frame))))
      (fs root)
      (x-path
       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                          frame)))))
     (:instance
      (:rewrite abs-find-file-helper-of-collapse-lemma-2)
      (x (1st-complete frame))
      (abs-file-alist2
       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                         frame))))
      (x-path
       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                          frame))))
      (abs-file-alist1 root))))))

(defthm
  abs-find-file-correctness-1-lemma-16
  (implies
   (not (equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                 frame)))
               (1st-complete-src frame)))
   (equal
    (abs-find-file-helper
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                     frame))))
             pathname))
    (mv (abs-file-fix nil) *enoent*)))
  :hints (("goal" :in-theory (enable 1st-complete-src))))

(defthm
  abs-find-file-correctness-1-lemma-34
  (implies
   (and
    (abs-file-alist-p root)
    (context-apply-ok
     root
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (1st-complete frame)
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame)))))
   (abs-directory-file-p
    (mv-nth
     0
     (abs-find-file-helper
      root
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame)))))))
  :hints
  (("goal"
    :in-theory (e/d (abs-find-file-helper)
                    ((:rewrite abs-find-file-helper-of-collapse-lemma-2)))
    :use
    ((:instance
      (:rewrite abs-find-file-helper-of-collapse-lemma-2)
      (x-path
       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                          frame))))
      (abs-file-alist1 root)
      (x (1st-complete frame))
      (abs-file-alist2
       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                         frame)))))))))

(defthmd
  abs-find-file-correctness-1-lemma-11
  (implies
   (and (prefixp (fat32-filename-list-fix pathname)
                 (fat32-filename-list-fix x-path))
        (m1-regular-file-p (mv-nth 0 (abs-find-file-helper fs pathname)))
        (not (fat32-filename-list-equiv pathname x-path)))
   (equal (abs-find-file-helper fs x-path)
          (mv (abs-file-fix nil) *enotdir*)))
  :hints
  (("goal" :in-theory (enable fat32-filename-list-equiv
                              abs-find-file-helper
                              prefixp fat32-filename-list-fix)
    :induct (mv (mv-nth 0 (abs-find-file-helper fs pathname))
                (fat32-filename-list-prefixp pathname x-path)))))

(defthm
  abs-find-file-correctness-1-lemma-12
  (implies
   (and (equal (mv-nth 1 (abs-find-file frame pathname))
               *enoent*)
        (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                 (fat32-filename-list-fix pathname)))
   (equal (abs-find-file-helper
           (frame-val->dir (cdr (assoc-equal x frame)))
           (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                   pathname))
          (mv (abs-file-fix nil) *enoent*)))
  :hints (("goal" :in-theory (enable abs-find-file hifat-find-file))))

(defthm
  abs-find-file-correctness-1-lemma-3
  (implies
   (and
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (consp (assoc-equal (1st-complete frame)
                        frame))
    (equal
     (mv-nth
      1
      (abs-find-file
       (remove-assoc-equal (1st-complete frame)
                           frame)
       pathname))
     2))
   (equal
    (abs-find-file frame pathname)
    (if
        (prefixp
         (frame-val->path
          (cdr (assoc-equal (1st-complete frame)
                            frame)))
         (fat32-filename-list-fix pathname))
        (abs-find-file-helper
         (frame-val->dir
          (cdr (assoc-equal (1st-complete frame)
                            frame)))
         (nthcdr
          (len
           (frame-val->path
            (cdr (assoc-equal (1st-complete frame)
                              frame))))
          pathname))
      (mv (abs-file-fix nil) *enoent*))))
  :hints
  (("goal"
    :in-theory (disable abs-find-file-of-put-assoc-lemma-6)
    :use (:instance abs-find-file-of-put-assoc-lemma-6
                    (x (1st-complete frame))))))

(defthm
  abs-find-file-correctness-1-lemma-19
  (implies
   (and
    (fat32-filename-list-p pathname)
    (equal
     (mv-nth
      1
      (abs-find-file-helper
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame)))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame))))))
     0)
    (abs-directory-file-p
     (mv-nth
      0
      (abs-find-file-helper
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame)))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame)))))))
    (equal
     (mv-nth
      1
      (abs-find-file-helper
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame)))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        pathname)))
     20))
   (not
    (prefixp
     (abs-enotdir-witness
      (frame-val->dir
       (cdr
        (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                       frame)))
                     frame)))
      (nthcdr
       (len
        (frame-val->path
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame))))
       pathname))
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame)))))))
  :hints
  (("goal"
    :do-not-induct t
    :use
    (:instance
     abs-find-file-helper-of-collapse-lemma-4
     (pathname
      (abs-enotdir-witness
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame)))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        pathname)))
     (fs
      (frame-val->dir
       (cdr
        (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                       frame)))
                     frame))))
     (x-path
      (nthcdr
       (len
        (frame-val->path
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame))))
       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                          frame)))))))))

(defthm
  abs-find-file-correctness-1-lemma-57
  (implies
   (and
    (fat32-filename-list-p pathname)
    (equal
     (mv-nth
      1
      (abs-find-file-helper
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame)))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        pathname)))
     *enotdir*)
    (context-apply-ok
     (frame-val->dir
      (cdr
       (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                      frame)))
                    frame)))
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (1st-complete frame)
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame))))))
   (not
    (prefixp
     (abs-enotdir-witness
      (frame-val->dir
       (cdr
        (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                       frame)))
                     frame)))
      (nthcdr
       (len
        (frame-val->path
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame))))
       pathname))
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame)))))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (disable abs-find-file-helper-of-collapse-lemma-2)
    :use
    (:instance
     abs-find-file-helper-of-collapse-lemma-2
     (x-path
      (nthcdr
       (len
        (frame-val->path
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame))))
       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                          frame)))))
     (x (1st-complete frame))
     (abs-file-alist2 (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                        frame))))
     (abs-file-alist1
      (frame-val->dir
       (cdr
        (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                       frame)))
                     frame))))))))

(defthmd
  abs-separate-correctness-1-lemma-41
  (implies
   (and
    (fat32-filename-list-p pathname)
    (equal
     (mv-nth
      1
      (abs-find-file-helper
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame)))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        pathname)))
     *enotdir*)
    (prefixp
     (frame-val->path
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame))))
    (prefixp
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame))))
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (fat32-filename-list-fix pathname)))
    (not
     (prefixp
      (abs-enotdir-witness
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame)))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        (fat32-filename-list-fix pathname)))
      (nthcdr
       (len
        (frame-val->path
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame))))
       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                          frame)))))))
   (member-equal
    (fat32-filename-fix
     (nth (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                  frame))))
          pathname))
    (names-at
     (frame-val->dir
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame)))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (disable nth-when-prefixp
             (:rewrite abs-find-file-correctness-1-lemma-6)
             (:rewrite take-when-prefixp)
             prefixp-one-way-or-another
             (:rewrite abs-find-file-correctness-1-lemma-57))
    :use
    ((:instance
      nth-when-prefixp
      (y
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        (fat32-filename-list-fix pathname)))
      (n
       (+
        (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame))))
        (-
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 frame)))))))
      (x
       (abs-enotdir-witness
        (frame-val->dir
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame)))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 frame))))
         pathname))))
     (:instance
      (:rewrite abs-find-file-correctness-1-lemma-6)
      (fs
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (pathname
       (abs-enotdir-witness
        (frame-val->dir
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame)))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 frame))))
         pathname)))
      (n
       (+
        (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame))))
        (-
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 frame))))))))
     (:instance
      (:rewrite take-when-prefixp)
      (y
       (abs-enotdir-witness
        (frame-val->dir
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame)))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 frame))))
         (fat32-filename-list-fix pathname))))
      (x
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame))))))
     (:instance
      prefixp-one-way-or-another
      (z
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        (fat32-filename-list-fix pathname)))
      (x
       (abs-enotdir-witness
        (frame-val->dir
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame)))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 frame))))
         (fat32-filename-list-fix pathname))))
      (y
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame))))))))))

(defthmd
  abs-find-file-correctness-1-lemma-55
  (implies
   (and
    (not
     (member-equal
      (fat32-filename-fix
       (nth (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                    frame))))
            pathname))
      (names-at
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame)))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame)))))))
    (<
     0
     (mv-nth
      1
      (abs-find-file-helper
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame)))
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        pathname))))
    (prefixp
     (frame-val->path
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame))))
    (context-apply-ok
     (frame-val->dir
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (1st-complete frame)
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame)))))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))
             (fat32-filename-list-fix pathname)))
   (equal
    (abs-find-file-helper
     (frame-val->dir
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      pathname))
    (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (take-of-nthcdr abs-find-file-helper)
                    (nthcdr-of-fat32-filename-list-fix
                     abs-separate-correctness-1-lemma-14
                     (:rewrite abs-find-file-correctness-1-lemma-18)
                     (:rewrite abs-find-file-correctness-1-lemma-57)))
    :use
    ((:instance
      (:rewrite abs-find-file-correctness-1-lemma-18)
      (pathname
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        pathname))
      (fs
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame)))))
     (:instance (:rewrite abs-separate-correctness-1-lemma-41)
                (pathname (fat32-filename-list-fix pathname)))
     (:instance (:rewrite abs-find-file-correctness-1-lemma-57)
                (pathname (fat32-filename-list-fix pathname)))))))

(defthm
  abs-find-file-correctness-1-lemma-27
  (implies
   (and
    (not (equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                  frame)))
                (1st-complete frame)))
    (prefixp
     (frame-val->path
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame))))
    (context-apply-ok
     (frame-val->dir
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (1st-complete frame)
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame)))))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))
             (fat32-filename-list-fix pathname))
    (abs-separate frame)
    (not
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                        frame))))
                pathname)))
      *enoent*)))
   (equal
    (abs-find-file-helper
     (frame-val->dir
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      pathname))
    (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d (take-of-nthcdr abs-find-file-helper)
         (nthcdr-of-fat32-filename-list-fix
          abs-separate-correctness-1-lemma-14
          (:rewrite abs-find-file-correctness-1-lemma-6)))
    :use
    ((:instance abs-separate-correctness-1-lemma-14
                (x (1st-complete frame))
                (y (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                     frame)))))
     (:instance
      (:rewrite intersectp-member)
      (a
       (car
        (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                        frame))))
                (fat32-filename-list-fix pathname))))
      (y
       (names-at
        (frame-val->dir
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame)))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 frame))))
         (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                            frame))))))
      (x (names-at
          (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame)))
          nil)))
     (:instance
      (:rewrite abs-find-file-correctness-1-lemma-6)
      (fs
       (frame-val->dir
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (pathname
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame))))
        (fat32-filename-list-fix pathname)))
      (n
       (+
        (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame))))
        (-
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 frame))))))))
     (:instance
      (:rewrite abs-find-file-correctness-1-lemma-26)
      (fs (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame))))
      (pathname (fat32-filename-list-fix pathname))
      (n (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                 frame))))))
     (:instance (:rewrite abs-find-file-correctness-1-lemma-55)
                (pathname (fat32-filename-list-fix pathname)))))))

(defthm
  abs-find-file-correctness-1-lemma-46
  (implies
   (and
    (not (equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                  frame)))
                (1st-complete frame)))
    (prefixp
     (frame-val->path
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame))))
    (context-apply-ok
     (frame-val->dir
      (cdr
       (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                      frame)))
                    frame)))
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (1st-complete frame)
     (nthcdr
      (len
       (frame-val->path
        (cdr
         (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame)))))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))
             (fat32-filename-list-fix pathname))
    (abs-separate frame)
    (not
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       frame)))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 frame))))
         pathname)))
      *enoent*)))
   (equal
    (abs-find-file-helper
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                     frame))))
             pathname))
    (mv (abs-file-fix nil) *enoent*)))
  :hints (("goal" :in-theory (disable abs-find-file-correctness-1-lemma-27)
           :use abs-find-file-correctness-1-lemma-27)))

(defthm abs-find-file-correctness-1-lemma-44
  (implies (and (mv-nth 1 (collapse frame))
                (consp (assoc-equal y (frame->frame frame))))
           (< '0
              (1st-complete (frame->frame frame))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable collapse)))
  :rule-classes (:linear :rewrite))

(defthm
  abs-find-file-correctness-1-lemma-45
  (implies
   (and
    (mv-nth 1 (collapse frame))
    (equal
     (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     0)
    (consp (assoc-equal y (frame->frame frame))))
   (context-apply-ok
    (frame->root frame)
    (frame-val->dir$inline
     (cdr (assoc-equal (1st-complete (frame->frame frame))
                       (frame->frame frame))))
    (1st-complete (frame->frame frame))
    (frame-val->path$inline
     (cdr (assoc-equal (1st-complete (frame->frame frame))
                       (frame->frame frame))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (enable collapse 1st-complete-src))))

(defthmd abs-find-file-correctness-1-lemma-31
  (equal (hifat-find-file fs pathname)
         (mv (mv-nth 0 (hifat-find-file fs pathname))
             (mv-nth 1 (hifat-find-file fs pathname))))
  :hints (("goal" :in-theory (enable hifat-find-file))))

(defthm
  abs-find-file-correctness-1-lemma-51
  (implies
   (and
    (not (equal (1st-complete-src frame)
                (1st-complete frame)))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                frame)))
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame))))
    (context-apply-ok
     (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                       frame)))
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (1st-complete frame)
     (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                     frame))))
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))
             (fat32-filename-list-fix pathname))
    (abs-separate frame)
    (not
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                          frame)))
        (nthcdr
         (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                 frame))))
         pathname)))
      *enoent*)))
   (equal
    (abs-find-file-helper
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                     frame))))
             pathname))
    (mv (abs-file-fix nil) *enoent*)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable 1st-complete-src))))

(defthm
  abs-find-file-correctness-1-lemma-39
  (implies
   (and
    (not (equal (1st-complete-src frame)
                (1st-complete frame)))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                frame)))
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame))))
    (context-apply-ok
     (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                       frame)))
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (1st-complete frame)
     (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                     frame))))
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))
             (fat32-filename-list-fix pathname))
    (abs-separate frame)
    (not
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                        frame))))
                pathname)))
      *enoent*)))
   (equal
    (abs-find-file-helper
     (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                       frame)))
     (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                     frame))))
             pathname))
    (mv (abs-file-fix nil) *enoent*)))
  :hints (("goal" :in-theory (enable 1st-complete-src))))

(defthm
  abs-find-file-correctness-1-lemma-17
  (implies (and (mv-nth 1 (collapse frame))
                (consp (assoc-equal y (frame->frame frame))))
           (consp (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame))))
  :hints
  (("goal"
    :in-theory (disable (:type-prescription 1st-complete-correctness-1))
    :use (:instance (:type-prescription 1st-complete-correctness-1)
                    (frame (frame->frame frame)))))
  :rule-classes :type-prescription)

(defthm
  abs-find-file-correctness-1-lemma-43
 (implies
  (and
   (< 0 (1st-complete-src frame))
   (context-apply-ok
    (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                      frame)))
    (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                      frame)))
    (1st-complete frame)
    (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                    frame))))
            (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                               frame)))))
   (frame-p frame)
   (no-duplicatesp-equal (strip-cars frame)))
  (not (equal (1st-complete-src frame)
              (1st-complete frame)))))

(defthm
  abs-find-file-correctness-1-lemma-42
  (implies
   (and
    (context-apply-ok
     (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                       frame)))
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (1st-complete frame)
     (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                     frame))))
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                frame)))
             (fat32-filename-list-fix pathname))
    (prefixp (fat32-filename-list-fix pathname)
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))))
   (not
    (m1-regular-file-p
     (mv-nth
      0
      (abs-find-file-helper
       (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                         frame)))
       (nthcdr
        (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                frame))))
        pathname))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (abs-find-file-helper)
                    (abs-find-file-helper-of-collapse-lemma-2
                     (:rewrite abs-find-file-of-put-assoc-lemma-6)))
    :use
    ((:instance
      abs-find-file-helper-of-collapse-lemma-2
      (abs-file-alist1
       (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                         frame))))
      (abs-file-alist2 (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                         frame))))
      (x (1st-complete frame))
      (x-path
       (nthcdr
        (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                frame))))
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame))))))
     (:instance
      abs-find-file-correctness-1-lemma-11
      (fs (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                            frame))))
      (pathname
       (nthcdr
        (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                frame))))
        pathname))
      (x-path
       (nthcdr
        (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                frame))))
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame))))))
     (:instance (:rewrite abs-find-file-of-put-assoc-lemma-6)
                (x (1st-complete-src frame)))
     (:instance (:rewrite abs-find-file-of-put-assoc-lemma-6)
                (x (1st-complete frame))
                (frame (remove-assoc-equal (1st-complete-src frame)
                                           frame)))))))

(defthm
  abs-find-file-correctness-1-lemma-53
  (implies
   (and (< 0 (1st-complete-src frame))
        (member-equal (1st-complete frame)
                      (abs-addrs root))
        (no-duplicatesp-equal (strip-cars frame))
        (subsetp-equal (abs-addrs root)
                       (frame-addrs-root frame)))
   (equal
    (mv-nth
     0
     (abs-find-file
      (put-assoc-equal
       (1st-complete-src frame)
       (frame-val
        (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                           frame)))
        (context-apply
         (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                           frame)))
         (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                           frame)))
         (1st-complete frame)
         (nthcdr
          (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                  frame))))
          (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                             frame)))))
        (frame-val->src (cdr (assoc-equal (1st-complete-src frame)
                                          frame))))
       (remove-assoc-equal (1st-complete frame)
                           frame))
      pathname))
    (mv-nth
     0
     (hifat-find-file
      (mv-nth
       0
       (collapse
        (frame-with-root
         root
         (put-assoc-equal
          (1st-complete-src frame)
          (frame-val
           (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                              frame)))
           (context-apply
            (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                              frame)))
            (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                              frame)))
            (1st-complete frame)
            (nthcdr
             (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                     frame))))
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))))
           (frame-val->src (cdr (assoc-equal (1st-complete-src frame)
                                             frame))))
          (remove-assoc-equal (1st-complete frame)
                              frame)))))
      pathname))))
  :hints (("goal" :in-theory (enable 1st-complete-src))))

(defthm
  abs-find-file-correctness-1-lemma-54
  (implies (equal (mv-nth 1
                          (hifat-find-file (frame->root frame)
                                           pathname))
                  0)
           (equal (cons (mv-nth 0
                                (hifat-find-file (frame->root frame)
                                                 pathname))
                        '(0))
                  (hifat-find-file (frame->root frame)
                                   pathname)))
  :instructions (:promote (:dive 2)
                          (:rewrite abs-find-file-correctness-1-lemma-31)
                          :top :s))

(defthm
  abs-find-file-correctness-1-lemma-56
  (implies (equal (mv-nth 1
                          (abs-find-file-helper (frame->root frame)
                                                pathname))
                  0)
           (equal (cons (mv-nth 0
                                (abs-find-file-helper (frame->root frame)
                                                      pathname))
                        '(0))
                  (abs-find-file-helper (frame->root frame)
                                        pathname)))
  :instructions (:promote (:dive 2)
                          (:rewrite abs-find-file-of-put-assoc-lemma-1)
                          :top :bash))

(defthm
  abs-find-file-correctness-1-lemma-58
  (implies (and (< 0
                   (1st-complete-src (frame->frame frame)))
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (subsetp-equal (abs-addrs (frame->root frame))
                               (frame-addrs-root (frame->frame frame))))
           (not (member-equal (1st-complete (frame->frame frame))
                              (abs-addrs (frame->root frame)))))
  :hints (("goal" :in-theory (enable 1st-complete-src))))

(encapsulate
  ()

  (local
   (defun
       induction-scheme (frame pathname x)
     (declare (xargs :measure (len (frame->frame frame))))
     (cond
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (not (zp (1st-complete-src (frame->frame frame))))
        (not
         (or
          (equal (1st-complete-src (frame->frame frame))
                 (1st-complete (frame->frame frame)))
          (atom
           (assoc-equal (1st-complete-src (frame->frame frame))
                        (remove-assoc-equal
                         (1st-complete (frame->frame frame))
                         (frame->frame frame))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal (1st-complete-src (frame->frame frame))
                        (remove-assoc-equal
                         (1st-complete (frame->frame frame))
                         (frame->frame frame)))))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
        (context-apply-ok
         (frame-val->dir
          (cdr
           (assoc-equal (1st-complete-src (frame->frame frame))
                        (remove-assoc-equal
                         (1st-complete (frame->frame frame))
                         (frame->frame frame)))))
         (frame-val->dir
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr (assoc-equal
                  (1st-complete-src (frame->frame frame))
                  (remove-assoc-equal
                   (1st-complete (frame->frame frame))
                   (frame->frame frame))))))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (equal x (1st-complete (frame->frame frame))))
       (induction-scheme
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (1st-complete-src (frame->frame frame))
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal (1st-complete-src (frame->frame frame))
                          (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr (assoc-equal
                   (1st-complete-src (frame->frame frame))
                   (remove-assoc-equal
                    (1st-complete (frame->frame frame))
                    (frame->frame frame)))))
            (frame-val->dir
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (1st-complete (frame->frame frame))
            (nthcdr
             (len
              (frame-val->path
               (cdr (assoc-equal
                     (1st-complete-src (frame->frame frame))
                     (remove-assoc-equal
                      (1st-complete (frame->frame frame))
                      (frame->frame frame))))))
             (frame-val->path
              (cdr
               (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal (1st-complete-src (frame->frame frame))
                          (frame->frame frame)))))
          (remove-assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
        pathname
        (frame-val->src
         (cdr (assoc-equal x (frame->frame frame))))))
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (not (zp (1st-complete-src (frame->frame frame))))
        (not
         (or
          (equal (1st-complete-src (frame->frame frame))
                 (1st-complete (frame->frame frame)))
          (atom
           (assoc-equal (1st-complete-src (frame->frame frame))
                        (remove-assoc-equal
                         (1st-complete (frame->frame frame))
                         (frame->frame frame))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal (1st-complete-src (frame->frame frame))
                        (remove-assoc-equal
                         (1st-complete (frame->frame frame))
                         (frame->frame frame)))))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
        (context-apply-ok
         (frame-val->dir
          (cdr
           (assoc-equal (1st-complete-src (frame->frame frame))
                        (remove-assoc-equal
                         (1st-complete (frame->frame frame))
                         (frame->frame frame)))))
         (frame-val->dir
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr (assoc-equal
                  (1st-complete-src (frame->frame frame))
                  (remove-assoc-equal
                   (1st-complete (frame->frame frame))
                   (frame->frame frame))))))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))))))
       (induction-scheme
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (1st-complete-src (frame->frame frame))
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal (1st-complete-src (frame->frame frame))
                          (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr (assoc-equal
                   (1st-complete-src (frame->frame frame))
                   (remove-assoc-equal
                    (1st-complete (frame->frame frame))
                    (frame->frame frame)))))
            (frame-val->dir
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (1st-complete (frame->frame frame))
            (nthcdr
             (len
              (frame-val->path
               (cdr (assoc-equal
                     (1st-complete-src (frame->frame frame))
                     (remove-assoc-equal
                      (1st-complete (frame->frame frame))
                      (frame->frame frame))))))
             (frame-val->path
              (cdr
               (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal (1st-complete-src (frame->frame frame))
                          (frame->frame frame)))))
          (remove-assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
        pathname x))
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (zp (1st-complete-src (frame->frame frame)))
        (context-apply-ok
         (frame->root frame)
         (frame-val->dir
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))))
       (induction-scheme
        (frame-with-root
         (context-apply
          (frame->root frame)
          (frame-val->dir
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
          (1st-complete (frame->frame frame))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))))
         (remove-assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))
        pathname x))
      (t (mv frame pathname x)))))

  ;; Rather general!
  (defthmd
    abs-find-file-correctness-1-lemma-36
    (implies
     (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
          (frame-p (frame->frame frame))
          (mv-nth 1 (collapse frame))
          (consp (assoc-equal x (frame->frame frame)))
          (prefixp (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
                   (fat32-filename-list-fix pathname))
          (not (equal (mv-nth 1
                              (abs-find-file-helper (frame->root frame)
                                                    pathname))
                      *enoent*))
          (dist-names (frame->root frame)
                      nil (frame->frame frame))
          (abs-separate (frame->frame frame)))
     (equal
      (abs-find-file-helper
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
       (nthcdr
        (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
        pathname))
      (mv (abs-file-fix nil) *enoent*)))
    :hints (("goal" :induct (induction-scheme frame pathname x)
             :in-theory (enable collapse)))))

(defthmd
  abs-find-file-correctness-1-lemma-15
  (implies
   (and
    (no-duplicatesp-equal (strip-cars frame))
    (frame-p frame)
    (context-apply-ok root
                      (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      (1st-complete frame)
                      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                         frame))))
    (mv-nth
     1
     (collapse
      (frame-with-root
       (context-apply root
                      (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                        frame)))
                      (1st-complete frame)
                      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                         frame))))
       (remove-assoc-equal (1st-complete frame)
                           frame))))
    (consp (assoc-equal y frame))
    (not (equal (1st-complete frame) y))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))
             (fat32-filename-list-fix pathname))
    (prefixp (frame-val->path (cdr (assoc-equal y frame)))
             (fat32-filename-list-fix pathname))
    (dist-names root nil frame)
    (abs-separate frame)
    (not
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                        frame))))
                pathname)))
      2)))
   (equal (abs-find-file-helper
           (frame-val->dir (cdr (assoc-equal y frame)))
           (nthcdr (len (frame-val->path (cdr (assoc-equal y frame))))
                   pathname))
          (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :do-not-induct t
    :use
    ((:instance
      (:rewrite abs-find-file-correctness-1-lemma-36)
      (frame
       (frame-with-root
        (context-apply root
                       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       (1st-complete frame)
                       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                          frame))))
        (remove-assoc-equal (1st-complete frame)
                            frame)))
      (x y))))))

(defthm
  abs-find-file-correctness-1-lemma-35
  (implies
   (and
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (mv-nth 1 (collapse frame))
    (equal (1st-complete-src (frame->frame frame))
           0)
    (frame-p (frame->frame frame))
    (consp (assoc-equal y (frame->frame frame)))
    (not (equal (1st-complete (frame->frame frame))
                y))
    (prefixp
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
     (fat32-filename-list-fix pathname))
    (prefixp (frame-val->path (cdr (assoc-equal y (frame->frame frame))))
             (fat32-filename-list-fix pathname))
    (dist-names (frame->root frame)
                nil (frame->frame frame))
    (abs-separate (frame->frame frame))
    (not
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (nthcdr
         (len (frame-val->path
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame)))))
         pathname)))
      2)))
   (equal
    (abs-find-file-helper
     (frame-val->dir (cdr (assoc-equal y (frame->frame frame))))
     (nthcdr
      (len (frame-val->path (cdr (assoc-equal y (frame->frame frame)))))
      pathname))
    (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (collapse 1st-complete-src)
                    ((:type-prescription 1st-complete-correctness-1)))
    :use
    ((:instance
      (:rewrite abs-find-file-correctness-1-lemma-36)
      (frame
       (frame-with-root
        (context-apply
         (frame->root frame)
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
        (remove-assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))
      (x y))
     (:instance (:rewrite abs-find-file-correctness-1-lemma-15)
                (frame (frame->frame frame))
                (root (frame->root frame))
                (y (1st-complete (frame->frame frame))))
     (:instance (:type-prescription 1st-complete-correctness-1)
                (frame (frame->frame frame)))))))

(defthm
  abs-find-file-correctness-1-lemma-38
  (implies
   (and
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (mv-nth 1 (collapse frame))
    (equal (1st-complete-src (frame->frame frame))
           0)
    (frame-p (frame->frame frame))
    (consp (assoc-equal x (frame->frame frame)))
    (not (equal x (1st-complete (frame->frame frame))))
    (prefixp (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
             (fat32-filename-list-fix pathname))
    (prefixp
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
     (fat32-filename-list-fix pathname))
    (dist-names (frame->root frame)
                nil (frame->frame frame))
    (abs-separate (frame->frame frame))
    (not
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
        (nthcdr
         (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
         pathname)))
      2)))
   (equal
    (abs-find-file-helper
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     (nthcdr
      (len
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
      pathname))
    (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :in-theory (enable collapse 1st-complete-src)
    :use
    ((:instance
      (:rewrite abs-find-file-correctness-1-lemma-36)
      (frame
       (frame-with-root
        (context-apply
         (frame->root frame)
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
        (remove-assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
     (:instance
      (:rewrite abs-find-file-helper-of-context-apply-lemma-4)
      (pathname
       (nthcdr (len (frame-val->path
                     (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame)))))
               pathname))
      (fs
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))))))

(encapsulate
  ()

  (local
   (defun induction-scheme (frame x y)
     (declare (xargs :measure (len (frame->frame frame))))
     (cond
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (not (zp (1st-complete-src (frame->frame frame))))
        (not
         (or
          (equal (1st-complete-src (frame->frame frame))
                 (1st-complete (frame->frame frame)))
          (atom
           (assoc-equal (1st-complete-src (frame->frame frame))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal (1st-complete-src (frame->frame frame))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
        (context-apply-ok
         (frame-val->dir
          (cdr
           (assoc-equal (1st-complete-src (frame->frame frame))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal (1st-complete-src (frame->frame frame))
                          (remove-assoc-equal (1st-complete (frame->frame frame))
                                              (frame->frame frame))))))
          (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                             (frame->frame frame))))))
        (equal x (1st-complete (frame->frame frame))))
       (induction-scheme
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (1st-complete-src (frame->frame frame))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal (1st-complete-src (frame->frame frame))
                              (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr (assoc-equal
                   (1st-complete-src (frame->frame frame))
                   (remove-assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame)))))
            (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                              (frame->frame frame))))
            (1st-complete (frame->frame frame))
            (nthcdr
             (len
              (frame-val->path
               (cdr (assoc-equal
                     (1st-complete-src (frame->frame frame))
                     (remove-assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
             (frame-val->path
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))))
           (frame-val->src
            (cdr (assoc-equal (1st-complete-src (frame->frame frame))
                              (frame->frame frame)))))
          (remove-assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
        (1st-complete-src (frame->frame frame)) y))
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (not (zp (1st-complete-src (frame->frame frame))))
        (not
         (or
          (equal (1st-complete-src (frame->frame frame))
                 (1st-complete (frame->frame frame)))
          (atom
           (assoc-equal (1st-complete-src (frame->frame frame))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal (1st-complete-src (frame->frame frame))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
        (context-apply-ok
         (frame-val->dir
          (cdr
           (assoc-equal (1st-complete-src (frame->frame frame))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal (1st-complete-src (frame->frame frame))
                          (remove-assoc-equal (1st-complete (frame->frame frame))
                                              (frame->frame frame))))))
          (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                             (frame->frame frame))))))
        (equal y (1st-complete (frame->frame frame))))
       (induction-scheme
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (1st-complete-src (frame->frame frame))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal (1st-complete-src (frame->frame frame))
                              (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr (assoc-equal
                   (1st-complete-src (frame->frame frame))
                   (remove-assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame)))))
            (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                              (frame->frame frame))))
            (1st-complete (frame->frame frame))
            (nthcdr
             (len
              (frame-val->path
               (cdr (assoc-equal
                     (1st-complete-src (frame->frame frame))
                     (remove-assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
             (frame-val->path
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))))
           (frame-val->src
            (cdr (assoc-equal (1st-complete-src (frame->frame frame))
                              (frame->frame frame)))))
          (remove-assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
        x (1st-complete-src (frame->frame frame))))
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (not (zp (1st-complete-src (frame->frame frame))))
        (not
         (or
          (equal (1st-complete-src (frame->frame frame))
                 (1st-complete (frame->frame frame)))
          (atom
           (assoc-equal (1st-complete-src (frame->frame frame))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal (1st-complete-src (frame->frame frame))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
        (context-apply-ok
         (frame-val->dir
          (cdr
           (assoc-equal (1st-complete-src (frame->frame frame))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal (1st-complete-src (frame->frame frame))
                          (remove-assoc-equal (1st-complete (frame->frame frame))
                                              (frame->frame frame))))))
          (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                             (frame->frame frame)))))))
       (induction-scheme
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (1st-complete-src (frame->frame frame))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal (1st-complete-src (frame->frame frame))
                              (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr (assoc-equal
                   (1st-complete-src (frame->frame frame))
                   (remove-assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame)))))
            (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                              (frame->frame frame))))
            (1st-complete (frame->frame frame))
            (nthcdr
             (len
              (frame-val->path
               (cdr (assoc-equal
                     (1st-complete-src (frame->frame frame))
                     (remove-assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
             (frame-val->path
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))))
           (frame-val->src
            (cdr (assoc-equal (1st-complete-src (frame->frame frame))
                              (frame->frame frame)))))
          (remove-assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
        x y))
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (zp (1st-complete-src (frame->frame frame)))
        (context-apply-ok
         (frame->root frame)
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))))
       (induction-scheme
        (frame-with-root
         (context-apply
          (frame->root frame)
          (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))
          (1st-complete (frame->frame frame))
          (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                             (frame->frame frame)))))
         (remove-assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))
        x y))
      (t (mv frame x y)))))

  ;; This is important, but the induction scheme and subgoals were a drag.
  (defthmd
    abs-find-file-correctness-1-lemma-41
    (implies
     (and
      (no-duplicatesp-equal (strip-cars (frame->frame frame)))
      (mv-nth 1 (collapse frame))
      (frame-p (frame->frame frame))
      (consp (assoc-equal x (frame->frame frame)))
      (consp (assoc-equal y (frame->frame frame)))
      (not (equal x y))
      (prefixp (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
               (fat32-filename-list-fix pathname))
      (prefixp (frame-val->path (cdr (assoc-equal y (frame->frame frame))))
               (fat32-filename-list-fix pathname))
      (dist-names (frame->root frame)
                  nil (frame->frame frame))
      (abs-separate (frame->frame frame))
      (not
       (equal
        (mv-nth
         1
         (abs-find-file-helper
          (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
          (nthcdr
           (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
           pathname)))
        2)))
     (equal
      (abs-find-file-helper
       (frame-val->dir (cdr (assoc-equal y (frame->frame frame))))
       (nthcdr
        (len (frame-val->path (cdr (assoc-equal y (frame->frame frame)))))
        pathname))
      (mv (abs-file-fix nil) *enoent*)))
    :hints (("goal" :induct (induction-scheme frame x y)
             :in-theory (e/d (collapse)
                             ())))))

(defthm
  abs-find-file-correctness-1-lemma-47
  (implies
   (and
    (no-duplicatesp-equal (strip-cars frame))
    (mv-nth 1
            (collapse (frame-with-root root frame)))
    (frame-p frame)
    (consp (assoc-equal x frame))
    (subsetp-equal indices (strip-cars frame))
    (not (member-equal x indices))
    (prefixp (frame-val->path (cdr (assoc-equal x frame)))
             (fat32-filename-list-fix pathname))
    (dist-names root
                nil frame)
    (abs-separate frame)
    (not
     (equal
      (mv-nth 1
              (abs-find-file-helper
               (frame-val->dir (cdr (assoc-equal x frame)))
               (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                       pathname)))
      *enoent*)))
   (equal (abs-find-file-alt frame indices pathname)
          (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :induct (abs-find-file-alt frame indices pathname)
    :in-theory
    (e/d
     (abs-find-file-alt)
     (member-of-a-nat-list (:type-prescription member-of-strip-cars . 2))))
   ("subgoal *1/2"
    :expand (subsetp-equal indices (strip-cars frame))
    :use ((:instance (:type-prescription member-of-strip-cars . 2)
                     (alist frame)
                     (x (car indices)))
          (:instance member-of-a-nat-list (x nil)
                     (lst (strip-cars frame)))
          (:instance (:rewrite abs-find-file-correctness-1-lemma-41)
                     (frame (frame-with-root root frame))
                     (y (car indices)))))))

(defthmd
  abs-find-file-correctness-1-lemma-48
  (implies
   (and
    (dist-names root
                nil frame)
    (frame-p frame)
    (mv-nth 1
            (collapse (frame-with-root root frame)))
    (consp (assoc-equal x frame))
    (prefixp (frame-val->path (cdr (assoc-equal x frame)))
             (fat32-filename-list-fix pathname))
    (abs-separate frame)
    (not
     (equal
      (mv-nth 1
              (abs-find-file-helper
               (frame-val->dir (cdr (assoc-equal x frame)))
               (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                       pathname)))
      *enoent*))
    (no-duplicatesp-equal (strip-cars frame)))
   (equal (abs-find-file (remove-assoc-equal x frame)
                         pathname)
          (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal" :in-theory (disable abs-find-file-correctness-1-lemma-47)
    :use (:instance abs-find-file-correctness-1-lemma-47
                    (indices (remove-equal x (strip-cars frame))))
    :do-not-induct t)))

(defthm
  abs-find-file-correctness-1-lemma-10
  (implies
   (and
    (< 0 (1st-complete frame))
    (< 0 (1st-complete-src frame))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                frame)))
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame))))
    (context-apply-ok
     (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                       frame)))
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (1st-complete frame)
     (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                     frame))))
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (dist-names root nil frame)
    (abs-separate frame)
    (mv-nth
     1
     (collapse
      (frame-with-root
       root
       (put-assoc-equal
        (1st-complete-src frame)
        (frame-val
         (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                            frame)))
         (context-apply
          (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                            frame)))
          (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame)))
          (1st-complete frame)
          (nthcdr
           (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                   frame))))
           (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                              frame)))))
         (frame-val->src (cdr (assoc-equal (1st-complete-src frame)
                                           frame))))
        (remove-assoc-equal (1st-complete frame)
                            frame)))))
    (not
     (equal
      (mv-nth
       1
       (abs-find-file
        (remove-assoc-equal (1st-complete frame)
                            (remove-assoc-equal (1st-complete-src frame)
                                                frame))
        pathname))
      2))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))
             (fat32-filename-list-fix pathname)))
   (equal
    (mv-nth
     1
     (hifat-find-file
      (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                        frame)))
      (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                      frame))))
              pathname)))
    2))
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (collapse)
                    ((:rewrite abs-find-file-of-put-assoc-2)
                     (:rewrite len-of-remove-assoc-equal-2)
                     (:rewrite remove-assoc-of-put-assoc)
                     (:rewrite abs-find-file-helper-of-context-apply)))
    :use ((:instance (:rewrite abs-find-file-correctness-1-lemma-48)
                     (x (1st-complete frame))))
    :expand (collapse (frame-with-root root frame)))))

(defthm
  abs-find-file-correctness-1-lemma-50
  (implies
   (and
    (equal (mv-nth 1 (abs-find-file frame pathname))
           0)
    (< 0 (1st-complete frame))
    (< 0 (1st-complete-src frame))
    (not (equal (1st-complete-src frame)
                (1st-complete frame)))
    (consp (assoc-equal (1st-complete-src frame)
                        frame))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                frame)))
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame))))
    (context-apply-ok
     (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                       frame)))
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (1st-complete frame)
     (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                     frame))))
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (dist-names root
                nil frame)
    (abs-separate frame)
    (mv-nth
     1
     (collapse
      (frame-with-root
       root
       (put-assoc-equal
        (1st-complete-src frame)
        (frame-val
         (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                            frame)))
         (context-apply
          (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                            frame)))
          (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame)))
          (1st-complete frame)
          (nthcdr
           (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                   frame))))
           (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                              frame)))))
         (frame-val->src (cdr (assoc-equal (1st-complete-src frame)
                                           frame))))
        (remove-assoc-equal (1st-complete frame)
                            frame)))))
    (not
     (equal
      (mv-nth
       1
       (abs-find-file
        (remove-assoc-equal (1st-complete frame)
                            (remove-assoc-equal (1st-complete-src frame)
                                                frame))
        pathname))
      2)))
   (equal
    (mv-nth
     1
     (abs-find-file
      (put-assoc-equal
       (1st-complete-src frame)
       (frame-val
        (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                           frame)))
        (context-apply
         (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                           frame)))
         (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                           frame)))
         (1st-complete frame)
         (nthcdr
          (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                  frame))))
          (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                             frame)))))
        (frame-val->src (cdr (assoc-equal (1st-complete-src frame)
                                          frame))))
       (remove-assoc-equal (1st-complete frame)
                           frame))
      pathname))
    0))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (collapse)
                    ((:rewrite abs-find-file-of-put-assoc-2)
                     (:definition remove-assoc-equal)
                     (:rewrite remove-assoc-of-put-assoc)
                     (:rewrite len-of-remove-assoc-equal-2)
                     (:rewrite abs-file-alist-p-when-m1-file-alist-p)
                     (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
                     (:rewrite nthcdr-when->=-n-len-l)))
    :use
    ((:instance
      (:rewrite abs-find-file-of-put-assoc-2)
      (frame (remove-assoc-equal (1st-complete frame)
                                 frame))
      (val
       (frame-val
        (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                           frame)))
        (context-apply
         (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                           frame)))
         (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                           frame)))
         (1st-complete frame)
         (nthcdr
          (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                  frame))))
          (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                             frame)))))
        (frame-val->src (cdr (assoc-equal (1st-complete-src frame)
                                          frame)))))
      (name (1st-complete-src frame)))
     (:instance (:rewrite abs-find-file-correctness-1-lemma-48)
                (x (1st-complete-src frame)))))))

(defthm
  abs-find-file-correctness-1-lemma-52
  (implies
   (and
    (equal (mv-nth 1 (abs-find-file frame pathname))
           0)
    (< 0 (1st-complete frame))
    (< 0 (1st-complete-src frame))
    (not (equal (1st-complete-src frame)
                (1st-complete frame)))
    (consp (assoc-equal (1st-complete-src frame)
                        frame))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                frame)))
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame))))
    (context-apply-ok
     (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                       frame)))
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (1st-complete frame)
     (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                     frame))))
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (dist-names root
                nil frame)
    (abs-separate frame)
    (mv-nth
     1
     (collapse
      (frame-with-root
       root
       (put-assoc-equal
        (1st-complete-src frame)
        (frame-val
         (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                            frame)))
         (context-apply
          (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                            frame)))
          (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame)))
          (1st-complete frame)
          (nthcdr
           (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                   frame))))
           (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                              frame)))))
         (frame-val->src (cdr (assoc-equal (1st-complete-src frame)
                                           frame))))
        (remove-assoc-equal (1st-complete frame)
                            frame))))))
   (equal
    (mv-nth
     1
     (abs-find-file
      (put-assoc-equal
       (1st-complete-src frame)
       (frame-val
        (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                           frame)))
        (context-apply
         (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                           frame)))
         (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                           frame)))
         (1st-complete frame)
         (nthcdr
          (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                  frame))))
          (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                             frame)))))
        (frame-val->src (cdr (assoc-equal (1st-complete-src frame)
                                          frame))))
       (remove-assoc-equal (1st-complete frame)
                           frame))
      pathname))
    0))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable (:rewrite abs-find-file-of-put-assoc-lemma-6))
    :use
    ((:instance (:rewrite abs-find-file-of-put-assoc-lemma-6)
                (x (1st-complete-src frame)))
     (:instance (:rewrite abs-find-file-of-put-assoc-lemma-6)
                (x (1st-complete frame))
                (frame (remove-assoc-equal (1st-complete-src frame)
                                           frame)))))))

(encapsulate
  ()

  (local
   (in-theory
    (disable
     (:definition remove-assoc-equal)
     (:rewrite remove-assoc-of-put-assoc)
     (:rewrite len-of-remove-assoc-equal-2)
     (:rewrite abs-file-alist-p-when-m1-file-alist-p)
     (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p))))

  ;; A subgoal hint is required here because abs-fs-p-of-append is the culprit
  ;; that introduces strip-cars terms, and I don't feel like it's a good idea
  ;; to change that to names-at.
  (defthm
    abs-find-file-correctness-1-lemma-32
    (implies
     (and
      (equal
       (abs-find-file (remove-assoc-equal (1st-complete-src frame)
                                          frame)
                      pathname)
       (hifat-find-file
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                        frame))))
                pathname)))
      (< 0 (1st-complete frame))
      (not (equal (1st-complete-src frame)
                  (1st-complete frame)))
      (consp (assoc-equal (1st-complete-src frame)
                          frame))
      (list-equiv (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                     frame)))
                  (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                     frame))))
      (context-apply-ok
       (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                         frame)))
       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                         frame)))
       (1st-complete frame)
       nil)
      (frame-p frame)
      (no-duplicatesp-equal (strip-cars frame))
      (abs-separate frame)
      (m1-regular-file-p (mv-nth 0 (abs-find-file frame pathname)))
      (equal
       (mv-nth
        1
        (abs-find-file
         (remove-assoc-equal (1st-complete frame)
                             (remove-assoc-equal (1st-complete-src frame)
                                                 frame))
         pathname))
       2))
     (m1-regular-file-p
      (mv-nth
       0
       (abs-find-file-helper
        (context-apply
         (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                           frame)))
         (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                           frame)))
         (1st-complete frame)
         nil)
        (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                        frame))))
                pathname)))))
    :hints
    (("goal"
      :in-theory (e/d (context-apply abs-find-file-helper)
                      (abs-separate-correctness-1-lemma-14
                       (:rewrite abs-find-file-helper-of-context-apply)))
      :use
      ((:instance abs-separate-correctness-1-lemma-14
                  (x (1st-complete frame))
                  (y (1st-complete-src frame)))
       (:instance
        (:rewrite abs-find-file-helper-of-context-apply)
        (pathname
         (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                         frame))))
                 pathname))
        (x-path nil)
        (x (1st-complete frame))
        (abs-file-alist2 (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                           frame))))
        (abs-file-alist1
         (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                           frame))))))
      :do-not-induct t)
     ("Subgoal 13'" :expand
      ((names-at (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                   frame)))
                 nil)
       (names-at
        (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                          frame)))
        nil)))))

  (defthm
    abs-find-file-correctness-1-lemma-61
    (implies
     (and
      (prefixp (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                  frame)))
               (fat32-filename-list-fix pathname))
      (not
       (equal
        (mv-nth
         1
         (abs-find-file-helper
          (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                            frame)))
          (nthcdr
           (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                   frame))))
           pathname)))
        2))
      (< 0 (1st-complete frame))
      (< 0 (1st-complete-src frame))
      (prefixp (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                  frame)))
               (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                  frame))))
      (context-apply-ok
       (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                         frame)))
       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                         frame)))
       (1st-complete frame)
       (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                       frame))))
               (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                  frame)))))
      (frame-p frame)
      (no-duplicatesp-equal (strip-cars frame))
      (dist-names root
                  nil frame)
      (abs-separate frame)
      (mv-nth
       1
       (collapse
        (frame-with-root
         root
         (put-assoc-equal
          (1st-complete-src frame)
          (frame-val
           (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                              frame)))
           (context-apply
            (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                              frame)))
            (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                              frame)))
            (1st-complete frame)
            (nthcdr
             (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                     frame))))
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))))
           (frame-val->src (cdr (assoc-equal (1st-complete-src frame)
                                             frame))))
          (remove-assoc-equal (1st-complete frame)
                              frame))))))
     (equal (mv-nth 1
                    (abs-find-file (remove-assoc-equal (1st-complete-src frame)
                                                       frame)
                                   pathname))
            *enoent*))
    :hints
    (("goal" :in-theory (enable collapse)
      :use (:instance (:rewrite abs-find-file-correctness-1-lemma-48)
                      (x (1st-complete-src frame)))))))

(defthm
  abs-find-file-correctness-1-lemma-60
  (implies
   (and
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                frame)))
             (fat32-filename-list-fix pathname))
    (not
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                          frame)))
        (nthcdr
         (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                 frame))))
         pathname)))
      2))
    (< 0 (1st-complete frame))
    (< 0 (1st-complete-src frame))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                frame)))
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame))))
    (context-apply-ok
     (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                       frame)))
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (1st-complete frame)
     (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                     frame))))
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (dist-names root nil frame)
    (abs-separate frame)
    (mv-nth
     1
     (collapse
      (frame-with-root
       root
       (put-assoc-equal
        (1st-complete-src frame)
        (frame-val
         (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                            frame)))
         (context-apply
          (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                            frame)))
          (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame)))
          (1st-complete frame)
          (nthcdr
           (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                   frame))))
           (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                              frame)))))
         (frame-val->src (cdr (assoc-equal (1st-complete-src frame)
                                           frame))))
        (remove-assoc-equal (1st-complete frame)
                            frame))))))
   (equal (mv-nth 1
                  (abs-find-file (remove-assoc-equal (1st-complete-src frame)
                                                     frame)
                                 pathname))
          2))
  :hints
  (("goal" :in-theory (e/d (collapse) nil)
    :use ((:instance (:rewrite abs-find-file-correctness-1-lemma-48)
                     (x (1st-complete-src frame)))
          (:instance (:rewrite abs-find-file-correctness-1-lemma-48)
                     (x (1st-complete frame)))))))

;; Removing this lemma causes the main theorem to run into problems of
;; extremely long duration.
(defthm
  abs-find-file-correctness-1-lemma-62
  (implies
   (and
    (< 0 (1st-complete frame))
    (< 0 (1st-complete-src frame))
    (not (equal (1st-complete-src frame)
                (1st-complete frame)))
    (consp (assoc-equal (1st-complete-src frame)
                        frame))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                frame)))
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame))))
    (context-apply-ok
     (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                       frame)))
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (1st-complete frame)
     (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                     frame))))
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-separate frame)
    (mv-nth
     1
     (collapse
      (frame-with-root
       root
       (put-assoc-equal
        (1st-complete-src frame)
        (frame-val
         (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                            frame)))
         (context-apply
          (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                            frame)))
          (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame)))
          (1st-complete frame)
          (nthcdr
           (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                   frame))))
           (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                              frame)))))
         (frame-val->src (cdr (assoc-equal (1st-complete-src frame)
                                           frame))))
        (remove-assoc-equal (1st-complete frame)
                            frame)))))
    (dist-names root nil frame)
    (m1-regular-file-p (mv-nth 0 (abs-find-file frame pathname))))
   (equal
    (abs-find-file
     (put-assoc-equal
      (1st-complete-src frame)
      (frame-val
       (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                          frame)))
       (context-apply
        (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                          frame)))
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (1st-complete frame)
        (nthcdr
         (len (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                 frame))))
         (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                            frame)))))
       (frame-val->src (cdr (assoc-equal (1st-complete-src frame)
                                         frame))))
      (remove-assoc-equal (1st-complete frame)
                          frame))
     pathname)
    (abs-find-file frame pathname))))

(defthm
  abs-find-file-correctness-1-lemma-63
  (implies
   (and
    (equal (1st-complete-src (frame->frame frame))
           0)
    (< 0 (1st-complete (frame->frame frame)))
    (context-apply-ok
     (frame->root frame)
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     (1st-complete (frame->frame frame))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))
    (prefixp
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
     (fat32-filename-list-fix pathname))
    (not
     (equal
      (mv-nth
       1
       (hifat-find-file
        (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (nthcdr
         (len (frame-val->path
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame)))))
         pathname)))
      2))
    (mv-nth
     1
     (collapse
      (frame-with-root
       (context-apply
        (frame->root frame)
        (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (1st-complete (frame->frame frame))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame)))))
       (remove-assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame)))))
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (dist-names (frame->root frame)
                nil (frame->frame frame))
    (abs-separate (frame->frame frame)))
   (equal
    (abs-find-file (remove-assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))
                   pathname)
    (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal" :in-theory (enable collapse)
    :use (:instance (:rewrite abs-find-file-correctness-1-lemma-48)
                    (frame (frame->frame frame))
                    (x (1st-complete (frame->frame frame)))
                    (root (frame->root frame))))))

(defthm
  abs-find-file-correctness-1
  (implies
   (and (mv-nth 1 (collapse frame))
        (frame-p (frame->frame frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame)))
        (abs-separate (frame-with-root (frame->root frame)
                                       (frame->frame frame)))
        (zp (mv-nth 1
                    (abs-find-file (frame-with-root (frame->root frame)
                                                    (frame->frame frame))
                                   pathname)))
        (m1-regular-file-p
         (mv-nth 0
                 (abs-find-file (frame-with-root (frame->root frame)
                                                 (frame->frame frame))
                                pathname))))
   (equal (abs-find-file (frame-with-root (frame->root frame)
                                          (frame->frame frame))
                         pathname)
          (mv (mv-nth 0
                      (hifat-find-file (mv-nth 0 (collapse frame))
                                       pathname))
              0)))
  :hints
  (("goal"
    :in-theory (e/d (abs-find-file collapse abs-separate intersectp-equal)
                    ((:rewrite nthcdr-when->=-n-len-l)
                     (:rewrite len-when-prefixp)
                     (:definition remove-assoc-equal)
                     (:rewrite remove-assoc-of-remove-assoc)
                     (:rewrite len-of-remove-assoc-equal-2)
                     (:rewrite abs-file-alist-p-when-m1-file-alist-p)
                     (:rewrite remove-assoc-of-put-assoc)))
    :induct (collapse frame))))

(defund 1st-complete-under-pathname (frame pathname)
  (declare (xargs :guard (frame-p frame)))
  (b* (((when (atom frame)) 0)
       (head-index (caar frame))
       (head-frame-val (cdar frame)))
    (if (and (abs-complete (frame-val->dir head-frame-val))
             (prefixp pathname (frame-val->path head-frame-val)))
        (mbe :exec head-index :logic (nfix head-index))
      (1st-complete-under-pathname (cdr frame) pathname))))

(defund 1st-complete-under-pathname-src (frame pathname)
  (declare (xargs :guard (and (frame-p frame)
                              (consp (assoc-equal (1st-complete-under-pathname
                                                   frame pathname)
                                                  frame)))))
  (frame-val->src (cdr (assoc-equal (1st-complete-under-pathname frame pathname) frame))))

(defund
  1st-complete-under-pathname-src
  (frame pathname)
  (declare
   (xargs
    :guard
    (and
     (frame-p frame)
     (consp
      (assoc-equal (1st-complete-under-pathname frame pathname)
                   frame)))))
  (frame-val->src
   (cdr
    (assoc-equal (1st-complete-under-pathname frame pathname)
                 frame))))

(defthm
  1st-complete-under-pathname-correctness-1
  (implies (not (zp (1st-complete-under-pathname frame pathname)))
           (consp (assoc-equal (1st-complete-under-pathname frame pathname)
                               frame)))
  :hints (("goal" :in-theory (enable 1st-complete-under-pathname)))
  :rule-classes :type-prescription)

(defund
  partial-collapse (frame pathname)
  (declare (xargs :guard (and (frame-p frame)
                              (consp (assoc-equal 0 frame)))
                  :measure (len (frame->frame frame))
                  :guard-debug t))
  (b*
      (((when (atom (frame->frame frame)))
        frame)
       (head-index (1st-complete-under-pathname (frame->frame frame) pathname))
       ((when (zp head-index))
        frame)
       (head-frame-val
        (cdr (assoc-equal head-index (frame->frame frame))))
       (src (1st-complete-under-pathname-src (frame->frame frame) pathname)))
    (if
        (zp src)
        (b*
            ((root-after-context-apply
              (context-apply (frame->root frame)
                             (frame-val->dir head-frame-val)
                             head-index
                             (frame-val->path head-frame-val)))
             ((when
                  (not
                   (context-apply-ok (frame->root frame)
                                     (frame-val->dir head-frame-val)
                                     head-index
                                     (frame-val->path head-frame-val))))
              frame)
             (frame
              (frame-with-root
               root-after-context-apply
               (remove-assoc-equal head-index (frame->frame frame)))))
          (partial-collapse frame pathname))
      (b*
          ((path (frame-val->path head-frame-val))
           ((when
                (or
                 (equal src head-index)
                 (atom
                  (assoc-equal src
                               (remove-assoc-equal
                                head-index (frame->frame frame))))))
            frame)
           (src-path
            (frame-val->path
             (cdr
              (assoc-equal src
                           (remove-assoc-equal
                            head-index (frame->frame frame))))))
           (src-dir
            (frame-val->dir
             (cdr
              (assoc-equal src
                           (remove-assoc-equal
                            head-index (frame->frame frame))))))
           ((unless (prefixp src-path path))
            frame)
           (src-dir-after-context-apply
            (context-apply src-dir (frame-val->dir head-frame-val)
                           head-index
                           (nthcdr (len src-path) path)))
           ((when (not (context-apply-ok
                        src-dir (frame-val->dir head-frame-val)
                        head-index
                        (nthcdr (len src-path) path))))
            frame)
           (frame
            (frame-with-root
             (frame->root frame)
             (put-assoc-equal
              src
              (frame-val
               (frame-val->path
                (cdr (assoc-equal src (frame->frame frame))))
               (abs-fs-fix
                src-dir-after-context-apply)
               (frame-val->src
                (cdr (assoc-equal src (frame->frame frame)))))
              (remove-assoc-equal
               head-index (frame->frame frame))))))
        (partial-collapse frame pathname)))))

(defthmd
  context-apply-ok-when-absfat-equiv-lemma-1
  (implies (and (abs-fs-p abs-file-alist1)
                (abs-fs-p abs-file-alist2)
                (absfat-equiv abs-file-alist1 abs-file-alist2))
           (equal (consp (assoc-equal x abs-file-alist1))
                  (consp (assoc-equal x abs-file-alist2))))
  :hints
  (("goal" :in-theory (e/d (absfat-equiv)
                           (absfat-equiv-implies-set-equiv-names-at-1-lemma-1))
    :do-not-induct t
    :use ((:instance absfat-equiv-implies-set-equiv-names-at-1-lemma-1
                     (abs-file-alist2 abs-file-alist1)
                     (abs-file-alist1 abs-file-alist2))
          absfat-equiv-implies-set-equiv-names-at-1-lemma-1))))

(defthm
  context-apply-ok-when-absfat-equiv-lemma-3
  (implies (and (abs-fs-p abs-file-alist1)
                (abs-fs-p abs-file-alist2)
                (absfat-equiv abs-file-alist1 abs-file-alist2)
                (consp (assoc-equal (fat32-filename-fix (car x-path))
                                    abs-file-alist1)))
           (consp (assoc-equal (fat32-filename-fix (car x-path))
                               abs-file-alist2)))
  :hints
  (("goal"
    :use (:instance (:rewrite context-apply-ok-when-absfat-equiv-lemma-1)
                    (abs-file-alist2 abs-file-alist1)
                    (abs-file-alist1 abs-file-alist2)
                    (x (fat32-filename-fix (car x-path)))))))

(defthm context-apply-ok-when-absfat-equiv-lemma-4
  (implies (and (natp x)
                (absfat-subsetp abs-file-alist1 abs-file-alist2)
                (member-equal x abs-file-alist1))
           (member-equal x abs-file-alist2))
  :hints (("goal" :in-theory (enable absfat-subsetp))))

(defthm
  context-apply-ok-when-absfat-equiv-lemma-5
  (implies (and (member-equal x abs-file-alist2)
                (natp x)
                (absfat-subsetp abs-file-alist1 abs-file-alist2)
                (absfat-subsetp abs-file-alist2 abs-file-alist1)
                (not (member-equal x (abs-addrs abs-file-alist3))))
           (not (equal (append (remove-equal x abs-file-alist1)
                               abs-file-alist3)
                       abs-file-alist1)))
  :instructions
  (:promote
   (:claim (not (member-equal x
                              (append (remove-equal x abs-file-alist1)
                                      abs-file-alist3))))
   (:claim (member-equal x abs-file-alist1))
   (:= t)))

;; OK, it would definitely be nice to make context-apply-ok-when-absfat-equiv-1
;; a congruence by removing the member-equal hypothesis. Here's the thing
;; though, it can't be done, because it's totally possible to context apply
;; something and end up with the same thing. Vacuous example: apply a tree
;; consisting only of the top-level variable x to a tree consisting only of the
;; top-level variable x (cue Spider-men pointing at each other...) This,
;; obviously, is not possible when we stipulate that only complete trees can be
;; applied any place, and in fact we have a really great fixing function for
;; that purpose - hifat-file-alist-fix. However, I'm going to spare myself that
;; bit of pain for now.
(encapsulate
  ()

  (local
   (defthmd
     context-apply-ok-when-absfat-equiv-lemma-6
     (implies (and (natp x)
                   (absfat-equiv abs-file-alist1 abs-file-alist2)
                   (abs-fs-p abs-file-alist1)
                   (abs-fs-p abs-file-alist2)
                   (abs-file-alist-p abs-file-alist3)
                   (not (member-equal x (abs-addrs abs-file-alist3))))
              (equal (context-apply-ok abs-file-alist1
                                       abs-file-alist3 x x-path)
                     (context-apply-ok abs-file-alist2
                                       abs-file-alist3 x x-path)))
     :hints
     (("goal" :in-theory (e/d (context-apply-ok context-apply absfat-equiv)
                              (absfat-subsetp-correctness-1
                               abs-file->contents-when-m1-file-p))
       :induct (mv (context-apply abs-file-alist1
                                  abs-file-alist3 x x-path)
                   (context-apply abs-file-alist2
                                  abs-file-alist3 x x-path))))))

  (defthmd
    context-apply-ok-when-absfat-equiv-1
    (implies (and (absfat-equiv abs-file-alist1 abs-file-alist2)
                  (not (member-equal (nfix x)
                                     (abs-addrs (abs-fs-fix abs-file-alist3)))))
             (equal (context-apply-ok abs-file-alist1
                                      abs-file-alist3 x x-path)
                    (context-apply-ok abs-file-alist2
                                      abs-file-alist3 x x-path)))
    :hints
    (("goal"
      :use (context-apply-ok-when-absfat-equiv-lemma-6
            (:instance context-apply-ok-when-absfat-equiv-lemma-6
                       (x (nfix x))
                       (abs-file-alist1 (abs-fs-fix abs-file-alist1))
                       (abs-file-alist2 (abs-fs-fix abs-file-alist2))
                       (abs-file-alist3 (abs-fs-fix abs-file-alist3))))))))

(defthm
  context-apply-ok-when-absfat-equiv-lemma-7
  (implies (and (natp x)
                (not (member-equal x (abs-addrs abs-file-alist1)))
                (member-equal x abs-file-alist3))
           (not (equal (append (remove-equal x abs-file-alist3)
                               abs-file-alist1)
                       abs-file-alist3)))
  :hints
  (("goal" :cases ((member-equal x
                                 (append (remove-equal x abs-file-alist3)
                                         abs-file-alist1))))))

;; This is kinda general.
(defthmd context-apply-ok-when-absfat-equiv-lemma-8
  (implies (and (natp x)
                (absfat-equiv abs-file-alist1 abs-file-alist2)
                (abs-fs-p abs-file-alist1)
                (abs-fs-p abs-file-alist2))
           (iff (member-equal x abs-file-alist1)
                (member-equal x abs-file-alist2)))
  :hints (("goal" :in-theory (enable absfat-equiv)
           :do-not-induct t)))

(defthm
  context-apply-ok-when-absfat-equiv-lemma-2
  (implies (and (member-equal x (abs-fs-fix abs-file-alist3))
                (integerp x)
                (<= 0 x)
                (absfat-equiv abs-file-alist1 abs-file-alist2)
                (not (member-equal x
                                   (abs-addrs (abs-fs-fix abs-file-alist1)))))
           (not (equal (append (remove-equal x (abs-fs-fix abs-file-alist3))
                               (abs-fs-fix abs-file-alist2))
                       (abs-fs-fix abs-file-alist3))))
  :instructions
  (:promote
   (:claim
    (not (member-equal x
                       (append (remove-equal x (abs-fs-fix abs-file-alist3))
                               (abs-fs-fix abs-file-alist2))))
    :hints :none)
   (:change-goal nil t)
   (:dive 1)
   (:rewrite member-of-append)
   :top
   :bash
   (:use (:instance (:rewrite context-apply-ok-when-absfat-equiv-lemma-8)
                    (abs-file-alist1 (abs-fs-fix abs-file-alist2))
                    (abs-file-alist2 (abs-fs-fix abs-file-alist1))))
   :bash :bash))

(defthmd
  context-apply-ok-when-absfat-equiv-2
  (implies (and (natp x)
                (absfat-equiv abs-file-alist1 abs-file-alist2)
                (not (and (member-equal x (abs-addrs (abs-fs-fix abs-file-alist1)))
                          (member-equal x (abs-addrs (abs-fs-fix abs-file-alist2))))))
           (equal (context-apply-ok abs-file-alist3
                                    abs-file-alist1 x x-path)
                  (context-apply-ok abs-file-alist3
                                    abs-file-alist2 x x-path)))
  :hints (("goal" :in-theory (enable context-apply-ok context-apply)
           :induct (mv (context-apply abs-file-alist3
                                      abs-file-alist1 x x-path)
                       (context-apply abs-file-alist3
                                      abs-file-alist2 x x-path)))))

(defthm
  absfat-equiv-of-context-apply-lemma-1
  (implies
   (and
    (subsetp-equal
     (abs-addrs (abs-file->contents y))
     (abs-addrs (abs-file->contents (cdr (assoc-equal x abs-file-alist2)))))
    (abs-directory-file-p (cdr (assoc-equal x abs-file-alist2))))
   (subsetp-equal (abs-addrs (abs-file->contents y))
                  (abs-addrs abs-file-alist2)))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm absfat-equiv-of-context-apply-lemma-4
  (implies (and (abs-file-alist-p abs-file-alist1)
                (absfat-subsetp abs-file-alist1 abs-file-alist2))
           (subsetp-equal (abs-addrs abs-file-alist1)
                          (abs-addrs abs-file-alist2)))
  :hints (("goal" :in-theory (enable absfat-subsetp abs-addrs
                                     member-of-abs-fs-fix-when-natp-lemma-1))))

(defthm
  absfat-equiv-of-context-apply-lemma-5
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                            abs-file-alist3)))
    (absfat-subsetp
     (context-apply
      (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                            abs-file-alist3)))
      abs-file-alist2 x (cdr x-path))
     (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                           abs-file-alist3))))
    (abs-file-alist-p abs-file-alist2))
   (absfat-subsetp
    (abs-file-contents-fix
     (context-apply (abs-file->contents$inline
                     (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                       abs-file-alist3)))
                    abs-file-alist2 x (cdr x-path)))
    (abs-file->contents$inline
     (cdr (assoc-equal (fat32-filename-fix (car x-path))
                       abs-file-alist3))))))

(defthm
  absfat-equiv-of-context-apply-lemma-6
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                            abs-file-alist3)))
    (absfat-subsetp
     (context-apply
      (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                            abs-file-alist3)))
      abs-file-alist2 x (cdr x-path))
     (context-apply
      (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                            abs-file-alist3)))
      abs-file-alist1 x (cdr x-path)))
    (abs-file-alist-p abs-file-alist1)
    (abs-file-alist-p abs-file-alist2))
   (absfat-subsetp
    (abs-file-contents-fix
     (context-apply (abs-file->contents$inline
                     (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                       abs-file-alist3)))
                    abs-file-alist2 x (cdr x-path)))
    (abs-file-contents-fix
     (context-apply (abs-file->contents$inline
                     (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                       abs-file-alist3)))
                    abs-file-alist1 x (cdr x-path))))))

(defthm absfat-equiv-of-context-apply-lemma-8
  (implies (and (consp (car x))
                (abs-file-alist-p x))
           (fat32-filename-p (caar x)))
  :hints (("goal" :in-theory (enable abs-file-alist-p)))
  :rule-classes
  (:rewrite
   (:type-prescription
    :corollary
    (implies (and (consp (car x))
                  (abs-file-alist-p x))
             (caar x)))))

(defthm
  absfat-equiv-of-context-apply-lemma-9
  (implies
   (and (abs-file-alist-p x)
        (consp (car x)))
   (abs-file-alist-p
    (list (cons (car (car x))
                (abs-file (abs-file->dir-ent (cdr (car x)))
                          (abs-fs-fix (abs-file->contents (cdr (car x)))))))))
  :hints (("goal" :in-theory (enable abs-file-alist-p abs-file))))

(defthm
  absfat-equiv-of-context-apply-lemma-10
  (implies
   (and (absfat-subsetp (abs-fs-fix (append (cdr x) y))
                        (abs-fs-fix (append (cdr x) z)))
        (abs-file-alist-p x)
        (abs-fs-p z)
        (consp (car x))
        (not (consp (assoc-equal (car (car x)) (cdr x))))
        (not (consp (assoc-equal (car (car x)) z))))
   (absfat-subsetp
    (abs-fs-fix (append (cdr x) y))
    (cons (cons (car (car x))
                (abs-file (abs-file->dir-ent (cdr (car x)))
                          (abs-fs-fix (abs-file->contents (cdr (car x))))))
          (abs-fs-fix (append (cdr x) z)))))
  :hints
  (("goal"
    :in-theory (e/d (abs-no-dups-p)
                    ((:rewrite absfat-subsetp-of-append-2)))
    :use
    (:instance
     (:rewrite absfat-subsetp-of-append-2)
     (z (abs-fs-fix (append (cdr x) z)))
     (y
      (list
       (cons (car (car x))
             (abs-file (abs-file->dir-ent (cdr (car x)))
                       (abs-fs-fix (abs-file->contents (cdr (car x))))))))
     (x (abs-fs-fix (append (cdr x) y)))))))

(defthm
  absfat-equiv-of-context-apply-lemma-11
  (implies (and (abs-file-alist-p x)
                (not (abs-directory-file-p (abs-file-fix (cdr (car x))))))
           (abs-file-alist-p (list (cons (car (car x))
                                         (abs-file-fix (cdr (car x)))))))
  :hints (("goal" :in-theory (enable abs-file-alist-p abs-file-fix))))

(defthm
  absfat-equiv-of-context-apply-lemma-12
  (implies (and (absfat-subsetp (abs-fs-fix (append (cdr x) y))
                                (abs-fs-fix (append (cdr x) z)))
                (abs-file-alist-p x)
                (abs-fs-p z)
                (consp (car x))
                (not (consp (assoc-equal (car (car x)) (cdr x))))
                (not (abs-directory-file-p (abs-file-fix (cdr (car x)))))
                (not (consp (assoc-equal (car (car x)) z))))
           (absfat-subsetp (abs-fs-fix (append (cdr x) y))
                           (cons (cons (car (car x))
                                       (abs-file-fix (cdr (car x))))
                                 (abs-fs-fix (append (cdr x) z)))))
  :hints
  (("goal" :in-theory (e/d (abs-no-dups-p)
                           ((:rewrite absfat-subsetp-of-append-2)))
    :use (:instance (:rewrite absfat-subsetp-of-append-2)
                    (z (abs-fs-fix (append (cdr x) z)))
                    (y (list (cons (car (car x))
                                   (abs-file-fix (cdr (car x))))))
                    (x (abs-fs-fix (append (cdr x) y)))))))

(defthm
  absfat-equiv-of-context-apply-lemma-13
  (implies (and (abs-file-alist-p x)
                (abs-fs-p y)
                (abs-fs-p z)
                (absfat-subsetp y z)
                (absfat-subsetp z y))
           (absfat-subsetp (abs-fs-fix (append x y))
                           (abs-fs-fix (append x z))))
  :hints
  (("goal"
    :in-theory (e/d (absfat-subsetp abs-fs-fix)
                    ((:rewrite abs-file-alist-p-when-m1-file-alist-p)
                     (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
                     (:rewrite abs-file-alist-p-correctness-1)
                     (:rewrite abs-file->contents-when-m1-file-p)
                     (:rewrite absfat-subsetp-transitivity-lemma-8)
                     (:rewrite absfat-subsetp-transitivity-lemma-3)))
    :induct t
    :expand ((:with assoc-equal-of-append-1
                    (assoc-equal (car (car x))
                                 (append (cdr x) z)))
             (:with assoc-equal-of-append-1
                    (assoc-equal (car (car x))
                                 (append (cdr x) y)))))))

(defthm
  abs-fs-fix-of-put-assoc-equal-lemma-2
  (implies (abs-directory-file-p (abs-file-fix x))
           (abs-file-alist-p (abs-file->contents$inline x)))
  :hints (("goal" :in-theory (enable abs-file-alist-p abs-directory-file-p
                                     abs-file->contents abs-file-fix))))

(defthm abs-fs-fix-of-put-assoc-equal-lemma-1
  (implies (and (abs-file-alist-p fs)
                (consp (car fs)))
           (abs-file-p (cdr (car fs))))
  :hints (("goal" :in-theory (enable abs-file-alist-p abs-file-p))))

(defthm
  abs-fs-fix-of-put-assoc-equal
  (implies
   (and (abs-fs-p fs)
        (consp (assoc-equal name fs)))
   (equal
    (abs-fs-fix (put-assoc-equal name val fs))
    (if (abs-directory-file-p (abs-file-fix val))
        (put-assoc-equal name
                         (abs-file (abs-file->dir-ent val)
                                   (abs-fs-fix (abs-file->contents val)))
                         fs)
      (put-assoc-equal name (abs-file-fix val)
                       fs))))
  :hints (("goal" :in-theory (enable abs-fs-fix abs-fs-p abs-no-dups-p
                                     member-of-abs-fs-fix-when-natp-lemma-1))))

(defthm
  absfat-equiv-of-context-apply-lemma-15
  (implies (and (abs-file-alist-p x)
                (abs-file-alist-p z)
                (abs-no-dups-p z)
                (fat32-filename-p name)
                (not (consp (assoc-equal name x))))
           (equal (assoc-equal name (abs-fs-fix (append z x)))
                  (assoc-equal name z)))
  :hints (("goal" :in-theory (enable abs-fs-fix abs-no-dups-p abs-fs-p))))

(defthm absfat-equiv-of-context-apply-lemma-16
  (implies (and (abs-directory-file-p (cdr (car y)))
                (abs-no-dups-p y))
           (abs-no-dups-p (abs-file->contents (cdr (car y)))))
  :hints (("goal" :in-theory (enable abs-no-dups-p))))

;; Head off a subinduction.
(defthm
  absfat-equiv-of-context-apply-lemma-3
  (implies (and (abs-file-alist-p x)
                (abs-no-dups-p x))
           (absfat-subsetp x (abs-fs-fix (append z x))))
  :hints
  (("goal"
    :in-theory (e/d (absfat-subsetp abs-fs-fix abs-fs-p)
                    ((:rewrite abs-file-alist-p-when-m1-file-alist-p)
                     (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
                     (:rewrite abs-file-alist-p-correctness-1)
                     (:rewrite abs-file->contents-when-m1-file-p)
                     (:rewrite absfat-subsetp-transitivity-lemma-8)
                     (:rewrite absfat-subsetp-transitivity-lemma-3))))))

(defthm
  absfat-equiv-of-context-apply-lemma-17
  (implies (and (abs-file-alist-p x)
                (abs-no-dups-p x)
                (abs-fs-p y)
                (abs-fs-p z)
                (absfat-subsetp y z))
           (absfat-subsetp (abs-fs-fix (append y x))
                           (abs-fs-fix (append z x))))
  :hints
  (("goal"
    :in-theory (e/d (absfat-subsetp abs-fs-fix abs-fs-p
                                    member-of-abs-fs-fix-when-natp-lemma-1)
                    ((:rewrite abs-file-alist-p-when-m1-file-alist-p)
                     (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
                     (:rewrite abs-file-alist-p-correctness-1)
                     (:rewrite abs-file->contents-when-m1-file-p)
                     (:rewrite absfat-subsetp-transitivity-lemma-8)
                     (:rewrite absfat-subsetp-transitivity-lemma-3)))
    :induct t
    :expand (:with assoc-equal-of-append-1
                   (assoc-equal (car (car y))
                                (append (cdr y) x))))))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies (and (natp x)
                   (absfat-equiv abs-file-alist1 abs-file-alist2)
                   (abs-fs-p abs-file-alist1)
                   (abs-fs-p abs-file-alist2))
              (absfat-equiv (context-apply abs-file-alist3
                                           abs-file-alist1 x x-path)
                            (context-apply abs-file-alist3
                                           abs-file-alist2 x x-path)))
     :hints (("goal" :in-theory (e/d (context-apply absfat-equiv))
              :induct (mv (context-apply abs-file-alist3
                                         abs-file-alist1 x x-path)
                          (context-apply abs-file-alist3
                                         abs-file-alist2 x x-path))))))

  ;; Pretty general.
  (defthm
    absfat-equiv-of-context-apply-1
    (implies (absfat-equiv abs-file-alist1 abs-file-alist2)
             (absfat-equiv (context-apply abs-file-alist3
                                          abs-file-alist1 x x-path)
                           (context-apply abs-file-alist3
                                          abs-file-alist2 x x-path)))
    :hints (("goal"
             :use (:instance lemma
                             (x (nfix x))
                             (abs-file-alist1 (abs-fs-fix abs-file-alist1))
                             (abs-file-alist2 (abs-fs-fix abs-file-alist2)))))
    :rule-classes :congruence))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies (and (natp x)
                   (absfat-equiv abs-file-alist1 abs-file-alist2)
                   (abs-fs-p abs-file-alist1)
                   (abs-fs-p abs-file-alist2))
              (absfat-equiv (context-apply abs-file-alist1
                                           abs-file-alist3 x x-path)
                            (context-apply abs-file-alist2
                                           abs-file-alist3 x x-path)))
     :hints
     (("goal" :in-theory (e/d (context-apply-ok context-apply absfat-equiv)
                              (absfat-subsetp-correctness-1
                               abs-file->contents-when-m1-file-p
                               (:rewrite abs-no-dups-p-when-m1-file-alist-p)
                               (:rewrite put-assoc-equal-without-change . 2)
                               (:definition put-assoc-equal)
                               (:rewrite abs-file-alist-p-correctness-1)))
       :induct (mv (context-apply abs-file-alist1
                                  abs-file-alist3 x x-path)
                   (context-apply abs-file-alist2
                                  abs-file-alist3 x x-path))
       :expand (:free (abs-file-alist2)
                      (absfat-subsetp nil abs-file-alist2))))))

  ;; Quite general.
  (defthmd
    absfat-equiv-of-context-apply-2
    (implies (absfat-equiv abs-file-alist1 abs-file-alist2)
             (absfat-equiv (context-apply abs-file-alist1
                                          abs-file-alist3 x x-path)
                           (context-apply abs-file-alist2
                                          abs-file-alist3 x x-path)))
    :hints
    (("goal"
      :use (:instance lemma
                      (x (nfix x))
                      (abs-file-alist1 (abs-fs-fix abs-file-alist1))
                      (abs-file-alist2 (abs-fs-fix abs-file-alist2)))))
    :rule-classes :congruence))

(defthm
  context-apply-ok-of-context-apply-lemma-1
  (implies
   (and (equal (append (remove-equal x2 (remove-equal x3 abs-file-alist1))
                       (remove-equal x2 abs-file-alist3)
                       abs-file-alist2)
               (append (remove-equal x3 abs-file-alist1)
                       abs-file-alist3))
        (member-equal x2
                      (append (remove-equal x3 abs-file-alist1)
                              abs-file-alist3)))
   (member-equal x2
                 (append (remove-equal x2 (remove-equal x3 abs-file-alist1))
                         (remove-equal x2 abs-file-alist3)
                         abs-file-alist2)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (integerp x2)
          (<= 0 x2)
          (not (equal x2 x3))
          (member-equal x2 abs-file-alist1)
          (not (member-equal x2 (abs-addrs abs-file-alist2))))
     (not (equal (append (remove-equal x2 (remove-equal x3 abs-file-alist1))
                         (remove-equal x2 abs-file-alist3)
                         abs-file-alist2)
                 (append (remove-equal x3 abs-file-alist1)
                         abs-file-alist3)))))))

(defthm
  context-apply-ok-of-context-apply-lemma-2
  (implies
   (and
    (equal
     (append
      (remove-equal
       x2
       (put-assoc-equal
        (fat32-filename-fix (car x3-path))
        (abs-file
         (abs-file->dir-ent
          (cdr (assoc-equal (fat32-filename-fix (car x3-path))
                            abs-file-alist1)))
         (context-apply
          (abs-file->contents
           (cdr (assoc-equal (fat32-filename-fix (car x3-path))
                             abs-file-alist1)))
          abs-file-alist3 x3 (cdr x3-path)))
        abs-file-alist1))
      abs-file-alist2)
     (put-assoc-equal
      (fat32-filename-fix (car x3-path))
      (abs-file
       (abs-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car x3-path))
                                            abs-file-alist1)))
       (context-apply
        (abs-file->contents
         (cdr (assoc-equal (fat32-filename-fix (car x3-path))
                           abs-file-alist1)))
        abs-file-alist3 x3 (cdr x3-path)))
      abs-file-alist1))
    (member-equal
     x2
     (put-assoc-equal
      (fat32-filename-fix (car x3-path))
      (abs-file
       (abs-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car x3-path))
                                            abs-file-alist1)))
       (context-apply
        (abs-file->contents
         (cdr (assoc-equal (fat32-filename-fix (car x3-path))
                           abs-file-alist1)))
        abs-file-alist3 x3 (cdr x3-path)))
      abs-file-alist1)))
   (member-equal
    x2
    (append
     (remove-equal
      x2
      (put-assoc-equal
       (fat32-filename-fix (car x3-path))
       (abs-file
        (abs-file->dir-ent
         (cdr (assoc-equal (fat32-filename-fix (car x3-path))
                           abs-file-alist1)))
        (context-apply
         (abs-file->contents
          (cdr (assoc-equal (fat32-filename-fix (car x3-path))
                            abs-file-alist1)))
         abs-file-alist3 x3 (cdr x3-path)))
       abs-file-alist1))
     abs-file-alist2)))
  :instructions (:promote (:dive 2) := :top :bash)
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (integerp x2)
          (<= 0 x2)
          (member-equal x2 abs-file-alist1)
          (not (member-equal x2 (abs-addrs abs-file-alist2))))
     (not
      (equal
       (append
        (remove-equal
         x2
         (put-assoc-equal
          (fat32-filename-fix (car x3-path))
          (abs-file
           (abs-file->dir-ent
            (cdr (assoc-equal (fat32-filename-fix (car x3-path))
                              abs-file-alist1)))
           (context-apply
            (abs-file->contents
             (cdr (assoc-equal (fat32-filename-fix (car x3-path))
                               abs-file-alist1)))
            abs-file-alist3 x3 (cdr x3-path)))
          abs-file-alist1))
        abs-file-alist2)
       (put-assoc-equal
        (fat32-filename-fix (car x3-path))
        (abs-file
         (abs-file->dir-ent
          (cdr (assoc-equal (fat32-filename-fix (car x3-path))
                            abs-file-alist1)))
         (context-apply
          (abs-file->contents
           (cdr (assoc-equal (fat32-filename-fix (car x3-path))
                             abs-file-alist1)))
          abs-file-alist3 x3 (cdr x3-path)))
        abs-file-alist1)))))))

(defthm
  context-apply-ok-of-context-apply-lemma-3
  (implies
   (and
    (integerp x3)
    (equal
     (put-assoc-equal
      (fat32-filename-fix (car x2-path))
      (abs-file
       (abs-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                                            abs-file-alist1)))
       (context-apply
        (abs-file->contents
         (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                           abs-file-alist1)))
        abs-file-alist2 x2 (cdr x2-path)))
      abs-file-alist1)
     abs-file-alist1)
    (fat32-filename-fix (car x2-path)))
   (equal
    (put-assoc-equal
     (fat32-filename-fix (car x2-path))
     (abs-file
      (abs-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                                           abs-file-alist1)))
      (context-apply (abs-file->contents
                      (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                                        abs-file-alist1)))
                     abs-file-alist2 x2 (cdr x2-path)))
     (remove-equal x3 abs-file-alist1))
    (remove-equal x3 abs-file-alist1)))
  :instructions
  (:promote
   (:dive 1)
   (:claim
    (and
     (consp (assoc-equal (fat32-filename-fix (car x2-path))
                         (remove-equal x3 abs-file-alist1)))
     (equal
      (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                        (remove-equal x3 abs-file-alist1)))
      (abs-file
       (abs-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                                            abs-file-alist1)))
       (context-apply
        (abs-file->contents
         (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                           abs-file-alist1)))
        abs-file-alist2 x2 (cdr x2-path)))))
    :hints :none)
   (:rewrite (:rewrite put-assoc-equal-without-change . 2))
   :top
   :s :bash))

(defthm
  context-apply-ok-of-context-apply-lemma-4
  (implies
   (and
    (not (equal (fat32-filename-fix (car x2-path))
                (fat32-filename-fix (car x3-path))))
    (equal
     (put-assoc-equal
      (fat32-filename-fix (car x2-path))
      (abs-file
       (abs-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                                            abs-file-alist1)))
       (context-apply
        (abs-file->contents
         (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                           abs-file-alist1)))
        abs-file-alist2 x2 (cdr x2-path)))
      abs-file-alist1)
     abs-file-alist1))
   (equal
    (put-assoc-equal
     (fat32-filename-fix (car x2-path))
     (abs-file
      (abs-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                                           abs-file-alist1)))
      (context-apply (abs-file->contents
                      (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                                        abs-file-alist1)))
                     abs-file-alist2 x2 (cdr x2-path)))
     (put-assoc-equal
      (fat32-filename-fix (car x3-path))
      (abs-file
       (abs-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car x3-path))
                                            abs-file-alist1)))
       (context-apply
        (abs-file->contents
         (cdr (assoc-equal (fat32-filename-fix (car x3-path))
                           abs-file-alist1)))
        abs-file-alist3 x3 (cdr x3-path)))
      abs-file-alist1))
    (put-assoc-equal
     (fat32-filename-fix (car x3-path))
     (abs-file
      (abs-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car x3-path))
                                           abs-file-alist1)))
      (context-apply (abs-file->contents
                      (cdr (assoc-equal (fat32-filename-fix (car x3-path))
                                        abs-file-alist1)))
                     abs-file-alist3 x3 (cdr x3-path)))
     abs-file-alist1)))
  :instructions
  (:promote
   (:dive 1)
   (:claim
    (and
     (consp
      (assoc-equal
       (fat32-filename-fix (car x2-path))
       (put-assoc-equal
        (fat32-filename-fix (car x3-path))
        (abs-file
         (abs-file->dir-ent
          (cdr (assoc-equal (fat32-filename-fix (car x3-path))
                            abs-file-alist1)))
         (context-apply
          (abs-file->contents
           (cdr (assoc-equal (fat32-filename-fix (car x3-path))
                             abs-file-alist1)))
          abs-file-alist3 x3 (cdr x3-path)))
        abs-file-alist1)))
     (equal
      (cdr
       (assoc-equal
        (fat32-filename-fix (car x2-path))
        (put-assoc-equal
         (fat32-filename-fix (car x3-path))
         (abs-file
          (abs-file->dir-ent
           (cdr (assoc-equal (fat32-filename-fix (car x3-path))
                             abs-file-alist1)))
          (context-apply
           (abs-file->contents
            (cdr (assoc-equal (fat32-filename-fix (car x3-path))
                              abs-file-alist1)))
           abs-file-alist3 x3 (cdr x3-path)))
         abs-file-alist1)))
      (abs-file
       (abs-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                                            abs-file-alist1)))
       (context-apply
        (abs-file->contents
         (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                           abs-file-alist1)))
        abs-file-alist2 x2 (cdr x2-path)))))
    :hints :none)
   (:rewrite (:rewrite put-assoc-equal-without-change . 2))
   :top
   :s :bash))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies (and (natp x2)
                   (natp x3)
                   (not (equal x2 x3))
                   (abs-fs-p abs-file-alist1)
                   (abs-fs-p abs-file-alist2)
                   (abs-fs-p abs-file-alist3)
                   (abs-fs-p (context-apply abs-file-alist1
                                            abs-file-alist3 x3 x3-path))
                   (not (member-equal x2 (abs-addrs (abs-fs-fix abs-file-alist2))))
                   (not (member-equal x2 (abs-addrs (abs-fs-fix abs-file-alist3)))))
              (iff (context-apply-ok (context-apply abs-file-alist1
                                                    abs-file-alist3 x3 x3-path)
                                     abs-file-alist2 x2 x2-path)
                   (context-apply-ok abs-file-alist1
                                     abs-file-alist2 x2 x2-path)))
     :hints
     (("goal"
       :in-theory (e/d (context-apply-ok
                        context-apply put-assoc-equal-match)
                       ((:definition no-duplicatesp-equal)
                        (:rewrite abs-file-alist-p-correctness-1)
                        (:rewrite abs-addrs-of-context-apply-3)
                        (:definition abs-complete-definition)
                        (:rewrite
                         abs-file-contents-p-when-m1-file-contents-p)
                        (:rewrite
                         abs-addrs-of-context-apply-1-lemma-4)))
       :induct (mv (context-apply abs-file-alist1
                                  abs-file-alist2 x2 x2-path)
                   (fat32-filename-list-prefixp x2-path x3-path))
       :expand ((:free (abs-file-alist1 abs-file-alist2 x2)
                       (context-apply abs-file-alist1
                                      abs-file-alist2 x2 x2-path))
                (:with (:rewrite assoc-equal-of-append-1)
                       (assoc-equal (fat32-filename-fix (car x2-path))
                                    (append (remove-equal x3 abs-file-alist1)
                                            abs-file-alist3)))
                (context-apply abs-file-alist1
                               abs-file-alist3 x3 x3-path)
                (:free (abs-file-alist1 abs-file-alist3 x3)
                       (context-apply abs-file-alist1
                                      abs-file-alist3 x3 x3-path)))))))

  (defthm
    context-apply-ok-of-context-apply-1
    (implies (and (not (equal (nfix x2) (nfix x3)))
                  (abs-fs-p (context-apply abs-file-alist1
                                           abs-file-alist3 x3 x3-path))
                  (not (member-equal (nfix x2)
                                     (abs-addrs (abs-fs-fix abs-file-alist2))))
                  (not (member-equal (nfix x2)
                                     (abs-addrs (abs-fs-fix abs-file-alist3)))))
             (iff (context-apply-ok (context-apply abs-file-alist1
                                                   abs-file-alist3 x3 x3-path)
                                    abs-file-alist2 x2 x2-path)
                  (context-apply-ok abs-file-alist1
                                    abs-file-alist2 x2 x2-path)))
    :hints
    (("goal" :in-theory (disable nfix)
      :use (:instance lemma (x2 (nfix x2))
                      (x3 (nfix x3))
                      (abs-file-alist1 (abs-fs-fix abs-file-alist1))
                      (abs-file-alist2 (abs-fs-fix abs-file-alist2))
                      (abs-file-alist3 (abs-fs-fix abs-file-alist3)))))))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies (and (abs-fs-p y)
                   (abs-fs-p z)
                   (abs-complete y)
                   (abs-complete z)
                   (natp y-var)
                   (natp z-var)
                   (not (equal (nfix y-var) (nfix z-var)))
                   (not (intersectp-equal (names-at y nil)
                                          (names-at z nil)))
                   (not (intersectp-equal (names-at y nil)
                                          (names-at x
                                                    y-path)))
                   (not (intersectp-equal (names-at z nil)
                                          (names-at x
                                                    y-path))))
              (absfat-subsetp (context-apply (context-apply x y y-var y-path)
                                             z z-var y-path)
                              (context-apply (context-apply x z z-var y-path)
                                             y y-var y-path)))
     :hints (("goal" :in-theory (enable context-apply
                                        context-apply-ok names-at)))))

  (defthm
    context-apply-of-context-apply-lemma-1
    (implies (and (abs-complete (abs-fs-fix y))
                  (abs-complete (abs-fs-fix z))
                  (not (equal (nfix y-var) (nfix z-var)))
                  (not (intersectp-equal (names-at y nil)
                                         (names-at z nil)))
                  (not (intersectp-equal (names-at y nil)
                                         (names-at x
                                                   y-path)))
                  (not (intersectp-equal (names-at z nil)
                                         (names-at x
                                                   y-path))))
             (absfat-subsetp (context-apply (context-apply x y y-var y-path)
                                            z z-var y-path)
                             (context-apply (context-apply x z z-var y-path)
                                            y y-var y-path)))
    :hints (("goal" :use (:instance lemma (y (abs-fs-fix y))
                                    (z (abs-fs-fix z))
                                    (y-var (nfix y-var))
                                    (z-var (nfix z-var)))))))

(defthm
  context-apply-of-context-apply-lemma-2
  (implies (and (context-apply-ok x z z-var z-path)
                (not (intersectp-equal (names-at z nil)
                                       (names-at x z-path)))
                (not (prefixp (fat32-filename-list-fix z-path)
                              (fat32-filename-list-fix y-path)))
                (not (intersectp-equal (names-at y nil)
                                       (names-at x y-path)))
                (natp y-var)
                (natp z-var))
           (absfat-subsetp (context-apply (context-apply x z z-var z-path)
                                          y y-var y-path)
                           (context-apply (context-apply x y y-var y-path)
                                          z z-var z-path)))
  :hints
  (("goal"
    :in-theory
    (e/d (context-apply context-apply-ok
                        names-at put-assoc-of-remove)
         ((:definition no-duplicatesp-equal)
          (:rewrite abs-addrs-of-context-apply-3)
          (:rewrite abs-file-contents-p-when-m1-file-contents-p)
          (:rewrite m1-file-contents-p-correctness-1)
          (:definition member-equal)
          (:rewrite abs-addrs-of-context-apply-1-lemma-4)
          (:definition assoc-equal)
          (:rewrite context-apply-ok-when-absfat-equiv-lemma-4)
          (:type-prescription abs-directory-file-p-when-m1-file-p-lemma-1)))
    :induct (mv (fat32-filename-list-prefixp z-path y-path)
                (context-apply x z z-var z-path)
                (context-apply x y y-var y-path)))
   ("subgoal *1/3" :expand ((:free (x y y-var)
                                   (context-apply x y y-var y-path))
                            (:free (x z z-var)
                                   (context-apply x z z-var z-path)))
    :cases ((null (fat32-filename-fix (car z-path)))))))

(defthm
  context-apply-of-context-apply-lemma-3
  (implies (and (context-apply-ok x z z-var z-path)
                (not (intersectp-equal (names-at z nil)
                                       (names-at x
                                                 z-path)))
                (not (prefixp (fat32-filename-list-fix z-path)
                              (fat32-filename-list-fix y-path)))
                (not (intersectp-equal (names-at y nil)
                                       (names-at x
                                                 y-path))))
           (absfat-subsetp (context-apply (context-apply x y y-var y-path)
                                          z z-var z-path)
                           (context-apply (context-apply x z z-var z-path)
                                          y y-var y-path)))
  :hints
  (("goal" :in-theory
    (e/d (context-apply context-apply-ok
                        names-at put-assoc-of-remove)
         (nfix (:definition no-duplicatesp-equal)
               (:rewrite abs-addrs-of-context-apply-3)
               (:rewrite abs-file-contents-p-when-m1-file-contents-p)
               (:rewrite m1-file-contents-p-correctness-1)
               (:definition member-equal)
               (:rewrite abs-addrs-of-context-apply-1-lemma-4)
               (:definition assoc-equal)
               (:rewrite context-apply-ok-when-absfat-equiv-lemma-4)))
    :induct (mv (fat32-filename-list-prefixp z-path y-path)
                (context-apply x z z-var z-path)
                (context-apply x y y-var y-path)))
   ("subgoal *1/3" :expand ((:free (x y y-var)
                                   (context-apply x y y-var y-path))
                            (:free (x z z-var)
                                   (context-apply x z z-var z-path)))
    :cases ((null (fat32-filename-fix (car z-path)))))))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies
      (and
       (abs-fs-p x)
       (abs-fs-p y)
       (abs-fs-p z)
       (abs-complete (abs-fs-fix y))
       (abs-complete (abs-fs-fix z))
       (context-apply-ok x y y-var y-path)
       (context-apply-ok x z z-var z-path)
       (not (equal (nfix y-var) (nfix z-var)))
       (abs-no-dups-p (context-apply (context-apply x z z-var z-path)
                                     y y-var y-path))
       (natp y-var)
       (natp z-var)
       (not (intersectp-equal (names-at y nil)
                              (names-at x y-path)))
       (not (intersectp-equal (names-at z nil)
                              (names-at x z-path)))
       (or
        (not (prefixp (fat32-filename-list-fix y-path)
                      (fat32-filename-list-fix z-path)))
        (not
         (intersectp-equal (names-at z nil)
                           (names-at y (nthcdr (len y-path) z-path))))))
      (absfat-equiv (context-apply (context-apply x z z-var z-path)
                                   y y-var y-path)
                    (context-apply (context-apply x y y-var y-path)
                                   z z-var z-path)))
     :hints (("goal" :in-theory (e/d (list-equiv absfat-equiv)
                                     ((:rewrite prefixp-when-equal-lengths)
                                      len-when-prefixp))
              :use ((:instance (:rewrite prefixp-when-equal-lengths)
                               (y (fat32-filename-list-fix z-path))
                               (x (fat32-filename-list-fix y-path)))
                    (:instance len-when-prefixp
                               (x (fat32-filename-list-fix y-path))
                               (y (fat32-filename-list-fix z-path)))
                    (:instance len-when-prefixp
                               (x (fat32-filename-list-fix z-path))
                               (y (fat32-filename-list-fix y-path))))
              :do-not-induct t
              :expand
              ((:with
                ABS-FS-FIX-WHEN-ABS-FS-P
                (ABS-FS-FIX (CONTEXT-APPLY (CONTEXT-APPLY X Y Y-VAR Y-PATH)
                                           Z Z-VAR Z-PATH)))
               (:with
                ABS-FS-FIX-WHEN-ABS-FS-P
                (ABS-FS-FIX (CONTEXT-APPLY (CONTEXT-APPLY X Z Z-VAR Z-PATH)
                                           Y Y-VAR Y-PATH))))))))

  ;; This theorem is interesting because it would really be awesome if it could
  ;; be made a congruence, but it's fairly obvious why it can't - there's no
  ;; way to ensure that abs-file-alist2 and abs-file-alist3 won't have names in
  ;; common. A weirdly restricted version of it could exist if it was accessing
  ;; elements from a frame fixed (by an appropriate fixing function) to have
  ;; separate elements.
  (defthmd
    context-apply-of-context-apply-1
    (implies
     (and
      (abs-complete (abs-fs-fix y))
      (abs-complete (abs-fs-fix z))
      (not (equal (nfix y-var) (nfix z-var)))
      (abs-no-dups-p (context-apply (context-apply x z z-var z-path)
                                    y y-var y-path))
      (not (intersectp-equal (names-at y nil)
                             (names-at x y-path)))
      (not (intersectp-equal (names-at z nil)
                             (names-at x z-path)))
      (or
       (not (prefixp (fat32-filename-list-fix y-path)
                     (fat32-filename-list-fix z-path)))
       (not
        (intersectp-equal (names-at z nil)
                          (names-at y (nthcdr (len y-path) z-path))))))
     (absfat-equiv (context-apply (context-apply x z z-var z-path)
                                  y y-var y-path)
                   (context-apply (context-apply x y y-var y-path)
                                  z z-var z-path)))
    :hints (("goal" :use ((:instance lemma (x (abs-fs-fix x))
                                     (y (abs-fs-fix y))
                                     (z (abs-fs-fix z))
                                     (y-var (nfix y-var))
                                     (z-var (nfix z-var))))
             :in-theory (disable nfix)))))

(defthm
  partial-collapse-correctness-lemma-3
  (implies
   (and
    (not
     (equal
      (context-apply
       (context-apply
        (abs-file->contents
         (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                           abs-file-alist1)))
        abs-file-alist3 x3 (cdr x3-path))
       abs-file-alist2 x2 (cdr x2-path))
      (context-apply (abs-file->contents
                      (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                                        abs-file-alist1)))
                     abs-file-alist3 x3 (cdr x3-path))))
    (abs-file-alist-p abs-file-alist2)
    (abs-file-alist-p abs-file-alist3)
    (abs-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                                            abs-file-alist1))))
   (not
    (equal
     (put-assoc-equal
      (fat32-filename-fix (car x2-path))
      (abs-file
       (abs-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                                            abs-file-alist1)))
       (context-apply
        (context-apply
         (abs-file->contents
          (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                            abs-file-alist1)))
         abs-file-alist3 x3 (cdr x3-path))
        abs-file-alist2 x2 (cdr x2-path)))
      (put-assoc-equal
       (fat32-filename-fix (car x2-path))
       (abs-file
        (abs-file->dir-ent
         (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                           abs-file-alist1)))
        (context-apply
         (abs-file->contents
          (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                            abs-file-alist1)))
         abs-file-alist3 x3 (cdr x3-path)))
       abs-file-alist1))
     (put-assoc-equal
      (fat32-filename-fix (car x2-path))
      (abs-file
       (abs-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                                            abs-file-alist1)))
       (context-apply
        (abs-file->contents
         (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                           abs-file-alist1)))
        abs-file-alist3 x3 (cdr x3-path)))
      abs-file-alist1))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite put-assoc-equal-without-change . 1))
    :use
    (:instance
     (:rewrite put-assoc-equal-without-change . 1)
     (alist abs-file-alist1)
     (val
      (abs-file
       (abs-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                                            abs-file-alist1)))
       (context-apply
        (abs-file->contents
         (cdr (assoc-equal (fat32-filename-fix (car x2-path))
                           abs-file-alist1)))
        abs-file-alist2 x2 (cdr x2-path))))
     (name (fat32-filename-fix (car x2-path)))))))

(defthm
  partial-collapse-correctness-lemma-4
  (implies
   (absfat-equiv abs-file-alist1 abs-file-alist2)
   (equal
    (abs-directory-file-p
     (cdr (assoc-equal (fat32-filename-fix (car x-path))
                       (abs-fs-fix abs-file-alist1))))
    (abs-directory-file-p
     (cdr (assoc-equal (fat32-filename-fix (car x-path))
                       (abs-fs-fix abs-file-alist2))))))
  :hints
  (("goal"
    :in-theory
    (disable absfat-equiv-implies-set-equiv-names-at-1-lemma-4)
    :use
    ((:instance absfat-equiv-implies-set-equiv-names-at-1-lemma-4
                (abs-file-alist1 (abs-fs-fix abs-file-alist1))
                (abs-file-alist2 (abs-fs-fix abs-file-alist2)))
     (:instance
      absfat-equiv-implies-set-equiv-names-at-1-lemma-4
      (abs-file-alist1 (abs-fs-fix abs-file-alist2))
      (abs-file-alist2 (abs-fs-fix abs-file-alist1))))))
  :rule-classes :congruence)

(defthmd
  partial-collapse-correctness-lemma-8
  (implies (and (abs-file-alist-p y)
                (consp (assoc-equal (fat32-filename-fix (car z-path))
                                    x))
                (consp (assoc-equal (fat32-filename-fix (car z-path))
                                    y)))
           (intersectp-equal (remove-equal nil (strip-cars x))
                             (remove-equal nil (strip-cars y))))
  :hints (("goal" :use (:instance (:rewrite intersectp-member)
                                  (a (fat32-filename-fix (car z-path)))
                                  (y (remove-equal nil (strip-cars y)))
                                  (x (remove-equal nil (strip-cars x)))))))

(defthm
  partial-collapse-correctness-lemma-9
  (implies
   (and
    (absfat-subsetp
     (context-apply
      (context-apply
       (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                             x)))
       y y-var (cdr y-path))
      z z-var (cdr y-path))
     (context-apply
      (context-apply
       (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                             x)))
       z z-var (cdr y-path))
      y y-var (cdr y-path)))
    (abs-file-alist-p x)
    (abs-no-dups-p x))
   (absfat-subsetp
    (put-assoc-equal
     (fat32-filename-fix (car y-path))
     (abs-file
      (abs-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                           x)))
      (context-apply
       (context-apply (abs-file->contents
                       (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                         x)))
                      y y-var (cdr y-path))
       z z-var (cdr y-path)))
     x)
    (put-assoc-equal
     (fat32-filename-fix (car y-path))
     (abs-file
      (abs-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                           x)))
      (context-apply
       (context-apply (abs-file->contents
                       (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                         x)))
                      z z-var (cdr y-path))
       y y-var (cdr y-path)))
     x)))
  :hints
  (("goal"
    :in-theory (e/d (context-apply context-apply-ok)
                    ((:rewrite absfat-subsetp-of-put-assoc-1)))
    :use
    ((:instance
      (:rewrite absfat-subsetp-of-put-assoc-1)
      (abs-file-alist2
       (put-assoc-equal
        (fat32-filename-fix (car y-path))
        (abs-file
         (abs-file->dir-ent
          (cdr (assoc-equal (fat32-filename-fix (car y-path))
                            x)))
         (context-apply
          (context-apply
           (abs-file->contents
            (cdr (assoc-equal (fat32-filename-fix (car y-path))
                              x)))
           z z-var (cdr y-path))
          y y-var (cdr y-path)))
        x))
      (abs-file-alist1 x)
      (val
       (abs-file
        (abs-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                             x)))
        (context-apply
         (context-apply
          (abs-file->contents
           (cdr (assoc-equal (fat32-filename-fix (car y-path))
                             x)))
          y y-var (cdr y-path))
         z z-var (cdr y-path))))
      (name (fat32-filename-fix (car y-path))))))))

(defthm
  partial-collapse-correctness-lemma-10
  (implies
   (not
    (intersectp-equal
     (names-at z nil)
     (names-at
      (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car z-path))
                                            x)))
      (cdr z-path))))
   (abs-no-dups-p
    (abs-file-contents-fix
     (context-apply (abs-file->contents$inline
                     (cdr (assoc-equal (fat32-filename-fix (car z-path))
                                       x)))
                    z z-var (cdr z-path))))))

(defthm
  partial-collapse-correctness-lemma-12
  (implies
   (and
    (absfat-subsetp
     (context-apply
      (context-apply
       (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                             x)))
       z z-var (cdr z-path))
      y y-var (cdr y-path))
     (context-apply
      (context-apply
       (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                             x)))
       y y-var (cdr y-path))
      z z-var (cdr z-path)))
    (m1-file-alist-p y)
    (m1-file-alist-p z)
    (abs-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                            x))))
   (absfat-subsetp
    (abs-file-contents-fix
     (context-apply
      (context-apply (abs-file->contents$inline
                      (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                        x)))
                     z z-var (cdr z-path))
      y y-var (cdr y-path)))
    (abs-file-contents-fix
     (context-apply
      (context-apply (abs-file->contents$inline
                      (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                        x)))
                     y y-var (cdr y-path))
      z z-var (cdr z-path))))))

(defthm
  partial-collapse-correctness-lemma-13
  (implies
   (not
    (intersectp-equal
     (names-at z nil)
     (names-at
      (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car z-path))
                                            x)))
      (cdr y-path))))
   (absfat-subsetp
    (abs-file-contents-fix
     (context-apply (abs-file->contents$inline
                     (cdr (assoc-equal (fat32-filename-fix (car z-path))
                                       x)))
                    z z-var (cdr y-path)))
    (abs-file-contents-fix
     (context-apply (abs-file->contents$inline
                     (cdr (assoc-equal (fat32-filename-fix (car z-path))
                                       x)))
                    z z-var (cdr y-path))))))

(defthm
  partial-collapse-correctness-lemma-56
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car z-path))
                                            x)))
    (abs-fs-p x)
    (abs-fs-p z)
    (not
     (intersectp-equal
      (strip-cars z)
      (remove-equal
       nil
       (strip-cars (abs-file->contents
                    (cdr (assoc-equal (fat32-filename-fix (car z-path))
                                      x))))))))
   (absfat-subsetp
    (abs-file-contents-fix
     (binary-append
      (remove-equal z-var
                    (abs-file->contents$inline
                     (cdr (assoc-equal (fat32-filename-fix (car z-path))
                                       x))))
      z))
    (abs-file-contents-fix
     (binary-append
      (remove-equal z-var
                    (abs-file->contents$inline
                     (cdr (assoc-equal (fat32-filename-fix (car z-path))
                                       x))))
      z)))))

(defthm
  partial-collapse-correctness-lemma-57
  (implies
   (and
    (fat32-filename-fix (car z-path))
    (consp (assoc-equal (fat32-filename-fix (car z-path))
                        x))
    (abs-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car z-path))
                                            x)))
    (abs-fs-p x)
    (abs-fs-p y)
    (abs-fs-p z)
    (not
     (intersectp-equal
      (strip-cars z)
      (remove-equal
       nil
       (strip-cars (abs-file->contents
                    (cdr (assoc-equal (fat32-filename-fix (car z-path))
                                      x)))))))
    (not (intersectp-equal (strip-cars y)
                           (remove-equal nil (strip-cars x))))
    (integerp y-var))
   (absfat-subsetp
    y
    (append
     (put-assoc-equal
      (fat32-filename-fix (car z-path))
      (abs-file
       (abs-file->dir-ent (cdr (assoc-equal (fat32-filename-fix (car z-path))
                                            x)))
       (append
        (remove-equal z-var
                      (abs-file->contents
                       (cdr (assoc-equal (fat32-filename-fix (car z-path))
                                         x))))
        z))
      (remove-equal y-var x))
     y)))
  :hints
  (("goal"
    :in-theory (disable (:rewrite absfat-subsetp-of-append-2))
    :use
    ((:instance
      (:rewrite absfat-subsetp-of-append-2)
      (z y)
      (y
       (put-assoc-equal
        (fat32-filename-fix (car z-path))
        (abs-file
         (abs-file->dir-ent
          (cdr (assoc-equal (fat32-filename-fix (car z-path))
                            x)))
         (append (remove-equal
                  z-var
                  (abs-file->contents
                   (cdr (assoc-equal (fat32-filename-fix (car z-path))
                                     x))))
                 z))
        (remove-equal y-var x)))
      (x y))))))

(defthm
  partial-collapse-correctness-lemma-31
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car z-path))
                                            x)))
    (abs-fs-p x)
    (abs-fs-p z)
    (not
     (intersectp-equal
      (strip-cars z)
      (remove-equal
       nil
       (strip-cars (abs-file->contents
                    (cdr (assoc-equal (fat32-filename-fix (car z-path))
                                      x))))))))
   (absfat-subsetp
    (abs-file-contents-fix
     (binary-append
      (remove-equal z-var
                    (abs-file->contents$inline
                     (cdr (assoc-equal (fat32-filename-fix (car z-path))
                                       x))))
      z))
    (abs-file-contents-fix
     (binary-append
      (remove-equal z-var
                    (abs-file->contents$inline
                     (cdr (assoc-equal (fat32-filename-fix (car z-path))
                                       x))))
      z)))))

(defthm
  partial-collapse-correctness-lemma-94
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car z-path))
                                            x)))
    (abs-fs-p x)
    (abs-fs-p z)
    (not
     (intersectp-equal
      (strip-cars z)
      (remove-equal
       nil
       (strip-cars (abs-file->contents
                    (cdr (assoc-equal (fat32-filename-fix (car z-path))
                                      x))))))))
   (abs-no-dups-p
    (abs-file-contents-fix
     (binary-append
      (remove-equal z-var
                    (abs-file->contents$inline
                     (cdr (assoc-equal (fat32-filename-fix (car z-path))
                                       x))))
      z)))))

(defthm
  partial-collapse-correctness-lemma-11
  (implies
   (and
    (absfat-subsetp
     (context-apply
      (context-apply
       (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                             x)))
       y y-var (cdr y-path))
      z z-var (cdr z-path))
     (context-apply
      (context-apply
       (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                             x)))
       z z-var (cdr z-path))
      y y-var (cdr y-path)))
    (m1-file-alist-p y)
    (m1-file-alist-p z)
    (abs-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                            x))))
   (absfat-subsetp
    (abs-file-contents-fix
     (context-apply
      (context-apply (abs-file->contents$inline
                      (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                        x)))
                     y y-var (cdr y-path))
      z z-var (cdr z-path)))
    (abs-file-contents-fix
     (context-apply
      (context-apply (abs-file->contents$inline
                      (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                        x)))
                     z z-var (cdr z-path))
      y y-var (cdr y-path))))))

(defthm
  partial-collapse-correctness-lemma-14
  (implies
   (and
    (abs-no-dups-p (frame->root frame1))
    (frame-p (frame->frame frame1))
    (no-duplicatesp-equal (strip-cars (frame->frame frame1)))
    (absfat-equiv (frame->root frame1)
                  (frame->root frame2))
    (< 0 (1st-complete (frame->frame frame1)))
    (context-apply-ok
     (frame->root frame2)
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                       (frame->frame frame1))))
     (1st-complete (frame->frame frame1))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                        (frame->frame frame1))))))
   (context-apply-ok
    (frame->root frame1)
    (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                      (frame->frame frame1))))
    (1st-complete (frame->frame frame1))
    (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                       (frame->frame frame1))))))
  :hints
  (("goal"
    :use
    (:instance
     (:rewrite context-apply-ok-when-absfat-equiv-1)
     (abs-file-alist2 (frame->root frame2))
     (x-path
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                         (frame->frame frame1)))))
     (x (1st-complete (frame->frame frame1)))
     (abs-file-alist3
      (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                        (frame->frame frame1)))))
     (abs-file-alist1 (frame->root frame1))))))

(defthm
  partial-collapse-correctness-lemma-19
  (implies
   (and
    (< 0 (1st-complete (frame->frame frame1)))
    (context-apply-ok
     (frame->root frame1)
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                       (frame->frame frame1))))
     (1st-complete (frame->frame frame1))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                        (frame->frame frame1)))))
    (abs-no-dups-p (frame->root frame1))
    (frame-p (frame->frame frame1))
    (no-duplicatesp-equal (strip-cars (frame->frame frame1)))
    (absfat-equiv (frame->root frame1)
                  (frame->root frame2)))
   (context-apply-ok
    (frame->root frame2)
    (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                      (frame->frame frame1))))
    (1st-complete (frame->frame frame1))
    (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                       (frame->frame frame1))))))
  :hints
  (("goal"
    :use
    (:instance
     (:rewrite context-apply-ok-when-absfat-equiv-1)
     (x-path
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                         (frame->frame frame1)))))
     (x (1st-complete (frame->frame frame1)))
     (abs-file-alist3
      (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                        (frame->frame frame1)))))
     (abs-file-alist1 (frame->root frame2))
     (abs-file-alist2 (frame->root frame1))))))

(defthm
  partial-collapse-correctness-lemma-5
  (implies
   (absfat-equiv (frame->root frame1)
                 (frame->root frame2))
   (absfat-equiv
    (context-apply
     (frame->root frame1)
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                       (frame->frame frame1))))
     (1st-complete (frame->frame frame1))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                        (frame->frame frame1)))))
    (context-apply
     (frame->root frame2)
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                       (frame->frame frame1))))
     (1st-complete (frame->frame frame1))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                        (frame->frame frame1)))))))
  :hints
  (("goal"
    :in-theory (disable absfat-equiv-of-context-apply-2)
    :use
    (:instance
     absfat-equiv-of-context-apply-2
     (abs-file-alist2 (frame->root frame2))
     (x-path
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                         (frame->frame frame1)))))
     (x (1st-complete (frame->frame frame1)))
     (abs-file-alist3
      (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                        (frame->frame frame1)))))
     (abs-file-alist1 (frame->root frame1))))))

(encapsulate
  ()

  (local
   (defun
       induction-scheme (frame1 frame2)
     (declare (xargs :verify-guards nil
                     :measure (len (frame->frame frame1))))
     (cond
      ((and
        (not (atom (frame->frame frame1)))
        (not (zp (1st-complete (frame->frame frame1))))
        (not (zp (1st-complete-src (frame->frame frame1))))
        (not
         (or
          (equal (1st-complete-src (frame->frame frame1))
                 (1st-complete (frame->frame frame1)))
          (atom
           (assoc-equal (1st-complete-src (frame->frame frame1))
                        (remove-assoc-equal (1st-complete (frame->frame frame1))
                                            (frame->frame frame1))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal (1st-complete-src (frame->frame frame1))
                        (remove-assoc-equal (1st-complete (frame->frame frame1))
                                            (frame->frame frame1)))))
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                            (frame->frame frame1)))))
        (context-apply-ok
         (frame-val->dir
          (cdr
           (assoc-equal (1st-complete-src (frame->frame frame1))
                        (remove-assoc-equal (1st-complete (frame->frame frame1))
                                            (frame->frame frame1)))))
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                           (frame->frame frame1))))
         (1st-complete (frame->frame frame1))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal (1st-complete-src (frame->frame frame1))
                          (remove-assoc-equal (1st-complete (frame->frame frame1))
                                              (frame->frame frame1))))))
          (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                             (frame->frame frame1)))))))
       (induction-scheme
        (frame-with-root
         (frame->root frame1)
         (put-assoc-equal
          (1st-complete-src (frame->frame frame1))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal (1st-complete-src (frame->frame frame1))
                              (frame->frame frame1))))
           (context-apply
            (frame-val->dir
             (cdr (assoc-equal
                   (1st-complete-src (frame->frame frame1))
                   (remove-assoc-equal (1st-complete (frame->frame frame1))
                                       (frame->frame frame1)))))
            (frame-val->dir
             (cdr (assoc-equal (1st-complete (frame->frame frame1))
                               (frame->frame frame1))))
            (1st-complete (frame->frame frame1))
            (nthcdr
             (len
              (frame-val->path
               (cdr (assoc-equal
                     (1st-complete-src (frame->frame frame1))
                     (remove-assoc-equal (1st-complete (frame->frame frame1))
                                         (frame->frame frame1))))))
             (frame-val->path
              (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                (frame->frame frame1))))))
           (frame-val->src
            (cdr (assoc-equal (1st-complete-src (frame->frame frame1))
                              (frame->frame frame1)))))
          (remove-assoc-equal (1st-complete (frame->frame frame1))
                              (frame->frame frame1))))
        (frame-with-root
         (frame->root frame2)
         (put-assoc-equal
          (1st-complete-src (frame->frame frame2))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal (1st-complete-src (frame->frame frame2))
                              (frame->frame frame2))))
           (context-apply
            (frame-val->dir
             (cdr (assoc-equal
                   (1st-complete-src (frame->frame frame2))
                   (remove-assoc-equal (1st-complete (frame->frame frame2))
                                       (frame->frame frame2)))))
            (frame-val->dir
             (cdr (assoc-equal (1st-complete (frame->frame frame2))
                               (frame->frame frame2))))
            (1st-complete (frame->frame frame2))
            (nthcdr
             (len
              (frame-val->path
               (cdr (assoc-equal
                     (1st-complete-src (frame->frame frame2))
                     (remove-assoc-equal (1st-complete (frame->frame frame2))
                                         (frame->frame frame2))))))
             (frame-val->path
              (cdr (assoc-equal (1st-complete (frame->frame frame2))
                                (frame->frame frame2))))))
           (frame-val->src
            (cdr (assoc-equal (1st-complete-src (frame->frame frame2))
                              (frame->frame frame2)))))
          (remove-assoc-equal (1st-complete (frame->frame frame2))
                              (frame->frame frame2))))))
      ((and
        (not (atom (frame->frame frame1)))
        (not (zp (1st-complete (frame->frame frame1))))
        (zp (1st-complete-src (frame->frame frame1)))
        (context-apply-ok
         (frame->root frame1)
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                           (frame->frame frame1))))
         (1st-complete (frame->frame frame1))
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                            (frame->frame frame1))))))
       (induction-scheme
        (frame-with-root
         (context-apply
          (frame->root frame1)
          (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                            (frame->frame frame1))))
          (1st-complete (frame->frame frame1))
          (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame1))
                                             (frame->frame frame1)))))
         (remove-assoc-equal (1st-complete (frame->frame frame1))
                             (frame->frame frame1)))
        (frame-with-root
         (context-apply
          (frame->root frame2)
          (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame2))
                                            (frame->frame frame2))))
          (1st-complete (frame->frame frame2))
          (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame2))
                                             (frame->frame frame2)))))
         (remove-assoc-equal (1st-complete (frame->frame frame2))
                             (frame->frame frame2)))))
      (t
       (mv frame1 frame2)))))

  (local
   (defthmd
     partial-collapse-correctness-lemma-24
     (implies (and (abs-no-dups-p (frame->root frame1))
                   (frame-p (frame->frame frame1))
                   (no-duplicatesp-equal (strip-cars (frame->frame frame1)))
                   (equal (frame->frame frame1)
                          (frame->frame frame2))
                   (absfat-equiv (frame->root frame1)
                                 (frame->root frame2))
                   (abs-separate (frame->frame frame1))
                   (dist-names (frame->root frame1)
                               nil (frame->frame frame1)))
              (and
               (absfat-equiv (mv-nth 0 (collapse frame1))
                             (mv-nth 0 (collapse frame2)))
               (equal (mv-nth 1 (collapse frame1))
                      (mv-nth 1 (collapse frame2)))))
     :hints (("goal" :in-theory (enable collapse)
              :induct (induction-scheme frame1 frame2))
             ("subgoal *1/3" :expand (collapse frame2))
             ("subgoal *1/2" :expand (collapse frame2)))))

  ;; This is important!
  (defthmd
    partial-collapse-correctness-lemma-20
    (implies (and (or (abs-no-dups-p (frame->root frame1))
                      (abs-no-dups-p (frame->root frame2)))
                  (frame-p (frame->frame frame1))
                  (no-duplicatesp-equal (strip-cars (frame->frame frame1)))
                  (equal (frame->frame frame1)
                         (frame->frame frame2))
                  (absfat-equiv (frame->root frame1)
                                (frame->root frame2))
                  (abs-separate (frame->frame frame1))
                  (or (dist-names (frame->root frame1)
                                  nil (frame->frame frame1))
                      (dist-names (frame->root frame2)
                                  nil (frame->frame frame2))))
             (and
              (absfat-equiv (mv-nth 0 (collapse frame1))
                            (mv-nth 0 (collapse frame2)))
              (equal (mv-nth 1 (collapse frame1))
                     (mv-nth 1 (collapse frame2)))))
    :hints (("goal" :in-theory (e/d (absfat-equiv)
                                    (absfat-equiv-implies-equal-dist-names-1))
             :do-not-induct t
             :use ((:instance
                    absfat-equiv-implies-equal-dist-names-1
                    (dir (frame->root frame1))
                    (dir-equiv (frame->root frame2))
                    (relpath nil)
                    (frame (frame->frame frame1)))
                   partial-collapse-correctness-lemma-24
                   (:instance partial-collapse-correctness-lemma-24
                              (frame1 frame2)
                              (frame2 frame1)))))))

(defthm
  partial-collapse-correctness-lemma-29
  (implies
   (and
    (equal
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
     (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
    (not (equal x (1st-complete (frame->frame frame))))
    (< 0 (1st-complete (frame->frame frame)))
    (abs-separate (frame->frame frame)))
   (not
    (intersectp-equal
     (names-at
      (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
      nil)
     (names-at
      (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
      nil))))
  :hints
  (("goal" :in-theory (disable abs-separate-correctness-1-lemma-14)
    :use (:instance abs-separate-correctness-1-lemma-14
                    (y (1st-complete (frame->frame frame)))
                    (frame (frame->frame frame))
                    (x x)))))

(defthm
  partial-collapse-correctness-lemma-30
  (implies
   (not
    (prefixp
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
     (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
   (not
    (equal
     (frame-val->path$inline
      (cdr (assoc-equal (1st-complete (frame->frame frame))
                        (frame->frame frame))))
     (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame))))))))

(defthm
  partial-collapse-correctness-lemma-32
  (implies
   (and
    (prefixp
     (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))
    (not
     (equal
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
      (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
   (not
    (prefixp
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
     (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
  :instructions
  (:promote
   (:dive 1)
   :top
   (:bash
    ("goal"
     :in-theory (e/d (list-equiv)
                     ((:rewrite prefixp-when-equal-lengths)))
     :use
     (:instance
      (:rewrite prefixp-when-equal-lengths)
      (y (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
      (x
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))))))))

(defthmd
  partial-collapse-correctness-lemma-21
  (implies (and (absfat-equiv root1 root2)
                (frame-p frame)
                (no-duplicatesp-equal (strip-cars frame))
                (abs-separate frame)
                (or (dist-names root1 nil frame)
                    (dist-names root2 nil frame)))
           (and
            (absfat-equiv (mv-nth 0
                                  (collapse (frame-with-root root1 frame)))
                          (mv-nth 0
                                  (collapse (frame-with-root root2 frame))))
            (equal (mv-nth 1
                           (collapse (frame-with-root root1 frame)))
                   (mv-nth 1
                           (collapse (frame-with-root root2 frame))))))
  :hints
  (("goal"
    :do-not-induct t
    :use ((:instance (:rewrite partial-collapse-correctness-lemma-20)
                     (frame1 (frame-with-root root1 frame))
                     (frame2 (frame-with-root root2 frame)))))))

;; This theorem is used in an :expand hint later...
(defthmd
  partial-collapse-correctness-lemma-22
  (implies
   (and
    (not (equal x (1st-complete (frame->frame frame))))
    (mv-nth
     1
     (collapse
      (frame-with-root
       (context-apply
        (context-apply
         (frame->root frame)
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
        (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
        x
        (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
       (remove-assoc-equal
        x
        (remove-assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))))
    (consp (assoc-equal x (frame->frame frame)))
    (not
     (consp
      (abs-addrs
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
    (< 0 (1st-complete (frame->frame frame)))
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (dist-names (frame->root frame)
                nil (frame->frame frame))
    (abs-separate (frame->frame frame))
    (abs-fs-p
     (context-apply
      (context-apply
       (frame->root frame)
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
       x
       (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
      (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
      (1st-complete (frame->frame frame))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))))
   (mv-nth
    1
    (collapse
     (frame-with-root
      (context-apply
       (context-apply
        (frame->root frame)
        (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
        x
        (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (1st-complete (frame->frame frame))
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
      (remove-assoc-equal
       x
       (remove-assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame)))))))
  :hints
  (("goal"
    :do-not-induct t
    :use
    ((:instance
      (:rewrite partial-collapse-correctness-lemma-20)
      (frame2
       (frame-with-root
        (context-apply
         (context-apply
          (frame->root frame)
          (frame-val->dir
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
          (1st-complete (frame->frame frame))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))))
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
         x
         (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
        (remove-assoc-equal
         x
         (remove-assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))))
      (frame1
       (frame-with-root
        (context-apply
         (context-apply
          (frame->root frame)
          (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
          x
          (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
        (remove-assoc-equal
         x
         (remove-assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
     (:instance
      (:rewrite context-apply-of-context-apply-1)
      (y-path (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
      (y-var x)
      (y (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
      (z-path
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
      (z-var (1st-complete (frame->frame frame)))
      (z (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame)))))
      (x (frame->root frame)))))))

(defthm
  partial-collapse-correctness-lemma-1
  (implies
   (and
    (not (zp x))
    (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
           0)
    (< 0
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
    (not
     (equal
      (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
      (1st-complete (frame->frame frame))))
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))
    (context-apply-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     (1st-complete (frame->frame frame))
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
    (not
     (equal
      x
      (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))))
    (mv-nth
     1
     (collapse
      (frame-with-root
       (context-apply
        (frame->root frame)
        (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
        x
        (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
       (put-assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame-val
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame))))
         (context-apply
          (frame-val->dir
           (cdr
            (assoc-equal
             (frame-val->src
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))
             (frame->frame frame))))
          (frame-val->dir
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
          (1st-complete (frame->frame frame))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src
                (cdr (assoc-equal (1st-complete (frame->frame frame))
                                  (frame->frame frame))))
               (frame->frame frame)))))
           (frame-val->path
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))
         (frame-val->src
          (cdr (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame)))))
        (remove-assoc-equal
         x
         (remove-assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))))))
    (< 0 (1st-complete (frame->frame frame))))
   (mv-nth
    1
    (collapse
     (frame-with-root
      (context-apply
       (frame->root frame)
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
       x
       (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
      (remove-assoc-equal x (frame->frame frame))))))
  :hints (("goal" :in-theory (enable 1st-complete-src collapse)
           :cases ((equal (1st-complete (frame->frame frame))
                          x))
           :do-not-induct t)))

(defthm
  partial-collapse-correctness-lemma-33
  (implies
   (and
    (not (equal x (1st-complete (frame->frame frame))))
    (absfat-equiv
     (mv-nth
      0
      (collapse
       (frame-with-root
        (context-apply
         (context-apply
          (frame->root frame)
          (frame-val->dir
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
          (1st-complete (frame->frame frame))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))))
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
         x
         (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
        (remove-assoc-equal
         x
         (remove-assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
     (mv-nth
      0
      (collapse
       (frame-with-root
        (context-apply
         (frame->root frame)
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
        (remove-assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))))
    (consp (assoc-equal x (frame->frame frame)))
    (not
     (consp
      (abs-addrs
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
    (< 0 (1st-complete (frame->frame frame)))
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (dist-names (frame->root frame)
                nil (frame->frame frame))
    (abs-separate (frame->frame frame)))
   (absfat-equiv
    (mv-nth
     0
     (collapse
      (frame-with-root
       (context-apply
        (context-apply
         (frame->root frame)
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
         x
         (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
        (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (1st-complete (frame->frame frame))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame)))))
       (remove-assoc-equal
        x
        (remove-assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))))
    (mv-nth
     0
     (collapse
      (frame-with-root
       (context-apply
        (frame->root frame)
        (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (1st-complete (frame->frame frame))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame)))))
       (remove-assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame)))))))
  :hints
  (("goal"
    :use
    ((:instance
      (:rewrite partial-collapse-correctness-lemma-21)
      (frame (remove-assoc-equal
              x
              (remove-assoc-equal (1st-complete (frame->frame frame))
                                  (frame->frame frame))))
      (root1
       (context-apply
        (context-apply
         (frame->root frame)
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
         x
         (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
        (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (1st-complete (frame->frame frame))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))))
      (root2
       (context-apply
        (context-apply
         (frame->root frame)
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
        (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
        x
        (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
     (:instance
      (:rewrite context-apply-of-context-apply-1)
      (y-path
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
      (y-var (1st-complete (frame->frame frame)))
      (y (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame)))))
      (z-path (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
      (z-var x)
      (z (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
      (x (frame->root frame))))
    :expand
    (:with
     abs-separate-of-put-assoc-lemma-14
     (dist-names
      (context-apply
       (context-apply
        (frame->root frame)
        (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
        x
        (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (1st-complete (frame->frame frame))
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
      nil
      (remove-assoc-equal
       x
       (remove-assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))))))

(defthm
  partial-collapse-correctness-lemma-40
  (implies
   (and (mv-nth 1 (collapse frame))
        (not (zp x)))
   (not (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               x)))
  :hints (("goal" :in-theory (enable collapse 1st-complete-src))))

(defthm
  partial-collapse-correctness-lemma-2
  (implies
   (and
    (not (zp x))
    (consp (assoc-equal x (frame->frame frame)))
    (abs-complete (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
    (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
    (mv-nth 1 (collapse frame))
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (dist-names (frame->root frame)
                nil (frame->frame frame))
    (abs-separate (frame->frame frame)))
   (and
    (mv-nth
     1
     (collapse
      (frame-with-root
       (context-apply
        (frame->root frame)
        (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
        x
        (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
       (remove-assoc-equal x (frame->frame frame)))))
    (absfat-equiv
     (mv-nth
      0
      (collapse
       (frame-with-root
        (context-apply
         (frame->root frame)
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
         x
         (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
        (remove-assoc-equal x (frame->frame frame)))))
     (mv-nth 0 (collapse frame)))))
  :hints
  (("goal" :in-theory
    (e/d (collapse abs-separate 1st-complete-src)
         ((:definition remove-assoc-equal)
          (:rewrite abs-file-alist-p-when-m1-file-alist-p)
          (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)))
    :induct (collapse frame))
   ("Subgoal *1/7'''"
    :expand
    ((COLLAPSE
      (FRAME-WITH-ROOT
       (CONTEXT-APPLY
        (FRAME->ROOT FRAME)
        (FRAME-VAL->DIR (CDR (ASSOC-EQUAL X (FRAME->FRAME FRAME))))
        X
        (FRAME-VAL->PATH (CDR (ASSOC-EQUAL X (FRAME->FRAME FRAME)))))
       (REMOVE-ASSOC-EQUAL X (FRAME->FRAME FRAME))))))
   ("subgoal *1/4"
    :expand
    ((collapse
      (frame-with-root
       (context-apply
        (frame->root frame)
        (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
        x
        (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
       (remove-assoc-equal x (frame->frame frame))))
     (:with
      partial-collapse-correctness-lemma-22
      (mv-nth
       '1
       (collapse
        (frame-with-root
         (context-apply
          (context-apply
           (frame->root frame)
           (frame-val->dir$inline (cdr (assoc-equal x (frame->frame frame))))
           x
           (frame-val->path$inline
            (cdr (assoc-equal x (frame->frame frame)))))
          (frame-val->dir$inline
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
          (1st-complete (frame->frame frame))
          (frame-val->path$inline
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))))
         (remove-assoc-equal
          x
          (remove-assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))))
    :cases ((equal x
                   (1st-complete (frame->frame frame)))))))

(defthm
  partial-collapse-correctness-lemma-38
  (implies
   (and (not (zp (1st-complete-under-pathname frame pathname)))
        (no-duplicatesp-equal (strip-cars frame)))
   (equal
    (abs-addrs
     (frame-val->dir
      (cdr (assoc-equal (1st-complete-under-pathname frame pathname)
                        frame))))
    nil))
  :hints (("goal" :in-theory (enable 1st-complete-under-pathname))))

;; This doesn't work as a pure type-prescription rule.
(defthm
  partial-collapse-correctness-lemma-39
  (implies
   (and (not (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
        (mv-nth 1 (collapse frame)))
   (consp
    (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame))))
  :hints (("goal" :in-theory (enable collapse 1st-complete-src)))
  :rule-classes (:type-prescription :rewrite))

(defthm partial-collapse-correctness-lemma-46
  (implies (and (abs-file-alist-p abs-file-alist)
                (abs-no-dups-p abs-file-alist))
           (not (consp (assoc-equal (car (car abs-file-alist))
                                    (cdr abs-file-alist)))))
  :hints (("goal" :expand (abs-no-dups-p abs-file-alist))))

(defthm
  partial-collapse-correctness-lemma-47
  (implies
   (and (abs-directory-file-p val)
        (abs-file-alist-p abs-file-alist)
        (abs-no-dups-p abs-file-alist)
        (fat32-filename-p name))
   (equal
    (intersectp-equal (abs-addrs (put-assoc-equal name val abs-file-alist))
                      x)
    (or (intersectp-equal (abs-addrs (abs-file->contents val))
                          x)
        (intersectp-equal (abs-addrs (remove-assoc-equal name abs-file-alist))
                          x))))
  :hints (("goal" :in-theory (e/d (abs-addrs intersectp-equal)
                                  (intersectp-is-commutative))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (abs-directory-file-p val)
          (abs-file-alist-p abs-file-alist)
          (abs-no-dups-p abs-file-alist)
          (fat32-filename-p name))
     (equal
      (intersectp-equal x
                        (abs-addrs (put-assoc-equal name val abs-file-alist)))
      (or (intersectp-equal x
                            (abs-addrs (abs-file->contents val)))
          (intersectp-equal x
                            (abs-addrs (remove-assoc-equal name abs-file-alist)))))))))

(defthm
  partial-collapse-correctness-lemma-25
  (implies
   (and (abs-directory-file-p val)
        (abs-file-alist-p abs-file-alist)
        (abs-no-dups-p abs-file-alist)
        (fat32-filename-p name))
   (iff
    (member-equal x
                  (abs-addrs (put-assoc-equal name val abs-file-alist)))
    (or (member-equal x (abs-addrs (abs-file->contents val)))
        (member-equal x
                      (abs-addrs (remove-assoc-equal name abs-file-alist))))))
  :hints
  (("goal" :do-not-induct t
    :use (:instance (:rewrite partial-collapse-correctness-lemma-47
                              . 2)
                    (abs-file-alist abs-file-alist)
                    (val val)
                    (name name)
                    (x (list x)))
    :in-theory (e/d (intersectp-equal)
                    (partial-collapse-correctness-lemma-47)))))

;; Revisit this; it takes three subinductions.
(defthm
  partial-collapse-correctness-lemma-50
  (implies
   (and (abs-directory-file-p val)
        (abs-no-dups-p abs-file-alist)
        (abs-file-alist-p abs-file-alist)
        (fat32-filename-p name))
   (equal
    (no-duplicatesp-equal
     (abs-addrs (put-assoc-equal name val abs-file-alist)))
    (and
     (no-duplicatesp-equal
      (abs-addrs (remove-assoc-equal name abs-file-alist)))
     (no-duplicatesp-equal (abs-addrs (abs-file->contents val)))
     (not
      (intersectp-equal (abs-addrs (remove-assoc-equal name abs-file-alist))
                        (abs-addrs (abs-file->contents val)))))))
  :hints (("goal" :in-theory (e/d (abs-addrs intersectp-equal
                                             member-of-abs-fs-fix-when-natp-lemma-1)))))

(defthm
  partial-collapse-correctness-lemma-34
  (implies (abs-separate frame)
           (no-duplicatesp-equal
            (abs-addrs (frame-val->dir (cdr (assoc-equal x frame))))))
  :hints (("goal" :in-theory (enable abs-separate))))

(defthm
  partial-collapse-correctness-lemma-54
  (implies
   (and
    (not (equal x (1st-complete (frame->frame frame))))
    (context-apply-ok
     (frame-val->dir
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     (1st-complete (frame->frame frame))
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))))
   (consp
    (remove-equal
     x
     (abs-addrs
      (frame-val->dir
       (cdr (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame))))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite member-of-remove))
    :use
    (:instance
     (:rewrite member-of-remove)
     (x
      (abs-addrs
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))))
     (b x)
     (a (1st-complete (frame->frame frame)))))))

(defthm
  partial-collapse-correctness-lemma-36
  (implies (and (absfat-equiv abs-file-alist1 abs-file-alist2)
                (m1-file-alist-p (abs-fs-fix abs-file-alist1))
                (abs-fs-p abs-file-alist2))
           (equal (abs-addrs abs-file-alist2) nil))
  :hints
  (("goal"
    :in-theory (e/d (absfat-equiv)
                    (absfat-equiv-of-context-apply-lemma-4))
    :use ((:instance absfat-equiv-of-context-apply-lemma-4
                     (abs-file-alist1 (abs-fs-fix abs-file-alist1)))
          (:instance absfat-equiv-of-context-apply-lemma-4
                     (abs-file-alist1 abs-file-alist2)
                     (abs-file-alist2 (abs-fs-fix abs-file-alist1)))))))

(defthm
  partial-collapse-correctness-lemma-44
  (implies
   (and
    (absfat-equiv
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     dir)
    (abs-fs-p dir))
   (subsetp-equal
    (abs-addrs dir)
    (abs-addrs
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame)))))))
  :hints (("goal" :in-theory (enable absfat-equiv))))

(defthm partial-collapse-correctness-lemma-45
  (implies
   (and
    (mv-nth 1 (collapse frame))
    (not (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))))
   (and
    (consp
     (abs-addrs
      (frame-val->dir
       (cdr (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame))))))
    (prefixp
     (frame-val->path
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
     (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
  :hints
  (("goal" :in-theory
    (e/d (collapse 1st-complete-src)
         ((:rewrite remove-assoc-of-put-assoc)
          (:rewrite remove-assoc-of-remove-assoc)
          (:rewrite abs-file-alist-p-when-m1-file-alist-p)
          (:linear abs-find-file-correctness-1-lemma-44)))
    :induct (collapse frame)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (mv-nth 1 (collapse frame))
      (not (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
      (abs-complete
       (frame-val->dir (cdr (assoc-equal y (frame->frame frame))))))
     (not (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 y))))
   (:rewrite
    :corollary
    (implies
     (and
      (mv-nth 1 (collapse frame))
      (not (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
      (list-equiv src-path
                  (frame-val->path
                   (cdr (assoc-equal
                         (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                         (frame->frame frame))))))
     (prefixp
      src-path
      (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))))

(defthm
  partial-collapse-correctness-lemma-15
  (implies (and (abs-separate frame)
                (consp (assoc-equal x frame))
                (absfat-equiv (frame-val->dir (cdr (assoc-equal x frame)))
                              (frame-val->dir val))
                (abs-no-dups-p (frame-val->dir val)))
           (equal (1st-complete (put-assoc-equal x val frame))
                  (1st-complete frame)))
  :hints (("goal" :in-theory (enable 1st-complete abs-separate))))

(defthm
  partial-collapse-correctness-lemma-53
  (implies
   (and
    (frame-p (frame->frame frame))
    (abs-separate (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (< 0 (1st-complete (frame->frame frame)))
    (mv-nth
     1
     (collapse
      (frame-with-root
       (context-apply
        (frame->root frame)
        (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (1st-complete (frame->frame frame))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame)))))
       (remove-assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame)))))
    (absfat-equiv
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     dir)
    (dist-names (frame->root frame)
                nil (frame->frame frame)))
   (mv-nth
    1
    (collapse
     (frame-with-root
      (context-apply
       (frame->root frame)
       dir (1st-complete (frame->frame frame))
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
      (remove-assoc-equal (1st-complete (frame->frame frame))
                          (frame->frame frame))))))
  :hints
  (("goal"
    :do-not-induct t
    :use
    (:instance
     (:rewrite partial-collapse-correctness-lemma-21)
     (frame (remove-assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame)))
     (root1
      (context-apply
       (frame->root frame)
       dir (1st-complete (frame->frame frame))
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))))
     (root2
      (context-apply
       (frame->root frame)
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (1st-complete (frame->frame frame))
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))))))))

(defthm
  partial-collapse-correctness-lemma-72
  (implies
   (and
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (< 0 (1st-complete (frame->frame frame)))
    (context-apply-ok
     (frame->root frame)
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     (1st-complete (frame->frame frame))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))
    (absfat-equiv
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     dir))
   (context-apply-ok
    (frame->root frame)
    dir (1st-complete (frame->frame frame))
    (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))))
  :hints
  (("goal"
    :use
    (:instance
     (:rewrite context-apply-ok-when-absfat-equiv-2)
     (abs-file-alist2
      (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))
     (x-path
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
     (x (1st-complete (frame->frame frame)))
     (abs-file-alist1 dir)
     (abs-file-alist3 (frame->root frame))))))

(defthm
  partial-collapse-correctness-lemma-73
  (implies
   (and
    (context-apply-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     (1st-complete (frame->frame frame))
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (not (consp (assoc-equal 0 (frame->frame frame))))
    (absfat-equiv
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     dir))
   (context-apply-ok
    dir
    (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                      (frame->frame frame))))
    (1st-complete (frame->frame frame))
    (nthcdr
     (len
      (frame-val->path
       (cdr
        (assoc-equal
         (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (frame->frame frame)))))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite abs-separate-correctness-1-lemma-4))
    :use
    ((:instance
      (:rewrite context-apply-ok-when-absfat-equiv-1)
      (x-path
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))))
      (x (1st-complete (frame->frame frame)))
      (abs-file-alist3
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
      (abs-file-alist1 dir)
      (abs-file-alist2
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame))))))
     (:instance (:rewrite abs-separate-correctness-1-lemma-4)
                (frame (frame->frame frame)))))))

(defthm
  partial-collapse-correctness-lemma-74
  (implies
   (and
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (< 0 (1st-complete (frame->frame frame)))
    (context-apply-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     (1st-complete (frame->frame frame))
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
    (absfat-equiv
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     dir))
   (context-apply-ok
    (frame-val->dir
     (cdr
      (assoc-equal
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (frame->frame frame))))
    dir (1st-complete (frame->frame frame))
    (nthcdr
     (len
      (frame-val->path
       (cdr
        (assoc-equal
         (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (frame->frame frame)))))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))))
  :hints
  (("goal"
    :use
    (:instance
     context-apply-ok-when-absfat-equiv-2
     (x-path
      (nthcdr
       (len
        (frame-val->path
         (cdr (assoc-equal
               (frame-val->src
                (cdr (assoc-equal (1st-complete (frame->frame frame))
                                  (frame->frame frame))))
               (frame->frame frame)))))
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))))
     (x (1st-complete (frame->frame frame)))
     (abs-file-alist1 dir)
     (abs-file-alist3
      (frame-val->dir
       (cdr
        (assoc-equal
         (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (frame->frame frame)))))
     (abs-file-alist2
      (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))))))

(defthm
  partial-collapse-correctness-lemma-75
  (implies
   (absfat-equiv abs-file-alist1 abs-file-alist2)
   (iff
    (intersectp-equal
     (remove-equal nil
                   (strip-cars (abs-fs-fix abs-file-alist1)))
     y)
    (intersectp-equal
     (remove-equal nil
                   (strip-cars (abs-fs-fix abs-file-alist2)))
     y)))
  :hints
  (("goal"
    :in-theory (e/d (absfat-equiv)
                    (absfat-equiv-implies-set-equiv-names-at-1-lemma-5))
    :use
    ((:instance (:rewrite absfat-equiv-implies-set-equiv-names-at-1-lemma-5
                          . 2)
                (abs-file-alist1 (abs-fs-fix abs-file-alist1))
                (abs-file-alist2 (abs-fs-fix abs-file-alist2)))
     (:instance
      (:rewrite absfat-equiv-implies-set-equiv-names-at-1-lemma-5
                . 2)
      (abs-file-alist1 (abs-fs-fix abs-file-alist2))
      (abs-file-alist2 (abs-fs-fix abs-file-alist1))))))
  :rule-classes :congruence)

(defthm
  partial-collapse-correctness-lemma-52
  (implies
   (absfat-equiv
    (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                      (frame->frame frame))))
    dir)
   (absfat-equiv
    (context-apply
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     (1st-complete (frame->frame frame))
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
    (context-apply
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     dir (1st-complete (frame->frame frame))
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))))))

(defthm
  partial-collapse-correctness-lemma-77
  (implies
   (and
    (context-apply-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     (1st-complete (frame->frame frame))
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
    (not (consp (assoc-equal 0 (frame->frame frame)))))
   (consp (assoc-equal (1st-complete (frame->frame frame))
                       (frame->frame frame)))))

(defthm
  partial-collapse-correctness-lemma-78
  (implies
   (absfat-equiv
    (frame-val->dir
     (cdr
      (assoc-equal
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (frame->frame frame))))
    dir)
   (absfat-equiv
    (context-apply
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     (1st-complete (frame->frame frame))
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
    (context-apply
     dir
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     (1st-complete (frame->frame frame))
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))))
  :hints
  (("goal"
    :use
    (:instance
     absfat-equiv-of-context-apply-2
     (abs-file-alist2 dir)
     (x-path
      (nthcdr
       (len
        (frame-val->path
         (cdr (assoc-equal
               (frame-val->src
                (cdr (assoc-equal (1st-complete (frame->frame frame))
                                  (frame->frame frame))))
               (frame->frame frame)))))
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))))
     (x (1st-complete (frame->frame frame)))
     (abs-file-alist3
      (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))
     (abs-file-alist1
      (frame-val->dir
       (cdr
        (assoc-equal
         (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (frame->frame frame)))))))))

(encapsulate
  ()

  (local
   (defun induction-scheme (dir frame x)
     (declare (xargs :verify-guards nil
                     :measure (len (frame->frame frame))))
     (cond
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (not (zp (1st-complete-src (frame->frame frame))))
        (not
         (or
          (equal (1st-complete-src (frame->frame frame))
                 (1st-complete (frame->frame frame)))
          (atom
           (assoc-equal (1st-complete-src (frame->frame frame))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal (1st-complete-src (frame->frame frame))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
        (context-apply-ok
         (frame-val->dir
          (cdr
           (assoc-equal (1st-complete-src (frame->frame frame))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal (1st-complete-src (frame->frame frame))
                          (remove-assoc-equal (1st-complete (frame->frame frame))
                                              (frame->frame frame))))))
          (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                             (frame->frame frame))))))
        (equal (1st-complete (frame->frame frame)) x))
       (induction-scheme
        (context-apply
         (frame-val->dir
          (cdr (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame))))
         dir (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame)))))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (1st-complete-src (frame->frame frame))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal (1st-complete-src (frame->frame frame))
                              (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr (assoc-equal
                   (1st-complete-src (frame->frame frame))
                   (remove-assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame)))))
            (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                              (frame->frame frame))))
            (1st-complete (frame->frame frame))
            (nthcdr
             (len
              (frame-val->path
               (cdr (assoc-equal
                     (1st-complete-src (frame->frame frame))
                     (remove-assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
             (frame-val->path
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))))
           (frame-val->src
            (cdr (assoc-equal (1st-complete-src (frame->frame frame))
                              (frame->frame frame)))))
          (remove-assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
        (1st-complete-src (frame->frame frame))))
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (not (zp (1st-complete-src (frame->frame frame))))
        (not
         (or
          (equal (1st-complete-src (frame->frame frame))
                 (1st-complete (frame->frame frame)))
          (atom
           (assoc-equal (1st-complete-src (frame->frame frame))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal (1st-complete-src (frame->frame frame))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
        (context-apply-ok
         (frame-val->dir
          (cdr
           (assoc-equal (1st-complete-src (frame->frame frame))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal (1st-complete-src (frame->frame frame))
                          (remove-assoc-equal (1st-complete (frame->frame frame))
                                              (frame->frame frame))))))
          (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                             (frame->frame frame))))))
        (equal x (1st-complete-src (frame->frame frame))))
       (induction-scheme
        (context-apply
         dir
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr (assoc-equal
                  (frame-val->src
                   (cdr (assoc-equal (1st-complete (frame->frame frame))
                                     (frame->frame frame))))
                  (frame->frame frame)))))
          (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                             (frame->frame frame))))))
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (1st-complete-src (frame->frame frame))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal (1st-complete-src (frame->frame frame))
                              (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr (assoc-equal
                   (1st-complete-src (frame->frame frame))
                   (remove-assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame)))))
            (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                              (frame->frame frame))))
            (1st-complete (frame->frame frame))
            (nthcdr
             (len
              (frame-val->path
               (cdr (assoc-equal
                     (1st-complete-src (frame->frame frame))
                     (remove-assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
             (frame-val->path
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))))
           (frame-val->src
            (cdr (assoc-equal (1st-complete-src (frame->frame frame))
                              (frame->frame frame)))))
          (remove-assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
        x))
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (not (zp (1st-complete-src (frame->frame frame))))
        (not
         (or
          (equal (1st-complete-src (frame->frame frame))
                 (1st-complete (frame->frame frame)))
          (atom
           (assoc-equal (1st-complete-src (frame->frame frame))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal (1st-complete-src (frame->frame frame))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
        (context-apply-ok
         (frame-val->dir
          (cdr
           (assoc-equal (1st-complete-src (frame->frame frame))
                        (remove-assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal (1st-complete-src (frame->frame frame))
                          (remove-assoc-equal (1st-complete (frame->frame frame))
                                              (frame->frame frame))))))
          (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                             (frame->frame frame)))))))
       (induction-scheme
        dir
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (1st-complete-src (frame->frame frame))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal (1st-complete-src (frame->frame frame))
                              (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr (assoc-equal
                   (1st-complete-src (frame->frame frame))
                   (remove-assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame)))))
            (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                              (frame->frame frame))))
            (1st-complete (frame->frame frame))
            (nthcdr
             (len
              (frame-val->path
               (cdr (assoc-equal
                     (1st-complete-src (frame->frame frame))
                     (remove-assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
             (frame-val->path
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))))
           (frame-val->src
            (cdr (assoc-equal (1st-complete-src (frame->frame frame))
                              (frame->frame frame)))))
          (remove-assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
        x))
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (zp (1st-complete-src (frame->frame frame)))
        (context-apply-ok
         (frame->root frame)
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))))
       (induction-scheme
        dir
        (frame-with-root
         (context-apply
          (frame->root frame)
          (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))
          (1st-complete (frame->frame frame))
          (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                             (frame->frame frame)))))
         (remove-assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))
        x))
      (t (mv dir frame x)))))

  (defthm
    partial-collapse-correctness-lemma-82
    (implies
     (and
      (frame-p (frame->frame frame))
      (abs-separate (frame->frame frame))
      (no-duplicatesp-equal (strip-cars (frame->frame frame)))
      (mv-nth 1 (collapse frame))
      (consp (assoc-equal x (frame->frame frame)))
      (atom (assoc-equal 0 (frame->frame frame)))
      (absfat-equiv (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
                    dir)
      (dist-names (frame->root frame)
                  nil (frame->frame frame)))
     (mv-nth
      1
      (collapse
       (frame-with-root
        (frame->root frame)
        (put-assoc-equal
         x
         (frame-val (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
                    dir
                    (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
         (frame->frame frame))))))
    :hints
    (("goal"
      :in-theory
      (e/d (collapse 1st-complete-src)
           ((:definition remove-assoc-equal)
            (:rewrite remove-assoc-of-remove-assoc)
            (:rewrite abs-file-alist-p-when-m1-file-alist-p)
            (:rewrite partial-collapse-correctness-lemma-36)
            (:rewrite absfat-equiv-implies-set-equiv-names-at-1-lemma-1)
            (:rewrite put-assoc-equal-without-change . 2)
            (:definition no-duplicatesp-equal)
            (:definition member-equal)
            (:rewrite nthcdr-when->=-n-len-l)))
      :induct (induction-scheme dir frame x)
      :do-not-induct t
      :expand
      ((collapse
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          x
          (frame-val
           (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
           dir
           (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
          (frame->frame frame))))
       (collapse
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (1st-complete (frame->frame frame))
          (frame-val (frame-val->path
                      (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
                     dir 0)
          (frame->frame frame)))))))))

(defthm
  partial-collapse-correctness-lemma-83
  (implies
   (and
    (< 0 x)
    (m1-file-alist-p x-dir)
    (abs-fs-p x-dir)
    (dist-names x-dir x-relpath frame)
    (prefixp (frame-val->path (cdr (assoc-equal src frame)))
             (fat32-filename-list-fix x-relpath))
    (context-apply-ok
     (frame-val->dir (cdr (assoc-equal src frame)))
     x-dir x
     (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
             x-relpath))
    (abs-separate frame)
    (< 0 y)
    (m1-file-alist-p y-dir)
    (abs-fs-p y-dir)
    (dist-names y-dir y-relpath frame)
    (not (prefixp (fat32-filename-list-fix y-relpath)
                  (fat32-filename-list-fix x-relpath)))
    (not
     (intersectp-equal
      (names-at y-dir nil)
      (names-at
       (context-apply
        (frame-val->dir (cdr (assoc-equal src frame)))
        x-dir x
        (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
                x-relpath))
       (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
               y-relpath))))
    (prefixp (frame-val->path (cdr (assoc-equal src frame)))
             (fat32-filename-list-fix y-relpath))
    (integerp x)
    (integerp y))
   (abs-separate
    (put-assoc-equal
     src
     (frame-val
      (frame-val->path (cdr (assoc-equal src frame)))
      (context-apply
       (context-apply
        (frame-val->dir (cdr (assoc-equal src frame)))
        x-dir x
        (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
                x-relpath))
       y-dir y
       (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
               y-relpath))
      (frame-val->src (cdr (assoc-equal src frame))))
     frame)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable abs-separate-of-put-assoc-1)
    :use
    ((:instance abs-separate-of-put-assoc-1 (dir x-dir)
                (relpath x-relpath))
     (:instance
      abs-separate-of-put-assoc-1 (x y)
      (dir y-dir)
      (relpath y-relpath)
      (frame
       (put-assoc-equal
        src
        (frame-val
         (frame-val->path (cdr (assoc-equal src frame)))
         (context-apply
          (frame-val->dir (cdr (assoc-equal src frame)))
          x-dir x
          (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
                  x-relpath))
         (frame-val->src (cdr (assoc-equal src frame))))
        frame)))
     (:instance (:rewrite abs-separate-of-put-assoc-lemma-4)
                (relpath2 x-relpath)
                (x2 x)
                (dir2 x-dir)
                (frame frame)
                (src src)
                (relpath1 y-relpath)
                (dir1 y-dir)))
    :expand
    (:with
     abs-separate-of-put-assoc-lemma-3
     (intersectp-equal
      (names-at x-dir nil)
      (names-at
       (frame-val->dir (cdr (assoc-equal src frame)))
       (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
               x-relpath)))))))

(defthm
  partial-collapse-correctness-lemma-43
  (implies
   (and
    (no-duplicatesp-equal (strip-cars frame))
    (frame-p frame)
    (< 0 x)
    (not (and (consp (assoc-equal x frame))
              (abs-complete (frame-val->dir (cdr (assoc-equal x frame)))))))
   (not (equal (1st-complete frame) x)))
  :hints (("goal" :in-theory (enable 1st-complete))))

;; This can be p helpful...
(defthm
  partial-collapse-correctness-lemma-59
  (implies
   (and
    (equal
     (assoc-equal x other-frame)
     (assoc-equal x frame))
    (mv-nth
     1
     (collapse
      (frame-with-root
       root
       (put-assoc-equal
        x
        (frame-val (frame-val->path (cdr (assoc-equal x other-frame)))
                   dir1
                   (frame-val->src (cdr (assoc-equal x other-frame))))
        frame))))
    (frame-p
     (put-assoc-equal
      x
      (frame-val (frame-val->path (cdr (assoc-equal x other-frame)))
                 dir1
                 (frame-val->src (cdr (assoc-equal x other-frame))))
      frame))
    (abs-separate
     (put-assoc-equal
      x
      (frame-val (frame-val->path (cdr (assoc-equal x other-frame)))
                 dir1
                 (frame-val->src (cdr (assoc-equal x other-frame))))
      frame))
    (no-duplicatesp-equal (strip-cars frame))
    (not (equal 0 x))
    (not (consp (assoc-equal 0 frame)))
    (absfat-equiv dir1 dir2)
    (dist-names
     (abs-fs-fix root)
     nil
     (put-assoc-equal
      x
      (frame-val (frame-val->path (cdr (assoc-equal x other-frame)))
                 dir1
                 (frame-val->src (cdr (assoc-equal x other-frame))))
      frame)))
   (mv-nth
    1
    (collapse
     (frame-with-root
      root
      (put-assoc-equal
       x
       (frame-val (frame-val->path (cdr (assoc-equal x other-frame)))
                  dir2
                  (frame-val->src (cdr (assoc-equal x other-frame))))
       frame)))))
  :hints
  (("goal"
    :in-theory (disable partial-collapse-correctness-lemma-82)
    :use
    (:instance
     partial-collapse-correctness-lemma-82
     (dir dir2)
     (frame (frame-with-root
             root
             (put-assoc-equal
              x
              (frame-val (frame-val->path (cdr (assoc-equal x frame)))
                         dir1
                         (frame-val->src (cdr (assoc-equal x frame))))
              frame)))))))

(defthm
  partial-collapse-correctness-lemma-61
  (implies
   (and
    (context-apply-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     (1st-complete (frame->frame frame))
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
    (equal
     (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
     (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame)))))
    (not
     (consp
      (abs-addrs
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))))))
   (not
    (equal
     x
     (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame)))))))
  :hints
  (("goal" :in-theory
    (e/d (collapse abs-separate)
         ((:definition remove-assoc-equal)
          (:rewrite len-of-remove-assoc-equal-2)
          (:definition member-equal)
          (:definition len)
          (:rewrite partial-collapse-correctness-lemma-32))))))

(defthm
  partial-collapse-correctness-lemma-62
  (implies
   (not
    (consp
     (abs-addrs (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
   (abs-complete
    (frame-val->dir$inline (cdr (assoc-equal x (frame->frame frame)))))))

;; This is important when you're reasoning about two ways of collapsing to get
;; to the same place...
(defthm
  partial-collapse-correctness-lemma-58
  (implies
   (and
    (abs-separate (frame->frame frame))
    (mv-nth 1 (collapse frame))
    (not (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
    (abs-complete (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (and
    (consp
     (abs-addrs
      (frame-val->dir
       (cdr (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame))))))
    (context-apply-ok
     (frame-val->dir
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
     (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
     x
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))))
  :hints
  (("goal"
    :in-theory (e/d (collapse 1st-complete-src)
                    ((:rewrite partial-collapse-correctness-lemma-43)
                     (:definition no-duplicatesp-equal)
                     (:rewrite remove-assoc-of-remove-assoc)
                     (:definition remove-assoc-equal)
                     (:rewrite remove-assoc-of-put-assoc)
                     (:definition member-equal)
                     (:rewrite abs-file-alist-p-when-m1-file-alist-p)
                     (:rewrite context-apply-ok-when-absfat-equiv-lemma-4)
                     (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)))
    :induct (collapse frame)
    :expand
    ((:with
      context-apply-ok-of-context-apply-1
      (context-apply-ok
       (context-apply
        (frame-val->dir
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
        (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (1st-complete (frame->frame frame))
        (nthcdr
         (len
          (frame-val->path
           (cdr
            (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))))
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
       x
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and
      (abs-separate (frame->frame frame))
      (mv-nth 1 (collapse frame))
      (not (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
      (abs-complete (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
      (frame-p (frame->frame frame))
      (no-duplicatesp-equal (strip-cars (frame->frame frame)))
      (fat32-filename-list-equiv relpath
                            (nthcdr
                             (len
                              (frame-val->path
                               (cdr (assoc-equal
                                     (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                                     (frame->frame frame)))))
                             (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
     (context-apply-ok
      (frame-val->dir
       (cdr (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame))))
      (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
      x
      relpath)))))

(defthm
  partial-collapse-correctness-lemma-35
  (implies
   (and (force (consp (assoc-equal x frame)))
        (abs-separate frame)
        (force (equal (assoc-equal x frame)
                      (assoc-equal x other-frame))))
   (dist-names (frame-val->dir (cdr (assoc-equal x other-frame)))
               (frame-val->path (cdr (assoc-equal x other-frame)))
               (remove-assoc-equal x frame)))
  :hints (("goal" :in-theory (disable abs-separate-correctness-1-lemma-22)
           :use abs-separate-correctness-1-lemma-22)))

(defthm
  partial-collapse-correctness-lemma-63
  (implies
   (and
    (consp (frame->frame frame))
    (< 0
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
    (< 0
       (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
    (< 0 (1st-complete (frame->frame frame)))
    (consp
     (assoc-equal
      (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
      (frame->frame frame)))
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))
    (context-apply-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     (1st-complete (frame->frame frame))
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
    (mv-nth
     1
     (collapse
      (frame-with-root
       (frame->root frame)
       (put-assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame-val
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame))))
         (context-apply
          (frame-val->dir
           (cdr
            (assoc-equal
             (frame-val->src
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))
             (frame->frame frame))))
          (frame-val->dir
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
          (1st-complete (frame->frame frame))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src
                (cdr (assoc-equal (1st-complete (frame->frame frame))
                                  (frame->frame frame))))
               (frame->frame frame)))))
           (frame-val->path
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))
         (frame-val->src
          (cdr (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame)))))
        (remove-assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))))
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (equal
     (1st-complete
      (put-assoc-equal
       (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
       (frame-val
        (frame-val->path
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
        (context-apply
         (frame-val->dir
          (cdr
           (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
         x
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
        (frame-val->src
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))
       (remove-assoc-equal x (frame->frame frame))))
     (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
   (context-apply-ok
    (frame-val->dir$inline
     (cdr
      (assoc-equal
       (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
       (frame->frame frame))))
    (frame-val->dir$inline (cdr (assoc-equal x (frame->frame frame))))
    x
    (nthcdr
     (len
      (frame-val->path$inline
       (cdr
        (assoc-equal
         (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
         (frame->frame frame)))))
     (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame)))))))
  :hints
  (("goal" :in-theory
    (e/d (collapse abs-separate 1st-complete-src)
         ((:definition remove-assoc-equal)
          (:rewrite len-of-remove-assoc-equal-2)
          (:definition member-equal)
          (:definition len)
          (:rewrite partial-collapse-correctness-lemma-32)
          (:definition assoc-equal)
          (:rewrite remove-assoc-of-put-assoc)
          (:definition remove-equal)
          (:type-prescription absfat-equiv-of-context-apply-lemma-8)
          (:definition put-assoc-equal)
          (:rewrite consp-of-remove-assoc-1))))))

(defthm
  partial-collapse-correctness-lemma-66
  (implies
   (and (abs-separate frame)
        (not (equal x y))
        (list-equiv (frame-val->path (cdr (assoc-equal y frame)))
                    (frame-val->path (cdr (assoc-equal x frame)))))
   (not
    (intersectp-equal
     (remove-equal nil
                   (strip-cars (frame-val->dir (cdr (assoc-equal x frame)))))
     (remove-equal
      nil
      (strip-cars (frame-val->dir (cdr (assoc-equal y frame))))))))
  :hints (("goal" :in-theory (e/d (names-at)
                                  (abs-separate-correctness-1-lemma-14))
           :use (abs-separate-correctness-1-lemma-14
                 (:instance abs-separate-correctness-1-lemma-14
                            (y x)
                            (x y)))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (abs-separate frame)
      (not (equal x y))
      (list-equiv (frame-val->path (cdr (assoc-equal y frame)))
                  (frame-val->path (cdr (assoc-equal x frame))))
      (not (member-equal
            nil
            (strip-cars (frame-val->dir (cdr (assoc-equal x frame)))))))
     (not
      (intersectp-equal
       (strip-cars (frame-val->dir (cdr (assoc-equal x frame))))
       (remove-equal
        nil
        (strip-cars (frame-val->dir (cdr (assoc-equal y frame)))))))))
   (:rewrite
    :corollary
    (implies
     (and
      (abs-separate frame)
      (not (equal x y))
      (list-equiv (frame-val->path (cdr (assoc-equal y frame)))
                  (frame-val->path (cdr (assoc-equal x frame))))
      (not (member-equal
            nil
            (strip-cars (frame-val->dir (cdr (assoc-equal x frame))))))
      (not
       (member-equal
        nil
        (strip-cars (frame-val->dir (cdr (assoc-equal y frame)))))))
     (not
      (intersectp-equal
       (strip-cars (frame-val->dir (cdr (assoc-equal x frame))))
       (strip-cars (frame-val->dir (cdr (assoc-equal y frame))))))))))

(defthm
  partial-collapse-correctness-lemma-68
  (implies
   (and (equal (1st-complete (put-assoc-equal key val frame))
               key)
        (frame-p (put-assoc-equal key val frame))
        (not (zp (1st-complete (put-assoc-equal key val frame))))
        (no-duplicatesp-equal (strip-cars (put-assoc-equal key val frame))))
   (equal (abs-addrs (frame-val->dir val))
          nil))
  :hints (("goal" :in-theory (disable abs-separate-correctness-1-lemma-4)
           :use ((:instance abs-separate-correctness-1-lemma-4
                            (frame (put-assoc-equal key val frame))))))
  :rule-classes :forward-chaining)

(defthm
  partial-collapse-correctness-lemma-80
  (implies
   (and
    (consp (frame->frame frame))
    (< 0
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
    (abs-separate (frame->frame frame))
    (< 0
       (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
    (< 0 (1st-complete (frame->frame frame)))
    (consp
     (assoc-equal
      (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
      (frame->frame frame)))
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))
    (context-apply-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     (1st-complete (frame->frame frame))
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
    (mv-nth
     1
     (collapse
      (frame-with-root
       (frame->root frame)
       (put-assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame-val
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame))))
         (context-apply
          (frame-val->dir
           (cdr
            (assoc-equal
             (frame-val->src
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))
             (frame->frame frame))))
          (frame-val->dir
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
          (1st-complete (frame->frame frame))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src
                (cdr (assoc-equal (1st-complete (frame->frame frame))
                                  (frame->frame frame))))
               (frame->frame frame)))))
           (frame-val->path
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))
         (frame-val->src
          (cdr (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame)))))
        (remove-assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))))
    (not
     (consp
      (abs-addrs
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (abs-fs-p
    (context-apply
     (frame-val->dir
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
     (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
     x
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))))
  :hints
  (("goal" :in-theory
    (e/d (collapse 1st-complete-src)
         ((:rewrite remove-assoc-of-put-assoc)
          (:rewrite partial-collapse-correctness-lemma-43)
          (:definition assoc-equal)
          (:rewrite remove-assoc-of-remove-assoc)
          (:definition remove-assoc-equal)
          (:rewrite abs-file-alist-p-when-m1-file-alist-p)
          (:rewrite put-assoc-equal-without-change . 2)
          (:rewrite 1st-complete-of-put-assoc-2)
          (:rewrite abs-fs-fix-when-abs-fs-p)
          (:rewrite abs-addrs-of-context-apply-1-lemma-14)
          (:rewrite assoc-after-put-assoc)
          (:rewrite strip-cars-of-remove-assoc)
          (:rewrite remove-when-absent)
          (:rewrite nthcdr-when->=-n-len-l))))))

(defthm
  partial-collapse-correctness-lemma-81
  (implies
   (and
    (consp (frame->frame frame))
    (< 0
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
    (abs-separate (frame->frame frame))
    (integerp x)
    (< 0 x)
    (< 0
       (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
    (< 0 (1st-complete (frame->frame frame)))
    (consp
     (assoc-equal
      (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
      (frame->frame frame)))
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))
    (context-apply-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     (1st-complete (frame->frame frame))
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
    (mv-nth
     1
     (collapse
      (frame-with-root
       (frame->root frame)
       (put-assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame-val
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame))))
         (context-apply
          (frame-val->dir
           (cdr
            (assoc-equal
             (frame-val->src
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))
             (frame->frame frame))))
          (frame-val->dir
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
          (1st-complete (frame->frame frame))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src
                (cdr (assoc-equal (1st-complete (frame->frame frame))
                                  (frame->frame frame))))
               (frame->frame frame)))))
           (frame-val->path
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))
         (frame-val->src
          (cdr (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame)))))
        (remove-assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))))
    (not
     (consp
      (abs-addrs
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (equal
     (1st-complete
      (put-assoc-equal
       (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
       (frame-val
        (frame-val->path
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
        (context-apply
         (frame-val->dir
          (cdr
           (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
         x
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
        (frame-val->src
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))
       (remove-assoc-equal x (frame->frame frame))))
     (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
   (not
    (consp
     (remove-equal
      x
      (abs-addrs
       (frame-val->dir$inline
        (cdr
         (assoc-equal
          (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
          (frame->frame frame)))))))))
  :hints
  (("goal"
    :in-theory (e/d nil
                    (abs-separate-correctness-1-lemma-4
                     1st-complete-of-put-assoc-3))
    :use
    (:instance
     abs-separate-correctness-1-lemma-4
     (frame
      (put-assoc-equal
       (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
       (frame-val
        (frame-val->path
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
        (context-apply
         (frame-val->dir
          (cdr
           (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
         x
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
        (frame-val->src
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))
       (remove-assoc-equal x (frame->frame frame))))))))

(defthm
  partial-collapse-correctness-lemma-64
  (implies
   (and
    (abs-separate (frame->frame frame))
    (mv-nth 1 (collapse frame))
    (consp (assoc-equal x (frame->frame frame)))
    (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
    (abs-complete (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (dist-names (frame->root frame)
                nil (frame->frame frame)))
   (context-apply-ok
    (frame->root frame)
    (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
    x
    (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
  :hints
  (("goal"
    :in-theory
    (e/d (collapse 1st-complete-src)
         ((:rewrite remove-assoc-of-put-assoc)
          (:rewrite partial-collapse-correctness-lemma-43)
          (:rewrite partial-collapse-correctness-lemma-63)
          (:definition remove-assoc-equal)
          (:rewrite remove-assoc-of-remove-assoc)
          (:rewrite abs-file-alist-p-when-m1-file-alist-p)
          (:rewrite put-assoc-equal-without-change . 2)
          (:rewrite context-apply-ok-when-absfat-equiv-lemma-4)
          (:type-prescription absfat-equiv-of-context-apply-lemma-8)))
    :induct (collapse frame)
    :expand
    (:with
     context-apply-ok-of-context-apply-1
     (context-apply-ok
      (context-apply
       (frame->root frame)
       (frame-val->dir$inline
        (cdr (assoc-equal (1st-complete (frame->frame frame))
                          (frame->frame frame))))
       (1st-complete (frame->frame frame))
       (frame-val->path$inline
        (cdr (assoc-equal (1st-complete (frame->frame frame))
                          (frame->frame frame)))))
      (frame-val->dir$inline (cdr (assoc-equal x (frame->frame frame))))
      x
      (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame)))))))))

(defthm
  partial-collapse-correctness-lemma-42
  (implies
   (and
    (not
     (equal
      (1st-complete
       (put-assoc-equal
        (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
        (frame-val
         (frame-val->path
          (cdr
           (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
         (context-apply
          (frame-val->dir
           (cdr
            (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame))))
          (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
          x
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))
           (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
         (frame-val->src
          (cdr
           (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame)))))
        (remove-assoc-equal x (frame->frame frame))))
      (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
    (not (equal x (1st-complete (frame->frame frame))))
    (abs-separate (frame->frame frame))
    (integerp x)
    (< 0 x)
    (< 0 (1st-complete (frame->frame frame)))
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (not
    (equal
     (1st-complete (frame->frame frame))
     (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame)))))))
  :hints
  (("goal" :in-theory
    (e/d (collapse abs-separate 1st-complete-src)
         ((:definition assoc-equal)
          (:definition remove-assoc-equal)
          (:rewrite put-assoc-equal-without-change . 2)
          (:rewrite nthcdr-when->=-n-len-l)
          (:rewrite abs-file-alist-p-when-m1-file-alist-p)
          m1-file-alist-p-of-cdr-when-m1-file-alist-p
          (:definition member-equal)
          (:definition remove-equal)
          (:rewrite remove-when-absent)
          (:definition nthcdr)
          (:definition len)
          (:rewrite remove-assoc-when-absent))))))

(defthm
  partial-collapse-correctness-lemma-48
  (implies
   (and
    (context-apply-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     (1st-complete (frame->frame frame))
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
    (not
     (consp
      (abs-addrs
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))))))
   (not (equal (frame-val->src$inline
                (cdr (assoc-equal (1st-complete (frame->frame frame))
                                  (frame->frame frame))))
               x)))
  :hints
  (("goal" :in-theory
    (e/d (collapse abs-separate 1st-complete-src)
         ((:definition assoc-equal)
          (:definition remove-assoc-equal)
          (:rewrite put-assoc-equal-without-change . 2)
          (:rewrite nthcdr-when->=-n-len-l)
          (:rewrite abs-file-alist-p-when-m1-file-alist-p)
          m1-file-alist-p-of-cdr-when-m1-file-alist-p
          (:definition member-equal)
          (:definition remove-equal)
          (:rewrite remove-when-absent)
          (:definition nthcdr)
          (:definition len)
          (:rewrite remove-assoc-when-absent))))))

(defthm
  partial-collapse-correctness-lemma-37
  (implies
   (and
    (not
     (equal
      (1st-complete
       (put-assoc-equal
        (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
        (frame-val
         (frame-val->path
          (cdr
           (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
         (context-apply
          (frame-val->dir
           (cdr
            (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame))))
          (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
          x
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))
           (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
         (frame-val->src
          (cdr
           (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame)))))
        (remove-assoc-equal x (frame->frame frame))))
      (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
    (not (equal x (1st-complete (frame->frame frame))))
    (< 0
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
    (not
     (equal
      (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
      (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))))
    (mv-nth
     1
     (collapse
      (frame-with-root
       (frame->root frame)
       (put-assoc-equal
        (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
        (frame-val
         (frame-val->path
          (cdr
           (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
         (context-apply
          (frame-val->dir
           (cdr
            (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame))))
          (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
          x
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))
           (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
         (frame-val->src
          (cdr
           (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame)))))
        (put-assoc-equal
         (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (frame-val
          (frame-val->path
           (cdr
            (assoc-equal
             (frame-val->src
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))
             (frame->frame frame))))
          (context-apply
           (frame-val->dir
            (cdr
             (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame))))
           (frame-val->dir
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
           (1st-complete (frame->frame frame))
           (nthcdr
            (len
             (frame-val->path
              (cdr
               (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame)))))
            (frame-val->path
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame))))))
          (frame-val->src
           (cdr
            (assoc-equal
             (frame-val->src
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))
             (frame->frame frame)))))
         (remove-assoc-equal
          x
          (remove-assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))))
    (abs-separate (frame->frame frame))
    (integerp x)
    (< 0 x)
    (< 0
       (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))
    (context-apply-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     (1st-complete (frame->frame frame))
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
    (not
     (consp
      (abs-addrs
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (not (consp (assoc-equal 0 (frame->frame frame)))))
   (mv-nth
    1
    (collapse
     (frame-with-root
      (frame->root frame)
      (put-assoc-equal
       (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
       (frame-val
        (frame-val->path
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
        (context-apply
         (frame-val->dir
          (cdr
           (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
         x
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
        (frame-val->src
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))
       (remove-assoc-equal x (frame->frame frame)))))))
  :hints
  (("goal" :in-theory
    (e/d (collapse abs-separate 1st-complete-src)
         ((:definition assoc-equal)
          (:definition remove-assoc-equal)
          (:rewrite put-assoc-equal-without-change . 2)
          (:rewrite nthcdr-when->=-n-len-l)
          (:rewrite abs-file-alist-p-when-m1-file-alist-p)
          m1-file-alist-p-of-cdr-when-m1-file-alist-p
          (:definition member-equal)
          (:definition remove-equal)
          (:rewrite remove-when-absent)
          (:definition nthcdr)
          (:definition len)
          (:rewrite remove-assoc-when-absent))))))

(defthm
  partial-collapse-correctness-lemma-27
  (implies
   (and
    (consp (frame->frame frame))
    (< 0
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
    (< 0 (1st-complete (frame->frame frame)))
    (consp
     (assoc-equal
      (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
      (frame->frame frame)))
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))
    (context-apply-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     (1st-complete (frame->frame frame))
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
    (mv-nth
     1
     (collapse
      (frame-with-root
       (frame->root frame)
       (put-assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame-val
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame))))
         (context-apply
          (frame-val->dir
           (cdr
            (assoc-equal
             (frame-val->src
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))
             (frame->frame frame))))
          (frame-val->dir
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
          (1st-complete (frame->frame frame))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src
                (cdr (assoc-equal (1st-complete (frame->frame frame))
                                  (frame->frame frame))))
               (frame->frame frame)))))
           (frame-val->path
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))
         (frame-val->src
          (cdr (assoc-equal
                (frame-val->src
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame))))
                (frame->frame frame)))))
        (remove-assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))))
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (not (consp (assoc-equal 0 (frame->frame frame)))))
   (equal
    (1st-complete
     (remove-assoc-equal
      (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
      (frame->frame frame)))
    (1st-complete (frame->frame frame))))
  :hints
  (("goal"
    :in-theory
    (e/d (collapse 1st-complete-src)
         ((:rewrite 1st-complete-of-remove-assoc-1)
          (:definition assoc-equal)
          (:definition remove-assoc-equal)
          (:rewrite put-assoc-equal-without-change . 2)
          (:rewrite nthcdr-when->=-n-len-l)
          (:rewrite abs-file-alist-p-when-m1-file-alist-p)
          m1-file-alist-p-of-cdr-when-m1-file-alist-p
          (:definition member-equal)
          (:definition remove-equal)
          (:rewrite remove-when-absent)
          (:definition nthcdr)
          (:definition len)
          (:rewrite remove-assoc-when-absent)))
    :use
    (:instance
     (:rewrite 1st-complete-of-remove-assoc-1)
     (frame (frame->frame frame))
     (x (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))))))

;; Ths is decently general, but it's not applied anywhere...
(defthmd
  partial-collapse-correctness-lemma-41
  (implies
   (and (no-duplicatesp-equal (strip-cars frame))
        (not (zp (1st-complete (remove-assoc-equal x frame)))))
   (equal
    (abs-addrs
     (frame-val->dir
      (cdr (assoc-equal (1st-complete (remove-assoc-equal x frame))
                        frame))))
    nil))
  :hints (("goal" :in-theory (e/d (1st-complete)
                                  (1st-complete-correctness-1)))
          ("subgoal *1/2"
           :use (:instance (:type-prescription 1st-complete-correctness-1)
                           (frame (remove-assoc-equal x (cdr frame)))))))

;; Ths is decently general, but it's not applied anywhere...
(defthmd
  partial-collapse-correctness-lemma-49
  (implies
   (and (atom (assoc-equal 0 frame))
        (frame-p frame)
        (zp (1st-complete frame))
        (consp (assoc-equal x frame)))
   (consp
    (abs-addrs (frame-val->dir (cdr (assoc-equal x frame))))))
  :hints (("goal" :in-theory (enable 1st-complete))))

(defthm
  partial-collapse-correctness-lemma-79
  (implies
   (and
    (< 0
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
    (< 0
       (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
    (context-apply-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     (1st-complete (frame->frame frame))
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
    (mv-nth 1 (collapse frame))
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (equal
    (1st-complete
     (remove-assoc-equal
      (1st-complete (frame->frame frame))
      (remove-assoc-equal
       (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
       (remove-assoc-equal
        (frame-val->src$inline
         (cdr (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
        (frame->frame frame)))))
    (1st-complete (remove-assoc-equal (1st-complete (frame->frame frame))
                                      (frame->frame frame))))))

(encapsulate
  ()

  (local
   (defthm
     lemma-1
     (implies
      (and
       (not
        (consp
         (abs-addrs
          (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))))
       (not
        (consp
         (abs-addrs
          (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
       (not (equal (nfix (1st-complete (frame->frame frame)))
                   (nfix x)))
       (abs-no-dups-p
        (context-apply
         (context-apply
          (frame-val->dir
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame))))
          (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
          x
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))
           (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))))
          (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                             (frame->frame frame)))))))
       (not
        (intersectp-equal
         (names-at
          (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))
          nil)
         (names-at
          (frame-val->dir
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame))))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))
           (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                              (frame->frame frame))))))))
       (not
        (intersectp-equal
         (names-at (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
                   nil)
         (names-at
          (frame-val->dir
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame))))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))
           (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))))
       (or
        (not
         (intersectp-equal
          (names-at (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
                    nil)
          (names-at
           (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                             (frame->frame frame))))
           (nthcdr
            (+
             (nfix
              (len
               (frame-val->path
                (cdr
                 (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame))))))
             (nfix
              (+
               (len (frame-val->path
                     (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame)))))
               (-
                (nfix
                 (len
                  (frame-val->path
                   (cdr
                    (assoc-equal
                     (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                     (frame->frame frame))))))))))
            (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))))
        (not
         (prefixp
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))
           (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                              (frame->frame frame)))))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))
           (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))))
      (absfat-equiv
       (context-apply
        (context-apply
         (frame-val->dir
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame))))
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
         x
         (nthcdr
          (len
           (frame-val->path
            (cdr (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))))
          (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
        (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (1st-complete (frame->frame frame))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))))
       (context-apply
        (context-apply
         (frame-val->dir
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame))))
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))))
          (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                             (frame->frame frame))))))
        (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
        x
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))))
     :hints
     (("goal"
       :use
       (:instance
        (:rewrite context-apply-of-context-apply-1)
        (y-path
         (nthcdr
          (len
           (frame-val->path
            (cdr (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))))
          (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                             (frame->frame frame))))))
        (y-var (1st-complete (frame->frame frame)))
        (y (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                             (frame->frame frame)))))
        (z-path
         (nthcdr
          (len
           (frame-val->path
            (cdr (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))))
          (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
        (z-var x)
        (z (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
        (x
         (frame-val->dir
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame))))))))))

  (defthm
    partial-collapse-correctness-lemma-84
    (implies
     (and
      (not
       (equal
        (1st-complete
         (put-assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
            x
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (remove-assoc-equal x (frame->frame frame))))
        (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
      (consp (frame->frame frame))
      (equal
       (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
      (abs-separate (frame->frame frame))
      (integerp x)
      (< 0 x)
      (< 0
         (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
      (< 0 (1st-complete (frame->frame frame)))
      (consp
       (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                    (frame->frame frame)))
      (prefixp
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
      (context-apply-ok
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (1st-complete (frame->frame frame))
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))))
      (mv-nth
       1
       (collapse
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (frame-val->dir
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame))))
            (1st-complete (frame->frame frame))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (remove-assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))
      (not
       (consp
        (abs-addrs
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
      (frame-p (frame->frame frame))
      (no-duplicatesp-equal (strip-cars (frame->frame frame))))
     (context-apply-ok
      (frame-val->dir$inline
       (cdr
        (assoc-equal
         (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
         (frame->frame frame))))
      (frame-val->dir$inline (cdr (assoc-equal x (frame->frame frame))))
      x
      (nthcdr
       (len
        (frame-val->path$inline
         (cdr
          (assoc-equal
           (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
           (frame->frame frame)))))
       (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame)))))))
    :hints
    (("goal" :in-theory
      (e/d (collapse abs-separate 1st-complete-src)
           ((:definition assoc-equal)
            (:definition remove-assoc-equal)
            (:rewrite put-assoc-equal-without-change . 2)
            (:rewrite nthcdr-when->=-n-len-l)
            (:rewrite abs-file-alist-p-when-m1-file-alist-p)
            m1-file-alist-p-of-cdr-when-m1-file-alist-p
            (:definition member-equal)
            (:definition remove-equal)
            (:rewrite remove-when-absent)
            (:definition nthcdr)
            (:definition len)
            (:rewrite remove-assoc-when-absent))))))

  (defthm
    partial-collapse-correctness-lemma-85
    (implies
     (and
      (not
       (equal
        (1st-complete
         (put-assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
            x
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (remove-assoc-equal x (frame->frame frame))))
        (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
      (not (equal x (1st-complete (frame->frame frame))))
      (consp (frame->frame frame))
      (equal
       (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
      (abs-separate (frame->frame frame))
      (integerp x)
      (< 0 x)
      (< 0
         (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
      (< 0 (1st-complete (frame->frame frame)))
      (consp
       (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                    (frame->frame frame)))
      (prefixp
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
      (context-apply-ok
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (1st-complete (frame->frame frame))
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))))
      (mv-nth
       1
       (collapse
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (frame-val->dir
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame))))
            (1st-complete (frame->frame frame))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (remove-assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))
      (not
       (consp
        (abs-addrs
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
      (frame-p (frame->frame frame))
      (no-duplicatesp-equal (strip-cars (frame->frame frame))))
     (not
      (<
       (binary-+
        (len
         (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame)))))
        (unary--
         (len
          (frame-val->path$inline
           (cdr
            (assoc-equal
             (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame)))))))
       0)))
    :hints
    (("goal"
      :in-theory
      (e/d (collapse abs-separate 1st-complete-src)
           ((:definition assoc-equal)
            (:definition remove-assoc-equal)
            (:rewrite put-assoc-equal-without-change . 2)
            (:rewrite nthcdr-when->=-n-len-l)
            (:rewrite abs-file-alist-p-when-m1-file-alist-p)
            m1-file-alist-p-of-cdr-when-m1-file-alist-p
            (:definition member-equal)
            (:definition remove-equal)
            (:rewrite remove-when-absent)
            (:definition nthcdr)
            (:definition len)
            (:rewrite remove-assoc-when-absent)))
      :use
      (:instance
       abs-separate-of-put-assoc-lemma-2
       (relpath
        (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame)))))
       (src (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame)))))
       (frame (frame->frame frame))))))

  (defthm
    partial-collapse-correctness-lemma-86
    (implies
     (prefixp
      (frame-val->path
       (cdr
        (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                     (frame->frame frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
     (not
      (<
       (binary-+
        (len (frame-val->path$inline
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame)))))
        (unary--
         (len
          (frame-val->path$inline
           (cdr
            (assoc-equal
             (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame)))))))
       0)))
    :hints
    (("goal"
      :in-theory
      (e/d (collapse abs-separate 1st-complete-src)
           ((:definition assoc-equal)
            (:definition remove-assoc-equal)
            (:rewrite put-assoc-equal-without-change . 2)
            (:rewrite nthcdr-when->=-n-len-l)
            (:rewrite abs-file-alist-p-when-m1-file-alist-p)
            m1-file-alist-p-of-cdr-when-m1-file-alist-p
            (:definition member-equal)
            (:definition remove-equal)
            (:rewrite remove-when-absent)
            (:definition nthcdr)
            (:definition len)
            (:rewrite remove-assoc-when-absent)))
      :use
      (:instance
       abs-separate-of-put-assoc-lemma-2
       (relpath (frame-val->path$inline
                 (cdr (assoc-equal (1st-complete (frame->frame frame))
                                   (frame->frame frame)))))
       (src (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame)))))
       (frame (frame->frame frame))))))

  (defthm
    partial-collapse-correctness-lemma-87
    (implies
     (and
      (prefixp
       (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
      (not (equal x (1st-complete (frame->frame frame))))
      (abs-separate (frame->frame frame))
      (context-apply-ok
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (1st-complete (frame->frame frame))
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))))
      (not (consp (assoc-equal 0 (frame->frame frame)))))
     (not
      (intersectp-equal
       (names-at (frame-val->dir$inline
                  (cdr (assoc-equal (1st-complete (frame->frame frame))
                                    (frame->frame frame))))
                 nil)
       (names-at
        (frame-val->dir$inline (cdr (assoc-equal x (frame->frame frame))))
        (nthcdr
         (len
          (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame)))))
         (frame-val->path$inline
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))))))
    :hints (("goal" :in-theory (disable abs-separate-correctness-1-lemma-14)
             :use (:instance abs-separate-correctness-1-lemma-14
                             (x (1st-complete (frame->frame frame)))
                             (frame (frame->frame frame))
                             (y x)))))

  (defthm
    partial-collapse-correctness-lemma-88
    (implies
     (and
      (equal
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))))
      (not
       (equal
        (1st-complete
         (put-assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
            x
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (remove-assoc-equal x (frame->frame frame))))
        (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
      (not (equal x (1st-complete (frame->frame frame))))
      (consp (frame->frame frame))
      (equal
       (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
      (abs-separate (frame->frame frame))
      (integerp x)
      (< 0 x)
      (< 0
         (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
      (< 0 (1st-complete (frame->frame frame)))
      (consp
       (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                    (frame->frame frame)))
      (prefixp
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
      (context-apply-ok
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (1st-complete (frame->frame frame))
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
      (mv-nth
       1
       (collapse
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (frame-val->dir
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame))))
            (1st-complete (frame->frame frame))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (remove-assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))
      (frame-p (frame->frame frame))
      (no-duplicatesp-equal (strip-cars (frame->frame frame))))
     (equal
      (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))
    :hints
    (("goal"
      :in-theory
      (e/d (collapse 1st-complete-src)
           ((:definition assoc-equal)
            (:definition remove-assoc-equal)
            (:rewrite put-assoc-equal-without-change . 2)
            (:rewrite nthcdr-when->=-n-len-l)
            (:rewrite abs-file-alist-p-when-m1-file-alist-p)
            m1-file-alist-p-of-cdr-when-m1-file-alist-p
            (:definition member-equal)
            (:definition remove-equal)
            (:rewrite remove-when-absent)
            (:definition nthcdr)
            (:definition len)
            (:rewrite remove-assoc-when-absent)
            append-when-prefixp))
      :use
      ((:instance
        append-when-prefixp
        (x
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (y
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))))
       (:instance
        append-when-prefixp
        (x
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (y (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))))))

  (defthm
    partial-collapse-correctness-lemma-89
    (implies
     (and
      (equal
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))))
      (not
       (equal
        (1st-complete
         (put-assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
            x
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (remove-assoc-equal x (frame->frame frame))))
        (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
      (consp (frame->frame frame))
      (equal
       (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
      (abs-separate (frame->frame frame))
      (integerp x)
      (< 0 x)
      (< 0
         (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
      (< 0 (1st-complete (frame->frame frame)))
      (consp
       (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                    (frame->frame frame)))
      (prefixp
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
      (context-apply-ok
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (1st-complete (frame->frame frame))
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
      (mv-nth
       1
       (collapse
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (frame-val->dir
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame))))
            (1st-complete (frame->frame frame))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (remove-assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))
      (not
       (consp
        (abs-addrs
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
      (frame-p (frame->frame frame))
      (no-duplicatesp-equal (strip-cars (frame->frame frame))))
     (absfat-equiv
      (context-apply
       (context-apply
        (frame-val->dir
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
        (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
        x
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (1st-complete (frame->frame frame))
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
      (context-apply
       (context-apply
        (frame-val->dir
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
        (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (1st-complete (frame->frame frame))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
       x
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))))
    :hints
    (("goal"
      :use
      (:instance
       (:rewrite context-apply-of-context-apply-1)
       (y-path
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))))
       (y-var (1st-complete (frame->frame frame)))
       (y (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
       (z-path
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
       (z-var x)
       (z (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
       (x
        (frame-val->dir
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))))))

  (local
   (defthm
     lemma-2
     (implies
      (and
       (not
        (equal
         (1st-complete
          (put-assoc-equal
           (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
           (frame-val
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (context-apply
             (frame-val->dir
              (cdr
               (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame))))
             (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
             x
             (nthcdr
              (len
               (frame-val->path
                (cdr
                 (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))))
              (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
            (frame-val->src
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))
           (remove-assoc-equal x (frame->frame frame))))
         (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
       (not (equal x (1st-complete (frame->frame frame))))
       (consp (frame->frame frame))
       (equal
        (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
       (abs-separate (frame->frame frame))
       (integerp x)
       (< 0 x)
       (< 0
          (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
       (< 0 (1st-complete (frame->frame frame)))
       (consp
        (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                     (frame->frame frame)))
       (prefixp
        (frame-val->path
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame)))))
       (context-apply-ok
        (frame-val->dir
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
        (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (1st-complete (frame->frame frame))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))))
       (mv-nth
        1
        (collapse
         (frame-with-root
          (frame->root frame)
          (put-assoc-equal
           (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
           (frame-val
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (context-apply
             (frame-val->dir
              (cdr
               (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame))))
             (frame-val->dir
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))
             (1st-complete (frame->frame frame))
             (nthcdr
              (len
               (frame-val->path
                (cdr
                 (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))))
              (frame-val->path
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))))
            (frame-val->src
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))
           (remove-assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame))))))
       (not
        (consp
         (abs-addrs
          (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
       (frame-p (frame->frame frame))
       (no-duplicatesp-equal (strip-cars (frame->frame frame)))
       (not (consp (assoc-equal 0 (frame->frame frame)))))
      (absfat-equiv
       (context-apply
        (context-apply
         (frame-val->dir
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame))))
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
         x
         (nthcdr
          (len
           (frame-val->path
            (cdr (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))))
          (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
        (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (1st-complete (frame->frame frame))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))))
       (context-apply
        (context-apply
         (frame-val->dir
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame))))
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))))
          (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                             (frame->frame frame))))))
        (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
        x
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))))
     :hints
     (("goal"
       :in-theory
       (e/d (collapse abs-separate 1st-complete-src)
            ((:definition assoc-equal)
             (:definition remove-assoc-equal)
             (:rewrite put-assoc-equal-without-change . 2)
             (:rewrite nthcdr-when->=-n-len-l)
             (:rewrite abs-file-alist-p-when-m1-file-alist-p)
             m1-file-alist-p-of-cdr-when-m1-file-alist-p
             (:definition member-equal)
             (:definition remove-equal)
             (:rewrite remove-when-absent)
             (:definition nthcdr)
             (:definition len)
             (:rewrite remove-assoc-when-absent)
             (:rewrite partial-collapse-correctness-lemma-43)
             (:definition put-assoc-equal)
             (:rewrite remove-assoc-of-put-assoc)
             (:rewrite abs-fs-p-of-context-apply)
             (:rewrite partial-collapse-correctness-lemma-45
                       . 2)
             (:rewrite assoc-after-put-assoc)
             (:rewrite abs-addrs-of-context-apply-1-lemma-14)
             (:rewrite consp-of-remove-assoc-1)
             (:rewrite abs-find-file-correctness-1-lemma-21)
             (:rewrite partial-collapse-correctness-lemma-63)
             (:rewrite abs-addrs-of-context-apply-1-lemma-7)
             (:rewrite partial-collapse-correctness-lemma-15)
             (:rewrite len-of-remove-assoc-equal-2)
             (:rewrite strip-cars-of-put-assoc)
             (:rewrite abs-find-file-correctness-1-lemma-9)))
       :cases
       ((and
         (not
          (equal
           (nthcdr
            (len
             (frame-val->path$inline
              (cdr (assoc-equal (frame-val->src$inline
                                 (cdr (assoc-equal x (frame->frame frame))))
                                (frame->frame frame)))))
            (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame)))))
           (nthcdr
            (len
             (frame-val->path$inline
              (cdr (assoc-equal (frame-val->src$inline
                                 (cdr (assoc-equal x (frame->frame frame))))
                                (frame->frame frame)))))
            (frame-val->path$inline
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame)))))))
         (not
          (prefixp
           (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame))))
           (frame-val->path$inline
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))
         (prefixp
          (frame-val->path$inline
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
          (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame))))))
        (and
         (not
          (equal
           (nthcdr
            (len
             (frame-val->path$inline
              (cdr (assoc-equal (frame-val->src$inline
                                 (cdr (assoc-equal x (frame->frame frame))))
                                (frame->frame frame)))))
            (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame)))))
           (nthcdr
            (len
             (frame-val->path$inline
              (cdr (assoc-equal (frame-val->src$inline
                                 (cdr (assoc-equal x (frame->frame frame))))
                                (frame->frame frame)))))
            (frame-val->path$inline
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame)))))))
         (prefixp
          (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame))))
          (frame-val->path$inline
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))))
         (not
          (member-equal
           (nth
            (len
             (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame)))))
            (frame-val->path$inline
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame)))))
           (names-at
            (frame-val->dir$inline
             (cdr
              (assoc-equal
               (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (nthcdr
             (len
              (frame-val->path$inline
               (cdr (assoc-equal (frame-val->src$inline
                                  (cdr (assoc-equal x (frame->frame frame))))
                                 (frame->frame frame)))))
             (frame-val->path$inline
              (cdr (assoc-equal x (frame->frame frame))))))))
         (prefixp
          (frame-val->path$inline
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
          (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame))))))
        (and
         (not
          (equal
           (nthcdr
            (len
             (frame-val->path$inline
              (cdr (assoc-equal (frame-val->src$inline
                                 (cdr (assoc-equal x (frame->frame frame))))
                                (frame->frame frame)))))
            (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame)))))
           (nthcdr
            (len
             (frame-val->path$inline
              (cdr (assoc-equal (frame-val->src$inline
                                 (cdr (assoc-equal x (frame->frame frame))))
                                (frame->frame frame)))))
            (frame-val->path$inline
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame)))))))
         (prefixp
          (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame))))
          (frame-val->path$inline
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))))
         (not
          (member-equal
           (nth
            (len
             (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame)))))
            (frame-val->path$inline
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame)))))
           (names-at
            (frame-val->dir$inline
             (cdr
              (assoc-equal
               (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (nthcdr
             (len
              (frame-val->path$inline
               (cdr (assoc-equal (frame-val->src$inline
                                  (cdr (assoc-equal x (frame->frame frame))))
                                 (frame->frame frame)))))
             (frame-val->path$inline
              (cdr (assoc-equal x (frame->frame frame))))))))
         (not
          (prefixp
           (frame-val->path$inline
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
           (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame)))))))
        (and
         (not
          (equal
           (nthcdr
            (len
             (frame-val->path$inline
              (cdr (assoc-equal (frame-val->src$inline
                                 (cdr (assoc-equal x (frame->frame frame))))
                                (frame->frame frame)))))
            (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame)))))
           (nthcdr
            (len
             (frame-val->path$inline
              (cdr (assoc-equal (frame-val->src$inline
                                 (cdr (assoc-equal x (frame->frame frame))))
                                (frame->frame frame)))))
            (frame-val->path$inline
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame)))))))
         (prefixp
          (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame))))
          (frame-val->path$inline
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))))
         (member-equal
          (nth
           (len
            (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame)))))
           (frame-val->path$inline
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame)))))
          (names-at
           (frame-val->dir$inline
            (cdr
             (assoc-equal
              (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
           (nthcdr
            (len
             (frame-val->path$inline
              (cdr (assoc-equal (frame-val->src$inline
                                 (cdr (assoc-equal x (frame->frame frame))))
                                (frame->frame frame)))))
            (frame-val->path$inline
             (cdr (assoc-equal x (frame->frame frame)))))))
         (prefixp
          (frame-val->path$inline
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
          (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame))))))
        (and
         (not
          (equal
           (nthcdr
            (len
             (frame-val->path$inline
              (cdr (assoc-equal (frame-val->src$inline
                                 (cdr (assoc-equal x (frame->frame frame))))
                                (frame->frame frame)))))
            (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame)))))
           (nthcdr
            (len
             (frame-val->path$inline
              (cdr (assoc-equal (frame-val->src$inline
                                 (cdr (assoc-equal x (frame->frame frame))))
                                (frame->frame frame)))))
            (frame-val->path$inline
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame)))))))
         (prefixp
          (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame))))
          (frame-val->path$inline
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))))
         (member-equal
          (nth
           (len
            (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame)))))
           (frame-val->path$inline
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame)))))
          (names-at
           (frame-val->dir$inline
            (cdr
             (assoc-equal
              (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
           (nthcdr
            (len
             (frame-val->path$inline
              (cdr (assoc-equal (frame-val->src$inline
                                 (cdr (assoc-equal x (frame->frame frame))))
                                (frame->frame frame)))))
            (frame-val->path$inline
             (cdr (assoc-equal x (frame->frame frame)))))))
         (not
          (prefixp
           (frame-val->path$inline
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
           (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame)))))))
        (equal
         (nthcdr
          (len
           (frame-val->path$inline
            (cdr
             (assoc-equal
              (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame)))))
         (nthcdr
          (len
           (frame-val->path$inline
            (cdr
             (assoc-equal
              (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (frame-val->path$inline
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))))))))))

  (local
   (defthm
     lemma-3
     (implies
      (and
       (equal
        (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                     (frame->frame frame))
        (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                     (remove-assoc-equal
                      x
                      (remove-assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
       (mv-nth
        1
        (collapse
         (frame-with-root
          (frame->root frame)
          (put-assoc-equal
           (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
           (frame-val
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (context-apply
             (context-apply
              (frame-val->dir
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame))))
              (frame-val->dir
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))
              (1st-complete (frame->frame frame))
              (nthcdr
               (len
                (frame-val->path
                 (cdr
                  (assoc-equal
                   (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                   (frame->frame frame)))))
               (frame-val->path
                (cdr (assoc-equal (1st-complete (frame->frame frame))
                                  (frame->frame frame))))))
             (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
             x
             (nthcdr
              (len
               (frame-val->path
                (cdr
                 (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))))
              (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
            (frame-val->src
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))
           (remove-assoc-equal
            x
            (remove-assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame)))))))
       (frame-p
        (put-assoc-equal
         (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
         (frame-val
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame))))
          (context-apply
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                              (frame->frame frame))))
            (1st-complete (frame->frame frame))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))))
           (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
           x
           (nthcdr
            (len
             (frame-val->path
              (cdr
               (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
            (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
          (frame-val->src
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
         (remove-assoc-equal
          x
          (remove-assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame)))))
       (case-split
        (abs-separate
         (put-assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame))))
           (context-apply
            (context-apply
             (frame-val->dir
              (cdr
               (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame))))
             (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                               (frame->frame frame))))
             (1st-complete (frame->frame frame))
             (nthcdr
              (len
               (frame-val->path
                (cdr
                 (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))))
              (frame-val->path
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))))
            (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
            x
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
           (frame-val->src
            (cdr (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))))
          (remove-assoc-equal
           x
           (remove-assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame))))))
       (no-duplicatesp-equal
        (remove-equal x
                      (remove-equal (1st-complete (frame->frame frame))
                                    (strip-cars (frame->frame frame)))))
       (not (equal 0
                   (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
       (not
        (consp (assoc-equal
                0
                (remove-assoc-equal
                 x
                 (remove-assoc-equal (1st-complete (frame->frame frame))
                                     (frame->frame frame))))))
       (absfat-equiv
        (context-apply
         (context-apply
          (frame-val->dir
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame))))
          (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))
          (1st-complete (frame->frame frame))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))
           (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                              (frame->frame frame))))))
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
         x
         (nthcdr
          (len
           (frame-val->path
            (cdr (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))))
          (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
        (context-apply
         (context-apply
          (frame-val->dir
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame))))
          (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
          x
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))
           (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))))
          (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                             (frame->frame frame)))))))
       (case-split
        (dist-names
         (frame->root frame)
         nil
         (put-assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame))))
           (context-apply
            (context-apply
             (frame-val->dir
              (cdr
               (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame))))
             (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                               (frame->frame frame))))
             (1st-complete (frame->frame frame))
             (nthcdr
              (len
               (frame-val->path
                (cdr
                 (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))))
              (frame-val->path
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))))
            (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
            x
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
           (frame-val->src
            (cdr (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))))
          (remove-assoc-equal
           x
           (remove-assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame)))))))
      (mv-nth
       1
       (collapse
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame))))
           (context-apply
            (context-apply
             (frame-val->dir
              (cdr
               (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame))))
             (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
             x
             (nthcdr
              (len
               (frame-val->path
                (cdr
                 (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))))
              (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
            (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                              (frame->frame frame))))
            (1st-complete (frame->frame frame))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))))
           (frame-val->src
            (cdr (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))))
          (remove-assoc-equal
           x
           (remove-assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame))))))))
     :hints
     (("goal"
       :in-theory (disable partial-collapse-correctness-lemma-59)
       :use
       (:instance
        partial-collapse-correctness-lemma-59
        (frame (remove-assoc-equal
                x
                (remove-assoc-equal (1st-complete (frame->frame frame))
                                    (frame->frame frame))))
        (dir2
         (context-apply
          (context-apply
           (frame-val->dir
            (cdr (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame))))
           (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
           x
           (nthcdr
            (len
             (frame-val->path
              (cdr
               (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
            (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
          (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))
          (1st-complete (frame->frame frame))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))
           (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                              (frame->frame frame)))))))
        (other-frame (frame->frame frame))
        (x (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
        (root (frame->root frame))
        (dir1
         (context-apply
          (context-apply
           (frame-val->dir
            (cdr (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame))))
           (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                             (frame->frame frame))))
           (1st-complete (frame->frame frame))
           (nthcdr
            (len
             (frame-val->path
              (cdr
               (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
            (frame-val->path
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame))))))
          (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
          x
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))
           (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))))))))

  (defthm
    partial-collapse-correctness-lemma-6
    (implies
     (and
      (equal
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
      (abs-separate (frame->frame frame))
      (< 0 (1st-complete (frame->frame frame)))
      (prefixp
       (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
      (context-apply-ok
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (1st-complete (frame->frame frame))
       (nthcdr
        (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))))
      (frame-p (frame->frame frame))
      (no-duplicatesp-equal (strip-cars (frame->frame frame))))
     (not
      (intersectp-equal
       (names-at (frame-val->dir$inline
                  (cdr (assoc-equal (1st-complete (frame->frame frame))
                                    (frame->frame frame))))
                 nil)
       (names-at
        (frame-val->dir$inline
         (cdr
          (assoc-equal
           (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
           (frame->frame frame))))
        (nthcdr
         (len
          (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame)))))
         (frame-val->path$inline
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))))))
    :hints
    (("goal"
      :in-theory
      (e/d (collapse abs-separate 1st-complete-src)
           ((:definition assoc-equal)
            (:definition remove-assoc-equal)
            (:rewrite put-assoc-equal-without-change . 2)
            (:rewrite nthcdr-when->=-n-len-l)
            (:rewrite abs-file-alist-p-when-m1-file-alist-p)
            m1-file-alist-p-of-cdr-when-m1-file-alist-p
            (:definition member-equal)
            (:definition remove-equal)
            (:rewrite remove-when-absent)
            (:definition len)
            (:rewrite remove-assoc-when-absent)
            lemma-3))
      :expand
      (:with
       (:rewrite abs-separate-correctness-1-lemma-14 . 2)
       (intersectp-equal
        (names-at (frame-val->dir$inline
                   (cdr (assoc-equal (1st-complete (frame->frame frame))
                                     (frame->frame frame))))
                  nil)
        (names-at
         (frame-val->dir$inline
          (cdr
           (assoc-equal
            (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
         (nthcdr
          (len
           (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame)))))
          (frame-val->path$inline
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))))))))))

  ;; Move later.
  (defthm
    partial-collapse-correctness-lemma-26
    (fat32-filename-list-equiv
     (nthcdr (len l) l)
     nil))

  (defthm
    partial-collapse-correctness-lemma-7
    (implies
     (and
      (equal
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
      (not (equal x (1st-complete (frame->frame frame))))
      (equal
       (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
      (abs-separate (frame->frame frame))
      (< 0 (1st-complete (frame->frame frame)))
      (consp
       (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                    (frame->frame frame)))
      (prefixp
       (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
      (context-apply-ok
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (1st-complete (frame->frame frame))
       (nthcdr
        (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))))
      (not
       (consp
        (abs-addrs
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
      (frame-p (frame->frame frame))
      (no-duplicatesp-equal (strip-cars (frame->frame frame))))
     (dist-names
      (context-apply
       (context-apply
        (frame-val->dir
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
        (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (1st-complete (frame->frame frame))
        (nthcdr
         (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))))
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
       x nil)
      (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
      (remove-assoc-equal
       x
       (remove-assoc-equal
        (1st-complete (frame->frame frame))
        (remove-assoc-equal
         (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
         (frame->frame frame))))))
    :hints
    (("goal"
      :in-theory (disable (:rewrite abs-separate-of-put-assoc-lemma-14))
      :use
      ((:instance
        (:rewrite abs-separate-of-put-assoc-lemma-14)
        (frame
         (remove-assoc-equal
          x
          (remove-assoc-equal
           (1st-complete (frame->frame frame))
           (remove-assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame)))))
        (relpath (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
        (x-path nil)
        (x x)
        (abs-file-alist2
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
        (abs-file-alist1
         (context-apply
          (frame-val->dir
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame))))
          (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))
          (1st-complete (frame->frame frame))
          (nthcdr
           (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
           (frame-val->path
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))))
       (:instance
        abs-separate-of-put-assoc-lemma-14
        (frame
         (remove-assoc-equal
          x
          (remove-assoc-equal
           (1st-complete (frame->frame frame))
           (remove-assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame)))))
        (relpath (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
        (x-path
         (nthcdr
          (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
          (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                             (frame->frame frame))))))
        (x (1st-complete (frame->frame frame)))
        (abs-file-alist2
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame)))))
        (abs-file-alist1
         (frame-val->dir
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame))))))))))

  (defthm
    partial-collapse-correctness-lemma-51
    (implies
     (and
      (equal
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
      (not (equal x (1st-complete (frame->frame frame))))
      (equal
       (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
      (abs-separate (frame->frame frame))
      (< 0 (1st-complete (frame->frame frame)))
      (consp
       (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                    (frame->frame frame)))
      (prefixp
       (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
      (context-apply-ok
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (1st-complete (frame->frame frame))
       (nthcdr
        (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))))
      (not
       (consp
        (abs-addrs
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
      (frame-p (frame->frame frame))
      (no-duplicatesp-equal (strip-cars (frame->frame frame)))
      (not (consp (assoc-equal 0 (frame->frame frame)))))
     (absfat-equiv
      (context-apply
       (context-apply
        (frame-val->dir
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
        (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (1st-complete (frame->frame frame))
        (nthcdr
         (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))))
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
       x nil)
      (context-apply
       (context-apply
        (frame-val->dir
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
        (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
        x nil)
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (1st-complete (frame->frame frame))
       (nthcdr
        (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))))))
    :hints
    (("goal"
      :in-theory
      (disable (:definition assoc-equal)
               (:definition remove-assoc-equal)
               (:rewrite put-assoc-equal-without-change . 2)
               (:rewrite nthcdr-when->=-n-len-l)
               (:rewrite abs-file-alist-p-when-m1-file-alist-p)
               m1-file-alist-p-of-cdr-when-m1-file-alist-p
               (:definition member-equal)
               (:definition remove-equal)
               (:rewrite remove-when-absent)
               (:definition len)
               (:rewrite remove-assoc-when-absent)
               lemma-3)
      :use
      (:instance
       (:rewrite context-apply-of-context-apply-1)
       (y-path nil)
       (y-var x)
       (y (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
       (z-path
        (nthcdr
         (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))))
       (z-var (1st-complete (frame->frame frame)))
       (z (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
       (x
        (frame-val->dir
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))))))

  (defthm
    partial-collapse-correctness-lemma-16
    (implies
     (and
      (< 0 (1st-complete (frame->frame frame)))
      (context-apply-ok
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (1st-complete (frame->frame frame))
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))))
      (frame-p (frame->frame frame))
      (no-duplicatesp-equal (strip-cars (frame->frame frame))))
     (not
      (equal
       (1st-complete (frame->frame frame))
       (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame)))))))
    :hints
    (("goal" :in-theory (e/d (collapse 1st-complete-src)
                             ((:definition assoc-equal)
                              (:definition remove-assoc-equal)
                              (:rewrite put-assoc-equal-without-change . 2)
                              (:rewrite nthcdr-when->=-n-len-l)
                              (:rewrite abs-file-alist-p-when-m1-file-alist-p)
                              m1-file-alist-p-of-cdr-when-m1-file-alist-p
                              (:definition member-equal)
                              (:definition remove-equal)
                              (:rewrite remove-when-absent)
                              (:definition len)
                              (:rewrite remove-assoc-when-absent))))))

  (defthm
    partial-collapse-correctness-lemma-55
    (implies
     (and
      (not
       (equal
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
      (prefixp
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
       (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
      (not
       (equal
        (1st-complete
         (put-assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
            x
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (remove-assoc-equal x (frame->frame frame))))
        (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
      (not (equal x (1st-complete (frame->frame frame))))
      (equal
       (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
      (abs-separate (frame->frame frame))
      (dist-names (frame->root frame)
                  nil (frame->frame frame))
      (< 0 (1st-complete (frame->frame frame)))
      (consp
       (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                    (frame->frame frame)))
      (prefixp
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
      (context-apply-ok
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (1st-complete (frame->frame frame))
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))))
      (not
       (consp
        (abs-addrs
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
      (frame-p (frame->frame frame))
      (no-duplicatesp-equal (strip-cars (frame->frame frame))))
     (not
      (intersectp-equal
       (names-at
        (frame->root frame)
        (frame-val->path
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))
       (names-at
        (context-apply
         (context-apply
          (frame-val->dir
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame))))
          (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))
          (1st-complete (frame->frame frame))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))
           (frame-val->path
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
         x
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
        nil))))
    :hints
    (("goal"
      :in-theory
      (e/d
       (collapse 1st-complete-src)
       ((:definition assoc-equal)
        (:definition remove-assoc-equal)
        (:rewrite put-assoc-equal-without-change . 2)
        (:rewrite nthcdr-when->=-n-len-l)
        (:rewrite abs-file-alist-p-when-m1-file-alist-p)
        m1-file-alist-p-of-cdr-when-m1-file-alist-p
        (:definition member-equal)
        (:definition remove-equal)
        (:rewrite remove-when-absent)
        (:definition len)
        (:rewrite remove-assoc-when-absent)))
      :cases
      ((member-equal
        (nth
         (len (frame-val->path$inline
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame)))))
         (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame)))))
        (names-at
         (frame-val->dir$inline
          (cdr
           (assoc-equal
            (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
         (nthcdr
          (len
           (frame-val->path$inline
            (cdr
             (assoc-equal
              (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (frame-val->path$inline
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))))))))))

  (defthm
    partial-collapse-correctness-lemma-17
    (implies
     (and
      (not
       (equal
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame)))))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
      (prefixp
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
       (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
      (not
       (equal
        (1st-complete
         (put-assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
            x
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (remove-assoc-equal x (frame->frame frame))))
        (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
      (not (equal x (1st-complete (frame->frame frame))))
      (consp (frame->frame frame))
      (equal
       (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
      (abs-separate (frame->frame frame))
      (integerp x)
      (< 0 x)
      (< 0
         (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
      (< 0 (1st-complete (frame->frame frame)))
      (consp
       (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                    (frame->frame frame)))
      (prefixp
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
      (context-apply-ok
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (1st-complete (frame->frame frame))
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))))
      (mv-nth
       1
       (collapse
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (frame-val->dir
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame))))
            (1st-complete (frame->frame frame))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (remove-assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))
      (not
       (consp
        (abs-addrs
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
      (frame-p (frame->frame frame))
      (no-duplicatesp-equal (strip-cars (frame->frame frame))))
     (abs-separate
      (put-assoc-equal
       (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
       (frame-val
        (frame-val->path
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
        (context-apply
         (context-apply
          (frame-val->dir
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame))))
          (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))
          (1st-complete (frame->frame frame))
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))
           (frame-val->path
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
         x
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
        (frame-val->src
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame)))))
       (remove-assoc-equal
        x
        (remove-assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))))
    :hints
    (("goal"
      :in-theory
      (e/d (collapse abs-separate 1st-complete-src)
           ((:definition assoc-equal)
            (:definition remove-assoc-equal)
            (:rewrite put-assoc-equal-without-change . 2)
            (:rewrite nthcdr-when->=-n-len-l)
            (:rewrite abs-file-alist-p-when-m1-file-alist-p)
            m1-file-alist-p-of-cdr-when-m1-file-alist-p
            (:definition member-equal)
            (:definition remove-equal)
            (:rewrite remove-when-absent)
            (:definition len)
            (:rewrite remove-assoc-when-absent)
            (:REWRITE
             PARTIAL-COLLAPSE-CORRECTNESS-LEMMA-88)
            (:DEFINITION PUT-ASSOC-EQUAL)
            (:rewrite remove-assoc-of-put-assoc)
            (:rewrite
             partial-collapse-correctness-lemma-45
             . 2)
            (:rewrite strip-cars-of-put-assoc)
            (:rewrite
             partial-collapse-correctness-lemma-15)))
      :cases
      ((member-equal
        (nth
         (len (frame-val->path$inline
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame)))))
         (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame)))))
        (names-at
         (frame-val->dir$inline
          (cdr
           (assoc-equal
            (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
         (nthcdr
          (len
           (frame-val->path$inline
            (cdr
             (assoc-equal
              (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (frame-val->path$inline
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))))))))))

  (defthm
    partial-collapse-correctness-lemma-18
    (implies
     (and
      (equal
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame)))))
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
      (not
       (equal
        (1st-complete
         (put-assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
            x
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (remove-assoc-equal x (frame->frame frame))))
        (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
      (not (equal x (1st-complete (frame->frame frame))))
      (consp (frame->frame frame))
      (equal
       (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
      (abs-separate (frame->frame frame))
      (integerp x)
      (< 0 x)
      (< 0
         (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
      (< 0 (1st-complete (frame->frame frame)))
      (consp
       (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                    (frame->frame frame)))
      (prefixp
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
      (context-apply-ok
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (1st-complete (frame->frame frame))
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
      (mv-nth
       1
       (collapse
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (frame-val->dir
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame))))
            (1st-complete (frame->frame frame))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (remove-assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))
      (frame-p (frame->frame frame))
      (no-duplicatesp-equal (strip-cars (frame->frame frame))))
     (dist-names
      (context-apply
       (context-apply
        (frame-val->dir
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
        (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (1st-complete (frame->frame frame))
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
       x
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
      (frame-val->path
       (cdr
        (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                     (frame->frame frame))))
      (remove-assoc-equal
       x
       (remove-assoc-equal
        (1st-complete (frame->frame frame))
        (remove-assoc-equal
         (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
         (frame->frame frame))))))
    :hints
    (("goal"
      :in-theory (e/d (collapse abs-separate 1st-complete-src)
                      ((:definition assoc-equal)
                       (:definition remove-assoc-equal)
                       (:rewrite put-assoc-equal-without-change . 2)
                       (:rewrite nthcdr-when->=-n-len-l)
                       (:rewrite abs-file-alist-p-when-m1-file-alist-p)
                       m1-file-alist-p-of-cdr-when-m1-file-alist-p
                       (:definition member-equal)
                       (:definition remove-equal)
                       (:rewrite remove-when-absent)
                       (:definition len)
                       (:rewrite remove-assoc-when-absent)
                       (:rewrite partial-collapse-correctness-lemma-88)
                       (:definition put-assoc-equal)
                       (:rewrite remove-assoc-of-put-assoc)
                       (:rewrite partial-collapse-correctness-lemma-45
                                 . 2)
                       (:rewrite strip-cars-of-put-assoc)
                       (:rewrite partial-collapse-correctness-lemma-15)
                       append-when-prefixp))
      :use
      ((:instance
        append-when-prefixp
        (x
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (y
         (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                            (frame->frame frame))))))
       (:instance
        append-when-prefixp
        (x
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (y (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))))))

  (defthm
    partial-collapse-correctness-lemma-23
    (implies
     (and
      (context-apply-ok
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (1st-complete (frame->frame frame))
       nil)
      (equal
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
      (equal
       (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
      (mv-nth
       1
       (collapse
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (frame-val->dir
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame))))
            (1st-complete (frame->frame frame))
            nil)
           (frame-val->src
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (remove-assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))
      (< 0
         (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
      (frame-p (frame->frame frame))
      (no-duplicatesp-equal (strip-cars (frame->frame frame)))
      (not (consp (assoc-equal 0 (frame->frame frame)))))
     (prefixp
      (frame-val->path$inline
       (cdr (assoc-equal (1st-complete (frame->frame frame))
                         (frame->frame frame))))
      (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame))))))
    :hints
    (("goal"
      :in-theory (e/d (collapse abs-separate 1st-complete-src)
                      ((:definition assoc-equal)
                       (:definition remove-assoc-equal)
                       (:rewrite put-assoc-equal-without-change . 2)
                       (:rewrite nthcdr-when->=-n-len-l)
                       (:rewrite abs-file-alist-p-when-m1-file-alist-p)
                       m1-file-alist-p-of-cdr-when-m1-file-alist-p
                       (:definition member-equal)
                       (:definition remove-equal)
                       (:rewrite remove-when-absent)
                       (:definition len)
                       (:rewrite remove-assoc-when-absent)
                       (:rewrite partial-collapse-correctness-lemma-88)
                       (:rewrite partial-collapse-correctness-lemma-43)
                       (:rewrite partial-collapse-correctness-lemma-42)
                       (:linear 1st-complete-of-put-assoc-1)
                       (:rewrite intersectp-is-commutative)
                       (:rewrite remove-assoc-of-put-assoc)
                       (:rewrite partial-collapse-correctness-lemma-15)
                       (:rewrite partial-collapse-correctness-lemma-61)
                       (:rewrite 1st-complete-of-put-assoc-3)
                       (:rewrite strip-cars-of-put-assoc)
                       (:rewrite len-of-remove-assoc-equal-2)
                       (:rewrite 1st-complete-of-put-assoc-2)
                       (:rewrite abs-separate-correctness-1-lemma-14 . 2)
                       (:definition put-assoc-equal)
                       (:definition nthcdr)
                       (:rewrite abs-find-file-correctness-1-lemma-21)
                       (:rewrite abs-find-file-correctness-1-lemma-9)
                       (:rewrite partial-collapse-correctness-lemma-32)))
      :expand
      (:with
       (:rewrite partial-collapse-correctness-lemma-45
                 . 3)
       (prefixp
        (frame-val->path$inline
         (cdr (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
        (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame)))))))))

  (defthm
    partial-collapse-correctness-lemma-91
    (implies
     (and
      (equal
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame)))))
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
      (not
       (equal
        (1st-complete
         (put-assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
            x
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (remove-assoc-equal x (frame->frame frame))))
        (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
      (not (equal x (1st-complete (frame->frame frame))))
      (consp (frame->frame frame))
      (equal
       (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
      (mv-nth
       1
       (collapse
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
           (context-apply
            (context-apply
             (frame-val->dir
              (cdr
               (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame))))
             (frame-val->dir
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))
             (1st-complete (frame->frame frame))
             (nthcdr
              (len
               (frame-val->path
                (cdr
                 (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))))
              (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
            (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
            x
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (remove-assoc-equal
           x
           (remove-assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame)))))))
      (abs-separate (frame->frame frame))
      (dist-names (frame->root frame)
                  nil (frame->frame frame))
      (integerp x)
      (< 0 x)
      (< 0
         (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
      (< 0 (1st-complete (frame->frame frame)))
      (consp
       (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                    (frame->frame frame)))
      (prefixp
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
      (context-apply-ok
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (1st-complete (frame->frame frame))
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
      (mv-nth
       1
       (collapse
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (frame-val->dir
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame))))
            (1st-complete (frame->frame frame))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (remove-assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))
      (not
       (consp
        (abs-addrs
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
      (frame-p (frame->frame frame))
      (no-duplicatesp-equal (strip-cars (frame->frame frame)))
      (not (consp (assoc-equal 0 (frame->frame frame)))))
     (mv-nth
      1
      (collapse
       (frame-with-root
        (frame->root frame)
        (put-assoc-equal
         (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
         (frame-val
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame))))
          (context-apply
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
            x
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
           (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                             (frame->frame frame))))
           (1st-complete (frame->frame frame))
           (nthcdr
            (len
             (frame-val->path
              (cdr
               (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
            (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
          (frame-val->src
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
         (remove-assoc-equal
          x
          (remove-assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))))
    :hints
    (("goal" :in-theory (e/d (collapse abs-separate 1st-complete-src)
                             ((:definition assoc-equal)
                              (:definition remove-assoc-equal)
                              (:rewrite put-assoc-equal-without-change . 2)
                              (:rewrite nthcdr-when->=-n-len-l)
                              (:rewrite abs-file-alist-p-when-m1-file-alist-p)
                              m1-file-alist-p-of-cdr-when-m1-file-alist-p
                              (:definition member-equal)
                              (:definition remove-equal)
                              (:rewrite remove-when-absent)
                              (:definition len)
                              (:rewrite remove-assoc-when-absent)
                              (:rewrite remove-assoc-of-put-assoc)
                              (:rewrite strip-cars-of-put-assoc)
                              (:rewrite partial-collapse-correctness-lemma-15)
                              (:definition put-assoc-equal)
                              (:rewrite assoc-after-put-assoc)
                              (:rewrite consp-of-remove-assoc-1)
                              (:rewrite partial-collapse-correctness-lemma-45
                                        . 2)
                              (:rewrite abs-find-file-correctness-1-lemma-21)
                              (:rewrite len-of-remove-assoc-equal-2)
                              (:rewrite abs-addrs-of-context-apply-1-lemma-7)
                              (:rewrite abs-find-file-correctness-1-lemma-9)
                              (:rewrite partial-collapse-correctness-lemma-32)
                              (:linear count-free-clusters-correctness-1)
                              lemma-3))
      :use lemma-3)))

  (defthm
    partial-collapse-correctness-lemma-99
    (implies
     (and
      (not
       (equal
        (1st-complete
         (put-assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
            x
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (remove-assoc-equal x (frame->frame frame))))
        (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
      (not (equal x (1st-complete (frame->frame frame))))
      (consp (frame->frame frame))
      (equal
       (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
      (mv-nth
       1
       (collapse
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
           (context-apply
            (context-apply
             (frame-val->dir
              (cdr
               (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame))))
             (frame-val->dir
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))
             (1st-complete (frame->frame frame))
             (nthcdr
              (len
               (frame-val->path
                (cdr
                 (assoc-equal
                  (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))))
              (frame-val->path
               (cdr (assoc-equal (1st-complete (frame->frame frame))
                                 (frame->frame frame))))))
            (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
            x
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (remove-assoc-equal
           x
           (remove-assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame)))))))
      (abs-separate (frame->frame frame))
      (dist-names (frame->root frame)
                  nil (frame->frame frame))
      (integerp x)
      (< 0 x)
      (< 0
         (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
      (< 0 (1st-complete (frame->frame frame)))
      (consp
       (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                    (frame->frame frame)))
      (prefixp
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame)))))
      (context-apply-ok
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (1st-complete (frame->frame frame))
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame))))))
      (mv-nth
       1
       (collapse
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (frame-val->dir
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame))))
            (1st-complete (frame->frame frame))
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path
              (cdr (assoc-equal (1st-complete (frame->frame frame))
                                (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (remove-assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))
      (not
       (consp
        (abs-addrs
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
      (frame-p (frame->frame frame))
      (no-duplicatesp-equal (strip-cars (frame->frame frame)))
      (not (consp (assoc-equal 0 (frame->frame frame)))))
     (mv-nth
      1
      (collapse
       (frame-with-root
        (frame->root frame)
        (put-assoc-equal
         (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
         (frame-val
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame))))
          (context-apply
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               (frame->frame frame))))
            (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
            x
            (nthcdr
             (len
              (frame-val->path
               (cdr
                (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
           (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                             (frame->frame frame))))
           (1st-complete (frame->frame frame))
           (nthcdr
            (len
             (frame-val->path
              (cdr
               (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
            (frame-val->path
             (cdr (assoc-equal (1st-complete (frame->frame frame))
                               (frame->frame frame))))))
          (frame-val->src
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame)))))
         (remove-assoc-equal
          x
          (remove-assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))))
    :hints
    (("goal"
      :in-theory (e/d (collapse abs-separate 1st-complete-src)
                      ((:definition assoc-equal)
                       (:definition remove-assoc-equal)
                       (:rewrite put-assoc-equal-without-change . 2)
                       (:rewrite nthcdr-when->=-n-len-l)
                       (:rewrite abs-file-alist-p-when-m1-file-alist-p)
                       m1-file-alist-p-of-cdr-when-m1-file-alist-p
                       (:definition member-equal)
                       (:definition remove-equal)
                       (:rewrite remove-when-absent)
                       (:definition len)
                       (:rewrite remove-assoc-when-absent)
                       (:rewrite
                        partial-collapse-correctness-lemma-43)
                       (:rewrite remove-assoc-of-put-assoc)
                       (:rewrite
                        partial-collapse-correctness-lemma-88)
                       (:rewrite strip-cars-of-put-assoc)
                       (:definition put-assoc-equal)
                       (:rewrite
                        partial-collapse-correctness-lemma-45
                        . 2)
                       (:rewrite assoc-after-put-assoc)
                       (:rewrite consp-of-remove-assoc-1)
                       (:rewrite
                        partial-collapse-correctness-lemma-15)
                       (:rewrite
                        partial-collapse-correctness-lemma-59)
                       (:rewrite
                        partial-collapse-correctness-lemma-87)
                       (:rewrite
                        abs-find-file-correctness-1-lemma-21)
                       (:rewrite
                        partial-collapse-correctness-lemma-59)))
      :cases
      ((and
        (not
         (equal
          (nthcdr
           (len
            (frame-val->path$inline
             (cdr (assoc-equal (frame-val->src$inline
                                (cdr (assoc-equal x (frame->frame frame))))
                               (frame->frame frame)))))
           (frame-val->path$inline
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame)))))
          (nthcdr
           (len
            (frame-val->path$inline
             (cdr (assoc-equal (frame-val->src$inline
                                (cdr (assoc-equal x (frame->frame frame))))
                               (frame->frame frame)))))
           (frame-val->path$inline
            (cdr (assoc-equal x (frame->frame frame)))))))
        (not
         (prefixp
          (frame-val->path$inline
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
          (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame))))))
        (not
         (prefixp
          (nthcdr
           (len
            (frame-val->path$inline
             (cdr (assoc-equal (frame-val->src$inline
                                (cdr (assoc-equal x (frame->frame frame))))
                               (frame->frame frame)))))
           (frame-val->path$inline
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame)))))
          (nthcdr
           (len
            (frame-val->path$inline
             (cdr (assoc-equal (frame-val->src$inline
                                (cdr (assoc-equal x (frame->frame frame))))
                               (frame->frame frame)))))
           (frame-val->path$inline
            (cdr (assoc-equal x (frame->frame frame)))))))
        (nthcdr
         (len
          (frame-val->path$inline
           (cdr
            (assoc-equal
             (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame)))))
         (frame-val->path$inline
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
        (nthcdr
         (len
          (frame-val->path$inline
           (cdr
            (assoc-equal
             (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame)))))
         (frame-val->path$inline
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))))
       (and
        (not
         (equal
          (nthcdr
           (len
            (frame-val->path$inline
             (cdr (assoc-equal (frame-val->src$inline
                                (cdr (assoc-equal x (frame->frame frame))))
                               (frame->frame frame)))))
           (frame-val->path$inline
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame)))))
          (nthcdr
           (len
            (frame-val->path$inline
             (cdr (assoc-equal (frame-val->src$inline
                                (cdr (assoc-equal x (frame->frame frame))))
                               (frame->frame frame)))))
           (frame-val->path$inline
            (cdr (assoc-equal x (frame->frame frame)))))))
        (not
         (prefixp
          (frame-val->path$inline
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
          (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame))))))
        (not
         (prefixp
          (nthcdr
           (len
            (frame-val->path$inline
             (cdr (assoc-equal (frame-val->src$inline
                                (cdr (assoc-equal x (frame->frame frame))))
                               (frame->frame frame)))))
           (frame-val->path$inline
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame)))))
          (nthcdr
           (len
            (frame-val->path$inline
             (cdr (assoc-equal (frame-val->src$inline
                                (cdr (assoc-equal x (frame->frame frame))))
                               (frame->frame frame)))))
           (frame-val->path$inline
            (cdr (assoc-equal x (frame->frame frame)))))))
        (nthcdr
         (len
          (frame-val->path$inline
           (cdr
            (assoc-equal
             (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame)))))
         (frame-val->path$inline
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
        (not
         (nthcdr
          (len
           (frame-val->path$inline
            (cdr
             (assoc-equal
              (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (frame-val->path$inline
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))))))
       (and
        (not
         (equal
          (nthcdr
           (len
            (frame-val->path$inline
             (cdr (assoc-equal (frame-val->src$inline
                                (cdr (assoc-equal x (frame->frame frame))))
                               (frame->frame frame)))))
           (frame-val->path$inline
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame)))))
          (nthcdr
           (len
            (frame-val->path$inline
             (cdr (assoc-equal (frame-val->src$inline
                                (cdr (assoc-equal x (frame->frame frame))))
                               (frame->frame frame)))))
           (frame-val->path$inline
            (cdr (assoc-equal x (frame->frame frame)))))))
        (not
         (prefixp
          (frame-val->path$inline
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
          (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame))))))
        (prefixp
         (nthcdr
          (len
           (frame-val->path$inline
            (cdr
             (assoc-equal
              (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (frame-val->path$inline
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))))
         (nthcdr
          (len
           (frame-val->path$inline
            (cdr
             (assoc-equal
              (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
          (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame)))))))
       (and
        (not
         (equal
          (nthcdr
           (len
            (frame-val->path$inline
             (cdr (assoc-equal (frame-val->src$inline
                                (cdr (assoc-equal x (frame->frame frame))))
                               (frame->frame frame)))))
           (frame-val->path$inline
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame)))))
          (nthcdr
           (len
            (frame-val->path$inline
             (cdr (assoc-equal (frame-val->src$inline
                                (cdr (assoc-equal x (frame->frame frame))))
                               (frame->frame frame)))))
           (frame-val->path$inline
            (cdr (assoc-equal x (frame->frame frame)))))))
        (prefixp
         (frame-val->path$inline
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))
         (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame))))))
       (equal
        (nthcdr
         (len
          (frame-val->path$inline
           (cdr
            (assoc-equal
             (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame)))))
         (frame-val->path$inline
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
        (nthcdr
         (len
          (frame-val->path$inline
           (cdr
            (assoc-equal
             (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame)))))
         (frame-val->path$inline
          (cdr (assoc-equal x (frame->frame frame)))))))))))

;; There's a fundamental hurdle with the induction scheme we are trying to
;; use. Let me explain. Think of an x which has its source elsewhere in the
;; frame, and gets context-applied without changing the root. Now, the new
;; frame might have the source of x as its 1st complete variable. This the the
;; only problematic scenario, because otherwise the 1st complete variable will
;; be the same as (1st-complete frame) (of course, assuming x itself is
;; different from (1st-complete frame)) and rearrangement of
;; put-assoc and remove-assoc terms will give us what we need. But this
;; rearrangement is not possible in the problematic scenario, because now the
;; 1st complete element is necessarily different from (1st-complete frame).
;;
;; Now, what we need to prove for induction (to be specific, induction on
;; (collapse frame)) is that first context-applying (1st-complete frame) and
;; then context-applying x gives us the same results, and it might seem at
;; first glance that there is no problem because the 1st complete variable
;; afterwards will be the source of x. Unfortunately, there is one further
;; scenario where this does not hold true - when the new 1st complete variable
;; after context-applying x and (1st-complete frame) is the source of
;; (1st-complete frame), it being assumed that this is different from the
;; source of x. This kind of thing can occur arbitrarily many times, making the
;; path through the frame arbitrarily different from what one would
;; expect... so there has to be a new induction scheme.
;;
;; Seriously though, I'm not sure a new induction scheme is needed. The trouble
;; is with a certain (context-apply-ok) term that arises when we're trying to
;; prove that the variable at the source of x - to which x has already been
;; context-applied - can be context-applied to its source. The proof of that
;; can come from another term in which x has been context-applied, by means of
;; partial-collapse-correctness-lemma-64. The trouble is, we enter hell when we
;; try to directly use that lemma instance, because... I don't
;; know... something goes wrong with the substitution and a lot of subgoals
;; arise. But that can be worked around, by making a side lemma and then using
;; brr. This weird infinite regression... can't so easily be worked
;; around. That's the scene. I keep second-guessing myself on this, but I can't
;; figure out what induction scheme allows us to work out the case where the
;; paths are different when x is folded up first, and afterwards...

;; Although, perhaps the previously proved theorem, the one about x and
;; (1st-complete frame) being interchangeable if x is going into the root, will
;; suffice... if we extend it
;; to a two-way theorem showing that (mv-nth 1 (collapse frame)) and (mv-nth 0
;; (collapse frame)) are both equivalent. If that is proved, we can just switch
;; the source of x and (1st-complete frame).
;; (thm
;;  (implies
;;   (and
;;    (abs-separate (frame->frame frame))
;;    (dist-names (frame->root frame) 'nil (frame->frame frame))
;;    (consp (frame->frame frame))
;;    (integerp x)
;;    (< 0 x)
;;    (< 0
;;       (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
;;    (not
;;     (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
;;            x))
;;    (consp
;;     (assoc-equal
;;      (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
;;      (frame->frame frame)))
;;    (prefixp
;;     (frame-val->path
;;      (cdr
;;       (assoc-equal
;;        (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
;;        (frame->frame frame))))
;;     (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
;;    (context-apply-ok
;;     (frame-val->dir
;;      (cdr
;;       (assoc-equal
;;        (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
;;        (frame->frame frame))))
;;     (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
;;     x
;;     (nthcdr
;;      (len
;;       (frame-val->path
;;        (cdr
;;         (assoc-equal
;;          (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
;;          (frame->frame frame)))))
;;      (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
;;    (mv-nth 1 (collapse frame))
;;    (abs-complete
;;     (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
;;    (frame-p (frame->frame frame))
;;    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
;;    (not (consp (assoc-equal 0 (frame->frame frame)))))
;;   (mv-nth
;;    1
;;    (collapse
;;     (frame-with-root
;;      (frame->root frame)
;;      (put-assoc-equal
;;       (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
;;       (frame-val
;;        (frame-val->path
;;         (cdr
;;          (assoc-equal
;;           (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
;;           (frame->frame frame))))
;;        (context-apply
;;         (frame-val->dir
;;          (cdr
;;           (assoc-equal
;;            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
;;            (frame->frame frame))))
;;         (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
;;         x
;;         (nthcdr
;;          (len
;;           (frame-val->path
;;            (cdr
;;             (assoc-equal
;;              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
;;              (frame->frame frame)))))
;;          (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
;;        (frame-val->src
;;         (cdr
;;          (assoc-equal
;;           (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
;;           (frame->frame frame)))))
;;       (remove-assoc-equal x (frame->frame frame)))))))
;;  :hints (("goal" :in-theory (e/d (collapse abs-separate 1st-complete-src)
;;                                  ((:definition assoc-equal)
;;                                   (:definition remove-assoc-equal)
;;                                   (:rewrite put-assoc-equal-without-change . 2)
;;                                   (:rewrite nthcdr-when->=-n-len-l)
;;                                   (:rewrite
;;                                    abs-file-alist-p-when-m1-file-alist-p)
;;                                   m1-file-alist-p-of-cdr-when-m1-file-alist-p
;;                                   (:definition member-equal)
;;                                   (:definition remove-equal)
;;                                   (:rewrite remove-when-absent)
;;                                   (:definition nthcdr)
;;                                   (:definition len)
;;                                   (:rewrite remove-assoc-when-absent)))
;;           :induct (collapse frame))
;;          ("subgoal *1/6"
;;           :cases ((not (equal x
;;                               (1st-complete (frame->frame frame))))))
;;          ("subgoal *1/6.1'"
;;           :cases
;;           ((equal
;;             (1st-complete
;;              (put-assoc-equal
;;               (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
;;               (frame-val
;;                (frame-val->path$inline
;;                 (cdr (assoc-equal (frame-val->src$inline
;;                                    (cdr (assoc-equal x (frame->frame frame))))
;;                                   (frame->frame frame))))
;;                (context-apply
;;                 (frame-val->dir$inline
;;                  (cdr
;;                   (assoc-equal (frame-val->src$inline
;;                                 (cdr (assoc-equal x (frame->frame frame))))
;;                                (frame->frame frame))))
;;                 (frame-val->dir$inline (cdr (assoc-equal x (frame->frame frame))))
;;                 x
;;                 (nthcdr
;;                  (len
;;                   (frame-val->path$inline
;;                    (cdr
;;                     (assoc-equal (frame-val->src$inline
;;                                   (cdr (assoc-equal x (frame->frame frame))))
;;                                  (frame->frame frame)))))
;;                  (frame-val->path$inline
;;                   (cdr (assoc-equal x (frame->frame frame))))))
;;                (frame-val->src$inline
;;                 (cdr (assoc-equal (frame-val->src$inline
;;                                    (cdr (assoc-equal x (frame->frame frame))))
;;                                   (frame->frame frame)))))
;;               (remove-assoc-equal x (frame->frame frame))))
;;             (frame-val->src$inline (cdr (assoc-equal x (frame->frame
;;                                                         frame)))))))
;;          ("subgoal *1/6.1.2.1''"
;;           :expand
;;           (collapse
;;            (frame-with-root
;;             (frame->root frame)
;;             (put-assoc-equal
;;              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
;;              (frame-val
;;               (frame-val->path
;;                (cdr (assoc-equal
;;                      (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
;;                      (frame->frame frame))))
;;               (context-apply
;;                (frame-val->dir
;;                 (cdr (assoc-equal
;;                       (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
;;                       (frame->frame frame))))
;;                (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
;;                x
;;                (nthcdr
;;                 (len
;;                  (frame-val->path
;;                   (cdr
;;                    (assoc-equal
;;                     (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
;;                     (frame->frame frame)))))
;;                 (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
;;               (frame-val->src
;;                (cdr (assoc-equal
;;                      (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
;;                      (frame->frame frame)))))
;;              (remove-assoc-equal x (frame->frame frame))))))
;;          ("subgoal *1/3.1'")))

(defthm
  partial-collapse-correctness-lemma-92
  (implies
   (and (equal (1st-complete-under-pathname-src (frame->frame frame)
                                                pathname)
               0)
        (< 0
           (1st-complete-under-pathname (frame->frame frame)
                                        pathname))
        (frame-p (frame->frame frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (dist-names (frame->root frame)
                    nil (frame->frame frame))
        (abs-separate (frame->frame frame))
        (mv-nth 1 (collapse frame)))
   (mv-nth
    1
    (collapse
     (frame-with-root
      (context-apply
       (frame->root frame)
       (frame-val->dir
        (cdr (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                       pathname)
                          (frame->frame frame))))
       (1st-complete-under-pathname (frame->frame frame)
                                    pathname)
       (frame-val->path
        (cdr (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                       pathname)
                          (frame->frame frame)))))
      (remove-assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                       pathname)
                          (frame->frame frame))))))
  :hints (("goal" :in-theory (enable 1st-complete-under-pathname-src))))

(defthm
  partial-collapse-correctness-lemma-93
  (implies
   (and (equal (1st-complete-under-pathname-src (frame->frame frame)
                                                pathname)
               0)
        (< 0
           (1st-complete-under-pathname (frame->frame frame)
                                        pathname))
        (frame-p (frame->frame frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (dist-names (frame->root frame)
                    nil (frame->frame frame))
        (abs-separate (frame->frame frame))
        (mv-nth 1 (collapse frame)))
   (mv-nth
    1
    (collapse
     (frame-with-root
      (context-apply
       (frame->root frame)
       (frame-val->dir
        (cdr (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                       pathname)
                          (frame->frame frame))))
       (1st-complete-under-pathname (frame->frame frame)
                                    pathname)
       (frame-val->path
        (cdr (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                       pathname)
                          (frame->frame frame)))))
      (remove-assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                       pathname)
                          (frame->frame frame))))))
  :hints (("goal" :in-theory (enable 1st-complete-under-pathname-src))))

(skip-proofs
 (defthm
   partial-collapse-correctness-lemma-95
   (implies
    (and
     (consp (frame->frame frame))
     (< 0
        (1st-complete-under-pathname (frame->frame frame)
                                     pathname))
     (< 0
        (1st-complete-under-pathname-src (frame->frame frame)
                                         pathname))
     (not (equal (1st-complete-under-pathname-src (frame->frame frame)
                                                  pathname)
                 (1st-complete-under-pathname (frame->frame frame)
                                              pathname)))
     (consp (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                          pathname)
                         (frame->frame frame)))
     (prefixp
      (frame-val->path
       (cdr (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                          pathname)
                         (frame->frame frame))))
      (frame-val->path
       (cdr (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                      pathname)
                         (frame->frame frame)))))
     (context-apply-ok
      (frame-val->dir
       (cdr (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                          pathname)
                         (frame->frame frame))))
      (frame-val->dir
       (cdr (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                      pathname)
                         (frame->frame frame))))
      (1st-complete-under-pathname (frame->frame frame)
                                   pathname)
      (nthcdr
       (len
        (frame-val->path
         (cdr (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                            pathname)
                           (frame->frame frame)))))
       (frame-val->path
        (cdr (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                       pathname)
                          (frame->frame frame))))))
     (not
      (mv-nth
       1
       (collapse
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (1st-complete-under-pathname-src (frame->frame frame)
                                           pathname)
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                           pathname)
                          (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                            pathname)
                           (frame->frame frame))))
            (frame-val->dir
             (cdr (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                            pathname)
                               (frame->frame frame))))
            (1st-complete-under-pathname (frame->frame frame)
                                         pathname)
            (nthcdr
             (len
              (frame-val->path
               (cdr (assoc-equal
                     (1st-complete-under-pathname-src (frame->frame frame)
                                                      pathname)
                     (frame->frame frame)))))
             (frame-val->path
              (cdr
               (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                         pathname)
                            (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                           pathname)
                          (frame->frame frame)))))
          (remove-assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                           pathname)
                              (frame->frame frame)))))))
     (frame-p (frame->frame frame))
     (no-duplicatesp-equal (strip-cars (frame->frame frame)))
     (subsetp-equal (abs-addrs (frame->root frame))
                    (frame-addrs-root (frame->frame frame)))
     (no-duplicatesp-equal (abs-addrs (frame->root frame)))
     (dist-names (frame->root frame)
                 nil (frame->frame frame))
     (abs-separate (frame->frame frame))
     (mv-nth 1 (collapse frame)))
    (absfat-equiv
     (mv-nth
      0
      (collapse
       (partial-collapse
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (1st-complete-under-pathname-src (frame->frame frame)
                                           pathname)
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                           pathname)
                          (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                            pathname)
                           (frame->frame frame))))
            (frame-val->dir
             (cdr (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                            pathname)
                               (frame->frame frame))))
            (1st-complete-under-pathname (frame->frame frame)
                                         pathname)
            (nthcdr
             (len
              (frame-val->path
               (cdr (assoc-equal
                     (1st-complete-under-pathname-src (frame->frame frame)
                                                      pathname)
                     (frame->frame frame)))))
             (frame-val->path
              (cdr
               (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                         pathname)
                            (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                           pathname)
                          (frame->frame frame)))))
          (remove-assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                           pathname)
                              (frame->frame frame))))
        pathname)))
     (mv-nth 0 (collapse frame))))))

(skip-proofs
 (defthm
   partial-collapse-correctness-lemma-96
   (implies
    (and
     (consp (frame->frame frame))
     (< 0
        (1st-complete-under-pathname (frame->frame frame)
                                     pathname))
     (< 0
        (1st-complete-under-pathname-src (frame->frame frame)
                                         pathname))
     (not (equal (1st-complete-under-pathname-src (frame->frame frame)
                                                  pathname)
                 (1st-complete-under-pathname (frame->frame frame)
                                              pathname)))
     (consp (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                          pathname)
                         (frame->frame frame)))
     (prefixp
      (frame-val->path
       (cdr (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                          pathname)
                         (frame->frame frame))))
      (frame-val->path
       (cdr (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                      pathname)
                         (frame->frame frame)))))
     (context-apply-ok
      (frame-val->dir
       (cdr (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                          pathname)
                         (frame->frame frame))))
      (frame-val->dir
       (cdr (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                      pathname)
                         (frame->frame frame))))
      (1st-complete-under-pathname (frame->frame frame)
                                   pathname)
      (nthcdr
       (len
        (frame-val->path
         (cdr (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                            pathname)
                           (frame->frame frame)))))
       (frame-val->path
        (cdr (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                       pathname)
                          (frame->frame frame))))))
     (absfat-equiv
      (mv-nth
       0
       (collapse
        (partial-collapse
         (frame-with-root
          (frame->root frame)
          (put-assoc-equal
           (1st-complete-under-pathname-src (frame->frame frame)
                                            pathname)
           (frame-val
            (frame-val->path
             (cdr
              (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                            pathname)
                           (frame->frame frame))))
            (context-apply
             (frame-val->dir
              (cdr (assoc-equal
                    (1st-complete-under-pathname-src (frame->frame frame)
                                                     pathname)
                    (frame->frame frame))))
             (frame-val->dir
              (cdr
               (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                         pathname)
                            (frame->frame frame))))
             (1st-complete-under-pathname (frame->frame frame)
                                          pathname)
             (nthcdr
              (len
               (frame-val->path
                (cdr (assoc-equal
                      (1st-complete-under-pathname-src (frame->frame frame)
                                                       pathname)
                      (frame->frame frame)))))
              (frame-val->path
               (cdr
                (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                          pathname)
                             (frame->frame frame))))))
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                            pathname)
                           (frame->frame frame)))))
           (remove-assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                            pathname)
                               (frame->frame frame))))
         pathname)))
      (mv-nth
       0
       (collapse
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (1st-complete-under-pathname-src (frame->frame frame)
                                           pathname)
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                           pathname)
                          (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                            pathname)
                           (frame->frame frame))))
            (frame-val->dir
             (cdr (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                            pathname)
                               (frame->frame frame))))
            (1st-complete-under-pathname (frame->frame frame)
                                         pathname)
            (nthcdr
             (len
              (frame-val->path
               (cdr (assoc-equal
                     (1st-complete-under-pathname-src (frame->frame frame)
                                                      pathname)
                     (frame->frame frame)))))
             (frame-val->path
              (cdr
               (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                         pathname)
                            (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                           pathname)
                          (frame->frame frame)))))
          (remove-assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                           pathname)
                              (frame->frame frame)))))))
     (frame-p (frame->frame frame))
     (no-duplicatesp-equal (strip-cars (frame->frame frame)))
     (subsetp-equal (abs-addrs (frame->root frame))
                    (frame-addrs-root (frame->frame frame)))
     (no-duplicatesp-equal (abs-addrs (frame->root frame)))
     (dist-names (frame->root frame)
                 nil (frame->frame frame))
     (abs-separate (frame->frame frame))
     (mv-nth 1 (collapse frame)))
    (absfat-equiv
     (mv-nth
      0
      (collapse
       (frame-with-root
        (frame->root frame)
        (put-assoc-equal
         (1st-complete-under-pathname-src (frame->frame frame)
                                          pathname)
         (frame-val
          (frame-val->path
           (cdr
            (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                          pathname)
                         (frame->frame frame))))
          (context-apply
           (frame-val->dir
            (cdr
             (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                           pathname)
                          (frame->frame frame))))
           (frame-val->dir
            (cdr (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                           pathname)
                              (frame->frame frame))))
           (1st-complete-under-pathname (frame->frame frame)
                                        pathname)
           (nthcdr
            (len
             (frame-val->path
              (cdr (assoc-equal
                    (1st-complete-under-pathname-src (frame->frame frame)
                                                     pathname)
                    (frame->frame frame)))))
            (frame-val->path
             (cdr (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                            pathname)
                               (frame->frame frame))))))
          (frame-val->src
           (cdr
            (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                          pathname)
                         (frame->frame frame)))))
         (remove-assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                          pathname)
                             (frame->frame frame))))))
     (mv-nth 0 (collapse frame))))))

(defthm
  partial-collapse-correctness-lemma-97
  (implies
   (and (equal (1st-complete-under-pathname-src (frame->frame frame)
                                                pathname)
               0)
        (< 0
           (1st-complete-under-pathname (frame->frame frame)
                                        pathname))
        (frame-p (frame->frame frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (dist-names (frame->root frame)
                    nil (frame->frame frame))
        (abs-separate (frame->frame frame))
        (mv-nth 1 (collapse frame)))
   (absfat-equiv
    (mv-nth
     0
     (collapse
      (frame-with-root
       (context-apply
        (frame->root frame)
        (frame-val->dir
         (cdr (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                        pathname)
                           (frame->frame frame))))
        (1st-complete-under-pathname (frame->frame frame)
                                     pathname)
        (frame-val->path
         (cdr (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                        pathname)
                           (frame->frame frame)))))
       (remove-assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                        pathname)
                           (frame->frame frame)))))
    (mv-nth 0 (collapse frame))))
  :hints (("goal" :in-theory (enable 1st-complete-under-pathname-src))))

(skip-proofs
 (defthm
   partial-collapse-correctness-lemma-98
   (implies
    (and
     (consp (frame->frame frame))
     (< 0
        (1st-complete-under-pathname (frame->frame frame)
                                     pathname))
     (< 0
        (1st-complete-under-pathname-src (frame->frame frame)
                                         pathname))
     (not (equal (1st-complete-under-pathname-src (frame->frame frame)
                                                  pathname)
                 (1st-complete-under-pathname (frame->frame frame)
                                              pathname)))
     (consp (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                          pathname)
                         (frame->frame frame)))
     (prefixp
      (frame-val->path
       (cdr (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                          pathname)
                         (frame->frame frame))))
      (frame-val->path
       (cdr (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                      pathname)
                         (frame->frame frame)))))
     (context-apply-ok
      (frame-val->dir
       (cdr (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                          pathname)
                         (frame->frame frame))))
      (frame-val->dir
       (cdr (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                      pathname)
                         (frame->frame frame))))
      (1st-complete-under-pathname (frame->frame frame)
                                   pathname)
      (nthcdr
       (len
        (frame-val->path
         (cdr (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                            pathname)
                           (frame->frame frame)))))
       (frame-val->path
        (cdr (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                       pathname)
                          (frame->frame frame))))))
     (member-equal (1st-complete-under-pathname (frame->frame frame)
                                                pathname)
                   (abs-addrs (frame->root frame)))
     (frame-p (frame->frame frame))
     (no-duplicatesp-equal (strip-cars (frame->frame frame)))
     (subsetp-equal (abs-addrs (frame->root frame))
                    (frame-addrs-root (frame->frame frame)))
     (no-duplicatesp-equal (abs-addrs (frame->root frame)))
     (dist-names (frame->root frame)
                 nil (frame->frame frame))
     (abs-separate (frame->frame frame))
     (mv-nth 1 (collapse frame)))
    (absfat-equiv
     (mv-nth
      0
      (collapse
       (partial-collapse
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (1st-complete-under-pathname-src (frame->frame frame)
                                           pathname)
          (frame-val
           (frame-val->path
            (cdr
             (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                           pathname)
                          (frame->frame frame))))
           (context-apply
            (frame-val->dir
             (cdr
              (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                            pathname)
                           (frame->frame frame))))
            (frame-val->dir
             (cdr (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                            pathname)
                               (frame->frame frame))))
            (1st-complete-under-pathname (frame->frame frame)
                                         pathname)
            (nthcdr
             (len
              (frame-val->path
               (cdr (assoc-equal
                     (1st-complete-under-pathname-src (frame->frame frame)
                                                      pathname)
                     (frame->frame frame)))))
             (frame-val->path
              (cdr
               (assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                         pathname)
                            (frame->frame frame))))))
           (frame-val->src
            (cdr
             (assoc-equal (1st-complete-under-pathname-src (frame->frame frame)
                                                           pathname)
                          (frame->frame frame)))))
          (remove-assoc-equal (1st-complete-under-pathname (frame->frame frame)
                                                           pathname)
                              (frame->frame frame))))
        pathname)))
     (mv-nth 0 (collapse frame))))))

(defthm partial-collapse-correctness-1
  (implies
   (and
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (subsetp (abs-addrs (frame->root frame))
             (frame-addrs-root (frame->frame frame)))
    (abs-separate (frame-with-root (frame->root frame)
                                   (frame->frame frame)))
    ;; The above 4 hypotheses seem reasonable since they're shared with
    ;; abs-separate-correctness-1.
    (mv-nth 1 (collapse frame)))
   (absfat-equiv
    (b*
        ((frame (partial-collapse frame pathname))
         ((mv root &) (collapse frame)))
      root)
    (mv-nth 0 (collapse frame))))
  :hints (("Goal" :in-theory (enable partial-collapse)
           :induct (PARTIAL-COLLAPSE FRAME PATHNAME)) ))
