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
                     (:rewrite take-when-atom)
                     (:rewrite take-of-take-split)
                     ;; Disabling this because it's defined in terms of helper
                     ;; functions and stuff.
                     position)))

(local
 (in-theory (disable nat-listp-if-fat32-masked-entry-list-p)))

(defthm abs-find-file-helper-of-collapse-lemma-3
  (implies (prefixp (fat32-filename-list-fix x) y)
           (prefixp (fat32-filename-list-fix x)
                    (fat32-filename-list-fix y)))
  :hints (("goal" :in-theory (e/d (fat32-filename-list-fix prefixp)
                                  ((:i fat32-filename-list-fix)))
           :induct (fat32-filename-list-prefixp x y)
           :expand ((fat32-filename-list-fix x)
                    (fat32-filename-list-fix y)))))

;; This rule is of more use on this project than it is in the larger set of
;; community books that include the STD prefixp book. It introduces a new
;; concept, namely prefixp, into proofs by backchaining - per a discussion on
;; Github (https://github.com/acl2/acl2/pull/1098) - so it might make some
;; proofs in other books take longer.
(defthm partial-collapse-correctness-lemma-2
  (implies (prefixp x y)
           (equal (< (len x) (len y))
                  (not (list-equiv x y))))
  :hints (("goal" :in-theory (enable prefixp))))

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

(defthmd
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

(defthmd
  abs-file-p-alt
  (equal (abs-file-p x)
         (or (m1-regular-file-p x)
             (abs-directory-file-p x)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable m1-regular-file-p
                              abs-file-p abs-directory-file-p
                              m1-file->contents m1-file-contents-fix
                              m1-file-p abs-file-contents-p
                              abs-file->contents))))

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

(defthm
  abs-addrs-when-m1-file-alist-p-lemma-2
  (implies (and (or (and (consp (car x))
                         (m1-file-alist-p (abs-file->contents (cdr (car x)))))
                    (not
                     (and (abs-file-alist-p (abs-file->contents (cdr (car x))))
                          (or (abs-directory-file-p (cdr (car x)))
                              (atom (abs-addrs (abs-file->contents (cdr (car x)))))))))
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
  abs-addrs-when-m1-file-alist-p-lemma-1
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

;; This doesn't work as a pure type-prescription rule...
(defthm abs-addrs-when-m1-file-alist-p
  (implies (m1-file-alist-p x)
           (equal (abs-addrs x) nil))
  :hints (("goal" :in-theory (enable abs-addrs
                                     abs-addrs-when-m1-file-alist-p-lemma-1)))
  :rule-classes (:type-prescription :rewrite))

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

(defthm abs-addrs-when-m1-file-contents-p
  (implies (m1-file-contents-p fs)
           (not (consp (abs-addrs fs))))
  :hints (("goal" :in-theory (enable abs-addrs m1-file-contents-p))))

;; top-complete is known to match up with alistp
(defun abs-complete (x)
  (declare
   (xargs :guard (abs-file-alist-p x)))
  (atom (abs-addrs x)))

(encapsulate
  ()

  (local
   (defthm
     lemma
     (implies (and (consp (car x))
                   (not (abs-directory-file-p (cdr (car x))))
                   (m1-file-alist-p (cdr x))
                   (abs-file-alist-p x))
              (m1-file-alist-p x))
     :hints (("goal" :in-theory (enable m1-file-alist-p
                                        abs-file-p m1-file-contents-p m1-file-p
                                        abs-directory-file-p abs-file->contents)
              :do-not-induct t
              :expand (abs-file-alist-p x)))))

  ;; This theorem states that an abstract filesystem tree without any body
  ;; addresses is just a HiFAT instance.
  (defthm
    abs-file-alist-p-correctness-1
    (implies (and (abs-file-alist-p x)
                  (abs-complete x))
             (m1-file-alist-p x))
    :hints (("goal" :in-theory (enable abs-file-alist-p abs-addrs
                                       abs-addrs-when-m1-file-alist-p-lemma-1)
             :induct (abs-addrs x)))))

(defthm abs-file-alist-p-of-put-assoc-equal
  (implies (abs-file-alist-p alist)
           (equal (abs-file-alist-p (put-assoc-equal name val alist))
                  (and (fat32-filename-p name)
                       (abs-file-p val))))
  :hints (("goal" :in-theory (enable abs-file-alist-p
                                     abs-file-p abs-file-contents-p))))

(defthm
  abs-file-alist-p-of-append
  (iff (abs-file-alist-p (append x y))
       (and (abs-file-alist-p (true-list-fix x))
            (abs-file-alist-p y)))
  :hints (("goal" :in-theory (enable abs-file-alist-p true-list-fix)
           :induct (mv (TRUE-LIST-FIX X) (APPEND X Y))
           :expand (abs-file-alist-p (cons (car x)
                                           (true-list-fix (cdr x)))))))

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
        ((atom (car abs-file-alist))
         (list* (mbe :exec (car abs-file-alist)
                     :logic (nfix (car abs-file-alist)))
                (abs-top-addrs (cdr abs-file-alist))))
        (t (abs-top-addrs (cdr abs-file-alist)))))

(defthm abs-top-addrs-of-append
  (equal (abs-top-addrs (append x y))
         (append (abs-top-addrs x)
                 (abs-top-addrs y)))
  :hints (("goal" :in-theory (enable abs-top-addrs))))

(defthmd abs-top-addrs-of-true-list-fix
  (equal (abs-top-addrs (true-list-fix x)) (abs-top-addrs x))
  :hints (("Goal" :in-theory (enable abs-top-addrs)) ))

(defcong list-equiv equal (abs-top-addrs x) 1
  :hints
  (("goal" :in-theory (enable list-equiv)
    :use (abs-top-addrs-of-true-list-fix
          (:instance abs-top-addrs-of-true-list-fix
                     (x x-equiv))))))

(defthm abs-top-addrs-of-remove
  (implies (abs-file-alist-p x)
           (equal (abs-top-addrs (remove-equal var x))
                  (remove-equal var (abs-top-addrs x))))
  :hints (("goal" :in-theory (enable abs-top-addrs abs-file-alist-p))))

(defthm abs-top-addrs-of-put-assoc
  (implies (fat32-filename-p name)
           (equal (abs-top-addrs (put-assoc-equal name val fs))
                  (abs-top-addrs fs)))
  :hints (("goal" :in-theory (enable abs-top-addrs))))

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

(defthmd abs-no-dups-p-of-remove
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
   (and (abs-file-alist-p (true-list-fix x))
	(abs-file-alist-p y))
   (equal (abs-no-dups-p (append x y))
	  (and (abs-no-dups-p (true-list-fix x))
	       (abs-no-dups-p y)
	       (not (intersectp-equal (remove-equal nil (strip-cars x))
				      (remove-equal nil (strip-cars y)))))))
  :hints (("goal" :in-theory (e/d (abs-no-dups-p
                                   intersectp-equal
                                   true-list-fix)
				  (intersectp-is-commutative))
	   :induct (append x y)
           :expand (abs-file-alist-p (cons (car x) (true-list-fix (cdr x)))))
	  ("subgoal *1/2" :cases ((null (car (car x))))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (m1-file-alist-p (true-list-fix x))
	  (m1-file-alist-p y))
     (equal (hifat-no-dups-p (append x y))
	    (and (hifat-no-dups-p (true-list-fix x))
	         (hifat-no-dups-p y)
	         (not (intersectp-equal (remove-equal nil (strip-cars x))
				        (remove-equal nil (strip-cars y))))))))))

(defthm abs-no-dups-p-of-remove-assoc
  (implies (abs-no-dups-p fs)
           (abs-no-dups-p (remove-assoc-equal x fs)))
  :hints (("goal" :in-theory (enable abs-no-dups-p))))

;; Potentially overlapping with abs-no-dups-p-when-m1-file-alist-p, which is
;; actually more general.
(defthm hifat-no-dups-p-when-abs-complete
  (implies (and (abs-no-dups-p dir)
                (abs-complete dir))
           (hifat-no-dups-p dir))
  :hints (("goal" :in-theory (enable abs-addrs
                                     abs-no-dups-p hifat-no-dups-p))))

(defthm abs-addrs-of-put-assoc-lemma-1
  (implies (and (abs-file-alist-p abs-file-alist)
                (abs-no-dups-p abs-file-alist))
           (not (consp (assoc-equal (car (car abs-file-alist))
                                    (cdr abs-file-alist)))))
  :hints (("goal" :expand (abs-no-dups-p abs-file-alist))))

(defthm abs-addrs-of-put-assoc-lemma-2
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
  abs-addrs-of-put-assoc-1
  (implies
   (and (abs-directory-file-p val)
        (abs-file-alist-p abs-file-alist)
        (abs-no-dups-p abs-file-alist)
        (fat32-filename-p name))
   (set-equiv (abs-addrs (put-assoc-equal name val abs-file-alist))
              (append (abs-addrs (abs-file->contents val))
                      (abs-addrs (remove-assoc-equal name abs-file-alist)))))
  :hints
  (("goal"
    :in-theory (e/d (abs-addrs)
                    ((:rewrite commutativity-2-of-append-under-set-equiv)))
    :induct (mv (remove-assoc-equal name abs-file-alist)
                (put-assoc-equal name val abs-file-alist)))
   ("subgoal *1/3"
    :use
    ((:instance (:rewrite commutativity-2-of-append-under-set-equiv)
                (z (abs-addrs (remove-assoc-equal name (cdr abs-file-alist))))
                (y (abs-addrs (abs-file->contents val)))
                (x (list (car abs-file-alist))))
     (:instance
      (:rewrite commutativity-2-of-append-under-set-equiv)
      (z (abs-addrs (remove-assoc-equal name (cdr abs-file-alist))))
      (y (abs-addrs (abs-file->contents val)))
      (x (abs-addrs (abs-file->contents (cdr (car abs-file-alist))))))
     (:instance (:rewrite commutativity-2-of-append-under-set-equiv)
                (z (abs-addrs (remove-assoc-equal name (cdr abs-file-alist))))
                (y (abs-addrs (abs-file->contents val)))
                (x '(0)))))))

(defthm
  abs-addrs-of-put-assoc-2
  (implies
   (and (m1-regular-file-p val)
        (abs-file-alist-p abs-file-alist)
        (abs-no-dups-p abs-file-alist)
        (fat32-filename-p name))
   (equal (abs-addrs (put-assoc-equal name val abs-file-alist))
          (abs-addrs (remove-assoc-equal name abs-file-alist))))
  :hints
  (("goal"
    :in-theory (e/d (abs-addrs)
                    ((:rewrite commutativity-2-of-append-under-set-equiv)))
    :induct (mv (remove-assoc-equal name abs-file-alist)
                (put-assoc-equal name val abs-file-alist)))))

(defthmd
  no-duplicatesp-of-abs-addrs-of-put-assoc-lemma-1
  (implies (and (abs-file-alist-p abs-file-alist)
                (consp abs-file-alist))
           (or (consp (car abs-file-alist))
               (natp (car abs-file-alist))))
  :hints (("goal" :do-not-induct t
           :expand (abs-file-alist-p abs-file-alist)))
  :rule-classes :type-prescription)

;; Revisit this; it takes three subinductions.
(defthm
  no-duplicatesp-of-abs-addrs-of-put-assoc-1
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
                                             no-duplicatesp-of-abs-addrs-of-put-assoc-lemma-1)))))

(defthm
  no-duplicatesp-of-abs-addrs-of-put-assoc-2
  (implies (and (m1-regular-file-p val)
                (abs-no-dups-p abs-file-alist)
                (abs-file-alist-p abs-file-alist)
                (fat32-filename-p name))
           (equal (no-duplicatesp-equal
                   (abs-addrs (put-assoc-equal name val abs-file-alist)))
                  (no-duplicatesp-equal
                   (abs-addrs (remove-assoc-equal name abs-file-alist)))))
  :hints
  (("goal"
    :in-theory
    (e/d (abs-addrs intersectp-equal
                    no-duplicatesp-of-abs-addrs-of-put-assoc-lemma-1)))))

(defthm
  no-duplicatesp-of-abs-addrs-of-remove-assoc-lemma-1
  (subsetp-equal (abs-addrs (remove-assoc-equal name abs-file-alist))
                 (abs-addrs abs-file-alist))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  no-duplicatesp-of-abs-addrs-of-remove-assoc-lemma-2
  (implies
   (not (intersectp-equal (abs-addrs abs-file-alist1)
                          (abs-addrs abs-file-alist2)))
   (not
    (intersectp-equal (abs-addrs abs-file-alist2)
                      (abs-addrs (remove-assoc-equal name abs-file-alist1))))))

(defthm no-duplicatesp-of-abs-addrs-of-remove-assoc-lemma-3
  (implies (and (abs-directory-file-p (cdr (car y)))
                (abs-no-dups-p y))
           (abs-no-dups-p (abs-file->contents (cdr (car y)))))
  :hints (("goal" :in-theory (enable abs-no-dups-p))))

(defthm
  no-duplicatesp-of-abs-addrs-of-remove-assoc-lemma-4
  (implies
   (not (member-equal x (abs-addrs abs-file-alist)))
   (not (member-equal x
                      (abs-addrs (remove-assoc-equal name abs-file-alist)))))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  no-duplicatesp-of-abs-addrs-of-remove-assoc
  (implies
   (and (abs-no-dups-p abs-file-alist)
        (abs-file-alist-p abs-file-alist)
        (fat32-filename-p name)
        (no-duplicatesp-equal
         (abs-addrs abs-file-alist)))
    (no-duplicatesp-equal
     (abs-addrs (remove-assoc-equal name abs-file-alist))))
  :hints (("goal" :in-theory (e/d (abs-addrs intersectp-equal
                                             no-duplicatesp-of-abs-addrs-of-put-assoc-lemma-1)))))
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

(defthm abs-fs-p-of-abs-file->contents-of-cdr-of-assoc
  (implies (and (abs-fs-p fs)
                (abs-directory-file-p (cdr (assoc-equal name fs))))
           (abs-fs-p (abs-file->contents (cdr (assoc-equal name fs)))))
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

(defthm member-of-abs-fs-fix-when-natp
  (implies (and (natp x) (abs-file-alist-p fs))
           (iff (member-equal x (abs-fs-fix fs))
                (member-equal x fs)))
  :hints (("goal" :in-theory (enable abs-fs-fix
                                     no-duplicatesp-of-abs-addrs-of-put-assoc-lemma-1))))

(defthm consp-of-assoc-of-abs-fs-fix
  (implies (abs-file-alist-p fs)
           (equal (consp (assoc-equal name (abs-fs-fix fs)))
                  (consp (assoc-equal name fs))))
  :hints (("goal" :in-theory (enable abs-fs-fix)
           :induct (mv (abs-fs-fix fs)
                       (assoc-equal name fs))
           :expand (abs-file-alist-p fs))))

(defthm
  abs-fs-fix-of-remove-equal
  (implies (and (natp x) (abs-file-alist-p fs))
           (equal (abs-fs-fix (remove-equal x fs))
                  (remove-equal x (abs-fs-fix fs))))
  :hints
  (("goal" :in-theory (enable abs-fs-fix abs-file-alist-p))))

(defthm
  abs-fs-fix-of-put-assoc-equal-lemma-1
  (implies (abs-directory-file-p (abs-file-fix x))
           (abs-file-alist-p (abs-file->contents$inline x)))
  :hints (("goal" :in-theory (enable abs-file-alist-p abs-directory-file-p
                                     abs-file->contents abs-file-fix))))

(defthm abs-fs-fix-of-put-assoc-equal-lemma-2
  (implies (and (abs-file-alist-p fs)
                (consp (car fs)))
           (abs-file-p (cdr (car fs))))
  :hints (("goal" :in-theory (enable abs-file-alist-p abs-file-p))))

(defthm abs-fs-fix-of-put-assoc-equal-lemma-3
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
  abs-fs-fix-of-put-assoc-equal
  (implies
   (and (abs-fs-p fs)
        (fat32-filename-p name))
   (equal
    (abs-fs-fix (put-assoc-equal name val fs))
    (if (abs-directory-file-p (abs-file-fix val))
        (put-assoc-equal name
                         (abs-file (abs-file->dir-ent val)
                                   (abs-fs-fix (abs-file->contents val)))
                         fs)
      (put-assoc-equal name (abs-file-fix val)
                       fs))))
  :hints
  (("goal" :in-theory (enable abs-fs-fix abs-fs-p abs-no-dups-p
                              no-duplicatesp-of-abs-addrs-of-put-assoc-lemma-1))))

(defthmd abs-fs-fix-of-true-list-fix
  (equal (abs-fs-fix (true-list-fix x)) (abs-fs-fix x))
  :hints (("Goal" :in-theory (enable abs-fs-fix)) ))

(defcong
  list-equiv equal (abs-fs-fix x)
  1
  :hints
  (("goal" :in-theory (enable list-equiv)
    :use (abs-fs-fix-of-true-list-fix
          (:instance abs-fs-fix-of-true-list-fix
                     (x x-equiv))))))

(defthm abs-top-addrs-of-abs-fs-fix
  (equal (abs-top-addrs (abs-fs-fix fs))
         (abs-top-addrs fs))
  :hints (("goal" :in-theory (enable abs-top-addrs abs-fs-fix))))

(defthm member-of-abs-top-addrs
  (implies (natp x)
           (iff (member-equal x (abs-top-addrs fs))
                (member-equal x (abs-fs-fix fs))))
  :hints (("goal" :in-theory (enable abs-top-addrs abs-fs-fix))))

;; I'm not sure what to do with abs-fs-equiv...
(fty::deffixtype abs-fs
                 :pred abs-fs-p
                 :fix abs-fs-fix
                 :equiv abs-fs-equiv
                 :define t
                 :forward t)

(defund
  addrs-at (fs relpath)
  (declare (xargs :guard (and (abs-fs-p fs)
                              (fat32-filename-list-p relpath))
                  :measure (len relpath)))
  (b*
      ((fs (mbe :logic (abs-fs-fix fs) :exec fs))
       ((when (atom relpath))
        (abs-top-addrs fs))
       (head (mbe :exec (car relpath)
                  :logic (fat32-filename-fix (car relpath))))
       ((unless
            (and (consp (abs-assoc head fs))
                 (abs-directory-file-p (cdr (abs-assoc head fs)))))
        nil))
    (addrs-at
     (abs-file->contents (cdr (abs-assoc head fs)))
     (cdr relpath))))

(defthm addrs-at-of-fat32-filename-list-fix
  (equal (addrs-at fs (fat32-filename-list-fix relpath))
         (addrs-at fs relpath))
  :hints (("goal" :in-theory (enable addrs-at))))

(defcong
  fat32-filename-list-equiv
  equal (addrs-at fs relpath)
  2
  :hints
  (("goal"
    :in-theory
    (e/d (fat32-filename-list-equiv)
         (addrs-at-of-fat32-filename-list-fix))
    :use
    (addrs-at-of-fat32-filename-list-fix
     (:instance addrs-at-of-fat32-filename-list-fix
                (relpath relpath-equiv))))))

(defthm addrs-at-of-abs-fs-fix
  (equal (addrs-at (abs-fs-fix fs)
                   relpath)
         (addrs-at fs relpath))
  :hints (("goal" :in-theory (enable addrs-at))))

(defthm
  addrs-at-of-append-lemma-1
  (implies (and (consp (assoc-equal (fat32-filename-fix (car relpath))
                                    root))
                (consp (assoc-equal (fat32-filename-fix (car relpath))
                                    abs-file-alist)))
           (intersectp-equal (remove-equal nil (strip-cars abs-file-alist))
                             (remove-equal nil (strip-cars root))))
  :hints
  (("goal"
    :use (:instance (:rewrite intersectp-member)
                    (a (fat32-filename-fix (car relpath)))
                    (y (remove-equal nil (strip-cars root)))
                    (x (remove-equal nil (strip-cars abs-file-alist)))))))

(defthm
  addrs-at-of-append
  (implies (abs-fs-p (append x y))
           (equal (addrs-at (append x y) relpath)
                  (cond ((atom relpath)
                         (append (addrs-at x relpath)
                                 (addrs-at y relpath)))
                        ((atom (addrs-at x relpath))
                         (addrs-at y relpath))
                        (t (addrs-at x relpath)))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (addrs-at abs-fs-p)
                    (abs-fs-fix-when-abs-fs-p))
    :expand ((:free (x) (addrs-at x relpath)))
    :use ((:instance abs-fs-fix-when-abs-fs-p
                     (x (true-list-fix x)))
          (:instance (:rewrite abs-fs-fix-when-abs-fs-p)
                     (x (append x y)))
          (:instance (:rewrite abs-fs-fix-when-abs-fs-p)
                     (x y))))))

(defthm
  addrs-at-of-remove
  (implies (and (natp var) (abs-fs-p x))
           (equal (addrs-at (remove-equal var x) relpath)
                  (if (consp relpath)
                      (addrs-at x relpath)
                    (remove-equal var (addrs-at x relpath)))))
  :hints
  (("goal" :do-not-induct t
    :expand ((:free (x) (addrs-at x relpath))))))

(defthm
  addrs-at-of-put-assoc
  (implies (and (fat32-filename-p name)
                (abs-fs-p fs))
           (equal (addrs-at (put-assoc name val fs)
                            relpath)
                  (cond ((atom relpath) (addrs-at fs relpath))
                        ((equal name (fat32-filename-fix (car relpath)))
                         (addrs-at (abs-file->contents val)
                                   (cdr relpath)))
                        (t (addrs-at fs relpath)))))
  :hints (("goal" :do-not-induct t
           :expand ((:free (fs) (addrs-at fs relpath))
                    (addrs-at (cdr (cadr val))
                              (cdr relpath)))
           :in-theory (enable addrs-at abs-directory-file-p
                              abs-file->contents abs-file-contents-p
                              abs-file-contents-fix
                              abs-file abs-file-p abs-fs-fix))))

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
;; ctx-app a nonexistent variable - not from any real filesystem
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
  ctx-app
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
          (ctx-app
           (abs-file->contents
            (cdr (abs-assoc head abs-file-alist1)))
           abs-file-alist2 x (cdr x-path)))
         abs-file-alist1)))
    ;; This is actually an error condition.
    abs-file-alist1))

(defthm
  abs-file-alist-p-of-ctx-app-lemma-1
  (implies
   (and (abs-directory-file-p (cdr (assoc-equal (car x-path)
                                                abs-file-alist1)))
        (abs-file-alist-p abs-file-alist1))
   (abs-file-alist-p
    (put-assoc-equal
     (car x-path)
     (abs-file (abs-file->dir-ent (cdr (assoc-equal (car x-path)
                                                    abs-file-alist1)))
               (ctx-app
                (abs-file->contents (cdr (assoc-equal (car x-path)
                                                      abs-file-alist1)))
                abs-file-alist2 x (cdr x-path)))
     abs-file-alist1)))
  :hints
  (("goal"
    :use (:instance abs-no-dups-p-of-append-lemma-1
                    (alist abs-file-alist1)
                    (x (car x-path))))))

(defthm abs-file-alist-p-of-ctx-app
  (abs-file-alist-p (ctx-app abs-file-alist1
                             abs-file-alist2 x x-path))
  :hints (("goal" :in-theory (enable ctx-app))))

(verify-guards ctx-app
  :guard-debug t
  :hints (("Goal" :in-theory (enable abs-file-alist-p)) ))

(defthm ctx-app-of-fat32-filename-list-fix
  (equal (ctx-app abs-file-alist1 abs-file-alist2
                  x (fat32-filename-list-fix x-path))
         (ctx-app abs-file-alist1
                  abs-file-alist2 x x-path))
  :hints (("goal" :in-theory (enable ctx-app))))

(defcong
  fat32-filename-list-equiv equal
  (ctx-app abs-file-alist1
           abs-file-alist2 x x-path)
  4
  :hints
  (("goal"
    :in-theory (e/d (fat32-filename-list-equiv)
                    (ctx-app-of-fat32-filename-list-fix))
    :use
    (ctx-app-of-fat32-filename-list-fix
     (:instance ctx-app-of-fat32-filename-list-fix
                (x-path x-path-equiv))))))

(defthmd ctx-app-of-nfix
  (equal (ctx-app abs-file-alist1 abs-file-alist2
                  (nfix x) x-path)
         (ctx-app abs-file-alist1
                  abs-file-alist2 x x-path))
  :hints (("goal" :in-theory (enable ctx-app))))

(defcong
  nat-equiv equal
  (ctx-app abs-file-alist1
           abs-file-alist2 x x-path)
  3
  :hints
  (("goal"
    :use ((:instance (:rewrite ctx-app-of-nfix)
                     (x x-equiv))
          (:rewrite ctx-app-of-nfix)))))

(defthm ctx-app-of-abs-fs-fix-1
  (equal (ctx-app (abs-fs-fix abs-file-alist1)
                  abs-file-alist2 x x-path)
         (ctx-app abs-file-alist1
                  abs-file-alist2 x x-path))
  :hints (("goal" :in-theory (enable ctx-app))))

(defthm ctx-app-of-abs-fs-fix-2
  (equal (ctx-app abs-file-alist1
                  (abs-fs-fix abs-file-alist2)
                  x x-path)
         (ctx-app abs-file-alist1
                  abs-file-alist2 x x-path))
  :hints (("goal" :in-theory (enable ctx-app))))

(defund ctx-app-ok
  (abs-file-alist1 x x-path)
  (declare (xargs :guard (and (abs-fs-p abs-file-alist1)
                              (natp x)
                              (fat32-filename-list-p x-path))))
  (iff
   (member-equal (nfix x) (addrs-at abs-file-alist1 x-path))
   t))

(defcong
  fat32-filename-list-equiv equal
  (ctx-app-ok abs-file-alist1 x x-path)
  3
  :hints
  (("goal"
    :in-theory (enable ctx-app-ok))))

(defthm ctx-app-ok-of-abs-fs-fix-1
  (equal (ctx-app-ok (abs-fs-fix abs-file-alist1) x x-path)
         (ctx-app-ok abs-file-alist1 x x-path))
  :hints (("goal" :in-theory (enable ctx-app-ok))))

(defthmd ctx-app-ok-of-nfix
  (equal (ctx-app-ok abs-file-alist1 (nfix x) x-path)
         (ctx-app-ok abs-file-alist1 x x-path))
  :hints (("goal" :in-theory (e/d (ctx-app-ok) (nfix)))))

(defcong
  nat-equiv equal
  (ctx-app-ok abs-file-alist1 x x-path)
  2
  :hints
  (("goal"
    :use ((:instance (:rewrite ctx-app-ok-of-nfix)
                     (x x-equiv))
          (:rewrite ctx-app-ok-of-nfix)))))

(defthm
  ctx-app-ok-when-abs-complete-lemma-1
  (subsetp-equal (abs-top-addrs fs) (abs-addrs fs))
  :hints (("goal" :in-theory (enable abs-addrs abs-top-addrs))))

(defthm
  ctx-app-ok-when-abs-complete-lemma-2
  (implies
   (abs-directory-file-p (cdr (assoc-equal name fs)))
   (subsetp-equal (abs-addrs (abs-file->contents (cdr (assoc-equal name fs))))
                  (abs-addrs fs)))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  ctx-app-ok-when-abs-complete-lemma-3
  (subsetp-equal (abs-top-addrs fs)
                 (abs-addrs (abs-fs-fix fs)))
  :hints (("goal" :in-theory (disable ctx-app-ok-when-abs-complete-lemma-1)
           :use (:instance ctx-app-ok-when-abs-complete-lemma-1
                           (fs (abs-fs-fix fs))))))

(defthm
  ctx-app-ok-when-abs-complete-lemma-4
  (subsetp-equal (addrs-at fs relpath)
                 (abs-addrs (abs-fs-fix fs)))
  :hints (("goal" :in-theory (enable abs-addrs addrs-at)))
  :rule-classes
  (:rewrite (:rewrite :corollary (implies (abs-fs-p fs)
                                          (subsetp-equal (addrs-at fs relpath)
                                                         (abs-addrs fs))))))

(defthm
  ctx-app-ok-when-abs-complete
  (implies (abs-complete (abs-fs-fix abs-file-alist1))
           (not (ctx-app-ok abs-file-alist1 x x-path)))
  :hints
  (("goal" :in-theory (e/d (ctx-app-ok) (nfix subsetp-member))
    :use ((:instance (:rewrite subsetp-member . 4)
                     (a (nfix x))
                     (x (addrs-at abs-file-alist1 x-path))
                     (y (abs-addrs (abs-fs-fix abs-file-alist1))))))))

(defthm
  ctx-app-ok-when-not-natp
  (implies (not (natp x))
           (iff (ctx-app-ok abs-file-alist1 x x-path)
                (ctx-app-ok abs-file-alist1 0 x-path)))
  :hints (("goal" :in-theory (disable nat-equiv-implies-equal-ctx-app-ok-2)
           :use ctx-app-ok-of-nfix)))

(defthm
  ctx-app-when-not-ctx-app-ok
  (implies (not (ctx-app-ok abs-file-alist1 x x-path))
           (equal (ctx-app abs-file-alist1
                           abs-file-alist2 x x-path)
                  (abs-fs-fix abs-file-alist1)))
  :hints (("goal" :in-theory (e/d (ctx-app-ok ctx-app addrs-at)
                                  (nfix member-of-abs-top-addrs))
           :induct (ctx-app abs-file-alist1
                            abs-file-alist2 x x-path))
          ("subgoal *1/1''" :use (:instance member-of-abs-top-addrs
                                            (fs (abs-fs-fix abs-file-alist1))
                                            (x (nfix x))))))

(defthm
  ctx-app-when-not-natp
  (implies (not (natp x))
           (equal (ctx-app abs-file-alist1
                           abs-file-alist2 x x-path)
                  (ctx-app abs-file-alist1
                           abs-file-alist2 0 x-path)))
  :hints (("goal" :in-theory (disable nat-equiv-implies-equal-ctx-app-3)
           :use (:instance nat-equiv-implies-equal-ctx-app-3
                           (x-equiv 0)))))

(defthm abs-addrs-of-ctx-app-1-lemma-1
  (subsetp-equal (abs-addrs (remove-equal x abs-file-alist))
                 (abs-addrs abs-file-alist))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  abs-addrs-of-ctx-app-1-lemma-3
  (implies (and (member-equal x abs-file-alist1)
                (integerp x)
                (<= 0 x)
                (no-duplicatesp-equal (abs-addrs abs-file-alist1)))
           (not (member-equal x
                              (abs-addrs (remove-equal x abs-file-alist1)))))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  abs-addrs-of-ctx-app-1-lemma-4
  (implies
   (and (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
        (no-duplicatesp-equal (abs-addrs abs-file-alist1)))
   (no-duplicatesp-equal
    (abs-addrs
     (abs-file->contents (cdr (assoc-equal name abs-file-alist1))))))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  abs-addrs-of-ctx-app-1-lemma-5
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
  abs-addrs-of-ctx-app-1-lemma-6
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

(defthm abs-addrs-of-ctx-app-1-lemma-2
  (implies (member-equal x (abs-top-addrs abs-file-alist1))
           (member-equal x (abs-addrs abs-file-alist1)))
  :hints (("goal" :in-theory (enable abs-addrs abs-top-addrs))))

;; Important - says clearly that the variable's name (or number, whatever) must
;; exist for context application to go right.
(defthmd
  abs-addrs-of-ctx-app-1-lemma-7
  (implies (not (member-equal (nfix x)
                              (abs-addrs (abs-fs-fix abs-file-alist1))))
           (not (ctx-app-ok abs-file-alist1 x x-path)))
  :hints (("goal" :in-theory (e/d (abs-addrs addrs-at ctx-app ctx-app-ok)
                                  (nfix)))))

(defthm
  abs-addrs-of-ctx-app-1-lemma-8
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
  abs-addrs-of-ctx-app-lemma-7
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
  abs-addrs-of-ctx-app-1-lemma-11
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

(defthm
  abs-addrs-of-ctx-app-1-lemma-13
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
  abs-addrs-of-ctx-app-lemma-13
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
    (not
     (member-equal
      x
      (abs-addrs
       (ctx-app (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))
                abs-file-alist2 x x-path))))
    (natp x)
    (no-duplicatesp-equal (abs-addrs abs-file-alist1))
    (not
     (equal
      (put-assoc-equal
       name
       (abs-file
        (abs-file->dir-ent (cdr (assoc-equal name abs-file-alist1)))
        (ctx-app (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))
                 abs-file-alist2 x x-path))
       abs-file-alist1)
      abs-file-alist1))
    (abs-fs-p abs-file-alist1))
   (not
    (member-equal
     x
     (abs-addrs
      (put-assoc-equal
       name
       (abs-file
        (abs-file->dir-ent (cdr (assoc-equal name abs-file-alist1)))
        (ctx-app (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))
                 abs-file-alist2 x x-path))
       abs-file-alist1)))))
  :hints
  (("goal"
    :in-theory (disable put-assoc-equal-without-change)
    :use
    ((:instance
      put-assoc-equal-without-change
      (alist abs-file-alist1)
      (val
       (abs-file
        (abs-file->dir-ent (cdr (assoc-equal name abs-file-alist1)))
        (ctx-app (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))
                 abs-file-alist2 x x-path))))
     (:instance
      (:rewrite abs-addrs-of-ctx-app-1-lemma-7)
      (abs-file-alist1
       (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))))
     (:rewrite abs-addrs-of-ctx-app-1-lemma-11))
    :do-not-induct t)))

;; This just might be made obsolete soon...
(defthm
  abs-addrs-of-ctx-app-2-lemma-1
  (implies (not (intersectp-equal (abs-addrs abs-file-alist1)
                                  y))
           (not (intersectp-equal (abs-addrs (remove-equal x abs-file-alist1))
                                  y)))
  :hints (("goal" :in-theory (e/d (abs-addrs intersectp-equal)
                                  (intersectp-is-commutative)))))

(defthm
  abs-addrs-of-ctx-app-2-lemma-3
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
  abs-addrs-of-ctx-app-lemma-8
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
    (not
     (intersectp-equal
      (abs-addrs
       (ctx-app
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
        (ctx-app
         (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))
         abs-file-alist2 x x-path))
       abs-file-alist1))
     y))))

(defthm
  abs-addrs-of-ctx-app-lemma-9
  (implies
   (and (abs-file-alist-p abs-file-alist2)
        (not (intersectp-equal (abs-addrs abs-file-alist1)
                               y))
        (not (intersectp-equal (abs-addrs (abs-fs-fix abs-file-alist2))
                               y))
        (abs-fs-p abs-file-alist1))
   (not (intersectp-equal (abs-addrs (ctx-app abs-file-alist1
                                              abs-file-alist2 x x-path))
                          y)))
  :hints (("goal" :in-theory (e/d ((:definition abs-addrs) ctx-app)
                                  (intersectp-is-commutative
                                   abs-addrs-of-put-assoc-1)))))

(defthm
  abs-addrs-of-ctx-app-lemma-10
  (implies
   (not (intersectp-equal
         (abs-addrs (abs-file->contents (cdr (car abs-file-alist1))))
         (abs-addrs (cdr abs-file-alist1))))
   (not
    (intersectp-equal
     (abs-addrs (remove-assoc-equal name (cdr abs-file-alist1)))
     (abs-addrs (abs-file->contents$inline (cdr (car abs-file-alist1))))))))

(defthm
  abs-addrs-of-ctx-app-2-lemma-9
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
  abs-addrs-of-ctx-app-lemma-12
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
  abs-addrs-of-ctx-app-2-lemma-14
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
  abs-addrs-of-ctx-app-lemma-11
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
      (ctx-app
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
       (ctx-app
        (abs-file->contents$inline (cdr (assoc-equal name abs-file-alist1)))
        abs-file-alist2 x (cdr x-path))))))))

(defthm
  abs-addrs-of-ctx-app-lemma-2
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
  abs-addrs-of-ctx-app-lemma-3
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
  abs-addrs-of-ctx-app-lemma-4
  (implies
   (and
    (member-equal
     (nfix x)
     (abs-addrs
      (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))))
    (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
    (equal
     (abs-addrs
      (ctx-app (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))
               abs-file-alist2 x (cdr x-path)))
     (remove-equal
      (nfix x)
      (abs-addrs
       (abs-file->contents (cdr (assoc-equal name abs-file-alist1))))))
    (no-duplicatesp-equal (abs-addrs abs-file-alist1)))
   (equal
    (abs-addrs
     (put-assoc-equal
      name
      (abs-file
       (abs-file->dir-ent (cdr (assoc-equal name abs-file-alist1)))
       (ctx-app (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))
                abs-file-alist2 x (cdr x-path)))
      abs-file-alist1))
    (remove-equal (nfix x)
                  (abs-addrs abs-file-alist1))))
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
       (ctx-app (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))
                abs-file-alist2 x (cdr x-path)))
      abs-file-alist1)))))

(defthm
  abs-addrs-of-ctx-app
  (implies
   (and (no-duplicatesp-equal (abs-addrs (abs-fs-fix abs-file-alist1)))
        (abs-complete (abs-fs-fix abs-file-alist2)))
   (equal (abs-addrs (ctx-app abs-file-alist1
                              abs-file-alist2 x x-path))
          (if (ctx-app-ok abs-file-alist1 x x-path)
              (remove-equal (nfix x)
                            (abs-addrs (abs-fs-fix abs-file-alist1)))
            (abs-addrs (abs-fs-fix abs-file-alist1)))))
  :hints (("goal" :in-theory (e/d (ctx-app ctx-app-ok addrs-at)
                                  (nfix)))))

(defthm
  abs-addrs-of-ctx-app-lemma-1
  (set-equiv
   (append (abs-addrs (abs-fs-fix abs-file-alist2))
           (cons (car abs-file-alist1)
                 (remove-equal x (abs-addrs (cdr abs-file-alist1)))))
   (cons (car abs-file-alist1)
         (append (abs-addrs (abs-fs-fix abs-file-alist2))
                 (remove-equal x (abs-addrs (cdr abs-file-alist1))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite commutativity-2-of-append-under-set-equiv))
    :use (:instance (:rewrite commutativity-2-of-append-under-set-equiv)
                    (z (remove-equal x (abs-addrs (cdr abs-file-alist1))))
                    (y (abs-addrs (abs-fs-fix abs-file-alist2)))
                    (x (list (car abs-file-alist1)))))))

(defthm
  abs-addrs-of-ctx-app-lemma-5
  (set-equiv
   (append (abs-addrs (abs-fs-fix abs-file-alist2))
           (cons 0
                 (remove-equal x (abs-addrs (cdr abs-file-alist1)))))
   (cons 0
         (append (abs-addrs (abs-fs-fix abs-file-alist2))
                 (remove-equal x (abs-addrs (cdr abs-file-alist1))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite commutativity-2-of-append-under-set-equiv))
    :use (:instance (:rewrite commutativity-2-of-append-under-set-equiv)
                    (z (remove-equal x (abs-addrs (cdr abs-file-alist1))))
                    (y (abs-addrs (abs-fs-fix abs-file-alist2)))
                    (x '(0))))))

(defthm
  abs-addrs-of-ctx-app-lemma-6
  (implies
   (and
    (member-equal
     (nfix x)
     (abs-addrs
      (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))))
    (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
    (set-equiv
     (abs-addrs
      (ctx-app (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))
               abs-file-alist2 x (cdr x-path)))
     (append
      (remove-equal
       (nfix x)
       (abs-addrs
        (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))))
      (abs-addrs (abs-fs-fix abs-file-alist2))))
    (no-duplicatesp-equal (abs-addrs abs-file-alist1)))
   (set-equiv
    (abs-addrs
     (put-assoc-equal
      name
      (abs-file
       (abs-file->dir-ent (cdr (assoc-equal name abs-file-alist1)))
       (ctx-app (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))
                abs-file-alist2 x (cdr x-path)))
      abs-file-alist1))
    (append (remove-equal (nfix x)
                          (abs-addrs abs-file-alist1))
            (abs-addrs (abs-fs-fix abs-file-alist2)))))
  :hints
  (("goal"
    :in-theory (e/d (abs-addrs)
                    ((:definition member-equal)
                     (:rewrite abs-fs-fix-of-put-assoc-equal-lemma-1)
                     (:rewrite abs-file-alist-p-when-m1-file-alist-p)
                     (:rewrite abs-addrs-when-m1-file-alist-p-lemma-2)
                     (:rewrite abs-fs-fix-of-put-assoc-equal-lemma-2)
                     (:type-prescription assoc-when-zp-len)
                     (:rewrite abs-addrs-of-ctx-app)))
    :induct
    (mv
     (abs-addrs abs-file-alist1)
     (put-assoc-equal
      name
      (abs-file
       (abs-file->dir-ent (cdr (assoc-equal name abs-file-alist1)))
       (ctx-app (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))
                abs-file-alist2 x (cdr x-path)))
      abs-file-alist1)))))

(defthm
  abs-addrs-of-ctx-app-2
  (implies
   (no-duplicatesp-equal (abs-addrs (abs-fs-fix abs-file-alist1)))
   (set-equiv
    (abs-addrs (ctx-app abs-file-alist1
                        abs-file-alist2 x x-path))
    (if (ctx-app-ok abs-file-alist1 x x-path)
        (append (remove-equal (nfix x)
                              (abs-addrs (abs-fs-fix abs-file-alist1)))
                (abs-addrs (abs-fs-fix abs-file-alist2)))
        (abs-addrs (abs-fs-fix abs-file-alist1)))))
  :hints
  (("goal" :in-theory
    (e/d (ctx-app ctx-app-ok addrs-at)
         (nfix (:rewrite abs-addrs-of-put-assoc-1))))))

(defthm
  ctx-app-ok-of-ctx-app-lemma-1
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
  ctx-app-ok-of-ctx-app-lemma-2
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
         (ctx-app
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
       (ctx-app
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
       (ctx-app
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
        (ctx-app
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
           (ctx-app
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
         (ctx-app
          (abs-file->contents
           (cdr (assoc-equal (fat32-filename-fix (car x3-path))
                             abs-file-alist1)))
          abs-file-alist3 x3 (cdr x3-path)))
        abs-file-alist1)))))))

(defthm
  ctx-app-ok-of-ctx-app-1
  (implies (and (case-split (not (equal (nfix x2) (nfix x3))))
                (abs-fs-p (ctx-app abs-file-alist1
                                   abs-file-alist3 x3 x3-path))
                (not (member-equal (nfix x2)
                                   (abs-addrs (abs-fs-fix abs-file-alist3)))))
           (iff (ctx-app-ok (ctx-app abs-file-alist1
                                     abs-file-alist3 x3 x3-path)
                            x2 x2-path)
                (ctx-app-ok abs-file-alist1 x2 x2-path)))
  :hints
  (("goal" :in-theory
    (e/d (ctx-app-ok ctx-app put-assoc-equal-match)
         (nfix (:definition no-duplicatesp-equal)
               (:rewrite abs-file-alist-p-correctness-1)
               (:rewrite abs-file-contents-p-when-m1-file-contents-p)))
    :induct (mv (ctx-app abs-file-alist1
                         abs-file-alist2 x2 x2-path)
                (fat32-filename-list-prefixp x2-path x3-path))
    :expand ((:free (abs-file-alist1 abs-file-alist2 x2)
                    (ctx-app abs-file-alist1
                             abs-file-alist2 x2 x2-path))
             (ctx-app abs-file-alist1
                      abs-file-alist3 x3 x3-path)
             (:free (abs-file-alist1 abs-file-alist3 x3)
                    (ctx-app abs-file-alist1
                             abs-file-alist3 x3 x3-path))
             (addrs-at abs-file-alist1 x2-path)))))

;; Both these names, below, merit some thought later...
(fty::defprod frame-val
              ((path fat32-filename-list-p)
               (dir abs-fs-p)
               (src natp)))

(fty::defalist frame
               :key-type nat
               :val-type frame-val
               :true-listp t)

(defthmd nat-listp-of-strip-cars-when-frame-p
  (implies (frame-p frame)
           (nat-listp (strip-cars frame))))

(defthm assoc-equal-when-frame-p
  (implies (and (frame-p frame) (not (natp x)))
           (atom (assoc-equal x frame)))
  :rule-classes :type-prescription)

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

;; This doesn't work as a pure type-prescription rule...
(defthm 1st-complete-correctness-1
  (implies (not (zp (1st-complete frame)))
           (consp (assoc-equal (1st-complete frame)
                               frame)))
  :hints (("goal" :in-theory (enable 1st-complete)))
  :rule-classes (:rewrite :type-prescription))

(defthm
  1st-complete-of-put-assoc-lemma-1
  (implies (and (frame-p frame)
                (not (member-equal (car (car frame))
                                   (strip-cars (cdr frame)))))
           (equal (remove-assoc-equal (car (car frame))
                                      (cdr frame))
                  (cdr frame)))
  :hints (("goal" :in-theory (disable (:rewrite remove-assoc-when-absent-1))
           :use (:instance (:rewrite remove-assoc-when-absent-1)
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

(defthmd
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

(defthmd 1st-complete-of-true-list-fix
  (equal (1st-complete (true-list-fix frame))
         (1st-complete frame))
  :hints (("goal" :in-theory (enable 1st-complete))))

(defcong
  list-equiv equal (1st-complete frame)
  1
  :hints (("goal" :use ((:instance 1st-complete-of-true-list-fix
                                   (frame frame-equiv))
                        1st-complete-of-true-list-fix))))

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

;; This is a "false" frame because the src value given to the root is 0, same
;; as its abstract variable. This is one of a few compromises in elegance
;; required for distinguishing the root, which is necessary to properly define
;; the collapse relation.
(defund frame-with-root (root frame)
  (declare (xargs :guard (and (abs-file-alist-p root)
                              (frame-p frame))))
  (list* (cons 0 (frame-val nil (abs-fs-fix root) 0))
         frame))

(defthm frame-with-root-of-true-list-fix
  (equal (frame-with-root root (true-list-fix frame))
         (true-list-fix (frame-with-root root frame)))
  :hints (("goal" :in-theory (enable frame-with-root))))

(defthm strip-cars-of-frame-with-root
  (equal (strip-cars (frame-with-root root frame))
         (cons 0 (strip-cars frame)))
  :hints (("goal" :in-theory (enable frame-with-root))))

(defthm true-listp-of-frame-with-root
  (equal (true-listp (frame-with-root root frame))
         (true-listp frame))
  :hints (("goal" :in-theory (enable frame-with-root true-listp))))

;; This is because of fixing.
(defthm frame-p-of-frame-with-root
  (equal (frame-p (frame-with-root root frame))
         (frame-p frame))
  :hints (("goal" :in-theory (enable frame-with-root))))

(defthm alistp-of-frame-with-root
  (implies (frame-p frame)
           (alistp (frame-with-root root frame)))
  :hints (("goal" :in-theory (disable alistp-when-frame-p)
           :use (:instance alistp-when-frame-p
                           (x (frame-with-root root frame))))))

(defund frame->root (frame)
  (declare (xargs :guard (and (frame-p frame) (consp (assoc-equal 0 frame)))))
  (frame-val->dir (cdr (assoc-equal 0 frame))))

(defund frame->frame (frame)
  (declare (xargs :guard (frame-p frame)))
  (remove-assoc-equal 0 frame))

(defthmd frame->root-of-true-list-fix
  (equal (frame->root (true-list-fix frame))
         (frame->root frame))
  :hints (("goal" :in-theory (enable frame->root))))

(defcong
  list-equiv equal (frame->root frame)
  1
  :hints (("goal" :use ((:instance frame->root-of-true-list-fix
                                   (frame frame-equiv))
                        frame->root-of-true-list-fix))))

(defthmd frame->frame-of-true-list-fix
  (equal (frame->frame (true-list-fix frame))
         (frame->frame frame))
  :hints (("goal" :in-theory (enable frame->frame))))

(defcong
  list-equiv equal (frame->frame frame)
  1
  :hints (("goal" :use ((:instance frame->frame-of-true-list-fix
                                   (frame frame-equiv))
                        frame->frame-of-true-list-fix))))

(defthm frame->root-of-frame-with-root
  (equal (frame->root (frame-with-root root frame))
         (abs-fs-fix root))
  :hints (("Goal" :in-theory (enable frame-with-root frame->root)) ))

(defthm frame->frame-of-frame-with-root
  (equal (frame->frame (frame-with-root root frame))
         (remove-assoc-equal 0 frame))
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

(defthm no-duplicatesp-of-strip-cars-of-frame->frame
  (implies
   (no-duplicatesp-equal (strip-cars frame))
   (no-duplicatesp-equal (strip-cars (frame->frame frame))))
  :hints (("goal" :in-theory (enable frame->frame))))

;; Move later.
(defthm consp-of-assoc-of-frame->frame
  (implies (not (consp (assoc-equal x frame)))
           (not (consp (assoc-equal x (frame->frame frame)))))
  :hints (("goal" :in-theory (enable frame->frame))))

(defund
  collapse-this (frame x)
  (declare
   (xargs
    :guard
    (and
     (frame-p frame)
     (natp x)
     (consp (assoc-equal 0 frame))
     (consp (assoc-equal x (frame->frame frame)))
     (not
      (equal (frame-val->src
              (cdr (assoc-equal x (frame->frame frame))))
             x))
     (or
      (zp (frame-val->src
           (cdr (assoc-equal x (frame->frame frame)))))
      (consp
       (assoc-equal
        (frame-val->src
         (cdr (assoc-equal x (frame->frame frame))))
        (frame->frame frame)))))))
  (if
      (zp
       (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
      (frame-with-root
       (ctx-app
        (frame->root frame)
        (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
        x
        (frame-val->path
         (cdr (assoc-equal x (frame->frame frame)))))
       (remove-assoc-equal x (frame->frame frame)))
    (frame-with-root
     (frame->root frame)
     (put-assoc-equal
      (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
      (frame-val
       (frame-val->path
        (cdr
         (assoc-equal
          (frame-val->src
           (cdr (assoc-equal x (frame->frame frame))))
          (frame->frame frame))))
       (abs-fs-fix
        (ctx-app
         (frame-val->dir
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr (assoc-equal x (frame->frame frame))))
            (remove-assoc-equal x (frame->frame frame)))))
         (frame-val->dir
          (cdr (assoc-equal x (frame->frame frame))))
         x
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src
               (cdr (assoc-equal x (frame->frame frame))))
              (remove-assoc-equal x (frame->frame frame))))))
          (frame-val->path
           (cdr (assoc-equal x (frame->frame frame)))))))
       (frame-val->src
        (cdr
         (assoc-equal
          (frame-val->src
           (cdr (assoc-equal x (frame->frame frame))))
          (frame->frame frame)))))
      (remove-assoc-equal x (frame->frame frame))))))

(defthm
  len-of-frame->frame-of-collapse-this
  (implies
   (and
    (consp (assoc-equal x (frame->frame frame)))
    (not (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                x))
    (or
     (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
     (consp
      (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                   (frame->frame frame)))))
   (< (len (frame->frame (collapse-this frame x)))
      (len (frame->frame frame))))
  :hints (("goal" :in-theory (enable collapse-this)))
  :rule-classes :linear)

(defthm frame-p-of-collapse-this
  (implies (frame-p frame)
           (frame-p (collapse-this frame x)))
  :hints (("goal" :in-theory (enable collapse-this))))

(defthm
  no-duplicatesp-of-strip-cars-of-frame->frame-of-collapse-this
  (implies
   (no-duplicatesp-equal (strip-cars (frame->frame frame)))
   (no-duplicatesp-equal (strip-cars (frame->frame (collapse-this frame x)))))
  :hints
  (("goal"
    :in-theory (e/d (collapse-this)
                    (strip-cars-of-put-assoc
                     (:rewrite member-of-abs-addrs-when-natp . 2))))))

(defthm frame-p-of-frame->frame-of-collapse-this
  (implies (frame-p (frame->frame frame))
           (frame-p (frame->frame (collapse-this frame x))))
  :hints (("goal" :in-theory (enable collapse-this))))

(defthmd collapse-this-of-true-list-fix
  (equal (collapse-this (true-list-fix frame) x)
         (collapse-this frame x))
  :hints (("goal" :in-theory (enable collapse-this))))

(defcong
  list-equiv equal (collapse-this frame x)
  1
  :hints
  (("goal" :use ((:instance collapse-this-of-true-list-fix
                            (frame frame-equiv))
                 collapse-this-of-true-list-fix))))

(defthm assoc-of-frame->frame-of-collapse-this-lemma-1
  (atom (assoc-equal 0 (frame->frame frame)))
  :hints (("goal" :in-theory (enable frame->frame)))
  :rule-classes :type-prescription)

(defthm
  assoc-of-frame->frame-of-collapse-this
  (equal
   (assoc-equal y
                (frame->frame (collapse-this frame x)))
   (cond
    ((and
      (not (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
      (equal y
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
     (cons
      y
      (frame-val
       (frame-val->path (cdr (assoc-equal y (frame->frame frame))))
       (ctx-app
        (frame-val->dir (cdr (and (not (equal y x))
                                  (assoc-equal y (frame->frame frame)))))
        (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
        x
        (nthcdr
         (len
          (frame-val->path (cdr (and (not (equal y x))
                                     (assoc-equal y (frame->frame frame))))))
         (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
       (frame-val->src (cdr (assoc-equal y (frame->frame frame)))))))
    ((and
      (not (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
      (not (equal y x)))
     (assoc-equal y (frame->frame frame)))
    ((and (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 0)
          (not (equal x y)))
     (assoc-equal y (frame->frame frame)))
    (t nil)))
  :hints (("goal" :in-theory (enable collapse-this))))

(defthm
  frame->root-of-collapse-this
  (equal
   (frame->root (collapse-this frame x))
   (cond
    ((equal (frame-val->src
             (cdr (assoc-equal x (frame->frame frame))))
            0)
     (abs-fs-fix
      (ctx-app
       (frame->root frame)
       (frame-val->dir
        (cdr (assoc-equal x (frame->frame frame))))
       x
       (frame-val->path
        (cdr (assoc-equal x (frame->frame frame)))))))
    (t (frame->root frame))))
  :hints (("goal" :in-theory (enable collapse-this))))

(defthm
  strip-cars-of-frame->frame-of-collapse-this
  (implies
   (and
    (not (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                x))
    (or
     (zp (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame)))))
     (consp
      (assoc-equal
       (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
       (frame->frame frame)))))
   (equal (strip-cars (frame->frame (collapse-this frame x)))
          (remove-equal x (strip-cars (frame->frame frame)))))
  :hints (("goal" :in-theory (enable collapse-this)
           :do-not-induct t)))

(defthm collapse-guard-lemma-1
  (consp (assoc-equal 0 (collapse-this frame x)))
  :hints (("goal" :in-theory (enable collapse-this)))
  :rule-classes :type-prescription)

;; I've tried - more than once - to replace this formulation with one where the
;; root is treated just like the rest of the variables, except that it's never
;; allowed to be 1st-complete. That approach, though, is terrible because the
;; base case of the recursive definition becomes "length of frame <= 1" which
;; is incredibly clunky. I mean, there are worse things, but this doesn't seem
;; like a very important refactoring to take on right now.
(defund
  collapse-iter (frame n)
  (declare (xargs :guard (and (frame-p frame) (consp (assoc-equal 0 frame))
                              (natp n))
                  :measure (nfix n)))
  (b*
      (((when (or (zp n) (atom (frame->frame frame))))
        frame)
       (head-index (1st-complete (frame->frame frame)))
       ((when (zp head-index))
        frame)
       (head-frame-val
        (cdr (assoc-equal head-index (frame->frame frame))))
       (src
        (frame-val->src
         (cdr (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))))
    (if
        (zp src)
        (b*
            (((unless (ctx-app-ok (frame->root frame)
                                  head-index
                                  (frame-val->path head-frame-val)))
              frame))
          (collapse-iter (collapse-this frame
                                        (1st-complete (frame->frame frame)))
                         (- n 1)))
      (b*
          ((path (frame-val->path head-frame-val))
           ((when (or (equal src head-index)
                      (atom (assoc-equal src (frame->frame frame)))))
            frame)
           (src-path
            (frame-val->path
             (cdr (assoc-equal src (frame->frame frame)))))
           (src-dir
            (frame-val->dir
             (cdr (assoc-equal src (frame->frame frame)))))
           ((unless (and (prefixp src-path path)
                         (ctx-app-ok src-dir head-index
                                     (nthcdr (len src-path) path))))
            frame))
        (collapse-iter (collapse-this frame
                                      (1st-complete (frame->frame frame)))
                       (- n 1))))))

(defthmd collapse-iter-of-nfix
  (equal (collapse-iter frame (nfix n))
         (collapse-iter frame n))
  :hints (("goal" :in-theory (enable collapse-iter))))

(defcong
  nat-equiv equal (collapse-iter frame n)
  2
  :hints
  (("goal"
    :use (collapse-iter-of-nfix
          (:instance collapse-iter-of-nfix (n n-equiv))))))

(defthm collapse-iter-of-collapse-iter
  (equal (collapse-iter (collapse-iter frame m)
                        n)
         (collapse-iter frame (+ (nfix m) (nfix n))))
  :hints (("goal" :in-theory (enable collapse-iter))))

(defthmd frame-p-of-collapse-iter
  (implies (frame-p frame)
           (frame-p (collapse-iter frame n)))
  :hints (("goal" :in-theory (enable collapse-iter))))

(defthm
  assoc-of-frame->frame-of-collapse-iter
  (implies (not (consp (assoc-equal x (frame->frame frame))))
           (not (consp (assoc-equal x
                                    (frame->frame (collapse-iter frame n))))))
  :hints (("goal" :in-theory (enable collapse-iter)))
  :rule-classes (:rewrite :type-prescription))

(defthm frame-p-of-frame->frame-of-collapse-iter
  (implies (frame-p (frame->frame frame))
           (frame-p (frame->frame (collapse-iter frame n))))
  :hints (("goal" :in-theory (enable collapse-iter))))

(defthm
  no-duplicatesp-of-strip-cars-of-frame->frame-of-collapse-iter
  (implies
   (no-duplicatesp-equal (strip-cars (frame->frame frame)))
   (no-duplicatesp-equal (strip-cars (frame->frame (collapse-iter frame n)))))
  :hints (("goal" :in-theory (enable collapse-iter))))

;; So, to recap, there are two good reasons for separating the root from
;; everything else: for one, the root is what everything else collapses into,
;; and for another, we do not want a bunch of inductions hinged on whether the
;; set of variables is singleton (i.e. length 1.)
(defund
  collapse (frame)
  (declare (xargs :guard (and (frame-p frame)
                              (consp (assoc-equal 0 frame)))
                  :measure (len (frame->frame frame))))
  (b*
      (((when (atom (frame->frame frame)))
        (mv (frame->root frame) t))
       (head-index (1st-complete (frame->frame frame)))
       ((when (zp head-index))
        (mv (frame->root frame) nil))
       (head-frame-val
        (cdr (assoc-equal head-index (frame->frame frame))))
       (src
        (frame-val->src
         (cdr (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))))
    (if
        (zp src)
        (b*
            (((unless (ctx-app-ok (frame->root frame)
                                  head-index
                                  (frame-val->path head-frame-val)))
              (mv (frame->root frame) nil)))
          (collapse
           (collapse-this frame
                          (1st-complete (frame->frame frame)))))
      (b*
          ((path (frame-val->path head-frame-val))
           ((when (or (equal src head-index)
                      (atom (assoc-equal src (frame->frame frame)))))
            (mv (frame->root frame) nil))
           (src-path
            (frame-val->path
             (cdr (assoc-equal src (frame->frame frame)))))
           (src-dir
            (frame-val->dir
             (cdr (assoc-equal src (frame->frame frame)))))
           ((unless (and (prefixp src-path path)
                         (ctx-app-ok src-dir head-index
                                     (nthcdr (len src-path) path))))
            (mv (frame->root frame) nil)))
        (collapse
         (collapse-this frame
                        (1st-complete (frame->frame frame))))))))

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

(defthmd collapse-of-true-list-fix
  (equal (collapse (true-list-fix frame))
         (collapse frame))
  :hints (("goal" :in-theory (enable collapse)
           :induct (collapse frame)
           :expand (collapse (true-list-fix frame)))))

(defcong
  list-equiv equal (collapse frame)
  1
  :hints (("goal" :use ((:instance collapse-of-true-list-fix
                                   (frame frame-equiv))
                        collapse-of-true-list-fix))))

(defthmd collapse-iter-is-collapse
  (implies (>= (nfix n) (len (frame->frame frame)))
           (equal (collapse frame)
                  (mv (frame->root (collapse-iter frame n))
                      (atom (frame->frame (collapse-iter frame n))))))
  :hints (("goal" :in-theory (enable collapse-iter collapse))))

(defthm collapse-of-collapse-iter
  (implies (mv-nth 1 (collapse frame))
           (mv-nth 1 (collapse (collapse-iter frame n))))
  :hints (("goal" :in-theory (enable collapse-iter collapse))))

;; I was thinking we could use this as the starting point for getting rid of
;; collapse entirely, so that we have a smaller number of functions to keep in
;; lockstep: namely collapse-iter, collapse-seq and partial-collapse. However,
;; I think it's quite likely that keeping these functions in lockstep will be
;; less work than trying to redo the dozen-plus lemmas that use induction on
;; collapse directly.
(defthmd
  collapse-iter-correctness-1
  (equal
   (collapse frame)
   (mv
    (frame->root (collapse-iter frame (len (frame->frame frame))))
    (atom (frame->frame (collapse-iter frame (len (frame->frame frame)))))))
  :hints (("goal" :use (:instance collapse-iter-is-collapse
                                  (n (len (frame->frame frame)))))))

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

(defthmd
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

(encapsulate
  ()

  (local
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
              :do-not-induct t))))

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

(defthm abs-addrs-when-absfat-equiv-lemma-1
  (implies (and (abs-file-alist-p abs-file-alist1)
                (absfat-subsetp abs-file-alist1 abs-file-alist2))
           (subsetp-equal (abs-addrs abs-file-alist1)
                          (abs-addrs abs-file-alist2)))
  :hints (("goal" :in-theory (enable absfat-subsetp abs-addrs
                                     no-duplicatesp-of-abs-addrs-of-put-assoc-lemma-1))))

(defthm
  abs-addrs-when-absfat-equiv
  (implies (absfat-equiv x y)
           (set-equiv (abs-addrs (abs-fs-fix x))
                      (abs-addrs (abs-fs-fix y))))
  :hints (("goal" :in-theory (e/d (absfat-equiv set-equiv abs-fs-p)
                                  (abs-addrs-when-absfat-equiv-lemma-1))
           :use ((:instance abs-addrs-when-absfat-equiv-lemma-1
                            (abs-file-alist1 (abs-fs-fix x))
                            (abs-file-alist2 (abs-fs-fix y)))
                 (:instance abs-addrs-when-absfat-equiv-lemma-1
                            (abs-file-alist2 (abs-fs-fix x))
                            (abs-file-alist1 (abs-fs-fix y))))))
  :rule-classes :congruence)

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
          (:rewrite absfat-subsetp-transitivity))))))

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

(defthmd absfat-equiv-implies-set-equiv-addrs-at-1-lemma-1
  (implies (and (not (natp x))
                (atom x)
                (not (member-equal 0 (abs-fs-fix fs))))
           (not (member-equal x fs)))
  :hints (("goal" :in-theory (enable abs-fs-fix))))

(defthm absfat-equiv-implies-set-equiv-addrs-at-1-lemma-4
  (implies (and (abs-file-alist-p fs-equiv)
                (absfat-subsetp fs fs-equiv))
           (subsetp-equal (abs-top-addrs fs)
                          (abs-top-addrs fs-equiv)))
  :hints (("goal" :in-theory (enable abs-top-addrs absfat-subsetp
                                     absfat-equiv-implies-set-equiv-addrs-at-1-lemma-1))))

(defthm absfat-equiv-implies-set-equiv-addrs-at-1-lemma-2
  (implies (and (abs-fs-p fs)
                (absfat-subsetp fs fs-equiv)
                (consp (assoc-equal (fat32-filename-fix (car relpath))
                                    fs)))
           (consp (assoc-equal (fat32-filename-fix (car relpath))
                               fs-equiv)))
  :hints (("goal" :in-theory (enable abs-fs-p))))

(defthm absfat-equiv-implies-set-equiv-addrs-at-1-lemma-3
  (implies (and (abs-fs-p fs)
                (abs-fs-p fs-equiv)
                (absfat-subsetp fs fs-equiv))
           (subsetp-equal (addrs-at fs relpath)
                          (addrs-at fs-equiv relpath)))
  :hints (("goal" :in-theory (enable addrs-at))))

(defcong absfat-equiv set-equiv (addrs-at fs relpath) 1
  :hints
  (("goal"
    :in-theory (e/d (absfat-equiv set-equiv)
                    (absfat-equiv-implies-set-equiv-addrs-at-1-lemma-3))
    :use
    ((:instance absfat-equiv-implies-set-equiv-addrs-at-1-lemma-3
                (fs (abs-fs-fix fs)) (fs-equiv (abs-fs-fix fs-equiv)))
     (:instance absfat-equiv-implies-set-equiv-addrs-at-1-lemma-3
                (fs (abs-fs-fix fs-equiv)) (fs-equiv (abs-fs-fix fs)))))))

(defthm
  abs-no-dups-p-of-ctx-app-lemma-1
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
  abs-no-dups-p-of-ctx-app-lemma-3
  (implies
   (and (abs-directory-file-p (cdr (assoc-equal (car x-path)
                                                abs-file-alist1)))
        (abs-file-alist-p abs-file-alist2))
   (equal
    (abs-file-contents-fix
     (ctx-app
      (abs-file->contents$inline (cdr (assoc-equal (car x-path)
                                                   abs-file-alist1)))
      abs-file-alist2 x (cdr x-path)))
    (ctx-app
     (abs-file->contents$inline (cdr (assoc-equal (car x-path)
                                                  abs-file-alist1)))
     abs-file-alist2 x (cdr x-path)))))

;; This doesn't work all the time as a type prescription rule, because
;; rewriting is sometimes needed to establish the hypotheses.
(defthm
  abs-no-dups-p-of-ctx-app-lemma-4
  (implies (and (abs-no-dups-p abs-file-alist)
                (fat32-filename-p name))
           (atom (assoc-equal name
                              (remove1-assoc-equal name abs-file-alist))))
  :hints (("goal" :in-theory (enable abs-no-dups-p))))

(defthm
  abs-no-dups-p-of-ctx-app
  (implies (ctx-app-ok abs-file-alist1 x x-path)
           (equal (abs-no-dups-p (ctx-app abs-file-alist1
                                          abs-file-alist2 x x-path))
                  (not (intersectp-equal (names-at abs-file-alist1 x-path)
                                         (names-at abs-file-alist2 nil)))))
  :hints (("goal" :in-theory (e/d (ctx-app ctx-app-ok
                                           names-at abs-no-dups-p addrs-at)
                                  (nfix))))
  :rule-classes
  ((:rewrite
    :corollary
    (equal (abs-no-dups-p (ctx-app abs-file-alist1
                                   abs-file-alist2 x x-path))
           (not (and (ctx-app-ok abs-file-alist1 x x-path)
                     (intersectp-equal (names-at abs-file-alist1 x-path)
                                       (names-at abs-file-alist2 nil))))))))

(defthm abs-fs-p-of-ctx-app
  (equal (abs-fs-p (ctx-app abs-file-alist1
                            abs-file-alist2 x x-path))
         (not (and (ctx-app-ok abs-file-alist1 x x-path)
                   (intersectp-equal (names-at abs-file-alist1 x-path)
                                     (names-at abs-file-alist2 nil)))))
  :hints (("goal" :in-theory (enable abs-fs-p))))

(defthm
  strip-cars-of-ctx-app
  (implies
   (ctx-app-ok abs-file-alist1 x x-path)
   (equal (strip-cars (ctx-app abs-file-alist1
                               abs-file-alist2 x x-path))
          (if (consp x-path)
              (strip-cars (abs-fs-fix abs-file-alist1))
            (append (strip-cars (remove-equal (nfix x)
                                              (abs-fs-fix abs-file-alist1)))
                    (strip-cars (abs-fs-fix abs-file-alist2))))))
  :hints (("goal" :in-theory (e/d (ctx-app ctx-app-ok addrs-at)
                                  (nfix))))
  :rule-classes
  ((:rewrite
    :corollary
    (equal
     (strip-cars (ctx-app abs-file-alist1
                          abs-file-alist2 x x-path))
     (if (or (not (ctx-app-ok abs-file-alist1 x x-path))
             (consp x-path))
         (strip-cars (abs-fs-fix abs-file-alist1))
       (append (strip-cars (remove-equal (nfix x)
                                         (abs-fs-fix abs-file-alist1)))
               (strip-cars (abs-fs-fix abs-file-alist2))))))))

;; The change we're making to this theorem is going to potentially make us
;; regret having done this...
(defthm
  names-at-of-ctx-app
  (implies
   (abs-fs-p (ctx-app root abs-file-alist x x-path))
   (equal
    (names-at (ctx-app root abs-file-alist x x-path)
              relpath)
    (cond ((and (ctx-app-ok root x x-path)
                (equal (fat32-filename-list-fix x-path)
                       (fat32-filename-list-fix relpath)))
           (append (names-at root relpath)
                   (names-at abs-file-alist nil)))
          ((and (ctx-app-ok root x x-path)
                (prefixp (fat32-filename-list-fix x-path)
                         (fat32-filename-list-fix relpath))
                (not (member-equal (nth (len x-path)
                                        (fat32-filename-list-fix relpath))
                                   (names-at root x-path))))
           (names-at abs-file-alist
                     (nthcdr (len x-path) relpath)))
          (t (names-at root relpath)))))
  :hints
  (("goal" :induct (mv (ctx-app root abs-file-alist x x-path)
                       (fat32-filename-list-prefixp x-path relpath))
    :in-theory (e/d (prefixp names-at ctx-app-ok addrs-at ctx-app
                             names-at fat32-filename-list-fix)
                    (nfix
                     (:REWRITE REMOVE-WHEN-ABSENT)
                     (:DEFINITION MEMBER-EQUAL)
                     (:DEFINITION REMOVE-EQUAL)
                     (:REWRITE ABS-FILE-ALIST-P-CORRECTNESS-1)
                     (:REWRITE ABS-ADDRS-WHEN-M1-FILE-ALIST-P)
                     (:DEFINITION NO-DUPLICATESP-EQUAL)
                     (:REWRITE
                      ABSFAT-EQUIV-IMPLIES-SET-EQUIV-ADDRS-AT-1-LEMMA-1)
                     (:REWRITE M1-FILE-CONTENTS-P-CORRECTNESS-1))))
   ("subgoal *1/4" :cases ((null (fat32-filename-fix (car relpath)))))))

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

(defthmd dist-names-of-true-list-fix
  (equal (dist-names dir relpath (true-list-fix frame))
         (dist-names dir relpath frame))
  :hints (("goal" :in-theory (enable dist-names))))

(defcong
  list-equiv
  equal (dist-names dir relpath frame)
  3
  :hints (("goal" :use ((:instance dist-names-of-true-list-fix
                                   (frame frame-equiv))
                        dist-names-of-true-list-fix))))

(defthm dist-names-of-ctx-app-lemma-2
  (equal (names-at fs (nthcdr (len relpath) relpath))
         (names-at fs nil))
  :hints (("goal" :in-theory (enable names-at))))

(defthm dist-names-of-ctx-app-lemma-3
  (implies (prefixp (frame-val->path (cdr (car frame)))
                    relpath)
           (prefixp (frame-val->path (cdr (car frame)))
                    (append relpath x-path))))

(defthm
  dist-names-of-ctx-app-lemma-4
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
  dist-names-of-ctx-app-lemma-1
  (implies
   (and
    (equal (fat32-filename-list-fix x-path)
           (nthcdr (len relpath)
                   (frame-val->path (cdr (car frame)))))
    (not (intersectp-equal
          (remove-equal nil
                        (strip-cars (frame-val->dir (cdr (car frame)))))
          (names-at abs-file-alist2
                    (nthcdr (+ (len relpath) (len x-path))
                            (frame-val->path (cdr (car frame))))))))
   (not (intersectp-equal
         (remove-equal nil
                       (strip-cars (abs-fs-fix abs-file-alist2)))
         (remove-equal nil
                       (strip-cars (frame-val->dir (cdr (car frame))))))))
  :hints
  (("goal" :in-theory (e/d (names-at)
                           ((:rewrite nthcdr-of-nthcdr)
                            (:rewrite nthcdr-when->=-n-len-l)))
    :use ((:instance (:rewrite nthcdr-when->=-n-len-l)
                     (l (fat32-filename-list-fix x-path))
                     (n (len (fat32-filename-list-fix x-path))))
          (:instance (:rewrite nthcdr-of-nthcdr)
                     (x (frame-val->path (cdr (car frame))))
                     (b (len relpath))
                     (a (len (fat32-filename-list-fix x-path))))))))

(defthm
  dist-names-of-ctx-app
  (implies (and (abs-fs-p (ctx-app abs-file-alist1
                                   abs-file-alist2 x x-path))
                (dist-names abs-file-alist1 relpath frame)
                (dist-names abs-file-alist2 (append relpath x-path)
                            frame))
           (dist-names (ctx-app abs-file-alist1
                                abs-file-alist2 x x-path)
                       relpath frame))
  :hints
  (("goal"
    :in-theory (e/d (dist-names names-at)
                    ((:rewrite remove-when-absent)
                     (:rewrite abs-fs-p-correctness-1))))))

(defthm
  names-at-of-put-assoc
  (implies (and (abs-fs-p fs)
                (fat32-filename-p name))
           (equal (names-at (put-assoc-equal name val fs)
                            relpath)
                  (cond ((and (atom relpath)
                              (atom (assoc-equal name fs)))
                         (append (names-at fs relpath)
                                 (list name)))
                        ((and (consp relpath)
                              (equal (fat32-filename-fix (car relpath))
                                     name)
                              (abs-directory-file-p (abs-file-fix val)))
                         (names-at (abs-file->contents val)
                                   (cdr relpath)))
                        ((and (consp relpath)
                              (equal (fat32-filename-fix (car relpath))
                                     name))
                         nil)
                        (t (names-at fs relpath)))))
  :hints (("goal" :in-theory (enable names-at))))

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
  abs-separate-of-put-assoc
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

(defthmd abs-separate-of-true-list-fix
  (equal (abs-separate (true-list-fix frame))
         (abs-separate frame))
  :hints (("goal" :in-theory (enable abs-separate))))

(defcong
  list-equiv equal (abs-separate frame)
  1
  :hints (("goal" :use ((:instance abs-separate-of-true-list-fix
                                   (frame frame-equiv))
                        abs-separate-of-true-list-fix))))

(defthm
  abs-separate-of-frame->frame-of-collapse-this-lemma-1
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

(defthm
  abs-separate-of-frame->frame-of-collapse-this-lemma-16
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
  :hints (("goal" :in-theory (enable dist-names names-at len-of-fat32-filename-list-fix))))

;; The :with hint doesn't work, because of hiding.
(defthm
  abs-separate-of-frame->frame-of-collapse-this-lemma-2
  (implies (abs-separate frame)
           (dist-names (frame-val->dir (cdr (assoc-equal x frame)))
                       (frame-val->path (cdr (assoc-equal x frame)))
                       (remove-assoc-equal x frame)))
  :hints
  (("goal" :in-theory (e/d (abs-separate dist-names len-of-fat32-filename-list-fix))
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

;; This is interesting because it talks about two arbitrarily chosen abstract
;; variables. Somehow it's hard to use directly, though...
(defthm
  abs-separate-of-frame->frame-of-collapse-this-lemma-3
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

(defthm
  abs-separate-of-frame->frame-of-collapse-this-lemma-4
  (implies (abs-separate frame)
           (no-duplicatesp-equal
            (abs-addrs (frame-val->dir (cdr (assoc-equal x frame))))))
  :hints (("goal" :in-theory (enable abs-separate))))

(defthm
  abs-separate-of-frame->frame-of-collapse-this-lemma-5
  (implies
   (and
    (consp
     (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))
    (prefixp
     (frame-val->path
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
     (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
    (ctx-app-ok
     (frame-val->dir
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
     x
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (abs-separate (frame->frame frame))
    (abs-complete
     (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))))
   (abs-separate (frame->frame (collapse-this frame x))))
  :hints (("goal" :in-theory (enable collapse-this
                                     abs-addrs-of-ctx-app-1-lemma-7))))

(defthm
  abs-separate-of-frame->frame-of-collapse-this-lemma-6
  (implies
   (and (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               0)
        (abs-separate (frame->frame frame)))
   (abs-separate (frame->frame (collapse-this frame x))))
  :hints (("goal" :in-theory (enable collapse-this))))

;; This doesn't work as a pure type-prescription rule.
(defthm
  abs-separate-of-frame->frame-of-collapse-this-lemma-7
  (implies
   (and (not (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
        (mv-nth 1 (collapse frame)))
   (consp
    (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 (frame->frame frame))))
  :hints (("goal" :in-theory (enable collapse)))
  :rule-classes (:type-prescription :rewrite))

(defthm abs-separate-of-frame->frame-of-collapse-this-lemma-8
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
    (e/d (collapse abs-addrs-of-ctx-app-1-lemma-7)
         ((:rewrite remove-assoc-of-put-assoc)
          (:rewrite remove-assoc-of-remove-assoc)
          (:rewrite abs-file-alist-p-when-m1-file-alist-p)))
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
  abs-separate-of-frame->frame-of-collapse-this-lemma-9
  (implies
   (and (not (zp (1st-complete frame)))
        (no-duplicatesp-equal (strip-cars frame)))
   (equal (abs-addrs (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                       frame))))
          nil))
  :hints (("goal" :in-theory (enable 1st-complete))))

(defthm
  abs-separate-of-frame->frame-of-collapse-this-lemma-10
  (implies
   (not
    (consp
     (abs-addrs (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
   (abs-complete
    (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))

(defthm
  abs-separate-of-frame->frame-of-collapse-this-lemma-11
  (implies (and (mv-nth 1 (collapse frame))
                (consp (assoc-equal y (frame->frame frame))))
           (< '0
              (1st-complete (frame->frame frame))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable collapse)))
  :rule-classes (:linear :rewrite))

(defthm abs-separate-of-frame->frame-of-collapse-this-lemma-12
  (implies (and (consp (frame->frame frame))
                (mv-nth 1 (collapse frame)))
           (< 0 (1st-complete (frame->frame frame))))
  :hints (("goal" :in-theory (enable collapse)))
  :rule-classes :linear)

(defthm
  abs-separate-of-frame->frame-of-collapse-this-lemma-13
  (implies
   (and (mv-nth 1 (collapse frame))
        (not (zp x)))
   (not (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               x)))
  :hints (("goal"
           :in-theory (enable collapse))))

(defthm
  abs-separate-of-frame->frame-of-collapse-this-lemma-14
  (implies
   (and
    (mv-nth 1 (collapse (collapse-this frame x)))
    (< 0
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
    (< 0
       (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
   (not
    (equal
     (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     (1st-complete (frame->frame frame)))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-13))
    :use (:instance (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-13)
                    (frame (collapse-this frame x))
                    (x (1st-complete (frame->frame frame)))))))

;; This is important when you're reasoning about two ways of collapsing to get
;; to the same place...
(defthm
  abs-separate-of-frame->frame-of-collapse-this-lemma-15
  (implies
   (and (abs-separate (frame->frame frame))
        (mv-nth 1 (collapse frame))
        (not (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
        (frame-p (frame->frame frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (and
    (consp
     (abs-addrs
      (frame-val->dir
       (cdr (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame))))))
    (ctx-app-ok
     (frame-val->dir
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
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
    :in-theory (e/d (collapse)
                    ((:definition no-duplicatesp-equal)
                     (:rewrite remove-assoc-of-remove-assoc)
                     (:definition remove-assoc-equal)
                     (:rewrite remove-assoc-of-put-assoc)
                     (:definition member-equal)
                     (:rewrite abs-file-alist-p-when-m1-file-alist-p)
                     (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)))
    :induct (collapse frame)
    :expand
    ((:with
      ctx-app-ok-of-ctx-app-1
      (ctx-app-ok
       (ctx-app
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
       x
       (nthcdr
        (len
         (frame-val->path
          (cdr
           (assoc-equal
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
      (frame-p (frame->frame frame))
      (no-duplicatesp-equal (strip-cars (frame->frame frame)))
      (fat32-filename-list-equiv
       relpath
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
     (ctx-app-ok
      (frame-val->dir
       (cdr
        (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                     (frame->frame frame))))
      x relpath)))))

(defthm
  abs-separate-of-frame->frame-of-collapse-this
  (implies
   (and
    (abs-separate (frame->frame frame))
    (frame-p (frame->frame frame))
    (mv-nth 1 (collapse frame))
    (not
     (consp
      (abs-addrs
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
    (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (abs-separate (frame->frame (collapse-this frame x))))
  :hints
  (("goal"
    :cases ((equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                   0)))))

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

(defthmd frame-addrs-root-of-true-list-fix
  (equal (frame-addrs-root (true-list-fix frame))
         (frame-addrs-root frame))
  :hints (("goal" :in-theory (enable frame-addrs-root))))

(defcong
  list-equiv
  equal (frame-addrs-root frame)
  1
  :hints
  (("goal" :use ((:instance frame-addrs-root-of-true-list-fix
                            (frame frame-equiv))
                 frame-addrs-root-of-true-list-fix))))

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
           (subsetp-equal (abs-addrs (ctx-app abs-file-alist1
                                              abs-file-alist2 x x-path))
                          (abs-addrs (abs-fs-fix abs-file-alist1))))
  :hints (("goal" :in-theory (e/d (ctx-app) (nfix))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (abs-fs-p abs-file-alist1)
          (atom (abs-addrs (abs-fs-fix abs-file-alist2))))
     (subsetp-equal (abs-addrs (ctx-app abs-file-alist1
                                        abs-file-alist2 x x-path))
                    (abs-addrs abs-file-alist1))))))

;; This is a hack...
(defthm
  abs-separate-correctness-1-lemma-2
  (implies (abs-file-alist-p abs-file-alist)
           (subsetp-equal (abs-addrs (abs-fs-fix abs-file-alist))
                          (abs-addrs abs-file-alist)))
  :hints
  (("goal"
    :expand (abs-addrs abs-file-alist)
    :induct (abs-fs-fix abs-file-alist)
    :in-theory (e/d (abs-addrs abs-fs-fix abs-file-alist-p
                               abs-file-fix abs-file->contents)
                    ((:rewrite abs-addrs-when-m1-file-alist-p-lemma-2)
                     (:rewrite abs-file-alist-p-correctness-1)
                     (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
                     (:rewrite abs-file->contents-when-m1-file-p)
                     (:rewrite m1-file-contents-p-correctness-1)
                     (:rewrite abs-directory-file-p-when-m1-file-p)
                     (:rewrite abs-file-alist-p-when-m1-file-alist-p)
                     (:rewrite abs-file-alist-p-of-cdr))))))

(defthm
  abs-separate-correctness-1-lemma-9
  (implies
   (and (no-duplicatesp-equal (abs-addrs (abs-fs-fix abs-file-alist1)))
        (abs-complete (abs-fs-fix abs-file-alist2))
        (ctx-app-ok abs-file-alist1 x x-path))
   (subsetp-equal (abs-addrs (abs-fs-fix (ctx-app abs-file-alist1
                                                  abs-file-alist2 x x-path)))
                  (remove-equal (nfix x)
                                (abs-addrs (abs-fs-fix abs-file-alist1)))))
  :hints
  (("goal"
    :in-theory (disable abs-addrs-of-ctx-app
                        abs-separate-correctness-1-lemma-2)
    :use
    (abs-addrs-of-ctx-app
     (:instance abs-separate-correctness-1-lemma-2
                (abs-file-alist (ctx-app abs-file-alist1
                                         abs-file-alist2 x x-path))))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (natp x)
          (no-duplicatesp-equal (abs-addrs (abs-fs-fix abs-file-alist1)))
          (abs-complete (abs-fs-fix abs-file-alist2))
          (ctx-app-ok abs-file-alist1 x x-path))
     (not
      (member-equal
       x
       (abs-addrs (abs-fs-fix (ctx-app abs-file-alist1
                                       abs-file-alist2 x x-path)))))))))

(defthm
  abs-separate-correctness-1-lemma-21
  (implies
   (dist-names root nil frame)
   (not (intersectp-equal
         (names-at (frame-val->dir (cdr (assoc-equal x frame)))
                   nil)
         (names-at root
                   (frame-val->path (cdr (assoc-equal x frame)))))))
  :hints (("goal" :in-theory (enable dist-names
                                     prefixp intersectp-equal names-at)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (dist-names root nil frame)
          (fat32-filename-list-equiv
           relpath
           (frame-val->path (cdr (assoc-equal x frame)))))
     (not
      (intersectp-equal (names-at (frame-val->dir (cdr (assoc-equal x frame)))
                                  nil)
                        (names-at root relpath)))))
   (:rewrite
    :corollary
    (implies
     (and (set-equiv names
                     (names-at (frame-val->dir (cdr (assoc-equal x frame)))
                               nil))
          (dist-names root nil frame))
     (not (intersectp-equal
           names
           (names-at root
                     (frame-val->path (cdr (assoc-equal x frame))))))))
   (:rewrite
    :corollary
    (implies
     (and (dist-names root nil frame)
          (fat32-filename-list-equiv
           relpath
           (frame-val->path (cdr (assoc-equal x frame)))))
     (not
      (intersectp-equal (names-at root relpath)
                        (names-at (frame-val->dir (cdr (assoc-equal x frame)))
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
    :expand ((names-at (remove-equal x fs)
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
                (abs-fs-p (ctx-app root abs-file-alist x x-path)))
           (dist-names (ctx-app root abs-file-alist x x-path)
                       nil frame))
  :hints (("goal" :in-theory (enable dist-names prefixp))))

;; Obtained by replacing (1st-complete frame) with x in the proof-builder.
(defthm
  abs-separate-correctness-1-lemma-4
  (implies
   (and
    (dist-names root nil frame)
    (abs-separate frame)
    (abs-fs-p (ctx-app root
                       (frame-val->dir (cdr (assoc-equal x frame)))
                       x
                       (frame-val->path (cdr (assoc-equal x frame))))))
   (dist-names
    (ctx-app root
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
     (ctx-app root
              (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                frame)))
              (1st-complete frame)
              (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                 frame))))))
   (abs-separate
    (frame-with-root
     (ctx-app root
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
                    (abs-addrs-of-ctx-app))
    :use
    (:instance
     (:rewrite abs-addrs-of-ctx-app)
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
                                     abs-file->contents abs-file-alist-p))))

(defthm
  abs-separate-correctness-1-lemma-27
  (implies
   (and
    (not (intersectp-equal (names-at (frame-val->dir (cdr (car frame)))
                                     nil)
                           (names-at root
                                     (frame-val->path (cdr (car frame))))))
    (prefixp (frame-val->path (cdr (car frame)))
             (fat32-filename-list-fix relpath))
    (not (intersectp-equal (names-at dir nil)
                           (names-at root relpath)))
    (abs-fs-p (ctx-app (frame-val->dir (cdr (car frame)))
                       dir x
                       (nthcdr (len (frame-val->path (cdr (car frame))))
                               relpath))))
   (not
    (intersectp-equal
     (names-at root
               (frame-val->path (cdr (car frame))))
     (names-at
      (ctx-app (frame-val->dir (cdr (car frame)))
               dir x
               (nthcdr (len (frame-val->path (cdr (car frame))))
                       relpath))
      nil))))
  :hints (("goal" :in-theory (e/d (names-at)
                                  (abs-separate-correctness-1-lemma-8))
           :use (:instance abs-separate-correctness-1-lemma-8
                           (x (frame-val->dir (cdr (car frame))))))))

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
     (ctx-app (frame-val->dir (cdr (assoc-equal src frame)))
              dir x
              (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
                      relpath))))
   (dist-names
    root nil
    (put-assoc-equal
     src
     (frame-val
      (frame-val->path (cdr (assoc-equal src frame)))
      (ctx-app (frame-val->dir (cdr (assoc-equal src frame)))
               dir x
               (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
                       relpath))
      (frame-val->src (cdr (assoc-equal src frame))))
     frame)))
  :hints (("goal" :in-theory (enable dist-names prefixp
                                     len-of-fat32-filename-list-fix))))

(defthm
  abs-separate-correctness-1-lemma-18
  (implies
   (and
    (abs-fs-p
     (ctx-app
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
      (ctx-app
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
     (ctx-app (frame-val->dir (cdr (car frame)))
              dir x
              (nthcdr (len (frame-val->path (cdr (car frame))))
                      relpath)))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite abs-addrs-of-ctx-app))
    :use ((:instance (:rewrite abs-addrs-of-ctx-app)
                     (x-path (nthcdr (len (frame-val->path (cdr (car frame))))
                                     relpath))
                     (x x)
                     (abs-file-alist2 dir)
                     (abs-file-alist1 (frame-val->dir (cdr (car frame)))))))))

(defthm
  abs-separate-correctness-1-lemma-10
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

(defthm abs-separate-correctness-1-lemma-14
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
         (ctx-app
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
       (ctx-app
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
        (ctx-app
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
         (ctx-app
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
           (ctx-app
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
         (ctx-app
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
        (ctx-app
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
  :hints (("goal" :in-theory (enable collapse collapse-this))))

(defthm
  abs-separate-correctness-1-lemma-7
  (implies
   (and (< 0 (1st-complete frame))
        (ctx-app-ok root (1st-complete frame)
                    (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                       frame))))
        (frame-p frame)
        (no-duplicatesp-equal (abs-addrs (abs-fs-fix root)))
        (no-duplicatesp-equal (strip-cars frame)))
   (not
    (member-equal
     (1st-complete frame)
     (abs-addrs
      (mv-nth
       0
       (collapse
        (frame-with-root
         (ctx-app root
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
    :in-theory (e/d (intersectp-equal))
    :use
    ((:instance
      abs-separate-correctness-1-lemma-6
      (frame
       (frame-with-root
        (ctx-app root
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
    (ctx-app-ok root (1st-complete frame)
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
          (ctx-app root
                   (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                     frame)))
                   (1st-complete frame)
                   (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                      frame))))
          (remove-assoc-equal (1st-complete frame)
                              frame)))))))
    (frame-p frame)
    (no-duplicatesp-equal (abs-addrs (abs-fs-fix root)))
    (no-duplicatesp-equal (strip-cars frame)))
   (not
    (intersectp-equal
     (strip-cars frame)
     (abs-addrs
      (mv-nth
       0
       (collapse
        (frame-with-root
         (ctx-app root
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
          (ctx-app root
                   (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                     frame)))
                   (1st-complete frame)
                   (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                      frame))))
          (remove-assoc-equal (1st-complete frame)
                              frame))))))
     (l (strip-cars frame))))))

(defthm
  abs-separate-correctness-1-lemma-19
  (implies
   (and (< 0
           (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
        (no-duplicatesp-equal (abs-addrs (frame->root frame))))
   (no-duplicatesp-equal (abs-addrs (frame->root (collapse-this frame x)))))
  :hints (("goal" :in-theory (enable collapse-this))))

(defthm
  abs-separate-correctness-1-lemma-32
  (implies
   (and
    (consp
     (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))
    (prefixp
     (frame-val->path
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
     (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
    (ctx-app-ok
     (frame-val->dir
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
     x
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
    (dist-names (frame->root frame)
                nil (frame->frame frame))
    (abs-separate (frame->frame frame))
    (not
     (consp
      (abs-addrs
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))))))
   (dist-names (frame->root frame)
               nil
               (frame->frame (collapse-this frame x))))
  :hints (("goal" :in-theory (enable collapse-this
                                     abs-addrs-of-ctx-app-1-lemma-7))))

(defthm
  abs-separate-correctness-1-lemma-28
  (implies
   (and (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               0)
        (frame-p (frame->frame frame))
        (subsetp-equal (abs-addrs (frame->root frame))
                       (frame-addrs-root (frame->frame frame))))
   (subsetp-equal (remove-equal x (abs-addrs (frame->root frame)))
                  (frame-addrs-root (frame->frame (collapse-this frame x)))))
  :hints (("goal" :in-theory (enable collapse-this))))

(defthm
  abs-separate-correctness-1-lemma-22
  (implies
   (and
    (ctx-app-ok (frame->root frame)
                x
                (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
    (no-duplicatesp-equal (abs-addrs (frame->root frame)))
    (dist-names (frame->root frame)
                nil (frame->frame frame))
    (abs-complete
     (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))))
   (no-duplicatesp-equal (abs-addrs (frame->root (collapse-this frame x)))))
  :hints (("goal" :in-theory (enable collapse-this))))

(defthm
  abs-separate-correctness-1-lemma-37
  (implies
   (and (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
        (dist-names (frame->root frame)
                    nil (frame->frame frame))
        (abs-separate (frame->frame frame)))
   (dist-names
    (ctx-app (frame->root frame)
             (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
             x
             (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
    nil
    (frame->frame (collapse-this frame x))))
  :hints (("goal" :in-theory (enable collapse-this))))

(defthm
  abs-separate-correctness-1-lemma-38
  (implies
   (and
    (< 0 x)
    (consp
     (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))
    (ctx-app-ok
     (frame-val->dir
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
     x
     (nthcdr
      (len
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              (frame->frame frame)))))
      (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
    (frame-p (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (subsetp-equal (abs-addrs (frame->root frame))
                   (frame-addrs-root (frame->frame frame)))
    (not
     (consp
      (abs-addrs
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))))))
   (subsetp-equal (abs-addrs (frame->root frame))
                  (frame-addrs-root (frame->frame (collapse-this frame x)))))
  :hints (("goal" :in-theory (enable collapse-this
                                     abs-addrs-of-ctx-app-1-lemma-7))))

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

(defund 1st-complete-under-path (frame path)
  (declare (xargs :guard (frame-p frame)))
  (b* (((when (atom frame)) 0)
       (head-index (caar frame))
       (head-frame-val (cdar frame)))
    (if (and (abs-complete (frame-val->dir head-frame-val))
             (prefixp path (frame-val->path head-frame-val)))
        (mbe :exec head-index :logic (nfix head-index))
      (1st-complete-under-path (cdr frame) path))))

(defund 1st-complete-under-path-src (frame path)
  (declare (xargs :guard (and (frame-p frame)
                              (consp (assoc-equal (1st-complete-under-path
                                                   frame path)
                                                  frame)))))
  (frame-val->src (cdr (assoc-equal (1st-complete-under-path frame path) frame))))

(defund
  1st-complete-under-path-src
  (frame path)
  (declare
   (xargs
    :guard
    (and
     (frame-p frame)
     (consp
      (assoc-equal (1st-complete-under-path frame path)
                   frame)))))
  (frame-val->src
   (cdr
    (assoc-equal (1st-complete-under-path frame path)
                 frame))))

(defthm
  1st-complete-under-path-correctness-1
  (implies (not (zp (1st-complete-under-path frame path)))
           (consp (assoc-equal (1st-complete-under-path frame path)
                               frame)))
  :hints (("goal" :in-theory (enable 1st-complete-under-path)))
  :rule-classes :type-prescription)

(defund
  partial-collapse (frame pathname)
  (declare (xargs :guard (and (frame-p frame)
                              (consp (assoc-equal 0 frame)))
                  :measure (len (frame->frame frame))))
  (b*
      (((when (atom (frame->frame frame)))
        frame)
       (head-index
        (1st-complete-under-path (frame->frame frame)
                                 pathname))
       ((when (zp head-index)) frame)
       (head-frame-val
        (cdr (assoc-equal head-index (frame->frame frame))))
       (src
        (frame-val->src
         (cdr
          (assoc-equal
           (1st-complete-under-path (frame->frame frame)
                                    pathname)
           (frame->frame frame))))))
    (if
        (zp src)
        (b*
            (((unless (ctx-app-ok (frame->root frame)
                                  head-index
                                  (frame-val->path head-frame-val)))
              frame))
          (partial-collapse (collapse-this frame head-index)
                            pathname))
      (b*
          ((path (frame-val->path head-frame-val))
           ((when (or (equal src head-index)
                      (atom (assoc-equal src (frame->frame frame)))))
            frame)
           (src-path
            (frame-val->path
             (cdr (assoc-equal src (frame->frame frame)))))
           (src-dir
            (frame-val->dir
             (cdr (assoc-equal src (frame->frame frame)))))
           ((unless (and (prefixp src-path path)
                         (ctx-app-ok src-dir head-index
                                     (nthcdr (len src-path) path))))
            frame))
        (partial-collapse (collapse-this frame head-index)
                          pathname)))))

(defthm frame-p-of-partial-collapse
  (implies (frame-p frame)
           (frame-p (partial-collapse frame path)))
  :hints (("goal" :in-theory (enable partial-collapse))))

(defthmd
  ctx-app-ok-when-absfat-equiv-lemma-1
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
  ctx-app-ok-when-absfat-equiv-lemma-3
  (implies (and (abs-fs-p abs-file-alist1)
                (abs-fs-p abs-file-alist2)
                (absfat-equiv abs-file-alist1 abs-file-alist2)
                (consp (assoc-equal (fat32-filename-fix (car x-path))
                                    abs-file-alist1)))
           (consp (assoc-equal (fat32-filename-fix (car x-path))
                               abs-file-alist2)))
  :hints
  (("goal"
    :use (:instance (:rewrite ctx-app-ok-when-absfat-equiv-lemma-1)
                    (abs-file-alist2 abs-file-alist1)
                    (abs-file-alist1 abs-file-alist2)
                    (x (fat32-filename-fix (car x-path)))))))

(defthm ctx-app-ok-when-absfat-equiv-lemma-4
  (implies (and (natp x)
                (absfat-subsetp abs-file-alist1 abs-file-alist2)
                (member-equal x abs-file-alist1))
           (member-equal x abs-file-alist2))
  :hints (("goal" :in-theory (enable absfat-subsetp))))

(defthm
  ctx-app-ok-when-absfat-equiv-1
  (implies (absfat-equiv abs-file-alist1 abs-file-alist2)
           (equal (ctx-app-ok abs-file-alist1 x x-path)
                  (ctx-app-ok abs-file-alist2 x x-path)))
  :hints
  (("goal"
    :in-theory (e/d (ctx-app-ok)
                    (abs-file->contents-when-m1-file-p nfix))))
  :rule-classes :congruence)

;; This is kinda general.
(defthmd ctx-app-ok-when-absfat-equiv-lemma-6
  (implies (and (natp x)
                (absfat-equiv abs-file-alist1 abs-file-alist2)
                (abs-fs-p abs-file-alist1)
                (abs-fs-p abs-file-alist2))
           (iff (member-equal x abs-file-alist1)
                (member-equal x abs-file-alist2)))
  :hints (("goal" :in-theory (enable absfat-equiv)
           :do-not-induct t)))

(defthm
  ctx-app-ok-when-absfat-equiv-lemma-2
  (implies (and (member-equal x (abs-fs-fix abs-file-alist3))
                (natp x)
                (absfat-equiv abs-file-alist1 abs-file-alist2)
                (not (member-equal x
                                   (abs-addrs (abs-fs-fix abs-file-alist1)))))
           (not (equal (append (remove-equal x (abs-fs-fix abs-file-alist3))
                               (abs-fs-fix abs-file-alist2))
                       (abs-fs-fix abs-file-alist3))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite member-of-append))
    :use ((:instance (:rewrite member-of-append)
                     (y (abs-fs-fix abs-file-alist2))
                     (x (remove-equal x (abs-fs-fix abs-file-alist3)))
                     (a x))
          (:instance (:rewrite ctx-app-ok-when-absfat-equiv-lemma-6)
                     (abs-file-alist1 (abs-fs-fix abs-file-alist2))
                     (abs-file-alist2 (abs-fs-fix abs-file-alist1)))))))

(defthm
  absfat-equiv-of-ctx-app-lemma-1
  (implies
   (and
    (subsetp-equal
     (abs-addrs (abs-file->contents y))
     (abs-addrs (abs-file->contents (cdr (assoc-equal x abs-file-alist2)))))
    (abs-directory-file-p (cdr (assoc-equal x abs-file-alist2))))
   (subsetp-equal (abs-addrs (abs-file->contents y))
                  (abs-addrs abs-file-alist2)))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  absfat-equiv-of-ctx-app-lemma-5
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                            abs-file-alist3)))
    (absfat-subsetp
     (ctx-app
      (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                            abs-file-alist3)))
      abs-file-alist2 x (cdr x-path))
     (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                           abs-file-alist3))))
    (abs-file-alist-p abs-file-alist2))
   (absfat-subsetp
    (abs-file-contents-fix
     (ctx-app (abs-file->contents$inline
               (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                 abs-file-alist3)))
              abs-file-alist2 x (cdr x-path)))
    (abs-file->contents$inline
     (cdr (assoc-equal (fat32-filename-fix (car x-path))
                       abs-file-alist3))))))

(defthm
  absfat-equiv-of-ctx-app-lemma-6
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                            abs-file-alist3)))
    (absfat-subsetp
     (ctx-app
      (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                            abs-file-alist3)))
      abs-file-alist2 x (cdr x-path))
     (ctx-app
      (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                            abs-file-alist3)))
      abs-file-alist1 x (cdr x-path)))
    (abs-file-alist-p abs-file-alist1)
    (abs-file-alist-p abs-file-alist2))
   (absfat-subsetp
    (abs-file-contents-fix
     (ctx-app (abs-file->contents$inline
               (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                 abs-file-alist3)))
              abs-file-alist2 x (cdr x-path)))
    (abs-file-contents-fix
     (ctx-app (abs-file->contents$inline
               (cdr (assoc-equal (fat32-filename-fix (car x-path))
                                 abs-file-alist3)))
              abs-file-alist1 x (cdr x-path))))))

(defthm
  absfat-equiv-of-ctx-app-lemma-2
  (implies
   (and (abs-file-alist-p x)
        (consp (car x)))
   (abs-file-alist-p
    (list (cons (car (car x))
                (abs-file (abs-file->dir-ent (cdr (car x)))
                          (abs-fs-fix (abs-file->contents (cdr (car x)))))))))
  :hints (("goal" :in-theory (enable abs-file-alist-p abs-file))))

(defthm
  absfat-equiv-of-ctx-app-lemma-10
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
  absfat-equiv-of-ctx-app-lemma-11
  (implies (and (abs-file-alist-p x)
                (not (abs-directory-file-p (abs-file-fix (cdr (car x))))))
           (abs-file-alist-p (list (cons (car (car x))
                                         (abs-file-fix (cdr (car x)))))))
  :hints (("goal" :in-theory (enable abs-file-alist-p abs-file-fix))))

(defthm
  absfat-equiv-of-ctx-app-lemma-12
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
                           ((:rewrite absfat-subsetp-of-append-2)
                            (:rewrite abs-fs-fix-of-put-assoc-equal-lemma-2)))
    :use (:instance (:rewrite absfat-subsetp-of-append-2)
                    (z (abs-fs-fix (append (cdr x) z)))
                    (y (list (cons (car (car x))
                                   (abs-file-fix (cdr (car x))))))
                    (x (abs-fs-fix (append (cdr x) y)))))))

;; Too much trouble at least for now to eliminate this subinduction...
(defthm
  absfat-equiv-of-ctx-app-lemma-7
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
                     (:rewrite absfat-subsetp-transitivity-lemma-3)
                     nfix
                     (:rewrite abs-fs-fix-of-put-assoc-equal-lemma-2)))
    :induct t)))

(defthm
  absfat-equiv-of-ctx-app-lemma-8
  (implies (and (abs-file-alist-p x)
                (abs-file-alist-p z)
                (abs-no-dups-p z)
                (fat32-filename-p name)
                (not (consp (assoc-equal name x))))
           (equal (assoc-equal name (abs-fs-fix (append z x)))
                  (assoc-equal name z)))
  :hints
  (("goal" :in-theory
    (e/d (abs-fs-fix abs-no-dups-p abs-fs-p)
         ((:rewrite remove-when-absent)
          (:rewrite abs-fs-p-of-append)
          (:definition remove-equal)
          (:definition member-equal)
          (:rewrite abs-file-alist-p-correctness-1)
          (:rewrite abs-file-alist-p-when-m1-file-alist-p)
          (:rewrite abs-file->contents-when-m1-file-p)
          (:rewrite abs-directory-file-p-when-m1-file-p)
          (:rewrite abs-addrs-when-m1-file-alist-p-lemma-2)
          (:rewrite abs-addrs-when-m1-file-alist-p)
          (:rewrite member-of-abs-addrs-when-natp . 2)
          (:rewrite abs-no-dups-p-when-m1-file-alist-p)
          (:rewrite hifat-file-alist-fix-guard-lemma-1)
          (:rewrite hifat-no-dups-p-when-abs-complete)
          (:definition abs-complete)
          (:rewrite abs-file-p-when-abs-directory-file-p)
          (:rewrite m1-file-alist-p-when-subsetp-equal)
          strip-cars)))))

;; Head off a subinduction.
(defthm
  absfat-equiv-of-ctx-app-lemma-3
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
                     (:rewrite absfat-subsetp-transitivity-lemma-3))))))

(defthm
  absfat-equiv-of-ctx-app-lemma-17
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
                                    no-duplicatesp-of-abs-addrs-of-put-assoc-lemma-1)
                    ((:rewrite abs-file-alist-p-when-m1-file-alist-p)
                     (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
                     (:rewrite abs-file-alist-p-correctness-1)
                     (:rewrite abs-file->contents-when-m1-file-p)
                     (:rewrite absfat-subsetp-transitivity-lemma-3)))
    :induct t)))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies (and (natp x)
                   (absfat-equiv abs-file-alist1 abs-file-alist2)
                   (abs-fs-p abs-file-alist1)
                   (abs-fs-p abs-file-alist2))
              (absfat-equiv (ctx-app abs-file-alist3
                                     abs-file-alist1 x x-path)
                            (ctx-app abs-file-alist3
                                     abs-file-alist2 x x-path)))
     :hints (("goal" :in-theory (e/d (ctx-app absfat-equiv))
              :induct (mv (ctx-app abs-file-alist3
                                   abs-file-alist1 x x-path)
                          (ctx-app abs-file-alist3
                                   abs-file-alist2 x x-path))))))

  ;; Pretty general.
  (defthm
    absfat-equiv-of-ctx-app-1
    (implies (absfat-equiv abs-file-alist1 abs-file-alist2)
             (absfat-equiv (ctx-app abs-file-alist3
                                    abs-file-alist1 x x-path)
                           (ctx-app abs-file-alist3
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
              (absfat-equiv (ctx-app abs-file-alist1
                                     abs-file-alist3 x x-path)
                            (ctx-app abs-file-alist2
                                     abs-file-alist3 x x-path)))
     :hints
     (("goal" :in-theory (e/d (ctx-app-ok ctx-app absfat-equiv)
                              (abs-file->contents-when-m1-file-p
                               (:rewrite abs-no-dups-p-when-m1-file-alist-p)
                               (:rewrite put-assoc-equal-without-change . 2)
                               (:definition put-assoc-equal)
                               (:rewrite abs-file-alist-p-correctness-1)))
       :induct (mv (ctx-app abs-file-alist1
                            abs-file-alist3 x x-path)
                   (ctx-app abs-file-alist2
                            abs-file-alist3 x x-path))
       :expand (:free (abs-file-alist2)
                      (absfat-subsetp nil abs-file-alist2))))))

  ;; Quite general.
  (defthm
    absfat-equiv-of-ctx-app-2
    (implies (absfat-equiv abs-file-alist1 abs-file-alist2)
             (absfat-equiv (ctx-app abs-file-alist1
                                    abs-file-alist3 x x-path)
                           (ctx-app abs-file-alist2
                                    abs-file-alist3 x x-path)))
    :hints
    (("goal"
      :use (:instance lemma
                      (x (nfix x))
                      (abs-file-alist1 (abs-fs-fix abs-file-alist1))
                      (abs-file-alist2 (abs-fs-fix abs-file-alist2)))))
    :rule-classes :congruence))

(defthm ctx-app-of-ctx-app-lemma-1
  (implies (and (abs-complete (abs-fs-fix y))
                (abs-complete (abs-fs-fix z))
                (not (equal (nfix y-var) (nfix z-var)))
                (not (intersectp-equal (names-at y nil)
                                       (names-at z nil)))
                (not (intersectp-equal (names-at y nil)
                                       (names-at x y-path)))
                (not (intersectp-equal (names-at z nil)
                                       (names-at x y-path))))
           (absfat-subsetp (ctx-app (ctx-app x y y-var y-path)
                                    z z-var y-path)
                           (ctx-app (ctx-app x z z-var y-path)
                                    y y-var y-path)))
  :hints (("goal" :in-theory (e/d (ctx-app ctx-app-ok names-at)
                                  (nfix)))))

(defthm
  ctx-app-of-ctx-app-lemma-2
  (implies (and (ctx-app-ok x z-var z-path)
                (not (intersectp-equal (names-at z nil)
                                       (names-at x z-path)))
                (not (prefixp (fat32-filename-list-fix z-path)
                              (fat32-filename-list-fix y-path)))
                (not (intersectp-equal (names-at y nil)
                                       (names-at x y-path)))
                (natp y-var)
                (natp z-var))
           (absfat-subsetp (ctx-app (ctx-app x z z-var z-path)
                                    y y-var y-path)
                           (ctx-app (ctx-app x y y-var y-path)
                                    z z-var z-path)))
  :hints
  (("goal"
    :in-theory
    (e/d (ctx-app ctx-app-ok
                  names-at put-assoc-of-remove addrs-at)
         ((:definition no-duplicatesp-equal)
          (:rewrite abs-addrs-of-ctx-app)
          (:rewrite abs-file-contents-p-when-m1-file-contents-p)
          (:rewrite m1-file-contents-p-correctness-1)
          (:definition member-equal)
          (:rewrite abs-addrs-of-ctx-app-1-lemma-4)
          (:definition assoc-equal)
          (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
          (:type-prescription abs-directory-file-p-when-m1-file-p-lemma-1)))
    :induct (mv (fat32-filename-list-prefixp z-path y-path)
                (ctx-app x z z-var z-path)
                (ctx-app x y y-var y-path)))
   ("subgoal *1/3" :expand ((:free (x y y-var)
                                   (ctx-app x y y-var y-path))
                            (:free (x z z-var)
                                   (ctx-app x z z-var z-path)))
    :cases ((null (fat32-filename-fix (car z-path)))))))

(defthm
  ctx-app-of-ctx-app-lemma-3
  (implies (and (ctx-app-ok x z-var z-path)
                (not (intersectp-equal (names-at z nil)
                                       (names-at x
                                                 z-path)))
                (not (prefixp (fat32-filename-list-fix z-path)
                              (fat32-filename-list-fix y-path)))
                (not (intersectp-equal (names-at y nil)
                                       (names-at x
                                                 y-path))))
           (absfat-subsetp (ctx-app (ctx-app x y y-var y-path)
                                    z z-var z-path)
                           (ctx-app (ctx-app x z z-var z-path)
                                    y y-var y-path)))
  :hints
  (("goal" :in-theory
    (e/d (ctx-app ctx-app-ok addrs-at
                  names-at put-assoc-of-remove)
         (nfix (:definition no-duplicatesp-equal)
               (:rewrite abs-addrs-of-ctx-app)
               (:rewrite abs-file-contents-p-when-m1-file-contents-p)
               (:rewrite m1-file-contents-p-correctness-1)
               (:definition member-equal)
               (:rewrite abs-addrs-of-ctx-app-1-lemma-4)
               (:definition assoc-equal)
               (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)))
    :induct (mv (fat32-filename-list-prefixp z-path y-path)
                (ctx-app x z z-var z-path)
                (ctx-app x y y-var y-path)))
   ("subgoal *1/3" :expand ((:free (x y y-var)
                                   (ctx-app x y y-var y-path))
                            (:free (x z z-var)
                                   (ctx-app x z z-var z-path)))
    :cases ((null (fat32-filename-fix (car z-path)))))))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies (and (abs-complete (abs-fs-fix y))
                   (abs-complete (abs-fs-fix z))
                   (ctx-app-ok x y-var y-path)
                   (ctx-app-ok x z-var z-path)
                   (not (equal (nfix y-var) (nfix z-var)))
                   (abs-no-dups-p (ctx-app (ctx-app x z z-var z-path)
                                           y y-var y-path))
                   (natp y-var)
                   (natp z-var)
                   (not (intersectp-equal (names-at y nil)
                                          (names-at x y-path)))
                   (not (intersectp-equal (names-at z nil)
                                          (names-at x z-path)))
                   (abs-no-dups-p (ctx-app (ctx-app x y y-var y-path)
                                           z z-var z-path)))
              (absfat-equiv (ctx-app (ctx-app x z z-var z-path)
                                     y y-var y-path)
                            (ctx-app (ctx-app x y y-var y-path)
                                     z z-var z-path)))
     :hints
     (("goal" :in-theory (e/d (list-equiv absfat-equiv)
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
       :expand ((:with abs-fs-fix-when-abs-fs-p
                       (abs-fs-fix (ctx-app (ctx-app x y y-var y-path)
                                            z z-var z-path)))
                (:with abs-fs-fix-when-abs-fs-p
                       (abs-fs-fix (ctx-app (ctx-app x z z-var z-path)
                                            y y-var y-path))))))))

  ;; This theorem is interesting because it would really be awesome if it could
  ;; be made hypothesis free, but it's fairly obvious why it can't - there's no
  ;; way to ensure that abs-file-alist2 and abs-file-alist3 won't have names in
  ;; common. A weirdly restricted version of it could exist if it was accessing
  ;; elements from a frame fixed (by an appropriate fixing function) to have
  ;; separate elements.
  (defthm
    ctx-app-of-ctx-app-1
    (implies
     (and
      (abs-complete (abs-fs-fix y))
      (abs-complete (abs-fs-fix z))
      (case-split
       (and (not (equal (nfix y-var) (nfix z-var)))
            (abs-no-dups-p (ctx-app (ctx-app x z z-var z-path)
                                    y y-var y-path))
            (abs-no-dups-p (ctx-app (ctx-app x y y-var y-path)
                                    z z-var z-path))))
      (not (intersectp-equal (names-at y nil)
                             (names-at x y-path)))
      (not (intersectp-equal (names-at z nil)
                             (names-at x z-path))))
     (absfat-equiv (ctx-app (ctx-app x z z-var z-path)
                            y y-var y-path)
                   (ctx-app (ctx-app x y y-var y-path)
                            z z-var z-path)))
    :hints (("goal" :use ((:instance lemma (x (abs-fs-fix x))
                                     (y (abs-fs-fix y))
                                     (z (abs-fs-fix z))
                                     (y-var (nfix y-var))
                                     (z-var (nfix z-var))))
             :in-theory (disable nfix)))))

(defthm
  collapse-congruence-lemma-1
  (implies (and (absfat-equiv (frame->root frame1)
                              (frame->root frame2))
                (syntaxp
                 (not (term-order frame1 frame2)))
                (equal (frame->frame frame1)
                       (frame->frame frame2)))
           (absfat-equiv (frame->root (collapse-this frame1 x))
                         (frame->root (collapse-this frame2 x))))
  :hints (("goal" :in-theory (enable collapse-this)))
  ;; :rule-classes ((:rewrite :loop-stopper ((frame1 frame2 collapse-this))))
  )

(defthm collapse-congruence-lemma-2
  (implies (and (equal (frame->frame frame1)
                       (frame->frame frame2))
                (syntaxp (not (term-order frame1 frame2))))
           (equal (frame->frame (collapse-this frame1 x))
                  (frame->frame (collapse-this frame2 x))))
  :hints (("goal" :in-theory (enable collapse-this))))

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
        (not
         (zp
          (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame1))
                             (frame->frame frame1))))))
        (not
         (or
          (equal
           (frame-val->src
            (cdr
             (assoc-equal (1st-complete (frame->frame frame1))
                          (frame->frame frame1))))
           (1st-complete (frame->frame frame1)))
          (atom
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame1))
                           (frame->frame frame1))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame1))
             (frame->frame frame1))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame1))
                           (frame->frame frame1))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame1))
             (frame->frame frame1)))))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame1))
                            (frame->frame frame1)))))
        (ctx-app-ok
         (frame-val->dir
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame1))
                           (frame->frame frame1))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame1))
             (frame->frame frame1)))))
         (1st-complete (frame->frame frame1))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src
               (cdr
                (assoc-equal (1st-complete (frame->frame frame1))
                             (frame->frame frame1))))
              (remove-assoc-equal
               (1st-complete (frame->frame frame1))
               (frame->frame frame1))))))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame1))
                             (frame->frame frame1)))))))
       (induction-scheme
        (collapse-this frame1
                       (1st-complete (frame->frame frame1)))
        (collapse-this frame2
                       (1st-complete (frame->frame frame2)))))
      ((and
        (not (atom (frame->frame frame1)))
        (not (zp (1st-complete (frame->frame frame1))))
        (zp
         (frame-val->src
          (cdr (assoc-equal (1st-complete (frame->frame frame1))
                            (frame->frame frame1)))))
        (ctx-app-ok
         (frame->root frame1)
         (1st-complete (frame->frame frame1))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame1))
                            (frame->frame frame1))))))
       (induction-scheme
        (collapse-this frame1
                       (1st-complete (frame->frame frame1)))
        (collapse-this frame2
                       (1st-complete (frame->frame frame2)))))
      (t (mv frame1 frame2)))))

  (defthmd
    collapse-congruence-lemma-3
    (implies (and (equal (frame->frame frame1)
                         (frame->frame frame2))
                  (absfat-equiv (frame->root frame1)
                                (frame->root frame2)))
             (and (absfat-equiv (mv-nth 0 (collapse frame1))
                                (mv-nth 0 (collapse frame2)))
                  (equal (mv-nth 1 (collapse frame1))
                         (mv-nth 1 (collapse frame2)))))
    :hints (("goal" :in-theory (enable collapse)
             :induct (induction-scheme frame1 frame2)
             :expand (collapse frame2)))))

(defthm
  collapse-congruence-1
  (implies
   (absfat-equiv root1 root2)
   (and
    (absfat-equiv
     (mv-nth 0
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
    :use
    ((:instance (:rewrite collapse-congruence-lemma-3)
                (frame1 (frame-with-root root1 frame))
                (frame2 (frame-with-root root2 frame))))))
  :rule-classes
  ((:congruence
    :corollary
    (implies
     (absfat-equiv root1 root2)
     (absfat-equiv
      (mv-nth 0
              (collapse (frame-with-root root1 frame)))
      (mv-nth 0
              (collapse (frame-with-root root2 frame))))))
   (:congruence
    :corollary
    (implies
     (absfat-equiv root1 root2)
     (equal
      (mv-nth 1
              (collapse (frame-with-root root1 frame)))
      (mv-nth 1
              (collapse (frame-with-root root2 frame))))))))

(defthm
  collapse-congruence-lemma-4
  (implies (and (absfat-equiv abs-file-alist1 abs-file-alist2)
                (m1-file-alist-p (abs-fs-fix abs-file-alist1))
                (abs-fs-p abs-file-alist2))
           (equal (abs-addrs abs-file-alist2) nil))
  :hints
  (("goal"
    :in-theory (e/d (absfat-equiv)
                    (abs-addrs-when-absfat-equiv-lemma-1))
    :use ((:instance abs-addrs-when-absfat-equiv-lemma-1
                     (abs-file-alist1 (abs-fs-fix abs-file-alist1)))
          (:instance abs-addrs-when-absfat-equiv-lemma-1
                     (abs-file-alist1 abs-file-alist2)
                     (abs-file-alist2 (abs-fs-fix abs-file-alist1)))))))

(defthm
  collapse-congruence-lemma-5
  (implies (and (consp (assoc-equal x frame))
                (absfat-equiv (frame-val->dir (cdr (assoc-equal x frame)))
                              (frame-val->dir val)))
           (equal (1st-complete (put-assoc-equal x val frame))
                  (1st-complete frame)))
  :hints (("goal" :in-theory (enable 1st-complete abs-separate))))

(encapsulate
  ()

  (local
   (defun
       induction-scheme (dir frame x)
     (declare (xargs :verify-guards nil
                     :measure (len (frame->frame frame))))
     (cond
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (not
         (zp
          (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (not
         (or
          (equal
           (frame-val->src
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
           (1st-complete (frame->frame frame)))
          (atom
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame))
             (frame->frame frame))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame))
             (frame->frame frame)))))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
        (ctx-app-ok
         (frame-val->dir
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame))
             (frame->frame frame)))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src
               (cdr
                (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
              (remove-assoc-equal
               (1st-complete (frame->frame frame))
               (frame->frame frame))))))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (equal x (1st-complete (frame->frame frame))))
       (induction-scheme
        (ctx-app
         (frame-val->dir
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (frame->frame frame))))
         dir (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src
               (cdr
                (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
              (frame->frame frame)))))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (collapse-this frame
                       (1st-complete (frame->frame frame)))
        (frame-val->src
         (cdr (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))))
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (not
         (zp
          (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (not
         (or
          (equal
           (frame-val->src
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
           (1st-complete (frame->frame frame)))
          (atom
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame))
             (frame->frame frame))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame))
             (frame->frame frame)))))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
        (ctx-app-ok
         (frame-val->dir
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame))
             (frame->frame frame)))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src
               (cdr
                (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
              (remove-assoc-equal
               (1st-complete (frame->frame frame))
               (frame->frame frame))))))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (equal x
               (frame-val->src
                (cdr
                 (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))))
       (induction-scheme
        (ctx-app
         dir
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
               (cdr
                (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
              (frame->frame frame)))))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (collapse-this frame
                       (1st-complete (frame->frame frame)))
        x))
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (not
         (zp
          (frame-val->src
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))))
        (not
         (or
          (equal
           (frame-val->src
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
           (1st-complete (frame->frame frame)))
          (atom
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame))
             (frame->frame frame))))))
        (prefixp
         (frame-val->path
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame))
             (frame->frame frame)))))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
        (ctx-app-ok
         (frame-val->dir
          (cdr
           (assoc-equal
            (frame-val->src
             (cdr
              (assoc-equal (1st-complete (frame->frame frame))
                           (frame->frame frame))))
            (remove-assoc-equal
             (1st-complete (frame->frame frame))
             (frame->frame frame)))))
         (1st-complete (frame->frame frame))
         (nthcdr
          (len
           (frame-val->path
            (cdr
             (assoc-equal
              (frame-val->src
               (cdr
                (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame))))
              (remove-assoc-equal
               (1st-complete (frame->frame frame))
               (frame->frame frame))))))
          (frame-val->path
           (cdr (assoc-equal (1st-complete (frame->frame frame))
                             (frame->frame frame)))))))
       (induction-scheme
        dir
        (collapse-this frame
                       (1st-complete (frame->frame frame)))
        x))
      ((and
        (not (atom (frame->frame frame)))
        (not (zp (1st-complete (frame->frame frame))))
        (zp
         (frame-val->src
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame)))))
        (ctx-app-ok
         (frame->root frame)
         (1st-complete (frame->frame frame))
         (frame-val->path
          (cdr (assoc-equal (1st-complete (frame->frame frame))
                            (frame->frame frame))))))
       (induction-scheme
        dir
        (collapse-this frame
                       (1st-complete (frame->frame frame)))
        x))
      (t (mv dir frame x)))))

  (defthm
    collapse-congruence-lemma-6
    (implies
     (and (syntaxp (variablep x))
          (consp (assoc-equal x (frame->frame frame)))
          (absfat-equiv
           (frame-val->dir
            (cdr (assoc-equal x (frame->frame frame))))
           dir))
     (and
      (equal
       (mv-nth
        1
        (collapse
         (frame-with-root
          (frame->root frame)
          (put-assoc-equal
           x
           (frame-val
            (frame-val->path
             (cdr (assoc-equal x (frame->frame frame))))
            dir
            (frame-val->src
             (cdr (assoc-equal x (frame->frame frame)))))
           (frame->frame frame)))))
       (mv-nth 1 (collapse frame)))
      (absfat-equiv
       (mv-nth
        0
        (collapse
         (frame-with-root
          (frame->root frame)
          (put-assoc-equal
           x
           (frame-val
            (frame-val->path
             (cdr (assoc-equal x (frame->frame frame))))
            dir
            (frame-val->src
             (cdr (assoc-equal x (frame->frame frame)))))
           (frame->frame frame)))))
       (mv-nth 0 (collapse frame)))))
    :hints
    (("goal"
      :in-theory
      (e/d
       (collapse collapse-this)
       ((:definition remove-assoc-equal)
        (:rewrite remove-assoc-of-remove-assoc)
        (:rewrite abs-file-alist-p-when-m1-file-alist-p)
        (:rewrite
         absfat-equiv-implies-set-equiv-names-at-1-lemma-1)
        (:rewrite put-assoc-equal-without-change . 2)
        (:definition no-duplicatesp-equal)
        (:definition member-equal)
        (:rewrite nthcdr-when->=-n-len-l)
        (:definition remove-equal)
        (:rewrite remove-when-absent)
        (:rewrite 1st-complete-of-put-assoc-2)
        (:definition put-assoc-equal)
        (:rewrite no-duplicatesp-of-strip-cars-of-put-assoc)
        (:type-prescription
         abs-fs-fix-of-put-assoc-equal-lemma-3)))
      :induct (induction-scheme dir frame x)
      :expand
      ((collapse frame)
       (collapse
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          x
          (frame-val
           (frame-val->path
            (cdr (assoc-equal x (frame->frame frame))))
           dir
           (frame-val->src
            (cdr (assoc-equal x (frame->frame frame)))))
          (frame->frame frame))))
       (collapse
        (frame-with-root
         (frame->root frame)
         (put-assoc-equal
          (1st-complete (frame->frame frame))
          (frame-val
           (frame-val->path
            (cdr (assoc-equal (1st-complete (frame->frame frame))
                              (frame->frame frame))))
           dir 0)
          (frame->frame frame)))))))))

(defthm
  collapse-congruence-lemma-7
  (equal
   (collapse (frame-with-root root (remove-assoc 0 frame)))
   (collapse (frame-with-root root frame)))
  :hints
  (("goal"
    :in-theory (enable collapse collapse-this)
    :expand
    ((collapse
      (frame-with-root root (remove-assoc-equal 0 frame)))
     (collapse (frame-with-root root frame)))
    :do-not-induct t)))

;; This can be p helpful...
(defthm
  collapse-congruence-2
  (implies
   (absfat-equiv dir1 dir2)
   (and
    (absfat-equiv
     (mv-nth
      0
      (collapse
       (frame-with-root
        root
        (put-assoc-equal
         x
         (frame-val (frame-val->path (cdr (assoc-equal x frame)))
                    dir1
                    (frame-val->src (cdr (assoc-equal x frame))))
         frame))))
     (mv-nth
      0
      (collapse
       (frame-with-root
        root
        (put-assoc-equal
         x
         (frame-val (frame-val->path (cdr (assoc-equal x frame)))
                    dir2
                    (frame-val->src (cdr (assoc-equal x frame))))
         frame)))))
    (equal
     (mv-nth
      1
      (collapse
       (frame-with-root
        root
        (put-assoc-equal
         x
         (frame-val (frame-val->path (cdr (assoc-equal x frame)))
                    dir1
                    (frame-val->src (cdr (assoc-equal x frame))))
         frame))))
     (mv-nth
      1
      (collapse
       (frame-with-root
        root
        (put-assoc-equal
         x
         (frame-val (frame-val->path (cdr (assoc-equal x frame)))
                    dir2
                    (frame-val->src (cdr (assoc-equal x frame))))
         frame)))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (disable collapse-congruence-lemma-6
             (:rewrite collapse-congruence-lemma-7))
    :use
    ((:instance
      collapse-congruence-lemma-6
      (dir dir2)
      (frame
       (frame-with-root
        root
        (put-assoc-equal
         x
         (frame-val
          (frame-val->path (cdr (assoc-equal x frame)))
          dir1
          (frame-val->src (cdr (assoc-equal x frame))))
         frame))))
     (:instance
      (:rewrite collapse-congruence-lemma-7)
      (frame
       (put-assoc-equal
        0
        (frame-val (frame-val->path (cdr (assoc-equal 0 frame)))
                   dir1
                   (frame-val->src (cdr (assoc-equal 0 frame))))
        frame))
      (root root))
     (:instance
      (:rewrite collapse-congruence-lemma-7)
      (frame
       (put-assoc-equal
        0
        (frame-val (frame-val->path (cdr (assoc-equal 0 frame)))
                   dir2
                   (frame-val->src (cdr (assoc-equal 0 frame))))
        frame))
      (root root))
     (:instance
      (:rewrite collapse-congruence-lemma-7)
      (frame
       (put-assoc-equal
        x
        (frame-val (frame-val->path (cdr (assoc-equal x frame)))
                   dir2
                   (frame-val->src (cdr (assoc-equal x frame))))
        frame))
      (root root)))))
  :rule-classes
  ((:congruence
    :corollary
    (implies
     (absfat-equiv dir1 dir2)
     (absfat-equiv
      (mv-nth
       0
       (collapse
        (frame-with-root
         root
         (put-assoc-equal
          x
          (frame-val (frame-val->path (cdr (assoc-equal x frame)))
                     dir1
                     (frame-val->src (cdr (assoc-equal x frame))))
          frame))))
      (mv-nth
       0
       (collapse
        (frame-with-root
         root
         (put-assoc-equal
          x
          (frame-val (frame-val->path (cdr (assoc-equal x frame)))
                     dir2
                     (frame-val->src (cdr (assoc-equal x frame))))
          frame)))))))
   (:congruence
    :corollary
    (implies
     (absfat-equiv dir1 dir2)
     (equal
      (mv-nth
       1
       (collapse
        (frame-with-root
         root
         (put-assoc-equal
          x
          (frame-val (frame-val->path (cdr (assoc-equal x frame)))
                     dir1
                     (frame-val->src (cdr (assoc-equal x frame))))
          frame))))
      (mv-nth
       1
       (collapse
        (frame-with-root
         root
         (put-assoc-equal
          x
          (frame-val (frame-val->path (cdr (assoc-equal x frame)))
                     dir2
                     (frame-val->src (cdr (assoc-equal x frame))))
          frame)))))))))

;; Ye olde hacky definition...
(defund
  collapse-seq (frame seq)
  (declare (xargs :guard (and (frame-p frame)
                              (consp (assoc-equal 0 frame))
                              (nat-listp seq))
                  :guard-debug t
                  :measure (len (frame->frame frame))))
  (b*
      (((when (or (atom (frame->frame frame))
                  (atom seq)))
        frame)
       (head-index (car seq))
       ((when (or (zp head-index)
                  (atom (assoc-equal (car seq)
                                     (frame->frame frame)))
                  (not (abs-complete
                        (frame-val->dir
                         (cdr (assoc-equal (car seq)
                                           (frame->frame frame))))))))
        frame)
       (head-frame-val
        (cdr (assoc-equal head-index (frame->frame frame))))
       (src
        (frame-val->src (cdr (assoc-equal (car seq)
                                          (frame->frame frame))))))
    (if
        (zp src)
        (b* (((unless (ctx-app-ok (frame->root frame)
                                  head-index
                                  (frame-val->path head-frame-val)))
              frame))
          (collapse-seq (collapse-this frame (car seq))
                        (cdr seq)))
      (b*
          ((path (frame-val->path head-frame-val))
           ((when (or (equal src head-index)
                      (atom (assoc-equal src (frame->frame frame)))))
            frame)
           (src-path
            (frame-val->path
             (cdr (assoc-equal src (frame->frame frame)))))
           (src-dir
            (frame-val->dir
             (cdr (assoc-equal src (frame->frame frame)))))
           ((unless (and (prefixp src-path path)
                         (ctx-app-ok src-dir head-index
                                     (nthcdr (len src-path) path))))
            frame))
        (collapse-seq (collapse-this frame (car seq))
                      (cdr seq))))))

(defthm frame-p-of-collapse-seq
  (implies (frame-p frame)
           (frame-p (collapse-seq frame seq)))
  :hints (("goal" :in-theory (enable collapse-seq))))

(defthm frame-p-of-frame->frame-of-collapse-seq
  (implies (frame-p (frame->frame frame))
           (frame-p (frame->frame (collapse-seq frame seq))))
  :hints (("goal" :in-theory (enable collapse-seq))))

(defthm
  no-duplicatesp-of-strip-cars-of-collapse-seq
  (implies
   (no-duplicatesp (strip-cars (frame->frame frame)))
   (no-duplicatesp (strip-cars (frame->frame (collapse-seq frame seq)))))
  :hints (("goal" :in-theory (enable collapse-seq))))

(defund valid-seqp (frame seq)
  (declare (xargs :guard (and (frame-p frame)
                              (consp (assoc-equal 0 frame))
                              (nat-listp seq))))
  (equal (len (frame->frame (collapse-seq frame seq)))
         (- (len (frame->frame frame))
            (len seq))))

(defthm
  valid-seqp-when-prefixp-lemma-1
  (implies
   (and (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               0)
        (< 0 x)
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (consp (assoc-equal x (frame->frame frame))))
   (equal (len (frame->frame (collapse-this frame x)))
          (+ -1 (len (frame->frame frame)))))
  :hints (("goal" :in-theory (enable collapse-this)
           :do-not-induct t)))

(defthm
  valid-seqp-when-prefixp-lemma-3
  (implies
   (and
    (natp x)
    (consp
     (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame)))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (not (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                x)))
   (equal (len (frame->frame (collapse-this frame x)))
          (+ -1 (len (frame->frame frame)))))
  :hints (("goal" :in-theory (enable collapse-this))))

(defthm
  valid-seqp-when-prefixp
  (implies (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (valid-seqp frame seq1)
                (prefixp seq2 seq1))
           (valid-seqp frame seq2))
  :hints (("goal" :in-theory (enable prefixp valid-seqp collapse-seq)
           :induct (mv (collapse-seq frame seq2)
                       (prefixp seq2 seq1)))))

(defund
  collapse-1st-index (frame x)
  (declare
   (xargs :measure (len (frame->frame frame))
          :hints (("goal" :in-theory (enable collapse-iter)))))
  (if (equal (1st-complete (frame->frame frame))
             x)
      0
    (if (< (len (frame->frame (collapse-iter frame 1)))
           (len (frame->frame frame)))
        (+ 1
           (collapse-1st-index (collapse-iter frame 1)
                               x))
      (len (frame->frame frame)))))

(defthm
  collapse-1st-index-correctness-lemma-1
  (implies
   (and
    (mv-nth 1 (collapse frame))
    (equal
     (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     0)
    (consp (assoc-equal y (frame->frame frame))))
   (ctx-app-ok (frame->root frame)
               (1st-complete (frame->frame frame))
               (frame-val->path$inline
                (cdr (assoc-equal (1st-complete (frame->frame frame))
                                  (frame->frame frame))))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable collapse))))

(defthm
  collapse-1st-index-correctness-1
  (implies
   (and (mv-nth 1 (collapse frame))
        (consp (assoc-equal x (frame->frame frame))))
   (and
    (equal
     (1st-complete
      (frame->frame (collapse-iter frame (collapse-1st-index frame x))))
     x)
    (< (collapse-1st-index frame x)
       (len (frame->frame frame)))))
  :hints
  (("goal" :in-theory
    (e/d (1st-complete collapse
                       collapse-1st-index collapse-iter)
         (member-equal no-duplicatesp-equal
                       nthcdr-when->=-n-len-l
                       (:definition remove-assoc-equal)))
    :induct (collapse-1st-index frame x)
    :expand ((collapse frame)
             (collapse-iter frame 1)))
   ("subgoal *1/1" :expand (1st-complete (frame->frame frame))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (mv-nth 1 (collapse frame))
          (consp (assoc-equal x (frame->frame frame))))
     (equal
      (1st-complete
       (frame->frame (collapse-iter frame (collapse-1st-index frame x))))
      x)))
   (:linear
    :corollary
    (implies
     (and (mv-nth 1 (collapse frame))
          (consp (assoc-equal x (frame->frame frame))))
     (< (collapse-1st-index frame x)
        (len (frame->frame frame))))
    :trigger-terms ((collapse-1st-index frame x)))))

(defthm
  collapse-1st-index-when-absent
  (implies (and (mv-nth 1 (collapse frame))
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (atom (assoc-equal x (frame->frame frame))))
           (equal (collapse-1st-index frame x)
                  (len (frame->frame frame))))
  :hints (("goal" :in-theory (enable collapse
                                     collapse-iter collapse-1st-index))))

(defthm
  collapse-seq-of-collapse-seq
  (implies (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (valid-seqp frame seq1))
           (equal (collapse-seq (collapse-seq frame seq1)
                                seq2)
                  (collapse-seq frame (append seq1 seq2))))
  :hints (("goal" :in-theory (e/d (collapse-seq valid-seqp))
           :induct (mv (collapse-seq frame seq1)
                       (append seq1 seq2)))))

(defund final-val (x frame)
  (frame-val->dir (cdr (assoc-equal
                        x
                        (frame->frame (collapse-iter
                                       frame
                                       (collapse-1st-index frame x)))))))

(defthm
  final-val-of-1st-complete
  (equal (final-val (1st-complete (frame->frame frame))
                    frame)
         (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                           (frame->frame frame)))))
  :hints (("goal" :in-theory (enable final-val
                                     collapse-1st-index collapse-iter))))

(defthmd
  final-val-of-collapse-this-lemma-1
  (implies
   (atom (frame->frame frame))
   (atom
    (assoc-equal
     x
     (frame->frame (collapse-this frame
                                  (1st-complete (frame->frame frame)))))))
  :hints (("goal" :in-theory (enable collapse-this)))
  :rule-classes :type-prescription)

(defthm
  final-val-of-collapse-this-lemma-2
  (implies (mv-nth 1 (collapse frame))
           (iff (consp (assoc-equal x
                                    (frame->frame (collapse-iter frame n))))
                (and (consp (assoc-equal x (frame->frame frame)))
                     (<= (nfix n)
                         (collapse-1st-index frame x)))))
  :hints
  (("goal"
    :in-theory (e/d (collapse collapse-1st-index collapse-iter)
                    ((:definition no-duplicatesp-equal)
                     (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
                     (:definition member-equal)
                     (:rewrite partial-collapse-correctness-lemma-2))))))

(defthm final-val-of-collapse-this-lemma-3
  (implies (and (not (zp x))
                (atom (assoc-equal x frame)))
           (not (equal x (1st-complete frame)))))

(defthm
  final-val-of-collapse-this-lemma-8
  (implies (mv-nth 1 (collapse frame))
           (iff (equal (1st-complete (frame->frame frame))
                       (1st-complete (frame->frame (collapse-iter frame n))))
                (or (zp (1st-complete (frame->frame frame)))
                    (zp n))))
  :hints (("goal" :in-theory (enable collapse collapse-iter))))

(defthmd
  final-val-of-collapse-this-lemma-9
  (implies
   (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (mv-nth 1 (collapse frame)))
   (equal
    (collapse-1st-index frame
                        (1st-complete (frame->frame (collapse-iter frame n))))
    (min (nfix n)
         (len (frame->frame frame)))))
  :hints (("goal" :in-theory (enable collapse-iter
                                     collapse-1st-index collapse))))

(defthm
  final-val-of-collapse-this-lemma-10
  (implies (and (mv-nth 1 (collapse frame))
                (no-duplicatesp-equal (strip-cars (frame->frame frame))))
           (equal (len (frame->frame (collapse-iter frame n)))
                  (nfix (- (len (frame->frame frame))
                           (nfix n)))))
  :hints (("goal" :in-theory (enable collapse collapse-iter))))

(defthm
  final-val-of-collapse-this-lemma-4
  (implies
   (and
    (not (zp n))
    (ctx-app-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
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
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (< 0 (1st-complete (frame->frame frame)))
    (prefixp
     (frame-val->path
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
        (frame->frame frame))))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))
    (mv-nth 1
            (collapse (collapse-this frame
                                     (1st-complete (frame->frame frame))))))
   (not
    (equal
     (collapse-1st-index
      (collapse-iter (collapse-this frame
                                    (1st-complete (frame->frame frame)))
                     n)
      (1st-complete (frame->frame (collapse-iter frame n))))
     (+ (- n)
        (collapse-1st-index
         (collapse-this frame
                        (1st-complete (frame->frame frame)))
         (1st-complete (frame->frame (collapse-iter frame n))))))))
  :hints
  (("goal" :in-theory (e/d (collapse collapse-iter abs-addrs-of-ctx-app-1-lemma-7)
                           ((:definition strip-cars)
                            (:definition assoc-equal)
                            (:rewrite nthcdr-when->=-n-len-l)
                            (:definition member-equal)
                            (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8
                                      . 2)
                            (:definition len)
                            (:definition nthcdr)))
    :use (:instance (:rewrite final-val-of-collapse-this-lemma-9)
                    (n (+ -1 n))
                    (frame (collapse-iter frame 1))))))

(defthm
  final-val-of-collapse-this-lemma-13
  (implies
   (and
    (equal
     (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     0)
    (not (zp n))
    (consp (frame->frame frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (< 0 (1st-complete (frame->frame frame)))
    (ctx-app-ok
     (frame->root frame)
     (1st-complete (frame->frame frame))
     (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame)))))
    (mv-nth 1
            (collapse (collapse-this frame
                                     (1st-complete (frame->frame frame))))))
   (not
    (equal
     (collapse-1st-index
      (collapse-iter (collapse-this frame
                                    (1st-complete (frame->frame frame)))
                     n)
      (1st-complete (frame->frame (collapse-iter frame n))))
     (+ (- n)
        (collapse-1st-index
         (collapse-this frame
                        (1st-complete (frame->frame frame)))
         (1st-complete (frame->frame (collapse-iter frame n))))))))
  :hints
  (("goal" :in-theory (e/d (collapse collapse-iter)
                           ((:definition strip-cars)
                            (:definition assoc-equal)
                            (:rewrite nthcdr-when->=-n-len-l)
                            (:definition member-equal)
                            (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8
                                      . 2)
                            (:definition len)
                            (:definition nthcdr)))
    :use (:instance (:rewrite final-val-of-collapse-this-lemma-9)
                    (n (+ -1 n))
                    (frame (collapse-iter frame 1))))))

(defthm
  final-val-of-collapse-this-lemma-14
  (implies (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (mv-nth 1 (collapse frame))
                (consp (assoc-equal x
                                    (frame->frame (collapse-iter frame n)))))
           (equal (collapse-1st-index (collapse-iter frame n)
                                      x)
                  (- (collapse-1st-index frame x)
                     (nfix n))))
  :hints
  (("goal" :in-theory
    (e/d (collapse-1st-index collapse-iter collapse)
         ((:definition no-duplicatesp-equal)
          (:definition member-equal)
          (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
          (:rewrite nthcdr-when->=-n-len-l)
          (:definition strip-cars)
          (:rewrite member-of-abs-addrs-when-natp . 2)
          (:definition nthcdr)
          (:rewrite final-val-of-collapse-this-lemma-3)
          (:rewrite ctx-app-ok-when-abs-complete)
          (:type-prescription abs-fs-fix-of-put-assoc-equal-lemma-3)
          (:rewrite frame->root-of-collapse-this)
          (:rewrite abs-addrs-when-m1-file-alist-p)
          (:rewrite ctx-app-ok-of-ctx-app-1)
          (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8 . 1)
          (:type-prescription assoc-when-zp-len)
          (:rewrite abs-fs-p-of-ctx-app)
          (:definition len)
          (:rewrite ctx-app-when-not-ctx-app-ok)
          (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-7)
          (:definition alistp)
          (:definition remove-equal)
          (:rewrite abs-fs-p-correctness-1)))
    :induct (collapse-1st-index frame x)
    :expand (collapse-iter frame 1))))

(encapsulate
  ()

  (local
   (defthmd
     lemma
     (implies
      (and
       (mv-nth 1 (collapse frame))
       (consp (frame->frame frame))
       (consp
        (assoc-equal
         x
         (frame->frame
          (collapse-this frame
                         (1st-complete (frame->frame frame)))))))
      (equal
       (final-val
        x
        (collapse-this frame
                       (1st-complete (frame->frame frame))))
       (final-val x frame)))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory
       (e/d (final-val collapse collapse-iter
                       collapse-1st-index 1st-complete)
            (final-val-of-collapse-this-lemma-14
             (:rewrite nthcdr-when->=-n-len-l)
             (:definition no-duplicatesp-equal)
             (:rewrite partial-collapse-correctness-lemma-2)
             (:rewrite final-val-of-collapse-this-lemma-3)
             (:definition member-equal)
             (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
             (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8
                       . 2)))
       :use (:instance
             (:rewrite final-val-of-collapse-this-lemma-14)
             (x x)
             (n 1)
             (frame frame))))))

  (defthm
    final-val-of-collapse-this-1
    (implies
     (and
      (mv-nth 1 (collapse frame))
      (consp
       (assoc-equal
        x
        (frame->frame
         (collapse-this frame
                        (1st-complete (frame->frame frame)))))))
     (equal
      (final-val
       x
       (collapse-this frame
                      (1st-complete (frame->frame frame))))
      (final-val x frame)))
    :hints
    (("goal" :do-not-induct t
      :use (lemma final-val-of-collapse-this-lemma-1)))))

(defthm
  m1-file-alist-p-of-final-val
  (implies (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (frame-p (frame->frame frame))
                (mv-nth 1 (collapse frame)))
           (m1-file-alist-p (final-val x frame)))
  :hints
  (("goal"
    :in-theory
    (e/d
     (final-val)
     (collapse-1st-index-correctness-1 abs-separate-of-frame->frame-of-collapse-this-lemma-9))
    :use
    (collapse-1st-index-correctness-1
     (:instance
      abs-separate-of-frame->frame-of-collapse-this-lemma-9
      (frame (frame->frame (collapse-iter frame
                                          (collapse-1st-index frame x)))))))))

(defthm
  abs-fs-p-of-final-val
  (abs-fs-p (final-val x frame))
  :hints (("goal" :in-theory (enable final-val)))
  :rule-classes
  (:rewrite
   (:rewrite :corollary (equal (abs-fs-fix (final-val x frame))
                               (final-val x frame)))))

(defund
  final-val-seq (x frame seq)
  (frame-val->dir
   (cdr
    (assoc-equal
     x
     (frame->frame
      (collapse-seq frame (take (position x seq) seq)))))))

(defthm final-val-seq-of-take
  (implies (and (<= (nfix n) (len seq))
                (member-equal x (take n seq)))
           (equal (final-val-seq x frame (take n seq))
                  (final-val-seq x frame seq)))
  :hints (("goal" :in-theory (enable final-val-seq)
           :do-not-induct t
           :expand (:with take-fewer-of-take-more
                          (take (position-equal x seq)
                                (take n seq))))))

(defthm
  abs-fs-p-of-final-val-seq
  (abs-fs-p (final-val-seq x frame seq))
  :hints (("goal" :in-theory (enable final-val-seq)))
  :rule-classes
  (:rewrite
   (:rewrite :corollary (equal (abs-fs-fix (final-val-seq x frame seq))
                               (final-val-seq x frame seq)))))

(defthm m1-file-alist-p-of-final-val-seq-lemma-1
  (implies (and (consp (assoc-equal x (frame->frame frame)))
                (natp x))
           (not (zp x)))
  :rule-classes :forward-chaining)

(defthm
  m1-file-alist-p-of-final-val-seq-lemma-2
  (implies
   (not (consp (assoc-equal x (frame->frame frame))))
   (not (consp (assoc-equal x
                            (frame->frame (collapse-seq frame seq))))))
  :hints (("goal" :in-theory (enable collapse-seq)))
  :rule-classes (:rewrite :type-prescription))

;; Out of x, y and frame, at least one has to be a free variable...
(defthm m1-file-alist-p-of-final-val-seq-lemma-3
  (implies (and (consp (assoc-equal y (frame->frame frame)))
                (not (equal x y)))
           (consp (frame->frame (collapse-this frame x))))
  :hints (("goal" :in-theory (enable collapse-this))))

(defthm
  m1-file-alist-p-of-final-val-seq-lemma-4
  (implies
   (and
    (nat-listp seq)
    (not (equal (frame-val->src (cdr (assoc-equal (car seq)
                                                  (frame->frame frame))))
                (car seq)))
    (member-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                    (frame->frame frame))))
                  (cdr seq)))
   (<
    0
    (position-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                      (frame->frame frame))))
                    seq)))
  :rule-classes :linear
  :hints
  (("goal"
    :in-theory (disable (:type-prescription position-when-member)
                        (:rewrite position-of-nthcdr))
    :use
    ((:instance
      (:rewrite position-of-nthcdr)
      (lst seq)
      (n 1)
      (item (frame-val->src (cdr (assoc-equal (car seq)
                                              (frame->frame frame))))))
     (:instance
      (:type-prescription position-when-member)
      (lst (nthcdr 1 seq))
      (item (frame-val->src (cdr (assoc-equal (car seq)
                                              (frame->frame frame))))))))))

(defthm
  m1-file-alist-p-of-final-val-seq
  (implies (and (valid-seqp frame seq)
                (member-equal x seq)
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (nat-listp seq))
           (m1-file-alist-p (final-val-seq x frame seq)))
  :hints (("goal" :in-theory (enable final-val-seq
                                     valid-seqp collapse-seq))))

(defthm
  final-val-seq-of-collapse-this-lemma-1
  (implies
   (and (< 0
           (frame-val->src (cdr (assoc-equal (car seq)
                                             (frame->frame frame)))))
        (frame-p (frame->frame frame))
        (valid-seqp frame seq))
   (ctx-app-ok
    (frame-val->dir
     (cdr
      (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                     (frame->frame frame))))
                   (frame->frame frame))))
    (car seq)
    (nthcdr
     (len
      (frame-val->path
       (cdr
        (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                       (frame->frame frame))))
                     (frame->frame frame)))))
     (frame-val->path (cdr (assoc-equal (car seq)
                                        (frame->frame frame)))))))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq)
           :do-not-induct t)))

(defthm
  final-val-seq-of-collapse-this-lemma-2
  (implies
   (and (frame-p (frame->frame frame))
        (valid-seqp frame seq))
   (equal
    (abs-addrs (frame-val->dir (cdr (assoc-equal (car seq)
                                                 (frame->frame frame)))))
    nil))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq)
           :do-not-induct t)))

(defthm
  final-val-seq-of-collapse-this-lemma-3
  (implies
   (valid-seqp frame seq)
   (not (equal (frame-val->src (cdr (assoc-equal (car seq)
                                                 (frame->frame frame))))
               (car seq))))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq))))

(defthm
  final-val-seq-of-collapse-this-lemma-4
  (implies
   (and (equal (frame-val->src (cdr (assoc-equal (car seq)
                                                 (frame->frame frame))))
               0)
        (consp (assoc-equal (car seq)
                            (frame->frame frame)))
        (frame-p (frame->frame frame))
        (valid-seqp frame seq))
   (ctx-app-ok (frame->root frame)
               (car seq)
               (frame-val->path (cdr (assoc-equal (car seq)
                                                  (frame->frame frame))))))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq))))

(defthm
  final-val-seq-of-collapse-this-lemma-5
  (implies
   (and (valid-seqp frame seq)
        (member-equal x (cdr seq))
        (< 0
           (frame-val->src (cdr (assoc-equal (car seq)
                                             (frame->frame frame))))))
   (prefixp
    (frame-val->path
     (cdr
      (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                     (frame->frame frame))))
                   (frame->frame frame))))
    (frame-val->path (cdr (assoc-equal (car seq)
                                       (frame->frame frame))))))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq))))

(defthm
  final-val-seq-of-collapse-this-lemma-6
  (implies
   (and (consp seq)
        (not (consp (assoc-equal (car seq)
                                 (frame->frame frame)))))
   (not (valid-seqp frame seq)))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq)
           :do-not-induct t))
  :rule-classes :type-prescription)

(defthm final-val-seq-of-collapse-this-lemma-7
  (implies (and (consp seq) (zp (car seq)))
           (not (valid-seqp frame seq)))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq)))
  :rule-classes :type-prescription)

(defthm
  final-val-seq-of-collapse-this-lemma-8
  (implies
   (and (< 0
           (frame-val->src (cdr (assoc-equal (car seq)
                                             (frame->frame frame)))))
        (frame-p (frame->frame frame))
        (valid-seqp frame seq))
   (consp
    (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                   (frame->frame frame))))
                 (frame->frame frame))))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq)))
  :rule-classes :type-prescription)

(defthm
  final-val-seq-of-collapse-this-1
  (implies (and (valid-seqp frame seq)
                (frame-p (frame->frame frame))
                (not (equal x (car seq)))
                (member-equal x seq)
                (nat-listp seq))
           (equal (final-val-seq x (collapse-this frame (car seq))
                                 (cdr seq))
                  (final-val-seq x frame seq)))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (final-val-seq collapse-seq)
                           ((:rewrite position-of-nthcdr)
                            position-of-cdr position-when-member))
           :expand (take (position-equal x seq) seq)
           :use ((:instance position-when-member (lst seq)
                            (item x))
                 (:instance (:rewrite position-of-nthcdr)
                            (lst seq)
                            (n 1)
                            (item x))))))

(defund frame-addrs-before (frame x n)
  (if
      (zp n)
      nil
    (append
     (frame-addrs-before (collapse-iter frame 1) x (- n 1))
     (if
         (not
          (equal (frame-val->src
                  (cdr
                   (assoc-equal
                    (1st-complete (frame->frame frame))
                    (frame->frame frame))))
                 x))
         nil
       (list (1st-complete (frame->frame frame)))))))

(defthm nat-listp-of-frame-addrs-before
  (nat-listp (frame-addrs-before frame x n))
  :hints (("goal" :in-theory (enable frame-addrs-before))))

(defthm member-of-frame-addrs-before-lemma-2
  (implies (and (atom (assoc-equal y (frame->frame frame)))
                (not (zp y)))
           (not (member-equal y (frame-addrs-before frame x n))))
  :hints (("goal" :in-theory (enable frame-addrs-before)))
  :rule-classes (:rewrite :type-prescription))

(defthm
  member-of-frame-addrs-before
  (implies
   (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        ;; i was hoping not to have to put this in...
        (equal (len (frame->frame (collapse-iter frame n)))
               (- (len (frame->frame frame))
                  (nfix n))))
   (iff
    (member-equal y (frame-addrs-before frame x n))
    (and (< (collapse-1st-index frame y)
            (nfix n))
         (consp (assoc-equal y (frame->frame frame)))
         (equal (frame-val->src (cdr (assoc-equal y (frame->frame frame))))
                x))))
  :hints (("goal" :in-theory (enable collapse-1st-index
                                     frame-addrs-before collapse-iter)
           :induct t
           :expand (collapse-iter frame 1))))

(defthm
  no-duplicatesp-of-frame-addrs-before
  (implies (and (mv-nth 1 (collapse frame))
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (<= (nfix n)
                    (len (frame->frame frame))))
           (no-duplicatesp-equal (frame-addrs-before frame x n)))
  :hints (("goal" :in-theory (enable frame-addrs-before
                                     intersectp-equal collapse-1st-index))))

(defund frame-addrs-before-seq (frame x seq)
  (if
      (atom seq)
      nil
    (append
     (frame-addrs-before-seq frame x (nthcdr 1 seq))
     (if
         (not
          (equal (frame-val->src
                  (cdr
                   (assoc-equal
                    (nth 0 seq)
                    (frame->frame frame))))
                 x))
         nil
       (take 1 seq)))))

(defthm nat-listp-of-frame-addrs-before-seq
  (implies (and (nat-listp seq))
           (nat-listp (frame-addrs-before-seq frame x seq)))
  :hints (("goal" :in-theory (enable frame-addrs-before-seq))))

(defthm subsetp-of-frame-addrs-before-seq
  (subsetp-equal (frame-addrs-before-seq frame x seq)
                 seq)
  :hints (("goal" :in-theory (enable frame-addrs-before-seq)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (subsetp-equal seq y)
     (subsetp-equal (frame-addrs-before-seq frame x seq)
                    y)))
   (:rewrite
    :corollary
    (implies
     (not (member-equal y seq))
     (not (member-equal y (frame-addrs-before-seq frame x seq)))))))

(defthm frame-addrs-before-seq-of-append
  (equal (frame-addrs-before-seq frame x (append l1 l2))
         (append (frame-addrs-before-seq frame x l2)
                 (frame-addrs-before-seq frame x l1)))
  :hints (("goal" :in-theory (enable frame-addrs-before-seq))))

(defthm no-duplicatesp-of-frame-addrs-before-seq
  (implies (no-duplicatesp-equal seq)
           (no-duplicatesp-equal (frame-addrs-before-seq frame x seq)))
  :hints (("goal" :in-theory (enable frame-addrs-before-seq
                                     intersectp-equal))))

(defthm
  frame-addrs-before-seq-of-collapse-this
  (implies
   (and
    (not (zp x))
    (not (equal x
                (frame-val->src (cdr (assoc-equal y (frame->frame frame)))))))
   (equal (frame-addrs-before-seq (collapse-this frame y)
                                  x seq)
          (frame-addrs-before-seq frame x seq)))
  :hints
  (("goal" :in-theory (enable frame-addrs-before-seq)
    :induct (frame-addrs-before-seq frame x seq))))

(defthm member-of-frame-addrs-before-seq-lemma-1
  (implies (frame-p frame)
           (not (member-equal nil (strip-cars frame)))))

(defthm member-of-frame-addrs-before-seq-lemma-2
  (implies (and (consp (assoc-equal x (frame->frame frame)))
                (frame-p (frame->frame frame)))
           (natp x))
  :rule-classes :forward-chaining)

(defthm
  member-of-frame-addrs-before-seq
  (implies
   (and (subsetp-equal seq (strip-cars (frame->frame frame)))
        (frame-p (frame->frame frame)))
   (iff
    (member-equal y (frame-addrs-before-seq frame x seq))
    (and (member-equal y seq)
         (consp (assoc-equal y (frame->frame frame)))
         (equal (frame-val->src (cdr (assoc-equal y (frame->frame frame))))
                x))))
  :hints (("goal" :in-theory (enable frame-addrs-before-seq)
           :induct (frame-addrs-before-seq frame x seq)
           :expand (subsetp-equal seq
                                  (strip-cars (frame->frame frame))))))

(defund
  ctx-app-list (fs relpath frame l)
  (b*
      (((when (atom l)) (mv fs t))
       ((mv tail tail-result)
        (ctx-app-list fs relpath frame (cdr l)))
       (fs
        (ctx-app
         tail (final-val (car l) frame)
         (car l)
         (nthcdr (len relpath)
                 (frame-val->path
                  (cdr (assoc-equal (car l)
                                    (frame->frame frame))))))))
    (mv
     fs
     (and
      tail-result (abs-fs-p fs)
      (prefixp relpath
               (frame-val->path
                (cdr (assoc-equal (car l)
                                  (frame->frame frame)))))
      (ctx-app-ok
       tail (car l)
       (nthcdr
        (len relpath)
        (frame-val->path
         (cdr (assoc-equal (car l)
                           (frame->frame frame))))))))))

(defthmd ctx-app-list-of-true-list-fix
  (equal (ctx-app-list fs path-len frame (true-list-fix l))
         (ctx-app-list fs path-len frame l))
  :hints (("goal" :in-theory (enable ctx-app-list))))

(defcong
  list-equiv
  equal (ctx-app-list fs path-len frame l)
  4
  :hints (("goal" :use ((:instance ctx-app-list-of-true-list-fix
                                   (l l-equiv))
                        ctx-app-list-of-true-list-fix))))

(defthm booleanp-of-ctx-app-list
  (booleanp (mv-nth 1 (ctx-app-list fs path-len frame l)))
  :hints (("goal" :in-theory (enable ctx-app-list)))
  :rule-classes :type-prescription)

(defthmd abs-file-alist-p-of-ctx-app-list
  (implies
   (abs-file-alist-p fs)
   (abs-file-alist-p (mv-nth 0 (ctx-app-list fs path-len frame l))))
  :hints (("goal" :in-theory (enable ctx-app-list))))

(defthmd ctx-app-list-correctness-1
  (equal (ctx-app-list fs path-len frame y)
         (mv (mv-nth 0 (ctx-app-list fs path-len frame y))
             (mv-nth 1 (ctx-app-list fs path-len frame y))))
  :hints (("goal" :in-theory (enable ctx-app-list))))

(defthm
  ctx-app-list-of-append
  (equal (ctx-app-list fs path-len frame (append x y))
         (mv-let (y-fs y-result)
           (ctx-app-list fs path-len frame y)
           (mv (mv-nth 0 (ctx-app-list y-fs path-len frame x))
               (and y-result
                    (mv-nth 1
                            (ctx-app-list y-fs path-len frame x))))))
  :hints
  (("goal" :in-theory (e/d (ctx-app-list)
                           ((:rewrite nthcdr-when->=-n-len-l)
                            (:rewrite partial-collapse-correctness-lemma-2)
                            (:definition len)
                            (:definition nthcdr)
                            (:rewrite ctx-app-ok-when-abs-complete)
                            (:definition abs-complete)
                            (:rewrite abs-addrs-when-m1-file-alist-p)
                            (:linear position-when-member)
                            (:linear position-equal-ac-when-member)
                            (:rewrite list-equiv-when-true-listp)
                            (:rewrite ctx-app-ok-when-not-natp)
                            (:type-prescription assoc-equal-when-frame-p)
                            (:definition assoc-equal)
                            (:definition member-equal)
                            (:rewrite abs-file-alist-p-correctness-1)
                            (:rewrite true-listp-when-abs-file-alist-p)
                            (:rewrite ctx-app-when-not-natp)))
    :induct (append x y))
   ("subgoal *1/1" :use ctx-app-list-correctness-1)))

(defthm ctx-app-list-when-set-equiv-lemma-1
  (implies (and (not (member-equal (fat32-filename-fix (nth n relpath))
                                   (names-at fs (take n relpath))))
                (< (nfix n) (len relpath)))
           (equal (addrs-at fs relpath) nil))
  :hints (("goal" :in-theory (enable addrs-at names-at))))

(defthmd ctx-app-list-when-set-equiv-lemma-2
  (implies (and (< (nfix n) (len relpath))
                (not (member-equal (fat32-filename-fix (nth n relpath))
                                   (names-at fs (take n relpath)))))
           (equal (names-at fs relpath) nil))
  :hints (("goal" :in-theory (enable names-at))))

;; Bizarre.
(defthm ctx-app-list-when-set-equiv-lemma-4
  (implies (natp (- (len seq)))
           (not (member-equal x seq)))
  :rule-classes :type-prescription)

(encapsulate
  ()

  (local
   (in-theory
    (disable
     (:rewrite abs-file-alist-p-correctness-1)
     (:rewrite
      abs-file-alist-p-when-m1-file-alist-p)
     (:rewrite member-of-abs-fs-fix-when-natp)
     (:rewrite m1-file-alist-p-when-subsetp-equal)
     (:rewrite abs-fs-p-correctness-1)
     subsetp-member
     (:definition nthcdr)
     (:rewrite subsetp-trans2)
     (:rewrite subsetp-trans)
     (:type-prescription assoc-when-zp-len)
     (:definition nth)
     (:rewrite nat-listp-when-unsigned-byte-listp)
     (:linear nth-when-dir-ent-p)
     (:rewrite ctx-app-ok-when-abs-complete)
     (:rewrite fat32-filename-list-p-of-names-at))))

  (local
   (defthm lemma-1 (equal (+ x (- x) y) (fix y))))

  (defthm
    ctx-app-list-when-set-equiv-lemma-5
    (implies
     (and
      (not
       (equal
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal (car l)
                                                   (frame->frame frame)))))
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
      (prefixp (frame-val->path (cdr (assoc-equal (car l)
                                                  (frame->frame frame))))
               (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
      (not
       (member-equal
        (nth (len (frame-val->path (cdr (assoc-equal (car l)
                                                     (frame->frame frame)))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
        (names-at
         (mv-nth 0
                 (ctx-app-list fs
                               relpath frame (remove-equal x (cdr l))))
         (nthcdr (len relpath)
                 (frame-val->path (cdr (assoc-equal (car l)
                                                    (frame->frame frame))))))))
      (prefixp relpath
               (frame-val->path (cdr (assoc-equal (car l)
                                                  (frame->frame frame))))))
     (equal
      (names-at
       (mv-nth 0
               (ctx-app-list fs
                             relpath frame (remove-equal x (cdr l))))
       (nthcdr (len relpath)
               (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
      nil))
    :hints
    (("goal"
      :in-theory (e/d (take-of-nthcdr))
      :use
      (:instance
       (:rewrite ctx-app-list-when-set-equiv-lemma-2)
       (relpath
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
       (fs (mv-nth 0
                   (ctx-app-list fs relpath
                                 frame (remove-equal x (cdr l)))))
       (n (- (len (frame-val->path (cdr (assoc-equal (car l)
                                                     (frame->frame frame)))))
             (len relpath))))
      :expand
      ((:with
        (:rewrite fat32-filename-p-of-nth-when-fat32-filename-list-p)
        (fat32-filename-p
         (nth (len (frame-val->path (cdr (assoc-equal (car l)
                                                      (frame->frame frame)))))
              (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
       (:with
        fat32-filename-fix-when-fat32-filename-p
        (fat32-filename-fix
         (nth
          (len (frame-val->path (cdr (assoc-equal (car l)
                                                  (frame->frame frame)))))
          (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))))))

  (defthm
    ctx-app-list-when-set-equiv-lemma-6
    (implies
     (and
      (consp l)
      (absfat-equiv
       (ctx-app
        (mv-nth 0
                (ctx-app-list fs
                              relpath frame (remove-equal x (cdr l))))
        (final-val x frame)
        x
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
       (mv-nth 0
               (ctx-app-list fs relpath frame (cdr l))))
      (nat-listp l)
      (ctx-app-ok
       (mv-nth 0
               (ctx-app-list fs
                             relpath frame (remove-equal x (cdr l))))
       (car l)
       (nthcdr (len relpath)
               (frame-val->path (cdr (assoc-equal (car l)
                                                  (frame->frame frame))))))
      (prefixp relpath
               (frame-val->path (cdr (assoc-equal (car l)
                                                  (frame->frame frame)))))
      (no-duplicatesp-equal (strip-cars (frame->frame frame)))
      (frame-p (frame->frame frame))
      (mv-nth 1 (collapse frame))
      (not
       (equal
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal (car l)
                                                   (frame->frame frame)))))
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
      (prefixp (frame-val->path (cdr (assoc-equal (car l)
                                                  (frame->frame frame))))
               (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
      (not
       (member-equal
        (nth (len (frame-val->path (cdr (assoc-equal (car l)
                                                     (frame->frame frame)))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
        (names-at
         (mv-nth 0
                 (ctx-app-list fs
                               relpath frame (remove-equal x (cdr l))))
         (nthcdr (len relpath)
                 (frame-val->path (cdr (assoc-equal (car l)
                                                    (frame->frame frame)))))))))
     (ctx-app-ok
      (mv-nth 0
              (ctx-app-list fs relpath frame (cdr l)))
      (car l)
      (nthcdr (len relpath)
              (frame-val->path (cdr (assoc-equal (car l)
                                                 (frame->frame frame)))))))
    :hints
    (("goal"
      :in-theory (e/d (intersectp-equal)
                      ((:rewrite ctx-app-ok-of-ctx-app-1)))
      :use
      (:instance
       (:rewrite ctx-app-ok-of-ctx-app-1)
       (x2-path
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal (car l)
                                                   (frame->frame frame))))))
       (x2 (car l))
       (x3-path
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
       (x3 x)
       (abs-file-alist3 (final-val x frame))
       (abs-file-alist1
        (mv-nth 0
                (ctx-app-list fs relpath
                              frame (remove-equal x (cdr l)))))))))

  (local
   (defthmd
     lemma-2
     (implies
      (and (not (member-equal (fat32-filename-fix (nth n x-path))
                              (names-at abs-file-alist1 (take n x-path))))
           (< (nfix n) (len x-path)))
      (equal (ctx-app-ok abs-file-alist1 x x-path)
             nil))
     :hints (("goal" :do-not-induct t
              :in-theory (enable ctx-app-ok)))))

  (defthm
    ctx-app-list-when-set-equiv-lemma-7
    (implies
     (and
      (not
       (equal
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal (car l)
                                                   (frame->frame frame)))))
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
      (prefixp (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
               (frame-val->path (cdr (assoc-equal (car l)
                                                  (frame->frame frame)))))
      (<=
       0
       (+ (- (len relpath))
          (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
      (not
       (member-equal
        (nth (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
             (frame-val->path (cdr (assoc-equal (car l)
                                                (frame->frame frame)))))
        (names-at
         (mv-nth 0
                 (ctx-app-list fs
                               relpath frame (remove-equal x (cdr l))))
         (nthcdr
          (len relpath)
          (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))))
     (not
      (ctx-app-ok
       (mv-nth 0
               (ctx-app-list fs
                             relpath frame (remove-equal x (cdr l))))
       (car l)
       (nthcdr (len relpath)
               (frame-val->path (cdr (assoc-equal (car l)
                                                  (frame->frame frame))))))))
    :hints
    (("goal"
      :in-theory (e/d (take-of-nthcdr)
                      ())
      :use
      (:instance
       (:rewrite lemma-2)
       (x-path
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal (car l)
                                                   (frame->frame frame))))))
       (x (car l))
       (abs-file-alist1 (mv-nth 0
                                (ctx-app-list fs relpath
                                              frame (remove-equal x (cdr l)))))
       (n (- (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
             (len relpath))))
      :expand
      ((:with
        (:rewrite fat32-filename-p-of-nth-when-fat32-filename-list-p)
        (fat32-filename-p
         (nth (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
              (frame-val->path (cdr (assoc-equal (car l)
                                                 (frame->frame frame)))))))
       (:with
        fat32-filename-fix-when-fat32-filename-p
        (fat32-filename-fix
         (nth (len (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
              (frame-val->path (cdr (assoc-equal (car l)
                                                 (frame->frame frame)))))))))))

  (defthm
    ctx-app-list-when-set-equiv-lemma-8
    (implies
     (and
      (absfat-equiv
       (ctx-app
        (mv-nth 0
                (ctx-app-list fs
                              relpath frame (remove-equal x (cdr l))))
        (final-val x frame)
        x
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
       (mv-nth 0
               (ctx-app-list fs relpath frame (cdr l))))
      (ctx-app-ok
       (mv-nth 0
               (ctx-app-list fs
                             relpath frame (remove-equal x (cdr l))))
       (car l)
       (nthcdr (len relpath)
               (frame-val->path (cdr (assoc-equal (car l)
                                                  (frame->frame frame))))))
      (not
       (intersectp-equal
        (names-at (final-val (car l) frame) nil)
        (names-at
         (mv-nth 0
                 (ctx-app-list fs
                               relpath frame (remove-equal x (cdr l))))
         (nthcdr (len relpath)
                 (frame-val->path (cdr (assoc-equal (car l)
                                                    (frame->frame frame))))))))
      (prefixp relpath
               (frame-val->path (cdr (assoc-equal (car l)
                                                  (frame->frame frame)))))
      (not
       (equal
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal (car l)
                                                   (frame->frame frame)))))
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
      (not
       (intersectp-equal
        (names-at (final-val x frame) nil)
        (names-at
         (mv-nth 0
                 (ctx-app-list fs
                               relpath frame (remove-equal x (cdr l))))
         (nthcdr
          (len relpath)
          (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))))
      (prefixp relpath
               (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
     (not
      (intersectp-equal
       (names-at (final-val (car l) frame) nil)
       (names-at
        (mv-nth 0
                (ctx-app-list fs relpath frame (cdr l)))
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal (car l)
                                                   (frame->frame frame)))))))))
    :hints
    (("goal"
      :in-theory (disable (:rewrite names-at-of-ctx-app))
      :use
      (:instance
       (:rewrite names-at-of-ctx-app)
       (relpath
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal (car l)
                                                   (frame->frame frame))))))
       (x-path
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
       (x x)
       (abs-file-alist (final-val x frame))
       (root (mv-nth 0
                     (ctx-app-list fs relpath
                                   frame (remove-equal x (cdr l)))))))))

  (defthm
    ctx-app-list-when-set-equiv-lemma-9
    (implies
     (and
      (mv-nth 1
              (ctx-app-list fs relpath frame (remove-equal x l)))
      (member-equal x l)
      (nat-listp l)
      (no-duplicatesp-equal (strip-cars (frame->frame frame)))
      (no-duplicatesp-equal l)
      (frame-p (frame->frame frame))
      (mv-nth 1 (collapse frame))
      (ctx-app-ok
       (mv-nth 0
               (ctx-app-list fs relpath frame (remove-equal x l)))
       x
       (nthcdr (len relpath)
               (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
      (not
       (intersectp-equal
        (names-at (final-val x frame) nil)
        (names-at
         (mv-nth 0
                 (ctx-app-list fs relpath frame (remove-equal x l)))
         (nthcdr
          (len relpath)
          (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))))
      (prefixp relpath
               (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
     (and
      (absfat-equiv
       (ctx-app
        (mv-nth 0
                (ctx-app-list fs relpath frame (remove-equal x l)))
        (final-val x frame)
        x
        (nthcdr (len relpath)
                (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
       (mv-nth 0 (ctx-app-list fs relpath frame l)))
      (mv-nth 1 (ctx-app-list fs relpath frame l))
      (not
       (intersectp-equal
        (names-at (final-val x frame) nil)
        (names-at
         (mv-nth 0
                 (ctx-app-list fs relpath frame (remove-equal x l)))
         (nthcdr
          (len relpath)
          (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))))))
    :hints
    (("goal" :in-theory (e/d (ctx-app-list intersectp-equal)
                             ((:rewrite nthcdr-when->=-n-len-l)
                              (:rewrite partial-collapse-correctness-lemma-2)
                              (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8 . 3)
                              (:definition len)
                              (:rewrite
                               ctx-app-ok-when-absfat-equiv-lemma-4)
                              (:rewrite prefixp-one-way-or-another . 1)
                              (:definition assoc-equal)
                              (:rewrite
                               nat-listp-if-fat32-masked-entry-list-p)
                              (:linear position-when-member)
                              (:linear position-equal-ac-when-member)
                              (:rewrite
                               ctx-app-list-when-set-equiv-lemma-7)))))))

(encapsulate
  ()

  (local
   (defun
       induction-scheme (l1 l2)
     (cond
      ((and (not (atom l1)))
       (induction-scheme (cdr l1) (remove-equal (car l1) l2)))
      (t (mv l1 l2)))))

  (local (in-theory (enable ctx-app-list)))

  (defthmd
    ctx-app-list-when-set-equiv
    (implies (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                  (no-duplicatesp-equal l1)
                  (no-duplicatesp-equal l2)
                  (set-equiv l1 l2)
                  (nat-listp l2)
                  (frame-p (frame->frame frame))
                  (mv-nth '1 (collapse frame))
                  (mv-nth 1 (ctx-app-list fs relpath frame l1)))
             (and (absfat-equiv (mv-nth 0 (ctx-app-list fs relpath frame l1))
                                (mv-nth 0 (ctx-app-list fs relpath frame l2)))
                  (mv-nth 1 (ctx-app-list fs relpath frame l2))))
    :hints
    (("goal" :induct (induction-scheme l1 l2))
     ("subgoal *1/1.1"
      :in-theory (disable (:rewrite ctx-app-list-when-set-equiv-lemma-9))
      :use (:instance (:rewrite ctx-app-list-when-set-equiv-lemma-9)
                      (l l2)
                      (x (car l1))
                      (frame frame)
                      (relpath relpath)
                      (fs fs))))))

(defund
  ctx-app-list-seq (fs relpath frame l seq)
  (b*
      (((when (atom l)) (mv fs t))
       ((mv tail tail-result)
        (ctx-app-list-seq fs relpath frame (cdr l) seq))
       (fs
        (ctx-app
         tail (final-val-seq (car l) frame seq)
         (car l)
         (nthcdr (len relpath)
                 (frame-val->path
                  (cdr (assoc-equal (car l)
                                    (frame->frame frame))))))))
    (mv
     fs
     (and
      tail-result (abs-fs-p fs)
      (prefixp relpath
               (frame-val->path
                (cdr (assoc-equal (car l)
                                  (frame->frame frame)))))
      (ctx-app-ok
       tail (car l)
       (nthcdr
        (len relpath)
        (frame-val->path
         (cdr (assoc-equal (car l)
                           (frame->frame frame))))))))))

(defthm booleanp-of-ctx-app-list-seq
  (booleanp (mv-nth 1
                    (ctx-app-list-seq fs relpath frame l seq)))
  :hints (("goal" :in-theory (enable ctx-app-list-seq)))
  :rule-classes :type-prescription)

(defthmd ctx-app-list-seq-correctness-1
  (equal (ctx-app-list-seq fs relpath frame y seq)
         (mv (mv-nth 0
                     (ctx-app-list-seq fs relpath frame y seq))
             (mv-nth 1
                     (ctx-app-list-seq fs relpath frame y seq))))
  :hints (("goal" :in-theory (enable ctx-app-list-seq))))

(defthm
  ctx-app-list-seq-of-append
  (equal (ctx-app-list-seq fs relpath frame (append x y)
                           seq)
         (b* (((mv y-fs y-result)
               (ctx-app-list-seq fs relpath frame y seq)))
           (mv (mv-nth 0
                       (ctx-app-list-seq y-fs relpath frame x seq))
               (and y-result
                    (mv-nth 1
                            (ctx-app-list-seq y-fs relpath frame x seq))))))
  :hints
  (("goal" :in-theory (e/d (ctx-app-list-seq)
                           ((:rewrite nthcdr-when->=-n-len-l)
                            (:rewrite partial-collapse-correctness-lemma-2)
                            (:definition len)
                            (:definition nthcdr)
                            (:rewrite ctx-app-ok-when-abs-complete)
                            (:definition abs-complete)
                            (:definition member-equal)
                            (:linear position-when-member)
                            (:linear position-equal-ac-when-member)
                            (:rewrite list-equiv-when-true-listp)
                            (:rewrite ctx-app-ok-when-not-natp)
                            (:definition assoc-equal)
                            (:rewrite abs-file-alist-p-correctness-1)
                            (:rewrite true-listp-when-abs-file-alist-p)
                            (:rewrite ctx-app-when-not-natp)))
    :induct (append x y))
   ("subgoal *1/1''" :use ctx-app-list-seq-correctness-1)))

(defthm
  abs-fs-p-of-ctx-app-list-seq
  (implies (and (abs-fs-p fs)
                (mv-nth 1
                        (ctx-app-list-seq fs relpath frame l seq)))
           (abs-fs-p (mv-nth 0
                             (ctx-app-list-seq fs relpath frame l seq))))
  :hints
  (("goal" :in-theory (e/d (ctx-app-list-seq set-difference$-redefinition)
                           (set-difference-equal))
    :induct (ctx-app-list-seq fs relpath frame l seq))))

(defthmd
  abs-addrs-of-ctx-app-list-seq
  (implies
   (and (abs-fs-p fs)
        (no-duplicatesp-equal (abs-addrs fs))
        (mv-nth 1
                (ctx-app-list-seq fs relpath frame l seq))
        (nat-listp l)
        (nat-listp seq)
        (valid-seqp frame seq)
        (subsetp-equal l seq)
        (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (and
    (equal (abs-addrs (mv-nth 0
                              (ctx-app-list-seq fs relpath frame l seq)))
           (set-difference-equal (abs-addrs fs)
                                 l))
    (subsetp-equal l (abs-addrs fs))))
  :hints
  (("goal" :in-theory (e/d (ctx-app-list-seq set-difference$-redefinition subsetp-equal
                                             ABS-ADDRS-OF-CTX-APP-1-LEMMA-7)
                           (set-difference-equal))
    :induct (ctx-app-list-seq fs relpath frame l seq))))

;; This could potentially get really expensive if it's a rewrite rule..
(defthm
  ctx-app-ok-of-ctx-app-list-seq-lemma-1
  (implies (and (valid-seqp frame seq)
                (no-duplicatesp-equal (strip-cars (frame->frame frame))))
           (and (subsetp-equal seq (strip-cars (frame->frame frame)))
                (no-duplicatesp-equal seq)
                (not (member-equal (car seq) (cdr seq)))))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq)
           :induct (collapse-seq frame seq)))
  :rule-classes
  (:forward-chaining
   (:rewrite
    :corollary
    (implies (and (valid-seqp frame seq)
                  (no-duplicatesp-equal (strip-cars (frame->frame frame))))
             (subsetp-equal seq
                            (strip-cars (frame->frame frame)))))))

(defthm
  ctx-app-ok-of-ctx-app-list-seq
  (implies (and (not (member-equal x l))
                (mv-nth 1
                        (ctx-app-list-seq fs relpath frame l seq))
                (nat-listp l)
                (nat-listp seq)
                (valid-seqp frame seq)
                (subsetp-equal l seq)
                (no-duplicatesp-equal (strip-cars (frame->frame frame))))
           (iff (ctx-app-ok (mv-nth 0
                                    (ctx-app-list-seq fs relpath frame l seq))
                            x x-path)
                (ctx-app-ok fs x x-path)))
  :hints (("goal" :in-theory (enable ctx-app-list-seq)
           :induct (ctx-app-list-seq fs relpath frame l seq))))

(defund
  seq-this
  (frame)
  (declare
   (xargs :measure (len (frame->frame frame))
          :verify-guards nil))
  (b*
      (((when (atom (frame->frame frame))) nil)
       (next-frame (collapse-iter frame 1))
       ((unless (< (len (frame->frame next-frame)) (len (frame->frame frame))))
        nil))
    (cons (1st-complete (frame->frame frame))
          (seq-this
           next-frame))))

;; While it would be nice to see this have no hypothesis, the way
;; collapse-iter-is-collapse has no hypotheses, the fact is that it won't work
;; because of the stupid truth that a frame with duplicate variables in it will
;; be accepted by collapse but not by collapse-seq.
(defthmd
  collapse-seq-of-seq-this-is-collapse
  (implies (no-duplicatesp-equal (strip-cars (frame->frame frame)))
           (equal (collapse frame)
                  (mv (frame->root (collapse-seq frame (seq-this frame)))
                      (equal (len (seq-this frame))
                             (len (frame->frame frame))))))
  :hints
  (("goal" :in-theory (e/d (collapse collapse-seq seq-this collapse-iter)
                           ((:definition assoc-equal)
                            (:rewrite nthcdr-when->=-n-len-l)
                            (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8 . 3)
                            (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8 . 2)
                            (:definition remove-equal)
                            (:rewrite remove-when-absent)))
    :induct (seq-this frame)
    :expand ((collapse frame)
             (collapse-iter frame 1)))))

(defthm nat-listp-of-seq-this
  (nat-listp (seq-this frame))
  :hints (("goal" :in-theory (enable seq-this))))

(defthm
  natp-of-nth-of-seq-this
  (implies (< (nfix n) (len (seq-this frame)))
           (natp (nth n (seq-this frame))))
  :hints (("goal" :in-theory (disable member-of-a-nat-list)
           :use (:instance member-of-a-nat-list
                           (x (nth n (seq-this frame)))
                           (lst (seq-this frame)))))
  :rule-classes
  (:type-prescription
   (:rewrite :corollary (implies (< (nfix n) (len (seq-this frame)))
                                 (integerp (nth n (seq-this frame)))))
   (:linear :corollary (implies (< (nfix n) (len (seq-this frame)))
                                (<= 0 (nth n (seq-this frame)))))))

(defthm no-duplicatesp-of-seq-this-lemma-1
  (subsetp-equal (seq-this frame)
                 (strip-cars (frame->frame frame)))
  :hints (("goal" :in-theory (enable seq-this collapse-iter)
           :induct (seq-this frame)
           :expand (collapse-iter frame 1)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (not (member-equal x
                        (strip-cars (frame->frame frame))))
     (not (member-equal x (seq-this frame)))))
   (:rewrite
    :corollary
    (implies
     (subsetp-equal x (seq-this frame))
     (subsetp-equal x (strip-cars (frame->frame frame)))))
   (:rewrite
    :corollary
    (implies
     (subsetp-equal (strip-cars (frame->frame frame)) y)
     (subsetp-equal (seq-this frame) y)))))

(defthm no-duplicatesp-of-seq-this
  (no-duplicatesp-equal (seq-this frame))
  :hints (("goal" :in-theory (enable seq-this)
           :induct (seq-this frame)
           :expand (collapse-iter frame 1))))

;; Enabling this theorem suddenly brings a lot of things to a halt, lol.
(defthmd
  nth-of-seq-this
  (implies
   (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (< (nfix n) (len (seq-this frame))))
   (equal
    (nth n (seq-this frame))
    (1st-complete
     (frame->frame (collapse-seq frame (take n (seq-this frame)))))))
  :hints
  (("goal" :in-theory (e/d (seq-this collapse-iter collapse-seq)
                           ((:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
                            (:definition member-equal)
                            (:definition no-duplicatesp-equal)
                            (:definition remove-equal)
                            (:definition nthcdr)
                            (:definition assoc-equal)
                            (:rewrite nthcdr-when->=-n-len-l)))
    :induct (collapse-iter frame n)
    :expand (seq-this frame))))

(defthm member-of-seq-this-when-zp
  (implies (zp x)
           (not (member-equal x (seq-this frame))))
  :hints (("goal" :in-theory (enable seq-this collapse-iter)))
  :rule-classes :type-prescription)

(defthm
  nth-of-seq-this-1
  (implies (< (nfix n) (len (seq-this frame)))
           (not (zp (nth n (seq-this frame)))))
  :hints (("goal" :do-not-induct t
           :in-theory (disable (:rewrite member-equal-nth))
           :use (:instance (:rewrite member-equal-nth)
                           (l (seq-this frame)))))
  :rule-classes
  (:type-prescription
   (:linear :corollary (implies (< (nfix n) (len (seq-this frame)))
                                (< 0 (nth n (seq-this frame)))))
   (:rewrite :corollary (implies (< (nfix n) (len (seq-this frame)))
                                 (integerp (nth n (seq-this frame)))))))

(defthm len-of-seq-this-1
  (<= (len (seq-this frame))
      (len (frame->frame frame)))
  :hints (("goal" :in-theory (enable seq-this)))
  :rule-classes :linear)

(defthmd
  partial-collapse-correctness-lemma-6
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
  partial-collapse-correctness-lemma-5
  (implies
   (and
    (absfat-subsetp
     (ctx-app
      (ctx-app
       (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                             x)))
       y y-var (cdr y-path))
      z z-var (cdr y-path))
     (ctx-app
      (ctx-app
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
      (ctx-app
       (ctx-app (abs-file->contents
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
      (ctx-app
       (ctx-app (abs-file->contents
                 (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                   x)))
                z z-var (cdr y-path))
       y y-var (cdr y-path)))
     x)))
  :hints
  (("goal"
    :in-theory (e/d (ctx-app ctx-app-ok)
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
         (ctx-app
          (ctx-app
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
        (ctx-app
         (ctx-app
          (abs-file->contents
           (cdr (assoc-equal (fat32-filename-fix (car y-path))
                             x)))
          y y-var (cdr y-path))
         z z-var (cdr y-path))))
      (name (fat32-filename-fix (car y-path))))))))

(defthm
  partial-collapse-correctness-lemma-9
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
     (ctx-app (abs-file->contents$inline
               (cdr (assoc-equal (fat32-filename-fix (car z-path))
                                 x)))
              z z-var (cdr z-path))))))

(defthm
  partial-collapse-correctness-lemma-3
  (implies
   (and
    (absfat-subsetp
     (ctx-app
      (ctx-app
       (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                             x)))
       z z-var (cdr z-path))
      y y-var (cdr y-path))
     (ctx-app
      (ctx-app
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
     (ctx-app
      (ctx-app (abs-file->contents$inline
                (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                  x)))
               z z-var (cdr z-path))
      y y-var (cdr y-path)))
    (abs-file-contents-fix
     (ctx-app
      (ctx-app (abs-file->contents$inline
                (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                  x)))
               y y-var (cdr y-path))
      z z-var (cdr z-path))))))

(defthm
  partial-collapse-correctness-lemma-4
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
     (ctx-app (abs-file->contents$inline
               (cdr (assoc-equal (fat32-filename-fix (car z-path))
                                 x)))
              z z-var (cdr y-path)))
    (abs-file-contents-fix
     (ctx-app (abs-file->contents$inline
               (cdr (assoc-equal (fat32-filename-fix (car z-path))
                                 x)))
              z z-var (cdr y-path))))))

(defthm
  partial-collapse-correctness-lemma-10
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
  partial-collapse-correctness-lemma-12
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
  partial-collapse-correctness-lemma-15
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
  partial-collapse-correctness-lemma-14
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
     (ctx-app
      (ctx-app
       (abs-file->contents (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                             x)))
       y y-var (cdr y-path))
      z z-var (cdr z-path))
     (ctx-app
      (ctx-app
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
     (ctx-app
      (ctx-app (abs-file->contents$inline
                (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                  x)))
               y y-var (cdr y-path))
      z z-var (cdr z-path)))
    (abs-file-contents-fix
     (ctx-app
      (ctx-app (abs-file->contents$inline
                (cdr (assoc-equal (fat32-filename-fix (car y-path))
                                  x)))
               z z-var (cdr z-path))
      y y-var (cdr y-path))))))

(defthm
  partial-collapse-correctness-lemma-19
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
  (("goal" :in-theory (disable abs-separate-of-frame->frame-of-collapse-this-lemma-3)
    :use (:instance abs-separate-of-frame->frame-of-collapse-this-lemma-3
                    (y (1st-complete (frame->frame frame)))
                    (frame (frame->frame frame))
                    (x x)))))

(defthm
  partial-collapse-correctness-lemma-20
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

;; (defthm
;;   partial-collapse-correctness-lemma-21
;;   (implies
;;    (and
;;     (prefixp
;;      (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
;;      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
;;                                         (frame->frame frame)))))
;;     (not
;;      (equal
;;       (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
;;                                          (frame->frame frame))))
;;       (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
;;    (not
;;     (prefixp
;;      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
;;                                         (frame->frame frame))))
;;      (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
;;   :hints
;;   (("goal"
;;     :in-theory (e/d (list-equiv)
;;                     ((:rewrite prefixp-when-equal-lengths)))
;;     :use
;;     (:instance
;;      (:rewrite prefixp-when-equal-lengths)
;;      (y (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
;;      (x (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
;;                                            (frame->frame frame)))))))))

(defthm
  partial-collapse-correctness-lemma-24
  (implies
   (and
    (not (and (consp (assoc-equal x frame))
              (abs-complete (frame-val->dir (cdr (assoc-equal x frame))))))
    (no-duplicatesp-equal (strip-cars frame))
    (frame-p frame)
    (< 0 x))
   (not (equal (1st-complete frame) x)))
  :hints (("goal" :in-theory (enable 1st-complete))))

;; This theorem is used in an :expand hint later...
(defthmd
  partial-collapse-correctness-lemma-22
  (implies
   (and
    (not (equal x (1st-complete (frame->frame frame))))
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
     (ctx-app
      (ctx-app
       (frame->root frame)
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
       x
       (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
      (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                        (frame->frame frame))))
      (1st-complete (frame->frame frame))
      (frame-val->path (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))))
   (equal
    (mv-nth
     1
     (collapse
      (frame-with-root
       (ctx-app
        (ctx-app
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
     1
     (collapse
      (frame-with-root
       (ctx-app
        (ctx-app
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
                            (frame->frame frame))))))))
  :hints
  (("goal"
    :do-not-induct t
    :use
    ((:instance
      (:rewrite collapse-congruence-lemma-3)
      (frame2
       (frame-with-root
        (ctx-app
         (ctx-app
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
        (ctx-app
         (ctx-app
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
                             (frame->frame frame))))))))))

;; The one hypothesis needs to cause a case-split some of the time - but does
;; it, all of the time?
(defthmd
  partial-collapse-correctness-lemma-23
  (implies
   (and
    (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
           0)
    (not (zp x))
    (not (equal x (1st-complete (frame->frame frame)))))
   (equal
    (1st-complete (frame->frame (collapse-this frame x)))
    (1st-complete (frame->frame frame))))
  :hints (("goal" :in-theory (enable collapse-this))))

(defthm
  partial-collapse-correctness-lemma-13
  (implies
   (and
    (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
           0)
    (< 0
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
    (not
     (consp
      (abs-addrs
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
    (ctx-app-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
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
                                         (frame->frame frame)))))))
   (equal
    (mv-nth 1
            (collapse (collapse-this (collapse-this frame x)
                                     (1st-complete (frame->frame frame)))))
    (mv-nth
     1
     (collapse
      (collapse-this (collapse-this frame
                                    (1st-complete (frame->frame frame)))
                     x)))))
  :hints (("goal" :in-theory (enable collapse-this abs-addrs-of-ctx-app-1-lemma-7))))

(defthm
  partial-collapse-correctness-lemma-26
  (implies
   (and
    (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
           0)
    (< 0
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
    (not
     (consp
      (abs-addrs
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
    (ctx-app-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
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
                                         (frame->frame frame)))))))
   (absfat-equiv
    (mv-nth 0
            (collapse (collapse-this (collapse-this frame x)
                                     (1st-complete (frame->frame frame)))))
    (mv-nth
     0
     (collapse
      (collapse-this (collapse-this frame
                                    (1st-complete (frame->frame frame)))
                     x)))))
  :hints (("goal" :in-theory (enable collapse-this abs-addrs-of-ctx-app-1-lemma-7))))


(defthmd
  partial-collapse-correctness-lemma-27
  (implies
   (and (no-duplicatesp-equal (strip-cars frame))
        (not (zp (1st-complete (remove-assoc-equal x frame)))))
   (and
    (consp (assoc-equal (1st-complete (remove-assoc-equal x frame))
                        frame))
    (equal
     (abs-addrs
      (frame-val->dir
       (cdr (assoc-equal (1st-complete (remove-assoc-equal x frame))
                         frame))))
     nil)))
  :hints (("goal" :in-theory (e/d (1st-complete)
                                  (1st-complete-correctness-1)))
          ("subgoal *1/2"
           :use (:instance (:type-prescription 1st-complete-correctness-1)
                           (frame (remove-assoc-equal x (cdr frame)))))))

(defthmd
  partial-collapse-correctness-lemma-32
  (implies
   (and (atom (assoc-equal 0 frame))
        (frame-p frame)
        (zp (1st-complete frame))
        (consp (assoc-equal x frame)))
   (consp
    (abs-addrs (frame-val->dir (cdr (assoc-equal x frame))))))
  :hints (("goal" :in-theory (enable 1st-complete))))

(defthm
  partial-collapse-correctness-lemma-28
  (implies
   (and
    (ctx-app-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
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
    (e/d (collapse abs-separate abs-addrs-of-ctx-app-1-lemma-7)
         ((:definition remove-assoc-equal)
          (:rewrite remove-assoc-when-absent-1)
          (:definition member-equal)
          (:definition len))))))

;; This is important.
(defthm
  partial-collapse-correctness-lemma-1
  (implies
   (and (abs-separate (frame->frame frame))
        (mv-nth 1 (collapse frame))
        (consp (assoc-equal x (frame->frame frame)))
        (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
        (frame-p (frame->frame frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (dist-names (frame->root frame)
                    nil (frame->frame frame)))
   (ctx-app-ok (frame->root frame)
               x
               (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
  :hints
  (("goal"
    :in-theory
    (e/d (collapse collapse-this)
         ((:rewrite remove-assoc-of-put-assoc)
          (:rewrite partial-collapse-correctness-lemma-24)
          (:definition remove-assoc-equal)
          (:rewrite remove-assoc-of-remove-assoc)
          (:rewrite abs-file-alist-p-when-m1-file-alist-p)
          (:rewrite put-assoc-equal-without-change . 2)
          (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
          (:type-prescription abs-fs-fix-of-put-assoc-equal-lemma-3)))
    :induct (collapse frame)
    :expand
    (:with
     ctx-app-ok-of-ctx-app-1
     (ctx-app-ok
      (ctx-app
       (frame->root frame)
       (frame-val->dir$inline
        (cdr (assoc-equal (1st-complete (frame->frame frame))
                          (frame->frame frame))))
       (1st-complete (frame->frame frame))
       (frame-val->path$inline
        (cdr (assoc-equal (1st-complete (frame->frame frame))
                          (frame->frame frame)))))
      x
      (frame-val->path$inline (cdr (assoc-equal x (frame->frame frame))))))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (abs-separate (frame->frame frame))
          (mv-nth 1 (collapse frame))
          (consp (assoc-equal x (frame->frame frame)))
          (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
          (frame-p (frame->frame frame))
          (no-duplicatesp-equal (strip-cars (frame->frame frame)))
          (dist-names (frame->root frame)
                      nil (frame->frame frame))
          (fat32-filename-list-equiv
           relpath
           (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
     (ctx-app-ok (frame->root frame)
                 x relpath)))))

(defthm
  partial-collapse-correctness-lemma-30
  (implies
   (and
    (syntaxp (variablep x))
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
   (equal
    (mv-nth
     1
     (collapse
      (frame-with-root
       (ctx-app
        (ctx-app
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
     1
     (collapse
      (frame-with-root
       (ctx-app
        (ctx-app
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
                            (frame->frame frame))))))))
  :hints
  (("goal"
    :in-theory (e/d (collapse-this collapse)
                    ((:definition member-equal)
                     (:definition assoc-equal)
                     (:definition remove-equal)
                     (:definition remove-assoc-equal)
                     (:definition no-duplicatesp-equal)
                     (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
                     (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8
                               . 2)
                     (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-7)
                     (:rewrite strip-cars-of-put-assoc)
                     (:rewrite partial-collapse-correctness-lemma-2)
                     intersect-with-subset))
    :use partial-collapse-correctness-lemma-22)))

(defthm
  partial-collapse-correctness-lemma-29
  (implies
   (and
    (syntaxp (variablep x))
    (equal
     (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame))))
     0)
    (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
           0)
    (absfat-equiv
     (mv-nth
      0
      (collapse
       (collapse-this (collapse-this frame
                                     (1st-complete (frame->frame frame)))
                      x)))
     (mv-nth 0
             (collapse (collapse-this frame
                                      (1st-complete (frame->frame frame))))))
    (consp (assoc-equal x (frame->frame frame)))
    (not
     (consp
      (abs-addrs
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
    (< 0 (1st-complete (frame->frame frame)))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (dist-names (frame->root frame)
                nil (frame->frame frame))
    (abs-separate (frame->frame frame)))
   (absfat-equiv
    (mv-nth 0
            (collapse (collapse-this (collapse-this frame x)
                                     (1st-complete (frame->frame frame)))))
    (mv-nth 0
            (collapse (collapse-this frame
                                     (1st-complete (frame->frame frame)))))))
  :hints
  (("goal"
    :in-theory
    (e/d (collapse-this)
         ((:rewrite partial-collapse-correctness-lemma-24)
          (:definition remove-equal)
          (:definition assoc-equal)
          (:rewrite remove-when-absent)
          (:rewrite strip-cars-of-remove-assoc)
          (:definition member-equal)
          (:definition remove-assoc-equal)
          (:definition no-duplicatesp-equal)
          (:rewrite subsetp-when-prefixp)
          (:rewrite partial-collapse-correctness-lemma-1)
          (:rewrite final-val-of-collapse-this-lemma-3)
          (:rewrite abs-file-alist-p-when-m1-file-alist-p)
          (:rewrite collapse-1st-index-correctness-lemma-1)
          abs-separate-of-frame->frame-of-collapse-this-lemma-8
          (:rewrite assoc-of-frame->frame-of-collapse-this)
          (:definition len)
          (:linear abs-separate-of-frame->frame-of-collapse-this-lemma-11)
          (:definition strip-cars))))))

(defthm
  partial-collapse-correctness-lemma-34
  (implies
   (and (not (zp (1st-complete-under-path frame path)))
        (no-duplicatesp-equal (strip-cars frame)))
   (equal
    (abs-addrs
     (frame-val->dir
      (cdr (assoc-equal (1st-complete-under-path frame path)
                        frame))))
    nil))
  :hints (("goal" :in-theory (enable 1st-complete-under-path))))

(defthm
  partial-collapse-correctness-lemma-25
  (implies
   (and (force (consp (assoc-equal x frame)))
        (abs-separate frame)
        (force (equal (assoc-equal x frame)
                      (assoc-equal x other-frame))))
   (dist-names (frame-val->dir (cdr (assoc-equal x other-frame)))
               (frame-val->path (cdr (assoc-equal x other-frame)))
               (remove-assoc-equal x frame)))
  :hints (("goal" :in-theory (disable abs-separate-of-frame->frame-of-collapse-this-lemma-2)
           :use abs-separate-of-frame->frame-of-collapse-this-lemma-2)))

(defthm
  partial-collapse-correctness-lemma-18
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
                                  (abs-separate-of-frame->frame-of-collapse-this-lemma-3))
           :use (abs-separate-of-frame->frame-of-collapse-this-lemma-3
                 (:instance abs-separate-of-frame->frame-of-collapse-this-lemma-3
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
  partial-collapse-correctness-lemma-48
  (implies
   (and (equal (1st-complete (put-assoc-equal key val frame))
               key)
        (frame-p (put-assoc-equal key val frame))
        (not (zp (1st-complete (put-assoc-equal key val frame))))
        (no-duplicatesp-equal (strip-cars (put-assoc-equal key val frame))))
   (equal (abs-addrs (frame-val->dir val))
          nil))
  :hints (("goal" :in-theory (disable abs-separate-of-frame->frame-of-collapse-this-lemma-9)
           :use ((:instance abs-separate-of-frame->frame-of-collapse-this-lemma-9
                            (frame (put-assoc-equal key val frame))))))
  :rule-classes :forward-chaining)

(defthm
  partial-collapse-correctness-lemma-33
  (implies
   (and
    (< 0
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame)))))
    (< 0
       (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
    (ctx-app-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
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

(defthmd
  partial-collapse-correctness-lemma-36
  (implies
   (and
    (mv-nth 1 (collapse (collapse-this frame x)))
    (consp (frame->frame frame))
    (< 0 x)
    (not
     (consp
      (abs-addrs
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
    (frame-p (frame->frame frame)))
   (> (1st-complete (frame->frame frame))
      0))
  :rule-classes :linear
  :hints
  (("goal" :do-not-induct t
    :in-theory (e/d (collapse-this collapse)
                    ((:linear abs-separate-of-frame->frame-of-collapse-this-lemma-12)))
    :use ((:instance (:linear abs-separate-of-frame->frame-of-collapse-this-lemma-12)
                     (frame (collapse-this frame x)))
          (:instance (:rewrite partial-collapse-correctness-lemma-32)
                     (frame (frame->frame frame))
                     (x x))))))

(defthm
  partial-collapse-correctness-lemma-31
  (implies
   (and (frame-p (frame->frame frame))
        (subsetp-equal l (strip-cars (frame->frame frame)))
        (not (member-equal (1st-complete (frame->frame frame))
                           l))
        (mv-nth 1 (collapse frame)))
   (equal (ctx-app-list fs path-len
                        (collapse-this frame
                                       (1st-complete (frame->frame frame)))
                        l)
          (ctx-app-list fs path-len frame l)))
  :hints (("goal" :in-theory (enable ctx-app-list subsetp-equal))))

(defthm
  partial-collapse-correctness-lemma-54
  (implies
   (or
    (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
    (consp
     (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame))))
   (subsetp-equal (strip-cars (frame->frame (collapse-this frame x)))
                  (strip-cars (frame->frame frame))))
  :hints (("goal" :in-theory (enable collapse-this))))

(defthm
  partial-collapse-correctness-lemma-78
  (implies (and (mv-nth 1 (collapse frame))
                (<= (nfix n) (len (frame->frame frame)))
                (no-duplicatesp-equal (strip-cars (frame->frame frame))))
           (subsetp-equal (frame-addrs-before frame x n)
                          (strip-cars (frame->frame frame))))
  :hints
  (("goal" :in-theory (e/d (frame-addrs-before collapse collapse-iter)
                           ((:rewrite partial-collapse-correctness-lemma-24)
                            (:definition no-duplicatesp-equal)
                            (:definition assoc-equal)
                            (:definition member-equal)
                            (:rewrite nthcdr-when->=-n-len-l)
                            (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
                            (:rewrite partial-collapse-correctness-lemma-2)))
    :induct (frame-addrs-before frame x n)
    :expand (collapse-iter frame 1)))
  :rule-classes ((:rewrite
                  :corollary
                  (implies (and (mv-nth 1 (collapse frame))
                                (<= (nfix n) (len (frame->frame frame)))
                                (no-duplicatesp-equal (strip-cars (frame->frame
                                                                   frame)))
                                (subsetp-equal (strip-cars (frame->frame frame)) y))
                           (subsetp-equal (frame-addrs-before frame x n) y)))
                 (:rewrite
                  :corollary
                  (implies (and (mv-nth 1 (collapse frame))
                                (<= (nfix n) (len (frame->frame frame)))
                                (no-duplicatesp-equal (strip-cars (frame->frame
                                                                   frame)))
                                (not (member-equal y
                                                   (strip-cars (frame->frame
                                                                frame)))))
                           (not
                            (member-equal
                             y
                             (frame-addrs-before frame x n)))))))

(defthm partial-collapse-correctness-lemma-55
  (implies (and (not (zp x))
                (mv-nth 1 (collapse frame)))
           (not (member-equal x (frame-addrs-before frame x n))))
  :hints (("goal" :in-theory (enable frame-addrs-before collapse))))

(defthmd
  partial-collapse-correctness-lemma-62
  (implies
   (and (abs-separate (frame->frame frame))
        (frame-p (frame->frame frame))
        (consp (assoc-equal x
                            (frame->frame (collapse-iter frame n))))
        (mv-nth 1 (collapse frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (and
    (equal
     (frame-val->dir
      (cdr (assoc-equal x
                        (frame->frame (collapse-iter frame n)))))
     (mv-nth 0
             (ctx-app-list
              (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
              (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
              frame (frame-addrs-before frame x n))))
    (mv-nth 1
            (ctx-app-list
             (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
             frame (frame-addrs-before frame x n)))))
  :hints
  (("goal" :induct (collapse-iter frame n)
    :do-not-induct t
    :in-theory
    (e/d (collapse-iter frame-addrs-before
                        ctx-app-list collapse)
         ((:definition no-duplicatesp-equal)
          (:definition member-equal)
          (:rewrite nthcdr-when->=-n-len-l)
          (:definition strip-cars)
          (:rewrite partial-collapse-correctness-lemma-24)
          (:definition remove-assoc-equal)
          (:definition nthcdr)
          (:rewrite 1st-complete-of-remove-assoc-2)
          (:rewrite final-val-of-collapse-this-lemma-3)
          (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8
                    . 1)
          (:type-prescription abs-fs-fix-of-put-assoc-equal-lemma-3)
          (:rewrite 1st-complete-of-put-assoc-lemma-1)
          (:definition len)
          (:rewrite partial-collapse-correctness-lemma-1))))))

(defthmd
  partial-collapse-correctness-lemma-63
  (implies
   (and
    (abs-separate (frame->frame frame))
    (frame-p (frame->frame frame))
    (consp
     (assoc-equal
      x
      (frame->frame (collapse-iter frame (collapse-1st-index frame x)))))
    (mv-nth 1 (collapse frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (equal
    (final-val x frame)
    (mv-nth 0
            (ctx-app-list
             (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
             frame
             (frame-addrs-before frame
                                 x (collapse-1st-index frame x))))))
  :hints (("goal" :in-theory (e/d (final-val))
           :use (:instance partial-collapse-correctness-lemma-62
                           (n (collapse-1st-index frame x))))))

(defthm
  partial-collapse-correctness-lemma-56
  (implies (and (valid-seqp frame seq)
                (no-duplicatesp-equal (strip-cars (frame->frame frame))))
           (valid-seqp (collapse-this frame (car seq))
                       (cdr seq)))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq)))
  :rule-classes (:rewrite :type-prescription))

(defthm
  partial-collapse-correctness-lemma-57
  (implies
   (and (< 0
           (frame-val->src (cdr (assoc-equal (car seq)
                                             (frame->frame frame)))))
        (frame-p (frame->frame frame))
        (valid-seqp frame seq)
        (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (prefixp
    (frame-val->path
     (cdr
      (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                     (frame->frame frame))))
                   (frame->frame frame))))
    (frame-val->path (cdr (assoc-equal (car seq)
                                       (frame->frame frame))))))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq))))

(defthm
  partial-collapse-correctness-lemma-58
  (implies (and (valid-seqp frame seq)
                (frame-p (frame->frame frame))
                (not (member-equal (car seq) l))
                (subsetp-equal l seq)
                (nat-listp seq))
           (equal (ctx-app-list-seq fs
                                    relpath (collapse-this frame (car seq))
                                    l (cdr seq))
                  (ctx-app-list-seq fs relpath frame l seq)))
  :hints (("goal" :in-theory (enable ctx-app-list-seq))))

(defthm
  partial-collapse-correctness-lemma-40
  (implies
   (and
    (or
     (equal (frame-val->src (cdr (assoc-equal (car seq)
                                              (frame->frame frame))))
            0)
     (not (equal x
                 (frame-val->src (cdr (assoc-equal (car seq)
                                                   (frame->frame frame)))))))
    (frame-p (frame->frame frame))
    (consp
     (assoc-equal x
                  (frame->frame (collapse-seq (collapse-this frame (car seq))
                                              (cdr seq))))))
   (equal (frame-addrs-before-seq (collapse-this frame (car seq))
                                  x (cdr seq))
          (frame-addrs-before-seq frame x seq)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (frame-addrs-before-seq)
                    ((:rewrite frame-p-of-frame->frame-of-collapse-seq)))
    :use (:instance (:rewrite frame-p-of-frame->frame-of-collapse-seq)
                    (seq (cdr seq))
                    (frame (collapse-this frame (car seq)))))))

(defthmd
  partial-collapse-correctness-lemma-71
  (implies (not (member-equal y seq))
           (equal (frame-addrs-before-seq (collapse-this frame y)
                                          x seq)
                  (frame-addrs-before-seq frame x seq)))
  :hints
  (("goal" :in-theory (enable frame-addrs-before-seq)
    :induct (frame-addrs-before-seq frame x seq))))

(defthm
  partial-collapse-correctness-lemma-72
  (implies (nat-listp seq)
           (equal (final-val-seq (car seq) frame seq)
                  (frame-val->dir (cdr (assoc-equal (car seq)
                                                    (frame->frame frame))))))
  :hints (("goal" :in-theory (enable final-val-seq
                                     position-equal collapse-seq)
           :do-not-induct t)))

(defthm
  partial-collapse-correctness-lemma-104
  (implies
   (and
    (equal
     (frame-val->dir
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal (car seq)
                                              (frame->frame frame))))
            (frame->frame (collapse-seq (collapse-this frame (car seq))
                                        (cdr seq))))))
     (mv-nth
      0
      (ctx-app-list-seq
       (ctx-app
        (frame-val->dir
         (cdr (assoc-equal
               (frame-val->src (cdr (assoc-equal (car seq)
                                                 (frame->frame frame))))
               (frame->frame frame))))
        (frame-val->dir (cdr (assoc-equal (car seq)
                                          (frame->frame frame))))
        (car seq)
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (car seq)
                                                   (frame->frame frame))))
                 (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal (car seq)
                                            (frame->frame frame))))))
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal (car seq)
                                                (frame->frame frame))))
              (frame->frame frame))))
       frame
       (frame-addrs-before-seq
        frame
        (frame-val->src (cdr (assoc-equal (car seq)
                                          (frame->frame frame))))
        (cdr seq))
       seq)))
    (mv-nth
     1
     (ctx-app-list-seq
      (ctx-app
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal (car seq)
                                                (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->dir (cdr (assoc-equal (car seq)
                                         (frame->frame frame))))
       (car seq)
       (nthcdr
        (len
         (frame-val->path
          (cdr (assoc-equal
                (frame-val->src (cdr (assoc-equal (car seq)
                                                  (frame->frame frame))))
                (frame->frame frame)))))
        (frame-val->path (cdr (assoc-equal (car seq)
                                           (frame->frame frame))))))
      (frame-val->path
       (cdr
        (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                       (frame->frame frame))))
                     (frame->frame frame))))
      frame
      (frame-addrs-before-seq
       frame
       (frame-val->src (cdr (assoc-equal (car seq)
                                         (frame->frame frame))))
       (cdr seq))
      seq))
    (abs-separate (frame->frame frame))
    (frame-p (frame->frame frame))
    (consp
     (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                    (frame->frame frame))))
                  (frame->frame (collapse-seq (collapse-this frame (car seq))
                                              (cdr seq)))))
    (valid-seqp frame seq)
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (nat-listp seq))
   (and
    (equal
     (frame-val->dir
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal (car seq)
                                              (frame->frame frame))))
            (frame->frame (collapse-seq (collapse-this frame (car seq))
                                        (cdr seq))))))
     (mv-nth
      0
      (ctx-app-list-seq
       (frame-val->dir
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal (car seq)
                                                (frame->frame frame))))
              (frame->frame frame))))
       (frame-val->path
        (cdr (assoc-equal
              (frame-val->src (cdr (assoc-equal (car seq)
                                                (frame->frame frame))))
              (frame->frame frame))))
       frame
       (frame-addrs-before-seq
        frame
        (frame-val->src (cdr (assoc-equal (car seq)
                                          (frame->frame frame))))
        seq)
       seq)))
    (mv-nth
     1
     (ctx-app-list-seq
      (frame-val->dir
       (cdr
        (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                       (frame->frame frame))))
                     (frame->frame frame))))
      (frame-val->path
       (cdr
        (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                       (frame->frame frame))))
                     (frame->frame frame))))
      frame
      (frame-addrs-before-seq
       frame
       (frame-val->src (cdr (assoc-equal (car seq)
                                         (frame->frame frame))))
       seq)
      seq))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (collapse-seq frame-addrs-before-seq
                                  ctx-app-list-seq collapse
                                  partial-collapse-correctness-lemma-71)
                    ((:definition no-duplicatesp-equal)
                     (:definition member-equal)
                     (:rewrite nthcdr-when->=-n-len-l)
                     (:definition remove-assoc-equal)
                     (:definition len)))
    :expand ((frame-addrs-before-seq
              frame
              (frame-val->src (cdr (assoc-equal (car seq)
                                                (frame->frame frame))))
              seq)))))

(defthm
  partial-collapse-correctness-lemma-61
  (implies
   (and (abs-separate (frame->frame frame))
        (frame-p (frame->frame frame))
        (consp (assoc-equal x
                            (frame->frame (collapse-seq frame seq))))
        (valid-seqp frame seq)
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (nat-listp seq))
   (and
    (equal
     (frame-val->dir
      (cdr (assoc-equal x
                        (frame->frame (collapse-seq frame seq)))))
     (mv-nth 0
             (ctx-app-list-seq
              (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
              (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
              frame
              (frame-addrs-before-seq frame x seq)
              seq)))
    (mv-nth 1
            (ctx-app-list-seq
             (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
             frame
             (frame-addrs-before-seq frame x seq)
             seq))))
  :hints
  (("goal"
    :in-theory (e/d (collapse-seq frame-addrs-before-seq
                                  ctx-app-list-seq collapse)
                    ((:definition no-duplicatesp-equal)
                     (:definition member-equal)
                     (:rewrite nthcdr-when->=-n-len-l)
                     (:definition remove-assoc-equal)
                     (:definition nthcdr)
                     (:definition len)))
    :induct (collapse-seq frame seq)
    :expand
    (:with
     partial-collapse-correctness-lemma-71
     (frame-addrs-before-seq
      (collapse-this frame (car seq))
      (frame-val->src$inline (cdr (assoc-equal (car seq)
                                               (frame->frame frame))))
      (cdr seq))))))

(defthmd
  partial-collapse-correctness-lemma-53
  (implies
   (and
    (abs-separate (frame->frame frame))
    (frame-p (frame->frame frame))
    (consp
     (assoc-equal
      x
      (frame->frame (collapse-seq frame
                                  (take (position-equal x seq) seq)))))
    (valid-seqp frame (take (position-equal x seq) seq))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (nat-listp (take (position-equal x seq) seq)))
   (equal
    (final-val-seq x frame seq)
    (mv-nth 0
            (ctx-app-list-seq
             (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
             (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
             frame
             (frame-addrs-before-seq frame
                                     x (take (position-equal x seq) seq))
             (take (position-equal x seq) seq)))))
  :hints (("goal" :in-theory (enable final-val-seq))))

(defthm
  partial-collapse-correctness-lemma-77
  (implies
   (and (mv-nth 1 (collapse frame))
        (consp (assoc-equal x (frame->frame frame)))
        (frame-p (frame->frame frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (not (equal (1st-complete (frame->frame frame))
               (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8 . 2))
    :use (:instance (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8 . 2)
                    (frame frame)
                    (x x)
                    (y (1st-complete (frame->frame frame)))))))

(defthm
  partial-collapse-correctness-lemma-79
  (implies
   (not (equal (1st-complete (frame->frame frame))
               x))
   (equal
    (collapse-1st-index
     (collapse-iter frame 1)
     (frame-val->src
      (cdr (assoc-equal x
                        (frame->frame (collapse-iter frame 1))))))
    (collapse-1st-index
     (collapse-iter frame 1)
     (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))))
  :hints
  (("goal"
    :in-theory (e/d (collapse-iter)
                    ((:rewrite final-val-of-collapse-this-lemma-14)))
    :use ((:instance (:rewrite final-val-of-collapse-this-lemma-14)
                     (x x)
                     (n 1)
                     (frame frame))
          (:instance
           (:rewrite final-val-of-collapse-this-lemma-14)
           (x (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
           (n 1)
           (frame frame)))
    :expand (collapse-iter frame 1))))

(defthm
  partial-collapse-correctness-lemma-82
  (implies
   (and (mv-nth 1 (collapse frame))
        (consp (assoc-equal x (frame->frame frame)))
        (frame-p (frame->frame frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (< (collapse-1st-index frame x)
      (collapse-1st-index
       frame
       (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))))
  :hints (("goal" :in-theory (enable collapse-1st-index collapse)))
  :rule-classes :linear)

(defthm
  partial-collapse-correctness-lemma-83
  (implies
   (consp
    (assoc-equal
     (frame-val->src (cdr (assoc-equal (nth (+ -1 n) seq)
                                       (frame->frame frame))))
     (frame->frame
      (collapse-seq
       frame
       (take (position-equal
              (frame-val->src (cdr (assoc-equal (nth (+ -1 n) seq)
                                                (frame->frame frame))))
              seq)
             seq)))))
   (consp (assoc-equal (nth (+ -1 n) seq)
                       (frame->frame frame)))))

(defthm
  partial-collapse-correctness-lemma-84
  (implies
   (and
    (frame-p (frame->frame frame))
    (consp
     (assoc-equal
      (frame-val->src (cdr (assoc-equal (nth (+ -1 n) seq)
                                        (frame->frame frame))))
      (frame->frame
       (collapse-seq
        frame
        (take (position-equal
               (frame-val->src (cdr (assoc-equal (nth (+ -1 n) seq)
                                                 (frame->frame frame))))
               seq)
              seq)))))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (mv-nth 1 (collapse frame)))
   (member-equal
    (nth (+ -1 n) seq)
    (frame-addrs-before
     frame
     (frame-val->src (cdr (assoc-equal (nth (+ -1 n) seq)
                                       (frame->frame frame))))
     (collapse-1st-index
      frame
      (frame-val->src (cdr (assoc-equal (nth (+ -1 n) seq)
                                        (frame->frame frame))))))))
  :hints
  (("goal"
    :do-not-induct t
    :cases
    ((equal
      (if
          (<
           (binary-+
            (len (frame->frame frame))
            (unary--
             (collapse-1st-index
              frame
              (frame-val->src$inline (cdr (assoc-equal (nth (binary-+ '-1 n) seq)
                                                       (frame->frame frame)))))))
           '0)
          '0
        (binary-+
         (len (frame->frame frame))
         (unary--
          (collapse-1st-index
           frame
           (frame-val->src$inline (cdr (assoc-equal (nth (binary-+ '-1 n) seq)
                                                    (frame->frame frame))))))))
      (binary-+
       (len (frame->frame frame))
       (unary-- (collapse-1st-index
                 frame
                 (frame-val->src$inline
                  (cdr (assoc-equal (nth (binary-+ '-1 n) seq)
                                    (frame->frame frame))))))))))))

(defthm
  partial-collapse-correctness-lemma-85
  (implies
   (and
    (not (zp n))
    (subsetp-equal (frame-addrs-before-seq frame x (take (+ -1 n) seq))
                   (frame-addrs-before frame x (collapse-1st-index frame x)))
    (frame-p (frame->frame frame))
    (consp
     (assoc-equal
      x
      (frame->frame (collapse-seq frame
                                  (take (position-equal x seq) seq)))))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (mv-nth 1 (collapse frame)))
   (subsetp-equal (frame-addrs-before-seq frame x (take n seq))
                  (frame-addrs-before frame x (collapse-1st-index frame x))))
  :hints
  (("goal"
    :in-theory (e/d (frame-addrs-before-seq)
                    ((:rewrite binary-append-take-nthcdr)
                     (:rewrite frame-addrs-before-seq-of-append)))
    :use
    ((:instance (:rewrite binary-append-take-nthcdr)
                (l (take n seq))
                (i (+ -1 n)))
     (:instance (:rewrite frame-addrs-before-seq-of-append)
                (l2 (nthcdr (+ -1 n) (take n seq)))
                (l1 (take (+ -1 n) seq))
                (x x)
                (frame frame))
     (:instance
      (:rewrite subsetp-append1)
      (a (nthcdr (+ -1 n) (take n seq)))
      (b (frame-addrs-before-seq
          frame
          (frame-val->src (cdr (assoc-equal (nth (+ -1 n) seq)
                                            (frame->frame frame))))
          (take (+ -1 n) seq)))
      (c
       (frame-addrs-before
        frame
        (frame-val->src (cdr (assoc-equal (nth (+ -1 n) seq)
                                          (frame->frame frame))))
        (collapse-1st-index
         frame
         (frame-val->src (cdr (assoc-equal (nth (+ -1 n) seq)
                                           (frame->frame frame))))))))
     (:instance take-of-nthcdr (l seq)
                (n2 (- n 1))
                (n1 1))))))

(defthm
  partial-collapse-correctness-lemma-81
  (implies
   (and
    (member-equal
     (nth (+ -1 n)
          (frame-addrs-before frame x (collapse-1st-index frame x)))
     (frame-addrs-before frame x (collapse-1st-index frame x)))
    (consp
     (assoc-equal
      x
      (frame->frame (collapse-seq frame
                                  (take (position-equal x seq) seq)))))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (mv-nth 1 (collapse frame)))
   (member-equal
    (nth (+ -1 n)
         (frame-addrs-before frame x (collapse-1st-index frame x)))
    (strip-cars (frame->frame frame))))
  :instructions
  (:promote
   (:rewrite (:rewrite subsetp-member . 2)
             ((x (frame-addrs-before frame x (collapse-1st-index frame x)))))
   (:claim (and (<= (nfix (collapse-1st-index frame x))
                    (len (frame->frame frame)))
                (subsetp-equal (strip-cars (frame->frame frame))
                               (strip-cars (frame->frame frame))))
           :hints :none)
   (:rewrite partial-collapse-correctness-lemma-78)
   :bash (:dive 1 2)
   (:apply-linear collapse-1st-index-correctness-1)
   :top
   :bash :bash))

(defthm
  partial-collapse-correctness-lemma-88
  (implies
   (and
    (not (zp n))
    (consp
     (assoc-equal
      x
      (frame->frame (collapse-seq frame
                                  (take (position-equal x seq) seq)))))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (mv-nth 1 (collapse frame))
    (<= n
        (len (frame-addrs-before frame x (collapse-1st-index frame x)))))
   (consp (assoc-equal
           (nth (+ -1 n)
                (frame-addrs-before frame x (collapse-1st-index frame x)))
           (frame->frame frame))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable (:rewrite member-of-strip-cars)
                        member-of-a-nat-list
                        (:rewrite member-equal-nth))
    :use
    ((:instance
      (:rewrite member-of-strip-cars)
      (alist (frame->frame frame))
      (x (nth (+ -1 n)
              (frame-addrs-before frame x (collapse-1st-index frame x)))))
     (:instance
      member-of-a-nat-list
      (x (nth (+ -1 n)
              (frame-addrs-before frame x (collapse-1st-index frame x))))
      (lst (frame-addrs-before frame x (collapse-1st-index frame x))))
     (:instance (:rewrite member-equal-nth)
                (l (frame-addrs-before frame x (collapse-1st-index frame x)))
                (n (+ -1 n)))))))

(defthmd
  partial-collapse-correctness-lemma-89
  (implies (member-equal y (frame-addrs-before frame x n))
           (equal (frame-val->src (cdr (assoc-equal y (frame->frame frame))))
                  x))
  :hints (("goal" :in-theory (enable frame-addrs-before collapse-iter)
           :induct (frame-addrs-before frame x n)
           :expand (collapse-iter frame 1))))

(defthm
  partial-collapse-correctness-lemma-91
  (implies
   (< (nfix m)
      (len (frame-addrs-before frame x n)))
   (equal
    (frame-val->src
     (cdr (assoc-equal (nth m (frame-addrs-before frame x n))
                       (frame->frame frame))))
    x))
  :hints
  (("goal"
    :use
    (:instance partial-collapse-correctness-lemma-89
               (y (nth m (frame-addrs-before frame x n)))))))

(defthm
  partial-collapse-correctness-lemma-94
  (implies (and (member-equal 0 seq)
                (no-duplicatesp-equal (strip-cars (frame->frame frame))))
           (not (equal (len (frame->frame (collapse-seq frame seq)))
                       (+ (len (frame->frame frame))
                          (- (len seq))))))
  :hints (("goal" :in-theory (e/d (valid-seqp)
                                  (ctx-app-ok-of-ctx-app-list-seq-lemma-1))
           :use ctx-app-ok-of-ctx-app-list-seq-lemma-1)))

(defthmd
  partial-collapse-correctness-lemma-73
  (implies
   (and
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (valid-seqp frame seq)
    (member-equal x seq)
    (not (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))))
   (consp
    (abs-addrs
     (frame-val->dir
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame)))))))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq))))

(encapsulate
  ()

  (local
   (defthm
     lemma-1
     (implies
      (and
       (equal (frame-val->src (cdr (assoc-equal (car seq)
                                                (frame->frame frame))))
              0)
       (consp (assoc-equal (car seq)
                           (frame->frame frame)))
       (not
        (consp
         (abs-addrs (frame-val->dir (cdr (assoc-equal (car seq)
                                                      (frame->frame frame)))))))
       (ctx-app-ok (frame->root frame)
                   (car seq)
                   (frame-val->path (cdr (assoc-equal (car seq)
                                                      (frame->frame frame)))))
       (equal (len (frame->frame (collapse-seq (collapse-this frame (car seq))
                                               (cdr seq))))
              (+ -1 (- (len (cdr seq)))
                 (len (frame->frame frame))))
       (no-duplicatesp-equal (strip-cars (frame->frame frame)))
       (member-equal x (cdr seq)))
      (not
       (equal (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
              (car seq))))
     :hints
     (("goal" :in-theory (e/d (valid-seqp collapse-seq))
       :use partial-collapse-correctness-lemma-73))))

  (local
   (defthm
     lemma-2
     (implies
      (and
       (consp seq)
       (not
        (consp
         (abs-addrs (frame-val->dir (cdr (assoc-equal (car seq)
                                                      (frame->frame frame)))))))
       (prefixp
        (frame-val->path
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                         (frame->frame frame))))
                       (frame->frame frame))))
        (frame-val->path (cdr (assoc-equal (car seq)
                                           (frame->frame frame)))))
       (ctx-app-ok
        (frame-val->dir
         (cdr
          (assoc-equal (frame-val->src (cdr (assoc-equal (car seq)
                                                         (frame->frame frame))))
                       (frame->frame frame))))
        (car seq)
        (nthcdr
         (len
          (frame-val->path
           (cdr (assoc-equal
                 (frame-val->src (cdr (assoc-equal (car seq)
                                                   (frame->frame frame))))
                 (frame->frame frame)))))
         (frame-val->path (cdr (assoc-equal (car seq)
                                            (frame->frame frame))))))
       (equal (len (frame->frame (collapse-seq (collapse-this frame (car seq))
                                               (cdr seq))))
              (+ -1 (- (len (cdr seq)))
                 (len (frame->frame frame))))
       (no-duplicatesp-equal (strip-cars (frame->frame frame)))
       (member-equal x (cdr seq)))
      (not
       (equal (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
              (car seq))))
     :hints
     (("goal" :in-theory (e/d (valid-seqp collapse-seq))
       :use (:rewrite partial-collapse-correctness-lemma-73)))))

  (defthmd
    partial-collapse-correctness-lemma-35
    (implies
     (and
      (nat-listp seq)
      (valid-seqp frame seq)
      (no-duplicatesp-equal (strip-cars (frame->frame frame)))
      (member-equal x seq)
      (not (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
      (member-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                    seq))
     (< (position-equal x seq)
        (position-equal
         (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
         seq)))
    :rule-classes :linear
    :hints (("goal" :in-theory (enable valid-seqp collapse-seq)
             :induct (collapse-seq frame seq)
             :expand (position-equal (car seq) seq)))))

(defthmd
  partial-collapse-correctness-lemma-96
  (implies
   (and (mv-nth 1 (collapse frame))
        (not (zp (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
        (abs-separate (frame->frame frame))
        (frame-p (frame->frame frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (member-equal
    x
    (abs-addrs
     (frame-val->dir
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame)))))))
  :hints
  (("goal" :in-theory (e/d (collapse abs-addrs-of-ctx-app-1-lemma-7)
                           ((:rewrite remove-assoc-of-put-assoc)
                            (:rewrite remove-assoc-of-remove-assoc)
                            (:rewrite abs-file-alist-p-when-m1-file-alist-p)))
    :induct (collapse frame))))

;; Ton of free variables here - at any rate, frame is free.
(defthm
  partial-collapse-correctness-lemma-106
  (implies
   (and
    (valid-seqp frame seq)
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (member-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  seq)
    (member-equal
     x
     (abs-addrs
      (frame-val->dir
       (cdr (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame))))))
    (abs-separate (frame->frame frame))
    (frame-p (frame->frame frame)))
   (member-equal x seq))
  :hints (("goal" :induct (collapse-seq frame seq)
           :in-theory (enable valid-seqp collapse-seq))))

(defthm
  partial-collapse-correctness-lemma-107
  (implies
   (and
    (member-equal x seq)
    (nat-listp seq)
    (not (zp n))
    (abs-separate (frame->frame frame))
    (frame-p (frame->frame frame))
    (consp
     (assoc-equal
      x
      (frame->frame (collapse-seq frame
                                  (take (position-equal x seq) seq)))))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (mv-nth 1 (collapse frame))
    (<= n
        (len (frame-addrs-before frame x (collapse-1st-index frame x)))))
   (member-equal
    (nth (binary-+ -1 n)
         (frame-addrs-before frame x (collapse-1st-index frame x)))
    (abs-addrs
     (frame-val->dir$inline (cdr (assoc-equal x (frame->frame frame)))))))
  :hints
  (("goal"
    :use
    (:instance
     partial-collapse-correctness-lemma-96
     (x (nth (binary-+ -1 n)
             (frame-addrs-before frame
                                 x (collapse-1st-index frame x))))))))

(defthm
  partial-collapse-correctness-lemma-99
  (implies
   (and
    (member-equal x seq)
    (nat-listp seq)
    (not (zp n))
    (abs-separate (frame->frame frame))
    (frame-p (frame->frame frame))
    (consp
     (assoc-equal
      x
      (frame->frame (collapse-seq frame
                                  (take (position-equal x seq) seq)))))
    (valid-seqp frame seq)
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (mv-nth 1 (collapse frame))
    (<= n
        (len (frame-addrs-before frame x (collapse-1st-index frame x)))))
   (< (position-equal
       (nth (+ -1 n)
            (frame-addrs-before frame x (collapse-1st-index frame x)))
       seq)
      (position-equal x seq)))
  :hints
  (("goal"
    :do-not-induct t
    :use (:instance
          (:linear partial-collapse-correctness-lemma-35)
          (seq seq)
          (frame frame)
          (x (nth (+ -1 n)
                  (frame-addrs-before frame
                                      x (collapse-1st-index frame x)))))))
  :rule-classes :linear)

(defthm
  partial-collapse-correctness-lemma-51
  (implies (not (member-equal x seq))
           (and
            (equal (frame-val->path
                    (cdr (assoc-equal x
                                      (frame->frame (collapse-seq frame seq)))))
                   (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
            (equal (frame-val->src
                    (cdr (assoc-equal x
                                      (frame->frame (collapse-seq frame seq)))))
                   (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
            (iff (consp (assoc-equal x
                                     (frame->frame (collapse-seq frame seq))))
                 (consp (assoc-equal x (frame->frame frame))))))
  :hints (("goal" :in-theory (enable collapse-seq valid-seqp))))

(encapsulate
  ()

  (local (include-book "std/basic/inductions" :dir :system))

  (local
   (defthm
     lemma
     (implies
      (and
       (member-equal x seq)
       (nat-listp seq)
       (not (zp n))
       (subsetp-equal
        (take (+ -1 n)
              (frame-addrs-before frame x (collapse-1st-index frame x)))
        (frame-addrs-before-seq frame
                                x (take (position-equal x seq) seq)))
       (abs-separate (frame->frame frame))
       (frame-p (frame->frame frame))
       (consp
        (assoc-equal
         x
         (frame->frame (collapse-seq frame
                                     (take (position-equal x seq) seq)))))
       (valid-seqp frame seq)
       (no-duplicatesp-equal (strip-cars (frame->frame frame)))
       (mv-nth 1 (collapse frame))
       (<= n
           (len (frame-addrs-before frame x (collapse-1st-index frame x)))))
      (subsetp-equal
       (take n
             (frame-addrs-before frame x (collapse-1st-index frame x)))
       (frame-addrs-before-seq frame
                               x (take (position-equal x seq) seq))))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory (e/d (member-of-take)
                       ((:rewrite binary-append-take-nthcdr)
                        (:rewrite subsetp-append1)
                        partial-collapse-correctness-lemma-51))
       :use
       ((:instance
         (:rewrite binary-append-take-nthcdr)
         (l (take n
                  (frame-addrs-before frame x (collapse-1st-index frame x))))
         (i (+ -1 n)))
        (:instance
         (:rewrite subsetp-append1)
         (a (take (+ -1 n)
                  (frame-addrs-before frame x (collapse-1st-index frame x))))
         (b
          (nthcdr
           (+ -1 n)
           (take n
                 (frame-addrs-before frame x (collapse-1st-index frame x)))))
         (c (frame-addrs-before-seq frame
                                    x (take (position-equal x seq) seq))))
        (:instance (:rewrite take-of-nthcdr)
                   (l (frame-addrs-before frame x (collapse-1st-index frame x)))
                   (n2 (+ -1 n))
                   (n1 1)))))))

  (defthm
    partial-collapse-correctness-lemma-86
    (implies
     (and
      (frame-p (frame->frame frame))
      (consp
       (assoc-equal
        x
        (frame->frame (collapse-seq frame
                                    (take (position-equal x seq) seq)))))
      (no-duplicatesp-equal (strip-cars (frame->frame frame)))
      (mv-nth 1 (collapse frame)))
     (subsetp-equal (frame-addrs-before-seq frame x (take n seq))
                    (frame-addrs-before frame x (collapse-1st-index frame x))))
    :hints
    (("goal" :induct (dec-induct n))))

  (defthm
    partial-collapse-correctness-lemma-110
    (implies
     (and
      (member-equal x seq)
      (nat-listp seq)
      (abs-separate (frame->frame frame))
      (frame-p (frame->frame frame))
      (consp
       (assoc-equal
        x
        (frame->frame (collapse-seq frame
                                    (take (position-equal x seq) seq)))))
      (valid-seqp frame seq)
      (no-duplicatesp-equal (strip-cars (frame->frame frame)))
      (mv-nth 1 (collapse frame))
      (<= n
          (len (frame-addrs-before frame x (collapse-1st-index frame x)))))
     (subsetp-equal
      (take n
            (frame-addrs-before frame x (collapse-1st-index frame x)))
      (frame-addrs-before-seq frame
                              x (take (position-equal x seq) seq))))
    :hints (("goal" :in-theory (enable final-val-seq member-of-take)
             :induct (dec-induct n)))))

(defthm
  partial-collapse-correctness-lemma-111
  (implies
   (and
    (member-equal x seq)
    (nat-listp seq)
    (abs-separate (frame->frame frame))
    (frame-p (frame->frame frame))
    (consp
     (assoc-equal
      x
      (frame->frame (collapse-seq frame
                                  (take (position-equal x seq) seq)))))
    (valid-seqp frame seq)
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (mv-nth 1 (collapse frame)))
   (set-equiv (frame-addrs-before-seq frame
                                      x (take (position-equal x seq) seq))
              (frame-addrs-before frame x (collapse-1st-index frame x))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (set-equiv member-of-take)
                    (partial-collapse-correctness-lemma-110))
    :use
    ((:instance partial-collapse-correctness-lemma-110
                (n (position-equal x seq)))
     (:instance
      partial-collapse-correctness-lemma-110
      (n (len (frame-addrs-before frame
                                  x (collapse-1st-index frame x)))))))))

(defund absfat-equiv-upto-n
  (frame seq n)
  (or
   (zp n)
   (and
    (absfat-equiv
     (final-val-seq (nth (- n 1) seq) frame seq)
     (final-val (nth (- n 1) seq) frame))
    (absfat-equiv-upto-n frame seq (- n 1)))))

(defthm absfat-equiv-upto-n-correctness-1
  (implies (and (absfat-equiv-upto-n frame seq n)
                (member-equal x seq)
                (< (position-equal x seq) (nfix n)))
           (absfat-equiv (final-val-seq x frame seq)
                         (final-val x frame)))
  :hints (("goal" :in-theory (enable absfat-equiv-upto-n))))

(defthmd
  partial-collapse-correctness-lemma-113
  (implies (and (valid-seqp frame seq)
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (member-equal x seq))
           (consp (assoc-equal x (frame->frame frame))))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq))))

(defthm
  partial-collapse-correctness-lemma-114
  (implies (and (valid-seqp frame seq)
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (< (nfix n) (len seq)))
           (consp (assoc-equal (nth n seq)
                               (frame->frame frame))))
  :hints (("goal"
           :use (:instance partial-collapse-correctness-lemma-113
                           (x (nth n seq))))))

(defthm
  partial-collapse-correctness-lemma-98
  (implies
   (and (< (nfix m) (len seq))
        (nat-listp seq)
        (abs-separate (frame->frame frame))
        (frame-p (frame->frame frame))
        (valid-seqp frame seq)
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (mv-nth 1 (collapse frame)))
   (set-equiv (frame-addrs-before-seq frame (nth m seq)
                                      (take m seq))
              (frame-addrs-before frame (nth m seq)
                                  (collapse-1st-index frame (nth m seq)))))
  :hints (("goal" :do-not-induct t
           :in-theory (disable partial-collapse-correctness-lemma-111
                               (:definition nfix)
                               (:definition nth))
           :use (:instance partial-collapse-correctness-lemma-111
                           (x (nth m seq))))))

(defthm
  partial-collapse-correctness-lemma-121
  (implies
   (and
    (not (zp n))
    (absfat-equiv
     (mv-nth 0
             (ctx-app-list-seq
              (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                (frame->frame frame))))
              (frame-val->path (cdr (assoc-equal (nth m seq)
                                                 (frame->frame frame))))
              frame
              (frame-addrs-before-seq frame (nth m seq)
                                      (take (+ -1 n) seq))
              (take m seq)))
     (mv-nth
      0
      (ctx-app-list (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                      (frame->frame frame))))
                    (frame-val->path (cdr (assoc-equal (nth m seq)
                                                       (frame->frame frame))))
                    frame
                    (frame-addrs-before-seq frame (nth m seq)
                                            (take (+ -1 n) seq)))))
    (absfat-equiv-upto-n frame seq m)
    (valid-seqp frame seq)
    (< m (len seq))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (nat-listp seq)
    (integerp m)
    (<= n m))
   (absfat-equiv
    (mv-nth
     0
     (ctx-app-list-seq
      (mv-nth 0
              (ctx-app-list-seq
               (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                 (frame->frame frame))))
               (frame-val->path (cdr (assoc-equal (nth m seq)
                                                  (frame->frame frame))))
               frame
               (frame-addrs-before-seq frame (nth m seq)
                                       (take (+ -1 n) seq))
               (take m seq)))
      (frame-val->path (cdr (assoc-equal (nth m seq)
                                         (frame->frame frame))))
      frame
      (frame-addrs-before-seq frame (nth m seq)
                              (nthcdr (+ -1 n) (take n seq)))
      (take m seq)))
    (mv-nth
     0
     (ctx-app-list
      (mv-nth 0
              (ctx-app-list
               (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                 (frame->frame frame))))
               (frame-val->path (cdr (assoc-equal (nth m seq)
                                                  (frame->frame frame))))
               frame
               (frame-addrs-before-seq frame (nth m seq)
                                       (take (+ -1 n) seq))))
      (frame-val->path (cdr (assoc-equal (nth m seq)
                                         (frame->frame frame))))
      frame
      (frame-addrs-before-seq frame (nth m seq)
                              (nthcdr (+ -1 n) (take n seq)))))))
  :hints
  (("goal"
    :in-theory (e/d (frame-addrs-before-seq ctx-app-list ctx-app-list-seq member-of-take)
                    ((:definition member-equal)
                     (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
                     (:rewrite binary-append-take-nthcdr)))
    :use ((:instance (:rewrite binary-append-take-nthcdr)
                     (l (take n seq))
                     (i (+ -1 n)))
          (:instance (:rewrite take-of-nthcdr)
                     (l seq)
                     (n2 (+ -1 n))
                     (n1 1))))))

(defthm
  partial-collapse-correctness-lemma-121
  (implies
   (and
    (not (zp n))
    (absfat-equiv
     (mv-nth 0
             (ctx-app-list-seq
              (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                (frame->frame frame))))
              (frame-val->path (cdr (assoc-equal (nth m seq)
                                                 (frame->frame frame))))
              frame
              (frame-addrs-before-seq frame (nth m seq)
                                      (take (+ -1 n) seq))
              (take m seq)))
     (mv-nth
      0
      (ctx-app-list (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                      (frame->frame frame))))
                    (frame-val->path (cdr (assoc-equal (nth m seq)
                                                       (frame->frame frame))))
                    frame
                    (frame-addrs-before-seq frame (nth m seq)
                                            (take (+ -1 n) seq)))))
    (absfat-equiv-upto-n frame seq m)
    (valid-seqp frame seq)
    (< m (len seq))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (nat-listp seq)
    (integerp m)
    (<= n m))
   (absfat-equiv
    (mv-nth
     0
     (ctx-app-list-seq
      (mv-nth 0
              (ctx-app-list-seq
               (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                 (frame->frame frame))))
               (frame-val->path (cdr (assoc-equal (nth m seq)
                                                  (frame->frame frame))))
               frame
               (frame-addrs-before-seq frame (nth m seq)
                                       (take (+ -1 n) seq))
               (take m seq)))
      (frame-val->path (cdr (assoc-equal (nth m seq)
                                         (frame->frame frame))))
      frame
      (frame-addrs-before-seq frame (nth m seq)
                              (nthcdr (+ -1 n) (take n seq)))
      (take m seq)))
    (mv-nth
     0
     (ctx-app-list
      (mv-nth 0
              (ctx-app-list
               (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                 (frame->frame frame))))
               (frame-val->path (cdr (assoc-equal (nth m seq)
                                                  (frame->frame frame))))
               frame
               (frame-addrs-before-seq frame (nth m seq)
                                       (take (+ -1 n) seq))))
      (frame-val->path (cdr (assoc-equal (nth m seq)
                                         (frame->frame frame))))
      frame
      (frame-addrs-before-seq frame (nth m seq)
                              (nthcdr (+ -1 n) (take n seq)))))))
  :hints
  (("goal"
    :in-theory (e/d (frame-addrs-before-seq ctx-app-list ctx-app-list-seq)
                    ((:definition member-equal)
                     (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
                     (:rewrite binary-append-take-nthcdr)))
    :use ((:instance (:rewrite binary-append-take-nthcdr)
                     (l (take n seq))
                     (i (+ -1 n)))
          (:instance (:rewrite take-of-nthcdr)
                     (l seq)
                     (n2 (+ -1 n))
                     (n1 1))))))

(encapsulate
  ()

  (local (include-book "std/basic/inductions" :dir :system))

  (local
   (defthm
     lemma
     (implies
      (and
       (not (zp n))
       (absfat-equiv
        (mv-nth 0
                (ctx-app-list-seq
                 (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                   (frame->frame frame))))
                 (frame-val->path (cdr (assoc-equal (nth m seq)
                                                    (frame->frame frame))))
                 frame
                 (frame-addrs-before-seq frame (nth m seq)
                                         (take (+ -1 n) seq))
                 (take m seq)))
        (mv-nth
         0
         (ctx-app-list (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                         (frame->frame frame))))
                       (frame-val->path (cdr (assoc-equal (nth m seq)
                                                          (frame->frame frame))))
                       frame
                       (frame-addrs-before-seq frame (nth m seq)
                                               (take (+ -1 n) seq)))))
       (absfat-equiv-upto-n frame seq m)
       (valid-seqp frame seq)
       (< m (len seq))
       (no-duplicatesp-equal (strip-cars (frame->frame frame)))
       (nat-listp seq)
       (integerp m)
       (<= n m))
      (absfat-equiv
       (mv-nth 0
               (ctx-app-list-seq
                (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                  (frame->frame frame))))
                (frame-val->path (cdr (assoc-equal (nth m seq)
                                                   (frame->frame frame))))
                frame
                (frame-addrs-before-seq frame (nth m seq)
                                        (take n seq))
                (take m seq)))
       (mv-nth
        0
        (ctx-app-list (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                        (frame->frame frame))))
                      (frame-val->path (cdr (assoc-equal (nth m seq)
                                                         (frame->frame frame))))
                      frame
                      (frame-addrs-before-seq frame (nth m seq)
                                              (take n seq))))))
     :instructions
     (:promote (:claim (equal (take n seq)
                              (append (take (+ -1 n) (take n seq))
                                      (nthcdr (+ -1 n) (take n seq))))
                       :hints :none)
               (:change-goal nil t)
               (:dive 2)
               (:rewrite binary-append-take-nthcdr)
               :top :s :bash (:dive 1 2 4 3)
               := :up
               (:rewrite frame-addrs-before-seq-of-append)
               :top (:dive 2 2 4 3)
               :=
               :up (:rewrite frame-addrs-before-seq-of-append)
               :top bash)))

  (defthm
    partial-collapse-correctness-lemma-68
    (implies
     (and (absfat-equiv-upto-n frame seq m)
          (valid-seqp frame seq)
          (< m (len seq))
          (no-duplicatesp-equal (strip-cars (frame->frame frame)))
          (nat-listp seq)
          (integerp m)
          (<= n m))
     (absfat-equiv
      (mv-nth 0
              (ctx-app-list-seq
               (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                 (frame->frame frame))))
               (frame-val->path (cdr (assoc-equal (nth m seq)
                                                  (frame->frame frame))))
               frame
               (frame-addrs-before-seq frame (nth m seq)
                                       (take n seq))
               (take m seq)))
      (mv-nth
       0
       (ctx-app-list (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                       (frame->frame frame))))
                     (frame-val->path (cdr (assoc-equal (nth m seq)
                                                        (frame->frame frame))))
                     frame
                     (frame-addrs-before-seq frame (nth m seq)
                                             (take n seq))))))
    :hints
    (("goal"
      :in-theory (e/d (frame-addrs-before-seq ctx-app-list ctx-app-list-seq)
                      ((:definition member-equal)
                       (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)))
      :induct (dec-induct n))))

  (defthm
    partial-collapse-correctness-lemma-127
    (implies
     (and (absfat-equiv-upto-n frame seq m)
          (mv-nth 1 (collapse frame))
          (abs-separate (frame->frame frame))
          (frame-p (frame->frame frame))
          (valid-seqp frame seq)
          (< m (len seq))
          (no-duplicatesp-equal (strip-cars (frame->frame frame)))
          (nat-listp seq)
          (natp m))
     (absfat-equiv
      (mv-nth 0
              (ctx-app-list-seq
               (frame-val->dir (cdr (assoc-equal (nth m seq)
                                                 (frame->frame frame))))
               (frame-val->path (cdr (assoc-equal (nth m seq)
                                                  (frame->frame frame))))
               frame
               (frame-addrs-before-seq frame (nth m seq)
                                       (take m seq))
               (take m seq)))
      (mv-nth
       0
       (ctx-app-list
        (frame-val->dir (cdr (assoc-equal (nth m seq)
                                          (frame->frame frame))))
        (frame-val->path (cdr (assoc-equal (nth m seq)
                                           (frame->frame frame))))
        frame
        (frame-addrs-before frame (nth m seq)
                            (collapse-1st-index frame (nth m seq)))))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (e/d (partial-collapse-correctness-lemma-62)
                      ())
      :use
      (:instance
       (:rewrite ctx-app-list-when-set-equiv)
       (l1 (frame-addrs-before frame (nth m seq)
                               (collapse-1st-index frame (nth m seq))))
       (l2 (frame-addrs-before-seq frame (nth m seq)
                                   (take m seq)))
       (relpath (frame-val->path (cdr (assoc-equal (nth m seq)
                                                   (frame->frame frame)))))
       (fs (frame-val->dir (cdr (assoc-equal (nth m seq)
                                             (frame->frame frame)))))))))

  (defthm
    partial-collapse-correctness-lemma-128
    (implies (and (abs-separate (frame->frame frame))
                  (frame-p (frame->frame frame))
                  (valid-seqp frame seq)
                  (<= (nfix n) (len seq))
                  (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                  (nat-listp seq)
                  (mv-nth '1 (collapse frame)))
             (absfat-equiv-upto-n frame seq n))
    :hints
    (("goal"
      :in-theory
      (e/d
       (absfat-equiv-upto-n (:rewrite partial-collapse-correctness-lemma-63)
                            (:rewrite partial-collapse-correctness-lemma-53)))
      :induct (dec-induct n)))))

(defthm
  partial-collapse-correctness-lemma-59
  (implies (and (abs-separate (frame->frame frame))
                (frame-p (frame->frame frame))
                (valid-seqp frame seq)
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (nat-listp seq)
                (mv-nth '1 (collapse frame)))
           (absfat-equiv-upto-n frame seq (len seq))))

(defthm
  partial-collapse-correctness-lemma-130
  (implies (and (abs-separate (frame->frame frame))
                (frame-p (frame->frame frame))
                (valid-seqp frame seq)
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (nat-listp seq)
                (mv-nth '1 (collapse frame))
                (member-equal x seq))
           (absfat-equiv (final-val-seq x frame seq)
                         (final-val x frame)))
  :hints (("goal" :in-theory (disable partial-collapse-correctness-lemma-59
                                      absfat-equiv-upto-n-correctness-1)
           :use ((:instance absfat-equiv-upto-n-correctness-1
                            (n (len seq)))
                 partial-collapse-correctness-lemma-59))))

(defthm
  partial-collapse-correctness-lemma-60
  (implies
   (and (<= (nfix n) (len (frame->frame frame)))
        (abs-separate (frame->frame frame))
        (dist-names (frame->root frame)
                    nil (frame->frame frame))
        (frame-p (frame->frame frame))
        (mv-nth 1 (collapse frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (and (equal (frame->root (collapse-iter frame n))
               (mv-nth 0
                       (ctx-app-list (frame->root frame)
                                     nil
                                     frame (frame-addrs-before frame 0 n))))
        (mv-nth 1
                (ctx-app-list (frame->root frame)
                              nil
                              frame (frame-addrs-before frame 0 n)))))
  :hints
  (("goal" :induct (collapse-iter frame n)
    :in-theory
    (e/d (collapse-iter frame-addrs-before
                        ctx-app-list collapse)
         ((:definition no-duplicatesp-equal)
          (:definition member-equal)
          (:rewrite nthcdr-when->=-n-len-l)
          (:definition strip-cars)
          (:rewrite partial-collapse-correctness-lemma-24)
          (:definition remove-assoc-equal)
          (:rewrite 1st-complete-of-remove-assoc-2)
          (:rewrite final-val-of-collapse-this-lemma-3)
          (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8 . 1)
          (:type-prescription abs-fs-fix-of-put-assoc-equal-lemma-3)
          (:rewrite 1st-complete-of-put-assoc-lemma-1)
          (:definition len)
          (:rewrite partial-collapse-correctness-lemma-1))))))

(defthmd
  partial-collapse-correctness-lemma-87
  (implies
   (and
    (abs-separate (frame->frame frame))
    (frame-p (frame->frame frame))
    (mv-nth 1 (collapse frame))
    (absfat-equiv
     (mv-nth
      0
      (ctx-app-list-seq (frame->root frame)
                        nil frame
                        (frame-addrs-before-seq frame 0 (take (+ -1 n) seq))
                        seq))
     (mv-nth
      0
      (ctx-app-list (frame->root frame)
                    nil frame
                    (frame-addrs-before-seq frame 0 (take (+ -1 n) seq)))))
    (valid-seqp frame seq)
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (nat-listp seq)
    (<= n (len seq)))
   (absfat-equiv
    (mv-nth
     0
     (ctx-app-list-seq
      (mv-nth
       0
       (ctx-app-list-seq
        (frame->root frame)
        nil frame
        (frame-addrs-before-seq frame 0 (take (+ -1 n) (take n seq)))
        seq))
      nil frame
      (frame-addrs-before-seq frame 0 (nthcdr (+ -1 n) (take n seq)))
      seq))
    (mv-nth
     0
     (ctx-app-list
      (mv-nth
       0
       (ctx-app-list
        (frame->root frame)
        nil frame
        (frame-addrs-before-seq frame 0 (take (+ -1 n) (take n seq)))))
      nil frame
      (frame-addrs-before-seq frame
                              0 (nthcdr (+ -1 n) (take n seq)))))))
  :hints (("goal" :in-theory (enable frame-addrs-before-seq
                                     ctx-app-list-seq ctx-app-list)
           :use (:instance (:rewrite take-of-nthcdr)
                           (l seq)
                           (n2 (+ -1 n))
                           (n1 1)))))

(defthm
  partial-collapse-correctness-lemma-41
  (implies
   (mv-nth 1
           (ctx-app-list-seq (frame->root frame)
                             nil frame
                             (frame-addrs-before-seq frame 0 (take n seq))
                             seq))
   (mv-nth
    1
    (ctx-app-list-seq (frame->root frame)
                      nil frame
                      (frame-addrs-before-seq frame 0 (take (+ -1 n) seq))
                      seq)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (frame-addrs-before-seq ctx-app-list-seq ctx-app-list)
                    ((:rewrite binary-append-take-nthcdr)
                     (:rewrite frame-addrs-before-seq-of-append)))
    :use ((:instance (:rewrite binary-append-take-nthcdr)
                     (l (take n seq))
                     (i (+ -1 n)))
          (:instance (:rewrite frame-addrs-before-seq-of-append)
                     (l2 (nthcdr (+ -1 n) (take n seq)))
                     (l1 (take (+ -1 n) (take n seq)))
                     (x 0)
                     (frame frame))))))

(defthm
  partial-collapse-correctness-lemma-38
  (implies
   (mv-nth 1
           (ctx-app-list (frame->root frame)
                         nil frame
                         (frame-addrs-before-seq frame 0 (take n seq))))
   (mv-nth
    1
    (ctx-app-list (frame->root frame)
                  nil frame
                  (frame-addrs-before-seq frame 0 (take (+ -1 n) seq)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (frame-addrs-before-seq ctx-app-list-seq ctx-app-list)
                    ((:rewrite binary-append-take-nthcdr)
                     (:rewrite frame-addrs-before-seq-of-append)))
    :use ((:instance (:rewrite binary-append-take-nthcdr)
                     (l (take n seq))
                     (i (+ -1 n)))
          (:instance (:rewrite frame-addrs-before-seq-of-append)
                     (l2 (nthcdr (+ -1 n) (take n seq)))
                     (l1 (take (+ -1 n) (take n seq)))
                     (x 0)
                     (frame frame))))))

(encapsulate
  ()

  (local (include-book "std/basic/inductions" :dir :system))

  (local
   (defthm
     lemma-3
     (implies
      (and
       (absfat-equiv
        (mv-nth
         0
         (ctx-app-list-seq (frame->root frame)
                           nil frame
                           (frame-addrs-before-seq frame 0 (take (+ -1 n) seq))
                           seq))
        (mv-nth
         0
         (ctx-app-list (frame->root frame)
                       nil frame
                       (frame-addrs-before-seq frame 0 (take (+ -1 n) seq)))))
       (abs-separate (frame->frame frame))
       (frame-p (frame->frame frame))
       (mv-nth 1 (collapse frame))
       (valid-seqp frame seq)
       (no-duplicatesp-equal (strip-cars (frame->frame frame)))
       (nat-listp seq)
       (<= n (len seq)))
      (absfat-equiv
       (mv-nth 0
               (ctx-app-list-seq (frame->root frame)
                                 nil frame
                                 (frame-addrs-before-seq frame 0 (take n seq))
                                 seq))
       (mv-nth 0
               (ctx-app-list (frame->root frame)
                             nil frame
                             (frame-addrs-before-seq frame 0 (take n seq))))))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory (e/d (frame-addrs-before-seq ctx-app-list-seq ctx-app-list)
                       ((:rewrite binary-append-take-nthcdr)
                        (:rewrite frame-addrs-before-seq-of-append)))
       :use ((:instance (:rewrite binary-append-take-nthcdr)
                        (l (take n seq))
                        (i (+ -1 n)))
             (:instance (:rewrite frame-addrs-before-seq-of-append)
                        (l2 (nthcdr (+ -1 n) (take n seq)))
                        (l1 (take (+ -1 n) (take n seq)))
                        (x 0)
                        (frame frame))
             partial-collapse-correctness-lemma-87)))))

  (defthm
    partial-collapse-correctness-lemma-43
    (implies
     (and (abs-separate (frame->frame frame))
          (frame-p (frame->frame frame))
          (mv-nth '1 (collapse frame))
          (valid-seqp frame seq)
          (no-duplicatesp-equal (strip-cars (frame->frame frame)))
          (nat-listp seq)
          (<= n (len seq)))
     (absfat-equiv
      (mv-nth 0
              (ctx-app-list-seq (frame->root frame)
                                nil frame
                                (frame-addrs-before-seq frame 0 (take n seq))
                                seq))
      (mv-nth 0
              (ctx-app-list (frame->root frame)
                            nil frame
                            (frame-addrs-before-seq frame 0 (take n seq))))))
    :hints
    (("goal"
      :in-theory (e/d (frame-addrs-before-seq ctx-app-list ctx-app-list-seq)
                      ((:definition member-equal)
                       (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)))
      :induct (dec-induct n))))

  (local
   (defthm
     lemma-2
     (implies
      (and
       (not (zp n))
       (mv-nth
        1
        (ctx-app-list (frame->root frame)
                      nil frame
                      (frame-addrs-before-seq frame 0 (take (+ -1 n) seq))))
       (abs-separate (frame->frame frame))
       (frame-p (frame->frame frame))
       (mv-nth 1 (collapse frame))
       (valid-seqp frame seq)
       (no-duplicatesp-equal (strip-cars (frame->frame frame)))
       (nat-listp seq)
       (<= n (len seq))
       (mv-nth 1
               (ctx-app-list-seq (frame->root frame)
                                 nil frame
                                 (frame-addrs-before-seq frame 0 (take n seq))
                                 seq)))
      (mv-nth 1
              (ctx-app-list (frame->root frame)
                            nil frame
                            (frame-addrs-before-seq frame 0 (take n seq)))))
     :hints
     (("goal"
       :do-not-induct t
       :in-theory (e/d (frame-addrs-before-seq ctx-app-list-seq ctx-app-list)
                       ((:rewrite binary-append-take-nthcdr)
                        (:rewrite frame-addrs-before-seq-of-append)
                        (:rewrite member-equal-nth-take-when-no-duplicatesp)
                        (:rewrite ctx-app-ok-of-ctx-app-list-seq)
                        ctx-app-ok-of-ctx-app-list-seq-lemma-1))
       :use ((:instance (:rewrite binary-append-take-nthcdr)
                        (l (take n seq))
                        (i (+ -1 n)))
             (:instance (:rewrite frame-addrs-before-seq-of-append)
                        (l2 (nthcdr (+ -1 n) (take n seq)))
                        (l1 (take (+ -1 n) (take n seq)))
                        (x 0)
                        (frame frame))
             (:instance (:rewrite take-of-nthcdr)
                        (l seq)
                        (n2 (+ -1 n))
                        (n1 1)))))))

  (local
   (defthm
     lemma-1
     (implies
      (and
       (not (zp n))
       (mv-nth
        1
        (ctx-app-list-seq (frame->root frame)
                          nil frame
                          (frame-addrs-before-seq frame 0 (take (+ -1 n) seq))
                          seq))
       (mv-nth
        1
        (ctx-app-list (frame->root frame)
                      nil frame
                      (frame-addrs-before-seq frame 0 (take (+ -1 n) seq))))
       (abs-separate (frame->frame frame))
       (frame-p (frame->frame frame))
       (mv-nth 1 (collapse frame))
       (valid-seqp frame seq)
       (no-duplicatesp-equal (strip-cars (frame->frame frame)))
       (nat-listp seq)
       (<= n (len seq))
       (mv-nth 1
               (ctx-app-list (frame->root frame)
                             nil frame
                             (frame-addrs-before-seq frame 0 (take n seq)))))
      (mv-nth 1
              (ctx-app-list-seq (frame->root frame)
                                nil frame
                                (frame-addrs-before-seq frame 0 (take n seq))
                                seq)))
     :instructions
     ((:bash
       ("goal"
        :do-not-induct t
        :in-theory (e/d (frame-addrs-before-seq ctx-app-list-seq ctx-app-list)
                        ((:rewrite binary-append-take-nthcdr)
                         (:rewrite frame-addrs-before-seq-of-append)
                         (:rewrite member-equal-nth-take-when-no-duplicatesp)
                         (:rewrite ctx-app-ok-of-ctx-app-list-seq)
                         ctx-app-ok-of-ctx-app-list-seq-lemma-1))
        :use ((:instance (:rewrite binary-append-take-nthcdr)
                         (l (take n seq))
                         (i (+ -1 n)))
              (:instance (:rewrite frame-addrs-before-seq-of-append)
                         (l2 (nthcdr (+ -1 n) (take n seq)))
                         (l1 (take (+ -1 n) (take n seq)))
                         (x 0)
                         (frame frame))
              partial-collapse-correctness-lemma-87)))
      (:dive 2 4)
      := :up
      (:rewrite ctx-app-list-seq-of-append)
      :top :s (:contrapose 15)
      (:dive 1 2 4)
      :=
      :up (:rewrite ctx-app-list-of-append)
      :top (:bash ("goal" :in-theory (e/d (frame-addrs-before-seq
                                           ctx-app-list-seq ctx-app-list)
                                          ((:rewrite member-equal-nth-take-when-no-duplicatesp)
                                           (:rewrite ctx-app-ok-of-ctx-app-list-seq)
                                           ctx-app-ok-of-ctx-app-list-seq-lemma-1))
                   :use (:instance (:rewrite take-of-nthcdr)
                                   (l seq)
                                   (n2 (+ -1 n))
                                   (n1 1)))))))

  (defthm
    partial-collapse-correctness-lemma-39
    (implies
     (and
      (abs-separate (frame->frame frame))
      (frame-p (frame->frame frame))
      (mv-nth '1 (collapse frame))
      (valid-seqp frame seq)
      (no-duplicatesp-equal (strip-cars (frame->frame frame)))
      (nat-listp seq)
      (<= n (len seq)))
     (iff
      (mv-nth 1
              (ctx-app-list-seq (frame->root frame)
                                nil frame
                                (frame-addrs-before-seq frame 0 (take n seq))
                                seq))
      (mv-nth 1
              (ctx-app-list (frame->root frame)
                            nil frame
                            (frame-addrs-before-seq frame 0 (take n seq))))))
    :hints
    (("goal"
      :in-theory (e/d (frame-addrs-before-seq ctx-app-list ctx-app-list-seq)
                      ((:definition member-equal)
                       (:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)))
      :induct (dec-induct n)))))

(defthm partial-collapse-correctness-lemma-44
  (implies (atom (frame->frame frame))
           (iff (valid-seqp frame seq) (atom seq)))
  :hints (("goal" :in-theory (enable valid-seqp collapse-seq))))

(encapsulate
  ()

  (local
   (in-theory (e/d (collapse-seq frame-addrs-before-seq
                                 ctx-app-list-seq collapse)
                   ((:definition no-duplicatesp-equal)
                    (:definition member-equal)
                    (:rewrite nthcdr-when->=-n-len-l)
                    (:definition remove-assoc-equal)
                    (:definition len)))))

  (defthmd
    partial-collapse-correctness-lemma-131
    (implies
     (and (abs-separate (frame->frame frame))
          (dist-names (frame->root frame)
                      nil (frame->frame frame))
          (frame-p (frame->frame frame))
          (valid-seqp frame seq)
          (no-duplicatesp-equal (strip-cars (frame->frame frame)))
          (nat-listp seq))
     (and (equal (frame->root (collapse-seq frame seq))
                 (mv-nth 0
                         (ctx-app-list-seq (frame->root frame)
                                           nil frame
                                           (frame-addrs-before-seq frame 0 seq)
                                           seq)))
          (mv-nth 1
                  (ctx-app-list-seq (frame->root frame)
                                    nil frame
                                    (frame-addrs-before-seq frame 0 seq)
                                    seq))))
    :hints (("goal" :induct (collapse-seq frame seq)
             :in-theory (enable partial-collapse-correctness-lemma-71)))))

(defthmd
  partial-collapse-correctness-lemma-135
  (implies (and (abs-separate (frame->frame frame))
                (dist-names (frame->root frame)
                            nil (frame->frame frame))
                (frame-p (frame->frame frame))
                (valid-seqp frame seq)
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (nat-listp seq)
                (mv-nth 1 (collapse frame)))
           (and
            (absfat-equiv
             (frame->root (collapse-seq frame seq))
             (mv-nth 0
                     (ctx-app-list (frame->root frame)
                                   nil frame
                                   (frame-addrs-before-seq frame 0 seq))))
            (mv-nth 1
                    (ctx-app-list (frame->root frame)
                                  nil frame
                                  (frame-addrs-before-seq frame 0 seq)))))
  :hints
  (("goal"
    :in-theory (disable partial-collapse-correctness-lemma-131
                        (:rewrite partial-collapse-correctness-lemma-43)
                        partial-collapse-correctness-lemma-39)
    :use (partial-collapse-correctness-lemma-131
          (:instance (:rewrite partial-collapse-correctness-lemma-43)
                     (seq seq)
                     (n (len seq))
                     (frame frame))
          (:instance
           partial-collapse-correctness-lemma-39
           (seq seq)
           (n (len seq))
           (frame frame))))))

(defthm
  partial-collapse-correctness-lemma-49
  (implies
   (mv-nth 1 (collapse frame))
   (or
    (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
           0)
    (and
     (consp
      (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                   (frame->frame frame)))
     (not (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                 x)))))
  :hints (("goal" :in-theory (enable collapse)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies (and (mv-nth 1 (collapse frame))
                  (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                  (consp (assoc-equal x (frame->frame frame)))
                  (not (zp x)))
             (equal (len (frame->frame (collapse-this frame x)))
                    (+ -1 (len (frame->frame frame)))))
    :hints
    (("goal"
      :cases
      ((equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
              0)))))))

(defthm
  partial-collapse-correctness-lemma-46
  (implies
   (and
    (abs-separate (frame->frame frame))
    (frame-p (frame->frame frame))
    (mv-nth 1 (collapse frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (< 0
       (1st-complete (frame->frame (collapse-this frame x))))
    (not (equal (1st-complete (frame->frame (collapse-this frame x)))
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
    (< 0
       (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
    (equal
     (frame-val->src
      (cdr (assoc-equal (1st-complete (frame->frame (collapse-this frame x)))
                        (frame->frame frame))))
     (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
   (ctx-app-ok
    (frame-val->dir
     (cdr
      (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                   (frame->frame frame))))
    (1st-complete (frame->frame (collapse-this frame x)))
    (nthcdr
     (len
      (frame-val->path
       (cdr (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame)))))
     (frame-val->path
      (cdr (assoc-equal (1st-complete (frame->frame (collapse-this frame x)))
                        (frame->frame frame)))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-15))
    :use
    (:instance
     (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-15)
     (relpath
      (nthcdr
       (len
        (frame-val->path
         (cdr
          (assoc-equal
           (frame-val->src
            (cdr (assoc-equal
                  (1st-complete (frame->frame (collapse-this frame x)))
                  (frame->frame frame))))
           (frame->frame frame)))))
       (frame-val->path
        (cdr
         (assoc-equal (1st-complete (frame->frame (collapse-this frame x)))
                      (frame->frame frame))))))
     (frame frame)
     (x (1st-complete (frame->frame (collapse-this frame x))))))))

(defthm
  partial-collapse-correctness-lemma-50
  (implies (and (not (zp n))
                (frame-p (frame->frame frame))
                (mv-nth 1 (collapse frame))
                (<= n
                    (len (seq-this (collapse-this frame x)))))
           (consp (assoc-equal (nth (+ -1 n)
                                    (seq-this (collapse-this frame x)))
                               (frame->frame frame))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite subsetp-trans)
                        (:rewrite subsetp-member . 1))
    :use
    ((:instance (:rewrite subsetp-member . 1)
                (y (strip-cars (frame->frame frame)))
                (a (nth (+ -1 n)
                        (seq-this (collapse-this frame x))))
                (x (seq-this (collapse-this frame x))))
     (:instance (:rewrite subsetp-trans)
                (z (strip-cars (frame->frame frame)))
                (x x)
                (y (strip-cars (frame->frame (collapse-this frame x)))))))))

(defthm
  partial-collapse-correctness-lemma-47
  (implies (and (mv-nth 1 (collapse frame))
                (not (zp x)))
           (not (equal (nth (+ -1 n)
                            (seq-this (collapse-this frame x)))
                       x)))
  :hints (("goal" :in-theory (disable (:rewrite member-equal-nth))
           :use (:instance (:rewrite member-equal-nth)
                           (l (seq-this (collapse-this frame x)))
                           (n (+ -1 n))))))

(defthm
  partial-collapse-correctness-lemma-42
  (implies
   (equal (nth (+ -1 n)
               (seq-this (collapse-this frame x)))
          (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
   (and
    (equal
     (frame-val->path
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
        (frame->frame
         (collapse-seq (collapse-this frame x)
                       (take (+ -1 n)
                             (seq-this (collapse-this frame x))))))))
     (frame-val->path
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame (collapse-this frame x))))))
    (equal
     (frame-val->src
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
        (frame->frame
         (collapse-seq (collapse-this frame x)
                       (take (+ -1 n)
                             (seq-this (collapse-this frame x))))))))
     (frame-val->src
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame (collapse-this frame x))))))
    (iff
     (consp
      (assoc-equal
       (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
       (frame->frame
        (collapse-seq (collapse-this frame x)
                      (take (+ -1 n)
                            (seq-this (collapse-this frame x)))))))
     (consp
      (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                   (frame->frame (collapse-this frame x)))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite member-equal-nth-take-when-no-duplicatesp))
    :use (:instance (:rewrite member-equal-nth-take-when-no-duplicatesp)
                    (l (seq-this (collapse-this frame x)))
                    (n (+ -1 n))
                    (x (nth (+ -1 n) (seq-this (collapse-this frame x))))))))

(defthmd
  partial-collapse-correctness-lemma-152
  (implies (and (not (member-equal x2
                                   (frame-addrs-before-seq frame 0 seq)))
                (abs-separate (frame->frame frame))
                (dist-names (frame->root frame)
                            nil (frame->frame frame))
                (frame-p (frame->frame frame))
                (valid-seqp frame seq)
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (nat-listp seq))
           (iff (ctx-app-ok (frame->root (collapse-seq frame seq))
                            x2 x2-path)
                (ctx-app-ok (frame->root frame)
                            x2 x2-path)))
  :hints (("goal" :in-theory (disable partial-collapse-correctness-lemma-131)
           :use partial-collapse-correctness-lemma-131)))

(defthm
  partial-collapse-correctness-lemma-153
  (implies
   (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (< (nfix n) (len (seq-this frame))))
   (equal
    (abs-addrs
     (frame-val->dir
      (cdr
       (assoc-equal
        (nth n (seq-this frame))
        (frame->frame (collapse-seq frame (take n (seq-this frame))))))))
    nil))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d nil
                    ((:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-9)))
    :use
    (nth-of-seq-this
     (:instance
      (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-9)
      (frame
       (frame->frame (collapse-seq frame (take n (seq-this frame))))))))))

(defthm
  partial-collapse-correctness-lemma-65
  (implies
   (and (not (member-equal x2
                           (frame-addrs-before-seq frame x seq)))
        (abs-separate (frame->frame frame))
        (frame-p (frame->frame frame))
        (consp (assoc-equal x
                            (frame->frame (collapse-seq frame seq))))
        (valid-seqp frame seq)
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (nat-listp seq))
   (iff
    (ctx-app-ok
     (frame-val->dir
      (cdr (assoc-equal x
                        (frame->frame (collapse-seq frame seq)))))
     x2 x2-path)
    (ctx-app-ok (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
                x2 x2-path)))
  :hints (("goal" :in-theory (disable partial-collapse-correctness-lemma-61)
           :use partial-collapse-correctness-lemma-61)))

(defthm
  partial-collapse-correctness-lemma-155
  (implies
   (equal (nth (+ -1 n)
               (seq-this (collapse-this frame x)))
          (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
   (not
    (member-equal
     (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
     (frame-addrs-before-seq (collapse-this frame x)
                             0
                             (take (binary-+ -1 n)
                                   (seq-this (collapse-this frame x)))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (disable (:rewrite member-equal-nth-take-when-no-duplicatesp))
    :use (:instance (:rewrite member-equal-nth-take-when-no-duplicatesp)
                    (x (nth (+ -1 n) (seq-this (collapse-this frame x))))
                    (l (seq-this (collapse-this frame x)))
                    (n (+ -1 n))))))

(defthm
  partial-collapse-correctness-lemma-115
  (implies
   (and
    (ctx-app-ok
     (frame-val->dir
      (cdr
       (assoc-equal
        (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                          (frame->frame frame))))
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
       (frame-val->dir (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))))))
   (not
    (equal
     (nth (+ -1 n)
          (seq-this (collapse-this frame
                                   (1st-complete (frame->frame frame)))))
     (1st-complete (frame->frame frame)))))
  :hints
  (("goal"
    :in-theory (e/d (seq-this collapse-iter collapse-seq)
                    ((:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
                     (:definition member-equal)
                     (:definition no-duplicatesp-equal)
                     (:definition remove-equal)
                     (:definition nthcdr)
                     (:definition assoc-equal)
                     (:rewrite nthcdr-when->=-n-len-l)
                     (:rewrite member-equal-nth)))
    :use
    (:instance
     (:rewrite member-equal-nth)
     (l (seq-this (collapse-this frame
                                 (1st-complete (frame->frame frame)))))
     (n (+ -1 n))))))

(defthm
  partial-collapse-correctness-lemma-157
  (implies
   (and (< (nfix n) (len (seq-this frame)))
        (not (zp (frame-val->src (cdr (assoc-equal (nth n (seq-this frame))
                                                   (frame->frame frame)))))))
   (consp
    (assoc-equal
     (frame-val->src (cdr (assoc-equal (nth n (seq-this frame))
                                       (frame->frame frame))))
     (frame->frame (collapse-seq frame (take n (seq-this frame)))))))
  :hints
  (("goal" :in-theory (e/d (seq-this collapse-iter collapse-seq member-of-take)
                           ((:rewrite ctx-app-ok-when-absfat-equiv-lemma-4)
                            (:definition member-equal)
                            (:definition no-duplicatesp-equal)
                            (:definition remove-equal)
                            (:definition nthcdr)
                            (:definition assoc-equal)
                            (:rewrite nthcdr-when->=-n-len-l)
                            (:rewrite member-equal-nth)))
    :induct (collapse-iter frame n)
    :expand ((seq-this frame)))))

(defthmd
  partial-collapse-correctness-lemma-69
  (implies
   (and (<= (nfix n) (len (seq-this frame)))
        (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (iff
    (consp
     (assoc-equal
      x
      (frame->frame (collapse-seq frame (take n (seq-this frame))))))
    (and
     (consp (assoc-equal x (frame->frame frame)))
     (not (member-equal x (take n (seq-this frame)))))))
  :hints
  (("goal"
    :in-theory (e/d (seq-this collapse-seq collapse-iter)
                    ((:definition assoc-equal)
                     (:rewrite take-of-len-free)
                     (:rewrite partial-collapse-correctness-lemma-24)
                     (:definition member-equal)
                     (:rewrite nthcdr-when->=-n-len-l)
                     (:definition remove-equal)
                     (:rewrite remove-when-absent)
                     (:rewrite partial-collapse-correctness-lemma-20)
                     (:definition strip-cars)))
    :induct (collapse-iter frame n)
    :expand
    ((seq-this frame)
     (collapse-seq frame
                   (cons (1st-complete (frame->frame frame))
                         (take (+ -1 n)
                               (seq-this (collapse-iter frame 1)))))))))

(defthm
  partial-collapse-correctness-lemma-100
  (implies
   (and
    (< (nfix n) (len (seq-this frame)))
    (not (zp (frame-val->src
              (cdr (assoc-equal (nth n (seq-this frame))
                                (frame->frame frame))))))
    (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (not
    (member-equal
     (frame-val->src (cdr (assoc-equal (nth n (seq-this frame))
                                       (frame->frame frame))))
     (take n (seq-this frame)))))
  :hints
  (("goal"
    :in-theory (disable partial-collapse-correctness-lemma-157)
    :do-not-induct t
    :use
    ((:instance
      partial-collapse-correctness-lemma-69
      (x (frame-val->src
          (cdr (assoc-equal (nth n (seq-this frame))
                            (frame->frame frame))))))
     partial-collapse-correctness-lemma-157))))

(defthm
  partial-collapse-correctness-lemma-109
  (implies
   (and (frame-p (frame->frame frame))
        (not (zp (frame-val->src (cdr (assoc-equal (nth n (seq-this frame))
                                                   (frame->frame frame))))))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (abs-separate (frame->frame frame)))
   (ctx-app-ok
    (frame-val->dir
     (cdr
      (assoc-equal (frame-val->src (cdr (assoc-equal (nth n (seq-this frame))
                                                     (frame->frame frame))))
                   (frame->frame frame))))
    (nth n (seq-this frame))
    (nthcdr
     (len
      (frame-val->path
       (cdr (assoc-equal
             (frame-val->src (cdr (assoc-equal (nth n (seq-this frame))
                                               (frame->frame frame))))
             (frame->frame frame)))))
     (frame-val->path (cdr (assoc-equal (nth n (seq-this frame))
                                        (frame->frame frame)))))))
  :hints
  (("goal"
    :in-theory (e/d (seq-this collapse-iter collapse-seq)
                    ((:definition member-equal)
                     (:definition no-duplicatesp-equal)
                     (:definition remove-equal)
                     (:definition nthcdr)
                     (:definition assoc-equal)
                     (:rewrite member-equal-nth)
                     (:rewrite final-val-of-collapse-this-lemma-3)
                     (:linear nth-of-seq-this-1)
                     (:linear natp-of-nth-of-seq-this)
                     (:rewrite partial-collapse-correctness-lemma-20)
                     (:definition strip-cars)
                     (:rewrite m1-file-alist-p-of-final-val-seq-lemma-3)
                     (:rewrite abs-file-alist-p-correctness-1)
                     (:rewrite nth-of-seq-this-1)
                     (:rewrite natp-of-nth-of-seq-this)
                     (:rewrite remove-when-absent)
                     (:rewrite abs-addrs-of-ctx-app-2)
                     (:rewrite ctx-app-when-not-ctx-app-ok)
                     (:linear position-when-member)))
    :induct (collapse-iter frame n)
    :expand ((seq-this frame)))))

(defthm
  partial-collapse-correctness-lemma-52
  (implies
   (and (abs-separate (frame->frame frame))
        (frame-p (frame->frame frame))
        (mv-nth 1 (collapse frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (< 0
           (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
        (equal (frame-val->src
                (cdr (assoc-equal (nth (+ -1 n)
                                       (seq-this (collapse-this frame x)))
                                  (frame->frame frame))))
               (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
   (ctx-app-ok
    (frame-val->dir
     (cdr
      (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                   (frame->frame frame))))
    (nth (+ -1 n)
         (seq-this (collapse-this frame x)))
    (nthcdr
     (len
      (frame-val->path
       (cdr (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame)))))
     (frame-val->path
      (cdr (assoc-equal (nth (+ -1 n)
                             (seq-this (collapse-this frame x)))
                        (frame->frame frame)))))))
  :instructions
  (:promote
   (:=
    (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
    (frame-val->src (cdr (assoc-equal (nth (+ -1 n)
                                           (seq-this (collapse-this frame x)))
                                      (frame->frame frame)))))
   (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-15)))

(defthm
  partial-collapse-correctness-lemma-66
  (implies
   (and
    (mv-nth 1 (collapse frame))
    (not (zp x))
    (<= n
        (len (seq-this (collapse-this frame x))))
    (< 0
       (nth (+ -1 n)
            (seq-this (collapse-this frame x))))
    (not (equal (nth (+ -1 n)
                     (seq-this (collapse-this frame x)))
                (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
    (< 0
       (frame-val->src
        (cdr (assoc-equal (nth (+ -1 n)
                               (seq-this (collapse-this frame x)))
                          (frame->frame frame))))))
   (consp
    (assoc-equal
     (frame-val->src
      (cdr (assoc-equal (nth (+ -1 n)
                             (seq-this (collapse-this frame x)))
                        (frame->frame frame))))
     (frame->frame
      (collapse-seq (collapse-this frame x)
                    (take (+ -1 n)
                          (seq-this (collapse-this frame x))))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite partial-collapse-correctness-lemma-157))
    :use (:instance (:rewrite partial-collapse-correctness-lemma-157)
                    (frame (collapse-this frame x))
                    (n (+ -1 n))))))

(defthm
  partial-collapse-correctness-lemma-163
  (implies
   (consp (assoc-equal y
                       (frame->frame (collapse-seq frame seq))))
   (and
    (equal (frame-val->src
            (cdr (assoc-equal y
                              (frame->frame (collapse-seq frame seq)))))
           (frame-val->src (cdr (assoc-equal y (frame->frame frame)))))
    (equal (frame-val->path
            (cdr (assoc-equal y
                              (frame->frame (collapse-seq frame seq)))))
           (frame-val->path (cdr (assoc-equal y (frame->frame frame)))))))
  :hints (("goal" :in-theory (enable collapse-seq))))

(defthm
  partial-collapse-correctness-lemma-164
  (implies
   (and (equal (frame-val->src
                (cdr (assoc-equal (nth (+ -1 n)
                                       (seq-this (collapse-this frame x)))
                                  (frame->frame frame))))
               (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
        (frame-p (frame->frame frame))
        (mv-nth 1 (collapse frame))
        (consp (assoc-equal x (frame->frame frame)))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (<= n
            (len (seq-this (collapse-this frame x))))
        (< 0
           (nth (+ -1 n)
                (seq-this (collapse-this frame x))))
        (< 0
           (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
   (consp
    (assoc-equal
     (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
     (frame->frame
      (collapse-seq (collapse-this frame x)
                    (take (+ -1 n)
                          (seq-this (collapse-this frame x))))))))
  :hints
  (("goal" :in-theory (e/d (valid-seqp collapse-seq seq-this
                                       subsetp-when-atom-set-difference$
                                       partial-collapse-correctness-lemma-152)
                           ((:rewrite partial-collapse-correctness-lemma-66)
                            collapse-seq-of-collapse-seq
                            take set-difference-equal
                            partial-collapse-correctness-lemma-61
                            (:definition member-equal)
                            (:rewrite partial-collapse-correctness-lemma-28)
                            (:definition assoc-equal)
                            (:definition no-duplicatesp-equal)
                            (:rewrite final-val-seq-of-collapse-this-lemma-2)
                            (:rewrite partial-collapse-correctness-lemma-83)
                            (:rewrite nthcdr-when->=-n-len-l)
                            (:rewrite m1-file-alist-p-of-final-val-seq-lemma-2)))
    :use (:rewrite partial-collapse-correctness-lemma-66))))

(defthm
  partial-collapse-correctness-lemma-64
  (implies
   (and
    (not (zp n))
    (equal
     (len
      (frame->frame (collapse-seq (collapse-this frame x)
                                  (take (+ -1 n)
                                        (seq-this (collapse-this frame x))))))
     (+ (- n) (len (frame->frame frame))))
    (abs-separate (frame->frame frame))
    (frame-p (frame->frame frame))
    (mv-nth 1 (collapse frame))
    (consp (assoc-equal x (frame->frame frame)))
    (not
     (consp
      (abs-addrs
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (<= n
        (len (seq-this (collapse-this frame x))))
    (< 0
       (nth (+ -1 n)
            (seq-this (collapse-this frame x))))
    (< 0
       (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
    (equal (frame-val->src
            (cdr (assoc-equal (nth (+ -1 n)
                                   (seq-this (collapse-this frame x)))
                              (frame->frame frame))))
           (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
   (ctx-app-ok
    (frame-val->dir
     (cdr
      (assoc-equal
       (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
       (frame->frame
        (collapse-seq (collapse-this frame x)
                      (take (+ -1 n)
                            (seq-this (collapse-this frame x))))))))
    (nth (+ -1 n)
         (seq-this (collapse-this frame x)))
    (nthcdr
     (len
      (frame-val->path
       (cdr (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame)))))
     (frame-val->path
      (cdr (assoc-equal (nth (+ -1 n)
                             (seq-this (collapse-this frame x)))
                        (frame->frame frame)))))))
  :hints
  (("goal"
    :in-theory (e/d (valid-seqp collapse-seq seq-this
                                subsetp-when-atom-set-difference$
                                partial-collapse-correctness-lemma-152)
                    ((:rewrite partial-collapse-correctness-lemma-65)
                     collapse-seq-of-collapse-seq
                     take set-difference-equal
                     partial-collapse-correctness-lemma-61
                     (:definition member-equal)
                     (:rewrite partial-collapse-correctness-lemma-28)
                     (:definition assoc-equal)
                     (:definition no-duplicatesp-equal)
                     (:rewrite final-val-seq-of-collapse-this-lemma-2)
                     (:rewrite partial-collapse-correctness-lemma-83)
                     (:rewrite nthcdr-when->=-n-len-l)
                     (:rewrite m1-file-alist-p-of-final-val-seq-lemma-2)))
    :use
    (:instance
     (:rewrite partial-collapse-correctness-lemma-65)
     (x2-path
      (nthcdr
       (len
        (frame-val->path
         (cdr
          (assoc-equal
           (frame-val->src
            (cdr (assoc-equal (nth (+ -1 n)
                                   (seq-this (collapse-this frame x)))
                              (frame->frame frame))))
           (frame->frame frame)))))
       (frame-val->path
        (cdr (assoc-equal (nth (+ -1 n)
                               (seq-this (collapse-this frame x)))
                          (frame->frame frame))))))
     (x2 (nth (+ -1 n)
              (seq-this (collapse-this frame x))))
     (seq (take (+ -1 n)
                (seq-this (collapse-this frame x))))
     (frame (collapse-this frame x))
     (x (frame-val->src
         (cdr (assoc-equal (nth (+ -1 n)
                                (seq-this (collapse-this frame x)))
                           (frame->frame frame)))))))))

(defthm
  partial-collapse-correctness-lemma-166
  (implies
   (and
    (equal (frame-val->src
            (cdr (assoc-equal (nth (+ -1 n)
                                   (seq-this (collapse-this frame x)))
                              (frame->frame frame))))
           0)
    (not (zp n))
    (equal
     (len
      (frame->frame (collapse-seq (collapse-this frame x)
                                  (take (+ -1 n)
                                        (seq-this (collapse-this frame x))))))
     (+ (- n) (len (frame->frame frame))))
    (abs-separate (frame->frame frame))
    (frame-p (frame->frame frame))
    (dist-names (frame->root frame)
                nil (frame->frame frame))
    (mv-nth 1 (collapse frame))
    (consp (assoc-equal x (frame->frame frame)))
    (not
     (consp
      (abs-addrs
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (<= n
        (len (seq-this (collapse-this frame x)))))
   (ctx-app-ok
    (frame->root (collapse-seq (collapse-this frame x)
                               (take (+ -1 n)
                                     (seq-this (collapse-this frame x)))))
    (nth (+ -1 n)
         (seq-this (collapse-this frame x)))
    (frame-val->path
     (cdr (assoc-equal (nth (+ -1 n)
                            (seq-this (collapse-this frame x)))
                       (frame->frame frame))))))
  :hints
  (("goal"
    :in-theory (e/d (valid-seqp collapse-seq seq-this
                                subsetp-when-atom-set-difference$
                                partial-collapse-correctness-lemma-152)
                    (collapse-seq-of-collapse-seq
                     take set-difference-equal
                     partial-collapse-correctness-lemma-61
                     (:definition member-equal)
                     (:rewrite partial-collapse-correctness-lemma-28)
                     (:definition assoc-equal)
                     (:definition no-duplicatesp-equal)
                     (:rewrite final-val-seq-of-collapse-this-lemma-2)
                     (:rewrite partial-collapse-correctness-lemma-83)
                     (:rewrite nthcdr-when->=-n-len-l)
                     (:rewrite m1-file-alist-p-of-final-val-seq-lemma-2)))
    :expand
    (:with
     partial-collapse-correctness-lemma-152
     (ctx-app-ok
      (frame->root (collapse-seq (collapse-this frame x)
                                 (take (binary-+ '-1 n)
                                       (seq-this (collapse-this frame x)))))
      (nth (binary-+ '-1 n)
           (seq-this (collapse-this frame x)))
      (frame-val->path$inline
       (cdr (assoc-equal (nth (binary-+ '-1 n)
                              (seq-this (collapse-this frame x)))
                         (frame->frame frame))))))
    :do-not-induct t)))

(defthm
  partial-collapse-correctness-lemma-167
  (implies
   (and
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (equal (nth (+ -1 n)
                (seq-this (collapse-this frame x)))
           (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
    (<
     0
     (frame-val->src
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))))
   (not
    (member-equal
     (frame-val->src
      (cdr (assoc-equal
            (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
            (frame->frame frame))))
     (take (+ -1 n)
           (seq-this (collapse-this frame x))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite partial-collapse-correctness-lemma-100))
    :use (:instance (:rewrite partial-collapse-correctness-lemma-100)
                    (frame (collapse-this frame x))
                    (n (+ -1 n))))))

(defthm
  partial-collapse-correctness-lemma-103
  (implies
   (equal (nth (+ -1 n)
               (seq-this (collapse-this frame x)))
          (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
   (not
    (member-equal
     (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
     (frame-addrs-before-seq
      frame
      (frame-val->src$inline
       (cdr
        (assoc-equal
         (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
         (frame->frame frame))))
      (take (binary-+ -1 n)
            (seq-this (collapse-this frame x)))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite member-equal-nth-take-when-no-duplicatesp))
    :use (:instance (:rewrite member-equal-nth-take-when-no-duplicatesp)
                    (l (seq-this (collapse-this frame x)))
                    (n (+ -1 n))
                    (x (nth (+ -1 n) (seq-this (collapse-this frame x))))))))

(defthm
  partial-collapse-correctness-lemma-95
  (implies
   (and
    (equal
     (len
      (frame->frame (collapse-seq (collapse-this frame x)
                                  (take (+ -1 n)
                                        (seq-this (collapse-this frame x))))))
     (+ (- n) (len (frame->frame frame))))
    (mv-nth 1 (collapse frame))
    (not
     (consp
      (abs-addrs
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (< 0
       (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
    (equal (nth (+ -1 n)
                (seq-this (collapse-this frame x)))
           (frame-val->src (cdr (assoc-equal x (frame->frame frame))))))
   (equal
    (len
     (frame->frame
      (collapse-this
       (collapse-seq (collapse-this frame x)
                     (take (+ -1 n)
                           (seq-this (collapse-this frame x))))
       (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))))
    (+ -1 (- n)
       (len (frame->frame frame)))))
  :hints
  (("goal"
    :cases
    ((zp
      (frame-val->src
       (cdr
        (assoc-equal
         (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
         (frame->frame
          (collapse-seq (collapse-this frame x)
                        (take (+ -1 n)
                              (seq-this (collapse-this frame x)))))))))))))

(defthm
  partial-collapse-correctness-lemma-97
  (implies
   (and
    (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
           0)
    (not (zp n))
    (equal
     (len
      (frame->frame (collapse-seq (collapse-this frame x)
                                  (take (+ -1 n)
                                        (seq-this (collapse-this frame x))))))
     (+ (- n) (len (frame->frame frame))))
    (frame-p (frame->frame frame))
    (mv-nth 1 (collapse frame))
    (consp (assoc-equal x (frame->frame frame)))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (<= n
        (len (seq-this (collapse-this frame x))))
    (< 0
       (nth (+ -1 n)
            (seq-this (collapse-this frame x)))))
   (equal
    (len
     (frame->frame
      (collapse-this (collapse-seq (collapse-this frame x)
                                   (take (+ -1 n)
                                         (seq-this (collapse-this frame x))))
                     (nth (+ -1 n)
                          (seq-this (collapse-this frame x))))))
    (+ -1 (- n)
       (len (frame->frame frame)))))
  :hints
  (("goal"
    :cases
    ((equal
      (frame-val->src
       (cdr
        (assoc-equal
         (nth (+ -1 n)
              (seq-this (collapse-this frame x)))
         (frame->frame
          (collapse-seq (collapse-this frame x)
                        (take (+ -1 n)
                              (seq-this (collapse-this frame x))))))))
      0)))))

(defthm
  partial-collapse-correctness-lemma-105
  (implies
   (and
    (not (zp n))
    (equal
     (len
      (frame->frame (collapse-seq (collapse-this frame x)
                                  (take (+ -1 n)
                                        (seq-this (collapse-this frame x))))))
     (+ (- n) (len (frame->frame frame))))
    (abs-separate (frame->frame frame))
    (frame-p (frame->frame frame))
    (dist-names (frame->root frame)
                nil (frame->frame frame))
    (mv-nth 1 (collapse frame))
    (consp (assoc-equal x (frame->frame frame)))
    (not
     (consp
      (abs-addrs
       (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (<= n
        (len (seq-this (collapse-this frame x)))))
   (equal
    (len
     (frame->frame
      (collapse-seq (collapse-seq (collapse-this frame x)
                                  (take (+ -1 n)
                                        (seq-this (collapse-this frame x))))
                    (list (nth (+ -1 n)
                               (seq-this (collapse-this frame x)))))))
    (+ -1 (- n)
       (len (frame->frame frame)))))
  :hints
  (("goal"
    :in-theory (e/d (valid-seqp collapse-seq seq-this
                                subsetp-when-atom-set-difference$
                                partial-collapse-correctness-lemma-152)
                    (collapse-seq-of-collapse-seq
                     take set-difference-equal
                     partial-collapse-correctness-lemma-61
                     (:definition member-equal)
                     (:rewrite partial-collapse-correctness-lemma-28)
                     (:definition assoc-equal)
                     (:definition no-duplicatesp-equal)
                     (:rewrite final-val-seq-of-collapse-this-lemma-2)
                     (:rewrite partial-collapse-correctness-lemma-83)
                     (:rewrite nthcdr-when->=-n-len-l)
                     (:rewrite m1-file-alist-p-of-final-val-seq-lemma-2)
                     (:rewrite partial-collapse-correctness-lemma-114)
                     (:rewrite final-val-of-collapse-this-lemma-10)
                     (:rewrite no-duplicatesp-of-seq-this-lemma-1 . 2)
                     (:definition remove-equal)
                     (:rewrite remove-when-absent)
                     (:rewrite subsetp-of-remove1)))
    :expand
    (collapse-seq (collapse-seq (collapse-this frame x)
                                (take (+ -1 n)
                                      (seq-this (collapse-this frame x))))
                  (list (nth (+ -1 n)
                             (seq-this (collapse-this frame x)))))
    :do-not-induct t)))

(encapsulate
  ()

  (local (include-book "std/basic/inductions" :dir :system))

  (local
   (defthm
     lemma
     (implies (and (valid-seqp frame
                               (cons x
                                     (take (+ -1 n)
                                           (seq-this (collapse-this frame x)))))
                   (abs-separate (frame->frame frame))
                   (frame-p (frame->frame frame))
                   (dist-names (frame->root frame)
                               nil (frame->frame frame))
                   (mv-nth 1 (collapse frame))
                   (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                   (<= n
                       (len (seq-this (collapse-this frame x)))))
              (valid-seqp frame
                          (cons x
                                (take n (seq-this (collapse-this frame x))))))
     :hints
     (("goal"
       :in-theory (e/d (valid-seqp collapse-seq seq-this)
                       ((:rewrite binary-append-take-nthcdr)
                        (:rewrite collapse-seq-of-collapse-seq)
                        (:rewrite collapse-seq-of-collapse-seq)
                        (:rewrite
                         assoc-of-frame->frame-of-collapse-this)
                        (:rewrite
                         abs-separate-of-frame->frame-of-collapse-this-lemma-8
                         . 2)
                        (:rewrite
                         final-val-seq-of-collapse-this-lemma-2)
                        (:definition assoc-equal)
                        (:rewrite
                         partial-collapse-correctness-lemma-2)
                        (:rewrite
                         partial-collapse-correctness-lemma-163)
                        (:rewrite
                         partial-collapse-correctness-lemma-51)
                        (:rewrite
                         partial-collapse-correctness-lemma-61)
                        (:rewrite
                         partial-collapse-correctness-lemma-28)
                        (:rewrite
                         m1-file-alist-p-of-final-val-seq-lemma-2)
                        (:rewrite
                         partial-collapse-correctness-lemma-114)))
       :use
       ((:instance (:rewrite take-of-nthcdr)
                   (l (seq-this (collapse-this frame x)))
                   (n2 (+ -1 n))
                   (n1 1))
        (:instance (:rewrite collapse-seq-of-collapse-seq)
                   (seq2 (nthcdr (+ -1 n)
                                 (take n (seq-this (collapse-this frame x)))))
                   (seq1 (take (+ -1 n)
                               (take n (seq-this (collapse-this frame x)))))
                   (frame (collapse-this frame x))))))))

  (defthmd
    partial-collapse-correctness-lemma-45
    (implies
     (and
      (abs-separate (frame->frame frame))
      (frame-p (frame->frame frame))
      (dist-names (frame->root frame)
                  nil (frame->frame frame))
      (mv-nth 1 (collapse frame))
      (consp (assoc-equal x (frame->frame frame)))
      (abs-complete
       (frame-val->dir
        (cdr (assoc-equal x (frame->frame frame)))))
      (no-duplicatesp-equal (strip-cars (frame->frame frame)))
      (<= n
          (len (seq-this (collapse-this frame x)))))
     (valid-seqp
      frame
      (cons x
            (take n (seq-this (collapse-this frame x))))))
    :hints
    (("goal"
      :induct (dec-induct n)
      :in-theory (e/d (collapse-seq seq-this)
                      ((:rewrite binary-append-take-nthcdr)
                       (:rewrite collapse-seq-of-collapse-seq)))
      :expand (valid-seqp frame (list x))))))

(defthm
  valid-seqp-after-collapse-this
  (implies
   (and (abs-separate (frame->frame frame))
        (frame-p (frame->frame frame))
        (dist-names (frame->root frame)
                    nil (frame->frame frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (mv-nth 1 (collapse frame))
        (consp (assoc-equal x (frame->frame frame)))
        (abs-complete
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))))
   (valid-seqp frame
               (cons x (seq-this (collapse-this frame x)))))
  :hints
  (("goal" :do-not-induct t
    :use (:instance partial-collapse-correctness-lemma-45
                    (n (len (seq-this (collapse-this frame x))))))))

(defthmd
  partial-collapse-correctness-lemma-174
  (implies
   (and (abs-separate (frame->frame frame))
        (dist-names (frame->root frame)
                    nil (frame->frame frame))
        (frame-p (frame->frame frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (nat-listp (cons x (seq-this (collapse-this frame x))))
        (mv-nth 1 (collapse frame))
        (consp (assoc-equal x (frame->frame frame)))
        (abs-complete
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))))
   (and
    (absfat-equiv
     (frame->root (collapse-seq frame
                                (cons x (seq-this (collapse-this frame x)))))
     (mv-nth
      0
      (ctx-app-list
       (frame->root frame)
       nil frame
       (frame-addrs-before-seq frame 0
                               (cons x
                                     (seq-this (collapse-this frame x)))))))
    (mv-nth
     1
     (ctx-app-list
      (frame->root frame)
      nil frame
      (frame-addrs-before-seq frame 0
                              (cons x
                                    (seq-this (collapse-this frame x))))))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (disable valid-seqp-after-collapse-this)
    :use ((:instance partial-collapse-correctness-lemma-135
                     (seq (cons x (seq-this (collapse-this frame x)))))
          valid-seqp-after-collapse-this))))

(defthm
  partial-collapse-correctness-lemma-37
  (implies
   (and
    (equal
     (1st-complete
      (frame->frame
       (collapse-seq
        (collapse-this frame
                       (1st-complete (frame->frame frame)))
        (seq-this (collapse-this frame
                                 (1st-complete (frame->frame frame)))))))
     (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                       (frame->frame frame)))))
    (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (and
   (equal
    (frame-val->path
     (cdr
      (assoc-equal
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (frame->frame
        (collapse-seq
         (collapse-this frame
                        (1st-complete (frame->frame frame)))
         (seq-this (collapse-this frame
                                  (1st-complete (frame->frame frame)))))))))
    (frame-val->path
     (cdr
      (assoc-equal
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (frame->frame (collapse-this frame
                                    (1st-complete (frame->frame frame))))))))
   (equal
    (frame-val->src
     (cdr
      (assoc-equal
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (frame->frame
        (collapse-seq
         (collapse-this frame
                        (1st-complete (frame->frame frame)))
         (seq-this (collapse-this frame
                                  (1st-complete (frame->frame frame)))))))))
    (frame-val->src
     (cdr
      (assoc-equal
       (frame-val->src (cdr (assoc-equal (1st-complete (frame->frame frame))
                                         (frame->frame frame))))
       (frame->frame (collapse-this frame
                                    (1st-complete (frame->frame frame))))))))))
  :hints
  (("goal"
    :in-theory (disable (:rewrite 1st-complete-correctness-1))
    :use
    (:instance
     (:rewrite 1st-complete-correctness-1)
     (frame
      (frame->frame
       (collapse-seq
        (collapse-this frame
                       (1st-complete (frame->frame frame)))
        (seq-this (collapse-this frame
                                 (1st-complete (frame->frame frame)))))))))))

(defthmd
  partial-collapse-correctness-lemma-75
  (implies
   (no-duplicatesp-equal (strip-cars (frame->frame frame)))
   (b*
       ((frame (collapse-seq frame (seq-this frame)))
        (1st-complete (1st-complete (frame->frame frame))))
     (or
      (zp 1st-complete)
      (and
       (zp
        (frame-val->src (cdr (assoc-equal 1st-complete (frame->frame frame)))))
       (not (ctx-app-ok
             (frame->root frame)
             1st-complete
             (frame-val->path
              (cdr (assoc-equal 1st-complete (frame->frame frame)))))))
      (and
       (not (zp (frame-val->src
                 (cdr (assoc-equal 1st-complete (frame->frame frame))))))
       (not
        (and
         (prefixp
          (frame-val->path
           (cdr
            (assoc-equal
             (frame-val->src
              (cdr (assoc-equal 1st-complete (frame->frame frame))))
             (frame->frame frame))))
          (frame-val->path
           (cdr (assoc-equal 1st-complete (frame->frame frame)))))
         (ctx-app-ok
          (frame-val->dir
           (cdr
            (assoc-equal
             (frame-val->src
              (cdr (assoc-equal 1st-complete (frame->frame frame))))
             (frame->frame frame))))
          1st-complete
          (nthcdr
           (len
            (frame-val->path
             (cdr
              (assoc-equal
               (frame-val->src
                (cdr (assoc-equal 1st-complete (frame->frame frame))))
               (frame->frame frame)))))
           (frame-val->path (cdr (assoc-equal 1st-complete
                                              (frame->frame frame))))))))))))
  :hints
  (("goal" :in-theory (e/d (seq-this collapse-seq collapse-iter)
                           ((:rewrite partial-collapse-correctness-lemma-24)
                            (:definition no-duplicatesp-equal)
                            (:rewrite subsetp-when-prefixp)
                            (:definition assoc-equal)
                            (:definition member-equal)
                            (:rewrite member-of-abs-addrs-when-natp . 2)
                            (:definition remove-equal)))
    :induct (seq-this frame)
    :expand (collapse-iter frame 1))))

;; This helps prove a necessary congruence.
;; (thm
;;  (implies
;;   (and (natp x)
;;        (abs-fs-p dir)
;;        (consp (assoc-equal x (frame->frame frame)))
;;        (absfat-equiv
;;         (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))
;;         dir))
;;   (equal (len (frame->frame (collapse-seq
;;                              (frame-with-root
;;                               (frame->root frame)
;;                               (put-assoc-equal
;;                                x
;;                                (change-frame-val
;;                                 (cdr (assoc-equal x (frame->frame frame)))
;;                                 :dir dir)
;;                                (frame->frame frame)))
;;                              seq)))
;;          (len (frame->frame (collapse-seq frame seq)))))
;;  :hints (("Goal" :in-theory (e/d (collapse-seq)
;;                                  ())
;;           :induct (collapse-seq frame seq)
;;           :expand
;;           (collapse-seq
;;            (frame-with-root
;;             (frame->root frame)
;;             (put-assoc-equal
;;              x
;;              (frame-val
;;               (frame-val->path (cdr (assoc-equal x (frame->frame frame))))
;;               dir
;;               (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
;;              (frame->frame frame)))
;;            seq))))

;; This theorem helps with
;; (valid-seqp (collapse-this frame x) (seq-this (collapse-this frame x)))
;; which is a pre-requisite of the next theorem.
;; (thm
;;  (implies
;;   (and (valid-seqp frame seq)
;;        (consp (assoc-equal x (frame->frame frame)))
;;        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
;;        (not (member-equal x seq))
;;        (dist-names (frame->root frame) nil (frame->frame frame))
;;        (abs-separate (frame->frame frame))
;;        (abs-complete (frame-val->dir (cdr (assoc-equal x (frame->frame
;;                                                           frame)))))
;;        (frame-p (frame->frame frame)))
;;   (valid-seqp (collapse-this frame x) seq))
;;  :hints (("goal" :in-theory (e/d (collapse-seq valid-seqp collapse-this)
;;                                  ((:DEFINITION ASSOC-EQUAL)
;;                                   (:DEFINITION member-EQUAL)
;;                                   (:LINEAR LEN-WHEN-PREFIXP)
;;                                   (:REWRITE LEN-WHEN-PREFIXP)
;;                                   (:REWRITE M1-FILE-CONTENTS-P-CORRECTNESS-1)
;;                                   nthcdr-when->=-n-len-l
;;                                   list-equiv-when-true-listp
;;                                   ABS-SEPARATE-OF-FRAME->FRAME-OF-COLLAPSE-THIS-LEMMA-8
;;                                   (:REWRITE
;;                                    ABS-SEPARATE-OF-FRAME->FRAME-OF-COLLAPSE-THIS-LEMMA-15)
;;                                   (:REWRITE
;;                                    PARTIAL-COLLAPSE-CORRECTNESS-LEMMA-28)
;;                                   (:REWRITE
;;                                    PARTIAL-COLLAPSE-CORRECTNESS-LEMMA-1)))
;;           :induct (collapse-seq frame seq)
;;           :expand (collapse-seq (collapse-this frame x)
;;                                 seq))))

;; This theorem needs to be set aside because there's no obvious path towards
;; proving
;; (valid-seqp (collapse-this frame x) (seq-this (collapse-this frame x)))
;; which is one of the subgoals.

;; (verify
;;  (implies (and (frame-p (frame->frame frame))
;;                (abs-separate (frame->frame frame))
;;                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
;;                (not (zp n))
;;                (<= n (len (seq-this frame)))
;;                (subsetp-equal (take (+ -1 n) (seq-this frame))
;;                               (cons x (seq-this (collapse-this frame x))))
;;                (mv-nth 1 (collapse frame))
;;                (<= 0 (len (seq-this frame)))
;;                (not (equal (nth (+ -1 n) (seq-this frame))
;;                            x))
;;                (abs-complete
;;                 (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))))
;;           (member-equal (nth (+ -1 n) (seq-this frame))
;;                         (seq-this (collapse-this frame x))))
;;  :instructions
;;  ((:use (:instance partial-collapse-correctness-lemma-69
;;                    (x (nth (+ -1 n) (seq-this frame)))
;;                    (n (len (seq-this (collapse-this frame x))))
;;                    (frame (collapse-this frame x))))
;;   :promote (:demote 1)
;;   (:dive 1 1)
;;   (:= t)
;;   :up
;;   (:= (take (len (seq-this (collapse-this frame x)))
;;             (seq-this (collapse-this frame x)))
;;       (seq-this (collapse-this frame x)))
;;   :top
;;   :split
;;   (:bash ("goal" :in-theory (disable member-of-a-nat-list
;;                                      member-of-strip-cars
;;                                      no-duplicatesp-of-seq-this-lemma-1)
;;           :use ((:instance member-of-a-nat-list
;;                            (x (nth (+ -1 n) (seq-this frame)))
;;                            (lst (seq-this frame)))
;;                 (:instance member-of-strip-cars
;;                            (x (nth (+ -1 n) (seq-this frame)))
;;                            (alist (frame->frame frame)))
;;                 no-duplicatesp-of-seq-this-lemma-1)))))

;; (thm
;;  (implies
;;   (and (not (zp n))
;;        (subsetp-equal (take (+ -1 n) (seq-this frame))
;;                       (cons x (seq-this (collapse-this frame x))))
;;        (mv-nth 1 (collapse frame))
;;        (<= 0 (len (seq-this frame)))
;;        (not (equal (nth (+ -1 n) (seq-this frame))
;;                    x)))
;;   (member-equal (nth (+ -1 n) (seq-this frame))
;;                 (seq-this (collapse-this frame x)))))

;; (verify
;;  (implies (and (not (zp n))
;;                (subsetp-equal (take (+ -1 n) (seq-this frame))
;;                               (cons x (seq-this (collapse-this frame x))))
;;                (mv-nth 1 (collapse frame))
;;                (<= 0 (len (seq-this frame))))
;;           (subsetp-equal (take n (seq-this frame))
;;                          (cons x (seq-this (collapse-this frame x)))))
;;  :instructions
;;  (:promote (:= (take n (seq-this frame))
;;                (append (take (- n 1) (take n (seq-this frame)))
;;                        (nthcdr (- n 1)
;;                                (take n (seq-this frame))))
;;                :hints :none)
;;            (:change-goal nil t)
;;            (:dive 2)
;;            (:rewrite binary-append-take-nthcdr)
;;            :top :s :bash (:rewrite subsetp-append1)
;;            (:bash ("goal" :use (:instance (:rewrite take-of-nthcdr)
;;                                           (l (seq-this frame))
;;                                           (n2 (+ -1 n))
;;                                           (n1 1))))))

;; (encapsulate
;;   ()

;;   (local (include-book "std/basic/inductions" :dir :system))

;;   (thm
;;    (implies
;;     (and
;;      (mv-nth 1 (collapse frame))
;;      (<= () (len (seq-this frame))))
;;     (subsetp-equal
;;      (take n (seq-this frame))
;;      (cons x (seq-this (collapse-this frame x)))))
;;    :hints (("Goal" :in-theory (e/d () ())
;;             :induct (dec-induct n)))))

(skip-proofs
 (defthm
   partial-collapse-correctness-lemma-108
   (implies
    (and
     (abs-separate (frame->frame frame))
     (dist-names (frame->root frame)
                 nil (frame->frame frame))
     (frame-p (frame->frame frame))
     (no-duplicatesp-equal (strip-cars (frame->frame frame)))
     (< 0 x)
     (mv-nth 1 (collapse frame))
     (consp (assoc-equal x (frame->frame frame)))
     (not
      (consp
       (abs-addrs
        (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))))))
    (and
     (set-equiv
      (frame-addrs-before-seq frame 0
                              (cons x (seq-this (collapse-this frame x))))
      (frame-addrs-before frame 0 (len (frame->frame frame))))
     (set-equiv
      (cons x (seq-this (collapse-this frame x)))
      (strip-cars (frame->frame frame)))))))

;; This rule is trouble, because it can rewrite
;; (mv-nth 0 (collapse (collapse-this frame (1st-complete (frame->frame frame)))))
;; and
;; (mv-nth 1 (collapse (collapse-this frame (1st-complete (frame->frame frame)))))
;; terms, which arise naturally from opening up the definition of collapse...
(defthmd
  partial-collapse-correctness-lemma-176
  (implies
   (and (abs-separate (frame->frame frame))
        (dist-names (frame->root frame)
                    nil (frame->frame frame))
        (frame-p (frame->frame frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (mv-nth 1 (collapse frame))
        (consp (assoc-equal x (frame->frame frame)))
        (abs-complete
         (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))))
   (and (absfat-equiv (mv-nth 0 (collapse (collapse-this frame x)))
                      (mv-nth 0 (collapse frame)))
        (iff (mv-nth 1 (collapse (collapse-this frame x)))
             (mv-nth 1 (collapse frame)))))
  :hints
  (("goal"
    :use
    (partial-collapse-correctness-lemma-174
     (:instance partial-collapse-correctness-lemma-60
                (n (len (frame->frame frame))))
     (:instance
      (:rewrite ctx-app-list-when-set-equiv)
      (l1 (frame-addrs-before frame 0 (len (frame->frame frame))))
      (l2
       (frame-addrs-before-seq frame 0
                               (cons x (seq-this (collapse-this frame x)))))
      (frame frame)
      (relpath nil)
      (fs (frame->root frame)))
     collapse-iter-correctness-1
     (:instance (:rewrite collapse-seq-of-seq-this-is-collapse)
                (frame (collapse-this frame x)))
     (:instance set-equiv-implies-equal-len-1-when-no-duplicatesp
                (x (cons x (seq-this (collapse-this frame x))))
                (y (strip-cars (frame->frame frame)))))
    :in-theory (e/d (collapse-seq)
                    (partial-collapse-correctness-lemma-60
                     (:rewrite collapse-seq-of-seq-this-is-collapse)
                     (:rewrite nthcdr-when->=-n-len-l)
                     (:rewrite
                      partial-collapse-correctness-lemma-28)
                     (:type-prescription frame-val->path$inline)
                     (:definition nthcdr)
                     (:type-prescription
                      abs-fs-fix-of-put-assoc-equal-lemma-3)
                     (:type-prescription assoc-when-zp-len)
                     (:rewrite
                      ctx-app-ok-when-absfat-equiv-lemma-4)
                     (:rewrite
                      partial-collapse-correctness-lemma-24)
                     (:rewrite final-val-of-collapse-this-lemma-3))))))

(defthm
  partial-collapse-correctness-lemma-67
  (implies
   (and (abs-separate (frame->frame frame))
        (dist-names (frame->root frame)
                    nil (frame->frame frame))
        (frame-p (frame->frame frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (mv-nth 1 (collapse frame))
        (consp (assoc-equal (1st-complete-under-path (frame->frame frame)
                                                         path)
                            (frame->frame frame))))
   (and
    (absfat-equiv
     (mv-nth
      0
      (collapse
       (collapse-this frame
                      (1st-complete-under-path (frame->frame frame)
                                                   path))))
     (mv-nth 0 (collapse frame)))
    (iff
     (mv-nth
      1
      (collapse
       (collapse-this frame
                      (1st-complete-under-path (frame->frame frame)
                                                   path))))
     (mv-nth 1 (collapse frame)))))
  :hints
  (("goal"
    :use (:instance partial-collapse-correctness-lemma-176
                    (x (1st-complete-under-path (frame->frame frame)
                                                    path))))))

(defund collapse-equiv (frame1 frame2)
  (b* (((mv root1 result1) (collapse frame1))
       ((mv root2 result2) (collapse frame2)))
    (or (not (or result1 result2))
        (and result1
             result2 (absfat-equiv root1 root2)))))

(defequiv collapse-equiv
  :hints (("goal" :in-theory (enable collapse-equiv))))

(defthm
  partial-collapse-correctness-1
  (implies
   (and (frame-p (frame->frame frame))
        (no-duplicatesp-equal (strip-cars (frame->frame frame)))
        (abs-separate (frame-with-root (frame->root frame)
                                       (frame->frame frame)))
        (mv-nth 1 (collapse frame)))
   (and (absfat-equiv (mv-nth 0
                              (collapse (partial-collapse frame path)))
                      (mv-nth 0 (collapse frame)))
        (iff (mv-nth 1
                     (collapse (partial-collapse frame path)))
             (mv-nth 1 (collapse frame)))))
  :hints (("goal" :in-theory (enable partial-collapse)
           :induct (partial-collapse frame path)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (and (frame-p (frame->frame frame))
                  (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                  (abs-separate (frame-with-root (frame->root frame)
                                                 (frame->frame frame)))
                  (mv-nth 1 (collapse frame)))
             (collapse-equiv (partial-collapse frame path)
                             frame))
    :hints (("goal" :in-theory (enable collapse-equiv))))))
