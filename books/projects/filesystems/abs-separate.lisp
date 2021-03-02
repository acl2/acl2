;  abs-separate.lisp                                    Mihir Mehta

; This is a model of the FAT32 filesystem, related to HiFAT but with abstract
; variables.

(in-package "ACL2")

(include-book "hifat/hifat-equiv")
(local (include-book "std/lists/prefixp" :dir :system))
(local (include-book "std/lists/intersection" :dir :system))

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
                            '(d-e contents))))
        nil)
       (d-e (cdr (std::da-nth 0 (cdr head))))
       (contents (cdr (std::da-nth 1 (cdr head)))))
    (and (fat32-filename-p (car head))
         (d-e-p d-e)
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

(defthm cdr-of-assoc-of-nil-when-abs-file-alist-p
  (implies
   (abs-file-alist-p fs)
   (equal (cdr (assoc-equal nil fs)) nil))
  :hints (("Goal" :in-theory (enable abs-file-alist-p))))

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
 ((d-e d-e-p :default (d-e-fix nil))
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
   (m1-regular-file-p (abs-file d-e contents))
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
           (abs-directory-file-p (abs-file d-e contents)))
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

(local
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
                     (abs-file-p (cdr (car x))))))))

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

(defthm
  abs-addrs-of-remove-assoc-lemma-3
  (implies
   (abs-file-alist-p fs)
   (subsetp-equal (abs-addrs (abs-file->contents (cdr (assoc-equal name fs))))
                  (abs-addrs fs)))
  :hints (("goal" :in-theory
           (e/d (abs-addrs abs-file-alist-p subsetp-equal)
                ((:compound-recognizer natp-compound-recognizer)
                 (:compound-recognizer true-listp-when-m1-file-alist-p)
                 (:elim car-cdr-elim)
                 (:executable-counterpart abs-file-alist-p)
                 (:executable-counterpart car)
                 (:executable-counterpart cons)
                 (:executable-counterpart fat32-filename-p)
                 (:executable-counterpart not)
                 (:executable-counterpart symbolp)
                 (:forward-chaining alistp-forward-to-true-listp)
                 (:induction abs-file-alist-p)
                 (:induction true-listp)
                 (:rewrite abs-addrs-when-m1-file-alist-p)
                 (:rewrite abs-addrs-when-m1-file-alist-p-lemma-2)
                 (:rewrite abs-directory-file-p-when-m1-file-p)
                 (:rewrite abs-file->contents-when-m1-file-p)
                 (:rewrite append-when-not-consp)
                 (:rewrite car-cons)
                 (:rewrite cdr-cons)
                 (:rewrite list-equiv-when-true-listp)
                 (:rewrite m1-file-alist-p-of-m1-file->contents)
                 (:rewrite m1-file-fix-when-m1-file-p)
                 (:rewrite prefixp-when-equal-lengths)
                 (:rewrite fty::strip-cars-under-iff)
                 (:rewrite subsetp-of-cdr)
                 (:rewrite subsetp-trans)
                 (:rewrite subsetp-trans2)
                 (:rewrite subsetp-when-atom-right)
                 (:type-prescription abs-addrs)
                 (:type-prescription abs-directory-file-p-when-m1-file-p-lemma-1)
                 (:type-prescription abs-file-contents-fix)
                 (:type-prescription fat32-filename-p)
                 (:type-prescription m1-directory-file-p)))
           :induct (mv (abs-addrs fs)
                       (assoc-equal name fs))
           :expand ((abs-file-alist-p fs)
                    (abs-directory-file-p (cdr (car fs)))
                    (abs-file->contents (cdr (car fs)))
                    (abs-file-p (cdr (car fs)))))))

;; top-complete is known to match up with alistp
(defund abs-complete (x)
  (declare
   (xargs :guard (abs-file-alist-p x)))
  (atom (abs-addrs x)))

(defthm abs-complete-when-stringp
  (implies (stringp x) (abs-complete x))
  :hints (("goal" :in-theory (enable abs-complete abs-addrs))))

(defthm
  abs-complete-correctness-1
  (implies (not (consp (abs-addrs x)))
           (abs-complete x))
  :hints (("goal" :do-not-induct t
           :in-theory (enable abs-complete))))

(defthm
  abs-file-alist-p-correctness-1
  (implies (and (abs-file-alist-p x)
                (abs-complete x))
           (m1-file-alist-p x))
  :hints (("goal" :in-theory (enable abs-file-alist-p abs-addrs
                                     abs-addrs-when-m1-file-alist-p-lemma-1
                                     abs-complete m1-file-alist-p
                                     abs-file-p m1-file-contents-p m1-file-p
                                     abs-directory-file-p abs-file->contents)
           :induct (abs-addrs x)
           :expand (abs-file-alist-p x))))

(defthm
  subsetp-of-abs-addrs-of-put-assoc-lemma-1
  (implies (abs-directory-file-p (abs-file-fix x))
           (abs-file-alist-p (abs-file->contents$inline x)))
  :hints (("goal" :in-theory (enable abs-file-alist-p abs-directory-file-p
                                     abs-file->contents abs-file-fix))))

(defthm subsetp-of-abs-addrs-of-put-assoc
  (implies (abs-complete (abs-file->contents file))
           (subsetp-equal (abs-addrs (put-assoc-equal name file fs))
                          (abs-addrs fs)))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  no-duplicatesp-of-abs-addrs-of-put-assoc
  (implies (and (abs-complete (abs-file->contents file))
                (no-duplicatesp-equal (abs-addrs fs)))
           (no-duplicatesp-equal (abs-addrs (put-assoc-equal name file fs))))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm abs-addrs-when-m1-file-contents-p
  (implies (m1-file-contents-p fs)
           (and
            (not (consp (abs-addrs fs)))
            (abs-complete fs)))
  :hints (("goal" :in-theory (enable abs-addrs m1-file-contents-p abs-complete))))

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
           :induct (mv (true-list-fix x) (append x y))
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
  abs-no-dups-p-of-remove1-assoc-1
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

(defthm
  abs-no-dups-p-of-remove1-assoc-2
  (implies (abs-no-dups-p fs)
           (abs-no-dups-p (remove1-assoc-equal name fs)))
  :hints (("goal" :in-theory (enable abs-no-dups-p remove1-assoc-equal))))

;; Potentially overlapping with abs-no-dups-p-when-m1-file-alist-p, which is
;; actually more general.
(defthm hifat-no-dups-p-when-abs-complete
  (implies (and (abs-no-dups-p dir)
                (abs-complete dir))
           (hifat-no-dups-p dir))
  :hints (("goal" :in-theory (enable abs-addrs abs-complete
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
   (and (abs-file-p val)
        (abs-file-alist-p abs-file-alist)
        (abs-no-dups-p abs-file-alist)
        (fat32-filename-p name))
   (set-equiv (abs-addrs (put-assoc-equal name val abs-file-alist))
              (append (abs-addrs (abs-file->contents val))
                      (abs-addrs (remove-assoc-equal name abs-file-alist)))))
  :hints
  (("goal"
    :in-theory (e/d (abs-addrs abs-file-p-alt)
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

;; Note, this is not subsumed by abs-addrs-of-put-assoc-1 because it is hinged
;; on equal rather than set-equiv.
(defthm
  abs-addrs-of-put-assoc-2
  (implies (and (abs-complete (abs-file->contents val))
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
                (put-assoc-equal name val abs-file-alist))
    :do-not-induct t)))

(defthmd
  no-duplicatesp-of-abs-addrs-of-put-assoc-lemma-1
  (implies (and (abs-file-alist-p abs-file-alist)
                (consp abs-file-alist))
           (or (consp (car abs-file-alist))
               (natp (car abs-file-alist))))
  :hints (("goal" :do-not-induct t
           :expand (abs-file-alist-p abs-file-alist)))
  :rule-classes :type-prescription)

(encapsulate
  ()

  (local (include-book "std/lists/intersectp" :dir :system))

  (defthm
    no-duplicatesp-of-abs-addrs-of-put-assoc-1
    (implies
     (and (abs-file-p val)
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
    :hints
    (("goal"
      :in-theory
      (e/d (abs-addrs intersectp-equal abs-file-p-alt
                      no-duplicatesp-of-abs-addrs-of-put-assoc-lemma-1))))))

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

;; This is used in multiple files.
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

(defthm
  no-duplicatesp-of-abs-addrs-of-abs-file->contents-of-cdr-of-assoc
  (implies (and (abs-file-alist-p fs)
                (no-duplicatesp-equal (abs-addrs fs)))
           (no-duplicatesp-equal
            (abs-addrs (abs-file->contents (cdr (assoc-equal name fs))))))
  :hints
  (("goal"
    :in-theory (e/d (abs-addrs abs-file-alist-p
                               abs-file->contents abs-file-contents-fix
                               abs-file-contents-p
                               abs-directory-file-p abs-file-p)
                    (m1-file-alist-p-of-cdr-when-m1-file-alist-p
                     abs-file-alist-p-correctness-1
                     m1-file-contents-p-correctness-1
                     assoc-when-zp-len
                     abs-addrs-when-m1-file-alist-p
                     abs-file-alist-p-when-m1-file-alist-p)))))

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

(defthm abs-fs-p-when-hifat-no-dups-p
  (implies (and (m1-file-alist-p fs)
                (hifat-no-dups-p fs))
           (abs-fs-p fs))
  :hints (("goal" :do-not-induct t
           :in-theory (enable abs-fs-p))))

(defthm abs-addrs-of-remove-assoc-lemma-1
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

(defthm abs-addrs-of-remove-assoc-lemma-2
  (implies (and (abs-no-dups-p (abs-file->contents file))
                (abs-directory-file-p file))
           (abs-fs-p (abs-file->contents file)))
  :hints (("goal" :in-theory (enable abs-directory-file-p)
           :do-not-induct t)))

(encapsulate
  ()

  (local (include-book "std/lists/intersectp" :dir :system))

  (defthm
    abs-addrs-of-remove-assoc
    (implies
     (and (abs-file-alist-p fs)
          (fat32-filename-p name)
          (abs-no-dups-p fs)
          (no-duplicatesp-equal (abs-addrs fs)))
     (equal
      (abs-addrs (remove-assoc-equal name fs))
      (set-difference-equal
       (abs-addrs fs)
       (abs-addrs (abs-file->contents (cdr (assoc-equal name fs)))))))
    :hints (("goal" :in-theory (enable abs-addrs
                                       abs-file-alist-p abs-no-dups-p)
             :induct (mv (abs-addrs fs)
                         (remove-assoc-equal name fs)))
            ("subgoal *1/4.2'" :expand ((abs-directory-file-p (cdr (car fs)))
                                        (abs-file-p (cdr (car fs)))
                                        (abs-file->contents (cdr (car fs))))))))

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
                     :d-e (abs-file->d-e (cdr head))
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

(defthm abs-fs-fix-of-put-assoc-equal-lemma-2
  (implies (and (abs-file-alist-p fs)
                (consp (car fs)))
           (abs-file-p (cdr (car fs))))
  :hints (("goal" :in-theory (enable abs-file-alist-p abs-file-p))))

(defthm
  abs-fs-fix-of-put-assoc-equal
  (implies
   (and (abs-fs-p fs)
        (fat32-filename-p name))
   (equal
    (abs-fs-fix (put-assoc-equal name val fs))
    (if (abs-directory-file-p (abs-file-fix val))
        (put-assoc-equal name
                         (abs-file (abs-file->d-e val)
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

;; This is a hack...
(defthm
  no-duplicatesp-of-abs-addrs-of-abs-fs-fix-lemma-1
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
                     (:rewrite abs-file-alist-p-of-cdr)))))
  :rule-classes
  (:rewrite
   (:rewrite :corollary
             (implies
              (abs-file-alist-p abs-file-alist)
              (implies
               (not (intersectp-equal x (abs-addrs abs-file-alist)))
               (not (intersectp-equal
                     x
                     (abs-addrs (abs-fs-fix abs-file-alist)))))))
   (:rewrite :corollary
             (implies
              (abs-file-alist-p abs-file-alist)
              (implies
               (not (intersectp-equal (abs-addrs abs-file-alist)
                                      x))
               (not
                (intersectp-equal (abs-addrs (abs-fs-fix abs-file-alist))
                                  x)))))))

;; The abs-file-alist-p hypothesis is required because otherwise the fixing
;; could introduce a lot of (duplicate) zeros.
(defthm no-duplicatesp-of-abs-addrs-of-abs-fs-fix
  (implies (and (abs-file-alist-p x)
                (no-duplicatesp-equal (abs-addrs x)))
           (no-duplicatesp-equal (abs-addrs (abs-fs-fix x))))
  :hints (("goal" :in-theory (enable abs-addrs abs-fs-fix))))

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
                             (remove-equal nil (strip-cars root)))))

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

(defthm
  addrs-at-when-abs-complete-lemma-1
  (subsetp-equal (abs-top-addrs fs) (abs-addrs fs))
  :hints (("goal" :in-theory (enable abs-addrs abs-top-addrs)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (subsetp-equal y (abs-top-addrs fs))
     (subsetp-equal y (abs-addrs fs))))))

(defthm
  addrs-at-when-abs-complete-lemma-3
  (subsetp-equal (abs-top-addrs fs)
                 (abs-addrs (abs-fs-fix fs))))

(defthm
  addrs-at-when-abs-complete
  (implies (abs-complete (abs-fs-fix fs))
           (equal (addrs-at fs relpath) nil))
  :hints (("goal" :in-theory (e/d (addrs-at)
                                  (addrs-at-when-abs-complete-lemma-3))
           :induct (addrs-at fs relpath))
          ("subgoal *1/1" :use addrs-at-when-abs-complete-lemma-3)))


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
          (abs-file->d-e
           (cdr (abs-assoc head abs-file-alist1)))
          (ctx-app
           (abs-file->contents
            (cdr (abs-assoc head abs-file-alist1)))
           abs-file-alist2 x (cdr x-path)))
         abs-file-alist1)))
    ;; This is actually an error condition.
    abs-file-alist1))

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
  ctx-app-ok-when-abs-complete-lemma-2
  (implies
   (abs-directory-file-p (cdr (assoc-equal name fs)))
   (subsetp-equal (abs-addrs (abs-file->contents (cdr (assoc-equal name fs))))
                  (abs-addrs fs)))
  :hints (("goal" :in-theory (enable abs-addrs))))

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

;; Rename later.
(defthm null-addrs-at-when-stringp
  (implies (stringp x)
           (equal (addrs-at x relpath) nil))
  :hints (("goal" :in-theory (enable addrs-at abs-fs-fix)))
  :rule-classes (:type-prescription :rewrite))
(defthm not-ctx-app-ok-when-stringp
  (implies (stringp x)
           (not (ctx-app-ok x var relpath)))
  :hints (("goal" :in-theory (enable ctx-app-ok)))
  :rule-classes (:type-prescription :rewrite))

(defthm abs-addrs-of-ctx-app-1-lemma-1
  (subsetp-equal (abs-addrs (remove-equal x abs-file-alist))
                 (abs-addrs abs-file-alist))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  abs-addrs-of-ctx-app-lemma-6
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

;; Important - says clearly that the variable's name (or number, whatever) must
;; exist for context application to go right.
(defthmd
  abs-addrs-of-ctx-app-lemma-2
  (implies (not (member-equal (nfix x)
                              (abs-addrs (abs-fs-fix abs-file-alist1))))
           (not (ctx-app-ok abs-file-alist1 x x-path)))
  :hints (("goal" :in-theory (e/d (abs-addrs addrs-at ctx-app ctx-app-ok)
                                  (nfix)))))

(defthmd
  abs-addrs-of-ctx-app-lemma-3
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

;; Inductive, hence kept.
(defthm
  abs-addrs-of-ctx-app-lemma-11
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
       (abs-file (abs-file->d-e (cdr (assoc-equal name abs-file-alist1)))
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
     (abs-file (abs-file->d-e (cdr (assoc-equal name abs-file-alist1)))
               abs-file-alist2)
     abs-file-alist1))))

;; This just might be made obsolete soon...
(defthm
  abs-addrs-of-ctx-app-lemma-5
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
       (abs-file (abs-file->d-e (cdr (assoc-equal name abs-file-alist1)))
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
        (abs-file->d-e (cdr (assoc-equal name abs-file-alist1)))
        (ctx-app
         (abs-file->contents (cdr (assoc-equal name abs-file-alist1)))
         abs-file-alist2 x x-path))
       abs-file-alist1))
     y))))

;; Inductive, hence kept.
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
  abs-addrs-of-ctx-app-lemma-7
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

;; Inductive, hence kept.
(defthm
  abs-addrs-of-ctx-app-lemma-12
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
       (abs-file->d-e (cdr (assoc-equal name abs-file-alist1)))
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
       (abs-file->d-e (cdr (assoc-equal name abs-file-alist1)))
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
       (abs-file->d-e (cdr (assoc-equal name abs-file-alist1)))
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
                     (:rewrite subsetp-of-abs-addrs-of-put-assoc-lemma-1)
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
       (abs-file->d-e (cdr (assoc-equal name abs-file-alist1)))
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

(defthm abs-file-alist-p-of-frame-val->dir
  (abs-file-alist-p (frame-val->dir x))
  :hints (("goal" :in-theory (e/d (frame-val->dir) nil))))

(defthm abs-no-dups-p-of-frame-val->dir
  (abs-no-dups-p (frame-val->dir x))
  :hints (("goal" :in-theory (e/d (frame-val->dir) nil))))

(fty::defalist frame
               :key-type nat
               :val-type frame-val
               :true-listp t)

(defthm nat-listp-of-strip-cars-when-frame-p
  (implies (frame-p frame)
           (nat-listp (strip-cars frame))))

(defthm assoc-equal-when-frame-p
  (implies (and (frame-p frame) (not (natp x)))
           (atom (assoc-equal x frame)))
  :rule-classes :type-prescription)

(defthm member-of-strip-cars-when-frame-p
  (implies (frame-p frame)
           (not (member-equal nil (strip-cars frame))))
  :hints (("Goal" :in-theory (enable frame-p strip-cars))))

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
      (abs-file (abs-file->d-e (cdr (abs-assoc head fs)))
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
       (abs-file (d-e-fix nil) ""))
      (cons
       "RUN        "
       (abs-file
        (d-e-fix nil)
        (list
         (cons
          "RSYSLOGDPID"
          (abs-file (d-e-fix nil) "")))))
      (cons
       "USR        "
       (abs-file (d-e-fix nil)
                 (list
                  (cons
                   "LOCAL      "
                   (abs-file (d-e-fix nil) ()))
                  (cons
                   "LIB        "
                   (abs-file (d-e-fix nil) ()))
                  1))))
     0))
   (cons
    1
    (frame-val
     (list "USR        ")
     (list
      (cons
       "SHARE      "
       (abs-file (d-e-fix nil) ()))
      (cons
       "BIN        "
       (abs-file (d-e-fix nil)
                 (list
                  (cons
                   "CAT        "
                   (abs-file (d-e-fix nil) ""))
                  2
                  (cons
                   "TAC        "
                   (abs-file (d-e-fix nil) ""))))))
     0))
   (cons
    2
    (frame-val
     (list "USR        " "BIN        ")
     (list
      (cons
       "COL        "
       (abs-file (d-e-fix nil) "")))
     1)))))

(assert-event
 (mv-let
   (fs addr-list sub-fs final-head)
   (unlink-abs-alloc-helper-1
    (list
     (cons
      "INITRD  IMG"
      (abs-file (d-e-fix nil) ""))
     (cons
      "RUN        "
      (abs-file
       (d-e-fix nil)
       (list
        (cons
         "RSYSLOGDPID"
         (abs-file (d-e-fix nil) "")))))
     (cons
      "USR        "
      (abs-file (d-e-fix nil)
                (list
                 (cons
                  "LOCAL      "
                  (abs-file (d-e-fix nil) ()))
                 (cons
                  "LIB        "
                  (abs-file (d-e-fix nil) ()))
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
        (d-e-fix nil)
        (list
         (cons
          "RSYSLOGDPID"
          (abs-file (d-e-fix nil) "")))))
      (cons
       "USR        "
       (abs-file (d-e-fix nil)
                 (list
                  (cons
                   "LOCAL      "
                   (abs-file (d-e-fix nil) ()))
                  (cons
                   "LIB        "
                   (abs-file (d-e-fix nil) ()))
                  1)))))
    (equal
     addr-list
     nil)
    (equal
     sub-fs
     (list
      (cons
       "INITRD  IMG"
       (abs-file (d-e-fix nil) ""))))
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
      (abs-file (d-e-fix nil) ""))
     (cons
      "RUN        "
      (abs-file
       (d-e-fix nil)
       (list
        (cons
         "RSYSLOGDPID"
         (abs-file (d-e-fix nil) "")))))
     (cons
      "USR        "
      (abs-file (d-e-fix nil)
                (list
                 (cons
                  "LOCAL      "
                  (abs-file (d-e-fix nil) ()))
                 (cons
                  "LIB        "
                  (abs-file (d-e-fix nil) ()))
                 1))))
    (list "RUN        " "RSYSLOGDPID")
    3)
   (and
    (equal
     fs
     (list
      (cons
       "INITRD  IMG"
       (abs-file (d-e-fix nil) ""))
      (cons
       "RUN        "
       (abs-file
        (d-e-fix nil)
        (list
         3)))
      (cons
       "USR        "
       (abs-file (d-e-fix nil)
                 (list
                  (cons
                   "LOCAL      "
                   (abs-file (d-e-fix nil) ()))
                  (cons
                   "LIB        "
                   (abs-file (d-e-fix nil) ()))
                  1)))))
    (equal
     addr-list
     nil)
    (equal
     sub-fs
     (list
      (cons
       "RSYSLOGDPID"
       (abs-file (d-e-fix nil) ""))))
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
      (abs-file (d-e-fix nil) ""))
     (cons
      "RUN        "
      (abs-file
       (d-e-fix nil)
       (list
        (cons
         "RSYSLOGDPID"
         (abs-file (d-e-fix nil) "")))))
     (cons
      "USR        "
      (abs-file (d-e-fix nil)
                (list
                 (cons
                  "LOCAL      "
                  (abs-file (d-e-fix nil) ()))
                 (cons
                  "LIB        "
                  (abs-file (d-e-fix nil) ()))
                 1))))
    (list "USR        " "BIN        " "COL        ")
    3)
   (and
    (equal
     fs
     (list
      (cons
       "INITRD  IMG"
       (abs-file (d-e-fix nil) ""))
      (cons
       "RUN        "
       (abs-file
        (d-e-fix nil)
        (list
         (cons
          "RSYSLOGDPID"
          (abs-file (d-e-fix nil) "")))))
      (cons
       "USR        "
       (abs-file (d-e-fix nil)
                 (list
                  (cons
                   "LOCAL      "
                   (abs-file (d-e-fix nil) ()))
                  (cons
                   "LIB        "
                   (abs-file (d-e-fix nil) ()))
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
        (abs-file (d-e-fix nil) ""))
       (cons
        "RUN        "
        (abs-file
         (d-e-fix nil)
         (list
          (cons
           "RSYSLOGDPID"
           (abs-file (d-e-fix nil) "")))))
       (cons
        "USR        "
        (abs-file (d-e-fix nil)
                  (list
                   (cons
                    "LOCAL      "
                    (abs-file (d-e-fix nil) ()))
                   (cons
                    "LIB        "
                    (abs-file (d-e-fix nil) ()))
                   1))))
      0))
    (cons
     1
     (frame-val
      (list "USR        ")
      (list
       (cons
        "SHARE      "
        (abs-file (d-e-fix nil) ()))
       (cons
        "BIN        "
        (abs-file (d-e-fix nil)
                  (list
                   (cons
                    "CAT        "
                    (abs-file (d-e-fix nil) ""))
                   2
                   (cons
                    "TAC        "
                    (abs-file (d-e-fix nil) ""))))))
      0))
    (cons
     2
     (frame-val
      (list "USR        " "BIN        ")
      (list
       (cons
        "COL        "
        (abs-file (d-e-fix nil) "")))
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
        (abs-file (d-e-fix nil) ""))
       (cons
        "RUN        "
        (abs-file
         (d-e-fix nil)
         (list
          (cons
           "RSYSLOGDPID"
           (abs-file (d-e-fix nil) "")))))
       (cons
        "USR        "
        (abs-file (d-e-fix nil)
                  (list
                   (cons
                    "LOCAL      "
                    (abs-file (d-e-fix nil) ()))
                   (cons
                    "LIB        "
                    (abs-file (d-e-fix nil) ()))
                   1))))
      0))
    (cons
     1
     (frame-val
      (list "USR        ")
      (list
       (cons
        "SHARE      "
        (abs-file (d-e-fix nil) ()))
       (cons
        "BIN        "
        (abs-file (d-e-fix nil)
                  (list
                   (cons
                    "CAT        "
                    (abs-file (d-e-fix nil) ""))
                   2
                   (cons
                    "TAC        "
                    (abs-file (d-e-fix nil) ""))))))
      0))
    (cons
     2
     (frame-val
      (list "USR        " "BIN        ")
      (list
       (cons
        "COL        "
        (abs-file (d-e-fix nil) "")))
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
        (abs-file (d-e-fix nil) ""))
       (cons
        "RUN        "
        (abs-file
         (d-e-fix nil)
         (list
          (cons
           "RSYSLOGDPID"
           (abs-file (d-e-fix nil) "")))))
       (cons
        "USR        "
        (abs-file (d-e-fix nil)
                  (list
                   (cons
                    "LOCAL      "
                    (abs-file (d-e-fix nil) ()))
                   (cons
                    "LIB        "
                    (abs-file (d-e-fix nil) ()))
                   1))))
      0))
    (cons
     1
     (frame-val
      (list "USR        ")
      (list
       (cons
        "SHARE      "
        (abs-file (d-e-fix nil) ()))
       (cons
        "BIN        "
        (abs-file (d-e-fix nil)
                  (list
                   (cons
                    "CAT        "
                    (abs-file (d-e-fix nil) ""))
                   2
                   (cons
                    "TAC        "
                    (abs-file (d-e-fix nil) ""))))))
      0))
    (cons
     2
     (frame-val
      (list "USR        " "BIN        ")
      (list
       (cons
        "COL        "
        (abs-file (d-e-fix nil) "")))
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
   (> (1st-complete (put-assoc-equal name val frame))
      0))
  :hints (("goal" :in-theory (enable 1st-complete abs-complete)))
  :rule-classes
  :linear)

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

(defthm
  1st-complete-correctness-2
  (implies (and (frame-p frame)
                (atom (assoc-equal 0 frame))
                (consp (assoc-equal x frame))
                (abs-complete (frame-val->dir (cdr (assoc-equal x frame)))))
           (< 0 (1st-complete frame)))
  :hints (("goal" :in-theory (enable 1st-complete)))
  :rule-classes :linear)

(defthm frame-val-p-of-cdr-of-assoc-equal-when-frame-p
  (implies (frame-p x)
           (iff (frame-val-p (cdr (assoc-equal k x)))
                (or (consp (assoc-equal k x))
                    (frame-val-p nil))))
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

(defthmd put-assoc-equal-of-frame-with-root
  (equal (put-assoc-equal key val (frame-with-root root frame))
         (if (equal key 0)
             (cons (cons 0 val) frame)
           (frame-with-root root (put-assoc-equal key val frame))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable frame-with-root))))

(defthmd assoc-equal-of-frame-with-root
  (equal (assoc-equal x (frame-with-root root frame))
         (if (equal x 0)
             (cons 0 (frame-val nil (abs-fs-fix root) 0))
             (assoc-equal x frame)))
  :hints (("goal" :in-theory (enable frame-with-root))))

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

(defthm consp-of-assoc-of-frame->frame
  (implies (not (consp (assoc-equal x frame)))
           (not (consp (assoc-equal x (frame->frame frame)))))
  :hints (("goal" :in-theory (enable frame->frame))))

(defthmd assoc-of-frame->frame
  (equal (assoc-equal x (frame->frame frame))
         (if (not (equal x 0))
             (assoc-equal x frame)
             nil))
  :hints (("goal" :in-theory (enable frame->frame))))

(defthm when-consp-assoc-of-frame->frame-1
  (implies (and (consp (assoc-equal x (frame->frame frame)))
                (natp x))
           (not (zp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable assoc-of-frame->frame))))

;; I regard both of the following rewrite rules as dangerous, so I'm keeping
;; them disabled except for where they're needed.
(defthmd frame->frame-of-put-assoc
  (equal (frame->frame (put-assoc-equal key val frame))
         (if (equal 0 key)
             (frame->frame frame)
             (put-assoc-equal key val (frame->frame frame))))
  :hints (("goal" :in-theory (enable frame->frame))))
(defthm frame->root-of-put-assoc
  (equal (frame->root (put-assoc-equal key val frame))
         (if (equal 0 key)
             (frame-val->dir val)
             (frame->root frame)))
  :hints (("goal" :in-theory (enable frame->root))))

(defthm abs-file-alist-p-of-frame->root
  (abs-file-alist-p (frame->root frame))
  :hints (("goal" :do-not-induct t
           :in-theory (enable frame->root))))

(defthm abs-no-dups-p-of-frame->root
  (abs-no-dups-p (frame->root frame))
  :hints (("goal" :do-not-induct t
           :in-theory (enable frame->root))))

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

(defthm true-listp-of-collapse-this
  (true-listp (collapse-this frame x))
  :hints (("goal" :do-not-induct t
           :in-theory (enable collapse-this)))
  :rule-classes :type-prescription)

(defthm equal-of-frame->frame-of-collapse-this
  (implies (and (equal (frame->frame frame1)
                       (frame->frame frame2))
                (syntaxp (not (term-order frame1 frame2))))
           (equal (frame->frame (collapse-this frame1 x))
                  (frame->frame (collapse-this frame2 x))))
  :hints (("goal" :in-theory (enable collapse-this))))

(defthm
  no-duplicatesp-of-strip-cars-of-collapse-this-1
  (implies
   (and (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               0)
        (no-duplicatesp-equal (strip-cars frame)))
   (no-duplicatesp-equal (strip-cars (collapse-this frame x))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable collapse-this))))

(defthm
  no-duplicatesp-of-strip-cars-of-collapse-this-2
  (implies
   (and
    (no-duplicatesp-equal (strip-cars frame))
    (not (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                x))
    (consp
     (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                  (frame->frame frame))))
   (no-duplicatesp-equal (strip-cars (collapse-this frame x))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable collapse-this))))

(defthm
  len-of-frame->frame-of-collapse-this-1
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
  len-of-frame->frame-of-collapse-this-2
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
           (abs-file (d-e-fix nil) ""))
          (cons
           "RUN        "
           (abs-file
            (d-e-fix nil)
            (list
             (cons
              "RSYSLOGDPID"
              (abs-file (d-e-fix nil) "")))))
          (cons
           "USR        "
           (abs-file (d-e-fix nil)
                     (list
                      (cons
                       "LOCAL      "
                       (abs-file (d-e-fix nil) ()))
                      (cons
                       "LIB        "
                       (abs-file (d-e-fix nil) ()))
                      1))))
         (list
          (cons
           1
           (frame-val
            (list "USR        ")
            (list
             (cons
              "SHARE      "
              (abs-file (d-e-fix nil) ()))
             (cons
              "BIN        "
              (abs-file (d-e-fix nil)
                        (list
                         (cons
                          "CAT        "
                          (abs-file (d-e-fix nil) ""))
                         2
                         (cons
                          "TAC        "
                          (abs-file (d-e-fix nil) ""))))))
            0))
          (cons
           2
           (frame-val
            (list "USR        " "BIN        ")
            (list
             (cons
              "COL        "
              (abs-file (d-e-fix nil) "")))
            1)))))))
   (and
    (equal
     root
     (list
      (cons
       "INITRD  IMG"
       (abs-file (d-e-fix nil) ""))
      (cons
       "RUN        "
       (abs-file (d-e-fix nil)
                 (list
                  (cons
                   "RSYSLOGDPID"
                   (abs-file (d-e-fix nil) "")))))
      (cons
       "USR        "
       (abs-file (d-e-fix nil)
                 (list
                  (cons
                   "LOCAL      "
                   (abs-file (d-e-fix nil) nil))
                  (cons
                   "LIB        "
                   (abs-file (d-e-fix nil) nil))
                  (cons
                   "SHARE      "
                   (abs-file (d-e-fix nil) nil))
                  (cons
                   "BIN        "
                   (abs-file (d-e-fix nil)
                             (list
                              (cons
                               "CAT        "
                               (abs-file (d-e-fix nil) ""))
                              (cons
                               "TAC        "
                               (abs-file (d-e-fix nil) ""))
                              (cons
                               "COL        "
                               (abs-file (d-e-fix nil) ""))))))))))
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
     (abs-file (d-e-fix nil) ""))
    (cons
     "RUN        "
     (abs-file
      (d-e-fix nil)
      (list
       (cons
        "RSYSLOGDPID"
        (abs-file (d-e-fix nil) "")))))
    (cons
     "USR        "
     (abs-file (d-e-fix nil)
               (list
                1
                (cons
                 "LIB        "
                 (abs-file (d-e-fix nil) ()))
                1)))))
  t))

(assert-event
 (equal
  (abs-no-dups-p
   (list
    (cons
     "INITRD  IMG"
     (abs-file (d-e-fix nil) ""))
    (cons
     "RUN        "
     (abs-file
      (d-e-fix nil)
      (list
       (cons
        "RSYSLOGDPID"
        (abs-file (d-e-fix nil) "")))))
    (cons
     "USR        "
     (abs-file (d-e-fix nil)
               (list
                (cons
                 "LIB        "
                 (abs-file (d-e-fix nil) ()))
                1
                (cons
                 "LIB        "
                 (abs-file (d-e-fix nil) ())))))))
  nil))

(assert-event
 (equal
  (abs-no-dups-p
   (list
    (cons
     "INITRD  IMG"
     (abs-file (d-e-fix nil) ""))
    (cons
     "RUN        "
     (abs-file
      (d-e-fix nil)
      (list
       (cons
        "RSYSLOGDPID"
        (abs-file (d-e-fix nil) "")))))
    (cons
     "USR        "
     (abs-file (d-e-fix nil)
               (list
                (cons
                 "LIB        "
                 (abs-file (d-e-fix nil) ()))
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

(defthm
  when-zp-src-of-1st-collapse-1
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

(defthm
  len-of-frame->frame-of-collapse-iter
  (implies (and (mv-nth 1 (collapse frame))
                (no-duplicatesp-equal (strip-cars (frame->frame frame))))
           (equal (len (frame->frame (collapse-iter frame n)))
                  (nfix (- (len (frame->frame frame))
                           (nfix n)))))
  :hints (("goal" :in-theory (enable collapse collapse-iter))))

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

(defthm
  absfat-subsetp-of-put-assoc-3
  (implies
   (and (abs-file-alist-p abs-file-alist1)
        (abs-no-dups-p abs-file-alist1)
        (absfat-subsetp (remove-assoc name abs-file-alist1)
                        abs-file-alist2)
        (m1-regular-file-p (cdr (assoc-equal name abs-file-alist2)))
        (fat32-filename-p name)
        (m1-regular-file-p val)
        (equal (abs-file->contents val)
               (abs-file->contents (cdr (assoc-equal name abs-file-alist2)))))
   (absfat-subsetp (put-assoc-equal name val abs-file-alist1)
                   abs-file-alist2))
  :hints (("goal" :in-theory (e/d (absfat-subsetp abs-no-dups-p) nil)
           :induct (put-assoc-equal name val abs-file-alist1))
          ("subgoal *1/2" :expand (abs-no-dups-p abs-file-alist1))))

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

(defthm abs-complete-when-m1-file-alist-p
  (implies (m1-file-alist-p fs) (abs-complete fs))
  :hints (("goal" :in-theory (enable abs-complete))))

(defthmd abs-complete-when-atom-abs-addrs
  (implies (not (consp (abs-addrs fs)))
           (abs-complete fs))
  :hints (("goal" :in-theory (enable abs-complete))))

(defthm
  absfat-equiv-implies-equal-m1-file-alist-p-of-abs-fs-fix-lemma-1
  (implies (and (absfat-equiv abs-file-alist1 abs-file-alist2)
                (m1-file-alist-p (abs-fs-fix abs-file-alist1)))
           (and
            (equal (abs-addrs
                    (abs-fs-fix abs-file-alist2))
                   nil)
            (abs-complete (abs-fs-fix abs-file-alist2))))
  :hints
  (("goal"
    :in-theory (e/d (absfat-equiv
                     abs-complete-when-atom-abs-addrs)
                    (abs-addrs-when-absfat-equiv-lemma-1))
    :use ((:instance abs-addrs-when-absfat-equiv-lemma-1
                     (abs-file-alist1 (abs-fs-fix abs-file-alist1))
                     (abs-file-alist2 (abs-fs-fix abs-file-alist2)))
          (:instance abs-addrs-when-absfat-equiv-lemma-1
                     (abs-file-alist1 (abs-fs-fix abs-file-alist2))
                     (abs-file-alist2 (abs-fs-fix abs-file-alist1))))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (and (absfat-equiv abs-file-alist1 abs-file-alist2)
                  (m1-file-alist-p (abs-fs-fix abs-file-alist1))
                  (abs-fs-p abs-file-alist2))
             (and
              (equal (abs-addrs abs-file-alist2) nil)
              (abs-complete abs-file-alist2))))))

(defthm
  absfat-equiv-implies-equal-m1-file-alist-p-of-abs-fs-fix-1
  (implies (absfat-equiv abs-file-alist1 abs-file-alist2)
           (equal (m1-file-alist-p (abs-fs-fix abs-file-alist1))
                  (m1-file-alist-p (abs-fs-fix abs-file-alist2))))
  :hints (("goal" :in-theory (disable absfat-equiv-implies-equal-m1-file-alist-p-of-abs-fs-fix-lemma-1)
           :use (absfat-equiv-implies-equal-m1-file-alist-p-of-abs-fs-fix-lemma-1
                 (:instance absfat-equiv-implies-equal-m1-file-alist-p-of-abs-fs-fix-lemma-1
                            (abs-file-alist1 abs-file-alist2)
                            (abs-file-alist2 abs-file-alist1)))))
  :rule-classes
  :congruence)

;; Probably tricky to get a refinement relationship (in the defrefinement
;; sense) between literally absfat-equiv and hifat-equiv. But we can still have
;; some kind of substitute...
(defthm
  hifat-equiv-when-absfat-equiv
  (implies (m1-file-alist-p (abs-fs-fix abs-file-alist1))
           (equal (absfat-equiv abs-file-alist1 abs-file-alist2)
                  (and (hifat-equiv (abs-fs-fix abs-file-alist1)
                                    (abs-fs-fix abs-file-alist2))
                       (m1-file-alist-p (abs-fs-fix abs-file-alist2)))))
  :hints
  (("goal"
    :in-theory (e/d (absfat-equiv hifat-equiv abs-fs-p
                                  absfat-subsetp-correctness-1 abs-fs-fix)
                    (absfat-equiv-implies-equal-m1-file-alist-p-of-abs-fs-fix-lemma-1))
    :use absfat-equiv-implies-equal-m1-file-alist-p-of-abs-fs-fix-lemma-1
    :do-not-induct t))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (m1-file-alist-p (abs-fs-fix abs-file-alist1))
             (equal (absfat-equiv abs-file-alist2 abs-file-alist1)
                    (and (hifat-equiv (abs-fs-fix abs-file-alist2)
                                      (abs-fs-fix abs-file-alist1))
                         (m1-file-alist-p (abs-fs-fix abs-file-alist2)))))
    :hints
    (("goal"
      :in-theory (e/d (absfat-equiv hifat-equiv abs-fs-p
                                    absfat-subsetp-correctness-1 abs-fs-fix)
                      (absfat-equiv-implies-equal-m1-file-alist-p-of-abs-fs-fix-lemma-1))
      :use absfat-equiv-implies-equal-m1-file-alist-p-of-abs-fs-fix-lemma-1
      :do-not-induct t)))))

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

(defthm
  names-at-when-prefixp
  (implies (and (prefixp (fat32-filename-list-fix x)
                         (fat32-filename-list-fix y))
                (not (consp (names-at fs x))))
           (not (consp (names-at fs y))))
  :hints
  (("goal" :in-theory (e/d (names-at abs-fs-fix)
                           ((:rewrite member-of-remove)))
    :induct (mv (fat32-filename-list-prefixp x y)
                (names-at fs x))
    :expand (names-at fs y))
   ("subgoal *1/1''" :use (:instance (:rewrite member-of-remove)
                                     (x (strip-cars (abs-fs-fix fs)))
                                     (b nil)
                                     (a (fat32-filename-fix (car y)))))))

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
     (abs-file (abs-file->d-e (cdr (assoc-equal name abs-file-alist1)))
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
      (abs-file (abs-file->d-e (cdr (assoc-equal name abs-file-alist1)))
                abs-file-alist2)
      abs-file-alist1))
    :expand (abs-file-alist-p abs-file-alist1))))

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
                     (:rewrite abs-fs-p-correctness-1)
                     (:rewrite prefixp-of-append-arg1)
                     (:rewrite prefixp-of-append-arg2))))))

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
                                     abs-addrs-of-ctx-app-lemma-2))))

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
    (e/d (collapse abs-addrs-of-ctx-app-lemma-2)
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
   (and
    (equal (abs-addrs (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                        frame))))
           nil)
    (abs-complete (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                    frame))))))
  :hints (("goal" :in-theory (enable 1st-complete abs-complete))))

(defthm
  abs-separate-of-frame->frame-of-collapse-this-lemma-10
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

(defthm
  abs-separate-of-frame->frame-of-collapse-this-lemma-17
  (implies
   (and (< 0 (1st-complete frame))
        (no-duplicatesp-equal (strip-cars frame)))
   (abs-complete (frame-val->dir$inline (cdr (assoc-equal (1st-complete frame)
                                                          frame)))))
  :hints
  (("goal" :do-not-induct t
    :in-theory
    (e/d (collapse abs-complete)
         ((:definition no-duplicatesp-equal)
          (:rewrite remove-assoc-of-remove-assoc)
          (:definition remove-assoc-equal)
          (:rewrite remove-assoc-of-put-assoc)
          (:definition member-equal)
          (:rewrite abs-file-alist-p-when-m1-file-alist-p)
          (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p))))))

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
    (abs-complete
     (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
    (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (abs-separate (frame->frame (collapse-this frame x))))
  :hints
  (("goal"
    :cases ((equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                   0)))))

;; This theorem is the reason for a lot of
;; (atom (frame-val->path (cdr (assoc-equal 0 frame))))
;; hypotheses. Without such a hypothesis, there would be no way to say that the
;; second argument of dist-names is nil.
(defthm
  dist-names-of-frame->root-and-frame->frame
  (implies (and (atom (frame-val->path (cdr (assoc-equal 0 frame))))
                (abs-separate frame))
           (dist-names (frame->root frame)
                       nil (frame->frame frame)))
  :hints (("goal" :in-theory (e/d (abs-separate frame->root frame->frame)))))

(defthm abs-separate-of-frame->frame
  (implies (abs-separate frame)
           (abs-separate (frame->frame frame)))
  :hints (("goal" :in-theory (e/d (abs-separate frame->frame)))))

(defthm abs-separate-of-frame-with-root
  (equal (abs-separate (frame-with-root root frame))
         (and (no-duplicatesp-equal (abs-addrs (abs-fs-fix root)))
              (dist-names root nil frame)
              (abs-separate frame)))
  :hints (("goal" :in-theory (enable frame-with-root abs-separate))))

(defthm
  abs-separate-of-collapse-this-lemma-1
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

;; Obtained by replacing (1st-complete frame) with x in the proof-builder.
(defthm
  abs-separate-of-collapse-this-lemma-2
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

(defthmd
  abs-separate-of-collapse-this-lemma-3
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
  abs-separate-of-collapse-this-lemma-4
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
    :use (:instance abs-separate-of-collapse-this-lemma-3
                    (src (frame-val->src (cdr (assoc-equal x frame))))
                    (dir (frame-val->dir (cdr (assoc-equal x frame))))
                    (relpath (frame-val->path (cdr (assoc-equal x frame))))
                    (frame (remove-assoc-equal x frame))))))

(defthm
  abs-separate-of-collapse-this-lemma-5
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
  abs-separate-of-collapse-this-lemma-6
  (implies (abs-separate frame)
           (no-duplicatesp-equal (abs-addrs (frame->root frame))))
  :hints (("goal" :in-theory (enable frame->root))))

(defthm
  abs-separate-of-collapse-this-1
  (implies
   (and
    (abs-separate frame)
    (frame-p (frame->frame frame))
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
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
    (abs-complete
     (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))))
   (abs-separate (collapse-this frame x)))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (collapse-this)
                           (WHEN-CONSP-ASSOC-OF-FRAME->FRAME-1)))))

(defthm
  abs-separate-of-collapse-this-2
  (implies
   (and
    (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
           0)
    (abs-separate frame)
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame)))))
    (ctx-app-ok (frame->root frame)
                x
                (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))
    (abs-complete
     (frame-val->dir (cdr (assoc-equal x (frame->frame frame))))))
   (abs-separate (collapse-this frame x)))
  :hints (("goal" :do-not-induct t
           :in-theory (enable collapse-this))))

(defthm
  abs-separate-of-collapse-this-lemma-7
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
          (:definition remove-assoc-equal)
          (:rewrite remove-assoc-of-remove-assoc)
          (:rewrite abs-file-alist-p-when-m1-file-alist-p)
          (:rewrite put-assoc-equal-without-change . 2)
          (:type-prescription abs-addrs-of-remove-assoc-lemma-1)))
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
  abs-separate-of-collapse-this
  (implies
   (and
    (frame-p frame)
    (mv-nth 1 (collapse frame))
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (consp (assoc-equal x (frame->frame frame)))
    (abs-complete (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
    (abs-separate frame)
    (not (consp (frame-val->path (cdr (assoc-equal 0 frame))))))
   (abs-separate (collapse-this frame x)))
  :hints
  (("goal"
    :do-not-induct t
    :cases ((equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                   0)))))

(defund frame-addrs-root (frame)
  (declare (xargs :guard (frame-p frame)))
  (cond ((atom frame) nil)
        ((zp (frame-val->src (cdar frame)))
         (cons (caar frame) (frame-addrs-root (cdr frame))))
        (t (frame-addrs-root (cdr frame)))))

(defthm
  frame-addrs-root-of-put-assoc
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

(defthm frame-addrs-root-of-remove-assoc
  (implies (frame-p frame)
           (equal (frame-addrs-root (remove-assoc-equal name frame))
                  (remove-equal name (frame-addrs-root frame))))
  :hints (("goal" :in-theory (enable frame-addrs-root))))

(defthm
  member-of-frame-addrs-root
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
  subsetp-of-frame-addrs-root-strip-cars
  (subsetp-equal (frame-addrs-root frame)
                 (strip-cars frame))
  :hints (("goal" :in-theory (enable frame-addrs-root)))
  :rule-classes
  ((:rewrite :corollary (implies (subsetp-equal x (frame-addrs-root frame))
                                 (subsetp-equal x (strip-cars frame))))))

(defthm
  frame-addrs-root-of-frame->frame-of-collapse-this-lemma-1
  (implies
   (ctx-app-ok
    (frame-val->dir
     (cdr
      (assoc-equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
                   (frame->frame frame))))
    x
    (nthcdr
     (len
      (frame-val->path
       (cdr (assoc-equal
             (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
             (frame->frame frame)))))
     (frame-val->path (cdr (assoc-equal x (frame->frame frame))))))
   (consp
    (assoc-equal
     (frame-val->src$inline (cdr (assoc-equal x (frame->frame frame))))
     (frame->frame frame))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable collapse-this))))

(defthm
  frame-addrs-root-of-frame->frame-of-collapse-this-2
  (implies
   (and
    (abs-complete (frame-val->dir (cdr (assoc-equal x (frame->frame frame)))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars (frame->frame frame)))
    (< 0 x)
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
      (frame-val->path (cdr (assoc-equal x (frame->frame frame)))))))
   (equal (frame-addrs-root (frame->frame (collapse-this frame x)))
          (frame-addrs-root (frame->frame frame))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable collapse-this))))

(defthm
  frame-addrs-root-of-frame->frame-of-collapse-this-1
  (implies
   (and (equal (frame-val->src (cdr (assoc-equal x (frame->frame frame))))
               0)
        (frame-p frame))
   (equal (frame-addrs-root (frame->frame (collapse-this frame x)))
          (remove-equal x
                        (frame-addrs-root (frame->frame frame)))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable collapse-this))))

;; Inductive, hence kept.
(defthm
  abs-separate-correctness-lemma-3
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
    (abs-file-alist-p abs-file-alist2)
    (subsetp-equal
     (abs-addrs abs-file-alist2)
     (abs-addrs
      (abs-file->contents (cdr (assoc-equal name abs-file-alist1))))))
   (subsetp-equal
    (abs-addrs (put-assoc-equal name (abs-file d-e abs-file-alist2)
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

;; Inductive, hence kept.
(defthm
  abs-separate-correctness-lemma-7
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

;; Inductive, hence kept.
(defthm
  abs-separate-correctness-lemma-10
  (implies (abs-file-alist-p x)
           (subsetp-equal (remove-equal nil (strip-cars (abs-fs-fix x)))
                          (remove-equal nil (strip-cars x))))
  :hints (("goal" :in-theory (enable abs-fs-fix abs-file-fix
                                     abs-file->contents abs-file-alist-p))))

(encapsulate
  ()

  (local
   (defthm
     lemma
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
                               (frame->frame frame)))))))))))))

  (defthmd
    abs-separate-correctness-lemma-5
    (implies
     (and (no-duplicatesp-equal (strip-cars (frame->frame frame)))
          (frame-p (frame->frame frame)))
     (subsetp-equal (abs-addrs (mv-nth 0 (collapse frame)))
                    (abs-addrs (frame->root frame))))
    :hints (("goal" :in-theory (enable collapse collapse-this)))))

(defthm
  abs-separate-correctness-lemma-6
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
                                     abs-addrs-of-ctx-app-lemma-2))))

(defthm
  abs-separate-correctness-lemma-4
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
  abs-separate-correctness-lemma-9
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
  :hints (("goal" :in-theory (e/d (collapse-this)
                                  (abs-separate-of-collapse-this-lemma-5)))))

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
                                     abs-addrs-of-ctx-app-lemma-2))))

(defthm
  abs-separate-correctness-lemma-1
  (equal (frame-val->path (cdr (assoc-equal 0 (frame-with-root root frame))))
         nil)
  :hints (("goal" :do-not-induct t
           :in-theory (enable frame-with-root))))

(defthm abs-separate-correctness-lemma-2
  (not
   (consp (frame-val->path (cdr (assoc-equal 0 (collapse-this frame x))))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable collapse-this)))
  :rule-classes :type-prescription)

(defthm
  abs-separate-correctness-2
  (implies (and (frame-p (frame->frame frame))
                (no-duplicatesp-equal (strip-cars (frame->frame frame)))
                (subsetp (abs-addrs (frame->root frame))
                         (frame-addrs-root (frame->frame frame)))
                (abs-separate frame)
                (atom (frame-val->path (cdr (assoc-equal 0 frame)))))
           (mv-let (fs result)
             (collapse frame)
             (implies (equal result t)
                      (and (m1-file-alist-p fs)
                           (hifat-no-dups-p fs)))))
  :hints
  (("goal" :in-theory (enable collapse intersectp-equal
                              abs-complete-when-atom-abs-addrs)
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

(defthm
  different-from-own-src-1
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
    (e/d (collapse abs-separate abs-addrs-of-ctx-app-lemma-2)
         ((:definition remove-assoc-equal)
          (:rewrite remove-assoc-when-absent-1)
          (:definition member-equal)
          (:definition len))))))

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
  collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-1
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
                     (:definition member-equal)
                     (:rewrite partial-collapse-correctness-lemma-2))))))

(defthm collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-2
  (implies (and (not (zp x))
                (atom (assoc-equal x frame)))
           (not (equal x (1st-complete frame)))))

(defthm
  collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-3
  (implies (mv-nth 1 (collapse frame))
           (iff (equal (1st-complete (frame->frame frame))
                       (1st-complete (frame->frame (collapse-iter frame n))))
                (or (zp (1st-complete (frame->frame frame)))
                    (zp n))))
  :hints (("goal" :in-theory (enable collapse collapse-iter))))

(defthmd
  collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-4
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
  collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-5
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
  (("goal" :in-theory (e/d (collapse collapse-iter abs-addrs-of-ctx-app-lemma-2)
                           ((:definition strip-cars)
                            (:definition assoc-equal)
                            (:rewrite nthcdr-when->=-n-len-l)
                            (:definition member-equal)
                            (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8
                                      . 2)
                            (:definition len)
                            (:definition nthcdr)))
    :use (:instance (:rewrite collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-4)
                    (n (+ -1 n))
                    (frame (collapse-iter frame 1))))))

(defthm
  collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-6
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
    :use (:instance (:rewrite collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-4)
                    (n (+ -1 n))
                    (frame (collapse-iter frame 1))))))

(defthm
  collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-7
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
          (:rewrite nthcdr-when->=-n-len-l)
          (:definition strip-cars)
          (:rewrite member-of-abs-addrs-when-natp . 2)
          (:definition nthcdr)
          (:rewrite ctx-app-ok-when-abs-complete)
          (:type-prescription abs-addrs-of-remove-assoc-lemma-1)
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

(defthm collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-8
  (implies (and (consp (assoc-equal x frame))
                (frame-p frame))
           (natp x))
  :rule-classes :forward-chaining)

(defthm
  collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-9
  (implies
   (and (mv-nth 1 (collapse frame))
        (consp (assoc-equal x (frame->frame frame)))
        (no-duplicatesp-equal (strip-cars (frame->frame frame))))
   (not (equal (1st-complete (frame->frame frame))
               (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))))
  :hints
  (("goal"
    :in-theory
    (disable (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8
                       . 2))
    :use
    (:instance (:rewrite abs-separate-of-frame->frame-of-collapse-this-lemma-8
                         . 2)
               (frame frame)
               (x x)
               (y (1st-complete (frame->frame frame)))))))

(defthm
  collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-10
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
    :in-theory
    (e/d
     (collapse-iter)
     ((:rewrite
       collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-7)))
    :use
    ((:instance
      (:rewrite
       collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-7)
      (x x)
      (n 1)
      (frame frame))
     (:instance
      (:rewrite
       collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-lemma-7)
      (x (frame-val->src (cdr (assoc-equal x (frame->frame frame)))))
      (n 1)
      (frame frame)))
    :expand (collapse-iter frame 1))))

(defthm
  collapse-1st-index-of-frame-val->src-of-cdr-of-assoc-linear-1
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

(defthm
  frame-val->src-of-cdr-of-assoc-when-member-of-frame-addrs-before
  (implies (member-equal y (frame-addrs-before frame x n))
           (equal (frame-val->src (cdr (assoc-equal y (frame->frame frame))))
                  x))
  :hints (("goal" :in-theory (enable frame-addrs-before collapse-iter)
           :induct (frame-addrs-before frame x n)
           :expand (collapse-iter frame 1))))

(defund good-frame-p (frame)
  (b*
      (((mv & result) (collapse frame)))
    (and result
         (atom (frame-val->path (cdr (assoc-equal 0 frame))))
         (consp (assoc-equal 0 frame))
         (equal (frame-val->src (cdr (assoc-equal 0 frame)))
                0)
         (frame-p frame)
         (no-duplicatesp-equal (strip-cars frame))
         (abs-separate frame)
         (subsetp-equal (abs-addrs (frame->root frame))
                        (frame-addrs-root (frame->frame frame))))))

(defund collapse-equiv (frame1 frame2)
  (b* ((good-frame-p1 (good-frame-p frame1))
       (good-frame-p2 (good-frame-p frame2))
       ((mv fs1 &) (collapse frame1))
       ((mv fs2 &) (collapse frame2)))
    (or (not (or good-frame-p1 good-frame-p2))
        (and good-frame-p1
             good-frame-p2 (absfat-equiv fs1 fs2)))))

(defequiv collapse-equiv
  :hints (("goal" :in-theory (enable collapse-equiv))))

(defthm
  collapse-of-frame-with-root-of-frame->root-and-frame->frame
  (equal (collapse (frame-with-root (frame->root frame)
                                    (frame->frame frame)))
         (collapse frame))
  :hints
  (("goal"
    :in-theory
    (e/d (collapse collapse-this)
         ((:definition no-duplicatesp-equal)
          (:definition assoc-equal)
          (:rewrite prefixp-when-equal-lengths)
          (:definition remove-equal)
          (:rewrite strip-cars-of-remove-assoc)
          (:rewrite assoc-after-put-assoc)
          (:rewrite strip-cars-of-put-assoc)
          (:rewrite no-duplicatesp-of-strip-cars-of-frame->frame)
          (:definition remove-assoc-equal)
          (:rewrite remove-when-absent)
          (:rewrite remove-assoc-of-put-assoc)
          (:rewrite remove-assoc-of-remove-assoc)
          abs-separate-of-frame->frame-of-collapse-this-lemma-8))
    :do-not-induct t
    :expand ((collapse frame)
             (collapse (frame-with-root (frame->root frame)
                                        (frame->frame frame)))))))

;; I guess I should say that this function can only really do so much, and if
;; we try to use this in our proofs we'll kinda be back to representing
;; filesystem trees as... filesystem trees. When I say it can only do so much,
;; I mean that it can only help us do some refinement proofs, which will tie
;; lofat to hifat and hifat to absfat. Ultimately, I guess we'll want theorems
;; that use the collapse-equiv relation defined previously...
(defund frame-reps-fs
    (frame fs)
  (b*
      (((mv fs-equiv result) (collapse frame)))
    (and result
         (hifat-equiv fs-equiv fs)
         (frame-p frame)
         (abs-separate frame)
         (subsetp-equal
          (abs-addrs (frame->root frame))
          (frame-addrs-root (frame->frame frame)))
         (no-duplicatesp-equal (strip-cars frame))
         (atom (frame-val->path (cdr (assoc-equal 0 frame))))
         (consp (assoc-equal 0 frame))
         (equal (frame-val->src (cdr (assoc-equal 0 frame)))
                0))))

(defthm frame-reps-fs-of-collapse-1
  (implies (good-frame-p frame)
           (frame-reps-fs frame (mv-nth 0 (collapse frame))))
  :hints (("goal" :in-theory (enable good-frame-p frame-reps-fs))))

(defthm good-frame-p-when-frame-reps-fs
  (implies (frame-reps-fs frame fs)
           (good-frame-p frame))
  :hints (("goal" :do-not-induct t
           :in-theory (enable good-frame-p frame-reps-fs))))

(defcong hifat-equiv equal (frame-reps-fs frame fs) 2
  :hints (("Goal" :in-theory (enable frame-reps-fs))))

(defcong collapse-equiv equal (frame-reps-fs frame fs) 1
  :hints (("Goal" :in-theory (enable frame-reps-fs collapse-equiv
                                     good-frame-p)
           :do-not-induct t))
  :otf-flg t)

(defthm frame-reps-fs-correctness-1
  (implies (frame-reps-fs frame fs)
           (hifat-equiv (mv-nth 0 (collapse frame))
                        fs))
  :hints (("goal" :in-theory (enable frame-reps-fs))))
