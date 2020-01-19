(in-package "ACL2")

(include-book "hifat")
(local (include-book "std/lists/prefixp" :dir :system))

;  abstract-separate.lisp                               Mihir Mehta

; This is a model of the FAT32 filesystem, related to HiFAT but with abstract
; variables.

(defthm
  prefixp-of-fat32-filename-list-fix
  (implies (prefixp x y)
           (prefixp (fat32-filename-list-fix x)
                    (fat32-filename-list-fix y)))
  :hints (("goal" :in-theory (enable prefixp fat32-filename-list-fix))))

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

(defund abs-directory-file-p (file)
  (declare (xargs :guard t))
  (and (abs-file-p file)
       (abs-file-alist-p (abs-file->contents file))))

(defthm
  abs-file-alist-p-when-m1-file-alist-p
  (implies (m1-file-alist-p x)
           (abs-file-alist-p x))
  :hints (("goal" :in-theory (enable abs-file-alist-p
                                     m1-file-alist-p))))

(defthm
  abs-file-contents-p-when-m1-file-contents-p
  (implies (m1-file-contents-p contents)
           (abs-file-contents-p contents))
  :hints (("goal" :in-theory (enable m1-file-contents-p
                                     abs-file-contents-p))))

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

(defthm
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
           :expand (abs-file-alist-p x))))

(defthm abs-file-alist-p-correctness-1-lemma-4
  (implies (stringp x)
           (not (abs-file-alist-p x)))
  :hints (("goal" :in-theory (enable abs-file-alist-p)))
  :rule-classes :type-prescription)

;; This theorem states that an abstract filesystem tree without any body
;; addresses is just a HiFAT instance.
(defthm
  abs-file-alist-p-correctness-1
  (implies (and (abs-file-alist-p x)
                (abs-complete x))
           (m1-file-alist-p x))
  :hints (("goal" :in-theory (enable abs-file-alist-p abs-complete)
           :induct (abs-complete x))))

(defthm abs-file-alist-p-of-put-assoc-equal
  (implies (and (fat32-filename-p name)
                (abs-file-p val)
                (abs-file-alist-p alist))
           (abs-file-alist-p (put-assoc-equal name val alist)))
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

;; For this function, it might be worth investing in the abs-file-alist-fix
;; thing, but that function just generally seems like a placeholder fixer and
;; I'm not going there for now. The purpose of this function is to quickly
;; allow a given abstract variable to be found in the frame - just keep looking
;; at the (abs-addrs ...) of all the elements in the frame.
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

(defthm abs-complete-definition
  (equal (abs-complete x)
         (atom (abs-addrs x)))
  :rule-classes :definition
  :hints (("goal" :in-theory (enable abs-complete abs-addrs))))

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
(defund context-apply
  (abs-file-alist1 abs-file-alist2 x x-path)
  (declare (xargs :guard
                  (and
                   (abs-file-alist-p abs-file-alist1)
                   (natp x)
                   (abs-file-alist-p abs-file-alist2)
                   (fat32-filename-list-p x-path))
                  :verify-guards nil))
  (b*
      (((when (and (consp x-path)
                   (consp (abs-assoc (car x-path) abs-file-alist1))
                   (abs-directory-file-p
                    (cdr (abs-assoc (car x-path) abs-file-alist1)))))
        (abs-put-assoc
         (car x-path)
         (abs-file
          (abs-file->dir-ent (cdr (abs-assoc (car x-path) abs-file-alist1)))
          (context-apply
           (abs-file->contents (cdr (abs-assoc (car x-path) abs-file-alist1)))
           abs-file-alist2
           x
           (cdr x-path)))
         abs-file-alist1))
       ;; This is actually an error condition.
       ((when (consp x-path))
        abs-file-alist1)
       ((when (member x abs-file-alist1))
        (append (remove x abs-file-alist1) abs-file-alist2)))
    abs-file-alist1))

(defthm abs-file-alist-p-of-context-apply-lemma-1
  (implies (and (abs-file-alist-p alist)
                (not (fat32-filename-p x)))
           (not (consp (assoc-equal x alist))))
  :hints (("goal" :in-theory (enable abs-file-alist-p))))

(defthm
  abs-file-alist-p-of-context-apply-lemma-2
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
  (("goal" :in-theory (disable abs-file-alist-p-of-context-apply-lemma-1)
    :use (:instance abs-file-alist-p-of-context-apply-lemma-1
                    (alist abs-file-alist1)
                    (x (car x-path))))))

(defthm abs-file-alist-p-of-context-apply
  (implies
   (and
    (abs-file-alist-p abs-file-alist1)
    (abs-file-alist-p abs-file-alist2))
   (abs-file-alist-p
    (context-apply
     abs-file-alist1 abs-file-alist2 x x-path)))
  :hints
  (("Goal" :in-theory (enable context-apply))))

(verify-guards context-apply
  :guard-debug t
  :hints (("Goal" :in-theory (enable abs-file-alist-p)) ))

(defthm abs-addrs-of-append
  (equal (abs-addrs (append x y))
         (append (abs-addrs x) (abs-addrs y)))
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
  abs-no-dups-p-of-cdr-of-assoc
  (implies (and (abs-file-alist-p fs)
                (abs-no-dups-p fs)
                (abs-directory-file-p (cdr (assoc-equal name fs))))
           (abs-no-dups-p (abs-file->contents (cdr (assoc-equal name fs)))))
  :hints (("goal" :in-theory (enable abs-no-dups-p)
           :expand (abs-file-alist-p fs))))

(defthm abs-addrs-of-context-apply-1-lemma-1
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

(defthm abs-addrs-of-context-apply-1-lemma-2
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
   (and
    (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
    (member-equal
     x
     (abs-addrs
      (abs-file->contents (cdr (assoc-equal name abs-file-alist1))))))
   (member-equal x (abs-addrs abs-file-alist1)))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm abs-addrs-of-context-apply-1-lemma-7
  (implies (and (natp x)
                (not (member-equal x (abs-addrs abs-file-alist1))))
           (equal (context-apply abs-file-alist1
                                     abs-file-alist2 x x-path)
                  abs-file-alist1))
  :hints (("goal" :in-theory (enable abs-addrs context-apply)
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

(defthm
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
   (and
    (abs-directory-file-p (cdr (assoc-equal (car x-path)
                                            abs-file-alist1)))
    (not
     (member-equal
      x
      (abs-addrs (context-apply
                  (abs-file->contents (cdr (assoc-equal (car x-path)
                                                        abs-file-alist1)))
                  abs-file-alist2 x (cdr x-path)))))
    (integerp x)
    (<= 0 x)
    (no-duplicatesp-equal (abs-addrs abs-file-alist1))
    (not
     (equal
      (put-assoc-equal
       (car x-path)
       (abs-file (abs-file->dir-ent (cdr (assoc-equal (car x-path)
                                                      abs-file-alist1)))
                 (context-apply
                  (abs-file->contents (cdr (assoc-equal (car x-path)
                                                        abs-file-alist1)))
                  abs-file-alist2 x (cdr x-path)))
       abs-file-alist1)
      abs-file-alist1))
    (abs-no-dups-p abs-file-alist1)
    (abs-file-alist-p abs-file-alist1)
    (abs-file-alist-p abs-file-alist2))
   (not
    (member-equal
     x
     (abs-addrs
      (put-assoc-equal
       (car x-path)
       (abs-file (abs-file->dir-ent (cdr (assoc-equal (car x-path)
                                                      abs-file-alist1)))
                 (context-apply
                  (abs-file->contents (cdr (assoc-equal (car x-path)
                                                        abs-file-alist1)))
                  abs-file-alist2 x (cdr x-path)))
       abs-file-alist1)))))
  :hints
  (("goal"
    :in-theory (disable put-assoc-equal-without-change
                        (:rewrite abs-addrs-of-context-apply-1-lemma-7)
                        (:rewrite abs-addrs-of-context-apply-1-lemma-11))
    :use
    ((:instance
      put-assoc-equal-without-change
      (alist abs-file-alist1)
      (val
       (abs-file (abs-file->dir-ent (cdr (assoc-equal (car x-path)
                                                      abs-file-alist1)))
                 (context-apply
                  (abs-file->contents (cdr (assoc-equal (car x-path)
                                                        abs-file-alist1)))
                  abs-file-alist2 x (cdr x-path))))
      (name (car x-path)))
     (:instance
      (:rewrite abs-addrs-of-context-apply-1-lemma-7)
      (x-path (cdr x-path))
      (x x)
      (abs-file-alist2 abs-file-alist2)
      (abs-file-alist1
       (abs-file->contents (cdr (assoc-equal (car x-path)
                                             abs-file-alist1)))))
     (:instance (:rewrite abs-addrs-of-context-apply-1-lemma-11)
                (abs-file-alist1 abs-file-alist1)
                (name (car x-path))
                (x x)))
    :do-not-induct t)))

;; There's a way of saying the same thing...
;; (implies (not (equal
;;                (context-apply
;;                 abs-file-alist1 abs-file-alist2 x x-path)
;;                abs-file-alist1))
;;          (equal (abs-addrs
;;                  (context-apply
;;                   abs-file-alist1 abs-file-alist2 x x-path))
;;                 (remove x (abs-addrs abs-file-alist1))))
;; ...that's very likely going to be tough to prove, so, let's leave it alone.
(defthm
  abs-addrs-of-context-apply-1
  (implies
   (and (natp x)
        (no-duplicatesp-equal (abs-addrs abs-file-alist1))
        (not (equal (context-apply abs-file-alist1
                                       abs-file-alist2 x x-path)
                    abs-file-alist1))
        (not (intersectp-equal (abs-addrs abs-file-alist1)
                               (abs-addrs abs-file-alist2)))
        (abs-no-dups-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist2))
   (not
    (member-equal x
                  (abs-addrs (context-apply abs-file-alist1
                                                abs-file-alist2 x x-path)))))
  :hints (("goal" :in-theory (enable abs-addrs context-apply)
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
  abs-addrs-of-context-apply-2-lemma-2
  (implies
   (no-duplicatesp-equal (abs-addrs abs-file-alist1))
   (no-duplicatesp-equal (abs-addrs (remove-equal x abs-file-alist1))))
  :hints
  (("goal"
    :in-theory (e/d (abs-addrs)
                    (intersectp-is-commutative))
    :expand
    ((:with intersectp-is-commutative
            (intersectp-equal
             (abs-addrs (abs-file->contents (cdr (car abs-file-alist1))))
             (abs-addrs (remove-equal x (cdr abs-file-alist1)))))
     (:with intersectp-is-commutative
            (intersectp-equal
             (abs-addrs (abs-file->contents (cdr (car abs-file-alist1))))
             (abs-addrs (cdr abs-file-alist1))))))))

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
  abs-addrs-of-context-apply-2-lemma-6
  (subsetp-equal (abs-addrs (remove-assoc-equal name abs-file-alist))
                 (abs-addrs abs-file-alist))
  :hints (("goal" :in-theory (enable abs-addrs))))

(defthm
  abs-addrs-of-context-apply-2-lemma-4
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal (car x-path)
                                            abs-file-alist1)))
    (not
     (intersectp-equal
      (abs-addrs (context-apply
                  (abs-file->contents (cdr (assoc-equal (car x-path)
                                                        abs-file-alist1)))
                  abs-file-alist2 x (cdr x-path)))
      y))
    (abs-file-alist-p abs-file-alist2)
    (not (intersectp-equal (abs-addrs abs-file-alist1)
                           y))
    (abs-file-alist-p abs-file-alist1)
    (abs-no-dups-p abs-file-alist1))
   (not
    (intersectp-equal
     (abs-addrs
      (put-assoc-equal
       (car x-path)
       (abs-file (abs-file->dir-ent (cdr (assoc-equal (car x-path)
                                                      abs-file-alist1)))
                 (context-apply
                  (abs-file->contents (cdr (assoc-equal (car x-path)
                                                        abs-file-alist1)))
                  abs-file-alist2 x (cdr x-path)))
       abs-file-alist1))
     y)))
  :hints
  (("goal"
    :use (:instance (:rewrite intersect-with-subset)
                    (z y)
                    (y (abs-addrs abs-file-alist1))
                    (x (abs-addrs (remove-assoc-equal (car x-path)
                                                      abs-file-alist1)))))))

(defthm
  abs-addrs-of-context-apply-2-lemma-7
  (implies
   (and (abs-file-alist-p abs-file-alist2)
        (not (intersectp-equal (abs-addrs abs-file-alist1)
                               y))
        (not (intersectp-equal (abs-addrs abs-file-alist2)
                               y))
        (abs-file-alist-p abs-file-alist1)
        (abs-no-dups-p abs-file-alist1))
   (not
    (intersectp-equal (abs-addrs (context-apply abs-file-alist1
                                                    abs-file-alist2 x x-path))
                      y)))
  :hints (("goal" :in-theory (e/d ((:definition abs-addrs)
                                   context-apply)
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
  abs-addrs-of-context-apply-2-lemma-5
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal name abs-file-alist1)))
    (no-duplicatesp-equal (abs-addrs abs-file-alist1))
    (not
     (intersectp-equal (abs-addrs (remove-assoc-equal name abs-file-alist1))
                       (abs-addrs abs-file-alist2)))
    (abs-no-dups-p abs-file-alist1)
    (abs-file-alist-p abs-file-alist1)
    (abs-file-alist-p abs-file-alist2)
    (no-duplicatesp-equal (abs-addrs abs-file-alist2)))
   (no-duplicatesp-equal
    (abs-addrs
     (put-assoc-equal
      name
      (abs-file (abs-file->dir-ent (cdr (assoc-equal name abs-file-alist1)))
                abs-file-alist2)
      abs-file-alist1))))
  :hints (("goal" :in-theory (e/d ((:definition abs-addrs)
                                   intersectp-equal)
                                  (intersectp-is-commutative)))))
(defthm
  abs-addrs-of-context-apply-2-lemma-13
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
  abs-addrs-of-context-apply-2-lemma-16
  (implies
   (and (abs-directory-file-p (cdr (assoc-equal (car x-path)
                                                abs-file-alist1)))
        (no-duplicatesp-equal (abs-addrs abs-file-alist1))
        (not (intersectp-equal (abs-addrs abs-file-alist1)
                               (abs-addrs abs-file-alist2)))
        (abs-no-dups-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist2))
   (not
    (intersectp-equal
     (abs-addrs (remove-assoc-equal (car x-path)
                                    abs-file-alist1))
     (abs-addrs
      (context-apply
       (abs-file->contents$inline (cdr (assoc-equal (car x-path)
                                                    abs-file-alist1)))
       abs-file-alist2 x (cdr x-path))))))
  :hints
  (("goal"
    :in-theory (disable intersectp-is-commutative)
    :do-not-induct t
    :expand
    (:with
     intersectp-is-commutative
     (intersectp-equal
      (abs-addrs (remove-assoc-equal (car x-path)
                                     abs-file-alist1))
      (abs-addrs
       (context-apply
        (abs-file->contents$inline (cdr (assoc-equal (car x-path)
                                                     abs-file-alist1)))
        abs-file-alist2 x (cdr x-path))))))))

(defthm
  abs-addrs-of-context-apply-2
  (implies (and (no-duplicatesp-equal (abs-addrs abs-file-alist1))
                (not (intersectp-equal (abs-addrs abs-file-alist1)
                                       (abs-addrs abs-file-alist2)))
                (abs-no-dups-p abs-file-alist1)
                (abs-file-alist-p abs-file-alist1)
                (abs-file-alist-p abs-file-alist2)
                (no-duplicatesp-equal (abs-addrs abs-file-alist2)))
           (no-duplicatesp-equal
            (abs-addrs (context-apply abs-file-alist1
                                          abs-file-alist2 x x-path))))
  :hints (("goal" :in-theory (enable abs-addrs context-apply)
           :induct (context-apply abs-file-alist1
                                      abs-file-alist2 x x-path))))

(defund
  abs-file-alist-fix (x)
  (declare
   (xargs
    :guard (abs-file-alist-p x)
    :guard-hints (("goal" :expand (abs-file-alist-p x)
                   :in-theory (enable abs-file-p)))))
  (b* (((when (atom x)) nil)
       (head (car x))
       ((when (atom head))
        (cons (nfix head)
              (abs-file-alist-fix (cdr x)))))
    (cons (cons (fat32-filename-fix (car head))
                (abs-file-fix (cdr head)))
          (abs-file-alist-fix (cdr x)))))

(encapsulate
  () ;; start lemmas for abs-file-alist-fix-when-abs-file-alist-p

  (local
   (defthm abs-file-alist-fix-when-abs-file-alist-p-lemma-1
     (implies (and (alistp (cddr (car x)))
                   (equal (car (cadr (car x))) 'dir-ent)
                   (equal (strip-cars (cddr (car x)))
                          '(contents))
                   (dir-ent-p (cdr (cadr (car x))))
                   (stringp (cdr (caddr (car x))))
                   (< (len (explode (cdr (caddr (car x)))))
                      4294967296))
              (abs-file-p (cdr (car x))))
     :hints (("goal" :in-theory (enable abs-file-p)))))

  (local
   (defthm abs-file-alist-fix-when-abs-file-alist-p-lemma-2
     (implies (and (alistp (cddr (car x)))
                   (equal (car (cadr (car x))) 'dir-ent)
                   (equal (strip-cars (cddr (car x)))
                          '(contents))
                   (dir-ent-p (cdr (cadr (car x))))
                   (abs-file-alist-p (cdr (caddr (car x)))))
              (abs-file-p (cdr (car x))))
     :hints (("goal" :in-theory (enable abs-file-p)))))

  (defthm
    abs-file-alist-fix-when-abs-file-alist-p
    (implies (abs-file-alist-p x)
             (equal (abs-file-alist-fix x) x))
    :hints (("goal" :in-theory (enable abs-file-alist-fix abs-file-alist-p)))))

(defthm
  abs-file-alist-p-of-abs-file-alist-fix
  (abs-file-alist-p (abs-file-alist-fix x))
  :hints (("goal" :in-theory (enable abs-file-alist-fix abs-file-alist-p
                                     abs-file-fix abs-file-contents-fix
                                     abs-file-contents-p))))

(fty::deffixtype abs-file-alist
                 :pred abs-file-alist-p
                 :fix abs-file-alist-fix
                 :equiv abs-file-alist-equiv
                 :define t
                 :forward t)

;; Both these names, below, merit some thought later...
(fty::defprod frame-val
              ((path fat32-filename-list-p)
               (dir abs-file-alist-p)
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

(defthm natp-of-1st-complete
  (natp (1st-complete frame))
  :hints (("goal" :in-theory (enable 1st-complete)))
  :rule-classes :type-prescription)

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

(defthm frame-p-of-remove-assoc-equal
  (implies (frame-p alist)
           (frame-p (remove-assoc-equal x alist)))
  :hints (("goal" :in-theory (enable frame-p))))

(defund 1st-complete-src (frame)
  (declare (xargs :guard (and (frame-p frame)
                              (consp (assoc-equal (1st-complete frame)
                                                  frame)))))
  (frame-val->src (cdr (assoc-equal (1st-complete frame) frame))))

(defund
  collapse (root frame)
  (declare (xargs :guard (and (abs-file-alist-p root)
                              (frame-p frame))
                  :measure (len frame)))
  (b*
      (((when (atom frame)) (mv root t))
       (head-index (1st-complete frame))
       ((when (zp head-index)) (mv root nil))
       (head-frame-val (cdr (assoc-equal head-index frame)))
       (src (1st-complete-src frame)))
    (if
     (zp src)
     (b*
         ((frame (remove-assoc-equal head-index frame))
          (root-after-context-apply
           (context-apply root (frame-val->dir head-frame-val)
                          head-index
                          (frame-val->path head-frame-val)))
          ((when (equal root-after-context-apply root))
           (mv root nil)))
       (collapse root-after-context-apply frame))
     (b*
         ((path (frame-val->path head-frame-val))
          ((when
            (or
             (equal src head-index)
             (atom
              (assoc-equal src
                           (remove-assoc-equal head-index frame)))))
           (mv root nil))
          (src-path
           (frame-val->path
            (cdr
             (assoc-equal src
                          (remove-assoc-equal head-index frame)))))
          (src-dir
           (frame-val->dir
            (cdr
             (assoc-equal src
                          (remove-assoc-equal head-index frame)))))
          (frame (remove-assoc-equal head-index frame))
          ((unless (prefixp src-path path))
           (mv root nil))
          (src-dir-after-context-apply
           (context-apply src-dir (frame-val->dir head-frame-val)
                          head-index
                          (nthcdr (len src-path) path)))
          ((when (equal src-dir-after-context-apply src-dir))
           (mv root nil))
          (frame
           (put-assoc-equal
            src
            (frame-val
             (frame-val->path (cdr (assoc-equal src frame)))
             src-dir-after-context-apply
             (frame-val->src (cdr (assoc-equal src frame))))
            frame)))
       (collapse root frame)))))

(assert-event
 (b*
     (((mv root result)
       (collapse
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
           1))))))
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
  (implies (abs-file-alist-p root)
           (abs-file-alist-p (mv-nth 0 (collapse root frame))))
  :hints (("goal" :in-theory (enable collapse))))

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

(defund
  names-at-relpath (fs relpath)
  (declare (xargs :guard (and (abs-file-alist-p fs)
                              (fat32-filename-list-p relpath))))
  (b*
      (((when (atom relpath))
        (abs-top-names fs))
       (head (car relpath))
       ((unless
         (and (consp (abs-assoc head fs))
              (abs-directory-file-p (cdr (abs-assoc head fs)))))
        nil))
    (names-at-relpath
     (abs-file->contents (cdr (abs-assoc head fs)))
     (cdr relpath))))

(defthm fat32-filename-list-p-of-names-at-relpath-lemma-1
  (implies (abs-file-alist-p fs)
           (fat32-filename-list-p (remove-equal nil (strip-cars fs))))
  :hints (("goal" :in-theory (enable abs-file-alist-p))))

(defthm fat32-filename-list-p-of-names-at-relpath
  (implies (abs-file-alist-p fs)
           (fat32-filename-list-p (names-at-relpath fs relpath)))
  :hints (("goal" :in-theory (enable names-at-relpath))))

(defund
  distinguish-names (dir relpath frame)
  (declare (xargs :guard (and (abs-file-alist-p dir)
                              (fat32-filename-list-p relpath)
                              (frame-p frame))))
  (b*
      (((when (atom frame)) t)
       (head-frame-val (cdar frame))
       ((when (prefixp relpath
                       (frame-val->path head-frame-val)))
        (and
         (not
          (intersectp-equal
           (names-at-relpath
            dir
            (nthcdr (len relpath)
                    (frame-val->path head-frame-val)))
           (abs-top-names (frame-val->dir head-frame-val))))
         (distinguish-names dir relpath (cdr frame))))
       ((when (prefixp (frame-val->path head-frame-val)
                       relpath))
        (and
         (not (intersectp-equal
               (names-at-relpath
                (frame-val->dir head-frame-val)
                (nthcdr (len (frame-val->path head-frame-val))
                        relpath))
               (abs-top-names dir)))
         (distinguish-names dir relpath (cdr frame)))))
    (distinguish-names dir relpath (cdr frame))))

(defthm distinguish-names-of-remove-assoc
  (implies (distinguish-names dir relpath frame)
           (distinguish-names dir
                              relpath (remove-assoc-equal x frame)))
  :hints (("goal" :in-theory (enable distinguish-names))))

(defund
  abs-separate (frame)
  (declare (xargs :guard (frame-p frame)))
  (or
   (atom frame)
   (and
    (abs-no-dups-p (frame-val->dir (cdar frame)))
    (distinguish-names
     (frame-val->dir (cdar frame))
     (frame-val->path (cdar frame))
     (cdr frame))
    (abs-separate (cdr frame)))))

(defthm abs-separate-of-remove-assoc
  (implies (abs-separate frame)
           (abs-separate (remove-assoc-equal x frame)))
  :hints (("goal" :in-theory (enable abs-separate))))

;; This is a "false" frame because the src value given to the root is 0, same
;; as its abstract variable. This is one of a few compromises in elegance
;; required for distinguishing the root, which is necessary to properly define
;; the collapse relation.
(defund frame-with-root (root frame)
  (declare (xargs :guard (and (abs-file-alist-p root)
                              (frame-p frame))))
  (list* (cons 0 (frame-val nil root 0))
         frame))

;; This is because of fixing.
(defthm frame-p-of-frame-with-root
  (equal (frame-p (frame-with-root root frame))
         (frame-p frame))
  :hints (("goal" :in-theory (enable frame-with-root))))

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

;; This has a free variable. Also, accumulated-persistence may call it useless,
;; but it is very much needed.
(defthm abs-separate-correctness-1-lemma-1
  (implies (and (abs-file-alist-p root)
                (not (consp (abs-addrs root)))
                (not (hifat-no-dups-p root)))
           (not (abs-separate (frame-with-root root frame))))
  :hints (("goal" :in-theory (enable frame-with-root abs-separate))))

(defthm
  abs-separate-correctness-1-lemma-2
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

(defthm
  abs-separate-correctness-1-lemma-3
  (implies
   (and (abs-file-alist-p abs-file-alist2)
        (atom (abs-addrs abs-file-alist2)))
   (subsetp-equal (abs-addrs (context-apply abs-file-alist1
                                                abs-file-alist2 x x-path))
                  (abs-addrs abs-file-alist1)))
  :hints (("goal" :in-theory (enable context-apply))))

(defthm abs-separate-correctness-1-lemma-4
  (implies (and (frame-p frame)
                (not (zp (1st-complete frame)))
                (no-duplicatesp-equal (strip-cars frame)))
           (equal (abs-addrs (frame-val->dir (cdr (assoc-equal
                                                   (1st-complete frame) frame))))
                  nil))
  :hints (("Goal" :in-theory (enable 1st-complete)) ))

(defthm
  abs-separate-correctness-1-lemma-5
  (implies (and (no-duplicatesp-equal (strip-cars frame))
                (frame-p frame))
           (subsetp-equal (abs-addrs (mv-nth 0 (collapse root frame)))
                          (abs-addrs root)))
  :hints (("goal" :in-theory (enable collapse))))

(defthm
  abs-separate-correctness-1-lemma-6
  (implies
   (and
    (< 0 (1st-complete frame))
    (not
     (equal
      (context-apply
       root
       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                         frame)))
       (1st-complete frame)
       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                          frame))))
      root))
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
        (context-apply
         root
         (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                           frame)))
         (1st-complete frame)
         (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                            frame))))
        (remove-assoc-equal (1st-complete frame)
                            frame)))))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (intersectp-equal)
                    (subsetp-member))
    :use
    (:instance
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
         (context-apply
          root
          (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame)))
          (1st-complete frame)
          (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                             frame))))
         (remove-assoc-equal (1st-complete frame)
                             frame)))))
     (a (1st-complete frame))))))

(defthm
  abs-separate-correctness-1-lemma-7
  (implies
   (and
    (< 0 (1st-complete frame))
    (not
     (equal
      (context-apply
       root
       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                         frame)))
       (1st-complete frame)
       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                          frame))))
      root))
    (not
     (intersectp-equal
      (remove-equal (1st-complete frame)
                    (strip-cars frame))
      (abs-addrs
       (mv-nth
        0
        (collapse
         (context-apply
          root
          (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame)))
          (1st-complete frame)
          (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                             frame))))
         (remove-assoc-equal (1st-complete frame)
                             frame))))))
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
        (context-apply
         root
         (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                           frame)))
         (1st-complete frame)
         (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                            frame))))
        (remove-assoc-equal (1st-complete frame)
                            frame)))))))
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
         (context-apply
          root
          (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame)))
          (1st-complete frame)
          (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                             frame))))
         (remove-assoc-equal (1st-complete frame)
                             frame)))))
     (l (strip-cars frame))))))

;; This has a free variable... which merits examination later.
(defthm abs-separate-correctness-1-lemma-8
  (implies (and (abs-file-alist-p root)
                (abs-separate (frame-with-root root frame)))
           (abs-no-dups-p root))
  :hints (("goal" :in-theory (enable abs-separate frame-with-root))))

(defthm
  abs-separate-correctness-1-lemma-10
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

(defthm abs-no-dups-p-of-append-lemma-2
  (implies (and (abs-no-dups-p x)
                (abs-file-alist-p x)
                (abs-file-alist-p y)
                (consp (assoc-equal (car (car x))
                                    (append (cdr x) y))))
           (member-equal (car (car x))
                         (strip-cars y)))
  :hints (("goal" :do-not-induct t
           :expand (abs-no-dups-p x)
           :cases ((equal (car (car x)) nil)))))

;; It would be nice to have fewer hypotheses and more terms in the RHS, but...
(defthm
  abs-no-dups-p-of-append
  (implies (and (abs-no-dups-p x)
                (abs-no-dups-p y)
                (abs-file-alist-p x)
                (abs-file-alist-p y))
           (equal (abs-no-dups-p (append x y))
                  (not (intersectp-equal (remove-equal nil (strip-cars x))
                                         (remove-equal nil (strip-cars y))))))
  :hints (("goal" :in-theory (e/d (abs-no-dups-p intersectp-equal)
                                  (intersectp-is-commutative))
           :induct (append x y)
           :do-not-induct t)))

(defthm abs-no-dups-p-of-remove-lemma-1
  (implies (and (not (consp (assoc-equal (car (car abs-file-alist))
                                         (cdr abs-file-alist))))
                (abs-file-alist-p (cdr abs-file-alist)))
           (not (consp (assoc-equal (car (car abs-file-alist))
                                    (remove-equal x (cdr abs-file-alist))))))
  :hints (("goal" :cases ((equal (car (car abs-file-alist))
                                 nil)))))

(defthm abs-no-dups-p-of-remove
  (implies (and (abs-file-alist-p abs-file-alist)
                (abs-no-dups-p abs-file-alist))
           (abs-no-dups-p (remove-equal x abs-file-alist)))
  :hints (("goal" :in-theory (enable abs-no-dups-p)
           :expand (abs-file-alist-p abs-file-alist)
           :induct (mv (abs-no-dups-p abs-file-alist)
                       (remove-equal x abs-file-alist)))))

(defthm member-equal-of-strip-cars-of-remove-equal
  (implies (not (member-equal x1 (strip-cars alist)))
           (not (member-equal x1
                              (strip-cars (remove-equal x2 alist)))))
  :rule-classes (:type-prescription :rewrite))

(defthm
  intersectp-equal-of-strip-cars-of-remove-equal
  (implies
   (not (intersectp-equal x1
                          (remove-equal nil (strip-cars abs-file-alist1))))
   (not (intersectp-equal
         x1
         (remove-equal nil
                       (strip-cars (remove-equal x2 abs-file-alist1))))))
  :hints (("goal" :in-theory (e/d (intersectp-equal)
                                  (intersectp-is-commutative))))
  :rule-classes (:rewrite :type-prescription))

(defthm
  abs-no-dups-p-of-context-apply
  (implies
   (and (abs-file-alist-p abs-file-alist1)
        (abs-no-dups-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist2)
        (abs-no-dups-p abs-file-alist2)
        (not (intersectp-equal (remove-equal nil (strip-cars abs-file-alist2))
                               (names-at-relpath abs-file-alist1 x-path))))
   (abs-no-dups-p (context-apply abs-file-alist1
                                     abs-file-alist2 x x-path)))
  :hints (("goal" :in-theory (enable names-at-relpath context-apply))))

(defthm
  abs-separate-correctness-1-lemma-11
  (implies
   (abs-separate frame)
   (abs-no-dups-p (frame-val->dir$inline (cdr (assoc-equal x frame)))))
  :hints (("goal" :in-theory (enable abs-separate)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (abs-separate frame)
          (abs-complete (frame-val->dir$inline (cdr (assoc-equal x frame)))))
     (hifat-no-dups-p (frame-val->dir$inline (cdr (assoc-equal x frame))))))))

(defthm
  abs-separate-correctness-1-lemma-12
  (implies
   (distinguish-names root nil frame)
   (not
    (intersectp-equal
     (remove-equal
      'nil
      (strip-cars (frame-val->dir$inline (cdr (assoc-equal x frame)))))
     (names-at-relpath
      root
      (frame-val->path$inline (cdr (assoc-equal x frame)))))))
  :hints (("goal" :in-theory (enable distinguish-names prefixp
                                     intersectp-equal names-at-relpath))))

(defthm abs-separate-correctness-1-lemma-9
  (implies (and (not (consp x))
                (fat32-filename-p (car relpath)))
           (equal (assoc-equal (car relpath)
                               (remove-equal x fs))
                  (assoc-equal (car relpath) fs)))
  :hints (("goal" :cases ((null (car relpath))))))

(defthm
  abs-separate-correctness-1-lemma-15
  (implies (and (atom x)
                (fat32-filename-list-p relpath))
           (equal (names-at-relpath (remove-equal x fs)
                                    relpath)
                  (names-at-relpath fs relpath)))
  :hints (("goal" :in-theory (enable names-at-relpath fat32-filename-list-p)
           :induct (names-at-relpath fs relpath)
           :expand (names-at-relpath (remove-equal x fs)
                                     relpath))))

(defthm
  abs-separate-correctness-1-lemma-16
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
  abs-separate-correctness-1-lemma-17
  (implies
   (and (abs-file-alist-p abs-file-alist)
        (not (prefixp x-path relpath)))
   (equal (names-at-relpath (context-apply root abs-file-alist x x-path)
                            relpath)
          (names-at-relpath root relpath)))
  :hints
  (("goal"
    :in-theory (enable prefixp
                       context-apply names-at-relpath)
    :induct t
    :expand
    (names-at-relpath
     (put-assoc-equal
      (car x-path)
      (abs-file
       (abs-file->dir-ent (cdr (assoc-equal (car x-path) root)))
       (context-apply
        (abs-file->contents (cdr (assoc-equal (car x-path) root)))
        abs-file-alist x (cdr x-path)))
      root)
     relpath))))

(defthm
  abs-separate-correctness-1-lemma-18
  (implies (and (abs-file-alist-p abs-file-alist)
                (fat32-filename-list-p relpath)
                (consp relpath))
           (equal (assoc-equal (car relpath)
                               (append (remove-equal x root)
                                       abs-file-alist))
                  (if (consp (assoc-equal (car relpath)
                                          (remove-equal x root)))
                      (assoc-equal (car relpath)
                                   (remove-equal x root))
                      (assoc-equal (car relpath)
                                   abs-file-alist))))
  :hints (("goal" :do-not-induct t
           :cases ((null (car relpath))))))

(defthm
  abs-separate-correctness-1-lemma-19
  (implies (and (abs-file-alist-p abs-file-alist)
                (consp (assoc-equal (car relpath) root))
                (consp (assoc-equal (car relpath)
                                    abs-file-alist)))
           (intersectp-equal (remove-equal nil (strip-cars abs-file-alist))
                             (remove-equal nil (strip-cars root))))
  :hints
  (("goal"
    :use (:instance (:rewrite intersectp-member)
                    (a (car relpath))
                    (y (remove-equal nil (strip-cars root)))
                    (x (remove-equal nil (strip-cars abs-file-alist)))))))

(defthm
  abs-separate-correctness-1-lemma-20
  (implies
   (and
    (abs-file-alist-p abs-file-alist)
    (fat32-filename-list-p relpath)
    (natp x)
    (prefixp x-path relpath)
    (not (intersectp-equal y
                           (names-at-relpath abs-file-alist
                                             (nthcdr (len x-path) relpath))))
    (not (intersectp-equal y (names-at-relpath root relpath))))
   (not
    (intersectp-equal
     y
     (names-at-relpath (context-apply root abs-file-alist x x-path)
                       relpath))))
  :hints (("goal" :in-theory (e/d ((:definition intersectp-equal)
                                   prefixp
                                   context-apply names-at-relpath)
                                  (intersectp-is-commutative))
           :induct t
           :expand ((names-at-relpath (append (remove-equal x root)
                                              abs-file-alist)
                                      relpath)
                    (names-at-relpath abs-file-alist relpath)))))

(defthm
  abs-separate-correctness-1-lemma-21
  (implies (and (natp x)
                (abs-file-alist-p abs-file-alist)
                (distinguish-names root nil frame)
                (distinguish-names abs-file-alist x-path frame))
           (distinguish-names (context-apply root abs-file-alist x x-path)
                              nil frame))
  :hints (("goal" :in-theory (enable distinguish-names prefixp))))

(defthm
  abs-separate-correctness-1-lemma-23
  (implies
   (and
    (prefixp relpath
             (frame-val->path (cdr (car frame))))
    (not
     (intersectp-equal
      (remove-equal nil
                    (strip-cars (frame-val->dir (cdr (car frame)))))
      (names-at-relpath dir
                        (nthcdr (len relpath)
                                (frame-val->path (cdr (car frame)))))))
    (prefixp (frame-val->path (cdr (car frame)))
             relpath))
   (not
    (intersectp-equal
     (remove-equal nil (strip-cars dir))
     (names-at-relpath (frame-val->dir (cdr (car frame)))
                       (nthcdr (len (frame-val->path (cdr (car frame))))
                               relpath)))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (list-equiv names-at-relpath)
                    ((:rewrite prefixp-when-equal-lengths)))
    :use (:instance (:rewrite prefixp-when-equal-lengths)
                    (y relpath)
                    (x (frame-val->path (cdr (car frame))))))))

(defthm
  abs-separate-correctness-1-lemma-29
  (implies (and (fat32-filename-list-p relpath)
                (prefixp (frame-val->path (cdr (car frame)))
                         relpath)
                (not (intersectp-equal (remove-equal nil (strip-cars dir))
                                       (names-at-relpath root relpath)))
                (<= (len relpath)
                    (len (frame-val->path (cdr (car frame))))))
           (not (intersectp-equal
                 (remove-equal nil (strip-cars dir))
                 (names-at-relpath root
                                   (frame-val->path (cdr (car frame)))))))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (list-equiv)
                           ((:rewrite prefixp-when-equal-lengths)))
           :use (:instance (:rewrite prefixp-when-equal-lengths)
                           (y relpath)
                           (x (frame-val->path (cdr (car frame))))))))

(defthm
  abs-separate-correctness-1-lemma-22
  (implies
   (and (distinguish-names dir relpath frame)
        (prefixp relpath
                 (frame-val->path (cdr (assoc-equal x frame)))))
   (not
    (intersectp-equal
     (remove-equal nil
                   (strip-cars (frame-val->dir (cdr (assoc-equal x frame)))))
     (names-at-relpath
      dir
      (nthcdr (len relpath)
              (frame-val->path (cdr (assoc-equal x frame))))))))
  :hints (("goal" :in-theory (enable distinguish-names
                                     prefixp intersectp-equal))))

(defthm
  abs-separate-correctness-1-lemma-24
  (implies
   (and (consp (assoc-equal x frame))
        (distinguish-names dir relpath frame)
        (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                 relpath))
   (not (intersectp-equal
         (remove-equal nil (strip-cars dir))
         (names-at-relpath
          (frame-val->dir (cdr (assoc-equal x frame)))
          (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                  relpath)))))
  :hints (("goal" :in-theory (enable distinguish-names))))

(defthm
  abs-separate-correctness-1-lemma-25
  (implies (and (consp (assoc-equal x frame))
                (abs-separate frame))
           (distinguish-names (frame-val->dir (cdr (assoc-equal x frame)))
                              (frame-val->path (cdr (assoc-equal x frame)))
                              (remove-assoc-equal x frame)))
  :hints (("goal" :in-theory (enable abs-separate distinguish-names))))

;; Obtained by replacing (1st-complete frame) with x in the proof-builder.
(defthm
  abs-separate-correctness-1-lemma-26
  (implies
   (and (consp (assoc-equal x frame))
        (integerp x)
        (< 0 x)
        (distinguish-names root nil frame)
        (abs-separate frame))
   (distinguish-names
    (context-apply root
                       (frame-val->dir (cdr (assoc-equal x frame)))
                       x
                       (frame-val->path (cdr (assoc-equal x frame))))
    nil (remove-assoc-equal x frame)))
  :hints (("goal" :in-theory (enable distinguish-names prefixp abs-separate)
           :do-not-induct t)))

(defthm
  abs-separate-correctness-1-lemma-27
  (implies
   (and (< 0 (1st-complete frame))
        (abs-file-alist-p root)
        (abs-separate (frame-with-root root frame)))
   (abs-separate
    (frame-with-root
     (context-apply
      root
      (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                        frame)))
      (1st-complete frame)
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame))))
     (remove-assoc-equal (1st-complete frame)
                         frame))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable frame-with-root abs-separate))))

(defthm
  abs-separate-correctness-1-lemma-28
  (implies (not (equal (context-apply abs-file-alist1
                                          abs-file-alist2 x x-path)
                       abs-file-alist1))
           (equal (strip-cars (context-apply abs-file-alist1
                                                 abs-file-alist2 x x-path))
                  (if (consp x-path)
                      (strip-cars abs-file-alist1)
                      (append (strip-cars (remove-equal x abs-file-alist1))
                              (strip-cars abs-file-alist2)))))
  :hints (("goal" :in-theory (enable context-apply))))

(defthm
  abs-separate-correctness-1-lemma-30
  (implies
   (and
    (abs-file-alist-p dir)
    (consp (assoc-equal src frame))
    (fat32-filename-list-p relpath)
    (prefixp (frame-val->path (cdr (assoc-equal src frame)))
             relpath)
    (not
     (equal (context-apply
             (frame-val->dir (cdr (assoc-equal src frame)))
             dir x
             (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
                     relpath))
            (frame-val->dir (cdr (assoc-equal src frame)))))
    (distinguish-names root nil frame)
    (not (intersectp-equal (remove-equal nil (strip-cars dir))
                           (names-at-relpath root relpath))))
   (distinguish-names
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
  :hints (("goal" :in-theory (enable distinguish-names prefixp))))

(defthm
  abs-separate-correctness-1-lemma-31
  (implies
   (and
    (not (equal (frame-val->src (cdr (assoc-equal x frame)))
                x))
    (consp (assoc-equal (frame-val->src (cdr (assoc-equal x frame)))
                        frame))
    (prefixp
     (frame-val->path
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal x frame)))
                        frame)))
     (frame-val->path (cdr (assoc-equal x frame))))
    (frame-p frame)
    (distinguish-names root nil frame))
   (distinguish-names
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
    :in-theory (disable abs-separate-correctness-1-lemma-30)
    :use ((:instance abs-separate-correctness-1-lemma-30
                     (src (frame-val->src (cdr (assoc-equal x frame))))
                     (dir (frame-val->dir (cdr (assoc-equal x frame))))
                     (relpath (frame-val->path (cdr (assoc-equal x frame))))
                     (frame (remove-assoc-equal x frame)))))))

(defthm abs-separate-correctness-1-lemma-32
  (implies (prefixp (frame-val->path (cdr (car frame)))
                    relpath)
           (prefixp (frame-val->path (cdr (car frame)))
                    (append relpath x-path))))

(defthm
  abs-separate-correctness-1-lemma-33
  (implies
   (prefixp relpath
            (frame-val->path (cdr (car frame))))
   (equal (prefixp (append relpath x-path)
                   (frame-val->path (cdr (car frame))))
          (prefixp x-path
                   (nthcdr (len relpath)
                           (frame-val->path$inline (cdr (car frame)))))))
  :hints (("goal" :in-theory (disable (:rewrite binary-append-take-nthcdr)
                                      (:rewrite take-when-prefixp))
           :use ((:instance (:rewrite binary-append-take-nthcdr)
                            (l (frame-val->path (cdr (car frame))))
                            (i (len relpath)))
                 (:instance (:rewrite take-when-prefixp)
                            (y (frame-val->path (cdr (car frame))))
                            (x relpath))))))

(defthm
  abs-separate-correctness-1-lemma-34
  (implies (and (fat32-filename-list-p x-path)
                (fat32-filename-list-p relpath)
                (abs-file-alist-p abs-file-alist2)
                (natp x)
                (not (equal (context-apply abs-file-alist1
                                           abs-file-alist2 x x-path)
                            abs-file-alist1))
                (distinguish-names abs-file-alist1 relpath frame)
                (distinguish-names abs-file-alist2 (append relpath x-path)
                                   frame))
           (distinguish-names (context-apply abs-file-alist1
                                             abs-file-alist2 x x-path)
                              relpath frame))
  :hints (("goal" :in-theory (enable distinguish-names))))

(defthm
  abs-separate-correctness-1-lemma-36
  (implies
   (and
    (< 0 x)
    (abs-file-alist-p dir)
    (fat32-filename-list-p relpath)
    (distinguish-names dir relpath (cdr frame))
    (prefixp (frame-val->path (cdr (car frame)))
             relpath)
    (not
     (equal
      (context-apply (frame-val->dir (cdr (car frame)))
                     dir x
                     (nthcdr (len (frame-val->path (cdr (car frame))))
                             relpath))
      (frame-val->dir (cdr (car frame)))))
    (distinguish-names (frame-val->dir (cdr (car frame)))
                       (frame-val->path (cdr (car frame)))
                       (cdr frame))
    (integerp x))
   (distinguish-names
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
  abs-separate-correctness-1-lemma-35
  (implies
   (and (fat32-filename-list-p relpath2)
        (prefixp (frame-val->path (cdr (car frame)))
                 relpath2)
        (not (intersectp-equal
              (remove-equal nil (strip-cars dir2))
              (names-at-relpath dir1 (nthcdr (len relpath1) relpath2))))
        (<= (len relpath2)
            (len (frame-val->path (cdr (car frame))))))
   (not
    (intersectp-equal
     (remove-equal nil (strip-cars dir2))
     (names-at-relpath dir1
                       (nthcdr (len relpath1)
                               (frame-val->path (cdr (car frame))))))))
  :hints (("goal" :in-theory (e/d (list-equiv)
                                  ((:rewrite prefixp-when-equal-lengths)))
           :use (:instance (:rewrite prefixp-when-equal-lengths)
                           (y relpath2)
                           (x (frame-val->path (cdr (car frame)))))
           :do-not-induct t)))

(defthm
  abs-separate-correctness-1-lemma-38
  (implies
   (and (distinguish-names dir1 relpath1 frame)
        (abs-file-alist-p dir2)
        (not (prefixp relpath1 relpath2))
        (not (prefixp relpath2 relpath1))
        (prefixp (frame-val->path (cdr (assoc-equal src frame)))
                 relpath2))
   (distinguish-names
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
  :hints (("goal" :in-theory (enable distinguish-names
                                     names-at-relpath intersectp-equal))))

(defthm
  abs-separate-correctness-1-lemma-40
  (implies
   (and
    (distinguish-names dir1 relpath1 frame)
    (abs-file-alist-p dir2)
    (fat32-filename-list-p relpath2)
    (not (prefixp relpath2 relpath1))
    (prefixp (frame-val->path (cdr (assoc-equal src frame)))
             relpath2)
    (not
     (equal (context-apply
             (frame-val->dir (cdr (assoc-equal src frame)))
             dir2 x2
             (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
                     relpath2))
            (frame-val->dir (cdr (assoc-equal src frame)))))
    (not
     (intersectp-equal (remove-equal nil (strip-cars dir2))
                       (names-at-relpath dir1
                                         (nthcdr (len relpath1) relpath2)))))
   (distinguish-names
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
  (("goal"
    :in-theory (e/d (distinguish-names names-at-relpath
                                       intersectp-equal prefixp)))))

(defthm
  abs-separate-correctness-1-lemma-41
  (implies
   (and
    (distinguish-names dir1 relpath1 frame)
    (abs-file-alist-p dir2)
    (not (prefixp relpath1 relpath2))
    (prefixp (frame-val->path (cdr (assoc-equal src frame)))
             relpath2)
    (not
     (intersectp-equal
      (remove-equal nil (strip-cars dir1))
      (names-at-relpath
       (context-apply
        (frame-val->dir (cdr (assoc-equal src frame)))
        dir2 x2
        (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
                relpath2))
       (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
               relpath1)))))
   (distinguish-names
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
  :hints (("goal" :in-theory (enable distinguish-names
                                     names-at-relpath
                                     intersectp-equal prefixp))))

(defthm
  abs-separate-correctness-1-lemma-42
  (implies
   (and
    (distinguish-names dir1 relpath1 frame)
    (abs-file-alist-p dir2)
    (fat32-filename-list-p relpath2)
    (prefixp (frame-val->path (cdr (assoc-equal src frame)))
             relpath2)
    (not
     (equal (context-apply
             (frame-val->dir (cdr (assoc-equal src frame)))
             dir2 x2
             (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
                     relpath2))
            (frame-val->dir (cdr (assoc-equal src frame)))))
    (not (intersectp-equal
          (remove-equal nil (strip-cars dir2))
          (names-at-relpath dir1 (nthcdr (len relpath1) relpath2))))
    (not
     (intersectp-equal
      (remove-equal nil (strip-cars dir1))
      (names-at-relpath
       (context-apply
        (frame-val->dir (cdr (assoc-equal src frame)))
        dir2 x2
        (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
                relpath2))
       (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
               relpath1)))))
   (distinguish-names
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
  (("goal"
    :in-theory (e/d (distinguish-names names-at-relpath
                                       intersectp-equal prefixp)))))

(defthm
  abs-separate-correctness-1-lemma-49
  (implies
   (and
    (< 0 x)
    (abs-file-alist-p dir)
    (integerp x)
    (prefixp
     (nthcdr (len (frame-val->path (cdr (assoc-equal src (cdr frame)))))
             relpath)
     (nthcdr (len (frame-val->path (cdr (assoc-equal src (cdr frame)))))
             (frame-val->path (cdr (car frame)))))
    (not
     (intersectp-equal
      (remove-equal nil
                    (strip-cars (frame-val->dir (cdr (car frame)))))
      (names-at-relpath
       dir
       (nthcdr
        (len
         (nthcdr (len (frame-val->path (cdr (assoc-equal src (cdr frame)))))
                 relpath))
        (nthcdr (len (frame-val->path (cdr (assoc-equal src (cdr frame)))))
                (frame-val->path (cdr (car frame))))))))
    (not
     (intersectp-equal
      (remove-equal nil
                    (strip-cars (frame-val->dir (cdr (car frame)))))
      (names-at-relpath
       (frame-val->dir (cdr (assoc-equal src (cdr frame))))
       (nthcdr (len (frame-val->path (cdr (assoc-equal src (cdr frame)))))
               (frame-val->path (cdr (car frame))))))))
   (not
    (intersectp-equal
     (remove-equal nil
                   (strip-cars (frame-val->dir (cdr (car frame)))))
     (names-at-relpath
      (context-apply
       (frame-val->dir (cdr (assoc-equal src (cdr frame))))
       dir x
       (nthcdr (len (frame-val->path (cdr (assoc-equal src (cdr frame)))))
               relpath))
      (nthcdr (len (frame-val->path (cdr (assoc-equal src (cdr frame)))))
              (frame-val->path (cdr (car frame)))))))))

(encapsulate
  ()

  (local (include-book "std/lists/prefixp" :dir :system))

  (defthm
    abs-separate-correctness-1-lemma-50
    (implies
     (prefixp (frame-val->path (cdr (assoc-equal src frame)))
              relpath)
     (not (< (+ (len relpath)
                (- (len (frame-val->path (cdr (assoc-equal src frame))))))
             0)))
    :rule-classes (:rewrite :linear))

  (defthm
    abs-separate-correctness-1-lemma-43
    (implies
     (and
      (distinguish-names (frame-val->dir (cdr (car frame)))
                         (frame-val->path (cdr (car frame)))
                         (cdr frame))
      (< 0 x)
      (consp (assoc-equal src (cdr frame)))
      (abs-file-alist-p dir)
      (fat32-filename-list-p relpath)
      (prefixp relpath
               (frame-val->path (cdr (car frame))))
      (not
       (intersectp-equal
        (remove-equal nil
                      (strip-cars (frame-val->dir (cdr (car frame)))))
        (names-at-relpath dir
                          (nthcdr (len relpath)
                                  (frame-val->path (cdr (car frame)))))))
      (prefixp (frame-val->path (cdr (assoc-equal src (cdr frame))))
               relpath)
      (not
       (equal
        (context-apply
         (frame-val->dir (cdr (assoc-equal src (cdr frame))))
         dir x
         (nthcdr (len (frame-val->path (cdr (assoc-equal src (cdr frame)))))
                 relpath))
        (frame-val->dir (cdr (assoc-equal src (cdr frame))))))
      (integerp x))
     (distinguish-names
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
    :hints (("goal" :in-theory (e/d (list-equiv)
                                    (nthcdr-when->=-n-len-l
                                     (:rewrite prefixp-when-equal-lengths)))
             :use ((:instance (:rewrite prefixp-when-equal-lengths)
                              (y relpath)
                              (x (frame-val->path (cdr (car frame))))))
             :cases ((prefixp (frame-val->path (cdr (car frame)))
                              relpath))))))

(defthm
  abs-separate-correctness-1-lemma-44
  (implies
   (and
    (< 0 x)
    (consp (assoc-equal src frame))
    (abs-file-alist-p dir)
    (abs-no-dups-p dir)
    (fat32-filename-list-p relpath)
    (distinguish-names dir relpath frame)
    (prefixp (frame-val->path (cdr (assoc-equal src frame)))
             relpath)
    (not
     (equal (context-apply
             (frame-val->dir (cdr (assoc-equal src frame)))
             dir x
             (nthcdr (len (frame-val->path (cdr (assoc-equal src frame))))
                     relpath))
            (frame-val->dir (cdr (assoc-equal src frame)))))
    (abs-separate frame)
    (integerp x))
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
  :hints (("goal" :in-theory (e/d (abs-separate distinguish-names prefixp names-at-relpath)
                                  (nthcdr-when->=-n-len-l)))))

(defthm
  abs-separate-correctness-1-lemma-45
  (implies
   (and
    (< 0 x)
    (not (equal (frame-val->src (cdr (assoc-equal x frame)))
                x))
    (prefixp
     (frame-val->path
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal x frame)))
                        frame)))
     (frame-val->path (cdr (assoc-equal x frame))))
    (not
     (equal
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
      (frame-val->dir
       (cdr (assoc-equal (frame-val->src (cdr (assoc-equal x frame)))
                         frame)))))
    (abs-separate frame)
    (integerp x)
    (consp (assoc-equal x frame)))
   (abs-separate
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
    :in-theory (disable abs-separate-correctness-1-lemma-44)
    :do-not-induct t
    :use (:instance abs-separate-correctness-1-lemma-44
                    (src (frame-val->src (cdr (assoc-equal x frame))))
                    (dir (frame-val->dir (cdr (assoc-equal x frame))))
                    (relpath (frame-val->path (cdr (assoc-equal x frame))))
                    (frame (remove-assoc-equal x frame))))))

(defthm
  abs-separate-correctness-1-lemma-46
  (implies
   (and
    (< 0 (1st-complete frame))
    (not (equal (1st-complete-src frame)
                (1st-complete frame)))
    (consp (assoc-equal (1st-complete-src frame)
                        frame))
    (prefixp
     (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                        frame)))
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame))))
    (not
     (equal
      (context-apply
       (frame-val->dir
        (cdr (assoc-equal (1st-complete-src frame)
                          frame)))
       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                         frame)))
       (1st-complete frame)
       (nthcdr
        (len (frame-val->path
              (cdr (assoc-equal (1st-complete-src frame)
                                frame))))
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame)))))
      (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                        frame)))))
    (frame-p frame)
    (abs-separate (frame-with-root root frame)))
   (abs-separate
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
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (1st-complete frame)
        (nthcdr
         (len (frame-val->path
               (cdr (assoc-equal (1st-complete-src frame)
                                 frame))))
         (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                            frame)))))
       (frame-val->src
        (cdr (assoc-equal (1st-complete-src frame)
                          frame))))
      (remove-assoc-equal (1st-complete frame)
                          frame)))))
  :hints
  (("goal" :do-not-induct t
    :in-theory (enable frame-with-root
                       abs-separate 1st-complete-src))))

(defthm
  abs-separate-correctness-1-lemma-47
  (implies
   (and (abs-separate frame)
        (< 0 (1st-complete frame))
        (frame-p frame)
        (no-duplicatesp-equal (strip-cars frame)))
   (hifat-no-dups-p
    (frame-val->dir$inline (cdr (assoc-equal (1st-complete frame)
                                             frame)))))
  :hints (("goal" :do-not-induct t)))

(defthm
  abs-separate-correctness-1-lemma-51
  (implies
   (and (< 0 (1st-complete-src frame))
        (member-equal (1st-complete frame)
                      (abs-addrs root))
        (no-duplicatesp-equal (strip-cars frame))
        (subsetp-equal (abs-addrs root)
                       (frame-addrs-root frame)))
   (hifat-no-dups-p
    (mv-nth
     0
     (collapse
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
  :hints (("goal" :in-theory (enable 1st-complete-src))))

(defthm
  abs-separate-correctness-1-lemma-52
  (implies
   (and (< 0 (1st-complete-src frame))
        (member-equal (1st-complete frame)
                      (abs-addrs root))
        (no-duplicatesp-equal (strip-cars frame))
        (subsetp-equal (abs-addrs root)
                       (frame-addrs-root frame)))
   (m1-file-alist-p
    (mv-nth
     0
     (collapse
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
  :hints (("goal" :in-theory (enable 1st-complete-src))))

;; ;; This one was tough... but now it seems to be useless, according to
;; ;; accumulated-persistence.
;; (defthm abs-separate-correctness-1-lemma-48
;;   (implies (and (abs-file-alist-p root)
;;                 (frame-p frame)
;;                 (abs-separate frame)
;;                 (abs-no-dups-p root)
;;                 (no-duplicatesp-equal (abs-addrs root))
;;                 (no-duplicatesp-equal (strip-cars frame))
;;                 (equal (mv-nth 1 (collapse root frame))
;;                        t)
;;                 (distinguish-names root nil frame)
;;                 (subsetp (abs-addrs root)
;;                          (frame-addrs-root frame)))
;;            (equal (abs-addrs (mv-nth 0 (collapse root frame)))
;;                   nil))
;;   :hints (("goal" :in-theory (enable collapse intersectp-equal))))

(defthm
  abs-separate-correctness-1
  (implies (and (frame-p frame)
                (no-duplicatesp-equal (strip-cars frame))
                (abs-file-alist-p root)
                (no-duplicatesp-equal (abs-addrs root))
                (subsetp (abs-addrs root)
                         (frame-addrs-root frame))
                (abs-separate (frame-with-root root frame)))
           (mv-let (fs result)
             (collapse root frame)
             (implies (equal result t)
                      (and (m1-file-alist-p fs)
                           (hifat-no-dups-p fs)))))
  :hints (("goal" :in-theory (enable collapse intersectp-equal))))

(defthm distinguish-names-of-append
  (equal (distinguish-names dir relpath (append frame1 frame2))
         (and (distinguish-names dir relpath frame1)
              (distinguish-names dir relpath frame2)))
  :hints (("goal" :in-theory (enable distinguish-names))))

(defund
  mutual-distinguish-names (frame1 frame2)
  (declare (xargs :guard (and (frame-p frame1)
                              (frame-p frame2))))
  (or (atom frame1)
      (and (distinguish-names (frame-val->dir (cdar frame1))
                              (frame-val->path (cdar frame1))
                              frame2)
           (mutual-distinguish-names (cdr frame1)
                                     frame2))))

(defthm abs-separate-of-append
  (equal (abs-separate (append frame1 frame2))
         (and (abs-separate frame1)
              (abs-separate frame2)
              (mutual-distinguish-names frame1 frame2)))
  :hints (("goal" :in-theory (enable abs-separate
                                     mutual-distinguish-names))))

(defund abs-find-file-helper (fs pathname)
  (declare (xargs :guard (and (abs-file-alist-p fs)
                              (fat32-filename-list-p pathname))
                  :measure (acl2-count pathname)))
  (b*
      ((fs (abs-file-alist-fix fs))
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

(defund abs-find-file (frame pathname)
  (declare (xargs :guard (and (frame-p frame)
                              (fat32-filename-list-p pathname))))
  (b*
      (((when (atom frame)) (mv (make-abs-file) *enoent*))
       ((unless (prefixp (frame-val->path (cdar frame)) pathname))
        (abs-find-file (cdr frame) pathname))
       ((mv file error-code)
        (abs-find-file-helper (frame-val->dir (cdar frame))
                              (nthcdr (len (frame-val->path (cdar frame)))
                                      pathname)))
       ((when (not (equal error-code *ENOENT*))) (mv file error-code)))
    (abs-find-file (cdr frame) pathname)))

(defthm natp-of-abs-find-file
  (natp (mv-nth 1 (abs-find-file frame pathname)))
  :hints (("goal" :in-theory (enable abs-find-file)))
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

(defthm
  abs-file->contents-when-m1-file-p
  (implies (m1-file-p file)
           (equal (abs-file->contents file)
                  (m1-file->contents file)))
  :hints
  (("goal" :in-theory (enable m1-file->contents
                              abs-file->contents m1-file-p))))

(defthm abs-find-file-helper-when-m1-file-alist-p
  (implies (and (m1-file-alist-p fs)
                (hifat-no-dups-p fs))
           (equal (abs-find-file-helper fs pathname)
                  (hifat-find-file fs pathname)))
  :hints (("goal" :in-theory (enable abs-find-file-helper
                                     hifat-find-file m1-file-alist-p)
           :induct t)))

(defthm abs-addrs-of-true-list-fix
  (equal (abs-addrs (true-list-fix abs-file-alist))
         (abs-addrs abs-file-alist))
  :hints (("goal" :in-theory (enable abs-addrs))))

;; Also useless, but reduces free variables, I guess.
(defthm
  abs-addrs-of-remove-lemma-1
  (implies
   (and
    (integerp x)
    (<= 0 x)
    (member-equal x (cdr abs-file-alist))
    (not (intersectp-equal
          (abs-addrs (cdr abs-file-alist))
          (abs-addrs (abs-file->contents (cdr (car abs-file-alist)))))))
   (not (member-equal x
                      (abs-file->contents (cdr (car abs-file-alist))))))
  :hints
  (("goal"
    :use
    (:instance (:rewrite intersectp-member)
               (y (abs-addrs (abs-file->contents (cdr (car abs-file-alist)))))
               (x (abs-addrs (cdr abs-file-alist)))
               (a x)))))

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

(defthm member-equal-of-strip-cars-when-m1-file-alist-p
  (implies (and (not (fat32-filename-p x))
                (m1-file-alist-p fs))
           (not (member-equal x (strip-cars fs)))))

(defthm
  abs-find-file-helper-of-context-apply-lemma-1
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
  abs-find-file-helper-of-context-apply-lemma-2
  (implies
   (and (abs-file-alist-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist2)
        (fat32-filename-list-p pathname)
        (integerp x)
        (not (equal (mv-nth 1
                            (abs-find-file-helper abs-file-alist1 pathname))
                    *enoent*)))
   (equal (abs-find-file-helper (append (remove-equal x abs-file-alist1)
                                        abs-file-alist2)
                                pathname)
          (abs-find-file-helper abs-file-alist1 pathname)))
  :hints
  (("goal" :expand (:free (abs-file-alist)
                          (abs-find-file-helper abs-file-alist pathname)))))

(defthm
  abs-find-file-helper-of-context-apply-lemma-3
  (implies
   (and (not (consp (assoc-equal (car pathname)
                                 abs-file-alist1)))
        (abs-file-alist-p abs-file-alist1)
        (m1-file-alist-p abs-file-alist2)
        (fat32-filename-list-p pathname)
        (integerp x))
   (equal
    (mv-nth 0
            (abs-find-file-helper (append (remove-equal x abs-file-alist1)
                                          abs-file-alist2)
                                  pathname))
    (mv-nth 0
            (abs-find-file-helper abs-file-alist2 pathname))))
  :hints
  (("goal"
    :expand ((abs-find-file-helper abs-file-alist2 pathname)
             (abs-find-file-helper (append (remove-equal x abs-file-alist1)
                                           abs-file-alist2)
                                   pathname)))))

(defthm
  abs-find-file-helper-of-context-apply-lemma-4
  (implies (and (fat32-filename-list-p pathname)
                (abs-file-alist-p fs)
                (< n (len pathname))
                (zp (mv-nth 1 (abs-find-file-helper fs pathname))))
           (member-equal (nth n pathname)
                         (names-at-relpath fs (take n pathname))))
  :hints (("goal" :in-theory (enable names-at-relpath abs-find-file-helper))))

(defthmd abs-find-file-helper-of-context-apply-lemma-5
  (implies (not (zp (mv-nth 1 (abs-find-file-helper fs pathname))))
           (equal (abs-find-file-helper fs pathname)
                  (mv (abs-file-fix nil)
                      (mv-nth 1 (abs-find-file-helper fs pathname)))))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  abs-find-file-helper-of-context-apply-lemma-6
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal (car pathname)
                                            abs-file-alist1)))
    (consp (cdr pathname))
    (abs-file-alist-p abs-file-alist1)
    (abs-file-alist-p abs-file-alist2)
    (fat32-filename-list-p pathname)
    (integerp x)
    (<= 0 x)
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
    :use ((:instance intersectp-member (a (car pathname))
                     (x (remove-equal nil (strip-cars abs-file-alist1)))
                     (y (remove-equal nil (strip-cars abs-file-alist2))))
          (:instance
           (:rewrite abs-find-file-helper-of-context-apply-lemma-5)
           (pathname (cdr pathname))
           (fs (abs-file->contents (cdr (assoc-equal (car pathname)
                                                     abs-file-alist1))))))
    :expand (:free (abs-file-alist)
                   (abs-find-file-helper abs-file-alist pathname)))))

(defthm
  abs-find-file-helper-of-context-apply-lemma-7
  (implies
   (and
    (abs-directory-file-p (cdr (assoc-equal (car pathname)
                                            abs-file-alist2)))
    (abs-file-alist-p abs-file-alist1)
    (abs-file-alist-p abs-file-alist2)
    (fat32-filename-list-p pathname)
    (integerp x)
    (not (intersectp-equal (remove-equal nil (strip-cars abs-file-alist1))
                           (remove-equal nil (strip-cars abs-file-alist2)))))
   (equal (abs-find-file-helper (append (remove-equal x abs-file-alist1)
                                        abs-file-alist2)
                                pathname)
          (abs-find-file-helper abs-file-alist2 pathname)))
  :hints
  (("goal" :in-theory (enable prefixp abs-find-file-helper
                              context-apply names-at-relpath)
    :expand (:free (abs-file-alist)
                   (abs-find-file-helper abs-file-alist pathname)))))

(defthm
  abs-find-file-helper-of-context-apply
  (implies
   (and (abs-file-alist-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist2)
        (fat32-filename-list-p pathname)
        (natp x)
        (not (intersectp-equal (remove-equal 'nil
                                             (strip-cars abs-file-alist2))
                               (names-at-relpath abs-file-alist1 x-path)))
        (not (equal (context-apply abs-file-alist1
                                   abs-file-alist2 x x-path)
                    abs-file-alist1)))
   (equal
    (abs-find-file-helper (context-apply abs-file-alist1
                                         abs-file-alist2 x x-path)
                          pathname)
    (cond
     ((and (equal (mv-nth 1
                          (abs-find-file-helper abs-file-alist1 pathname))
                  0)
           (prefixp pathname x-path))
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
           (prefixp x-path pathname))
      (abs-find-file-helper abs-file-alist2
                            (nthcdr (len x-path) pathname)))
     (t (abs-find-file-helper abs-file-alist1 pathname)))))
  :hints
  (("goal"
    :in-theory (enable prefixp abs-find-file-helper
                       context-apply names-at-relpath)
    :induct
    (mv (mv-nth 0
                (abs-find-file-helper (context-apply abs-file-alist1
                                                     abs-file-alist2 x x-path)
                                      pathname))
        (prefixp x-path pathname)
        (context-apply abs-file-alist1
                       abs-file-alist2 x x-path))
    :expand
    (abs-find-file-helper
     (put-assoc-equal
      (car x-path)
      (abs-file
       (abs-file->dir-ent (cdr (assoc-equal (car x-path)
                                            abs-file-alist1)))
       (context-apply (abs-file->contents (cdr (assoc-equal (car x-path)
                                                            abs-file-alist1)))
                      abs-file-alist2 x (cdr x-path)))
      abs-file-alist1)
     pathname))))

(defthmd abs-find-file-of-put-assoc-lemma-1
  (equal (abs-find-file-helper fs pathname)
         (mv (mv-nth 0 (abs-find-file-helper fs pathname))
             (mv-nth 1 (abs-find-file-helper fs pathname))))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  abs-find-file-of-put-assoc-lemma-7
  (implies
   (and
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (or
     (not (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                   pathname))
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
    (:instance (:rewrite abs-find-file-helper-of-context-apply-lemma-5)
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
    (:instance (:rewrite abs-find-file-helper-of-context-apply-lemma-5)
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
                       pathname)
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
        (equal (mv-nth 1
                       (abs-find-file (remove-assoc-equal name frame)
                                      pathname))
               2))
   (equal (abs-find-file (put-assoc-equal name val frame)
                         pathname)
          (if (prefixp (frame-val->path val) pathname)
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
    (or
     (not (prefixp (frame-val->path val)
                   pathname))
     (equal
      (mv-nth 1
              (abs-find-file-helper (frame-val->dir val)
                                    (nthcdr (len (frame-val->path val))
                                            pathname)))
      *enoent*)))
   (equal (abs-find-file (put-assoc-equal name val frame)
                         pathname)
          (abs-find-file (remove-assoc-equal name frame)
                         pathname)))
  :hints
  (("goal" :in-theory (enable abs-find-file))))

(defund abs-find-file-alt
  (frame indices pathname)
  (b* (((when (atom indices))
        (mv (make-abs-file) *enoent*))
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
  (implies (and (abs-file-alist-p fs)
                (consp (assoc-equal name fs))
                (not (abs-directory-file-p (cdr (assoc-equal name fs)))))
           (m1-regular-file-p (cdr (assoc-equal name fs))))
  :hints (("goal" :in-theory (e/d
                              (abs-file-alist-p abs-directory-file-p
                                                m1-regular-file-p m1-file-p abs-file-p
                                                abs-file->contents m1-file->contents)
                              (abs-file-alist-p-when-m1-file-alist-p
                               abs-file-alist-p-correctness-1-lemma-3)))))

(defthm
 abs-enotdir-witness-correctness-2-lemma-2
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
    :use (:instance (:rewrite abs-find-file-helper-of-context-apply-lemma-5)
                    (fs root)))))

;; Important!
;; It's a pain in the neck that we have to stipulate x-path has at least one
;; element in it... but it's unavoidable. This is really a fundamental
;; difference between abs-find-file-helper and context-apply.
(defthm
  abs-find-file-helper-of-collapse-lemma-2
  (implies (and (abs-file-alist-p abs-file-alist1)
                (consp x-path)
                (fat32-filename-list-p x-path)
                (not (equal (context-apply abs-file-alist1
                                           abs-file-alist2 x x-path)
                            abs-file-alist1)))
           (and (equal (mv-nth 1
                               (abs-find-file-helper abs-file-alist1 x-path))
                       0)
                (abs-directory-file-p
                 (mv-nth 0
                         (abs-find-file-helper abs-file-alist1 x-path)))))
  :hints (("goal" :in-theory (enable abs-find-file-helper context-apply))))

(encapsulate
  ()

  (local
   (defthmd
     abs-find-file-helper-of-collapse-lemma-3
     (implies
      (and (consp pathname)
           (prefixp pathname x-path)
           (zp (mv-nth 1 (abs-find-file-helper fs x-path)))
           (fat32-filename-list-p x-path)
           (true-listp pathname))
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
          (prefixp pathname x-path)
          (zp (mv-nth 1 (abs-find-file-helper fs x-path))))
     (and
      (equal
       (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs pathname)))
       (or (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs x-path)))
           (not (fat32-filename-list-equiv pathname x-path))))
      (equal (mv-nth 1 (abs-find-file-helper fs pathname))
             0)))
    :hints
    (("goal" :use (:instance abs-find-file-helper-of-collapse-lemma-3
                             (x-path (fat32-filename-list-fix x-path))
                             (pathname (fat32-filename-list-fix pathname)))))))

(defthm
  abs-find-file-helper-of-collapse-lemma-5
  (implies
   (and
    (equal (mv-nth 1 (abs-find-file-helper root pathname))
           0)
    (not
     (equal
      (context-apply
       root
       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                         frame)))
       (1st-complete frame)
       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                          frame))))
      root))
    (abs-file-alist-p root)
    (prefixp
     pathname
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame)))))
   (not (m1-regular-file-p (mv-nth 0
                                   (abs-find-file-helper root pathname)))))
  :instructions
  (:promote
   (:claim
    (abs-directory-file-p (mv-nth 0 (abs-find-file-helper root pathname)))
    :hints :none)
   :bash
   (:claim
    (and
     (consp pathname)
     (zp
      (mv-nth
       1
       (abs-find-file-helper
        root
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame))))))
     (abs-directory-file-p
      (mv-nth
       0
       (abs-find-file-helper
        root
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame)))))))
    :hints :none)
   (:rewrite
    abs-find-file-helper-of-collapse-lemma-4
    ((x-path
      (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                         frame))))))
   (:in-theory (enable abs-find-file-helper))
   :bash
   :bash
   (:rewrite
    abs-find-file-helper-of-collapse-lemma-2
    ((x (1st-complete frame))
     (abs-file-alist2
      (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                        frame))))))
   :bash :bash (:dive 1 2)
   (:rewrite
    abs-find-file-helper-of-collapse-lemma-2
    ((x (1st-complete frame))
     (abs-file-alist2
      (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                        frame))))))
   :bash :bash))

(defthm
  abs-find-file-helper-of-collapse-lemma-6
  (implies
   (and (not (equal (1st-complete-src frame)
                    (1st-complete frame)))
        (consp (assoc-equal (1st-complete-src frame)
                            frame))
        (prefixp (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                    frame)))
                 (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                    frame))))
        (frame-p frame)
        (distinguish-names root nil frame))
   (distinguish-names
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
                           ((:rewrite abs-separate-correctness-1-lemma-31)))
    :use (:instance (:rewrite abs-separate-correctness-1-lemma-31)
                    (x (1st-complete frame))))))

(defthm
  abs-find-file-helper-of-collapse-lemma-7
  (implies
   (and
    (< 0 (1st-complete frame))
    (not (equal (1st-complete-src frame)
                (1st-complete frame)))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                frame)))
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame))))
    (not
     (equal
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
      (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                        frame)))))
    (abs-separate frame))
   (abs-separate
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
                           ((:rewrite abs-separate-correctness-1-lemma-45)))
    :use (:instance (:rewrite abs-separate-correctness-1-lemma-45)
                    (x (1st-complete frame))))))

(defthm
  abs-find-file-helper-of-collapse-1
  (implies
   (and (frame-p frame)
        (abs-file-alist-p root)
        (fat32-filename-list-p pathname)
        (abs-separate frame)
        (distinguish-names root nil frame)
        (m1-regular-file-p (mv-nth 0
                                   (abs-find-file-helper root pathname))))
   (equal (abs-find-file-helper (mv-nth 0 (collapse root frame))
                                pathname)
          (abs-find-file-helper root pathname)))
  :hints
  (("goal" :in-theory (enable collapse distinguish-names)
    :induct (collapse root frame))
   ("subgoal *1/4"
    :use (:instance (:rewrite abs-find-file-helper-of-context-apply-lemma-5)
                    (fs root))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (frame-p frame)
          (abs-file-alist-p root)
          (fat32-filename-list-p pathname)
          (abs-separate frame)
          (distinguish-names root nil frame)
          (m1-regular-file-p
           (mv-nth 0 (abs-find-file-helper root pathname)))
          (m1-file-alist-p (mv-nth 0 (collapse root frame)))
          (hifat-no-dups-p (mv-nth 0 (collapse root frame))))
     (equal (hifat-find-file (mv-nth 0 (collapse root frame))
                             pathname)
            (abs-find-file-helper root pathname))))))

(defthm
  abs-find-file-helper-of-collapse-2
  (implies
   (and (frame-p frame)
        (abs-file-alist-p root)
        (fat32-filename-list-p pathname)
        (abs-separate frame)
        (distinguish-names root nil frame)
        (not (equal (mv-nth 1 (abs-find-file-helper root pathname))
                    0))
        (not (equal (mv-nth 1 (abs-find-file-helper root pathname))
                    *enoent*)))
   (equal
    (abs-find-file-helper (mv-nth 0 (collapse root frame))
                          pathname)
    (abs-find-file-helper root pathname)))
  :hints (("goal" :in-theory (enable collapse distinguish-names)
           :induct (collapse root frame)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (frame-p frame)
          (abs-file-alist-p root)
          (fat32-filename-list-p pathname)
          (abs-separate frame)
          (distinguish-names root nil frame)
          (not (equal (mv-nth 1 (abs-find-file-helper root pathname))
                      0))
          (not (equal (mv-nth 1 (abs-find-file-helper root pathname))
                      *enoent*))
          (m1-file-alist-p (mv-nth 0 (collapse root frame)))
          (hifat-no-dups-p (mv-nth 0 (collapse root frame))))
     (equal
      (hifat-find-file (mv-nth 0 (collapse root frame))
                       pathname)
      (abs-find-file-helper root pathname))))))

;; The somewhat weaker conclusion, in terms of (mv-nth 1 (abs-find-file ...))
;; rather than (abs-find-file ...), is because of the possibility that the file
;; returned is a directory with holes, which gets filled in during collapse.
(defthm
  abs-find-file-helper-of-collapse-3
  (implies
   (and (frame-p frame)
        (abs-file-alist-p root)
        (fat32-filename-list-p pathname)
        (abs-separate frame)
        (distinguish-names root nil frame)
        (not (equal (mv-nth 1 (abs-find-file-helper root pathname))
                    *enoent*)))
   (equal (mv-nth 1
                  (abs-find-file-helper (mv-nth 0 (collapse root frame))
                                        pathname))
          (mv-nth 1
                  (abs-find-file-helper root pathname))))
  :hints (("goal" :in-theory (enable collapse distinguish-names)
           :induct (collapse root frame)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (and (frame-p frame)
                  (abs-file-alist-p root)
                  (fat32-filename-list-p pathname)
                  (abs-separate frame)
                  (distinguish-names root nil frame)
                  (not (equal (mv-nth 1 (abs-find-file-helper root pathname))
                              *enoent*))
                  (m1-file-alist-p (mv-nth 0 (collapse root frame)))
                  (hifat-no-dups-p (mv-nth 0 (collapse root frame))))
             (equal (mv-nth 1
                            (hifat-find-file (mv-nth 0 (collapse root frame))
                                             pathname))
                    (mv-nth 1
                            (abs-find-file-helper root pathname)))))))

(defthm
  abs-find-file-correctness-1-lemma-1
  (implies
   (and (abs-file-alist-p root)
        (not (consp (abs-addrs root)))
        (abs-separate (frame-with-root root nil))
        (m1-regular-file-p (mv-nth 0
                                   (abs-find-file (frame-with-root root nil)
                                                  pathname))))
   (equal (mv-nth 0
                  (abs-find-file (frame-with-root root nil)
                                 pathname))
          (mv-nth 0 (hifat-find-file root pathname))))
  :hints (("goal" :in-theory (enable frame-with-root
                                     abs-find-file abs-separate))))

(defthm
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

(defthm
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

;; It seems this is useless, but it's not too clunky, so we can keep it.
(defthm
  abs-find-file-correctness-1-lemma-5
  (implies
   (and (natp x)
        (equal (abs-addrs abs-file-alist2) nil)
        (not (equal (context-apply abs-file-alist1
                                   abs-file-alist2 x x-path)
                    abs-file-alist1))
        (no-duplicatesp-equal (abs-addrs abs-file-alist1))
        (abs-file-alist-p abs-file-alist2))
   (not
    (member-equal
     x
     (abs-addrs (context-apply abs-file-alist1
                               abs-file-alist2 x x-path)))))
  :hints (("goal" :in-theory (enable context-apply))))

(defthm
  abs-find-file-correctness-1-lemma-6
  (implies
   (and (distinguish-names root nil frame)
        (m1-file-alist-p (frame-val->dir$inline (cdr (assoc-equal x frame)))))
   (not (intersectp-equal
         (strip-cars (frame-val->dir$inline (cdr (assoc-equal x frame))))
         (names-at-relpath
          root
          (frame-val->path$inline (cdr (assoc-equal x frame)))))))
  :hints (("goal" :in-theory (disable abs-separate-correctness-1-lemma-12)
           :do-not-induct t
           :use abs-separate-correctness-1-lemma-12)))

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
    (abs-file-alist-p abs-file-alist1)
    (m1-file-alist-p abs-file-alist2)
    (fat32-filename-list-p pathname)
    (natp x)
    (prefixp x-path pathname)
    (not (equal (context-apply abs-file-alist1
                               abs-file-alist2 x x-path)
                abs-file-alist1))
    (not (intersectp-equal (strip-cars abs-file-alist2)
                           (names-at-relpath abs-file-alist1 x-path))))
   (and (equal (mv-nth 1
                       (abs-find-file-helper abs-file-alist1 pathname))
               *enoent*)
        (equal (mv-nth 1
                       (abs-find-file-helper abs-file-alist2
                                             (nthcdr (len x-path) pathname)))
               *enoent*))))

(defthm
  abs-find-file-correctness-1-lemma-13
  (implies
   (and
    (fat32-filename-list-p pathname)
    (< 0 (1st-complete frame))
    (not
     (equal
      (context-apply
       root
       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                         frame)))
       (1st-complete frame)
       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                          frame))))
      root))
    (equal
     (mv-nth
      1
      (abs-find-file-helper
       (context-apply
        root
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (1st-complete frame)
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame))))
       pathname))
     2)
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-file-alist-p root)
    (distinguish-names root nil frame))
   (equal
    (mv-nth 0
            (abs-find-file (remove-assoc-equal (1st-complete frame)
                                               frame)
                           pathname))
    (mv-nth 0 (abs-find-file frame pathname)))))

(defthm
  abs-find-file-correctness-1-lemma-15
  (implies
   (and
    (not (consp (assoc-equal (car pathname)
                             abs-file-alist1)))
    (abs-file-alist-p abs-file-alist1)
    (m1-file-alist-p abs-file-alist2)
    (fat32-filename-list-p pathname)
    (integerp x)
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
    :expand ((abs-find-file-helper abs-file-alist2 pathname)
             (abs-find-file-helper (append (remove-equal x abs-file-alist1)
                                           abs-file-alist2)
                                   pathname))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies
     (and (not (consp (assoc-equal (car pathname)
                                   abs-file-alist1)))
          (abs-file-alist-p abs-file-alist1)
          (m1-file-alist-p abs-file-alist2)
          (fat32-filename-list-p pathname)
          (integerp x)
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
   (and (abs-directory-file-p (cdr (assoc-equal (car pathname)
                                                abs-file-alist1)))
        (abs-file-alist-p abs-file-alist1)
        (m1-file-alist-p abs-file-alist2)
        (fat32-filename-list-p pathname)
        (integerp x)
        (equal (mv-nth 1
                       (abs-find-file-helper abs-file-alist1 pathname))
               *enoent*))
   (equal
    (mv-nth 1
            (abs-find-file-helper (append (remove-equal x abs-file-alist1)
                                          abs-file-alist2)
                                  pathname))
    *enoent*))
  :hints
  (("goal"
    :expand ((abs-find-file-helper abs-file-alist1 pathname)
             (abs-find-file-helper (append (remove-equal x abs-file-alist1)
                                           abs-file-alist2)
                                   pathname)))))

(defthm
  abs-find-file-correctness-1-lemma-17
  (implies
   (and
    (abs-file-alist-p abs-file-alist1)
    (m1-file-alist-p abs-file-alist2)
    (fat32-filename-list-p pathname)
    (natp x)
    (equal (mv-nth 1
                   (abs-find-file-helper abs-file-alist1 pathname))
           *enoent*)
    (equal
     (mv-nth 1
             (abs-find-file-helper (context-apply abs-file-alist1
                                                  abs-file-alist2 x x-path)
                                   pathname))
     0))
   (and
    (prefixp x-path pathname)
    (equal (mv-nth 1
                   (abs-find-file-helper abs-file-alist2
                                         (nthcdr (len x-path) pathname)))
           0)
    (equal
     (mv-nth 0
             (abs-find-file-helper (context-apply abs-file-alist1
                                                  abs-file-alist2 x x-path)
                                   pathname))
     (mv-nth 0
             (abs-find-file-helper abs-file-alist2
                                   (nthcdr (len x-path) pathname))))))
  :hints
  (("goal"
    :in-theory (enable prefixp abs-find-file-helper
                       context-apply names-at-relpath)
    :induct
    (mv (mv-nth 0
                (abs-find-file-helper (context-apply abs-file-alist1
                                                     abs-file-alist2 x x-path)
                                      pathname))
        (prefixp x-path pathname)
        (context-apply abs-file-alist1
                       abs-file-alist2 x x-path))
    :expand
    (abs-find-file-helper
     (put-assoc-equal
      (car x-path)
      (abs-file
       (abs-file->dir-ent (cdr (assoc-equal (car x-path)
                                            abs-file-alist1)))
       (context-apply (abs-file->contents (cdr (assoc-equal (car x-path)
                                                            abs-file-alist1)))
                      abs-file-alist2 x (cdr x-path)))
      abs-file-alist1)
     pathname)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (abs-file-alist-p abs-file-alist1)
      (m1-file-alist-p abs-file-alist2)
      (fat32-filename-list-p pathname)
      (natp x)
      (equal (mv-nth 1
                     (abs-find-file-helper abs-file-alist1 pathname))
             *enoent*)
      (not
       (and
        (prefixp x-path pathname)
        (equal (mv-nth 1
                       (abs-find-file-helper abs-file-alist2
                                             (nthcdr (len x-path) pathname)))
               0))))
     (not
      (equal
       (mv-nth 1
               (abs-find-file-helper (context-apply abs-file-alist1
                                                    abs-file-alist2 x x-path)
                                     pathname))
       0))))))

(defthm
  abs-find-file-correctness-1-lemma-9
  (implies
   (and
    (true-listp relpath)
    (abs-file-alist-p dir)
    (not
     (prefixp relpath
              (frame-val->path (cdr (assoc-equal x frame)))))
    (fat32-filename-list-p pathname)
    (prefixp relpath pathname)
    (equal (mv-nth 1
                   (abs-find-file-helper
                    dir (nthcdr (len relpath) pathname)))
           0)
    (equal
     (mv-nth
      1
      (abs-find-file-helper
       (frame-val->dir (cdr (assoc-equal x frame)))
       (nthcdr
        (len (frame-val->path (cdr (assoc-equal x frame))))
        pathname)))
     0)
    (prefixp (frame-val->path (cdr (assoc-equal x frame)))
             pathname))
   (intersectp-equal
    (remove-equal nil (strip-cars dir))
    (names-at-relpath
     (frame-val->dir (cdr (assoc-equal x frame)))
     (nthcdr
      (len (frame-val->path (cdr (assoc-equal x frame))))
      relpath))))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory
    (e/d (names-at-relpath abs-find-file-helper take-of-nthcdr)
         (abs-find-file-helper-of-context-apply-lemma-4
          (:rewrite abs-separate-correctness-1-lemma-50)))
    :use
    ((:instance
      (:rewrite intersectp-member)
      (y
       (names-at-relpath
        (frame-val->dir (cdr (assoc-equal x frame)))
        (nthcdr
         (len (frame-val->path (cdr (assoc-equal x frame))))
         relpath)))
      (x (remove-equal nil (strip-cars dir)))
      (a (nth (len relpath) pathname)))
     (:instance abs-find-file-helper-of-context-apply-lemma-4
                (fs dir)
                (pathname (nthcdr (len relpath) pathname))
                (n 0))
     (:instance
      abs-find-file-helper-of-context-apply-lemma-4
      (fs (frame-val->dir (cdr (assoc-equal x frame))))
      (pathname
       (nthcdr
        (len (frame-val->path (cdr (assoc-equal x frame))))
        pathname))
      (n
       (+
        (len relpath)
        (-
         (len
          (frame-val->path (cdr (assoc-equal x frame))))))))
     (:instance (:rewrite abs-separate-correctness-1-lemma-50)
                (src x))))))

(defthm
  abs-find-file-correctness-1-lemma-33
  (implies
   (and
    (fat32-filename-list-p pathname)
    (not (equal (mv-nth 1 (abs-find-file-helper fs pathname))
                *enoent*))
    (abs-file-alist-p fs))
   (member-equal (car pathname)
                 (remove-equal nil (strip-cars fs))))
  :hints (("goal" :in-theory (enable abs-find-file-helper))))

(defthm
  abs-find-file-correctness-1-lemma-37
  (implies
   (and (fat32-filename-list-p pathname)
        (not (equal (mv-nth 1
                            (abs-find-file-helper fs (nthcdr n pathname)))
                    *enoent*))
        (abs-file-alist-p fs))
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

(defthm
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
    (e/d (names-at-relpath take-of-nthcdr abs-find-file-helper)
         (abs-find-file-helper-of-context-apply-lemma-4 member-of-remove))
    :cases ((prefixp relpath
                     (frame-val->path (cdr (assoc-equal x frame))))))))

(defthm
  abs-find-file-correctness-1-lemma-21
  (implies
   (and
    (abs-file-alist-p dir)
    (not (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                  relpath))
    (fat32-filename-list-p pathname)
    (prefixp relpath pathname)
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
             pathname))
   (intersectp-equal
    (remove-equal nil
                  (strip-cars (frame-val->dir (cdr (assoc-equal x frame)))))
    (names-at-relpath
     dir
     (nthcdr (len relpath)
             (frame-val->path (cdr (assoc-equal x frame)))))))
  :hints
  (("goal"
    :in-theory
    (e/d (names-at-relpath take-of-nthcdr abs-find-file-helper)
         (abs-find-file-helper-of-context-apply-lemma-4 member-of-remove))
    :use
    ((:instance
      abs-find-file-helper-of-context-apply-lemma-4
      (fs (frame-val->dir (cdr (assoc-equal x frame))))
      (pathname (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                        pathname))
      (n 0))
     (:instance abs-find-file-helper-of-context-apply-lemma-4
                (fs dir)
                (pathname (nthcdr (len relpath) pathname))
                (n (+ (len (frame-val->path (cdr (assoc-equal x frame))))
                      (- (len relpath)))))
     (:theorem (equal (+ (len relpath)
                         (- (len relpath))
                         (len (frame-val->path (cdr (assoc-equal x frame)))))
                      (len (frame-val->path (cdr (assoc-equal x frame))))))
     (:instance
      intersectp-member
      (a (nth (len (frame-val->path (cdr (assoc-equal x frame))))
              pathname))
      (y (names-at-relpath
          dir
          (nthcdr (len relpath)
                  (frame-val->path (cdr (assoc-equal x frame))))))
      (x (remove-equal
          nil
          (strip-cars (frame-val->dir (cdr (assoc-equal x frame)))))))))))

(defthm
  abs-find-file-correctness-1-lemma-70
  (implies
   (and
    (abs-file-alist-p dir)
    (true-listp relpath)
    (not
     (intersectp-equal
      (remove-equal nil
                    (strip-cars (frame-val->dir (cdr (assoc-equal x frame)))))
      (names-at-relpath
       dir
       (nthcdr (len relpath)
               (frame-val->path (cdr (assoc-equal x frame)))))))
    (fat32-filename-list-p pathname)
    (prefixp relpath pathname)
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
             pathname))
   (intersectp-equal
    (remove-equal nil (strip-cars dir))
    (names-at-relpath
     (frame-val->dir (cdr (assoc-equal x frame)))
     (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
             relpath))))
  :hints
  (("goal"
    :do-not-induct t
    :cases ((and (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                          relpath)
                 (prefixp relpath
                          (frame-val->path (cdr (assoc-equal x frame))))))
    :in-theory (e/d (list-equiv nthcdr-when->=-n-len-l names-at-relpath)
                    ((:rewrite prefixp-when-equal-lengths)
                     member-of-remove))
    :use
    ((:instance (:rewrite prefixp-when-equal-lengths)
                (y (frame-val->path (cdr (assoc-equal x frame))))
                (x relpath))
     (:instance
      (:rewrite intersectp-member)
      (a (nth (len (frame-val->path (cdr (assoc-equal x frame))))
              pathname))
      (y (names-at-relpath
          dir
          (nthcdr (len relpath)
                  (frame-val->path (cdr (assoc-equal x frame))))))
      (x (remove-equal
          nil
          (strip-cars (frame-val->dir (cdr (assoc-equal x frame)))))))))))

;; This theorem is kinda inadequate. It would be better to prove that the
;; subterm of the LHS, which is proved to be non-zero, is actually
;; *enoent*. But that's not possible, because proving that it cannot be
;; *ENOTDIR* (necessary) can't be done without the additional knowledge of
;; collapsibility...
(defthm
  abs-find-file-correctness-1-lemma-22
  (implies
   (and
    (distinguish-names dir relpath frame)
    (abs-file-alist-p dir)
    (true-listp relpath)
    (consp (assoc-equal x frame))
    (fat32-filename-list-p pathname)
    (prefixp relpath pathname)
    (equal (mv-nth 1
                   (abs-find-file-helper dir (nthcdr (len relpath) pathname)))
           0)
    (prefixp (frame-val->path (cdr (assoc-equal x frame)))
             pathname))
   (not
    (equal
     (mv-nth 1
             (abs-find-file-helper
              (frame-val->dir (cdr (assoc-equal x frame)))
              (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                      pathname)))
     0)))
  :hints (("goal" :do-not-induct t
           :in-theory (disable abs-separate-correctness-1-lemma-22
                               abs-separate-correctness-1-lemma-24)
           :use (abs-separate-correctness-1-lemma-22
                 abs-separate-correctness-1-lemma-24)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (distinguish-names dir relpath frame)
      (abs-file-alist-p dir)
      (true-listp relpath)
      (consp (assoc-equal x frame))
      (fat32-filename-list-p pathname)
      (prefixp relpath pathname)
      (equal
       (mv-nth 1
               (abs-find-file-helper dir (nthcdr (len relpath) pathname)))
       0)
      (prefixp (frame-val->path (cdr (assoc-equal x frame)))
               pathname)
      (m1-file-alist-p (frame-val->dir (cdr (assoc-equal x frame))))
      (hifat-no-dups-p (frame-val->dir (cdr (assoc-equal x frame)))))
     (not
      (equal
       (mv-nth
        1
        (hifat-find-file
         (frame-val->dir (cdr (assoc-equal x frame)))
         (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                 pathname)))
       0))))))

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
    (fat32-filename-list-p pathname)
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
             pathname))
   (equal
    (abs-find-file-helper
     (frame-val->dir (cdr (assoc-equal x frame)))
     (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
             pathname))
    (abs-find-file frame pathname)))
  :hints (("goal" :induct t
           :in-theory (enable abs-find-file abs-separate)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and
      (consp (assoc-equal x frame))
      (fat32-filename-list-p pathname)
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
               pathname)
      (m1-file-alist-p (frame-val->dir (cdr (assoc-equal x frame))))
      (hifat-no-dups-p (frame-val->dir (cdr (assoc-equal x frame)))))
     (equal
      (hifat-find-file
       (frame-val->dir (cdr (assoc-equal x frame)))
       (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
               pathname))
      (abs-find-file frame pathname))))))

(defthm
  abs-find-file-correctness-1-lemma-25
  (implies
   (and
    (fat32-filename-list-p pathname)
    (equal (mv-nth 1 (abs-find-file-helper root pathname))
           2)
    (< 0 (1st-complete frame))
    (equal
     (mv-nth
      1
      (abs-find-file-helper
       (context-apply
        root
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (1st-complete frame)
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame))))
       pathname))
     0)
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-file-alist-p root)
    (abs-separate frame))
   (equal
    (mv-nth
     '1
     (hifat-find-file
      (frame-val->dir$inline (cdr (assoc-equal (1st-complete frame)
                                               frame)))
      (nthcdr (len (frame-val->path$inline
                    (cdr (assoc-equal (1st-complete frame)
                                      frame))))
              pathname)))
    '0)))

(defthm
  abs-find-file-correctness-1-lemma-26
  (implies
   (and
    (fat32-filename-list-p pathname)
    (equal (mv-nth 1 (abs-find-file-helper root pathname))
           2)
    (< 0 (1st-complete frame))
    (equal
     (mv-nth
      1
      (abs-find-file-helper
       (context-apply
        root
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (1st-complete frame)
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame))))
       pathname))
     0)
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-file-alist-p root))
   (prefixp
    (frame-val->path$inline (cdr (assoc-equal (1st-complete frame)
                                              frame)))
    pathname)))

(defthm
  abs-find-file-correctness-1-lemma-29
  (implies
   (and (abs-file-alist-p abs-file-alist1)
        (m1-file-alist-p abs-file-alist2)
        (fat32-filename-list-p pathname)
        (natp x)
        (m1-regular-file-p
         (mv-nth 0
                 (abs-find-file-helper abs-file-alist1 pathname))))
   (equal
    (mv-nth 0
            (abs-find-file-helper (context-apply abs-file-alist1
                                                 abs-file-alist2 x x-path)
                                  pathname))
    (mv-nth 0
            (abs-find-file-helper abs-file-alist1 pathname))))
  :hints
  (("goal"
    :in-theory (enable prefixp abs-find-file-helper
                       context-apply names-at-relpath)
    :induct
    (mv (mv-nth 0
                (abs-find-file-helper (context-apply abs-file-alist1
                                                     abs-file-alist2 x x-path)
                                      pathname))
        (prefixp x-path pathname)
        (context-apply abs-file-alist1
                       abs-file-alist2 x x-path))
    :expand
    ((abs-find-file-helper (append (remove-equal x abs-file-alist1)
                                   abs-file-alist2)
                           pathname)
     (abs-find-file-helper
      (put-assoc-equal
       (car x-path)
       (abs-file (abs-file->dir-ent (cdr (assoc-equal (car x-path)
                                                      abs-file-alist1)))
                 (context-apply
                  (abs-file->contents (cdr (assoc-equal (car x-path)
                                                        abs-file-alist1)))
                  abs-file-alist2 x (cdr x-path)))
       abs-file-alist1)
      pathname)))))

(defthm
  abs-find-file-correctness-1-lemma-30
  (implies
   (and (abs-file-alist-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist2)
        (fat32-filename-list-p pathname)
        (not (prefixp x-path pathname)))
   (equal
    (mv-nth 1
            (abs-find-file-helper (context-apply abs-file-alist1
                                                 abs-file-alist2 x x-path)
                                  pathname))
    (mv-nth 1
            (abs-find-file-helper abs-file-alist1 pathname))))
  :hints
  (("goal"
    :in-theory (enable prefixp abs-find-file-helper
                       context-apply names-at-relpath)
    :induct
    (mv (mv-nth 0
                (abs-find-file-helper (context-apply abs-file-alist1
                                                     abs-file-alist2 x x-path)
                                      pathname))
        (prefixp x-path pathname)
        (context-apply abs-file-alist1
                       abs-file-alist2 x x-path))
    :expand
    (abs-find-file-helper
     (put-assoc-equal
      (car x-path)
      (abs-file
       (abs-file->dir-ent (cdr (assoc-equal (car x-path)
                                            abs-file-alist1)))
       (context-apply (abs-file->contents (cdr (assoc-equal (car x-path)
                                                            abs-file-alist1)))
                      abs-file-alist2 x (cdr x-path)))
      abs-file-alist1)
     pathname))))

(defthm
  abs-find-file-correctness-1-lemma-32
  (implies
   (and
    (prefixp
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame)))
     pathname)
    (< 0 (1st-complete frame))
    (not
     (equal
      (context-apply
       root
       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                         frame)))
       (1st-complete frame)
       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                          frame))))
      root))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-file-alist-p root)
    (distinguish-names root nil frame)
    (abs-separate frame)
    (fat32-filename-list-p pathname)
    (equal
     (mv-nth
      1
      (abs-find-file-helper
       (context-apply
        root
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (1st-complete frame)
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame))))
       pathname))
     2))
   (equal
    (mv-nth
     '1
     (hifat-find-file
      (frame-val->dir$inline (cdr (assoc-equal (1st-complete frame)
                                               frame)))
      (nthcdr (len (frame-val->path$inline
                    (cdr (assoc-equal (1st-complete frame)
                                      frame))))
              pathname)))
    '2)))

(defthm
  abs-find-file-correctness-1-lemma-35
  (implies
   (and (consp (assoc-equal (car pathname)
                            abs-file-alist1))
        (abs-file-alist-p abs-file-alist1)
        (abs-file-alist-p abs-file-alist2)
        (fat32-filename-list-p pathname)
        (not (equal (mv-nth 1
                            (abs-find-file-helper abs-file-alist2 pathname))
                    2)))
   (intersectp-equal (remove-equal nil (strip-cars abs-file-alist1))
                     (remove-equal nil (strip-cars abs-file-alist2))))
  :hints
  (("goal"
    :use (:instance (:rewrite intersectp-member)
                    (a (car pathname))
                    (y (remove-equal nil (strip-cars abs-file-alist2)))
                    (x (remove-equal nil (strip-cars abs-file-alist1)))))))

(defthm
  abs-find-file-correctness-1-lemma-40
  (implies
   (and
    (equal (mv-nth 1
                   (abs-find-file (frame-with-root root frame)
                                  pathname))
           0)
    (< 0 (1st-complete frame))
    (not
     (equal
      (context-apply
       root
       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                         frame)))
       (1st-complete frame)
       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                          frame))))
      root))
    (equal
     (mv-nth
      1
      (abs-find-file
       (frame-with-root
        (context-apply
         root
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
                                              pathname)))
    (fat32-filename-list-p pathname))
   (equal
    (mv-nth 0
            (abs-find-file (frame-with-root root frame)
                           pathname))
    (mv-nth
     0
     (abs-find-file
      (frame-with-root
       (context-apply
        root
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (1st-complete frame)
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame))))
       (remove-assoc-equal (1st-complete frame)
                           frame))
      pathname))))
  :hints (("goal" :in-theory (enable abs-find-file frame-with-root abs-separate
                                     abs-find-file-correctness-1-lemma-59)
           :do-not-induct t)))

;; Kinda general
(defthm
  abs-find-file-correctness-1-lemma-14
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
   (and
    (fat32-filename-list-p pathname)
    (abs-file-alist-p root)
    (prefixp
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame)))
     pathname)
    (equal (mv-nth 1 (abs-find-file-helper root pathname))
           0)
    (distinguish-names root nil frame))
   (equal
    (mv-nth
     1
     (abs-find-file-helper
      (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                        frame)))
      (nthcdr
       (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                               frame))))
       pathname)))
    *enoent*))
  :hints
  (("goal"
    :do-not-induct t
    :cases
    ((equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (nthcdr
         (len
          (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                             frame))))
         pathname)))
      0)
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (nthcdr
         (len
          (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                             frame))))
         pathname)))
      *enotdir*))
    :in-theory (e/d (abs-find-file-helper)
                    ((:rewrite abs-separate-correctness-1-lemma-12)
                     abs-find-file-helper-of-context-apply-lemma-4
                     (:rewrite abs-find-file-correctness-1-lemma-18)))
    :use
    ((:instance (:rewrite abs-separate-correctness-1-lemma-12)
                (x (1st-complete frame)))
     (:instance
      (:rewrite intersectp-member)
      (a
       (car
        (nthcdr
         (len
          (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                             frame))))
         pathname)))
      (y
       (names-at-relpath
        root
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame)))))
      (x
       (remove-equal
        nil
        (strip-cars
         (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                           frame)))))))
     (:instance
      abs-find-file-helper-of-context-apply-lemma-4
      (fs root)
      (n
       (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                               frame))))))
     (:instance
      (:rewrite abs-find-file-correctness-1-lemma-18)
      (pathname
       (nthcdr
        (len
         (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                            frame))))
        pathname))
      (fs (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame)))))))))

;; This is interesting because it talks about two arbitrarily chosen abstract
;; variables.
(defthm
  abs-find-file-correctness-1-lemma-34
  (implies
   (and (abs-separate frame)
        (consp (assoc-equal y frame))
        (not (equal x y))
        (prefixp (frame-val->path (cdr (assoc-equal y frame)))
                 (frame-val->path (cdr (assoc-equal x frame)))))
   (not
    (intersectp-equal
     (remove-equal nil
                   (strip-cars (frame-val->dir (cdr (assoc-equal x frame)))))
     (names-at-relpath
      (frame-val->dir (cdr (assoc-equal y frame)))
      (nthcdr (len (frame-val->path (cdr (assoc-equal y frame))))
              (frame-val->path (cdr (assoc-equal x frame))))))))
  :hints (("goal" :in-theory (enable abs-separate)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies
     (and (abs-separate frame)
          (consp (assoc-equal y frame))
          (not (equal x y))
          (prefixp (frame-val->path (cdr (assoc-equal y frame)))
                   (frame-val->path (cdr (assoc-equal x frame))))
          (not
           (member-equal
            nil
            (strip-cars (frame-val->dir (cdr (assoc-equal x frame)))))))
     (not
      (intersectp-equal
       (strip-cars (frame-val->dir (cdr (assoc-equal x frame))))
       (names-at-relpath
        (frame-val->dir (cdr (assoc-equal y frame)))
        (nthcdr (len (frame-val->path (cdr (assoc-equal y frame))))
                (frame-val->path (cdr (assoc-equal x frame)))))))))))

(defthm
  abs-find-file-correctness-1-lemma-43
  (implies
   (and (fat32-filename-list-p pathname2)
        (abs-file-alist-p fs)
        (zp (mv-nth 1 (abs-find-file-helper fs pathname1)))
        (abs-directory-file-p (mv-nth 0 (abs-find-file-helper fs pathname1)))
        (equal (mv-nth 1 (abs-find-file-helper fs pathname2))
               *enotdir*)
        (prefixp pathname1 pathname2))
   (member-equal (nth (len pathname1) pathname2)
                 (names-at-relpath fs pathname1)))
  :hints (("goal" :in-theory (enable abs-find-file-helper
                                     names-at-relpath prefixp))
          ("goal''" :induct t
           :expand ((names-at-relpath fs pathname1)))))

(defthm
  abs-find-file-correctness-1-lemma-49
  (implies
   (and
    (not
     (equal
      (context-apply
       root
       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                         frame)))
       (1st-complete frame)
       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                          frame))))
      root))
    (fat32-filename-list-p pathname)
    (abs-file-alist-p root)
    (prefixp
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame)))
     pathname)
    (not (equal (mv-nth 1 (abs-find-file-helper root pathname))
                2))
    (distinguish-names root nil frame))
   (equal
    (abs-find-file-helper
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (nthcdr
      (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                              frame))))
      pathname))
    (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :do-not-induct t
    :in-theory (e/d (abs-find-file-helper)
                    ((:rewrite abs-find-file-correctness-1-lemma-33)))
    :use
    ((:instance
      (:rewrite abs-find-file-correctness-1-lemma-33)
      (fs (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame))))
      (pathname
       (nthcdr
        (len
         (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                            frame))))
        pathname)))
     (:instance
      (:rewrite intersectp-member)
      (a
       (car
        (nthcdr
         (len
          (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                             frame))))
         pathname)))
      (y
       (names-at-relpath
        root
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame)))))
      (x
       (remove-equal
        nil
        (strip-cars
         (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                           frame))))))))
    :cases
    ((and
      (fat32-filename-list-p
       (nthcdr
        (len
         (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                            frame))))
        pathname))
      (not
       (equal
        (mv-nth
         1
         (abs-find-file-helper
          (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame)))
          (nthcdr
           (len
            (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                               frame))))
           pathname)))
        2))
      (abs-file-alist-p
       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                         frame))))
      (equal (mv-nth 1 (abs-find-file-helper root pathname))
             0))
     (and
      (fat32-filename-list-p
       (nthcdr
        (len
         (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                            frame))))
        pathname))
      (not
       (equal
        (mv-nth
         1
         (abs-find-file-helper
          (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame)))
          (nthcdr
           (len
            (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                               frame))))
           pathname)))
        2))
      (abs-file-alist-p
       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                         frame))))
      (not (equal (mv-nth 1 (abs-find-file-helper root pathname))
                  0)))))
   ("subgoal 1''"
    :in-theory (enable names-at-relpath abs-find-file-helper)
    :cases
    ((consp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                               frame))))))))

(defthm
  abs-find-file-correctness-1-lemma-7
  (implies
   (and
    (not
     (equal
      (context-apply
       root
       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                         frame)))
       (1st-complete frame)
       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                          frame))))
      root))
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
  abs-find-file-correctness-1-lemma-11
  (implies
   (and (not (equal (1st-complete frame)
                    (1st-complete-src frame)))
        (equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                 frame)))
               (1st-complete frame)))
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

(encapsulate
  ()

  (local
   (defun
       induction-scheme (frame pathname root x)
     (declare (xargs :measure (len frame)))
     (cond
      ((and
        (not (atom frame))
        (not (zp (1st-complete frame)))
        (not (zp (1st-complete-src frame)))
        (not (or (equal (1st-complete-src frame)
                        (1st-complete frame))
                 (atom (assoc-equal (1st-complete-src frame)
                                    (remove-assoc-equal (1st-complete frame)
                                                        frame)))))
        (prefixp (frame-val->path
                  (cdr (assoc-equal (1st-complete-src frame)
                                    (remove-assoc-equal (1st-complete frame)
                                                        frame))))
                 (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                    frame))))
        (not
         (equal
          (context-apply
           (frame-val->dir
            (cdr (assoc-equal (1st-complete-src frame)
                              (remove-assoc-equal (1st-complete frame)
                                                  frame))))
           (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                             frame)))
           (1st-complete frame)
           (nthcdr
            (len (frame-val->path
                  (cdr (assoc-equal (1st-complete-src frame)
                                    (remove-assoc-equal (1st-complete frame)
                                                        frame)))))
            (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                               frame)))))
          (frame-val->dir
           (cdr (assoc-equal (1st-complete-src frame)
                             (remove-assoc-equal (1st-complete frame)
                                                 frame))))))
        (equal x (1st-complete frame)))
       (induction-scheme
        (put-assoc-equal
         (1st-complete-src frame)
         (frame-val
          (frame-val->path
           (cdr (assoc-equal (1st-complete-src frame)
                             (remove-assoc-equal (1st-complete frame)
                                                 frame))))
          (context-apply
           (frame-val->dir
            (cdr (assoc-equal (1st-complete-src frame)
                              (remove-assoc-equal (1st-complete frame)
                                                  frame))))
           (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                             frame)))
           (1st-complete frame)
           (nthcdr
            (len (frame-val->path
                  (cdr (assoc-equal (1st-complete-src frame)
                                    (remove-assoc-equal (1st-complete frame)
                                                        frame)))))
            (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                               frame)))))
          (frame-val->src
           (cdr (assoc-equal (1st-complete-src frame)
                             (remove-assoc-equal (1st-complete frame)
                                                 frame)))))
         (remove-assoc-equal (1st-complete frame)
                             frame))
        pathname root
        (frame-val->src (cdr (assoc-equal x frame)))))
      ((and
        (not (atom frame))
        (not (zp (1st-complete frame)))
        (not (zp (1st-complete-src frame)))
        (not (or (equal (1st-complete-src frame)
                        (1st-complete frame))
                 (atom (assoc-equal (1st-complete-src frame)
                                    (remove-assoc-equal (1st-complete frame)
                                                        frame)))))
        (prefixp (frame-val->path
                  (cdr (assoc-equal (1st-complete-src frame)
                                    (remove-assoc-equal (1st-complete frame)
                                                        frame))))
                 (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                    frame))))
        (not
         (equal
          (context-apply
           (frame-val->dir
            (cdr (assoc-equal (1st-complete-src frame)
                              (remove-assoc-equal (1st-complete frame)
                                                  frame))))
           (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                             frame)))
           (1st-complete frame)
           (nthcdr
            (len (frame-val->path
                  (cdr (assoc-equal (1st-complete-src frame)
                                    (remove-assoc-equal (1st-complete frame)
                                                        frame)))))
            (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                               frame)))))
          (frame-val->dir
           (cdr (assoc-equal (1st-complete-src frame)
                             (remove-assoc-equal (1st-complete frame)
                                                 frame)))))))
       (induction-scheme
        (put-assoc-equal
         (1st-complete-src frame)
         (frame-val
          (frame-val->path
           (cdr (assoc-equal (1st-complete-src frame)
                             (remove-assoc-equal (1st-complete frame)
                                                 frame))))
          (context-apply
           (frame-val->dir
            (cdr (assoc-equal (1st-complete-src frame)
                              (remove-assoc-equal (1st-complete frame)
                                                  frame))))
           (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                             frame)))
           (1st-complete frame)
           (nthcdr
            (len (frame-val->path
                  (cdr (assoc-equal (1st-complete-src frame)
                                    (remove-assoc-equal (1st-complete frame)
                                                        frame)))))
            (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                               frame)))))
          (frame-val->src
           (cdr (assoc-equal (1st-complete-src frame)
                             (remove-assoc-equal (1st-complete frame)
                                                 frame)))))
         (remove-assoc-equal (1st-complete frame)
                             frame))
        pathname root x))
      ((and
        (not (atom frame))
        (not (zp (1st-complete frame)))
        (zp (1st-complete-src frame))
        (not
         (equal
          (context-apply root
                         (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                           frame)))
                         (1st-complete frame)
                         (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                            frame))))
          root)))
       (induction-scheme
        (remove-assoc-equal (1st-complete frame)
                            frame)
        pathname
        (context-apply root
                       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       (1st-complete frame)
                       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                          frame))))
        x))
      (t (list frame pathname root x)))))

  ;; Rather general!
  (defthmd
    abs-find-file-correctness-1-lemma-50
    (implies
     (and
      (fat32-filename-list-p pathname)
      (abs-file-alist-p root)
      (frame-p frame)
      (equal (mv-nth 1 (collapse root frame))
             t)
      (consp (assoc-equal x frame))
      (prefixp (frame-val->path (cdr (assoc-equal x frame)))
               pathname)
      (not
       (equal (mv-nth 1 (abs-find-file-helper root pathname))
              *enoent*))
      (distinguish-names root nil frame)
      (abs-separate frame))
     (equal
      (abs-find-file-helper
       (frame-val->dir (cdr (assoc-equal x frame)))
       (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
               pathname))
      (mv (abs-file-fix nil) *enoent*)))
    :hints (("goal" :induct (induction-scheme frame pathname root x)
             :in-theory (enable collapse)))))

(defthm
  abs-find-file-correctness-1-lemma-36
  (implies
   (and
    (abs-file-alist-p root)
    (not
     (equal
      (context-apply
       root
       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                         frame)))
       (1st-complete frame)
       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                          frame))))
      root)))
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

(encapsulate
  ()

  (local
   (defthmd
     abs-find-file-correctness-1-lemma-60
     (implies
      (and (prefixp pathname x-path)
           (m1-regular-file-p (mv-nth 0 (abs-find-file-helper fs pathname)))
           (fat32-filename-list-p pathname)
           (fat32-filename-list-p x-path))
      (equal
       (abs-find-file-helper fs x-path)
       (if
           (equal pathname x-path)
           (abs-find-file-helper fs pathname)
         (mv (abs-file-fix nil) *enotdir*))))
     :hints
     (("goal" :in-theory (enable abs-find-file-helper prefixp)))))

  (defthmd
    abs-find-file-correctness-1-lemma-61
    (implies
     (and (prefixp pathname x-path)
          (m1-regular-file-p (mv-nth 0 (abs-find-file-helper fs pathname)))
          (not
           (fat32-filename-list-equiv pathname x-path)))
     (equal
      (abs-find-file-helper fs x-path)
      (mv (abs-file-fix nil) *enotdir*)))
    :hints
    (("goal"
      :use
      (:instance
       abs-find-file-correctness-1-lemma-60
       (pathname (fat32-filename-list-fix pathname))
       (x-path (fat32-filename-list-fix x-path)))))))

(defthm
  abs-find-file-correctness-1-lemma-12
  (implies
   (and (equal (mv-nth 1 (abs-find-file frame pathname))
               *enoent*)
        (consp (assoc-equal x frame))
        (prefixp (frame-val->path (cdr (assoc-equal x frame)))
                 pathname))
   (equal
     (abs-find-file-helper
      (frame-val->dir (cdr (assoc-equal x frame)))
      (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
              pathname))
    (mv (abs-file-fix nil)
        *enoent*)))
  :hints (("goal" :in-theory (enable abs-find-file))))

;; (encapsulate
;;   ()

;;   (local
;;    (include-book "std/basic/inductions" :dir :system))

;;   ;; Use abs-find-file-correctness-1-lemma-50 for this one.
;;   (defthm
;;     abs-find-file-correctness-1-lemma-64
;;     (implies (and (fat32-filename-list-p pathname)
;;                   (abs-file-alist-p root)
;;                   (frame-p frame)
;;                   (equal (mv-nth 1 (collapse root frame))
;;                          t)
;;                   (not (equal (mv-nth 1 (abs-find-file-helper root pathname))
;;                               *enoent*))
;;                   (distinguish-names root nil frame)
;;                   (abs-separate frame)
;;                   (natp n)
;;                   (no-duplicatesp-equal (strip-cars frame)))
;;              (equal (abs-find-file (nthcdr (- (len frame) n) frame)
;;                                    pathname)
;;                     (mv (abs-file-fix nil) *enoent*)))
;;     :hints
;;     (("goal" :induct (dec-induct n)
;;       :in-theory (enable abs-find-file))
;;      ("subgoal *1/2''"
;;       :in-theory (disable (:rewrite consp-of-nth-when-alistp))
;;       :use ((:instance (:rewrite abs-find-file-correctness-1-lemma-50)
;;                        (pathname pathname)
;;                        (frame frame)
;;                        (x (car (nth (+ (- n) (len frame)) frame))))
;;             (:instance (:rewrite consp-of-nth-when-alistp)
;;                        (l frame)
;;                        (n (+ (- n) (len frame)))))))))

;; ;; Nifty use hint! But also, it seems like this theorem is useless...
;; (defthm
;;   abs-find-file-correctness-1-lemma-66
;;   (implies (and (fat32-filename-list-p pathname)
;;                 (abs-file-alist-p root)
;;                 (frame-p frame)
;;                 (equal (mv-nth 1 (collapse root frame))
;;                        t)
;;                 (not (equal (mv-nth 1 (abs-find-file-helper root pathname))
;;                             *enoent*))
;;                 (distinguish-names root nil frame)
;;                 (abs-separate frame)
;;                 (no-duplicatesp-equal (strip-cars frame)))
;;            (equal (abs-find-file frame pathname)
;;                   (mv (abs-file-fix nil) *enoent*)))
;;   :hints (("goal" :in-theory (disable abs-find-file-correctness-1-lemma-64)
;;            :use (:instance abs-find-file-correctness-1-lemma-64
;;                            (n (len frame))))))

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
      pathname)
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
  abs-find-file-correctness-1-lemma-51
  (implies
   (and
    (< 0 (1st-complete frame))
    (fat32-filename-list-p pathname)
    (abs-file-alist-p root)
    (frame-p frame)
    (not
     (equal
      (context-apply
       root
       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                         frame)))
       (1st-complete frame)
       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                          frame))))
      root))
    (equal
     (mv-nth
      1
      (collapse
       (context-apply
        root
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (1st-complete frame)
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame))))
       (remove-assoc-equal (1st-complete frame)
                           frame)))
     t)
    (consp (assoc-equal y frame))
    (not (equal (1st-complete frame)
                y))
    (prefixp
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame)))
     pathname)
    (prefixp (frame-val->path (cdr (assoc-equal y frame)))
             pathname)
    (distinguish-names root nil frame)
    (abs-separate frame)
    (not
     (equal
      (mv-nth
       1
       (abs-find-file-helper
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (nthcdr
         (len
          (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                             frame))))
         pathname)))
      2)))
   (equal (abs-find-file-helper
           (frame-val->dir (cdr (assoc-equal y frame)))
           (nthcdr (len (frame-val->path (cdr (assoc-equal y frame))))
                   pathname))
          '(((dir-ent 0 0 0 0 0 0 0 0 0 0 0 0
                      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
             (contents))
            2)))
  :hints
  (("goal"
    :use
    ((:instance
      (:rewrite abs-find-file-correctness-1-lemma-50)
      (frame (remove-assoc-equal (1st-complete frame)
                                 frame))
      (x y)
      (root
       (context-apply
        root
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (1st-complete frame)
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame))))))))))

(defthm
  abs-find-file-correctness-1-lemma-72
  (implies
   (and
    (< 0 (1st-complete frame))
    (fat32-filename-list-p pathname)
    (abs-file-alist-p root)
    (frame-p frame)
    (not
     (equal
      (context-apply
       root
       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                         frame)))
       (1st-complete frame)
       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                          frame))))
      root))
    (equal
     (mv-nth
      1
      (collapse
       (context-apply
        root
        (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                          frame)))
        (1st-complete frame)
        (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                           frame))))
       (remove-assoc-equal (1st-complete frame)
                           frame)))
     t)
    (consp (assoc-equal x frame))
    (not (equal x (1st-complete frame)))
    (prefixp (frame-val->path (cdr (assoc-equal x frame)))
             pathname)
    (prefixp
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame)))
     pathname)
    (distinguish-names root nil frame)
    (abs-separate frame)
    (not
     (equal
      (abs-find-file-helper
       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                         frame)))
       (nthcdr
        (len
         (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                            frame))))
        pathname))
      '(((dir-ent 0 0 0 0 0 0 0 0 0 0 0 0
                  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
         (contents))
        2))))
   (equal
    (mv-nth 1
            (abs-find-file-helper
             (frame-val->dir (cdr (assoc-equal x frame)))
             (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                     pathname)))
    2))
  :hints
  (("goal"
    :use
    (:instance
     (:rewrite abs-find-file-correctness-1-lemma-50)
     (root
      (context-apply
       root
       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                         frame)))
       (1st-complete frame)
       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                          frame)))))
     (frame (remove-assoc-equal (1st-complete frame)
                                frame))
     (x x)))))

(defthm
  abs-find-file-correctness-1-lemma-74
  (implies
   (and
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
  abs-find-file-correctness-1-lemma-75
  (implies
   (and
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
     20)
    (not
     (equal
      (context-apply
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
      (frame-val->dir
       (cdr
        (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                       frame)))
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
  (("goal"
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

(defthm
  abs-find-file-correctness-1-lemma-76
  (implies
   (and
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
     20)
    (prefixp
     (frame-val->path
      (cdr (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                          frame)))
                        frame)))
     (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                        frame))))
    (fat32-filename-list-p pathname)
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
      pathname))
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
   (member-equal
    (nth (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                 frame))))
         pathname)
    (names-at-relpath
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
    :in-theory
    (disable nth-when-prefixp
             (:rewrite abs-find-file-helper-of-context-apply-lemma-4)
             (:rewrite take-when-prefixp)
             prefixp-one-way-or-another
             (:rewrite abs-find-file-correctness-1-lemma-75))
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
        pathname))
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
      (:rewrite abs-find-file-helper-of-context-apply-lemma-4)
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
         pathname)))
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
        pathname))
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
         pathname)))
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

(defthm
  abs-find-file-correctness-1-lemma-77
  (implies
   (and
    (not
     (member-equal
      (nth (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                   frame))))
           pathname)
      (names-at-relpath
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
    (not
     (equal
      (context-apply
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
      (frame-val->dir
       (cdr
        (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                       frame)))
                     frame)))))
    (fat32-filename-list-p pathname)
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))
             pathname))
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
    :in-theory (e/d (take-of-nthcdr abs-find-file-helper)
                    (abs-find-file-correctness-1-lemma-34
                     (:rewrite abs-find-file-correctness-1-lemma-18)))
    :use
    (:instance
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
                     frame))))))))

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
    (not
     (equal
      (context-apply
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
      (frame-val->dir
       (cdr
        (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                       frame)))
                     frame)))))
    (fat32-filename-list-p pathname)
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))
             pathname)
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
         (abs-find-file-correctness-1-lemma-34
          (:rewrite abs-find-file-helper-of-context-apply-lemma-4)))
    :use
    ((:instance abs-find-file-correctness-1-lemma-34
                (x (1st-complete frame))
                (y (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                     frame)))))
     (:instance
      (:rewrite intersectp-member)
      (a
       (car
        (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                        frame))))
                pathname)))
      (y
       (names-at-relpath
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
      (x
       (remove-equal
        nil
        (strip-cars (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                      frame)))))))
     (:instance
      (:rewrite abs-find-file-helper-of-context-apply-lemma-4)
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
        pathname))
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
                 frame))))))))))))

(defthm
  abs-find-file-correctness-1-lemma-80
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
    (not
     (equal
      (context-apply
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
      (frame-val->dir
       (cdr
        (assoc-equal (frame-val->src (cdr (assoc-equal (1st-complete frame)
                                                       frame)))
                     frame)))))
    (fat32-filename-list-p pathname)
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))
             pathname)
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
      2)))
   (equal
    (abs-find-file-helper
     (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                       frame)))
     (nthcdr (len (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                     frame))))
             pathname))
    '(((dir-ent 0 0 0 0 0 0 0 0 0 0 0 0
                0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
       (contents))
      2)))
  :hints (("goal" :in-theory (disable abs-find-file-correctness-1-lemma-27)
           :use abs-find-file-correctness-1-lemma-27)))

(defthm
  abs-find-file-correctness-1-lemma-19
  (implies
   (and
    (equal (1st-complete-src frame) 0)
    (fat32-filename-list-p pathname)
    (abs-file-alist-p root)
    (frame-p frame)
    (equal (mv-nth 1 (collapse root frame))
           t)
    (consp (assoc-equal y frame))
    (not (equal (1st-complete frame) y))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))
             pathname)
    (prefixp (frame-val->path (cdr (assoc-equal y frame)))
             pathname)
    (distinguish-names root nil frame)
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
   (equal (abs-find-file-helper
           (frame-val->dir (cdr (assoc-equal y frame)))
           (nthcdr (len (frame-val->path (cdr (assoc-equal y frame))))
                   pathname))
          (mv (abs-file-fix nil) *enoent*)))
  :hints
  (("goal"
    :in-theory (enable collapse 1st-complete-src)
    :use
    ((:instance
      (:rewrite abs-find-file-correctness-1-lemma-50)
      (root (context-apply
             root
             (frame-val->dir (cdr (abs-assoc (1st-complete frame) frame)))
             (1st-complete frame)
             (frame-val->path (cdr (abs-assoc (1st-complete frame)
                                              frame)))))
      (frame (remove-assoc-equal (1st-complete frame)
                                 frame))
      (x y))))))

(defthm
  abs-find-file-correctness-1-lemma-31
  (implies
   (and
    (equal (1st-complete-src frame) 0)
    (fat32-filename-list-p pathname)
    (abs-file-alist-p root)
    (frame-p frame)
    (equal (mv-nth 1 (collapse root frame))
           t)
    (consp (assoc-equal x frame))
    (not (equal x (1st-complete frame)))
    (prefixp (frame-val->path (cdr (assoc-equal x frame)))
             pathname)
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))
             pathname)
    (distinguish-names root nil frame)
    (abs-separate frame)
    (not
     (equal
      (mv-nth 1
              (abs-find-file-helper
               (frame-val->dir (cdr (assoc-equal x frame)))
               (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
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
  :hints
  (("goal"
    :in-theory (enable collapse 1st-complete-src)
    :use
    ((:instance
      (:rewrite abs-find-file-correctness-1-lemma-50)
      (frame (abs-remove-assoc (1st-complete frame)
                               frame))
      (root (context-apply
             root
             (frame-val->dir (cdr (abs-assoc (1st-complete frame) frame)))
             (1st-complete frame)
             (frame-val->path (cdr (abs-assoc (1st-complete frame)
                                              frame))))))))))

(defthm
  abs-find-file-correctness-1-lemma-38
  (implies
   (and
    (not (equal (1st-complete-src frame)
                (1st-complete frame)))
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                frame)))
             (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame))))
    (not
     (equal
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
      (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                        frame)))))
    (fat32-filename-list-p pathname)
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))
             pathname)
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
  :hints (("goal" :in-theory (enable 1st-complete-src))))

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
    (not
     (equal
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
      (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                        frame)))))
    (fat32-filename-list-p pathname)
    (prefixp (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                frame)))
             pathname)
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

(encapsulate
  ()

  (local
   (defun induction-scheme (frame pathname root x y)
     (declare (xargs :measure (len frame)))
     (cond
      ((and
        (not (atom frame))
        (not (zp (1st-complete frame)))
        (not (zp (1st-complete-src frame)))
        (not (or (equal (1st-complete-src frame)
                        (1st-complete frame))
                 (atom (assoc-equal (1st-complete-src frame)
                                    (remove-assoc-equal (1st-complete frame)
                                                        frame)))))
        (prefixp (frame-val->path
                  (cdr (assoc-equal (1st-complete-src frame)
                                    (remove-assoc-equal (1st-complete frame)
                                                        frame))))
                 (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                    frame))))
        (not
         (equal
          (context-apply
           (frame-val->dir
            (cdr (assoc-equal (1st-complete-src frame)
                              (remove-assoc-equal (1st-complete frame)
                                                  frame))))
           (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                             frame)))
           (1st-complete frame)
           (nthcdr
            (len (frame-val->path
                  (cdr (assoc-equal (1st-complete-src frame)
                                    (remove-assoc-equal (1st-complete frame)
                                                        frame)))))
            (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                               frame)))))
          (frame-val->dir
           (cdr (assoc-equal (1st-complete-src frame)
                             (remove-assoc-equal (1st-complete frame)
                                                 frame))))))
        (equal x (1st-complete frame)))
       (induction-scheme
        (put-assoc-equal
         (1st-complete-src frame)
         (frame-val
          (frame-val->path
           (cdr (assoc-equal (1st-complete-src frame)
                             (remove-assoc-equal (1st-complete frame)
                                                 frame))))
          (context-apply
           (frame-val->dir
            (cdr (assoc-equal (1st-complete-src frame)
                              (remove-assoc-equal (1st-complete frame)
                                                  frame))))
           (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                             frame)))
           (1st-complete frame)
           (nthcdr
            (len (frame-val->path
                  (cdr (assoc-equal (1st-complete-src frame)
                                    (remove-assoc-equal (1st-complete frame)
                                                        frame)))))
            (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                               frame)))))
          (frame-val->src
           (cdr (assoc-equal (1st-complete-src frame)
                             (remove-assoc-equal (1st-complete frame)
                                                 frame)))))
         (remove-assoc-equal (1st-complete frame)
                             frame))
        pathname root (1st-complete-src frame)
        y))
      ((and
        (not (atom frame))
        (not (zp (1st-complete frame)))
        (not (zp (1st-complete-src frame)))
        (not (or (equal (1st-complete-src frame)
                        (1st-complete frame))
                 (atom (assoc-equal (1st-complete-src frame)
                                    (remove-assoc-equal (1st-complete frame)
                                                        frame)))))
        (prefixp (frame-val->path
                  (cdr (assoc-equal (1st-complete-src frame)
                                    (remove-assoc-equal (1st-complete frame)
                                                        frame))))
                 (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                    frame))))
        (not
         (equal
          (context-apply
           (frame-val->dir
            (cdr (assoc-equal (1st-complete-src frame)
                              (remove-assoc-equal (1st-complete frame)
                                                  frame))))
           (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                             frame)))
           (1st-complete frame)
           (nthcdr
            (len (frame-val->path
                  (cdr (assoc-equal (1st-complete-src frame)
                                    (remove-assoc-equal (1st-complete frame)
                                                        frame)))))
            (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                               frame)))))
          (frame-val->dir
           (cdr (assoc-equal (1st-complete-src frame)
                             (remove-assoc-equal (1st-complete frame)
                                                 frame))))))
        (equal y (1st-complete frame)))
       (induction-scheme
        (put-assoc-equal
         (1st-complete-src frame)
         (frame-val
          (frame-val->path
           (cdr (assoc-equal (1st-complete-src frame)
                             (remove-assoc-equal (1st-complete frame)
                                                 frame))))
          (context-apply
           (frame-val->dir
            (cdr (assoc-equal (1st-complete-src frame)
                              (remove-assoc-equal (1st-complete frame)
                                                  frame))))
           (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                             frame)))
           (1st-complete frame)
           (nthcdr
            (len (frame-val->path
                  (cdr (assoc-equal (1st-complete-src frame)
                                    (remove-assoc-equal (1st-complete frame)
                                                        frame)))))
            (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                               frame)))))
          (frame-val->src
           (cdr (assoc-equal (1st-complete-src frame)
                             (remove-assoc-equal (1st-complete frame)
                                                 frame)))))
         (remove-assoc-equal (1st-complete frame)
                             frame))
        pathname
        root x (1st-complete-src frame)))
      ((and
        (not (atom frame))
        (not (zp (1st-complete frame)))
        (not (zp (1st-complete-src frame)))
        (not (or (equal (1st-complete-src frame)
                        (1st-complete frame))
                 (atom (assoc-equal (1st-complete-src frame)
                                    (remove-assoc-equal (1st-complete frame)
                                                        frame)))))
        (prefixp (frame-val->path
                  (cdr (assoc-equal (1st-complete-src frame)
                                    (remove-assoc-equal (1st-complete frame)
                                                        frame))))
                 (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                    frame))))
        (not
         (equal
          (context-apply
           (frame-val->dir
            (cdr (assoc-equal (1st-complete-src frame)
                              (remove-assoc-equal (1st-complete frame)
                                                  frame))))
           (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                             frame)))
           (1st-complete frame)
           (nthcdr
            (len (frame-val->path
                  (cdr (assoc-equal (1st-complete-src frame)
                                    (remove-assoc-equal (1st-complete frame)
                                                        frame)))))
            (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                               frame)))))
          (frame-val->dir
           (cdr (assoc-equal (1st-complete-src frame)
                             (remove-assoc-equal (1st-complete frame)
                                                 frame)))))))
       (induction-scheme
        (put-assoc-equal
         (1st-complete-src frame)
         (frame-val
          (frame-val->path
           (cdr (assoc-equal (1st-complete-src frame)
                             (remove-assoc-equal (1st-complete frame)
                                                 frame))))
          (context-apply
           (frame-val->dir
            (cdr (assoc-equal (1st-complete-src frame)
                              (remove-assoc-equal (1st-complete frame)
                                                  frame))))
           (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                             frame)))
           (1st-complete frame)
           (nthcdr
            (len (frame-val->path
                  (cdr (assoc-equal (1st-complete-src frame)
                                    (remove-assoc-equal (1st-complete frame)
                                                        frame)))))
            (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                               frame)))))
          (frame-val->src
           (cdr (assoc-equal (1st-complete-src frame)
                             (remove-assoc-equal (1st-complete frame)
                                                 frame)))))
         (remove-assoc-equal (1st-complete frame)
                             frame))
        pathname root x y))
      ((and
        (not (atom frame))
        (not (zp (1st-complete frame)))
        (zp (1st-complete-src frame))
        (not
         (equal
          (context-apply root
                         (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                           frame)))
                         (1st-complete frame)
                         (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                            frame))))
          root)))
       (induction-scheme
        (remove-assoc-equal (1st-complete frame)
                            frame)
        pathname
        (context-apply root
                       (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                         frame)))
                       (1st-complete frame)
                       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                          frame))))
        x y))
      (t
       (mv frame pathname root x y)))))

  ;; This is important, but the induction scheme and subgoals were a drag.
  (defthm
    abs-find-file-correctness-1-lemma-41
    (implies
     (and
      (fat32-filename-list-p pathname)
      (abs-file-alist-p root)
      (frame-p frame)
      (equal (mv-nth 1 (collapse root frame))
             t)
      (consp (assoc-equal x frame))
      (consp (assoc-equal y frame))
      (not (equal x y))
      (prefixp (frame-val->path (cdr (assoc-equal x frame)))
               pathname)
      (prefixp (frame-val->path (cdr (assoc-equal y frame)))
               pathname)
      (distinguish-names root nil frame)
      (abs-separate frame)
      (not
       (equal
        (mv-nth
         1
         (abs-find-file-helper
          (frame-val->dir (cdr (assoc-equal x frame)))
          (nthcdr (len (frame-val->path (cdr (assoc-equal x frame))))
                  pathname)))
        *enoent*)))
     (equal
      (abs-find-file-helper
       (frame-val->dir (cdr (assoc-equal y frame)))
       (nthcdr (len (frame-val->path (cdr (assoc-equal y frame))))
               pathname))
      (mv (abs-file-fix nil) *enoent*)))
    :hints
    (("goal" :do-not-induct t
      :induct (induction-scheme frame pathname root x y)
      :in-theory (enable collapse)))))

(defthm
  abs-find-file-correctness-1-lemma-52
  (implies
   (and
    (fat32-filename-list-p pathname)
    (abs-file-alist-p root)
    (frame-p frame)
    (equal (mv-nth 1 (collapse root frame))
           t)
    (consp (assoc-equal x frame))
    (subsetp-equal indices (strip-cars frame))
    (not (member-equal x indices))
    (prefixp (frame-val->path (cdr (assoc-equal x frame)))
             pathname)
    (distinguish-names root nil frame)
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
   ("subgoal *1/2'"
    :expand (subsetp-equal indices (strip-cars frame))
    :use ((:instance (:type-prescription member-of-strip-cars . 2)
                     (alist frame)
                     (x (car indices)))
          (:instance member-of-a-nat-list (x nil)
                     (lst (strip-cars frame)))))))

(defthm
  abs-find-file-correctness-1-lemma-85
  (implies
   (and
    (fat32-filename-list-p pathname)
    (abs-file-alist-p root)
    (frame-p frame)
    (equal (mv-nth 1 (collapse root frame))
           t)
    (consp (assoc-equal x frame))
    (prefixp (frame-val->path (cdr (assoc-equal x frame)))
             pathname)
    (distinguish-names root nil frame)
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
  (("goal" :in-theory (disable abs-find-file-correctness-1-lemma-52)
    :use (:instance abs-find-file-correctness-1-lemma-52
                    (indices (remove-equal x (strip-cars frame)))))))

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
    (not
     (equal
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
      (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                        frame)))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-file-alist-p root)
    (distinguish-names root nil frame)
    (abs-separate frame)
    (equal
     (mv-nth
      1
      (collapse
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
                            frame))))
     t)
    (fat32-filename-list-p pathname)
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
             pathname))
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
                    ((:rewrite abs-find-file-correctness-1-lemma-85)
                     (:rewrite abs-find-file-of-put-assoc-lemma-7)
                     (:rewrite abs-find-file-correctness-1-lemma-77)
                     (:rewrite abs-find-file-of-put-assoc-2)
                     (:rewrite len-of-remove-assoc-equal-2)
                     (:rewrite remove-assoc-equal-of-put-assoc-equal)
                     (:rewrite abs-find-file-helper-of-context-apply)))
    :use ((:instance (:rewrite abs-find-file-of-put-assoc-lemma-7)
                     (frame (remove-assoc-equal (1st-complete frame)
                                                frame))
                     (x (1st-complete-src frame)))
          (:instance (:rewrite abs-find-file-correctness-1-lemma-85)
                     (x (1st-complete frame)))))))

(defthm
  abs-find-file-correctness-1-lemma-88
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
    (not
     (equal
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
      (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                        frame)))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-file-alist-p root)
    (distinguish-names root nil frame)
    (abs-separate frame)
    (equal
     (mv-nth
      1
      (collapse
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
                            frame))))
     t)
    (fat32-filename-list-p pathname)
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
                     abs-find-file-correctness-1-lemma-85
                     (:definition remove-assoc-equal)
                     (:rewrite remove-assoc-equal-of-put-assoc-equal)
                     (:rewrite len-of-remove-assoc-equal-2)
                     (:rewrite abs-file-alist-p-of-context-apply-lemma-1)
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
     (:instance (:rewrite abs-find-file-correctness-1-lemma-85)
                (x (1st-complete-src frame)))))))

(defthm
  abs-find-file-correctness-1-lemma-89
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
    (not
     (equal
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
      (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                        frame)))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-file-alist-p root)
    (distinguish-names root nil frame)
    (abs-separate frame)
    (equal
     (mv-nth
      1
      (collapse
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
                            frame))))
     t)
    (fat32-filename-list-p pathname))
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
    :in-theory (disable (:rewrite abs-find-file-of-put-assoc-lemma-6)
                        (:rewrite abs-find-file-of-put-assoc-1))
    :use
    ((:instance (:rewrite abs-find-file-of-put-assoc-lemma-6)
                (x (1st-complete-src frame)))
     (:instance (:rewrite abs-find-file-of-put-assoc-lemma-6)
                (x (1st-complete frame))
                (frame (remove-assoc-equal (1st-complete-src frame)
                                           frame)))
     (:instance
      (:rewrite abs-find-file-of-put-assoc-1)
      (pathname pathname)
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
      (name (1st-complete-src frame)))))))

(encapsulate
  ()

  (local
   (in-theory
    (disable
     (:definition remove-assoc-equal)
     (:rewrite remove-assoc-equal-of-put-assoc-equal)
     (:rewrite len-of-remove-assoc-equal-2)
     (:rewrite abs-file-alist-p-of-context-apply-lemma-1)
     (:rewrite abs-file-alist-p-when-m1-file-alist-p)
     (:rewrite m1-file-alist-p-of-cdr-when-m1-file-alist-p)
     (:rewrite abs-find-file-correctness-1-lemma-77)
     (:rewrite abs-find-file-correctness-1-lemma-76)
     (:rewrite abs-find-file-correctness-1-lemma-20))))

  (defthm
    abs-find-file-correctness-1-lemma-91
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
      (not
       (equal (context-apply
               (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                                 frame)))
               (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                                 frame)))
               (1st-complete frame)
               nil)
              (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                                frame)))))
      (frame-p frame)
      (no-duplicatesp-equal (strip-cars frame))
      (abs-separate frame)
      (m1-regular-file-p (mv-nth 0 (abs-find-file frame pathname)))
      (fat32-filename-list-p pathname)
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
                      (abs-find-file-correctness-1-lemma-34
                       (:rewrite abs-find-file-helper-of-context-apply)))
      :use
      ((:instance abs-find-file-correctness-1-lemma-34
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
                                           frame)))))))))

  (defthm
    abs-find-file-correctness-1-lemma-92
    (implies
     (and
      (< 0 (1st-complete frame))
      (not (equal (1st-complete-src frame)
                  (1st-complete frame)))
      (consp (assoc-equal (1st-complete-src frame)
                          frame))
      (prefixp
       (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                          frame)))
       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                          frame))))
      (not
       (equal
        (context-apply
         (frame-val->dir
          (cdr (assoc-equal (1st-complete-src frame)
                            frame)))
         (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                           frame)))
         (1st-complete frame)
         (nthcdr
          (len (frame-val->path
                (cdr (assoc-equal (1st-complete-src frame)
                                  frame))))
          (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                             frame)))))
        (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                          frame)))))
      (frame-p frame)
      (no-duplicatesp-equal (strip-cars frame))
      (abs-separate frame)
      (m1-regular-file-p
       (mv-nth 0 (abs-find-file frame pathname)))
      (fat32-filename-list-p pathname)
      (equal
       (mv-nth 1
               (abs-find-file
                (remove-assoc-equal
                 (1st-complete-src frame)
                 (remove-assoc-equal (1st-complete frame)
                                     frame))
                pathname))
       2))
     (m1-regular-file-p
      (mv-nth
       0
       (if
        (prefixp
         (frame-val->path
          (frame-val
           (frame-val->path
            (cdr (assoc-equal (1st-complete-src frame)
                              frame)))
           (context-apply
            (frame-val->dir
             (cdr (assoc-equal (1st-complete-src frame)
                               frame)))
            (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                              frame)))
            (1st-complete frame)
            (nthcdr
             (len (frame-val->path
                   (cdr (assoc-equal (1st-complete-src frame)
                                     frame))))
             (frame-val->path
              (cdr (assoc-equal (1st-complete frame)
                                frame)))))
           (frame-val->src
            (cdr (assoc-equal (1st-complete-src frame)
                              frame)))))
         pathname)
        (abs-find-file-helper
         (frame-val->dir
          (frame-val
           (frame-val->path
            (cdr (assoc-equal (1st-complete-src frame)
                              frame)))
           (context-apply
            (frame-val->dir
             (cdr (assoc-equal (1st-complete-src frame)
                               frame)))
            (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                              frame)))
            (1st-complete frame)
            (nthcdr
             (len (frame-val->path
                   (cdr (assoc-equal (1st-complete-src frame)
                                     frame))))
             (frame-val->path
              (cdr (assoc-equal (1st-complete frame)
                                frame)))))
           (frame-val->src
            (cdr (assoc-equal (1st-complete-src frame)
                              frame)))))
         (nthcdr
          (len
           (frame-val->path
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
                                frame))))))
          pathname))
        (mv (abs-file-fix nil) *enoent*)))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory
      (e/d (abs-find-file-helper)
           (abs-find-file-helper-of-collapse-lemma-2
            (:rewrite abs-find-file-of-put-assoc-lemma-6)))
      :use
      ((:instance
        abs-find-file-helper-of-collapse-lemma-2
        (abs-file-alist1
         (frame-val->dir
          (cdr (assoc-equal (1st-complete-src frame)
                            frame))))
        (abs-file-alist2
         (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                           frame))))
        (x (1st-complete frame))
        (x-path
         (nthcdr
          (len (frame-val->path
                (cdr (assoc-equal (1st-complete-src frame)
                                  frame))))
          (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                             frame))))))
       (:instance
        abs-find-file-correctness-1-lemma-61
        (fs (frame-val->dir
             (cdr (assoc-equal (1st-complete-src frame)
                               frame))))
        (pathname
         (nthcdr
          (len (frame-val->path
                (cdr (assoc-equal (1st-complete-src frame)
                                  frame))))
          pathname))
        (x-path
         (nthcdr
          (len (frame-val->path
                (cdr (assoc-equal (1st-complete-src frame)
                                  frame))))
          (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                             frame))))))
       (:instance (:rewrite abs-find-file-of-put-assoc-lemma-6)
                  (x (1st-complete-src frame)))
       (:instance
        (:rewrite abs-find-file-of-put-assoc-lemma-6)
        (x (1st-complete frame))
        (frame (remove-assoc-equal (1st-complete-src frame)
                                   frame)))))))

  (defthm
    abs-find-file-correctness-1-lemma-93
    (implies
     (and
      (consp frame)
      (< 0 (1st-complete frame))
      (< 0 (1st-complete-src frame))
      (not (equal (1st-complete-src frame)
                  (1st-complete frame)))
      (consp (assoc-equal (1st-complete-src frame)
                          frame))
      (prefixp
       (frame-val->path
        (cdr (assoc-equal (1st-complete-src frame)
                          frame)))
       (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                          frame))))
      (not
       (equal
        (context-apply
         (frame-val->dir
          (cdr (assoc-equal (1st-complete-src frame)
                            frame)))
         (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                           frame)))
         (1st-complete frame)
         (nthcdr
          (len (frame-val->path
                (cdr (assoc-equal (1st-complete-src frame)
                                  frame))))
          (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                             frame)))))
        (frame-val->dir
         (cdr (assoc-equal (1st-complete-src frame)
                           frame)))))
      (frame-p frame)
      (no-duplicatesp-equal (strip-cars frame))
      (abs-file-alist-p root)
      (distinguish-names root nil frame)
      (abs-separate frame)
      (equal
       (mv-nth
        1
        (collapse
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
             (len (frame-val->path
                   (cdr (assoc-equal (1st-complete-src frame)
                                     frame))))
             (frame-val->path
              (cdr (assoc-equal (1st-complete frame)
                                frame)))))
           (frame-val->src
            (cdr (assoc-equal (1st-complete-src frame)
                              frame))))
          (remove-assoc-equal (1st-complete frame)
                              frame))))
       t)
      (m1-regular-file-p
       (mv-nth 0 (abs-find-file frame pathname)))
      (fat32-filename-list-p pathname)
      (not
       (equal
        (mv-nth
         1
         (abs-find-file
          (remove-assoc-equal
           (1st-complete frame)
           (remove-assoc-equal (1st-complete-src frame)
                               frame))
          pathname))
        2)))
     (m1-regular-file-p
      (mv-nth
       0
       (abs-find-file
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
           (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                             frame)))
           (1st-complete frame)
           (nthcdr
            (len (frame-val->path
                  (cdr (assoc-equal (1st-complete-src frame)
                                    frame))))
            (frame-val->path
             (cdr (assoc-equal (1st-complete frame)
                               frame)))))
          (frame-val->src
           (cdr (assoc-equal (1st-complete-src frame)
                             frame))))
         (remove-assoc-equal (1st-complete frame)
                             frame))
        pathname))))
    :hints
    (("goal"
      :do-not-induct t
      :in-theory (e/d (collapse)
                      ((:rewrite abs-find-file-of-put-assoc-2)))
      :use
      (:instance
       (:rewrite abs-find-file-of-put-assoc-2)
       (frame (remove-assoc-equal (1st-complete frame)
                                  frame))
       (val
        (frame-val
         (frame-val->path
          (cdr (assoc-equal (1st-complete-src frame)
                            frame)))
         (context-apply
          (frame-val->dir
           (cdr (assoc-equal (1st-complete-src frame)
                             frame)))
          (frame-val->dir (cdr (assoc-equal (1st-complete frame)
                                            frame)))
          (1st-complete frame)
          (nthcdr
           (len (frame-val->path
                 (cdr (assoc-equal (1st-complete-src frame)
                                   frame))))
           (frame-val->path
            (cdr (assoc-equal (1st-complete frame)
                              frame)))))
         (frame-val->src
          (cdr (assoc-equal (1st-complete-src frame)
                            frame)))))
       (name (1st-complete-src frame))))))

  (defthm
    abs-find-file-correctness-1-lemma-94
    (implies
     (and
      (consp frame)
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
      (not
       (equal
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
        (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                          frame)))))
      (frame-p frame)
      (no-duplicatesp-equal (strip-cars frame))
      (abs-file-alist-p root)
      (distinguish-names root nil frame)
      (abs-separate frame)
      (equal
       (mv-nth
        1
        (collapse
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
                              frame))))
       t)
      (m1-regular-file-p (mv-nth 0 (abs-find-file frame pathname)))
      (fat32-filename-list-p pathname))
     (m1-regular-file-p
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
        pathname))))
    :hints
    (("goal"
      :cases
      ((equal
        (mv-nth
         1
         (abs-find-file
          (remove-assoc-equal (1st-complete-src frame)
                              (remove-assoc-equal (1st-complete frame)
                                                  frame))
          pathname))
        2)))
     ("subgoal 1"
      :in-theory (disable (:rewrite abs-find-file-of-put-assoc-1)
                          abs-find-file-correctness-1-lemma-92)
      :use
      ((:instance
        (:rewrite abs-find-file-of-put-assoc-1)
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
       abs-find-file-correctness-1-lemma-92)))))

(defthm
  abs-find-file-correctness-1-lemma-95
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
    (not
     (equal
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
      (frame-val->dir (cdr (assoc-equal (1st-complete-src frame)
                                        frame)))))
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-file-alist-p root)
    (distinguish-names root nil frame)
    (abs-separate frame)
    (equal
     (mv-nth
      1
      (collapse
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
                            frame))))
     t)
    (m1-regular-file-p (mv-nth 0 (abs-find-file frame pathname)))
    (fat32-filename-list-p pathname))
   (equal
    (mv-nth 0 (abs-find-file frame pathname))
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
      pathname))))
  :instructions
  (:promote
   (:dive 2 2)
   (:casesplit
    (and
     (frame-p
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
                           frame)))
     (no-duplicatesp-equal
      (strip-cars
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
     (equal
      (mv-nth
       1
       (abs-find-file
        (remove-assoc-equal (1st-complete-src frame)
                            (remove-assoc-equal (1st-complete frame)
                                                frame))
        pathname))
      2)))
   (:rewrite abs-find-file-of-put-assoc-1)
   (:change-goal nil t)
   :top :bash (:dive 2 2)
   (:claim
    (and
     (frame-p
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
                           frame)))
     (no-duplicatesp-equal
      (strip-cars
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
     (not
      (equal
       (mv-nth
        1
        (abs-find-file
         (remove-assoc-equal (1st-complete-src frame)
                             (remove-assoc-equal (1st-complete frame)
                                                 frame))
         pathname))
       2))
     (or
      (not
       (prefixp
        (frame-val->path
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
        pathname))
      (equal
       (mv-nth
        1
        (abs-find-file-helper
         (frame-val->dir
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
         (nthcdr
          (len
           (frame-val->path
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
               (len
                (frame-val->path (cdr (assoc-equal (1st-complete-src frame)
                                                   frame))))
               (frame-val->path (cdr (assoc-equal (1st-complete frame)
                                                  frame)))))
             (frame-val->src (cdr (assoc-equal (1st-complete-src frame)
                                               frame))))))
          pathname)))
       2)))
    :hints :none)
   (:rewrite abs-find-file-of-put-assoc-2)
   :top :bash
   (:bash
    ("goal"
     :do-not-induct t
     :in-theory (disable (:rewrite abs-find-file-correctness-1-lemma-85)
                         (:rewrite abs-find-file-of-put-assoc-lemma-7))
     :use ((:instance (:rewrite abs-find-file-of-put-assoc-lemma-7)
                      (frame (remove-assoc-equal (1st-complete frame)
                                                 frame))
                      (x (1st-complete-src frame)))
           (:instance (:rewrite abs-find-file-correctness-1-lemma-85)
                      (x (1st-complete frame))))))
   (:bash
    ("goal"
     :in-theory (e/d (collapse)
                     ((:rewrite abs-find-file-correctness-1-lemma-85)
                      (:rewrite abs-find-file-of-put-assoc-lemma-7)))
     :use ((:instance (:rewrite abs-find-file-correctness-1-lemma-85)
                      (x (1st-complete-src frame)))
           (:instance (:rewrite abs-find-file-of-put-assoc-lemma-7)
                      (frame (remove-assoc-equal (1st-complete-src frame)
                                                 frame))
                      (x (1st-complete frame))))))
   :top
   (:bash
    ("goal"
     :in-theory (disable (:rewrite abs-find-file-of-put-assoc-lemma-7))
     :use (:instance (:rewrite abs-find-file-of-put-assoc-lemma-7)
                     (frame (remove-assoc-equal (1st-complete-src frame)
                                                frame))
                     (x (1st-complete frame)))))
   (:bash
    ("goal"
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
       abs-find-file-correctness-1-lemma-61
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
                                            frame))))))
   (:dive 1 2)
   (:rewrite abs-find-file-of-put-assoc-lemma-6
             ((x (1st-complete frame))))
   :top :bash
   (:bash
    ("goal" :in-theory (e/d (collapse)
                            ((:rewrite abs-find-file-correctness-1-lemma-85)))
     :use (:instance (:rewrite abs-find-file-correctness-1-lemma-85)
                     (x (1st-complete frame)))))
   (:bash
    ("goal"
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
       abs-find-file-correctness-1-lemma-61
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
                                            frame))))))))

(defthm
  abs-find-file-correctness-1-lemma-42
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
                             frame))))
      pathname))))
  :hints (("goal" :in-theory (enable 1st-complete-src))))

(defthm
  abs-find-file-correctness-1
  (implies
   (and
    (frame-p frame)
    (no-duplicatesp-equal (strip-cars frame))
    (abs-file-alist-p root)
    (no-duplicatesp-equal (abs-addrs root))
    (subsetp (abs-addrs root)
             (frame-addrs-root frame))
    (abs-separate (frame-with-root root frame))
    (equal (mv-nth 1 (collapse root frame))
           t)
    (zp (mv-nth 1
                (abs-find-file (frame-with-root root frame)
                               pathname)))
    (m1-regular-file-p
     (mv-nth 0
             (abs-find-file (frame-with-root root frame)
                            pathname)))
    (fat32-filename-list-p pathname))
   (and
    (equal (mv-nth 1
                   (abs-find-file (frame-with-root root frame)
                                  pathname))
           0)
    (equal
     (mv-nth 0
             (abs-find-file (frame-with-root root frame)
                            pathname))
     (mv-nth 0
             (hifat-find-file (mv-nth 0 (collapse root frame))
                              pathname)))))
  :hints
  (("goal"
    :in-theory
    (e/d (abs-find-file collapse frame-with-root
                        abs-separate intersectp-equal)
         ((:rewrite abs-find-file-correctness-1-lemma-17
                    . 2)
          (:rewrite nthcdr-when->=-n-len-l)
          (:rewrite len-when-prefixp)
          (:definition remove-assoc-equal)
          (:rewrite remove-assoc-of-remove-assoc)
          (:rewrite len-of-remove-assoc-equal-2)
          (:rewrite abs-file-alist-p-of-context-apply-lemma-1)
          (:rewrite abs-file-alist-p-when-m1-file-alist-p)
          (:rewrite abs-find-file-correctness-1-lemma-41)
          (:rewrite remove-assoc-equal-of-put-assoc-equal)
          (:rewrite abs-file-alist-p-correctness-1-lemma-3)))
    :induct (collapse root frame))))
