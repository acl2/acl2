(in-package "ACL2")

;; Some lemmas below are taken from other books with credit; in most cases they
;; replaced a theorem developed for this project which either had the same name
;; (causing a name conflict), or which rewrote the same target (causing :use
;; hints to become :useless even if the project-specific lemma was disabled for
;; the goal in question.)

(defthm make-character-list-makes-character-list
  (character-listp (make-character-list x)))

;; The following are redundant with the definition in
;; books/std/lists/append.lisp, from where they were taken with thanks.
(defthm len-of-append
  (equal (len (append x y))
         (+ (len x) (len y))))
(defthm consp-of-append
  (equal (consp (append x y))
         (or (consp x) (consp y))))

(defthm len-of-make-character-list
  (equal (len (make-character-list x)) (len x)))

(defthm len-of-revappend
  (equal (len (revappend x y)) (+ (len x) (len y))))

(defthm len-of-take (equal (len (take n xs)) (nfix n)))

;; The following is redundant with the definition in
;; books/coi/lists/basic.lisp, from where it was taken with thanks.
(defthm nthcdr-of-append
  (equal (nthcdr n (append a b))
         (if (<= (nfix n) (len a))
             (append (nthcdr n a) b)
           (nthcdr (- n (len a)) b)))
  :hints(("Goal" :in-theory (enable nthcdr))))

(defthm take-of-binary-append-1
  (implies (and (natp i) (<= i (len x)))
           (equal (take i (binary-append x y))
                  (take i x))))

(defthm
  by-slice-you-mean-the-whole-cake-1
  (equal (first-n-ac (len l) l ac)
         (revappend ac (true-list-fix l)))
  :hints (("goal" :induct (revappend l ac)))
  :rule-classes
  ((:rewrite
    :corollary
    (implies (equal i (len l))
             (equal (first-n-ac i l ac)
                    (revappend ac (true-list-fix l)))))))

;; The following is redundant with the definition in
;; books/std/lists/take.lisp, from where it was taken with thanks.
(defthm take-of-len-free
  (implies (equal len (len x)) (equal (take len x) (true-list-fix x))))

(defthm assoc-after-remove1-assoc
  (implies (not (equal name1 name2))
           (equal (assoc-equal name1 (remove1-assoc name2 alist))
                  (assoc-equal name1 alist))))

(defthm assoc-after-remove-assoc
  (equal (assoc-equal name1 (remove-assoc name2 alist))
         (if (not (equal name1 name2))
             (assoc-equal name1 alist)
           nil)))

(defthm character-listp-of-revappend
  (equal (character-listp (revappend x y))
         (and (character-listp (true-list-fix x))
              (character-listp y))))

(defthm character-listp-of-take
  (implies (character-listp l)
           (equal (character-listp (take n l))
                  (<= (nfix n) (len l)))))

(defthm character-listp-of-nthcdr
  (implies (and (character-listp l))
           (character-listp (nthcdr n l))))

;; The following is redundant with the definition in
;; books/std/strings/make-character-list.lisp, from where it was taken with
;; thanks.
(defthm str::make-character-list-when-character-listp
  (implies (character-listp x)
           (equal (make-character-list x) x)))

(defthm make-character-list-of-binary-append
  (equal (make-character-list (binary-append x y))
         (binary-append (make-character-list x) (make-character-list y))))

;; The following is redundant with the definition in
;; books/std/lists/nthcdr.lisp, from where it was taken with thanks.
(defthm len-of-nthcdr
  (equal (len (nthcdr n l))
         (nfix (- (len l) (nfix n))))
  :hints (("Goal" :induct (nthcdr n l))))

;; The following is redundant with the definition in
;; books/std/lists/nthcdr.lisp, from where it was taken with thanks.
(defthm consp-of-nthcdr
  (equal (consp (nthcdr n x))
         (< (nfix n) (len x)))
  :hints (("Goal" :in-theory (disable len-of-nthcdr)
           :use ((:instance len-of-nthcdr (l x)))
           :expand (len (nthcdr n x)))))

(defthm revappend-of-binary-append-1
  (equal (binary-append (revappend x y) z)
         (revappend x (binary-append y z))))

(defthm
  binary-append-first-n-ac-nthcdr
  (implies (<= i (len l))
           (equal (binary-append (first-n-ac i l ac)
                                 (nthcdr i l))
                  (revappend ac l)))
  :hints (("goal" :induct (first-n-ac i l ac))))

;; The following is redundant with the definition in books/std/lists/nth.lisp,
;; from where it was taken with thanks.
(defthm nth-of-append
  (equal (nth n (append x y))
         (if (< (nfix n) (len x))
             (nth n x)
           (nth (- n (len x)) y))))

;; The following is redundant with the definition in
;; books/std/lists/append.lisp, from where it was taken with thanks.
(defthm associativity-of-append
  (equal (append (append a b) c)
         (append a (append b c))))

(defthm member-of-a-nat-list
  (implies (and (member-equal x lst)
                (nat-listp lst))
           (natp x))
  :rule-classes :forward-chaining)

(defthm update-nth-of-boolean-list
  (implies (boolean-listp l)
           (equal (boolean-listp (update-nth key val l))
                  (booleanp val))))

(defthm nat-listp-of-binary-append
  (equal (nat-listp (binary-append x y))
         (and (nat-listp (true-list-fix x)) (nat-listp y))))

(defthm eqlable-listp-if-nat-listp (implies (nat-listp l) (eqlable-listp l)))

(defthm member-of-binary-append
  (iff (member-equal x (binary-append lst1 lst2))
       (or (member-equal x lst1)
           (member-equal x lst2))))

(defthm no-duplicatesp-of-append
  (equal (no-duplicatesp-equal (binary-append x y))
         (and (no-duplicatesp x)
              (no-duplicatesp y)
              (not (intersectp-equal x y)))))

(defthm intersectp-of-append-1
  (equal (intersectp-equal z (binary-append x y))
         (or (intersectp-equal z x)
             (intersectp-equal z y))))

(defthm intersectp-of-append-2
  (equal (intersectp-equal (binary-append x y) z)
         (or (intersectp-equal x z)
             (intersectp-equal y z))))

(defthm intersectp-is-commutative
  (equal (intersectp-equal x y)
         (intersectp-equal y x)))

;; The following five theorems are redundant with the eponymous theorems in
;; books/std/lists/sets.lisp, from where they were taken with thanks.
(defthm subsetp-append1
  (equal (subsetp (append a b) c)
         (and (subsetp a c)
              (subsetp b c))))
(defthm subsetp-append2
  (subsetp a (append a b)))
(defthm subsetp-append3
  (subsetp b (append a b)))
(defthm subsetp-trans
  (implies (and (subsetp x y) (subsetp y z))
           (subsetp x z)))
(defthm
  subsetp-member
  (implies (and (member a x) (subsetp x y))
           (member a y))
  :rule-classes
  ((:rewrite)
   (:rewrite :corollary (implies (and (subsetp x y) (member a x))
                                 (member a y)))
   (:rewrite
    :corollary (implies (and (not (member a y)) (subsetp x y))
                        (not (member a x))))
   (:rewrite
    :corollary (implies (and (subsetp x y) (not (member a y)))
                        (not (member a x))))))
(defthm subsetp-trans2
  (implies (and (subsetp y z)
                (subsetp x y))
           (subsetp x z))
  :hints(("Goal" :in-theory (enable subsetp-member))))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/nth.lisp, from where it was taken with thanks.
(defthm nth-of-revappend
  (equal (nth n (revappend x y))
         (if (< (nfix n) (len x))
             (nth (- (len x) (+ 1 (nfix n))) x)
           (nth (- n (len x)) y))))

;; The following is redundant with the eponymous theorem in
;; books/misc/gentle.lisp, from where it was taken with thanks to
;; Messrs. Boyer, Hunt and Davis.
(defthm true-listp-of-make-list-ac
  (equal (true-listp (make-list-ac n val ac))
         (true-listp ac))
  :rule-classes ((:rewrite)
                 (:type-prescription
                  :corollary
                  (implies (true-listp ac)
                           (true-listp (make-list-ac n val ac))))))

;; The following is redundant with the eponymous theorem in
;; books/centaur/ubdds/param.lisp, from where it was taken with thanks to
;; Messrs. Boyer and Hunt.
(defthm len-of-make-list-ac
  (equal (len (make-list-ac n val acc))
         (+ (nfix n) (len acc))))

(defthm consp-of-make-list-ac
  (iff (consp (make-list-ac n val ac))
       (or (not (zp n)) (consp ac))))

(defthm boolean-listp-of-make-list-ac
  (implies (booleanp val)
           (equal (boolean-listp (make-list-ac n val ac))
                  (boolean-listp ac))))

(defthm booleanp-of-car-make-list
  (implies (and (booleanp val)
                (boolean-listp ac)
                (> (+ n (len ac)) 0))
           (booleanp (car (make-list-ac n val ac)))))

(defthm car-of-make-list
  (equal (car (make-list-ac n val ac))
         (if (zp n) (car ac) val)))

(defthm cdr-of-make-list
  (equal (cdr (make-list-ac n val ac))
         (if (zp n)
             (cdr ac)
           (make-list-ac (- n 1) val ac))))

;; The following is redundant with the eponymous theorem in
;; books/data-structures/list-defthms.lisp, from where it was taken with thanks.
(defthm member-equal-nth
  (implies (< (nfix n) (len l))
           (member-equal (nth n l) l))
  :hints (("Goal" :in-theory (enable nth))))

(defthm make-character-list-of-revappend
  (equal (make-character-list (revappend x y))
         (revappend (make-character-list x)
                    (make-character-list y))))

(defthm
  take-of-make-character-list
  (implies (<= i (len l))
           (equal (take i (make-character-list l))
                  (make-character-list (take i l)))))

(defthm revappend-of-true-list-fix
  (equal (revappend x (true-list-fix y))
         (true-list-fix (revappend x y))))

(defthm append-of-true-list-fix
  (equal (append (true-list-fix x) y)
         (append x y)))

(defthm boolean-listp-of-revappend
  (equal (boolean-listp (revappend x y))
         (and (boolean-listp (true-list-fix x))
              (boolean-listp y))))

(defthm boolean-listp-of-first-n-ac
  (implies (boolean-listp l)
           (equal (boolean-listp (first-n-ac i l ac))
                  (boolean-listp (true-list-fix ac)))))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/take.lisp, from where it was taken with thanks.
(defthm consp-of-take
    (equal (consp (take n xs))
           (not (zp n))))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/nth.lisp, from where it was taken with thanks.
(defthm nth-of-make-list-ac
  (equal (nth n (make-list-ac m val acc))
         (if (< (nfix n) (nfix m))
             val
           (nth (- n (nfix m)) acc))))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/nth.lisp, from where it was taken with thanks.
(defthm nth-of-nthcdr
  (equal (nth n (nthcdr m x))
         (nth (+ (nfix n) (nfix m)) x)))

(defthm intersect-with-subset
  (implies (and (subsetp-equal x y)
                (intersectp-equal x z))
           (intersectp-equal y z))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (and (intersectp-equal x z)
                  (subsetp-equal x y))
             (intersectp-equal y z)))
   (:rewrite
    :corollary
    (implies (and (intersectp-equal z x)
                  (subsetp-equal x y))
             (intersectp-equal y z)))
   (:rewrite
    :corollary
    (implies (and (subsetp-equal x y)
                  (intersectp-equal z x))
             (intersectp-equal z y)))
   (:rewrite
    :corollary
    (implies (and (intersectp-equal z x)
                  (subsetp-equal x y))
             (intersectp-equal z y)))
   (:rewrite
    :corollary
    (implies (and (intersectp-equal x z)
                  (subsetp-equal x y))
             (intersectp-equal z y)))
   (:rewrite
    :corollary
    (implies (and (subsetp-equal x y)
                  (not
                   (intersectp-equal y z)))
             (not
              (intersectp-equal x z))))
   (:rewrite
    :corollary
    (implies (and (not
                   (intersectp-equal y z))
                  (subsetp-equal x y))
             (not
              (intersectp-equal x z))))
   (:rewrite
    :corollary
    (implies (and (not
                   (intersectp-equal z y))
                  (subsetp-equal x y))
             (not
              (intersectp-equal x z))))
   (:rewrite
    :corollary
    (implies (and (subsetp-equal x y)
                  (not
                   (intersectp-equal y z)))
             (not
              (intersectp-equal z x))))
   (:rewrite
    :corollary
    (implies (and (not
                   (intersectp-equal y z))
                  (subsetp-equal x y))
             (not
              (intersectp-equal z x))))
   (:rewrite
    :corollary
    (implies (and (not
                   (intersectp-equal z y))
                  (subsetp-equal x y))
             (not
              (intersectp-equal z x))))
   (:rewrite
    :corollary
    (implies (and (intersectp-equal x z)
                  (not
                   (intersectp-equal z y)))
             (not
              (subsetp-equal x y))))
   (:rewrite
    :corollary
    (implies (and (intersectp-equal z x)
                  (not
                   (intersectp-equal z y)))
             (not
              (subsetp-equal x y))))
   (:rewrite
    :corollary
    (implies (and (not
                   (intersectp-equal z y))
                  (intersectp-equal x z))
             (not
              (subsetp-equal x y))))
   (:rewrite
    :corollary
    (implies (and (not
                   (intersectp-equal y z))
                  (intersectp-equal x z))
             (not
              (subsetp-equal x y))))))

(defthm update-nth-of-make-list
  (implies (and (integerp key) (>= key n) (natp n))
           (equal (update-nth key val (make-list-ac n l ac))
                  (make-list-ac n l (update-nth (- key n) val ac)))))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/update-nth.lisp, from where it was taken with thanks.
(defthm nthcdr-of-update-nth
  (equal (nthcdr n1 (update-nth n2 val x))
         (if (< (nfix n2) (nfix n1))
             (nthcdr n1 x)
           (update-nth (- (nfix n2) (nfix n1)) val (nthcdr n1 x)))))

(defthm update-nth-of-update-nth-1
  (implies (not (equal (nfix key1) (nfix key2)))
           (equal (update-nth key1 val1 (update-nth key2 val2 l))
                  (update-nth key2 val2 (update-nth key1 val1 l)))))

(defthm update-nth-of-update-nth-2
  (equal (update-nth key val2 (update-nth key val1 l))
         (update-nth key val2 l)))

;; This can probably be replaced by a functional instantiation.
(defthm nat-listp-of-remove
  (implies (nat-listp l)
           (nat-listp (remove-equal x l))))

;; This should be moved into the community books.
(defthm subsetp-of-remove
  (subsetp-equal (remove-equal x l) l))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/sets.lisp, from where it was taken with thanks.
(defthm member-of-remove
  (iff (member a (remove b x))
       (and (member a x)
            (not (equal a b))))
  :hints(("goal" :induct (len x))))

(defthm
  assoc-after-put-assoc
  (equal (assoc-equal name1 (put-assoc-equal name2 val alist))
         (if (equal name1 name2)
             (cons name1 val)
           (assoc-equal name1 alist))))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/nthcdr.lisp, from where it was taken with thanks.
(defthm nthcdr-of-cdr
  (equal (nthcdr i (cdr x))
         (cdr (nthcdr i x))))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/update-nth.lisp, from where it was taken with thanks.
(defthm update-nth-of-nth
  (implies (< (nfix n) (len x))
           (equal (update-nth n (nth n x) x) x)))

(defthm character-listp-of-make-list-ac
  (equal (character-listp (make-list-ac n val ac))
         (and (character-listp ac)
              (or (zp n) (characterp val)))))

(defthm string-listp-of-append
  (equal (string-listp (append x y))
         (and (string-listp (true-list-fix x))
              (string-listp y))))

(defthm true-listp-when-string-list
  (implies (string-listp x)
           (true-listp x)))

(defthm
  binary-append-take-nthcdr
  (implies (<= i (len l))
           (equal (binary-append (take i l)
                                 (nthcdr i l))
                  l)))

(defthm true-list-fix-when-true-listp
  (implies (true-listp x)
           (equal (true-list-fix x) x)))

(defthm true-list-fix-of-coerce
  (equal (true-list-fix (coerce text 'list))
         (coerce text 'list)))

(defthm len-of-true-list-fix
  (equal (len (true-list-fix x)) (len x)))

(defthm nth-of-make-character-list
  (equal (nth n (make-character-list x))
         (cond ((>= (nfix n) (len x)) nil)
               ((characterp (nth n x)) (nth n x))
               (t (code-char 0)))))

(defthm nth-of-first-n-ac
  (equal (nth n (first-n-ac i l ac))
         (cond ((>= (nfix n) (+ (len ac) (nfix i)))
                nil)
               ((< (nfix n) (len ac))
                (nth (- (len ac) (+ (nfix n) 1)) ac))
               (t (nth (- (nfix n) (len ac)) l)))))

;; Contributed to books/std/lists/nth.lisp
(defthm nth-of-take
  (equal (nth i (take n l))
         (if (< (nfix i) (nfix n))
             (nth i l)
           nil)))

(defthm nthcdr-of-nil (equal (nthcdr n nil) nil))

(defthm nthcdr-when->=-n-len-l
  (implies (and (true-listp l)
                (>= (nfix n) (len l)))
           (equal (nthcdr n l) nil)))

(defthm revappend-of-revappend
  (equal (revappend (revappend x y1) y2)
         (revappend y1 (append x y2)))
  :hints
  (("goal" :in-theory (disable revappend-of-binary-append-1))))

(defthm
  character-listp-of-member
  (implies (character-listp lst)
           (character-listp (member-equal x lst)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (and (character-listp lst)
                  (consp (member-equal x lst)))
             (character-listp (cdr (member-equal x lst)))))))

(defthm true-listp-of-member
  (implies (true-listp lst)
           (true-listp (member-equal x lst)))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary
    (implies (and (true-listp lst)
                  (consp (member-equal x lst)))
             (true-listp (cdr (member-equal x lst)))))))

(defthm len-of-member
  (<= (len (member-equal x lst))
      (len lst))
  :rule-classes :linear)

(defthm len-of-remove1-assoc
  (implies (consp (assoc-equal key alist))
           (equal (len (remove1-assoc-equal key alist))
                  (- (len alist) 1))))

;; Contributed to books/std/lists/remove1-equal.lisp
(defthm len-of-remove1-equal
  (equal (len (remove1-equal x l))
         (if (member-equal x l)
             (- (len l) 1)
           (len l))))

(defthm
  assoc-of-remove1-assoc
  (implies
   (and (case-split (not (null key1)))
        (not (consp (assoc-equal key1 alist))))
   (not (consp (assoc-equal key1
                            (remove1-assoc-equal key2 alist))))))

;; Contributed to books/std/lists/remove1-equal.lisp
(defthm
  assoc-equal-of-remove1-equal
  (implies
   (and (not (equal key1 nil))
        (not (consp (assoc-equal key1 alist))))
   (not (consp (assoc-equal key1 (remove1-equal x alist)))))
  :rule-classes (:rewrite :type-prescription))

(defthm assoc-of-car-when-member
  (implies (and (member-equal x lst)
                (or (not (equal (car x) nil)) (alistp lst)))
           (consp (assoc-equal (car x) lst))))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/nthcdr.lisp, from where it was taken with thanks.
(defthm car-of-nthcdr
  (equal (car (nthcdr i x))
         (nth i x)))

(defthm stringp-of-nth
  (implies (string-listp l)
           (iff (stringp (nth n l))
                (< (nfix n) (len l)))))

(defthm string-listp-of-update-nth
  (implies (string-listp l)
           (equal (string-listp (update-nth key val l))
                  (and (<= (nfix key) (len l))
                       (stringp val)))))

(defthm revappend-of-binary-append-2
  (equal (revappend (binary-append x y1) y2)
         (revappend y1 (revappend x y2))))

(defthm add-pair-of-add-pair-1
  (equal (add-pair key value2 (add-pair key value1 l))
         (add-pair key value2 l)))

(defthm princ$-of-princ$
  (implies (and (stringp x) (stringp y))
           (equal (princ$ y channel (princ$ x channel state))
                  (princ$ (string-append x y) channel state))))

(defthmd
  painful-debugging-lemma-1
  (implies (and (integerp x) (integerp y))
           (integerp (+ x y))))

(defthmd
  painful-debugging-lemma-2
  (implies (and (integerp x) (integerp y))
           (integerp (* x y))))

(defthmd painful-debugging-lemma-3
  (implies (integerp x)
           (integerp (unary-- x))))

(defthmd painful-debugging-lemma-4
  (equal (<= x (+ x y)) (>= y 0))
  :rule-classes
  ((:rewrite :corollary (equal (< (+ x y) x) (< y 0)))))

(defthmd painful-debugging-lemma-5
  (implies (and (>= x 0) (>= y 0))
           (not (< (+ x y) 0))))

(defthm
  painful-debugging-lemma-6
  (equal (- (- x)) (fix x)))

(defthmd
  painful-debugging-lemma-7
  (implies (not (zp x1))
           (equal (< 0 (* x1 (len x2)))
                  (consp x2))))

(defthmd
  painful-debugging-lemma-12
  (implies
   (and (integerp x) (integerp y))
   (iff (equal (+ x (- y)) 0)
        (equal x y))))

(defthmd painful-debugging-lemma-13
  (implies (and (integerp x) (integerp y) (< x y))
           (<= (+ 1 x) y)))

;; The following is redundant with the eponymous theorem in
;; books/std/typed-lists/integer-listp.lisp, from where it was taken with
;; thanks.
(defthm
  integerp-of-nth-when-integer-listp
  (implies (integer-listp x)
           (iff (integerp (nth n x))
                (< (nfix n) (len x)))))

(defthm true-list-listp-of-append
  (equal (true-list-listp (append x y))
         (and (true-list-listp (true-list-fix x)) (true-list-listp y))))

(defthmd rationalp-of-nth-when-rational-listp
  (implies (rational-listp x)
           (iff (rationalp (nth n x))
                (< (nfix n) (len x)))))

(defthm
  member-of-remove1-assoc
  (implies
   (not (member-equal x lst))
   (not (member-equal x (remove1-assoc-equal key lst)))))

(defthm acl2-count-of-true-list-fix
  (<= (acl2-count (true-list-fix x))
      (acl2-count x))
  :rule-classes :linear)

(defthmd
  update-nth-of-revappend
  (equal (update-nth key val (revappend x y))
         (if (< (nfix key) (len x))
             (revappend (update-nth (- (len x) (+ 1 (nfix key)))
                                    val x)
                        y)
           (revappend x
                      (update-nth (- (nfix key) (len x))
                                  val y)))))

(defthm
  true-listp-of-update-nth
  (equal (true-listp (update-nth key val l))
         (or (>= (nfix key) (len l))
             (true-listp l)))
  :hints (("goal" :in-theory (enable update-nth)
           :induct (update-nth key val l)
           :expand ((true-listp l)
                    (:free (x y)
                           (true-listp (cons x y)))))))

(defthm nthcdr-of-nthcdr
  (equal (nthcdr a (nthcdr b x))
         (nthcdr (+ (nfix a) (nfix b)) x))
  :hints(("goal" :induct (nthcdr b x))))

(defthm acl2-count-of-member
  (<= (acl2-count (member-equal x lst))
      (acl2-count lst))
  :rule-classes :linear)

(defthm
  string-listp-of-resize-list
  (implies (and (string-listp lst)
                (stringp default-value))
           (string-listp (resize-list lst n default-value))))

(encapsulate
  ()

  (local
   (defthm
     update-nth-of-first-n-ac
     (implies
      (< (nfix key) (+ (nfix i) (len ac)))
      (equal
       (update-nth key val (first-n-ac i l ac))
       (if (< (nfix key) (len ac))
           (first-n-ac i l
                       (update-nth (- (len ac) (+ (nfix key) 1))
                                   val ac))
         (first-n-ac i
                     (update-nth (- (nfix key) (len ac))
                                 val l)
                     ac))))
     :hints (("goal" :induct (first-n-ac i l ac)
              :in-theory (enable update-nth-of-revappend)))))

  (defthm
    first-n-ac-of-update-nth
    (equal (first-n-ac i (update-nth key val l) ac)
           (if (< (nfix key) (nfix i))
               (update-nth (+ (nfix key) (len ac))
                           val (first-n-ac i l ac))
             (first-n-ac i l ac)))
    :hints
    (("goal" :induct (mv (first-n-ac i l ac)
                         (update-nth key val l))))))

(defthm take-of-update-nth
  (equal (take n (update-nth key val l))
         (if (< (nfix key) (nfix n))
             (update-nth key val (take n l))
           (take n l))))

(encapsulate
  ()

  (local
   (defthmd lemma
     (implies (and (equal (nfix key) (- (len l) 1))
                   (true-listp l))
              (equal (revappend ac (update-nth key val l))
                     (append (first-n-ac key l ac)
                             (list val))))
     :hints (("goal" :induct (mv (first-n-ac key l ac)
                                 (update-nth key val l))
              :expand ((len l) (len (cdr l)))))))

  (defthmd
    remember-that-time-with-update-nth
    (implies (and (equal (nfix key) (- (len l) 1))
                  (true-listp l))
             (equal (update-nth key val l)
                    (append (take key l) (list val))))
    :hints
    (("goal"
      :use (:instance lemma
                      (ac nil))))))

(defthm append-of-take-and-cons
  (implies (and (natp n) (equal x (nth n l)))
           (equal (append (take n l) (cons x y))
                  (append (take (+ n 1) l) y)))
  :hints (("Goal" :induct (take n l)) ))

(defthmd take-of-nthcdr
  (equal (take n1 (nthcdr n2 l))
         (nthcdr n2 (take (+ (nfix n1) (nfix n2)) l))))

(defthm
  put-assoc-equal-without-change
  (iff (equal (put-assoc-equal name val alist)
              alist)
       (and (consp (assoc-equal name alist))
            (equal (cdr (assoc-equal name alist))
                   val)))
  :rule-classes
  ((:rewrite
    :corollary (implies (not (and (consp (assoc-equal name alist))
                                  (equal (cdr (assoc-equal name alist))
                                         val)))
                        (not (equal (put-assoc-equal name val alist)
                                    alist))))
   (:rewrite :corollary (implies (and (consp (assoc-equal name alist))
                                      (equal (cdr (assoc-equal name alist))
                                             val))
                                 (equal (put-assoc-equal name val alist)
                                        alist)))))

;; Contributed to books/std/lists/remove1-equal.lisp
(defthm member-equal-of-remove1-equal
  (implies (not (equal x1 x2))
           (iff (member-equal x1 (remove1-equal x2 l))
                (member-equal x1 l))))

;; Contributed to books/std/lists/intersection.lisp
(defthm
  member-of-intersection$
  (iff (member a (intersection$ x y))
       (and (member a x) (member a y)))
  :rule-classes
  (:rewrite
   (:type-prescription
    :corollary
    (implies (not (member a x))
             (not (member a (intersection$ x y)))))
   (:type-prescription
    :corollary
    (implies (not (member a y))
             (not (member a (intersection$ x y)))))))

(defthm
  nth-of-intersection$
  (implies (< (nfix n)
              (len (intersection-equal x y)))
           (and
            (member-equal (nth n (intersection-equal x y))
                          x)
            (member-equal (nth n (intersection-equal x y))
                          y)))
  :hints
  (("goal"
    :in-theory (disable member-of-intersection$)
    :use (:instance member-of-intersection$
                    (a (nth n (intersection-equal x y)))))))

(defthm
  member-of-strip-cars-of-remove-assoc
  (iff
   (member-equal x1
                 (strip-cars (remove-assoc-equal x2 alist)))
   (and
    (member-equal x1 (strip-cars alist))
    (not (equal x1 x2)))))

(defthm
  no-duplicatesp-of-strip-cars-of-remove-assoc
  (implies (no-duplicatesp-equal (strip-cars alist))
           (no-duplicatesp-equal
            (strip-cars (remove-assoc-equal x alist)))))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/take.lisp, from where it was taken with thanks.
(defthm take-fewer-of-take-more
  (implies (<= (nfix a) (nfix b))
           (equal (take a (take b x)) (take a x))))

(defthm len-of-remove-when-no-duplicatesp
  (implies (no-duplicatesp-equal l)
           (equal (len (remove-equal x l))
                  (if (member-equal x l)
                      (- (len l) 1)
                    (len l)))))

(defthm no-duplicatesp-of-remove
  (implies (no-duplicatesp-equal l)
           (no-duplicatesp-equal (remove-equal x l))))

(encapsulate
  ()

  ;; The following is redundant with the eponymous function in
  ;; books/std/basic/inductions.lisp, from where it was taken with thanks.
  (local
   (defun dec-dec-induct (n m)
     (if (or (zp n)
             (zp m))
         nil
       (dec-dec-induct (- n 1) (- m 1)))))

  (local
   (defthm take-of-make-list-ac-lemma-1
     (implies (not (zp n1))
              (equal (cons val (make-list-ac (+ -1 n1) val nil))
                     (make-list-ac n1 val nil)))
     :hints (("Goal" :in-theory (disable cons-car-cdr make-list-ac)
              :use ((:instance cons-car-cdr
                               (x (make-list-ac n1 val nil))))))))

  (defthm take-of-make-list-ac
    (implies (<= (nfix n1) (nfix n2))
             (equal (take n1 (make-list-ac n2 val ac))
                    (make-list-ac n1 val nil)))
    :hints (("goal" :induct (dec-dec-induct n1 n2)))))

(defthm stringp-of-append
  (equal (stringp (append x y)) (and (atom x) (stringp y))))

(defthm remove-assoc-of-put-assoc
  (equal (remove-assoc key (put-assoc name val alist))
         (if
             (equal key name)
             (remove-assoc key alist)
           (put-assoc name val (remove-assoc key alist)))))

(defthm last-of-member
  (equal (last (member-equal x lst))
         (if (member-equal x lst)
             (last lst)
           nil)))

(defthm integerp-of-car-of-last-when-integer-listp
  (implies (integer-listp l)
           (equal
            (integerp (car (last l)))
            (consp l))))

(defthm non-negativity-of-car-of-last-when-nat-listp
  (implies (nat-listp l)
           (<= 0 (car (last l))))
  :rule-classes :linear)

(defthm len-of-put-assoc-equal
  (implies (not (null name))
           (equal (len (put-assoc-equal name val alist))
                  (if (consp (assoc-equal name alist))
                      (len alist)
                      (+ 1 (len alist))))))

(defthm remove-assoc-when-absent-1
  (implies (and (not (null x))
                (atom (assoc-equal x alist)))
           (equal (remove-assoc-equal x alist)
                  (true-list-fix alist))))

(defthm remove-assoc-when-absent-2
  (implies (and (not (null x))
                (atom (assoc-equal x alist)))
           (equal (remove-assoc-equal x (remove-assoc-equal y alist))
                  (remove-assoc-equal y alist)))
  :hints (("Goal" :in-theory (disable)
           :use (:instance remove-assoc-when-absent-1
                           (alist (remove-assoc-equal y alist)))) ))

(defthm
  remove-assoc-of-remove-assoc
  (equal (remove-assoc x1 (remove-assoc x2 alist))
         (remove-assoc x2 (remove-assoc x1 alist))))

(defthm len-of-remove-assoc-1
  (<= (len (remove-assoc-equal x alist))
      (len alist))
  :rule-classes :linear)

(defthm len-of-remove-assoc-2
  (implies (consp (assoc-equal x alist))
           (< (len (remove-assoc-equal x alist))
              (len alist)))
  :rule-classes :linear)

(defthm
  member-of-strip-cars
  (implies (case-split (not (null x)))
           (iff
            (member-equal x (strip-cars alist))
            (consp (assoc-equal x alist)))))

(defthm len-of-remove-assoc-when-no-duplicatesp-strip-cars
  (implies (and (no-duplicatesp-equal (strip-cars alist))
                (not (null x)))
           (equal (len (remove-assoc-equal x alist))
                  (if (atom (assoc-equal x alist))
                      (len alist)
                    (- (len alist) 1)))))

(defthm strip-cars-of-remove-assoc
  (equal (strip-cars (remove-assoc-equal x alist))
         (remove-equal x (strip-cars alist))))

(defthm strip-cars-of-put-assoc
  (implies (case-split (not (null name)))
           (equal (strip-cars (put-assoc-equal name val alist))
                  (if (consp (assoc-equal name alist))
                      (strip-cars alist)
                      (append (strip-cars alist)
                              (list name))))))

(defthm remove-when-absent
  (implies (not (member-equal x l))
           (equal (remove-equal x l)
                  (true-list-fix l))))

(defthmd intersectp-when-member
  (implies (member-equal x l)
           (iff (intersectp-equal l y)
                (or (intersectp-equal (remove-equal x l) y)
                    (member-equal x y))))
  :hints (("goal" :in-theory (e/d (intersectp-equal)
                                  (intersectp-is-commutative)))))

(defthm consp-of-assoc-equal-of-append
  (implies (not (null name))
           (equal (consp (assoc-equal name (append x y)))
                  (or (consp (assoc-equal name x))
                      (consp (assoc-equal name y))))))

(defthm consp-of-assoc-of-remove
  (implies (and (not (null x1))
                (not (consp (assoc-equal x1 l))))
           (not (consp (assoc-equal x1 (remove-equal x2 l)))))
  :rule-classes :type-prescription)

(defthm strip-cars-of-append
  (equal (strip-cars (append x y))
         (append (strip-cars x) (strip-cars y))))

(defthm remove-of-append
  (equal (remove-equal x1 (append x2 y))
         (append (remove-equal x1 x2)
                 (remove-equal x1 y))))

(defthm
  remove-of-strip-cars-of-remove
  (implies (atom x)
           (equal (remove-equal nil (strip-cars (remove-equal x alist)))
                  (remove-equal nil (strip-cars alist)))))

(defthm assoc-of-append-1
  (implies (case-split (not (null x1)))
           (equal (assoc-equal x1 (append x2 y))
                  (if (consp (assoc-equal x1 x2))
                      (assoc-equal x1 x2)
                      (assoc-equal x1 y)))))

(defthm assoc-of-append-2
  (implies (and (atom (assoc-equal nil x))
                (atom (assoc-equal nil y)))
           (not (consp (assoc-equal nil (append x y)))))
  :rule-classes (:rewrite :type-prescription))

(encapsulate
  ()

  (local (defthm lemma-1
           (iff (equal (cons (car x) y) x)
                (and (consp x) (equal (cdr x) y)))))

  (local
   (defthm
     lemma-2
     (iff (equal alist (put-assoc-equal name val alist))
          (and (consp (assoc-equal name alist))
               (equal (cdr (assoc-equal name alist))
                      val)))
     :rule-classes
     (:rewrite
      (:rewrite
       :corollary (iff (equal (put-assoc-equal name val alist)
                              alist)
                       (and (consp (assoc-equal name alist))
                            (equal (cdr (assoc-equal name alist))
                                   val)))))))

  (defthmd put-assoc-equal-match
    (iff (equal (put-assoc-equal name1 val1 alist)
                (put-assoc-equal name2 val2 alist))
         (or (and (equal name1 name2)
                  (equal val1 val2))
             (and (consp (assoc-equal name1 alist))
                  (equal (cdr (assoc-equal name1 alist))
                         val1)
                  (consp (assoc-equal name2 alist))
                  (equal (cdr (assoc-equal name2 alist))
                         val2))))))

(defthm assoc-of-remove
  (implies (and (atom x1) (case-split (not (null x2))))
           (equal (assoc-equal x2 (remove-equal x1 l))
                  (assoc-equal x2 l))))

(defthm member-of-car-of-nth-in-strip-cars
  (implies (< (nfix n) (len l))
           (member-equal (car (nth n l))
                         (strip-cars l))))

(defthm
  assoc-of-car-of-nth
  (implies (and (no-duplicatesp-equal (strip-cars l))
                (< (nfix n) (len l)))
           (equal (assoc-equal (car (nth n l)) l)
                  (nth n l)))
  :hints
  (("goal" :induct (mv (assoc-equal (car (nth n l)) l)
                       (len l)
                       (nth n l)))
   ("subgoal *1/1"
    :in-theory (disable (:rewrite member-of-car-of-nth-in-strip-cars))
    :use (:instance (:rewrite member-of-car-of-nth-in-strip-cars)
                    (l (cdr l))
                    (n (+ -1 n))))))

(defthm consp-of-nth-when-alistp
  (implies (and (alistp l) (< (nfix n) (len l)))
           (consp (nth n l))))

(defthm member-equal-of-strip-cars-of-put-assoc
  (iff (member-equal x
                     (strip-cars (put-assoc-equal name val alist)))
       (or (equal x name)
           (member-equal x (strip-cars alist)))))

(defthm
  no-duplicatesp-of-strip-cars-of-put-assoc
  (equal (no-duplicatesp-equal (strip-cars (put-assoc-equal name val alist)))
         (no-duplicatesp-equal (strip-cars alist))))

(defthm nth-when->=-n-len-l
  (implies (>= (nfix n) (len l))
           (equal (nth n l) nil)))

(defthm strip-cars-of-remove1-assoc
  (equal (strip-cars (remove1-assoc-equal key alist))
         (remove1-equal key (strip-cars alist))))

(defthm
  intersectp-equal-of-strip-cars-of-remove-equal
  (implies
   (not (intersectp-equal x1 (remove-equal nil (strip-cars lst))))
   (not (intersectp-equal
         x1
         (remove-equal nil
                       (strip-cars (remove-equal x2 lst))))))
  :hints (("goal" :in-theory (e/d (intersectp-equal)
                                  (intersectp-is-commutative)))))

(defthm intersectp-of-remove
  (implies (not (intersectp-equal l1 l2))
	   (not (intersectp-equal (remove-equal x l1)
				  l2)))
  :hints (("goal" :in-theory (enable intersectp-equal)))
  :rule-classes
  (:type-prescription
   (:type-prescription
    :corollary
    (implies (not (intersectp-equal l1 l2))
	     (not (intersectp-equal l2
				    (remove-equal x l1)))))))

(defthm remove-of-remove
  (equal (remove-equal x1 (remove-equal x2 l))
	 (remove-equal x2 (remove-equal x1 l))))

(defthm remove1-assoc-of-append
  (equal (remove1-assoc key (append x y))
         (if (equal (remove1-assoc key x)
                    (true-list-fix x))
             (append x (remove1-assoc key y))
             (append (remove1-assoc key x) y))))

(defthm remove1-assoc-when-absent
  (implies (not (null key))
           (iff
            (equal (remove1-assoc key alist) (true-list-fix alist))
            (atom (assoc key alist))))
  :rule-classes
  ((:rewrite
    :corollary
    (implies (and
              (not (null key))
              (atom (assoc key alist)))
             (equal (remove1-assoc key alist) (true-list-fix alist))))
   (:rewrite
    :corollary
    (implies (and
              (not (null key))
              (consp (assoc key alist)))
             (not
              (equal (remove1-assoc key alist) (true-list-fix alist)))))
   (:rewrite
    :corollary
    (implies (and
              (not (null key))
              (consp (assoc key alist))
              (true-listp alist))
             (not
              (equal (remove1-assoc key alist) alist))))))

(defthm put-assoc-of-put-assoc-1
  (equal (put-assoc-equal name val2 (put-assoc-equal name val1 alist))
         (put-assoc-equal name val2 alist)))

(defthm
  put-assoc-of-put-assoc-2
  (implies (and (or (consp (assoc-equal name1 alist))
                    (consp (assoc-equal name2 alist)))
                (not (equal name1 name2)))
           (equal (put-assoc-equal name1
                                   val1 (put-assoc-equal name2 val2 alist))
                  (put-assoc-equal name2 val2
                                   (put-assoc-equal name1 val1 alist)))))

(defthm put-assoc-of-append
  (implies (not (null name))
           (equal (put-assoc-equal name val (append x y))
                  (if (atom (assoc-equal name x))
                      (append x (put-assoc-equal name val y))
                      (append (put-assoc-equal name val x)
                              y)))))

;; This is disabled because I cannot decide on a normal form.
(defthmd put-assoc-of-remove
  (implies (and (not (null name)) (atom x))
           (equal (remove-equal x (put-assoc-equal name val alist))
                  (put-assoc-equal name val (remove-equal x alist)))))

(defthm member-of-put-assoc
  (implies (and (atom x) (case-split (not (null name))))
           (iff (member x (put-assoc-equal name val alist))
                (member x alist))))

(defthm
  consp-of-remove-assoc-1
  (implies (and (not (equal x2 x1))
                (consp (assoc-equal x1 alist)))
           (consp (remove-assoc-equal x2 alist))))

(defthm assoc-of-true-list-fix
  (equal (assoc-equal x (true-list-fix l))
         (assoc-equal x l))
  :hints (("goal" :in-theory (enable true-list-fix))))

(defthm strip-cars-of-true-list-fix
  (equal (strip-cars (true-list-fix x)) (strip-cars x)))

(defthm remove-assoc-of-true-list-fix
  (equal (remove-assoc-equal x (true-list-fix alist))
         (remove-assoc-equal x alist)))

(defthm put-assoc-equal-of-true-list-fix
  (equal (put-assoc-equal name val (true-list-fix alist))
         (true-list-fix (put-assoc-equal name val alist))))

(defthmd len-when-consp
  (implies (consp x) (not (zp (len x))))
  :rule-classes :type-prescription)

(defthm subsetp-of-strip-cars-of-put-assoc
  (implies (and (subsetp-equal (strip-cars x) l)
                (member-equal key l))
           (subsetp-equal (strip-cars (put-assoc-equal key val x))
                          l)))

(defthm position-equal-ac-of-nthcdr
  (implies (not (member-equal item (take n lst)))
           (equal (position-equal-ac item (nthcdr n lst)
                                     ac)
                  (position-equal-ac item lst (- ac (nfix n))))))

(defthm position-equal-ac-of-+
  (equal (position-equal-ac item lst (+ acc n))
         (if (member-equal item lst)
             (+ n (position-equal-ac item lst acc))
             nil)))

(defthm position-equal-ac-when-member
  (implies (and (member-equal item lst) (natp acc))
           (and
            (< (position-equal-ac item lst acc) (+ acc (len lst)))
            (natp (position-equal-ac item lst acc))))
  :rule-classes
  ((:type-prescription
    :corollary
    (implies (and (member-equal item lst) (natp acc))
             (natp (position-equal-ac item lst acc))))
   (:linear
    :corollary
    (implies (and (member-equal item lst) (natp acc))
             (and
              (< (position-equal-ac item lst acc) (+ acc (len lst)))
              (<= 0 (position-equal-ac item lst acc)))))))

(defthmd nth-of-position-equal-ac
  (implies (member-equal item lst)
           (equal (nth (- (position-equal-ac item lst acc) acc)
                       lst)
                  item)))

(defthm position-equal-ac-of-nth
  (implies (and (no-duplicatesp-equal l)
                (< (nfix n) (len l)))
           (equal (position-equal-ac (nth n l) l acc)
                  (+ acc (nfix n))))
  :hints (("goal" :induct (mv (position-equal-ac (nth n l) l acc)
                              (nth n l))
           :in-theory (disable member-equal-nth))
          ("subgoal *1/2" :use (:instance member-equal-nth (l (cdr l))
                                          (n (+ -1 n))))))

(defthm position-equal-ac-of-take
  (implies (and (member-equal item (take n l))
                (<= (nfix n) (len l)))
           (equal (position-equal-ac item (take n l) ac)
                  (position-equal-ac item l ac))))

(defthm position-equal-ac-when-member-of-take
  (implies (and (member-equal x (take n l))
                (<= (nfix n) (len l)))
           (<= (position-equal-ac x l acc)
               (+ (nfix n) acc)))
  :rule-classes :linear)

(encapsulate
  ()

  (local (in-theory (disable position-equal)))

  (defthm position-of-nthcdr
    (implies (and (true-listp lst)
                  (not (member-equal item (take n lst)))
                  (member-equal item lst))
             (equal (position-equal item (nthcdr n lst))
                    (- (position-equal item lst) (nfix n))))
    :hints (("goal" :in-theory (e/d (position-equal)
                                    ((:rewrite position-equal-ac-of-+)))
             :do-not-induct t
             :use (:instance (:rewrite position-equal-ac-of-+)
                             (n (- (nfix n)))
                             (acc 0)
                             (lst lst)
                             (item item)))))

  (defthm position-when-member
    (implies (member-equal item lst)
             (and
              (natp (position-equal item lst))
              (< (position-equal item lst) (len lst))))
    :hints (("goal" :in-theory (enable position-equal)))
    :rule-classes
    ((:type-prescription
      :corollary
      (implies (member-equal item lst)
               (natp (position-equal item lst))))
     (:linear
      :corollary
      (implies (member-equal item lst)
               (and
                (<= 0 (position-equal item lst))
                (< (position-equal item lst) (len lst)))))
     (:rewrite
      :corollary
      (implies (member-equal item lst)
               (and
                (integerp (position-equal item lst))
                (acl2-numberp (position-equal item lst)))))))

  (defthm nth-of-position-equal
    (implies (member-equal item lst)
             (equal (nth (position-equal item lst) lst)
                    item))
    :hints (("goal" :in-theory (enable position-equal)
             :use (:instance nth-of-position-equal-ac (acc 0)))))

  (defthm position-equal-of-nth
    (implies (and (no-duplicatesp-equal l)
                  (< (nfix n) (len l)))
             (equal (position-equal (nth n l) l)
                    (nfix n)))
    :hints (("Goal" :in-theory (enable position-equal))))

  (defthm position-of-take
    (implies (and (member-equal item (take n l))
                  (<= (nfix n) (len l)))
             (equal (position-equal item (take n l))
                    (position-equal item l)))
    :hints (("goal" :in-theory (enable position-equal))))

  (defthm
    position-when-member-of-take
    (implies (and (member-equal x (take n l))
                  (<= (nfix n) (len l)))
             (<= (position-equal x l) (nfix n)))
    :hints (("goal" :in-theory (e/d (position-equal)
                                    (position-equal-ac-when-member-of-take))
             :use (:instance position-equal-ac-when-member-of-take
                             (acc 0))))
    :rule-classes :linear))

;; Contributed to books/std/lists/nthcdr.lisp
(defthm
  subsetp-of-nthcdr
  (subsetp-equal (nthcdr n l) l))

(defthm no-duplicatesp-equal-of-nthcdr
  (implies (no-duplicatesp-equal l)
           (no-duplicatesp-equal (nthcdr n l))))

(defthm remove-assoc-of-append
  (equal (remove-assoc-equal x (append alist1 alist2))
         (append (remove-assoc-equal x alist1)
                 (remove-assoc-equal x alist2))))

(defthm nat-listp-of-take
  (implies (nat-listp l)
           (iff (nat-listp (take n l))
                (<= (nfix n) (len l)))))

(defthm assoc-when-zp-len
  (implies (zp (len alist))
           (atom (assoc-equal x alist)))
  :rule-classes :type-prescription)

(defthmd
  member-of-take
  (implies (and (true-listp l)
                (< (nfix n) (len l)))
           (iff (member-equal x (take n l))
                (and (member-equal x l)
                     (< (position-equal x l) (nfix n)))))
  :hints (("goal" :induct (mv (member-equal x l) (take n l))
           :expand (position-equal (car l) l))
          ("subgoal *1/2" :in-theory (disable (:rewrite position-of-nthcdr))
           :use (:instance (:rewrite position-of-nthcdr)
                           (lst l)
                           (n 1)
                           (item x)))
          ("subgoal *1/1.1'"
           :in-theory (disable (:type-prescription position-when-member))
           :use (:instance (:type-prescription position-when-member)
                           (lst l)
                           (item x)))))

(defthm position-of-cdr
  (implies (and (true-listp lst)
                (not (equal item (car lst)))
                (member-equal item lst))
           (equal (position-equal item (cdr lst))
                  (- (position-equal item lst) 1)))
  :hints (("goal" :in-theory (e/d (position-equal)
                                  (position-of-nthcdr))
           :use (:instance position-of-nthcdr (n 1)))))

(defthm member-equal-nth-take-when-no-duplicatesp
  (implies (and (equal x (nth n l))
                (< (nfix n) (len l))
                (no-duplicatesp-equal l))
           (not (member-equal x (take n l)))))

(defthmd consp-of-set-difference$
  (iff (consp (set-difference-equal l1 l2))
       (not (subsetp-equal l1 l2))))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/sets.lisp, from where it was taken with thanks.
(defthm member-of-set-difference-equal
  (iff (member a (set-difference-equal x y))
       (and (member a x) (not (member a y))))
  :hints (("goal" :induct (len x))))

(defthm no-duplicatesp-of-set-difference$
  (implies
   (no-duplicatesp-equal l1)
   (no-duplicatesp-equal (set-difference-equal l1 l2))))

(encapsulate
  ()

  (local (defthmd lemma-1
           (implies (atom l2)
                    (equal (set-difference-equal l1 l2)
                           (true-list-fix l1)))))

  (local
   (defthmd
     lemma-2
     (implies
      (consp l2)
      (equal
       (set-difference-equal l1 l2)
       (remove-equal (car l2)
                     (set-difference-equal l1 (cdr l2)))))))

  (defthmd
    set-difference$-redefinition
    (equal
     (set-difference-equal l1 l2)
     (if (atom l2)
         (true-list-fix l1)
       (remove-equal (car l2)
                     (set-difference-equal l1 (cdr l2)))))
    :hints (("goal" :use (lemma-1 lemma-2)))
    :rule-classes :definition))

(defthm len-of-remove-when-member-1
  (implies (member-equal x l)
           (< (len (remove-equal x l)) (len l)))
  :rule-classes :linear)

(defthm
  len-of-set-difference$-when-subsetp
  (implies (and (subsetp-equal x y)
                (no-duplicatesp-equal x))
           (<= (+ (len x)
                  (len (set-difference-equal y x)))
               (len y)))
  :hints
  (("goal"
    :in-theory (e/d (set-difference$-redefinition subsetp-equal)
                    (set-difference-equal))))
  :rule-classes :linear)

(defthm member-of-remove-duplicates
  (iff (member-equal x (remove-duplicates-equal lst))
       (member-equal x lst)))

(defthm no-duplicatesp-of-remove-duplicates
  (no-duplicatesp-equal (remove-duplicates-equal l)))

(defthm len-of-strip-cars (equal (len (strip-cars x)) (len x)))

(defthm consp-of-last (iff (consp (last l)) (consp l)))

(defthm member-of-car-of-last
  (implies (consp x)
           (member-equal (car (last x)) x)))

(defthm append-of-take-and-last
  (equal (append (take (+ -1 (len path)) path)
                 (last path))
         path))

(defthm atom-of-cdr-of-last
  (atom (cdr (last x)))
  :rule-classes :type-prescription)

(defthm last-when-equal-len-1
  (implies (equal (len l) 1) (equal (last l) l)))

;; The following two theorems are redundant with the eponymous theorems in
;; books/std/lists/resize-list.lisp, from where they were taken with thanks.
(defthm len-of-resize-list
  (equal (len (resize-list lst n default))
         (nfix n)))
(defthm resize-list-of-len-free
  (implies (equal (nfix n) (len lst))
           (equal (resize-list lst n default-value)
                  (true-list-fix lst))))

(defthm true-listp-of-put-assoc
  (implies (not (null name))
           (iff (true-listp (put-assoc-equal name val alist))
                (or (true-listp alist)
                    (atom (assoc-equal name alist))))))

(defthm
  assoc-after-remove1-assoc-when-no-duplicatesp
  (implies (and (not (null name))
                (no-duplicatesp-equal (remove-equal nil (strip-cars alist))))
           (not (consp (assoc-equal name
                                    (remove1-assoc-equal name alist))))))

(defthmd last-alt (equal (last x) (nthcdr (- (len x) 1) x)))

(defthm nat-listp-when-subsetp
  (implies (and (subsetp-equal x y) (nat-listp y))
           (nat-listp (true-list-fix x)))
  :hints (("goal" :in-theory (enable subsetp-equal))))

;; The following is redundant with the eponymous theorem in
;; books/std/lists/remove.lisp, from where it was taken with thanks.
(defthm remove-of-set-difference-equal
  (equal (remove a (set-difference-equal x y))
         (set-difference-equal (remove a x) y)))

(defthm set-difference$-of-remove-when-member-1
  (implies (member-equal a y)
           (equal (set-difference-equal (remove a x) y)
                  (set-difference-equal x y))))

(defthm
  set-difference$-of-intersection$-1
  (equal (set-difference-equal l1 (intersection-equal l1 l2))
         (set-difference-equal l1 l2))
  :hints
  (("goal"
    :induct (mv (intersection-equal l1 l2)
                (set-difference-equal l1 l2))
    :expand
    (:with set-difference$-redefinition
           (set-difference-equal l1
                                 (cons (car l1)
                                       (intersection-equal (cdr l1) l2)))))))

(defthm len-of-put-assoc-equal-2
  (implies (consp (assoc-equal name alist))
           (equal (len (put-assoc-equal name val alist))
                  (len alist))))

(defthm intersection$-of-remove-1
  (equal (intersection-equal y (remove-equal x l))
         (if (not (member-equal x y))
             (intersection-equal y l)
             (remove-equal x (intersection-equal y l)))))

(defthm set-difference$-when-not-intersectp
  (implies (not (intersectp-equal x y))
           (equal (set-difference-equal x y)
                  (true-list-fix x))))

(defthm set-difference$-of-append-2
  (equal (set-difference-equal x (append x y))
         nil))

(defthm
  set-difference$-of-self-lemma-1
  (equal (set-difference-equal x (append y nil)) (set-difference-equal x y)))

(defthm
  set-difference$-of-self
  (equal (set-difference-equal x x) nil)
  :hints (("goal" :in-theory (disable set-difference$-of-append-2)
           :use (:instance set-difference$-of-append-2 (y nil)))))

(defthm set-difference$-of-append-1
  (equal (set-difference-equal (append x y) z)
         (append (set-difference-equal x z)
                 (set-difference-equal y z))))

(defthm remove-duplicates-when-no-duplicatesp
  (implies (no-duplicatesp-equal x)
           (equal (remove-duplicates-equal x)
                  (true-list-fix x))))

(defthm
  not-intersectp-of-set-difference$-when-subsetp-1
  (implies (subsetp-equal z y)
           (not (intersectp-equal z (set-difference-equal x y))))
  :rule-classes
  (:rewrite
   (:rewrite
    :corollary (implies (subsetp-equal z y)
                        (not (intersectp-equal (set-difference-equal x y)
                                               z))))))

(defthm subsetp-of-set-difference$
  (subsetp-equal (set-difference-equal x y)
                 x))

(defthm alistp-of-append
  (equal (alistp (append x y))
         (and (alistp (true-list-fix x))
              (alistp y))))

;; Contributed to books/std/lists/take.lisp
(defthmd take-as-append-and-nth
  (equal (take n l)
         (if (zp n)
             nil
             (append (take (- n 1) l)
                     (list (nth (- n 1) l)))))
  :rule-classes ((:definition :install-body nil)))

(theory-invariant (incompatible (:rewrite take-as-append-and-nth)
                                (:rewrite append-of-take-and-cons)))

(defthm consp-of-assoc-of-nth-of-strip-cars
  (implies (not (null (nth n (strip-cars alist))))
           (consp (assoc-equal (nth n (strip-cars alist))
                               alist)))
  :hints (("goal" :in-theory (disable (:rewrite member-equal-nth)
                                      (:rewrite member-of-strip-cars))
           :use ((:instance (:rewrite member-equal-nth)
                            (l (strip-cars alist))
                            (n n))
                 (:instance (:rewrite member-of-strip-cars)
                            (alist alist)
                            (x (nth n (strip-cars alist))))))))

(defthmd painful-debugging-lemma-21
  (equal (+ x (- x) y) (fix y))
  :hints (("goal" :in-theory (disable (:e force)))))

(encapsulate () (local (in-theory (disable fix)))
  (defthm fix-when-acl2-numberp
    (implies (acl2-numberp x)
             (equal (fix x) x))
    :hints (("goal" :in-theory (enable fix)))))

(encapsulate () (local (in-theory (disable length string-append)))
  (defthm length-of-string-append
    (equal (length (string-append str1 str2))
           (+ (len (coerce str1 'list))
              (len (coerce str2 'list))))
    :hints (("goal" :in-theory (enable length string-append)))))

(encapsulate () (local (in-theory (disable nfix)))
  (defthm
    nfix-of-position-ac-linear
    (implies (<= 0 acc)
             (<= (nfix (position-equal-ac item lst acc))
                 (+ acc (len lst))))
    :rule-classes :linear :hints (("Goal" :in-theory (enable nfix)))))

(encapsulate () (local (in-theory (disable length)))
  (defthm
    length-when-stringp
    (implies (stringp x)
    (equal
     (length x)
     (len (coerce x 'list))))
    :hints (("goal" :in-theory (enable length)))))

(encapsulate () (local (in-theory (disable string-append)))
  (defthm string-append-of-empty-string-1
    (equal (string-append "" str2)
           (if (stringp str2) str2 ""))
    :hints (("goal" :in-theory (enable string-append))))
  (defthm string-append-of-empty-string-2
    (equal (string-append str1 "")
           (if (stringp str1) str1 ""))
    :hints (("goal" :in-theory (enable string-append)))))

(encapsulate () (local (in-theory (disable nfix natp)))
  (defthm nfix-when-natp
    (implies (natp x) (equal (nfix x) x))
    :hints (("goal" :do-not-induct t
             :in-theory (enable nfix natp))))

  (defthm nfix-when-zp
    (implies (zp x) (equal (nfix x) 0))
    :hints (("goal" :in-theory (enable nfix natp)))))

;; The following are redundant with the eponymous theorems in
;; books/std/lists/take.lisp, from where they were taken with thanks.
(defthm take-of-append
  (equal (take n (append x y))
         (if (< (nfix n) (len x))
             (take n x)
             (append x (take (- n (len x)) y))))
  :hints (("goal" :induct (take n x))))

(encapsulate () (local (in-theory (disable subseq string-append)))

  (local
   (defthm lemma-1 (iff (equal (len (coerce str1 'list)) 0)
                        (equal (coerce str1 'list) nil))
     :hints
     (("goal" :expand (len (coerce str1 'list))))))

  (local
   (defthmd lemma-2
     (implies (and (<= 0 (- start)) (<= 0 start))
              (integerp (- start)))))

  ;; There's no simple way to reduce the number of cases here.
  (defthm subseq-of-string-append
    (equal (subseq (string-append str1 str2) start end)
           (cond ((and (not (stringp str2)) (not (stringp str1))) (subseq "" start end))
                 ((not (stringp str1)) (subseq str2 start end))
                 ((not (stringp str2)) (subseq str1 start end))
                 ((and (integerp start) (<= (length str1) end)
                       (<= start (length str1)) (<= 0 start) (integerp end))
                  (string-append (subseq str1 start nil)
                                 (subseq str2 0 (- end (length str1)))))
                 ((and (< end (+ start (length str1))) (not (null end))
                       (natp (- end start)) (not (integerp start)))
                  (subseq str1 0 (- end start)))
                 ((and (>= end (+ start (length str1))) (not (null end))
                       (integerp (- end start)) (not (integerp start)))
                  (string-append str1 (subseq str2 0 (- end (+ start (length str1))))))
                 ((not (integerp (- start))) "")
                 ((and (integerp start) (<= start (length str1)) (<= 0 start) (null end))
                  (string-append (subseq str1 start nil) str2))
                 ((and (<= start 0) (equal (length str1) 0)
                       (not (null end)) (not (acl2-numberp end)))
                  (string-append str1 (subseq str2 0 (- start))))
                 ((and (< (- start) (length str1)) (not (null end)) (not (acl2-numberp end)))
                  (subseq str1 0 (- start)))
                 ((and (< start 0) (<= (length str1) (- start))
                       (not (null end)) (not (acl2-numberp end)))
                  (string-append str1 (subseq str2 0 (- (+ start (length str1))))))
                 ((and (< start 0) (integerp end)
                       (<= (+ (length str1) start) end))
                  (string-append str1 (subseq str2 0 (- end (+ start (length str1))))))
                 ((and (< (length str1) start) (null end)
                       (<= start (+ (length str1) (length str2))))
                  (subseq str2 (- start (length str1)) nil))
                 ((and (< (length str1) start) (integerp end)
                       (<= start (+ (length str1) (length str2))))
                  (subseq str2 (- start (length str1)) (- end (length str1))))
                 ((and (<= 0 start) (<= start end) (<= end (length str1)) (integerp end))
                  (subseq str1 start end))
                 ((and (integerp start) (< start 0) (null end))
                  (string-append str1 (subseq str2 0 (- (length str2) start))))
                 ((and (< start 0) (< end (+ start (length str1)))
                       (not (null end)) (<= start end))
                  (subseq str1 start end))
                 ((and (integerp start) (< (+ (length str1) (length str2)) start))
                  (subseq "" start end))
                 ((and (acl2-numberp end) (not (integerp end))) "")
                 ((and (not (null end)) (< end start)) "")
                 (t (string-append str1 str2))))
    :hints (("goal" :in-theory
             (e/d (subseq string-append)
                  ((:e force) (:rewrite coerce-inverse-1) (:rewrite coerce-inverse-2)))
             :do-not-induct t
             :use
             ((:instance painful-debugging-lemma-21 (x start) (y (- (length str1))))
              (:theorem (iff (integerp (+ (- start) (length str1) (length str2)))
                             (integerp (- start))))
              lemma-2
              (:instance completion-of-coerce (y 'string)
                         (x (take (+ end (- start) (- (len (coerce str1 'list))))
                                  (coerce str2 'list))))
              (:instance completion-of-coerce (y 'string)
                         (x (append (coerce str1 'list)
                                    (take (+ end (- start) (- (len (coerce str1 'list))))
                                          (coerce str2 'list)))))
              (:instance completion-of-coerce (y 'string)
                         (x (take (+ (- start) (len (coerce str2 'list))) (coerce str2 'list))))
              (:instance completion-of-coerce (y 'string)
                         (x (append (coerce str1 'list)
                                    (take (+ (- start) (len (coerce str2 'list)))
                                          (coerce str2 'list)))))
              (:instance completion-of-coerce (y 'string)
                         (x (take (+ end (- (len (coerce str1 'list))))
                                  (coerce str2 'list))))
              (:instance completion-of-coerce (y 'string)
                         (x (append (nthcdr start (coerce str1 'list))
                                    (take (+ end (- (len (coerce str1 'list))))
                                          (coerce str2 'list)))))
              (:instance (:rewrite coerce-inverse-1)
                         (x (make-character-list (take (+ end (- start)
                                                          (- (len (coerce str1 'list))))
                                                       (coerce str2 'list)))))
              (:instance (:rewrite coerce-inverse-1) (x (nthcdr start (coerce str1 'list))))
              (:instance (:rewrite coerce-inverse-1)
                         (x (append (coerce str1 'list) (coerce str2 'list))))
              (:instance (:rewrite coerce-inverse-1)
                         (x (take (+ end (- (len (coerce str1 'list)))) (coerce str2 'list))))
              (:instance (:rewrite painful-debugging-lemma-21)
                         (x (len (coerce str1 'list))) (y (len (coerce str2 'list))))
              (:instance (:rewrite coerce-inverse-1)
                         (x (make-character-list (take (+ (- start) (len (coerce str2 'list)))
                                                       (coerce str2 'list)))))
              (:instance (:rewrite coerce-inverse-2) (x str1))
              (:instance (:rewrite coerce-inverse-1)
                         (x (make-character-list
                             (take (- end (len (coerce str1 'list))) (coerce str2 'list)))))))))

  (defthm then-subseq-empty-1
    (implies (and (stringp seq)
                  (>= start (length seq)))
             (equal (subseq seq start nil) ""))
    :hints (("goal" :in-theory (enable subseq subseq-list))))

  (defthm then-subseq-same-1
    (implies (stringp seq)
             (equal (subseq seq 0 nil) seq))
    :hints (("goal" :in-theory (enable subseq subseq-list))))

  (defthm subseq-of-length-1
    (implies (equal (length seq) end)
             (equal (subseq seq start end)
                    (subseq seq start nil)))
    :hints (("goal" :do-not-induct t
             :in-theory (enable subseq subseq-list))))

  (defthm subseq-of-empty-list
    (equal (subseq "" start end)
           (coerce (take (+ end (- start)) nil) 'string))
    :hints (("goal" :in-theory (enable subseq subseq-list))))

  (defthm then-subseq-same-2
    (implies
     (and (stringp seq) (equal end (length seq)))
     (equal (subseq seq 0 end) seq))
    :hints (("Goal" :in-theory (enable subseq subseq-list)))))

(defthm when-append-same
  (iff (equal x (append x y))
       (equal y (if (consp x) (cdr (last x)) x))))

(defthm
  set-difference$-becomes-intersection$
  (equal (set-difference-equal l1 (set-difference-equal l1 l2))
         (intersection-equal l1 l2))
  :hints
  (("goal"
    :induct (intersection-equal l1 l2)
    :in-theory (e/d nil nil)
    :expand
    (:with
     set-difference$-redefinition
     (set-difference-equal (cdr l1)
                           (cons (car l1)
                                 (set-difference-equal (cdr l1) l2)))))))

(defthm subsetp-of-set-difference$-2
  (equal (subsetp-equal z (set-difference-equal x y))
         (and (subsetp-equal z x)
              (not (intersectp-equal z y))))
  :hints (("goal" :in-theory (e/d () (intersectp-is-commutative))
           :induct (mv (intersectp-equal z y) (subsetp-equal z x)))))

(defthm intersectp-when-subsetp
  (implies (subsetp-equal x y)
           (equal (intersectp-equal x y)
                  (consp x))))

(defthm nth-under-iff-1
  (implies (not (member-equal nil l))
           (iff (nth n l) (< (nfix n) (len l)))))

(defthm consp-when-member
  (implies (member-equal x lst)
           (consp lst))
  :rule-classes :forward-chaining)

(encapsulate ()
  (local (in-theory (disable min)))

  (defthm painful-debugging-lemma-11 (iff (< (min x y) y) (< x y))
    :hints (("Goal" :in-theory (enable min))))

  (defthm painful-debugging-lemma-22
    (implies (equal (+ w y) z)
             (iff (equal (+ w (min x y)) z)
                  (<= y x)))
    :hints (("Goal" :in-theory (enable min))))

  (defthm painful-debugging-lemma-17
    (zp (+ (- x) (min x y)))
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (enable min)))))

(defthmd
  painful-debugging-lemma-8
  (implies (not (zp cluster-size))
           (and
            (equal (ceiling cluster-size cluster-size) 1)
            (equal (ceiling 0 cluster-size) 0))))

(defthm painful-debugging-lemma-9
  (implies (and (not (zp j)) (integerp i) (>= i 0))
           (>= (ceiling i j) 0))
  :rule-classes (:linear :type-prescription))

(defthm painful-debugging-lemma-10
  (implies (and (not (zp j)) (integerp i) (> i 0))
           (> (ceiling i j) 0))
  :rule-classes (:linear :type-prescription))

(defthm member-of-nth-when-not-intersectp
  (implies (and (not (intersectp-equal l x))
                (< (nfix n) (len l)))
           (not (member-equal (nth n l) x))))

(defthm true-list-listp-of-remove
  (implies (true-list-listp l)
           (true-list-listp (remove-equal x l))))

(defthm subsetp-of-set-difference$-when-subsetp
  (implies (subsetp-equal x y)
           (subsetp-equal (set-difference-equal x z)
                          (set-difference-equal y z)))
  :hints (("goal" :induct (mv (set-difference-equal x z)
                              (subsetp-equal x y))
           :in-theory (e/d nil (intersectp-is-commutative)))))

(defthm
  true-list-listp-of-set-difference
  (implies (true-list-listp l1)
           (true-list-listp (set-difference-equal l1 l2)))
  :hints (("goal" :in-theory (enable set-difference-equal true-list-listp))))

(defthm last-of-append
  (equal (last (append x y))
         (cond ((consp y) (last y))
               ((consp x) (cons (car (last x)) y))
               (t y))))

;; This only addresses the linear part, because the integerp part is covered by
;; integerp-of-nth-when-integer-listp.
(defthm natp-of-nth-when-nat-listp
  (implies (nat-listp l) (<= 0 (nth n l)))
  :hints (("goal" :in-theory (enable nth nat-listp)))
  :rule-classes :linear)

(defthm acl2-number-listp-when-rational-listp
  (implies (rational-listp l)
           (acl2-number-listp l)))

(defthm rational-listp-when-integer-listp
  (implies (integer-listp l)
           (rational-listp l)))

(defthm integer-listp-when-nat-listp
  (implies (nat-listp l)
           (integer-listp l)))

(defthm consp-of-strip-cars (equal (consp (strip-cars x)) (consp x)))
