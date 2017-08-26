; (certify-book "utilities")

(in-package "ACL2")

(include-book "arithmetic/top-with-meta" :dir :system)
(include-book "ordinals/lexicographic-ordering" :dir :system)
(in-theory (enable posp))

; A little digression... Here is a little fact ACL2 ought to know but can't
; puzzle out from its axioms, without help.
(defthm coerce-lemma
  (implies (and (stringp pat)
                (not (equal pat "")))
           (consp (coerce pat 'list)))
  :hints (("Goal" :use (:instance coerce-inverse-2
                                  (x pat))
           :in-theory (disable coerce-inverse-2))))

(defthm coerce-lemma-corrollary
  (implies (and (stringp pat)
                (not (equal pat "")))
           (coerce pat 'list))
  :hints (("Goal" :use coerce-lemma :in-theory (disable coerce-lemma))))

(defthm nthcdr-len
  (implies (true-listp x) (equal (nthcdr (len x) x) nil)))


; This lemma is ugly but is the way it is to avoid folding len via the more
; natural (len (cdr x)) = (- (len x) 1).
(defthm nthcdr-firstn
  (implies (and (natp i)
                (natp d)
                (<= i d))
           (equal (nthcdr i (firstn d x))
                  (firstn (- d i) (nthcdr i x)))))

(defthm len-firstn
  (equal (len (firstn n x)) (min (len x) (nfix n))))

(defthm car-firstn
  (equal (car (firstn n x)) (if (zp n) nil (car x))))

(defthm true-listp-nthcdr
  (implies (true-listp x)
           (true-listp (nthcdr n x))))

(defthm true-listp-cdr
  (implies (true-listp x)
           (true-listp (cdr x))))

(defthm nthcdr-nil-2
  (equal (nthcdr i nil) nil))

(defthm nth-nthcdr
  (equal (nth n (nthcdr m x))
	 (nth (+ (nfix n) (nfix m)) x)))

(defthm len-nthcdr
  (equal (len (nthcdr n x))
	 (nfix (- (len x) (nfix n)))))

; This lemma is ugly but is the way it is to avoid folding len via the more
; natural (len (cdr x)) = (- (len x) 1).

(defthm len-cdr
  (implies (natp j)
           (equal (len (cdr (nthcdr j pat)))
                  (nfix (- (len pat) (+ j 1))))))


(defthm nthcdr-cdr
  (equal (nthcdr i (cdr x)) (cdr (nthcdr i x))))

(defthm consp-nthcdr-2
  (iff (consp (nthcdr i x))
       (< (nfix i) (len x))))

(defthm nth-is-car-nthcdr-2
  (equal (nth i x) (car (nthcdr i x))))


(defthm dumb-lemma
  (implies (and (integerp i)
		(integerp j))
	   (equal (equal (+ i j) 0)
		  (equal i (- j)))))

(defthm nth-is-car-nthcdr
  (equal (nth i x) (car (nthcdr i x))))

(defthm nthcdr-nil
  (equal (nthcdr i nil) nil))

(defthm consp-nthcdr
  (implies (natp i)
	   (iff (consp (nthcdr i x))
		(< i (len x)))))

(defthm nthcdr-firstn-nthcdr
  (implies (and (natp n)
                (natp i)
                (natp d))
           (equal (nthcdr n (firstn d (nthcdr i txt)))
                  (firstn (+ d (- n))
                          (nthcdr (+ i n) txt)))))

(defun up-down-hint (i d)
  (cond ((zp d) (list i d))
        (t (up-down-hint (+ 1 i) (- d 1)))))

(defthm firstn-nthcdr-firstn
  (implies (and (natp i)
                (natp n)
                (<= (+ d i) n))
         (equal (firstn d (nthcdr i (firstn n txt)))
                (firstn d (nthcdr i txt))))
  :hints (("goal" :induct (up-down-hint i d))))

(defthm nthcdr-non-nil
  (iff (nthcdr j pat)
       (if (natp j)
           (or (< j (len pat))
               (and (not (true-listp pat))
                    (equal j (len pat))))
         pat)))

; !!!

; We are going to explore using the elim rule to replace txt by (append a b),
; where a and b are new variables representing the firstn and nthcdr of txt.
; If we get through this proof we should move this work into utilities and
; start over, using this technique widely.

; These lemmas were typed in ahead of time, anticipating what would happen.

(defthm firstn-nthcdr-elim
  (implies (and (natp n)
                (< n (len x)))
           (equal (append (firstn n x) (nthcdr n x)) x))
  :rule-classes :elim)

(defthm len-firstn-gen
  (equal (len (firstn n x))
         (min (len x) (nfix n)))
  :rule-classes :generalize)

(defthm len-append
  (equal (len (append x y))
         (+ (len x) (len y))))

(defthm len-nthcdr-gen
  (equal (len (nthcdr n x))
         (nfix (- (len x) (nfix n))))
  :rule-classes :generalize)

; Then we discovered the need for these lemmas using The Method as
; we banged away on matchpx-pmatchp below.

(defthm firstn-firstn
  (equal (firstn n (firstn k x))
         (if (<= (nfix n) (nfix k))
             (firstn n x)
           (firstn k x))))
  
(defthm true-listp-nthcdr-gen
  (implies (true-listp x)
           (true-listp (nthcdr n x)))
  :rule-classes :generalize)


(defthm firstn-len
  (implies (true-listp x)
           (equal (firstn (len x) x) x)))

(defthm firstn-too-big
  (implies (and (natp n)
                (<= (len x) n)
                (true-listp x))
           (equal (firstn n x) x)))

(defthm firstn-append
  (equal (firstn n (append a b))
         (if (<= (nfix n) (len a))
             (firstn n a)
           (append a (firstn (- (nfix n) (len a)) b)))))

(defun hint2 (a b)
  (if (consp a)
      (if (consp b)
          (hint2 (cdr a) (cdr b))
        (list a b))
    (list a b)))

(defthm equal-append
  (implies (and (true-listp a)
                (true-listp b)
                (equal (len a) (len b)))
           (equal (equal (append a c)
                         (append b d))
                  (and (equal a b)
                       (equal c d))))
  :hints (("Goal" :induct (hint2 a b))))

(defthm nthcdr-append
  (equal (nthcdr n (append a b))
         (if (<= (nfix n) (len a))
             (append (nthcdr n a) b)
           (nthcdr (- (nfix n) (len a)) b))))

(defthm characterp-car-nthcdr-coerce
  (implies (character-listp x)
           (equal (characterp (car (nthcdr i x)))
                  (< (nfix i) (len x)))))

(defthm lens-differ
  (implies (not (equal (len x) (len y)))
           (not (equal x y))))

; These two lemmas are needed for reasoning about M1 code.

(defthm equal-char-codes
  (implies (and (characterp x)
                (characterp y))
           (equal (equal (char-code x) (char-code y))
                  (equal x y)))
  :hints (("Goal"
           :use ((:instance CODE-CHAR-CHAR-CODE-IS-IDENTITY (c x))
                 (:instance CODE-CHAR-CHAR-CODE-IS-IDENTITY (c y)))
           :in-theory (disable CODE-CHAR-CHAR-CODE-IS-IDENTITY))))

; Found locally in books/ordinals/lexicographic-book.lisp:
(defthm len-0
  (equal (equal (len x) 0)
         (atom x)))

(defthm equal-length-0
  (equal (equal (length x) 0)
         (if (stringp x) (equal x "") (atom x))))
