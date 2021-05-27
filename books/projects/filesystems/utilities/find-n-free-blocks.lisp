(in-package "ACL2")

;  find-n-free-blocks.lisp                     Mihir Mehta

(local (include-book "../file-system-lemmas"))
(include-book "bounded-nat-listp")

(defthm mv-nth-replacement
  (equal (mv-nth n (cons a b))
         (if (zp n) a (mv-nth (- n 1) b))))

(in-theory (disable mv-nth))

(defun count-free-blocks (alv)
  (declare (xargs :guard (and (boolean-listp alv))))
  (if (atom alv)
      0
    (if (car alv)
        (count-free-blocks (cdr alv))
      (+ (count-free-blocks (cdr alv)) 1))))

(defthm count-free-blocks-correctness-1
  (equal (count-free-blocks (binary-append x y))
         (+ (count-free-blocks x)
            (count-free-blocks y))))

(defthm count-free-blocks-correctness-2
  (equal (count-free-blocks (revappend x y))
         (+ (count-free-blocks x)
            (count-free-blocks y))))

(defthm count-free-blocks-correctness-3
  (implies (and (nth key l) (not val))
           (equal (count-free-blocks (update-nth key val l))
                  (+ 1 (count-free-blocks l)))))

(defund find-n-free-blocks-helper (alv n start)
  (declare (xargs :guard (and (boolean-listp alv)
                              (natp n)
                              (natp start))))
  (if (or (atom alv) (zp n))
      nil
    (if (car alv)
        ;; this block is taken
        (find-n-free-blocks-helper (cdr alv) n (+ start 1))
      ;; this block isn't taken
      (cons start (find-n-free-blocks-helper (cdr alv) (- n 1) (+ start 1))))))

(defthmd find-n-free-blocks-helper-correctness-1
  (<= (len (find-n-free-blocks-helper alv n start))
      (nfix n))
  :rule-classes (:rewrite :linear)
  :hints (("goal" :in-theory (enable find-n-free-blocks-helper))))

(defthmd find-n-free-blocks-helper-correctness-2
  (equal (len (find-n-free-blocks-helper alv n start))
         (min (count-free-blocks alv) (nfix n)))
  :hints (("goal" :in-theory (enable find-n-free-blocks-helper))))

(defthmd find-n-free-blocks-helper-correctness-3
  (implies (natp start)
           (nat-listp (find-n-free-blocks-helper alv n start)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("goal" :in-theory (enable find-n-free-blocks-helper))))

(defthm
  find-n-free-blocks-helper-correctness-4
  (implies (> start m)
           (not (member-equal m
                              (find-n-free-blocks-helper alv n start))))
  :hints (("goal" :in-theory (enable find-n-free-blocks-helper))))

(defthm
  find-n-free-blocks-helper-correctness-5
  (implies (and (natp start)
                (equal (nth (- m start) alv) t))
           (not (member-equal m
                              (find-n-free-blocks-helper alv n start))))
  :hints
  (("goal" :in-theory (enable find-n-free-blocks-helper
                              find-n-free-blocks-helper-correctness-3))))

(defthmd find-n-free-blocks-helper-correctness-6
  (no-duplicatesp-equal (find-n-free-blocks-helper alv n start))
  :hints (("goal" :in-theory (enable find-n-free-blocks-helper))))

(defthmd find-n-free-blocks-helper-correctness-7
  (implies (natp start)
           (bounded-nat-listp (find-n-free-blocks-helper alv n start)
                              (+ start (len alv))))
  :hints (("goal" :in-theory (enable find-n-free-blocks-helper))))


(defund find-n-free-blocks (alv n)
  (declare (xargs :guard (and (boolean-listp alv)
                              (natp n))))
  (find-n-free-blocks-helper alv n 0))

  ;; Here are some examples showing how this works.
  ;; ACL2 !>(find-n-free-blocks (list t nil t) 1)
  ;; (1)
  ;; ACL2 !>(find-n-free-blocks (list t nil t) 2)
  ;; (1)
  ;; ACL2 !>(find-n-free-blocks (list t nil nil) 2)
  ;; (1 2)

(defthm
  find-n-free-blocks-correctness-1
  (<= (len (find-n-free-blocks alv n))
      (nfix n))
  :rule-classes (:rewrite :linear)
  :hints
  (("goal" :in-theory (enable find-n-free-blocks
                              find-n-free-blocks-helper-correctness-1))))

(defthm
  find-n-free-blocks-correctness-2
  (equal (len (find-n-free-blocks alv n))
         (min (count-free-blocks alv) (nfix n)))
  :hints
  (("goal" :in-theory (enable find-n-free-blocks
                              find-n-free-blocks-helper-correctness-2))))

(defthm
  find-n-free-blocks-correctness-3
  (nat-listp (find-n-free-blocks alv n))
  :rule-classes (:rewrite :type-prescription)
  :hints
  (("goal" :in-theory (enable find-n-free-blocks
                              find-n-free-blocks-helper-correctness-3))))

(defthm
  find-n-free-blocks-correctness-5
  (implies (equal (nth m alv) t)
           (not (member-equal m (find-n-free-blocks alv n))))
  :hints
  (("goal"
    :in-theory (e/d (find-n-free-blocks)
                    ((:rewrite find-n-free-blocks-helper-correctness-5)))
    :use (:instance (:rewrite find-n-free-blocks-helper-correctness-5)
                    (start 0)))))

(defthm
  find-n-free-blocks-correctness-6
  (no-duplicatesp-equal (find-n-free-blocks alv n))
  :hints
  (("goal" :in-theory (enable find-n-free-blocks
                              find-n-free-blocks-helper-correctness-6))))

(defthm
  find-n-free-blocks-correctness-7
  (implies (equal m (len alv))
           (bounded-nat-listp (find-n-free-blocks alv n)
                              m))
  :hints (("goal" :in-theory (enable find-n-free-blocks)
           :use (:instance find-n-free-blocks-helper-correctness-7
                           (start 0)))))

(defun count-free-blocks-alt (alv n)
  (declare (xargs :guard (and (natp n) (boolean-listp alv))))
  (if (zp n)
      0
    (+ (if (nth (- n 1) alv) 0 1)
       (count-free-blocks-alt alv (- n 1)))))

(defthm
  count-free-blocks-alt-correctness-1
  (implies (and (boolean-listp alv)
                (boolean-listp ac)
                (natp n)
                (<= n (len alv)))
           (equal (count-free-blocks-alt (revappend ac alv)
                                         (+ n (len ac)))
                  (count-free-blocks (first-n-ac n alv ac))))
  :hints (("goal" :induct (first-n-ac n alv ac))))

;; Might be useful at some point.
(defthm
  count-free-blocks-alt-correctness-lemma-1
  (equal (count-free-blocks (true-list-fix alv))
         (count-free-blocks alv))
  :hints (("Goal" :in-theory (enable true-list-fix))))

(defthm
  count-free-blocks-alt-correctness-2
  (implies (and (boolean-listp alv)
                (equal n (len alv)))
           (equal (count-free-blocks-alt alv n)
                  (count-free-blocks alv)))
  :hints (("goal" :in-theory (disable count-free-blocks-alt-correctness-1)
           :use (:instance count-free-blocks-alt-correctness-1
                           (ac nil)))))

(defun count-before-n (l b)
      (declare (xargs :guard (and (natp b) (nat-listp l))))
      (if (atom l) 0 (+ (if (< (car l) b) 1 0) (count-before-n (cdr l) b))))

(defthm count-before-n-correctness-1
  (<= (count-before-n l b) (len l))
  :rule-classes (:linear))

(defthm count-before-n-correctness-2
  (implies (nat-listp l)
           (iff (equal (count-before-n l b) (len l))
                (bounded-nat-listp l b))))

(defthm count-before-n-correctness-3
  (implies (nat-listp l)
           (equal (count-before-n l 0) 0)))
