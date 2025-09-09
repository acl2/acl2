;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; arithmetic-5++.lisp
;;;
;;; A few things that really should be added to arithmetic-5
;;;
;;; Includes arithmetic-5, so use this book instead of
;;; arithmetic-5/top
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "arithmetic-5/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Some handy induction schemes

(local
 (defun ind-hint+ (x)
   (cond ((zip x)
          42)
         ((equal x -1)
          42)
         (t
          (ind-hint+ (floor x 2))))))

(local
 (defun ind-hint-2 (x y)
   (if (or (zp x) (zp y))
       42
     (ind-hint-2 (floor x 2) (floor y 2)))))

(local
 (defun ind-hint-2+ (x n)
   (declare (xargs :measure (abs (ifix n))))
   (cond ((or (zip x) (zip n))
          42)
         ((< 0 n)
          (ind-hint-2+ (ash x -1) (+ -1 n)))
         ((< n 0)
          (ind-hint-2+ (ash x 1) (+ 1 n))))))

(local
 (defun ind-hint-3 (x y n)
   (if (or (zp x) (zp y) (zp n))
       42
     (ind-hint-3 (floor x 2) (floor y 2) (+ -1 n)))))

(local
 (defun ind-hint-3+ (x y n)
   (declare (xargs :measure (abs (ifix n))))
   (cond ((or (zip x) (zip y) (zip n))
          42)
         ((< 0 n)
          (ind-hint-3+ (ash x -1) (ash y -1) (+ -1 n)))
         ((< n 0)
          (ind-hint-3+ (ash x 1) (ash y 1) (+ 1 n))))))

(defun ind-hint-3-0 (x y z)
  (if (or (zip x) (equal x -1))
      (cons y z)
    (ind-hint-3-0 (floor x 2) (floor y 2) (floor z 2))))

;;; Some extras to be added to building-bocks

(defun p-o-2-g-fn-n (c)
  ;; original is in expt.lisp, but binds x which is a bad name for
  ;; here.
  (let ((n (power-of-2-generalized c)))
    (if n
        (list (cons 'n (kwote n)))
      nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; ash

(defthm default-ash-1
  (implies (syntaxp (not (proveably-integer 'x `((x . ,x))
                                            mfc state)))
           (equal (ash x n)
                  (if (integerp x)
                      (ash x n)
                    0))))

(defthm default-ash-2
  (implies (syntaxp (not (proveably-integer 'n `((n . ,n))
                                            mfc state)))
           (equal (ash x n)
                  (if (integerp n)
                      (ash x n)
                    (ash x 0)))))

(defthm |(ash 0 n)|
  (equal (ash 0 n)
         0))

(defthm |(ash x 0)|
  (implies (integerp x)
           (equal (ash x 0)
                  x)))

(defthm natp-ash
  (implies (and (<= 0 x) )
           (and (integerp (ash x n))
                (<= 0 (ash x n))))
  :rule-classes :type-prescription)

(SET-DEFAULT-HINTS
     '((NONLINEARP-DEFAULT-HINT++ ID
                                  STABLE-UNDER-SIMPLIFICATIONP HIST NIL)))

(defthm |(< (ash x n) x) --- linear|
  (implies (and (integerp x)
                (< 0 x)
                (integerp n)
                (< n 0))
           (< (ash x n) x)))

(defthm |(< x (ash x n)) --- linear|
  (implies (and (integerp x)
                (< 0 x)
                (integerp n)
                (< 0 n))
           (< x (ash x n))))

(defthm |(< (ash x n) y)|
  (implies (and (integerp x)
                (integerp n)
                (integerp y)
                (< x (floor y (expt 2 n))))
           (< (ash x n) y)))

(defthm |(<= (ash x n) y)|
  (implies (and (integerp x)
                (integerp n)
                (integerp y)
                (<= x (floor y (expt 2 n))))
           (<= (ash x n) y)))

(set-default-hints nil)

(defthm |(ash (ash x n) (- n))|
  (implies (and (integerp x)
                (integerp n)
                (<= 0 n))
           (equal (ash (ash x n) (- n))
                  x)))

(defthm |(integerp (* 1/2 (ash x n)))|
  (implies (and (integerp x)
                (integerp n)
                (< 0 n))
           (integerp (* 1/2 (ash x n)))))

(defthm |(ash (* 2 x) n)|
  (implies (and (integerp x)
                (integerp n))
           (equal (ash (* 2 x) n)
                  (ash x (+ 1 n))))
  :hints (("GOAL" :in-theory (e/d ()
                                  ())
                  :do-not '(generalize eliminate-destructors)
                  :induct (ind-hint-2+ x n))))

(defthm |(equal (ash (mod x c) nn) 0)|
  (implies (and (syntaxp (quotep c))
                (bind-free (p-o-2-g-fn-n c) (n))
                (integerp n)
                (equal (expt 2 n) c)
                (integerp x)
                (integerp nn)
                (<= n nn))
           (equal (ash (mod x c) (- nn))
                  0)))

(defthm |(ash (ash x n1) n2)|
  (and (implies (and (integerp x)
                     (integerp n1)
                     (<= 0 n1)
                     (integerp n2))
                (equal (ash (ash x n1) n2)
                       (ash x (+ n1 n2))))
       (implies (and (integerp x)
                     (integerp n1)
                     (<= n1 0)
                     (integerp n2)
                     (<= n2 0))
                (equal (ash (ash x n1) n2)
                       (ash x (+ n1 n2))))))

(in-theory (disable ash
                    ash-to-floor))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; logand

(defthm break-logand-apart
  (implies (and (natp x)
                (natp y))
           (equal (logand x y)
                  (+ (* 2 (logand (floor x 2)
                                  (floor y 2)))
                     (logand (mod x 2)
                             (mod y 2)))))
  :rule-classes nil)

(defthm break-logand-apart-1
  (implies (and (integerp x)
                (integerp y))
           (equal (logand x y)
                  (+ (* 2 (logand (floor x 2)
                                  (floor y 2)))
                     (logand (mod x 2)
                             (mod y 2)))))
  :otf-flg t
  :rule-classes nil)

(defthm break-logand-apart-n
  (implies (and (integerp x)
                (integerp y)
                (integerp n)
                (<= 0 n))
           (equal (logand x y)
                  (+ (* (expt 2 n)
                        (logand (floor x (expt 2 n))
                                (floor y (expt 2 n))))
                     (logand (mod x (expt 2 n))
                             (mod y (expt 2 n))))))
  :otf-flg t
  :rule-classes nil)

(defthm |(< (logand x y) (expt 2 n))|
  (and (implies (and (integerp x)
                     (<= 0 x)
                     (integerp y)
                     (integerp n)
                     (< 0 n)
                     (< x (expt 2 n)))
                (< (logand x y)
                   (expt 2 n)))
       (implies (and (integerp x)
                     (integerp y)
                     (<= 0 y)
                     (integerp n)
                     (< 0 n)
                     (< y (expt 2 n)))
                (< (logand x y)
                   (expt 2 n)))))

;;; How to easily generalize this, so I don't need an ever expanding
;;; collection of lemmatta?
(defthm |(logand x (lognot x))|
  (equal (logand x (lognot x))
         0)
  :hints (("Goal" :induct (ind-hint+ x))))

(defthm |(logand x (lognot x) y)|
  (equal (logand x (lognot x) y)
         0)
  ;; very irritating type of hint!
  :hints (("Goal" :use ((:instance
                         (:theorem
                          (equal (logand x (lognot x) a)
                                 0))
                         (a y))))))

;;; this was irritatingly hard to push through ACL2
(encapsulate
 ()

 (local
  (defthm crock-1+
    (implies (and (integerp x)
                  (integerp y)
                  (equal x y))
             (equal (ash x 1)
                    (ash y 1)))
    :rule-classes nil))

 (local
  (defthm crock-1-
    (implies (and (integerp x)
                  (integerp y)
                  (equal x y))
             (equal (ash x -1)
                    (ash y -1)))
    :rule-classes nil))

 (local
  (defthm |(ash (logand x y) 1)|
    (equal (ash (logand x y) 1)
           (logand (ash x 1) (ash y 1)))
    :hints (("Goal" :in-theory (enable ash-to-floor)))))

 (local
  (defthm |(ash (logand x y) -1)|
    (equal (ash (logand x y) -1)
           (logand (ash x -1) (ash y -1)))
    :hints (("Goal" :in-theory (enable ash-to-floor)))))

 (local
  (defun ind-hint (n)
    (declare (xargs :measure (abs (ifix n))))
    (cond ((zip n)
           42)
          ((< 0 n)
           (ind-hint (+ -1 n)))
          ((< n 0)
           (ind-hint (+ 1 n))))))

 (defthm |(ash (logand x y) n)|
   (implies (integerp n)
            (equal (ash (logand x y) n)
                   (logand (ash x n) (ash y n))))
   :hints (("GOAL" :in-theory (e/d (zip)
                                   (ash-to-floor))
            :do-not '(generalize)
            :induct (ind-hint n))
           ("Subgoal *1/3"
            :use ((:instance crock-1-
                             (x (LOGAND (ASH X (+ 1 N))
                                        (ASH Y (+ 1 N))))
                             (y (ASH (LOGAND X Y)
                                     (+ 1 N))))))

           ("Subgoal *1/2"
            :use ((:instance crock-1+
                             (x (LOGAND (ASH X (+ -1 N))
                                        (ASH Y (+ -1 N))))
                             (y (ASH (LOGAND X Y)
                                     (+ -1 N))))))
           ))
 )

(defthm |(mod (logand x y) c)|
  (implies (and (syntaxp (quotep c))
                (bind-free (p-o-2-g-fn-n c) (n))
                (integerp n)
                (equal (expt 2 n) c)
                (integerp x)
                (integerp y))
           (equal (mod (logand x y) c)
                  (logand (mod x c) (mod y c)))))

;;; what is the right direction?  Is there one?

(defthm |(logand x (logior y z))|
  (equal (logand x (logior y z))
         (logior (logand x y)
                 (logand x z)))
  :hints (("Goal" :induct (ind-hint-3-0 x y z))))

(defthm |(logand (logior x y) z)|
  (equal (logand (logior x y) z)
         (logior (logand x z)
                 (logand y z))))

;;; These are slighty odd rules, but they were needed in, at least,
;;; Machine/constants.lisp.  Is there a general pattern that we could
;;; use?
(encapsulate
 ()

 (local
  (defthm crock-1
    (implies (and (integerp x)
                  (integerp y)
                  (integerp n)
                  (< 0 n))
             (equal (logand x (mod y (expt 2 n)))
                    (logand (mod x (expt 2 n))
                            (mod y (expt 2 n)))))
    :hints (("Goal" :use ((:instance break-logand-apart-n
                                     (x x)
                                     (y (mod y (expt 2 n)))
                                     (n n))
                          (:instance break-logand-apart-n
                                     (x (mod x (expt 2 n)))
                                     (y (mod y (expt 2 n)))
                                     (n n)))))
    :rule-classes nil))

;;; Do I want this to apply when c and d are not constants?
;;; the final hyp seems unlikey to succeed in that case.
 (defthm |(logand c (mod x d)) = (mod x d)|
   (implies (and (syntaxp (quotep c))
                 (syntaxp (quotep d))
                 (integerp d)
                 (bind-free (p-o-2-g-fn-n d) (n))
                 (integerp n)
                 (< 0 n)
                 (equal (expt 2 n) d)
                 (integerp x)
                 (equal (logand c (+ -1 d))
                        (+ -1 d)))
            (equal (logand c (mod x d))
                   (mod x d)))
   :hints (("Goal" :use ((:instance crock-1
                                    (x c)
                                    (y x)
                                    (n n))))
           ;; what goes wrong if I give this use hint at Goal?
           ("Subgoal 2" :in-theory (disable logand-mask)
            :use ((:instance logand-mask
                             (x (MOD X (EXPT 2 N)))
                             (n n)))))
   :otf-flg t)

 (defthm |(logand c (mod x d)) = 0|
   (implies (and (syntaxp (quotep c))
                 (syntaxp (quotep d))
                 (integerp d)
                 (bind-free (p-o-2-g-fn-n d) (n))
                 (integerp n)
                 (< 0 n)
                 (equal (expt 2 n) d)
                 (integerp x)
                 (equal (logand c (+ -1 d))
                        0))
            (equal (logand c (mod x d))
                   0))
   :hints (("Goal" :use ((:instance crock-1
                                    (x c)
                                    (y x)
                                    (n n))))
           ;; what goes wrong if I give this use hint at Goal?
           ("Subgoal 2" :in-theory (disable logand-mask)
            :use ((:instance logand-mask
                             (x (MOD X (EXPT 2 N)))
                             (n n)))))
   :otf-flg t)

 (local
  (defthm crock-2
    (implies (and (integerp x)
                  (integerp y)
                  (integerp n)
                  (< 0 n))
             (equal (logand x (ash y n))
                    (ash (logand (ash x (- n)) y) n)))
    :hints (("Goal" :in-theory (e/d (ash-to-floor)
                                    (LOGAND-FLOOR-EXPT-2-N
                                     |(ash (logand x y) n)|))
             :use ((:instance break-logand-apart-n
                              (x x)
                              (y (ash y n))
                              (n n)))))
    :rule-classes nil))

 (local
  (defthm crock-3
    (implies (and (integerp x)
                  (integerp y)
                  (integerp n)
                  (< 0 n))
             (equal (equal (ash x n)
                           (ash y n))
                    (equal x y)))
    :hints (("Goal" :in-theory (enable ash-to-floor)))))

 (defthm |(logand c (ash (mod x d) e)) = (ash (mod x d) e)|
   (implies (and (syntaxp (quotep c))
                 (syntaxp (quotep d))
                 (syntaxp (quotep e))
                 (integerp c)
                 (integerp d)
                 (bind-free (p-o-2-g-fn-n d) (n))
                 (integerp n)
                 (< 0 n)
                 (equal (expt 2 n) d)
                 (integerp e)
                 (< 0 e)
                 (integerp x)
                 (equal (logand c (ash (+ -1 d) e))
                        (ash (+ -1 d) e)))
            (equal (logand c (ash (mod x d) e))
                   (ash (mod x d) e)))
   :hints (("Goal" :in-theory (disable |(ash (logand x y) n)|
                                       logand-mask)
            :use ((:instance crock-2
                             (x c)
                             (y (mod x d))
                             (n e))
                  (:instance crock-2
                             (x c)
                             (y (+ -1 d))
                             (n e))
                  (:instance |(ash (logand x y) n)|
                             (x (ASH C (- E)))
                             (y (MOD X (EXPT 2 N)))
                             (n e))
                  (:instance |(logand c (mod x d)) = (mod x d)|
                             (c (ASH C (- E)))
                             (x x)
                             (d (expt 2 n)))
                  )))
   :otf-flg t)

 (local
  (defthm crock-4
    (implies (and (integerp x)
                  (integerp y)
                  (integerp n)
                  (< 0 n))
             (equal (equal (ash x n)
                           0)
                    (equal x 0)))
    :hints (("Goal" :in-theory (enable ash-to-floor)))))

 (defthm |(logand c (ash (mod x d) e)) = 0|
   (implies (and (syntaxp (quotep c))
                 (syntaxp (quotep d))
                 (syntaxp (quotep e))
                 (integerp c)
                 (integerp d)
                 (bind-free (p-o-2-g-fn-n d) (n))
                 (integerp n)
                 (< 0 n)
                 (equal (expt 2 n) d)
                 (integerp e)
                 (< 0 e)
                 (integerp x)
                 (equal (logand c (ash (+ -1 d) e))
                        0))
            (equal (logand c (ash (mod x d) e))
                   0))
   :hints (("Goal" :in-theory (disable |(ash (logand x y) n)|
                                       logand-mask)
            :use ((:instance crock-2
                             (x c)
                             (y (mod x d))
                             (n e))
                  (:instance crock-2
                             (x c)
                             (y (+ -1 d))
                             (n e))
                  (:instance |(ash (logand x y) n)|
                             (x (ASH C (- E)))
                             (y (MOD X (EXPT 2 N)))
                             (n e))
                  (:instance |(logand c (mod x d)) = 0|
                             (c (ASH C (- E)))
                             (x x)
                             (d (expt 2 n)))
                  )))
   :otf-flg t)
 )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; logior

(defthm break-logior-apart
  (implies (and (natp x)
                (natp y))
           (equal (logior x y)
                  (+ (* 2 (logior (floor x 2)
                                  (floor y 2)))
                     (logior (mod x 2)
                             (mod y 2)))))
  :rule-classes nil)

(defthm |(< (logior x y) (expt 2 n))|
  ;; fairly weak as a :linear rule, due to free variable ---
  ;; (logior x y) will be the trigger term
  (implies (and (natp x)
                (natp y)
                (< x (expt 2 n))
                (< y (expt 2 n)))
           (< (logior x y) (expt 2 n)))
  :hints (("GOAL" :induct (ind-hint-3 x y n))
          ("SUBGOAL *1/2.10'4'" :use ((:instance break-logior-apart)))
          ("SUBGOAL *1/2.9'4'" :use ((:instance break-logior-apart)))
          ("SUBGOAL *1/2.6'4'" :use ((:instance break-logior-apart))))
  :rule-classes ((:rewrite)
                 (:linear)))

(defthm |(< (logior x y) c)|
  (implies (and (syntaxp (quotep c))
                (bind-free (p-o-2-g-fn-n c) (n))
                (integerp n)
                (equal (expt 2 n) c)
                (natp x)
                (natp y)
                (< x (expt 2 n))
                (< y (expt 2 n)))
           (< (logior x y) c)))

(encapsulate
 ()

 (local
  (defthm crock-1+
    (implies (and (integerp x)
                  (integerp y)
                  (equal x y))
             (equal (ash x 1)
                    (ash y 1)))
    :rule-classes nil))

 (local
  (defthm crock-1-
    (implies (and (integerp x)
                  (integerp y)
                  (equal x y))
             (equal (ash x -1)
                    (ash y -1)))
    :rule-classes nil))

 (local
  (defthm |(ash (logior x y) 1)|
    (equal (ash (logior x y) 1)
           (logior (ash x 1) (ash y 1)))
    :hints (("Goal" :in-theory (enable ash-to-floor)))))

 (local
  (defthm |(ash (logior x y) -1)|
    (equal (ash (logior x y) -1)
           (logior (ash x -1) (ash y -1)))
    :hints (("Goal" :in-theory (enable ash-to-floor)))))

 (local
  (defun ind-hint (n)
    (declare (xargs :measure (abs (ifix n))))
    (cond ((zip n)
           42)
          ((< 0 n)
           (ind-hint (+ -1 n)))
          ((< n 0)
           (ind-hint (+ 1 n))))))

 (defthm |(ash (logior x y) n)|
   (implies (integerp n)
            (equal (ash (logior x y) n)
                   (logior (ash x n) (ash y n))))
   :hints (("GOAL" :in-theory (e/d (zip)
                                   (ash-to-floor))
            :do-not '(generalize)
            :induct (ind-hint n))
           ("Subgoal *1/3"
            :use ((:instance crock-1-
                             (x (LOGIOR (ASH X (+ 1 N))
                                        (ASH Y (+ 1 N))))
                             (y (ASH (LOGIOR X Y)
                                     (+ 1 N))))))

           ("Subgoal *1/2"
            :use ((:instance crock-1+
                             (x (LOGIOR (ASH X (+ -1 N))
                                        (ASH Y (+ -1 N))))
                             (y (ASH (LOGIOR X Y)
                                     (+ -1 N))))))
           ))
 )

(defthm |(mod (logior x y) c)|
  (implies (and (syntaxp (quotep c))
                (bind-free (p-o-2-g-fn-n c) (n))
                (integerp n)
                (equal (expt 2 n) c)
                (integerp x)
                (integerp y))
           (equal (mod (logior x y) c)
                  (logior (mod x c) (mod y c)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; logxor

(defthm break-logxor-apart
  (implies (and (natp x)
                (natp y))
           (equal (logxor x y)
                  (+ (* 2 (logxor (floor x 2)
                                  (floor y 2)))
                     (logxor (mod x 2)
                             (mod y 2)))))
  :rule-classes nil)

(defthm logxor-greater-or-equal-to-zero
  (implies (and (natp x)
                (natp y))
           (and (integerp (logxor x y))
                (<= 0 (logxor x y))))
  :hints (("GOAL" :induct (ind-hint-2 x y)))
  :rule-classes :type-prescription)

(defthm |(< (logxor x y) (expt 2 n)) --- linear|
  ;; fairly weak as a :linear rule, due to free variable ---
  ;; (logxor x y) will be the trigger term
  (implies (and (natp x)
                (natp y)
                (< x (expt 2 n))
                (< y (expt 2 n)))
           (< (logxor x y) (expt 2 n)))
  :hints (("GOAL" :induct (ind-hint-3 x y n))
          ("SUBGOAL *1/2.6'4'" :use ((:instance break-logxor-apart)))
          ("SUBGOAL *1/2.10'4'" :use ((:instance break-logxor-apart))))
  :rule-classes :linear)

(defthm |(< (logxor x y) c)|
  (implies (and (syntaxp (quotep c))
                (bind-free (p-o-2-g-fn-n c) (n))
                (integerp n)
                (equal (expt 2 n) c)
                (natp x)
                (natp y)
                (< x (expt 2 n))
                (< y (expt 2 n)))
           (< (logxor x y) c)))

(defthm |(logxor (* 2 x) (* 2 y))|
  (implies (and (integerp x)
                (integerp y))
           (equal (logxor (* 2 x) (* 2 y))
                  (* 2 (logxor x y))))
  :hints (("Goal" :use ((:instance |(logxor (floor x 2) (floor y 2))|
                                   (x (* 2 x))
                                   (y (* 2 y)))))))

(encapsulate
 ()

 (local
  (defthm crock-1+
    (implies (and (integerp x)
                  (integerp y)
                  (equal x y))
             (equal (ash x 1)
                    (ash y 1)))
    :rule-classes nil))

 (local
  (defthm crock-1-
    (implies (and (integerp x)
                  (integerp y)
                  (equal x y))
             (equal (ash x -1)
                    (ash y -1)))
    :rule-classes nil))

 (local
  (defthm |(ash (logxor x y) 1)|
    (equal (ash (logxor x y) 1)
           (logxor (ash x 1) (ash y 1)))
    :hints (("Goal" :in-theory (enable ash-to-floor)))))

 (local
  (defthm |(ash (logxor x y) -1)|
    (equal (ash (logxor x y) -1)
           (logxor (ash x -1) (ash y -1)))
    :hints (("Goal" :in-theory (enable ash-to-floor)))))

 (local
  (defun ind-hint (n)
    (declare (xargs :measure (abs (ifix n))))
    (cond ((zip n)
           42)
          ((< 0 n)
           (ind-hint (+ -1 n)))
          ((< n 0)
           (ind-hint (+ 1 n))))))

 (defthm |(ash (logxor x y) n)|
   (implies (integerp n)
            (equal (ash (logxor x y) n)
                   (logxor (ash x n) (ash y n))))
   :hints (("GOAL" :in-theory (e/d (zip)
                                   (ash-to-floor))
            :do-not '(generalize)
            :induct (ind-hint n))
           ("Subgoal *1/3"
            :use ((:instance crock-1-
                             (x (LOGXOR (ASH X (+ 1 N))
                                        (ASH Y (+ 1 N))))
                             (y (ASH (LOGXOR X Y)
                                     (+ 1 N))))))

           ("Subgoal *1/2"
            :use ((:instance crock-1+
                             (x (LOGXOR (ASH X (+ -1 N))
                                        (ASH Y (+ -1 N))))
                             (y (ASH (LOGXOR X Y)
                                     (+ -1 N))))))
           ))
 )

#||
(local
 (defun ind-hint-4+ (x y n c)
   (declare (xargs :measure (abs (ifix n))))
   (cond ((or (zip x) (zip y) (zip n))
          c)
         ((< 0 n)
          (ind-hint-4+ (ash x -1) (ash y -1) (+ -1 n) (* 1/2 c)))
         ((< n 0)
          (ind-hint-4+ (ash x 1) (ash y 1) (+ 1 n) (* 2 c))))))

(defthm |(mod (logxor x y) c)|
  (implies (and (syntaxp (quotep c))
                (bind-free (p-o-2-g-fn-n c) (n))
                (integerp n)
                (equal (expt 2 n) c)
                (integerp x)
                (integerp y))
           (equal (mod (logxor x y) c)
                  (logxor (mod x c) (mod y c))))
  :hints (("Goal" :induct (ind-hint-4+ x y n c))))
||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; lognot

(encapsulate
 ()

 (local
  (defthm |(ash (lognot x) -1)|
    (implies (integerp x)
             (equal (ash (lognot x) -1)
                    (lognot (ash x -1))))
    :hints (("Goal" :in-theory (enable ash-to-floor)))))

 (local
  (defthm crock-1-
    (implies (and (integerp x)
                  (integerp y)
                  (equal x y))
             (equal (ash x -1)
                    (ash y -1)))
    :rule-classes nil))

 (local
  (defun ind-hint (n)
    (declare (xargs :measure (abs (ifix n))))
    (cond ((zip n)
           42)
          ((< 0 n)
           (ind-hint (+ -1 n)))
          ((< n 0)
           (ind-hint (+ 1 n))))))

 ;;; Is there a comparable theorem when shifting by a positive amount?
 (defthm |(ash (lognot x) (- n))|
   (implies (and (integerp x)
                 (integerp n)
                 (<= 0 n))
            (equal (ash (lognot x) (- n))
                   (lognot (ash x (- n)))))
   :hints (("Goal" :induct (ind-hint n))
           ("Subgoal *1/2" :use ((:instance crock-1-
                                            (x (ASH (LOGNOT X) (+ 1 (- N))))
                                            (y (LOGNOT (ASH X (+ 1 (- N))))))))))
 )
