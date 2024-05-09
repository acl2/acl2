; Copyright (C) 2022, Regents of the University of Texas
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(include-book "projects/apply/top" :dir :system)

(defun rev (x)
  (if (endp x)
      nil
      (append (rev (cdr x)) (list (car x)))))

(defthm assoc-of-append
  (equal (append (append a b) c)
         (append a (append b c))))

(thm
  (implies (true-listp lst)
           (equal (loop$ with ans = ans0
                         with lst = xxx
                         do
                         (if (consp lst)
                             (progn (setq ans (cons (car lst) ans))
                                    (setq lst (cdr lst)))
                             (return ans)))
                  (append (rev xxx) ans0))))

; Note that we (unnecessarily) pick up (true-listp lst) as a Q here, and prove
; the formula.
(thm
  (implies (true-listp lst)
           (equal (loop$ with ans = ans0
                         with lst = lst
                         do
                         (if (consp lst)
                             (progn (setq ans (cons (car lst) ans))
                                    (setq lst (cdr lst)))
                             (return ans)))
                  (append (rev lst) ans0)))
  :hints (("Goal" :in-theory (disable (:induction rev) (:induction true-listp)))))

; This works.  And we pick up (true-listp xxx) as Q.
(thm
  (implies (true-listp xxx)
           (equal (loop$ with ans = ans0
                         with lst = xxx
                         do
                         (if (consp lst)
                             (progn (setq ans (cons (car lst) ans))
                                    (setq lst (cdr lst)))
                             (return ans)))
                  (append (rev xxx) ans0)))
  :hints (("Goal" :in-theory (disable (:induction rev) (:induction true-listp)))))

; This proves.  We pick (natp iii) as Q.
(thm
  (implies (natp iii)
           (equal (loop$ with iii = iii
                         do
                         (if (equal iii 0)
                             (return 'silly)
                             (setq iii (- iii 1))))
                  'silly)))

; This works.  But we do not automatically choose Q when there is an induct hint.
; So we have to make sure the induct hint includes it, which means if the induct
; hint is a do loop$ we need to modify its body to include the q.

(thm
 (implies (natp iii)
          (equal (loop$ with iii = iii
                        do
                        (if (equal iii 0)
                            (return 'silly)
                            (setq iii (- iii 1))))
                 'silly))
 :hints (("Goal" :induct (loop$ with iii = iii
                                do
                                (if (natp iii)  ; <--- modified do loop as hint!
                                    (if (equal iii 0)
                                        (return 'silly)
                                        (setq iii (- iii 1)))
                                    (return 'dumb))))))

; This works.  We choose Q correctly.
(thm
 (implies (and (natp iii)
               (natp nnn))
          (equal (loop$ with i = iii
                        with n = nnn
                        do
                        :guard (and (natp i) (natp n))
                        :measure (nfix (- n i))
                        (if (< i n)
                            (setq i (+ i 1))
                            (return t)))
                 t))
 :otf-flg t)

; This works and we choose Q correctly.
(thm
 (implies (and (natp iii)
               (natp nnn))
          (equal (loop$ with i = iii
                        with n = nnn
                        do
                        :guard (and (natp i) (natp n))
                        :measure (nfix (- n i))
                        (if (< i n)
                            (setq i (+ i 1))
                            (return t)))
                 t))
 :hints (("Goal" :induct t)))

; This works.  We choose (natp iii) for Q.
(thm
 (implies (natp iii)
          (equal (loop$ with i = iii
                        with n = 10
                        do
                        :guard  (and (natp n) (natp i))
                        :measure (nfix (- n i))
                        (if (< i n)
                            (setq i (+ i 1))
                            (return t)))
                 t)))

; This works.  It tests the ability to do a true (:induction do$) induction
; rather than semi-concrete one.

(thm (implies (and (natp (cdr (assoc-eq-safe 'n alist)))
                   (natp (cdr (assoc-eq-safe 'm alist))))
              (equal
               (do$ (lambda$ (alist) (acl2-count (cdr (assoc-eq-safe 'n alist))))
                    alist
                    (lambda$ (alist)
                             (if (zp (cdr (assoc-eq-safe 'n alist)))
                                 (list :return (cdr (assoc-eq-safe 'm alist)) alist)
                                 (list nil nil
                                       (list (cons 'n (- (cdr (assoc-eq-safe 'n alist)) 1))
                                             (cons 'm (+ (cdr (assoc-eq-safe 'm alist)) 1))))))
                    (lambda$ (alist)
                             (list nil nil 
                                   (list (cons 'n (cdr (assoc-eq-safe 'n alist))))))
                    nil nil nil)
               (+ (cdr (assoc-eq-safe 'n alist))
                  (cdr (assoc-eq-safe 'm alist))))))


(defun rev1 (x ac)
  (if (endp x)
      ac
      (rev1 (cdr x) (cons (car x) ac))))

(thm
  (equal (loop$ with x = lst
                with ans = ans0
                do
                (if (consp x)
                    (progn (setq ans (cons (car x) ans))
                           (setq x (cdr x)))
                    (return ans)))
         (rev1 lst ans0)))

; Write a do loop$ that computes (member e lst) and prove it correct.

(thm
  (equal (loop$ with x = lst
                do
                (if (consp x)
                    (if (equal (car x) e)
                        (return x)
                        (setq x (cdr x)))
                    (return nil)))
         (member e lst)))

(thm
  (implies (natp ans0)
           (equal (loop$ with x = lst
                         with ans = ans0
                         do
                         (if (consp x)
                             (progn (setq ans (+ 1 ans))
                                    (setq x (cdr x)))
                             (return ans)))
                  (+ ans0 (len lst)))))

(thm
  (implies (natp n)
           (equal (loop$ with x = lst
                         with i = n
                         do
                         (cond ((endp x) (return nil))
                               ((equal i 0) (return (car x)))
                               (t (progn (setq i (- i 1))
                                         (setq x (cdr x))))))
                  (nth n lst))))

(thm
  (implies (and (true-listp ans0)
                (true-listp lst))
           (equal (loop$ with x = lst
                         with ans = ans0
                         do
                         (if (consp x)
                             (progn (setq ans (append ans (list (car x))))
                                    (setq x (cdr x)))
                             (return ans)))
                  (append ans0 lst)))
  :hints (("Goal" :in-theory (disable (:induction binary-append)))))


(thm
  (implies (and (natp m)
                (natp n))
           (equal (loop$ with i = m
                         with j = n
                         do
                         (if (integerp i)
                             (if (< 0 i)
                                 (progn (setq i (- i 1))
                                        (setq j (+ 1 j)))
                                 (return j))
                             (return j)))
                  (+ m n))))

(defun fact (n)
  (if (zp n)
      1
      (* n (fact (- n 1)))))

(defthm commutivity-2-of-*
  (equal (* a (* b c)) (* b (* a c)))
  :hints
  (("Goal" :use ((:instance commutativity-of-*
                            (x a)(y (* b c)))))))

(thm
 (implies (and (natp n)
               (natp ans0))
          (equal (loop$ with i = n
                        with ans = ans0
                        do
                        (if (integerp i)
                            (if (< 0 i)
                                (progn (setq ans (* i ans))
                                       (setq i (- i 1)))
                                (return ans))
                            (return ans)))
                 (* ans0 (fact n)))))

(defun sq (x) (* x x))
(defwarrant sq)

(thm
  (implies (and (warrant sq)
                (integer-listp lst0)
                (integerp u0)
                (integerp v0))
           (equal (loop$ with lst = lst0
                         with u = u0
                         with v = v0
                         do
                         (cond ((consp lst)
                                (progn (setq u (+ u (car lst)))
                                       (setq v (+ v (* (car lst) (car lst))))
                                       (setq lst (cdr lst))))
                               (t (return (cons u v)))))
                  (cons (+ u0 (loop$ for e in lst0 sum e))
                        (+ v0 (loop$ for e in lst0 sum (sq e)))))))

(thm
  (equal (loop$ with lst = lst
                with syms = syms
                with non-syms = non-syms
                do
                (cond ((consp lst)
                       (cond
                        ((symbolp (car lst))
                         (progn (setq syms (cons (car lst) syms))
                                (setq lst (cdr lst))))
                        (t
                         (progn (setq non-syms (cons (car lst) non-syms))
                                (setq lst (cdr lst))))))
                      (t (return (cons syms non-syms)))))
         (cons (append (rev (loop$ for e in lst when (symbolp e) collect e))
                       syms)
               (append (rev (loop$ for e in lst when (not (symbolp e)) collect e))
                       non-syms))))

(defun nats-ac-up (i n ans)
  (declare (xargs :measure (nfix (- (+ 1 (nfix n)) (nfix i)))))
  (let ((i (nfix i))
        (n (nfix n)))
    (if (> i n)
        ans
        (nats-ac-up (+ i 1) n (cons i ans)))))

(thm
 (implies (and (natp n)
               (natp i0))
          (equal 
           (loop$ with i = i0
                  with ans = ans0
                  do
                  :measure (nfix (+ 1 (- i) n))
		  (if (< n i)
                      (return ans)
                      (progn (setq ans (cons i ans))
                             (setq i (+ 1 i)))))
           (nats-ac-up i0 n ans0))))

(defun make-pair (i j)
  (declare (xargs :guard t))
  (cons i j))

(defwarrant make-pair)

(defun apdh2 (i j ans)
  (cond
   ((natp j)
    (cond ((< j 1) ans)
          (t (apdh2 i (- j 1) (cons (make-pair i j) ans)))))
   (t nil)))

(defun apdh1 (i jmax ans)
  (cond
   ((natp i)
    (cond ((< i 1) ans)
          (t (apdh1 (- i 1) jmax (apdh2 i jmax ans)))))
   (t nil)))

(defthm lemma1
  (implies (natp jmax)                              ; <--- no warrant req'd
           (equal                                   ;      because no make-
            (loop$ with j = jmax                    ;      pair anymore
                   with ans = ans0
                   do
                   :guard (natp j)
                   (cond
                    ((< j 1)
                     (return ans))
                    (t (progn
                         (setq ans (cons (cons i j) ; <--- make-pair opened
                                         ans))
                         (setq j (- j 1))))))
            (apdh2 i jmax ans0))))

; Prove that the generalized outer loop$ is apdh1.
(thm
  (implies
   (and (warrant do$)                             ; <--- no warrant make-pair
        (natp imax)
        (natp jmax))
   (equal
    (loop$ with i = imax
           with ans = ans0                        ; <--- ans0 instead of nil
           do
           :guard (and (natp i) (natp jmax))
           (cond
            ((< i 1)
             (return ans))
            (t (progn
                 (setq ans (loop$ with j = jmax   ; <--- normalized inner
                                  with ans = ans  ;      loop$
                                  do
                                  :guard (natp j)
                                  (cond
                                   ((< j 1)
                                    (return ans))
                                   (t (progn
                                        (setq ans (cons (cons i j) ans))
                                        (setq j (- j 1)))))))
                 (setq i (- i 1))))))
    (apdh1 imax jmax ans0))))







