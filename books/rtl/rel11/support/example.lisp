(in-package "RTL")

; Includes tweaks made by Mihir Mehta 4/2019 for a change to the
; definition of take.

(include-book "newton")
(include-book "rcp")
(local (include-book "bits"))
(local (include-book "float"))
(local (include-book "round"))
(local (include-book "reps"))

(local (include-book "arithmetic-5/top" :dir :system))

;; The following lemmas from arithmetic-5 have given me trouble:
#|
(local (in-theory #!acl2(disable |(mod (+ x y) z) where (<= 0 z)| |(mod (+ x (- (mod a b))) y)| |(mod (mod x y) z)| |(mod (+ x (mod a b)) y)|
                    simplify-products-gather-exponents-equal mod-cancel-*-const cancel-mod-+ reduce-additive-constant-<
                    |(floor x 2)| |(equal x (if a b c))| |(equal (if a b c) x)|)))
|#

(local-defthm formatp-sp
  (formatp (sp))
  :hints (("Goal" :in-theory (enable sp))))

(defun check-mant (m)
  (let* ((b (1+ (/ m (expt 2 23))))
         (y (rcp24 b)))
    (and (<= 1/2 y)
         (<= y 1)
	 (exactp y 24)
         (< (abs (- 1 (* b y))) (expt 2 -23)))))

(defun check-mants (m)
  (if (zp m)
      t
    (and (check-mant (1- m))
         (check-mants (1- m)))))

(comp t)

(defthm check-mants-lemma
  (check-mants #x800000))

(local-in-theory (disable check-mant (check-mant) rcp24 (rcp24)))

(local-defthm cf-1
  (implies (and (natp n)
                (natp m)
                (< m n)
                (check-mants n))
           (check-mant m))
  :rule-classes ())

(local-in-theory (disable check-mants (check-mants)))

(local-defthm cf-2
  (implies (and (natp m)
                (< m #x800000))
           (check-mant m))
  :hints (("Goal" :use (check-mants-lemma
                        (:instance cf-1 (n #x800000))))))

(local-defun mant (b) (* #x800000 (1- b)))

(local-defthm me-2
  (implies (and (rationalp b)
                (exactp b 24)
                (<= 1 b)
                (< b 2))
           (and (natp (mant b))
                (< (mant b) #x800000)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable exactp2))))

(local-defthm me-4
  (implies (rationalp b)
           (equal (1+ (/ (mant b) (expt 2 23)))
                  b)))

(local-defthmd me-5
  (implies (and (rationalp b)
                (exactp b 24)
                (<= 1 b)
                (< b 2)
                (check-mant (mant b)))
           (and (exactp (rcp24 b) 24)
                (<= 1/2 (rcp24 b))
                (<= (rcp24 b) 1)
                (< (abs (- 1 (* b (rcp24 b)))) (expt 2 -23))))
  :hints (("Goal" :use (me-4) :in-theory '(check-mant))))

(local-in-theory (disable mant (mant) rcp24 (rcp24)))

(defthm rcp24-spec
  (implies (and (rationalp b)
                (exactp b 24)
                (<= 1 b)
                (< b 2))
           (and (exactp (rcp24 b) 24)
                (<= 1/2 (rcp24 b))
                (<= (rcp24 b) 1)
                (< (abs (- 1 (* b (rcp24 b)))) (expt 2 -23))))
  :rule-classes ()
  :hints (("Goal" :use (me-5 me-2))))

(encapsulate ()

(local-defund y0 (b) (rcp24 b))
(local-defund q0 (a b) (rne (* a (y0 b)) 24))
(local-defund e0 (b) (rne (- 1 (* b (y0 b))) 24))
(local-defund r0 (a b) (rne (- a (* b (q0 a b))) 24))
(local-defund y1 (b) (rne (+ (y0 b) (* (e0 b) (y0 b))) 24))
(local-defund q1 (a b) (rne (+ (q0 a b) (* (r0 a b) (y1 b))) 24))
(local-defund r1 (a b) (rne (- a (* b (q1 a b))) 24))
(local-defund quot (a b mode) (rnd (+ (q1 a b) (* (r1 a b) (y1 b))) mode 24))

(local-defun phi (e) (+ e (/ (1+ e) (expt 2 24))))

(local-defun eps0 () (expt 2 -23))

(local-defun eps1p () (* (eps0) (phi (eps0))))

(local-defun eps1 () (phi (eps1p)))

(local-defund y1p (b) (+ (y0 b) (* (e0 b) (y0 b))))

(local-defun d () (cg (* (expt 2 48) (eps1p))))

;;(= (d) 7)
;;If we used the tighter bound 64927/549755813888 for eps0, we would have (= (d) 6).

(local-defthm sp-1
  (implies (and (rationalp b)
                (<= 1 b)
                (< b 2)
                (exactp b 24))
           (<= (abs (- 1 (* b (y0 b)))) (eps0)))
  :rule-classes ()
  :hints (("Goal" :use (rcp24-spec)
                  :in-theory (enable y0))))

(local-defthm sp-2
  (implies (and (rationalp b)
                (<= 1 b)
                (< b 2)
                (exactp b 24))
           (<= (abs (- 1 (* b (y1p b)))) (eps1p)))
  :rule-classes ()
  :hints (("Goal" :use (sp-1
                        (:instance recip-refinement-1 (y1 (y0 b))(p 24)  (y2 (y0 b)) (ep1 (eps0)) (ep2 (eps0))))
                  :in-theory (enable y1 y1p e0))))

(local-defthm sp-3
  (implies (and (rationalp b)
                (<= 1 b)
                (< b 2)
                (exactp b 24))
           (<= (abs (- 1 (* b (y1 b)))) (eps1)))
  :rule-classes ()
  :hints (("Goal" :use (sp-1
                        (:instance recip-refinement-2 (y1 (y0 b))(p 24)  (y2 (y0 b)) (ep1 (eps0)) (ep2 (eps0))))
                  :in-theory (enable y1 y1p e0))))

(local-defthm excp-cases
  (implies (member b (h-excps (d) 24))
           (< (abs (- 1 (* b (y1 b)))) (expt 2 -24)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable h-excps))))

(local-in-theory (disable (h-excps)))

(local-defthm sp-4
  (implies (and (rationalp b)
                (<= 1 b)
                (< b 2)
                (exactp b 24))
           (< (abs (- 1 (* b (y1 b)))) (expt 2 -24)))
  :rule-classes ()
  :hints (("Goal" :use (sp-2 excp-cases
                        (:instance harrison-lemma (yp (y1p b)) (ep (eps1p)) (p 24)))
                  :in-theory (enable y1 y1p e0))))

(local-defun del0 () (phi (eps0)))

(local-defthm sp-5
  (implies (and (rationalp a)
                (rationalp b)
                (<= 1 a)
                (< a 2)
                (<= 1 b)
                (< b 2)
                (exactp a 24)
                (exactp b 24))
           (<= (abs (- 1 (* (/ b a) (q0 a b)))) (del0)))
  :rule-classes ()
  :hints (("Goal" :use (sp-1
                        (:instance init-approx (y (y0 b)) (ep (eps0)) (p 24)))
                  :in-theory (enable q0))))

(local-defthm sp-6
  (implies (and (rationalp a)
                (rationalp b)
                (<= 1 a)
                (< a 2)
                (<= 1 b)
                (< b 2)
                (exactp a 24)
                (exactp b 24))
           (< (abs (- (q1 a b) (/ a b)))
              (expt 2 (if (> a b) -23 -24))))
  :rule-classes ()
  :hints (("Goal" :use (sp-3 sp-5
                        (:instance quotient-refinement-2 (p 24) (y (y1 b)) (q0 (q0 a b)) (ep (eps1)) (de (del0))))
                  :in-theory (enable q1 r0))))

(local-defthm sp-7
  (implies (and (rationalp a)
                (rationalp b)
                (<= 1 a)
                (< a 2)
                (<= 1 b)
                (< b 2)
                (exactp a 24)
                (exactp b 24))
           (exactp (- a (* b (q1 a b))) 24))
  :rule-classes ()
  :hints (("Goal" :use (sp-4 sp-6
                        (:instance r-exactp (p 24) (q (q1 a b))))
                  :in-theory (enable q1 r0))))

(local-defthm sp-8
  (implies (and (rationalp a)
                (rationalp b)
                (<= 1 a)
                (< a 2)
                (<= 1 b)
                (< b 2)
                (exactp a 24)
                (exactp b 24))
           (equal (r1 a b) (- a (* b (q1 a b)))))
  :hints (("Goal" :use (sp-7
                        (:instance rne-exactp-b (x (- a (* b (q1 a b)))) (n 24)))
                  :in-theory (enable r1))))

(local-defthm sp-9
  (implies (and (rationalp a)
                (rationalp b)
                (<= 1 a)
                (< a 2)
                (<= 1 b)
                (< b 2)
                (exactp a 24)
                (exactp b 24))
           (exactp (q1 a b) 24))
  :hints (("Goal" :in-theory (enable q1))))

(local-defthm sp-10
  (implies (and (rationalp a)
                (rationalp b)
                (<= 1 a)
                (< a 2)
                (<= 1 b)
                (< b 2)
                (exactp a 24)
                (exactp b 24)
                (ieee-rounding-mode-p mode))
           (= (quot a b mode) (rnd (/ a b) mode 24)))
  :rule-classes ()
  :hints (("Goal" :use (sp-4 sp-6 sp-7
                        (:instance markstein-lemma  (p 24) (q (q1 a b)) (y (y1 b))))
                  :in-theory (enable quot))))

(defund divsp (a b mode)
  (let* ((y0 (rcp24 b))
         (q0 (rne (* a y0) 24))
         (e0 (rne (- 1 (* b y0)) 24))
         (r0 (rne (- a (* b q0)) 24))
         (y1 (rne (+ y0 (* e0 y0)) 24))
         (q1 (rne (+ q0 (* r0 y1)) 24))
         (r1 (rne (- a (* b q1)) 24)))
    (rnd (+ q1 (* r1 y1)) mode 24)))

(local-defthm sp-11
  (= (divsp a b mode)
     (quot a b mode))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable divsp y0 q0 e0 r0 y1 q1 r1 quot))))

(defthm divsp-correct
  (implies (and (rationalp a)
                (rationalp b)
                (<= 1 a)
                (< a 2)
                (<= 1 b)
                (< b 2)
                (exactp a 24)
                (exactp b 24)
                (ieee-rounding-mode-p mode))
           (= (divsp a b mode) (rnd (/ a b) mode 24)))
  :rule-classes ()
  :hints (("Goal" :use (sp-10 sp-11))))

)

(local-defthm rcp-6
  (implies (and (rationalp b)
                (rationalp x)
                (<= 1 b)
                (< b 2))
           (<= (abs (* x (rcp24 (rtz b 24))))
               (abs x)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rcp24-spec (b (rtz b 24)))
                        (:instance rtz-upper-pos (x b) (n 24))
                        (:instance rtz-exactp-c (a 1) (x b) (n 24))))))

(local-defthm rcp-8
  (implies (and (rationalp b)
                (<= 1 b)
                (< b 2))
           (and (<= 1 (rtz b 24))
                (< (rtz b 24) 2)
                (<= (abs (- 1 (* (rtz b 24) (rcp24 (rtz b 24))))) (expt 2 -23))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rcp24-spec (b (rtz b 24)))
                        (:instance rtz-upper-pos (x b) (n 24))
                        (:instance rtz-exactp-c (a 1) (x b) (n 24))))))

(local-defthm rcp-9
  (implies (and (rationalp b)
                (<= 1 b)
                (< b 2))
           (<= (abs (- (* (rtz b 24) (rcp24 (rtz b 24)))
                       (* b (rcp24 (rtz b 24)))))
               (abs (- (rtz b 24) b))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rcp24-spec (b (rtz b 24)))
                        (:instance rcp-6 (x (- (rtz b 24) b)))))))

(local-defthm rcp-10
  (implies (and (rationalp b)
                (<= 1 b)
                (< b 2))
           (<= (abs (- (* (rtz b 24) (rcp24 (rtz b 24)))
                       (* b (rcp24 (rtz b 24)))))
               (expt 2 -23)))
  :rule-classes ()
  :hints (("Goal" :use (rcp-9
                        (:instance rtz-diff (x b) (n 24))
                        (:instance expo<= (x b) (n 0))
                        (:instance expo>= (x b) (n 0))))))

(local-defthm rcp-11
  (implies (and (rationalp x)
                (rationalp y)
                (rationalp a)
                (<= (abs (- x y)) a)
                (<= (abs (- 1 x)) a))
           (<= (abs (- 1 y)) (+ a a)))
  :rule-classes ())

(local-defthm rcp-12
  (implies (and (rationalp b)
                (rationalp (expt 2 -23))
                (rationalp (rtz b 24))
                (exactp (rtz b 24) 24)
                (rationalp (* (rtz b 24) (rcp24 (rtz b 24))))
                (rationalp (* b (rcp24 (rtz b 24))))
                (<= 1 b)
                (< b 2))
           (<= (abs (- 1 (* b (rcp24 (rtz b 24))))) (+ (expt 2 -23) (expt 2 -23))))
  :rule-classes ()
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (rcp-8 rcp-10
                        (:instance rcp-11 (a (expt 2 -23)) (x (* (rtz b 24) (rcp24 (rtz b 24)))) (y (* b (rcp24 (rtz b 24)))))
                        (:instance rcp24-spec (b (rtz b 24)))))))

(defthm rcp24-rtz-error
  (implies (and (rationalp b)
                (<= 1 b)
                (< b 2))
           (<= (abs (- 1 (* b (rcp24 (rtz b 24))))) (expt 2 -22)))
  :rule-classes ()
  :hints (("Goal" :use (rcp-12))))

(local-defund y0 (b) (rcp24 (rtz b 24)))
(local-defund q0 (a b) (rne (* a (y0 b)) 53))
(local-defund e0 (b) (rne (- 1 (* b (y0 b))) 53))
(local-defund r0 (a b) (rne (- a (* b (q0 a b))) 53))
(local-defund y1 (b) (rne (+ (y0 b) (* (e0 b) (y0 b))) 53))
(local-defund e1 (b) (rne (- 1 (* b (y1 b))) 53))
(local-defund y2 (b) (rne (+ (y0 b) (* (e0 b) (y1 b))) 53))
(local-defund q1 (a b) (rne (+ (q0 a b) (* (r0 a b) (y1 b))) 53))
(local-defund y3 (b) (rne (+ (y1 b) (* (e1 b) (y2 b))) 53))
(local-defund r1 (a b) (rne (- a (* b (q1 a b))) 53))
(local-defund quot (a b mode) (rnd (+ (q1 a b) (* (r1 a b) (y3 b))) mode 53))

(local-defun eps0 () (expt 2 -22))

(local-defun phi (e) (+ e (/ (1+ e) (expt 2 53))))

(local-defun eps1p () (* (eps0) (phi (eps0))))

(local-defun eps1 () (phi (eps1p)))

(local-defun eps2p () (* (eps0) (phi (eps1))))

(local-defun eps2 () (phi (eps2p)))

(local-defun eps3p () (* (eps1) (phi (eps2))))

(local-defund y3p (b) (+ (y1 b) (* (e1 b) (y2 b))))

(local-defun d () (cg (* (expt 2 106) (eps3p))))

;;(= (d) 1027)

(local-defun del0 () (phi (eps0)))

(local-defthm dp-1
  (implies (and (rationalp b)
                (<= 1 b)
                (< b 2))
           (<= (abs (- 1 (* b (y0 b)))) (eps0)))
  :rule-classes ()
  :hints (("Goal" :use (rcp24-rtz-error)
                  :in-theory (enable y0))))

(local-defthm dp-2
  (implies (and (rationalp b)
                (<= 1 b)
                (< b 2)
                (exactp b 53))
           (<= (abs (- 1 (* b (y1 b)))) (eps1)))
  :rule-classes ()
  :hints (("Goal" :use (dp-1
                        (:instance recip-refinement-2 (y1 (y0 b)) (p 53) (y2 (y0 b)) (ep1 (eps0)) (ep2 (eps0))))
                  :in-theory (enable y1 e0))))

(local-defthm dp-3
  (implies (and (rationalp b)
                (<= 1 b)
                (< b 2)
                (exactp b 53))
           (<= (abs (- 1 (* b (y2 b)))) (eps2)))
  :rule-classes ()
  :hints (("Goal" :use (dp-1 dp-2
                        (:instance recip-refinement-2 (y1 (y0 b)) (p 53) (y2 (y1 b)) (ep1 (eps0)) (ep2 (eps1))))
                  :in-theory (enable y2 e0))))

(local-defthm dp-4
  (implies (and (rationalp b)
                (<= 1 b)
                (< b 2)
                (exactp b 53))
           (<= (abs (- 1 (* b (y3p b)))) (eps3p)))
  :rule-classes ()
  :hints (("Goal" :use (dp-2 dp-3
                        (:instance recip-refinement-1 (y1 (y1 b)) (p 53) (y2 (y2 b)) (ep1 (eps1)) (ep2 (eps2))))
                  :in-theory (enable y3p e1))))

; Added by Matt K., 2/23/2015:

; The following events allow the proof of excp-cases below to go through
; without needing to call set-rewrite-stack-limit.  We found that Allegro CL
; 9.0 goes out to lunch, even with (set-rewrite-stack-limit 10000) and also
; with (comp t) here.  This is reminiscent of the "snorkeling" used by J Moore
; in his application of codewalker.

(local (defconst *mem-open-len* 50)) ; other values work too

(local
 (encapsulate
  ()

  (local-defthm member-revappend
    (iff (member-equal a (revappend x y))
         (or (member-equal a x)
             (member-equal a y)))
    :hints (("Goal" :induct (revappend x y))))

  (local-defthm member-open-1-lemma
    (implies (and (natp n)
                  (<= n (len lst)))
             (iff (member-equal a lst)
                  (or (member-equal a (take n lst))
                      (member-equal a (nthcdr n lst)))))
    :hints (("Goal" :induct (take n lst)))
    :rule-classes nil)

  (defthm member-open-1
    (implies (and (syntaxp (and (quotep lst)
                                (> (len (acl2::unquote lst)) *mem-open-len*)))
                  (<= *mem-open-len* (len lst)))
             (iff (member-equal a lst)
                  (or (member-equal a (take *mem-open-len* lst))
                      (member-equal a (nthcdr *mem-open-len* lst)))))
    :hints (("Goal" :use ((:instance member-open-1-lemma
                                     (n *mem-open-len*)
                                     (lst lst))))))
))

(local-defthm member-open-2
  (implies (syntaxp (and (quotep lst)
                         (<= (len (acl2::unquote lst)) *mem-open-len*)))
           (equal (member-equal a lst)
                  (cond ((endp lst) nil)
                        ((equal a (car lst))
                         lst)
                        (t (member-equal a (cdr lst)))))))

(local (in-theory (disable member-equal)))

(local-defthm excp-cases
  (implies (member b (h-excps (d) 53))
           (< (abs (- 1 (* b (y3 b)))) (expt 2 -53)))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable h-excps))))

(local-defthm divdp-small-cases-1
  (implies (and (not (zp k))
                (<= k 1027))
           (let ((b (- 2 (* (expt 2 -52) k))))
             (member b (h-excps (d) 53))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable bvecp h-excps d)
                  :use ((:instance bvecp-member (x k) (n 11))))))

(local-in-theory (disable (h-excps)))

(defthm divdp-small-cases
  (implies (and (not (zp k))
                (<= k 1027))
           (let* ((b (- 2 (* (expt 2 -52) k)))
                  (y0 (rcp24 (rtz b 24)))
                  (e0 (rne (- 1 (* b y0)) 53))
                  (y1 (rne (+ y0 (* e0 y0)) 53))
                  (e1 (rne (- 1 (* b y1)) 53))
                  (y2 (rne (+ y0 (* e0 y1)) 53))
                  (y3 (rne (+ y1 (* e1 y2)) 53)))
             (< (abs (- 1 (* b y3)))
                (expt 2 -53))))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable y0 e0 y1 e1 y2 y3)
           :use (divdp-small-cases-1
                 (:instance excp-cases (b (- 2 (* (expt 2 -52) k))))))))

(local-defthm dp-5
  (implies (and (rationalp b)
                (<= 1 b)
                (< b 2)
                (exactp b 53))
           (< (abs (- 1 (* b (y3 b)))) (expt 2 -53)))
  :rule-classes ()
  :hints (("Goal" :use (dp-4 excp-cases
                        (:instance harrison-lemma (yp (y3p b)) (ep (eps3p)) (p 53)))
                  :in-theory (enable y3 y3p e1))))

(local-defun del0 () (phi (eps0)))

(local-defthm dp-6
  (implies (and (rationalp a)
                (rationalp b)
                (<= 1 a)
                (< a 2)
                (<= 1 b)
                (< b 2)
                (exactp a 53)
                (exactp b 53))
           (<= (abs (- 1 (* (/ b a) (q0 a b)))) (del0)))
  :rule-classes ()
  :hints (("Goal" :use (dp-1
                        (:instance init-approx (y (y0 b)) (ep (eps0)) (p 53)))
                  :in-theory (enable q0))))

(local-defthm dp-7
  (implies (and (rationalp a)
                (rationalp b)
                (<= 1 a)
                (< a 2)
                (<= 1 b)
                (< b 2)
                (exactp a 53)
                (exactp b 53))
           (< (abs (- (q1 a b) (/ a b)))
              (expt 2 (if (> a b) -52 -53))))
  :rule-classes ()
  :hints (("Goal" :use (dp-6 dp-2
                        (:instance quotient-refinement-2 (p 53) (y (y1 b)) (q0 (q0 a b)) (ep (eps1)) (de (del0))))
                  :in-theory (enable q1 r0))))

(local-defthm dp-8
  (implies (and (rationalp a)
                (rationalp b)
                (<= 1 a)
                (< a 2)
                (<= 1 b)
                (< b 2)
                (exactp a 53)
                (exactp b 53))
           (exactp (- a (* b (q1 a b))) 53))
  :rule-classes ()
  :hints (("Goal" :use (dp-7
                        (:instance r-exactp (p 53) (q (q1 a b))))
                  :in-theory (enable q1 r0))))

(local-defthm dp-9
  (implies (and (rationalp a)
                (rationalp b)
                (<= 1 a)
                (< a 2)
                (<= 1 b)
                (< b 2)
                (exactp a 53)
                (exactp b 53))
           (equal (r1 a b) (- a (* b (q1 a b)))))
  :hints (("Goal" :use (dp-8
                        (:instance rne-exactp-b (x (- a (* b (q1 a b)))) (n 53)))
                  :in-theory (enable r1))))

(local-defthm dp-10
  (implies (and (rationalp a)
                (rationalp b)
                (<= 1 a)
                (< a 2)
                (<= 1 b)
                (< b 2)
                (exactp a 53)
                (exactp b 53))
           (exactp (q1 a b) 53))
  :hints (("Goal" :in-theory (enable q1))))

 (local-defthm dp-11
  (implies (and (rationalp a)
                (rationalp b)
                (<= 1 a)
                (< a 2)
                (<= 1 b)
                (< b 2)
                (exactp a 53)
                (exactp b 53)
                (ieee-rounding-mode-p mode))
           (= (quot a b mode) (rnd (/ a b) mode 53)))
  :rule-classes ()
  :hints (("Goal" :use (dp-5 dp-7 dp-8
                        (:instance markstein-lemma  (p 53) (q (q1 a b)) (y (y3 b))))
                  :in-theory (enable quot))))

(defund divdp (a b mode)
  (let* ((y0 (rcp24 (rtz b 24)))
         (q0 (rne (* a y0) 53))
         (e0 (rne (- 1 (* b y0)) 53))
         (r0 (rne (- a (* b q0)) 53))
         (y1 (rne (+ y0 (* e0 y0)) 53))
         (e1 (rne (- 1 (* b y1)) 53))
         (y2 (rne (+ y0 (* e0 y1)) 53))
         (q1 (rne (+ q0 (* r0 y1)) 53))
         (y3 (rne (+ y1 (* e1 y2)) 53))
         (r1 (rne (- a (* b q1)) 53)))
    (rnd (+ q1 (* r1 y3)) mode 53)))

(local-defthm dp-12
  (= (divdp a b mode)
     (quot a b mode))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable divdp y0 q0 e0 r0 y1 e1 y2 q1 y3 r1 quot))))

(defthm divdp-correct
  (implies (and (rationalp a)
                (rationalp b)
                (<= 1 a)
                (< a 2)
                (<= 1 b)
                (< b 2)
                (exactp a 53)
                (exactp b 53)
                (ieee-rounding-mode-p mode))
           (= (divdp a b mode) (rnd (/ a b) mode 53)))
  :rule-classes ()
  :hints (("Goal" :use (dp-12 dp-11))))
