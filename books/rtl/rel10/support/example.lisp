(in-package "ACL2")

(include-book "newton")

(include-book "rcp")

(defun rcp24 (b)
  (ndecode (frcp (nencode b 24 8)) 24 8))

(defun check-mant (m)
  (let* ((enc (cat #x7F 9 m 23))
         (b (ndecode enc 24 8))
         (y (ndecode (frcp enc) 24 8)))
    (and (<= y 1)
         (> y 1/2)
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

(local-in-theory (disable check-mant (check-mant) frcp (frcp)))

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

(local-defthmd me-3
  (implies (and (rationalp b)
                (exactp b 24)
                (<= 1 b)
                (< b 2))
           (equal (nencode b 24 8)
                  (cat #x7F 9 (mant b) 23)))
  :hints (("Goal" :in-theory (enable sig sgn nencode)
                  :use ((:instance expo<= (x b) (n 0))
                        (:instance expo>= (x b) (n 0))))))

(local-defthm me-4
  (implies (and (rationalp b)
                (exactp b 24)
                (<= 1 b)
                (< b 2))
           (nrepp b 24 8))
  :hints (("Goal" :in-theory (enable nrepp)
                  :use ((:instance expo<= (x b) (n 0))
                        (:instance expo>= (x b) (n 0))))))

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
  :hints (("Goal" :in-theory (e/d (me-3 check-mant) (mant ndecode-nencode))
                  :use ((:instance ndecode-nencode (x b) (p 24) (q 8))))))

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
(local-defund q0 (a b) (near (* a (y0 b)) 24))
(local-defund e0 (b) (near (- 1 (* b (y0 b))) 24))
(local-defund r0 (a b) (near (- a (* b (q0 a b))) 24))
(local-defund y1 (b) (near (+ (y0 b) (* (e0 b) (y0 b))) 24))
(local-defund q1 (a b) (near (+ (q0 a b) (* (r0 a b) (y1 b))) 24))
(local-defund r1 (a b) (near (- a (* b (q1 a b))) 24))
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
                        (:instance recip-refine-1 (y1 (y0 b))(p 24)  (y2 (y0 b)) (ep1 (eps0)) (ep2 (eps0))))
                  :in-theory (enable y1 y1p e0))))

(local-defthm sp-3
  (implies (and (rationalp b)
                (<= 1 b)
                (< b 2)
                (exactp b 24))
           (<= (abs (- 1 (* b (y1 b)))) (eps1)))
  :rule-classes ()
  :hints (("Goal" :use (sp-1
                        (:instance recip-refine-2 (y1 (y0 b))(p 24)  (y2 (y0 b)) (ep1 (eps0)) (ep2 (eps0))))
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
                        (:instance harrison (yp (y1p b)) (ep (eps1p)) (p 24)))
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
                        (:instance initial-approximation (y (y0 b)) (ep (eps0)) (p 24)))
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
                        (:instance refine-quotient-2 (p 24) (y (y1 b)) (q0 (q0 a b)) (ep (eps1)) (de (del0))))
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
                        (:instance near-exactp-b (x (- a (* b (q1 a b)))) (n 24)))
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
                (ieee-mode-p mode))
           (= (quot a b mode) (rnd (/ a b) mode 24)))
  :rule-classes ()
  :hints (("Goal" :use (sp-4 sp-6 sp-7
                        (:instance markstein  (p 24) (q (q1 a b)) (y (y1 b))))
                  :in-theory (enable quot))))

(defund sp-divide (a b mode)
  (let* ((y0 (rcp24 b))
         (q0 (near (* a y0) 24))
         (e0 (near (- 1 (* b y0)) 24))
         (r0 (near (- a (* b q0)) 24))
         (y1 (near (+ y0 (* e0 y0)) 24))
         (q1 (near (+ q0 (* r0 y1)) 24))
         (r1 (near (- a (* b q1)) 24)))
    (rnd (+ q1 (* r1 y1)) mode 24)))

(local-defthm sp-11
  (= (sp-divide a b mode)
     (quot a b mode))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable sp-divide y0 q0 e0 r0 y1 q1 r1 quot))))

(defthm sp-divide-correct
  (implies (and (rationalp a)
                (rationalp b)
                (<= 1 a)
                (< a 2)
                (<= 1 b)
                (< b 2)
                (exactp a 24)
                (exactp b 24)
                (ieee-mode-p mode))
           (= (sp-divide a b mode) (rnd (/ a b) mode 24)))
  :rule-classes ()
  :hints (("Goal" :use (sp-10 sp-11))))

)

(local-defthm rcp-6
  (implies (and (rationalp b)
                (rationalp x)
                (<= 1 b)
                (< b 2))
           (<= (abs (* x (rcp24 (trunc b 24))))
               (abs x)))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rcp24-spec (b (trunc b 24)))
                        (:instance trunc-upper-pos (x b) (n 24))
                        (:instance trunc-exactp-c (a 1) (x b) (n 24))))))

(local-defthm rcp-8
  (implies (and (rationalp b)
                (<= 1 b)
                (< b 2))
           (and (<= 1 (trunc b 24))
                (< (trunc b 24) 2)
                (<= (abs (- 1 (* (trunc b 24) (rcp24 (trunc b 24))))) (expt 2 -23))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rcp24-spec (b (trunc b 24)))
                        (:instance trunc-upper-pos (x b) (n 24))
                        (:instance trunc-exactp-c (a 1) (x b) (n 24))))))

(local-defthm rcp-9
  (implies (and (rationalp b)
                (<= 1 b)
                (< b 2))
           (<= (abs (- (* (trunc b 24) (rcp24 (trunc b 24)))
                       (* b (rcp24 (trunc b 24)))))
               (abs (- (trunc b 24) b))))
  :rule-classes ()
  :hints (("Goal" :use ((:instance rcp24-spec (b (trunc b 24)))
                        (:instance rcp-6 (x (- (trunc b 24) b)))))))

(local-defthm rcp-10
  (implies (and (rationalp b)
                (<= 1 b)
                (< b 2))
           (<= (abs (- (* (trunc b 24) (rcp24 (trunc b 24)))
                       (* b (rcp24 (trunc b 24)))))
               (expt 2 -23)))
  :rule-classes ()
  :hints (("Goal" :use (rcp-9
                        (:instance trunc-diff (x b) (n 24))
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
                (rationalp (trunc b 24))
                (exactp (trunc b 24) 24)
                (rationalp (* (trunc b 24) (rcp24 (trunc b 24))))
                (rationalp (* b (rcp24 (trunc b 24))))
                (<= 1 b)
                (< b 2))
           (<= (abs (- 1 (* b (rcp24 (trunc b 24))))) (+ (expt 2 -23) (expt 2 -23))))
  :rule-classes ()
  :hints (("Goal" :in-theory (theory 'minimal-theory)
                  :use (rcp-8 rcp-10
                        (:instance rcp-11 (a (expt 2 -23)) (x (* (trunc b 24) (rcp24 (trunc b 24)))) (y (* b (rcp24 (trunc b 24)))))
                        (:instance rcp24-spec (b (trunc b 24)))))))

(defthm rcp24-trunc-error
  (implies (and (rationalp b)
                (<= 1 b)
                (< b 2))
           (<= (abs (- 1 (* b (rcp24 (trunc b 24))))) (expt 2 -22)))
  :rule-classes ()
  :hints (("Goal" :use (rcp-12))))

(local-defund y0 (b) (rcp24 (trunc b 24)))
(local-defund q0 (a b) (near (* a (y0 b)) 53))
(local-defund e0 (b) (near (- 1 (* b (y0 b))) 53))
(local-defund r0 (a b) (near (- a (* b (q0 a b))) 53))
(local-defund y1 (b) (near (+ (y0 b) (* (e0 b) (y0 b))) 53))
(local-defund e1 (b) (near (- 1 (* b (y1 b))) 53))
(local-defund y2 (b) (near (+ (y0 b) (* (e0 b) (y1 b))) 53))
(local-defund q1 (a b) (near (+ (q0 a b) (* (r0 a b) (y1 b))) 53))
(local-defund y3 (b) (near (+ (y1 b) (* (e1 b) (y2 b))) 53))
(local-defund r1 (a b) (near (- a (* b (q1 a b))) 53))
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
  :hints (("Goal" :use (rcp24-trunc-error)
                  :in-theory (enable y0))))

(local-defthm dp-2
  (implies (and (rationalp b)
                (<= 1 b)
                (< b 2)
                (exactp b 53))
           (<= (abs (- 1 (* b (y1 b)))) (eps1)))
  :rule-classes ()
  :hints (("Goal" :use (dp-1
                        (:instance recip-refine-2 (y1 (y0 b)) (p 53) (y2 (y0 b)) (ep1 (eps0)) (ep2 (eps0))))
                  :in-theory (enable y1 e0))))

(local-defthm dp-3
  (implies (and (rationalp b)
                (<= 1 b)
                (< b 2)
                (exactp b 53))
           (<= (abs (- 1 (* b (y2 b)))) (eps2)))
  :rule-classes ()
  :hints (("Goal" :use (dp-1 dp-2
                        (:instance recip-refine-2 (y1 (y0 b)) (p 53) (y2 (y1 b)) (ep1 (eps0)) (ep2 (eps1))))
                  :in-theory (enable y2 e0))))

(local-defthm dp-4
  (implies (and (rationalp b)
                (<= 1 b)
                (< b 2)
                (exactp b 53))
           (<= (abs (- 1 (* b (y3p b)))) (eps3p)))
  :rule-classes ()
  :hints (("Goal" :use (dp-2 dp-3
                        (:instance recip-refine-1 (y1 (y1 b)) (p 53) (y2 (y2 b)) (ep1 (eps1)) (ep2 (eps2))))
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
             (iff (or (member-equal a lst)
                      (member-equal a acc))
                  (or (member-equal a (first-n-ac n lst acc))
                      (member-equal a (nthcdr n lst)))))
    :hints (("Goal" :induct (first-n-ac n lst acc)))
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
                                     (lst lst)
                                     (acc nil))))))))

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

(local-in-theory (disable (h-excps)))

(local-defthm dp-5
  (implies (and (rationalp b)
                (<= 1 b)
                (< b 2)
                (exactp b 53))
           (< (abs (- 1 (* b (y3 b)))) (expt 2 -53)))
  :rule-classes ()
  :hints (("Goal" :use (dp-4 excp-cases
                        (:instance harrison (yp (y3p b)) (ep (eps3p)) (p 53)))
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
                        (:instance initial-approximation (y (y0 b)) (ep (eps0)) (p 53)))
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
                        (:instance refine-quotient-2 (p 53) (y (y1 b)) (q0 (q0 a b)) (ep (eps1)) (de (del0))))
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
                        (:instance near-exactp-b (x (- a (* b (q1 a b)))) (n 53)))
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
                (ieee-mode-p mode))
           (= (quot a b mode) (rnd (/ a b) mode 53)))
  :rule-classes ()
  :hints (("Goal" :use (dp-5 dp-7 dp-8
                        (:instance markstein  (p 53) (q (q1 a b)) (y (y3 b))))
                  :in-theory (enable quot))))

(defund dp-divide (a b mode)
  (let* ((y0 (rcp24 (trunc b 24)))
         (q0 (near (* a y0) 53))
         (e0 (near (- 1 (* b y0)) 53))
         (r0 (near (- a (* b q0)) 53))
         (y1 (near (+ y0 (* e0 y0)) 53))
         (e1 (near (- 1 (* b y1)) 53))
         (y2 (near (+ y0 (* e0 y1)) 53))
         (q1 (near (+ q0 (* r0 y1)) 53))
         (y3 (near (+ y1 (* e1 y2)) 53))
         (r1 (near (- a (* b q1)) 53)))
    (rnd (+ q1 (* r1 y3)) mode 53)))

(local-defthm dp-12
  (= (dp-divide a b mode)
     (quot a b mode))
  :rule-classes ()
  :hints (("Goal" :in-theory (enable dp-divide y0 q0 e0 r0 y1 e1 y2 q1 y3 r1 quot))))

(defthm dp-divide-correct
  (implies (and (rationalp a)
                (rationalp b)
                (<= 1 a)
                (< a 2)
                (<= 1 b)
                (< b 2)
                (exactp a 53)
                (exactp b 53)
                (ieee-mode-p mode))
           (= (dp-divide a b mode) (rnd (/ a b) mode 53)))
  :rule-classes ()
  :hints (("Goal" :use (dp-12 dp-11))))
