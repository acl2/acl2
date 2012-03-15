(in-package "ACL2")

(defconst *duration-factor* 

; make this larger if you want the proofs to take longer

  50)

; call (set-waterfall-parallelism :full) to execute these proofs in parallel

(defun countdown(n acc)
 (declare (xargs :guard (and (natp n)
                             (integerp acc))))
 (if (or (zp n) (<= n 0))
     acc
   (countdown (1- n) (1+ acc))))

(defun countdown-wrapper (x)
 (if (equal x 1)
     (countdown (* *duration-factor* 2000000) 0)
   (countdown (* *duration-factor* 2000001) 0)))

(defun p1 (n) (not (equal (countdown-wrapper n) 11)))
(defun p2 (n) (not (equal (countdown-wrapper n) 12)))
(defun p3 (n) (not (equal (countdown-wrapper n) 13)))
(defun p4 (n) (not (equal (countdown-wrapper n) 14)))
(defun p5 (n) (not (equal (countdown-wrapper n) 15)))
(defun p6 (n) (not (equal (countdown-wrapper n) 16)))
(defun p7 (n) (not (equal (countdown-wrapper n) 17)))
(defun p8 (n) (not (equal (countdown-wrapper n) 18)))

(comp t) ; avoid stack overflow, e.g. in Allegro CL

(defthm ideal-8-way
  (and (p1 x) (p2 x) (p3 x) (p4 x) (p5 x) (p6 x) (p7 x) (p8 x))
  :otf-flg t
  :rule-classes nil)

#|
(thm (and (p1 x) (p2 x) (p3 x) (p4 x))
    :hints (("Goal" :do-not '(preprocess)))
    :otf-flg t)
|#

(defun p9 (n) (not (equal (countdown-wrapper n) 19)))
(defun p10 (n) (not (equal (countdown-wrapper n) 20)))
(defun p11 (n) (not (equal (countdown-wrapper n) 21)))
(defun p12 (n) (not (equal (countdown-wrapper n) 22)))
(defun p13 (n) (not (equal (countdown-wrapper n) 23)))
(defun p14 (n) (not (equal (countdown-wrapper n) 24)))
(defun p15 (n) (not (equal (countdown-wrapper n) 25)))
(defun p16 (n) (not (equal (countdown-wrapper n) 26)))
(defun p17 (n) (not (equal (countdown-wrapper n) 27)))
(defun p18 (n) (not (equal (countdown-wrapper n) 28)))
(defun p19 (n) (not (equal (countdown-wrapper n) 29)))
(defun p20 (n) (not (equal (countdown-wrapper n) 30)))

(defthm ideal-20-way
  (and (p1 x) (p2 x) (p3 x) (p4 x) (p5 x) (p6 x) (p7 x) (p8 x) (p9 x) 
       (p10 x) (p11 x) (p12 x) (p13 x) (p14 x) (p15 x) (p16 x) (p17 x) (p18 x) (p19 x) 
       (p20 x))
  :otf-flg t 
  :rule-classes nil)

(defun p21 (n) (not (equal (countdown-wrapper n) 31)))
(defun p22 (n) (not (equal (countdown-wrapper n) 32)))
(defun p23 (n) (not (equal (countdown-wrapper n) 33)))
(defun p24 (n) (not (equal (countdown-wrapper n) 34)))

(defthm ideal-24-way
  (and (p1 x) (p2 x) (p3 x) (p4 x) (p5 x) (p6 x) (p7 x) (p8 x) (p9 x) 
       (p10 x) (p11 x) (p12 x) (p13 x) (p14 x) (p15 x) (p16 x) (p17 x) (p18 x) (p19 x) 
       (p20 x) (p21 x) (p22 x) (p23 x) (p24 x))
  :otf-flg t 
  :rule-classes nil)

(defun p25 (n) (not (equal (countdown-wrapper n) 35)))
(defun p26 (n) (not (equal (countdown-wrapper n) 36)))
(defun p27 (n) (not (equal (countdown-wrapper n) 37)))
(defun p28 (n) (not (equal (countdown-wrapper n) 38)))
(defun p29 (n) (not (equal (countdown-wrapper n) 39)))

(defun p30 (n) (not (equal (countdown-wrapper n) 40)))
(defun p31 (n) (not (equal (countdown-wrapper n) 41)))
(defun p32 (n) (not (equal (countdown-wrapper n) 42)))
(defun p33 (n) (not (equal (countdown-wrapper n) 43)))
(defun p34 (n) (not (equal (countdown-wrapper n) 44)))
(defun p35 (n) (not (equal (countdown-wrapper n) 45)))
(defun p36 (n) (not (equal (countdown-wrapper n) 46)))
(defun p37 (n) (not (equal (countdown-wrapper n) 47)))
(defun p38 (n) (not (equal (countdown-wrapper n) 48)))
(defun p39 (n) (not (equal (countdown-wrapper n) 49)))
(defun p40 (n) (not (equal (countdown-wrapper n) 50)))

(defthm ideal-40-way
  (and (p1 x) (p2 x) (p3 x) (p4 x) (p5 x) (p6 x) (p7 x) (p8 x) (p9 x) 
       (p10 x) (p11 x) (p12 x) (p13 x) (p14 x) (p15 x) (p16 x) (p17 x) 
       (p18 x) (p19 x) 
       (p20 x) (p21 x) (p22 x) (p23 x) (p24 x) (p25 x) (p26 x) (p27 x) 
       (p28 x) (p29 x) 
       (p30 x) (p31 x) (p32 x) (p33 x) (p34 x) (p35 x) (p36 x) (p37 x) 
       (p38 x) (p39 x) 
       (p40 x))
  :otf-flg t
  :rule-classes nil)


(defun p41 (n) (not (equal (countdown-wrapper n) 51)))
(defun p42 (n) (not (equal (countdown-wrapper n) 52)))
(defun p43 (n) (not (equal (countdown-wrapper n) 53)))
(defun p44 (n) (not (equal (countdown-wrapper n) 54)))
(defun p45 (n) (not (equal (countdown-wrapper n) 55)))
(defun p46 (n) (not (equal (countdown-wrapper n) 56)))
(defun p47 (n) (not (equal (countdown-wrapper n) 57)))
(defun p48 (n) (not (equal (countdown-wrapper n) 58)))
(defun p49 (n) (not (equal (countdown-wrapper n) 59)))

(defun p50 (n) (not (equal (countdown-wrapper n) 60)))
(defun p51 (n) (not (equal (countdown-wrapper n) 61)))
(defun p52 (n) (not (equal (countdown-wrapper n) 62)))
(defun p53 (n) (not (equal (countdown-wrapper n) 63)))
(defun p54 (n) (not (equal (countdown-wrapper n) 64)))
(defun p55 (n) (not (equal (countdown-wrapper n) 65)))
(defun p56 (n) (not (equal (countdown-wrapper n) 66)))
(defun p57 (n) (not (equal (countdown-wrapper n) 67)))
(defun p58 (n) (not (equal (countdown-wrapper n) 68)))
(defun p59 (n) (not (equal (countdown-wrapper n) 69)))

(defun p60 (n) (not (equal (countdown-wrapper n) 70)))
(defun p61 (n) (not (equal (countdown-wrapper n) 71)))
(defun p62 (n) (not (equal (countdown-wrapper n) 72)))
(defun p63 (n) (not (equal (countdown-wrapper n) 73)))
(defun p64 (n) (not (equal (countdown-wrapper n) 74)))

(defthm ideal-64-way
  (and (p1 x) (p2 x) (p3 x) (p4 x) (p5 x) (p6 x) (p7 x) (p8 x) (p9 x) 
       (p10 x) (p11 x) (p12 x) (p13 x) (p14 x) (p15 x) (p16 x) (p17 x) 
       (p18 x) (p19 x) 
       (p20 x) (p21 x) (p22 x) (p23 x) (p24 x) (p25 x) (p26 x) (p27 x) 
       (p28 x) (p29 x) 
       (p30 x) (p31 x) (p32 x) (p33 x) (p34 x) (p35 x) (p36 x) (p37 x) 
       (p38 x) (p39 x) 
       (p40 x) (p41 x) (p42 x) (p43 x) (p44 x) (p45 x) (p46 x) (p47 x) 
       (p48 x) (p49 x) 
       (p50 x) (p51 x) (p52 x) (p53 x) (p54 x) (p55 x) (p56 x) (p57 x) 
       (p58 x) (p59 x) 
       (p60 x) (p61 x) (p62 x) (p63 x) (p64 x))
  :otf-flg t
  :rule-classes nil)
