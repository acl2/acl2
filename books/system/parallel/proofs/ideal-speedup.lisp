(in-package "ACL2")

(defconst *general-duration-factor*

; make this larger if you want the proofs to take longer

  108) ; was 60

(defconst *4-way-duration-factor*
  (* *general-duration-factor*
     (round (/ 40 4) 1)))

(defconst *8-way-duration-factor*
  (* *general-duration-factor*
     (round (/ 40 8) 1)))

(defconst *20-way-duration-factor*
  (* *general-duration-factor*
     (round (/ 40 20) 1)))

(defconst *32-way-duration-factor*
  (* *general-duration-factor*
     (round (/ 40 32) 1)))

(defconst *40-way-duration-factor*
  (* *general-duration-factor*
     (round (/ 40 40) 1)))

; call (set-waterfall-parallelism :full) to execute these proofs in parallel

(defun countdown (n1 n2 n2-top acc)
  (declare (type (unsigned-byte 26) n1 n2 n2-top)
           (type (integer 0 100) acc)
           (xargs :measure (cons (cons (1+ (nfix n1)) 1) (nfix n2))))
  (cond ((mbe :logic (zp n1)
              :exec (eql n1 0))
         (cond ((mbe :logic (zp n2)
                     :exec (eql n2 0))
                acc)
               (t (countdown n1
                             (the (unsigned-byte 26) (1- n2))
                             n2-top
                             (if (< acc 100)
                                 (the (integer 0 100)
                                      (1+ acc))
                               0)))))
        ((mbe :logic (zp n2)
              :exec (eql n2 0))
         (countdown (the (unsigned-byte 26) (1- n1))
                    n2-top
                    n2-top
                    (if (< acc 100)
                        (the (integer 0 100)
                             (1+ acc))
                      0)))
        (t (countdown n1
                      (the (unsigned-byte 26) (1- n2))
                      n2-top
                      (if (< acc 100)
                          (the (integer 0 100)
                               (1+ acc))
                        0)))))

(defun countdown-wrapper-4-way (x)
  (if (equal x 1)
      (countdown 2000000 *4-way-duration-factor* *4-way-duration-factor* 0)
    (countdown 2000001 *4-way-duration-factor* *4-way-duration-factor* 0)))

(defun countdown-wrapper-8-way (x)
  (if (equal x 1)
      (countdown 2000000 *8-way-duration-factor* *8-way-duration-factor* 0)
    (countdown 2000001 *8-way-duration-factor* *8-way-duration-factor* 0)))

(defun countdown-wrapper-20-way (x)
  (if (equal x 1)
      (countdown 2000000 *20-way-duration-factor* *20-way-duration-factor* 0)
    (countdown 2000001 *20-way-duration-factor* *20-way-duration-factor* 0)))

(defun countdown-wrapper-32-way (x)
  (if (equal x 1)
      (countdown 2000000 *32-way-duration-factor* *32-way-duration-factor* 0)
    (countdown 2000001 *32-way-duration-factor* *32-way-duration-factor* 0)))

(defun countdown-wrapper-40-way (x)
  (if (equal x 1)
      (countdown 2000000 *40-way-duration-factor* *40-way-duration-factor* 0)
    (countdown 2000001 *40-way-duration-factor* *40-way-duration-factor* 0)))

(defun p1-4-way (n) (not (equal (countdown-wrapper-4-way n) 11)))
(defun p2-4-way (n) (not (equal (countdown-wrapper-4-way n) 12)))
(defun p3-4-way (n) (not (equal (countdown-wrapper-4-way n) 13)))
(defun p4-4-way (n) (not (equal (countdown-wrapper-4-way n) 14)))


(comp t) ; avoid stack overflow, e.g. in Allegro CL

(defthm ideal-4-way
  (and (p1-4-way x) (p2-4-way x) (p3-4-way x) (p4-4-way x))
  :otf-flg t
  :rule-classes nil)

(defun p1-8-way (n) (not (equal (countdown-wrapper-8-way n) 11)))
(defun p2-8-way (n) (not (equal (countdown-wrapper-8-way n) 12)))
(defun p3-8-way (n) (not (equal (countdown-wrapper-8-way n) 13)))
(defun p4-8-way (n) (not (equal (countdown-wrapper-8-way n) 14)))
(defun p5-8-way (n) (not (equal (countdown-wrapper-8-way n) 15)))
(defun p6-8-way (n) (not (equal (countdown-wrapper-8-way n) 16)))
(defun p7-8-way (n) (not (equal (countdown-wrapper-8-way n) 17)))
(defun p8-8-way (n) (not (equal (countdown-wrapper-8-way n) 18)))

(defthm ideal-8-way
  (and (p1-8-way x) (p2-8-way x) (p3-8-way x) (p4-8-way x) (p5-8-way x)
       (p6-8-way x) (p7-8-way x) (p8-8-way x))
  :otf-flg t
  :rule-classes nil)

(defun p1-20-way (n) (not (equal (countdown-wrapper-20-way n) 11)))
(defun p2-20-way (n) (not (equal (countdown-wrapper-20-way n) 12)))
(defun p3-20-way (n) (not (equal (countdown-wrapper-20-way n) 13)))
(defun p4-20-way (n) (not (equal (countdown-wrapper-20-way n) 14)))
(defun p5-20-way (n) (not (equal (countdown-wrapper-20-way n) 15)))
(defun p6-20-way (n) (not (equal (countdown-wrapper-20-way n) 16)))
(defun p7-20-way (n) (not (equal (countdown-wrapper-20-way n) 17)))
(defun p8-20-way (n) (not (equal (countdown-wrapper-20-way n) 18)))
(defun p9-20-way (n) (not (equal (countdown-wrapper-20-way n) 19)))
(defun p10-20-way (n) (not (equal (countdown-wrapper-20-way n) 20)))
(defun p11-20-way (n) (not (equal (countdown-wrapper-20-way n) 21)))
(defun p12-20-way (n) (not (equal (countdown-wrapper-20-way n) 22)))
(defun p13-20-way (n) (not (equal (countdown-wrapper-20-way n) 23)))
(defun p14-20-way (n) (not (equal (countdown-wrapper-20-way n) 24)))
(defun p15-20-way (n) (not (equal (countdown-wrapper-20-way n) 25)))
(defun p16-20-way (n) (not (equal (countdown-wrapper-20-way n) 26)))
(defun p17-20-way (n) (not (equal (countdown-wrapper-20-way n) 27)))
(defun p18-20-way (n) (not (equal (countdown-wrapper-20-way n) 28)))
(defun p19-20-way (n) (not (equal (countdown-wrapper-20-way n) 29)))
(defun p20-20-way (n) (not (equal (countdown-wrapper-20-way n) 30)))

(comp t)

(defthm ideal-20-way
  (and (p1-20-way x) (p2-20-way x) (p3-20-way x) (p4-20-way x) (p5-20-way x)
       (p6-20-way x) (p7-20-way x) (p8-20-way x) (p9-20-way x)
       (p10-20-way x) (p11-20-way x) (p12-20-way x) (p13-20-way x)
       (p14-20-way x) (p15-20-way x) (p16-20-way x) (p17-20-way x)
       (p18-20-way x) (p19-20-way x)
       (p20-20-way x))
  :otf-flg t
  :rule-classes nil)


(defun p1-32-way (n) (not (equal (countdown-wrapper-32-way n) 11)))
(defun p2-32-way (n) (not (equal (countdown-wrapper-32-way n) 12)))
(defun p3-32-way (n) (not (equal (countdown-wrapper-32-way n) 13)))
(defun p4-32-way (n) (not (equal (countdown-wrapper-32-way n) 14)))
(defun p5-32-way (n) (not (equal (countdown-wrapper-32-way n) 15)))
(defun p6-32-way (n) (not (equal (countdown-wrapper-32-way n) 16)))
(defun p7-32-way (n) (not (equal (countdown-wrapper-32-way n) 17)))
(defun p8-32-way (n) (not (equal (countdown-wrapper-32-way n) 18)))
(defun p9-32-way (n) (not (equal (countdown-wrapper-32-way n) 19)))
(defun p10-32-way (n) (not (equal (countdown-wrapper-32-way n) 20)))

(defun p11-32-way (n) (not (equal (countdown-wrapper-32-way n) 21)))
(defun p12-32-way (n) (not (equal (countdown-wrapper-32-way n) 22)))
(defun p13-32-way (n) (not (equal (countdown-wrapper-32-way n) 23)))
(defun p14-32-way (n) (not (equal (countdown-wrapper-32-way n) 24)))
(defun p15-32-way (n) (not (equal (countdown-wrapper-32-way n) 25)))
(defun p16-32-way (n) (not (equal (countdown-wrapper-32-way n) 26)))
(defun p17-32-way (n) (not (equal (countdown-wrapper-32-way n) 27)))
(defun p18-32-way (n) (not (equal (countdown-wrapper-32-way n) 28)))
(defun p19-32-way (n) (not (equal (countdown-wrapper-32-way n) 29)))
(defun p20-32-way (n) (not (equal (countdown-wrapper-32-way n) 30)))

(defun p21-32-way (n) (not (equal (countdown-wrapper-32-way n) 31)))
(defun p22-32-way (n) (not (equal (countdown-wrapper-32-way n) 32)))
(defun p23-32-way (n) (not (equal (countdown-wrapper-32-way n) 33)))
(defun p24-32-way (n) (not (equal (countdown-wrapper-32-way n) 34)))
(defun p25-32-way (n) (not (equal (countdown-wrapper-32-way n) 35)))
(defun p26-32-way (n) (not (equal (countdown-wrapper-32-way n) 36)))
(defun p27-32-way (n) (not (equal (countdown-wrapper-32-way n) 37)))
(defun p28-32-way (n) (not (equal (countdown-wrapper-32-way n) 38)))
(defun p29-32-way (n) (not (equal (countdown-wrapper-32-way n) 39)))

(defun p30-32-way (n) (not (equal (countdown-wrapper-32-way n) 32)))
(defun p31-32-way (n) (not (equal (countdown-wrapper-32-way n) 41)))
(defun p32-32-way (n) (not (equal (countdown-wrapper-32-way n) 42)))

(comp t)

(defthm ideal-32-way
  (and (p1-32-way x) (p2-32-way x) (p3-32-way x) (p4-32-way x) (p5-32-way x)
       (p6-32-way x) (p7-32-way x) (p8-32-way x) (p9-32-way x)
       (p10-32-way x) (p11-32-way x) (p12-32-way x) (p13-32-way x)
       (p14-32-way x) (p15-32-way x) (p16-32-way x) (p17-32-way x)
       (p18-32-way x) (p19-32-way x)
       (p20-32-way x) (p21-32-way x) (p22-32-way x) (p23-32-way x)
       (p24-32-way x) (p25-32-way x) (p26-32-way x) (p27-32-way x)
       (p28-32-way x) (p29-32-way x)
       (p30-32-way x) (p31-32-way x) (p32-32-way x))
  :otf-flg t
  :rule-classes nil)


(defun p1-40-way (n) (not (equal (countdown-wrapper-40-way n) 11)))
(defun p2-40-way (n) (not (equal (countdown-wrapper-40-way n) 12)))
(defun p3-40-way (n) (not (equal (countdown-wrapper-40-way n) 13)))
(defun p4-40-way (n) (not (equal (countdown-wrapper-40-way n) 14)))
(defun p5-40-way (n) (not (equal (countdown-wrapper-40-way n) 15)))
(defun p6-40-way (n) (not (equal (countdown-wrapper-40-way n) 16)))
(defun p7-40-way (n) (not (equal (countdown-wrapper-40-way n) 17)))
(defun p8-40-way (n) (not (equal (countdown-wrapper-40-way n) 18)))
(defun p9-40-way (n) (not (equal (countdown-wrapper-40-way n) 19)))
(defun p10-40-way (n) (not (equal (countdown-wrapper-40-way n) 20)))

(defun p11-40-way (n) (not (equal (countdown-wrapper-40-way n) 21)))
(defun p12-40-way (n) (not (equal (countdown-wrapper-40-way n) 22)))
(defun p13-40-way (n) (not (equal (countdown-wrapper-40-way n) 23)))
(defun p14-40-way (n) (not (equal (countdown-wrapper-40-way n) 24)))
(defun p15-40-way (n) (not (equal (countdown-wrapper-40-way n) 25)))
(defun p16-40-way (n) (not (equal (countdown-wrapper-40-way n) 26)))
(defun p17-40-way (n) (not (equal (countdown-wrapper-40-way n) 27)))
(defun p18-40-way (n) (not (equal (countdown-wrapper-40-way n) 28)))
(defun p19-40-way (n) (not (equal (countdown-wrapper-40-way n) 29)))
(defun p20-40-way (n) (not (equal (countdown-wrapper-40-way n) 30)))

(defun p21-40-way (n) (not (equal (countdown-wrapper-40-way n) 31)))
(defun p22-40-way (n) (not (equal (countdown-wrapper-40-way n) 32)))
(defun p23-40-way (n) (not (equal (countdown-wrapper-40-way n) 33)))
(defun p24-40-way (n) (not (equal (countdown-wrapper-40-way n) 34)))
(defun p25-40-way (n) (not (equal (countdown-wrapper-40-way n) 35)))
(defun p26-40-way (n) (not (equal (countdown-wrapper-40-way n) 36)))
(defun p27-40-way (n) (not (equal (countdown-wrapper-40-way n) 37)))
(defun p28-40-way (n) (not (equal (countdown-wrapper-40-way n) 38)))
(defun p29-40-way (n) (not (equal (countdown-wrapper-40-way n) 39)))

(defun p30-40-way (n) (not (equal (countdown-wrapper-40-way n) 40)))
(defun p31-40-way (n) (not (equal (countdown-wrapper-40-way n) 41)))
(defun p32-40-way (n) (not (equal (countdown-wrapper-40-way n) 42)))
(defun p33-40-way (n) (not (equal (countdown-wrapper-40-way n) 43)))
(defun p34-40-way (n) (not (equal (countdown-wrapper-40-way n) 44)))
(defun p35-40-way (n) (not (equal (countdown-wrapper-40-way n) 45)))
(defun p36-40-way (n) (not (equal (countdown-wrapper-40-way n) 46)))
(defun p37-40-way (n) (not (equal (countdown-wrapper-40-way n) 47)))
(defun p38-40-way (n) (not (equal (countdown-wrapper-40-way n) 48)))
(defun p39-40-way (n) (not (equal (countdown-wrapper-40-way n) 49)))
(defun p40-40-way (n) (not (equal (countdown-wrapper-40-way n) 50)))

(comp t)

(defthm ideal-40-way
  (and (p1-40-way x) (p2-40-way x) (p3-40-way x) (p4-40-way x) (p5-40-way x)
       (p6-40-way x) (p7-40-way x) (p8-40-way x) (p9-40-way x)
       (p10-40-way x) (p11-40-way x) (p12-40-way x) (p13-40-way x)
       (p14-40-way x) (p15-40-way x) (p16-40-way x) (p17-40-way x)
       (p18-40-way x) (p19-40-way x)
       (p20-40-way x) (p21-40-way x) (p22-40-way x) (p23-40-way x)
       (p24-40-way x) (p25-40-way x) (p26-40-way x) (p27-40-way x)
       (p28-40-way x) (p29-40-way x)
       (p30-40-way x) (p31-40-way x) (p32-40-way x) (p33-40-way x)
       (p34-40-way x) (p35-40-way x) (p36-40-way x) (p37-40-way x)
       (p38-40-way x) (p39-40-way x)
       (p40-40-way x))
  :otf-flg t
  :rule-classes nil)
