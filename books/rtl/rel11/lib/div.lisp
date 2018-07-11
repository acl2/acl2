; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
;
; Contact:
;   David M. Russinoff
;   1106 W 9th St., Austin, TX 78703
;   david@russinoff.com
;   http://www.russinoff.com/
;
; See license file books/rtl/rel11/license.txt.
;

(in-package "RTL")

(set-enforce-redundancy t)

(local (include-book "../support/div"))

(set-inhibit-warnings "theory") ; avoid warning in the next event
(local (in-theory nil))

(include-book "defs")

;;;**********************************************************************
;;;		    	    Quotient Refinement
;;;**********************************************************************

(defsection-rtl |Quotient Refinement| |FMA-Based Division|

(defthm init-approx
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp y)
                (rationalp ep)
                (not (zp p))
                (> a 0)
                (> b 0)
                (<= (abs (- 1 (* b y))) ep))
           (<= (abs (- 1 (* (/ b a) (rne (* a y) p))))
               (+ ep (* (expt 2 (- p)) (1+ ep)))))
  :rule-classes ())

(defthm r-exactp
  (implies (and (rationalp a)
                (rationalp b)
                (integerp p)
                (> p 1)
                (exactp a p)
                (exactp b p)
                (<= 1 a)
                (< a 2)
                (<= 1 b)
                (< b 2)
                (rationalp q)
                (exactp q p)
                (< (abs (- (/ a b) q)) (expt 2 (- (1+ (if (> a b) 0 -1)) p))))
           (exactp (- a (* b q)) p))
  :rule-classes ())

(defthm markstein-lemma
  (let ((e (if (> a b) 0 -1))
        (r (- a (* b q))))
    (implies (and (rationalp a)
                  (rationalp b)
                  (rationalp q)
                  (rationalp y)
                  (integerp p)
                  (<= 1 a)
                  (< a 2)
                  (<= 1 b)
                  (< b 2)
                  (> p 1)
                  (exactp a p)
                  (exactp b p)
                  (exactp q p)
                  (< (abs (- 1 (* b y))) (/ (expt 2 p)))
                  (< (abs (- (/ a b) q)) (expt 2 (- (1+ e) p)))
                  (ieee-rounding-mode-p mode))
             (= (rnd (+ q (* r y)) mode p)
                (rnd (/ a b) mode p))))
  :rule-classes ())

(defthm quotient-refinement-1
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp y)
                (rationalp q0)
                (rationalp ep)
                (rationalp de)
                (not (zp p))
                (<= 1 a)
                (< a 2)
                (<= 1 b)
                (< b 2)
                (<= (abs (- 1 (* b y))) ep)
                (<= (abs (- 1 (* (/ b a) q0))) de))
            (let* ((r (rne (- a (* b q0)) p))
                   (q (rne (+ q0 (* r y)) p)))
              (<= (abs (- q (/ a b)))
                  (* (/ a b)
                     (+ (expt 2 (- p))
                        (* (1+ (expt 2 (- p))) de ep)
                        (* (expt 2 (- p)) de (1+ ep))
                        (* (expt 2 (- (* 2 p))) de (1+ ep)))))))
  :rule-classes ())

(defthm quotient-refinement-2
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp y)
                (rationalp q0)
                (rationalp ep)
                (rationalp de)
                (not (zp p))
                (<= 1 a)
                (< a 2)
                (<= 1 b)
                (< b 2)
                (<= (abs (- 1 (* b y))) ep)
                (<= (abs (- 1 (* (/ b a) q0))) de)
                (< (+ (* ep de) (* (expt 2 (- p)) de (1+ ep))) (expt 2 (- (1+ p)))))
            (let* ((r (rne (- a (* b q0)) p))
                   (q (rne (+ q0 (* r y)) p))
                   (e (if (> a b) 0 -1)))
              (< (abs (- q (/ a b)))
                 (expt 2 (- (1+ e) p)))))
  :rule-classes ())
)

;;;**********************************************************************
;;;		    	  Reciprocal Refinement
;;;**********************************************************************

(defsection-rtl |Reciprocal Refinement| |FMA-Based Division|

(defthm recip-refinement-1
  (let* ((e1 (rne (- 1 (* b y1)) p))
         (y3p (+ y1 (* e1 y2)))
         (ep3p (* ep1 (+ ep2 (* (expt 2 (- p)) (1+ ep2))))))
    (implies (and (rationalp y1)
                  (rationalp y2)
                  (rationalp b)
                  (rationalp ep1)
                  (rationalp ep2)
                  (integerp p)
                  (> p 0)
                  (<= (abs (- 1 (* b y1))) ep1)
                  (<= (abs (- 1 (* b y2))) ep2))
             (<= (abs (- 1 (* b y3p)))
                 ep3p)))
  :rule-classes ())

(defthm recip-refinement-2
  (let* ((e1 (rne (- 1 (* b y1)) p))
         (y3p (+ y1 (* e1 y2)))
         (y3 (rne y3p p))
         (ep3p (* ep1 (+ ep2 (* (expt 2 (- p)) (1+ ep2)))))
         (ep3 (+ ep3p (* (expt 2 (- p)) (1+ ep3p)))))
    (implies (and (rationalp y1)
                  (rationalp y2)
                  (rationalp b)
                  (rationalp ep1)
                  (rationalp ep2)
                  (integerp p)
                  (> p 0)
                  (<= (abs (- 1 (* b y1))) ep1)
                  (<= (abs (- 1 (* b y2))) ep2))
             (<= (abs (- 1 (* b y3)))
                 ep3)))
  :rule-classes ())

(defund h-excps (d p)
  (if (zp d)
      ()
    (cons (- 2 (* (expt 2 (- 1 p)) d))
          (h-excps (1- d) p))))

(defthm harrison-lemma
  (let ((y (rne yp p))
        (d (cg (* (expt 2 (* 2 p)) ep))))
    (implies (and (rationalp b)
                  (rationalp yp)
                  (rationalp ep)
                  (integerp p)
                  (> p 1)
                  (<= 1 b)
                  (< b 2)
                  (exactp b p)
                  (not (member b (h-excps d p)))
                  (< ep (expt 2 (- (1+ p))))
                  (<= (abs (- 1 (* b yp))) ep))
             (< (abs (- 1 (* b y))) (expt 2 (- p)))))
  :rule-classes ())
)

;;;**********************************************************************
;;;		    	      Examples
;;;**********************************************************************

(defsection-rtl |Examples| |FMA-Based Division|

(defun rcp0 () '(134217725 133177280 132152840 131144040 130150521
  129171946 128207980 127258288 126322566 125400505 124491806
  123596178 122713348 121843044 120984994 120138944 119304646
  118481854 117670336 116869856 116080194 115301132 114532460
  113773968 113025454 112286728 111557592 110837866 110127368
  109425916 108733350 108049488 107374182 106707262 106048574
  105397968 104755298 104120420 103493188 102873470 102261126
  101656030 101058054 100467072 99882960 99305602 98734878 98170678
  97612894 97061406 96516116 95976924 95443718 94916402 94394884
  93879066 93368852 92864160 92364888 91870956 91382282 90898780
  90420364 89946956 89478486 89014868 88556026 88101890 87652394
  87207458 86767016 86331002 85899346 85471986 85048856 84629897
  84215046 83804240 83397422 82994534 82595524 82200330 81808902
  81421180 81037118 80656663 80279762 79906366 79536432 79169904
  78806738 78446892 78090313 77736964 77386800 77039774 76695844
  76354973 76017120 75682240 75350304 75021262 74695082 74371728
  74051160 73733342 73418242 73105826 72796056 72488900 72184324
  71882297 71582788 71285764 70991194 70699052 70409300 70121914
  69836868 69554126 69273666 68995460 68719478 68445694 68174084
  67904624 67637280 67372036))

(defun rcp1 () '(131067 129044 127066 125134 123244 121398 119594 117828
  116102 114414 112762 111144 109562 108014 106498 105014 103560
  102136 100742 99376 98038 96726 95442 94182 92946 91736 90548 89384
  88242 87120 86022 84942 83884 82846 81826 80824 79842 78878 77930
  77000 76086 75188 74306 73440 72588 71752 70928 70120 69326 68544
  67776 67022 66280 65548 64830 64124 63428 62746 62072 61410 60758
  60118 59486 58864 58254 57652 57058 56474 55900 55334 54776 54228
  53686 53154 52628 52111 51602 51100 50604 50116 49636 49162 48696
  48234 47780 47333 46892 46456 46028 45604 45186 44776 44368 43968
  43574 43184 42798 42419 42044 41674 41310 40950 40594 40244 39898
  39556 39218 38886 38557 38232 37912 37595 37282 36974 36668 36368
  36070 35776 35486 35200 34916 34636 34360 34086 33816 33550 33286
  33026))

(defun rcp2 () '(4047 3956 3864 3780 3690 3608 3532 3452 3378 3307 3236
  3164 3096 3032 2968 2908 2844 2784 2728 2676 2624 2568 2524 2472
  2420 2376 2328 2288 2244 2196 2160 2116 2076 2040 2004 1960 1928
  1896 1860 1828 1796 1764 1732 1704 1672 1648 1612 1588 1560 1532
  1508 1484 1464 1432 1412 1392 1364 1348 1324 1304 1280 1264 1240
  1220 1208 1188 1164 1148 1132 1116 1096 1084 1064 1052 1032 1018
  1004 992 972 960 948 932 924 904 892 882 872 856 848 832 820 816 798
  788 784 772 756 750 736 728 720 712 700 692 684 676 664 660 650 640
  636 626 616 612 600 596 588 580 572 572 560 552 548 540 532 528 524
  520))

(defun rcp24 (b)
  (let* ((i (fl (* (expt 2 7) (1- b))))
         (x (- b (1+ (* (expt 2 -7) i))))
         (c0 (* (expt 2 -27) (nth i (rcp0))))
         (c1 (- (* (expt 2 -17) (nth i (rcp1)))))
         (c2 (* (expt 2 -12) (nth i (rcp2)))))
    (rne (+ c0 (* c1 x) (* c2 x x)) 24)))

(defthm rcp24-spec
  (implies (and (rationalp b)
                (exactp b 24)
                (<= 1 b)
                (< b 2))
           (and (exactp (rcp24 b) 24)
                (<= 1/2 (rcp24 b))
                (<= (rcp24 b) 1)
                (< (abs (- 1 (* b (rcp24 b)))) (expt 2 -23))))
  :rule-classes ())

(defund divsp (a b mode)
  (let* ((y0 (rcp24 b))
         (q0 (rne (* a y0) 24))
         (e0 (rne (- 1 (* b y0)) 24))
         (r0 (rne (- a (* b q0)) 24))
         (y1 (rne (+ y0 (* e0 y0)) 24))
         (q1 (rne (+ q0 (* r0 y1)) 24))
         (r1 (rne (- a (* b q1)) 24)))
    (rnd (+ q1 (* r1 y1)) mode 24)))

(defthm divsp-small-cases
  (implies (and (not (zp k))
                (<= k 7))
           (let* ((b (- 2 (* (expt 2 -23) k)))
                  (y0 (rcp24 b))
                  (e0 (rne (- 1 (* b y0)) 24))
                  (y1 (rne (+ y0 (* e0 y0)) 24)))
             (< (abs (- 1 (* b y1)))
                (expt 2 -24))))
  :rule-classes ())

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
  :rule-classes ())

(defthm rcp24-rtz-error
  (implies (and (rationalp b)
                (<= 1 b)
                (< b 2))
           (<= (abs (- 1 (* b (rcp24 (rtz b 24))))) (expt 2 -22)))
  :rule-classes ())

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
  :rule-classes ())

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
  :rule-classes ())
)
