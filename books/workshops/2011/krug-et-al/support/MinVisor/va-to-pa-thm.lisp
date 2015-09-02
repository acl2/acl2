
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; We set the page tables up correctly
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "setup-nested-page-tables")

;;;(set-gag-mode :goals)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "arithmetic-5/top" :dir :system)

(encapsulate
 ()

 (local
  (defun ind-fn (x y)
    (cond ((zip x)
           y)
          ((equal x -1)
           y)
          (t
           (ind-fn (floor x 2) (floor y 2))))))

 (defthm |(logand x (logior x y))|
   (implies (integerp x)
            (equal (logand x (logior x y))
                   x))
   :hints (("Goal" :induct (ind-fn x y))))
 )

(in-theory (disable of sf zf
                   subl-cf
                   create_nested_pt-exists-next-exitpoint
                   create_nested_pt-modify))

(defthm va-to-pa-when-paging
  (implies (y86-p s)
           (equal (va-to-pa addr (set-paging t s))
                  (get-pa addr s)))
  :hints (("Goal" :in-theory (enable va-to-pa
                                     set-paging
                                     paging-p
                                     get-bit-32
                                     set-bit-32
                                     get-pa)))
  :otf-flg t)

;;; va-to-pa is in terms of r32-low, but we wnat to reason about r32
(encapsulate
 ()

 (defthm crock-1-1
   (implies (and (integerp x)
                 (integerp n1)
                 (integerp n2)
                 (<= n1 n2))
            (equal (logand (expt 2 n2)
                           (mod x (expt 2 n1)))
                   0))
   :hints (("Goal" :use ((:instance logand-mask-shifted
                                    (x (mod x (expt 2 n1)))
                                    (n1 n2)
                                    (n2 1))))))

 (defthm crock-1
   (implies (y86-p s)
            (equal (VA-TO-PA ADDR (SET-PAGING NIL S))
                   addr))
   :hints (("Goal" :in-theory (enable va-to-pa
                                      set-paging
                                      paging-p
                                      get-bit-32
                                      set-bit-32)
                   :use ((:instance crock-1-1
                                    (x (g :CR0 s))
                                    (n1 31)
                                    (n2 31))))))

 (defthm crock-2
   (equal (g :mem (set-paging flag s))
          (g :mem s))
   :hints (("Goal" :in-theory (enable set-paging))))

 (defthm r32-low-thm
   (implies (and  (y86-p s)
                  (n32p addr))
            (equal (r32-low addr (g :mem s))
                   (r32 addr (set-paging nil s))))
   :hints (("Goal" :in-theory (enable r32))))
 )

(defthm |(g :cr3 (set-paging flag s))|
  (equal (g :cr3 (set-paging flag s))
         (g :cr3 s))
   :hints (("Goal" :in-theory (enable set-paging))))

(defthm |(paging-p (set-paging t s))|
  (paging-p (set-paging t s))

   :hints (("Goal" :in-theory (enable paging-p
                                      set-paging
                                      get-bit-32
                                      set-bit-32))))



;;; Why was this so darned hard?
(encapsulate
 ()

 (local
  (defthm crock-300-1
    (implies (and (n32p x)
                  (equal (logand (expt 2 31)
                                 x)
                         0))
             (equal (logand (+ -1 (expt 2 31))
                            x)
                    x))
    :hints (("Goal" :use ((:instance logand-mask-shifted
                                     (n1 31)
                                     (n2 1)))))))


 (local
  (defthm crock-300
    (implies (create_nested_pt-pre s)
             (equal (SET-BIT-32 31 NIL (G :CR0 S))
                    (g :cr0 s)))
    :hints (("Goal" :in-theory (e/d (paging-p
                                     get-bit-32
                                     set-bit-32)

                                    (ash-to-floor
                                     logand-constant-mask))
             :use ((:instance crock-300-1
                              (x (g :cr0 s))))))))

 (defthm |(SET-PAGING NIL (CREATE_NESTED_PT-MODIFY S))|
   (implies (create_nested_pt-pre s)
            (equal (SET-PAGING NIL (CREATE_NESTED_PT-MODIFY S))
                   (CREATE_NESTED_PT-MODIFY S)))
   :hints (("Goal" :in-theory (e/d (set-paging)
                                   (create_nested_pt-pre
                                    |(g :cr0 (create_nested_pt-modify s))|))
            :use ((:instance  |(g :cr0 (create_nested_pt-modify s))|))
            :do-not '(generalize eliminate-destructors)))
   :otf-flg t)
 )




(defthm pasting-1
  (implies (n32p x)
           (n32p (+ (* 8 (PDPT-INDEX x))
                    (PG-ALIGN y))))
  :hints (("Goal" :in-theory (enable pdpt-index
                                     pg-align)))
  :otf-flg t)

(defthm pasting-2
  (implies (n32p x)
           (n32p (+ (* 8 (PDT-INDEX x))
                    (PG-ALIGN y))))
  :hints (("Goal" :in-theory (enable pdt-index
                                     pg-align)))
  :otf-flg t)

(defthm pasting-1a
  (implies (n32p x)
           (n32p (+ (* 8 (ASH x -30))
                    (LOGAND y *PG-MASK*))))
  :hints (("Goal" :in-theory (enable pdpt-index
                                     pg-align)))
  :otf-flg t)

(defthm pasting-2a
  (implies (n32p x)
           (n32p (+ (* 8 (LOGAND (ASH x -21)
                                 (1- (EXPT 2 9))))
                    (LOGAND y *PG-MASK*))))
  :hints (("Goal" :in-theory (enable pdt-index
                                     pg-align)))
  :otf-flg t)






(local
  (defthm ash-thm-100
    (implies (n32p x)
             (and (<= 0 (ash x -30))
                  (< (ash x -30) 4)))
    :hints (("Goal" :in-theory (enable ash-to-floor)))
    :rule-classes :linear))

;;; This theorem could be simplified or generalized
(defthm pg-align-reduction
  (implies (and (n32p addr)
                (EQUAL (LOGAND 4294963200
                               (R32 (+ 12 (R32 (+ 8 (G :ESP S0)) S0))
                                    S0))
                       (R32 (+ 12 (R32 (+ 8 (G :ESP S0)) S0))
                            S0))
                (EQUAL (LOGAND 4294963200
                               (R32 (+ 8 (R32 (+ 8 (G :ESP S0)) S0))
                                    S0))
                       (R32 (+ 8 (R32 (+ 8 (G :ESP S0)) S0))
                            S0))
                (EQUAL (LOGAND 4294963200
                               (R32 (+ 4 (R32 (+ 8 (G :ESP S0)) S0))
                                    S0))
                       (R32 (+ 4 (R32 (+ 8 (G :ESP S0)) S0))
                            S0))
                (EQUAL (LOGAND 4294963200
                               (R32 (R32 (+ 8 (G :ESP S0)) S0) S0))
                       (R32 (R32 (+ 8 (G :ESP S0)) S0) S0)))
           (equal (LOGAND 4294963200
                          (R32 (+ (* 4 (ASH ADDR -30))
                                  (R32 (+ 8 (G :ESP S0)) S0))
                               S0))
                  (R32 (+ (* 4 (ASH ADDR -30))
                          (R32 (+ 8 (G :ESP S0)) S0))
                       S0)))
  :hints (("Goal" :cases ((equal (ASH ADDR -30) 0)
                          (equal (ASH ADDR -30) 1)
                          (equal (ASH ADDR -30) 2)
                          (equal (ASH ADDR -30) 3)))))



(defthm pasting-2b
  (implies (and (n32p addr1)
                (equal addr2
                       (logand addr2 *pg-mask*)))
           (n32p (+ (* 8 (mod (ash addr1 -21) 512))
                    addr2))))


(defthm |(present-bit-p (logior 1 x))|
  (present-bit-p (logior 1 x))
  :hints (("Goal" :in-theory (enable present-bit-p
                                     get-bit-32))))

(defthm |(present-bit-p (logior 231 x))|
  (present-bit-p (logior 231 x))
  :hints (("Goal" :in-theory (enable present-bit-p
                                     get-bit-32))))

(defthm |(ash (logand 1071644672 x) -21)|
  (equal (ash (logand 1071644672 x) -21)
         (mod (ash x -21) 512))
  :hints (("Goal" :use ((:instance logand-mask-shifted
                                   (n1 21)
                                   (n2 9))))))





(local
  (encapsulate
   ()

   (local
    (defthm crock-333-1
      (not (memberp x nil))
      :hints (("Goal" :in-theory (enable memberp)))))

   (local
    (defthm crock-333
      (implies (and (integerp x)
                    (integerp start)
                    (integerp end)
                    (< x start)
                    (not (memberp x acc)))
               (not (memberp x (range-1 start end acc))))
      :hints (("Goal" :in-theory (enable range-1
                                         memberp)))))

   (local
    (defthm crock-334
      (implies (and (integerp x)
                    (integerp start)
                    (integerp end)
                    (< end x)
                    (not (memberp x acc)))
               (not (memberp x (range-1 start end acc))))
      :hints (("Goal" :in-theory (enable range-1
                                         memberp)))))

   (local
    (defthm crock-335-1
      (implies (memberp x acc)
               (memberp x (range-1 start end acc)))
      :hints (("Goal" :in-theory (enable range-1
                                         memberp)))))

   (local
    (defthm crock-335
      (implies (and (integerp x)
                    (integerp start)
                    (integerp end)
                    (<= start end)
                    (<= start x)
                    (<= x end))
               (memberp x (range-1 start end acc)))
      :hints (("Goal" :in-theory (enable range-1
                                         memberp)
               :expand ((RANGE-1 END END ACC)
                        (RANGE-1 (+ -1 END) END ACC)
                        (RANGE-1 (+ -1 END)
                                 (+ -1 END)
                                 (CONS END ACC)))))))

   (defthm extra-disjointp-thm
     (implies (and (integerp x)
                   (integerp base)
                   (integerp offset)
                   (integerp length)
                   (< 0 length))
              (equal (disjointp (list (list x)
                                      (range base offset length)))
                     (or (< x
                            (+ base offset))
                         (<= (+ base offset length)
                             x))))
     :hints (("Goal" :in-theory (enable disjointp
                                        disjointp-1
                                        disjoint-bags-p
                                        range
                                        range-1)))
     :otf-flg t)
   ))

 (local
  (in-theory (disable extra-disjointp-thm)))









(encapsulate
 ()

 (local
  (defthm break-logand-apart
    (implies (and (integerp x)
                  (integerp y))
             (equal (logand x y)
                    (+ (* 2 (logand (floor x 2) (floor y 2)))
                       (logand (mod x 2) (mod y 2)))))
    :rule-classes nil))

 (local
  (defun ind-fn-3 (x y z)
    (cond ((zip x)
           (+ y z))
          ((equal x -1)
           42)
          (t
           (ind-fn-3 (floor x 2) (floor y 2) (floor z 2))))))

 (local
  (defthm crock-100-1
    (implies (and (integerp x)
                  (integerp y)
                  (integerp z))
             (equal (logior (logand x y) (logand x z))
                    (logand x (logior y z))))
    :hints (("Goal" :induct (ind-fn-3 x y z)))))

 (local
  (defthm crock-100
    (implies (integerp x)
             (equal (LOGAND 4292870144
                            (LOGIOR 231 x))
                    (logand 4292870144 x)))
    :hints (("Goal" :in-theory (disable crock-100-1)
             :use ((:instance crock-100-1
                              (x 4292870144)
                              (y 231)
                              (z x)))))))

 (defthm helper-1
   (implies (n32p addr)
            (EQUAL (+ (MOD ADDR 2097152)
                      (LOGAND 4292870144
                              (LOGIOR 231
                                      (+ (* 1073741824 (ASH ADDR -30))
                                         (* 2097152 (MOD (ASH ADDR -21) 512))))))
                   ADDR))
   :hints (("Goal" :use ((:instance logand-mask-shifted
                                    (x (+ (* 1073741824 (ASH ADDR -30))
                                          (* 2097152 (MOD (ASH ADDR -21) 512))))
                                    (n1 21)
                                    (n2 11))))))


 (defthm helper-2
   (implies (and (y86-p s)
                 (n32p addr)
                 (n32p (+ 4095 (r32 (r32 (+ 8 (g :esp s)) s) s)))
                 (n32p (+ 4095 (r32 (+ 4 (r32 (+ 8 (g :esp s)) s)) s)))
                 (n32p (+ 4095 (r32 (+ 8 (r32 (+ 8 (g :esp s)) s)) s)))
                 (n32p (+ 4095 (r32 (+ 12 (r32 (+ 8 (g :esp s)) s)) s))))
            (N32P (+ 3 (* 8 (MOD (ASH ADDR -21) 512))
                     (R32 (+ (* 4 (ASH ADDR -30))
                             (R32 (+ 8 (G :ESP S)) S))
                          S))))
   :hints (("Goal" :cases ((equal (ASH ADDR -30) 0)
                           (equal (ASH ADDR -30) 1)
                           (equal (ASH ADDR -30) 2)
                           (equal (ASH ADDR -30) 3))
            :in-theory (disable ash-to-floor)))
   :otf-flg t)

 (local
  (defthm crock-101
    (implies (n32p addr)
             (EQUAL (+ (MOD ADDR 2097152)
                       (* 1073741824 (ASH ADDR -30))
                       (* 2097152 (MOD (ASH ADDR -21) 512)))
                    ADDR))))

 (defthm helper-3
   (implies (and (y86-p s0)
                 (n32p addr)
                 (n32p (+ (R32 (+ 12 (G :ESP S0)) S0)
                          (R32 (+ 16 (G :ESP S0)) S0)))
                 (< (MOD (ASH ADDR -21) 512)
                    (MOD (ASH (R32 (+ 12 (G :ESP S0)) S0) -21)
                         512))
                 (EQUAL (ASH (+ (R32 (+ 12 (G :ESP S0)) S0)
                                (R32 (+ 16 (G :ESP S0)) S0))
                             -30)
                        (ASH (R32 (+ 12 (G :ESP S0)) S0) -30))
                 (<= (R32 (+ 12 (G :ESP S0)) S0) ADDR))
            (<= (+ (R32 (+ 12 (G :ESP S0)) S0)
                   (R32 (+ 16 (G :ESP S0)) S0))
                ADDR))
   :hints (("Goal" :in-theory (disable ash-to-floor
                                       crock-101)
            :cases ((< (ASH (R32 (+ 12 (G :ESP S0)) S0) -30)
                       (ASH ADDR -30))
                    (< (ASH ADDR -30)
                       (ASH (R32 (+ 12 (G :ESP S0)) S0) -30)))
            :use ((:instance crock-101
                             (addr addr))
                  (:instance crock-101
                             (addr (+ (R32 (+ 12 (G :ESP S0)) S0)
                                      (R32 (+ 16 (G :ESP S0)) S0))))
                  (:instance crock-101
                             (addr (R32 (+ 12 (G :ESP S0)) S0))))))
   :otf-flg t)

 (defthm helper-4
   (implies (and (y86-p s0)
                 (n32p addr)
                 (EQUAL (ASH ADDR -30)
                        (ASH (R32 (+ 12 (G :ESP S0)) S0) -30))
                 (<= (MOD (ASH (R32 (+ 12 (G :ESP S0)) S0) -21)
                          512)
                     (MOD (ASH ADDR -21) 512))
                 (EQUAL (LOGAND 4292870144
                                (R32 (+ 12 (G :ESP S0)) S0))
                        (R32 (+ 12 (G :ESP S0)) S0)))
            (<= (R32 (+ 12 (G :ESP S0)) S0) ADDR))
   :hints (("Goal" :in-theory (disable ash-to-floor
                                       crock-101)
            :use ((:instance crock-101
                             (addr addr))
                  (:instance crock-101
                             (addr (R32 (+ 12 (G :ESP S0)) S0)))
                  (:instance logand-mask-shifted
                             (x (R32 (+ 12 (G :ESP S0)) S0))
                             (n1 21)
                             (n2 11)))))
   :otf-flg t)


 (defthm helper-5
   (implies (and (n32p addr)
                 (y86-p s0)
                 (< (MOD (ASH ADDR -21) 512)
                    (MOD (ASH (+ (R32 (+ 12 (G :ESP S0)) S0)
                                 (R32 (+ 16 (G :ESP S0)) S0))
                              -21)
                         512))
                 (EQUAL (ASH (+ (R32 (+ 12 (G :ESP S0)) S0)
                                (R32 (+ 16 (G :ESP S0)) S0))
                             -30)
                        (ASH ADDR -30)))
            (< ADDR
               (+ (R32 (+ 12 (G :ESP S0)) S0)
                  (R32 (+ 16 (G :ESP S0)) S0))))
   :hints (("Goal" :in-theory (disable ash-to-floor
                                       crock-101)
            :use ((:instance crock-101
                             (addr addr))
                  (:instance crock-101
                             (addr (+ (R32 (+ 12 (G :ESP S0)) S0)
                                      (R32 (+ 16 (G :ESP S0)) S0)))))))
   :otf-flg t)


 (defthm helper-6
   (implies (and (n32p addr)
                 (y86-p s0)
                 (n32p (+ (R32 (+ 12 (G :ESP S0)) S0)
                          (R32 (+ 16 (G :ESP S0)) S0)))
                 (< (MOD (ASH (+ (R32 (+ 12 (G :ESP S0)) S0)
                                 (R32 (+ 16 (G :ESP S0)) S0))
                              -21)
                         512)
                    (+ 1 (MOD (ASH ADDR -21) 512)))
                 (EQUAL (ASH (+ (R32 (+ 12 (G :ESP S0)) S0)
                                (R32 (+ 16 (G :ESP S0)) S0))
                             -30)
                        (ASH (R32 (+ 12 (G :ESP S0)) S0) -30))
                 (EQUAL (LOGAND 4292870144 (R32 (+ 12 (G :ESP S0)) S0))
                        (R32 (+ 12 (G :ESP S0)) S0))
                 (EQUAL (LOGAND 4292870144 (R32 (+ 16 (G :ESP S0)) S0))
                        (R32 (+ 16 (G :ESP S0)) S0))
                 (<= (R32 (+ 12 (G :ESP S0)) S0) ADDR))
            (<= (+ (R32 (+ 12 (G :ESP S0)) S0)
                   (R32 (+ 16 (G :ESP S0)) S0))
                ADDR))
   :hints (("Goal" :in-theory (disable ash-to-floor
                                       crock-101)
            :cases ((< (ASH (R32 (+ 12 (G :ESP S0)) S0) -30)
                       (ASH ADDR -30))
                    (< (ASH ADDR -30)
                       (ASH (R32 (+ 12 (G :ESP S0)) S0) -30)))
            :use ((:instance crock-101
                             (addr addr))
                  (:instance crock-101
                             (addr (+ (R32 (+ 12 (G :ESP S0)) S0)
                                      (R32 (+ 16 (G :ESP S0)) S0))))
                  (:instance crock-101
                             (addr (R32 (+ 12 (G :ESP S0)) S0)))

                  (:instance logand-mask-shifted
                             (x (R32 (+ 12 (G :ESP S0)) S0))
                             (n1 21)
                             (n2 11))
                  (:instance logand-mask-shifted
                             (x (R32 (+ 16 (G :ESP S0)) S0))
                             (n1 21)
                             (n2 11)))))
   :otf-flg t)

 (defthm helper-7
   (implies (and (n32p addr)
                 (y86-p s0)
                 (n32p (+ (R32 (+ 12 (G :ESP S0)) S0)
                          (R32 (+ 16 (G :ESP S0)) S0)))
                 (NOT (EQUAL (ASH (R32 (+ 12 (G :ESP S0)) S0) -30)
                             (ASH ADDR -30)))
                 (EQUAL (ASH (+ (R32 (+ 12 (G :ESP S0)) S0)
                                (R32 (+ 16 (G :ESP S0)) S0))
                             -30)
                        (ASH (R32 (+ 12 (G :ESP S0)) S0) -30))
                 (<= (R32 (+ 12 (G :ESP S0)) S0) ADDR))
            (<= (+ (R32 (+ 12 (G :ESP S0)) S0)
                   (R32 (+ 16 (G :ESP S0)) S0))
                ADDR))
   :hints (("Goal" :in-theory (disable ash-to-floor
                                       crock-101)
            :use ((:instance crock-101
                             (addr addr))
                  (:instance crock-101
                             (addr (+ (R32 (+ 12 (G :ESP S0)) S0)
                                      (R32 (+ 16 (G :ESP S0)) S0))))
                  (:instance crock-101
                             (addr (R32 (+ 12 (G :ESP S0)) S0)))

                  (:instance logand-mask-shifted
                             (x (R32 (+ 12 (G :ESP S0)) S0))
                             (n1 21)
                             (n2 11))
                  (:instance logand-mask-shifted
                             (x (R32 (+ 16 (G :ESP S0)) S0))
                             (n1 21)
                             (n2 11)))))
   :otf-flg t)
 )


(defthm main-thm-Step-1
  (implies (and (create_nested_pt-pre s0)
                (create_nested_pt-exists-next-exitpoint s0)

                ;; the pdpt is 4k page-aligned
                (equal (PG-ALIGN (R32 (+ 4 (G :ESP S0)) S0))
                       (R32 (+ 4 (G :ESP S0)) S0))
                ;; visor-start and visor-size are multiples of 2M
                (equal (big-pg-align (R32 (+ 12 (G :ESP S0)) S0))
                       (R32 (+ 12 (G :ESP S0)) S0))
                (equal (big-pg-align (R32 (+ 16 (G :ESP S0)) S0))
                       (R32 (+ 16 (G :ESP S0)) S0))

                (n32p addr))

           (b* ((pdpt (r32 (+ 4 (g :esp s0)) s0))
                (visor-start (R32 (+ 12 (G :ESP S0)) S0))
                (visor-size (R32 (+ 16 (G :ESP S0)) S0))

                (s1 (create_nested_pt-modify s0))
                (s1 (s :cr3 pdpt s1))
                (s1 (set-paging t s1)))

               (equal (va-to-pa addr s1)
                      (if (disjointp (list (list addr)
                                           (range visor-start 0 visor-size)))
                          addr
                        :PAGE-FAULT))))

  :hints (("Goal" :in-theory (e/d (va-to-pa
                                     get-pa
                                     pg-align
                                     pdt-index
                                     pdpt-index

                                     big-pg-align
                                     addr-offset

                                     extra-disjointp-thm
                                     )
                                  (ash-to-floor

                                   evenp
                                   |(logior 1 x)|

                                   |(r32 addr (create_nested_pt-modify s)) --- init_pdts --- 1|
                                   |(r32 addr (create_nested_pt-modify s)) --- init_pdts --- 2|
                                   |(r32 addr (create_nested_pt-modify s)) --- sec_not_present|))
           :do-not '(generalize eliminate-destructors fertilize))
          ("Subgoal 5"
           :use ((:instance |(r32 addr (create_nested_pt-modify s)) --- init_pdts --- 1|
                                        (j-prime (MOD (ASH ADDR -21) 512))
                                        (i-prime (ASH ADDR -30))
                                        (s s0))
                 (:instance |(r32 addr (create_nested_pt-modify s)) --- init_pdts --- 2|
                                        (j-prime (MOD (ASH ADDR -21) 512))
                                        (i-prime (ASH ADDR -30))
                                        (s s0))
                 (:instance |(r32 addr (create_nested_pt-modify s)) --- sec_not_present|
                            (i-prime (MOD (ASH ADDR -21) 512))
                            (s s0))))
          ("Subgoal 5.2" :cases ((equal (ASH ADDR -30) 0)
                                  (equal (ASH ADDR -30) 1)
                                  (equal (ASH ADDR -30) 2)
                                  (equal (ASH ADDR -30) 3)))
          ("Subgoal 4"
           :use ((:instance |(r32 addr (create_nested_pt-modify s)) --- init_pdts --- 1|
                                        (j-prime (MOD (ASH ADDR -21) 512))
                                        (i-prime (ASH ADDR -30))
                                        (s s0))
                 (:instance |(r32 addr (create_nested_pt-modify s)) --- init_pdts --- 2|
                                        (j-prime (MOD (ASH ADDR -21) 512))
                                        (i-prime (ASH ADDR -30))
                                        (s s0))
                 (:instance |(r32 addr (create_nested_pt-modify s)) --- sec_not_present|
                            (i-prime (MOD (ASH ADDR -21) 512))
                            (s s0))))
          ("Subgoal 4.3" :cases ((equal (ASH ADDR -30) 0)
                                  (equal (ASH ADDR -30) 1)
                                  (equal (ASH ADDR -30) 2)
                                  (equal (ASH ADDR -30) 3)))
          ("Subgoal 3"
           :use ((:instance |(r32 addr (create_nested_pt-modify s)) --- init_pdts --- 1|
                                        (j-prime (MOD (ASH ADDR -21) 512))
                                        (i-prime (ASH ADDR -30))
                                        (s s0))
                 (:instance |(r32 addr (create_nested_pt-modify s)) --- init_pdts --- 2|
                                        (j-prime (MOD (ASH ADDR -21) 512))
                                        (i-prime (ASH ADDR -30))
                                        (s s0))
                 (:instance |(r32 addr (create_nested_pt-modify s)) --- sec_not_present|
                            (i-prime (MOD (ASH ADDR -21) 512))
                            (s s0))))

          ("Subgoal 3.22" :cases ((equal (ASH (R32 (+ 12 (G :ESP S0)) S0) -30) 0)
                                  (equal (ASH (R32 (+ 12 (G :ESP S0)) S0) -30) 1)
                                  (equal (ASH (R32 (+ 12 (G :ESP S0)) S0) -30) 2)
                                  (equal (ASH (R32 (+ 12 (G :ESP S0)) S0) -30) 3)))
          ("Subgoal 3.20" :cases ((equal (ASH (R32 (+ 12 (G :ESP S0)) S0) -30)
                                         (ASH ADDR -30))))
          ("Subgoal 3.18" :cases ((equal (ASH (R32 (+ 12 (G :ESP S0)) S0) -30) 0)
                                  (equal (ASH (R32 (+ 12 (G :ESP S0)) S0) -30) 1)
                                  (equal (ASH (R32 (+ 12 (G :ESP S0)) S0) -30) 2)
                                  (equal (ASH (R32 (+ 12 (G :ESP S0)) S0) -30) 3)))

          ("Subgoal 3.16" :cases ((equal (ASH (R32 (+ 12 (G :ESP S0)) S0) -30)
                                         (ASH ADDR -30))))
          ("Subgoal 3.15" :cases ((equal (ASH (R32 (+ 12 (G :ESP S0)) S0) -30)
                                         (ASH ADDR -30))))
          ("Subgoal 3.14" :cases ((equal (ASH (R32 (+ 12 (G :ESP S0)) S0) -30) 0)
                                  (equal (ASH (R32 (+ 12 (G :ESP S0)) S0) -30) 1)
                                  (equal (ASH (R32 (+ 12 (G :ESP S0)) S0) -30) 2)
                                  (equal (ASH (R32 (+ 12 (G :ESP S0)) S0) -30) 3)))
          ("Subgoal 3.12" :cases ((equal (ASH (R32 (+ 12 (G :ESP S0)) S0) -30)
                                         (ASH ADDR -30))))
          ("Subgoal 3.11" :cases ((equal (ASH (R32 (+ 12 (G :ESP S0)) S0) -30) 0)
                                  (equal (ASH (R32 (+ 12 (G :ESP S0)) S0) -30) 1)
                                  (equal (ASH (R32 (+ 12 (G :ESP S0)) S0) -30) 2)
                                  (equal (ASH (R32 (+ 12 (G :ESP S0)) S0) -30) 3)))
          ("Subgoal 3.9" :cases ((equal (ASH (R32 (+ 12 (G :ESP S0)) S0) -30)
                                         (ASH ADDR -30))))
          ("Subgoal 3.2" :cases ((equal (ASH ADDR -30) 0)
                                  (equal (ASH ADDR -30) 1)
                                  (equal (ASH ADDR -30) 2)
                                  (equal (ASH ADDR -30) 3)))
          ("Subgoal 2"
           :use ((:instance |(r32 addr (create_nested_pt-modify s)) --- init_pdts --- 1|
                                        (j-prime (MOD (ASH ADDR -21) 512))
                                        (i-prime (ASH ADDR -30))
                                        (s s0))
                 (:instance |(r32 addr (create_nested_pt-modify s)) --- init_pdts --- 2|
                                        (j-prime (MOD (ASH ADDR -21) 512))
                                        (i-prime (ASH ADDR -30))
                                        (s s0))
                 (:instance |(r32 addr (create_nested_pt-modify s)) --- sec_not_present|
                            (i-prime (MOD (ASH ADDR -21) 512))
                            (s s0))))
          ("Subgoal 1"
           :use ((:instance |(r32 addr (create_nested_pt-modify s)) --- init_pdts --- 1|
                                        (j-prime (MOD (ASH ADDR -21) 512))
                                        (i-prime (ASH ADDR -30))
                                        (s s0))
                 (:instance |(r32 addr (create_nested_pt-modify s)) --- init_pdts --- 2|
                                        (j-prime (MOD (ASH ADDR -21) 512))
                                        (i-prime (ASH ADDR -30))
                                        (s s0))
                 (:instance |(r32 addr (create_nested_pt-modify s)) --- sec_not_present|
                            (i-prime (MOD (ASH ADDR -21) 512))
                            (s s0))))
          )
  :otf-flg t)

(defthm main-thm
  (implies (and (create_nested_pt-pre s0)
                (create_nested_pt-exists-next-exitpoint s0)

                ;; the pdpt is 4k page-aligned
                (equal (PG-ALIGN (R32 (+ 4 (G :ESP S0)) S0))
                       (R32 (+ 4 (G :ESP S0)) S0))
                ;; visor-start and visor-size are multiples of 2M
                (equal (big-pg-align (R32 (+ 12 (G :ESP S0)) S0))
                       (R32 (+ 12 (G :ESP S0)) S0))
                (equal (big-pg-align (R32 (+ 16 (G :ESP S0)) S0))
                       (R32 (+ 16 (G :ESP S0)) S0))

                (n32p addr))

           (b* ((pdpt (r32 (+ 4 (g :esp s0)) s0))
                (visor-start (R32 (+ 12 (G :ESP S0)) S0))
                (visor-size (R32 (+ 16 (G :ESP S0)) S0))

                (s1 (create_nested_pt-next-exitpoint s0))
                (s1 (s :cr3 pdpt s1))
                (s1 (set-paging t s1)))

               (equal (va-to-pa addr s1)
                      (if (disjointp (list (list addr)
                                           (range visor-start 0 visor-size)))
                          addr
                        :PAGE-FAULT))))

  :hints (("Goal" :use ((:instance CREATE_NESTED_PT-CORRECT
                                   (s1 s0))
                        (:instance MAIN-THM-STEP-1))
           :in-theory (disable MAIN-THM-STEP-1
                               create_nested_pt-next-exitpoint
                               create_nested_pt-modify
                               in-create_nested_pt
                               create_nested_pt-pre))))
