; (value :q)
; (ccl::gc-verbose nil nil)
; (lp)
; (include-book "tmi-reductions")
; (time$ (with-output :off :all (certify-book "implementation" 1)))
; Timings on Whitehart:
; Mon Jul 16 09:26:20 2012
; 86.29 seconds realtime, 77.47 seconds runtime

(in-package "M1")
(include-book "defsys")

(defthm nst-out-bound
  (implies (natp w)
           (< (nst-out cell w) (expt 2 w)))
  :hints (("Goal" :in-theory (enable nst-out)))
  :rule-classes :linear)

(defthm current-symn-bound
  (< (current-symn tape pos) 2)
  :hints (("Goal" :in-theory (enable current-symn)))
  :rule-classes :linear)

(defun ninstr1 (st sym tm w nnil)
  (if (natp w)
      (if (zp tm)
          -1
          (if (equal tm nnil)
              -1
              (let ((cell (ncar tm w)))
                (if (and (equal st (nst-in cell w))
                         (equal sym (nsym cell w)))
                    cell
                    (ninstr1 st sym (ncdr tm w) w nnil)))))
      -1))

(defthm ninstr1-nnil-is-ninstr
  (equal (ninstr1 st sym tm w (nnil w))
         (ninstr st sym tm w))
  :hints (("Goal" :in-theory (enable ninstr))))

(in-theory (enable nst-in nsym nop nst-out ncar ncdr current-symn new-tape2))

(defsys :ld-flg nil
  :modules
  ((lessp :formals (x y)
          :input (and (natp x)
                      (natp y))
          :output (if (< x y) 1 0)
          :code (ifeq y
                      0
                      (ifeq x
                            1
                            (lessp (- x 1) (- y 1)))))
   (mod :formals (x y)
        :input (and (natp x)
                    (natp y)
                    (not (equal y 0)))
        :output (mod x y)
        :code (ifeq (lessp x y)
                    (mod (- x y) y)
                    x))
   (floor :formals (x y a)
          :input (and (natp x)
                      (natp y)
                      (not (equal y 0))
                      (natp a))
          :output (+ a (floor x y))
          :code (ifeq (lessp x y)
                      (floor (- x y) y (+ a 1))
                      a))
   (log2 :formals (x a)
         :input (and (natp x)
                     (natp a))
         :output (+ a (log2 x))
         :code (ifeq x
                     a
                     (ifeq (- x 1)
                           a
                           (log2 (floor x 2 0) (+ 1 a)))))
   (expt :formals (x n a)
         :input (and (natp x)
                     (natp n)
                     (natp a))
         :output (* a (expt x n))
         :code (ifeq n
                     a
                     (expt x (- n 1) (* x a))))
   (nst-in :formals (cell w)
           :input (and (natp cell)
                       (natp w))
           :output (nst-in cell w)
           :code (mod cell (expt 2 w 1)))

   (nsym :formals (cell w)
         :input (and (natp cell) (natp w))
         :output (nsym cell w)
         :code (mod (floor cell (expt 2 w 1) 0) 2))

   (nop :formals (cell w)
        :input (and (natp cell) (natp w))
        :output (nop cell w)
        :code (mod (floor cell (expt 2 (+ 1 w) 1) 0)
                   8))

   (nst-out :formals (cell w)
            :input (and (natp cell) (natp w))
            :output (nst-out cell w)
            :code (mod (floor cell (expt 2 (+ 4 w) 1) 0)
                       (expt 2 w 1)))

   (ncar :formals (tm w)
         :input (and (natp tm) (natp w))
         :output (ncar tm w)
         :code (mod tm (expt 2 (+ 4 (* 2 w)) 1)))

   (ncdr :formals (tm w)
         :input (and (natp tm) (natp w))
         :output (ncdr tm w)
         :code (floor tm (expt 2 (+ 4 (* 2 w)) 1) 0))

   (current-symn :formals (tape pos)
                 :input (and (natp tape)
                             (natp pos))
                 :output (current-symn tape pos)
                 :code (ifeq (- pos (log2 tape 0))
                             0
                             (mod (floor tape (expt 2 pos 1) 0)
                                  2)))

   (ninstr1 :formals (st sym tm w nnil)
            :input (and (natp st)
                        (natp sym)
                        (natp tm)
                        (natp w)
                        (equal nnil (nnil w)))
            :output (ninstr1 st sym tm w nnil)
            :code
            (ifeq tm
                  -1
                  (ifeq (- tm nnil)
                        -1
                        (ifeq (ifeq (- st (nst-in (ncar tm w) w))
                                    (- sym (nsym (ncar tm w) w))
                                    1)
                              (ncar tm w)
                              (ninstr1 st sym (ncdr tm w) w nnil)))))

   (new-tape2 :formals (op tape pos)
              :input (and (natp op)
                          (natp tape)
                          (natp pos))
              :output (mv (acl2::mv-nth 0 (new-tape2 op tape pos))
                          (acl2::mv-nth 1 (new-tape2 op tape pos)))
              :code
              (ifeq (ifeq op
                          0
                          (ifeq (- op 1)
                                0
                                1))
                    (ifeq (- pos (log2 tape 0))
                          (ifeq op
                                (mv (+ tape (expt 2 pos 1)) pos)
                                (mv (+ tape (expt 2 (+ pos 1) 1)) pos))
                          (ifeq (- (current-symn tape pos) op)
                                (mv tape pos)
                                (ifeq (current-symn tape pos)
                                      (mv (+ tape (expt 2 pos 1)) pos)
                                      (mv (- tape (expt 2 pos 1)) pos))))
                    (ifeq (- op 2)
                          (ifeq pos
                                (mv (* 2 tape) 0)
                                (mv tape (- pos 1)))

                          (ifeq (- pos (log2 tape 0))
                                (mv (+ (- tape (expt 2 pos 1))
                                       (expt 2 (+ 1 pos) 1))
                                    (+ 1 pos))
                                (mv tape (+ pos 1)))))
              :ghost-base-value (mv tape pos))

   (tmi3 :formals (st tape pos tm w nnil)
         :dcls ((declare (xargs :measure (acl2-count n))))
         :input (and (natp st)
                     (natp tape)
                     (natp pos)
                     (natp tm)
                     (natp w)
                     (equal nnil (nnil w))
                     (< st (expt 2 w)))
         :output (tmi3 st tape pos tm w n) ; the logic's tmi3 doesn't take nnil as an arg.
         :output-arity 4
         :code
         (ifeq (- (ninstr1 st (current-symn tape pos) tm w nnil) -1)
               (mv 1 st tape pos)
               (tmi3 (nst-out (ninstr1 st (current-symn tape pos) tm w nnil)
                              w)
                     (new-tape2 (nop (ninstr1 st (current-symn tape pos) tm w nnil)
                                     w)
                                tape pos)
                     tm w nnil))
         :ghost-formals (n)
         :ghost-base-test (zp n)
         :ghost-base-value (mv 0 st tape pos)
         :ghost-decr ((- n 1)))

   (main :formals (st tape pos tm w nnil)
         :input (and (natp st)
                     (natp tape)
                     (natp pos)
                     (natp tm)
                     (natp w)
                     (equal nnil (nnil w))
                     (< st (expt 2 w)))
         :output (tmi3 st tape pos tm w n)
         :output-arity 4
         :code (tmi3 st tape pos tm w nnil)
         :ghost-formals (n)
         :ghost-base-value (mv 0 st tape pos)))
  :edit-commands
  ((defun !ninstr1
     :before
     ((defthm natp-ncar
        (implies (natp tm)
                 (natp (ncar tm w)))
        :rule-classes :type-prescription)

      (defthm natp-ncdr-x
        (implies (natp tm)
                 (natp (ncdr tm w)))
        :rule-classes :type-prescription)

      (in-theory (disable ncar ncdr))

      (defthm natp-nst-in
        (implies (natp cell)
                 (natp (nst-in cell w)))
        :rule-classes :type-prescription)

; The type-prescriptions for nsym, nop, and nst-out specify NATP.

      (in-theory (disable nst-in nsym nop nst-out))

; The type-prescription for current-symn specifies NATP.

      (in-theory (disable current-symn))
      ))
   (defun !tmi3
     :before
     ((defthm integerp-ninstr1
        (implies (and (natp st)
                      (natp sym)
                      (natp tm)
                      (natp w)
                      (equal nnil (nnil w)))
                 (and (integerp (ninstr1 st sym tm w nnil))
                      (<= -1 (ninstr1 st sym tm w nnil))))
        :rule-classes
        ((:type-prescription
          :corollary
          (implies (and (natp st)
                        (natp sym)
                        (natp tm)
                        (natp w)
                        (equal nnil (nnil w)))
                   (integerp (ninstr1 st sym tm w nnil))))
         (:linear
          :corollary
          (implies (and (natp st)
                        (natp sym)
                        (natp tm)
                        (natp w)
                        (equal nnil (nnil w)))
                   (<= -1 (ninstr1 st sym tm w nnil))))
         (:rewrite
          :corollary
          (implies (and (natp st)
                        (natp sym)
                        (natp tm)
                        (natp w)
                        (equal nnil (nnil w))
                        (not (equal (ninstr1 st sym tm w nnil) -1)))
                   (and (integerp (ninstr1 st sym tm w nnil))
                        (<= 0 (ninstr1 st sym tm w nnil)))))))

      (defthm integerp-ninstr
        (implies (and (natp st)
                      (natp sym)
                      (natp tm)
                      (natp w))
                 (and (integerp (ninstr st sym tm w))
                      (<= -1 (ninstr st sym tm w))))
        :rule-classes
        ((:type-prescription
          :corollary
          (implies (and (natp st)
                        (natp sym)
                        (natp tm)
                        (natp w))
                   (integerp (ninstr st sym tm w))))
         (:linear
          :corollary
          (implies (and (natp st)
                        (natp sym)
                        (natp tm)
                        (natp w))
                   (<= -1 (ninstr st sym tm w))))
         (:rewrite
          :corollary
          (implies (and (natp st)
                        (natp sym)
                        (natp tm)
                        (natp w)
                        (not (equal (ninstr st sym tm w) -1)))
                   (and (integerp (ninstr st sym tm w))
                        (<= 0 (ninstr st sym tm w)))))))

      (defthm natp-mv-nth-0-new-tape2
        (implies (and (natp tape)
                      (natp pos))
                 (natp (acl2::mv-nth 0 (new-tape2 op tape pos))))
        :hints (("Goal" :nonlinearp t :in-theory (enable current-symn)))
        :rule-classes :type-prescription)

      (defthm natp-mv-nth-1-new-tape2
        (implies (and (natp tape)
                      (natp pos))
                 (natp (acl2::mv-nth 1 (new-tape2 op tape pos))))
        :hints (("Goal" :nonlinearp t :in-theory (enable current-symn)))
        :rule-classes :type-prescription)

      (in-theory (disable  ncar  ncdr  ninstr1  new-tape2  current-symn
                           !ncar !ncdr !ninstr1 !new-tape2 !current-symn
                           nst-in  nst-out  nop  nsym
                           !nst-in !nst-out !nop !nsym))))
   (defthm !tmi3-spec
     :hints
     (("Subgoal *1/10'" :expand (!TMI3 ST TAPE POS TM W (NNIL W) N))))))


