(in-package "ACL2")

#||

; [Jared and Sol]: fool make_cert_help.pl into allowing more memory for this
; book. We would just include centaur/misc/memory-mgmt, but that has a ttag.

(set-max-mem (* 6 (expt 2 30)))

||#

(include-book "x86-state")
(include-book "std/lists/list-defuns" :dir :system)

(local
 (defmacro enable-stobj-fns-fn (x86-32-model)
   `(IN-THEORY
     (ENABLE ,@(disable-stobj-fns-fn-1 x86-32-model)))))

(local
 (make-event
  `(enable-stobj-fns-fn ,*x86-32-model*)))

(local (include-book "centaur/gl/gl" :dir :system))

(local (encapsulate ()

(local (include-book "arithmetic-5++"))

(defthm ash-thm-1
  (IMPLIES (AND (< I 4294967296)
                (<= 0 I)
                (INTEGERP I))
           (and (<= 0 (ASH I -24))
                (< (ASH I -24) 16777216)))
  :rule-classes :linear)

(defthm ash-thm-2
  (IMPLIES (AND (< I 4294967296)
                (<= 0 I)
                (INTEGERP I))
           (and (<= 0 (ASH I -24))
                (< (ASH I -24) 256)))
  :rule-classes :linear)

(defthm good-mem-table-entriesp-logic-property
  (let ((addr (nth i mem-table)))
    (implies (and (good-mem-table-entriesp-logic
                   z table-bound array-next-addr mem-table)
                  (integerp i)
                  (<= 0 i)
                  (<= z i)
                  (<= i table-bound)
                  (not (eql addr 1)))
             (and (natp addr)
                  (equal (logand 16777215 addr) 0)
                  (< (+ 16777215 addr) array-next-addr))))
  :hints (("Goal"
           :in-theory (enable good-mem-table-entriesp-logic)
           :induct (good-mem-table-entriesp-logic
                    z table-bound array-next-addr mem-table))))

(defthm logior-logand-2^24-1
  (implies (and (integerp x)
                (<= 0 x)
                (equal (logand 16777215 x) 0))
           (equal x (* *2^24* (floor x *2^24*))))
  :rule-classes nil)

(encapsulate
 ()

; (Matt K., 10/2013: Changed rel8 to rel9.)
(local (include-book "rtl/rel9/support/lib3/log" :dir :system))

(defthm logior-logand-2^24-2
  (implies (and (integerp x1)
                (<= 0 x1)
                (n24p y))
           (equal (logior (* *2^24* x1) y)
                  (+ (* *2^24* x1) y)))
  :hints (("Goal"
           :in-theory (enable bvecp)
           :use ((:instance logior-expt
                            (n 24) (x x1))))))
) ;; End of encapsulate

(defthm logior-with-multiple-of-2^24
  (implies (and (integerp x)
                (<= 0 x)
                (equal (logand 16777215 x) 0)
                (n24p y))
           (equal (logior x y)
                  (+ x y)))
  :hints (("Goal"
           :use (logior-logand-2^24-1
                 (:instance logior-logand-2^24-2
                            (x1 (floor x *2^24*)))))))

(defthm logior-with-multiple-of-2^24-commuted
  (implies (and (integerp x)
                (<= 0 x)
                (equal (logand 16777215 x) 0)
                (n24p y))
           (equal (logior y x)
                  (+ x y))))

(defthm logand-mem-tablei-is-0
  (let ((addr (NTH I (NTH *MEM-TABLEI* X86-32))))
    (implies (and (force (x86-32p x86-32))
                  ;;(force (natp i))
                  (force (integerp i))
                  (force (<= 0 i))
                  (force (< i *mem-table-size*))
                  (not (eql addr 1)))
             (equal (logand 16777215 addr) 0)))
  :hints (("Goal" :in-theory (enable x86-32p
                                     x86-32p-pre
                                     good-memp
                                     mem-tablei
                                     mem-table-length))))

(defthm good-memp-linear-1
  (let ((addr (NTH I (NTH *MEM-TABLEI* X86-32))))
    (implies (and (force (x86-32p x86-32))
                  ;;(force (natp i))
                  (force (integerp i))
                  (force (<= 0 i))
                  (force (< i *mem-table-size*))
                  (not (eql addr 1)))
             (< (+ 16777215 addr) (nth *mem-array-next-addr* x86-32))))
  :hints (("Goal" :in-theory (enable x86-32p
                                     x86-32p-pre
                                     good-memp
                                     mem-tablei
                                     mem-array-next-addr
                                     mem-table-length)))
  :rule-classes :linear)

(defthm good-memp-linear-2
  (let ((addr (NTH I (NTH *MEM-TABLEI* X86-32))))
    (implies (and (not (eql addr 1))
                  (force (x86-32p x86-32))
                  (force (integerp i))
                  (force (<= 0 i))
                  ;;(force (natp i))
                  (force (< i *mem-table-size*)))
             (< (+ 16777215 addr) (len (nth *mem-arrayi* x86-32)))))
  :hints (("Goal" :in-theory (enable x86-32p
                                     x86-32p-pre
                                     good-memp
                                     mem-tablei
                                     mem-array-next-addr
                                     mem-table-length
                                     mem-array-length)))
  :rule-classes :linear)

(defthm crock-001
  (IMPLIES (AND (X86-32P X86-32)
                (< I 4294967296)
                (<= 0 I)
                (INTEGERP I)
                (NOT (EQUAL (NTH (ASH I -24) (NTH *MEM-TABLEI* X86-32))
                            1)))
           (< (LOGIOR (LOGAND 16777215 I)
                      (NTH (ASH I -24)
                           (NTH *MEM-TABLEI* X86-32)))
              (LEN (NTH *MEM-ARRAYI* X86-32))))
  :hints (("Goal" :in-theory (e/d (x86-32p
                                   x86-32p-pre
                                   good-memp)
                                  (good-memp-linear-2
                                   ))
           :use ((:instance good-memp-linear-2
                            (i (ash i -24)))))))

(defthm crock-002
  (IMPLIES (AND (X86-32P X86-32)
                (< I 4294967296)
                (<= 0 I)
                (INTEGERP I)
                (NOT (EQUAL (NTH (ASH I -24) (NTH *MEM-TABLEI* X86-32))
                            1)))
           (< (LOGIOR (LOGAND 16777215 I)
                      (NTH (ASH I -24)
                           (NTH *MEM-TABLEI* X86-32)))
              (NTH *MEM-ARRAY-NEXT-ADDR* X86-32)))
  :hints (("Goal" :in-theory (e/d (x86-32p
                                   x86-32p-pre
                                   good-memp)
                                  (good-memp-linear-1
                                   ))
           :use ((:instance good-memp-linear-1
                            (i (ash i -24)))))))
)) ;; End of local encapsulate


(defun memi (i x86-32)
  (declare (xargs :stobjs x86-32
                  :guard (and (integerp i)
                              (<= 0 i)
                              (< i *mem-size-in-bytes*)
                              (x86-32p x86-32))))
  (let* ((i-top (ash i (- *2^x-byte-pseudo-page*)))
         (addr (mem-tablei i-top x86-32)))
    (cond ((eql addr 1) ; page is not present
           *default-mem-value*)
          (t (let ((index (logior addr (logand 16777215 i))))
               (mem-arrayi index x86-32))))))

; Start proof obligations for guard verification for add-page.

(defthmd mem-array-next-addr-is-expected-mem-array-next-addr
  (implies (x86-32p x86-32)
           (equal (nth *mem-array-next-addr* x86-32)
                  (expected-mem-array-next-addr 0
                                                (mem-table-length x86-32)
                                                x86-32)))
  :hints (("Goal" :in-theory (enable mem-array-next-addr x86-32p))))

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm expected-mem-array-next-addr-bound-general
   (implies (and (equal 1 (nth j (nth *mem-tablei* x86-32)))
                 (natp i)
                 (natp j)
                 (natp k)
                 (<= i j)
                 (< j k)
                 (<= k *mem-table-size*))
            (<= (expected-mem-array-next-addr i k x86-32)
                (* *pseudo-page-size-in-bytes* (1- (- k i)))))
   :hints (("Goal" :expand ((expected-mem-array-next-addr j k x86-32))
            :use (expected-mem-array-in-parts)))
   :rule-classes nil)
) ;; End of encapsulate

(defthm expected-mem-array-next-addr-bound-linear
   (implies (and (equal 1 (nth i (nth *mem-tablei* x86-32))) ; i is free
                 (force (natp i))
                 (force (< i *mem-table-size*)))
            (<= (expected-mem-array-next-addr 0 *mem-table-size* x86-32)
                (- *mem-size-in-bytes* *pseudo-page-size-in-bytes*)))
   :hints (("Goal" ;:expand ((expected-mem-array-next-addr j k x86-32))
            :use ((:instance expected-mem-array-next-addr-bound-general
                             (i 0)
                             (j i)
                             (k *mem-table-size*)))))
   :rule-classes :linear)

(defthm mem-array-next-addr-increment-bound
  (implies (and (equal 1 (nth i (nth *mem-tablei* x86-32))) ; i is free
                (force (x86-32p x86-32))
                (force (natp i))
                (force (< i *mem-table-size*)))
           (<= (+ *pseudo-page-size-in-bytes* (nth *mem-array-next-addr* x86-32))
               *mem-size-in-bytes*))
  :hints (("Goal"
           :in-theory
           (enable mem-array-next-addr-is-expected-mem-array-next-addr)))
  :rule-classes :linear)

(local
(defthm crock-54973
  (implies (x86-32p x86-32)
           (and (integerp (nth *mem-array-next-addr* x86-32))
                (<= 0 (nth *mem-array-next-addr* x86-32))))
  :hints (("Goal" :use ((:instance NATP-MEM-ARRAY-NEXT-ADDR))))
  :rule-classes :type-prescription))

(defun add-page-x86-32 (i x86-32)
  (declare (xargs :stobjs x86-32
                  :guard (and (integerp i) ; index into mem-table
                              (<= 0 i)
                              (< i *mem-table-size*)
                              (x86-32p x86-32)
                              (equal 1 ; "page not present"
                                     (mem-tablei i x86-32)))))
  (let* ((addr (mem-array-next-addr x86-32))
         (len (mem-array-length x86-32))
         (x86-32 (cond ((eql addr len) ; must resize!
                        (resize-mem-array (min (* *mem-array-resize-factor*
                                                  len)
                                               *mem-size-in-bytes*)
                                          x86-32))
                       (t x86-32)))
         (x86-32 (!mem-array-next-addr (+ addr *pseudo-page-size-in-bytes*) x86-32))
         (x86-32 (!mem-tablei i addr x86-32)))
    (mv addr x86-32)))

; Start guard proof for !memi.

(defthm len-resize-list
  (equal (len (resize-list lst n default-value))
         (nfix n)))

(encapsulate
 ()
 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm logand-expected-mem-array-next-addr
   (equal (logand 16777215
                  (expected-mem-array-next-addr i j x86-32))
          0)
   :hints (("Goal" :in-theory (enable expected-mem-array-next-addr))))

 (defthm *-*mem-array-resize-factor*-preserves-0-mod-*pseudo-page-size-in-bytes*
   (implies (and (natp x)
                 (equal (logand 16777215 x) 0))
            (equal (logand 16777215 (* *mem-array-resize-factor* x)) 0)))
) ;; End of encapsulate


(encapsulate
 ()

(local
 (encapsulate
        ()

(local (include-book "arithmetic-5++"))

(defthm <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
  (implies (and (< next len)
                (integerp i)
                (<= 0 i)
                (< i *pseudo-page-size-in-bytes*)
                (force (natp next))
                (force (natp len))
                (force (equal (logand 16777215 next) 0))
                (equal (logand 16777215 len) 0))
           (< (+ next i)
              len)))
)) ;; End of local encapsulate

(defun !memi (i v x86-32)
  (declare (xargs :stobjs x86-32
                  :guard (and (integerp i)
                              (<= 0 i)
                              (< i *mem-size-in-bytes*)
                              (n08p v)
                              (x86-32p x86-32))
                  :guard-hints (("Goal" :in-theory (e/d (x86-32p)
                                                        (crock-001))
                                 :use ((:instance crock-001))))))
  (let* ((i-top (ash i (- *2^x-byte-pseudo-page*)))
         (addr (mem-tablei i-top x86-32)))
    (mv-let (addr x86-32)
            (cond ((eql addr 1) ; page is not present
                   (add-page-x86-32 i-top x86-32))
                  (t (mv addr x86-32)))
            (!mem-arrayi (logior addr (logand 16777215 i))
                         v
                         x86-32))))
) ;; End of encapsulate

(in-theory (disable memi !memi))

; Memory update lemmas

; Start proof of x86-32p-!memi

; Start proof of x86-32p-pre-!memi

; Start proof of x86-32p-!memi

; Start proof of x86-32p-!memi-not-new-page

; Start proof of x86-32p-!mem-arrayi

;; TO-DO@Shilpi: Enable (and disable functions like length in a consistent
;; manner)
(in-theory (enable length))

(defthm x86-32p-pre-update-nth-mem-arrayi
  (implies (forced-and (x86-32p-pre x86-32)
                       (n08p v)
                       (natp addr)
                       (< addr (len (nth *mem-arrayi* x86-32))))
           (x86-32p-pre (update-nth
                         *mem-arrayi*
                         (update-nth addr v (nth *mem-arrayi* x86-32))
                         x86-32)))
  :hints (("Goal" :in-theory (enable x86-32p-pre))))

(defthm good-mem-arrayp-1-logic-update-nth
  (implies (and (n08p v)
                (natp addr)
                (< addr mem-array-next-addr)
                (good-mem-arrayp-1-logic mem-array-next-addr
                                         (len mem-array)
                                         mem-array))
           (good-mem-arrayp-1-logic mem-array-next-addr
                                    (len mem-array)
                                    (update-nth addr v mem-array)))
  :hints (("Goal" :in-theory (enable x86-32p))
          ("[1]Goal" :in-theory (enable x86-32p))))

(defthm x86-32p-update-nth-mem-arrayi
  (implies (forced-and (x86-32p x86-32)
                       (n08p v)
                       (natp addr)
                       (< addr (nth *mem-array-next-addr* x86-32)))
           (x86-32p (update-nth
                     *mem-arrayi*
                     (update-nth addr v (nth *mem-arrayi* x86-32))
                     x86-32)))
  :hints (("Goal" :in-theory (enable x86-32p))
          ("[1]Goal" :in-theory (enable x86-32p))))



(defthm x86-32p-!memi-not-new-page
  (implies (and (x86-32p x86-32)
                (integerp i)
                (<= 0 i)
                (< i *mem-size-in-bytes*)
                (n08p v)
                (not (equal (mem-tablei (ash i (- *2^x-byte-pseudo-page*)) x86-32)
                            1)))
           (x86-32p (!mem-arrayi (logior (nth (ash i (- *2^x-byte-pseudo-page*))
                                              (nth *mem-tablei* x86-32))
                                         (logand 16777215 i))
                                 v
                                 x86-32)))
  :hints (("[1]Subgoal 1" :in-theory (disable crock-002)
           :use ((:instance crock-002))))
  :rule-classes nil)

; Start proof of x86-32p-!memi-new-page

; Start proof of x86-32p-!memi-new-page-no-resize

(defthm expected-mem-array-next-addr-update-nth-mem-tablei
  (implies (forced-and (equal (nth index (nth *mem-tablei* x86-32))
                              1)
                       (natp index)
                       (natp lower)
                       (natp upper)
                       (<= upper *mem-table-size*)
                       (not (equal any-value 1))
                       (equal mem-table (nth *mem-tablei* x86-32)))
           (equal (expected-mem-array-next-addr
                   lower upper
                   (update-nth *mem-tablei*
                               (update-nth index any-value mem-table)
                               x86-32))
                  (if (and (<= lower index)
                           (< index upper))
                      (+ *pseudo-page-size-in-bytes*
                         (expected-mem-array-next-addr
                          lower upper
                          x86-32))
                    (expected-mem-array-next-addr
                     lower upper
                     x86-32))))
  :hints (("Goal" :in-theory (enable expected-mem-array-next-addr))))

(defthm logand-mem-array-next-addr
  (implies (good-memp x86-32)
           (equal (logand 16777215
                          (nth *mem-array-next-addr* x86-32))
                  0)))

(defthm logand-ffffff-0-implies-not-1
  (implies (equal (logand 16777215 x) 0)
           (not (equal x 1))))

(defthm good-mem-table-entriesp-logic-update
  (implies
   (and (natp index)
        (good-mem-table-entriesp-logic lower upper array-next-addr mem-table)
        (natp val)
        (<= val array-next-addr)
        (equal (logand 16777215 val) 0))
   (good-mem-table-entriesp-logic
    lower upper
    (+ *pseudo-page-size-in-bytes* array-next-addr)
    (update-nth index val mem-table)))
  :hints (("Goal" :in-theory (enable nth good-mem-table-entriesp-logic))))

; Start proof of good-mem-table-no-dupsp-logic-update-nth
; (and good-mem-table-no-dupsp-logic-update-nth-lemma).

(defthm member-revappend-lemma
  (implies (member a y)
           (member a (revappend x y))))

(defthm member-revappend
  (iff (member a (revappend x y))
       (or (member a x)
           (member a y))))

(defthm member-merge-<-into->
  (iff (member a (merge-<-into-> x y z))
       (or (member a x)
           (member a y)
           (member a z))))

(defthm member-merge->-into-<
  (iff (member a (merge->-into-< x y z))
       (or (member a x)
           (member a y)
           (member a z))))

;; Jared added this after fixing up std/lists/sets stuff
(local (in-theory (e/d (revappend)
                       (revappend-removal))))

(defthm no-duplicatesp-sorted-revappend-2
  (implies (not (no-duplicatesp-sorted y))
           (not (no-duplicatesp-sorted (revappend x y)))))

(defthm no-duplicatesp-sorted-revappend-1
  (implies (not (no-duplicatesp-sorted x))
           (not (no-duplicatesp-sorted (revappend x y)))))

(defthm no-duplicatesp-sorted-merge-<-into->-3
  (implies (not (no-duplicatesp-sorted z))
           (not (no-duplicatesp-sorted (merge-<-into-> x y z)))))

(defthm no-duplicatesp-sorted-merge-<-into->-1
  (implies (not (no-duplicatesp-sorted x))
           (not (no-duplicatesp-sorted (merge-<-into-> x y z)))))

(defthm no-duplicatesp-sorted-merge-<-into->-2
  (implies (not (no-duplicatesp-sorted y))
           (not (no-duplicatesp-sorted (merge-<-into-> x y z)))))

(defthm no-duplicatesp-sorted-merge->-into-<-3
  (implies (not (no-duplicatesp-sorted z))
           (not (no-duplicatesp-sorted (merge->-into-< x y z)))))

(defthm no-duplicatesp-sorted-merge->-into-<-1
  (implies (not (no-duplicatesp-sorted x))
           (not (no-duplicatesp-sorted (merge->-into-< x y z)))))

(defthm no-duplicatesp-sorted-merge->-into-<-2
  (implies (not (no-duplicatesp-sorted y))
           (not (no-duplicatesp-sorted (merge->-into-< x y z)))))

(defun all-< (lst x)
  (cond ((endp lst) t)
        ((< (car lst) x)
         (all-< (cdr lst) x))
        (t nil)))

(defthm member-implies-not-all-<
  (implies (and (not (< b a))
                (member b y))
           (not (all-< y a))))

(defthm all-<-revappend
  (equal (all-< (revappend x y) a)
         (and (all-< x a)
              (all-< y a))))

(defthm all-<-merge-<-into->
  (equal (all-< (merge-<-into-> x y z) a)
         (and (all-< x a)
              (all-< y a)
              (all-< z a))))

(defthm all-<-merge->-into-<
  (equal (all-< (merge->-into-< x y z) a)
         (and (all-< x a)
              (all-< y a)
              (all-< z a))))

; Start proof of all-<-mem-table-entries-logic-next-addr

(encapsulate
 ()

 (local (in-theory (enable good-mem-table-entriesp-logic)))

 (local (defthm good-mem-table-entriesp-logic-preserved-lemma
          (implies (and (good-mem-table-entriesp-logic lower upper1 array-bound
                                                       x86-32)
                        (natp upper2)
                        (<= lower upper2)
                        (<= upper2 upper1))
                   (good-mem-table-entriesp-logic lower upper2 array-bound
                                                  x86-32))
          :hints (("Goal" :in-theory (disable (force))))))

 (defthm good-mem-table-entriesp-logic-preserved
   (implies (and (good-mem-table-entriesp-logic lower1 upper1 array-bound
                                                x86-32)
                 (natp lower2)
                 (natp upper2)
                 (<= lower1 lower2)
                 (<= lower2 upper2)
                 (<= upper2 upper1))
            (good-mem-table-entriesp-logic lower2 upper2 array-bound x86-32))
   :hints (("Goal" :in-theory (disable (force)))))
)

(defthm all-<-mem-table-entries-logic-next-addr
  (implies (good-mem-table-entriesp-logic lower upper next-addr mem-table)
           (all-< (mem-table-entries-logic lower upper mem-table parity)
                  next-addr))
  :hints (("Goal" :expand ((good-mem-table-entriesp-logic lower (+ 1 lower)
                                                          next-addr mem-table)
                           (good-mem-table-entriesp-logic (+ 1 lower)
                                                          (+ 1 lower)
                                                          next-addr
                                                          mem-table)
                           (good-mem-table-entriesp-logic lower lower next-addr
                                                          mem-table))
           :in-theory ; New axiom added after v6-5 breaks the proof:
           (disable fold-consts-in-+))))

(defthm merge-<-into->-append-1
  (implies (and (all-< x a)
                (all-< y a))
           (equal (merge-<-into-> (append x (list a)) y z)
                  (cons a (merge-<-into-> x y z)))))

(defthm merge-<-into->-append-2
  (implies (and (all-< x a)
                (all-< y a))
           (equal (merge-<-into-> x (append y (list a)) z)
                  (cons a (merge-<-into-> x y z)))))

(defthm merge->-into-<-append-last
  (equal (merge->-into-< x y (append z1 z2))
         (append (merge->-into-< x y z1)
                 z2))
  :rule-classes nil)

(defthm merge->-into-<-append-1
  (implies (and (all-< x a)
                (all-< y a))
           (equal (merge->-into-< (cons a x) y nil)
                  (append (merge->-into-< x y nil)
                          (list a))))
  :hints (("Goal" :use ((:instance merge->-into-<-append-last
                                   (x x)
                                   (y y)
                                   (z1 nil)
                                   (z2 (list a))))
           :expand ((merge->-into-< (cons a x) y nil)))))

(defthm merge->-into-<-append-2
  (implies (and (all-< x a)
                (all-< y a))
           (equal (merge->-into-< x (cons a y) nil)
                  (append (merge->-into-< x y nil)
                          (list a))))
  :hints (("Goal" :use ((:instance merge->-into-<-append-last
                                   (x x)
                                   (y y)
                                   (z1 nil)
                                   (z2 (list a))))
           :expand ((merge->-into-< x (cons a y) nil)))))

(defthm mem-table-entries-logic-update-nth
  (implies (and (natp next-addr)
                (not (equal next-addr 1))
                (natp lower)
                (natp upper)
                (natp index)
                (< index (len mem-table))
                (equal (nth index mem-table) 1)
                (booleanp parity)
                (all-< (mem-table-entries-logic lower upper mem-table parity)
                       next-addr))
           (equal (mem-table-entries-logic lower upper
                                           (update-nth index next-addr mem-table)
                                           parity)
                  (if (and (<= lower index)
                           (<= index upper))
                      (if parity
                          (append (mem-table-entries-logic lower upper mem-table
                                                           parity)
                                  (list next-addr))
                        (cons next-addr
                              (mem-table-entries-logic lower upper mem-table
                                                       parity)))
                    (mem-table-entries-logic lower upper mem-table parity)))))

(defthm not-all-<-car
  (equal (all-< x (car x))
         (not (consp x))))

(defthm no-duplicatesp-sorted-append
  (equal (no-duplicatesp-sorted (append x y))
         (and (no-duplicatesp-sorted x)
              (no-duplicatesp-sorted y)
              (or (atom x)
                  (atom y)
                  (not (equal (car (last x)) (car y)))))))

(defthm not-all-<-car-last
  (equal (all-< x (car (last x)))
         (not (consp x))))

(defthm good-mem-table-no-dupsp-logic-update-nth-lemma-0
  (implies (and (natp lower)
                (natp upper)
                (natp index)
                (< index (len mem-table))
                (natp next-addr)
                (not (equal next-addr 1))
                (booleanp parity)
                (equal (nth index mem-table) 1)
                (no-duplicatesp-sorted
                 (mem-table-entries-logic lower upper mem-table parity))
                (all-< (mem-table-entries-logic lower upper mem-table parity)
                       next-addr))
           (no-duplicatesp-sorted
            (mem-table-entries-logic lower upper
                                     (update-nth index next-addr mem-table)
                                     parity))))

(in-theory (disable mem-table-entries-logic-update-nth))

(defthm good-mem-table-no-dupsp-logic-update-nth-lemma
  (implies (and (natp lower)
                (natp upper)
                (natp index)
                (< index (len mem-table))
                (<= lower index)
                (<= index upper)
                (natp next-addr)
                (not (equal 1 next-addr))
                (booleanp parity)
                (equal (nth index mem-table) 1)
                (no-duplicatesp-sorted
                 (mem-table-entries-logic lower upper mem-table parity))
                (good-mem-table-entriesp-logic lower upper next-addr
                                               mem-table))
           (no-duplicatesp-sorted
            (mem-table-entries-logic lower upper
                                     (update-nth index next-addr mem-table)
                                     parity))))

(defthm good-mem-table-no-dupsp-logic-update-nth
  (implies (and (natp lower)
                (natp upper)
                (natp index)
                (< index (len mem-table))
                (<= lower index)
                (<= index upper)
                (natp next-addr)
                (not (equal 1 next-addr))
                (equal (nth index mem-table) 1)
                (good-mem-table-no-dupsp-logic lower upper mem-table)
                (good-mem-table-entriesp-logic lower upper next-addr
                                               mem-table))
           (good-mem-table-no-dupsp-logic lower upper
                                          (update-nth index next-addr
                                                      mem-table)))
  :hints (("Goal" :in-theory (enable good-mem-table-no-dupsp-logic
                                     good-mem-table-entriesp-logic))))

(defthm good-mem-arrayp-1-logic-preserved-upward
  (implies (and (good-mem-arrayp-1-logic index1 len mem-array)
                (natp index1)
                (natp index2)
                (<= index1 index2))
           (good-mem-arrayp-1-logic index2 len mem-array)))


;; (local (in-theory (disable nth-when-zp)))

(encapsulate
 ()

 (local
  (encapsulate
   ()

(local
 (include-book "arithmetic-5++"))

(defthm <=-preserved-by-adding-<=-*pseudo-page-size-in-bytes*
  (implies (and (< next len)
                (integerp i)
                (<= 0 i)
                (<= i *pseudo-page-size-in-bytes*)
                (force (natp next))
                (force (natp len))
                (force (equal (logand 16777215 next) 0))
                (equal (logand 16777215 len) 0))
           (<= (+ next i)
              len)))
)) ;; End of local encapsulate

(defthm x86-32p-!memi-new-page-no-resize-lemma-1
  (implies
   (and (x86-32p x86-32)
        (integerp index) ; (ash i (- *2^x-byte-pseudo-page*))
        (<= 0 index)
        (< index *mem-table-size*)
        (equal (mem-tablei index x86-32)
               1)
        (not (equal (nth *mem-array-next-addr* x86-32)
                    (len (nth *mem-arrayi* x86-32)))))
   (x86-32p
    (update-nth *mem-tablei*
                (update-nth index
                            (nth *mem-array-next-addr* x86-32)
                            (nth *mem-tablei* x86-32))
                (update-nth *mem-array-next-addr*
                            (+ *pseudo-page-size-in-bytes*
                               (nth *mem-array-next-addr* x86-32))
                            x86-32))))
  :hints (("Goal"
           :in-theory
           (e/d (mem-array-next-addr-is-expected-mem-array-next-addr
                   x86-32p
                   x86-32p-pre)
                (<=-preserved-by-adding-<=-*pseudo-page-size-in-bytes*))
           :use ((:instance <=-preserved-by-adding-<=-*pseudo-page-size-in-bytes*
                            (next (NTH *MEM-ARRAY-NEXT-ADDR* X86-32))
                            (i 16777216)
                            (len (LEN (NTH *MEM-ARRAYI* X86-32))))))))
) ;; End of encapsulate

(encapsulate
 ()

 (local
  (encapsulate
   ()

(local
 (include-book "arithmetic-5++"))

(defthm <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
  (implies (and (< next len)
                (integerp i)
                (<= 0 i)
                (< i *pseudo-page-size-in-bytes*)
                (force (natp next))
                (force (natp len))
                (force (equal (logand 16777215 next) 0))
                (equal (logand 16777215 len) 0))
           (< (+ next i)
              len)))
))

(defthm x86-32p-!memi-new-page-no-resize-lemma-2
  (implies (and (x86-32p x86-32)
                (n08p v)
                (natp addr)
                (equal (logand 16777215 addr) 0)
                (< addr (nth *mem-array-next-addr* x86-32))
                ;(< addr (len mem-array))
                (equal mem-array (nth *mem-arrayi* x86-32)))
           (x86-32p
            (update-nth
             *mem-arrayi*
             (update-nth (+ addr (logand 16777215 i))
                         v
                         mem-array)
             x86-32))))
) ;; End of encapsulate


(defthm x86-32p-!memi-new-page-no-resize
  (implies
   (and (x86-32p x86-32)
        (integerp i)
        (<= 0 i)
        (< i *mem-size-in-bytes*)
        (n08p v)
        (equal (mem-tablei (ash i (- *2^x-byte-pseudo-page*)) x86-32)
               1)
        (not (equal (nth *mem-array-next-addr* x86-32)
                    (len (nth *mem-arrayi* x86-32)))))
   (x86-32p
    (update-nth
     *mem-arrayi*
     (update-nth (logior (nth *mem-array-next-addr* x86-32)
                         (logand 16777215 i))
                 v (nth *mem-arrayi* x86-32))
     (update-nth *mem-tablei*
                 (update-nth (ash i (- *2^x-byte-pseudo-page*))
                             (nth *mem-array-next-addr* x86-32)
                             (nth *mem-tablei* x86-32))
                 (update-nth *mem-array-next-addr*
                             (+ *pseudo-page-size-in-bytes*
                                (nth *mem-array-next-addr* x86-32))
                             x86-32)))))
  :otf-flg t
  :rule-classes nil)

; Start proof of x86-32p-!memi-new-page-resize

(defthm mem-arrayp-repeat
  (implies (unsigned-byte-p 8 x)
           (mem-arrayp (replicate n x)))
  :hints(("Goal" :in-theory (enable replicate))))

(defthm mem-arrayp-resize-list
  (implies (and (mem-arrayp lst)
                (unsigned-byte-p 8 default-value))
           (mem-arrayp (resize-list lst new-len default-value)))
  :hints(("Goal" :in-theory (enable resize-list))))


(local
 (progn
   (defun nth-resize-list-induction (i lst n default-value)
     (declare (ignorable i lst n default-value))
     (if (posp n)
         (nth-resize-list-induction (1- i)
                                    (if (atom lst) lst (cdr lst))
                                    (1- n)
                                    default-value)
       nil))

   (defthm nth-resize-list
     (implies (and (natp i)
                   (natp n)
                   (<= (len lst) n)
                   (< i n))
              (equal (nth i (resize-list lst n default))
                     (if (< i (len lst))
                         (nth i lst)
                       default)))
     :hints (("Goal" :in-theory (enable resize-list nth)
              :induct (nth-resize-list-induction i lst n default-value))))))

(defthm good-mem-arrayp-1-logic-resize-list
  (implies (and (natp next-addr)
                (natp new-len)
                (<= (len mem-array) new-len)
                (good-mem-arrayp-1-logic next-addr
                                         (len mem-array)
                                         mem-array))
           (good-mem-arrayp-1-logic next-addr
                                    new-len
                                    (resize-list mem-array new-len 0)))
; It's very unusual that the following works but :hints (("Goal" :induct t))
; does not!
  :instructions ((then induct prove)))

(defthm x86-32p-resize-mem-array
   (implies
    (and (x86-32p x86-32)
         (natp new-len)
         (equal (logand 16777215 new-len) 0)
         (< (len (nth *mem-arrayi* x86-32)) new-len)
         (<= new-len *mem-size-in-bytes*))
    (x86-32p (update-nth *mem-arrayi*
                         (resize-list (nth *mem-arrayi* x86-32)
                                      new-len 0)
                         x86-32)))
   :hints (("Goal" :in-theory (enable x86-32p x86-32p-pre))))



(defthm x86-32p-!memi-new-page-resize
  (implies
   (and (x86-32p x86-32)
        (integerp i)
        (<= 0 i)
        (< i *mem-size-in-bytes*)
        (n08p v)
        (equal (mem-tablei (ash i (- *2^x-byte-pseudo-page*)) x86-32)
               1)
        (equal (nth *mem-array-next-addr* x86-32)
               (len (nth *mem-arrayi* x86-32)))
        (natp new-len)
        (equal (logand 16777215 new-len) 0)
        (< (len (nth *mem-arrayi* x86-32)) new-len)
        (<= new-len *mem-size-in-bytes*))
   (x86-32p
    (update-nth
     *mem-arrayi*
     (update-nth (+ (nth *mem-array-next-addr* x86-32)
                    (logand 16777215 i))
                 v
                 (resize-list (nth *mem-arrayi* x86-32)
                              new-len
                              0))
     (update-nth
      *mem-tablei*
      (update-nth (ash i (- *2^x-byte-pseudo-page*))
                  (nth *mem-array-next-addr* x86-32)
                  (nth *mem-tablei* x86-32))
      (update-nth
       *mem-array-next-addr*
       (+ *pseudo-page-size-in-bytes*
          (nth *mem-array-next-addr* x86-32))
       (update-nth
        *mem-arrayi*
        (resize-list (nth *mem-arrayi* x86-32)
                     new-len
                     0)
        x86-32))))))
  :hints (("Goal" :use
           ((:instance
             x86-32p-!memi-new-page-no-resize
             (x86-32 (update-nth *mem-arrayi*
                                 (resize-list (nth *mem-arrayi* x86-32)
                                              new-len 0)
                                 x86-32)))))))


(defthm len-mem-array-positive
  (implies (x86-32p x86-32)
           (posp (len (nth *mem-arrayi* x86-32))))
  :hints (("Goal" :in-theory (enable x86-32p)))
  :rule-classes :type-prescription)

(defthm dumb-crock-0
  (implies (x86-32p x86-32)
           (not (equal (LEN (NTH *MEM-ARRAYI* X86-32))
                       0)))
  :hints (("Goal" :in-theory (enable x86-32p
                                        x86-32p-pre))))

(defthm x86-32p-!memi-new-page
  (implies (and (x86-32p x86-32)
                (integerp i)
                (<= 0 i)
                (< i *mem-size-in-bytes*)
                (n08p v)
                (equal (mem-tablei (ash i (- *2^x-byte-pseudo-page*)) x86-32)
                       1))
           (mv-let (addr x86-32)
                   (add-page-x86-32 (ash i (- *2^x-byte-pseudo-page*)) x86-32)
                   (x86-32p (!mem-arrayi (logior addr
                                                 (logand 16777215 i))
                                         v
                                         x86-32))))
  :hints (("Goal" :use ((:instance x86-32p-!memi-new-page-no-resize)
                        (:instance x86-32p-!memi-new-page-resize
                                   (new-len (if (< (* 2 (NTH *MEM-ARRAY-NEXT-ADDR* X86-32))
                                                   281474976710656)
                                                (* 2 (NTH *MEM-ARRAY-NEXT-ADDR* X86-32))
                                              281474976710656)
                                   )))))
  :otf-flg t
  :rule-classes nil)




(defthm x86-32p-!memi
  (implies (forced-and (x86-32p x86-32)
                       (integerp i)
                       (<= 0 i)
                       (< i *mem-size-in-bytes*)
                       (n08p v))
           (x86-32p (!memi i v x86-32)))
  :hints (("Goal"
           :use (x86-32p-!memi-new-page x86-32p-!memi-not-new-page)
           :in-theory (enable !memi))))

; Shilpi: Excluded for now
; Relics of 32-bit model -- might need to be restored suitably.

;; (defthm x86-32p-properties
;;   (implies (x86-32p-pre x86-32)
;;            (and (true-listp x86-32)
;;                 (equal (len x86-32) 13)

;;                 (rgfp (nth *rgfi* x86-32))
;;                 (equal (len (nth 0 x86-32))
;;                        *64-bit-general-purpose-registers-len*)

;;                 (ripp (nth *rip* x86-32))
;;                 (flgp (nth *flg* x86-32))

;;                 (segp (nth *segi* x86-32))
;;                 (equal (len (nth *segi* x86-32))
;;                        *segment-register-names-len*)

;;                 (strp (nth *stri* x86-32))
;;                 (equal (len (nth *stri* x86-32))
;;                        *gdtr-idtr-names-len*)

;;                 (ssrp (nth *ssri* x86-32))
;;                 (equal (len (nth *ssri* x86-32))
;;                        *ldtr-tr-names-len*)

;;                 (ctrp (nth *ctri* x86-32))
;;                 (equal (len (nth *ctri* x86-32))
;;                        *control-register-names-len*)

;;                 (dbgp (nth *dbgi* x86-32))
;;                 (equal (len (nth *dbgi* x86-32))
;;                        *debug-register-names-len*)

;;                 (mem-tablep (nth *mem-tablei* x86-32))
;;                 (equal (len (nth *mem-tablei* x86-32))
;;                        *mem-table-size*)

;;                 (mem-arrayp (nth *mem-arrayi* x86-32))
;; ; Consider a conjunct equating (len (nth *mem-arrayi* x86-32)) with something,
;; ; but be careful about looping if we use (mem-array-length x86-32)).

;; #|| Relics of 32-bit model -- might need to be restored suitably.

;;                 (seg-basep (nth *seg-basei* x86-32))
;;                 (equal (len (nth *seg-basei* x86-32))
;;                        *m86-64-segment-reg-names-len*)

;;                 (seg-limitp (nth *seg-limiti* x86-32))
;;                 (equal (len (nth *seg-limiti* x86-32))
;;                        *m86-64-segment-reg-names-len*)

;;                 (seg-accessp (nth *seg-accessi* x86-32))
;;                 (equal (len (nth *seg-accessi* x86-32))
;;                        *m86-64-segment-reg-names-len*)
;; ||#
;;                 ))
;;   :hints (("Goal" :in-theory (enable x86-32p-pre
;;                                      rgfp ripp flgp ;segp strp ssrp ctrp dbgp
;;                                      mem-tablep mem-arrayp
;; #|| Relics of 32-bit model -- might need to be restored suitably.
;;                                      seg-basep seg-limitp seg-accessp
;; ||#
;;                                      )))
;;   :rule-classes :forward-chaining)
;;                    ))


; Read memory byte and memory double-word functions

; Start proof of memi-is-unsigned-byte-8

(encapsulate
 ()

(local
 (defthm memi-is-unsigned-byte-8-lemma
   (implies (and (x86-32p x86-32)
                 (integerp addr)
                 (<= 0 addr)
                 (< addr *mem-size-in-bytes*)
                 (not (equal (mem-tablei
                              (ash addr (- *2^x-byte-pseudo-page*)) x86-32)
                             1)))
            (< (logior (logand 16777215 addr)
                       (mem-tablei
                        (ash addr (- *2^x-byte-pseudo-page*)) x86-32))
               (len (nth *mem-arrayi* x86-32))))
   :hints (("Goal" :in-theory (e/d (x86-32p
                                    mem-tablei)
                                   (crock-001))
            :use ((:instance crock-001
                             (i addr)))))))

 (defthm memi-is-unsigned-byte-8
   (implies (and (x86-32p x86-32)
                 (integerp addr)
                 (<= 0 addr)
                 (< addr *mem-size-in-bytes*))
            (n08p (memi addr x86-32)))
   :hints (("Goal" :in-theory (e/d (memi
                                    mem-tablei)
                                   (NATP-MEM-ARRAYI
                                    MEM-ARRAYI-LESS-THAN-EXPT-2-8
                                    memi-is-unsigned-byte-8-lemma))
            :use ((:instance NATP-MEM-ARRAYI
                             (i (LOGIOR (LOGAND 16777215 ADDR)
                                        (NTH (ASH ADDR -24)
                                             (NTH *MEM-TABLEI* X86-32)))))
                  (:instance MEM-ARRAYI-LESS-THAN-EXPT-2-8
                             (i (LOGIOR (LOGAND 16777215 ADDR)
                                        (NTH (ASH ADDR -24)
                                             (NTH *MEM-TABLEI* X86-32)))))
                  (:instance memi-is-unsigned-byte-8-lemma
                             ))))
   :otf-flg t
   :rule-classes
   ((:type-prescription
     :corollary
     (implies (forced-and (x86-32p x86-32)
                          (integerp addr)
                          (<= 0 addr)
                          (< addr *mem-size-in-bytes*))
              (natp (memi addr x86-32))))
    (:linear
     :corollary
     (implies (forced-and (x86-32p x86-32)
                          (integerp addr)
                          (<= 0 addr)
                          (< addr *mem-size-in-bytes*))
              (< (memi addr x86-32)
                 *2^8*)))))
) ;; End of encapsulate

(encapsulate
 ()

 (local
  (include-book "arithmetic/top" :dir :system))

 (defthm member-mem-table-entries-logic
   (implies (and (natp i)
                 (natp lower)
                 (natp upper)
                 (<= lower i)
                 (<= i upper)
                 (not (equal (nth i mem-table) 1)))
            (member (nth i mem-table)
                    (mem-table-entries-logic lower upper mem-table parity)))
   :hints (("Goal" :in-theory (enable mem-table-entries-logic)
            :induct (mem-table-entries-logic lower upper mem-table parity))
           ("Subgoal *1/7" :cases ((equal lower i)))
           ("Subgoal *1/6" :cases ((equal lower i)))
           ("Subgoal *1/5" :cases ((equal lower i)))
           ("Subgoal *1/4" :cases ((equal lower i)))
           ("Subgoal *1/3" :cases ((equal lower i)))))
) ;; End of encapsulate

(local
 (defun sortedp (x parity)

; A parity of true means that x should be increasing.

   (cond ((or (endp x) (endp (cdr x)))
          t)
         ((if parity
              (<= (car x) (cadr x))
            (>= (car x) (cadr x)))
          (sortedp (cdr x) parity))
         (t nil))))

(local
 (defthm sortedp-revappend
   (iff (and (sortedp x (not parity))
             (sortedp y parity)
             (or (atom x)
                 (atom y)
                 (if parity
                     (<= (car x) (car y))
                   (>= (car x) (car y)))))
        (sortedp (revappend x y) parity))
   :rule-classes ((:rewrite
                   :corollary
                   (equal (sortedp (revappend x y) parity)
                          (and (sortedp x (not parity))
                               (sortedp y parity)
                               (or (atom x)
                                   (atom y)
                                   (if parity
                                       (<= (car x) (car y))
                                     (>= (car x) (car y))))))))))

(local
 (defthm sortedp-merge-<-into->
   (implies (and (sortedp x t)
                 (sortedp y t)
                 (sortedp z nil)
                 (or (atom z) (atom x) (>= (car x) (car z)))
                 (or (atom z) (atom y) (>= (car y) (car z))))
            (sortedp (merge-<-into-> x y z) nil))
   :hints (("Goal" :in-theory (enable merge-<-into->)))))

(local
 (defthm sortedp-merge->-into-<
   (implies (and (sortedp x nil)
                 (sortedp y nil)
                 (sortedp z t)
                 (or (atom z) (atom x) (<= (car x) (car z)))
                 (or (atom z) (atom y) (<= (car y) (car z))))
            (sortedp (merge->-into-< x y z) t))
   :hints (("Goal" :in-theory (enable merge->-into-<)))))

(local
 (defthm no-duplicatesp-sorted-revappend
   (equal (no-duplicatesp-sorted (revappend x y))
          (and (no-duplicatesp-sorted x)
               (no-duplicatesp-sorted y)
               (or (atom x)
                   (atom y)
                   (not (equal (car x) (car y))))))
   :hints (("Goal" :in-theory (enable no-duplicatesp-sorted)))))

(local
 (defthm not-member-sortedp-t
   (implies (and (sortedp x t)
                 (< a (car x)))
            (not (member a x)))))

(local
 (defthm member-sortedp-t
   (implies (and (sortedp x t)
                 (consp x)
                 (<= a (car x))
                 (rational-listp x))
            (iff (member a x)
                 (equal a (car x))))
   :hints (("Goal" :induct t))))

(local
 (defthm member-of-both-implies-not-no-duplicatesp-sorted-merge-<-into->
   (implies (and (rational-listp x)
                 (rational-listp y)
                 (member a x)
                 (member b y)
                 (equal a b)
                 (sortedp x t)
                 (sortedp y t))
            (not (no-duplicatesp-sorted (merge-<-into-> x y z))))
   :hints (("Goal"
            :in-theory (enable no-duplicatesp-sorted
                               merge-<-into->)
            :induct (merge-<-into-> x y z)
            :expand ((merge-<-into-> x y z)
                     (sortedp x t)
                     (merge-<-into-> x
                                     (cdr y)
                                     (cons (car x) z)))))))

(local
 (defthm not-member-sortedp-nil
   (implies (and (sortedp x nil)
                 (> a (car x)))
            (not (member a x)))))

(local
 (defthm member-sortedp-nil
   (implies (and (sortedp x nil)
                 (consp x)
                 (>= a (car x))
                 (rational-listp x))
            (iff (member a x)
                 (equal a (car x))))
   :hints (("Goal" :induct t))))

(local
 (defthm member-of-both-implies-not-no-duplicatesp-sorted-merge->-into-<
   (implies (and (rational-listp x)
                 (rational-listp y)
                 (member a x)
                 (member b y)
                 (equal a b)
                 (sortedp x nil)
                 (sortedp y nil))
            (not (no-duplicatesp-sorted (merge->-into-< x y z))))
   :hints (("Goal"
            :in-theory (enable no-duplicatesp-sorted
                               merge->-into-<)
            :induct (merge->-into-< x y z)
            :expand ((merge->-into-< x y z)
                     (sortedp x nil)
                     (merge->-into-< x
                                     (cdr y)
                                     (cons (car x) z)))))))

(local
 (defthm rationalp-nth
   (implies (and (rational-listp x)
                 (natp n)
                 (< n (len x)))
            (rationalp (nth n x)))
   :hints (("Goal" :in-theory (enable nth)))))

(local
 (defthm rational-listp-merge->-into-<
   (implies (and (rational-listp x)
                 (rational-listp y)
                 (rational-listp z))
            (rational-listp (merge->-into-< x y z)))
   :hints (("Goal" :in-theory (enable merge->-into-<)))))

(local
 (defthm rational-listp-merge-<-into->
   (implies (and (rational-listp x)
                 (rational-listp y)
                 (rational-listp z))
            (rational-listp (merge-<-into-> x y z)))
   :hints (("Goal" :in-theory (enable merge-<-into->)))))

(local
 (defthm rational-listp-mem-table-entries-logic
   (implies (and (rational-listp mem-table)
                 (natp lower)
                 (<= lower upper)
                 (natp upper)
                 (< upper (len mem-table)))
            (rational-listp (mem-table-entries-logic lower upper mem-table
                                                     parity)))))

(local
 (defthm sortedp-mem-table-entries-logic
   (implies (and (rational-listp mem-table)
                 (natp lower)
                 (natp upper)
                 (< upper (len mem-table))
                 (booleanp parity))
            (sortedp (mem-table-entries-logic lower upper mem-table parity)
                     parity))))

(local
 (defthm member-mem-table-entries-logic-alt
   (implies (and (equal (nth i mem-table) (nth j mem-table))
                 (natp i)
                 (natp lower)
                 (natp upper)
                 (<= lower i)
                 (<= i upper)
                 (not (equal (nth i mem-table) 1)))
            (member (nth j mem-table)
                    (mem-table-entries-logic lower upper mem-table parity)))))

(local
 (defthm crock-340
   (NOT (NO-DUPLICATESP-SORTED (LIST x x)))
   :hints (("Goal" :in-theory (enable no-duplicatesp-sorted)))))

(local
 (defthm mem-table-is-one-to-one-lemma
   (implies (and (rational-listp mem-table)
                 (natp lower)
                 (natp upper)
                 (natp i)
                 (natp j)
                 (<= lower i)
                 (< i j)
                 (<= j upper)
                 (< upper (len mem-table))
                 (booleanp parity)
                 (not (equal (nth i mem-table) 1))
                 (equal (nth i mem-table)
                        (nth j mem-table)))
            (not (no-duplicatesp-sorted
                  (mem-table-entries-logic lower upper mem-table parity))))
   :hints
   (("Goal"
     :restrict
     ((member-of-both-implies-not-no-duplicatesp-sorted-merge->-into-<
       ((a (nth i mem-table))
        (b (nth j mem-table))))
      (member-of-both-implies-not-no-duplicatesp-sorted-merge-<-into->
       ((a (nth i mem-table))
        (b (nth j mem-table)))))))
   :rule-classes nil))

(local
 (defthm crock-341
   (implies (mem-tablep mem-table)
            (rational-listp mem-table))))

(local
 (defthm mem-table-is-one-to-one-helper
   (implies (and (x86-32p x86-32)
                 (integerp i)
                 (<= 0 i)
                 (<= i 255) ;; Size of mem-table
                 (integerp j)
                 (<= 0 j)
                 (<= j 255) ;; Size of mem-table
                 (<= i j)
                 (not (equal (mem-tablei i x86-32)
                             1)))
            (equal (equal (mem-tablei i x86-32)
                          (mem-tablei j x86-32))
                   (equal i j)))
   :hints (("Goal"
            :in-theory (enable x86-32p
                               x86-32p-pre
                               good-memp
                               good-mem-table-no-dupsp-logic
                               mem-tablei
                               mem-table-length)
            :use ((:instance mem-table-is-one-to-one-lemma
                             (lower 0)
                             (upper 255) ;; Size of mem-table
                             (mem-table (nth *mem-tablei* x86-32))
                             (parity t)))))
   :rule-classes nil))

(local
 (defthm mem-table-is-one-to-one
   (implies (and (x86-32p x86-32)
                 (integerp i)
                 (<= 0 i)
                 (<= i 255) ;; Size of mem-table
                 (integerp j)
                 (<= 0 j)
                 (<= j 255) ;; Size of mem-table
                 (not (equal (mem-tablei i x86-32)
                             1)))
            (equal (equal (mem-tablei i x86-32)
                          (mem-tablei j x86-32))
                   (equal i j)))
   :hints (("Goal" :use ((:instance mem-table-is-one-to-one-helper
                                    (i i)
                                    (j j))
                         (:instance mem-table-is-one-to-one-helper
                                    (i j)
                                    (j i)))))))

(encapsulate
 ()

(local
 (include-book "arithmetic-5++"))

(defthm logior-1
  (implies (and (integerp x1)
                (<= 0 x1)
                (integerp y1)
                (<= 0 y1)
                (equal (logand 16777215 x1)
                       x1)
                (equal (logand 16777215 y1)
                       0)
                (integerp x2)
                (<= 0 x2)
                (integerp y2)
                (<= 0 y2)
                (equal (logand 16777215 x2)
                       x2)
                (equal (logand 16777215 y2)
                       0))
           (equal (equal (logior x1 y1)
                         (logior x2 y2))
                  (and (equal x1 x2)
                       (equal y1 y2))))
  :hints (("Subgoal 1.1.1.1" :cases ((< k j)
                                     (< j k))))
  :otf-flg t)

(defthm logior-2
  (implies (and (integerp x1)
                (<= 0 x1)
                (integerp y1)
                (<= 0 y1)
                (equal (logand 16777215 x1)
                       x1)
                (equal (logand 16777215 y1)
                       0)
                (integerp x2)
                (<= 0 x2)
                (integerp y2)
                (<= 0 y2)
                (equal (logand 16777215 x2)
                       x2)
                (equal (logand 16777215 y2)
                       0))
           (equal (equal (logior y1 x1)
                         (logior x2 y2))
                  (and (equal x1 x2)
                       (equal y1 y2))))
  :hints (("Goal" :in-theory (disable LOGAND-CONSTANT-MASK))))

(defthm logior-3
  (implies (and (integerp x1)
                (<= 0 x1)
                (integerp y1)
                (<= 0 y1)
                (equal (logand 16777215 x1)
                       x1)
                (equal (logand 16777215 y1)
                       0)
                (integerp x2)
                (<= 0 x2)
                (integerp y2)
                (<= 0 y2)
                (equal (logand 16777215 x2)
                       x2)
                (equal (logand 16777215 y2)
                       0))
           (equal (equal (logior x1 y1)
                         (logior y2 x2))
                  (and (equal x1 x2)
                       (equal y1 y2))))
  :hints (("Goal" :in-theory (disable LOGAND-CONSTANT-MASK))))

(defthm logior-4
  (implies (and (integerp x1)
                (<= 0 x1)
                (integerp y1)
                (<= 0 y1)
                (equal (logand 16777215 x1)
                       x1)
                (equal (logand 16777215 y1)
                       0)
                (integerp x2)
                (<= 0 x2)
                (integerp y2)
                (<= 0 y2)
                (equal (logand 16777215 x2)
                       x2)
                (equal (logand 16777215 y2)
                       0))
           (equal (equal (logior y1 x1)
                         (logior y2 x2))
                  (and (equal x1 x2)
                       (equal y1 y2))))
  :hints (("Goal" :in-theory (disable LOGAND-CONSTANT-MASK))))

(defthm logand-thm-1
  (equal (logand 16777215 (LOGAND 16777215 I1))
         (LOGAND 16777215 I1)))

(defthm logior-thm-1
  (implies (and (integerp x)
                (<= 0 x)
                (integerp y)
                (<= 0 y))
           (<= x
               (logior x y)))
  :rule-classes :linear)

(defthm logand-ash-thm-1
  (implies (and (INTEGERP I1)
                (<= 0 I1)
                (< I1 281474976710656)
                (INTEGERP I2)
                (<= 0 I2)
                (< I2 281474976710656)
                (EQUAL (LOGAND 16777215 I2)
                       (LOGAND 16777215 I1))
                (EQUAL (ASH I2 -24) (ASH I1 -24)))
           (equal (EQUAL I1 I2)
                  t))
  :hints (("Goal" :in-theory (enable ash-to-floor))))
 ) ;; End of encapsulate

(defthm crock-876
  (implies (AND (X86-32P X86-32)
                (< I 4294967296)
                (<= 0 I)
                (INTEGERP I))
           (not (equal (NTH (ASH I -24)
                            (NTH *MEM-TABLEI* X86-32))
                       (NTH *MEM-ARRAY-NEXT-ADDR* X86-32))))
  :hints (("Goal" :use ((:instance crock-002)))))


(defthm crock-thm-958-helper-helper
  (implies (and (good-mem-table-entriesp-logic low
                                               high
                                               (nth
                                                *mem-array-next-addr* x86-32)
                                               mem-table)
                (integerp x)
                (<= low x)
                (<= x high)
                (not (equal (nth x
                                 mem-table)
                            1)))
           (equal (logand 16777215 (nth x
                                        mem-table))
                  0))
  :hints (("goal" :in-theory (enable good-mem-table-entriesp-logic))))

(defthm crock-thm-958-helper
  (implies (and (x86-32p x86-32)
                (integerp x)
                (<= 0 x)
                (< x 256) ;; size of mem-table, i.e. 256 pages in all
                (not (equal (NTH x
                                 (NTH *MEM-TABLEI* X86-32))
                            1)))
           (equal (logand 16777215 (NTH x
                                        (NTH *MEM-TABLEI* X86-32)))
                  0))
  :hints (("Goal" :in-theory (enable x86-32p
                                     good-memp))))

(defthm crock-thm-958
  (implies (and (x86-32p x86-32)
                (integerp i)
                (<= 0 i)
                (< i *mem-size-in-bytes*)
                (not (equal (NTH (ASH I -24)
                                 (NTH *MEM-TABLEI* X86-32))
                            1)))
           (equal (logand 16777215 (NTH (ASH I -24)
                                        (NTH *MEM-TABLEI* X86-32)))
                  0)))

;; (defthm nth-resize-list++
;;   (implies (and (natp i)
;;                 (natp n)
;;                 (<= (len lst) n))
;;            (equal (nth i (resize-list lst n default))
;;                   (cond ((< i (len lst))
;;                          (nth i lst))
;;                         ((< i n)
;;                          default)
;;                         (t
;;                          nil))))
;;   :hints (("Goal" :in-theory (enable resize-list nth)
;;            :induct (nth-resize-list-induction i lst n default-value))))

; At least some of the following enables and disables are required on 7/28/2013
; for read-write, perhaps due to a change in or under centaur/books/gl/gl.lisp
; -- actually the culprit is at least in part probably the additions of some
; rules to centaur/misc/arith-equivs.lisp.
;; (local (in-theory (e/d (nfix natp)
;;                        (natp-when-gte-0
;;                         natp-when-integerp
;;                         nfix-when-natp
;;                         nfix-when-not-natp
;;                         nth-when-too-large))))

(encapsulate
 ()

(local
 (encapsulate
   ()

   (local
    (include-book "arithmetic-5++"))


(defthm <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
  (implies (and (< next len)
                (integerp i)
                (<= 0 i)
                (< i *pseudo-page-size-in-bytes*)
                (force (natp next))
                (force (natp len))
                (force (equal (logand 16777215 next) 0))
                (equal (logand 16777215 len) 0))
           (< (+ next i)
              len)))

(defthm good-mem-arrayp-thm-1-helper
  (implies (and (good-mem-arrayp-1-logic start len mem-array)
                (integerp start)
                (<= 0 start)
                (integerp len)
                (<= 0 len)
                (<= start len)
                (integerp addr)
                (<= 0 addr)
                (<= start addr)
                (< addr len)
                )
           (equal (nth addr mem-array)
                  0)))

(defthm good-mem-arrayp-thm-1
  (implies (and (x86-32p x86-32)
                (integerp addr)
                (<= 0 addr)
                (<= (MEM-ARRAY-NEXT-ADDR X86-32) addr)
                (< addr (MEM-ARRAY-LENGTH X86-32)))
           (equal (nth addr (NTH *MEM-ARRAYI* X86-32))
                  0))
  :hints (("Goal" :in-theory (enable x86-32p
                                     good-memp
                                     good-mem-arrayp))))
)) ;; End of local encapsulate

(defthm dumb-crock-32
  (implies (x86-32p x86-32)
           (<= (NTH *MEM-ARRAY-NEXT-ADDR* X86-32)
               (LEN (NTH *MEM-ARRAYI* X86-32))))
  :hints (("Goal" :in-theory (enable x86-32p
                                     good-memp)))
  :rule-classes :linear)

(defthm dumb-crock-33
  (implies (x86-32p x86-32)
           (EQUAL (LOGAND 16777215 (LEN (NTH *MEM-ARRAYI* X86-32)))
                  0))
  :hints (("Goal" :in-theory (enable x86-32p
                                     good-memp))))

(defthmd logior-with-multiple-of-2^24-commuted-hack
  (implies (and (integerp x)
                (<= 0 x)
                (equal (logand 16777215 x) 0)
                (n24p y))
           (equal (+ y x)
                  (logior x y))))

(defthm read-write
  (implies (forced-and (x86-32p x86-32)
                       (integerp i1)
                       (<= 0 i1)
                       (< i1 *mem-size-in-bytes*)
                       (integerp i2)
                       (<= 0 i2)
                       (< i2 *mem-size-in-bytes*)
                       (n08p v))
           (equal (memi i2 (!memi i1 v x86-32))
                  (if (equal i1 i2)
                      v
                    (memi i2 x86-32))))
  :hints (("Goal" :in-theory (e/d (memi
                                   !memi)
                                  (good-mem-arrayp-thm-1
                                   good-mem-arrayp-thm-1-helper)))
          ("Subgoal 10.8"
           :in-theory (e/d
                       (logior-with-multiple-of-2^24-commuted-hack)
                       (mem-table-is-one-to-one
                        logior-with-multiple-of-2^24-commuted
                        logior-with-multiple-of-2^24))
           :use ((:instance mem-table-is-one-to-one
                            (i (ASH I1 -24))
                            (j (ASH I2 -24)))))
          ("Subgoal 8.4.1" :in-theory
           (disable good-mem-arrayp-thm-1
                    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*)
           :use ((:instance good-mem-arrayp-thm-1
                            (addr (+ (NTH *MEM-ARRAY-NEXT-ADDR* X86-32)
                                     (LOGAND 16777215 I2))))
                 (:instance <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
                            (next (NTH *MEM-ARRAY-NEXT-ADDR* X86-32))
                            (i (LOGAND 16777215 I2))
                            (len (LEN (NTH *MEM-ARRAYI* X86-32)))))))
  :otf-flg t)


) ;; End of encapsulate

;; ======================================================================

;; Memory read and write functions --- rm* and wm*:

(defun rm08 (addr x86-32)
   (declare (xargs :stobjs x86-32
                   :guard (and (integerp addr)
                               (<= 0 addr)
                               (< addr *mem-size-in-bytes*)
                               (x86-32p x86-32))))
   (memi addr x86-32))

(defthm natp-rm08
  (implies (and (force (x86-32p x86-32))
                (force (n32p addr)))
           (and (integerp (rm08 addr x86-32))
                (<= 0 (rm08 addr x86-32))))
  :rule-classes :type-prescription)

(defthm rm08-less-than-expt-2-32
  (implies (and (x86-32p x86-32)
                (n32p addr))
           (< (rm08 addr x86-32) 256))
  :rule-classes :linear)

(in-theory (disable rm08))

(defun rm16 (addr x86-32)
;; Note that the "memory wrap" is done is byte1 to be consistent with the
;; original Y86 model.
   (declare (xargs :stobjs x86-32
                   :guard (and (n32p addr)
                               (x86-32p x86-32))))
   (let* ((byte0 (memi addr x86-32))
          (byte1 (memi (n32+ addr 1) x86-32))
          (word  (logior (ash byte1 8)
                         byte0)))
     word))

(defthm integerp-rm16
  (implies (and (force (x86-32p x86-32))
                (force (n32p addr)))
           (and (integerp (rm16 addr x86-32))
                (<= 0 (rm16 addr x86-32))))
  :rule-classes :type-prescription)

(local
  (def-gl-thm rm16-less-than-expt-2-16-helper
    :hyp (and (n08p byte0)
              (n08p byte1))
    :concl (< (logior (ash byte1 8)
                      byte0)
              65536)
    :g-bindings
    `((byte0 (:g-number ,(gl-int 0 1 9)))
      (byte1 (:g-number ,(gl-int 9 1 9))))))

(defthm rm16-less-than-expt-2-16
  (implies (and (x86-32p x86-32)
                (n32p addr))
           (< (rm16 addr x86-32) 65536))
  :rule-classes :linear)

(in-theory (disable rm16))

(defun rm32 (addr x86-32)
   (declare (xargs :stobjs x86-32
                   :guard (and (n32p addr)
                               (x86-32p x86-32))))
   (let* ((byte0 (memi      addr x86-32))
          (byte1 (memi (n32+ 1 addr) x86-32))
          (word0 (logior (ash byte1 8)
                         byte0))

          (byte2 (memi (n32+ 2 addr) x86-32))
          (byte3 (memi (n32+ 3 addr) x86-32))
          (word1 (logior (ash byte3 8)
                         byte2))

          (dword (logior (ash word1 16)
                         word0)))
     dword))

(defthm integerp-rm32
  (implies (and (force (x86-32p x86-32))
                (force (n32p addr)))
           (and (integerp (rm32 addr x86-32))
                (<= 0 (rm32 addr x86-32))))
  :rule-classes :type-prescription)

(local
  (def-gl-thm rm132-less-than-expt-2-32-helper
    :hyp (and (n08p byte0)
              (n08p byte1)
              (n08p byte2)
              (n08p byte3))
    :concl (< (LOGIOR (ASH (LOGIOR (ASH byte3 8)
                                   byte2)
                           16)
                      (ASH byte1 8)
                      byte0)
              4294967296)
    :g-bindings
    `((byte0 (:g-number ,(gl-int 0 2 9)))
      (byte1 (:g-number ,(gl-int 9 2 9)))
      (byte2 (:g-number ,(gl-int 18 2 9)))
      (byte3 (:g-number ,(gl-int 27 2 9))))))

(defthm rm32-less-than-expt-2-32
  (implies (and (x86-32p x86-32)
                (n32p addr))
           (< (rm32 addr x86-32) 4294967296))
  :rule-classes :linear)

(in-theory (disable rm32))

(defun wm08 (addr val x86-32)
  (declare (xargs :stobjs x86-32
                  :guard (and (integerp addr)
                              (<= 0 addr)
                              (< addr *mem-size-in-bytes*)
                              (n08p val)
                              (x86-32p x86-32))))
  (!memi addr val x86-32))

(defthm x86-32p-wm08
  (implies (and (x86-32p x86-32)
                (n32p addr)
                (n08p byte))
           (x86-32p (wm08 addr byte x86-32))))

(in-theory (disable wm08))

(defun wm16 (addr val x86-32)
  (declare (xargs :stobjs x86-32
                  :guard (and (n32p addr)
                              (n16p val)
                              (x86-32p x86-32))))
  (let* ((byte0 (logand #xff val))
         (byte1 (logand #xff (ash val -8)))

         (x86-32 (!memi      addr  byte0 x86-32))
         (x86-32 (!memi (n32+ 1 addr) byte1 x86-32)))
    x86-32))

 (defthm x86-32p-wm16
   (implies (and (x86-32p x86-32)
                 (n32p addr)
                 (n16p word))
            (x86-32p (wm16 addr word x86-32))))

(in-theory (disable wm16))

(defun wm32 (addr val x86-32)
  (declare (xargs :stobjs x86-32
                  :guard (and (n32p addr)
                              (n32p val)
                              (x86-32p x86-32))))
  (let* ((byte0 (logand #xff val))
         (byte1 (logand #xff (ash val -8)))
         (byte2 (logand #xff (ash val -16)))
         (byte3 (logand #xff (ash val -32)))
         (x86-32 (!memi      addr  byte0 x86-32))
         (x86-32 (!memi (n32+ 1 addr) byte1 x86-32))
         (x86-32 (!memi (n32+ 2 addr) byte2 x86-32))
         (x86-32 (!memi (n32+ 3 addr) byte3 x86-32)))
    x86-32))

(defthm x86-32p-wm32
  (implies (and (x86-32p x86-32)
                (n32p addr)
                (n32p dword))
           (x86-32p (wm32 addr dword x86-32))))

(in-theory (disable wm32))

; ======================================================================
