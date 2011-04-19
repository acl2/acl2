

(in-package "GL")


(include-book "bvec-ite")
(include-book "tools/mv-nth" :dir :system)

                                          
              




;; equality of two unsigned bdd vectors
(defund =-uu (a b)
  (declare (xargs :guard (and (bfr-listp a) (bfr-listp b))
                  :verify-guards nil
                  :measure (+ (len a) (len b))))
  (bfr-list-fix-vars
   (a b)
   (if (and (atom a) (atom b))
       t
     (b* (((mv head1 tail1)
           (if (atom a) (mv nil nil) (mv (car a) (cdr a))))
          ((mv head2 tail2)
           (if (atom b) (mv nil nil) (mv (car b) (cdr b)))))
       (bfr-and (bfr-iff head1 head2)
                (=-uu tail1 tail2))))))

(defthm bfr-p-=-uu
  (bfr-p (=-uu a b))
  :hints(("Goal" :in-theory (enable =-uu))))

(prove-congruences (bfr-list-equiv bfr-list-equiv) =-uu)


(verify-guards =-uu)

(defund =-ss (a b)
  (declare (xargs :guard (and (bfr-listp a) (bfr-listp b))
                  :verify-guards nil
                  :measure (+ (len a) (len b))))
  (bfr-list-fix-vars
   (a b)
   (b* (((mv head1 tail1 end1)
         (if (atom a)
             (mv nil nil t)
           (if (atom (cdr a))
               (mv (car a) a t)
             (mv (car a) (cdr a) nil))))
        ((mv head2 tail2 end2)
         (if (atom b)
             (mv nil nil t)
           (if (atom (cdr b))
               (mv (car b) b t)
             (mv (car b) (cdr b) nil)))))
     (if (and end1 end2)
         (bfr-iff head1 head2)
       (bfr-and (bfr-iff head1 head2)
                (=-ss tail1 tail2))))))

(defthm bfr-p-=-ss
  (bfr-p (=-ss a b))
  :hints(("Goal" :in-theory (enable =-ss))))

(verify-guards =-ss)

(prove-congruences (bfr-list-equiv bfr-list-equiv) =-ss)






(defund s-nthcdr (place n)
  (declare (xargs :guard (and (natp place) (bfr-listp n))))
  (bfr-list-fix-vars
   (n)
   (if (or (zp place) (atom n) (atom (cdr n)))
       n
     (s-nthcdr (1- place) (cdr n)))))

(defthm bfr-listp-s-nthcdr
  (bfr-listp (s-nthcdr place n))
  :hints(("Goal" :in-theory (enable s-nthcdr))))

(prove-congruences (nil bfr-list-equiv) s-nthcdr)



(defund s-sign (x)
  (declare (xargs :guard (bfr-listp x)))
  (bfr-list-fix-vars
   (x)
   (if (atom x) nil (car (last x)))))

(defthm bfr-p-s-sign
  (bfr-p (s-sign x))
  :hints(("Goal" :in-theory (enable s-sign bfr-list-fix))))

(prove-congruences (bfr-list-equiv) s-sign)








(defund +-ss (c v1 v2)
  (declare (xargs :measure (+ (len v1) (len v2))
                  :guard (and (bfr-p c)
                              (bfr-listp v1)
                              (bfr-listp v2))))
  (bfr-list-fix-vars
   (v1 v2)
   (bfr-fix-vars
    (c)
    (b* (((mv head1 tail1 end1)
          (if (atom v1)
              (mv nil nil t)
            (if (atom (cdr v1))
                (mv (car v1) v1 t)
              (mv (car v1) (cdr v1) nil))))
         ((mv head2 tail2 end2)
          (if (atom v2)
              (mv nil nil t)
            (if (atom (cdr v2))
                (mv (car v2) v2 t)
              (mv (car v2) (cdr v2) nil))))
         (axorb (bfr-xor head1 head2))
         (s (bfr-xor c axorb)))
      (if (and end1 end2)
          (let ((last (bfr-ite axorb (bfr-not c) head1)))
            (if (hqual s last)
                (list s)
              (list s last)))
        (let* ((c (bfr-or (bfr-and c axorb)
                          (bfr-and head1 head2)))
               (rst (+-ss c tail1 tail2)))
          (if (and (atom (cdr rst))
                   (hqual s (car rst)))
              rst
            (cons s rst))))))))


(defthm bfr-listp-+-ss
  (bfr-listp (+-ss c v1 v0))
  :hints(("Goal" :in-theory (enable +-ss))))

(prove-congruences (bfr-equiv bfr-list-equiv bfr-list-equiv) +-ss)







(defund lognot-bv (x)
  (declare (xargs :guard (bfr-listp x)
                  :measure (len x)))
  (bfr-list-fix-vars
   (x)
   (if (atom x)
       nil
     (prog2$
      (acl2::last-chance-wash-memory)
      (cons (bfr-not (car x))
            (lognot-bv (cdr x)))))))

(defthm bfr-listp-lognot-bv
  (bfr-listp (lognot-bv x))
  :hints(("Goal" :in-theory (enable lognot-bv))))

(prove-congruences (bfr-list-equiv) lognot-bv)

(defund unary-minus-s (x)
  (declare (xargs :guard (bfr-listp x)))
  (bfr-list-fix-vars
   (x)
   (if (consp x)
       (+-ss t nil (lognot-bv x))
     nil)))

(defthm bfr-listp-unary-minus-s
  (bfr-listp (unary-minus-s x))
  :hints(("Goal" :in-theory (enable unary-minus-s))))

(prove-congruences (bfr-list-equiv) unary-minus-s)





(defund *-ss (v1 v2)
  (declare (xargs :guard (and (bfr-listp v1) (bfr-listp v2))
                  :measure (+ (len v1) (len v2))))
  (bfr-list-fix-vars
   (v1 v2)
   (b* (((mv dig1 end1)
         (if (atom v1)
             (mv nil t)
           (if (atom (cdr v1))
               (mv (car v1) t)
             (mv (car v1) nil)))))
     (if end1
         (bfr-ite-bss dig1
                      (unary-minus-s v2)
                      nil)
       (let ((rest (*-ss (cdr v1) v2)))
         (+-ss nil
               (bfr-ite-bss dig1 v2 nil)
               (cons nil rest)))))))


(defthm bfr-listp-*-ss
  (bfr-listp (*-ss v1 v2))
  :hints(("Goal" :in-theory (enable *-ss))))

(prove-congruences (bfr-list-equiv bfr-list-equiv) *-ss)



(defund <-=-ss (a b)
  (declare (xargs :guard (and (bfr-listp a) (bfr-listp b))
                  :verify-guards nil
                  :measure (+ (len a) (len b))))
  (bfr-list-fix-vars
   (a b)
   (b* (((mv head1 tail1 end1)
         (if (atom a)
             (mv nil nil t)
           (if (atom (cdr a))
               (mv (car a) a t)
             (mv (car a) (cdr a) nil))))
        ((mv head2 tail2 end2)
         (if (atom b)
             (mv nil nil t)
           (if (atom (cdr b))
               (mv (car b) b t)
             (mv (car b) (cdr b) nil)))))
     (if (and end1 end2)
         (mv (bfr-and head1 (bfr-not head2))
             (bfr-iff head1 head2))
       (mv-let (rst< rst=)
         (<-=-ss tail1 tail2)
         (mv (bfr-or rst< (bfr-and rst= head2 (bfr-not head1)))
             (bfr-and rst= (bfr-iff head1 head2))))))))

(defthm bfr-p-<-=-ss
  (and (bfr-p (mv-nth 0 (<-=-ss a b)))
       (bfr-p (mv-nth 1 (<-=-ss a b))))
  :hints(("Goal" :in-theory (enable <-=-ss))))

(verify-guards <-=-ss)

(prove-congruences (bfr-list-equiv bfr-list-equiv) <-=-ss)


(defund <-ss (a b)
  (declare (xargs :guard (and (bfr-listp a) (bfr-listp b))))
  (bfr-list-fix-vars
   (a b)
   (b* (((mv head1 tail1 end1)
         (if (atom a)
             (mv nil nil t)
           (if (atom (cdr a))
               (mv (car a) a t)
             (mv (car a) (cdr a) nil))))
        ((mv head2 tail2 end2)
         (if (atom b)
             (mv nil nil t)
           (if (atom (cdr b))
               (mv (car b) b t)
             (mv (car b) (cdr b) nil)))))
     (if (and end1 end2)
         (bfr-and head1 (bfr-not head2))
       (mv-let (rst< rst=)
         (<-=-ss tail1 tail2)
         (bfr-or rst< (bfr-and rst= head2 (bfr-not head1))))))))


(defthm bfr-p-<-ss
  (bfr-p (<-ss a b))
  :hints(("Goal" :in-theory (enable <-ss))))

(prove-congruences (bfr-list-equiv bfr-list-equiv) <-ss)



(defund mk-bfr-list-ac (n x acc)
  (declare (xargs :guard (and (natp n) (bfr-p x) (bfr-listp acc))))
  (bfr-list-fix-vars
   (acc)
   (bfr-fix-vars
    (x)
    (make-list-ac n x acc))))

(defthm bfr-listp-mk-list-ac
  (implies (and (bfr-p x) (bfr-listp acc))
           (bfr-listp (make-list-ac n x acc))))

(defthm bfr-listp-mk-bfr-list-ac
  (bfr-listp (mk-bfr-list-ac n x acc))
  :hints(("Goal" :in-theory (enable mk-bfr-list-ac))))

(prove-congruences (nil bfr-equiv bfr-list-equiv) mk-bfr-list-ac)
  


(defund ash-ss (place n shamt)
  (declare (xargs :guard (and (posp place)
                              (bfr-listp n)
                              (bfr-listp shamt))
                  :verify-guards nil
                  :measure (len shamt)))
  (bfr-list-fix-vars
   (n shamt)
   (b* (((mv shdig shrst shend)
         (if (atom shamt)
             (mv nil nil t)
           (if (atom (cdr shamt))
               (mv (car shamt) shamt t)
             (mv (car shamt) (cdr shamt) nil)))))
     (if shend
         (bfr-ite-bss shdig
                      (s-nthcdr 1 n)
                      (mk-bfr-list-ac (1- place) nil n))
       (let ((rst (ash-ss (* 2 place) n shrst)))
         (bfr-ite-bss shdig
                      rst
                      (s-nthcdr place rst)))))))

(defthm bfr-listp-ash-ss
  (bfr-listp (ash-ss place n shamt))
  :hints(("Goal" :in-theory (enable ash-ss))))

(verify-guards ash-ss)

(prove-congruences (nil bfr-list-equiv bfr-list-equiv) ash-ss)




(defund logbitp-n2v (place digit n)
  (declare (xargs :guard (and (natp place) (bfr-listp digit) (bfr-listp n))
                  :verify-guards nil
                  :hints (("goal" :in-theory (enable len bfr-list-fix)))
                  :measure (len digit)))
   (bfr-list-fix-vars
    (n digit)
    (if (atom n)
        nil
      (if (or (atom digit) (atom (cdr n)))
          (car n)
        (bfr-ite (car digit)
                 (logbitp-n2v (ash place 1) (cdr digit) (s-nthcdr place n))
                 (logbitp-n2v (ash place 1) (cdr digit) n))))))

(defthm bfr-p-logbitp-n2v
  (bfr-p (logbitp-n2v place digit n))
  :hints(("Goal" :in-theory (enable logbitp-n2v))))

(verify-guards logbitp-n2v
               :hints (("goal" :in-theory (enable ash))))

(prove-congruences (nil bfr-list-equiv bfr-list-equiv) logbitp-n2v)


(defund integer-length-s1 (offset x)
  (declare (xargs :guard (and (natp offset) (bfr-listp x))
                  :measure (len x)
                  :verify-guards nil))
  (bfr-list-fix-vars
   (x)
   (if (or (atom x) (atom (cdr x)))
       (mv nil nil)
     (mv-let (changed res)
       (integer-length-s1 (1+ offset) (cdr x))
       (if (eq changed t)
           (mv t res)
         (let ((change (bfr-xor (car x) (cadr x))))
           (mv (bfr-or changed change)
               (bfr-ite-bss changed
                            res
                            (bfr-ite-bss change
                                         (i2v offset)
                                         nil)))))))))

(defthm bfr-listp-integer-length-s1
  (and (bfr-p (mv-nth 0 (integer-length-s1 offs x)))
       (bfr-listp (mv-nth 1 (integer-length-s1 offs x))))
  :hints(("Goal" :in-theory (enable integer-length-s1))))

(verify-guards integer-length-s1)

(prove-congruences (nil bfr-list-equiv) integer-length-s1)

(defund integer-length-s (x)
  (declare (xargs :guard (bfr-listp x)))
  (bfr-list-fix-vars
   (x)
   (mv-let (ign res)
     (integer-length-s1 1 x)
     (declare (ignore ign))
     res)))

(defthm bfr-listp-integer-length-s
  (bfr-listp (integer-length-s x))
  :hints(("Goal" :in-theory (enable integer-length-s))))

(prove-congruences (bfr-list-equiv) integer-length-s)




(defund logand-ss (a b)
  (declare (xargs :guard (and (bfr-listp a) (bfr-listp b))
                  :measure (+ (len a) (len b))))
  (bfr-list-fix-vars
   (a b)
   (b* (((mv af ar aend)
         (if (atom a)
             (mv nil nil t)
           (if (atom (cdr a))
               (mv (car a) a t)
             (mv (car a) (cdr a) nil))))
        ((mv bf br bend)
         (if (atom b)
             (mv nil nil t)
           (if (atom (cdr b))
               (mv (car b) b t)
             (mv (car b) (cdr b) nil)))))
     (if (and aend bend)
         (list (bfr-and af bf))
       (b* ((c (bfr-and af bf))
            (r (logand-ss ar br)))
         (if (and (atom (cdr r))
                  (hqual (car r) c))
             r
           (cons c r)))))))

(defthm bfr-listp-logand-ss
  (bfr-listp (logand-ss a b))
  :hints(("Goal" :in-theory (enable logand-ss))))

(prove-congruences (bfr-list-equiv bfr-list-equiv) logand-ss)


;; Symbolically computes the FLOOR and MOD for positive divisor B (when MINUS-B
;; is the negation of B.)
(defund floor-mod-ss (a b minus-b)
  (declare (xargs :guard (and (bfr-listp a) (bfr-listp b)
                              (bfr-listp minus-b))
                  :verify-guards nil
                  :hints(("Goal" :in-theory (enable bfr-list-fix)))
                  :measure (len a)))
  (bfr-list-fix-vars
   (a b minus-b)
   (b* (((mv digit endp)
         (if (atom a)
             (mv nil t)
           (if (atom (cdr a))
               (mv (car a) t)
             (mv (car a) nil)))))
     (if endp
         (mv (bfr-ite-bss
              digit
              '(t) ;; (floor -1  b) = -1 with b > 0
              '(nil)) ;; (floor  0  b) = 0
             (bfr-ite-bss
              digit
              (+-ss nil '(t) b) ;; (mod -1 b) = b-1 with b > 0
              '(nil))) ;; (mod  0  b) = 0
       (b* (((mv rf rm)
             (floor-mod-ss (cdr a) b minus-b))
            (rm (cons (car a) (if (atom rm) '(nil) rm)))
            (less (<-ss rm b))
            (rf (cons nil rf)))
         (mv (bfr-ite-bss
              less
              rf
              (+-ss t nil rf))
             (bfr-ite-bss
              less rm
              (+-ss nil minus-b rm))))))))

(defthm bfr-listp-floor-mod-ss
  (and (bfr-listp (mv-nth 0 (floor-mod-ss a b minus-b)))
       (bfr-listp (mv-nth 1 (floor-mod-ss a b minus-b))))
  :hints(("Goal" :in-theory (enable floor-mod-ss))))

(verify-guards floor-mod-ss)

(prove-congruences (bfr-list-equiv bfr-list-equiv bfr-list-equiv) floor-mod-ss)

(defund floor-ss (a b)
  (declare (xargs :guard (and (bfr-listp a) (bfr-listp b))))
  (bfr-list-fix-vars
   (a b)
   (bfr-ite-bss (=-ss b nil)
                nil
                (b* ((bsign (s-sign b))
                     (babs (bfr-ite-bss bsign (unary-minus-s b) b))
                     (anorm (bfr-ite-bss bsign (unary-minus-s a) a))
                     (bneg (unary-minus-s babs))
                     ((mv f &) (floor-mod-ss anorm babs bneg)))
                  f))))

(defthm bfr-listp-floor-ss
  (bfr-listp (floor-ss a b))
  :hints(("Goal" :in-theory (enable floor-ss))))

(prove-congruences (bfr-list-equiv bfr-list-equiv) floor-ss)


(defund mod-ss (a b)
  (declare (xargs :guard (and (bfr-listp a) (bfr-listp b))))
  (bfr-list-fix-vars
   (a b)
   (bfr-ite-bss (=-ss b nil)
                a
                (b* ((bsign (s-sign b))
                     (babs (bfr-ite-bss bsign (unary-minus-s b) b))
                     (anorm (bfr-ite-bss bsign (unary-minus-s a) a))
                     (bneg (unary-minus-s babs))
                     ((mv & m) (floor-mod-ss anorm babs bneg)))
                  (bfr-ite-bss bsign (unary-minus-s m) m)))))

(defthm bfr-listp-mod-ss
  (bfr-listp (mod-ss a b))
  :hints(("Goal" :in-theory (enable mod-ss))))

(prove-congruences (bfr-list-equiv bfr-list-equiv) mod-ss)


(defund truncate-ss (a b)
  (declare (xargs :guard (and (bfr-listp a) (bfr-listp b))))
  (bfr-list-fix-vars
   (a b)
   (bfr-ite-bss (=-ss b nil)
                nil
                (b* ((bsign (s-sign b))
                     (asign (s-sign a))
                     (babs (bfr-ite-bss bsign (unary-minus-s b) b))
                     (aabs (bfr-ite-bss asign (unary-minus-s a) a))
                     (bneg (unary-minus-s babs))
                     ((mv f &) (floor-mod-ss aabs babs bneg)))
                  (bfr-ite-bss (bfr-xor bsign asign)
                               (unary-minus-s f) f)))))

(defthm bfr-listp-truncate-ss
  (bfr-listp (truncate-ss a b))
  :hints(("Goal" :in-theory (enable truncate-ss))))

(prove-congruences (bfr-list-equiv bfr-list-equiv) truncate-ss)

                  




(defund rem-ss (a b)
  (declare (xargs :guard (and (bfr-listp a) (bfr-listp b))))
  (bfr-list-fix-vars
   (a b)
   (bfr-ite-bss (=-ss b nil)
                a
                (b* ((bsign (s-sign b))
                     (asign (s-sign a))
                     (babs (bfr-ite-bss bsign (unary-minus-s b) b))
                     (aabs (bfr-ite-bss asign (unary-minus-s a) a))
                     (bneg (unary-minus-s babs))
                     ((mv & m) (floor-mod-ss aabs babs bneg)))
                  (bfr-ite-bss asign (unary-minus-s m) m)))))

(defthm bfr-listp-rem-ss
  (bfr-listp (rem-ss a b))
  :hints(("Goal" :in-theory (enable rem-ss))))

(prove-congruences (bfr-list-equiv bfr-list-equiv) rem-ss)







(defund lognot-s (a)
  (declare (xargs :guard (bfr-listp a)
                  :measure (len a)))
  (bfr-list-fix-vars
   (a)
   (b* (((mv a1 aend)
         (if (atom a)
             (mv nil t)
           (if (atom (cdr a))
               (mv (car a) t)
             (mv (car a) nil)))))
     (if aend
         (list (bfr-not a1))
       (cons (bfr-not a1) (lognot-s (cdr a)))))))

(defthm bfr-listp-lognot-s
  (bfr-listp (lognot-s a))
  :hints(("Goal" :in-theory (enable lognot-s))))


(prove-congruences (bfr-list-equiv) lognot-s)



(defund logior-ss (a b)
  (declare (xargs :guard (and (bfr-listp a) (bfr-listp b))
                  :measure (+ (len a) (len b))))
  (bfr-list-fix-vars
   (a b)
   (b* (((mv af ar aend)
         (if (atom a)
             (mv nil nil t)
           (if (atom (cdr a))
               (mv (car a) a t)
             (mv (car a) (cdr a) nil))))
        ((mv bf br bend)
         (if (atom b)
             (mv nil nil t)
           (if (atom (cdr b))
               (mv (car b) b t)
             (mv (car b) (cdr b) nil)))))
     (if (and aend bend)
         (list (bfr-or af bf))
       (b* ((c (bfr-or af bf))
            (r (logior-ss ar br)))
         (if (and (atom (cdr r))
                  (hqual (car r) c))
             r
           (cons c r)))))))

(defthm bfr-listp-logior-ss
  (bfr-listp (logior-ss a b))
  :hints(("Goal" :in-theory (enable logior-ss))))

(prove-congruences (bfr-list-equiv bfr-list-equiv) logior-ss)

