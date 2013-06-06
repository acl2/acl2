

(in-package "GL")


(include-book "bvec-ite")
(include-book "tools/mv-nth" :dir :system)
(include-book "ihs/logops-definitions" :dir :system)

(defund int-set-sign (negp i)
  (declare (xargs :guard (integerp i)))
  (let ((i (lifix i)))
    (acl2::logapp (integer-length i) i (if negp -1 0))))

(defthm sign-of-int-set-sign
  (iff (< (int-set-sign negp i) 0)
       negp)
  :hints(("Goal" :in-theory (e/d* (int-set-sign)
                                  (acl2::logapp
                                   acl2::ifix-under-int-equiv)))))

(defthm int-set-sign-integerp
  (integerp (int-set-sign negp i))
  :rule-classes :type-prescription)

(defund non-int-fix (x)
  (declare (xargs :guard t))
  (and (not (integerp x)) x))

(defthm non-int-fix-when-non-integer
  (implies (not (integerp x))
           (equal (non-int-fix x) x))
  :hints(("Goal" :in-theory (enable non-int-fix)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defund maybe-integer (i x intp)
  (declare (xargs :guard (integerp i)))
  (if intp
      (ifix i)
    (non-int-fix x)))

(defthm maybe-integer-t
  (equal (maybe-integer i x t)
         (ifix i))
  :hints(("Goal" :in-theory (enable maybe-integer))))

(defthm maybe-integer-nil
  (equal (maybe-integer i x nil)
         (non-int-fix x))
  :hints(("Goal" :in-theory (enable maybe-integer))))






;; equality of two unsigned bdd vectors
(defund =-uu (a b)
  (declare (xargs :guard t
                  :measure (+ (len a) (len b))))
  (if (and (atom a) (atom b))
      t
    (b* (((mv head1 tail1)
          (if (atom a) (mv nil nil) (mv (car a) (cdr a))))
         ((mv head2 tail2)
          (if (atom b) (mv nil nil) (mv (car b) (cdr b)))))
      (bfr-and (bfr-iff head1 head2)
               (=-uu tail1 tail2)))))

(defund =-ss (a b)
  (declare (xargs :guard t
                  :measure (+ (len a) (len b))))
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
               (=-ss tail1 tail2)))))





(defund s-nthcdr (place n)
  (declare (xargs :guard (natp place)))
  (if (or (zp place) (atom n) (atom (cdr n)))
      n
    (s-nthcdr (1- place) (cdr n))))

(defund s-sign (x)
  (declare (xargs :guard t))
  (if (atom x) nil (car (last x))))


(defund +-ss (c v1 v2)
  (declare (xargs :measure (+ (len v1) (len v2))
                  :guard t))
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
          (cons s rst))))))




(defund lognot-bv (x)
  (declare (xargs :guard t
                  :measure (len x)))
  (if (atom x)
      nil
    (prog2$
     (acl2::last-chance-wash-memory)
     (cons (bfr-not (car x))
           (lognot-bv (cdr x))))))

(defund unary-minus-s (x)
  (declare (xargs :guard t))
  (if (consp x)
      (+-ss t nil (lognot-bv x))
    nil))


(defund *-ss (v1 v2)
  (declare (xargs :guard t
                  :measure (+ (len v1) (len v2))))
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
              (cons nil rest))))))

(defund <-=-ss (a b)
  (declare (xargs :guard t
                  :measure (+ (len a) (len b))))
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
            (bfr-and rst= (bfr-iff head1 head2)))))))

(defund <-ss (a b)
  (declare (xargs :guard t))
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
        (bfr-or rst< (bfr-and rst= head2 (bfr-not head1)))))))





(defund ash-ss (place n shamt)
  (declare (xargs :guard (posp place)
                  :measure (len shamt)))
  (b* (((mv shdig shrst shend)
        (if (atom shamt)
            (mv nil nil t)
          (if (atom (cdr shamt))
              (mv (car shamt) shamt t)
            (mv (car shamt) (cdr shamt) nil)))))
    (if shend
        (bfr-ite-bss shdig
                     (s-nthcdr 1 n)
                     (make-list-ac (1- place) nil n))
      (let ((rst (ash-ss (* 2 place) n shrst)))
        (bfr-ite-bss shdig
                     rst
                     (s-nthcdr place rst))))))



(defund logbitp-n2v (place digit n)
  (declare (xargs :guard (natp place)
                  :hints (("goal" :in-theory (enable len)))
                  :guard-hints ('(:in-theory (enable ash)))
                  :measure (len digit)))
  (if (atom n)
      nil
    (if (or (atom digit) (atom (cdr n)))
        (car n)
      (bfr-ite (car digit)
               (logbitp-n2v (ash place 1) (cdr digit) (s-nthcdr place n))
               (logbitp-n2v (ash place 1) (cdr digit) n)))))

(defund integer-length-s1 (offset x)
  (declare (xargs :guard (natp offset)
                  :measure (len x)))
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
                                        nil))))))))

(defund integer-length-s (x)
  (declare (xargs :guard t))
  (mv-let (ign res)
    (integer-length-s1 1 x)
    (declare (ignore ign))
    res))



(defund logand-ss (a b)
  (declare (xargs :guard t
                  :measure (+ (len a) (len b))))
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
          (cons c r))))))


;; Symbolically computes the FLOOR and MOD for positive divisor B (when MINUS-B
;; is the negation of B.)
(defund floor-mod-ss (a b minus-b)
  (declare (xargs :guard t
                  :measure (len a)))
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
             (+-ss nil minus-b rm)))))))

(defund floor-ss (a b)
  (declare (xargs :guard t))
  (bfr-ite-bss (=-ss b nil)
               nil
               (b* ((bsign (s-sign b))
                    (babs (bfr-ite-bss bsign (unary-minus-s b) b))
                    (anorm (bfr-ite-bss bsign (unary-minus-s a) a))
                    (bneg (unary-minus-s babs))
                    ((mv f &) (floor-mod-ss anorm babs bneg)))
                 f)))

(defund mod-ss (a b)
  (declare (xargs :guard t))
  (bfr-ite-bss (=-ss b nil)
               a
               (b* ((bsign (s-sign b))
                    (babs (bfr-ite-bss bsign (unary-minus-s b) b))
                    (anorm (bfr-ite-bss bsign (unary-minus-s a) a))
                    (bneg (unary-minus-s babs))
                    ((mv & m) (floor-mod-ss anorm babs bneg)))
                 (bfr-ite-bss bsign (unary-minus-s m) m))))

(defund truncate-ss (a b)
  (declare (xargs :guard t))
  (bfr-ite-bss (=-ss b nil)
               nil
               (b* ((bsign (s-sign b))
                    (asign (s-sign a))
                    (babs (bfr-ite-bss bsign (unary-minus-s b) b))
                    (aabs (bfr-ite-bss asign (unary-minus-s a) a))
                    (bneg (unary-minus-s babs))
                    ((mv f &) (floor-mod-ss aabs babs bneg)))
                 (bfr-ite-bss (bfr-xor bsign asign)
                              (unary-minus-s f) f))))




(defund rem-ss (a b)
  (declare (xargs :guard t))
  (bfr-ite-bss (=-ss b nil)
               a
               (b* ((bsign (s-sign b))
                    (asign (s-sign a))
                    (babs (bfr-ite-bss bsign (unary-minus-s b) b))
                    (aabs (bfr-ite-bss asign (unary-minus-s a) a))
                    (bneg (unary-minus-s babs))
                    ((mv & m) (floor-mod-ss aabs babs bneg)))
                 (bfr-ite-bss asign (unary-minus-s m) m))))






(defund lognot-s (a)
  (declare (xargs :guard t
                  :measure (len a)))
  (b* (((mv a1 aend)
        (if (atom a)
            (mv nil t)
          (if (atom (cdr a))
              (mv (car a) t)
            (mv (car a) nil)))))
    (if aend
        (list (bfr-not a1))
      (cons (bfr-not a1) (lognot-s (cdr a))))))


(defund logior-ss (a b)
  (declare (xargs :guard t
                  :measure (+ (len a) (len b))))
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
          (cons c r))))))


