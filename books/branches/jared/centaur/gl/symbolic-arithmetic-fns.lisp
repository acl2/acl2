

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




;; equality of two unsigned bool/bfr vectors
;; (defund =-uu (a b)
;;   (declare (xargs :guard t
;;                   :measure (+ (len a) (len b))))
;;   (if (and (atom a) (atom b))
;;       t
;;     (b* (((mv head1 tail1) (car/cdr a))
;;          ((mv head2 tail2) (car/cdr b)))
;;       (and (iff head1 head2)
;;            (=-uu tail1 tail2)))))

(defund bfr-=-uu (a b)
  (declare (xargs :guard t
                  :measure (+ (len a) (len b))))
  (if (and (atom a) (atom b))
      t
    (b* (((mv head1 tail1) (car/cdr a))
         ((mv head2 tail2) (car/cdr b)))
      (bfr-and (bfr-iff head1 head2)
               (bfr-=-uu tail1 tail2)))))



;; (defund =-ss (a b)
;;   (declare (xargs :guard t
;;                   :measure (+ (len a) (len b))))
;;   (b* (((mv head1 tail1 end1) (first/rest/end a))
;;        ((mv head2 tail2 end2) (first/rest/end b)))
;;     (if (and end1 end2)
;;         (iff head1 head2)
;;       (and (iff head1 head2)
;;            (=-ss tail1 tail2)))))

(defund bfr-=-ss (a b)
  (declare (xargs :guard t
                  :measure (+ (len a) (len b))))
  (b* (((mv head1 tail1 end1) (first/rest/end a))
       ((mv head2 tail2 end2) (first/rest/end b)))
    (if (and end1 end2)
        (bfr-iff head1 head2)
      (bfr-and (bfr-iff head1 head2)
               (bfr-=-ss tail1 tail2)))))





(defund logtail-ns (place n)
  (declare (xargs :guard (natp place)))
  (if (or (zp place) (s-endp n))
      n
    (logtail-ns (1- place) (scdr n))))

(defund s-sign (x)
  (declare (xargs :guard t))
  (b* (((mv first rest endp) (first/rest/end x)))
    (if endp
        first
      (s-sign rest))))


;; (defund +-ss (c v1 v2)
;;   (declare (xargs :measure (+ (len v1) (len v2))
;;                   :guard t))
;;   (b* (((mv head1 tail1 end1) (first/rest/end v1))
;;        ((mv head2 tail2 end2) (first/rest/end v2))
;;        (axorb (xor head1 head2))
;;        (s (xor c axorb)))
;;     (if (and end1 end2)
;;         (let ((last (if axorb (not c) head1)))
;;           (scons s (sterm last)))
;;       (let* ((c (or (and c axorb)
;;                     (and head1 head2)))
;;              (rst (+-ss c tail1 tail2)))
;;         (scons s rst)))))

(defund bfr-+-ss (c v1 v2)
  (declare (xargs :measure (+ (len v1) (len v2))
                  :guard t))
  (b* (((mv head1 tail1 end1) (first/rest/end v1))
       ((mv head2 tail2 end2) (first/rest/end v2))
       (axorb (bfr-xor head1 head2))
       (s (bfr-xor c axorb)))
    (if (and end1 end2)
        (let ((last (bfr-ite axorb (bfr-not c) head1)))
          (bfr-scons s (bfr-sterm last)))
      (let* ((c (bfr-or (bfr-and c axorb)
                        (bfr-and head1 head2)))
             (rst (bfr-+-ss c tail1 tail2)))
        (bfr-scons s rst)))))

(defthm not-s-endp-compound-recognizer
  (implies (not (s-endp x))
           (consp x))
  :hints(("Goal" :in-theory (enable s-endp)))
  :rule-classes :compound-recognizer)

;; (defund lognot-s (x)
;;   (declare (xargs :guard t))
;;   (b* (((mv head tail end) (first/rest/end x)))
;;     (if end
;;         (sterm (not head))
;;       (scons (not head)
;;              (lognot-s tail)))))

;; (defund lognot-bv (x)
;;   (declare (xargs :guard t
;;                   :measure (len x)))
;;   (if (atom x)
;;       nil
;;     (cons (not (car x))
;;           (lognot-bv (cdr x)))))

(defund bfr-lognot-s (x)
  (declare (xargs :guard t))
  (b* (((mv head tail end) (first/rest/end x)))
    (if end
        (bfr-sterm (bfr-not head))
      (bfr-scons (bfr-not head)
                 (bfr-lognot-s tail)))))

;; (defund unary-minus-s (x)
;;   (declare (xargs :guard t))
;;   (+-ss t nil (lognot-s x)))

(defund bfr-unary-minus-s (x)
  (declare (xargs :guard t))
  (bfr-+-ss t nil (bfr-lognot-s x)))

;; (defund *-ss (v1 v2)
;;   (declare (xargs :guard t
;;                   :measure (+ (len v1) (len v2))))
;;   (b* (((mv dig1 rest end1) (first/rest/end v1)))
;;     (if end1
;;         (if dig1
;;             (unary-minus-s v2)
;;           nil)
;;       (let ((rest (*-ss rest v2)))
;;         (+-ss nil
;;               (if dig1 v2 nil)
;;               (scons nil rest))))))


(defund bfr-*-ss (v1 v2)
  (declare (xargs :guard t
                  :measure (+ (len v1) (len v2))))
  (b* (((mv dig1 rest end1) (first/rest/end v1)))
    (if end1
        (bfr-ite-bss dig1
                     (bfr-unary-minus-s v2)
                     nil)
      (let ((rest (bfr-*-ss rest v2)))
        (bfr-+-ss nil
              (bfr-ite-bss dig1 v2 nil)
              (bfr-scons nil rest))))))

;; (defund <-=-ss (a b)
;;   (declare (xargs :guard t
;;                   :measure (+ (len a) (len b))))
;;   (b* (((mv head1 tail1 end1) (first/rest/end a))
;;        ((mv head2 tail2 end2) (first/rest/end b)))
;;     (if (and end1 end2)
;;         (mv (and head1 (not head2))
;;             (iff head1 head2))
;;       (mv-let (rst< rst=)
;;         (<-=-ss tail1 tail2)
;;         (mv (or rst< (and rst= head2 (not head1)))
;;             (and rst= (iff head1 head2)))))))

(defund bfr-<-=-ss (a b)
  (declare (xargs :guard t
                  :measure (+ (len a) (len b))))
  (b* (((mv head1 tail1 end1) (first/rest/end a))
       ((mv head2 tail2 end2) (first/rest/end b)))
    (if (and end1 end2)
        (mv (bfr-and head1 (bfr-not head2))
            (bfr-iff head1 head2))
      (mv-let (rst< rst=)
        (bfr-<-=-ss tail1 tail2)
        (mv (bfr-or rst< (bfr-and rst= head2 (bfr-not head1)))
            (bfr-and rst= (bfr-iff head1 head2)))))))


;; (defund <-ss (a b)
;;   (declare (xargs :guard t))
;;   (b* (((mv head1 tail1 end1) (first/rest/end a))
;;        ((mv head2 tail2 end2) (first/rest/end b)))
;;     (if (and end1 end2)
;;         (and head1 (not head2))
;;       (mv-let (rst< rst=)
;;         (<-=-ss tail1 tail2)
;;         (or rst< (and rst= head2 (not head1)))))))

(defund bfr-<-ss (a b)
  (declare (xargs :guard t))
  (b* (((mv head1 tail1 end1) (first/rest/end a))
       ((mv head2 tail2 end2) (first/rest/end b)))
    (if (and end1 end2)
        (bfr-and head1 (bfr-not head2))
      (mv-let (rst< rst=)
        (bfr-<-=-ss tail1 tail2)
        (bfr-or rst< (bfr-and rst= head2 (bfr-not head1)))))))


;; (defund logapp-nss (n a b)
;;   (declare (xargs :guard (natp n)))
;;   (if (zp n)
;;       b
;;     (b* (((mv first rest &) (first/rest/end a)))
;;       (scons first (logapp-nss (1- n) rest b)))))

(defund bfr-logapp-nss (n a b)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      b
    (b* (((mv first rest &) (first/rest/end a)))
      (bfr-scons first (bfr-logapp-nss (1- n) rest b)))))

(defund bfr-logapp-nus (n a b)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      b
    (b* (((mv first rest) (car/cdr a)))
      (bfr-scons first (bfr-logapp-nus (1- n) rest b)))))

;; (defund ash-ss (place n shamt)
;;   (declare (xargs :guard (posp place)
;;                   :measure (len shamt)))
;;   (b* (((mv shdig shrst shend) (first/rest/end shamt)))
;;     (if shend
;;         (if shdig
;;             (logtail-ns 1 n)
;;           (logapp-nss (1- place) nil n))
;;       (let ((rst (ash-ss (* 2 place) n shrst)))
;;         (if shdig
;;             rst
;;           (logtail-ns place rst))))))

(defund bfr-ash-ss (place n shamt)
  (declare (xargs :guard (posp place)
                  :measure (len shamt)))
  (b* (((mv shdig shrst shend) (first/rest/end shamt)))
    (if shend
        (bfr-ite-bss shdig
                     (logtail-ns 1 n)
                     (bfr-logapp-nss (1- place) nil n))
      (let ((rst (bfr-ash-ss (* 2 place) n shrst)))
        (bfr-ite-bss shdig
                     rst
                     (logtail-ns place rst))))))

;; (defund logbitp-n2v (place digit n)
;;   (declare (xargs :guard (natp place)
;;                   :hints (("goal" :in-theory (enable len)))
;;                   ;; :guard-hints ('(:in-theory (e/d (ash) (floor))))
;;                   :measure (len digit)))
;;   (b* (((mv first & end) (first/rest/end n)))
;;     (if (or (atom digit) end)
;;         first
;;       (if (car digit)
;;           (logbitp-n2v (* 2 place) (cdr digit) (logtail-ns place n))
;;         (logbitp-n2v (* 2 place) (cdr digit) n)))))


(defund bfr-logbitp-n2v (place digit n)
  (declare (xargs :guard (natp place)
                  :hints (("goal" :in-theory (enable len)))
                  :guard-hints ('(:in-theory (enable ash)))
                  :measure (len digit)))
  (b* (((mv first & end) (first/rest/end n)))
    (if (or (atom digit) end)
        first
      (bfr-ite (car digit)
               (bfr-logbitp-n2v (* 2 place) (cdr digit) (logtail-ns place n))
               (bfr-logbitp-n2v (* 2 place) (cdr digit) n)))))


;; (defund integer-length-s1 (offset x)
;;   (declare (xargs :guard (natp offset)
;;                   :measure (len x)))
;;   (b* (((mv first rest end) (first/rest/end x)))
;;     (if end
;;         (mv nil nil)
;;       (mv-let (changed res)
;;         (integer-length-s1 (1+ offset) rest)
;;         (if (eq changed t)
;;             (mv t res)
;;           (let ((change (xor first (car rest))))
;;             (mv (or changed change)
;;                 (if changed
;;                     res
;;                   (if change
;;                       (i2v offset)
;;                     nil)))))))))

(defund bfr-integer-length-s1 (offset x)
  (declare (xargs :guard (natp offset)
                  :measure (len x)))
  (b* (((mv first rest end) (first/rest/end x)))
    (if end
        (mv nil nil)
      (mv-let (changed res)
        (bfr-integer-length-s1 (1+ offset) rest)
        (if (eq changed t)
            (mv t res)
          (let ((change (bfr-xor first (car rest))))
            (mv (bfr-or changed change)
                (bfr-ite-bss changed
                             res
                             (bfr-ite-bss change
                                          (i2v offset)
                                          nil)))))))))

;; (defund integer-length-s (x)
;;   (declare (xargs :guard t))
;;   (mv-let (ign res)
;;     (integer-length-s1 1 x)
;;     (declare (ignore ign))
;;     res))

(defund bfr-integer-length-s (x)
  (declare (xargs :guard t))
  (mv-let (ign res)
    (bfr-integer-length-s1 1 x)
    (declare (ignore ign))
    res))



;; (defund logand-ss (a b)
;;   (declare (xargs :guard t
;;                   :measure (+ (len a) (len b))))
;;   (b* (((mv af ar aend) (first/rest/end a))
;;        ((mv bf br bend) (first/rest/end b)))
;;     (if (and aend bend)
;;         (sterm (and af bf))
;;       (b* ((c (and af bf))
;;            (r (logand-ss ar br)))
;;         (scons c r)))))

(defund bfr-logand-ss (a b)
  (declare (xargs :guard t
                  :measure (+ (len a) (len b))))
  (b* (((mv af ar aend) (first/rest/end a))
       ((mv bf br bend) (first/rest/end b)))
    (if (and aend bend)
        (bfr-sterm (bfr-and af bf))
      (b* ((c (bfr-and af bf))
           (r (bfr-logand-ss ar br)))
        (bfr-scons c r)))))


;; ;; Symbolically computes the FLOOR and MOD for positive divisor B (when MINUS-B
;; ;; is the negation of B.)
;; (defund floor-mod-ss (a b minus-b)
;;   (declare (xargs :guard t
;;                   :measure (len a)))
;;   (b* (((mv first rest endp) (first/rest/end a)))
;;     (if endp
;;         (mv (sterm first)
;;             (if first
;;                 (+-ss nil '(t) b) ;; (mod -1 b) = b-1 with b > 0
;;               '(nil))) ;; (mod  0  b) = 0
;;       (b* (((mv rf rm)
;;             (floor-mod-ss rest b minus-b))
;;            (rm (scons first rm))
;;            (less (<-ss rm b))
;;            (rf (scons nil rf)))
;;         (mv (if less
;;                 rf
;;               (+-ss t nil rf))
;;             (if less
;;                 rm
;;               (+-ss nil minus-b rm)))))))

(defund bfr-floor-mod-ss (a b minus-b)
  (declare (xargs :guard t
                  :measure (len a)))
  (b* (((mv first rest endp) (first/rest/end a)))
    (if endp
        (mv (bfr-sterm first) ;; (floor  0  b) = 0
            (bfr-ite-bss
             first
             (bfr-+-ss nil '(t) b) ;; (mod -1 b) = b-1 with b > 0
             '(nil))) ;; (mod  0  b) = 0
      (b* (((mv rf rm)
            (bfr-floor-mod-ss rest b minus-b))
           (rm (bfr-scons first rm))
           (less (bfr-<-ss rm b))
           (rf (bfr-scons nil rf)))
        (mv (bfr-ite-bss
             less
             rf
             (bfr-+-ss t nil rf))
            (bfr-ite-bss
             less rm
             (bfr-+-ss nil minus-b rm)))))))


;; ;; (mv (sign b) (- b) (abs b) (- (abs b)))
;; (defund sign-abs-neg-s (x)
;;   (declare (xargs :guard t))
;;   (b* ((sign (s-sign x))
;;        (minus (unary-minus-s x)))
;;     (if sign
;;         (mv sign minus minus x)
;;       (mv sign minus x minus))))


(defund bfr-sign-abs-neg-s (x)
  (declare (xargs :guard t))
  (b* ((sign (s-sign x))
       (minus (bfr-unary-minus-s x))
       (abs (bfr-ite-bss sign minus x))
       (neg (bfr-ite-bss sign x minus)))
    (mv sign minus abs neg)))


;; (defund floor-ss (a b)
;;   (declare (xargs :guard t))
;;   (if (=-ss b nil)
;;       nil
;;     (b* (((mv bsign & babs bneg) (sign-abs-neg-s b))
;;          (anorm (if bsign (unary-minus-s a) a))
;;          ((mv f &) (floor-mod-ss anorm babs bneg)))
;;       f)))

(defund bfr-floor-ss (a b)
  (declare (xargs :guard t))
  (bfr-ite-bss (bfr-=-ss b nil)
               nil
               (b* (((mv bsign & babs bneg) (bfr-sign-abs-neg-s b))
                    (anorm (bfr-ite-bss bsign (bfr-unary-minus-s a) a))
                    ((mv f &) (bfr-floor-mod-ss anorm babs bneg)))
                 f)))

;; (defund mod-ss (a b)
;;   (declare (xargs :guard t))
;;   (if (=-ss b nil)
;;       a
;;     (b* (((mv bsign & babs bneg) (sign-abs-neg-s b))
;;          (anorm (if bsign (unary-minus-s a) a))
;;          ((mv & m) (floor-mod-ss anorm babs bneg)))
;;       (if bsign (unary-minus-s m) m))))

(defund bfr-mod-ss (a b)
  (declare (xargs :guard t))
  (bfr-ite-bss (bfr-=-ss b nil)
               a
               (b* (((mv bsign & babs bneg) (bfr-sign-abs-neg-s b))
                    (anorm (bfr-ite-bss bsign (bfr-unary-minus-s a) a))
                    ((mv & m) (bfr-floor-mod-ss anorm babs bneg)))
                 (bfr-ite-bss bsign (bfr-unary-minus-s m) m))))


;; (defund truncate-ss (a b)
;;   (declare (xargs :guard t))
;;   (if (=-ss b nil)
;;       nil
;;     (b* (((mv bsign & babs bneg) (sign-abs-neg-s b))
;;          ((mv asign & aabs &) (sign-abs-neg-s a))
;;          ((mv f &) (floor-mod-ss aabs babs bneg)))
;;       (if (xor bsign asign)
;;           (unary-minus-s f)
;;         f))))

(defund bfr-truncate-ss (a b)
  (declare (xargs :guard t))
  (bfr-ite-bss (bfr-=-ss b nil)
               nil
               (b* (((mv bsign & babs bneg) (bfr-sign-abs-neg-s b))
                    ((mv asign & aabs &) (bfr-sign-abs-neg-s a))
                    ((mv f &) (bfr-floor-mod-ss aabs babs bneg)))
                 (bfr-ite-bss (bfr-xor bsign asign)
                              (bfr-unary-minus-s f) f))))



;; (defund rem-ss (a b)
;;   (declare (xargs :guard t))
;;   (if (=-ss b nil)
;;       a
;;     (b* (((mv & & babs bneg) (sign-abs-neg-s b))
;;          ((mv asign & aabs &) (sign-abs-neg-s a))
;;          ((mv & m) (floor-mod-ss aabs babs bneg)))
;;       (if asign (unary-minus-s m) m))))


(defund bfr-rem-ss (a b)
  (declare (xargs :guard t))
  (bfr-ite-bss (bfr-=-ss b nil)
               a
               (b* (((mv & & babs bneg) (bfr-sign-abs-neg-s b))
                    ((mv asign & aabs &) (bfr-sign-abs-neg-s a))
                    ((mv & m) (bfr-floor-mod-ss aabs babs bneg)))
                 (bfr-ite-bss asign (bfr-unary-minus-s m) m))))


;; (defund logior-ss (a b)
;;   (declare (xargs :guard t
;;                   :measure (+ (len a) (len b))))
;;   (b* (((mv af ar aend) (first/rest/end a))
;;        ((mv bf br bend) (first/rest/end b)))
;;     (if (and aend bend)
;;         (sterm (or af bf))
;;       (b* ((c (or af bf))
;;            (r (logior-ss ar br)))
;;         (scons c r)))))

(defund bfr-logior-ss (a b)
  (declare (xargs :guard t
                  :measure (+ (len a) (len b))))
  (b* (((mv af ar aend) (first/rest/end a))
       ((mv bf br bend) (first/rest/end b)))
    (if (and aend bend)
        (bfr-sterm (bfr-or af bf))
      (b* ((c (bfr-or af bf))
           (r (bfr-logior-ss ar br)))
        (bfr-scons c r)))))




