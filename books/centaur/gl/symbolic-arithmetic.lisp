; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")
(include-book "symbolic-arithmetic-fns")
(local (include-book "clause-processors/find-subterms" :dir :system))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))


(defthm equal-complexes-rw
  (implies (and (acl2-numberp x)
                (rationalp a)
                (rationalp b))
           (equal (equal (complex a b) x)
                  (and (equal a (realpart x))
                       (equal b (imagpart x)))))
  :hints (("goal" :use ((:instance realpart-imagpart-elim)))))


(local (in-theory (disable bfr-ite-bss-fn)))

(local (defun cdr3-ind (a e b)
         (declare (xargs :measure (+ (len a) (len e) (len b))))
         (if (and (atom a) (atom e) (atom b))
             (list a e b)
           (cdr3-ind (cdr a) (cdr e) (cdr b)))))

(local (defun scdr2-ind (a e)
         (declare (xargs :measure (+ (len a) (len e))))
         (if (and (s-endp a) (s-endp e))
             (list a e)
           (scdr2-ind (scdr a) (scdr e)))))

(local (defun scdr3-ind (a e b)
         (declare (xargs :measure (+ (len a) (len e) (len b))))
         (if (and (s-endp a) (s-endp e) (s-endp b))
             (list a e b)
           (scdr3-ind (scdr a) (scdr e) (scdr b)))))



(defsection =-uu

  (local (in-theory (enable bfr-=-uu)))

  ;; (defcong uv-equiv equal (=-uu a b) 1
  ;;   :hints(("Goal" :in-theory (e/d (uv-equiv-implies-cars-equiv)
  ;;                                  (uv-equiv))
  ;;           :induct (cdr3-ind a a-equiv b))))
  ;; (defcong uv-equiv equal (=-uu a b) 2
  ;;   :hints(("Goal" :in-theory (e/d (uv-equiv-implies-cars-equiv)
  ;;                                  (uv-equiv))
  ;;           :induct (cdr3-ind a b b-equiv))))

  (defthm bfr-=-uu-correct
    (equal (bfr-eval (bfr-=-uu a b) env)
           (= (bfr-list->u a env) (bfr-list->u b env))))

  (defthm pbfr-depends-on-of-bfr-=-uu
    (implies (and (not (pbfr-list-depends-on n p a))
                  (not (pbfr-list-depends-on n p b)))
             (not (pbfr-depends-on n p (bfr-=-uu a b))))
    :hints(("Goal" :in-theory (enable pbfr-list-depends-on)))))

(defsection =-ss

  (local (in-theory (enable bfr-=-ss)))

  ;; (defcong sv-equiv equal (=-ss a b) 1
  ;;   :hints(("Goal" :in-theory (e/d (scdr-when-equiv-to-endp)
  ;;                                  (sv-equiv))
  ;;           :induct (scdr3-ind a a-equiv b))))
  ;; (defcong sv-equiv equal (=-ss a b) 2
  ;;   :hints(("Goal" :in-theory (e/d (scdr-when-equiv-to-endp)
  ;;                                  (sv-equiv))
  ;;           :induct (scdr3-ind a b b-equiv))))

  (defthm bfr-=-ss-correct
    (equal (bfr-eval (bfr-=-ss a b) env)
           (= (bfr-list->s a env)
              (bfr-list->s b env)))
    :hints (("goal" :induct (scdr2-ind a b))))

  (defthm pbfr-depends-on-of-bfr-=-ss
    (implies (and (not (pbfr-list-depends-on n p a))
                  (not (pbfr-list-depends-on n p b)))
             (not (pbfr-depends-on n p (bfr-=-ss a b))))
    :hints(("Goal" :in-theory (enable pbfr-list-depends-on)))))

(defsection logtail-ns

  (local (in-theory (enable logtail-ns)))

  ;; (local (defun scdr2/count-ind (n x y)
  ;;          (declare (xargs :measure (nfix n)))
  ;;          (if (or (zp n) (s-endp x) (s-endp y))
  ;;              (list n x y)
  ;;            (scdr2/count-ind (1- (nfix n)) (scdr x) (scdr y)))))

  ;; (local (defthm logtail-of-equiv-to-endp
  ;;          (IMPLIES (AND (S-ENDP X-EQUIV)
  ;;                        (SV-EQUIV X X-EQUIV))
  ;;                   (SV-EQUIV (LOGTAIL-NS N X)
  ;;                             X))
  ;;          :hints (("goal" :induct (LOGTAIL-NS N X)
  ;;                   :in-theory (e/d (scdr-when-equiv-to-endp)
  ;;                                   (sv-equiv))))))

  ;; (defcong sv-equiv sv-equiv (logtail-ns n x) 2
  ;;   :hints(("Goal" :in-theory (e/d (scdr-when-equiv-to-endp)
  ;;                                  (sv-equiv))
  ;;           :induct (scdr2/count-ind n x x-equiv)
  ;;           :expand ((:free (x) (logtail-ns n x))))))

  (defthm bfr-logtail-ns-correct
    (equal (bfr-list->s (logtail-ns place n) env)
           (logtail place (bfr-list->s n env)))
    :hints(("Goal" :in-theory (enable acl2::logtail**))))

  (defthm pbfr-list-depends-on-of-logtail-ns
    (implies (not (pbfr-list-depends-on k p n))
             (not (pbfr-list-depends-on k p (logtail-ns place n))))
    :hints(("Goal" :in-theory (enable pbfr-list-depends-on)))))

  ;; (defthm logtail-ns-correct
  ;;   (equal (v2i (logtail-ns place n))
  ;;          (logtail place (v2i n)))
  ;;   :hints(("Goal" :in-theory (e/d (bfr-eval-list v2i acl2::logtail**))))))


(defsection s-sign
  (local (in-theory (enable s-sign)))

  ;; (defcong sv-equiv iff (s-sign x) 1
  ;;   :hints(("Goal" :in-theory (e/d (scdr-when-equiv-to-endp)
  ;;                                  (sv-equiv))
  ;;           :induct (scdr2-ind x x-equiv))))

  (defthm bfr-s-sign-correct
    (equal (bfr-eval (s-sign x) env)
           (< (bfr-list->s x env) 0)))

  (defthm pbfr-depends-on-of-s-sign
    (implies (not (pbfr-list-depends-on k p n))
             (not (pbfr-depends-on k p (s-sign n))))
    :hints(("Goal" :in-theory (enable pbfr-list-depends-on)))))

  ;; (defthm s-sign-correct
  ;;   (iff (s-sign x)
  ;;        (< (v2i x) 0))
  ;;   :hints(("Goal" :in-theory (enable v2i last s-sign)))))


(defsection +-ss

  ;; (local (defthm consp-cdr-sfix
  ;;          (implies (not (consp (cdr x)))
  ;;                   (not (consp (cdr (sfix x)))))))

  ;; (local (in-theory (enable car-of-sfix)))

  (local (in-theory (enable bfr-+-ss)))

  (defthm bfr-+-ss-correct
    (equal (bfr-list->s (bfr-+-ss c v1 v2) env)
           (+ (acl2::bool->bit (bfr-eval c env))
              (bfr-list->s v1 env)
              (bfr-list->s v2 env)))
    :hints(("Goal" :in-theory (e/d (logcons)
                                   ((:d bfr-+-ss)))
            :induct (bfr-+-ss c v1 v2)
            :expand ((bfr-+-ss c v1 v2)
                     ;; (:free (a b) (bfr-eval-list (cons a b) env))
                     ;; (bfr-eval-list nil env)
                     ))))


  (defthm pbfr-list-depends-on-of-bfr-+-ss
    (implies (and (not (pbfr-depends-on n p c))
                  (not (pbfr-list-depends-on n p v1))
                  (not (pbfr-list-depends-on n p v2)))
             (not (pbfr-list-depends-on n p (bfr-+-ss c v1 v2))))
    :hints(("Goal" :in-theory (e/d (pbfr-list-depends-on)
                                   ((pbfr-list-depends-on)
                                    (pbfr-depends-on)
                                    (:d bfr-+-ss)))
            :induct (bfr-+-ss c v1 v2)
            :expand ((bfr-+-ss c v1 v2)))))
)
 ;;           (and stable-under-simplificationp
;;                 (let ((call (acl2::find-call '+-ss (caddr (car (last clause))))))
;;                   (and call
;;                        (let ((res `(:expand (,call
;;                                              (bfr-+-ss c v1 v2)
;;                                              (:free (a b) (sfix (cons a b)))
;;                                              ;; (:free (a b) (bfr-eval-list (cons a b) env))
;;                                              ;; (bfr-eval-list nil env)
;;                                              )
;;                                     :use ((:instance
;;                                            bfr-eval-list-when-not-s-endp
;;                                            (x v1))
;;                                           (:instance
;;                                            bfr-eval-list-when-not-s-endp
;;                                            (x v2))))))
;; ;                         (or (cw "expand: ~x0~%" res)
;;                          res))))
;;            (bfr-reasoning)))

;;   ;; (defcong iff sv-equiv (+-ss c a b) 1)


;;   ;; (defthm +-ss-correct
;;   ;;   (equal (v2i (+-ss c v1 v2))
;;   ;;          (+ (acl2::bool->bit c)
;;   ;;             (v2i v1) (v2i v2)))
;;   ;;   :hints(("Goal" :in-theory (enable v2i +-ss logcons xor (:t v2i)))))


;;   ;; (defcong sv-equiv sv-equiv (+-ss c a b) 2
;;   ;;   :hints (("goal" :use ((:instance i2v-v2i
;;   ;;                          (v (+-ss c a b)))
;;   ;;                         (:instance i2v-v2i
;;   ;;                          (v (+-ss c a-equiv b))))
;;   ;;            :in-theory (disable sv-equiv)
;;   ;;            :do-not-induct t)
;;   ;;           (and stable-under-simplificationp
;;   ;;                '(:in-theory (enable sv-equiv)))))

;;   ;; (defcong sv-equiv sv-equiv (+-ss c a b) 3
;;   ;;   :hints (("goal" :use ((:instance i2v-v2i
;;   ;;                          (v (+-ss c a b)))
;;   ;;                         (:instance i2v-v2i
;;   ;;                          (v (+-ss c a b-equiv))))
;;   ;;            :in-theory (disable sv-equiv)
;;   ;;            :do-not-induct t)
;;   ;;           (and stable-under-simplificationp
;;   ;;                '(:in-theory (enable sv-equiv)))))


;;   ;; (local (defthm sv-equiv-sterm
;;   ;;          (implies (and (sv-equiv a b)
;;   ;;                        (s-endp b))
;;   ;;                   (and (equal (sv-equiv a (sterm c))
;;   ;;                               (iff (car b) c))
;;   ;;                        (equal (sv-equiv (sterm c) a)
;;   ;;                               (iff (car b) c))))
;;   ;;          :rule-classes ((:rewrite :backchain-limit-lst 0))))

;;   ;; (local (defthmd sv-equiv-+-ss-endp
;;   ;;          (implies (and (sv-equiv a a-equiv)
;;   ;;                        (s-endp a-equiv)
;;   ;;                        (s-endp b))
;;   ;;                   (sv-equiv (+-ss c a b)
;;   ;;                             ;; (scons (xor c (xor (car a-equiv) (car b)))
;;   ;;                             ;;        (sterm (if (xor (car a-equiv) (car b))
;;   ;;                             ;;                   c
;;   ;;                             ;;                 (car a-equiv))))))
;;   ;;                             (+-ss c a-equiv b)))
;;   ;;          :hints (("goal" :induct (+-ss c a b)
;;   ;;                   :expand ((:free (c b) (+-ss c a b))
;;   ;;                            (:free (c b) (+-ss c a-equiv b)))
;;   ;;                   :in-theory (e/d (sv-equiv-of-scons)
;;   ;;                                   (sv-equiv (:d +-ss) (sterm)))))))

;;   ;; ;; (local (defthm sv-equiv-+-ss-endp2
;;   ;; ;;          (implies (and (sv-equiv a a-equiv)
;;   ;; ;;                        (s-endp a-equiv)
;;   ;; ;;                        (s-endp b))
;;   ;; ;;                   (sv-equiv (+-ss c a b)
;;   ;; ;;                             (scons (xor c (xor (car a-equiv) (car b)))
;;   ;; ;;                                    (sterm (if (xor (car a-equiv) (car b))
;;   ;; ;;                                               (not c)
;;   ;; ;;                                             (car a-equiv))))))
;;   ;; ;;          :hints (("goal" :use sv-equiv-+-ss-endp
;;   ;; ;;                   :in-theory (disable sv-equiv)
;;   ;; ;;                   :do-not-induct t))))


;;   ;; ;; (local (defthm sv-equiv-sterm-2
;;   ;; ;;          (implies (sv-equiv (scdr a) (sterm c))
;;   ;; ;;                   (and (equal (sv-equiv a (sterm c))
;;   ;; ;;                               (iff (car a) c))
;;   ;; ;;                        (equal (sv-equiv (sterm c) a)
;;   ;; ;;                               (iff (car a) c))))
;;   ;; ;;          :hints(("Goal" :in-theory (e/d (scons sterm))))
;;   ;; ;;          :rule-classes ((:rewrite :backchain-limit-lst 0))))

;;   ;; (local (defthm sv-equiv-of-scons-2
;;   ;;          (equal (sv-equiv c (scons a b))
;;   ;;                 (and (iff (car c) a)
;;   ;;                      (sv-equiv (scdr c) b)))
;;   ;;          :hints (("goal" :in-theory (disable sv-equiv-of-scons)
;;   ;;                   :use sv-equiv-of-scons))))

;;   ;; ;; (local (defthm sv-equiv-of-singleton-2
;;   ;; ;;          (implies (and (sv-equiv a b)
;;   ;; ;;                        (s-endp b))
;;   ;; ;;                   (equal (sv-equiv (list c) a)
;;   ;; ;;                          (iff (car b) c)))
;;   ;; ;;          :hints(("Goal" :in-theory (enable sfix s-endp)))
;;   ;; ;;          :rule-classes ((:rewrite :backchain-limit-lst 0))))

;;   ;; (local (defun-nx +-ss-cong-ind (c a b e)
;;   ;;          (declare (xargs :measure (+ (len a) (len b) (len e))))
;;   ;;          (b* (((mv heada taila enda) (first/rest/end a))
;;   ;;               ((mv headb tailb endb) (first/rest/end b))
;;   ;;               ((mv ?heade taile ende) (first/rest/end e))
;;   ;;               (axorb (xor heada headb)))
;;   ;;            (if (and enda endb ende)
;;   ;;                (list c a b e)
;;   ;;              (+-ss-cong-ind (or (and c axorb)
;;   ;;                                 (and heada headb))
;;   ;;                             taila tailb taile)))))


;;   ;; (defcong sv-equiv sv-equiv (+-ss c a b) 2
;;   ;;   :hints (("goal" :induct (+-ss-cong-ind c a b a-equiv)
;;   ;;            :expand ((:free (c) (+-ss c a b))
;;   ;;                     (:free (c) (+-ss c a-equiv b)))
;;   ;;            :in-theory (e/d (scdr-when-equiv-to-endp
;;   ;;                             ;; sv-equiv-of-scons
;;   ;;                             )
;;   ;;                            (sv-equiv (sterm)
;;   ;;                                      ; sterm-when-s-endp
;;   ;;                                      ;; (:d +-ss)
;;   ;;                                      )))
;;   ;;           (and stable-under-simplificationp
;;   ;;                '(:use ((:instance sv-equiv-+-ss-endp))))))

;;   ;; (defthmd +-ss-commutes
;;   ;;   (sv-equiv (+-ss c a b)
;;   ;;             (+-ss c b a))
;;   ;;   :hints (("goal" :induct t :do-not-induct t
;;   ;;            :in-theory (disable sv-equiv))))

;;   ;; (defcong sv-equiv sv-equiv (+-ss c a b) 3
;;   ;;   :hints (("goal" :do-not-induct t
;;   ;;            :in-theory (disable sv-equiv)
;;   ;;            :use ((:instance +-ss-commutes)
;;   ;;                  (:instance +-ss-commutes (b b-equiv))))))

;;   ;; (defthmd bfr-eval-list-when-not-s-endp
;;   ;;   (implies (not (s-endp x))
;;   ;;            (sv-equiv (bfr-eval-list x env)
;;   ;;                      (scons (bfr-eval (car x) env)
;;   ;;                             (bfr-eval-list (scdr x) env))))
;;   ;;   :hints(("Goal" :in-theory (enable s-endp scdr scons))))

;;   ;; ;; (local (defthm v2i-when-empty
;;   ;; ;;          (implies (not (consp (cdr x)))
;;   ;; ;;                   (equal (v2i x)
;;   ;; ;;                          (if (car x) -1 0)))
;;   ;; ;;          :hints(("Goal" :in-theory (enable v2i)))
;;   ;; ;;          :rule-classes ((:rewrite :backchain-limit-lst 0))))

;;   ;; (local (in-theory (disable (:t acl2::logcons-negp)
;;   ;;                            (:t acl2::logcons-posp-2)
;;   ;;                            (:t acl2::logcons-natp)
;;   ;;                            (:t acl2::logcons-posp-1)
;;   ;;                            (:t natp)
;;   ;;                            (:t acl2::negp)
;;   ;;                            (:t posp)
;;   ;;                            (:t bfr-eval)
;;   ;;                            (:t bfr-+-ss)
;;   ;;                            (:t +-ss)
;;   ;;                            (:t v2i)
;;   ;;                            (:t acl2::logcons-type)
;;   ;;                            iff xor not
;;   ;;                            equal-of-booleans-rewrite
;;   ;;                            sets::double-containment
;;   ;;                            boolean-list-bfr-eval-list-const)))

;;   ;; (local (defthm open-+-ss-rec
;;   ;;          (implies (or (consp (cdr v1))
;;   ;;                       (consp (cdr v2)))
;;   ;;                   (equal (+-ss c v1 v2)
;;   ;;                          (B* (((MV HEAD1 TAIL1 ?END1)
;;   ;;                                (FIRST/REST/END V1))
;;   ;;                               ((MV HEAD2 TAIL2 ?END2)
;;   ;;                                (FIRST/REST/END V2))
;;   ;;                               (AXORB (XOR HEAD1 HEAD2))
;;   ;;                               (S (XOR C AXORB)))
;;   ;;                            (LET* ((C (OR (AND C AXORB) (AND HEAD1 HEAD2)))
;;   ;;                                   (RST (+-SS C TAIL1 TAIL2)))
;;   ;;                                  (IF (AND (ATOM (CDR RST)) (IFF S (CAR RST)))
;;   ;;                                      RST (CONS S RST))))))
;;   ;;          :rule-classes ((:rewrite :backchain-limit-lst 1))))

;;   ;; (local (defthm consp-of-bfr-eval-list
;;   ;;          (equal (consp (bfr-eval-list x env))
;;   ;;                 (consp x))
;;   ;;          :hints(("Goal" :in-theory (enable bfr-eval-list)))))

;;   ;; (local (defthm open-+-ss-base
;;   ;;          (implies (and (not (consp (cdr v1)))
;;   ;;                        (not (consp (cdr v2))))
;;   ;;                   (equal (+-ss c v1 v2)
;;   ;;                          (B* (((MV HEAD1 ?TAIL1 ?END1)
;;   ;;                                (FIRST/REST/END V1))
;;   ;;                               ((MV HEAD2 ?TAIL2 ?END2)
;;   ;;                                (FIRST/REST/END V2))
;;   ;;                               (AXORB (XOR HEAD1 HEAD2))
;;   ;;                               (S (XOR C AXORB)))
;;   ;;                            (LET ((LAST (IF AXORB (NOT C) HEAD1)))
;;   ;;                                 (IF (IFF S LAST)
;;   ;;                                     (LIST S)
;;   ;;                                     (LIST S LAST))))))
;;   ;;          :rule-classes ((:rewrite :backchain-limit-lst 0))))

;;   (local (in-theory (e/d (;; bfr-eval-list-when-not-s-endp
;;                           )
;;                          (bfr-eval-list-of-scdr))))

;;   (defthm s-endp-of-scons
;;     (equal (s-endp (scons b x))
;;            (and (s-endp x)
;;                 (iff b (car x))))
;;     :hints(("Goal" :in-theory (enable s-endp scons))))

;;   ;; (defthm sterm-of-bfr-eval-of-car
;;   ;;   (implies (s-endp x)
;;   ;;            (equal (sterm (bfr-eval (car x) env))
;;   ;;                   (bfr-eval-list x env)))
;;   ;;   :hints(("Goal" :in-theory (enable s-endp sterm)

;;   (defthm bfr-+-ss-correct
;;     (sv-equiv (bfr-eval-list (bfr-+-ss c v1 v2) env)
;;               (+-ss (bfr-eval c env)
;;                     (bfr-eval-list v1 env)
;;                     (bfr-eval-list v2 env)))
;;     :hints(("Goal" :in-theory (e/d ()
;;                                    ((:d bfr-+-ss) sv-equiv (sterm)))
;;             :induct (bfr-+-ss c v1 v2)
;;             :expand ((bfr-+-ss c v1 v2)
;;                      (:free (a b) (sfix (cons a b)))
;;                      ;; (:free (a b) (bfr-eval-list (cons a b) env))
;;                      ;; (bfr-eval-list nil env)
;;                      ))
;;            (and stable-under-simplificationp
;;                 (let ((call (acl2::find-call '+-ss (caddr (car (last clause))))))
;;                   (and call
;;                        (let ((res `(:expand (,call
;;                                              (bfr-+-ss c v1 v2)
;;                                              (:free (a b) (sfix (cons a b)))
;;                                              ;; (:free (a b) (bfr-eval-list (cons a b) env))
;;                                              ;; (bfr-eval-list nil env)
;;                                              )
;;                                     :use ((:instance
;;                                            bfr-eval-list-when-not-s-endp
;;                                            (x v1))
;;                                           (:instance
;;                                            bfr-eval-list-when-not-s-endp
;;                                            (x v2))))))
;; ;                         (or (cw "expand: ~x0~%" res)
;;                              res))))
;;            (bfr-reasoning)))

;; )


(defsection lognot-s
  (local (in-theory (enable bfr-lognot-s)))

  (defthm bfr-lognot-s-correct
    (equal (bfr-list->s (bfr-lognot-s x) env)
           (lognot (bfr-list->s x env))))

  (defthm pbfr-list-depends-on-of-bfr-lognot-s
    (implies (not (pbfr-list-depends-on k p x))
             (not (pbfr-list-depends-on k p (bfr-lognot-s x))))
    :hints(("Goal" :in-theory (enable pbfr-list-depends-on)))))

  ;; (defthm lognot-s-correct
  ;;   (equal (v2i (lognot-s x))
  ;;          (lognot (v2i x)))
  ;;   :hints(("Goal" :in-theory (enable v2i)))))


(defsection unary-minus-s
  (local (in-theory (enable bfr-unary-minus-s)))

  (defthm bfr-unary-minus-s-correct
    (equal (bfr-list->s (bfr-unary-minus-s x) env)
           (- (bfr-list->s x env)))
    :hints(("Goal" :in-theory (enable logcons lognot))))

  (defthm pbfr-list-depends-on-of-bfr-unary-minus-s
    (implies (not (pbfr-list-depends-on n p x))
             (not (pbfr-list-depends-on n p (bfr-unary-minus-s x))))
    :hints(("Goal" :in-theory (enable pbfr-list-depends-on)))))

  ;; (defthm unary-minus-s-correct
  ;;   (equal (v2i (unary-minus-s x))
  ;;          (- (v2i x)))
  ;;   :hints(("Goal" :in-theory (enable v2i lognot)))))

(defsection *-ss

  (local (in-theory (enable bfr-*-ss)))

  (defthm bfr-*-ss-correct
    (equal (bfr-list->s (bfr-*-ss v1 v2) env)
           (* (bfr-list->s v1 env)
              (bfr-list->s v2 env)))
    :hints(("Goal" :induct (bfr-*-ss v1 v2)
            :in-theory (enable bfr-*-ss logcons)
            :expand ((bfr-*-ss v1 v2)
                     (bfr-*-ss nil v2)))))

  (defthm pbfr-list-depends-on-of-bfr-*-ss
    (implies (and (not (pbfr-list-depends-on n p v1))
                  (not (pbfr-list-depends-on n p v2)))
             (not (pbfr-list-depends-on n p (bfr-*-ss v1 v2))))
    :hints(("Goal" :in-theory (e/d (pbfr-list-depends-on)
                                   ((pbfr-list-depends-on)
                                    (pbfr-depends-on)
                                    (:d bfr-*-ss)))
            :induct (bfr-*-ss v1 v2)
            :expand ((bfr-*-ss v1 v2))))))

  ;; (local (defthm +-double-minus
  ;;          (equal (+ x (- (* 2 x)))
  ;;                 (- x))))

  ;; (local (defthm +-double-minus-s
  ;;          (sv-equiv (+-ss nil v2 (scons nil (unary-minus-s v2)))
  ;;                    (unary-minus-s v2))
  ;;          :hints (("goal" :use ((:instance i2v-v2i
  ;;                                 (v (+-ss nil v2 (scons nil (unary-minus-s
  ;;                                                             v2)))))
  ;;                                (:instance i2v-v2i
  ;;                                 (v (unary-minus-s v2))))
  ;;                   :in-theory (enable logcons)))))

  ;; (local (defthmd *-ss-equiv-when-end
  ;;          (implies (and (sv-equiv v1 v1-equiv)
  ;;                        (s-endp v1-equiv))
  ;;                   (sv-equiv (*-ss v1 v2)
  ;;                             (*-ss v1-equiv v2)))
  ;;          :hints (("goal" :induct (*-ss v1 v2)
  ;;                   :in-theory (disable sv-equiv)))))

  ;; ;; (local (defun *-ss-cong-ind-1 (v1 v1e)
  ;; ;;          (b* (((mv dig1 rest1 end1) (first/rest/end v1))
  ;; ;;               ((mv ?dige reste ende) (first/rest/end v1e)))
  ;; ;;            (if (and end1 ende)
  ;; ;;                (list v1 v1e)
  ;; ;;              (*-ss-cong-ind-1 rest1 reste)))))

  ;; (defcong sv-equiv sv-equiv (*-ss x y) 1
  ;;   :hints (("goal" :induct (scdr2-ind x x-equiv)
  ;;            :in-theory (disable sv-equiv)))))

  ;; (local (in-theory (disable bfr-ite-bss-fn v2i
  ;;                            (:definition bfr-*-ss))))

  ;; (defthm bfr-*-ss-correct
  ;;   (



  ;; (local (bfr-reasoning-mode t))



  ;; )


(defsection <-=-ss
  (local (in-theory (enable bfr-<-=-ss)))

  (defthm bfr-<-=-ss-correct
    (b* (((mv less equal) (bfr-<-=-ss a b)))
      (and (equal (bfr-eval less env)
                  (< (bfr-list->s a env)
                     (bfr-list->s b env)))
           (equal (bfr-eval equal env)
                  (= (bfr-list->s a env)
                     (bfr-list->s b env)))))
    :hints(("Goal" :in-theory (e/d () ((:d bfr-<-=-ss)))
            :induct (bfr-<-=-ss a b)
            :expand ((bfr-<-=-ss a b)))))

  (defthm pbfr-depends-on-of-bfr-<-=-ss
    (b* (((mv less equal) (bfr-<-=-ss a b)))
      (implies (and (not (pbfr-list-depends-on n p a))
                    (not (pbfr-list-depends-on n p b)))
               (and (not (pbfr-depends-on n p less))
                    (not (pbfr-depends-on n p equal)))))))


(defsection bfr-<-ss

  (local (in-theory (enable bfr-<-ss)))

  (defthm bfr-<-ss-correct
    (equal (bfr-eval (bfr-<-ss a b) env)
           (< (bfr-list->s a env)
              (bfr-list->s b env))))

  (defthm pbfr-depends-on-of-bfr-<-ss
    (implies (and (not (pbfr-list-depends-on n p a))
                  (not (pbfr-list-depends-on n p b)))
             (not (pbfr-depends-on n p (bfr-<-ss a b))))))


(defsection bfr-logapp-nss
  (local (in-theory (enable bfr-logapp-nss)))

  (defthm bfr-logapp-nss-correct
    (equal (bfr-list->s (bfr-logapp-nss n a b) env)
           (logapp n (bfr-list->s a env)
                   (bfr-list->s b env)))
    :hints(("Goal" :in-theory (enable acl2::logapp** acl2::ash**))))

  (defthm pbfr-list-depends-on-of-bfr-logapp-nss
    (implies (and (not (pbfr-list-depends-on n p a))
                  (not (pbfr-list-depends-on n p b)))
             (not (pbfr-list-depends-on n p (bfr-logapp-nss m a b))))))

(defsection bfr-logapp-nus
  (local (in-theory (enable bfr-logapp-nus)))

  (defthm bfr-logapp-nus-correct
    (equal (bfr-list->s (bfr-logapp-nus n a b) env)
           (logapp n (bfr-list->u a env)
                   (bfr-list->s b env)))
    :hints(("Goal" :in-theory (enable acl2::logapp**
                                      acl2::ash**
                                      acl2::loghead**))))

  (defthm pbfr-list-depends-on-of-bfr-logapp-nus
    (implies (and (not (pbfr-list-depends-on n p a))
                  (not (pbfr-list-depends-on n p b)))
             (not (pbfr-list-depends-on n p (bfr-logapp-nus m a b))))))

(defsection bfr-ash-ss

  (local (in-theory (enable bfr-ash-ss)))

  (local
   (defthm reverse-distrib-1
     (and (equal (+ n n) (* 2 n))
          (implies (syntaxp (quotep k))
                   (equal (+ n (* k n)) (* (+ 1 k) n)))
          (implies (syntaxp (quotep k))
                   (equal (+ (- n) (* k n)) (* (+ -1 k) n)))
          (implies (syntaxp (quotep k))
                   (equal (+ (- n) (* k n) m) (+ (* (+ -1 k) n) m)))
          (implies (syntaxp (and (quotep a) (quotep b)))
                   (equal (+ (* a n) (* b n)) (* (+ a b) n)))
          (equal (+ n n m) (+ (* 2 n) m))
          (implies (syntaxp (quotep k))
                   (equal (+ n (* k n) m) (+ (* (+ 1 k) n) m)))
          (implies (syntaxp (and (quotep a) (quotep b)))
                   (equal (+ (* a n) (* b n) m) (+ (* (+ a b) n) m)))
          (equal (+ n (- (* 2 n)) m)
                 (+ (- n) m))
          )))

  (defthm bfr-ash-ss-correct
    (implies (posp place)
             (equal (bfr-list->s (bfr-ash-ss place n shamt) env)
                    (ash (bfr-list->s n env)
                         (+ -1 place (* place (bfr-list->s shamt env))))))
    :hints(("Goal" :in-theory (e/d (acl2::ash**) ((:d bfr-ash-ss)))
            :induct (bfr-ash-ss place n shamt)
            :expand ((bfr-ash-ss place n shamt)
                     (:free (b) (logcons b (bfr-list->s (scdr shamt) env)))))))

  (defthm pbfr-list-depends-on-of-bfr-ash-ss
    (implies (and (not (pbfr-list-depends-on n p a))
                  (not (pbfr-list-depends-on n p b)))
             (not (pbfr-list-depends-on n p (bfr-ash-ss place a b))))
    :hints(("Goal" :in-theory (enable pbfr-list-depends-on)))))

;; (encapsulate nil
;;   (local (defthm ash-of-logcons-0
;;            (implies (<= 0 (ifix m))
;;                     (equal (ash (logcons 0 n) m)
;;                            (logcons 0 (ash n m))))
;;            :hints(("Goal" :in-theory (enable* acl2::ihsext-inductions
;;                                               acl2::ihsext-recursive-redefs)))))

;;   (local
;;    (defthm make-list-ac-nil-v2i-eval
;;      (equal (v2i (bfr-eval-list (make-list-ac n nil m) env))
;;             (acl2::logapp (nfix n) 0 (v2i (bfr-eval-list m env))))
;;      :hints(("Goal" :in-theory (enable bfr-eval-list v2i acl2::ash**)))))

;;   (local (in-theory (disable acl2::logtail-identity
;;                              bfr-ite-bss-fn
;;                              equal-of-booleans-rewrite)))
;;   (local (in-theory (enable bfr-ash-ss logcons)))

;;   (local (defthm logtail-of-logtail-free
;;            (implies (equal y (logtail m z))
;;                     (equal (logtail n y)
;;                            (logtail (+ (nfix m) (nfix n)) z)))))


;;   ;; (local (bfr-reasoning-mode t))
;;   (defthm bfr-ash-ss-correct
;;     (implies (and
;;               (posp place))
;;              (equal (v2i (bfr-eval-list (bfr-ash-ss place n shamt) env))
;;                     (ash (v2i (bfr-eval-list n env))
;;                          (+ -1 place (* place (v2i (bfr-eval-list shamt env)))))))
;;     :hints (("goal" :induct (bfr-ash-ss place n shamt)
;;              :in-theory (e/d () ((:definition bfr-ash-ss)))
;;              :expand ((bfr-ash-ss place n shamt)
;;                       (bfr-ash-ss place n nil)
;;                       (bfr-eval-list shamt env)
;;                       (:free (a b) (v2i (cons a b)))))
;;             (and stable-under-simplificationp
;;                  '(:cases ((<= 0 (+ -1 PLACE
;;                                     (* 2 PLACE
;;                                        (V2I (BFR-EVAL-LIST (CDR SHAMT)
;;                                                            ENV))))))))
;;             (and stable-under-simplificationp
;;                  '(:cases ((<= 0 (+ -1 (* 2 PLACE)
;;                                     (* 2 PLACE
;;                                        (V2I (BFR-EVAL-LIST (CDR SHAMT)
;;                                        ENV)))))))))))

(defsection bfr-logbitp-n2v
  (local (in-theory (enable bfr-logbitp-n2v)))

  (defthm bfr-logbitp-n2v-correct
    (implies (posp place)
             (equal (bfr-eval (bfr-logbitp-n2v place digit n) env)
                    (logbitp (* place (bfr-list->u digit env))
                             (bfr-list->s n env))))
    :hints(("Goal" :in-theory (e/d (acl2::logbitp** logcons acl2::bool->bit)
                                   ((:d bfr-logbitp-n2v) floor
                                    boolean-listp))
            :induct (bfr-logbitp-n2v place digit n)
            :expand ((bfr-logbitp-n2v place digit n)))))

  (defthm pbfr-list-depends-on-of-bfr-logbitp-n2v
    (implies (and (not (pbfr-list-depends-on n p digit))
                  (not (pbfr-list-depends-on n p x)))
             (not (pbfr-depends-on n p (bfr-logbitp-n2v place digit x))))))

;; (encapsulate nil
;;   (local (in-theory (enable bfr-logbitp-n2v logcons acl2::ash**)))

;;   (defthm bfr-logbitp-n2v-correct
;;     (implies (and
;;               (posp place))
;;              (equal (bfr-eval (bfr-logbitp-n2v place digit n) env)
;;                     (logbitp (* place (v2n (bfr-eval-list digit env)))
;;                              (v2i (bfr-eval-list n env)))))
;;     :hints(("Goal" :in-theory (e/d (bfr-eval-list acl2::bool->bit)
;;                                    ((:definition bfr-logbitp-n2v) floor
;;                                     boolean-listp))
;;             :induct (bfr-logbitp-n2v place digit n)
;;             :expand ((bfr-logbitp-n2v place digit n)
;;                      (bfr-logbitp-n2v place nil n)
;;                      (bfr-logbitp-n2v place digit nil)
;;                      (:free (n) (logbitp 0 n))
;;                      (:free (a b) (v2i (cons a b)))
;;                      (:free (a b) (v2n (cons a b))))))))

(defsection bfr-integer-length
  (local (defthm bfr-eval-of-car-when-bfr-list->s
           (implies (and (equal (bfr-list->s x env) c)
                         (syntaxp (quotep c)))
                    (equal (bfr-eval (car x) env)
                           (equal 1 (logcar c))))))

  (defthm bfr-integer-length-s1-correct1
    (b* (((mv done ilen) (bfr-integer-length-s1 offset x))
         (xval (bfr-list->s x env)))
      (implies (posp offset)
               (and (equal (bfr-eval done env)
                           (and (not (equal xval 0))
                                (not (equal xval -1))))
                    (equal (bfr-list->s ilen env)
                           (if (or (equal xval 0)
                                   (equal xval -1))
                               0
                             (+ -1 offset (integer-length xval)))))))
    :hints(("Goal" :induct (bfr-integer-length-s1 offset x)
            :in-theory (enable (:i bfr-integer-length-s1)
                               acl2::integer-length**)
            ;; :in-theory (enable v2i-of-list-implies-car)
            :expand ((bfr-integer-length-s1 offset x)))
           (bfr-reasoning)))

  (defthm pbfr-depends-on-of-bfr-integer-length-s1-rw
    (b* (((mv done ilen) (bfr-integer-length-s1 offset x)))
      (implies (not (pbfr-list-depends-on n p x))
               (and (not (pbfr-depends-on n p done))
                    (not (pbfr-list-depends-on n p ilen)))))
    :hints(("Goal" :in-theory (enable pbfr-list-depends-on
                                      bfr-integer-length-s1))))

  (defthm bfr-integer-length-s-correct
    (equal (bfr-list->s (bfr-integer-length-s x) env)
           (integer-length (bfr-list->s x env)))
    :hints(("Goal" :in-theory (enable bfr-integer-length-s))))

  (defthm pbfr-depends-on-of-bfr-integer-length-s
    (implies (not (pbfr-list-depends-on n p x))
             (not (pbfr-list-depends-on n p (bfr-integer-length-s x))))
    :hints(("Goal" :in-theory (enable pbfr-list-depends-on
                                      bfr-integer-length-s)))))



;; (encapsulate nil
;;   (local (in-theory (enable bfr-integer-length-s1 bfr-integer-length-s)))
;;   (local (bfr-reasoning-mode t))
;;   (local (defthm bfr-integer-length-s1-correct1
;;            (implies (posp offset)
;;                     (and (equal (bfr-eval (mv-nth 0 (bfr-integer-length-s1 offset x)) env)
;;                                 (not (or (equal (v2i (bfr-eval-list x env)) 0)
;;                                          (equal (v2i (bfr-eval-list x env)) -1))))
;;                          (equal (v2i (bfr-eval-list (mv-nth 1 (bfr-integer-length-s1 offset
;;                                                                                  x))
;;                                                     env))
;;                                 (if (or (equal (v2i (bfr-eval-list x env)) 0)
;;                                         (equal (v2i (bfr-eval-list x env)) -1))
;;                                     0
;;                                   (+ -1 offset (integer-length (v2i (bfr-eval-list x env))))))))
;;            :hints(("Goal" :induct (bfr-integer-length-s1 offset x)
;;                    :in-theory (enable acl2::integer-length**)
;;                    ;; :in-theory (enable v2i-of-list-implies-car)
;;                    :expand ((bfr-integer-length-s1 offset x)
;;                             (bfr-integer-length-s1 offset nil)
;;                             (bfr-eval-list x env)
;;                             (:free (a b) (v2i (cons a b)))
;;                             (:free (a B) (bfr-eval-list (cons a b) env)))))))


;;   (defthm bfr-integer-length-s-correct
;;     (equal (v2i (bfr-eval-list (bfr-integer-length-s x) env))
;;            (integer-length (v2i (bfr-eval-list x env))))
;;     :hints(("Goal" :in-theory (disable bfr-integer-length-s1)))))

(defsection bfr-logand-ss
  (defthm bfr-logand-ss-correct
    (equal (bfr-list->s (bfr-logand-ss a b) env)
           (logand (bfr-list->s a env)
                   (bfr-list->s b env)))
    :hints(("Goal"
            :induct (scdr2-ind a b)
            :in-theory (e/d (acl2::logand**))
            :expand ((bfr-logand-ss a b)))))

  (defthm pbfr-list-depends-on-of-bfr-logand-ss
    (implies (and (not (pbfr-list-depends-on n p v1))
                  (not (pbfr-list-depends-on n p v2)))
             (not (pbfr-list-depends-on n p (bfr-logand-ss v1 v2))))
    :hints(("Goal" :in-theory (e/d (pbfr-list-depends-on bfr-logand-ss)
                                   ((pbfr-list-depends-on)
                                    (pbfr-depends-on)
                                    (:d bfr-logand-ss)))
            :induct (bfr-logand-ss v1 v2)
            :expand ((bfr-logand-ss v1 v2))))))

(defsection bfr-logior-ss
  (defthm bfr-logior-ss-correct
    (equal (bfr-list->s (bfr-logior-ss a b) env)
           (logior (bfr-list->s a env)
                   (bfr-list->s b env)))
    :hints(("Goal"
            :induct (scdr2-ind a b)
            :in-theory (e/d (acl2::logior**))
            :expand ((bfr-logior-ss a b)))))

  (defthm pbfr-list-depends-on-of-bfr-logior-ss
    (implies (and (not (pbfr-list-depends-on n p v1))
                  (not (pbfr-list-depends-on n p v2)))
             (not (pbfr-list-depends-on n p (bfr-logior-ss v1 v2))))
    :hints(("Goal" :in-theory (e/d (pbfr-list-depends-on bfr-logior-ss)
                                   ((pbfr-list-depends-on)
                                    (pbfr-depends-on)
                                    (:d bfr-logior-ss)))
            :induct (bfr-logior-ss v1 v2)
            :expand ((bfr-logior-ss v1 v2))))))


;; ------




;; (defthmd logtail-ns-0
;;   (equal (logtail-ns 0 n) n)
;;   :hints(("Goal" :in-theory (enable logtail-ns))))



;; (defthmd boolean-listp-bfr-+-ss-v2i-bind-env-car-env
;;   (implies (and (bind-free '((env . (car env))) (env))
;; ;                 (bfr-p c) (bfr-listp v1) (bfr-listp v2)
;;                 (boolean-listp (bfr-+-ss c v1 v2)))
;;            (equal (v2i (bfr-+-ss c v1 v2))
;;                   (+ (if (bfr-eval c env) 1 0)
;;                      (v2i (bfr-eval-list v1 env))
;;                      (v2i (bfr-eval-list v2 env)))))
;;   :hints (("goal" :use ((:instance bfr-eval-list-consts
;;                                    (x (bfr-+-ss c v1 v2)))
;;                         bfr-+-ss-correct)
;;            :in-theory (disable bfr-+-ss bfr-+-ss-correct
;;                                bfr-eval-list-consts))))


;; (defthmd boolean-listp-bfr-*-ss-v2i-bind-env-car-env
;;   (implies (and (bind-free '((env . (car env))) (env))
;;                 (boolean-listp (bfr-*-ss v1 v2)))
;;            (equal (v2i (bfr-*-ss v1 v2))
;;                   (* (v2i (bfr-eval-list v1 env))
;;                      (v2i (bfr-eval-list v2 env)))))
;;   :hints (("goal" :use ((:instance bfr-eval-list-consts
;;                                    (x (bfr-*-ss v1 v2)))
;;                         bfr-*-ss-correct)
;;            :in-theory (disable bfr-*-ss bfr-*-ss-correct
;;                                bfr-eval-list-consts))))








;; ---------------- bfr-floor-mod-ss ---------------------

(defsection bfr-floor-mod-ss

  (local (include-book "ihs/quotient-remainder-lemmas" :dir :system)) ;

  (local
   (encapsulate nil
     (local
      (progn
        (defthm floor-between-b-and-2b
          (implies (and (integerp a)
                        (integerp b)
                        (< 0 b)
                        (<= b a)
                        (< a (* 2 b)))
                   (equal (floor a b) 1))
          :hints(("Goal" :in-theory (disable floor acl2::floor-bounds
                                             acl2::<-*-/-left)
                  :use ((:instance acl2::floor-bounds
                         (x a) (y b))
                        (:theorem (implies (and (integerp a)
                                                (integerp b)
                                                (< 0 b)
                                                (< a (* 2 b)))
                                           (< (* a (/ b)) 2)))))
                 (and stable-under-simplificationp
                      '(:in-theory (disable floor)))))

        (defthm floor-less-than-b
          (implies (and (integerp a)
                        (integerp b)
                        (< 0 b)
                        (<= 0 a)
                        (< a b))
                   (equal (floor a b) 0))
          :hints(("Goal" :in-theory (disable floor acl2::floor-bounds
                                             acl2::<-*-/-left)
                  :use ((:instance acl2::floor-bounds
                         (x a) (y b))
                        (:theorem (implies (and (integerp a)
                                                (integerp b)
                                                (< 0 b)
                                                (< a b))
                                           (< (* a (/ b)) 1)))))
                 (and stable-under-simplificationp
                      '(:in-theory (disable floor)))))

        (defthm mod-between-b-and-2-b
          (implies (and (integerp a)
                        (integerp b)
                        (< 0 b)
                        (<= b a)
                        (< a (* 2 b)))
                   (equal (mod a b) (- a b)))
          :hints(("Goal" :in-theory (e/d (mod)
                                         (floor acl2::floor-bounds
                                                acl2::<-*-/-left))
                  :use ((:instance acl2::floor-bounds
                         (x a) (y b))
                        (:theorem (implies (and (integerp a)
                                                (integerp b)
                                                (< 0 b)
                                                (< a (* 2 b)))
                                           (< (* a (/ b)) 2)))))
                 (and stable-under-simplificationp
                      '(:in-theory (disable floor)))))

        (defthm mod-less-than-b
          (implies (and (integerp a)
                        (integerp b)
                        (< 0 b)
                        (<= 0 a)
                        (< a b))
                   (equal (mod a b) a))
          :hints(("Goal" :in-theory (disable floor acl2::floor-bounds
                                             acl2::<-*-/-left)
                  :use ((:instance acl2::floor-bounds
                         (x a) (y b))
                        (:theorem (implies (and (integerp a)
                                                (integerp b)
                                                (< 0 b)
                                                (< a (* 2 b)))
                                           (< (* a (/ b)) 2)))))
                 (and stable-under-simplificationp
                      '(:in-theory (disable floor)))))))


     ;; (defthm floor-rewrite-+-1-*-2-a
     ;;   (implies (and (integerp a) (integerp b)
     ;;                 (< 0 b))
     ;;            (equal (floor (+ 1 (* 2 a)) b)
     ;;                   (if (<= b (+ 1 (* 2 (mod a b))))
     ;;                       (+ 1 (* 2 (floor a b)))
     ;;                     (* 2 (floor a b)))))
     ;;   :hints(("Goal" :in-theory (disable floor))))

     ;; (defthm floor-rewrite-*-2-a
     ;;   (implies (and (integerp a) (integerp b)
     ;;                 (< 0 b))
     ;;            (equal (floor (* 2 a) b)
     ;;                   (if (<= b (* 2 (mod a b)))
     ;;                       (+ 1 (* 2 (floor a b)))
     ;;                     (* 2 (floor a b)))))
     ;;   :hints(("Goal" :in-theory (disable floor))))

     (defthm floor-rewrite-+-bit-*-2-a
       (implies (and (integerp a) (integerp b)
                     (< 0 b))
                (equal (floor (logcons c a) b)
                       (if (<= b (logcons c (mod a b)))
                           (logcons 1 (floor a b))
                         (logcons 0 (floor a b)))))
       :hints(("Goal" :in-theory (e/d (logcons bfix) (floor)))))

     ;; (defthm mod-rewrite-*-2-a
     ;;   (implies (and (integerp a) (integerp b)
     ;;                 (< 0 b))
     ;;            (equal (mod (* 2 a) b)
     ;;                   (if (<= b (* 2 (mod a b)))
     ;;                       (+ (* -1  b)
     ;;                          (* 2 (mod a b)))
     ;;                     (* 2 (mod a b)))))
     ;;   :hints (("goal" :in-theory (disable mod))))

     ;; (defthm mod-rewrite-+-1-*-2-a
     ;;   (implies (and (integerp a) (integerp b)
     ;;                 (< 0 b))
     ;;            (equal (mod (+ 1 (* 2 a)) b)
     ;;                   (if (<= b (+ 1 (* 2 (mod a b))))
     ;;                       (+ 1 (* -1  b)
     ;;                          (* 2 (mod a b)))
     ;;                     (+ 1 (* 2 (mod a b))))))
     ;;   :hints (("goal" :in-theory (e/d (mod) (floor)))))

     (defthm mod-rewrite-+-bit-*-2-a
       (implies (and (integerp a) (integerp b)
                     (< 0 b))
                (equal (mod (logcons c a) b)
                       (if (<= b (logcons c (mod a b)))
                           (+ (- b)
                              (logcons c (mod a b)))
                         (logcons c (mod a b)))))
       :hints (("goal" :in-theory (e/d (logcons bfix mod) (floor)))))



     ;; (in-theory (disable mod-between-b-and-2-b
     ;;                     mod-less-than-b
     ;;                     floor-between-b-and-2b
     ;;                     floor-less-than-b))

     (defthm denominator-of-unary-/
       (implies (and (integerp n) (< 0 n))
                (equal (denominator (/ n)) n))
       :hints (("goal" :use ((:instance rational-implies2
                              (x (/ n)))))))

     (defthm <-1-not-integer-recip
       (implies (and (integerp n)
                     (< 1 n))
                (not (integerp (/ n))))
       :hints (("goal"
                :use ((:instance denominator-of-unary-/))
                :in-theory (disable denominator-of-unary-/))))

     (defthm integer-and-integer-recip
       (implies (and (integerp n)
                     (< 0 n))
                (equal (integerp (/ n))
                       (equal n 1))))))

  (local (add-bfr-pat (bfr-<-ss . &)))

  (local (defthm +-1-logcons-0
           (equal (+ 1 (logcons 0 a))
                  (logcons 1 a))
           :hints(("Goal" :in-theory (enable logcons)))))

  (defthm bfr-floor-mod-ss-correct
    (b* (((mv floor mod) (bfr-floor-mod-ss a b bminus))
         (a (bfr-list->s a env))
         (b (bfr-list->s b env))
         (bminus (bfr-list->s bminus env)))
      (implies
       (and (< 0 b)
            (equal bminus (- b)))
       (and (equal (bfr-list->s floor env)
                   (floor a b))
            (equal (bfr-list->s mod env)
                   (mod a b)))))
    :hints (("goal" :induct (bfr-floor-mod-ss a b bminus)
             :in-theory (e/d* ((:i bfr-floor-mod-ss))
                              (floor mod
                                     bfr-eval-list
                                     equal-of-booleans-rewrite
                                     (:definition bfr-floor-mod-ss)
                                     acl2::mod-type
                                     acl2::floor-type-3 acl2::floor-type-1
                                     acl2::logcons-posp-1 acl2::logcons-posp-2
                                     acl2::logcons-negp
                                     acl2::rationalp-mod (:t floor) (:t mod)))
             :do-not-induct t
             :expand ((bfr-floor-mod-ss a b bminus)
                      (bfr-floor-mod-ss nil b bminus)))
            (bfr-reasoning)))

  (defthm pbfr-list-depends-on-of-bfr-floor-mod-ss
    (b* (((mv floor mod) (bfr-floor-mod-ss a b bminus)))
      (implies (and (not (pbfr-list-depends-on n p a))
                    (not (pbfr-list-depends-on n p b))
                    (not (pbfr-list-depends-on n p bminus)))
               (and (not (pbfr-list-depends-on n p floor))
                    (not (pbfr-list-depends-on n p mod)))))
    :hints(("Goal" :in-theory (enable bfr-floor-mod-ss pbfr-list-depends-on)))))

(defsection bfr-sign-abs-neg-s

  (local (in-theory (enable bfr-sign-abs-neg-s)))
  (local (add-bfr-pat (s-sign . &)))

  (defthm bfr-sign-abs-neg-s-correct
    (b* (((mv sign minus abs neg) (bfr-sign-abs-neg-s x))
         (x (bfr-list->s x env)))
      (and (equal (bfr-eval sign env)
                  (< x 0))
           (equal (bfr-list->s minus env)
                  (- x))
           (equal (bfr-list->s abs env)
                  (abs x))
           (equal (bfr-list->s neg env)
                  (- (abs x)))))
    :hints ((bfr-reasoning)))

  (defthm pbfr-list-depends-on-of-bfr-sign-abs-neg-s-rw
    (b* (((mv sign minus abs neg) (bfr-sign-abs-neg-s x)))
      (implies (not (pbfr-list-depends-on n p x))
               (and (not (pbfr-depends-on n p sign))
                    (not (pbfr-list-depends-on n p minus))
                    (not (pbfr-list-depends-on n p abs))
                    (not (pbfr-list-depends-on n p neg)))))))


(defsection bfr-floor-ss

  (local (add-bfr-pat (bfr-=-ss . &)))
  (local (add-bfr-pat (mv-nth 0 (bfr-sign-abs-neg-s . &))))

  (local (defthm floor-negative
           (equal (floor x (- y))
                  (floor (- x) y))
           :hints(("Goal" :in-theory (enable floor)))))

  (defthm bfr-floor-ss-correct
    (equal (bfr-list->s (bfr-floor-ss a b) env)
           (floor (bfr-list->s a env)
                  (bfr-list->s b env)))
    :hints (("goal" :do-not-induct t
             :in-theory (enable bfr-floor-ss))
            (bfr-reasoning)))

  (defthm pbfr-list-depends-on-of-bfr-floor-ss
      (implies (and (not (pbfr-list-depends-on n p a))
                    (not (pbfr-list-depends-on n p b)))
               (not (pbfr-list-depends-on n p (bfr-floor-ss a b))))
    :hints(("Goal" :in-theory (enable bfr-floor-ss
                                      pbfr-list-depends-on)))))

(defsection bfr-mod-ss

  (local (add-bfr-pat (bfr-=-ss . &)))
  (local (add-bfr-pat (mv-nth 0 (bfr-sign-abs-neg-s . &))))

  (local (defthm floor-negative
           (equal (floor x (- y))
                  (floor (- x) y))
           :hints(("Goal" :in-theory (enable floor)))))

  (local (defthm mod-negative
           (equal (mod x (- y))
                  (- (mod (- x) y)))
           :hints(("Goal" :in-theory (enable mod)))))

  (defthm bfr-mod-ss-correct
    (equal (bfr-list->s (bfr-mod-ss a b) env)
           (mod (bfr-list->s a env)
                  (bfr-list->s b env)))
    :hints (("goal" :do-not-induct t
             :in-theory (enable bfr-mod-ss))
            (bfr-reasoning)))

  (defthm pbfr-list-depends-on-of-bfr-mod-ss
      (implies (and (not (pbfr-list-depends-on n p a))
                    (not (pbfr-list-depends-on n p b)))
               (not (pbfr-list-depends-on n p (bfr-mod-ss a b))))
    :hints(("Goal" :in-theory (enable bfr-mod-ss
                                      pbfr-list-depends-on)))))

(defsection bfr-truncate-ss

  (local (add-bfr-pat (bfr-=-ss . &)))
  (local (add-bfr-pat (mv-nth 0 (bfr-sign-abs-neg-s . &))))

  (local
   (defthm truncate-is-floor
     (implies (and (integerp a) (integerp b)
                   (not (equal b 0)))
              (equal (truncate a b)
                     (if (acl2::xor (< a 0) (< b 0))
                         (- (floor (abs a) (abs b)))
                       (floor (abs a) (abs b)))))
     :hints(("Goal" :in-theory (enable truncate floor)))))


  (local (defthm truncate-0
           (equal (truncate x 0) 0)
           :hints(("Goal" :in-theory (enable truncate)))))

  (local (in-theory (disable truncate)))


  (defthm bfr-truncate-ss-correct
    (equal (bfr-list->s (bfr-truncate-ss a b) env)
           (truncate (bfr-list->s a env)
                     (bfr-list->s b env)))
    :hints (("goal" :do-not-induct t
             :in-theory (enable bfr-truncate-ss))
            (bfr-reasoning))
    :otf-flg t)

  (defthm pbfr-list-depends-on-of-bfr-truncate-ss
      (implies (and (not (pbfr-list-depends-on n p a))
                    (not (pbfr-list-depends-on n p b)))
               (not (pbfr-list-depends-on n p (bfr-truncate-ss a b))))
    :hints(("Goal" :in-theory (enable bfr-truncate-ss
                                      pbfr-list-depends-on)))))

(defsection bfr-rem-ss

  (local (add-bfr-pat (bfr-=-ss . &)))
  (local (add-bfr-pat (mv-nth 0 (bfr-sign-abs-neg-s . &))))

  (local (defthm rem-0
           (equal (rem x 0) (fix x))))


  (local
   (defthm truncate-is-floor
     (implies (and (integerp a) (integerp b)
                   (not (equal b 0)))
              (equal (truncate a b)
                     (if (acl2::xor (< a 0) (< b 0))
                         (- (floor (abs a) (abs b)))
                       (floor (abs a) (abs b)))))
     :hints(("Goal" :in-theory (enable truncate floor)))))

  (local
   (defthm rem-is-mod
     (implies (and (integerp a) (integerp b)
                   (not (equal b 0)))
              (equal (rem a b)
                     (if (< a 0)
                         (- (mod (abs a) (abs b)))
                       (mod (abs a) (abs b)))))
     :hints(("Goal" :in-theory (e/d (rem mod) (floor truncate))))))

  (local (in-theory (disable rem)))

  (defthm bfr-rem-ss-correct
    (equal (bfr-list->s (bfr-rem-ss a b) env)
           (rem (bfr-list->s a env)
                  (bfr-list->s b env)))
    :hints (("goal" :do-not-induct t
             :in-theory (enable bfr-rem-ss))
            (bfr-reasoning)))

  (defthm pbfr-list-depends-on-of-bfr-rem-ss
      (implies (and (not (pbfr-list-depends-on n p a))
                    (not (pbfr-list-depends-on n p b)))
               (not (pbfr-list-depends-on n p (bfr-rem-ss a b))))
    :hints(("Goal" :in-theory (enable bfr-rem-ss
                                      pbfr-list-depends-on)))))
