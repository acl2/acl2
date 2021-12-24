; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

(in-package "ACL2")

(local (include-book "arithmetic"))
(include-book "ihs/ihs-definitions" :dir :system)
(include-book "ihs/ihs-lemmas" :dir :system)

(in-theory (disable
            LOGNOT
            LOGCOUNT
            LOGBITP
            TRUE-LIST-LISTP
            SIGNED-BYTE-P
            UNSIGNED-BYTE-P
            INTEGER-LENGTH
            BINARY-LOGAND
            LOGNAND
            BINARY-LOGIOR
            LOGORC1
            LOGORC2
            LOGANDC1
            LOGANDC2
            BINARY-LOGEQV
            BINARY-LOGXOR
            LOGNOR
            BITP
            logcar
            LOGCDR
            LOGCONS
            LOGBIT
            LOGMASK
            LOGMASKP
            LOGHEAD
            LOGTAIL
            LOGAPP
            LOGRPL
            LOGEXT
            LOGREV1
            LOGREV
            LOGSAT
            LOGEXTU
            LOGNOTU
            ASHU
            BSPP
            ))

;; induction schemes

(defun add1-add1-logcdr-induction (x y z)
  (declare (xargs :measure (abs (ifix x))
                  :hints (("goal" :in-theory (enable ifix)))))
  (if (<= 0 (ifix x))
      (or y z)
    (add1-add1-logcdr-induction (1+ x) (1+ y) (logcdr z))))

(defun add1-add1-induction (x y)
  (declare (xargs :measure (abs (ifix x))
                  :hints (("goal" :in-theory (enable ifix)))))
  (if (<= 0 (ifix x))
      y
    (add1-add1-induction (1+ x) (1+ y))))


(defun add1-logcdr-logcdr-induction (m x y)
  (declare (xargs :measure (abs (ifix m))
                  :hints (("goal" :in-theory (enable ifix)))))
  (if (<= 0 (ifix m))
      (or x y)
    (add1-logcdr-logcdr-induction (1+ m) (logcdr x) (logcdr y))))


(defun logcdr-induction (x)
  (if (or (equal x -1) (zip x))
      t
    (logcdr-induction (logcdr x))))


(defun sub1-induction (x)
  (if (zp x)
      x
    (sub1-induction (1- x))))


(defun add1-sub1-induction (a b)
  (declare (xargs :measure (abs (ifix a))
                  :hints (("goal" :in-theory (enable ifix)))))
  (if (<= 0 (ifix a))
      b
    (add1-sub1-induction (1+ a) (1- b))))


(defun add1-induction (x)
  (declare (xargs :measure (abs (ifix x))
                  :hints (("goal" :in-theory (enable ifix)))))
  (if (<= 0 (ifix x))
      x
    (add1-induction (1+ x))))


(defun sub1-logcdr-logcdr-induction (m x y)
  (if (zp m)
      (or x y)
    (sub1-logcdr-logcdr-induction (1- m) (logcdr x) (logcdr y))))


(defun logcdr-logcdr-logcdr-induction (a b c)
  (declare (xargs :measure (abs (ifix a))
                  :hints (("goal" :in-theory (enable logcdr)))))
  (if (or (equal a -1) (zip a))
      (or b c)
    (logcdr-logcdr-logcdr-induction (logcdr a) (logcdr b) (logcdr c))))


(defun add1-logcdr-induction (m x)
  (declare (xargs :measure (abs (ifix m))
                  :hints (("goal" :in-theory (enable ifix)))))
  (if (<= 0 (ifix m))
      x
    (add1-logcdr-induction (1+ m) (logcdr x))))


(defun logcdr-logcdr-induction (b c)
  (declare (xargs :measure (abs (ifix b))
                  :hints (("goal" :in-theory (enable logcdr)))))
  (if (or (equal b -1) (zip b))
      c
    (logcdr-logcdr-induction (logcdr b) (logcdr c))))


(defun sub1-logcdr-induction (m x)
  (if (zp m)
      x
    (sub1-logcdr-induction (1- m) (logcdr x))))


(defun sub1-sub1-induction (m n)
  (if (zp m)
      n
    (sub1-sub1-induction (1- m) (1- n))))


(defun sub1-sub1-logcdr-induction (a b v)
  (if (zp b)
      (or a v)
    (sub1-sub1-logcdr-induction (1- a) (1- b) (logcdr v))))

(defun sub1-sub1-logcdr-logcdr-induction (a b x v)
  (if (zp b)
      (or a v x)
    (sub1-sub1-logcdr-logcdr-induction (1- a) (1- b) (logcdr x) (logcdr v))))


(defun add1-sub1-logcdr-induction (a b v)
  (if (zp b)
      (or a v)
    (add1-sub1-logcdr-induction (1+ a) (1- b) (logcdr v))))

(defun sub1-logcdr-logcdr-carry-induction (m x y c)
  (if (zp m)
      (or x y c)
    (sub1-logcdr-logcdr-carry-induction
     (1- m)
     (logcdr x)
     (logcdr y)
     (b-ior (b-and (logcar x) (logcar y))
            (b-ior (b-and (logcar x) c)
                   (b-and (logcar y) c))))))

(defun sub1-logcdr-logcdr-logcdr-carry-induction (m x y z c)
  (if (zp m)
      (or x y c z)
    (sub1-logcdr-logcdr-logcdr-carry-induction
     (1- m)
     (logcdr x)
     (logcdr y)
     (logcdr z)
     (b-ior (b-and (logcar x) (logcar y))
            (b-ior (b-and (logcar x) c)
                   (b-and (logcar y) c))))))

(defun sub1-sub1-logcdr-logcdr-carry-induction (m n x y c)
  (if (or (zp m) (zp n))
      (or x y c)
    (sub1-sub1-logcdr-logcdr-carry-induction
     (1- m)
     (1- n)
     (logcdr x)
     (logcdr y)
     (b-ior (b-and (logcar x) (logcar y))
            (b-ior (b-and (logcar x) c)
                   (b-and (logcar y) c))))))

;; now let's try to get acl2 to automatically guess the right inductions to use:

(defund logendp (x)
  (declare (xargs :guard (integerp x)))
  (or (zip x)
      (= x -1)))

(defun b-maj (a b c)
  (declare (xargs :guard (and (bitp a)
                              (bitp b)
                              (bitp c))))
  (b-ior (b-and a b)
         (b-ior (b-and a c)
                (b-and b c))))

;; (if (or (and (equal a 1) (equal b 1))
;;           (and (equal a 1) (equal c 1))
;;           (and (equal b 1) (equal c 1)))
;;       1 0))

(defthm logcdr-logend-acl2-count
  (implies (not (logendp x))
           (< (acl2-count (logcdr x))
              (acl2-count x)))
  :hints (("goal" :in-theory (enable logcdr logendp
                                     )))
  :rule-classes :linear)

(local
 (defthm logcdr-logend-acl2-count-2
   (implies (or (zip x) (equal x -1))
            (equal (logcdr x)
                   (ifix x)))
   :hints (("goal" :in-theory (enable logcdr)))))

(defthm logcdr-logend-acl2-count-3
  (<= (acl2-count (logcdr x))
      (acl2-count x))
  :hints (("goal" :in-theory (enable logcdr)))
  :rule-classes :linear)

(defun +-r (a b c)
  (declare (xargs :measure (+ (acl2-count a) (acl2-count b))
                  :hints (("goal" :in-theory (disable acl2-count)))))
  (if (and (logendp a)
           (logendp b))
      c
    (+-r (logcdr a)
         (logcdr b)
         (b-maj (logcar a) (logcar b) c))))

(defthm +-induction t
  :rule-classes ((:induction :pattern (+ a b c)
                             :condition (unsigned-byte-p 1 c)
                             :scheme (+-r a b c))))

(defun lognotr (x)
  (declare (xargs :hints (("Goal" :in-theory (enable logendp)))))
  (or (logendp x)
      (lognotr (logcdr x))))

(defthm lognot-induction t
  :rule-classes ((:induction :pattern (lognot x)
                             :condition t
                             :scheme (lognotr x))))

(defun logbinr (x y)
  (declare (xargs :hints (("goal" :in-theory (disable acl2-count)))))
  (or (logendp x)
      (logendp y)
      (logbinr (logcdr x) (logcdr y))))

(defthm logand-induction t
  :rule-classes ((:induction :pattern (logand x y)
                             :condition t
                             :scheme (logbinr x y))))

(defthm logior-induction t
  :rule-classes ((:induction :pattern (logior x y)
                             :condition t
                             :scheme (logbinr x y))))

(defthm logxor-induction t
  :rule-classes ((:induction :pattern (logxor x y)
                             :condition t
                             :scheme (logbinr x y))))

(defun loglistr (n x)
  (if (zp n)
      (ifix x)
    (logcons 0 (loglistr (1- n) (logcdr x)))))

(defun loglist-fwd-r (n x)
  (cond ((zip n) (ifix x))
        ((< n 0) (loglist-fwd-r (1+ n) x))
        (t (logcons 0 (loglist-fwd-r (1- n) (logcdr x))))))

(defun loglist-bwd-r (n x)
  (cond ((zip n) (ifix x))
        ((< n 0) (loglist-bwd-r (1+ n) (logcdr x)))
        (t (logcons 0 (loglist-bwd-r (1- n) x)))))



(defthm logtail-induction t
  :rule-classes ((:induction :pattern (logtail n x)
                             :condition t
                             :scheme (loglistr n x))))

(defthm sbp-induction t
  :rule-classes ((:induction :pattern (signed-byte-p n x)
                             :condition t
                             :scheme (loglistr n x))))

(defthm ubp-induction t
  :rule-classes ((:induction :pattern (unsigned-byte-p n x)
                             :condition t
                             :scheme (loglistr n x))))

(defthm logbitp-induction t
  :rule-classes ((:induction :pattern (logbitp n x)
                             :condition t
                             :scheme (loglistr n x))))

(defthm logext-induction t
  :rule-classes ((:induction :pattern (logext n x)
                             :condition t
                             :scheme (loglistr n x))))

(defthm logapp-induction t
  :rule-classes ((:induction :pattern (logapp n x y)
                             :condition t
                             :scheme (loglistr n x))))

(defthm ash-induction t
  :rule-classes ((:induction :pattern (ash x n)
                             :condition t
                             :scheme (loglist-bwd-r n x))))

;; when we see (foo n (ash x m)) where foo is a function that recurses
;; using loglist-fwd-r, we use the following induction.

(defun loglist-ashr (m n x)
  (cond ((or (zip m) (zp n)) x)
        ((< m 0) (loglist-ashr (1+ m) n (logcdr x)))
        (t (loglist-ashr (1- m) (1- n) x))))

(defthm loglist-ash-induction t
  :rule-classes ((:induction :pattern (loglistr n (ash x m))
                             :condition t
                             :scheme (loglist-ashr m n x))))

;swap fwd and bwd if n is negated:

(defthm loglistr-- t
  :rule-classes ((:induction :pattern (loglistr (- n) x)
                             :condition t
                             :scheme (loglist-bwd-r n x))))

(defthm loglist-fwd-r-- t
  :rule-classes ((:induction :pattern (loglist-fwd-r (- n) x)
                             :condition t
                             :scheme (loglist-bwd-r n x))))

(defthm loglist-bwd-r-- t
  :rule-classes ((:induction :pattern (loglist-bwd-r (- n) x)
                             :condition t
                             :scheme (loglist-fwd-r n x))))

;and ignore the negation of x:

(defthm loglistr--2 t
  :rule-classes ((:induction :pattern (loglistr n (- x))
                             :condition t
                             :scheme (loglistr n x))))

(defthm loglist-fwd-r--2 t
  :rule-classes ((:induction :pattern (loglist-fwd-r n (- x))
                             :condition t
                             :scheme (loglist-fwd-r n x))))

(defthm loglist-bwd-r--2 t
  :rule-classes ((:induction :pattern (loglist-bwd-r n (- x))
                             :condition t
                             :scheme (loglist-bwd-r n x))))



;combining the induction schemes for + and the above loglist-fwd-r rules:

(defthm loglist-+-induction t
   :rule-classes ((:induction :pattern (loglistr n (+ x y c))
                              :condition t
                              :scheme (sub1-logcdr-logcdr-carry-induction n
                                                                          x
                                                                          y
                                                                          c))))

;same for lognot:

(defthm loglist-lognot-induction t
  :rule-classes ((:induction :pattern (loglistr n (lognot x))
                             :condition t
                             :scheme (loglistr n x))))

;now some rules combining specific loglist functions with loglist:

(defun loglist-loglistr (m n x)
  (if (or (zp m)
          (zp n))
      x
    (loglist-loglistr (1- m) (1- n) (logcdr x))))

(defthm loglist-loghead t
  :rule-classes ((:induction :pattern (loglistr n1 (loghead n2 x))
                             :condition t
                             :scheme (loglist-loglistr n2 n1 x))))

;; use loglistr instead?
;; (defun logappr (n x y)
;;   (if (zp n)
;;       y
;;     (logcons (logcar x) (logappr (1- n) (logcdr x) y))))


(defun logmaskpr (x)
  (declare (xargs :hints (("goal" :in-theory (disable acl2-count)))))

; Matt K. mod, withdrawn but explained here:
; The following commented-out change is necessary for LispWorks 8.0.  However,
; LispWorks has provided me a patch that presumably will be made publicly
; available, so we leave the original code as is, as a way of testing LispWorks
; in the future.
#|
; The LispWorks 8.0 compiler causes an error for the :logic version of this
; defun body, which up till now was the entire body.  This use of mbe fixes the
; problem.  Presumably the raw Lisp version of this function has never been
; called.

  (mbe :logic
       (if (logendp x)
           nil
         (logcons nil (logmaskpr (logcdr x))))
       :exec
       nil)
|#

  (if (logendp x)
      nil
    (logcons nil (logmaskpr (logcdr x)))))



(defthm logmaskp-induction t
  :rule-classes ((:induction :pattern (logmaskp x)
                             :condition t
                             :scheme (logmaskpr x))))
