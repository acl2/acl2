; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book supports schroeder-bernstein.lisp.  See comments there.

(in-package "ZF")

(include-book "std/util/defrule" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "projects/schroeder-bernstein/witness" :dir :system)
(include-book "injective-funp")
(include-book "zify")

(defmacro define (&rest x)
  (cons 'acl2::define x))

(defmacro defrule (&rest x)
  (cons 'acl2::defrule x))

(extend-zfc-table sbt-prop
                  zfc prod2$prop inverse$prop domain$prop)

(defun good-f-g (f g)

; Recognize injective functions f:A->B and g:B->A where A and B are the
; respective domains of f and g.  Only consider these when sbt-prop holds.

  (declare (xargs :guard t))
  (and (injective-funp f)
       (injective-funp g)
       (subset (image f) (domain g))
       (subset (image g) (domain f))
       (sbt-prop)))

; Replacements for the original (from projects/schroeder-bernstein/) generic
; functions.

(defun f-fn (f g x)
  (declare (xargs :guard t)
           (ignore g))
  (apply f x))
(defun g-fn (f g x)
  (declare (xargs :guard t)
           (ignore f))
  (apply g x))
(defun p-fn (f g x)
  (declare (xargs :guard t))
  (and (good-f-g f g)
       (in x (domain f))))
(defun q-fn (f g x)
  (declare (xargs :guard t))
  (and (good-f-g f g)
       (in x (domain g))))

(defmacro f (x)
  `(f-fn fun-f fun-g ,x))
(defmacro g (x)
  `(g-fn fun-f fun-g ,x))
(defmacro p (x)
  `(p-fn fun-f fun-g ,x))
(defmacro q (x)
  `(q-fn fun-f fun-g ,x))

(defthm q-of-f-when-p
  (implies (p x)
           (q (f x)))
  :hints (("Goal" :restrict ((subset-preserves-in-2
                              ((x (image fun-f))))))))

(defthm injectivity-of-f
  (implies (and (p x)
                (p y)
                (equal (f x) (f y)))
           (equal x y))
  :rule-classes nil)

(defthm injectivity-of-g
  (implies (and (q x)
                (q y)
                (equal (g x) (g y)))
           (equal x y))
  :rule-classes nil)

(defthm p-of-g-when-q
  (implies (q x)
           (p (g x)))
  :hints (("Goal" :restrict ((subset-preserves-in-2
                              ((x (image fun-g))))))))
; The following events were originally in an encapsulate in
; projects/schroeder-bernstein/ (although in the "SBT" package.  They are now
; redundant.
(progn

  (defrule zf::q-of-f-when-p
    (implies (zf::p x)
             (zf::q (zf::f x))))

  (defrule zf::injectivity-of-f
    (implies (and (zf::p x)
                  (zf::p y)
                  (equal (zf::f x) (zf::f y)))
             (equal x y))
    :rule-classes nil)

  (defrule zf::p-of-g-when-q
    (implies (zf::q x)
             (zf::p (zf::g x))))

  (defrule zf::injectivity-of-g
    (implies (and (zf::q x)
                  (zf::q y)
                  (equal (zf::g x) (zf::g y)))
             (equal x y))
    :rule-classes nil))

; In an earlier version I ran the following form to generate events, after
; evaluating (include-book "change-pkg").  But then I wanted to add arguments
; fun-f and fun-g, so I did that manually as shown below in lower case.
#|
(acl2::make-repkg-events
 #!sbt(is-g-inverse g-inverse
                    chain-elemp polarity in-g-imagep
                    is-f-inverse f-inverse in-f-imagep
                    val initialp chain-elem chain-step
                    chain-steps)
 "ZF")
|#

(PROGN (DEFUN IS-G-INVERSE (fun-f fun-g SBT::INV SBT::X)
         (AND (Q SBT::INV)
              (P SBT::X)
              (EQUAL (G SBT::INV) SBT::X)))
       (DEFCHOOSE G-INVERSE (SBT::INV)
                            (fun-f fun-g SBT::X)
         (IS-G-INVERSE fun-f fun-g SBT::INV SBT::X))
       (DEFUN CHAIN-ELEMP (fun-f fun-g SBT::X)
         (LET ((ACL2::__FUNCTION__ 'SBT::CHAIN-ELEMP))
           (DECLARE (IGNORABLE ACL2::__FUNCTION__))
           (AND (CONSP SBT::X)
                (BOOLEANP (CAR SBT::X))
                (IF (CAR SBT::X)
                    (AND (P (CDR SBT::X)) T)
                  (AND (Q (CDR SBT::X)) T)))))
       (DEFUN POLARITY (SBT::ELEM)
         (LET ((ACL2::__FUNCTION__ 'SBT::POLARITY))
           (DECLARE (IGNORABLE ACL2::__FUNCTION__))
           (AND (CAR SBT::ELEM) T)))
       (DEFUN IN-G-IMAGEP (fun-f fun-g SBT::X)
         (IS-G-INVERSE fun-f fun-g
                       (G-INVERSE fun-f fun-g SBT::X)
                       SBT::X))
       (DEFUN IS-F-INVERSE (fun-f fun-g SBT::INV SBT::X)
         (AND (P SBT::INV)
              (Q SBT::X)
              (EQUAL (F SBT::INV) SBT::X)))
       (DEFCHOOSE F-INVERSE (SBT::INV)
                            (fun-f fun-g SBT::X)
         (IS-F-INVERSE fun-f fun-g SBT::INV SBT::X))
       (DEFUN IN-F-IMAGEP (fun-f fun-g SBT::X)
         (IS-F-INVERSE fun-f fun-g
                       (F-INVERSE fun-f fun-g SBT::X)
                       SBT::X))
       (DEFUN VAL (SBT::ELEM)
         (LET ((ACL2::__FUNCTION__ 'SBT::VAL))
           (DECLARE (IGNORABLE ACL2::__FUNCTION__))
           (CDR SBT::ELEM)))
       (DEFUN INITIALP (fun-f fun-g SBT::ELEM)
         (LET ((ACL2::__FUNCTION__ 'SBT::INITIALP))
           (DECLARE (IGNORABLE ACL2::__FUNCTION__))
           (IF (POLARITY SBT::ELEM)
               (NOT (IN-G-IMAGEP fun-f fun-g (SBT::VAL SBT::ELEM)))
             (NOT (IN-F-IMAGEP fun-f fun-g (SBT::VAL SBT::ELEM))))))
       (DEFUN CHAIN-ELEM (SBT::POLARITY SBT::VAL)
         (LET ((ACL2::__FUNCTION__ 'SBT::CHAIN-ELEM))
           (DECLARE (IGNORABLE ACL2::__FUNCTION__))
           (CONS (AND SBT::POLARITY T) SBT::VAL)))
       (DEFUN CHAIN-STEP (fun-f fun-g SBT::ELEM)
         (LET ((ACL2::__FUNCTION__ 'SBT::CHAIN-STEP))
           (DECLARE (IGNORABLE ACL2::__FUNCTION__))
           (LET ((SBT::POLARITY (POLARITY SBT::ELEM)))
             (CHAIN-ELEM (NOT SBT::POLARITY)
                         (IF SBT::POLARITY (F (VAL SBT::ELEM))
                           (G (VAL SBT::ELEM)))))))
       (DEFUN CHAIN-STEPS (fun-f fun-g SBT::ELEM SBT::STEPS)
         (LET ((ACL2::__FUNCTION__ 'SBT::CHAIN-STEPS))
           (DECLARE (IGNORABLE ACL2::__FUNCTION__))
           (IF (ZP SBT::STEPS)
               SBT::ELEM
             (CHAIN-STEPS fun-f fun-g
                          (CHAIN-STEP fun-f fun-g SBT::ELEM)
                          (- SBT::STEPS 1))))))

; Introduce chain<= and chain<=-witness directly.

(defun-sk chain<= (fun-f fun-g sbt::x sbt::y)
  (declare (xargs :verify-guards nil))
  (declare (xargs :guard (consp sbt::x)))
  (declare (xargs :guard t))
  (exists (sbt::n)
          (equal (chain-steps fun-f fun-g sbt::x (nfix sbt::n)) sbt::y))
  :skolem-name chain<=-witness
  :thm-name chain<=-suff)

; Now finish up, again adding fun-f and fun-g manually as described above the
; earlier commented-out call of acl2::make-repkg-events.
#|
(acl2::make-repkg-events
 #!sbt(initial-wrt
       get-initial exists-initial in-q-stopper
       sb-witness is-sb-inverse sb-inverse
       in-sb-imagep)
 "ZF")
|#

(PROGN (DEFUN INITIAL-WRT (fun-f fun-g SBT::INITIAL SBT::ELEM)
         (LET ((ACL2::__FUNCTION__ 'SBT::INITIAL-WRT))
           (DECLARE (IGNORABLE ACL2::__FUNCTION__))
           (AND (CHAIN-ELEMP fun-f fun-g SBT::INITIAL)
                (INITIALP fun-f fun-g SBT::INITIAL)
                (CHAIN<= fun-f fun-g SBT::INITIAL SBT::ELEM))))
       (DEFCHOOSE GET-INITIAL (SBT::INITIAL)
                              (fun-f fun-g SBT::ELEM)
         (INITIAL-WRT fun-f fun-g SBT::INITIAL SBT::ELEM))
       (DEFUN EXISTS-INITIAL (fun-f fun-g SBT::ELEM)
         (LET ((ACL2::__FUNCTION__ 'SBT::EXISTS-INITIAL))
           (DECLARE (IGNORABLE ACL2::__FUNCTION__))
           (AND (CHAIN-ELEMP fun-f fun-g (GET-INITIAL fun-f fun-g SBT::ELEM))
                (INITIAL-WRT fun-f fun-g
                             (GET-INITIAL fun-f fun-g SBT::ELEM)
                             SBT::ELEM))))
       (DEFUN IN-Q-STOPPER (fun-f fun-g SBT::ELEM)
         (LET ((ACL2::__FUNCTION__ 'SBT::IN-Q-STOPPER))
           (DECLARE (IGNORABLE ACL2::__FUNCTION__))
           (AND (EXISTS-INITIAL fun-f fun-g SBT::ELEM)
                (NOT (POLARITY (GET-INITIAL fun-f fun-g SBT::ELEM))))))
       (DEFUN SB-WITNESS (fun-f fun-g SBT::X)
         (LET ((ACL2::__FUNCTION__ 'SBT::SB-WITNESS))
           (DECLARE (IGNORABLE ACL2::__FUNCTION__))
           (IF (IN-Q-STOPPER fun-f fun-g (CHAIN-ELEM T SBT::X))
               (G-INVERSE fun-f fun-g SBT::X)
             (F SBT::X))))
       (DEFUN IS-SB-INVERSE (fun-f fun-g SBT::INV SBT::X)
         (LET ((ACL2::__FUNCTION__ 'SBT::IS-SB-INVERSE))
           (DECLARE (IGNORABLE ACL2::__FUNCTION__))
           (AND (P SBT::INV)
                (Q SBT::X)
                (EQUAL (SB-WITNESS fun-f fun-g SBT::INV) SBT::X))))
       (DEFCHOOSE SB-INVERSE (SBT::INV)
                             (fun-f fun-g SBT::X)
         (IS-SB-INVERSE fun-f fun-g SBT::INV SBT::X))
       (DEFUN IN-SB-IMAGEP (fun-f fun-g SBT::X)
         (LET ((ACL2::__FUNCTION__ 'SBT::IN-SB-IMAGEP))
           (DECLARE (IGNORABLE ACL2::__FUNCTION__))
           (IS-SB-INVERSE fun-f fun-g
                          (SB-INVERSE fun-f fun-g SBT::X)
                          SBT::X))))

;;; From definverse
(defrule equal-of-f-and-f
  (implies (and (p sbt::x) (p sbt::y))
           (equal (equal (f sbt::x) (f sbt::y))
                  (equal sbt::x sbt::y)))
  :use ((:instance injectivity-of-f (x sbt::x) (y sbt::y))))

(in-theory (disable f-fn g-fn p-fn q-fn))

;;; For (defchoose f-inverse ...)
(defthm f-inverse-of-f-when-p
  (implies (p sbt::x)
           (equal (f-inverse fun-f fun-g (f sbt::x))
                  sbt::x))
  :hints
  (("Goal" :in-theory (enable is-f-inverse)
    :use ((:instance f-inverse (sbt::inv sbt::x)
                     (sbt::x (f sbt::x)))))))

;;; Analogous to equal-of-f-and-f
(defrule equal-of-g-and-g
  (implies (and (q sbt::x) (q sbt::y))
           (equal (equal (g sbt::x) (g sbt::y))
                  (equal sbt::x sbt::y)))
  :use ((:instance injectivity-of-g
                   (x sbt::x)
                   (y sbt::y))))

;;; For (defchoose g-inverse ...)
(defthm g-inverse-of-g-when-q
  (implies (q sbt::x)
           (equal (g-inverse fun-f fun-g (g sbt::x))
                  sbt::x))
  :hints
  (("Goal" :in-theory (enable is-g-inverse)
    :use ((:instance g-inverse
                     (sbt::inv sbt::x)
                     (sbt::x (g sbt::x)))
          (:instance zf::injectivity-of-g
                     (sbt::x (zf::g-inverse fun-f fun-g (zf::g sbt::x)))
                     (sbt::y sbt::x))))))

; Next I deal with goals generated by proof of q-of-sb-witness-when-p using the
; minimal-theory.

(defthm q-of-sb-witness-when-p-24.2
  (implies (in-q-stopper fun-f fun-g (chain-elem t sbt::x))
           (equal (sb-witness fun-f fun-g sbt::x)
                  (g-inverse fun-f fun-g sbt::x))))

(defthm q-of-sb-witness-when-p-24.1
  (implies (not (in-q-stopper fun-f fun-g (chain-elem t sbt::x)))
           (equal (sb-witness fun-f fun-g sbt::x) (f sbt::x))))

(defthm q-of-sb-witness-when-p-23
  (implies (and (q sbt::x)
                (q sbt::y)
                (equal (g sbt::x) (g sbt::y)))
           (equal (equal sbt::x sbt::y)
                  t)))

(defthm q-of-sb-witness-when-p-22
  (implies (q sbt::x) (p (g sbt::x))))

(defthm q-of-sb-witness-when-p-21
  (implies (and (p sbt::x)
                (p sbt::y)
                (equal (f sbt::x) (f sbt::y)))
           (equal (equal sbt::x sbt::y)
                  t)))

(defthm q-of-sb-witness-when-p-20
  (implies (p sbt::x) (q (f sbt::x))))

(defthm q-of-sb-witness-when-p-19
  (implies (is-g-inverse fun-f fun-g sbt::inv sbt::x)
           (is-g-inverse fun-f fun-g
                         (g-inverse fun-f fun-g sbt::x)
                         sbt::x)))

(defthm q-of-sb-witness-when-p-18.3prime
  (implies (not (q sbt::inv))
           (not (is-g-inverse fun-f fun-g sbt::inv sbt::x))))

(defthm q-of-sb-witness-when-p-18.2.2prime
  (implies (and (q sbt::inv) (p (g sbt::inv)))
           (equal (is-g-inverse fun-f fun-g sbt::inv (g sbt::inv))
                  t)))

(defthm q-of-sb-witness-when-p-18.2.1
  (implies (and (q sbt::inv)
                (p sbt::x)
                (not (equal (g sbt::inv) sbt::x)))
           (not (is-g-inverse fun-f fun-g sbt::inv sbt::x))))

(defthm q-of-sb-witness-when-p-18.1prime
  (implies (not (p sbt::x))
           (not (is-g-inverse fun-f fun-g sbt::inv sbt::x))))

(defthm q-of-sb-witness-when-p-17.2
  (implies sbt::polarity
           (equal (chain-elem sbt::polarity sbt::val)
                  (cons t sbt::val))))

(defthm q-of-sb-witness-when-p-17.1prime
  (equal (chain-elem nil sbt::val)
         (cons nil sbt::val)))

(defthm q-of-sb-witness-when-p-16.3prime
  (implies (not (exists-initial fun-f fun-g sbt::elem))
           (not (in-q-stopper fun-f fun-g sbt::elem))))

(defthm q-of-sb-witness-when-p-16.2
  (implies (and (exists-initial fun-f fun-g sbt::elem)
                (not (polarity (get-initial fun-f fun-g sbt::elem))))
           (equal (in-q-stopper fun-f fun-g sbt::elem) t)))

(defthm q-of-sb-witness-when-p-16.1prime
  (implies (polarity (get-initial fun-f fun-g sbt::elem))
           (not (in-q-stopper fun-f fun-g sbt::elem))))

(defthm q-of-sb-witness-when-p-15
  (implies (initial-wrt fun-f fun-g sbt::initial sbt::elem)
           (initial-wrt fun-f fun-g
                        (get-initial fun-f fun-g sbt::elem)
                        sbt::elem))
  :hints (("Goal" :use get-initial)))

(defthm q-of-sb-witness-when-p-14.3prime
  (implies (not (chain-elemp fun-f fun-g sbt::initial))
           (not (initial-wrt fun-f fun-g sbt::initial sbt::elem))))

(defthm q-of-sb-witness-when-p-14.2
  (implies (and (chain-elemp fun-f fun-g sbt::initial)
                (initialp fun-f fun-g sbt::initial))
           (equal (initial-wrt fun-f fun-g sbt::initial sbt::elem)
                  (chain<= fun-f fun-g sbt::initial sbt::elem))))

(defthm q-of-sb-witness-when-p-14.1prime
  (implies (not (initialp fun-f fun-g sbt::initial))
           (not (initial-wrt fun-f fun-g sbt::initial sbt::elem))))

(defthm q-of-sb-witness-when-p-12.6prime
  (implies (not (integerp (chain<=-witness fun-f fun-g
                                           sbt::x
                                           (chain-steps fun-f fun-g
                                                        sbt::x 0))))
           (equal (chain<= fun-f fun-g
                           sbt::x
                           (chain-steps fun-f fun-g sbt::x 0))
                  t)))

(defthm q-of-sb-witness-when-p-12.5
  (implies (and (not (integerp (chain<=-witness fun-f fun-g sbt::x sbt::y)))
                (not (equal (chain-steps fun-f fun-g sbt::x 0) sbt::y)))
           (not (chain<= fun-f fun-g sbt::x sbt::y))))

(defthm q-of-sb-witness-when-p-12.4
  (implies (and (integerp (chain<=-witness fun-f fun-g sbt::x sbt::y))
                (<= 0 (chain<=-witness fun-f fun-g sbt::x sbt::y))
                (equal (chain-steps fun-f fun-g
                                    sbt::x
                                    (chain<=-witness fun-f fun-g sbt::x sbt::y))
                       sbt::y))
           (equal (chain<= fun-f fun-g sbt::x sbt::y) t)))

(defthm q-of-sb-witness-when-p-12.3
  (implies
   (and (integerp (chain<=-witness fun-f fun-g sbt::x sbt::y))
        (<= 0 (chain<=-witness fun-f fun-g sbt::x sbt::y))
        (not (equal (chain-steps fun-f fun-g
                                 sbt::x
                                 (chain<=-witness fun-f fun-g sbt::x sbt::y))
                    sbt::y)))
   (not (chain<= fun-f fun-g sbt::x sbt::y))))

(defthm q-of-sb-witness-when-p-12.2prime
  (implies (< (chain<=-witness fun-f fun-g
                               sbt::x
                               (chain-steps fun-f fun-g sbt::x 0))
              0)
           (equal (chain<= fun-f fun-g
                           sbt::x
                           (chain-steps fun-f fun-g sbt::x 0))
                  t)))

(defthm q-of-sb-witness-when-p-12.1
  (implies (and (< (chain<=-witness fun-f fun-g sbt::x sbt::y) 0)
                (not (equal (chain-steps fun-f fun-g sbt::x 0) sbt::y)))
           (not (chain<= fun-f fun-g sbt::x sbt::y))))

(defthm q-of-sb-witness-when-p-11.2
  (implies (zp sbt::steps)
           (equal (chain-steps fun-f fun-g sbt::elem sbt::steps)
                  sbt::elem)))

(defthm q-of-sb-witness-when-p-11.1
  (implies (not (zp sbt::steps))
           (equal (chain-steps fun-f fun-g sbt::elem sbt::steps)
                  (chain-steps fun-f fun-g
                               (chain-step fun-f fun-g sbt::elem)
                               (+ -1 sbt::steps)))))

(defthm q-of-sb-witness-when-p-10.2
  (implies (polarity sbt::elem)
           (equal (chain-step fun-f fun-g sbt::elem)
                  (chain-elem nil (f (val sbt::elem))))))

(defthm q-of-sb-witness-when-p-10.1
  (implies (not (polarity sbt::elem))
           (equal (chain-step fun-f fun-g sbt::elem)
                  (chain-elem t (g (val sbt::elem))))))

(defthm q-of-sb-witness-when-p-9.2
  (implies (car sbt::elem)
           (equal (polarity sbt::elem) t)))

(defthm q-of-sb-witness-when-p-9.1prime
  (implies (not (car sbt::elem))
           (not (polarity sbt::elem))))

(defthm q-of-sb-witness-when-p-8
  (equal (val sbt::elem) (cdr sbt::elem)))

(in-theory (enable sbt::val))

(defthm q-of-sb-witness-when-p-7.4prime
  (implies (and (polarity sbt::elem)
                (in-g-imagep fun-f fun-g (val sbt::elem)))
           (not (initialp fun-f fun-g sbt::elem))))

(defthm q-of-sb-witness-when-p-7.3
  (implies (and (polarity sbt::elem)
                (not (in-g-imagep fun-f fun-g (val sbt::elem))))
           (equal (initialp fun-f fun-g sbt::elem) t)))

(defthm q-of-sb-witness-when-p-7.2prime
  (implies (and (not (polarity sbt::elem))
                (in-f-imagep fun-f fun-g (val sbt::elem)))
           (not (initialp fun-f fun-g sbt::elem))))

(defthm q-of-sb-witness-when-p-7.1
  (implies (and (not (polarity sbt::elem))
                (not (in-f-imagep fun-f fun-g (val sbt::elem))))
           (equal (initialp fun-f fun-g sbt::elem) t)))

(defthm q-of-sb-witness-when-p-6
  (equal (in-f-imagep fun-f fun-g sbt::x)
         (is-f-inverse fun-f fun-g
                       (f-inverse fun-f fun-g sbt::x)
                       sbt::x)))

(defthm q-of-sb-witness-when-p-5
  (implies (is-f-inverse fun-f fun-g sbt::inv sbt::x)
           (is-f-inverse fun-f fun-g
                         (f-inverse fun-f fun-g sbt::x)
                         sbt::x)))

(defthm q-of-sb-witness-when-p-4.3prime
  (implies (not (p sbt::inv))
           (not (is-f-inverse fun-f fun-g sbt::inv sbt::x))))

(defthm q-of-sb-witness-when-p-4.2.2prime
  (implies (and (p sbt::inv) (q (f sbt::inv)))
           (equal (is-f-inverse fun-f fun-g sbt::inv (f sbt::inv))
                  t)))

(defthm q-of-sb-witness-when-p-4.2.1
  (implies (and (p sbt::inv)
                (q sbt::x)
                (not (equal (f sbt::inv) sbt::x)))
           (not (is-f-inverse fun-f fun-g sbt::inv sbt::x))))

(defthm q-of-sb-witness-when-p-4.1prime
  (implies (not (q sbt::x))
           (not (is-f-inverse fun-f fun-g sbt::inv sbt::x))))

(defthm q-of-sb-witness-when-p-3
  (equal (in-g-imagep fun-f fun-g sbt::x)
         (is-g-inverse fun-f fun-g
                       (g-inverse fun-f fun-g sbt::x)
                       sbt::x)))

(defthm q-of-sb-witness-when-p-2.6prime
  (implies (not (consp sbt::x))
           (not (chain-elemp fun-f fun-g sbt::x))))

(defthm q-of-sb-witness-when-p-2.5
  (implies (and (consp sbt::x)
                (booleanp (car sbt::x))
                (car sbt::x)
                (p (cdr sbt::x)))
           (equal (chain-elemp fun-f fun-g sbt::x) t)))

(defthm q-of-sb-witness-when-p-2.4prime
  (implies (and (consp sbt::x)
                (not (car sbt::x))
                (q (cdr sbt::x)))
           (equal (chain-elemp fun-f fun-g sbt::x) t)))

(defthm q-of-sb-witness-when-p-2.3prime
  (implies (not (booleanp (car sbt::x)))
           (not (chain-elemp fun-f fun-g sbt::x))))

(defthm q-of-sb-witness-when-p-2.2prime
  (implies (and (not (car sbt::x))
                (not (q (cdr sbt::x))))
           (not (chain-elemp fun-f fun-g sbt::x))))

(defthm q-of-sb-witness-when-p-2.1prime
  (implies (and (car sbt::x)
                (not (p (cdr sbt::x))))
           (not (chain-elemp fun-f fun-g sbt::x))))

(defthm q-of-sb-witness-when-p-1.2
  (implies (chain-elemp fun-f fun-g
                        (get-initial fun-f fun-g sbt::elem))
           (equal (exists-initial fun-f fun-g sbt::elem)
                  (initial-wrt fun-f fun-g
                               (get-initial fun-f fun-g sbt::elem)
                               sbt::elem))))

(defthm q-of-sb-witness-when-p-1.1prime
  (implies (not (chain-elemp fun-f fun-g
                             (get-initial fun-f fun-g sbt::elem)))
           (not (exists-initial fun-f fun-g sbt::elem))))

; I actually created the rules above when using (theory 'ground-zero) rather
; than (theory 'minimal-theory) below, but I don't think that matters for those
; rules.

; Now try q-of-sb-witness-when-p, having skipped q-of-sb-witness-when-p-13.3,
; q-of-sb-witness-when-p-13.2, and q-of-sb-witness-when-p-13.1.  We get two
; more goals.

(defthm q-of-sb-witness-when-p-new-11.2
  (implies (equal (chain-steps fun-f fun-g
                               sbt::x
                               (nfix (chain<=-witness fun-f fun-g
                                                      sbt::x sbt::y)))
                  sbt::y)
           (equal (chain<= fun-f fun-g sbt::x sbt::y) t)))

(defthm q-of-sb-witness-when-p-new-11.1
  (implies (not (equal (chain-steps fun-f fun-g
                                    sbt::x
                                    (nfix (chain<=-witness fun-f fun-g
                                                           sbt::x sbt::y)))
                       sbt::y))
           (not (chain<= fun-f fun-g sbt::x sbt::y))))

; Now return to skipped theorems q-of-sb-witness-when-p-13.3,
; q-of-sb-witness-when-p-13.2, and q-of-sb-witness-when-p-13.1.
; Here is Subgoal 12, seen with :pso.

(defthm q-of-sb-witness-when-p-12-lemma
  (implies (equal (chain-steps fun-f fun-g sbt::x (nfix sbt::n))
                  sbt::y)
           (chain<= fun-f fun-g sbt::x sbt::y))
  :hints (("Goal" :by chain<=-suff))
  :rule-classes nil)

(defthm q-of-sb-witness-when-p-12
  (chain<= fun-f fun-g
           sbt::x
           (chain-steps fun-f fun-g sbt::x (nfix sbt::n)))
  :hints (("Goal"
           :use
           ((:instance q-of-sb-witness-when-p-12-lemma
                       (sbt::y (chain-steps fun-f fun-g
                                            sbt::x (nfix sbt::n))))))))

; Here is how I originally generated the functional substitution below, though
; later I manually edited it to accommodate the addition of fun-f and fun-g.
#|
(let ((wrld (w state)))
  (loop$ for doublet in
         '((sbt::is-g-inverse is-g-inverse)
           (sbt::g-inverse g-inverse)
           (sbt::chain-elemp chain-elemp)
           (sbt::polarity polarity)
           (sbt::in-g-imagep in-g-imagep)
           (sbt::is-f-inverse is-f-inverse)
           (sbt::f-inverse f-inverse)
           (sbt::in-f-imagep in-f-imagep)
           (sbt::val val)
           (sbt::initialp initialp)
           (sbt::chain-elem chain-elem)
           (sbt::chain-step chain-step)
           (sbt::chain-steps chain-steps)
;          (sbt::chain<=-witness chain<=-witness)
           (sbt::chain<= chain<=)
           (sbt::initial-wrt initial-wrt)
           (sbt::get-initial get-initial)
           (sbt::exists-initial exists-initial)
           (sbt::in-q-stopper in-q-stopper)
           (sbt::sb-witness sb-witness)
           (sbt::is-sb-inverse is-sb-inverse)
           (sbt::sb-inverse sb-inverse)
           (sbt::in-sb-imagep in-sb-imagep))
         collect
         (let* ((old (car doublet))
                (new (cadr doublet))
                (formals (formals new wrld))
                (lambda-formals (set-difference-eq formals '(fun-f fun-g))))
           (list old (list 'lambda
                           lambda-formals
                           (cons new formals))))))
|#

; Main result 1
(defthm q-of-sb-witness-when-p
 (implies (p x)
          (q (sb-witness fun-f fun-g x)))
 :otf-flg t
 :hints (("Goal"
          :in-theory (union-theories
                      (theory 'minimal-theory)
                      '(q-of-sb-witness-when-p-24.2
                        q-of-sb-witness-when-p-24.1
                        q-of-sb-witness-when-p-23
                        q-of-sb-witness-when-p-22
                        q-of-sb-witness-when-p-21
                        q-of-sb-witness-when-p-20
                        q-of-sb-witness-when-p-19
                        q-of-sb-witness-when-p-18.3prime
                        q-of-sb-witness-when-p-18.2.2prime
                        q-of-sb-witness-when-p-18.2.1
                        q-of-sb-witness-when-p-18.1prime
                        q-of-sb-witness-when-p-17.2
                        q-of-sb-witness-when-p-17.1prime
                        q-of-sb-witness-when-p-16.3prime
                        q-of-sb-witness-when-p-16.2
                        q-of-sb-witness-when-p-16.1prime
                        q-of-sb-witness-when-p-15
                        q-of-sb-witness-when-p-14.3prime
                        q-of-sb-witness-when-p-14.2
                        q-of-sb-witness-when-p-14.1prime
                        q-of-sb-witness-when-p-12.6prime
                        q-of-sb-witness-when-p-12.5
                        q-of-sb-witness-when-p-12.4
                        q-of-sb-witness-when-p-12.3
                        q-of-sb-witness-when-p-12.2prime
                        q-of-sb-witness-when-p-12.1
                        q-of-sb-witness-when-p-11.2
                        q-of-sb-witness-when-p-11.1
                        q-of-sb-witness-when-p-10.2
                        q-of-sb-witness-when-p-10.1
                        q-of-sb-witness-when-p-9.2
                        q-of-sb-witness-when-p-9.1prime
                        q-of-sb-witness-when-p-8
                        q-of-sb-witness-when-p-7.4prime
                        q-of-sb-witness-when-p-7.3
                        q-of-sb-witness-when-p-7.2prime
                        q-of-sb-witness-when-p-7.1
                        q-of-sb-witness-when-p-6
                        q-of-sb-witness-when-p-5
                        q-of-sb-witness-when-p-4.3prime
                        q-of-sb-witness-when-p-4.2.2prime
                        q-of-sb-witness-when-p-4.2.1
                        q-of-sb-witness-when-p-4.1prime
                        q-of-sb-witness-when-p-3
                        q-of-sb-witness-when-p-2.6prime
                        q-of-sb-witness-when-p-2.5
                        q-of-sb-witness-when-p-2.4prime
                        q-of-sb-witness-when-p-2.3prime
                        q-of-sb-witness-when-p-2.2prime
                        q-of-sb-witness-when-p-2.1prime
                        q-of-sb-witness-when-p-1.2
                        q-of-sb-witness-when-p-1.1prime
                        q-of-sb-witness-when-p-new-11.2
                        q-of-sb-witness-when-p-new-11.1
                        q-of-sb-witness-when-p-12))
          :by (:functional-instance
               sbt::q-of-sb-witness-when-p
               (sbt::f (lambda (x) (f x)))
               (sbt::g (lambda (x) (g x)))
               (sbt::p (lambda (x) (p x)))
               (sbt::q (lambda (x) (q x)))
               (SBT::IS-G-INVERSE (LAMBDA (SBT::INV SBT::X)
                                          (IS-G-INVERSE FUN-F FUN-G SBT::INV SBT::X)))
               (SBT::G-INVERSE (LAMBDA (SBT::X)
                                       (G-INVERSE FUN-F FUN-G SBT::X)))
               (SBT::CHAIN-ELEMP (LAMBDA (SBT::X)
                                         (CHAIN-ELEMP FUN-F FUN-G SBT::X)))
               (SBT::POLARITY (LAMBDA (SBT::ELEM)
                                      (POLARITY SBT::ELEM)))
               (SBT::IN-G-IMAGEP (LAMBDA (SBT::X)
                                         (IN-G-IMAGEP FUN-F FUN-G SBT::X)))
               (SBT::IS-F-INVERSE (LAMBDA (SBT::INV SBT::X)
                                          (IS-F-INVERSE FUN-F FUN-G SBT::INV SBT::X)))
               (SBT::F-INVERSE (LAMBDA (SBT::X)
                                       (F-INVERSE FUN-F FUN-G SBT::X)))
               (SBT::IN-F-IMAGEP (LAMBDA (SBT::X)
                                         (IN-F-IMAGEP FUN-F FUN-G SBT::X)))
               (SBT::VAL (LAMBDA (SBT::ELEM) (VAL SBT::ELEM)))
               (SBT::INITIALP (LAMBDA (SBT::ELEM)
                                      (INITIALP FUN-F FUN-G SBT::ELEM)))
               (SBT::CHAIN-ELEM (LAMBDA (SBT::POLARITY SBT::VAL)
                                        (CHAIN-ELEM SBT::POLARITY SBT::VAL)))
               (SBT::CHAIN-STEP (LAMBDA (SBT::ELEM)
                                        (CHAIN-STEP FUN-F FUN-G SBT::ELEM)))
               (SBT::CHAIN-STEPS (LAMBDA (SBT::ELEM SBT::STEPS)
                                         (CHAIN-STEPS FUN-F FUN-G SBT::ELEM SBT::STEPS)))
               (SBT::CHAIN<=-WITNESS
                (LAMBDA (ACL2::X3 ACL2::X4)
                        (CHAIN<=-WITNESS fun-f fun-g ACL2::X3 ACL2::X4)))
               (SBT::CHAIN<= (LAMBDA (SBT::X SBT::Y)
                                     (CHAIN<= FUN-F FUN-G SBT::X SBT::Y)))
               (SBT::INITIAL-WRT (LAMBDA (SBT::INITIAL SBT::ELEM)
                                         (INITIAL-WRT FUN-F FUN-G SBT::INITIAL SBT::ELEM)))
               (SBT::GET-INITIAL (LAMBDA (SBT::ELEM)
                                         (GET-INITIAL FUN-F FUN-G SBT::ELEM)))
               (SBT::EXISTS-INITIAL (LAMBDA (SBT::ELEM)
                                            (EXISTS-INITIAL FUN-F FUN-G SBT::ELEM)))
               (SBT::IN-Q-STOPPER (LAMBDA (SBT::ELEM)
                                          (IN-Q-STOPPER FUN-F FUN-G SBT::ELEM)))
               (SBT::SB-WITNESS (LAMBDA (SBT::X)
                                        (SB-WITNESS FUN-F FUN-G SBT::X)))
               (SBT::IS-SB-INVERSE (LAMBDA (SBT::INV SBT::X)
                                           (IS-SB-INVERSE FUN-F FUN-G SBT::INV SBT::X)))
               (SBT::SB-INVERSE (LAMBDA (SBT::X)
                                        (SB-INVERSE FUN-F FUN-G SBT::X)))
               (SBT::IN-SB-IMAGEP (LAMBDA (SBT::X)
                                          (IN-SB-IMAGEP FUN-F FUN-G SBT::X)))))))

; Main result 2
(defthm injectivity-of-sb-witness
  (implies (and (p sbt::x)
                (p sbt::y)
                (equal (sb-witness fun-f fun-g sbt::x)
                       (sb-witness fun-f fun-g sbt::y)))
           (equal sbt::x sbt::y))
  :hints (("Goal"
           :by
           (:functional-instance
            sbt::injectivity-of-sb-witness
            (sbt::f (lambda (x) (f x)))
            (sbt::g (lambda (x) (g x)))
            (sbt::p (lambda (x) (p x)))
            (sbt::q (lambda (x) (q x)))
            (SBT::IS-G-INVERSE (LAMBDA (SBT::INV SBT::X)
                                       (IS-G-INVERSE FUN-F FUN-G SBT::INV SBT::X)))
            (SBT::G-INVERSE (LAMBDA (SBT::X)
                                    (G-INVERSE FUN-F FUN-G SBT::X)))
            (SBT::CHAIN-ELEMP (LAMBDA (SBT::X)
                                      (CHAIN-ELEMP FUN-F FUN-G SBT::X)))
            (SBT::POLARITY (LAMBDA (SBT::ELEM)
                                   (POLARITY SBT::ELEM)))
            (SBT::IN-G-IMAGEP (LAMBDA (SBT::X)
                                      (IN-G-IMAGEP FUN-F FUN-G SBT::X)))
            (SBT::IS-F-INVERSE (LAMBDA (SBT::INV SBT::X)
                                       (IS-F-INVERSE FUN-F FUN-G SBT::INV SBT::X)))
            (SBT::F-INVERSE (LAMBDA (SBT::X)
                                    (F-INVERSE FUN-F FUN-G SBT::X)))
            (SBT::IN-F-IMAGEP (LAMBDA (SBT::X)
                                      (IN-F-IMAGEP FUN-F FUN-G SBT::X)))
            (SBT::VAL (LAMBDA (SBT::ELEM) (VAL SBT::ELEM)))
            (SBT::INITIALP (LAMBDA (SBT::ELEM)
                                   (INITIALP FUN-F FUN-G SBT::ELEM)))
            (SBT::CHAIN-ELEM (LAMBDA (SBT::POLARITY SBT::VAL)
                                     (CHAIN-ELEM SBT::POLARITY SBT::VAL)))
            (SBT::CHAIN-STEP (LAMBDA (SBT::ELEM)
                                     (CHAIN-STEP FUN-F FUN-G SBT::ELEM)))
            (SBT::CHAIN-STEPS (LAMBDA (SBT::ELEM SBT::STEPS)
                                      (CHAIN-STEPS FUN-F FUN-G SBT::ELEM SBT::STEPS)))
            (SBT::CHAIN<=-WITNESS
             (LAMBDA (ACL2::X3 ACL2::X4)
                     (CHAIN<=-WITNESS fun-f fun-g ACL2::X3 ACL2::X4)))
            (SBT::CHAIN<= (LAMBDA (SBT::X SBT::Y)
                                  (CHAIN<= FUN-F FUN-G SBT::X SBT::Y)))
            (SBT::INITIAL-WRT (LAMBDA (SBT::INITIAL SBT::ELEM)
                                      (INITIAL-WRT FUN-F FUN-G SBT::INITIAL SBT::ELEM)))
            (SBT::GET-INITIAL (LAMBDA (SBT::ELEM)
                                      (GET-INITIAL FUN-F FUN-G SBT::ELEM)))
            (SBT::EXISTS-INITIAL (LAMBDA (SBT::ELEM)
                                         (EXISTS-INITIAL FUN-F FUN-G SBT::ELEM)))
            (SBT::IN-Q-STOPPER (LAMBDA (SBT::ELEM)
                                       (IN-Q-STOPPER FUN-F FUN-G SBT::ELEM)))
            (SBT::SB-WITNESS (LAMBDA (SBT::X)
                                     (SB-WITNESS FUN-F FUN-G SBT::X)))
            (SBT::IS-SB-INVERSE (LAMBDA (SBT::INV SBT::X)
                                        (IS-SB-INVERSE FUN-F FUN-G SBT::INV SBT::X)))
            (SBT::SB-INVERSE (LAMBDA (SBT::X)
                                     (SB-INVERSE FUN-F FUN-G SBT::X)))
            (SBT::IN-SB-IMAGEP (LAMBDA (SBT::X)
                                       (IN-SB-IMAGEP FUN-F FUN-G SBT::X))))))
  :rule-classes nil)

; Next I deal with goals generated by proof of surjectivity-of-sb-witness using
; the minimal-theory.

(defthm surjectivity-of-sb-witness-3
  (equal (in-sb-imagep fun-f fun-g sbt::x)
         (is-sb-inverse fun-f fun-g
                        (sb-inverse fun-f fun-g sbt::x)
                        sbt::x)))

(defthm surjectivity-of-sb-witness-2
  (implies (is-sb-inverse fun-f fun-g sbt::inv sbt::x)
           (is-sb-inverse fun-f fun-g
                          (sb-inverse fun-f fun-g sbt::x)
                          sbt::x))
  :hints (("Goal" :use sb-inverse)))

(defthm surjectivity-of-sb-witness-1.3prime
  (implies (not (p sbt::inv))
           (not (is-sb-inverse fun-f fun-g sbt::inv sbt::x))))

(defthm surjectivity-of-sb-witness-1.2.2prime
  (implies (and (p sbt::inv)
                (q (sb-witness fun-f fun-g sbt::inv)))
           (equal (is-sb-inverse fun-f fun-g
                                 sbt::inv
                                 (sb-witness fun-f fun-g sbt::inv))
                  t)))

(defthm surjectivity-of-sb-witness-1.2.1
  (implies (and (p sbt::inv)
                (q sbt::x)
                (not (equal (sb-witness fun-f fun-g sbt::inv) sbt::x)))
           (not (is-sb-inverse fun-f fun-g sbt::inv sbt::x))))

(defthm surjectivity-of-sb-witness-1.1prime
  (implies (not (q sbt::x))
           (not (is-sb-inverse fun-f fun-g sbt::inv sbt::x))))

; Main result 3
(defthm surjectivity-of-sb-witness
  (implies (q sbt::x)
           (in-sb-imagep fun-f fun-g sbt::x))
  :hints (("Goal"
           :in-theory (union-theories
                       (theory 'minimal-theory)
                       '(surjectivity-of-sb-witness-3
                         surjectivity-of-sb-witness-2
                         surjectivity-of-sb-witness-1.3prime
                         surjectivity-of-sb-witness-1.2.2prime
                         surjectivity-of-sb-witness-1.2.1
                         surjectivity-of-sb-witness-1.1prime))
           :by
           (:functional-instance
            sbt::surjectivity-of-sb-witness
            (sbt::f (lambda (x) (f x)))
            (sbt::g (lambda (x) (g x)))
            (sbt::p (lambda (x) (p x)))
            (sbt::q (lambda (x) (q x)))
            (SBT::IS-G-INVERSE (LAMBDA (SBT::INV SBT::X)
                                       (IS-G-INVERSE FUN-F FUN-G SBT::INV SBT::X)))
            (SBT::G-INVERSE (LAMBDA (SBT::X)
                                    (G-INVERSE FUN-F FUN-G SBT::X)))
            (SBT::CHAIN-ELEMP (LAMBDA (SBT::X)
                                      (CHAIN-ELEMP FUN-F FUN-G SBT::X)))
            (SBT::POLARITY (LAMBDA (SBT::ELEM)
                                   (POLARITY SBT::ELEM)))
            (SBT::IN-G-IMAGEP (LAMBDA (SBT::X)
                                      (IN-G-IMAGEP FUN-F FUN-G SBT::X)))
            (SBT::IS-F-INVERSE (LAMBDA (SBT::INV SBT::X)
                                       (IS-F-INVERSE FUN-F FUN-G SBT::INV SBT::X)))
            (SBT::F-INVERSE (LAMBDA (SBT::X)
                                    (F-INVERSE FUN-F FUN-G SBT::X)))
            (SBT::IN-F-IMAGEP (LAMBDA (SBT::X)
                                      (IN-F-IMAGEP FUN-F FUN-G SBT::X)))
            (SBT::VAL (LAMBDA (SBT::ELEM) (VAL SBT::ELEM)))
            (SBT::INITIALP (LAMBDA (SBT::ELEM)
                                   (INITIALP FUN-F FUN-G SBT::ELEM)))
            (SBT::CHAIN-ELEM (LAMBDA (SBT::POLARITY SBT::VAL)
                                     (CHAIN-ELEM SBT::POLARITY SBT::VAL)))
            (SBT::CHAIN-STEP (LAMBDA (SBT::ELEM)
                                     (CHAIN-STEP FUN-F FUN-G SBT::ELEM)))
            (SBT::CHAIN-STEPS (LAMBDA (SBT::ELEM SBT::STEPS)
                                      (CHAIN-STEPS FUN-F FUN-G SBT::ELEM SBT::STEPS)))
            (SBT::CHAIN<=-WITNESS
             (LAMBDA (ACL2::X3 ACL2::X4)
                     (CHAIN<=-WITNESS fun-f fun-g ACL2::X3 ACL2::X4)))
            (SBT::CHAIN<= (LAMBDA (SBT::X SBT::Y)
                                  (CHAIN<= FUN-F FUN-G SBT::X SBT::Y)))
            (SBT::INITIAL-WRT (LAMBDA (SBT::INITIAL SBT::ELEM)
                                      (INITIAL-WRT FUN-F FUN-G SBT::INITIAL SBT::ELEM)))
            (SBT::GET-INITIAL (LAMBDA (SBT::ELEM)
                                      (GET-INITIAL FUN-F FUN-G SBT::ELEM)))
            (SBT::EXISTS-INITIAL (LAMBDA (SBT::ELEM)
                                         (EXISTS-INITIAL FUN-F FUN-G SBT::ELEM)))
            (SBT::IN-Q-STOPPER (LAMBDA (SBT::ELEM)
                                       (IN-Q-STOPPER FUN-F FUN-G SBT::ELEM)))
            (SBT::SB-WITNESS (LAMBDA (SBT::X)
                                     (SB-WITNESS FUN-F FUN-G SBT::X)))
            (SBT::IS-SB-INVERSE (LAMBDA (SBT::INV SBT::X)
                                        (IS-SB-INVERSE FUN-F FUN-G SBT::INV SBT::X)))
            (SBT::SB-INVERSE (LAMBDA (SBT::X)
                                     (SB-INVERSE FUN-F FUN-G SBT::X)))
            (SBT::IN-SB-IMAGEP (LAMBDA (SBT::X)
                                       (IN-SB-IMAGEP FUN-F FUN-G SBT::X)))))))

(defthm surjectivity-of-sb-witness-alt
  (implies (q x)
           (let ((inv (sb-inverse fun-f fun-g x)))
             (and (p inv)
                  (equal (sb-witness fun-f fun-g inv) x))))
  :hints (("Goal" :use ((:instance surjectivity-of-sb-witness
                                   (sbt::x x))))))

; Convert to set-theoretic result.

(defthm zify-f-lemma
  (implies (and (good-f-g fun-f fun-g)
                (in x (domain fun-f)))
           (in (f x) (domain fun-g)))
  :hints (("Goal"
           :in-theory (enable f-fn g-fn p-fn q-fn)
           :use q-of-f-when-p)))

(defthm injectivity-of-sb-witness-alt
  (implies (and (p x)
                (p y)
                (equal (sb-witness fun-f fun-g x)
                       (sb-witness fun-f fun-g y)))
           (equal x y))
  :hints (("Goal" :by injectivity-of-sb-witness))
  :rule-classes nil)

(encapsulate
  (((my-sb-witness * * *) => *)
   ((my-sb-inverse * * *) => *))

; We put parameter x first to support the use of zify below.

  (local (defun my-sb-witness (x fun-f fun-g)
           (sb-witness fun-f fun-g x)))

  (local (defun my-sb-inverse (x fun-f fun-g)
           (sb-inverse fun-f fun-g x)))

  (defthm q-of-my-sb-witness-when-p
    (implies (p x)
             (q (my-sb-witness x fun-f fun-g)))
    :hints (("Goal"
             :in-theory (disable q-of-sb-witness-when-p)
             :use q-of-sb-witness-when-p)))

  (defthm injectivity-of-my-sb-witness
    (implies (and (p x)
                  (p y)
                  (equal (my-sb-witness x fun-f fun-g)
                         (my-sb-witness y fun-f fun-g)))
             (equal x y))
    :hints (("Goal" :use injectivity-of-sb-witness-alt))
    :rule-classes nil)

  (defthm surjectivity-of-my-sb-witness-alt
    (implies (q x)
             (let ((inv (my-sb-inverse x fun-f fun-g)))
               (and (p inv)
                    (equal (my-sb-witness inv fun-f fun-g) x))))
    :hints (("Goal"
             :in-theory (disable surjectivity-of-sb-witness-alt)
             :use surjectivity-of-sb-witness-alt))))

(defthm good-f-g-forward
  (implies (good-f-g f g)
           (and (injective-funp f)
                (injective-funp g)
                (subset (image f) (domain g))
                (subset (image g) (domain f))
                (sbt-prop)))
  :rule-classes :forward-chaining)

(defthm my-sb-witness-maps-to-domain-fun-g
  (implies (and (good-f-g fun-f fun-g)
                (in x (domain fun-f)))
           (in (my-sb-witness x fun-f fun-g)
               (domain fun-g)))
  :hints (("Goal"
           :in-theory (e/d (f-fn g-fn p-fn q-fn) (q-of-my-sb-witness-when-p))
           :use q-of-my-sb-witness-when-p)))

(in-theory (disable good-f-g injective-funp))

(zify fun-bij (my-sb-witness x fun-f fun-g)
      :dom (if (good-f-g fun-f fun-g) (domain fun-f) 0)
      :ran (if (good-f-g fun-f fun-g) (domain fun-g) 0))

(defthmz schroeder-bernstein-main-1
  (implies (and (injective-funp f)
                (injective-funp g)
                (subset (image f) (domain g))
                (subset (image g) (domain f)))
           (funp (inverse (fun-bij f g))))
  :hints (("Goal"
           :in-theory (enable injective-funp good-f-g
                              p-fn q-fn)
           :expand ((funp (inverse (fun-bij f g))))
           :use
           ((:instance
             injectivity-of-my-sb-witness
             (x (cdr (mv-nth 0 (funp-witness (inverse (fun-bij f g))))))
             (y (cdr (mv-nth 1 (funp-witness (inverse (fun-bij f g))))))
             (fun-f f)
             (fun-g g)))))
  :props (sbt-prop fun-bij$prop))

(defthmz schroeder-bernstein-main-2-1
  (implies (and (injective-funp f)
                (injective-funp g)
                (subset (image f) (domain g))
                (subset (image g) (domain f)))
           (subset (image (fun-bij f g))
                   (domain g)))
  :hints (("Goal"
           :in-theory (e/d (image in-domain-rewrite)
                           (domain-inverse in-cons-apply))
           :expand ((subset (domain (inverse (fun-bij f g)))
                            (domain g)))))
  :props (sbt-prop fun-bij$prop))

(defthmz schroeder-bernstein-main-2-2-1
  (implies (and (injective-funp f)
                (injective-funp g)
                (subset (image f) (domain g))
                (subset (image g) (domain f))
                (in x (domain g)))
           (and (in (my-sb-inverse x f g)
                    (domain f))
                (equal (my-sb-witness (my-sb-inverse x f g) f g)
                       x)))
  :hints (("Goal"
           :use ((:instance surjectivity-of-my-sb-witness-alt
                            (fun-f f)
                            (fun-g g)))
           :in-theory (e/d (p-fn q-fn good-f-g)
                           (surjectivity-of-my-sb-witness-alt))))
  :props (sbt-prop fun-bij$prop))

(defthmz schroeder-bernstein-main-2-2-2
  (implies (and (injective-funp f)
                (injective-funp g)
                (subset (image f) (domain g))
                (subset (image g) (domain f))
                (in x (domain g)))
           (in (cons (my-sb-inverse x f g) x)
               (fun-bij f g)))
  :hints (("Goal" :in-theory (enable good-f-g)))
  :props (sbt-prop fun-bij$prop))


(defthmz schroeder-bernstein-main-2-2

; Here's a proof outline.  We want to show that if x \in (domain g) then x \in
; (image (fun-bij f g)).  Let inv = (my-sb-inverse x f g).  Then by
; surjectivity-of-my-sb-witness-alt, (in inv (domain f) and (my-sb-witness inv
; f g) = x.  Then by fun-bij$comprehension, since (good-f-g f g) holds by
; hypothesis, we have (cons inv x) \in (fun-bij f g).  So x \in (image
; (fun-bij f g)).

  (implies (and (injective-funp f)
                (injective-funp g)
                (subset (image f) (domain g))
                (subset (image g) (domain f)))
           (subset (domain g)
                   (image (fun-bij f g))))
  :hints (("Goal"
           :restrict
           ((in-image-suff
             ((p (cons (my-sb-inverse
                        (subset-witness (domain g)
                                        (image (fun-bij f g)))
                        f g)
                       (subset-witness (domain g)
                                       (image (fun-bij f g))))))))
           :expand ((subset (domain g)
                            (image (fun-bij f g))))))
  :props (sbt-prop fun-bij$prop))

(defthmz schroeder-bernstein-main-2
  (implies (and (injective-funp f)
                (injective-funp g)
                (subset (image f) (domain g))
                (subset (image g) (domain f)))
           (equal (image (fun-bij f g))
                  (domain g)))
  :hints (("Goal" :in-theory (enable extensionality-rewrite)))
  :props (sbt-prop fun-bij$prop))

(defthmz schroeder-bernstein-main
  (implies (and (injective-funp f)
                (injective-funp g)
                (subset (image f) (domain g))
                (subset (image g) (domain f)))
           (let ((bij (fun-bij f g)))
             (and (injective-funp bij)
                  (equal (domain bij) (domain f))
                  (equal (image bij) (domain g)))))
  :hints (("Goal" :in-theory (enable injective-funp good-f-g)))
  :props (sbt-prop fun-bij$prop))

(defun-sk exists-bijection (s1 s2)
  (exists fn
    (and (injective-funp fn)
         (equal (domain fn) s1)
         (equal (image fn) s2))))

(in-theory (disable exists-bijection
                    (:e injective-funp)))

(defthmz schroeder-bernstein
  (implies (and (injective-funp f)
                (injective-funp g)
                (equal s1 (domain f))
                (equal s2 (domain g))
                (subset (image f) s2)
                (subset (image g) s1))
           (exists-bijection s1 s2))
  :props (sbt-prop fun-bij$prop)
  :hints (("Goal" :restrict ((exists-bijection-suff
                              ((fn (fun-bij f g))))))))
