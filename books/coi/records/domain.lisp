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

;;
;; Here is an alternate view of record domains using list::sets
;;

(include-book "../alists/keyquiv")
(include-book "records")
(include-book "../bags/basic")

(local (in-theory (enable alist::keys)))

(defund rkeys (r)
  (declare (type t r))
  (alist::keys (acl2->rcd r)))

(encapsulate
    ()

  (local
   (defthm non-memberp
     (implies
      (and
       (RCDP r)
       (<< A (CAAR R)))
      (not (list::memberp a (alist::keys r))))
     :hints (("Goal" :in-theory (enable list::memberp)))))

  (local
   (defthm unique-keys
     (implies
      (rcdp r)
      (bag::unique (alist::keys r)))
     :hints (("Goal" :in-theory (enable bag::unique)))))


  (defthm unique-rkeys
    (bag::unique (rkeys r))
    :hints (("Goal" :in-theory (enable rkeys))))

  )

(defthm in-key-set-s-aux-better
  (implies (not (ifrp r))  ;(wfr r)
           (equal (list::memberp a (alist::keys (s-aux p v r)))
                  (if v (or (equal a p)
                            (list::memberp a (alist::keys r)))
                    (and (not (equal a p))
                         (list::memberp a (alist::keys r))))))
  :hints (("goal" :in-theory (e/d (wfkeyed wfr s-aux) ()))))



;bzo - improve this proof?
(encapsulate
 ()

 ;make non-local?
 (local
  (defthm not-ifrp-means-rcdp
    (implies (not (IFRP R))
             (rcdp r))))

 (local
  (defthm h1
    (IMPLIES (AND (rcdp R) (<< A (CAAR R)))
             (NOT (LIST::MEMBERP A (ALIST::KEYS R))))))

 (local
  (defthm j1
    (IMPLIES (AND (NOT (IFRP R))
                  V (CONSP (S-AUX A V R))
                  (NOT (CDR (S-AUX A V R)))
                  (CONSP (CAR (S-AUX A V R)))
                  (NOT (CAAR (S-AUX A V R)))
                  (IFRP (CDAR (S-AUX A V R)))
                  A)
             (LIST::MEMBERP NIL (ALIST::KEYS R)))))

 (local
  (defthm j2
    (IMPLIES (AND (NOT (IFRP R))
                  V (CONSP (S-AUX A V R))
                  (NOT (CDR (S-AUX A V R)))
                  (CONSP (CAR (S-AUX A V R)))
                  (NOT (CAAR (S-AUX A V R)))
                  a)
             (NOT (IFRP (CDAR (S-AUX A V R)))))))

 (local
  (defthm j3
    (IMPLIES (AND (NOT (IFRP R))
                  V (CONSP (S-AUX A V R))
                  (NOT (CDR (S-AUX A V R)))
                  (CONSP (CAR (S-AUX A V R)))
                  (NOT (CAAR (S-AUX A V R)))
                  (IFRP (CDAR (S-AUX A V R)))
                  SET::ARBITRARY-ELEMENT)
             (NOT (LIST::MEMBERP SET::ARBITRARY-ELEMENT (ALIST::KEYS R))))))

 (local
  (defthm j4
    (IMPLIES (AND (NOT (IFRP R))
                  (CONSP (S-AUX A NIL R))
                  (NOT (CDR (S-AUX A NIL R)))
                  (CONSP (CAR (S-AUX A NIL R)))
                  (NOT (CAAR (S-AUX A NIL R)))
                  (IFRP (CDAR (S-AUX A NIL R))))
             (LIST::MEMBERP NIL (ALIST::KEYS R)))))

 (local
  (defthm j5
    (IMPLIES (AND (NOT (IFRP R))
                  (CONSP (S-AUX NIL NIL R))
                  (NOT (CDR (S-AUX NIL NIL R)))
                  (CONSP (CAR (S-AUX NIL NIL R)))
                  (NOT (CAAR (S-AUX NIL NIL R))))
             (NOT (IFRP (CDAR (S-AUX NIL NIL R)))))))

 (local
  (defthm j6
    (IMPLIES (AND (NOT (IFRP R))
                  (CONSP (S-AUX A NIL R))
                  (NOT (CDR (S-AUX A NIL R)))
                  (CONSP (CAR (S-AUX A NIL R)))
                  (NOT (CAAR (S-AUX A NIL R)))
                  (IFRP (CDAR (S-AUX A NIL R)))
                  SET::ARBITRARY-ELEMENT
                  (NOT (EQUAL SET::ARBITRARY-ELEMENT A)))
             (NOT (LIST::MEMBERP SET::ARBITRARY-ELEMENT (ALIST::KEYS R))))))

 ;; This used to have hyps, but no longer!  -EWS
 (defthm rkeys-s
   (list::setequiv (rkeys (s a v r))
                   (if v
                       (cons a (rkeys r))
                     (list::remove a (rkeys r))))
   :otf-flg t
   :hints (("goal" :do-not-induct t
            :do-not '(generalize eliminate-destructors)
            :in-theory (e/d (s ACL2->RCD rkeys
                               RCD->ACL2) )))))

(defthm rkeys-of-clr
  (list::setequiv (rkeys (clr key r))
                  (list::remove key (rkeys r)))
  :hints (("Goal" :in-theory (e/d (clr) (S==R)))))

(encapsulate
    ()

  ;; DAG - should probably be moved to bags somewhere
  (local
   (defthm count-unique-is-memberp
     (implies
      (bag::unique list)
      (equal (bag::count a list)
             (if (list::memberp a list) 1 0)))
     :hints (("Goal" :in-theory (e/d (bag::unique bag::count list::memberp)
                                     (bag::count-of-cdr)))))
   )

  (local (include-book "../bags/pick-a-point"))

  ;; DAG - should probably be moved to bags somewhere
  (local
   (defthm count-remove
     (equal (bag::count a (remove b list))
            (if (equal a b) 0
              (bag::count a list))))
   )

  (defthm rkeys-of-clr-perm
    (bag::perm (rkeys (clr key r))
               (list::remove key (rkeys r)))
    :hints (("Goal" :in-theory (enable bag::perm-by-double-containment))))

  (defthm rkeys-s-perm
    (bag::perm (rkeys (s a v r))
               (if v
                   (cons a (remove a (rkeys r)))
                 (remove a (rkeys r))))
    :hints (("Goal" :in-theory (enable bag::perm-by-double-containment))))

  )

;bzo make a t-p rule?
(defthm rkeys-iff
  (iff (rkeys r)
       r)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable RKEYS ACL2->RCD))))

(defthm rkeys-non-nil-tp
  (implies r
           (rkeys r))
  :rule-classes (:type-prescription))

;do we need all of these?

(defthm rkeys-when-not-consp
  (implies (not (consp r))
           (equal (RKEYS R)
                  (if (equal r nil)
                      nil
                    (list nil))))
  :hints (("Goal" :in-theory (enable rkeys ACL2->RCD))))

(defthm not-memberp-g-aux
  (implies
   (not (list::memberp a (alist::keys alist)))
   (equal (g-aux a alist) nil)))

(defthm non-memberp-g
  (implies
   (not (list::memberp a (rkeys r)))
   (not (g a r)))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable rkeys g))))

(defthm memberp-g-aux
  (implies
   (and
    (rcdp alist)
    (list::memberp a (alist::keys alist)))
   (g-aux a alist)))

(defthm memberp-g
  (implies
   (list::memberp a (rkeys r))
   (g a r))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable rkeys g))))

(defthmd memberp-rkeys-reduction
  (iff (list::memberp a (rkeys r))
       (g a r)))

(defthm not-memberp-r
  (implies
   (not (list::memberp a (rkeys r)))
   (equal (clr a r) r))
  :hints (("Goal" :in-theory (e/d (clr memberp-rkeys-reduction) (s==r)))))

(defthm not-consp-rkeys-not-r
  (implies
   (not (consp (rkeys r)))
   (not r))
  :rule-classes (:forward-chaining))


(defthm wfkeyed-implies-not-nil-memberp
  (implies
   (wfkeyed tr)
   (not (list::memberp nil (alist::keys tr))))
  :hints (("Goal" :in-theory (enable wfkeyed alist::keys list::memberp))))

(defthm wfr-implies-not-nil-memberp
  (implies
   (wfr tr)
   (not (list::memberp nil (rkeys tr))))
  :hints (("Goal" :in-theory (enable rkeys wfr))))

;;
;; rkeyquiv
;;

(defun rkeysub (keys r1 r2)
  (if (consp keys)
      (let ((key (car keys)))
        (and (equal (g key r1) (g key r2))
             (rkeysub (remove (car keys) keys) (clr key r1) (clr key r2))))
    t))

(defthm rkeysub-id
  (rkeysub keys x x))

(defthmd rkeysub-implies-equal
  (implies
   (and
    (rkeysub rkeys r1 r2)
    (subsetp (rkeys r1) rkeys)
    (subsetp (rkeys r2) rkeys))
   (iff (equal r1 r2) t)))

(defthm memberp-rkeysub-implication
  (implies
   (and
    (list::memberp a keys)
    (rkeysub keys r1 r2))
   (equal (g a r1) (g a r2)))
  :rule-classes (:forward-chaining))

(defthm memberp-rkeysub-implication-2
  (implies
   (and
    (list::memberp a keys)
    (not (equal (g a r1) (g a r2))))
   (not (rkeysub keys r1 r2)))
  :rule-classes (:forward-chaining))


(defthm rkeysub-setequiv-implication
  (implies
   (and
    (rkeysub (rkeys x) x y)
    (rkeysub (rkeys y) x y))
   (list::setequiv (rkeys x) (rkeys y)))
  :rule-classes (:forward-chaining))

(defun rkeysub-equiv-induction (s1 s2 x y)
  (if (consp s1)
      (let ((key (car s1)))
        (if (list::memberp key s2)
            (if (equal (g key x) (g key y))
                (rkeysub-equiv-induction (remove key s1) (remove key s2) (clr key x) (clr key y))
              nil)
          nil))
    (list s1 s2 x y)))

(defthm open-rkeysub-on-memberp
  (implies
   (list::memberp key keys)
   (equal (rkeysub keys r1 r2)
          (and (equal (g key r1) (g key r2))
               (rkeysub (remove key keys) (clr key r1) (clr key r2)))))
  :hints (("Goal" :expand ((RKEYSUB KEYS R1 R2) (LIST::MEMBERP KEY KEYS)))))

(defcong list::setequiv equal (rkeysub set x y) 1
  :hints (("Goal" :expand (LIST::SETEQUIV SET SET-EQUIV)
           :induct (rkeysub-equiv-induction set set-equiv x y))))

(defun rkeyquiv (x y)
  (and
   (rkeysub (rkeys x) x y)
   (rkeysub (rkeys y) x y)))

(defthm rkeyquiv-id
  (rkeyquiv x x))

(defthm rkeyquiv-implication
  (implies
   (rkeyquiv x y)
   (equal x y))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (enable rkeysub-implies-equal))))

(in-theory (disable rkeyquiv))

(defequiv rkeyquiv)

(encapsulate
 ()

 (encapsulate
  (((rkeyquiv-hyps) => *)
   ((rkeyquiv-lhs) => *)
   ((rkeyquiv-rhs) => *)
   )

  (local (defun rkeyquiv-hyps () nil))
  (local (defun rkeyquiv-lhs  () nil))
  (local (defun rkeyquiv-rhs  () nil))

  (defthm rkeyquiv-multiplicity-constraint
    (implies
     (rkeyquiv-hyps)
     (equal (g arbitrary-element (rkeyquiv-lhs))
            (g arbitrary-element (rkeyquiv-rhs))))
    :rule-classes nil)
  )

 (local
  (encapsulate
      ()

    (defun bad-guy (keys r1 r2)
      (if (consp keys)
          (let ((key (car keys)))
            (if (equal (g key r1) (g key r2))
                (bad-guy (remove (car keys) keys) (clr key r1) (clr key r2))
              key))
        nil))

    (defthm rkeysub-implies-not-bad-guy
      (implies
       (rkeysub a x y)
       (not (bad-guy a x y)))
      :rule-classes (:forward-chaining :rewrite))

    (defthm not-rkeysub-implies-not-equal-g-bad-guy
      (implies
       (not (rkeysub a x y))
       (not (equal (g (bad-guy a x y) x)
                   (g (bad-guy a x y) y)))))

    (defun bad-guy2 (x y)
      (let ((a (bad-guy (rkeys x) x y)))
        (if (equal (g a x) (g a y))
            (bad-guy (rkeys y) x y)
          a)))

    (defthm not-rkeyquiv-implies-not-equal-g-bad-guy
      (implies
       (not (rkeyquiv x y))
       (not (equal (g (bad-guy2 x y) x)
                   (g (bad-guy2 x y) y))))
      :hints (("Goal" :in-theory (enable rkeyquiv))))

    (in-theory (disable bad-guy2))


    (defthm rkeyquiv-reduction
      (equal (rkeyquiv x y)
             (equal x y)))

    ))

 (defthm rkeyquiv-by-multiplicity-driver
   (implies
    (rkeyquiv-hyps)
    (rkeyquiv (rkeyquiv-lhs) (rkeyquiv-rhs)))
   :rule-classes nil
   :hints(("Goal"
           :use ((:instance
                  rkeyquiv-multiplicity-constraint
                  (arbitrary-element (bad-guy2 (rkeyquiv-lhs) (rkeyquiv-rhs))))))))

 (ADVISER::defadvice rkeyquiv-by-multiplicity
                     (implies (rkeyquiv-hyps)
                              (rkeyquiv (rkeyquiv-lhs) (rkeyquiv-rhs)))
                     :rule-classes (:pick-a-point :driver rkeyquiv-by-multiplicity-driver))
 )
