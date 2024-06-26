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

(in-package "SET")

(include-book "domain")
(include-book "../osets/sets")
(include-book "../osets/extras")

;; Here we define a "set" version of rkeys.

(defun rkeys (r)
  (declare (type t r))
  (list::2set (acl2::rkeys r)))

(defthm setp-rkeys
  (setp (rkeys r)))

(defthm rkeys-of-s
  (equal (rkeys (acl2::s a v r))
         (if (null v) (delete a (rkeys r))
           (insert a (rkeys r)))))

(defthm rkeys-of-clr
  (equal (rkeys (acl2::clr a r))
         (delete a (rkeys r))))

;; Is this what we want?  Or should we stick with forward chaining, as
;; with (consp (rkeys ..)) ??

(defthm emptyp-rkeys-not-r
  (equal (emptyp (rkeys r))
         (not r))
  ;;:rule-classes (:forward-chaining)
  :hints (("Goal" :in-theory (e/d nil
                                  (EMPTYP-WHEN-SETP-MEANS-NIL)))))

(defthm rkeys-iff-r
  (iff (set::rkeys r) r)
  :hints (("Goal" :in-theory (e/d (set::rkeys) (set::2SET-REWRAP))
           :expand (list::2set (acl2::rkeys r)))))

(defthm not-memberp-r
  (implies
   (not (in a (rkeys r)))
   (equal (acl2::clr a r) r)))

(defthm memberp-g
  (implies
   (in a (rkeys r))
   (acl2::g a r))
  :rule-classes (:forward-chaining))

(defthm non-memberp-g
  (implies
   (not (in a (rkeys r)))
   (not (acl2::g a r)))
  :rule-classes (:forward-chaining))

(defthm wfr-implies-nil-not-in-rkeys
  (implies
   (acl2::wfr tr)
   (not (in nil (rkeys tr)))))

(in-theory (disable rkeys))

#|
;; This book provides a "domain" function for records called RKEYS along with
;; the key lemma about how calling S affects what RKEYS returns.  RKEYS
;; returns an oset.

(include-book "records")
(include-book "../osets/sets")
(local (include-book "../osets/map"))
(local (include-book "../osets/extras"))

(defun key-set (r)
  (if (consp r)
      (set::insert (caar r)
                   (key-set (cdr r)))
    (set::emptyset)))

(defthm setp-key-set
  (set::setp (key-set r)))

(defund rkeys (r)
  (key-set (acl2->rcd r)))

(defthm setp-of-rkeys
  (set::setp (rkeys r))
  :hints (("Goal" :in-theory (enable rkeys))))

(defthm in-key-set-s-aux-better
  (implies (not (ifrp r))  ;(wfr r)
           (equal (set::in a (key-set (s-aux p v r)))
                  (if v (or (equal a p)
                            (set::in a (key-set r)))
                    (and (not (equal a p))
                         (set::in a (key-set r))))))
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
             (NOT (SET::IN A (KEY-SET R))))))

 (local
  (defthm j1
    (IMPLIES (AND (NOT (IFRP R))
                  V (CONSP (S-AUX A V R))
                  (NOT (CDR (S-AUX A V R)))
                  (CONSP (CAR (S-AUX A V R)))
                  (NOT (CAAR (S-AUX A V R)))
                  (IFRP (CDAR (S-AUX A V R)))
                  A)
             (SET::IN NIL (KEY-SET R)))))

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
             (NOT (SET::IN SET::ARBITRARY-ELEMENT (KEY-SET R))))))

 (local
  (defthm j4
    (IMPLIES (AND (NOT (IFRP R))
                  (CONSP (S-AUX A NIL R))
                  (NOT (CDR (S-AUX A NIL R)))
                  (CONSP (CAR (S-AUX A NIL R)))
                  (NOT (CAAR (S-AUX A NIL R)))
                  (IFRP (CDAR (S-AUX A NIL R))))
             (SET::IN NIL (KEY-SET R)))))

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
             (NOT (SET::IN SET::ARBITRARY-ELEMENT (KEY-SET R))))))

 ;; This used to have hyps, but no longer!  -EWS
 (defthm rkeys-s
   (equal (rkeys (s a v r))
          (if v
              (set::insert a (rkeys r))
            (set::delete a (rkeys r))))
   :otf-flg t
   :hints (("goal" :do-not-induct t
            :do-not '(generalize eliminate-destructors)
            :in-theory (e/d (s ACL2->RCD rkeys
                               RCD->ACL2) ( ;SET::PICK-A-POINT-SUBSET-STRATEGY
                                           SET::SUBSET-OF-DELETE
                               ))))))

(defthm rkeys-of-clr
  (equal (rkeys (clr key r))
         (set::delete key (rkeys r)))
  :hints (("Goal" :in-theory (e/d (clr) (S==R)))))

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

(defthm emptyp-of-rkeys
  (equal (set::emptyp (rkeys r))
         (equal r nil))
  :hints (("Goal" :in-theory (enable rkeys acl2->rcd))))

(defthm rkeys-when-not-consp
  (implies (not (consp r))
           (equal (RKEYS R)
                  (if (equal r nil)
                      nil
                    (list nil))))
  :hints (("Goal" :in-theory (enable rkeys ACL2->RCD))))
|#