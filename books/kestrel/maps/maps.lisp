; Additions to the records library
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Clean this up

;FIXME move stuff into maps0?
;FIXME put in more support for fast execution - see books/defexec/other-apps/records/records.lisp - maybe base this book on that one

;maps are basically records with "domain" and "new address" operators

;; TODO: See also ../axe/maps2.lisp

;fixme some of these are set theorems?

(include-book "maps0")
(include-book "../sets/sets")

(defun key-set (r)
  (declare (xargs :guard (rcdp r)))
  (if (consp r)
      (set::insert (caar r)
		   (key-set (cdr r)))
    (set::emptyset)))

(defthm setp-key-set
  (set::setp (key-set r)))

(defun rkeys (r)
  (declare (type t r))
  (key-set (acl2->rcd r)))

(defthm true-list-p-of-rkeys
  (true-listp (rkeys r))
  :rule-classes :type-prescription)

(defthm in-key-set-s-aux
  (implies
   (wfr r)
   (equal (set::in a (key-set (s-aux p v r)))
	  (if v (or (equal a p)
		    (set::in a (key-set r)))
	    (and (not (equal a p))
		 (set::in a (key-set r))))))
  :hints (("goal" :in-theory (e/d (WFKEYED wfr s-aux) (set::in)))))

(defthm rkeys-s
  (implies (and (wfr r)
	;(wfkey a)
        )
   (equal (rkeys (s a v r))
	  (if v (set::insert a (rkeys r))
	    (set::delete a (rkeys r)))))
  :hints (("goal" :in-theory (enable s SET::DOUBLE-CONTAINMENT-EXPENSIVE))))

(in-theory (disable rkeys))

;; stuff that should be in the records book:
(defthm s-hack-1
  (equal (s a nil nil)
         nil)
  :hints (("Goal" :in-theory (enable s))))

(in-theory (enable g-of-s-redux))

;dup
(defthm acl2->rcd-does-nothing
  (implies (not (ifrp r))
           (equal (acl2->rcd r)
                  r))
  :hints (("Goal" :in-theory (enable acl2->rcd))))

;logically the same as g, but has a guard and should execute much faster
(defun fastg (a x)
  (declare (xargs :guard (not (IFRP X)))) ;fixme - should the guard be mapp?
  (mbe :logic (G-AUX A (ACL2->RCD X))
       :exec (G-AUX A X)))

(defthm fastg-becomes-g
  (equal (fastg a x)
         (g a x))
  :hints (("Goal" :in-theory (enable g fastg))))

(defun dom (s) (declare (type t s)) (rkeys s))

;disabling since this can introduce map reasoning into an unrelated problem
(defthmd wfr-hack1
  (IMPLIES (AND (not (ifrp r)) ;(WFR R)
                (CAAR R))
           (CDAR R))
  :hints (("Goal" :in-theory (enable WFR))))

(defthm wfr-hack2
  (IMPLIES (AND (CONSP R)
                (not (ifrp r)) ;(WFR R)
                ;A
                (<< A (CAAR R)))
           (NOT (G-AUX A (CDR R))))
  :hints (("Goal" :in-theory (enable wfr))))

(DEFUN WFR2 (R)
  (DECLARE (TYPE T R))
  (AND (rcdp r) (NOT (IFRP R)) (WFKEYED R)))

(defthm wfr-hack3
  (IMPLIES (AND (CONSP R)
                (WFR2 R)
                )
           (WFR2 (CDR R)))
  :hints (("Goal" :in-theory (enable wfr2 WFKEYED))))

(defthm wfr-hack3-good
  (IMPLIES (AND (CONSP R)
                (WFR R)
                )
           (WFR (CDR R)))
  :hints (("Goal" :use wfr-hack3
           :in-theory (e/d (wfr) ( wfr-hack3)))))

;; (defthm wfr-hack3-ifrp
;;   (IMPLIES (AND (CONSP R)
;;                 ;(rcdp r)
;;                 (not (ifrp r)) ;(WFR R)
;;                 )
;;            (not (ifrp (cdr r))) ;(WFR (CDR R))
;;            )
;;   :hints (("Goal" :do-not '(generalize ;eliminate-destructors
;;                                        )
;; ;           :expand (IFRP r)
;;            :in-theory (enable wfr WFKEYED))))

(defthm wfr-hack4
  (IMPLIES (AND (WFR R)
                a
                (NOT (G A R)))
           (NOT (SET::IN A (KEY-SET R))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable rkeys key-set g ;wfr
                              wfr-hack1
                              wfkeyed))))

;; (defthm wfr-hack4-try
;;   (IMPLIES (AND (not (ifrp r)) ;(WFR R)
;;                 a
;;                 (NOT (G A R)))
;;            (NOT (SET::IN A (KEY-SET R))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable rkeys key-set g ;wfr
;;                               wfkeyed))))

;disable?!
(defthm wfr-hack5
  (IMPLIES (AND (NOT (G A (CDR R)))
                (not (ifrp r)) ;(WFR R)
                A
                (G A R))
           (EQUAL (CAAR R) A))
  :hints (("Goal" :in-theory (e/d (g wfr WFKEYED) ()))))

(defthm g-of-caar
  (IMPLIES (AND (not (ifrp r))
                (CONSP R)
                )
           (G (CAAR R) R))
  :hints (("Goal" :in-theory (enable g)
           :do-not '(generalize eliminate-destructors))))

(defthm g-iff
  (implies (and
            (wfr r)
;            (not (ifrp r))
            a
            )
           (iff (g a r)
                (set::in a (rkeys r))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable rkeys key-set))))

(defthm g-iff-ifrp
  (implies (and ;(wfr r)
            (ifrp r) ;weird case
            ;a
            )
           (iff (g a r)
                (set::in a (rkeys r))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((SET::IN A '(NIL)))
           :in-theory (e/d (RKEYS ACL2->RCD g) (ifrp)))))

;; (thm
;;  (IMPLIES (AND (not (ifrp R)) A (G A R))
;;           (SET::IN A (KEY-SET R)))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;           :induct t
;;           :in-theory (e/d (RKEYS ACL2->RCD g) (ifrp)))))

(defthm in-of-key-set-hack
  (IMPLIES (AND (<< A (CAAR R))
                (RCDP R))
           (NOT (SET::IN A (KEY-SET R)))))

(defthm rcdp-when-not-ifrp
  (implies (not (ifrp r))
           (rcdp r)))

(defthm in-of-key-set-hack-2
  (IMPLIES (AND (rcdp r) ;(NOT (IFRP R))
                (NOT (G-AUX A R)))
           (NOT (SET::IN A (KEY-SET R))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm in-of-key-set-hack-3
  (IMPLIES (AND (rcdp r) ;(NOT (IFRP R))
                (G-AUX A R))
           (SET::IN A (KEY-SET R)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm g-iff-gen
  (iff (g a r)
       (set::in a (rkeys r)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :use (:instance g-iff-ifrp)
    ;           :induct t
           :in-theory (e/d (RKEYS ACL2->RCD g key-set) (g-iff-ifrp)))))

;move to sets
;expensive?
(defthm head-when-empty
  (implies (set::empty ads)
           (equal (set::head ads)
                  nil))
  :hints (("Goal" :in-theory (enable set::head set::sfix))))

(defthm setp-of-rkeys
  (equal (set::setp (rkeys r))
         t)
  :hints (("Goal" :in-theory (enable rkeys))))

;slow proof!
(defthm in-key-set-s-aux-two
  (implies (not (ifrp r)) ;(wfr r)
           (equal (set::in a (key-set (s-aux p v r)))
                  (if v (or (equal a p)
                            (set::in a (key-set r)))
                    (and (not (equal a p))
                         (set::in a (key-set r))))))
  :hints (("goal" :in-theory (e/d (WFKEYED wfr s-aux) (set::in)))))

(defthm rkeys-s-two-main-case
  (implies (not (ifrp r))
           (equal (rkeys (s a v r))
                  (if v (set::insert a (rkeys r))
                    (set::delete a (rkeys r)))))
  :hints (("goal" :in-theory (enable s rkeys SET::DOUBLE-CONTAINMENT-EXPENSIVE))))

(defthm rkeys-s-two-weird-case
  (implies (ifrp r)
           (equal (rkeys (s a v r))
                  (if v (set::insert a (rkeys r))
                    (set::delete a (rkeys r)))))
  :hints (("goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable s rkeys ACL2->RCD RCD->ACL2 set::in SET::DOUBLE-CONTAINMENT-EXPENSIVE))))

(defthm rkeys-s-two
  (equal (rkeys (s a v r))
         (if v (set::insert a (rkeys r))
           (set::delete a (rkeys r))))
  :hints (("Goal" :cases ((ifrp r)))))

(defthm g-when-not-in-rkeys-cheap
  (implies (NOT (SET::IN key (RKEYS rec)))
           (equal (G key rec)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm equal-nil-s
  (implies (not (equal nil v))
           (equal (equal nil (s a v r))
                  nil)))


;return the keys of the map as a list
(defun key-list (map)
  (declare (type t map))
  (set::2list (acl2::rkeys map)))

;fixme flesh out - or use a different version of maps
(defund mapp (map)
  (declare (xargs :guard t))
  (wfr map) ;requires the keys to be non-nil
  )

(local
 (defthm mapp-of-s-helper
  (implies (and (mapp map)
                v
                a
                )
           (mapp (s a v map)))
  :hints (("Goal" :induct  (S-AUX A V MAP)
           :in-theory (enable wfr WFKEYED wfkey s s-aux mapp ifrp RCD->ACL2)))))

(local
 (defthm mapp-of-s-helper-nil
   (implies (and (mapp map)
                 (equal v nil) ;this case
                 a
                 )
            (mapp (s a v map)))
   :hints (("Goal" ;:induct  (S-AUX A V MAP)
            :use (:instance wfr-of-clr (key a) (r map))
;           :in-theory (e/d (S-AUX mapp s ifrp) (RCDP-WHEN-NOT-IFRP))
            :in-theory (e/d (clr mapp) (S==R))
            ))))

(defthm mapp-of-s
  (implies (and (mapp map)
                a)
           (mapp (s a v map)))
  :hints (("Goal" :cases ((equal v nil)))))

(defthm in-of-rkeys-of-s-one
  (implies (and v
               (set::in k1 (rkeys map)))
           (set::in k1 (rkeys (s k2 v map)))))

(defthm in-of-rkeys-of-s-two
  (implies (and v
               (equal k1 k2))
           (set::in k1 (rkeys (s k2 v map)))))

;does something like this already exist?
(defun alist-to-map (alist)
  (declare (xargs :guard (alistp alist)))
  (if (endp alist)
      (empty-map)
    (let* ((entry (car alist))
           (key (car entry))
           (val (cdr entry)))
      (s key val (alist-to-map (cdr alist))))))

;expensive?
(defthm clr-when-not-in-rkeys
  (implies (not (set::in ad (RKEYS heap)))
           (equal (CLR ad heap)
                  heap))
  :hints (("Goal" :in-theory (e/d (CLR) (;S-NIL-BECOMES-CLR ;fixme looped!
                                         s==r
                                         )))))

(defthmd rkeys-of-s-safe
  (implies (not (equal nil v)) ;phrasing is for axe (TODO: can we just say v?)
           (equal (rkeys (s a v r))
                  (set::insert a (rkeys r)))))
