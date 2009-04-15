#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

;;This book is sort of a wrapper around misc/records.  It includes that booka
;;and then defines and proves some more stuff about records.

(local (include-book "basic" :dir :lists)) ;trying with this local..
(include-book "misc/records" :dir :system)

;;
;; The "clr" function
;;

(defund clr (a r)
  (declare (type t a r))
  (s a nil r))

(defthm clr-over-clr
  (implies
   (not (equal a1 a2))
   (equal (clr a1 (clr a2 r))
          (clr a2 (clr a1 r))))
  :hints (("Goal" :in-theory (enable clr))))

(defthm clr-of-clr
  (equal (clr a (clr a r))
         (clr a r))
  :hints (("Goal" :in-theory (enable clr))))

(defthm clr-over-s
  (equal (clr a1 (s a2 v r))
         (if (equal a1 a2)
             (clr a1 r)
           (s a2 v (clr a1 r))))
  :hints (("Goal" :in-theory (enable clr))))

(defthm g-of-clr
  (equal (g a1 (clr a2 r))
         (if (equal a1 a2) 
             nil
           (g a1 r)))
  :hints (("Goal" :in-theory (enable clr))))

(defun failed-location (tag)
  (declare (ignore tag))
  nil)

(defthm not-failed-location
  (implies
   (failed-location x)
   nil)
  :rule-classes (:forward-chaining))

(in-theory (disable failed-location (failed-location) (:type-prescription failed-location)))

(defun tag-location (tag b)
  (implies (not b)
           (failed-location tag)))

(defthmd tag-location-elimination
  (iff (tag-location tag b) b)
  :hints (("goal" :in-theory (enable failed-location))))

(in-theory (disable (tag-location)))

(in-theory (e/d (tag-location-elimination) (tag-location)))

;; For proofs failing as a result of certain existential rules,
;; the command (enable-fail-tags), entered at the ACL2 prompt,
;; will cause the theorem prover to "tag" the locations of the
;; failed subgoals to aide in debugging.

(defmacro enable-fail-tags ()
  `(in-theory (e/d (tag-location) (tag-location-elimination))))

; jcd - extracted this from later encapsulate and made it local to this book
; so that it won't be exported
(local (defthm s-aux-is-bounded
         (implies (and (rcdp r)
                       (s-aux a v r)
                       (<< e a)
                       (<< e (caar r)))
                  (<< e (caar (s-aux a v r))))))
 
; jcd - extracted this from later encapsulate and made it local to this book
; so that it won't be exported
(local (defthm s-aux-preserves-rcdp
         (implies (rcdp r)
                  (rcdp (s-aux a v r)))))

(encapsulate
 ()

   (defthm rcdp-implies-true-listp
     (implies (rcdp x)
              (true-listp x))
     :rule-classes :forward-chaining)

   (defthm g-aux-same-s-aux
     (implies (rcdp r)
              (equal (g-aux a (s-aux a v r))
                     v)))

   (defthm g-aux-diff-s-aux
     (implies (and (rcdp r)
                   (not (equal a b)))
              (equal (g-aux a (s-aux b v r))
                     (g-aux a r))))

   (defthm s-aux-same-g-aux
     (implies (rcdp r)
              (equal (s-aux a (g-aux a r) r) 
                     r)))

   (defthm s-aux-same-s-aux
     (implies (rcdp r)
              (equal (s-aux a y (s-aux a x r))
                     (s-aux a y r))))

   (defthm s-aux-diff-s-aux
     (implies (and (rcdp r)
                   (not (equal a b)))
              (equal (s-aux b y (s-aux a x r))
                     (s-aux a x (s-aux b y r))))
     :rule-classes ((:rewrite :loop-stopper ((b a s)))))

   (defthm s-aux-non-nil-cannot-be-nil
     (implies (and v (rcdp r))
              (s-aux a v r)))

   (defthm g-aux-is-nil-for-<<
     (implies (and (rcdp r)
                   (<< a (caar r)))
              (equal (g-aux a r) nil)))

   (local (in-theory (enable acl2->rcd rcd->acl2)))

   (defthm acl2->rcd-rcd->acl2-of-rcdp
     (implies (rcdp x)
              (equal (acl2->rcd (rcd->acl2 x))
                     x)))
 
   (defthm acl2->rcd-returns-rcdp
     (rcdp (acl2->rcd x)))

   (local
    (defthm acl2->rcd-preserves-equality
      (equal (equal (acl2->rcd x) (acl2->rcd y))
             (equal x y))))

   (defthm rcd->acl2-acl2->rcd-inverse
     (equal (rcd->acl2 (acl2->rcd x)) x))

   (defthm rcd->acl2-of-record-non-nil
     (implies (and r (rcdp r))
              (rcd->acl2 r)))

   (local (in-theory (disable acl2->rcd rcd->acl2)))

   (defthm s-aux-preserves-rcdp
     (implies (rcdp r)
              (rcdp (s-aux a v r))))

 (local
  (encapsulate
   ()

;-------------------------------------------------------------

   (defun s-g-induction (a r1 r2)
     (if (and (or (endp r1) (<< a (caar r1))) t)
         nil
       (if (equal a (caar r1))
           (equal r2 r2)
         (s-g-induction a (cdr r1) (cdr r2)))))

   (defthm s-aux==r-aux-lemma
     (implies (and (rcdp r1)
                   (rcdp r2)
                   (not (equal r1 (s-aux a (g-aux a r1) r2))))
              (not (equal (s-aux a 0 r2) (s-aux a 0 r1))))
     :hints (("goal" :do-not '(generalize eliminate-destructors)
              :in-theory (e/d (rcdp) (list::equal-cons-cases))
              :induct (s-g-induction a r1 r2))))
  
   (defthm s-aux==r-aux
     (implies (and (syntaxp (not (equal v '(quote 0))))
                   (rcdp r1)
                   (rcdp r2))
              (equal (equal r1 (s-aux a v r2))
                     (and (equal v (g-aux a r1))
                          (equal (s-aux a 0 r2)
                                 (s-aux a 0 r1))))))

   (defthm rcd->acl2-preserves-equality
     (implies (and (rcdp x) (rcdp y))
              (equal (equal (rcd->acl2 x) (rcd->acl2 y))
                     (equal x y)))
     :hints (("goal" :in-theory (enable rcd->acl2))))

   (defthm worht
     (implies (rcdp y)
              (equal (equal x (rcd->acl2 y)) 
                     (equal (acl2->rcd x) y))))

   ))

 (defthm s==r
   (equal (equal (s a v r2) r1)
          (and (tag-location a (equal v (g a r1)))
               (equal (clr a r2)
                      (clr a r1))))
   :hints (("goal" :in-theory (e/d (clr s g)))
           ))

 (defthm equal-s-record-equality
   (implies
    (and
     (equal rec2 rec1)
     (equal v (g a rec1)))
    (and (equal (equal rec1 (s a v rec2)) t)
;(equal (equal (s a v rec2) rec1) t)
         )))

 )

(theory-invariant (incompatible (:rewrite S==R) (:definition clr)))

(encapsulate
 ()

 (local
  (encapsulate
   ()

   (defthm s-aux-non-nil-cannot-be-nil
     (implies (and v (rcdp r))
              (s-aux a v r)))
   
   (defthm cdr-s-aux
     (equal (cdr (s-aux a v r))
            (cdr (cond ((or (endp r) (<< a (caar r)))
                        (if v (cons (cons a v) r) r))
                       ((equal a (caar r))
                        (if v (cons (cons a v) (cdr r))
                          (cdr r)))
                       (t (cons (car r) (s-aux a v (cdr r))))))))
   
   (defun len-len-induction (r1 r2)
     (if (or (endp r1) (endp r2)) nil
       (cons (cons (car r1) (car r2)) (len-len-induction (cdr r1) (cdr r2)))))
   
   (defthm s-aux-equal-differential
     (implies (and (rcdp rcd1)
                   (rcdp rcd2)
                   (equal (s-aux a v rcd1)
                          (s-aux a v rcd2))
                   (not (equal rcd1 rcd2)))
              (equal (equal (g-aux a rcd1)
                          (g-aux a rcd2)) nil))
     :hints (("goal" :induct (len-len-induction rcd1 rcd2))))
   
   (defthm rcd->acl2-preserves-equality
     (implies
      (and
       (rcdp x)
       (rcdp y))
      (equal (equal (rcd->acl2 x) (rcd->acl2 y))
           (equal x y)))
     :hints (("goal" :in-theory (enable rcd->acl2))))
   
   (defthm car-s-aux
     (equal (car (s-aux a v r))
            (car (cond ((or (endp r) (<< a (caar r)))
                        (if v (cons (cons a v) r) r))
                       ((equal a (caar r))
                        (if v (cons (cons a v) (cdr r))
                          (cdr r)))
                       (t (cons (car r) (s-aux a v (cdr r))))))))
   
   (defthm s-aux-preserves-rcdp
     (implies
      (rcdp r)
      (rcdp (s-aux a v r))))
   
   (defthm rcdp-acl2->rcd
     (rcdp (acl2->rcd x))
     :hints (("goal" :in-theory (enable acl2->rcd))))
   
   (local
    (defthm acl2->rcd-preserves-equality
      (implies
       (syntaxp (symbolp x))
       (equal (equal x y)
              (equal (acl2->rcd x) (acl2->rcd y))))
      :hints (("goal" :in-theory (enable acl2->rcd)))))
   
   (defthm s-equal-differential-g
     (implies (and (equal (s a v rcd1)
                          (s a v rcd2))
                   (not (equal rcd1 rcd2)))
              (equal (equal (g a rcd1) (g a rcd2))
                     nil))
     :hints (("goal" :in-theory (enable s g))))
 
   (defthm s-equal-differential-v
     (implies (and (equal (s a v1 rcd1)
                          (s a v2 rcd2))
                   (not (equal rcd1 rcd2)))
              (equal (equal v1 v2) t)))
 
   ))

;Part of this is hung on equal

 (defthmd s-equal-differential
   (implies (and (equal (s a v1 rcd1)
                        (s a v2 rcd2))
                 (not (equal rcd1 rcd2)))
            (and (equal (equal v1 v2)
                        t)
                 (equal (equal (g a rcd1) (g a rcd2))
                        nil)))
   :hints (("goal" :in-theory nil
            :use ((:instance s-equal-differential-g (v v2))
                  (:instance s-equal-differential-v)))))

 (defthm g-s-differential
   (implies
    (and
     (not (equal rcd1 rcd2))
     (equal (g a rcd1) (g a rcd2)))
    (equal (equal (s a v rcd1)
                  (s a v rcd2)) nil))
   :hints (("goal" :in-theory nil
            :use ((:instance s-equal-differential (v1 v) (v2 v))))))
 
 (defthm clr-differential
   (implies
    (equal (clr a r1) (clr a r2))
    (equal (equal r1 r2)
           (equal (g a r1)
                  (g a r2))))
   :hints (("goal" :in-theory '(clr g-s-differential s-equal-differential))))
 
 
 )

; jcd - made this local to this book, so it won't be exported
(local (defthm acl2-count-of-g-aux-bound
         (<= (acl2-count (acl2::g-aux a r))
             (acl2-count r))
         :hints (("Goal" :do-not '(generalize eliminate-destructors)))))

(defthm acl2-count-of-g-bound
  (<= (acl2-count (g a r)) (acl2-count r))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable g acl2::g-aux ACL2::ACL2->RCD ))))

; jcd - made this local to this book, so it won't be exported
(local (defthm iff-s-aux-cases
         (implies (rcdp r)
                  (iff (s-aux a v r)
                       (not (or (and (ENDP R) 
                                     (not V))
                                (and (consp r) 
                                     (not v) 
                                     (EQUAL A (CAAR R)) 
                                     (not (cdr r)))))))))

; jcd - change this to more simple if form
; was: (defun wfkey (k)
;        (declare (type t k))
;        (not (not k)))

(defun wfkey (k)
  (declare (type t k))
  (if k t nil))

;; (defun wfkeys (list)
;;   (declare (type t list))
;;   (if (consp list)
;;       (and (wfkey (car list))
;;            (wfkeys (cdr list)))
;;     t))

(defun wfkeyed (r)
  (declare (type t r))
  (if (consp r)
      (and (consp (car r))
           (wfkey (caar r))
           (wfkeyed (cdr r)))
    t))

; jcd - made this local to this book, so it won't be exported
(local (defthm not-ifrp-s-aux
         (implies (and
                   (not (ifrp r))
                   (rcdp r)
                   (wfkeyed r)
                   (wfkey a))
                  (not (ifrp (s-aux a v r))))
         :hints (("goal" :induct (s-aux a v r)))))

; jcd - made this local to this book, so it won't be exported
; ews - doh! I needed this (at least temporarily) to be non-local
(local 
 (defthm wfkeyed-s-aux
         (implies (and (not (ifrp r))
                       (rcdp r)
                       (wfkeyed r)
                       (wfkey a))
                  (wfkeyed (s-aux a v r)))
         :hints (("goal" :induct (s-aux a v r))))
)

(defun wfr (r)
  (declare (type t r))
  (and (rcdp r)
       (not (ifrp r))
       (wfkeyed r)))

(defthm wfr-implies
  (implies
   (wfr r)
   (and (rcdp r)
       (not (ifrp r))
       (wfkeyed r)))
  :rule-classes (:forward-chaining))

; jcd - added this rule (s-nil-nil-wfr)
(encapsulate 
 nil
 
 (defthm wfr-cancellations
   (implies (wfr r)
            (and (equal (rcd->acl2 r) r)
                 (equal (acl2->rcd r) r)))
   :hints(("Goal" :in-theory (enable rcd->acl2 acl2->rcd))))
 
 (local (defthm s-aux-nil-nil-wfr
          (implies (rcdp r)
                   (wfr (s-aux nil nil r)))))
 
 (local (defthm acl2->rcd-rcd
          (rcdp (acl2->rcd r))
          :hints(("Goal" :in-theory (enable acl2->rcd)))))

 (defthm s-nil-nil-wfr
   (wfr (s nil nil r))
   :hints(("Goal" :in-theory (e/d (s) (wfr)))))
)

; jcd - made this local to this book, so it won't be exported
(local (defthm wfr-s-aux
         (implies (and (wfr r) (wfkey a))
                  (wfr (s-aux a v r)))))

;; when can s-aux be nil?
(defthm s-preserves-wfr
  (implies (and (wfkey a) (wfr r))
           (wfr (s a v r)))
  :hints (("goal" :in-theory (enable s acl2->rcd rcd->acl2))))


; jcd - made this local to this book, so it won't be exported
(local (defthm acl2-count-g-aux-decreases
         (implies (and (wfr r)
                       (g-aux a r))
                  (< (acl2-count (g-aux a r))
                     (acl2-count r)))
         :hints (("goal" :induct (g-aux a r)))))

(defthm acl2-count-g-decreases
  (implies (and (wfr r)
                (g a r))
           (< (acl2-count (g a r))
              (acl2-count r)))
  :hints (("goal" :in-theory (enable g acl2->rcd)))
  :rule-classes (:linear :rewrite))

(in-theory (disable clr
                    wfr
                    wfkey
                    wfkeyed ; jcd - added wfkeyed
;                    wfkeys
                    ))

(defthm s-when-v-and-r-are-nil
  (equal (s key nil nil)
         nil))

(defthm clr-of-nil
  (equal (clr key nil)
         nil)
  :hints (("Goal" :in-theory (e/d (clr) (S==R)))))

;prove with lemmas instead of enabling
(defthm clr-when-r-is-not-a-consp
  (implies (not (consp r))
           (equal (clr nil r)
                  nil))
  :hints (("Goal" :in-theory (e/d (clr s acl2->rcd) (S==R)))))

;This is true even when the key is nil.
(defthm wfr-of-clr
  (implies (wfr r)
           (wfr (clr key r)))
  :hints (("Goal" :cases (key)
           :in-theory (e/d (clr wfkey) (S==R)))))

(defthm wfkeyed-of-s
  (implies (and (wfr r)
                (wfkey key)
                (wfkeyed r))
           (wfkeyed (s key v r)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :use (:instance S-PRESERVES-WFR (a key))
           :in-theory (e/d (wfr  WFKEY RCD->ACL2
                                 ) (S-PRESERVES-WFR)))))

(defthmd s-becomes-clr
  (equal (s a nil r)
         (clr a r)))

(theory-invariant (incompatible (:rewrite s-becomes-clr) (:definition clr)))

