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

;this is a version of tr-path-connection that uses fast memories instead of typed records.

;The book provides a mapping between typed records and the nested record structures accessed by paths.

;bzo some of this stuff should be moved to paths..

(include-book "mem-fast")
(include-book "../paths/path")
(include-book "../records/mem-domain")
(include-book "../osets/extras")
(include-book "../paths/path") ;don't use much of this


;;
;; mypush (turn a record into a fast memory)
;;

;bzo what do we do in the base case? need to know the size of the target record, right?
(defun mypush-aux (keys r size)
  (if (set::empty keys)
      (mem::new size) ;nil ;the empty typed record
    (gacc::wr (set::head keys)
              (g (set::head keys) r)
              (mypush-aux (set::tail keys) r size))))

(defund mypush (r size)
  (mypush-aux (set::rkeys r) r size))

(local (table theory-invariant-table nil nil :clear)) ;grrr

;; ;bzo add (or maybe this doesn't type-check?)
;; (defthm load-of-nil
;;   (equal (mem::load a nil)
;;          nil)
;;   :hints (("Goal" :in-theory (enable MEM::LOAD
;;                                      MEM::|_LOAD|))))

(defthm rd-of-new
  (equal (gacc::rd a (mem::new size))
         0)
  :hints (("Goal" :in-theory (enable gacc::rd))))

(defthm rd-of-mypush-aux
  (equal (gacc::rd a (mypush-aux rkeys r size))
         (if (set::in a rkeys)
             (loghead 8 (g a r))
           0)))

;for dave
(defthm rd-of-mypush
  (equal (gacc::rd a (mypush r size))
         (if (set::in a (set::rkeys r))
             (loghead 8 (g a r))
           0))
  :hints (("Goal" :in-theory (enable mypush))))

(defthm memory-clr-of-new
  (equal (gacc::memory-clr a (mem::new size))
         (mem::new size))
  :hints (("Goal" :in-theory (enable gacc::memory-clr))))

(defthm memory-clr-of-mypush-aux
  (equal (gacc::memory-clr key (mypush-aux rkeys r size))
         (mypush-aux rkeys (clr key r) size)))

;; (thm
;;  (iff (GACC::WR A v r)
;;       (or (unsigned-byte-p 8 v)
;;           (GACC::memory-clr A r)))
;;  :hints (("Goal" :in-theory (enable GACC::WR))))

;; ;what we really need is the analogous theorem for insert?
;; (defthm mypush-aux-of-cons
;;   (equal (mypush-aux (cons a rkeys) r)
;;          (gacc::wr a (g a r) (mypush-aux rkeys r)))
;;   :hints (("Goal" :induct t
;;            :expand ((MYPUSH-AUX (CONS A (SET::TAIL RKEYS))
;;                                  R)
;;                     (MYPUSH-AUX (CONS A RKEYS) R)
;;                     (SET::HEAD (CONS A RKEYS))
;;                     (SET::SETP (CONS A RKEYS))
;;                     (SET::EMPTY (CONS A RKEYS))
;;                     (SET::TAIL (CONS A RKEYS)))
;;            :in-theory (disable GACC::WR==R!)
;;            :do-not '(generalize eliminate-destructors))))


(local
 (defun my-ind (a rkeys r)
   (if (set::empty rkeys)
       (list a rkeys r)
     (if (equal a (set::head (set::insert a rkeys)))
         (list a rkeys r)
       (my-ind a (set::tail rkeys) (s (set::head rkeys) (g (set::head rkeys) r) r))))))




;clean up conclusion?
(defthmd car-of-insert
  (equal (car (set::insert a x))
         (cond ((set::empty x) a)
               ((equal (set::head x) a) (set::head x))
               ((<< a (set::head x)) a)
               (t (set::head x))))
  :hints (("Goal" :expand (set::insert a x)
           :in-theory (enable set::insert set::head))))

(defthm set-hack
  (implies (not (equal a (set::head (set::insert a s))))
           (equal (set::tail (set::insert a s))
                  (set::insert a (set::tail s))))
  :otf-flg t
  :hints (
          ("Goal" :expand ((SET::INSERT A S) ;prove a setp of cons rule?
                           (SET::SETP S)
                           (SET::INSERT A NIL)
                           (SET::INSERT A (CDR S))
                           (SET::SETP (CDDR S))
                           (SET::SETP (CDR S))
                           (:free (x y) (set::setp (cons x y)))
                           )
           :in-theory (e/d (car-of-insert SET::EMPTY SET::HEAD SET::tail SET::SFIX) ( SET::PICK-A-POINT-SUBSET-STRATEGY))
           :do-not '(generalize eliminate-destructors))))

(defthm set-hack2
  (implies (not (equal a (set::head (set::insert a s))))
           (equal (SET::HEAD (SET::INSERT A s))
                  (SET::HEAD s)))
  :otf-flg t
  :hints (("Goal" :expand ((SET::INSERT A S) ;prove a setp of cons rule?
                           (SET::SETP S)
                           (SET::INSERT A NIL)
                           (SET::INSERT A (CDR S))
                           (SET::SETP (CDDR S))
                           (SET::SETP (CDR S))
                           (:free (x y) (set::setp (cons x y)))
                           )
           :in-theory (e/d (car-of-insert SET::EMPTY SET::HEAD SET::tail SET::SFIX) ( SET::PICK-A-POINT-SUBSET-STRATEGY))
           :do-not '(generalize eliminate-destructors))))


;expensive?
(defthm not-in-when-<<-car
  (implies (<< a (car s))
           (not (set::in a s)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((set::empty s)
                    (set::setp s))
           :in-theory (enable set::head set::tail))))



(defthm tail-of-insert-when-equal-head-of-insert
  (implies (and (syntaxp (not (equal a ''nil)))
                (equal a (set::head (set::insert a s))))
           (equal (set::tail (set::insert a s))
                  (set::delete a s)))
  :otf-flg t
  :hints (("Goal" :expand ((SET::INSERT A S) ;prove a setp of cons rule?
                           (SET::SETP S)
                           (SET::INSERT A NIL)
                           (SET::INSERT A (CDR S))
                           (SET::SETP (CDDR S))
                           (SET::SETP (CDR S))
                           (:free (x y) (set::setp (cons x y)))
                           )
           :in-theory (e/d (car-of-insert SET::EMPTY SET::HEAD SET::tail SET::SFIX) ( SET::PICK-A-POINT-SUBSET-STRATEGY))
           :do-not '(generalize eliminate-destructors))))




;combine these cases?
(defthm mypush-aux-of-insert
  (equal (mypush-aux (set::insert a rkeys) r size)
         (if (set::in a rkeys)
             (mypush-aux rkeys r size)
           (gacc::wr a (g a r) (mypush-aux rkeys r size))))
  :otf-flg t
  :hints (("Goal" :induct (my-ind a rkeys r)
           :expand ((MYPUSH-AUX (SET::INSERT A nil) R size)
                    (MYPUSH-AUX (SET::INSERT A RKEYS) R size))
           :in-theory (disable GACC::WR==R!
                               )
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))))


(defthm memory-clr-of-mypush-aux2
  (equal (gacc::memory-clr key (mypush-aux rkeys r size))
         (mypush-aux (set::delete key rkeys) r size))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


;rename to say insert
(defthm mypush-aux-of-cons-irrel
  (implies (not (g key r))
           (equal (mypush-aux (set::insert key rkeys) r size)
                  (mypush-aux rkeys r size)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))




;drop?
(defthm mypush-aux-of-insert-irrel-of-clr
  (equal (mypush-aux (set::insert key rkeys) (clr key r) size)
         (mypush-aux rkeys (clr key r) size))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


(defthm mypush-irrel
  (implies (not (set::in key rkeys))
           (equal (mypush-aux rkeys (clr key r) size)
                  (mypush-aux rkeys r size)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


(defthm mypush-aux-of-clr
  (equal (mypush-aux rkeys (clr a r) size)
         (mypush-aux (set::delete a rkeys) r size))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


(defthm mypush-irrel2
  (implies (not (set::in key rkeys))
           (equal (mypush-aux rkeys (s key v r) size)
                  (mypush-aux rkeys r size)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

;; (thm
;;  (equal (mypush-aux (set::insert a rkeys) (s a v r))
;;         (gacc::wr a v (mypush-aux rkeys r)))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

;; (thm
;;  (equal (mypush-aux (set::rkeys r) (s a v r))
;;         (gacc::wr a v (mypush-aux (set::rkeys r) r))))

;for dave
(defthm mypush-of-s
  (equal (mypush (s a v r) size)
         (gacc::wr a v (mypush r size)))
  :hints (("Goal" :in-theory (enable mypush))))


;for dave
(defthm mypush-of-sp
  (equal (mypush (cpath::sp (list a) v r) size)
         (gacc::wr a v (mypush r size)))
  :hints (("Goal" :in-theory (enable cpath::sp))))

;need a way to get the keys of a typed record...  -can it be rkeys?
;then prove keys of wr = blah...

;;
;; my-lift (turn a typed-record into a regular record)
;;

;keys "bound" to 0 don't show up in the typed record (since 0 is the default
;value for typed records) and so become keys "bound" to nil in the record
;(such keys don't show up, since nil is the default value for records).
(defun mylift-aux (keys tr)
  (if (set::empty keys)
      nil ;the empty record
    (s (set::head keys)
       (gacc::rd (set::head keys) tr)
       (mylift-aux (set::tail keys) tr))))

;bzo
(defund mylift (m)
  (mylift-aux (mem::domain m) m))

(defthm domain-of-wr
  (implies (good-memoryp tr)
           (equal (mem::domain (gacc::wr a v tr))
                  (if (gacc::wf-usbp8 (mem::load a tr))
                      (if (gacc::usbp8-zp v)
                          (if (cdr (mem::load a tr))
                              (set::insert a (mem::domain tr))
                            (set::delete a (mem::domain tr)))
                        (set::insert a (mem::domain tr)))
                    (if (gacc::usbp8-zp v)
                        (mem::domain tr)
                      (set::insert a (mem::domain tr))))))
  :otf-flg t
  :hints (("Goal" :expand ((gacc::wr a v tr))
;          :induct nil
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))))

(defthm domain-of-wr-forced
  (implies (force (good-memoryp tr))
           (equal (mem::domain (gacc::wr a v tr))
                  (if (gacc::wf-usbp8 (mem::load a tr))
                      (if (gacc::usbp8-zp v)
                          (if (cdr (mem::load a tr))
                              (set::insert a (mem::domain tr))
                            (set::delete a (mem::domain tr)))
                        (set::insert a (mem::domain tr)))
                    (if (gacc::usbp8-zp v)
                        (mem::domain tr)
                      (set::insert a (mem::domain tr)))))))

(defthm g-of-mylift-aux
  (equal (g a (mylift-aux rkeys tr))
         (if (set::in a rkeys)
             (loghead 8 (gacc::rd a tr))
           nil)))

;for dave
(defthm g-of-mylift
  (equal (g a (mylift tr))
         (if (set::in a (mem::domain; rkeys
                         tr))
             (loghead 8 (gacc::rd a tr))
           nil))
  :hints (("Goal" :in-theory (enable mylift))))

;;
;; VAL-FIX
;;

(defun val-fix (v)
  (if (equal 0 (loghead 8 v))
      nil
     (loghead 8 v)))

;does this cause case splits?
(defthm integerp-of-val-fix
  (equal (integerp (acl2::val-fix x))
         (not (equal 0 (acl2::loghead 8 x))))
  :hints (("Goal" :in-theory (enable acl2::val-fix))))

(defthm loghead-8-of-val-fix
  (equal (acl2::loghead 8 (acl2::val-fix x))
         (acl2::loghead 8 x))
  :hints (("Goal" :in-theory (enable acl2::val-fix))))

(defthm wr-of-0-is-clr
  (implies (EQUAL (LOGHEAD 8 V) 0)
           (equal (GACC::WR A V TR)
                  (gacc::memory-clr A TR))))


;bzo improve CLR-OVER-CLR?

(defthm clr-of-clr-match-hack
  (implies (equal (clr b r1)
                  (clr b r2))
           (equal (equal (clr b (clr a r1))
                         (clr b (clr a r2)))
                  t))
  :hints (("Goal" :cases ((equal a b)))))

(defthm mylist-aux-of-insert
  (equal (mylift-aux (set::insert a rkeys) tr)
         (if (set::in a rkeys)
             (mylift-aux rkeys tr)
           (s a (gacc::rd a tr) (mylift-aux rkeys tr))))
  :otf-flg t
  :hints (("Goal" :induct (my-ind a rkeys rt)
           :expand ((MYLIFT-AUX (SET::INSERT A RKEYS) tR))
           :in-theory (disable GACC::WR==R!
                               )
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))))

(defthm empty-means-tail-nil
  (implies (set::empty s)
           (equal (set::tail s)
                  (set::emptyset)))
  :hints (("Goal" :in-theory (enable set::empty set::tail set::sfix))))

;bzo may loop with defn delete or something?
(defthmd delete-from-tail-when-not-head
  (implies (not (equal key (set::head s)))
           (equal (set::delete key (set::tail s))
                  (set::delete (set::head s) (set::delete key s))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand ((set::delete key s)))))

(defthm clr-of-mylift-aux
  (equal (clr key (mylift-aux rkeys tr))
         (mylift-aux (set::delete key rkeys) (gacc::memory-clr key tr)))
  :hints (("Goal" :in-theory (disable SET::DELETE)
           :expand ((SET::DELETE KEY RKEYS))
           :do-not '(generalize eliminate-destructors))))

;; ;drop?
;; (defun wfr-weak (r)
;;   (and (rcdp r)
;;        (not (ifrp r)) ;;should really just use a typed version of ifrp?
;;        ))


(defun non-nil (x)
  (declare (xargs :guard t))
  (not (null x)))

;; ;sheesh even the guard has a guard...
;; (set::quantify-predicate (mem::address-p key mem) :arg-guard ((MEM::MEMORY-P MEM)))


(defun check-tr-val (val)
  (and (unsigned-byte-p 8 val)
       (not (equal 0 val))))

(defun check-tr-entry (val)
  (and ;(GACC::WF-USBP8 (cdr val))
   (equal nil (cdr val))
   (check-tr-val (car val))))

;bzo rename?
(defun check-fr-key (key tr)
  ;;   (declare (xargs :guard (and (MEM::MEMORY-P TR)
  ;;                               (NATP KEY)
  ;;                               (< KEY (MEM::SIZE TR)))))
  (let* ((val (mem::load key tr)))
    (or (null val)
        (and ;(consp val)
;(equal nil (cdr val)) ;(equal 1 (len val))
;(unsigned-byte-p 8 (car val))
;(not (equal 0 (car val)))
         (check-tr-entry val)
         ))))



;bzo bad name? really this checks the values?
(defun check-fr-keys (keys tr)
  (if (set::empty keys)
      t
    (and (check-fr-key (set::head keys) tr)
         (check-fr-keys (set::tail keys) tr))))


;; ;crapola. I need the arg-guard to come first because it guards the list-guard and set-guard.
;; ;I just want a way to keep quantify-predicate from generating functions with guards...
;; (set::quantify-predicate (check-fr-key key mem)
;;                          :arg-guard ((mem::memory-p mem))
;;                          :list-guard ((set::all-list<address-p> set::?list mem))
;;                          :set-guard ((set::all<address-p> set::?set mem)))



(set-verify-guards-eagerness 2)

(set::quantify-predicate (non-nil x))   ; see quantify.lisp for explanation

(set-verify-guards-eagerness 1)

;; Well-formed fast-record, - bzo, bad name?
(defun wf-fr (tr)
  (and ;;(wfr-weak tr) ;;
       (good-memoryp tr) ;(wfr tr)
       ;(set::all<non-nil> (mem::domain TR)) ;like wfkeyed
       (check-fr-keys (mem::domain tr) tr)))

(defthm mylift-of-wr-1
  (implies (and (good-memoryp tr)
                (not (EQUAL 0 (LOGHEAD 8 V))))
           (equal (mylift (gacc::wr a v tr))
                  (s a (val-fix v) (mylift tr))))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable ;gacc::wr
                       mylift
                       ))))

(theory-invariant (incompatible (:rewrite WR-OF-0-IS-CLR) (:definition GACC::MEMORY-CLR)))

;; ;ttt
;; (defthm cdr-of-g-nil-when-in-keys
;;   (implies (and (check-fr-keys keys tr)
;;                 (set::in k keys)
;;                 (set::subset keys (mem::domain tr))
;;                 )
;;            (not (cdr (mem::load k tr))))
;;   :hints (("Goal" :cases ((mem::load k tr))
;;            :do-not '(generalize eliminate-destructors))))

;drop?
(defthm sfix-of-rkeys
  (equal (set::sfix (set::rkeys tr))
         (set::rkeys tr))
  :hints (("Goal" :in-theory (enable rkeys))))

;false
;; (thm
;;  (implies (rcdp r)
;;           (not (ifrp r)))
;;  :hints (("Goal" :in-theory (enable rcdp ifrp))))

(defthm wfr-implies-wfr-of-cdr
  (implies (wfr tr)
           (wfr (cdr tr)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand (ifrp (cdr tr))
           :in-theory (enable wfr ifrp rcdp wfkeyed))))

;; (defthm wfr-weak-implies-wfr-weak-of-cdr
;;   (implies (wfr-weak tr)
;;            (wfr-weak (cdr tr)))
;;   :otf-flg t
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :expand (ifrp (cdr tr))
;;            :in-theory (enable wfr ifrp rcdp wfkeyed))))


;; (defthm wfr-weak-cancellations
;;   (implies (wfr-weak r)
;;            (and (equal (rcd->acl2 r) r)
;;                 (equal (acl2->rcd r) r)))
;;   :hints (("Goal" :in-theory (enable rcd->acl2 acl2->rcd))))

;; (defthm wf-fr-cancellations
;;   (implies (wf-fr r)
;;            (and (equal (rcd->acl2 r) r)
;;                 (equal (acl2->rcd r) r)))
;;   :hints (("Goal" :in-theory (enable rcd->acl2 acl2->rcd))))


;; (defthm wf-fr-implies-wf-fr-of-cdr
;;   (implies (wf-fr tr)
;;            (wf-fr (cdr tr)))
;;   :otf-flg t
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :expand (ifrp (cdr tr))
;;            :in-theory (enable wfr ifrp rcdp wfkeyed))))

;skipping for now...
;; (defthm not-consp-g-of-cdr-but-consp-g
;;   (IMPLIES (AND (NOT (CONSP (mem::load ;G
;;                              A (CDR TR))))
;;                 (CONSP (mem::load ;G
;;                         A TR))
;;                 (WFR TR) ;was wfr-weak
;;                 )
;;            (EQUAL (CAAR TR) A))
;;   :hints (("Goal" :in-theory (enable g
;;                                      ))))

;cool!  didn't have to open up the "record operations"
;go the other way too?
(defthm not-in-domain-means-load-is-nil
  (implies (and (not (set::in key (mem::domain fm)))
                (good-memoryp fm)
                )
           (equal (mem::load key fm)
                  nil))
  :hints (("Goal" :use (:instance domain-of-store
                                  (a key)
                                  (v (mem::load key fm))
                                  (mem fm))
           :in-theory (disable ;MEM::STORE-OF-SAME-LOAD
                       domain-of-store))))

(defthm not-in-domain-means-load-is-nil2
  (implies (good-memoryp fm)
           (equal (set::in key (mem::domain fm))
                  (not (equal nil (mem::load key fm)))))
  :hints (("Goal" :use (:instance domain-of-store
                                  (a key)
                                  (v (mem::load key fm))
                                  (mem fm))
           :in-theory (disable ;MEM::STORE-OF-SAME-LOAD
                       domain-of-store))))

;; ;see ACL2::NOT-IN-DOMAIN-MEANS-LOAD-IS-NIL2 and ACL2::G-MEANS-IN-KEYS
;; (defthm consp-g-means-in-keys
;;   (implies (and (good-memoryp tr) ;more generally, could say non-nil?
;;                 (consp (mem::load a tr)))
;;            (set::in a (mem::domain tr)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable rkeys key-set))))
;replace the consp-g-version?
(defthm g-means-in-keys
  (implies (and (mem::load a tr)
                (GOOD-MEMORYP tr) ;(wfr tr)
                )
           (set::in a (mem::domain tr)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           ;:in-theory (enable rkeys key-set g))))
           )))

;; (defthm g-of-caar
;;   (implies (wfr tr)
;;            (equal (g (caar tr) tr)
;;                   (CDAR TR)
;;                   ))
;;   :hints (("Goal" :in-theory (enable g)
;;            :do-not '(generalize eliminate-destructors))))

;; (defthm cons-g-cdr-means-consp-g
;;   (implies (and (consp (g a (cdr tr)))
;;                 (wfr tr))
;;            (consp (g a tr)))
;;   :hints (("Goal" :in-theory (enable g wfr))))

;bzo disable?
;; (defthm cdar-of-wfr-non-nil
;;   (implies (and (consp tr)
;;                 (wfr tr))
;;            (cdar tr))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :expand (rcdp tr)
;;            :in-theory (enable wfr rcdp wfkeyed wfkey))))

;bzo combine?
;; (defthm not-g-means-not-in-rkeys
;;   (implies (and (not (g a tr))
;;                 (wfr tr))
;;            (not (set::in a (set::rkeys tr))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;; ;           :expand ((G A TR))
;;            :in-theory (enable rkeys key-set))))

(defthm mylift-irrel
  (implies (not (set::in key keys))
           (equal (mylift-aux keys (gacc::memory-clr key tr))
                  (mylift-aux keys tr)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


;; (defthm mylift-aux-of-clr
;;   (equal (mylift-aux rkeys (gacc::memory-clr a t))
;;          (mylift-aux (set::delete a rkeys) t))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors))))


(defthm rd-of-s-irrel
  (implies (not (equal key1 key2))
           (equal (GACC::RD key1 (mem::store ;S
                                  KEY2 V TR))
                  (GACC::RD key1 TR)))
  :hints (("Goal" :in-theory (enable GACC::RD))))

(defthm mylift-irrel2
  (implies (not (set::in key rkeys))
           (equal (mylift-aux rkeys (mem::store ;s
                                     key v tr))
                  (mylift-aux rkeys tr)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


;; (thm
;;  (IMPLIES (AND (WFR TR)
;;                ;(CHECK-FR-KEYS (SET::RKEYS TR) TR)
;;                ;(NOT (CONSP (G A TR)))
;;                )
;;           (EQUAL (MYLIFT-AUX (SET::DELETE A (SET::RKEYS TR))
;;                              (GACC::WR A 0 TR))
;;                  (MYLIFT-AUX (SET::RKEYS TR)
;;                              (GACC::WR A 0 TR)))))

;ttt
;; (defthmd check-fr-keys-lemma
;;   (IMPLIES (and (CHECK-FR-KEYS keys TR)
;;                 (set::in a keys)
;;                 (consp tr))
;;            (NOT (EQUAL (LOGHEAD 8 (CAR (mem::load ;G
;;                                         A TR))) 0))))

;ttt
;; (defthmd check-fr-keys-lemma2
;;   (IMPLIES (and (CHECK-FR-KEYS keys TR)
;;                 (set::in a keys)
;;                 (consp tr))
;;            (UNSIGNED-BYTE-P 8 (CAR (mem::load ;G
;;                                     A TR)))))

;maybe this is really load of new?
(defthm load-of-non-consp
  (implies (and (not (consp tr))
                (good-memoryp tr))
           (equal (MEM::LOAD A TR)
                  nil
                  ))
  :hints (("Goal" :in-theory (enable GOOD-MEMORYP
                                     MEM::LOAD
                                     MEM::MEMORY-P
                                     MEM::|_BAD-MEMORY-P|
                                     MEM::SIZE
                                     MEM::|_MEMORY-SIZE|
                                     MEM::|_MEMORY-P|
                                     MEM::|_MEMTREE-P|
                                     MEM::|_MEMTREE-FIX|
                                     MEM::|_MEMORY-MTREE|
                                     MEM::|_MEMORY-DEPTH|
                                     MEM::|_MEMTREE-LOAD|
                                     MEM::|_MEMORY-FIX|
                                     MEM::|_MEMORY-RECORD|
                                     mem::|_TO-MEM|
                                     MEM::|_LOAD|))))

;do we need this?
(defthm domain-of-non-consp
  (implies (not (consp m))
           (equal (mem::domain m)
                  nil))
  :hints (("Goal" :in-theory (enable MEM::DOMAIN
                                     GOOD-MEMORYP
                                     MEM::LOAD
                                     MEM::MEMORY-P
                                     MEM::|_BAD-MEMORY-P|
                                     MEM::SIZE
                                     MEM::|_MEMORY-SIZE|
                                     MEM::|_MEMORY-P|
                                     MEM::|_MEMTREE-P|
                                     MEM::|_MEMTREE-FIX|
                                     MEM::|_MEMORY-MTREE|
                                     MEM::|_MEMORY-DEPTH|
                                     MEM::|_MEMTREE-LOAD|
                                     MEM::|_MEMORY-FIX|
                                     MEM::|_MEMORY-RECORD|
                                     mem::|_TO-MEM|
                                     MEM::|_LOAD|))))

(defthm use-check-fr-keys
  (implies (and (check-fr-keys keys r)
                (set::in a keys))
           (check-fr-key a r)))

(in-theory (disable check-fr-key check-fr-keys))

(defthm use-check-fr-keys-2
  (implies (and (check-fr-keys keys r)
                (set::subset (mem::domain r) keys)
                (set::in a (mem::domain r)))
           (check-fr-key a r)))


(defthm mylift-of-wr-0-case
  (implies (and (wf-fr tr) ;(wfr tr)
                (good-memoryp tr)
                (equal 0 (loghead 8 v)))
           (equal (mylift (gacc::wr a v tr))
;if what was there was well-formed, we get 0.  otherwise (including if it was 0 before!), we get what was there!
                  (s a nil (mylift tr))))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;  :cases ((SET::in A (SET::RKEYS TR)))
           :use (;(:instance check-fr-keys-lemma (keys (mem::domain tr)))
                 ;(:instance check-fr-keys-lemma2 (keys (mem::domain tr)))
                 (:instance use-check-fr-keys (r tr) (keys (MEM::DOMAIN TR)))
                 )
           :in-theory (e/d ( ;gacc::wr
                            mylift
                            check-fr-keys
                            check-fr-key
                            GACC::MEMORY-CLR
                            )
                           (WR-OF-0-IS-CLR
                            LOGHEAD*-BETTER ;bzo why isn't this disabled?
                            LOGCAR-LOGCDR-ELIM
                            )))))

(in-theory (disable LOGHEAD*-BETTER))

;bzo can we improve this?
;for dave
(defthm mylift-of-wr
  (implies (and; (good-memoryp tr)
                (wf-fr tr)
                ;v
                )
           (equal (mylift (gacc::wr a v tr))
                  (s a (val-fix v) (mylift tr))))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :use ((:instance mylift-of-wr-0-case)
                 (:instance mylift-of-wr-1))
           :in-theory (disable MYLIFT
                               g-of-mylift
                               ))))

;see S-PRESERVES-WFR (should WFKEY be enabled?)

;bzo maybe wf-fr should allow nil keys?

;bzo move
(defthm load-of-store-redux
  (equal (mem::load a (mem::store b v r))
         (if (equal a b)
             v
           (mem::load a r))))

;bzo really what's checked by CHECK-FR-KEYS is the value -rename

(defthm check-fr-keys-of-store
  (implies (and (check-fr-keys keys tr)
                (or (null v)
                    (check-tr-entry v)) ;the whole entry, not the val
                )
           (check-fr-keys keys (mem::store a v tr)))
  :hints (("Goal" :in-theory (enable check-fr-keys check-fr-key)
           :do-not '(generalize eliminate-destructors))))

(defthm check-fr-keys-of-s-irrel
  (implies (not (set::in a keys))
           (equal (check-fr-keys keys (mem::store a nil tr))
                  (check-fr-keys keys tr)))
  :hints (("Goal" :in-theory (enable check-fr-keys check-fr-key))))

(defthm delete-when-would-be-head
  (implies (equal a (set::head (set::insert a keys)))
           (equal (set::delete a keys)
                  (if (set::in a keys)
                      (set::tail keys)
                    (set::sfix keys))))
  :hints (("Goal" :in-theory (enable set::sfix ;bzo
                                     ))))

(defthm car-of-insert-of-nil
  (equal (car (set::insert k nil))
         k)
  :hints (("Goal" :in-theory (enable set::insert))))

(defthm check-fr-keys-of-insert
  (equal (check-fr-keys (set::insert a keys) tr)
         (let* ((val (mem::load a tr)))
           (and (check-fr-keys keys tr)
                (or (null val)
                    (and (consp val)
                         (equal nil (cdr val))
                         (unsigned-byte-p 8 (car val))
                         (not (equal 0 (car val)))
                         )))))
  :otf-flg t
  :hints (("Goal" :induct (my-ind a keys r)
           :expand ((CHECK-FR-KEYS (SET::INSERT A KEYS) tR)
                    )
           :in-theory (e/d (CHECK-FR-KEYS CHECK-FR-KEY) ( gacc::wr==r! ))
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))))

(defthm check-fr-keys-of-delete
  (implies (check-fr-keys keys tr)
           (check-fr-keys (set::delete a keys) tr))
  :hints (("Goal"
           :in-theory (e/d (CHECK-FR-KEYS CHECK-FR-KEY) (  ))
           :expand (CHECK-FR-KEYS (SET::INSERT (SET::HEAD KEYS)
                                               (SET::DELETE A (SET::TAIL KEYS)))
                                  TR)
           :do-not '(generalize eliminate-destructors))))
;ttt
;; (defthm consp-g-when-in-keys-and-check-fr-keys
;;   (implies (and (check-fr-keys keys tr)
;;                 (set::in a keys)
;;                 )
;;            (consp (mem::load ;g
;;                    a tr)))
;;   :hints (("Goal" :in-theory (enable check-fr-keys))))

;ttt
;; (defthm consp-g-when-g-and-check-fr-keys
;;   (implies (and (check-fr-keys (mem::domain ;rkeys
;;                                 tr) tr)
;;                 (mem::load ;g
;;                  a tr) ;is not nil
;;                 (good-memoryp ;;wfr
;;                  tr)
;;                 )
;;            (consp (mem::load ;g
;;                    a tr)))
;;   :hints (("Goal" :use (:instance consp-g-when-in-keys-and-check-fr-keys (keys (mem::domain ;rkeys
;;                                                                                 tr)))
;;            :in-theory (e/d (check-fr-keys) (consp-g-when-in-keys-and-check-fr-keys)))))

;; ;maybe this isn't true...
;; ;darn.  i wish wfkeyed just took the rkeys and looked at it...
;; (thm
;;  (implies v
;;           (not (wfkeyed (s nil v r))))
;;  :hints (("Goal" :in-theory (enable wfkeyed s ACL2->RCD RCD->ACL2 IFRP))))

;; (defthm s-preserves-wfr-2
;;   (implies (wfr r)
;;            (equal (wfr (s a v r))
;;                   (or (wfkey a)
;;                       (not v))))
;;   :hints (("goal" :in-theory (enable ;s acl2->rcd rcd->acl2
;;                               WFR
;;                               WFKEY
;;                               ))))


(defthm use-check-fr-key-1
  (implies (check-fr-key a tr)
           (not (CDR (MEM::LOAD A TR))))
  :hints (("Goal" :in-theory (enable check-fr-key))))

(defthm use-check-fr-key-2
  (implies (check-fr-key a tr)
           (iff (consp (mem::load a tr))
                (mem::load a tr))
           )
  :hints (("Goal" :in-theory (enable check-fr-key))))

(defthm use-check-fr-key-3
  (implies (check-fr-key a tr)
           (or (null (mem::load a tr))
               (gacc::wf-usbp8 (mem::load a tr))
               ))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable check-fr-key))))


;for dave
(defthm wf-fr-of-wr
  (implies (and (wf-fr tr)
                ;;a ;that is, a is not nil
                )
           (wf-fr (gacc::wr a v tr)))
  :otf-flg t
  :hints (("Goal" :expand (CHECK-FR-KEYS (SET::INSERT A NIL) (mem::store A (LIST (LOGHEAD 8 V)) NIL))
           :use ( ;(:instance check-fr-keys-lemma2 (keys (mem::domain tr)))
;(:instance check-fr-keys-lemma (keys (mem::domain tr)))
                 (:instance use-check-fr-keys-2 (keys (MEM::DOMAIN TR)) (r tr))
                 use-check-fr-key-3
                 )
           :cases ((set::in a (MEM::DOMAIN TR)))
           :in-theory (e/d (GACC::WR wfkey ;GACC::WF-USBP8
                                     CHECK-TR-ENTRY
                                     ) ( ;check-fr-keys-lemma2 check-fr-keys-lemma
                                        ;;check-tr-entry
                                     USE-CHECK-FR-KEYS-2
                                     GACC::WF-USBP8
                                     )))))


;for dave
(defthm mylift-of-wr-sp-version
  (implies (wf-fr tr)
           (equal (mylift (gacc::wr a v tr))
                  (cpath::sp (list a) (val-fix v) (mylift tr))))
  :hints (("Goal" :in-theory (e/d ( CPATH::SP) (MYLIFT WF-FR val-fix)))))




;; ;bzo dup?
;; (defun all-non-nil (lst)
;; ;  (declare (xargs :guard t))
;;   (if (set::empty lst)
;;       t
;;     (and (not (null (set::head lst)))
;;          (all-non-nil (set::tail lst)))))

(defthm head-non-nil-when-all-non-nil
  (implies (and (set::all<non-nil> s)
                (not (set::empty s)))
           (set::head s))
  :hints (("Goal" :in-theory (enable))))

(defthm wfr-of-mylift-aux
  (implies (set::all<non-nil> keys)
           (wfr (mylift-aux keys tr)))
  :hints (("Goal" :in-theory (enable wfkey)
           :do-not '(generalize eliminate-destructors))))

(defthm rkeys-of-mylift-aux
  (implies (and (wf-fr tr)
;                (set::all<non-nil> keys)
                (set::setp keys))
           (equal (set::rkeys (mylift-aux keys tr))
                  keys))
  :hints (("Goal" :in-theory (enable SET::EMPTY))))

;;bzo wfkeyed should be rewritten to be more abstract.  just call rkeys and check for nils in the result.

;; (defthm all-non-nil-of-rkeys
;;   (implies (and (wfkeyed tr)
;;                 ;(wfr tr)
;;                 (good-memoryp tr)
;;                 )
;;            (set::all<non-nil> (mem::domain ;rkeys
;;                                tr)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable ;wfr
;;                        wfkeyed wfkey rkeys))))

;trying without...
;; (defthm all-non-nil-of-rkeys2
;;   (implies (wf-fr tr)
;;            (set::all<non-nil> (mem::domain ;RKEYS
;;                                TR)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable wfr WFKEYED))))

(defthm empty-rkeys-when-wfr
  (equal (set::empty (set::rkeys tr))
         (not tr))
  :hints (("Goal" :in-theory (e/d (set::rkeys)
                                  (SET::EMPTY-WHEN-SETP-MEANS-NIL)))))

(local
 (defun ind (keys tr)
   (declare (xargs :verify-guards nil))
   (if (or (not (set::setp keys))
           (set::empty keys))
       (list keys tr)
     (ind (set::tail keys)
          (GACC::MEMORY-CLR (SET::HEAD (mem::domain ;;RKEYS
                                        TR)) tr) ;
    ;(gacc::wr (set::head keys) (gacc::rd (set::head keys) tr) tr)
          ))))

(defthm rkeys-of-memory-clr
  (implies (and ;(rcdp tr) ;; (wfr tr)
                ;(not (ifrp tr))
            (wf-fr tr) ;hope this is okay...
                )
           (equal (mem::domain ;;rkeys
                   (gacc::memory-clr a tr))
                  (if (gacc::wf-usbp8 (mem::load ;g
                                       a tr))
                      (if (cdr (mem::load ;g
                                a tr))
                          (set::insert a (mem::domain ;;rkeys
                                          tr))
                        (set::delete a (mem::domain ;;rkeys
                                        tr)))
                    (mem::domain ;;rkeys
                     tr))))
  :hints (("Goal" :in-theory (e/d (gacc::memory-clr) (WR-OF-0-IS-CLR)))))

;bzo move?
;; (defthm wfr-of-wr
;;   (implies (and (wfr tr)
;;                 (wfkey a))
;;            (wfr (GACC::WR A v TR)))
;;   :hints (("Goal" :in-theory (e/d (GACC::WR) ()))))

;; (defthm wfr-of-memory-clr
;;   (implies (and (wfr tr)
;;                 (wfkey a))
;;            (wfr (gacc::memory-clr a tr)))
;;   :hints (("Goal" :in-theory (e/d (gacc::memory-clr) (wr-of-0-is-clr)))))


(defthm CHECK-FR-KEYS-when-empty
  (implies (SET::EMPTY RKEYS)
           (CHECK-FR-KEYS RKEYS TR))
  :hints (("Goal" :in-theory (enable CHECK-FR-KEYS))))

(defthm not-check-fr-keys-1
  (implies (and (MEM::LOAD (SET::HEAD RKEYS) TR)
                (equal 0 (loghead 8 (car (mem::load (set::head rkeys) tr)))))
           (equal (check-fr-keys rkeys tr)
                  (set::empty rkeys)))
  :otf-flg t
  :hints (("Goal" :use (:instance use-check-fr-keys (keys rkeys) (a (set::head rkeys)) (r tr))
           :in-theory (e/d (;CHECK-FR-KEYS
                            CHECK-FR-KEY
                            ) (use-check-fr-keys)))))

(defthm check-fr-keys-of-memory-clr-irrel
  (implies (and (not (set::in key keys))
                ;(wfr tr)
                (wf-fr tr)
                )
           (equal (check-fr-keys keys (gacc::memory-clr key tr))
                  (check-fr-keys keys tr)))
  :hints (("Goal" :in-theory (e/d (GACC::MEMORY-CLR GACC::WR) (WR-OF-0-IS-CLR))
           :do-not '(generalize eliminate-destructors))))

;; (defthm nil-not-in-key-set-when-wfkeyed
;;   (implies (WFKEYED R)
;;            (not (set::in nil (key-set r))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable key-set wfr wfkeyed wfkey))))

;; (defthm nil-not-in-key-set-when-wfr
;;  (implies (wfr r)
;;           (not (set::in nil (key-set r))))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;           :in-theory (enable key-set wfr wfkeyed wfkey))))

;trying without
;; (defthm wfkey-when-in-rkeys
;;   (implies (and ;(wfr tr)
;;             (wf-fr tr)
;; ;               tr ;
;;                 (set::in key (mem::domain ;rkeys
;;                               tr))
;;                 )
;;            (wfkey key))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (e/d (wfr rkeys wfkey wfkeyed) (NOT-IN-DOMAIN-MEANS-LOAD-IS-NIL2)))))

;skipping for now
;; (defthm wkeys-of-head-of-rkeys
;;   (implies (and ;(wfr tr)
;;             (wf-fr tr)
;;                 ;tr ;need to say something stronger now to imply the domain isn't empty...
;;                 )
;;            (wfkey (set::head (mem::domain ;rkeys
;;                               tr))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (e/d (;wfr rkeys wfkey wfkeyed
;;                        ) (wf-fr)))))

(defthm good-memoryp-of-wr
 (implies (and (good-memoryp tr)
               ;a
               )
          (good-memoryp (gacc::wr a v tr)))
 :hints (("Goal" :in-theory (e/d (gacc::wr) ()))))

(defthm good-memoryp-of-memory-clr
  (implies (and (good-memoryp tr)
                ;a ;drop?
                )
           (good-memoryp (gacc::memory-clr a tr)))
  :hints (("Goal" :in-theory (e/d (gacc::memory-clr) (wr-of-0-is-clr)))))



;; ;Bbzo now gotta show this is preserved...
;; ;show that new satisfies this?
;; (defund good-memoryp2 (mem)
;;   (and (good-memoryp mem)
;;        (equal (signed-byte-p 29 (caddr mem))
;;               (cdar mem))
;;        (equal (MEM::|_LOG2| (+ -1 (CADR mem)))
;;               (CADDR mem))
;;        ))

;moved to records
#+joe
(defthm rkeys-iff-when-wfr
  (iff (set::rkeys r)
       (not (equal r nil)))
  :hints (("Goal" :in-theory (enable rkeys ACL2->RCD))))

;move to fast memory book
;crud.  only true if keys didn't sneak into the wrong part (keys for the memory sneaking into the record or vice versa...)
;crud.  good-memoryp may also have to say that the fast flag is right?
(defthm empty-domain-means
  (implies (and (not (mem::domain fr))
                (good-memoryp fr))
           (equal fr (mem::new (mem::size fr))))
  :otf-flg t
  :hints (("subgoal 2" :in-theory (enable MEM::|_MEMORY-P|
                                          MEM::|_MEMORY-FIX|
                                          MEM::|_MEMORY-SIZE|
                                          MEM::MEMORY-P
                                          MEM::SIZE
                                          GOOD-MEMORYP
                                          MEM::MEM-TREE-DOMAIN
                                          MEM::|_MEMORY-DEPTH|
                                          ))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable ;MEM::|_MEMORY-P|

                       MEM::MEM-TREE-DOMAIN
                       mem::domain
                       mem::new
                       good-memoryp
                       MEM::MEMORY-P
;MEM::SIZE

                       MEM::|_MEMORY-P|
                       MEM::|_MEMORY-FIX|
                       MEM::|_MEMORY-SIZE|
                       MEM::|_MEMORY-DEPTH|
                       MEM::MEMORY-P
                       MEM::SIZE
;                       GOOD-MEMORYP2
                       GOOD-MEMORYP
                       MEM::MEM-TREE-DOMAIN
                       )))
  :rule-classes nil)

;bzo rename?
(defthm size-of-store
  (implies (good-memoryp fr)
           (equal (mem::size (gacc::memory-clr a fr))
                  (mem::size fr)))
  :hints (("Goal" :in-theory (e/d (GACC::MEMORY-CLR
                                   GACC::WR
                                   GOOD-MEMORYP)
                                  (WR-OF-0-IS-CLR)))))

(defthm wf-fr-of-memory-clr
  (implies (and (wf-fr tr)
                ;;a ;that is, a is not nil
                )
           (wf-fr (gacc::memory-clr a tr)))
  :hints (("Goal" :in-theory (e/d (gacc::memory-clr) (;wf-fr-of-wr
                                                      GACC::WF-USBP8
                                                      wr-of-0-is-clr)))))


;; (defthm check-fr-keys-of-memory-clr
;;   (implies (and (wf-fr fr)
;;                 ;(set::in key (mem::domain fr))
;;                 )
;;            (check-fr-keys (mem::domain fr) (gacc::memory-clr key fr)))
;;   :hints (("Goal" :cases ((set::in key (mem::domain fr)))
;;            :use (:instance wf-fr-of-wr
;;                                   (a key)
;;                                   (v 0)
;;                                   (tr fr)
;;                                   )
;;            :in-theory (e/d (gacc::memory-clr) (wf-fr-of-wr
;;                                                GACC::WF-USBP8
;;                                                wr-of-0-is-clr)))))

(defthm domain-not-nil-when-load-not-nil
  (implies (and (mem::load a mem)
                (force (GOOD-MEMORYP MEM)) ;drop?
                )
           (mem::domain mem))
  :hints (("Goal" :in-theory (disable mem::store-of-same-load
                                      MEM::STORE-EQUAL-REWRITE)
           :use (:instance mem::store-of-same-load (mem::mem mem)))))


(defthmd load-iff
  (implies (force (GOOD-MEMORYP MEM)) ;drop?
           (iff (MEM::LOAD a mem)
                (set::in a (mem::domain mem)))))

(theory-invariant (incompatible (:rewrite NOT-IN-DOMAIN-MEANS-LOAD-IS-NIL2) (:rewrite load-iff)))

(defthm load-of-head-of-domain-iff
  (implies (force (GOOD-MEMORYP MEM)) ;drop?
           (iff (mem::load (set::head (mem::domain mem)) mem)
                (not (set::empty (mem::domain mem)))))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (load-iff)
                                  ( mem::store-of-same-load
                                    NOT-IN-DOMAIN-MEANS-LOAD-IS-NIL
                                    NOT-IN-DOMAIN-MEANS-LOAD-IS-NIL2
                                    MEM::STORE-EQUAL-REWRITE))
                     ;          :use (:instance mem::store-of-same-load (a (SET::HEAD (MEM::DOMAIN mem))) (mem::mem mem))
           )))


(defthm mypush-aux-of-mylift-aux
  (implies (and (wf-fr fr)
                (equal rkeys (mem::domain ;;rkeys
                              fr)))
           (equal (mypush-aux rkeys
                              (mylift-aux rkeys fr)
                              (mem::size fr)
                              )
                  fr))
  :hints (("subgoal *1/1" :use (:instance empty-domain-means))
          ("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d ( ;wfr
                            CHECK-FR-KEY
                            CHECK-FR-KEYS
                            mypush-aux mylift-aux)
                           ( ;gacc::wr==r!
                            ))
           :induct (ind rkeys fr)
           )))

;for dave
(defthm mypush-of-mylift
  (implies (wf-fr tr)
           (equal (mypush (mylift tr) (mem::size tr))
                  tr))
  :hints (("Goal" :in-theory (enable MYPUSH mylift))))

(defthm mypush-of-mylift-matches-better
  (implies (and (acl2::wf-fr tr)
                (equal sz (mem::size tr)))
           (equal (acl2::mypush (acl2::mylift tr) sz)
                  tr))
  :hints (("Goal" :in-theory (enable acl2::mypush acl2::mylift))))

(defun typed-fix-aux (keys r)
  (declare (xargs :verify-guards nil))
  (if (set::empty keys)
      nil ;the empty record
    (s ;mem::store
     (set::head keys)
       (val-fix (g (set::head keys) r))
       (typed-fix-aux (set::tail keys) r))))

;takes a true record and fixes it by dropping all pairs whose value has a
;loghead8 of 0 and chopping the value on all pairs whose value is not a usb8.
(defund typed-fix (r)
  (declare (xargs :verify-guards nil))
  (typed-fix-aux (set::rkeys r) r))


(DEFTHM RKEYS-OF-WR-alt
  (IMPLIES (wf-fr tr)
           (EQUAL (mem::domain ;RKEYS
                   (GACC::WR A V TR))
                  (IF (GACC::WF-USBP8 (mem::load ;G
                                       A TR))
                      (IF (GACC::USBP8-ZP V)
                          (IF (CDR (mem::load ;G
                                    A TR))
                              (SET::INSERT A (mem::domain ;RKEYS
                                              TR))
                              (SET::DELETE A (mem::domain ;RKEYS
                                              TR)))
                          (SET::INSERT A (mem::domain ;RKEYS
                                          TR)))
                      (IF (GACC::USBP8-ZP V)
                          (mem::domain ; RKEYS
                           TR)
                          (SET::INSERT A (mem::domain ;RKEYS
                                          TR))))))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (GACC::WR GACC::MEMORY-CLR) (WR-OF-0-IS-CLR)))))


;; (SET::RKEYS (MYPUSH-AUX (SET::RKEYS R) R))

;; ;crikey!  this (wfkeyed 3) equals t !

;; (thm
;;  (not (wfkeyed (s nil v r)))
;;  :otf-flg t
;;  :hints (("Goal" ;:cases ((IFRP R))
;;           :in-theory (enable wfkeyed s ACL2->RCD))))

;; (thm
;;  (NOT (WFKEYED (GACC::WR NIL V TR)))
;;  :otf-flg t
;;  :hints (("Goal" :in-theory (enable WFKEYED GACC::WR))))

;; (thm
;;  (NOT (WFR (GACC::WR NIL V TR)))
;;  :hints (("Goal" :in-theory (enable wfr))))

;; (DEFTHM WFR-OF-WR-strong
;;   (IMPLIES (WFR TR)
;;            (equal (WFR (GACC::WR A V TR))
;;                   (WFKEY A)))
;;   :HINTS (("Goal" :IN-THEORY (E/D (wfkey) NIL))))



(local
 (defun ind3 (keys r)
   (declare (xargs :verify-guards nil))
   (if (or (not (set::setp keys))
           (set::empty keys))
       (list keys r)
     (ind3 (set::tail keys)
           (CLR (SET::HEAD (SET::RKEYS R)) r) ;
    ;(gacc::wr (set::head keys) (gacc::rd (set::head keys) tr) tr)
           ))))




;; ;bbzo - in the record library but local there!
;; ;(skip-proofs
;; ;bzo dup from records book
;; (defthm wfkeyed-s-aux
;;          (implies (and (not (ifrp r))
;;                        (rcdp r)
;;                        (wfkeyed r)
;;                        (wfkey a))
;;                   (wfkeyed (s-aux a v r)))
;;          :hints (("goal" :induct (s-aux a v r))))
;; ;)

;; (defthm wfkeyed-of-s
;;   (implies (and (wfr r)
;;                 (wfkey key)
;;                 (wfkeyed r))
;;            (wfkeyed (s key v r)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :use (:instance S-PRESERVES-WFR (a key))
;;            :in-theory (e/d (wfr  WFKEY RCD->ACL2
;;                                  ) (S-PRESERVES-WFR)))))


(defthmd g-when-not-g-of-cdr
  (implies (and (not (g key (cdr r)))
                (wfr r)
                )
           (equal (g key r)
                  (if (equal key (caar r))
                      (cdar r)
                    nil)))
  :hints (("Goal" :in-theory (enable g)
           :do-not '(generalize eliminate-destructors))))

;could improve other lemmas (e.g., lemmas above this and the analogue of this in tr-path-connection) using a similar hint?
(defthm g-when-not-in-rkeys
  (implies (not (set::in key (set::rkeys r)))
           (equal (g key r)
                  nil))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :use (:instance S-SAME-G (a key))
           :in-theory (e/d ( ) (S-SAME-G S==R EQUAL-S-RECORD-EQUALITY)))))

;; subset is enough?
;; (thm
;;  (equal (SET::RKEYS (MYPUSH-AUX keys R))
;;         ..


(defthm clr-of-typed-fix-aux-irrel
  (implies (not (set::in key keys))
           (equal (clr
                   key (TYPED-FIX-AUX keys R))
                  (TYPED-FIX-AUX keys (clr key r))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm good-memoryp-of-mypush-aux
  (implies (posp size)
           (good-memoryp (mypush-aux keys r size))))

(defthm not-in-of-rkeys-of-mypush-aux
  (implies (and (NOT (SET::IN key keys))
;                (set::all<non-nil> keys) ;drop?
                (posp size)
                (wfr r))
           (NOT (SET::IN key (mem::domain ;RKEYS
                              (MYPUSH-AUX keys R size)))))
  :hints (("Goal" :in-theory (e/d (GACC::WR)
                                  (  ;disables for efficiency -why are things suddenyl so slow?
;                                           G-OF-MYPUSH-AUX-WHEN-NOT-IN-KEYS
                                           ))
           :do-not '(generalize eliminate-destructors))))


;bzo rename stuff like this...
(defthm g-of-mypush-aux-when-not-in-keys
  (implies (not (set::in key keys))
           (equal (mem::load ;g
                   key (mypush-aux keys r size))
                  nil))
  :hints (("Goal" :in-theory (e/d (GACC::WR)
                                  (NOT-IN-DOMAIN-MEANS-LOAD-IS-NIL
                                   NOT-CHECK-FR-KEYS-1))
           :do-not '(generalize eliminate-destructors))))

(local (in-theory (disable SET::SUBSET))) ;bzo make non-local?
(local (in-theory (disable SET::DELETE)))

;moved to records
#+joe
(defthm nil-not-in-keys
  (implies (wfkeyed tr)
           (not (bag::memberp nil (alist::keys tr))))
  :hints (("Goal" :in-theory (enable wfkeyed alist::keys))))

;moved to records?
#+joe
(defthm all-non-nil-of-rkeys
  (implies (wfr tr)
           (set::all<non-nil> (set::rkeys TR)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable set::rkeys rkeys wfr))))

;too strong?
;; (thm
;;  (equal (mem::domain (mypush-aux keys r size))
;;         (set::intersect keys (set::rkeys r)))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;           :in-theory (enable ;SET::SUBSET
;;                       SET::PICK-A-POINT-SUBSET-STRATEGY
;;                       ))))

(defthm domain-of-mypush-aux-subset
  (implies (posp size)
           (set::subset (mem::domain (mypush-aux keys r size))
                        (set::intersect keys (set::rkeys r))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable ;SET::SUBSET
                       SET::PICK-A-POINT-SUBSET-STRATEGY
                       ))))


(defthm mylift-of-mypush-helper
  (implies (and; (wfr r)
;                (set::all<non-nil> keys) ;drop?
                (posp size)
                (equal keys (set::rkeys r)))
           (equal (mylift-aux (mem::domain ;rkeys
                               (mypush-aux keys r size))
                              (mypush-aux keys r size))
                  (typed-fix-aux keys r)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (disable SET::IN
                               G-WHEN-NOT-IN-RKEYS
                               SET::ALL<NON-NIL>
                               SET::ALL<NOT-NON-NIL>
                               )
           :induct (ind3 keys r)
           )))

(defthm mylift-of-mypush
  (implies (posp size)
           (equal (mylift (mypush r size))
                  (typed-fix r)))
  :hints (("Goal" :in-theory (enable mypush mylift TYPED-FIX))))

;bzo rename?
(defun all-vals-okay-aux (keys r)
  (declare (xargs :verify-guards nil))
  (if (set::empty keys)
      t
    (and (unsigned-byte-p 8(g (set::head keys) r))
         (not (equal 0 (g (set::head keys) r)))
         (all-vals-okay-aux (set::tail keys) r))))

(defthm all-vals-okay-aux-of-clr-irrel
  (implies (not (set::in key keys))
           (equal (all-vals-okay-aux keys (clr key r))
                  (all-vals-okay-aux keys r)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;          :induct (ind3 keys r)
           )))

(defthm typed-fix-does-nothing-helper
  (implies (and (all-vals-okay-aux keys r)
                (equal keys (set::rkeys r))
                (wfr r)
                )
           (equal (typed-fix r)
                  r))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable TYPED-FIX)
           :induct (ind3 keys r))))

;;bzo Dave, what do we want to call this?
(defund well-typed-record (r)
  (declare (xargs :verify-guards nil))
  (and (wfr r)
       (all-vals-okay-aux (set::rkeys r) r)))

;for Dave
;bzo is this stuff common to both tr- and fr-?
(defthm typed-fix-does-nothing
  (implies (well-typed-record r)
           (equal (typed-fix r)
                  r))
  :hints (("Goal" :in-theory (enable typed-fix well-typed-record)
           :do-not '(generalize eliminate-destructors))))

(defthm good-memoryp-implies-non-nil-hack
  (implies (not x)
           (not (acl2::good-memoryp x))))

(defthm wr-non-nil-when-good-memoryp
  (implies (acl2::good-memoryp m)
           (GACC::WR a v m))
  :otf-flg t
  :hints (("Goal"
           :use ((:instance acl2::good-memoryp-of-store
                            (acl2::a a)
                            (acl2::v (CDR (MEM::LOAD A M)))
                            (acl2::mem m))
                 (:instance acl2::good-memoryp-of-store
                            (acl2::a a)
                            (acl2::v (CONS (ACL2::LOGHEAD 8 V)
                                           (MEM::LOAD A M)))
                            (acl2::mem m))
                 (:instance acl2::good-memoryp-of-store
                            (acl2::a a)
                            (acl2::v (CONS (ACL2::LOGHEAD 8 V)
                                           (CDR (MEM::LOAD A M))))
                            (acl2::mem m)))

           :in-theory (e/d (GACC::WR) (acl2::good-memoryp-of-store)))))
;; (thm
;;  (ACL2::MYPUSH-AUX keys (set::rkeys r) size))

;; (thm
;;  (iff (ACL2::MYPUSH r size)
;;       t)
;;  :hints (("Goal" :in-theory (enable ACL2::MYPUSH))))

(defthm acl2::good-memoryp-of-mypush
  (implies (posp acl2::size) ;drop?
           (acl2::good-memoryp (acl2::mypush acl2::r acl2::size)))
  :hints (("Goal" :in-theory (enable acl2::mypush))))

(defthm mypush-non-nil
  (implies (posp acl2::size)
           (acl2::mypush acl2::r acl2::size))
  :rule-classes (:rewrite :type-prescription) ;is t-p smart enough to know about posp?
  :hints (("Goal" :use (:instance acl2::good-memoryp-of-mypush)
           :in-theory (disable acl2::good-memoryp-of-mypush))))





;; (thm
;;  (equal (clr key (acl2::mylift-aux dom m))
;;         (acl2::mylift-aux (set::delete key dom)
;;                           (mem::clear p m)))
;;  :hints (("Goal" :in-theory (enable acl2::mylift-aux))))

(defthm domain-of-memory-clr
  (implies (good-memoryp m)
           (equal (mem::domain (gacc::memory-clr a m))
                  (IF (GACC::WF-USBP8 (MEM::LOAD A m))
                      (IF (CDR (MEM::LOAD A m))
                          (SET::INSERT A (MEM::DOMAIN m))
                          (SET::DELETE A (MEM::DOMAIN m)))
                      (MEM::DOMAIN m))))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (mem::clear gacc::memory-clr) (wr-of-0-is-clr)))))

(defthm rd-of-clear
  (equal (gacc::rd key1 (mem::clear key2 m))
         (if (equal key1 key2)
             0
           (gacc::rd key1 m)))
  :hints (("Goal" :in-theory (enable gacc::rd))))

(defthm mylift-aux-of-clear-irrel
  (implies (not (set::in key keys))
           (equal (mylift-aux keys (mem::clear key m))
                  (mylift-aux keys m)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable ))))

(defthm clr-of-mylift
  (implies (good-memoryp m)
           (equal (clr key (acl2::mylift m))
                  (acl2::mylift ( ;gacc::memory-clr
                                 mem::clear
                                 key m))))
  :hints (("Goal" :in-theory (enable acl2::mylift))))

(defthm clear-of-wr
  (equal (mem::clear a (gacc::wr a v r))
         (mem::clear a r))
  :hints (("Goal" :in-theory (enable gacc::wr))))

(defthm clear-of-wr-diff
  (implies (not (equal a b))
           (equal (mem::clear a (gacc::wr b v r))
                  (gacc::wr b v (mem::clear a r))))
  :hints (("Goal" :in-theory (enable gacc::wr))))

(defthm clear-of-wr-both
  (equal (mem::clear a (gacc::wr b v r))
         (if (equal a b)
             (mem::clear a r)
           (gacc::wr b v (mem::clear a r))))
  :hints (("Goal" :in-theory (enable gacc::wr))))


;bzo move to memory
(defthm clear-of-new
  (equal (mem::clear key (mem::new size))
         (mem::new size))
  :hints (("Goal" :in-theory (enable mem::clear))))

(defthm clear-of-mypush-aux-irrel
  (implies (not (set::in key keys))
           (equal (MEM::CLEAR key (ACL2::MYPUSH-AUX keys R SIZE))
                  (ACL2::MYPUSH-AUX keys R SIZE))))

(defthm clear-of-mypush-aux
  (equal (MEM::CLEAR KEY (ACL2::MYPUSH-AUX keys R SIZE))
         (ACL2::MYPUSH-AUX keys (acl2::clr key R) SIZE))
  :hints (("Goal" :in-theory (enable set::delete))))

(defthm clear-of-mypush
  (implies (posp size)
           (equal (mem::clear key (acl2::mypush r size))
                  (acl2::mypush (acl2::clr key r) size)))
  :hints (("Goal" :in-theory (enable acl2::mypush))))

;; see proof in shell
(defthm all-vals-okay-aux-of-delete
  (implies (acl2::all-vals-okay-aux keys m)
           (acl2::all-vals-okay-aux (set::delete key keys) m))
  :hints (("Goal" :in-theory (enable set::delete))))

;bzo same for s?
(defthm well-typed-record-of-clr
  (implies (acl2::well-typed-record m)
           (acl2::well-typed-record (acl2::clr key m)))
  :hints (("Goal" :in-theory (e/d (acl2::well-typed-record) (;clrp-singleton-back
                                                             )))))
(in-theory (disable WF-FR))

(defthm wf-fr-of-new
  (implies (posp size)
           (wf-fr (mem::new size)))
  :hints (("Goal" :in-theory (enable wf-fr))))

;; (thm
;;  (implies (check-fr-keys keys1 r)
;;           (check-fr-keys keys1 (gacc::wr a v r)))
;;  :hints (("Goal" :in-theory (e/d (gacc::wr) (check-fr-keys)))))

;; (thm
;;  (IMPLIES (AND (GOOD-MEMORYP R)
;;                (CHECK-FR-KEYS keys2 ;;(MEM::DOMAIN R)
;;                               R)
;;                ;(POSP SIZE)
;;                (set::subset keys1 keys2)
;;                )
;;           (CHECK-FR-KEYS keys1 (MYPUSH-AUX keys2 R SIZE))))

(defthm wf-fr-of-mypush-aux
  (implies (posp size)
           (wf-fr (mypush-aux keys2 r size)))
  :hints (("Goal" :in-theory (enable check-fr-keys))))

(defthm wf-fr-of-mypush
  (implies (posp size)
           (wf-fr (mypush r size)))
  :hints (("Goal" :use (:instance wf-fr-of-MYPUSH-AUX (keys2 (set::rkeys R)))
           :in-theory (e/d (mypush wf-fr) (wf-fr-of-MYPUSH-AUX)))))

;bzo or put this elsewhere and don't include paths for this book (there's not much pathy stuff here?)
(defthm gp-of-mylift-singleton
  (equal (cpath::gp (list a) (acl2::mylift tr))
         (if (set::in a (mem::domain tr))
             (acl2::loghead 8 (gacc::rd a tr))
           nil))
  :hints (("Goal" :in-theory (enable cpath::gp))))

;bzo same for sp?
(defthm well-typed-record-of-clrp-singleton
  (implies (acl2::well-typed-record m)
           (acl2::well-typed-record (cpath::clrp (list key) m)))
  :hints (("Goal" :in-theory (e/d (cpath::clrp-singleton-becomes-clr)
                                  (cpath::clr-becomes-clrp-singleton
                                   )))))

(defthm clrp-of-mylift-singleton
  (implies (acl2::good-memoryp m)
           (equal (cpath::clrp (list key) (acl2::mylift m))
                  (acl2::mylift (mem::clear key m))))
  :hints (("Goal" :in-theory (e/d (cpath::clrp-singleton-becomes-clr)
                                  (cpath::SP==R ;bzo looped
                                   cpath::clr-becomes-clrp-singleton)))))

(defthm use-check-fr-keys-8
  (implies (and (acl2::check-fr-keys keys tr)
                (set::in a keys)
                (mem::load a tr)
                )
           (acl2::unsigned-byte-p 8 (car (mem::load a tr))))
  :hints (("Goal" :in-theory (enable acl2::check-fr-keys
                                     acl2::check-fr-key))))

(defthm use-check-fr-keys-9
  (implies (and (acl2::check-fr-keys keys tr)
                (set::in a keys)
                (mem::load a tr)
                )
           (NOT (GACC::USBP8-ZP (CAR (MEM::LOAD A TR)))))
  :hints (("Goal" :in-theory (enable acl2::check-fr-keys
                                     GACC::USBP8-ZP
                                     acl2::check-fr-key))))

(defthm use-check-fr-keys-10
  (implies (and (acl2::check-fr-keys keys tr)
                (set::in a keys)
                (mem::load a tr)
                )
           (NOT (equal 0 (CAR (MEM::LOAD A TR)))))
  :hints (("Goal" :in-theory (enable acl2::check-fr-keys
                                     GACC::USBP8-ZP
                                     acl2::check-fr-key))))

;disable? ;move?
(defthm rd-not-equal-0-helper
  (implies (and (acl2::wf-fr tr)
                (set::in a (mem::domain tr)))
           (not (equal 0 (gacc::rd a tr))))
  :hints (("Goal" :cases ((set::in a  (mem::domain tr)))
           :in-theory (enable gacc::rd acl2::wf-fr))))

;move?
(defthm rd-is-0
  (implies (and (not (set::in a (mem::domain tr)))
                (acl2::good-memoryp tr))
           (equal (gacc::rd a tr) 0))
  :hints (("Goal" :in-theory (enable gacc::rd acl2::not-in-domain-means-load-is-nil))))

(defthm wf-fr-implies-good-memoryp
  (implies (acl2::wf-fr tr)
           (acl2::good-memoryp tr))
  :hints (("Goal" :in-theory (enable acl2::wf-fr))))

;better version - kill the other?

(defthm g-of-mylift-2
  (implies (acl2::wf-fr tr)
           (equal (g a (acl2::mylift tr))
                  (acl2::val-fix (acl2::loghead 8 (gacc::rd a tr)))))
  :hints (("Goal" :in-theory (enable ACL2::NOT-IN-DOMAIN-MEANS-LOAD-IS-NIL))))

(in-theory (disable acl2::g-of-mylift))
(in-theory (disable acl2::val-fix))



;will this defeat the purpose of keeping val-fix closed?
(defthm val-fix-iff
  (iff (acl2::val-fix v)
       (not (equal 0 (acl2::loghead 8 v))))
  :hints (("Goal" :in-theory (enable acl2::val-fix))))


;bzo replace the other!
(defthm acl2::rd-of-mypush-better
  (equal (gacc::rd acl2::a (acl2::mypush acl2::r acl2::size))
         (acl2::loghead 8 (g acl2::a acl2::r)))
  :hints (("Goal" :in-theory (enable acl2::mypush))))

(in-theory (disable acl2::rd-of-mypush))

;bzo replace the other!
(defthm acl2::rkeys-of-wr-alt-2
  (implies (acl2::wf-fr acl2::tr)
           (equal (mem::domain (gacc::wr acl2::a acl2::v acl2::tr))
                  (if (gacc::usbp8-zp acl2::v)
                      (set::delete acl2::a (mem::domain acl2::tr))
                    (set::insert acl2::a (mem::domain acl2::tr)))))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (gacc::wr gacc::memory-clr
                                            ACL2::WF-FR
                                            )
                                  (acl2::wr-of-0-is-clr)))))

(in-theory (disable acl2::rkeys-of-wr-alt))

(defthm wf-usbp8-of-load
  (implies (acl2::wf-fr acl2::m)
           (iff (gacc::wf-usbp8 (mem::load acl2::key acl2::m))
                (mem::load acl2::key acl2::m)))
  :hints (("Goal" :in-theory (enable acl2::wf-fr))))

(defthm use-check-fr-keys-another
  (implies (and (set::in acl2::key keys)
                (acl2::check-fr-keys keys acl2::m))
           (not (cdr (mem::load acl2::key acl2::m))))
  :hints (("Goal" :in-theory (enable acl2::check-fr-keys))))

(defthm not-cdr-load
 (implies (ACL2::WF-FR ACL2::M)
          (not (CDR (MEM::LOAD ACL2::KEY ACL2::M))))
 :hints (("Goal" :cases ((set::in ACL2::KEY (MEM::DOMAIN ACL2::M)))
          :use (:instance use-check-fr-keys-another
                          (keys (MEM::DOMAIN ACL2::M))
                          )
          :in-theory (e/d (ACL2::WF-FR ACL2::CHECK-FR-KEYS) (use-check-fr-keys-another)))))

;bzo replace the other?
(defthm acl2::clr-of-mylift-better
  (implies ;(acl2::good-memoryp acl2::m)
   (acl2::wf-fr acl2::m)
           (equal (acl2::clr acl2::key (acl2::mylift acl2::m))
                  (acl2::mylift (gacc::memory-clr acl2::key acl2::m))))
  :otf-flg t
  :hints (("Goal" :cases ((SET::in ACL2::KEY (MEM::DOMAIN ACL2::M)))
           :use (:instance acl2::mylift-irrel
                           (acl2::key ACL2::KEY)
                           (acl2::keys (MEM::DOMAIN ACL2::M))
                           (acl2::tr acl2::m))

           :in-theory (e/d (acl2::mylift) (acl2::mylift-irrel)))))

(in-theory (disable acl2::clr-of-mylift))

(defthm memory-clr-of-mypush
  (equal (gacc::memory-clr key (acl2::mypush r size))
         (acl2::mypush (acl2::clr key r) size))
  :hints (("Goal" :in-theory (enable acl2::mypush)
           :do-not '(generalize eliminate-destructors))))
