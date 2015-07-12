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

;The book provides a mapping between typed records and the nested record structures accessed by paths.

;bzo some of this stuff should be moved to paths..

;; (acl2::add-include-book-dir :paths "/rfs/proj/milsrtos/Users/ewsmith/new4/4/paths/")
;; (acl2::add-include-book-dir :gacc "/rfs/proj/milsrtos/Users/ewsmith/new4/4/gacc/")
;; (acl2::add-include-book-dir :records "/rfs/proj/milsrtos/Users/ewsmith/new4/4/records/")

(include-book "mem")
(include-book "../paths/path")
(include-book "../records/domain")
(include-book "../osets/conversions")
(include-book "../osets/quantify")

;; [Jared] reworking this to be redundant with coi/records/set-domain.lisp
;; (defun set::rkeys (r)
;;   (list::2set (rkeys r)))
#!SET
(defun rkeys (r)
  (declare (type t r))
  (list::2set (acl2::rkeys r)))


;;
;; mypush (turn a record into a typed-record)
;;

(defun mypush-aux (keys r)
  (if (set::empty keys)
      nil ;the empty typed record
    (gacc::wr (set::head keys)
              (g (set::head keys) r)
              (mypush-aux (set::tail keys) r))))

(defun mypush (r)
  (mypush-aux (set::rkeys r) r))


(defthm rd-of-mypush-aux
  (equal (gacc::rd a (mypush-aux rkeys r))
         (if (set::in a rkeys)
             (loghead 8 (g a r))
           0)))


(defthm rd-of-mypush
  (equal (gacc::rd a (mypush r))
         (if (set::in a (set::rkeys r))
             (loghead 8 (g a r))
           0)))

(defthm memory-clr-of-mypush-aux
  (equal (gacc::memory-clr key (mypush-aux rkeys r))
         (mypush-aux rkeys (clr key r))))

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


(defun my-ind (a rkeys r)
  (if (set::empty rkeys)
      (list a rkeys r)
    (if (equal a (set::head (set::insert a rkeys)))
        (list a rkeys r)
      (my-ind a (set::tail rkeys) (s (set::head rkeys) (g (set::head rkeys) r) r)))))



;clean up conclusion?
(defthmd car-of-insert
  (equal (CAR (SET::INSERT a x))
         (COND ((SET::EMPTY X) A)
               ((EQUAL (SET::HEAD X) A) (SET::HEAD X))
               ((<< A (SET::HEAD X)) A)
               (T (SET::HEAD X))))
  :hints (("Goal" :expand (SET::INSERT A X)
           :in-theory (enable SET::INSERT SET::HEAD))))

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



(defthm not-in-when-<<-car
 (IMPLIES (AND ;A (SET::SETP S)
               ;(NOT (EQUAL (CAR S) A))
               (<< A (CAR S))
               ;(CONSP S)
               )
          (not (set::in a s)))
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
          :expand ((SET::EMPTY S)
                   (SET::SETP S))
          :in-theory (enable SET::HEAD set::tail))))



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
  (equal (mypush-aux (set::insert a rkeys) r)
         (if (set::in a rkeys)
             (mypush-aux rkeys r)
           (gacc::wr a (g a r) (mypush-aux rkeys r))))
  :otf-flg t
  :hints (("Goal" :induct (my-ind a rkeys r)
           :expand ((MYPUSH-AUX (SET::INSERT A RKEYS) R))
           :in-theory (disable GACC::WR==R!
                               )
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))))


(defthm memory-clr-of-mypush-aux2
  (equal (gacc::memory-clr key (mypush-aux rkeys r))
         (mypush-aux (set::delete key rkeys) r))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


;rename to say insert
(defthm mypush-aux-of-cons-irrel
  (implies (not (g key r))
           (equal (mypush-aux (set::insert key rkeys) r)
                  (mypush-aux rkeys r)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))




;drop?
(defthm mypush-aux-of-insert-irrel-of-clr
  (equal (mypush-aux (set::insert key rkeys) (clr key r))
         (mypush-aux rkeys (clr key r)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


(defthm mypush-irrel
  (implies (not (set::in key rkeys))
           (equal (mypush-aux rkeys (clr key r))
                  (mypush-aux rkeys r)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


(defthm mypush-aux-of-clr
  (equal (mypush-aux rkeys (clr a r))
         (mypush-aux (set::delete a rkeys) r))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


(defthm mypush-irrel2
  (implies (not (set::in key rkeys))
           (equal (mypush-aux rkeys (s key v r))
                  (mypush-aux rkeys r)))
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
  (equal (mypush (s a v r))
         (gacc::wr a v (mypush r)))
  :otf-flg t)

;for dave
(defthm mypush-of-sp
  (equal (mypush (cpath::sp (list a) v r))
         (gacc::wr a v (mypush r)))
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
(defun mylift (tr)
  (mylift-aux (set::rkeys tr) tr))

(defthm rkeys-of-wr
  (equal (set::rkeys (gacc::wr a v tr))
         (if (gacc::wf-usbp8 (g a tr))
             (if (gacc::usbp8-zp v)
                 (if (cdr (g a tr))
                     (set::insert a (set::rkeys tr))
                   (set::delete a (set::rkeys tr)))
               (set::insert a (set::rkeys tr)))
           (if (gacc::usbp8-zp v)
               (set::rkeys tr)
             (set::insert a (set::rkeys tr)))))
  :hints (("Goal" :expand ((gacc::wr a v tr))
;          :induct nil
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))))

(defthm g-of-mylift-aux
  (equal (g a (mylift-aux rkeys tr))
         (if (set::in a rkeys)
             (loghead 8 (gacc::rd a tr))
           nil)))


(defthm g-of-mylift
  (equal (g a (mylift tr))
         (if (set::in a (set::rkeys tr))
             (loghead 8 (gacc::rd a tr))
           nil)))

(defun val-fix (v)
  (if (equal 0 (loghead 8 v))
      nil
     (loghead 8 v)))

(defthm wr-of-0-is-clr
  (implies (EQUAL (LOGHEAD 8 V) 0)
           (equal (GACC::WR A V TR)
                  (gacc::memory-clr A TR))))


;bzo improve CLR-OVER-CLR?

(defthm clr-of-clr-match-hack
  (IMPLIES (EQUAL (CLR b r1)
                  (CLR b r2))
           (EQUAL (equal (CLR b (CLR a r1))
                         (CLR b (CLR a r2)))
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

(defthm delete-of-head
  (equal (set::delete (set::head s) s)
         (if (set::setp s)
             (set::tail s)
           nil ;the empty set - is there a function for that?
           ))
  :hints (("Goal" :in-theory (enable SET::EMPTY))))

;could be expensive?
(defthm empty-means-tail-nil
  (implies (set::empty s)
           (equal (set::tail s)
                  nil))
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


;bzo bad name? really this checks the values?
(defun check-tr-keys (keys tr)
  (if (set::empty keys)
      t
    (let* ((val (g (set::head keys) tr)))
      (and (equal nil (cdr val)) ;(equal 1 (len val))
           (unsigned-byte-p 8 (car val))
           (not (equal 0 (car val)))
           (check-tr-keys (set::tail keys) tr)
           ))))

;; ;drop?
;; (defun wfr-weak (r)
;;   (and (rcdp r)
;;        (not (ifrp r)) ;;should really just use a typed version of ifrp?
;;        ))


(defun wf-tr (tr)
  (and ;;(wfr-weak tr) ;;
       (wfr tr)
       (check-tr-keys (set::rkeys tr) tr)))

(defun wf-tr-weak (tr)
  (and ;;(wfr-weak tr) ;;
;       (wfr tr)
       (check-tr-keys (set::rkeys tr) tr)))

(defthm mylift-of-wr-1
  (implies (and (wf-tr-weak tr)
                (not (EQUAL 0 (LOGHEAD 8 V))))
           (equal (mylift (gacc::wr a v tr))
                  (s a (val-fix v) (mylift tr))))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable ;gacc::wr
                       ))))

(theory-invariant (incompatible (:rewrite WR-OF-0-IS-CLR) (:definition GACC::MEMORY-CLR)))

(defthm cdr-of-g-nil-when-in-keys
  (implies (and (check-tr-keys keys tr)
                (set::in k keys)
                )
           (not (cdr (g k tr))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm sfix-of-rkeys
  (equal (SET::SFIX (SET::RKEYS TR))
         (SET::RKEYS TR))
  :hints (("Goal" :in-theory (enable RKEYS))))

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

(defthm wf-tr-cancellations
  (implies (wf-tr r)
           (and (equal (rcd->acl2 r) r)
                (equal (acl2->rcd r) r)))
  :hints (("Goal" :in-theory (enable rcd->acl2 acl2->rcd))))


;; (defthm wf-tr-implies-wf-tr-of-cdr
;;   (implies (wf-tr tr)
;;            (wf-tr (cdr tr)))
;;   :otf-flg t
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :expand (ifrp (cdr tr))
;;            :in-theory (enable wfr ifrp rcdp wfkeyed))))


(defthm not-consp-g-of-cdr-but-consp-g
  (IMPLIES (AND (NOT (CONSP (G A (CDR TR))))
                (CONSP (G A TR))
                (WFR TR) ;was wfr-weak
                )
           (EQUAL (CAAR TR) A))
  :hints (("Goal" :in-theory (enable g))))

(defthm consp-g-means-in-keys
  (implies (and (consp (g a tr))
                (wfr tr)
                )
           (set::in a (set::rkeys tr)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))
;;         :in-theory (enable rkeys key-set))))

(defthm g-of-caar
  (implies (wfr tr)
           (equal (g (caar tr) tr)
                  (cdar tr)
                  ))
  :hints (("Goal" :in-theory (enable g)
           :do-not '(generalize eliminate-destructors))))

(defthm cons-g-cdr-means-consp-g
  (implies (and (consp (g a (cdr tr)))
                (wfr tr))
           (consp (g a tr)))
  :hints (("Goal" :in-theory (enable g wfr))))

;bzo disable?
(defthm cdar-of-wfr-non-nil
  (implies (and (consp tr)
                (wfr tr))
           (cdar tr))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand (rcdp tr)
           :in-theory (enable wfr rcdp wfkeyed wfkey))))

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
           (equal (GACC::RD key1 (S KEY2 V TR))
                  (GACC::RD key1 TR)))
  :hints (("Goal" :in-theory (enable GACC::RD))))

(defthm mylift-irrel2
  (implies (not (set::in key rkeys))
           (equal (mylift-aux rkeys (s key v tr))
                  (mylift-aux rkeys tr)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


;; (thm
;;  (IMPLIES (AND (WFR TR)
;;                ;(CHECK-TR-KEYS (SET::RKEYS TR) TR)
;;                ;(NOT (CONSP (G A TR)))
;;                )
;;           (EQUAL (MYLIFT-AUX (SET::DELETE A (SET::RKEYS TR))
;;                              (GACC::WR A 0 TR))
;;                  (MYLIFT-AUX (SET::RKEYS TR)
;;                              (GACC::WR A 0 TR)))))

(defthmd check-tr-keys-lemma
  (IMPLIES (and (CHECK-TR-KEYS keys TR)
                (set::in a keys)
                (consp tr))
           (NOT (EQUAL (LOGHEAD 8 (CAR (G A TR))) 0))))

(defthmd check-tr-keys-lemma2
  (IMPLIES (and (CHECK-TR-KEYS keys TR)
                (set::in a keys)
                (consp tr))
           (UNSIGNED-BYTE-P 8 (CAR (G A TR)))))

(defthm mylift-of-wr-0-case
 (implies (and (wf-tr tr) ;(wfr tr)
               (equal 0 (loghead 8 v)))
          (equal (mylift (gacc::wr a v tr))
                 ;if what was there was well-formed, we get 0.  otherwise (including if it was 0 before!), we get what was there!
                 (s a nil (mylift tr))))
 :otf-flg t
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
        ;  :cases ((SET::in A (SET::RKEYS TR)))
          :use ((:instance check-tr-keys-lemma (keys (set::rkeys tr)))
                (:instance check-tr-keys-lemma2 (keys (set::rkeys tr))))
          :in-theory (e/d ( ;gacc::wr
                           GACC::MEMORY-CLR
                           )
                          (
                           set::rkeys
                           WR-OF-0-IS-CLR
                           LOGHEAD*-BETTER ;bzo why isn't this disabled?
                           LOGCAR-LOGCDR-ELIM
                           )))))

(in-theory (disable LOGHEAD*-BETTER))

;for dave
(defthm mylift-of-wr
  (implies (wf-tr tr)
           (equal (mylift (gacc::wr a v tr))
                  (s a (val-fix v) (mylift tr))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :use ((:instance mylift-of-wr-0-case)
                 (:instance mylift-of-wr-1))
           :in-theory (disable MYLIFT g-of-mylift))))

;see S-PRESERVES-WFR (should WFKEY be enabled?)

;bzo maybe wf-tr should allow nil keys?

(defun check-tr-val (val)
  (and (UNSIGNED-BYTE-P 8 VAL)
       (NOT (EQUAL 0 VAL))))

(defun check-tr-entry (val)
  (and (equal nil (cdr val))
       (check-tr-val (car val))))

;bzo really what's checked by CHECK-TR-KEYS is the value -rename

(defthm check-tr-keys-of-s
  (implies (and (check-tr-keys keys tr)
                (check-tr-entry v) ;the whole entry, not the val
                )
           (check-tr-keys keys (s a v tr)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


(defthm CHECK-TR-KEYS-of-s-irrel
  (implies (not (set::in a keys))
           (equal (CHECK-TR-KEYS keys (S A NIL TR))
                  (CHECK-TR-KEYS keys TR))))

(defthm delete-when-would-be-head
  (implies (equal a (set::head (set::insert a keys)))
           (equal (set::delete a keys)
                  (if (set::in a keys)
                      (set::tail keys)
                    (set::sfix keys))))
  :hints (("Goal" :in-theory (enable SET::SFIX ;bzo
                                     ))))

(defthm car-of-insert-of-nil
  (equal (car (set::insert k nil))
         k)
  :hints (("Goal" :in-theory (enable set::insert))))

(defthm check-tr-keys-of-insert
  (equal (check-tr-keys (set::insert a keys) tr)
         (let* ((val (g a tr)))
           (and (equal nil (cdr val))
                (unsigned-byte-p 8 (car val))
                (not (equal 0 (car val)))
                (check-tr-keys keys tr))))
  :otf-flg t
  :hints (("Goal" :induct (my-ind a keys r)
           :expand ((CHECK-TR-KEYS (SET::INSERT A KEYS) tR)
                    )
           :in-theory (disable gacc::wr==r! )
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))))

(defthm check-tr-keys-of-delete
  (implies (check-tr-keys keys tr)
           (check-tr-keys (set::delete a keys) tr))
  :hints (("Goal"
           :expand (CHECK-TR-KEYS (SET::INSERT (SET::HEAD KEYS)
                                               (SET::DELETE A (SET::TAIL KEYS)))
                                  TR)
           :do-not '(generalize eliminate-destructors))))

(defthm consp-g-when-in-keys-and-check-tr-keys
  (implies (and (check-tr-keys keys tr)
                (set::in a keys)
                )
           (consp (g a tr)))
  :hints (("Goal" :in-theory (enable check-tr-keys))))

;replace the consp-g-version?
(defthm g-means-in-keys
  (implies (and (g a tr)
                (wfr tr)
                )
           (set::in a (set::rkeys tr)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))
;;           :in-theory (enable rkeys key-set g))))

(defthm consp-g-when-g-and-check-tr-keys
  (implies (and (check-tr-keys (set::rkeys tr) tr)
                (g a tr) ;is not nil
                (wfr tr)
                )
           (consp (g a tr)))
  :hints (("Goal" :use (:instance consp-g-when-in-keys-and-check-tr-keys (keys (set::rkeys tr)))
           :in-theory (e/d (check-tr-keys) (consp-g-when-in-keys-and-check-tr-keys)))))

(defthm set::rkeys-s
  (equal (set::rkeys (s a v r))
         (if v (set::insert a (set::rkeys r))
           (set::delete a (set::rkeys r)))))

;for dave
(defthm wf-tr-of-wr
  (implies (and (wf-tr tr)
                a ;that is, a is not nil
                )
           (wf-tr (gacc::wr a v tr)))
  :otf-flg t
  :hints (("Goal" :expand (CHECK-TR-KEYS (SET::INSERT A NIL)
                                         (S A (LIST (LOGHEAD 8 V)) NIL))
           :use ((:instance check-tr-keys-lemma2 (keys (set::rkeys tr)))
                 (:instance check-tr-keys-lemma (keys (set::rkeys tr))))
           :in-theory (e/d (GACC::WR wfkey) (set::rkeys
                                             check-tr-keys-lemma2
                                             check-tr-keys-lemma)))))


;for dave
(defthm mylift-of-wr-sp-version
  (implies (wf-tr tr)
           (equal (mylift (gacc::wr a v tr))
                  (cpath::sp (list a) (val-fix v) (mylift tr))))
  :hints (("Goal" :in-theory (e/d ( CPATH::SP) (MYLIFT WF-TR val-fix)))))

(defun non-nil (x)
  (declare (xargs :guard t))
  (not (null x)))

(set-verify-guards-eagerness 2)

(set::quantify-predicate (non-nil x))   ; see quantify.lisp for explanation




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
  (implies (and (wf-tr tr)
                (set::all<non-nil> keys)
                (set::setp keys))
           (equal (set::rkeys (mylift-aux keys tr))
                  keys))
  :hints (("Goal" :in-theory (enable SET::EMPTY))))

#+joe
(defthm wfkeyed-implies-not-nil-memberp
  (implies
   (wfkeyed r)
   (not (bag::memberp nil (alist::Keys r))))
  :hints (("Goal" :in-theory (enable wfkeyed alist::keys bag::memberp))))

#+joe
(defthm wfr-implies-not-nil-memberp
  (implies
   (wfr r)
   (not (bag::memberp nil (rkeys r))))
  :hints (("Goal" :in-theory (enable wfr rkeys))))

(defthm all-non-nil-of-rkeys
  (implies (and (wfkeyed tr)
                (wfr tr))
           (set::all<non-nil> (set::rkeys tr)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))
;;           :in-theory (enable ;wfr
;;                       wfkeyed wfkey rkeys))))

(defthm all-non-nil-of-rkeys2
  (implies (wf-tr tr)
           (set::all<non-nil> (SET::RKEYS TR)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable wfr WFKEYED))))

(defthm empty-list2set
  (equal (set::empty (list::2set list))
         (not (consp list)))
  :hints (("Goal" :in-theory (e/d (list::2set)
                                  (SET::|2SET-REWRAP|)))))

(defthm empty-rkeys-when-wfr
  (IMPLIES (AND  (WFR TR))
           (equal (SET::EMPTY (SET::RKEYS TR))
                  (NOT TR)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))
;;           :in-theory (enable wfr RKEYS))))

(defun ind (keys tr)
  (declare (xargs :verify-guards nil))
  (if (or (not (set::setp keys))
          (set::empty keys))
      (list keys tr)
    (ind (set::tail keys)
         (GACC::MEMORY-CLR (SET::HEAD (SET::RKEYS TR)) tr);
         ;(gacc::wr (set::head keys) (gacc::rd (set::head keys) tr) tr)
         )))

(in-theory (disable set::rkeys))

(defthm rkeys-of-memory-clr
  (implies (and (rcdp tr) ;; (wfr tr)
                (not (ifrp tr)))
           (equal (set::rkeys (gacc::memory-clr a tr))
                  (if (gacc::wf-usbp8 (g a tr))
                      (if (cdr (g a tr))
                          (set::insert a (set::rkeys tr))
                        (set::delete a (set::rkeys tr)))
                    (set::rkeys tr))))
  :hints (("Goal" :in-theory (e/d (gacc::memory-clr) (WR-OF-0-IS-CLR)))))

;bzo move?
(defthm wfr-of-wr
  (implies (and (wfr tr)
                (wfkey a))
           (wfr (GACC::WR A v TR)))
  :hints (("Goal" :in-theory (e/d (GACC::WR) ()))))

(defthm wfr-of-memory-clr
  (implies (and (wfr tr)
                (wfkey a))
           (wfr (gacc::memory-clr a tr)))
  :hints (("Goal" :in-theory (e/d (gacc::memory-clr) (wr-of-0-is-clr)))))



(defthm not-check-tr-keys-1
  (implies (equal (loghead 8 (car (g (set::head rkeys) tr))) 0)
           (equal (check-tr-keys rkeys tr)
                  (set::empty rkeys))))

(defthm check-tr-keys-of-memory-clr-irrel
  (implies (and (not (set::in key keys))
                (wfr tr))
           (equal (check-tr-keys keys (gacc::memory-clr key tr))
                  (check-tr-keys keys tr)))
  :hints (("Goal" :in-theory (e/d (GACC::MEMORY-CLR GACC::WR) (WR-OF-0-IS-CLR))
           :do-not '(generalize eliminate-destructors))))

#|
(defthm nil-not-in-key-set-when-wfkeyed
  (implies (WFKEYED R)
           (not (set::in nil (key-set r))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable key-set wfr wfkeyed wfkey))))

(defthm nil-not-in-key-set-when-wfr
 (implies (wfr r)
          (not (set::in nil (key-set r))))
 :hints (("Goal" :do-not '(generalize eliminate-destructors)
          :in-theory (enable key-set wfr wfkeyed wfkey))))
|#

(defthm wfkey-when-in-rkeys
  (implies (and (wfr tr)
                (set::in key (set::rkeys tr))
                )
           (wfkey key))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable wfkey set::rkeys))))
;;            :in-theory (enable wfr rkeys wfkey wfkeyed))))

(defthm wkeys-of-head-of-rkeys
  (implies (and (wfr tr)
                tr ;
                )
           (wfkey (set::head (set::rkeys tr))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable ;wfr rkeys wfkey wfkeyed
                       ))))

(defthm setp-rkeys
  (set::setp (set::rkeys tr))
  :hints (("Goal" :in-theory (enable set::rkeys))))

(defthm mypuhs-aux-of-mylift-aux
  (implies (and (wf-tr tr)
                (equal rkeys (set::rkeys tr)))
           (equal (mypush-aux rkeys
                              (mylift-aux rkeys tr))
                  tr))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d ( ;wfr
                            CHECK-TR-KEYS
                            mypush-aux mylift-aux)
                           ( ;gacc::wr==r!
                            ))
           :induct (ind rkeys tr)
           )))

;for dave
(defthm mypush-of-mylift
  (implies (wf-tr tr)
           (equal (mypush (mylift tr))
                  tr)))


(defun typed-fix-aux (keys r)
  (declare (xargs :verify-guards nil))
  (if (set::empty keys)
      nil ;the empty record
    (s (set::head keys)
       (val-fix (g (set::head keys) r))
       (typed-fix-aux (set::tail keys) r))))

;takes a true record and fixes it by dropping all pairs whose value has a
;loghead8 of 0 and chopping the value on all pairs whose value is not a usb8.
(defun typed-fix (r)
  (declare (xargs :verify-guards nil))
  (typed-fix-aux (set::rkeys r) r))


(DEFTHM RKEYS-OF-WR-alt
  (IMPLIES (wfr tr)
           (EQUAL (SET::RKEYS (GACC::WR A V TR))
                  (IF (GACC::WF-USBP8 (G A TR))
                      (IF (GACC::USBP8-ZP V)
                          (IF (CDR (G A TR))
                              (SET::INSERT A (SET::RKEYS TR))
                              (SET::DELETE A (SET::RKEYS TR)))
                          (SET::INSERT A (SET::RKEYS TR)))
                      (IF (GACC::USBP8-ZP V)
                          (SET::RKEYS TR)
                          (SET::INSERT A (SET::RKEYS TR))))))
)

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



(defun ind3 (keys r)
  (declare (xargs :verify-guards nil))
  (if (or (not (set::setp keys))
          (set::empty keys))
      (list keys r)
    (ind3 (set::tail keys)
         (CLR (SET::HEAD (SET::RKEYS R)) r);
         ;(gacc::wr (set::head keys) (gacc::rd (set::head keys) tr) tr)
         )))





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




(defthmd g-when-not-g-of-cdr
  (implies (and (not (g key (cdr r)))
                (wfr r))
           (equal (g key r)
                  (if (equal key (caar r))
                      (cdar r)
                    nil)))
  :hints (("Goal" :in-theory (enable g)
           :do-not '(generalize eliminate-destructors))))


(defthm g-when-not-in-rkeys
  (implies (and (not (set::in key (set::rkeys r)))
                (wfr r))
           (equal (g key r)
                  nil))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable rkeys g-when-not-g-of-cdr ))))

(defthm nil-not-in-rkeys
  (implies (and (wfkeyed r) ;drop?
                (wfr r))
           (not (set::in nil (set::rkeys r))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable rkeys wfkeyed))))

(defthm g-of-nil
  (implies (and ;(wfkeyed r)
                (wfr r))
           (not (g nil r)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable ;wfkeyed wfkey
                       ))))

;bzo move some of these?
(defthm s-nil-nil
  (implies (wfr r)
           (equal (S NIL NIL R)
                  r)))

(defthm wfkeyed-of-clr
  (implies (and (wfr r)
                ;(wfkeyed r)
                )
           (wfkeyed (clr key r)))
  :otf-flg t
  :hints (("Goal" :cases (key)
           :in-theory (e/d (clr WFKEY) (S==R)))))

;; (defthm wfr-of-mypush-aux-helper
;;   (implies (and (wfr r)
;;                 (wfkeyed r)
;;                 (equal keys (set::rkeys r))
;;                 )
;;            (wfr (mypush-aux keys r)))
;;   :hints (("Goal" :induct (ind3 keys r)
;;            :do-not '(generalize eliminate-destructors))))

;; (defthm wfr-of-mypush-aux-helper
;;   (implies (and (wfr r)
;;                 (wfkeyed r)
;;                 (set::setp keys)
;;                 (set::subset keys (set::rkeys r))
;;                 )
;;            (wfr (mypush-aux keys r)))
;;   :hints (("Goal" :induct (ind3 keys r)
;;            :in-theory (disable SET::SUBSET ;bzo was getting specious simp..
;;                                )
;;            :do-not '(generalize eliminate-destructors))))

(defthm wfr-of-mypush-aux-helper
  (implies (and (wfr r)
                (set::all<non-nil> keys)
                )
           (wfr (mypush-aux keys r)))
  :hints (("Goal" ;:induct (ind3 keys r)
           :in-theory (e/d (wfkey) (set::subset ;bzo was getting specious simp..
                               ))
           :do-not '(generalize eliminate-destructors))))


;; subset is enough?
;; (thm
;;  (equal (SET::RKEYS (MYPUSH-AUX keys R))
;;         ..

(defthm g-of-mypush-aux-when-not-in-keys
  (implies (not (set::in key keys))
           (equal (g key (mypush-aux keys r))
                  nil))
  :hints (("Goal" :in-theory (enable GACC::WR)
           :do-not '(generalize eliminate-destructors))))

(defthm clr-of-typed-fix-aux-irrel
  (implies (not (set::in key keys))
           (equal (CLR key (TYPED-FIX-AUX keys R))
                  (TYPED-FIX-AUX keys (CLR key r))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm not-in-of-rkeys-of-mypush-aux
  (implies (and (NOT (SET::IN key keys))
                (set::all<non-nil> keys) ;drop?
                (wfr r))
           (NOT (SET::IN key (SET::RKEYS (MYPUSH-AUX keys R)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm set::rkeys-clr
  (equal (set::rkeys (clr a r))
         (set::delete a (set::rkeys r)))
  :hints (("Goal" :in-theory (enable set::rkeys))))

(defthm MYLIFt-of-mypush-helper
  (IMPLIES (and (WFR R)
                (equal keys (SET::RKEYS R)))
           (EQUAL (MYLIFT-AUX (SET::RKEYS (MYPUSH-AUX keys R))
                              (MYPUSH-AUX keys R))
                  (TYPED-FIX-AUX keys R)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (ind3 keys r)
           )))

(defthm mylift-of-mypush
  (implies (wfr r)
           (equal (mylift (mypush r))
                  (typed-fix r))))

;Bbzo give the predicate for which lift of push really is the identity and prove that typed-fix is a no-op if that predicate is true

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
           :induct (ind3 keys r))))

;;bzo Dave, what do we want to call this?
(defun well-typed-record (r)
  (declare (xargs :verify-guards nil))
  (and (wfr r)
       (all-vals-okay-aux (set::rkeys r) r)))

;for Dave
(defthm typed-fix-does-nothing
  (implies (well-typed-record r)
           (equal (typed-fix r)
                  r))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))


;; (thm
;;  (iff (SET::DELETE A S)
;;       (and
;;       (not (or (set::empty s)
;;                (equal s (list a)) ;gross?
;;                ))

;;       ))

;; (thm
;;  (implies (set::setp s)
;;           (equal (car (SET::DELETE A s))
;;                  (if (set::in a s)
;;                      (if (<< a (cadr s))
;;                          (cadr s)
;;                        (caddr s))
;;                    (car s))))
;;  :otf-flg t
;;  :hints (("Goal" :in-theory (e/d (set::head set::tail SET::SFIX SET::EMPTY
;;                                  CAR-OF-INSERT
;;                                             )
;;                                  (set::delete
;;                                   set::insert))
;;           :expand ((SET::SETP S)
;;                    (SET::DELETE A S)
;;                    )
;;           :do-not '(generalize eliminate-destructors))))

;; (thm
;;  (equal (SET::HEAD (SET::INSERT (SET::HEAD KEYS) (SET::DELETE A (SET::TAIL KEYS))))
;;         (SET::HEAD KEYS))
;;  :otf-flg t
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;           :expand ((SET::SETP KEYS)
;;                    (SET::INSERT (CAR KEYS)
;;                                   (SET::DELETE A (CDR KEYS)))
;; ;;                    (SET::SETP (CDR KEYS))
;; ;;                    (SET::INSERT (CAR KEYS)
;; ;;                                   (SET::INSERT (CADR KEYS) NIL))
;; ;;                    (SET::INSERT (CAR KEYS) (CDDR KEYS))
;; ;;                    (SET::INSERT (CAR KEYS)
;; ;;                                 (SET::DELETE A (CDR KEYS)))
;; ;;                    (SET::INSERT (CADR KEYS)
;; ;;                                 (SET::DELETE A (CDDR KEYS)))
;; ;;                    (SET::INSERT (CAR KEYS)
;; ;;                                 (SET::INSERT (CADR KEYS)
;; ;;                                              (SET::DELETE A (CDDR KEYS))))
;;                    )
;;           :in-theory (e/d (set::head set::tail SET::SFIX SET::EMPTY
;;     CAR-OF-INSERT
;;                                      )
;;                           (set::delete
;;                            set::insert)))))








;bzo add lemmas to establish wr-tr..





;; (defun mypush (r)
;;   (if (endp r)
;;       nil
;;     (let* ((entry (car r))
;;            (key (car entry))
;;            (val (cdr entry)) ;not cadr
;;            )
;;       (gacc::wr key val (mypush (cdr r))))))

;; (defun wf-tr (tr)
;;   (if (endp tr)
;;       (null tr)
;;     (let* ((entry (car tr))
;; ;           (key (car entry))
;;            (val (cadr entry)) ;not cdr
;;            )
;;       (and (equal 2 (len entry))
;;            (unsigned-byte-p 8 val)
;;            (not (equal 0 val))
;;            (wf-tr (cdr tr))))))
