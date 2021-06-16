; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "FGL")

(include-book "std/stobjs/absstobjs" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/basic/arith-equiv-defs" :dir :system)
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (in-theory (disable acl2::resize-list-when-atom
                           nth update-nth
                           resize-list)))

(define fgarray-alistp (x)
  (if (atom x)
      t
    (and (consp (car x))
         (natp (caar x))
         (fgarray-alistp (cdr x))))
  ///
  (defthm fgarray-alistp-of-cdr
    (implies (fgarray-alistp x)
             (fgarray-alistp (cdr x))))

  (defthm fgarray-alistp-of-acons
    (implies (and (fgarray-alistp x)
                  (consp pair)
                  (natp (car pair)))
             (fgarray-alistp (cons pair x))))

  (defthm fgarray-alistp-of-append
    (implies (and (fgarray-alistp x)
                  (fgarray-alistp y))
             (fgarray-alistp (append x y)))))


(local
 (defthm car-of-hons-assoc-equal
   (implies (hons-assoc-equal k x)
            (equal (car (hons-assoc-equal k x)) k))))

(define fgarrayp$a (x)
  :enabled t
  (fgarray-alistp x))

(define fgarray-get$a ((i natp) (x fgarrayp$a))
  :enabled t
  (hons-assoc-equal (lnfix i) x))

(define fgarray-set$a ((i natp) val (x fgarrayp$a))
  :enabled t
  (cons (cons (lnfix i) val) x))


(define create-fgarray$a () nil)

(define fgarray-max-key ((x fgarray-alistp))
  :Returns (max natp :rule-classes :type-prescription)
  :verify-guards nil
  (if (atom x)
      0
    (if (mbt (And (consp (car x))
                  (natp (caar x))))
        (max (+ 1 (caar x)) (fgarray-max-key (cdr x)))
      (fgarray-max-key (cdr x))))
  ///
  (verify-guards fgarray-max-key
    :hints (("goal" :in-theory (enable fgarray-alistp))))

  (defthmd lookup-past-fgarray-max-key
    (implies (and (<= (fgarray-max-key x) i)
                  (natp i))
             (not (hons-assoc-equal i x)))
    :hints(("Goal" :in-theory (enable fgarray-alistp))))

  (defthmd max-key-implies-lookup
    (implies (posp (fgarray-max-key x))
             (hons-assoc-equal (1- (fgarray-max-key x)) x))
    :hints(("Goal" :in-theory (enable fgarray-alistp)))))

(local (in-theory (enable lookup-past-fgarray-max-key)))
    

(define fgarray-compress$a-aux ((i natp) (max natp) (x fgarrayp$a))
  :guard (<= i max)
  :measure (nfix (- (nfix max) (nfix i)))
  :Returns (new-x fgarray-alistp)
  (if (mbe :logic (zp (- (nfix max) (nfix i)))
           :exec (eql i max))
      nil
    (let ((look (hons-assoc-equal (lnfix i) x)))
      (if look
          (cons look (fgarray-compress$a-aux (1+ (lnfix i)) max x))
        (fgarray-compress$a-aux (1+ (lnfix i)) max x))))
  ///
  (defthm lookup-in-fgarray-compress$a-aux
    (equal (hons-assoc-equal k (fgarray-compress$a-aux i max x))
           (and (natp k)
                (<= (nfix i) k)
                (< k (nfix max))
                (hons-assoc-equal k x))))

  (local
   (defthm fgarray-compress$a-aux-of-i-greater-than-max-key
     (implies (<= (fgarray-max-key x) (nfix i))
              (equal (fgarray-compress$a-aux i max x) nil))))

  (defthm fgarray-compress$a-aux-of-greater-than-max-key
    (implies (and (syntaxp (case-match max
                             (('fgarray-max-key a) (not (equal a x)))
                             (& t)))
                  (<= (fgarray-max-key x) (nfix max)))
             (equal (fgarray-compress$a-aux i max x)
                    (fgarray-compress$a-aux i (fgarray-max-key x) x)))))
              

(define fgarray-compress$a ((x fgarrayp$a))
  :enabled t
  (fgarray-compress$a-aux 0 (fgarray-max-key x) x))

(define fgarray->alist$a ((x fgarrayp$a))
  :enabled t
  x)

(define fgarray-init$a ((size natp) (x fgarrayp$a))
  (declare (ignore x size))
  nil)

(define maybe-nat-pair-p (x)
  (or (not x)
      (and (consp x)
           (natp (car x))))
  ///
  (defthm maybe-nat-pair-p-of-cons
    (implies (natp i)
             (maybe-nat-pair-p (cons i v)))))


(defstobj fgarray$c
  (fgarray$c->data :type (array (and (or cons null)
                                     (satisfies maybe-nat-pair-p))
                                (0)) :resizable t :initially nil)
  (fgarray$c->alist :type (satisfies fgarray-alistp) :initially nil)
  :inline t)
 
(defun-sk fgarray$c-invariant (x)
  (forall i
          (equal (nth i (nth *fgarray$c->datai* x))
                 (hons-assoc-equal (nfix i) (nth *fgarray$c->alist* x))))
  :rewrite :direct)

(defthm fgarray$c-invariant-of-create-fgarray$c
  (fgarray$c-invariant (create-fgarray$c))
  :hints(("Goal" :in-theory (enable nth))))

(defthm fgarray$c-invariant-of-empty
  (fgarray$c-invariant '(nil nil))
  :hints(("Goal" :in-theory (enable nth fgarray$c-invariant))))

(local (in-theory (disable fgarray$c-invariant)))


(local (defthm nth-past-len
         (implies (<= (len x) (nfix i))
                  (equal (nth i x) nil))
         :hints(("Goal" :in-theory (enable nth)))))

(define fgarray-get$c ((i natp) fgarray$c)
  (mbe :logic (fgarray$c->datai i fgarray$c)
       :exec (and (< i (fgarray$c->data-length fgarray$c))
                  (fgarray$c->datai i fgarray$c)))
  ///
  (defthm fgarray-get$c-under-invariant
    (implies (fgarray$c-invariant fgarray$c)
             (equal (fgarray-get$c i fgarray$c)
                    (hons-assoc-equal (nfix i) (fgarray$c->alist fgarray$c))))))

(define fgarray-set$c ((i natp) val fgarray$c)
  (b* ((fgarray$c (let ((len (fgarray$c->data-length fgarray$c)))
                    (if (< (lnfix i) len)
                        fgarray$c
                      (resize-fgarray$c->data
                       (max (* 2 len) (+ 1 (lnfix i)))
                       fgarray$c))))
       (pair (cons (lnfix i) val))
       (fgarray$c (update-fgarray$c->datai i pair fgarray$c)))
    (update-fgarray$c->alist (cons pair
                                   (fgarray$c->alist fgarray$c))
                             fgarray$c))
  ///
  (defthm fgarray$c-invariant-of-fgarray-set$c
    (implies (fgarray$c-invariant fgarray$c)
             (fgarray$c-invariant (fgarray-set$c i val fgarray$c)))
    :hints(("Goal" :in-theory (disable fgarray$c-invariant
                                       fgarray$c-invariant-necc))
           (and stable-under-simplificationp
                (let ((lit (car (last clause))))
                  `(:expand (,lit)
                    :use ((:instance fgarray$c-invariant-necc
                           (x fgarray$c)
                           (i (fgarray$c-invariant-witness . ,(cdr lit))))))))))

  (defthm fgarray$c->alist-of-fgarray-set$c
    (equal (fgarray$c->alist (fgarray-set$c i val fgarray$c))
           (cons (cons (nfix i) val) (fgarray$c->alist fgarray$c)))))



(local (defthm consp-nth-of-fgarray$c->datap
         (implies (fgarray$c->datap x)
                  (iff (consp (nth n x))
                       (nth n x)))
         :hints(("Goal" :in-theory (enable nth)))))

(local (defthm append-take-nthcdr
         (implies (and (<= (nfix i) (len x))
                       (true-listp x))
                  (equal (append (take i x) (nthcdr i x))
                         x))))

(local (defthm associativity-of-append
         (equal (append (append a b) c)
                (append a b c))))

(define fgarray-compress$c-aux ((i natp) fgarray$c (acc alistp))
  :guard (<= i (fgarray$c->data-length fgarray$c))
  :prepwork ((local (defthm nth-of-fgarray$c->datap
                      (implies (And (fgarray$c->datap x)
                                    (nth i x))
                               (and (consp (nth i x))
                                    (natp (car (nth i x)))))
                      :hints(("Goal" :in-theory (enable fgarray$c->datap
                                                        maybe-nat-pair-p
                                                        nth))))))
  :returns (alist fgarray-alistp :hyp (and (fgarray$c->datap (nth *fgarray$c->datai* fgarray$c))
                                           (fgarray-alistp acc)))
  (if (zp i)
      acc
    (let* ((i (1- i))
           (elt (fgarray$c->datai i fgarray$c)))
      (fgarray-compress$c-aux
       i fgarray$c
       (mbe :logic (if (consp elt) (cons elt acc) acc)
            :exec (if elt (cons elt acc) acc)))))
  ///


  ;; (defthm fgarray-alistp-of-fgarray-compress$c-aux-when-fgarray$c-invariant
  ;;   (implies (and (fgarray$c-invariant fgarray$c)
  ;;                 (fgarray-alistp acc))
  ;;            (fgarray-alistp (fgarray-compress$c-aux i fgarray$c acc)))
  ;;   :hints (("goal" :induct (fgarray-compress$c-aux i fgarray$c acc)
  ;;            :expand ((fgarray-compress$c-aux i fgarray$c acc)))))


  ;; (local (defthm nthcdr-of-take
  ;;          (equal (nthcdr i (take (+ 1 (nfix i)) x))
  ;;                 (list (nth i x)))
  ;;          :hints(("Goal" :in-theory (enable nth)))))
  ;; (local (defthm take-of-take
  ;;          (implies (and (natp n) (natp m))
  ;;                   (equal (take n (take (+ n m) x))
  ;;                          (take n x)))))
  ;; (local (defthm expand-take-in-reverse
  ;;          (implies (not (zp i))
  ;;                   (equal (take i x)
  ;;                          (append (take (+ -1 i) x)
  ;;                                  (list (nth (+ -1 i) x)))))
  ;;          :hints (("goal" :use ((:instance append-take-nthcdr
  ;;                                 (x (take i x))
  ;;                                 (i (+ -1 i)))
  ;;                                (:instance nthcdr-of-take
  ;;                                 (i (+ -1 i)))
  ;;                                (:instance take-of-take (n (1- i)) (m 1)))
  ;;                   :in-theory (disable append-take-nthcdr
  ;;                                       nthcdr-of-take
  ;;                                       take-of-take
  ;;                                       take)))))

  (local (defthm fgarray-compress$a-aux-alt
           (equal (fgarray-compress$a-aux i max x)
                  (if (zp (- (nfix max) (nfix i)))
                      nil
                    (append (fgarray-compress$a-aux i (1- (nfix max)) x)
                            (let ((pair (hons-assoc-equal (1- (nfix max)) x)))
                              (and pair (list pair))))))
           :hints(("Goal" :in-theory (enable fgarray-compress$a-aux)))
           :rule-classes :definition))

  (defthm fgarray-compress$c-aux-elim
    (implies (fgarray$c-invariant fgarray$c)
             (equal (fgarray-compress$c-aux i fgarray$c acc)
                    (append (fgarray-compress$a-aux 0 i (nth *fgarray$c->alist* fgarray$c)) acc)))
    :hints (("goal" :induct (fgarray-compress$c-aux i fgarray$c acc)))))




;; (define collect-conses (x)
;;   :returns (new-x alistp)
;;   (if (atom x)
;;       nil
;;     (if (consp (car x))
;;         (cons (car x) (collect-conses (cdr x)))
;;       (collect-conses (cdr x))))
;;   ///
;;   (defthm collect-conses-of-append
;;     (equal (collect-conses (append x y))
;;            (append (collect-conses x)
;;                    (collect-conses y))))

;;   (defthm collect-conses-of-true-list-fix
;;     (equal (collect-conses (true-list-fix x))
;;            (collect-conses x))
;;     :hints(("Goal" :in-theory (enable true-list-fix))))

;;   (defthm hons-assoc-equal-of-collect-conses
;;     (equal (hons-assoc-equal k (collect-conses x))
;;            (hons-assoc-equal k x)))

;;   (defthm fgarray-alistp-of-collect-conses
;;     (implies (fgarray$c->datap x)
;;              (fgarray-alistp (collect-conses x)))
;;     :hints(("Goal" :in-theory (enable fgarray-alistp maybe-nat-pair-p)))))


;; (local (defthm len-of-take
;;          (equal (len (take n x))
;;                 (nfix n))))


;; (local (defthm take-of-len
;;          (equal (Take (len x) x)
;;                 (true-list-fix x))
;;          :hints(("Goal" :in-theory (enable true-list-fix)))))



;; (defthm fgarray$c-invariant-implies-data-keys
;;   (implies (and (fgarray$c-invariant fgarray$c)
;;                 (nth i (nth *fgarray$c->datai* fgarray$c)))
;;            (equal (car (nth i (nth *fgarray$c->datai* fgarray$c)))
;;                   (nfix i)))
;;   :hints (("goal" :use ((:instance fgarray$c-invariant-necc
;;                          (i (nfix i)) (x fgarray$c))))))

;; (local
;;  (defthm nth-when-member
;;    (implies (member k x)
;;             (equal (nth (- (len x) (len (member k x))) x) k))
;;    :hints(("Goal" :in-theory (enable nth)))))

;; (local
;;  (defthm member-of-hons-assoc-equal
;;    (implies (hons-assoc-equal k x)
;;             (member (hons-assoc-equal k x) x))))

;; (local (defthm hons-assoc-equal-when-car-of-member
;;          (implies (and (member elt x)
;;                        (consp elt))
;;                   (hons-assoc-equal (car elt) x))))

;; (local (defthm member-of-nth
;;          (implies (< (nfix i) (len x))
;;                   (member (nth i x) x))
;;          :hints(("Goal" :in-theory (enable nth)))))

;; (defthm fgarray$c-invariant-implies-hons-assoc-equal
;;   (implies (and (fgarray$c-invariant fgarray$c)
;;                 (natp i))
;;            (equal (hons-assoc-equal i (nth *fgarray$c->datai* fgarray$c))
;;                   (hons-assoc-equal i (nth *fgarray$c->alist* fgarray$c))))
;;   :hints (("goal" :in-theory (disable ;; member-of-hons-assoc-equal
;;                                       nth-when-member
;;                                       member-of-nth
;;                                       fgarray$c-invariant-necc
;;                                       fgarray$c-invariant-implies-data-keys
;;                                       hons-assoc-equal-when-car-of-member
;;                                       ;; nth-past-len
;;                                       acl2::natp-when-integerp
;;                                       acl2::nfix-when-not-natp
;;                                       )
;;            :use ((:instance member-of-nth
;;                   (x (nth *fgarray$c->datai* fgarray$c)))
;;                  (:instance fgarray$c-invariant-necc
;;                   (x fgarray$c))
;;                  (:instance hons-assoc-equal-when-car-of-member
;;                   (elt (nth i (nth *fgarray$c->datai* fgarray$c)))
;;                   (x (nth *fgarray$c->datai* fgarray$c)))
;;                  (:instance fgarray$c-invariant-implies-data-keys)
;;                  (:instance fgarray$c-invariant-implies-data-keys
;;                   (i (+
;;                       (LEN (NTH *FGARRAY$C->DATAI* FGARRAY$C))
;;                       (-
;;                        (LEN
;;                         (MEMBER-EQUAL (HONS-ASSOC-EQUAL I (NTH *FGARRAY$C->DATAI* FGARRAY$C))
;;                                       (NTH *FGARRAY$C->DATAI* FGARRAY$C)))))))
;;                  (:instance nth-when-member
;;                   (k (hons-assoc-equal i (nth *fgarray$c->datai* fgarray$c)))
;;                   (x (nth *fgarray$c->datai* fgarray$c)))
;;                  )))
;;   :otf-flg t)


  

(define fgarray-compress$c (fgarray$c)
  (b* ((alist (fgarray-compress$c-aux (fgarray$c->data-length fgarray$c)
                                      fgarray$c nil)))
    (update-fgarray$c->alist alist fgarray$c))
  ///
  (defthm fgarray$c-invariant-of-fgarray-compress$c
    (implies (fgarray$c-invariant fgarray$c)
             (fgarray$c-invariant (fgarray-compress$c fgarray$c)))
    :hints ((and stable-under-simplificationp
                 (let ((lit (car (last clause))))
                   `(:expand (,lit)
                     :in-theory (disable fgarray$c-invariant-necc)
                     :use ((:instance fgarray$c-invariant-necc
                            (x fgarray$c)
                            (i (fgarray$c-invariant-witness . ,(cdr lit))))))))))
  
  (defthm len-gte-max-key
    (implies (fgarray$c-invariant fgarray$c)
             (<= (fgarray-max-key (nth *fgarray$c->alist* fgarray$c))
                 (len (nth *fgarray$c->datai* fgarray$c))))
    :hints (("goal" :use ((:instance max-key-implies-lookup
                           (x (nth *fgarray$c->alist* fgarray$c)))
                          (:instance fgarray$c-invariant-necc
                           (x fgarray$c)
                           (i (1- (fgarray-max-key (nth *fgarray$c->alist* fgarray$c))))))
             :in-theory (disable fgarray$c-invariant-necc))))

  (defthm fgarray$c->alist-of-fgarray-compress$c
    (implies (fgarray$c-invariant fgarray$c)
             (equal (fgarray$c->alist (fgarray-compress$c fgarray$c))
                    (fgarray-compress$a (fgarray$c->alist fgarray$c))))))


(define fgarray-init$c ((size natp) fgarray$c)
  (b* ((fgarray$c (resize-fgarray$c->data 0 fgarray$c))
       (fgarray$c (resize-fgarray$c->data size fgarray$c)))
    (update-fgarray$c->alist nil fgarray$c))
  ///
  (defthm fgarray$c-invariant-of-fgarray-init$c
    (fgarray$c-invariant (fgarray-init$c size fgarray$c))
    :hints(("Goal" :in-theory (enable fgarray$c-invariant))))

  (defthm fgarray$c->alist-of-fgarray-init$c
    (equal (fgarray$c->alist (fgarray-init$c size fgarray$c)) nil)))

;; (define fgarray->alist$c (fgarray$c)
;;   :enabled t
;;   (fgarray$c->alist fgarray$c))


(local (define fgarray-corr (fgarray$c fgarray$a)
         :enabled t
         :non-executable t
         :verify-guards nil
         (and (fgarray$c-invariant fgarray$c)
              (equal fgarray$a (fgarray$c->alist fgarray$c)))))

(local (in-theory (disable fgarray$c->alist)))

(acl2::defabsstobj-events fgarray
  :foundation fgarray$c
  :corr-fn fgarray-corr
  :recognizer (fgarrayp :exec fgarray$cp :logic fgarrayp$a)
  :creator (create-fgarray :exec create-fgarray$c :logic create-fgarray$a)
  :exports ((fgarray-get :exec fgarray-get$c :logic fgarray-get$a)
            (fgarray-set :exec fgarray-set$c :logic fgarray-set$a :protect t)
            (fgarray-compress :exec fgarray-compress$c :logic fgarray-compress$a :protect t)
            (fgarray-init :exec fgarray-init$c :logic fgarray-init$a :protect t)
            (fgarray->alist :exec fgarray$c->alist :logic fgarray->alist$a)))


(defxdoc fgarray
  :parents (fgl-array-support)
  :short "The abstract stobj interface on which FGL's array support is based"
  :long "<p> An @('fgarray') is an abstract stobj whose logical form is an
alist with natural number keys and whose implementation uses an array for fast
lookups.  The fgarray interface is used in FGL for fast array access during rewriting.</p>

<p>The supported interface functions are the following:</p>

<ul>

<li>@('(fgarray-get i fgarray)') gets the key/value pair associated with index
@('i'), or @('nil') if it doesn't exist.  Logically equal to
@('(hons-assoc-equal (nfix i) fgarray)').</li>

<li>@('(fgarray-set i val fgarray)') sets the key @('i') to value @('val');
logically equal to @('(cons (cons (nfix i) val) fgarray)').</li>

<li>@('(fgarray-compress fgarray)') rearranges the alist representation so that
the keys are in order with no duplicates.</li>

<li>@('(fgarray-init size fgarray)') empties the fgarray and sets its backing
array to the given size; logically equal to @('nil').</li>

<li>@('(fgarray->alist fgarray)') returns the alist object of the fgarray.</li>
</ul>

<p>The stobj creator function is @('(create-fgarray)'), but as with all stobjs,
this can only be invoked indirectly using @(see with-local-stobj).</p>

<p>Implementation note: The implementation of the fgarray builds a real alist
equal to the logical representation.  This is unnecessary for standalone use
and is done so that FGL can ensure that the stobj storing the fgarray data is
correctly in sync with the symbolic object representation.  Thus if all you
want is a stobj array that is logically represented as an alist, it would be
better to define a different abstract stobj without this feature.</p>")

