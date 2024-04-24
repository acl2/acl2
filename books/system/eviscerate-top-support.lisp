; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann, June, 2023
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(in-theory (enable iprint-oracle-updates))

(verify-termination bounded-integer-alistp) ; and guards

(defthm character-listp-explode-nonnegative-integer
  (equal (character-listp (explode-nonnegative-integer n print-base ans))
         (character-listp ans)))

(verify-termination make-sharp-atsign) ; and guards

(verify-termination get-sharp-atsign) ; and guards

(verify-termination iprint-alistp1) ; and guards

(verify-termination iprint-alistp) ; and guards

(verify-termination update-iprint-alist-fal) ; and guards

(defthm posp-cdr-hons-assoc-equal-iprint-fal
  (implies (and (iprint-falp iprint-fal-old)
                (hons-assoc-equal x iprint-fal-old))
           (posp (cdr (hons-assoc-equal x iprint-fal-old))))
  :rule-classes :type-prescription)

(verify-termination eviscerate1
  (declare (xargs :verify-guards nil)))

(include-book "tools/flag" :dir :system)

(make-flag flag-eviscerate1 eviscerate1)

(defthm iprint-alistp1-update-iprint-alist-fal
  (let ((result (mv-nth 1
                        (update-iprint-alist-fal iprint-alist iprint-fal-new
                                                 iprint-fal-old val))))
    (equal (iprint-alistp1 result)
           (if (or (equal result iprint-alist)
                   (consp iprint-alist))
               (iprint-alistp1 iprint-alist)
             (posp (1+ iprint-alist))))))

(defthm-flag-eviscerate1

(defthm iprint-alistp1-mv-nth-1-eviscerate1
  (let ((result
         (mv-nth 1
                 (eviscerate1 x v max-v max-n alist evisc-table hiding-cars
                              iprint-alist iprint-fal-new iprint-fal-old
                              eager-p))))
    (implies (and (iprint-alistp iprint-alist)
                  (not (eq result t))
                  (not (natp result)))
             (iprint-alistp1 result)))
  :flag eviscerate1)

(defthm iprint-alistp-mv-nth-1-eviscerate1-lst
  (let ((result
         (mv-nth 1
                 (eviscerate1-lst lst v n max-v max-n alist evisc-table
                                  hiding-cars iprint-alist iprint-fal-new
                                  iprint-fal-old eager-p))))
    (implies (and (iprint-alistp iprint-alist)
                  (not (eq result t))
                  (not (natp result)))
             (iprint-alistp1 result)))
  :flag eviscerate1-lst)

:hints (("Goal" :in-theory (disable assoc-equal update-iprint-alist-fal posp

; Found with accumulated-persistence (reduced time from 12.64 seconds to 1.08
; seconds):

                                    explode-nonnegative-integer
                                    string-append
                                    string-append-lst
                                    get-sharp-atsign
                                    make-sharp-atsign
                                    floor
                                    mod
                                    hons-assoc-equal
                                    digit-to-char
                                    nonnegative-integer-quotient)))
)

(defthm iprint-falp-update-iprint-alist-fal
  (implies (and (iprint-falp iprint-fal-new)
                (iprint-alistp iprint-alist))
           (iprint-falp
            (mv-nth 2
                    (update-iprint-alist-fal iprint-alist iprint-fal-new
                                             iprint-fal-old val)))))
(defthm-flag-eviscerate1

(defthm iprint-falp-mv-nth-2-eviscerate1
  (implies (and (iprint-alistp iprint-alist)
                (iprint-falp iprint-fal-new))
           (iprint-falp
            (mv-nth 2
                    (eviscerate1 x v max-v max-n alist evisc-table
                                 hiding-cars iprint-alist iprint-fal-new
                                 iprint-fal-old eager-p))))
  :flag eviscerate1)

(defthm iprint-fal-mv-nth-2-eviscerate1-lst
  (implies (and (iprint-alistp iprint-alist)
                (iprint-falp iprint-fal-new))
           (iprint-falp
            (mv-nth 2
                    (eviscerate1-lst lst v n max-v max-n alist evisc-table
                                     hiding-cars iprint-alist iprint-fal-new
                                     iprint-fal-old eager-p))))
  :flag eviscerate1-lst)

:hints (("Goal" :in-theory (disable assoc-equal update-iprint-alist-fal posp)))
)

(verify-guards eviscerate1 ; and guards
  :hints (("Goal"
           :in-theory (disable assoc-equal)
           :do-not-induct t))
  :otf-flg t)

(verify-termination eviscerate1p) ; and guards

(verify-termination eviscerate) ; and guards

(defthm-flag-eviscerate1

(defthm eviscerate-simple-lemma-eviscerate1
  (let ((result (eviscerate1 x v max-v max-n alist evisc-table
                             hiding-cars iprint-alist iprint-fal-new
                             iprint-fal-old eager-p)))
    (implies (and (booleanp iprint-alist)
                  (equal iprint-fal-new nil)
                  (equal iprint-fal-old nil))
             (and (booleanp (mv-nth 1 result))
                  (equal (mv-nth 2 result)
                         nil))))
  :rule-classes nil
  :flag eviscerate1)

(defthm eviscerate-simple-lemma-eviscerate1-lst
  (let ((result (eviscerate1-lst lst v n max-v max-n alist
                                 evisc-table hiding-cars iprint-alist
                                 iprint-fal-new iprint-fal-old
                                 eager-p)))
    (implies (and (booleanp iprint-alist)
                  (equal iprint-fal-new nil)
                  (equal iprint-fal-old nil))
             (and (booleanp (mv-nth 1 result))
                  (equal (mv-nth 2 result)
                         nil))))
  :rule-classes nil
  :flag eviscerate1-lst)

:hints (("Goal" :in-theory (disable assoc-equal)))
)

(defthm eviscerate-simple-lemma-eviscerate
  (let ((result (eviscerate x print-level
                            print-length alist evisc-table
                            hiding-cars nil nil nil nil)))
    (and (booleanp (mv-nth 1 result))
         (equal (mv-nth 2 result)
                nil)))
  :hints (("Goal" :use ((:instance eviscerate-simple-lemma-eviscerate1
                                   (v 0)
                                   (max-v -1)
                                   (max-n -1)
                                   (iprint-alist nil)
                                   (iprint-fal-new nil)
                                   (iprint-fal-old nil)
                                   (eager-p nil))
                        (:instance eviscerate-simple-lemma-eviscerate1
                                   (v 0)
                                   (max-v (or print-level -1))
                                   (max-n (or print-length -1))
                                   (iprint-alist nil)
                                   (iprint-fal-new nil)
                                   (iprint-fal-old nil)
                                   (eager-p nil)))))
  :rule-classes nil)

(verify-termination eviscerate-simple
  (declare (xargs
            :guard-hints
            (("Goal"
              :in-theory (disable assoc-equal eviscerate1 eviscerate1-lst)
              :use eviscerate-simple-lemma-eviscerate)))))

(defthm boundp-global-iprint-hard-bound
  (implies (state-p1 state)
           (assoc-equal 'iprint-hard-bound
                        (nth 2 state)))
  :hints (("Goal" :in-theory (enable state-p1))))

(verify-termination iprint-hard-bound (declare (xargs :verify-guards t)))

(defthm boundp-global-iprint-soft-bound
  (implies (state-p1 state)
           (assoc-equal 'iprint-soft-bound
                        (nth 2 state)))
  :hints (("Goal" :in-theory (enable state-p1))))

(verify-termination iprint-soft-bound (declare (xargs :verify-guards t)))

(verify-termination iprint-last-index*) ; and guards

(defthm boundp-global-iprint-ar
  (implies (state-p1 state)
           (assoc-equal 'iprint-ar
                        (nth 2 state)))
  :hints (("Goal" :in-theory (enable state-p1))))

(verify-termination iprint-last-index) ; and guards

(verify-termination iprint-ar-illegal-index) ; and guards

(verify-termination iprint-enabledp) ; and guards

(verify-termination iprint-blockedp) ; and guards

#+acl2-devel ; avoid non-LOCAL redundant definition error
(verify-termination iprint-ar-aref1) ; and guards

(verify-termination iprint-alistp1-weak) ; and guards

(verify-termination collect-posp-indices-to-header) ; and guards

(verify-termination iprint-fal-name) ; and guards
(verify-termination iprint-eager-p) ; and guards

(defthm symbolp-cdr-last-iprint-falp
  (implies (iprint-falp x)
           (symbolp (cdr (last x)))))

(defthm boundp-global-iprint-fal
  (implies (state-p1 state)
           (assoc-equal 'iprint-fal
                        (nth 2 state)))
  :hints (("Goal" :in-theory (enable state-p1))))

(verify-termination init-iprint-fal) ; and guards

; Perhaps the following can be replaced by the later lemma,
; state-p1-put-global, followed by (in-theory (disable put-global)).
(defthm state-p1-update-nth-2-add-pair
  (implies (and (state-p1 state)
                (symbolp name)
                (not (eq name 'current-acl2-world))
                (not (eq name 'timer-alist)))
           (state-p1 (update-nth 2
                                 (add-pair name val (nth 2 state))
                                 state)))
  :hints (("Goal" :in-theory (enable state-p1))))

(defthm alistp-collect-posp-indices-to-header
  (implies (and (array1p 'iprint-ar iprint-ar)
                (alistp iprint-alist))
           (alistp (collect-posp-indices-to-header iprint-ar iprint-alist))))

(defthm iprint-alistp1-forward-to-iprint-alistp1-weak
  (implies (iprint-alistp1 x)
           (iprint-alistp1-weak x))
  :rule-classes :forward-chaining)

(defthm iprint-alistp1-weak-forward-to-alistp
  (implies (iprint-alistp1-weak x)
           (alistp x))
  :rule-classes :forward-chaining)

(defthm iprint-array-p-monotone
  (implies (and (iprint-array-p ar n1)
                (<= n1 n2))
           (iprint-array-p ar n2)))

(defthm bounded-integer-alistp-monotone
  (implies (and (bounded-integer-alistp iprint-alist n1)
                (<= n1 n2))
           (bounded-integer-alistp iprint-alist n2)))

(defthm bounded-integer-alistp-collect-posp-indices-to-header
  (implies (and (bounded-integer-alistp iprint-alist bound)
                (iprint-array-p iprint-ar bound))
           (bounded-integer-alistp
            (collect-posp-indices-to-header iprint-ar iprint-alist)
            bound)))

(defthm iprint-alistp1-implies-bounded-integer-alistp
  (implies (and (iprint-alistp1 x)
                (alistp x)
                (< (caar x) bound))
           (bounded-integer-alistp x bound)))

#+skip
(defthm bounded-integer-alistp-collect-posp-indices-to-header
  (implies (and (consp iprint-alist)
                (iprint-alistp1 iprint-alist)
                (iprint-array-p iprint-ar bound)
                (natp bound)
                (< (caar iprint-alist) bound))
           (bounded-integer-alistp
            (collect-posp-indices-to-header iprint-ar iprint-alist)
            bound))
  :hints
  (("Goal"
    :use
    ((:instance bounded-integer-alistp-collect-posp-indices-to-header-lemma
                (bound1 bound)
                (bound2 bound))))))

(verify-termination rollover-iprint-ar ; and guards
  (declare (xargs :guard-hints (("Goal" :do-not-induct t)))))

(verify-termination update-iprint-fal-rec) ; and guards
(verify-termination update-iprint-fal) ; and guards

(in-theory (disable rollover-iprint-ar))

(defthm iprint-alistp1-forward-to-nat-alistp
  (implies (iprint-alistp1 x)
           (nat-alistp x))
  :rule-classes :forward-chaining)

(encapsulate
  ()
  (local (include-book "kestrel"))
  (verify-termination aset1-lst) ; and guards
  )

; The following proves without needing a lemma about bounded-integer-listp,
; because it proves the relevant top-level checkpoints by induction.
(verify-termination update-iprint-ar-fal) ; and guards

(defthm state-p1-put-global
  (implies (and (state-p1 state)
                (symbolp name)
                (not (eq name 'current-acl2-world))
                (not (eq name 'timer-alist)))
           (state-p1 (put-global name value state)))
  :hints (("Goal" :in-theory (enable state-p1))))

(in-theory (disable put-global))

(verify-termination iprint-oracle-updates?) ; and guards

; The rest of this file was originally developed before eviscerate-top was
; redefined to call brr-evisc-tuple-oracle-update.  It seems to me that the
; easiest way to modify the proof is to introduce the following function
; composition and replace the original lemmas about iprint-oracle-updates? with
; lemmas about this composition.

(defun-nx composed-oracle-updates (state)
  (brr-evisc-tuple-oracle-update
   (iprint-oracle-updates? state)))

; It seems simpler to reason about boundp-global than about calls of
; assoc-equal into (nth 2 <some-state>).  But boundp-global1 is called in the
; guard of get-global, so we deal with boundp-global1 instead.

(defthm assoc-equal-read-acl2-oracle
  (implies (assoc-equal name (nth 2 state))
           (assoc-equal name
                        (nth 2 (mv-nth 2 (read-acl2-oracle state)))))
  :hints (("Goal" :in-theory (enable read-acl2-oracle
                                     update-acl2-oracle))))

(in-theory (disable standard-evisc-tuplep
                    aref1 array1p iprint-blockedp
                    nfix nth iprint-last-index* natp)) ; for efficiency

(defthm boundp-global1-iprint-fal-composed-oracle-updates
  (implies (boundp-global1 name state)
           (boundp-global1 name
                           (composed-oracle-updates state)))
  :hints (("Goal" :in-theory (enable put-global))))

(defthm nth-2-mv-nth-2-read-acl2-oracle
  (equal (nth 2 (mv-nth 2 (read-acl2-oracle state)))
         (nth 2 state))
  :hints (("Goal" :in-theory (enable read-acl2-oracle
                                     update-acl2-oracle))))

(in-theory (disable )) ; for efficiency

(defthm iprint-falp-get-global-iprint-fal-composed-oracle-updates
  (implies (iprint-falp (get-global 'iprint-fal state))
           (iprint-falp (get-global 'iprint-fal
                                    (composed-oracle-updates state))))
  :hints (("Goal" :in-theory (enable put-global))))

(defthm state-p1-composed-oracle-updates
  (implies (state-p1 state)
           (state-p1 (composed-oracle-updates state))))

(defthm array1p-iprint-ar-composed-oracle-updates
  (implies (array1p 'iprint-ar (get-global 'iprint-ar state))
           (array1p 'iprint-ar (get-global 'iprint-ar
                                           (composed-oracle-updates state))))
  :hints (("Goal" :in-theory (enable put-global))))

(defthm natp-iprint-hard-bound-composed-oracle-updates
  (implies (natp (get-global 'iprint-hard-bound state))
           (natp (get-global 'iprint-hard-bound
                             (composed-oracle-updates state))))
  :hints (("Goal" :in-theory (enable put-global))))

(defthm iprint-hard-bound-inequality-preserved-by-iprint-oracle-updates?
  (implies (<= (* 4
                  (+ 1
                     (get-global 'iprint-hard-bound state)))
               (array-maximum-length-bound))
           (<= (* 4
                  (+ 1
                     (get-global 'iprint-hard-bound
                                 (composed-oracle-updates state))))
               (array-maximum-length-bound)))
  :hints (("Goal" :in-theory (enable put-global)))
  :rule-classes :linear)

(defmacro dimension (ar)

; I need a lemma about the following term, which represents the dimension of an
; array, so I'm introducing this abbreviation.

  `(car
    (cadr
     (assoc-keyword
      :dimensions
      (cdr
       (assoc-equal :header ,ar))))))

(thm ; sanity check
 (equal (car (dimensions name x))
        (dimension x)))

(defthm iprint-hard-bound-<-dimension-iprint-ar-iprint-after-composed-oracle-updates
  (implies (< (get-global 'iprint-hard-bound state)
              (dimension (get-global 'iprint-ar state)))
           (< (get-global 'iprint-hard-bound
                          (composed-oracle-updates state))
              (dimension (get-global 'iprint-ar
                                     (composed-oracle-updates state)))))
  :hints (("Goal" :in-theory (enable put-global)))
  :rule-classes :linear)

(in-theory (disable boundp-global1 get-global composed-oracle-updates
                    assoc-equal
                    ))

; Start proof of verify-termination (really, guard verification) for
; eviscerate-top with its subfunctions disabled.

(defthm iprint-array-p-implies-rationalp-car-dimensions
  (implies (array1p name ar)
           (rationalp (car (dimensions name ar)))))

(defthm iprint-array-p-implies-consp-dimensions
  (implies (array1p name ar)
           (consp (dimensions name ar))))

(defthm composed-oracle-updates-preserves-natp-iprint-last-index
  (implies (natp (iprint-last-index state))
           (natp (iprint-last-index (composed-oracle-updates state))))
  :hints (("Goal" :in-theory (enable composed-oracle-updates
                                     update-acl2-oracle
                                     get-global
                                     put-global)))
  :rule-classes :type-prescription)

(defthm iprint-alistp1-mv-nth-1-eviscerate
  (let ((result
         (mv-nth
          1
          (eviscerate x print-level print-length alist evisc-table hiding-cars
                      iprint-alist iprint-fal-new iprint-fal-old eager-p))))
    (implies (and (iprint-alistp iprint-alist)
                  (not (eq result t))
                  (not (natp result)))
             (iprint-alistp1 result))))

(defthm iprint-falp-mv-nth-2-eviscerate
  (implies
   (and (iprint-alistp iprint-alist)
        (iprint-falp iprint-fal-new))
   (iprint-falp
    (mv-nth
     2
     (eviscerate x print-level print-length alist evisc-table hiding-cars
                 iprint-alist iprint-fal-new iprint-fal-old eager-p)))))

(encapsulate
  ()

  (local
   (defthm-flag-eviscerate1

     (defthm lemma-eviscerate1
       (implies
        (symbolp iprint-alist)
        (symbolp
         (mv-nth
          1
          (eviscerate1 x v max-v max-n alist evisc-table hiding-cars
                       iprint-alist iprint-fal-new iprint-fal-old eager-p))))
       :flag eviscerate1)

     (defthm lemma-eviscerate1-lst
       (implies
        (symbolp iprint-alist)
        (symbolp
         (mv-nth
          1
          (eviscerate1-lst lst v n max-v max-n alist evisc-table hiding-cars
                           iprint-alist iprint-fal-new iprint-fal-old eager-p))))
       :flag eviscerate1-lst)

     :hints (("Goal" :in-theory (disable assoc-equal update-iprint-alist-fal posp)))
     ))

  (defthm not-consp-iprint-alist-from-eviscerate-with-nil-iprint-last-index
    (not
     (consp
      (mv-nth
       1
       (eviscerate x print-level print-length alist evisc-table hiding-cars
                   nil ; ; iprint-last-index
                   iprint-fal-new iprint-fal-old
                   eager-p)))))

  (defthm not-consp-iprint-alist-from-eviscerate1-with-nil-iprint-last-index
    (implies
     (symbolp iprint-alist)
     (not
      (consp
       (mv-nth
        1
        (eviscerate1 x v max-v max-n alist evisc-table hiding-cars
                     iprint-alist iprint-fal-new iprint-fal-old eager-p)))))
    :hints (("Goal" :use lemma-eviscerate1))))

; Start proof of
; iprint-array-p-preserved-by-eviscerate-and-iprint-oracle-updates?.

(defthm iprint-array-p-preserved-by-eviscerate-and-composed-oracle-updates-lemma
  (implies (iprint-array-p (get-global 'iprint-ar state)
                           (1+ (iprint-last-index state)))
           (iprint-array-p
            (get-global 'iprint-ar
                        (composed-oracle-updates state))
            (1+ (iprint-last-index (composed-oracle-updates state)))))
  :hints (("Goal" :in-theory (e/d (put-global
                                   get-global
                                   composed-oracle-updates)
                                  (iprint-array-p))))
  :rule-classes nil)

(defthm-flag-eviscerate1

  (defthm eviscerate1-adds-bigger-index
    (let ((iprint-alist-new
           (mv-nth
            1
            (eviscerate1 x v max-v max-n alist evisc-table hiding-cars
                         iprint-alist
                         iprint-fal-new iprint-fal-old eager-p)))
          (k (if (consp iprint-alist)
                 (car (car iprint-alist))
               iprint-alist)))
      (implies
       (natp k)
       (or (and (integerp (car (car iprint-alist-new)))
                (< k
                   (car (car iprint-alist-new))))
           (equal iprint-alist iprint-alist-new))))
    :rule-classes nil
    :flag eviscerate1)

  (defthm eviscerate1-lst-adds-bigger-index
    (let ((iprint-alist-new
           (mv-nth
            1
            (eviscerate1-lst lst v n max-v max-n alist evisc-table
                             hiding-cars
                             iprint-alist
                             iprint-fal-new iprint-fal-old eager-p)))
          (k (if (consp iprint-alist)
                 (car (car iprint-alist))
               iprint-alist)))
      (implies
       (natp k)
       (or (and (integerp (car (car iprint-alist-new)))
                (< k
                   (car (car iprint-alist-new))))
           (equal iprint-alist iprint-alist-new))))
    :rule-classes nil
    :flag eviscerate1-lst)

  )

(in-theory (disable eviscerate1 eviscerate1-lst))

(defthm eviscerate-adds-bigger-index-main
  (let ((iprint-alist-new
         (mv-nth
          1
          (eviscerate x print-level print-length alist evisc-table hiding-cars
                      iprint-last-index
                      iprint-fal-new iprint-fal-old
                      eager-p))))
    (implies
     (and (natp iprint-last-index)
          (consp iprint-alist-new)
          (or print-level
              print-length))
     (<= (1+ iprint-last-index)
         (car (car iprint-alist-new)))))
  :hints (("Goal" :use ((:instance eviscerate1-adds-bigger-index
                                   (x (if eager-p (hons-copy x) x))
                                   (v 0)
                                   (max-v (or print-level -1))
                                   (max-n (or print-length -1))
                                   (iprint-alist iprint-last-index)))))
  :rule-classes nil)

(defthm natp-iprint-last-index-composed-oracle-updates
  (implies (natp (iprint-last-index state))
           (natp (iprint-last-index (composed-oracle-updates state))))
  :rule-classes :type-prescription)

(defthm iprint-array-p-preserved-by-eviscerate-and-composed-oracle-updates
  (let ((iprint-alist-new
         (mv-nth
          1
          (eviscerate x print-level print-length alist evisc-table hiding-cars
                      (iprint-last-index (composed-oracle-updates state))
                      iprint-fal-new iprint-fal-old
                      eager-p))))
    (implies
     (and (natp (iprint-last-index state))
          (consp iprint-alist-new)
          (iprint-array-p
           (get-global 'iprint-ar state)
           (1+ (iprint-last-index state))))
     (iprint-array-p
      (get-global 'iprint-ar
                  (composed-oracle-updates state))
      (car (car iprint-alist-new)))))
  :hints
  (("Goal"
    :in-theory (disable iprint-last-index)
    :use
    (iprint-array-p-preserved-by-eviscerate-and-composed-oracle-updates-lemma
     (:instance eviscerate-adds-bigger-index-main
                (iprint-last-index (iprint-last-index
                                    (composed-oracle-updates state))))))))

(encapsulate
  ()

; Sigh, I need lemmas already proved above except that they are needed in terms
; of boundp-global1.

  (local (in-theory (enable boundp-global1)))

  (defthm boundp-global1-iprint-hard-bound
    (implies (state-p1 state)
             (boundp-global1 'iprint-hard-bound state))
    :hints (("Goal" :in-theory (enable state-p1))))

  (defthm boundp-global1-iprint-soft-bound
    (implies (state-p1 state)
             (boundp-global1 'iprint-soft-bound state))
    :hints (("Goal" :in-theory (enable state-p1))))

  (defthm boundp-global1-iprint-ar
    (implies (state-p1 state)
             (boundp-global1 'iprint-ar state))
    :hints (("Goal" :in-theory (enable state-p1))))

  (defthm boundp-global1-iprint-fal
    (implies (state-p1 state)
             (boundp-global1 'iprint-fal state))
    :hints (("Goal" :in-theory (enable state-p1)))))

(defthm one-more-lemma ; I'm tired of naming these!
  (implies (< (get-global 'iprint-hard-bound state)
              (car (dimensions 'iprint-ar
                               (get-global 'iprint-ar state))))
           (< (get-global 'iprint-hard-bound
                          (composed-oracle-updates state))
              (car (dimensions 'iprint-ar
                               (get-global 'iprint-ar
                                           (composed-oracle-updates state)))))))

(defthm fold-into-composed-oracle-updates
  (equal (brr-evisc-tuple-oracle-update
          (iprint-oracle-updates? state))
         (composed-oracle-updates state))
  :hints (("Goal" :in-theory (enable composed-oracle-updates))))

(verify-termination eviscerate-top-state-p) ; and guards

(verify-termination eviscerate-top ; and guards
  (declare (xargs :guard-hints
                  (("Goal"
                    :in-theory
                    (disable assoc-equal
                             dimensions
                             array1p
                             eviscerate
                             update-iprint-ar-fal
                             iprint-enabledp
                             iprint-last-index
                             iprint-eager-p
                             brr-evisc-tuple-oracle-update
                             iprint-oracle-updates?
                             composed-oracle-updates))))))
