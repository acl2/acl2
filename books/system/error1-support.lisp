; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore, July-August 2023
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "fmt-support")

; For abbrev-evisc-tuple and maybe others:
(include-book "system/verified-termination-and-guards" :dir :system)

(in-theory (disable array1p iprint-last-index fmt-state-p
                    standard-evisc-tuplep))

(defthm fmt0-preserves-array1p-iprint-ar
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 channel :character state))
           (array1p
            'iprint-ar
            (cdr
             (assoc-equal
              'iprint-ar
              (nth 2
                   (mv-nth 1
                           (fmt0 s alist i maximum col pn channel state
                                 evisc-tuple clk)))))))
  :hints (("Goal"
           :in-theory (e/d (fmt-state-p eviscerate-top-state-p)
                           (fmt-state-p-fmt0))
           :use fmt-state-p-fmt0)))

(verify-termination fmt-abbrev1 ; and guards
  (declare (xargs :guard-hints (("Goal" :do-not-induct t)))))

(verify-termination fmt-abbrev) ; and guards

(verify-termination fmt-ctx ; and guards
; For efficiency only:
  (declare (xargs :guard-hints
                  (("Goal" :in-theory (disable abbrev-evisc-tuple
                                               member-equal
                                               world-evisceration-alist))))))

(defthm standard-evisc-tuplep-suff
  (implies (or (null x)
               (and (true-listp x)
                    (= (length x) 4)
                    (alistp (car x))
                    (or (null (cadr x))
                        (integerp (cadr x)))
                    (or (null (caddr x))
                        (integerp (caddr x)))
                    (symbol-listp (cadddr x))))
           (standard-evisc-tuplep x))
  :hints (("Goal" :in-theory (enable standard-evisc-tuplep))))

(defconst *fmt-globals*

; These are the state globals that can be modified by fmt.

  '(iprint-ar
    brr-evisc-tuple
    evisc-hitp-without-iprint
    iprint-fal
    wormhole-status
    iprint-hard-bound
    iprint-soft-bound))

(make-event
; Avoid excessive output during development.
 (if (@ certify-book-info)
     (value '(value-triple nil))
   (er-progn (set-evisc-tuple (evisc-tuple 6 10 nil nil)
                              :iprint t
                              :sites :all)
             (set-iprint t :soft-bound 100000 :hard-bound 110000)
             (value '(value-triple nil)))))

; Start proof of fmt0-preserves-globals.

(defthm spaces1-preserves-globals
  (equal (assoc-equal sym
                      (nth 2
                           (spaces1 n col hard-right-margin channel state)))
         (assoc-equal sym (nth 2 state))))

(defthm spaces-preserves-globals
  (equal (assoc-equal sym
                      (nth 2
                           (spaces n col channel state)))
         (assoc-equal sym (nth 2 state)))
  :hints (("Goal" :in-theory (enable spaces))))

(defthm prin1-with-slashes1-preserves-globals
  (equal (assoc-equal sym
                      (nth 2
                           (prin1-with-slashes1 l slash-char channel state)))
         (assoc-equal sym (nth 2 state))))

(defthm prin1-with-slashes-preserves-globals
  (equal (assoc-equal sym
                      (nth 2
                           (prin1-with-slashes s slash-char channel state)))
         (assoc-equal sym (nth 2 state)))
  :hints (("Goal" :in-theory (enable prin1-with-slashes))))

(defthm splat-atom-preserves-globals
  (equal (assoc-equal sym
                      (nth 2
                           (mv-nth 1
                                   (splat-atom x print-base print-radix indent
                                               col channel state))))
         (assoc-equal sym (nth 2 state)))
  :hints (("Goal" :in-theory (enable splat-atom))))

(defthm splat-string-preserves-globals
  (equal (assoc-equal sym
                      (nth 2
                           (mv-nth 1
                                   (splat-string x indent col channel state))))
         (assoc-equal sym (nth 2 state)))
  :hints (("Goal" :in-theory (enable splat-string))))

(defthm-flag-splat

(defthm splat-preserves-globals
  (equal (assoc-equal sym
                      (nth 2
                           (mv-nth 1
                                   (splat x print-base print-radix indent
                                          eviscp col channel state))))
         (assoc-equal sym (nth 2 state)))
  :flag splat)

(defthm splat1-preserves-globals
  (equal (assoc-equal sym
                      (nth 2
                           (mv-nth 1
                                   (splat1 x print-base print-radix indent
                                           eviscp col channel state))))
         (assoc-equal sym (nth 2 state)))
  :flag splat1)
)

(defthm eviscerate-top-preserves-globals
  (implies
   (not (member-equal sym *fmt-globals*))
   (equal (assoc-equal sym
                       (nth 2
                            (mv-nth 1
                                    (eviscerate-top x print-level print-length
                                                    alist evisc-table
                                                    hiding-cars state) )))
          (assoc-equal sym (nth 2 state))))
  :hints (("Goal" :in-theory (enable eviscerate-top))))

(defthm-flag-flpr1
  (defthm flpr1-preserves-globals
    (equal (assoc-equal sym
                        (nth 2
                             (flpr1 x channel state eviscp)))
           (assoc-equal sym (nth 2 state)))
    :flag flpr1)
  (defthm flpr11-preserves-globals
    (equal (assoc-equal sym
                        (nth 2
                             (flpr11 x channel state eviscp)))
           (assoc-equal sym (nth 2 state)))
    :flag flpr11))

(defthm ppr2-flat-preserves-globals
  (equal (assoc-equal sym
                      (nth 2
                           (ppr2-flat x channel state eviscp)))
         (assoc-equal sym (nth 2 state))))

(defthm-flag-ppr2
  (defthm ppr2-column-preserves-globals
    (equal (assoc-equal sym
                        (nth 2
                             (ppr2-column lst loc col channel state eviscp)))
           (assoc-equal sym (nth 2 state)))
    :flag ppr2-column)
  (defthm ppr2-preserves-globals
    (equal (assoc-equal sym
                        (nth 2
                             (ppr2 x col channel state eviscp)))
           (assoc-equal sym (nth 2 state)))
    :flag ppr2))

(defthm fmt-ppr-preserves-globals
  (equal (assoc-equal sym
                      (nth 2
                           (fmt-ppr x width rpc col channel state eviscp)))
         (assoc-equal sym (nth 2 state)))
  :hints (("Goal" :in-theory (enable fmt-ppr))))

(defthm-flag-fmt0

  (defthm fmt0*-preserves-globals
    (implies
     (not (member-equal sym *fmt-globals*))
     (equal (assoc-equal sym
                         (nth 2
                              (mv-nth 1
                                      (fmt0* str0 str1 str2 str3 lst alist col
                                             channel state evisc-tuple clk))))
            (assoc-equal sym (nth 2 state))))
    :flag fmt0*)

  (defthm fmt0&v-preserves-globals
    (implies
     (not (member-equal sym *fmt-globals*))
     (equal (assoc-equal sym
                         (nth 2
                              (mv-nth 1
                                      (fmt0&v flg lst punct col channel state
                                              evisc-tuple clk))))
            (assoc-equal sym (nth 2 state))))
    :flag fmt0&v)

  (defthm spell-number-preserves-globals
    (implies
     (not (member-equal sym *fmt-globals*))
     (equal (assoc-equal sym
                         (nth 2
                              (mv-nth 1
                                      (spell-number n cap col channel state
                                                    evisc-tuple clk))))
            (assoc-equal sym (nth 2 state))))
    :flag spell-number)

  (defthm fmt-tilde-s-preserves-globals
    (implies
     (not (member-equal sym *fmt-globals*))
     (equal (assoc-equal sym
                         (nth 2
                              (mv-nth 1
                                      (fmt-tilde-s s col channel state clk))))
            (assoc-equal sym (nth 2 state))))
    :flag fmt-tilde-s)

  (defthm fmt-tilde-cap-s-preserves-globals
    (implies
     (not (member-equal sym *fmt-globals*))
     (equal (assoc-equal sym
                         (nth 2
                              (mv-nth 1
                                      (fmt-tilde-cap-s s col channel state clk))))
            (assoc-equal sym (nth 2 state))))
    :flag fmt-tilde-cap-s)

  (defthm fmt0-preserves-globals
    (implies
     (not (member-equal sym *fmt-globals*))
     (equal (assoc-equal sym
                         (nth 2
                              (mv-nth 1
                                      (fmt0 s alist i maximum col pn channel
                                            state evisc-tuple clk))))
            (assoc-equal sym (nth 2 state))))
    :flag fmt0)

  :hints (("Goal"
           :expand
           ((:free (str0 str1 str2 str3 lst alist col channel state)
                   (fmt0* str0 str1 str2 str3 lst alist col channel state
                          evisc-tuple clk))
            (:free (flg lst punct col channel state evisc-tuple)
                   (fmt0&v flg lst punct col channel state evisc-tuple clk))
            (:free (n cap col channel state evisc-tuple)
                   (spell-number n cap col channel state evisc-tuple clk))
            (:free (col channel state)
                   (fmt-tilde-s s col channel state clk))
            (:free (col channel state)
                   (fmt-tilde-cap-s s col channel state clk))
            (:free (alist i maximum col pn channel state evisc-tuple)
                   (fmt0 s alist i maximum col pn channel state evisc-tuple
                         clk)))
           :in-theory
           (e/d ()
                (splat
                 fmt0* fmt0&v spell-number fmt-tilde-s fmt-tilde-cap-s fmt0
                 punctp
                 characterp-fmt-char-type-prescription-forced
                 characterp-fmt-char
                 find-alternative-skip
                 find-alternative-stop
                 natp-find-alternative-stop
                 find-alternative-stop
                 cancel_times-equal-correct
                 cancel_plus-equal-correct
                 fold-consts-in-+
                 rationalp-implies-acl2-numberp
                 assoc-equal
                 natp-find-alternative-skip
                 mv-nth
                 fmt-var
                 spaces1
                 standard-evisc-tuplep
                 scan-past-whitespace
                 princ$
                 fmt-state-p
                 min-fixnat$inline
                 min
                 fix
                 member-equal
                 ))))
  )

(defthm natp-fmt0-rewrite
; This avoids some expensive forcing in (verify-termination fmt-in-ctx).
  (implies
   (and (natp col)
        (fmt-state-p state)
        (open-output-channel-p1 channel
                                :character state))
   (natp (car (fmt0 s alist i maximum col pn
                    channel state evisc-tuple clk)))))

(verify-termination fmt-in-ctx) ; and guards

(verify-termination er-off-p1) ; and guards
(verify-termination er-off-p) ; and guards

(in-theory (disable fmt-abbrev1 abbrev-evisc-tuple fmt-ctx fmt-in-ctx fmt1
                    world-evisceration-alist))

(defthm fmt1-preserves-globals
  (implies
   (not (member-equal sym *fmt-globals*))
   (equal (assoc-equal sym
                       (nth 2
                            (mv-nth 1
                                    (fmt1 str alist col channel state
                                          evisc-tuple))))
          (assoc-equal sym (nth 2 state))))
  :hints (("Goal" :in-theory (enable fmt1))))

(defthm fmt-preserves-globals
  (implies
   (not (member-equal sym *fmt-globals*))
   (equal (assoc-equal sym
                       (nth 2
                            (mv-nth 1
                                    (fmt str alist channel state
                                         evisc-tuple))))
          (assoc-equal sym (nth 2 state))))
  :hints (("Goal" :in-theory (enable fmt))))

(defthm fmt-abbrev1-preserves-globals
  (implies
   (not (member-equal sym *fmt-globals*))
   (equal (assoc-equal sym
                       (nth 2
                            (mv-nth 1
                                    (fmt-abbrev1 str alist col channel state
                                                 suffix-msg))))
          (assoc-equal sym (nth 2 state))))
  :hints (("Goal" :in-theory (enable fmt-abbrev1))))

(defthm fmt-abbrev-preserves-globals
  (implies
   (not (member-equal sym *fmt-globals*))
   (equal (assoc-equal sym
                       (nth 2
                            (fmt-abbrev str alist col channel state
                                        suffix-msg)))
          (assoc-equal sym (nth 2 state))))
  :hints (("Goal" :in-theory (enable fmt-abbrev))))

(defthm fmt-ctx-preserves-abbrev-evisc-tuple
  (equal (abbrev-evisc-tuple (mv-nth 1
                                     (fmt-ctx ctx col channel state)))
         (abbrev-evisc-tuple state))
  :hints (("Goal" :in-theory (enable abbrev-evisc-tuple
                                     fmt-ctx
                                     world-evisceration-alist))))

(defthm fmt0-preserves-abbrev-evisc-tuple
  (equal (abbrev-evisc-tuple (mv-nth 1
                                     (fmt0 s alist i maximum col pn channel
                                           state evisc-tuple clk)))
         (abbrev-evisc-tuple state))
  :hints (("Goal" :in-theory (enable abbrev-evisc-tuple
                                     world-evisceration-alist))))

(defthm fmt1-preserves-abbrev-evisc-tuple
  (equal (abbrev-evisc-tuple (mv-nth 1
                                     (fmt1 str alist col channel state
                                           evisc-tuple)))
         (abbrev-evisc-tuple state))
  :hints (("Goal" :in-theory (enable fmt1))))

(defthm fmt-in-ctx-preserves-abbrev-evisc-tuple
  (equal (abbrev-evisc-tuple (mv-nth 1
                                     (fmt-in-ctx ctx col channel state)))
         (abbrev-evisc-tuple state))
  :hints (("Goal" :in-theory (enable ;abbrev-evisc-tuple
                                     fmt-in-ctx
                                     ;world-evisceration-alist
                                     ))))

(defthm open-output-channel-p1-fmt1
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 channel :character state))
           (open-output-channel-p1 channel :character
                                   (mv-nth 1 (fmt1 str alist col channel state
                                                   evisc-tuple))))
  :hints (("Goal" :in-theory (enable fmt1))))

(defthm-od fmt1
  :mv-nth 1
  :hints (("Goal" :in-theory (enable fmt1))))

(defthm open-output-channel-p1-fmt1-strong
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 chan1 :character state))
           (open-output-channel-p1 chan1 :character
                                   (mv-nth 1 (fmt1 str alist col channel state
                                                   evisc-tuple))))
  :hints (("Goal"
           :cases ((equal chan1 channel))
           :in-theory (enable* open-output-channel-diff))))

(defthm fmt-state-p-fmt1
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 channel :character state))
           (fmt-state-p (mv-nth 1
                                (fmt1 str alist col channel state
                                      evisc-tuple))))
  :hints (("Goal" :in-theory (enable fmt1))))

(defthm open-output-channel-p1-fmt-abbrev1
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 channel :character state))
           (open-output-channel-p1 channel :character
                                   (mv-nth 1 (fmt-abbrev1 str alist col channel
                                                          state suffix-msg))))
  :hints (("Goal" :in-theory (enable fmt-abbrev1))))

(defthm-od fmt-abbrev1
  :mv-nth 1
  :hints (("Goal" :in-theory (enable fmt-abbrev1))))

(defthm open-output-channel-p1-fmt-ctx
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 channel :character state))
           (open-output-channel-p1 channel :character
                                   (mv-nth 1 (fmt-ctx ctx col channel state))))
  :hints (("Goal" :in-theory (enable fmt-ctx))))

(defthm-od fmt-ctx
  :mv-nth 1
  :hints (("Goal" :in-theory (enable fmt-ctx))))

(defthm fmt-state-p-fmt-abbrev1
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 channel :character state))
           (fmt-state-p (mv-nth 1
                                (fmt-abbrev1 str alist col channel state
                                             suffix-msg))))
  :hints (("Goal" :in-theory (enable fmt-abbrev1))))

(defthm fmt-state-p-fmt-ctx
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 channel :character state))
           (fmt-state-p (mv-nth 1
                                (fmt-ctx ctx col channel state))))
  :hints (("Goal" :in-theory (enable fmt-ctx))))

(defthm open-output-channel-p1-fmt-in-ctx
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 channel :character state))
           (open-output-channel-p1 channel :character
                                   (mv-nth 1 (fmt-in-ctx ctx col channel
                                                         state))))
  :hints (("Goal" :in-theory (enable fmt-in-ctx))))

(defthm-od fmt-in-ctx
  :mv-nth 1
  :hints (("Goal" :in-theory (enable fmt-in-ctx))))

(defthm natp-fmt1
  (implies
   (and (natp col)
        (fmt-state-p state)
        (open-output-channel-p1 channel :character state))
   (natp (car (fmt1 str alist col channel state evisc-tuple))))
  :rule-classes (:type-prescription :rewrite)
  :hints (("goal" :in-theory (enable fmt1))))

(defthm fmt1-bound
  (implies
   (and (natp col)
        (fmt-state-p state)
        (open-output-channel-p1 channel :character state)
        (character-alistp alist))
   (<= (car (fmt1 str alist col channel state evisc-tuple))
       (fixnum-bound)))
  :rule-classes (:linear :rewrite)
  :hints (("goal" :in-theory (enable fmt1))))

(defthm integer-range-p-0
; Stop introducing integerp into proof (found using with-brr-data):
  (equal (integer-range-p 0 upper x)
         (and (natp x)
              (< x upper))))

(defthm natp-fmt-abbrev1
  (implies
   (and (natp col)
        (fmt-state-p state)
        (open-output-channel-p1 channel :character state))
   (natp (car (fmt-abbrev1 str alist col channel state suffix-msg))))
  :rule-classes (:type-prescription :rewrite)
  :hints (("goal" :in-theory (enable fmt-abbrev1))))

(defthm natp-fmt-ctx
  (implies
   (and (natp col)
        (fmt-state-p state)
        (open-output-channel-p1 channel :character state))
   (natp (car (fmt-ctx ctx col channel state))))
  :rule-classes (:type-prescription :rewrite)
  :hints (("goal" :in-theory (enable fmt-ctx))))

(defthm world-evisceration-alist-princ$
  (equal (world-evisceration-alist (princ$ x channel state) y)
         (world-evisceration-alist state y))
  :hints (("Goal" :in-theory (enable world-evisceration-alist))))

(defthm abbrev-evisc-tuple-princ$
  (equal (abbrev-evisc-tuple (princ$ x channel state))
         (abbrev-evisc-tuple state))
  :hints (("Goal" :in-theory (enable abbrev-evisc-tuple))))

(verify-termination error-fms-channel ; and guards
  (declare (xargs :guard-hints (("Goal" :in-theory (enable fmt-in-ctx))))))

(verify-termination standard-co ; and guards
  (declare (xargs :verify-guards t)))

(verify-termination error-fms ; and guards
  (declare (xargs :guard-hints
                  (("Goal" :in-theory (enable error-fms-channel))))))

; Start proof of (verify-termination error1)

(defthm fmt-state-p-fmt-in-ctx
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 channel :character state))
           (fmt-state-p (mv-nth 1
                                (fmt-in-ctx ctx col channel state))))
  :hints (("Goal" :in-theory (enable fmt-in-ctx))))

(defthm fmt-state-p-error-fms
  (implies (and (fmt-state-p state)
                (open-output-channel-p (standard-co state) :character state))
           (fmt-state-p (error-fms hardp ctx summary str alist state)))
  :rule-classes (:rewrite
                 (:forward-chaining
                  :trigger-terms
                  ((error-fms hardp ctx summary str alist state)))))

(defthm fmt-ctx-preserves-globals
  (implies
   (not (member-equal sym *fmt-globals*))
   (equal (assoc-equal sym
                       (nth 2
                            (mv-nth 1 (fmt-ctx ctx col channel state))))
          (assoc-equal sym (nth 2 state))))
  :hints (("Goal" :in-theory (enable fmt-ctx))))

(defthm fmt-in-ctx-preserves-globals
  (implies
   (not (member-equal sym *fmt-globals*))
   (equal (assoc-equal sym
                       (nth 2
                            (mv-nth 1 (fmt-in-ctx ctx col channel state))))
          (assoc-equal sym (nth 2 state))))
  :hints (("Goal" :in-theory (enable fmt-in-ctx))))

(defthm error-fms-preserves-globals
  (implies
   (not (member-equal sym *fmt-globals*))
   (equal (assoc-equal sym
                       (nth 2
                            (error-fms hardp ctx summary str alist state)))
          (assoc-equal sym (nth 2 state)))))

(defthm error-fms-preserves-open
  (implies
   (not (member-equal sym *fmt-globals*))
   (equal (assoc-equal sym
                       (nth 2
                            (error-fms hardp ctx summary str alist state)))
          (assoc-equal sym (nth 2 state)))))

(defthm open-output-channel-p1-error-fms-standard-co
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 (standard-co state) :character state))
           (open-output-channel-p1 (cdr (assoc-equal 'standard-co (nth 2 state)))
                                   :character
                                   (error-fms hardp ctx summary str alist
                                              state))))

(defthm open-output-channel-p1-error-fms
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 channel :character state))
           (open-output-channel-p1 channel
                                   :character
                                   (error-fms hardp ctx summary str alist
                                              state)))
  :hints (("Goal"
           :cases ((equal channel (standard-co state)))
           :in-theory (e/d* (open-output-channel-diff)
                            ((:e force))))))

(in-theory (disable error-fms))

; From data-structures/list-defthms.lisp:
(defthm update-nth-nth
  (implies
   (< (nfix n) (len x))
   (equal (update-nth n (nth n x) x) x))
  :hints (("Goal" :in-theory (enable nth))))

(defthm update-nth-update-nth-same
  (equal (update-nth n v1
                     (update-nth n v2 x))
         (update-nth n v1 x)))

(defthm len-state->-2
  (implies (state-p1 state)
           (< 2 (len state)))
  :hints (("Goal" :in-theory (enable state-p1))))

(defthm world-evisceration-alist-update-nth-2-add-pair
  (implies (not (equal sym 'current-acl2-world))
           (equal (world-evisceration-alist
                   (update-nth 2 (add-pair sym val global-table) state)
                   alist)
                  (world-evisceration-alist
                   (update-nth 2 global-table state)
                   alist)))
  :hints (("Goal" :in-theory (enable world-evisceration-alist))))

(defthm abbrev-evisc-tuple-update-nth-2-add-pair
  (implies (not (member-equal sym '(abbrev-evisc-tuple current-acl2-world)))
           (equal (abbrev-evisc-tuple
                   (update-nth 2 (add-pair sym val global-table) state))
                  (abbrev-evisc-tuple
                   (update-nth 2 global-table state))))
  :hints (("Goal" :in-theory (enable abbrev-evisc-tuple))))

; Start proof of state-p1-error-fms

(defthm state-p1-fmt0
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 channel :character state))
           (let ((state2
                  (mv-nth
                   1
                   (fmt0 s alist i maximum col pn channel state
                         evisc-tuple clk))))
             (state-p1 state2)))
  :hints (("Goal"
           :in-theory (disable state-p-fmt0)
           :use state-p-fmt0)))

(defthm state-p1-fmt1
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 channel :character state))
           (let ((state2
                  (mv-nth
                   1
                   (fmt1 str alist col channel state evisc-tuple))))
             (state-p1 state2)))
  :hints (("Goal"
           :in-theory (enable fmt1))))

(defthm state-p1-fmt-abbrev1
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 channel :character state))
           (let ((state2
                  (mv-nth
                   1
                   (fmt-abbrev1 str alist col channel state suffix-msg))))
             (state-p1 state2)))
  :hints (("Goal" :in-theory (enable fmt-abbrev1))))

(defthm state-p1-fmt-ctx
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 channel :character state))
           (let ((state2
                  (mv-nth
                   1
                   (fmt-ctx ctx col channel state))))
             (state-p1 state2)))
  :hints (("Goal" :in-theory (enable fmt-ctx))))

(defthm state-p1-fmt-in-ctx
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 channel :character state))
           (let ((state2
                  (mv-nth
                   1
                   (fmt-in-ctx ctx col channel state))))
             (state-p1 state2)))
  :hints (("Goal" :in-theory (enable fmt-in-ctx))))

(defthm state-p1-error-fms
  (implies (and (fmt-state-p state)
                (open-output-channel-p1 (standard-co state) :character state))
           (state-p1 (error-fms hardp ctx summary str alist state)))
  :hints (("Goal" :in-theory (enable error-fms))))

(in-theory (enable* open-output-channel-diff))

(defthm fmt-state-p-put-global-2
  (implies (and (fmt-state-p (update-nth 2 global-table state))
                (symbolp sym)
                (not (equal sym 'timer-alist))
                (not (equal sym 'current-acl2-world))
                (not (equal sym 'fmt-hard-right-margin))
                (not (equal sym 'fmt-soft-right-margin))
                (not (equal sym 'print-base))
                (not (equal sym 'ppr-flat-right-margin))
                (not (equal sym 'iprint-fal))
                (not (equal sym 'iprint-ar))
                (not (equal sym 'iprint-soft-bound))
                (not (equal sym 'iprint-hard-bound))
                (not (equal sym 'brr-evisc-tuple)))
           (fmt-state-p (update-nth 2
                                    (add-pair sym val global-table)
                                    state)))
  :hints (("Goal" :in-theory (enable fmt-state-p eviscerate-top-state-p
                                     iprint-last-index))))

(verify-termination error1-state-p) ; and guards

(defthm standard-evisc-tuplep-abbrev-evisc-tuple
  (let ((e (cdr (assoc-equal 'abbrev-evisc-tuple (nth 2 state)))))
    (implies (or (equal e :default)
                 (standard-evisc-tuplep e) )
             (standard-evisc-tuplep (abbrev-evisc-tuple state))))
  :hints (("Goal" :in-theory (enable abbrev-evisc-tuple
                                     standard-evisc-tuplep
                                     world-evisceration-alist))))

(verify-termination standard-co) ; and guards

(verify-termination error1-state-p) ; and guards

(verify-termination error1) ; and guards

(verify-termination error1-safe) ; and guards
