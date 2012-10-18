; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "f-put-global")

;; Various guard-related facts about IO functions.

(defthm assoc-equal-of-add-pair
    (equal (assoc-equal k1 (add-pair k2 v a))
           (if (equal k1 k2)
               (cons k2 v)
             (assoc-equal k1 a))))

(local (in-theory (disable open-channels-p
                           ordered-symbol-alistp
                           plist-worldp
                           symbol-alistp
                           timer-alistp
                           known-package-alistp
                           true-listp
                           32-bit-integer-listp
                           integer-listp
                           readable-files-p
                           written-files-p
                           read-files-p
                           writeable-files-p
                           true-list-listp
                           all-boundp)))

(local (table evisc-table (list 'quote *INITIAL-GLOBAL-TABLE*) "*INITIAL-GLOBAL-TABLE*"))
(local (in-theory (disable nth update-nth)))

;; Misc.
(defthm open-channel-listp-of-add-pair
  (implies (and (open-channel1 v)
                (open-channel-listp x))
           (open-channel-listp (add-pair k v x))))

(defthm ordered-symbol-alistp-of-add-pair
  (implies (and (symbolp k)
                (ordered-symbol-alistp x))
           (ordered-symbol-alistp (add-pair k v x))))

(defthm open-channels-p-of-add-pair
  (implies (and (symbolp k)
                (open-channel1 v)
                (open-channels-p x))
           (open-channels-p (add-pair k v x)))
  :hints(("Goal" :in-theory (enable open-channels-p))))

(defthm open-channels-p-of-delete-assoc-equal
  (implies (open-channels-p x)
           (open-channels-p (delete-assoc-equal k x)))
  :hints(("Goal" :in-theory (enable open-channels-p
                                    open-channel-listp
                                    ordered-symbol-alistp))))

(defthm lookup-in-readable-files-p
  (implies (and (readable-files-p x)
                (assoc-equal k x)
                (equal type (cadr k)))
           (typed-io-listp (cdr (assoc-equal k x)) type))
  :hints(("Goal" :in-theory (enable readable-files-p))))


;; READING -- opening/closing an input channel
(defthm state-p1-of-open-input-channel
  (implies (and (state-p1 state)
                (stringp fname)
                (member type *file-types*))
           (state-p1 (mv-nth 1 (open-input-channel fname type state))))
  :hints(("Goal" :in-theory (enable state-p1))))

(defthm symbolp-of-open-input-channel
  (symbolp (mv-nth 0 (open-input-channel fname type state)))
  :rule-classes (:rewrite :type-prescription))

(defthm open-input-channel-p1-of-open-input-channel
  (implies (and (state-p1 state)
                (stringp fname)
                (member type *file-types*)
                (equal channel (mv-nth 0 (open-input-channel fname type state)))
                channel)
           (open-input-channel-p1
            channel
            type
            (mv-nth 1 (open-input-channel fname type state))))
  :hints(("Goal" :in-theory (enable state-p1))))




;; helper theorems for reading
(local
 (progn
   (defthm lookup-in-open-channels-p
     (implies (and (open-channels-p x)
                   (assoc k x))
              (open-channel1 (cdr (assoc k x))))
     :hints(("Goal" :in-theory (enable open-channels-p
                                       ordered-symbol-alistp
                                       open-channel-listp))))

   (defthm open-channel1-of-read
     (implies (open-channel1 x)
              (open-channel1 (cons (car x) (cddr x)))))))


(local
 (defthm read-file-listp1-from-open-channel1
   (implies (and (open-channel1 x)
                 (natp y))
            (read-file-listp1 (list (caddar x)
                                    (cadar x)
                                    (cadddr (car x))
                                    y)))
   :hints(("Goal" :in-theory (enable open-channel1 read-file-listp1)))))

;; type is a free variable here.  the two variants that follow try to get
;; around this problem
(defthm state-p1-of-close-input-channel-free
  (implies (and (open-input-channel-p1 channel type state)
                (state-p1 state))
           (state-p1 (close-input-channel channel state)))
  :hints(("Goal" :in-theory (e/d (state-p1
                                  read-files-p)
                                 (read-file-listp1)))))

(defthm state-p1-of-close-input-channel-types
  (implies (and (or (open-input-channel-p1 channel :byte state)
                    (open-input-channel-p1 channel :object state)
                    (open-input-channel-p1 channel :character state))
                (state-p1 state))
           (state-p1 (close-input-channel channel state)))
  :hints(("Goal" :in-theory (disable close-input-channel
                                     open-input-channel-p1))))

(defthm state-p1-of-close-input-channel-of-open
  (implies (and (open-input-channel-p1
                 (mv-nth 0 (open-input-channel fname type state1))
                 type state)
                (state-p1 state))
           (state-p1 (close-input-channel
                      (mv-nth 0 (open-input-channel fname type state1))
                      state)))
  :hints(("Goal" :in-theory (disable close-input-channel
                                     open-input-channel-p1
                                     open-input-channel))))



;; Read-char$
(defthm state-p1-of-read-char$
  (implies (and (state-p1 state)
                (symbolp channel)
                (open-input-channel-p1 channel :character state))
           (state-p1 (mv-nth 1 (read-char$ channel state))))
  :hints(("Goal" :in-theory (e/d (state-p1) (open-channel1)))))

(defthm open-input-channel-p1-of-read-char$
  (implies (and (state-p1 state)
                (open-input-channel-p1 channel :character state))
           (open-input-channel-p1 channel :character (mv-nth 1 (read-char$ channel state)))))

(local (defthm character-cadr-of-open-channel1
         (implies (and (open-channel1 x)
                       (equal (cadar x) :character)
                       (cdr x))
                  (characterp (cadr x)))))

(defthm characterp-of-read-char$
  (implies (and (mv-nth 0 (read-char$ channel state))
                (state-p1 state)
                (open-input-channel-p1 channel :character state))
           (characterp (mv-nth 0 (read-char$ channel state))))
  :hints(("Goal" :in-theory (e/d (state-p1) (open-channel1))))
  :rule-classes
  (:rewrite
   (:type-prescription :corollary
    (implies (and (state-p1 state)
                  (open-input-channel-p1 channel :character state))
             (or (characterp (mv-nth 0 (read-char$ channel state)))
                 (null (mv-nth 0 (read-char$ channel state))))))))


;; since peek-char$ doesn't return state there isn't too much to prove about it
(defthm characterp-of-peek-char$
  (implies (and (peek-char$ channel state)
                (state-p1 state)
                (open-input-channel-p1 channel :character state))
           (characterp (peek-char$ channel state)))
  :hints(("Goal" :in-theory (e/d (state-p1) (open-channel1))))
  :rule-classes
  (:rewrite
   (:type-prescription :corollary
    (implies (and (state-p1 state)
                  (open-input-channel-p1 channel :character state))
             (or (characterp (peek-char$ channel state))
                 (null (peek-char$ channel state)))))))





;; Read-byte$
(defthm state-p1-of-read-byte$
  (implies (and (state-p1 state)
                (symbolp channel)
                (open-input-channel-p1 channel :byte state))
           (state-p1 (mv-nth 1 (read-byte$ channel state))))
  :hints(("Goal" :in-theory (e/d (state-p1) (open-channel1)))))

(defthm open-input-channel-p1-of-read-byte$
  (implies (and (state-p1 state)
                (open-input-channel-p1 channel :byte state))
           (open-input-channel-p1 channel :byte (mv-nth 1 (read-byte$ channel state)))))

;; this should probably be defined elsewhere
(defun bytep (x)
  (declare (xargs :guard t))
  (and (natp x) (< x 256)))


(local (defthm bytep-cadr-of-open-channel1
         (implies (and (open-channel1 x)
                       (equal (cadar x) :byte)
                       (cdr x))
                  (and (bytep (cadr x))
                       (natp (cadr x))
                       (integerp (cadr x))))))
  
(defthm bytep-of-read-byte$
  (implies (and (state-p1 state)
                (open-input-channel-p1 channel :byte state)
                (mv-nth 0 (read-byte$ channel state)))
           (and (bytep (mv-nth 0 (read-byte$ channel state)))
                (natp (mv-nth 0 (read-byte$ channel state)))
                (integerp (mv-nth 0 (read-byte$ channel state)))))
  :hints(("Goal" :in-theory (e/d (state-p1) (open-channel1 bytep)))))

(defthm bytep-of-read-byte$-type
  (implies (and (state-p1 state)
                (open-input-channel-p1 channel :byte state))
           (or (null (mv-nth 0 (read-byte$ channel state)))
               (natp (mv-nth 0 (read-byte$ channel state)))))
  :hints(("Goal" :use bytep-of-read-byte$))
  :rule-classes :type-prescription)

(defthm bytep-of-read-byte$-linear
  (implies (and (state-p1 state)
                (open-input-channel-p1 channel :byte state))
           (and (< (mv-nth 0 (read-byte$ channel state)) 256)
                (<= 0 (mv-nth 0 (read-byte$ channel state)))))
  :hints(("Goal" :use bytep-of-read-byte$))
  :rule-classes :linear)





;; Read-object
(defthm state-p1-of-read-object
  (implies (and (state-p1 state)
                (symbolp channel)
                (open-input-channel-p1 channel :object state))
           (state-p1 (mv-nth 2 (read-object channel state))))
  :hints(("Goal" :in-theory (e/d (state-p1) (open-channel1)))))

(defthm open-input-channel-p1-of-read-object
  (implies (and (state-p1 state)
                (open-input-channel-p1 channel :object state))
           (open-input-channel-p1 channel :object (mv-nth 2 (read-object
                                                             channel state)))))




;; sometimes it's useful to know that state isn't modified when read at EOF
;; (copied from unicode)
(encapsulate
 ()

 (local (defthm lemma
          (equal (equal a (cons x y))
                 (and (consp a)
                      (equal (car a) x)
                      (equal (cdr a) y)))))

 (local (defthm lemma2-char
          (implies (and (open-channel1 foo)
                        (equal (cadar foo) :character)
                        (not (cadr foo)))
                   (equal (cddr foo) (cdr foo)) )))

 (local (defthm lemma2-byte
          (implies (and (open-channel1 foo)
                        (equal (cadar foo) :byte)
                        (not (cadr foo)))
                   (equal (cddr foo) (cdr foo)) )))

 (local (in-theory (disable open-channel1)))

 (local (defthm add-pair-same
          (implies (and (ordered-symbol-alistp x)
                        (assoc-equal k x))
                   (equal (add-pair k (cdr (assoc-equal k x)) x)
                          x))
          :hints(("Goal" :in-theory (enable ordered-symbol-alistp)))))

 (local (defthm update-nth-of-nth-same
          (implies (< (nfix n) (len x))
                   (equal (update-nth n (nth n x) x)
                          x))
          :hints(("Goal" :in-theory (enable nth update-nth)))))
                 

 (defthm state-preserved-by-read-char$-when-eof
   (implies (and (not (mv-nth 0 (read-char$ channel state)))
                 (state-p1 state)
                 (open-input-channel-p1 channel :character state))
            (equal (mv-nth 1 (read-char$ channel state))
                   state))
   :hints(("Goal" :in-theory (e/d (read-char$ state-p1)))))

 (defthm state-preserved-by-read-byte$-when-eof
   (implies (and (not (mv-nth 0 (read-byte$ channel state)))
                 (state-p1 state)
                 (open-input-channel-p1 channel :byte state))
            (equal (mv-nth 1 (read-byte$ channel state))
                   state))
   :hints(("Goal" :in-theory (e/d (read-byte$ state-p1)))))

 (defthm state-preserved-by-read-object-when-eof
   (implies (and (mv-nth 0 (read-object channel state))
                 (state-p1 state)
                 (open-input-channel-p1 channel :object state))
            (equal (mv-nth 2 (read-object channel state))
                   state))
   :hints(("Goal" :in-theory (e/d (read-object state-p1))))))





;; Writing -- opening an output channel
(defthm state-p1-of-open-output-channel
  (implies (and (state-p1 state)
                (stringp fname)
                (member type *file-types*))
           (state-p1 (mv-nth 1 (open-output-channel fname type state))))
  :hints(("Goal" :in-theory (enable state-p1))))

(defthm symbolp-of-open-output-channel
  (symbolp (mv-nth 0 (open-output-channel fname type state)))
  :rule-classes (:rewrite :type-prescription))

(defthm open-output-channel-p1-of-open-output-channel
  (implies (and (state-p1 state)
                (stringp fname)
                (member type *file-types*)
                (equal channel (mv-nth 0 (open-output-channel fname type state)))
                channel)
           (open-output-channel-p1
            channel
            type
            (mv-nth 1 (open-output-channel fname type state))))
  :hints(("Goal" :in-theory (enable state-p1))))


;; this is needed for open-output-channel!.
(defthm open-output-channel-p1-of-put-global
  (equal (open-output-channel-p1 channel type (put-global key val state))
         (open-output-channel-p1 channel type state))
  :hints(("Goal" :in-theory (enable open-output-channel-p1 put-global))))


(local
 (defthm written-file-from-open-channel1
   (implies (and (open-channel1 x)
                 (natp y))
            (written-file (cons (list (caddar x)
                                      (cadar x)
                                      (cadddr (car x))
                                      y)
                                (cdr x))))
   :hints(("Goal" :in-theory (enable open-channel1 written-file)))))


;; type is a free variable here.  the two variants that follow try to get
;; around this problem
(defthm state-p1-of-close-output-channel-free
  (implies (and (open-output-channel-p1 channel type state)
                (state-p1 state))
           (state-p1 (close-output-channel channel state)))
  :hints(("Goal" :in-theory (e/d (state-p1
                                  written-files-p)
                                 (written-file)))))


(defthm state-p1-of-close-output-channel-types
  (implies (and (or (open-output-channel-p1 channel :byte state)
                    (open-output-channel-p1 channel :object state)
                    (open-output-channel-p1 channel :character state))
                (state-p1 state))
           (state-p1 (close-output-channel channel state)))
  :hints(("Goal" :in-theory (disable close-output-channel
                                     open-output-channel-p1))))

(defthm state-p1-of-close-output-channel-of-open
  (implies (and (open-output-channel-p1
                 (mv-nth 0 (open-output-channel fname type state1))
                 type state)
                (state-p1 state))
           (state-p1 (close-output-channel
                      (mv-nth 0 (open-output-channel fname type state1))
                      state)))
  :hints(("Goal" :in-theory (disable close-output-channel
                                     open-output-channel-p1
                                     open-output-channel))))






(defthm open-channel1-of-cons-byte
  (implies (and (open-channel1 x)
                (equal (cadar x) :byte)
                (natp y)
                (< y 256))
           (open-channel1 (list* (car x) y (cdr x)))))

(defthm open-channel1-of-cons-object
  (implies (and (open-channel1 x)
                (equal (cadar x) :object))
           (open-channel1 (list* (car x) y (cdr x)))))

(defthm open-channel1-of-revappend-charlist
  (implies (and (open-channel1 x)
                (equal (cadar x) :character)
                (character-listp y))
           (open-channel1 (cons (car x) (revappend y (cdr x)))))
  :otf-flg t)
           
;; matches unicode/explode-nonnegative-integer.lisp
(defthm character-listp-of-explode-nonnegative-integer
  (equal (character-listp (explode-nonnegative-integer n base acc))
         (character-listp acc))
  :hints(("Goal" :in-theory (disable floor mod digit-to-char))))

;; does NOT match unicode/explode-atom.lisp (so we renamed this theorem).
;; unicode version includes print-base-p hyp.
(defthm character-listp-explode-atom
  (character-listp (explode-atom x base)))


;; Princ$
(defthm state-p1-of-princ$
  (implies (and (state-p1 state)
                (symbolp channel)
                (open-output-channel-p1 channel :character state))
           (state-p1 (princ$ x channel state)))
  :hints(("Goal" :in-theory (e/d (state-p1) (open-channel1 explode-atom)))))

(defthm open-output-channel-p1-of-princ$
  (implies (and (state-p1 state)
                (open-output-channel-p1 channel :character state))
           (open-output-channel-p1 channel :character (princ$ x channel state))))


;; Write-byte$
(defthm state-p1-of-write-byte$
  (implies (and (state-p1 state)
                (symbolp channel)
                (natp byte)
                (< byte 256)
                (open-output-channel-p1 channel :byte state))
           (state-p1 (write-byte$ byte channel state)))
  :hints(("Goal" :in-theory (e/d (state-p1) (open-channel1)))))

(defthm open-output-channel-p1-of-write-byte$
  (implies (and (state-p1 state)
                (open-output-channel-p1 channel :byte state))
           (open-output-channel-p1 channel :byte (write-byte$ byte channel state))))

;; print-object$
(defthm state-p1-of-print-object$
  (implies (and (state-p1 state)
                (symbolp channel)
                (open-output-channel-p1 channel :object state))
           (state-p1 (print-object$ x channel state)))
  :hints(("Goal" :in-theory (e/d (state-p1) (open-channel1)))))

(defthm open-output-channel-p1-of-print-object$
  (implies (and (state-p1 state)
                (open-output-channel-p1 channel :object state))
           (open-output-channel-p1 channel :object (print-object$ x channel state))))


;; Close-output-channel's guard requires that the channel is not the symbol:
;; ACL2-OUTPUT-CHANNEL::STANDARD-CHARACTER-OUTPUT-0.
;; So we need to prove that this symbol is never returned from
;; open-output-channel.  This is true because symbol created ends in "-" and
;; then the new file clock, which is at least 1.  Blech!
(encapsulate nil
  (local (in-theory (disable floor mod print-base-p)))
  (local (include-book "ihs/quotient-remainder-lemmas" :dir :System))

  (defthm print-base-p-implies-posp
    (implies (print-base-p x)
             (posp x))
    :hints(("Goal" :in-theory (enable print-base-p)))
    :rule-classes :forward-chaining)

  (defthm print-base-p-bound
    (implies (print-base-p x)
             (<= x 16))
    :hints(("Goal" :in-theory (enable print-base-p)))
    :rule-classes :forward-chaining)

  (local (defthm explode-nonnegative-integer-length-incr
           (<= (len ans) (len (explode-nonnegative-integer n base ans)))
           :rule-classes :linear))

  (local (defthm explode-nonnegative-integer-length-incr-strict
           (implies (and (posp n) (print-base-p base))
                    (< (len ans) (len (explode-nonnegative-integer n base ans))))
           :hints(("Goal" :in-theory (enable mod)
                   :induct (explode-nonnegative-integer n base ans)
                   :expand ((:free (base) (explode-nonnegative-integer n base ans)))))
           :rule-classes nil))

  (local (defthm ans-not-zero-when-member-nonzero
           (implies (and (bind-free `((c . (car ,ans))))
                         (member (double-rewrite c) ans)
                         (not (equal (double-rewrite c) #\0)))
                    (not (equal (explode-nonnegative-integer x base ans)
                                '(#\0))))))

  (local (defthm posp-x/base
           (implies (and (integerp x)
                         (< 0 x)
                         (print-base-p base))
                    (or (not (integerp (* (/ base) x)))
                        (< 0 (* (/ base) x))))
           :rule-classes :type-prescription))

  (local (defthm explode-nonnegative-integer-of-positive-is-not-zero-list
           (implies (and (posp x)
                         (print-base-p base))
                    (not (equal (explode-nonnegative-integer x base ans)
                                '(#\0))))
           :hints(("Goal" ; :in-theory (enable mod)
                   :expand ((:free (base) (explode-nonnegative-integer x base ans)))
                   :use ((:instance explode-nonnegative-integer-length-incr-strict
                          (n (* (/ base) x)) (ans (cons #\0 ans))))
                   :do-not-induct t))
           :otf-flg t))

  (local (defun charlist-suffixp (x suff)
           (or (equal x suff)
               (and (consp x)
                    (charlist-suffixp (cdr x) suff)))))

  (local (defun symb-ends-in-dash-zero (x)
           (charlist-suffixp (coerce (symbol-name x) 'list)
                             '(#\- #\0))))

  (local (defthm suffixp-dash-zero-implies-member-dash
           (implies (not (member #\- x))
                    (not (charlist-suffixp x '(#\- #\0))))))

  (local (defthm explode-nonneg-no-dash
           (implies (not (member #\- ans))
                    (not (member #\- (explode-nonnegative-integer x base
                                                                  ans))))))

  (local (defthm character-listp-explode-nonneg
           (equal
            (character-listp (explode-nonnegative-integer n base ans))
            (character-listp ans))))

  (local (defthm charlist-suffixp-append-dash-x
           (equal (charlist-suffixp (append x (cons #\- y)) '(#\- #\0))
                  (charlist-suffixp (cons #\- y) '(#\- #\0)))
           :hints (("goal" :induct (append x (cons #\- y))
                    :in-theory (enable append)))))

  (local (defthm symb-ends-in-dash-zero-of-make-output-channel
           (implies (posp clock)
                    (not (symb-ends-in-dash-zero (make-output-channel str clock))))))

  (local (defthm symb-ends-in-dash-zero-of-make-input-channel
           (implies (posp clock)
                    (not (symb-ends-in-dash-zero (make-input-channel str clock))))))

  (defthm make-output-channel-not-standard-co
    (implies (posp clock)
             (not (equal (make-output-channel str clock)
                         *standard-co*)))
    :hints (("goal" :in-theory (disable
                                symb-ends-in-dash-zero-of-make-output-channel
                                make-output-channel)
             :use symb-ends-in-dash-zero-of-make-output-channel)))

  (defthm make-input-channel-not-standard-ci
    (implies (posp clock)
             (not (equal (make-input-channel str clock)
                         *standard-ci*)))
    :hints (("goal" :in-theory (disable
                                symb-ends-in-dash-zero-of-make-input-channel
                                make-input-channel)
             :use symb-ends-in-dash-zero-of-make-input-channel)))

  (defthm make-input-channel-not-standard-oi
    (implies (posp clock)
             (not (equal (make-input-channel str clock)
                         *standard-oi*)))
    :hints (("goal" :in-theory (disable
                                symb-ends-in-dash-zero-of-make-input-channel
                                make-input-channel)
             :use symb-ends-in-dash-zero-of-make-input-channel)))

  (defthm open-output-channel-is-not-standard-co
    (implies (state-p1 state)
             (not (equal (mv-nth 0 (open-output-channel fname type state))
                         *standard-co*)))
    :hints(("Goal" :in-theory (disable make-output-channel))))

  (defthm open-input-channel-is-not-standard-ci
    (implies (state-p1 state)
             (not (equal (mv-nth 0 (open-input-channel fname type state))
                         *standard-ci*)))
    :hints(("Goal" :in-theory (disable make-input-channel))))

  (defthm open-input-channel-is-not-standard-oi
    (implies (state-p1 state)
             (not (equal (mv-nth 0 (open-input-channel fname type state))
                         *standard-oi*)))
    :hints(("Goal" :in-theory (disable make-input-channel)))))


;; This is slightly different than unicode's file-measure, which allows us to
;; prove it decreasing without assuming state-p1 in the object case.  Really
;; it's just a workaround for the fact that read-object checks
;; (cdr entry) as a substitute for (consp (cdr entry)) to find whether there
;; are objects remaining.
(defun file-measure (channel state-state)
  (declare (xargs :guard (and (symbolp channel)
                              (state-p1 state-state))))
  (+ (len (cddr (assoc-equal channel (open-input-channels state-state))))
     (if (consp (cddr (assoc-equal channel (open-input-channels state-state))))
         (if (cdr (last (cddr (assoc-equal channel (open-input-channels
                                                    state-state))))) 1 0)
       (if (cddr (assoc-equal channel (open-input-channels state-state))) 1 0))))

(defthm file-measure-of-read-byte$-weak
  (<= (file-measure channel (mv-nth 1 (read-byte$ channel state)))
      (file-measure channel state))
  :rule-classes (:rewrite :linear))

(defthm file-measure-of-read-byte$-strong
  (implies (mv-nth 0 (read-byte$ channel state))
           (< (file-measure channel (mv-nth 1 (read-byte$ channel state)))
              (file-measure channel state)))
  :rule-classes (:rewrite :linear))

(defthm file-measure-of-read-byte$-rw
  (implies (mv-nth 0 (read-byte$ channel state))
           (equal (file-measure channel (mv-nth 1 (read-byte$ channel state)))
                  (+ -1 (file-measure channel state)))))

(defthm file-measure-of-read-char$-weak
  (<= (file-measure channel (mv-nth 1 (read-char$ channel state)))
      (file-measure channel state))
  :rule-classes (:rewrite :linear))

(defthm file-measure-of-read-char$-strong
  (implies (mv-nth 0 (read-char$ channel state))
           (< (file-measure channel (mv-nth 1 (read-char$ channel state)))
              (file-measure channel state)))
  :rule-classes (:rewrite :linear))

(defthm file-measure-of-read-char$-rw
  (implies (mv-nth 0 (read-char$ channel state))
           (equal (file-measure channel (mv-nth 1 (read-char$ channel state)))
                  (1- (file-measure channel state)))))

(defthm file-measure-of-read-object-weak
  (<= (file-measure channel (mv-nth 2 (read-object channel state)))
      (file-measure channel state))
  :rule-classes (:rewrite :linear))

(defthm file-measure-of-read-object-strong
  (implies (not (mv-nth 0 (read-object channel state)))
           (< (file-measure channel (mv-nth 2 (read-object channel state)))
              (file-measure channel state)))
  :rule-classes (:rewrite :linear))

(defthm file-measure-of-read-object-rw
  (implies (not (mv-nth 0 (read-object channel state)))
           (equal (file-measure channel (mv-nth 2 (read-object channel state)))
                  (1- (file-measure channel state)))))


(in-theory (disable state-p1
                    open-input-channel-p1
                    open-input-channel
                    close-input-channel
                    read-char$
                    read-byte$
                    read-object
                    open-output-channel-p1
                    open-output-channel
                    close-output-channel
                    princ$
                    write-byte$
                    print-object$
                    file-measure))
