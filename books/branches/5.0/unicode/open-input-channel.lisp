;; Processing Unicode Files with ACL2
;; Copyright (C) 2005-2006 by Jared Davis <jared@cs.utexas.edu>
;;
;; This program is free software; you can redistribute it and/or modify it
;; under the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 2 of the License, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
;; more details.
;;
;; You should have received a copy of the GNU General Public License along with
;; this program; if not, write to the Free Software Foundation, Inc., 59 Temple
;; Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "ACL2")
(local (include-book "tools/mv-nth" :dir :system))
(local (include-book "update-state"))
(local (include-book "open-input-channels"))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (local (defthm assoc-eq-is-assoc-equal
;          (equal (assoc-eq a x)
;                 (assoc-equal a x))))

(local (defthm readable-files-ok
  (implies (state-p1 state)
           (readable-files-listp (readable-files state)))))

(local (defthm readable-files-list-contents-have-correct-type
  (implies (readable-files-listp table)
           (typed-io-listp (cdr (assoc-equal entry table))
                           (cadr entry)))))

(local (defthm open-input-channel-lemma
  (implies (and (symbolp channel)
                (stringp file-name)
                (member-eq type *file-types*)
                (integerp clock)
                (state-p1 state)
                (readable-files-listp table)
                (assoc-equal (list file-name type clock) table)
                (open-channels-p channels))
           (open-channels-p
            (add-pair channel
                      (cons (list :header type file-name clock)
                            (cdr (assoc-equal (list file-name type clock)
                                              table)))
                      channels)))))

(encapsulate
 nil

 ;; We show that the channel returned by open-input-channel is a symbol and
 ;; that it is not either of ACL2-INPUT-CHANNEL::standard-character-input-0
 ;; or ACL2-INPUT-CHANNEL::standard-object-input-0.  These facts are needed
 ;; to verify the guards on close-input-channel after opening a channel.

 (local (include-book "arithmetic/top" :dir :system))
 (local (include-book "explode-nonnegative-integer"))
 (local (include-book "intern-in-package-of-symbol"))
 (local (include-book "coerce"))

 (local (defthm lemma-0
          (implies (and (base10-digit-char-listp y1)
                        (base10-digit-char-listp y2)
                        (not (base10-digit-charp x)))
                   (equal (equal (cons x y1)
                                 (cons x y2))
                          (equal y1 y2)))))

 (local (defthm lemma-1
          (implies (and (base10-digit-char-listp y1)
                        (base10-digit-char-listp y2)
                        (not (base10-digit-charp x)))
                   (not (equal (cons a (cons x y1))
                               (cons x y2))))))

 (local (defthm lemma-2
          (implies (and (base10-digit-char-listp y1)
                        (base10-digit-char-listp y2)
                        (not (base10-digit-charp x))
                        (equal (append a (cons x y1))
                               (cons x y2)))
                   (not (consp a)))
          :hints(("Goal" :induct (append a (cons x y1))
                  :do-not '(generalize)))))

 (local (defthm lemma-3
          (implies (and (base10-digit-char-listp y1)
                        (base10-digit-char-listp y2)
                        (not (base10-digit-charp x)))
                   (equal (equal (append a (cons x y1))
                                 (cons x y2))
                          (and (not (consp a))
                               (equal y1 y2))))
          :hints(("Goal"
                  :in-theory (disable lemma-2)
                  :use (:instance lemma-2 (a a) (x x) (y1 y1) (y2 y2))))))

 (local (defun cdr-cdr-induction (a1 a2)
          (if (and (consp a1)
                   (consp a2))
              (cdr-cdr-induction (cdr a1) (cdr a2))
            (list a1 a2))))

 (local (defthm lemma-4
          (implies (and (base10-digit-char-listp y1)
                        (base10-digit-char-listp y2)
                        (not (base10-digit-charp x))
                        (true-listp a1)
                        (true-listp a2))
                   (equal (equal (append a1 (cons x y1))
                                 (append a2 (cons x y2)))
                          (and (equal y1 y2)
                               (equal a1 a2))))
          :hints(("Goal" :induct (cdr-cdr-induction a1 a2)))))

 (local (defthm lemma-5
          (implies (and (base10-digit-char-listp y1)
                        (base10-digit-char-listp y2)
                        (true-listp x1)
                        (true-listp x2))
                   (equal (equal (append x1 (cons #\- y1))
                                 (append x2 (cons #\- y2)))
                          (and (equal x1 x2)
                               (equal y1 y2))))))

 (local (defthm lemma-6
          (implies (and (true-listp x)
                        (natp clock))
                   (equal (equal (append x (cons #\- (explode-atom clock 10)))
                                 (append x (cons #\- (explode-atom 0 10))))
                          (equal clock 0)))))

 (local (defthm main-lemma
          (implies (and (natp clock)
                        (character-listp x))
                   (equal (equal (make-input-channel filename clock)
                                 (intern-in-package-of-symbol
                                  (coerce (append x (cons #\- (explode-atom 0 10)))
                                          'string)
                                  'ACL2-INPUT-CHANNEL::A-RANDOM-SYMBOL-FOR-INTERN))
                          (and (equal (coerce filename 'list) x)
                               (equal clock 0))))
          :hints(("Goal" :in-theory (disable (explode-atom))))))

 (local (defthm coerce-reduction
          (implies (and (syntaxp (quotep list))
                        (character-listp list)
                        (stringp x))
                   (equal (equal (coerce x 'list) list)
                          (equal x (coerce list 'string))))))

 (local (defthm make-input-channel-standard-character-input-0
          (implies (and (stringp filename)
                        (natp clock))
                   (equal (equal (make-input-channel filename clock)
                                 'ACL2-INPUT-CHANNEL::STANDARD-CHARACTER-INPUT-0)
                          (and (equal filename "STANDARD-CHARACTER-INPUT")
                               (equal clock 0))))
          :hints(("Goal"
                  :in-theory (disable main-lemma)
                  :use ((:instance main-lemma
                                   (clock clock)
                                   (filename filename)
                                   (x (coerce "STANDARD-CHARACTER-INPUT" 'list))))))))

 (local (defthm make-input-channel-standard-object-input-0
          (implies (and (stringp filename)
                        (natp clock))
                   (equal (equal (make-input-channel filename clock)
                                 'ACL2-INPUT-CHANNEL::STANDARD-OBJECT-INPUT-0)
                          (and (equal filename "STANDARD-OBJECT-INPUT")
                               (equal clock 0))))
          :hints(("Goal"
                  :in-theory (disable main-lemma)
                  :use ((:instance main-lemma
                                   (clock clock)
                                   (filename filename)
                                   (x (coerce "STANDARD-OBJECT-INPUT" 'list))))))))


 (local (defthm open-input-channel-channel-elim
          (implies (and (mv-nth 0 (open-input-channel filename type state))
                        (state-p1 state))
                   (equal (mv-nth 0 (open-input-channel filename type state))
                          (make-input-channel filename (1+ (file-clock state)))))
          :hints(("Goal" :in-theory (disable statep-functions
                                             make-input-channel)))))

 (defthm open-input-channel-symbol
   (symbolp (mv-nth 0 (open-input-channel filename type state)))
   :rule-classes ((:rewrite) (:type-prescription)))

 (defthm open-input-channel-not-standard-object-input
   (implies (and (stringp filename)
                 (state-p1 state))
            (not (equal (mv-nth 0 (open-input-channel filename type state))
                        'ACL2-INPUT-CHANNEL::STANDARD-OBJECT-INPUT-0)))
   :hints(("Goal" :in-theory (disable make-input-channel))))

 (defthm open-input-channel-not-standard-character-input
   (implies (and (stringp filename)
                 (state-p1 state))
            (not (equal (mv-nth 0 (open-input-channel filename type state))
                        'ACL2-INPUT-CHANNEL::STANDARD-CHARACTER-INPUT-0)))
   :hints(("Goal" :in-theory (disable make-input-channel))))
 )

(local (defthm expand-file-clock-p
         (equal (file-clock-p x)
                (natp x))))

(local (defthm file-clock-natural
         (implies (state-p1 state)
                  (and (integerp (file-clock state))
                       (<= 0 (file-clock state))))
         :rule-classes :type-prescription
         :hints(("Goal" :expand (state-p1 state)))))

(defthm open-input-channel-state
  (implies (and (force (state-p1 state))
                (force (stringp filename))
                (force (member-equal type *file-types*)))
           (state-p1 (mv-nth 1 (open-input-channel filename type state))))
  :hints(("Goal" :in-theory (disable statep-functions
                                     make-input-channel))))

(defthm open-input-channel-creates-open-channel
  (implies (and (mv-nth 0 (open-input-channel filename type state))
                (force (state-p1 state))
                (force (stringp filename))
                (force (member-equal type *file-types*)))
           (open-input-channel-p1
            (mv-nth 0 (open-input-channel filename type state))
            type
            (mv-nth 1 (open-input-channel filename type state))))
  :hints(("Goal" :in-theory (disable statep-functions
                                     make-input-channel))))

(in-theory (disable state-p1 open-input-channel-p1 open-input-channel))
