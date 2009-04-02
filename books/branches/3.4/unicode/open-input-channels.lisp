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

; The open input channels table is the logical fiction that supports our
; ability to read from files.  When a file is opened, it is added to this
; table.  When it is read from, we consult this table to find its contents and
; update the table to consume one object of input.  When it is closed, this
; table must be updated to handle the closure.  The table itself is just an
; object that satisfies open-channels-p, and it is easy to show that calling
; open-input-channels on a state returns an object of this form.

(defthm open-input-channels-ok
  (implies (state-p1 state)
           (open-channels-p (open-input-channels state))))

(defthm ordered-symbol-alistp-of-open-input-channels
  (implies (state-p1 state)
           (ordered-symbol-alistp (open-input-channels state))))



; We typically update this table by using the function add-pair.  We will find
; several lemmas about this function to be useful.  First, we give a very nice
; little rewrite rule that shows that add-pair does indeed act as we would
; expect with respect to assoc-equal.  (Note that we canonicalize all uses of
; assoc-eq and assoc to their assoc-equal form, so this will cover those cases
; as well after rewriting.)

(defthm add-pair-assoc-equal
  (equal (assoc-equal key1 (add-pair key2 val alist))
         (if (equal key1 key2)
             (cons key2 val)
           (assoc-equal key1 alist))))



; In order to prove that an update to our open channels list preserves the
; basic open-channels-p property, we will need to show that such updates
; satisfy both ordered-symbol-alistp and open-channel-listp.  We introduce the
; lemmas below towards this purpose.

(defthm add-pair-ordered-symbol-alistp
  (implies (ordered-symbol-alistp list)
           (equal (ordered-symbol-alistp (add-pair key val list))
                  (symbolp key))))

(defthm delete-pair-ordered-symbol-alistp
  (implies (ordered-symbol-alistp list)
           (ordered-symbol-alistp (delete-pair key list))))

(defthm add-pair-open-channel-listp
  (implies (open-channel-listp list)
           (equal (open-channel-listp (add-pair key val list))
                  (open-channel1 val))))

(defthm delete-pair-open-channel-listp
  (implies (open-channel-listp list)
           (open-channel-listp (delete-pair key list))))

(defthm add-pair-open-channels-p
  (implies (open-channels-p list)
           (equal (open-channels-p (add-pair key val list))
                  (and (symbolp key)
                       (open-channel1 val)))))

(defthm delete-pair-open-channels-p
  (implies (open-channels-p list)
           (open-channels-p (delete-pair key list))))



; If we grab something out of the open channels list, what can we say about it?
; Well, by looking at the definition of open-channel-listp, the most obvious
; thing to do is to prove that it is an open-channel1, and then to prove
; properties about such objects instead of having to reason about assoc'ing
; into an open channel list all the time.  Towards this end, we will show that
; if we find a channel in an open-channels-p list, it is an open-channel1, and
; if we have an open-channel1, we know that its contents are a typed list of
; the correct type.

(defthm open-channels-assoc
  (implies (and (open-channels-p x)
                (assoc-equal channel x))
           (open-channel1 (cdr (assoc-equal channel x)))))

(defthm open-channel1-contents-type
  (implies (open-channel1 x)
           (typed-io-listp (cdr x) (cadar x))))



; Now, here is a lemma that we'll use to show that our reading operations
; preserve open-channel1.  The form (cons (car x) (cddr x)) below is a basic
; operation which preserves the header of an open channel's contents, while
; eliminating the first element of its contents.  Here we show that this usage
; preserves open-channel1.

(defthm open-channel1-advance
  (implies (open-channel1 x)
           (open-channel1 (cons (car x) (cddr x)))))



; All of our reading operations require that we have an open input channel of
; the right type, i.e., that (open-input-channel-p1 channel type state) is true
; of our state.  What can we conclude given that this holds for some state?
; First off, we know that looking up the channel in the open-input-channels
; list will be successful.  Secondly, we know that the type of the channel
; returned will be the same as type in our call to open-input-channel-p1.

(local (defthm assoc-eq-is-assoc-equal
         (equal (assoc-eq a x) 
                (assoc-equal a x))))

(defthm assoc-open-input-channels-exists
  (implies (open-input-channel-p1 channel type state)
           (assoc-equal channel (open-input-channels state))))

(defthm assoc-open-input-channels-type
  (implies (open-input-channel-p1 channel type state)
           (equal (cadadr (assoc-equal channel (open-input-channels state)))
                  type)))



; We can go further and say that given an open input channel and a state,
; the contents of the channel are a typed io list of the correct type.

(defthm assoc-open-input-channels-contents
  (implies (and (state-p1 state)
                (open-input-channel-p1 channel type state))
           (typed-io-listp (cddr (assoc-equal channel (open-input-channels state)))
                           type))
  :hints(("Goal" :use (:instance open-input-channels-ok))))



; We're now ready for a really ugly but important lemma.  This is the core
; operation that read-byte$, read-char$, and read-object use in order to
; "consume" an object from their input streams.  We show that when they do
; this, they still have an open-channels-p.

(defthm add-pair-open-channels
  (implies (and (state-p1 state)
                (open-input-channel-p1 channel type state)
                (symbolp channel))
           (open-channels-p
            (add-pair channel
                      (cons (cadr (assoc-equal channel 
                                               (open-input-channels state)))
                            (cdddr (assoc-equal channel 
                                                (open-input-channels state))))
                      (open-input-channels state))))
  :hints(("Goal" :in-theory (disable open-input-channels
                                     open-channels-p))))





(defthm equal-of-update-open-input-channels-with-state
  (implies (state-p1 state)
           (equal (equal (update-open-input-channels x state) state)
                  (equal x (open-input-channels state))))
  :hints(("Goal" :in-theory (enable update-open-input-channels
                                    open-input-channels
                                    state-p1))))
        
(defthm equal-of-add-pair-with-channels
  (implies (ordered-symbol-alistp channels)
           (equal (equal (add-pair channel x channels) channels)
                  (equal (assoc-equal channel channels)
                         (cons channel x))))
  :hints(("Goal" 
          :in-theory (enable ordered-symbol-alistp add-pair)
          :induct (add-pair channel x channels))))
