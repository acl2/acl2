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
(local (include-book "update-state"))
(local (include-book "open-input-channels"))

(local (defthm assoc-eq-is-assoc-equal
         (equal (assoc-eq a x)
                (assoc-equal a x))))

(local (defthm update-read-files-state
  (implies (state-p1 state)
           (equal (state-p1 (update-read-files updates state))
                  (read-file-listp updates)))))

(local (defthm update-read-files-lemma
  (implies (read-files-p read-files)
           (equal (read-file-listp (cons entry read-files))
                  (read-file-listp1 entry)))))

(local (defthm some-header-part-is-string
  (implies (open-channel1 channel)
           (stringp (caddar channel)))))

(local (defthm some-header-part-is-integer
  (implies (open-channel1 channel)
           (integerp (cadddr (car channel))))))

(local (defthm really-ugly-lemma
  (implies (and (open-channel1 channel)
                (integerp clock)
                (member-equal type *file-types*))
           (read-file-listp1
            (list (caddar channel) type (cadddr (car channel)) clock)))))

(local (defthm expand-file-clock-p
         (equal (file-clock-p x)
                (natp x))))

(local (defthm file-clock-natural
         (implies (state-p1 state)
                  (and (integerp (file-clock state))
                       (<= 0 (file-clock state))))
         :rule-classes :type-prescription
         :hints(("Goal" :expand (state-p1 state)))))


; I would just use the following lemma as the main theorem, instead of
; replacing it with close-input-channel-state below, but it does not seem to
; work to force the member-equal and open-input-channel-p1 hypotheses when the
; type is a free variable.  So, instead I prove the weirder-looking theorem
; that lets me force without free variables.

(local (defthm close-input-channel-state-lemma
         (implies (and (state-p1 state)
                       (member-equal type *file-types*)
                       (open-input-channel-p1 channel type state))
                  (state-p1 (close-input-channel channel state)))
         :hints(("Goal" :in-theory (disable statep-functions)
                 :use ((:instance state-p1
                                  (x state))
                       (:instance state-p1
                                  (x (close-input-channel channel state))))))))

(defthm close-input-channel-state
  (implies (and (force (state-p1 state))
                (force (or (open-input-channel-p1 channel :byte state)
                           (open-input-channel-p1 channel :character state)
                           (open-input-channel-p1 channel :object state))))
           (state-p1 (close-input-channel channel state)))
  :hints(("Goal" :in-theory (disable close-input-channel open-input-channel-p1
                                     state-p1)
          :use ((:instance close-input-channel-state-lemma (type :byte))
                (:instance close-input-channel-state-lemma (type :character))
                (:instance close-input-channel-state-lemma (type :object))))))

(in-theory (disable state-p1 open-input-channel-p1 close-input-channel))