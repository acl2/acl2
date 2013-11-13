; Copyright (C) 2013 Centaur Technology
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

(include-book "tools/bstar" :dir :system)


(defun scan-for-current-theory (w)
  (if (atom w)
      nil
    (if (and (eq (caar w) 'current-theory)
             (eq (cadar w) 'global-value))
        (cddar w)
      (scan-for-current-theory (cdr w)))))

(defun scan-for-last-en/disabling (rune en/dis w)
  (declare (xargs :mode :program))
  (b* (((when (atom w)) nil)
       ((unless (and (eq (caar w) 'event-landmark)
                     (eq (access-event-tuple-type (cddar w))
                         'in-theory)))
        (scan-for-last-en/disabling rune en/dis (cdr w)))
       (tail (scan-to-event (cdr w)))
       (prev-theory (current-theory1 tail nil nil))
       (prev-enabled (consp (member-equal rune prev-theory)))
       (- (cw "event: ~x0~%prev enabled: ~x1~%"
              (access-event-tuple-form (cddar w))
              prev-enabled))
       ((when (xor en/dis prev-enabled))
        w))
    (scan-for-last-en/disabling rune en/dis tail)))

(defun find-last-en/disabling (rune state)
  ;; find the last time a rune was enabled/disabled and print it like with :pe
  (declare (xargs :mode :program :stobjs state))
  (b* ((w (w state))
       (en/dis (consp (member-equal rune (current-theory1 w nil nil))))
       (- (cw "enabled: ~x0~%" en/dis))
       (ev-wrld (scan-for-last-en/disabling rune en/dis w))
       ((er cmd-wrld) (superior-command-world
                       ev-wrld w 'find-last-en/disabling state))
       (state (pe-fn1 w (standard-co state) ev-wrld cmd-wrld state)))
    (value :invisible)))
