; Copyright (C) 2013 Centaur Technology
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

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)


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
       ;; (- (cw "event: ~x0~%prev enabled: ~x1~%"
       ;;        (access-event-tuple-form (cddar w))
       ;;        prev-enabled))
       ((when (xor en/dis prev-enabled))
        w))
    (scan-for-last-en/disabling rune en/dis tail)))

(defun find-last-en/disabling (rune state)
  ;; find the last time a rune was enabled/disabled and print it like with :pe
  (declare (xargs :mode :program :stobjs state))
  (b* ((w (w state))
       (en/dis (consp (member-equal rune (current-theory1 w nil nil))))
       ;; (- (cw "enabled: ~x0~%" en/dis))
       (ev-wrld (scan-for-last-en/disabling rune en/dis w))
       ((unless ev-wrld)
        (cw "Never enabled/disabled~%")
        (value :invisible))
       ((er cmd-wrld) (superior-command-world
                       ev-wrld w 'find-last-en/disabling state))
       (state (pe-fn1 w (standard-co state) ev-wrld cmd-wrld state)))
    (value :invisible)))
