; Memoize Library
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
; Original author: Jared Davis <jared@centtech.com>
;
; This library is a descendant of the memoization scheme developed by Bob Boyer
; and Warren A. Hunt, Jr. which was incorporated into the HONS version of ACL2,
; sometimes called ACL2(h).

(in-package "MEMOIZE")

;; basic tests of return-value/argument stuff

(assert (equal (numargs 'length) 1))
(assert (equal (numargs 'binary-append) 2))
(assert (equal (numvals 'length) 1))
(assert (equal (numargs 'open-input-channel) 3))
(assert (equal (numvals 'open-input-channel) 2))

#+Clozure
(assert (equal (numargs 'numargs) 1))
#+Clozure
(assert (equal (numargs 'numvals) 1))

(assert (not (numargs 'frob)))
(assert (not (numvals 'frob)))
(declare-numargs 'frob 3 7)
(assert (equal (numargs 'frob) 3))
(assert (equal (numvals 'frob) 7))

;; some special forms that should not have fixed arities
(assert (not (numargs 'let)))
(assert (not (numargs 'let*)))
(assert (not (numargs 'append)))
(assert (not (numargs 'if)))
(assert (not (numargs 'return-last)))
(assert (not (numargs 'mv)))
(assert (not (numargs 'mv-let)))
(assert (not (numargs 'lambda)))

(assert (not (numvals 'let)))
(assert (not (numvals 'let*)))
(assert (not (numvals 'append)))
(assert (not (numvals 'if)))
(assert (not (numvals 'return-last)))
(assert (not (numvals 'mv)))
(assert (not (numvals 'mv-let)))
(assert (not (numargs 'lambda)))

;; basic time measurement accuracy

#||

commenting out this check for now, since it sometimes fails on certain machines.

(assert
 (let* ((start (ticks))
        (wait  (sleep 3))
        (end   (ticks))
        (secs  (/ (- end start) (ticks-per-second))))
   (format t "Measured time for sleeping 3 seconds: ~a~%" secs)
   (and (<= 2.8 secs)
        (<= secs 3.2))))

(assert
 (let* ((start (ticks))
        (wait  (sleep 2))
        (end   (ticks))
        (secs  (/ (- end start) (ticks-per-second))))
   (format t "Measured time for sleeping 2 seconds: ~a~%" secs)
   (and (<= 1.85 secs)
        (<= secs 2.15))))

(assert
 (let* ((start (ticks))
        (wait  (sleep 1))
        (end   (ticks))
        (secs  (/ (- end start) (ticks-per-second))))
   (format t "Measured time for sleeping 1 seconds: ~a~%" secs)
   (and (<= 0.9 secs)
        (<= secs 1.1))))

||#
