; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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


; solutions.lisp - Solutions to the tutorial exercises
;
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "gl")
; cert_param: (hons-only)


;; Solutions to exercises in the GL Basic Tutorial
;;
;; We space these out excessively, so you can avoid looking at answers you
;; haven't gotten to yet.













(def-gl-thm 1a
  :hyp (and (unsigned-byte-p 4 x)
            (unsigned-byte-p 4 y))
  :concl (equal (+ x y) (+ y x))
  :g-bindings '((x (:g-number (1 2 3 4 5)))
                (y (:g-number (6 7 8 9 10)))))

















(def-gl-thm 1b-using-auto-bindings
  :hyp (and (unsigned-byte-p 4 x)
            (unsigned-byte-p 4 y))
  :concl (equal (+ x y) (+ y x))
  :g-bindings (gl::auto-bindings (:nat x 4)
                                 (:nat y 4)))


















(def-gl-thm 1b-using-g-int
  :hyp (and (unsigned-byte-p 4 x)
            (unsigned-byte-p 4 y))
  :concl (equal (+ x y) (+ y x))
  :g-bindings `((x ,(gl::g-int 0 1 5))
                (y ,(gl::g-int 6 1 5))))















;; We already did 1b manually (see 1a).


















(def-gl-thm 1c
  :hyp (and (unsigned-byte-p 20 x)
            (unsigned-byte-p 20 y))
  :concl (equal (+ x y) (+ y x))
  :g-bindings (gl::auto-bindings (:nat x 20)
                                 (:nat y 20)))

;; The above took 24 seconds.


(value-triple (hons-summary))  ;; It allocated 8 million honses.


















; 1d doesn't require a new proof.

#||

:u
(def-gl-thm 1c
  :hyp (and (unsigned-byte-p 20 x)
            (unsigned-byte-p 20 y))
  :concl (equal (+ x y) (+ y x))
  :g-bindings (gl::auto-bindings (:nat x 20)
                                 (:nat y 20)))

||#

















(value-triple (clear-memoize-tables))
(value-triple (hons-clear nil))

(def-gl-thm 1e
  :hyp (and (unsigned-byte-p 20 x)
            (unsigned-byte-p 20 y))
  :concl (equal (+ x y) (+ y x))
  :g-bindings (gl::auto-bindings (:mix (:nat x 20)
                                       (:nat y 20))))

(value-triple (clear-memoize-tables))
(value-triple (hons-clear nil))

(def-gl-thm 1e-alt
  :hyp (and (unsigned-byte-p 20 x)
            (unsigned-byte-p 20 y))
  :concl (equal (+ x y) (+ y x))
  :g-bindings `((x ,(gl::g-int 0 2 21))
                (y ,(gl::g-int 1 2 21))))











; To make this execute much faster, we'll want a higher memory ceiling.

; Added 8/24/13 by Matt K.: This book failed to certify because of a missing
; :ttags for the include-book form below..  However, the difference between
; using the two forms below, and not, was trivial when I used time$ to time the
; proof of 1f below:
;
;   ; including memory-mgmt:
;   36.39 seconds realtime, 36.29 seconds runtime
;   (3,472,888,144 bytes allocated).
;
;   ; NOT including memory-mgmt:
;   36.46 seconds realtime, 36.37 seconds runtime
;   (3,472,888,240 bytes allocated).
;
; (include-book "centaur/misc/memory-mgmt" :dir :system)
; (value-triple (set-max-mem (* 8 (expt 2 30))))

(def-gl-thm 1f
  :hyp (and (unsigned-byte-p 3000 x)
            (unsigned-byte-p 3000 y))
  :concl (equal (+ x y) (+ y x))
  :g-bindings (gl::auto-bindings (:mix (:nat x 3000)
                                       (:nat y 3000))))






