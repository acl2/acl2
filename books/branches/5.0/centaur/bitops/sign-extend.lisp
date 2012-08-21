; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "misc/definline" :dir :system)
(include-book "tools/bstar" :dir :system)
(include-book "ihs/logops-definitions" :dir :system)
(local (include-book "ihs-extensions"))

; BOZO we also have stupid stuff like signed-val-of-nat in extra-defs, need to
; standardize this stuff.


;; X is typically a natural; this function interprets it as a signed number of
;; the given width b, i.e. the sign bit is at b-1.  
;; This is from bit-twiddling hacks: 

;; unsigned b; // number of bits representing the number in x
;; int x;      // sign extend this b-bit number to r
;; int r;      // resulting sign-extended number
;; int const m = 1U << (b - 1); // mask can be pre-computed if b is fixed
;; x = x & ((1U << b) - 1);  // (Skip this if bits in x above position b are already zero.)
;; r = (x ^ m) - m;

(definlined sign-extend-exec (b x)
  (declare (xargs :guard (and (posp b)
                              (integerp x))))
  (b* ((x1 (logand (1- (ash 1 b)) x)) ;; x = x & ((1U << b) - 1)
       (m  (ash 1 (- b 1))))          ;; int const m = 1U << (b - 1)
    (- (logxor x1 m) m)))             ;; r = (x ^ m) - m

(defun sign-extend (b x)
  (declare (xargs :guard (and (posp b)
                              (integerp x))
                  :verify-guards nil))
  (mbe :logic (acl2::logext b x)
       :exec (sign-extend-exec b x)))

(local (defthmd equal-constant
         (implies (and (syntaxp (and (quotep x)
                                     (not (and (consp y)
                                               (member (car y) '(logcar logcdr))))))
                       (integerp x))
                  (equal (equal x y)
                         (and (integerp y)
                              (equal (logcar x) (logcar y))
                              (equal (logcdr x) (logcdr y)))))))

(local (defthm minus-in-terms-of-lognot
         (implies (integerp x)
                  (equal (- x)
                         (+ 1 (lognot x))))
         :hints(("Goal" :in-theory (enable lognot)))))

(defthm sign-extend-exec-is-logext
  (implies (posp b)
           (equal (sign-extend-exec b x)
                  (logext b x)))
  :hints(("Goal" :in-theory (e/d* (ihsext-recursive-redefs
                                   ihsext-arithmetic
                                   ihsext-inductions
                                   sign-extend-exec
                                   equal-logcons-strong)
                                  (ash-1-removal
                                   logand-with-bitmask
                                   logand-with-negated-bitmask
                                   logxor->=-0-linear-2
                                   logxor-<-0-linear-2))
          :induct t)))

(verify-guards sign-extend)

#||

;; basic timing test:

;; 2.1 seconds
(time (loop for i fixnum from 1 to 100000000 do (sign-extend 16 i)))

;; 8.64 seconds
(time (loop for i fixnum from 1 to 100000000 do (logext 16 i)))

||#