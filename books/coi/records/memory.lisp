; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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

(in-package "ACL2")

;This book is a wrapper that includes Jared's fast memories book and then adds some more stuff.

(include-book "data-structures/memories/memory" :dir :system)

;; We could instead use zero as the default value, I guess.
(defund mem::clear (addr mem)
  (declare (xargs :guard (and (mem::memory-p mem)
                              (mem::address-p addr mem))))
  (mem::store addr nil mem))


(defthm clear-over-clear
  (implies (not (equal a1 a2))
           (equal (mem::clear a1 (mem::clear a2 r))
                  (mem::clear a2 (mem::clear a1 r))))
  :hints (("Goal" :in-theory (enable mem::clear))))

(defthm clear-of-clear
  (equal (mem::clear a (mem::clear a r))
         (mem::clear a r))
  :hints (("Goal" :in-theory (enable mem::clear))))

(defthm clear-over-store
  (equal (mem::clear a1 (mem::store a2 v r))
         (if (equal a1 a2)
             (mem::clear a1 r)
           (mem::store a2 v (mem::clear a1 r))))
  :hints (("Goal" :in-theory (enable mem::clear))))

(defthm load-of-clear
  (equal (mem::load a1 (mem::clear a2 r))
         (if (equal a1 a2) nil
           (mem::load a1 r)))
  :hints (("Goal" :in-theory (enable mem::clear))))


;bzo add the other usual theorems about clear

(encapsulate
 ()
 (local (defthm mem::store-equal-rewrite-hard-direction-helper
          (implies (and (equal v (mem::load a r1))
                        (equal (mem::clear a r2) (mem::clear a r1)))
                   (equal (equal (mem::store a v           r2) r1)
                          (equal (mem::store a (mem::load a r1) (mem::store a nil r2))
                                 (mem::store a (mem::load a r1) (mem::store a nil r1)))))
          :rule-classes nil))

 (local (defthm mem::store-equal-rewrite-hard-direction
          (implies (and (equal v (mem::load a r1))
                        (equal (mem::clear a r2) (mem::clear a r1)))
                   (equal (mem::store a v r2) r1))
          :rule-classes nil
          :hints (("goal" :use (:instance mem::store-equal-rewrite-hard-direction-helper)
                   :in-theory (e/d (mem::clear) (MEM::STORE-OF-SAME-STORE
                                                 MEM::STORE-OF-SAME-LOAD
                                                 ))))))

;bzo this same proof should apply to the usual records (do we currently have a more difficult proof of this?)
 (defthm mem::store-equal-rewrite
   (equal (equal (mem::store a v r2) r1)
          (and (equal v (mem::load a r1))
               (equal (mem::clear a r2) (mem::clear a r1))))
   :hints (("Goal" :use (:instance mem::store-equal-rewrite-hard-direction)))))

(encapsulate
 ()
 (local (defthmd store-load-clear
          (equal (mem::store a (mem::load a r) (mem::clear a r))
                 r)))

 (local (defthm clr-differential-hard-direction
          (implies (equal (mem::clear a r1) (mem::clear a r2))
                   (implies (equal (mem::load a r1)
                                   (mem::load a r2))
                            (equal r1
                                   r2)))
          :hints (("Goal" :use ((:instance store-load-clear (r r1))
                                (:instance store-load-clear (r r2)))
                   :in-theory (disable mem::STORE-EQUAL-REWRITE)))
          :rule-classes nil))

 (defthm mem::clr-differential
   (implies (equal (mem::clear a r1) (mem::clear a r2))
            (equal (equal r1 r2)
                   (equal (mem::load a r1)
                          (mem::load a r2))))
   :hints (("Goal" :use (:instance clr-differential-hard-direction)))))

(local (table theory-invariant-table nil nil :clear)) ;grrr

(defthm consp-of-new
  (consp (mem::new size))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable mem::new))))