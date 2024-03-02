; Copyright (C) 2023 Intel Corporation
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
; Original author: Sol Swords <sol.swords@intel.com>


(in-package "ACL2")

(include-book "std/util/define" :dir :system)

(define list-to-tree-aux2 ((logn natp)
                           x)
  :guard (<= (expt 2 logn) (len x))
  :returns (mv tree rest)
  :verify-guards nil
  (b* (((When (zp logn))
        (mv (car x) (cdr x)))
       ((mv first-n rest-after-n)
        (list-to-tree-aux2 (1- logn) x))
       ((mv next-n rest) (list-to-tree-aux2 (1- logn) rest-after-n)))
    (mv (cons first-n next-n) rest))
  ///
  (defret len-rest-of-<fn>
    (equal (len rest)
           (max 0 (- (len x) (expt 2 (nfix logn))))))
  
  (verify-guards list-to-tree-aux2
    :hints (("goal" :expand ((expt 2 logn))))))

(define list-to-tree-aux ((n natp) x)
  :guard (eql n (len x))
  :prepwork ((local (include-book "centaur/bitops/ihsext-basics" :dir :system))
             (local (defthm integer-length-gte-1
                      (implies (not (zp x))
                               (<= 1 (integer-length x)))
                      :hints(("Goal" :expand ((integer-length x))))
                      :rule-classes :type-prescription))
             (local (defthm natp-expt
                      (implies (natp x)
                               (natp (expt 2 x)))
                      :hints(("Goal" :in-theory (enable expt)))
                      :rule-classes :type-prescription))
             (local (defthm expt-2-integer-length-minus-1
                      (implies (not (zp x))
                               (<= (expt 2 (+ -1 (integer-length x))) x))
                      :hints (("goal" :in-theory (enable* bitops::ihsext-inductions
                                                          bitops::ihsext-recursive-redefs
                                                          bitops::logcons-<-n-strong)
                               :induct t)
                              (and stable-under-simplificationp
                                   '(:expand ((:free (j) (expt 2 (integer-length j)))))))
                      :rule-classes :linear)))
  (b* (((when (zp n)) nil)
       (logn (1- (integer-length n)))
       ((mv firsttree rest) (list-to-tree-aux2 logn x)))
    (cons firsttree (list-to-tree-aux (- n (expt 2 logn)) rest))))


(define list-to-tree (x)
  (list-to-tree-aux (len x) x))
                          
