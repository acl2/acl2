; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2024 Intel Corporation
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

(in-package "FGL")

(include-book "bfr")

(defines fgl-object-bfrcount-tr
  (define fgl-object-bfrcount-tr ((x fgl-object-p)
                                  (count natp))
    :measure (acl2::two-nats-measure (fgl-object-count x) 0)
    :verify-guards nil
    :returns (bfrcount natp :rule-classes :type-prescription)
    (fgl-object-case x
      :g-concrete (lnfix count)
      :g-boolean (+ 1 (lnfix count))
      :g-integer (+ (len x.bits) (lnfix count))
      :g-ite (fgl-object-bfrcount-tr
              x.else
              (fgl-object-bfrcount-tr
               x.then
               (fgl-object-bfrcount-tr x.test count)))
      :g-apply (fgl-objectlist-bfrcount-tr x.args count)
      :g-var (lnfix count)
      :g-cons (fgl-object-bfrcount-tr x.cdr
                                      (fgl-object-bfrcount-tr x.car count))
      :g-map (fgl-object-alist-bfrcount-tr x.alist count)))
  (define fgl-objectlist-bfrcount-tr ((x fgl-objectlist-p)
                                      (count natp))
    :measure (acl2::two-nats-measure (fgl-objectlist-count x) 0)
    :returns (bfrcount natp :rule-classes :type-prescription)
    (if (atom x)
        (lnfix count)
      (fgl-objectlist-bfrcount-tr (cdr x)
                                  (fgl-object-bfrcount-tr (car x) count))))
  (define fgl-object-alist-bfrcount-tr ((x fgl-object-alist-p)
                                        (count natp))
    :measure (acl2::two-nats-measure (fgl-object-alist-count x) (len x))
    :returns (bfrcount natp :rule-classes :type-prescription)
    (if (atom x)
        (lnfix count)
      (if (mbt (consp (car x)))
          (fgl-object-alist-bfrcount-tr
           (cdr x)
           (fgl-object-bfrcount-tr (cdar x) count))
        (fgl-object-alist-bfrcount-tr (cdr x) count))))
  ///
  
  (verify-guards fgl-object-bfrcount-tr)
             

  (fty::deffixequiv-mutual fgl-object-bfrcount-tr
    :hints ((and stable-under-simplificationp
                 '(:expand ((fgl-object-alist-fix x))))))


  (defines fgl-object-bfrcount
    (define fgl-object-bfrcount ((x fgl-object-p))
      :measure (acl2::two-nats-measure (fgl-object-count x) 0)
      :verify-guards nil
      :returns (bfrcount natp :rule-classes :type-prescription)
      (mbe :logic
           (fgl-object-case x
             :g-concrete 0
             :g-boolean 1
             :g-integer (len x.bits)
             :g-ite (+ (fgl-object-bfrcount x.test)
                       (fgl-object-bfrcount x.then)
                       (fgl-object-bfrcount x.else))
             :g-apply (fgl-objectlist-bfrcount x.args)
             :g-var 0
             :g-cons (+ (fgl-object-bfrcount x.car)
                        (fgl-object-bfrcount x.cdr))
             :g-map (fgl-object-alist-bfrcount x.alist))
           :exec (fgl-object-bfrcount-tr x 0)))
    (define fgl-objectlist-bfrcount ((x fgl-objectlist-p))
      :measure (acl2::two-nats-measure (fgl-objectlist-count x) 0)
      :returns (bfrcount natp :rule-classes :type-prescription)
      (mbe :logic
           (if (atom x)
               0
             (+ (fgl-object-bfrcount (car x))
                (fgl-objectlist-bfrcount (cdr x))))
           :exec (fgl-objectlist-bfrcount-tr x 0)))
    (define fgl-object-alist-bfrcount ((x fgl-object-alist-p))
      :measure (acl2::two-nats-measure (fgl-object-alist-count x) (len x))
      :returns (bfrcount natp :rule-classes :type-prescription)
      (mbe :logic
           (if (atom x)
               0
             (if (mbt (consp (car x)))
                 (+ (fgl-object-bfrcount (cdar x))
                    (fgl-object-alist-bfrcount (cdr x)))
               (fgl-object-alist-bfrcount (cdr x))))
           :exec (fgl-object-alist-bfrcount-tr x 0)))
    ///
  
    (local
     (std::defret-mutual <fn>-tr-is-<fn>
       (defret <fn>-tr-is-<fn>
         (equal bfrcount
                (+ (fgl-object-bfrcount x) (nfix count)))
         :hints ('(:expand (<call>
                            (fgl-object-bfrcount x))))
         :fn fgl-object-bfrcount-tr)

       (defret <fn>-tr-is-<fn>
         (equal bfrcount
                (+ (fgl-objectlist-bfrcount x) (nfix count)))
         :hints ('(:expand (<call>
                            (fgl-objectlist-bfrcount x))))
         :fn fgl-objectlist-bfrcount-tr)

       (defret <fn>-tr-is-<fn>
         (equal bfrcount
                (+ (fgl-object-alist-bfrcount x) (nfix count)))
         :hints ('(:expand (<call>
                            (fgl-object-alist-bfrcount x))))
         :fn fgl-object-alist-bfrcount-tr)
       :mutual-recursion fgl-object-bfrcount-tr))

    (verify-guards fgl-object-bfrcount)
  
    (std::defret-mutual <fn>-is-len-of-bfrlist
      (defret <fn>-is-len-of-bfrlist
        (equal bfrcount
               (len (fgl-object-bfrlist x)))
        :hints ('(:expand (<call>
                           (fgl-object-bfrlist x))))
        :fn fgl-object-bfrcount)

      (defret <fn>-is-len-of-bfrlist
        (equal bfrcount
               (len (fgl-objectlist-bfrlist x)))
        :hints ('(:expand (<call>
                           (fgl-objectlist-bfrlist x))))
        :fn fgl-objectlist-bfrcount)

      (defret <fn>-is-len-of-bfrlist
        (equal bfrcount
               (len (fgl-object-alist-bfrlist x)))
        :hints ('(:expand (<call>
                           (fgl-object-alist-bfrlist x))))
        :fn fgl-object-alist-bfrcount)
      :mutual-recursion fgl-object-bfrcount)
             

    (fty::deffixequiv-mutual fgl-object-bfrcount
      :hints ((and stable-under-simplificationp
                   '(:expand ((fgl-object-alist-fix x))))))))

