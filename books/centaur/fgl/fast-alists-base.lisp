; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
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

(in-package "FGL")
(include-book "logicman")
(local (std::add-default-post-define-hook :fix))


(define fgl-make-fast-alist-concrete-rec (x)
  :returns (mv ok (new-x fgl-object-alist-p))
  (if (atom x)
      (mv t x)
    (if (atom (car x))
        (mv nil nil)
      (b* (((mv ok rest) (fgl-make-fast-alist-concrete-rec (cdr x))))
        (if ok
            (mv t (cons (cons (caar x) (g-concrete (cdar x))) rest))
          (mv nil nil)))))
  ///
  (defret fgl-object-alist-eval-of-<fn>
    (implies ok
             (equal (fgl-object-alist-eval new-x env) x))
    :hints (("goal" :induct <call>
             :expand ((fgl-object-alist-eval x env)))))

  (defret fgl-object-alist-bfrlist-of-<fn>
    (equal (fgl-object-alist-bfrlist new-x) nil)))

(define fgl-make-fast-alist-concrete-rec-tr (x (acc fgl-object-alist-p))
  :guard (true-listp acc)
  :returns (mv ok (new-x fgl-object-alist-p))
  (if (atom x)
      (mv t (revappend (fgl-object-alist-fix acc) x))
    (if (atom (car x))
        (mv nil nil)
      (fgl-make-fast-alist-concrete-rec-tr
       (cdr x) (cons (cons (caar x) (g-concrete (cdar x))) acc))))
  ///
  (defret <fn>-normalize-to-fgl-make-fast-alist-concrete-rec
    (b* (((mv ok-spec new-x-spec) (fgl-make-fast-alist-concrete-rec x)))
      (and (iff ok ok-spec)
           (implies ok-spec
                    (equal new-x
                           (revappend (fgl-object-alist-fix acc) new-x-spec)))))
    :hints(("Goal" :in-theory (enable fgl-make-fast-alist-concrete-rec)))))
        

(define fgl-make-fast-alist-rec ((x fgl-object-p))
  :returns (mv ok (new-x fgl-object-alist-p))
  :measure (fgl-object-count x)
  (fgl-object-case x
    :g-concrete (fgl-make-fast-alist-concrete-rec x.val)
    :g-map (mv t x.alist)
    :g-cons (b* (((mv rest-ok rest) (fgl-make-fast-alist-rec x.cdr))
                 ((unless rest-ok) (mv nil nil)))
              (fgl-object-case x.car
                :g-concrete (if (consp x.car.val)
                                (mv t (cons (cons (car x.car.val) (g-concrete (cdr x.car.val))) rest))
                              (mv nil nil))
                :g-cons (fgl-object-case x.car.car
                          :g-concrete (mv t (cons (cons x.car.car.val x.car.cdr)
                                                  rest))
                          :otherwise (mv nil nil))
                :otherwise (mv nil nil)))
    :otherwise (mv nil nil))
  ///
  (defret fgl-object-alist-eval-of-<fn>
    (implies ok
             (equal (fgl-object-alist-eval new-x env)
                    (fgl-object-eval x env))))

  (defret fgl-object-alist-bfrlist-of-<fn>
    (implies (not (member v (fgl-object-bfrlist x)))
             (not (member v (fgl-object-alist-bfrlist new-x))))))

(define fgl-make-fast-alist-rec-tr ((x fgl-object-p)
                                    (acc fgl-object-alist-p))
  :guard (true-listp acc)
  :returns (mv ok (new-x fgl-object-alist-p))
  :measure (fgl-object-count x)
  (fgl-object-case x
    :g-concrete (fgl-make-fast-alist-concrete-rec-tr x.val acc)
    :g-map (mv t (revappend (fgl-object-alist-fix acc) x.alist))
    :g-cons (fgl-object-case x.car
              :g-concrete
              (if (consp x.car.val)
                  (fgl-make-fast-alist-rec-tr x.cdr
                                              (cons (cons (car x.car.val) (g-concrete (cdr x.car.val))) acc))
                (mv nil nil))
              :g-cons
              (fgl-object-case x.car.car
                :g-concrete
                (fgl-make-fast-alist-rec-tr
                 x.cdr (cons (cons x.car.car.val x.car.cdr) acc))
                :otherwise (mv nil nil))
              :otherwise (mv nil nil))
    :otherwise (mv nil nil))
  ///
  (defret <fn>-normalize-to-fgl-make-fast-alist-rec
    (b* (((mv ok-spec new-x-spec) (fgl-make-fast-alist-rec x)))
      (and (iff ok ok-spec)
           (implies ok
                    (equal new-x (revappend (fgl-object-alist-fix acc) new-x-spec)))))
    :hints(("Goal" :in-theory (enable fgl-make-fast-alist-rec)))))

