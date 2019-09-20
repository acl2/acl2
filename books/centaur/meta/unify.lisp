; Centaur Meta-reasoning Library
; Copyright (C) 2019 Centaur Technology
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

(in-package "CMR")

(include-book "subst")

(defines pseudo-term-unify
  (define pseudo-term-unify ((pat pseudo-termp)
                             (x pseudo-termp)
                             (alist pseudo-term-subst-p))
    :measure (pseudo-term-count pat)
    :hints ((and stable-under-simplificationp
                 '(:cases ((equal (pseudo-term-kind pat) :lambda)
                           (equal (pseudo-term-kind pat) :fncall)))))
    :returns (mv ok (new-alist pseudo-term-subst-p))
    :verify-guards nil
    (b* ((x (pseudo-term-fix x))
         (alist (pseudo-term-subst-fix alist)))
      (pseudo-term-case pat
        :var (b* ((look (assoc pat.name alist)))
               (if look
                   (if (equal (cdr look) x)
                       (mv t alist)
                     (mv nil alist))
                 (mv t (cons (cons pat.name x) alist))))
        :const (pseudo-term-case x
                 :const
                 (if (equal x.val pat.val)
                     (mv t alist)
                   (mv nil alist))
                 :otherwise (mv nil alist))
        :call (pseudo-term-case x
                :call
                (if (equal x.fn pat.fn)
                    (pseudo-term-list-unify pat.args x.args alist)
                  (mv nil alist))
                :otherwise (mv nil alist)))))
  (define pseudo-term-list-unify ((pat pseudo-term-listp)
                                  (x pseudo-term-listp)
                                  (alist pseudo-term-subst-p))
    :measure (pseudo-term-list-count pat)
    :returns (mv ok (new-alist pseudo-term-subst-p))
    (b* ((alist (pseudo-term-subst-fix alist)))
      (if (atom pat)
          (if (atom x)
              (mv t alist)
            (mv nil alist))
        (if (atom x)
            (mv nil alist)
          (b* (((mv ok alist) (pseudo-term-unify (car pat) (car x) alist))
               ((unless ok) (mv nil alist)))
            (pseudo-term-list-unify (cdr pat) (cdr x) alist))))))

  ///
  (verify-guards pseudo-term-unify)
  
  (fty::deffixequiv-mutual pseudo-term-unify))
