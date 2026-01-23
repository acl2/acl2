; Centaur Meta-reasoning Library
; Copyright (C) 2019 Centaur Technology
;
; Copied into separate book (2025)
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
; Original author: Sol Swords <sol.swords@arm.com>


(in-package "CMR")

(include-book "subst")
(local (std::add-default-post-define-hook :fix))

(define pseudo-term-var-listp ((x pseudo-term-listp))
  (if (atom x)
      t
    (and (pseudo-term-case (car x) :var)
         (pseudo-term-var-listp (cdr x))))
  ///
  (defthm pseudo-term-var-listp-of-cons
    (equal (pseudo-term-var-listp (cons a b))
           (and (pseudo-term-case a :var)
                (pseudo-term-var-listp b))))
  (defthm pseudo-term-var-listp-of-append
    (equal (pseudo-term-var-listp (append a b))
           (and (pseudo-term-var-listp a)
                (pseudo-term-var-listp b)))))


(define pseudo-term-var-list->names ((x pseudo-term-listp))
  :guard (pseudo-term-var-listp x)
  :returns (vars pseudo-var-list-p)
  :prepwork ((local (in-theory (enable pseudo-term-var-listp))))
  :verify-guards nil
  (mbe :logic
       (if (atom x)
           nil
         (cons (pseudo-term-var->name (car x))
               (pseudo-term-var-list->names (cdr x))))
       :exec x)
  ///
  (local (defthm var-name-identity-when-well-typed
           (implies (and (pseudo-termp x)
                         (pseudo-term-case x :var))
                    (equal (pseudo-term-var->name x) x))
           :hints(("Goal" :in-theory (enable pseudo-term-var->name
                                             pseudo-term-kind)))))
  
  (verify-guards pseudo-term-var-list->names)
  
  (defthm pseudo-term-var-list->names-when-pseudo-term-listp
    (implies (and (pseudo-term-listp x)
                  (pseudo-term-var-listp x))
             (equal (pseudo-term-var-list->names x) x))
    :hints(("Goal" :in-theory (enable pseudo-termp
                                      pseudo-term-kind
                                      pseudo-term-var->name))))


  (local (in-theory (enable pseudo-term-list-fix)))


  (defthm pseudo-term-var-list->names-of-cons
    (equal (pseudo-term-var-list->names (cons a b))
           (cons (pseudo-term-var->name a)
                (pseudo-term-var-list->names b))))
  (defthm pseudo-term-var-list->names-of-append
    (equal (pseudo-term-var-list->names (append a b))
           (append (pseudo-term-var-list->names a)
                   (pseudo-term-var-list->names b)))))
