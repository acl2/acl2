; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
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
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "primitives")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defund << (x y)
  ;; This is a total order over Milawa objects.
  ;;
  ;; We say naturals are smaller than symbols, which are smaller than conses,
  ;; which are recursively ordered lexiographically.  We include a special hack
  ;; for ACL2 compatibility to make this a total order on ACL2 objects as well.
  (declare (xargs :guard t
                  :export
                  ;; We export a Milawa definition that doesn't include the
                  ;; special case for ACL2 compatibility.
                  (cond ((natp x)
                         (if (natp y)
                             (< x y)
                           t))
                        ((natp y)
                         nil)
                        ((symbolp x)
                         (if (symbolp y)
                             (symbol-< x y)
                           t))
                        ((symbolp y)
                         nil)
                        (t
                         (if (equal (car x) (car y))
                             (<< (cdr x) (cdr y))
                           (<< (car x) (car y)))))))
  (cond ((natp x)
         (if (natp y)
             (< x y)
           t))
        ((natp y)
         nil)
        ((symbolp x)
         (if (symbolp y)
             (symbol-< x y)
           t))
        ((symbolp y)
         nil)
        ((or (not (consp x))
             (not (consp y)))
         ;; HACK: Special case for ACL2 compatibility.  We should not need
         ;; this case in Milawa.
         (if (consp x)
             nil
           (if (consp y)
               t
             (and (ACL2::lexorder x y)   ;; ACL2's usual total order
                  (not (equal x y))))))
        (t
         (if (equal (car x) (car y))
             (<< (cdr x) (cdr y))
           (<< (car x) (car y))))))

(local (defthm booleanp-of-acl2-lexorder
         (equal (booleanp (ACL2::lexorder x y))
                t)
         :hints(("Goal" :in-theory (enable booleanp)))))

(defthm booleanp-of-<<
  (equal (booleanp (<< x y))
         t)
  :hints(("Goal" :in-theory (enable <<))))

(defthm irreflexivity-of-<<
  (equal (<< x x)
         nil)
  :hints(("Goal" :in-theory (enable <<))))

(defthm asymmetry-of-<<
  (implies (<< x y)
           (equal (<< y x)
                  nil))
  :hints(("Goal" :in-theory (enable <<))))

(defthm transitivity-of-<<
  (implies (and (<< x y)
                (<< y z))
           (equal (<< x z)
                  t))
  :hints(("Goal" :in-theory (enable <<))))

(defthm forcing-trichotomy-of-<<
  (implies (and (not (<< x y))
                (not (equal x y)))
           (equal (<< y x)
                  t))
  :hints(("Goal" :in-theory (enable <<))))
