; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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

(include-book "clause-processors/pseudo-term-fty" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "logicman")
(include-book "centaur/misc/starlogic" :dir :system)

(local (std::add-default-post-define-hook :fix))

(define equiv-context-p (x)
  (or (pseudo-fnsym-p x)
      (and (consp x)
           (pseudo-termp (car x))
           (equiv-context-p (cdr x))))
  ///
  (define equiv-context-fix ((x equiv-context-p))
    :Returns (new-x equiv-context-p)
    (mbe :logic (if (atom x)
                    (pseudo-fnsym-fix x)
                  (cons (pseudo-term-fix (car x))
                        (equiv-context-fix (cdr x))))
         :exec x)
    ///
    (defthm equiv-context-fix-when-equiv-context-p
      (implies (equiv-context-p x)
               (equal (equiv-context-fix x) x)))

    ;; (defthm len-of-equiv-context-fix
    ;;   (equal (len (equiv-context-fix x)) (len x)))

    (fty::deffixtype equiv-context :pred equiv-context-p :fix equiv-context-fix :equiv equiv-context-equiv
      :define t))

  (defthm pseudo-fnsym-p-of-equiv-context-when-atom
    (implies (atom x)
             (equal (equiv-context-p x)
                    (pseudo-fnsym-p x))))

  (defthm equiv-context-p-of-cdr
    (implies (equiv-context-p x)
             (equiv-context-p (cdr x)))))

(fty::deflist equiv-contexts :pred equiv-contextsp :elt-type equiv-context-p :true-listp t)



(define fgl-ev-equiv-context-equiv ((context equiv-context-p) x y)
  :measure (len (equiv-context-fix context))
  (b* ((context (equiv-context-fix context)))
    (cond ((not context) (equal x y))
          ((atom context)
           (fgl-ev (pseudo-term-fncall context (list (pseudo-term-quote x)
                                                     (pseudo-term-quote y)))
                   nil))
          (t (fgl-ev-equiv-context-equiv
              (cdr context)
              (fgl-ev (car context) `((x . ,x)))
              (fgl-ev (car context) `((x . ,y)))))))
  ///
  (defthm fgl-ev-equiv-context-equiv-equal
    (equal (fgl-ev-equiv-context-equiv nil x y)
           (equal x y)))

  (defthm fgl-ev-equiv-context-equiv-iff
    (equal (fgl-ev-equiv-context-equiv 'iff x y)
           (iff* x y))))

(define fgl-ev-context-equiv ((contexts equiv-contextsp) x y)
  (if (atom contexts)
      (equal x y)
    (or (fgl-ev-equiv-context-equiv (car contexts) x y)
        (fgl-ev-context-equiv (cdr contexts) x y)))
  ///
  (defthm fgl-ev-context-equiv-reflective
    (fgl-ev-context-equiv contexts x x))

  (defthm fgl-ev-context-equiv-nil
    (equal (fgl-ev-context-equiv nil x y)
           (equal x y)))

  (defthm fgl-ev-context-equiv-iff
    (equal (fgl-ev-context-equiv '(iff) x y)
           (iff* x y))))




