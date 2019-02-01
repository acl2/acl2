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

(in-package "STR")

(include-book "printtree")
(local (include-book "printtree-fix"))

(defsection printable-empty-p
  (defund-inline printable-empty-p (x)
    (declare (xargs :guard (printable-p x)))
    (let ((x (printable-fix x)))
      (or (not x) (equal x ""))))

  (local (in-theory (enable printable-empty-p
                            printable-fix
                            printable-p
                            printable->str)))

  (local (defthm character-listp-of-make-character-list
           (character-listp (make-character-list x))))

  (local (defthm coerce-inverse-better
           (equal (coerce (coerce x 'string) 'list)
                  (make-character-list x))
           :hints (("goal" :use ((:instance acl2::completion-of-coerce
                                  (x x) (y 'string)))))))

  (local (defthm length-of-coerce-list-x
           (equal (length (coerce (list x) 'string)) 1)
           :rule-classes nil))

  (local (defthm char-to-list-not-empty
           (not (equal (coerce (list x) 'string) ""))
           :hints (("goal" :use ((:instance length-of-coerce-list-x))))))

  (defthm printable-empty-p-means-empty
    (equal (printable-empty-p x)
           (equal (printable->str x) ""))))

(defsection printtree-obviously-empty-p

  (local (in-theory (enable printtree->str
                            printtree-p)))

  (defund-inline printtree-obviously-empty-p (x)
    (declare (xargs :guard (printtree-p x)))
    (and (atom x)
         (printable-empty-p x)))

  (local (in-theory (enable printtree-obviously-empty-p)))

  (defthmd printtree-obviously-empty-p-implies-empty
    (implies (printtree-obviously-empty-p x)
             (equal (printtree->str x) ""))))

(defsection printtree-concat
  (local (in-theory (enable printtree-obviously-empty-p-implies-empty)))

  (defund printtree-concat (x y)
    (declare (xargs :guard (and (printtree-p x)
                                (printtree-p y))))
    (cond ((printtree-obviously-empty-p x) (printtree-fix y))
          ((printtree-obviously-empty-p y) (printtree-fix x))
          (t (cons (printtree-fix y) (printtree-fix x)))))

  (local (in-theory (enable printtree-concat)))

  (defthm printtree-p-of-printtree-concat
    (printtree-p (printtree-concat x y)))

  (defthm printtree->str-of-printtree-concat
    (equal (printtree->str (printtree-concat x y))
           (string-append (printtree->str x) (printtree->str y)))
    :hints(("Goal" :in-theory (enable printtree->str)))))


(defmacro printtree-rconcat (x y)
  `(printtree-concat ,y ,x))

(defmacro pcat (&rest args)
  (xxxjoin 'printtree-rconcat (reverse args)))
