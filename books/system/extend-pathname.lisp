; Proof of termination for extend-pathname
; Copyright (C) 2012 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>
;
; This just proves that EXTEND-PATHNAME terminates.  It doesn't look like we
; can verify its guards, because functions it calls don't have appropriate
; guards, e.g., remove-after-last-directory-separator obviously expects its
; argument to be a string but doesn't have any type/guard declaration for that.

(in-package "ACL2")
(set-state-ok t)


;; Substantially copied from VL/arithmetic
(local
 (encapsulate ()

  (local (in-theory (enable make-character-list)))

  (defthm make-character-list-when-character-listp
    (implies (character-listp x)
             (equal (make-character-list x)
                    x)))

  (defthm character-listp-of-make-character-list
    (character-listp (make-character-list x)))

  (defthm len-of-make-character-list
    (equal (len (make-character-list x))
           (len x)))))


(local (defthm coerce-inverse-1-better
         (equal (coerce (coerce x 'string) 'list)
                (if (stringp x)
                    nil
                  (make-character-list x)))
         :hints(("Goal"
                 :use ((:instance acl2::completion-of-coerce
                                  (acl2::x x)
                                  (acl2::y 'string)))))))

(in-theory (disable coerce-inverse-1))

(local (defthm len-revappend
         (equal (len (revappend x y))
                (+ (len x) (len y)))))

; Mihir M. mod, 04/2019: Adapt to the new definition of take.
(local (defthm len-of-take
         (equal (len (take i l))
                (nfix i))))

(verify-termination find-dot-dot)

(local (defthm length-subseq
         (implies (and (stringp s)
                       (natp m)
                       (natp n)
                       (<= m n)
                       (<= n (length s)))
                  (equal (length (subseq s m n))
                         (- n m)))))

(local (defthm length-string-0
         (implies (and (stringp s)
                       (not (equal s "")))
                  (not (equal (length s) 0)))
         :hints (("Goal"
                  :use ((:instance coerce-inverse-2 (x s)))
                  :in-theory (disable coerce-inverse-2)
                  :expand ((len (coerce s 'list)))))))

(local (in-theory (disable subseq length)))

(verify-termination cancel-dot-dots
; includes get-parent-directory and merge-using-dot-dot
                    (declare (xargs :verify-guards nil)))

(verify-termination our-merge-pathnames)

(verify-termination directory-of-absolute-pathname)

(verify-termination expand-tilde-to-user-home-dir)

(verify-termination extend-pathname)

