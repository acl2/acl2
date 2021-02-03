; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
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

(in-package "STR")
(include-book "coerce")
(include-book "std/lists/equiv" :dir :system)
(include-book "std/lists/rev" :dir :system)
(include-book "centaur/fty/fixtype" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(local (include-book "arithmetic"))

(in-theory (disable char<))

(defsection char<-order-thms
  :parents (char<)
  :short "Basic ordering facts about @('char<')."

  (local (in-theory (enable char< char-fix)))

  (defthm char<-irreflexive
    (equal (char< x x)
           nil))

  (defthm char<-antisymmetric
    (implies (char< x y)
             (not (char< y x))))

  (defthm char<-transitive
    (implies (and (char< x y)
                  (char< y z))
             (char< x z)))

  (defthm char<-trichotomy-weak
    (implies (and (not (char< x y))
                  (not (char< y x)))
             (equal (chareqv x y)
                    t))
    :hints(("Goal" :in-theory (enable chareqv))))

  (defthm char<-trichotomy-strong
    (equal (char< x y)
           (and (not (chareqv x y))
                (not (char< y x))))
    :rule-classes ((:rewrite :loop-stopper ((x y))))))


(define character-list-fix ((x character-listp))
  :parents (character-listp make-character-list)
  :short "Inline fixing function for character lists."
  :long "<p>This is identical to @(see make-character-list) except that the
guard requires that @('x') is already a @(see character-listp) so that, via
@(see mbe), we can just return @('x') without fixing it.  We leave this
function enabled and never expect to reason about it.</p>"
  :inline t
  :enabled t
  (mbe :logic (make-character-list x)
       :exec x))


(define charlisteqv ((x character-listp)
                     (y character-listp))
  :returns equivp
  :parents (equivalences)
  :inline t
  :short "Case-sensitive character-list equivalence test."

  :long "<p>@(call charlisteqv) determines if @('x') and @('y') are equivalent
when interpreted as character lists.  That is, @('x') and @('y') must have the
same length and their elements must be @(see chareqv) to one another.</p>

<p>See also @(see icharlisteqv) for a case-insensitive alternative.</p>"

  (mbe :logic
       (equal (make-character-list x)
              (make-character-list y))
       :exec
       (equal x y))
  ///
  (defequiv charlisteqv)

  (local (defun ind (x y)
           (if (or (atom x) (atom y))
               (list x y)
             (ind (cdr x) (cdr y)))))

  (defrefinement list-equiv charlisteqv
    :hints(("Goal"
            :in-theory (enable list-equiv)
            :induct (ind x y))))

  (local (in-theory (enable chareqv)))

  (defcong charlisteqv chareqv     (car x)      1)
  (defcong charlisteqv charlisteqv (cdr x)      1)
  (defcong chareqv     charlisteqv (cons a x)   1)
  (defcong charlisteqv charlisteqv (cons a x)   2)
  (defcong charlisteqv equal       (len x)      1 :hints(("Goal" :induct (ind x x-equiv))))
  (defcong charlisteqv charlisteqv (list-fix x) 1)
  (defcong charlisteqv chareqv     (nth n x)    2)
  (defcong charlisteqv charlisteqv (take n x)   2)
  (defcong charlisteqv charlisteqv (nthcdr n x) 2)
  (defcong charlisteqv charlisteqv (append x y) 1)
  (defcong charlisteqv charlisteqv (append x y) 2)
  (defcong charlisteqv charlisteqv (rev x)      1)
  (defcong charlisteqv charlisteqv (revappend x y) 2)
  (defcong charlisteqv charlisteqv (revappend x y) 1)
  (defcong charlisteqv equal (make-character-list x) 1)

  (defcong charlisteqv equal (implode x) 1
    :hints(("Goal"
            :in-theory (disable implode-of-make-character-list)
            :use ((:instance implode-of-make-character-list (x x))
                  (:instance implode-of-make-character-list (x x-equiv))))))

  (defthm charlisteqv-when-not-consp-left
    (implies (not (consp x))
             (equal (charlisteqv x y)
                    (atom y))))

  (defthm charlisteqv-when-not-consp-right
    (implies (not (consp y))
             (equal (charlisteqv x y)
                    (atom x))))

  (defthm charlisteqv-of-cons-right
    (equal (charlisteqv x (cons a y))
           (and (consp x)
                (chareqv (car x) (double-rewrite a))
                (charlisteqv (cdr x) (double-rewrite y)))))

  (defthm charlisteqv-of-cons-left
    (equal (charlisteqv (cons a x) y)
           (and (consp y)
                (chareqv (double-rewrite a) (car y))
                (charlisteqv (double-rewrite x) (cdr y)))))

  (defthm charlisteqv-when-not-same-lens
    (implies (not (equal (len x) (len y)))
             (not (charlisteqv x y)))
    :hints(("Goal" :induct (ind x y))))

  (defthm make-character-list-is-identity-under-charlisteqv
    (str::charlisteqv (make-character-list x)
                      x))

  (defthmd charlisteqv*
    ;; For compatibility with the old definition
    (equal (charlisteqv x y)
           (if (consp x)
               (and (consp y)
                    (chareqv (car x) (car y))
                    (charlisteqv (cdr x) (cdr y)))
             (atom y)))
    :rule-classes ((:definition :controller-alist ((charlisteqv$inline t nil))))
    :hints(("Goal" :induct (ind x y)))))

;; BOZO kind of misplaced

(defcong streqv equal (explode x) 1
  :hints(("Goal" :in-theory (enable streqv str-fix))))

(fty::deffixtype character-list
  :pred character-listp
  :fix make-character-list
  :equiv charlisteqv
  :topic character-listp)

(define string-list-fix ((x string-listp))
  :returns (x-fix string-listp)
  (mbe :logic (if (atom x)
                  nil
                (cons (str-fix (car x))
                      (string-list-fix (cdr x))))
       :exec x)
  ///
  (defthm string-list-fix-when-atom
    (implies (atom x)
             (equal (string-list-fix x)
                    nil)))
  (defthm string-list-fix-of-cons
    (equal (string-list-fix (cons a x))
           (cons (str-fix a) (string-list-fix x))))
  (defthm string-list-fix-when-string-listp
    (implies (string-listp x)
             (equal (string-list-fix x)
                    x)))
  (defthm consp-of-string-list-fix
    (equal (consp (string-list-fix x))
           (consp x)))
  (defthm len-of-string-list-fix
    (equal (len (string-list-fix x))
           (len x))))

(defsection string-list-equiv

  (local (in-theory (enable string-list-fix)))

  (fty::deffixtype string-list
    :pred string-listp
    :fix string-list-fix
    :equiv string-list-equiv
    :define t
    :forward t
    :topic string-listp)

  (fty::deffixcong string-list-equiv streqv (car x) x)
  (fty::deffixcong string-list-equiv string-list-equiv (cdr x) x)
  (fty::deffixcong streqv string-list-equiv (cons x y) x)
  (fty::deffixcong string-list-equiv string-list-equiv (cons x y) y))
