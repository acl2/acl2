; Memoize Library
; Copyright (C) 2013 Centaur Technology
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
; This library is a descendant of the memoization scheme developed by Bob Boyer
; and Warren A. Hunt, Jr. which was incorporated into the HONS version of ACL2,
; sometimes called ACL2(h).

(in-package "MEMOIZE")

; PONS is the critical function for generating memoization keys.  To a rough
; approximation, here is how we memoize (F arg1 arg2 ... argN):
;
;     PONS := (PIST* arg1 ... argN)
;     LOOK := MemoTableForF[PONS]
;     if (LOOK exists)
;        return LOOK
;     else
;        RESULT := (F arg1 arg2 ... argN)
;        MemoTableForF[PONS] = RESULT
;        return RESULT
;
; In other words, we use (PIST* arg1 ... argN) to create the hash key for the
; arguments arg1 ... argN.  And PIST* is defined in terms of PONS.
;
;    (PIST*)          = NIL
;    (PIST* X1)       = X1
;    (PIST* X1 X2)    = (PONS X1 X2)
;    (PIST* X1 X2 X3) = (PONS X1 (PONS X2 X3))
;      ...                ...
;
; As its name suggests, PONS is similar to a HONS.  The main difference is that
; whereas (HONS X Y) requires us to recursively generate a "canonical" version
; of X and Y, (PONS X Y) does not descend into its arguments.
;
; It is worth noting that in the 0 and 1-ary cases of PIST*, no PONSing is
; necessary!  Because of this it can be considerably cheaper to memoize unary
; and zero-ary functions than higher-arity functions.  Note also that as the
; arity of the function increases, the amount of ponsing (and hence its cost)
; increases.
;
; The soundness requirement on PIST* is that two argument lists should produce
; an EQL keys only if they are pairwise EQUAL.  This follows from a stronger
; property of PONS:
;
;     (EQL (PONS A B) (PONS C D))  --->  (EQL A C) && (EQL B D).
;
; Why is this property sufficient?  The 0-2 argument cases are trivial.  Here
; is an sketch of the 3-ary case, which generalizes easily to the N-ary case:
;
;    Our goal is to ensure:
;
;       If   (EQL (PIST* A1 B1 C1) (PIST* A2 B2 C2))
;       Then (EQUAL A1 A2) && (EQUAL B1 B2) && (EQUAL C2 C2)
;
;    Assume the hypothesis:
;
;       (EQL (PONS A1 (PONS B1 C1)) (PONS A2 (PONS B2 C2)))
;
;    Then from our PONS property it follows immediately that
;
;      1. (EQL A1 A2), and hence (EQUAL A1 A2) since EQL implies EQUAL.
;      2. (EQL (PONS B1 C1) (PONS B2 C2)).
;
;    From 2, again from our PONS property it follows that
;
;      1. (EQL B1 B2), and hence (EQUAL B1 B2) since EQL implies EQUAL.
;      2. (EQL C1 C2), and hence (EQUAL C1 C2) since EQL implies EQUAL.
;
;    Which is what we wanted to show.
;
; For our memoization scheme to be effective, it is desirable for PIST* to
; produce EQL keys when given pairwise-EQL argument lists.  This follows easily
; if our PONS property holds in both directions, that is:
;
;     (EQL (PONS A B) (PONS C D))  <--->  (EQL A C) && (EQL B D).
;
; Okay, so how does PONS actually work?  First we will introduce a "slow"
; ponsing scheme, and then explain an optimization that avoids slow ponsing in
; many cases.
;
;
; Slow Ponsing.
;
; The above discussion hides the fact that PONS and PIST* take an additional
; argument, called the Pons Table.  This table is essentially a scheme for
; remembering which keys we have produced for argument lists that have been
; encountered thus far.  Note that the act of PONSing implicitly modifies the
; Pons Table.
;
; The Pons Table is similar to the CDR-HT-EQL in the Classic Honsing scheme;
; see the Essay on Classic Honsing.  That is, it is an EQL hash table that
; binds each
;
;    Y ->  { key : key is the key for (PONS X Y) }
;
; As in classic honsing, these sets are represented as Flex Alists.  The basic
; implementation of (PONS X Y), then, is as follows:
;
;     Y_KEYS := PonsTable[Y]
;     XY_KEY := FlexAssoc(X, Y_KEYS)
;     If (XY_KEY was found)
;        return XY_KEY
;     Else
;        NewKey = (CONS X Y)
;        Y_KEYS := FlexAcons(NewKey, Y_KEYS)
;        PonsTable[Y] := Y_KEYS
;        return NewKey
;
; In other words, we build a new (X . Y) cons and use it as the key, unless we
; had previously seen these same arguments and such a key is already available.
;
;
; Avoiding Slow Ponsing.
;
; When static honsing is enabled, we activate an improvement to slow ponsing.
;
; In particular, if X and Y can be assigned addresses (see the discussion of
; Static Hons Addressing from hons-raw.lisp) without the use of an OTHER-HT or
; STR-HT, then we can just combine their addresses with hl-addr-combine (which
; is one-to-one) and use the resulting integer as our key.  In many cases this
; allows us to avoid the hash table lookups required in Slow Ponsing.
;
; The basic ideas here are:
;
;   - Some ACL2 objects (any static conses, symbol, or small fixnum) have
;     addresses, but other objects (larger numbers, characters, strings, and
;     ordinary conses) do not.
;
;   - If (PONS X Y) is given X and Y that both had addresses, we basically just
;     hash their addresses with hl-addr-combine.  The resulting integer is used
;     as the key.
;
;   - Otherwise, we fall back to Slow Ponsing.  Since slow ponsing always
;     creates a cons instead of an integer, there's no possibility of confusion
;     between the keys from the two schemes.

#+static-hons
(defun pons-addr-of-argument (x)

; See hl-addr-of.  This is similar, except without the STR-HT or OTHER-HT we
; can simply fail to assign addresses to strings, large numbers, rationals, and
; so forth.

; NOTE: Keep this in sync with hl-addr-of and hl-addr-of-unusual-atom.

  (cond ((eq x nil) 256)
        ((eq x t)   257)

        ((symbolp x)
         (hl-symbol-addr x))

        ((and (typep x 'fixnum)
              (<= hl-minimum-static-int (the fixnum x))
              (<= (the fixnum x) hl-maximum-static-int))
         (the fixnum
           (+ hl-static-int-shift (the fixnum x))))

        ((characterp x)
         (char-code x))

        (t
         nil)))

(defabbrev pons-addr-hash (x y)

; We try to compute the addresses of X and Y and hash them together.  If either
; doesn't have an address, we just return NIL.

  #+static-hons
  (let ((xaddr (pons-addr-of-argument x)))
    (if (not xaddr)
        nil
      (let ((yaddr (pons-addr-of-argument y)))
        (if (not yaddr)
            nil
          (hl-addr-combine* xaddr yaddr)))))

  #-static-hons
  ;; We don't try to avoid ponsing here.
  nil)

(defun pons (x y ht)
  (declare (hash-table ht))

  #+static-hons
  (let ((addr (pons-addr-hash x y)))
    (when addr (return-from pons addr)))

  (let* ((flex-alist (gethash y ht))
         (entry      (hl-flex-assoc x flex-alist)))
    (or entry
        (let* ((was-alistp (listp flex-alist))
               ;; BOZO think about maybe using static cons here... ??
               (new-cons       (cons x y))
               (new-flex-alist (hl-flex-acons new-cons flex-alist)))
          ;; Ctrl+C safety is subtle.  If was-alistp, then the above
          ;; was applicative.  We now install the flex alist, which
          ;; occurs as a single update to the hash table.
          (when was-alistp
            (setf (gethash y ht) new-flex-alist))
          ;; Otherwise, the flex-acons was non-applicative and the table
          ;; was already extended, so there's nothing more we need to do.
          new-cons))))

(defmacro pist* (table &rest x)
  (cond ((atom x) x)
        ((atom (cdr x)) (car x))
        (t `(pons ,(car x)
                  (pist* ,table ,(cdr x))
                  ,table))))



