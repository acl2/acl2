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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "STR")

(include-book "std/basic/defs" :dir :system)

;; Primarily proves transitivity of string< and its behavior on str-fix.

(local (defthm lemma
         (implies (and (character-listp x)
                       (character-listp y)
                       (character-listp z)
                       (string<-l x y n)
                       (string<-l y z n))
                  (string<-l x z n))
         :hints(("Goal" :in-theory (enable string<-l)))))

(local (defthm equal-of-char-code
         (implies (and (characterp x)
                       (characterp y))
                  (equal (equal (char-code x) (char-code y))
                         (equal x y)))
         :hints (("goal" :use ((:instance code-char-char-code-is-identity
                                (c x))
                               (:instance code-char-char-code-is-identity
                                (c y)))
                  :in-theory (disable code-char-char-code-is-identity)))))

(local (defthm lemma2
         (implies (and (character-listp x)
                       (character-listp y)
                       (character-listp z)
                       (integerp n)
                       (not (string<-l x y n))
                       (not (string<-l y z n)))
                  (not (string<-l x z n)))
         :hints(("Goal" :in-theory (enable string<-l)))))

(defthm transitivity-of-string<
  (implies (and (string< x y)
                (string< y z))
           (string< x z))
  :hints(("Goal" :in-theory (enable string<))))

(defthm transitivity-of-string<-negated
  (implies (and (not (string< x y))
                (not (string< y z)))
           (not (string< x z)))
  :hints(("Goal" :in-theory (enable string<))))

(defthm string<-of-str-fix-1
  (equal (string< (str-fix x) y)
         (string< x y))
  :hints(("Goal" :in-theory (enable string< str-fix))))

(defthm string<-of-str-fix-2
  (equal (string< x (str-fix y))
         (string< x y))
  :hints(("Goal" :in-theory (enable string< str-fix))))
