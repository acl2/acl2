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
(include-book "decimal")
(include-book "tools/mv-nth" :dir :system)
(local (include-book "arithmetic"))

(defsection charlistnat<
  :parents (ordering)
  :short "Mixed alphanumeric character-list less-than test."

  :long "<p>@(call charlistnat<) determines if the character list @('x') is
\"smaller\" than the character list @('y'), using an ordering that is nice for
humans.</p>

<p>This is almost an ordinary case-sensitive lexicographic ordering.  But,
unlike a simple lexicographic order, we identify sequences of natural number
digits and group them together so that they can be sorted numerically.</p>

<p>Even though this function operates on character lists, let's just talk about
strings instead since they are easier to write down.  If you give most string
sorts a list of inputs like \"x0\" through \"x11\", they will end up in a
peculiar order:</p>

@({\"x0\", \"x1\", \"x10\", \"x11\", \"x2\", \"x3\", ... \"x9\"})

<p>But in @('charlistnat<'), we see the adjacent digits as bundles and sort
them as numbers.  This leads to a nicer ordering:</p>

@({\"x0\", \"x1\", \"x2\", ..., \"x9\", \"x10\", \"x11\"})

<p>This is almost entirely straightforward.  One twist is how to accommodate
leading zeroes.  Our approach is: instead of grouping adjacent digits and
treating them as a natural number, treat them as a pair with a value and a
length.  We then sort these pairs first by value, and then by length.  Hence, a
string such as \"x0\" is considered to be less than \"x00\", etc.</p>

<p>See also @(see strnat<) and @(see icharlist<).</p>"

  (local (in-theory (disable acl2::nth-when-bigger
                             acl2::negative-when-natp
                             default-+-2
                             default-+-1
                             default-<-2
                             commutativity-of-+
                             default-<-1
                             ACL2::|x < y  =>  0 < y-x|
                             char<-trichotomy-strong
                             char<-antisymmetric
                             char<-trichotomy-weak
                             char<-transitive
                             expt
                             default-car
                             default-cdr)))

  (defund charlistnat< (x y)
    (declare (xargs :guard (and (character-listp x)
                                (character-listp y))
                    :measure (len x)))

    (cond ((atom y)
           nil)
          ((atom x)
           t)
          ((and (dec-digit-char-p (car x))
                (dec-digit-char-p (car y)))
           (b* (((mv v1 l1 rest-x) (parse-nat-from-charlist x 0 0))
                ((mv v2 l2 rest-y) (parse-nat-from-charlist y 0 0)))

; The basic idea is to order numbers by their values, and then by their
; lengths.  This second part only is necessary to accomodate leading zeroes.

             (cond ((or (< v1 v2)
                        (and (int= v1 v2)
                             (< l1 l2)))
                    t)
                   ((or (< v2 v1)
                        (and (int= v1 v2)
                             (< l2 l1)))
                    nil)
                   (t
                    (charlistnat< rest-x rest-y)))))

          ((char< (car x) (car y))
           t)
          ((char< (car y) (car x))
           nil)
          (t
           (charlistnat< (cdr x) (cdr y)))))

  (local (in-theory (enable charlistnat<)))

  (defcong charlisteqv equal (charlistnat< x y) 1)
  (defcong charlisteqv equal (charlistnat< x y) 2)

  (defthm charlistnat<-irreflexive
    (not (charlistnat< x x)))

  (defthm charlistnat<-antisymmetric
    (implies (charlistnat< x y)
             (not (charlistnat< y x)))
    :hints(("goal" :in-theory (enable char<-antisymmetric))))

  (encapsulate
    ()
    (local (defthm char<-nonsense-2
             (implies (and (char< a y)
                           (not (dec-digit-char-p a))
                           (dec-digit-char-p y)
                           (dec-digit-char-p z))
                      (char< a z))
             :rule-classes ((:rewrite :backchain-limit-lst 0))
             :hints(("Goal" :in-theory (enable char< dec-digit-char-p)))))

    (local (defthm char<-nonsense-3
             (implies (and (char< y a)
                           (not (dec-digit-char-p a))
                           (dec-digit-char-p x)
                           (dec-digit-char-p y))
                      (char< x a))
             :rule-classes ((:rewrite :backchain-limit-lst 0))
             :hints(("Goal" :in-theory (enable char< dec-digit-char-p)))))

    (local (defthm char<-nonsense-4
             (implies (and (char< x y)
                           (not (dec-digit-char-p y))
                           (dec-digit-char-p x)
                           (dec-digit-char-p z))
                      (not (char< y z)))
             :rule-classes ((:rewrite :backchain-limit-lst 0))
             :hints(("Goal" :in-theory (enable dec-digit-char-p char<)))))



    (defthm charlistnat<-transitive
      (implies (and (charlistnat< x y)
                    (charlistnat< y z))
               (charlistnat< x z))
      :hints(("Goal" :in-theory (e/d ((:induction charlistnat<)
                                      char<-trichotomy-strong
                                      char<-transitive)
                                     (expt charlistnat<-antisymmetric
                                           take-leading-dec-digit-chars-when-dec-digit-char-listp
                                           default-+-2 default-+-1
                                           BOUND-OF-LEN-OF-TAKE-LEADING-DEC-DIGIT-CHARS
                                           LEN-OF-PARSE-NAT-FROM-CHARLIST))
              :induct t
              :expand ((:free (y) (charlistnat< x y))
                       (:free (z) (charlistnat< y z)))))))




    ;; (local (defthm crock
    ;;          (implies (and (equal (take-leading-dec-digit-chars y)
    ;;                               (take-leading-dec-digit-chars x))
    ;;                        (charlisteqv (skip-leading-digits x)
    ;;                                     (skip-leading-digits y)))
    ;;                   (charlisteqv x y))
    ;;          :hints(("Goal"
    ;;                  :induct (my-induction x y)
    ;;                  :expand ((take-leading-dec-digit-chars x)
    ;;                           (take-leading-dec-digit-chars y)
    ;;                           (skip-leading-digits x)
    ;;                           (skip-leading-digits y))))))

    ;; (local (defthm lemma-3
    ;;          (implies (and (equal (len (take-leading-dec-digit-chars y))
    ;;                               (len (take-leading-dec-digit-chars x)))
    ;;                        (equal (dec-digit-chars-value (take-leading-dec-digit-chars y))
    ;;                               (dec-digit-chars-value (take-leading-dec-digit-chars x)))
    ;;                        (charlisteqv (skip-leading-digits x)
    ;;                                     (skip-leading-digits y)))
    ;;                   (equal (charlisteqv x y)
    ;;                          t))
    ;;          :hints(("Goal"
    ;;                  :in-theory (enable chareqv
    ;;                                     take-leading-dec-digit-chars
    ;;                                     skip-leading-digits
    ;;                                     dec-digit-chars-value)))))
    ;; (defthm charlistnat<-trichotomy-weak
    ;;   (implies (and (not (charlistnat< x y))
    ;;                 (not (charlistnat< y x)))
    ;;            (equal (charlisteqv x y)
    ;;                   t))
    ;;   :hints (("goal" :induct (charlistnat< x y)
    ;;            :expand ((charlisteqv x y)
    ;;                     (charlistnat< y x)
    ;;                     (charlistnat< x y)))))

  (encapsulate
    ()
    (local (defthm dec-digit-chars-value-max
             (< (dec-digit-chars-value x) (expt 10 (len x)))
             :hints(("Goal" :in-theory (enable dec-digit-chars-value)))
             :rule-classes :linear))

    (local (defthmd equal-of-sum-digits-lemma1
             (implies (and (posp b)
                           (natp big1)
                           (natp big2)
                           (natp little1)
                           (natp little2)
                           (< little1 b)
                           (< little2 b)
                           (not (equal big1 big2)))
                      (not (equal (+ (* big1 b) little1)
                                  (+ (* big2 b) little2))))
             :hints (("goal" :use ((:instance distributivity (x b) (y big1) (z (- big2)))
                                   (:instance distributivity (x b) (y big2) (z (- big1))))
                      :in-theory (disable distributivity))
                     (and stable-under-simplificationp
                          '(:use ((:instance ACL2::<-*-Y-X-Y
                                   (y b) (x (- big1 big2)))
                                  (:instance ACL2::<-*-Y-X-Y
                                   (y b) (x (- big2 big1))))
                            :in-theory (disable distributivity acl2::<-*-y-x-y)
                            :cases ((and (< (+ big1 (- big2)) 1)
                                         (< (+ big2 (- big1)) 1))))))
             :otf-flg t))

    (local (defthm equal-of-sum-digits
             (implies (and (posp b)
                           (natp big1)
                           (natp big2)
                           (natp little1)
                           (natp little2)
                           (< little1 b)
                           (< little2 b))
                      (iff (equal (+ (* big1 b) little1)
                                  (+ (* big2 b) little2))
                           (and (equal big1 big2)
                                (equal little1 little2))))
             :hints (("goal" :use ((:instance equal-of-sum-digits-lemma1))))))


    (local (defun my-induction (x y)
             (if (and (consp x)
                      (consp y))
                 (my-induction (cdr x) (cdr y))
               nil)))

    (local (defthm lemma-2
             (implies (and (equal (len x) (len y))
                           (character-listp x)
                           (character-listp y)
                           (dec-digit-char-listp x)
                           (dec-digit-char-listp y))
                      (equal (equal (dec-digit-chars-value x)
                                    (dec-digit-chars-value y))
                             (equal x y)))
             :hints(("Goal"
                     :induct (my-induction x y)
                     :in-theory (enable dec-digit-char-listp
                                        dec-digit-chars-value
                                        commutativity-of-+))
                    (and stable-under-simplificationp
                         '(:use ((:instance equal-of-sum-digits
                                  (b (expt 10 (len (cdr x))))
                                  (little1 (dec-digit-chars-value (cdr x)))
                                  (little2 (dec-digit-chars-value (cdr y)))
                                  (big1 (dec-digit-char-value (car x)))
                                  (big2 (dec-digit-char-value (car y))))))))))

    (local (defthm crock
             (implies (and (equal (take-leading-dec-digit-chars y)
                                  (take-leading-dec-digit-chars x))
                           (charlisteqv (skip-leading-digits x)
                                        (skip-leading-digits y)))
                      (charlisteqv x y))
             :hints(("Goal"
                     :induct (my-induction x y)
                     :expand ((take-leading-dec-digit-chars x)
                              (take-leading-dec-digit-chars y)
                              (skip-leading-digits x)
                              (skip-leading-digits y))))))

    (local (defthm lemma-3
             (implies (and (equal (len (take-leading-dec-digit-chars y))
                                  (len (take-leading-dec-digit-chars x)))
                           (equal (dec-digit-chars-value (take-leading-dec-digit-chars y))
                                  (dec-digit-chars-value (take-leading-dec-digit-chars x)))
                           (charlisteqv (skip-leading-digits x)
                                        (skip-leading-digits y)))
                      (equal (charlisteqv x y)
                             t))
             :hints(("Goal"
                     :in-theory (enable chareqv
                                        take-leading-dec-digit-chars
                                        skip-leading-digits
                                        dec-digit-chars-value)))))

    (defthm charlistnat<-trichotomy-weak
      (implies (and (not (charlistnat< x y))
                    (not (charlistnat< y x)))
               (equal (charlisteqv x y)
                      t))
      :hints(("Goal" :in-theory (e/d (char<-trichotomy-strong)
                                     (BOUND-OF-LEN-OF-TAKE-LEADING-DEC-DIGIT-CHARS
                                      TAKE-LEADING-DEC-DIGIT-CHARS-WHEN-DEC-DIGIT-CHAR-LISTP
                                      ACL2::RIGHT-CANCELLATION-FOR-+
                                      CHARLISTNAT<-ANTISYMMETRIC
                                      CHARLISTNAT<-IRREFLEXIVE
                                      )))))

    (defthm charlistnat<-trichotomy-strong
      (equal (charlistnat< x y)
             (and (not (charlisteqv x y))
                  (not (charlistnat< y x))))
      :rule-classes ((:rewrite :loop-stopper ((x y)))))))




(defsection strnat<-aux
  :parents (strnat<)
  :short "Implementation of @(see strnat<)."

  :long "<p>@(call strnat<-aux) is basically the adaptation of @(see
charlistnat<) for strings.  Here, X and Y are the strings being compared, and
XL and YL are their pre-computed lengths.  XN and YN are the indices into the
two strings that are our current positions.</p>

<p>BOZO why do we have XN and YN separately?  It seems like we should only need
one index.</p>"

  (local (in-theory (disable acl2::nth-when-bigger
                             acl2::negative-when-natp
                             default-+-2
                             default-+-1
                             default-<-2
                             commutativity-of-+
                             default-<-1
                             ACL2::|x < y  =>  0 < y-x|
                             ACL2::|x < y  =>  0 < -x+y|
                             char<-trichotomy-strong
                             char<-antisymmetric
                             char<-trichotomy-weak
                             char<-transitive
                             acl2::negative-when-natp
                             acl2::natp-rw
                             expt
                             default-car
                             default-cdr
                             ;(:rewrite PROGRESS-OF-PARSE-NAT-FROM-STRING)
                             )))


  (defund strnat<-aux (x y xn yn xl yl)
    (declare (type string x)
             (type string y)
             (type integer xn)
             (type integer yn)
             (type integer xl)
             (type integer yl)
             (xargs :guard (and (stringp x)
                                (stringp y)
                                (natp xn)
                                (natp yn)
                                (equal xl (length x))
                                (equal yl (length y))
                                (<= xn xl)
                                (<= yn yl))
                    :verify-guards nil
                    :measure
                    (let* ((x  (if (stringp x) x ""))
                           (y  (if (stringp y) y ""))
                           (xn (nfix xn))
                           (yn (nfix yn))
                           (xl (length x))
                           (yl (length y)))
                      (nfix (+ (- yl yn) (- xl xn))))
                    :hints(("Goal" :in-theory (disable ;val-of-parse-nat-from-string
                                                       ;len-of-parse-nat-from-string
                                                       ))))
             (ignorable xl yl))
    (mbe :logic
         (let* ((x  (if (stringp x) x ""))
                (y  (if (stringp y) y ""))
                (xn (nfix xn))
                (yn (nfix yn))
                (xl (length x))
                (yl (length y)))
           (cond ((zp (- yl yn))
                  nil)
                 ((zp (- xl xn))
                  t)
                 ((and (dec-digit-char-p (char x xn))
                       (dec-digit-char-p (char y yn)))
                  (b* (((mv v1 l1)
                        (parse-nat-from-string x 0 0 xn xl))
                       ((mv v2 l2)
                        (parse-nat-from-string y 0 0 yn yl)))
                    (cond ((or (< v1 v2)
                               (and (int= v1 v2)
                                    (< l1 l2)))
                           t)
                          ((or (< v2 v1)
                               (and (int= v1 v2)
                                    (< l2 l1)))
                           nil)
                          (t
                           (strnat<-aux x y (+ xn l1) (+ yn l2) xl yl)))))
                 ((char< (char x xn)
                         (char y yn))
                  t)
                 ((char< (char y yn)
                         (char x xn))
                  nil)
                 (t
                  (strnat<-aux x y (+ 1 xn) (+ 1 yn) xl yl))))
         :exec
         (cond ((int= yn yl)
                nil)
               ((int= xn xl)
                t)
               (t
                (let* ((char-x (the character (char (the string x) (the integer xn))))
                       (char-y (the character (char (the string y) (the integer yn))))
                       (code-x (the (unsigned-byte 8) (char-code (the character char-x))))
                       (code-y (the (unsigned-byte 8) (char-code (the character char-y)))))
                  (declare (type character char-x)
                           (type character char-y)
                           (type (unsigned-byte 8) code-x)
                           (type (unsigned-byte 8) code-y))
                  (cond
                   ((and
                     ;; (dec-digit-char-p (char x xn))
                     (<= (the (unsigned-byte 8) 48) (the (unsigned-byte 8) code-x))
                     (<= (the (unsigned-byte 8) code-x) (the (unsigned-byte 8) 57))
                     ;; (dec-digit-char-p (char y yn))
                     (<= (the (unsigned-byte 8) 48) (the (unsigned-byte 8) code-y))
                     (<= (the (unsigned-byte 8) code-y) (the (unsigned-byte 8) 57)))
                    (b* (((mv v1 l1)
                          (parse-nat-from-string (the string x)
                                                 (the integer 0)
                                                 (the integer 0)
                                                 (the integer xn)
                                                 (the integer xl)))
                         ((mv v2 l2)
                          (parse-nat-from-string (the string y)
                                                 (the integer 0)
                                                 (the integer 0)
                                                 (the integer yn)
                                                 (the integer yl))))
                      (cond ((or (< (the integer v1) (the integer v2))
                                 (and (int= v1 v2)
                                      (< (the integer l1) (the integer l2))))
                             t)
                            ((or (< (the integer v2) (the integer v1))
                                 (and (int= v1 v2)
                                      (< (the integer l2) (the integer l1))))
                             nil)
                            (t
                             (strnat<-aux (the string x)
                                          (the string y)
                                          (the integer (+ (the integer xn) (the integer l1)))
                                          (the integer (+ (the integer yn) (the integer l2)))
                                          (the integer xl)
                                          (the integer yl))))))
                   ((< (the (unsigned-byte 8) code-x) (the (unsigned-byte 8) code-y))
                    t)
                   ((< (the (unsigned-byte 8) code-y) (the (unsigned-byte 8) code-x))
                    nil)
                   (t
                    (strnat<-aux (the string x)
                                 (the string y)
                                 (the integer (+ (the integer 1) (the integer xn)))
                                 (the integer (+ (the integer 1) (the integer yn)))
                                 (the integer xl)
                                 (the integer yl)))))))))

  (local (in-theory (enable strnat<-aux)))
  (set-inhibit-warnings "theory") ;; implicitly local

  (encapsulate
    nil
    (local (in-theory (disable acl2::nth-when-bigger
                               take-leading-dec-digit-chars-when-dec-digit-char-listp
                               dec-digit-char-listp-when-not-consp
                               (:type-prescription character-listp)
                               (:type-prescription eqlable-listp)
                               (:type-prescription atom-listp)
                               (:type-prescription dec-digit-char-p$inline)
                               (:type-prescription strnat<-aux)
                               (:type-prescription char<)
                               default-char-code
                               char<-antisymmetric
                               char<-trichotomy-strong
                               default-<-1 default-<-2
                               default-+-1 default-+-2
                               acl2::open-small-nthcdr
                               acl2::nthcdr-when-zp
                               acl2::nthcdr-when-atom
                               ACL2::|x < y  =>  0 < -x+y|
                               nthcdr len nth not
                               strnat<-aux
                               acl2::natp-fc-1
                               acl2::natp-fc-2
                               (:FORWARD-CHAINING EQLABLE-LISTP-FORWARD-TO-ATOM-LISTP)
                               (:FORWARD-CHAINING CHARACTER-LISTP-FORWARD-TO-EQLABLE-LISTP)
                               (:FORWARD-CHAINING ATOM-LISTP-FORWARD-TO-TRUE-LISTP)
                               )))
    (verify-guards strnat<-aux
      :hints((and stable-under-simplificationp
                  '(:in-theory (enable dec-digit-char-p
                                       dec-digit-char-value
                                       char-fix
                                       char<))))))

  (local (defthm skip-leading-digits-to-nthcdr
           (implies (force (true-listp x))
                    (equal (skip-leading-digits x)
                           (nthcdr (len (take-leading-dec-digit-chars x)) x)))
           :hints(("Goal" :in-theory (enable skip-leading-digits take-leading-dec-digit-chars)))))

  (defthm strnat<-aux-correct
    (implies (and (stringp x)
                  (stringp y)
                  (natp xn)
                  (natp yn)
                  (equal xl (length x))
                  (equal yl (length y))
                  (<= xn xl)
                  (<= yn yl))
             (equal (strnat<-aux x y xn yn xl yl)
                    (charlistnat< (nthcdr xn (explode x))
                                  (nthcdr yn (explode y)))))
    :hints(("Goal"
            :induct (strnat<-aux x y xn yn xl yl)
            :expand ((charlistnat< (nthcdr xn (explode x))
                                   (nthcdr yn (explode y)))
                     (:free (xl yl) (strnat<-aux x y xn yn xl yl)))
            :in-theory (e/d (charlistnat<
                             commutativity-of-+
                             )
                            (charlistnat<-antisymmetric
                             charlistnat<-trichotomy-strong
                             take-leading-dec-digit-chars-when-dec-digit-char-listp
                             dec-digit-char-listp-when-not-consp
                             charlistnat<
                             (:definition strnat<-aux)
                             default-+-1 default-+-2
                             acl2::nth-when-bigger))
            :do-not '(generalize fertilize)))))



(define strnat< ((x :type string)
                 (y :type string))
  :parents (ordering)
  :short "Mixed alphanumeric string less-than test."

  :long "<p>@(call strnat<) determines if the string @('x') is \"smaller\"
than the string @('y'), using an ordering that is nice for humans.</p>

<p>See @(see charlistnat<) for a description of this order.</p>

<p>We avoid coercing the strings into character lists, and this is altogether
pretty fast.</p>"

  :inline t
  (mbe :logic
       (charlistnat< (explode x) (explode y))
       :exec
       (strnat<-aux (the string x)
                    (the string y)
                    (the integer 0)
                    (the integer 0)
                    (the integer (length (the string x)))
                    (the integer (length (the string y)))))
  ///
  (defcong streqv equal (strnat< x y) 1)
  (defcong streqv equal (strnat< x y) 2)

  (defthm strnat<-irreflexive
    (not (strnat< x x)))

  (defthm strnat<-antisymmetric
    (implies (strnat< x y)
             (not (strnat< y x))))

  (defthm strnat<-transitive
    (implies (and (strnat< x y)
                  (strnat< y z))
             (strnat< x z)))

  (defthm strnat<-transitive-alt
    (implies (and (strnat< y z)
                  (strnat< x y))
             (strnat< x z))))
