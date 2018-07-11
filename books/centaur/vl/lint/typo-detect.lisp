; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "VL")
(include-book "../util/defs")
(include-book "../util/string-alists")
(include-book "../util/character-list-listp")
(include-book "../loader/lexer/defchar")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))

(defxdoc typo-detection
  :parents (lucid)
  :short "We try to detect possible typos in wire names."

  :long "<p>Verilog implementations allow the use of implicit wires.  Because
of this, a typo in a wire name might go undetected.  As part of our @(see
lucid) analysis, we now try to detect wires that might be typos.</p>

<p>How do we know whether a wire name is actually misspelled, and is not simply
some implicit wire that a logic designer is using?  It is not clear that there
is any hard and fast way to tell.  Our goal, then, is to develop a heuristic
method to identify as many typos as possible (and as few non-typos as
possible).</p>

<p>Here is our approach at a high level.</p>

<ul>

<li>First, we will only consider wires that are not explicitly defined, since
these wires seem to be the obvious starting place to look for typos.  Note that
it is quite easy to identify these wires, e.g., see @(see make-implicit-wires),
which adds declarations to the modules to make these wires explicit.</li>

<li>Next, we will only consider the subset of these wires that are either
unused or unset, per our ordinary @(see lucid) analysis.  The idea behind
this restriction is that typos are probably relatively rare, and it is unlikely
that someone would misspell the name in both contexts.</li>

<li>The names of the remaining wires are then analyzed and compared with the
names of existing, defined wires.  The idea here is that most typos are
probably minor things: character transpositions or omissions, incorrect case,
improper underscores, etc.  Only if the wire's name is somewhat similar to
another wire do we report it as a potential typo.</li>

</ul>

<h3>Analyzing Wire Names</h3>

<p>How can we determine if one wire name is similar to another?  This problem
is reminiscent of spell-checking, where approaches such as Soundex are used to
determine if say that two words sound the same.</p>

<p>The reason that Soundex codes work well for spell checking prose is that,
even though people may not know how to spell the words they want to write, they
usually know how to say them.  So, if someone wants to write the word
<i>Cholera</i>, they might at least write something like <i>Colara</i> instead.
The two \"words\" are phonetically similar, so by assigning and comparing
phonetic codes, we can easily determine which words to suggest.</p>

<p>Soundex codes do not seem particularly appropriate for our task.  Actually,
our job seems easier.  First, let us look at some of the wire names used
throughout the design.  There are some all-uppercase signals such as:</p>

<ul>
 <li>STPCLKB</li>
 <li>THERMDC</li>
 <li>THERMTRIPB</li>
</ul>

<p>And there are some all-lowercase names, such as:</p>

<ul>
 <li>in</li>
 <li>tclk</li>
 <li>vbpa</li>
</ul>

<p>But mostly what we find are mixed-case names, often with underscores, such
as:</p>

<ul>
 <li>mmSnoopDataValid_CX_P</li>
 <li>msBusWriteLOCK_C1_T0_P</li>
 <li>rrT0McTm1PdgClr_P</li>
 <li>orvHi</li>
 <li>x1I3_ReadGflags_X</li>
 <li>rnRomEnSel_A</li>
 <li>matchb39_6b</li>
 <li>bcDWCBAEnt_C0_P</li>
</ul>

<h5>Wire Name Partitioning</h5>

<p>These names are such nonphonetic garble that ordinary algorithms like
Soundex would probably not produce anything meaningful.  On the other hand,
these names seem quite easy to split up into pieces.  And, probably, as someone
trying to type one of these names, I am at least going to get most of these
pieces right.  For instance, if I am trying to write @('rnRomEnSel_A'), I might
forget the abbreviations used and type something like @('rnRomEnableSel_A'), or
forget the underscore and type @('rnRomEnSelA'), or miscapitalize and type
something like @('rnRomEnsel_A').</p>

<p>So, our first move is to split up the wire names into lists of pieces.
Then, we can compare signal names on a piece-by-piece basis.  To carry out this
partitioning, we adopt the following strategy:</p>

<ul>
<li>Consider numbers as lowercase characters.</li>

<li>We split into pieces upon encountering any underscore or other
non-alphanumeric characters, and these special characters are simply dropped.
For instance, given a name like @('rnRomEnSel_A'), we will split into
@('rnRomEnSel') and @('A').</li>

<li>We split on every transition from a lowercase character to an uppercase
character.  For instance, in @('rnRomEnSel_A'), this rule leads us to split
into @('rn'), @('Rom'), @('En'), and @('Sel_A') (which is further split into
@('Sel') and @('A') by the previous rule).</li>

<li>If we see two uppercase characters followed by a lowercase character, we
split between the uppercase characters.  For instance, in @('bcDWCBAEnt_C0_P'),
this rule leads us to split between @('bcDWCBA') and @('Ent_C0_P') (which are
further split by the previous rules into @('bc'), @('DWCBA'), @('Ent'),
@('C0'), and @('P').</li> </ul>


<h5>Comparing Partitioned Names</h5>

<p>Now, suppose we have an implicit wire, <i>a</i>, and an explicit wire
<i>b</i>, and we want to decide whether <i>a</i> might be a typo and the
designer really meant to write <i>b</i>.  We begin by partitioning both wire
names; call the resulting partitionings <i>x</i> and <i>y</i>.</p>

<p>If <i>x</i> and <i>y</i> are equal, then <i>a</i> and <i>b</i> differ only
in that one might have underscores where the other does not.  We think this is
very likely to be a typo.</p>

<p>Otherwise, we compare the pieces of <i>x</i> and <i>y</i> in order.  If
exactly one piece differs, then we may wish to consider whether one to be a
typo of the other after some further analysis.  If more than a single piece is
different, we think <i>x</i> and <i>y</i> are sufficiently distinct from one
another that we will not consider <i>x</i> to be a typo of <i>y</i>.</p>

<p>This further analysis is motivated by looking at examples of matches.</p>

<ul>

<li>First, we require that the two pieces have the same (case insensitive)
leading character.  The motivation here is to prevent considering a wire like
@('bcDWCBAEnt_C0_P') to be a typo of @('bcDWCBAEnt_D0_P').</li>

<li>We additionally require that adding a trailing @('b') or @('B') to either
name does not cause them to become identical.</li>

<li>Finally, if the pieces have the same length, and are identical except that
they end with distinct numbers, we reject the match.  This is intended to
prevent matching between signals like @('bcDWCBAEnt_C0_P') and
@('bcDWCBAEnt_C1_P').</li>

</ul>")

(local (xdoc::set-default-parents typo-detection))

(defchar typo-lowercase
  (or (and (<= 97 (char-code x)) (<= (char-code x) 122))  ;; a-z in ascii.
      (and (<= 48 (char-code x)) (<= (char-code x) 57)))) ;; 0-9 in ascii

(defchar typo-uppercase
  (and (<= 65 (char-code x)) (<= (char-code x) 90))) ;; A-Z in ascii

(defchar typo-number
  (and (<= 48 (char-code x)) (<= (char-code x) 57))) ;; 0-9 in ascii


(defconst *typo-special-substrings*
  ;; Special substrings to consider as parts.  Note that these are tried in
  ;; order, so if there are same-prefixed specials, put the longer ones first.
  (list "eeph1"
        "eph1"
        "ph1"
        "clk"
        "scan"
        "bht"
        "write"
        "data"
        "enable"
        "load"
        "buf"
        "unused"
        "bit"
        "latch"
        "EC"
        ))

(defval *typo-special-substrings-chars*
  (explode-list *typo-special-substrings*))

(define typo-read-special ((substrings character-list-listp)
                           (x          character-listp))
  :returns (mv (prefix character-listp :hyp (force (character-listp x)))
               (remainder character-listp :hyp (force (character-listp x))))
  (cond ((atom substrings)
         (mv nil x))
        ((str::iprefixp (car substrings) x)
         (let ((len (mbe :logic (len (car substrings))
                         :exec (length (car substrings)))))
           (mv (take len x)
               (nthcdr len x))))
        (t
         (typo-read-special (cdr substrings) x)))
  :prepwork
  ((local (defthm lemma
            (implies (str::iprefixp a b)
                     (<= (len a) (len b)))
            :rule-classes ((:rewrite) (:linear))
            :hints(("Goal" :in-theory (enable str::iprefixp))))))
  ///
  (defthm true-listp-of-typo-read-special
    (true-listp (mv-nth 0 (typo-read-special substrings x)))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm acl2-count-of-typo-read-special-weak
    (<= (acl2-count (mv-nth 1 (typo-read-special substrings x)))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-typo-read-special-strong
    (implies (mv-nth 0 (typo-read-special substrings x))
             (< (acl2-count (mv-nth 1 (typo-read-special substrings x)))
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear))))


(define typo-read-lowercase-part
  :short "Read as many lowercase characters as possible, but stop early if a special
          is encountered."
  ((x character-listp))
  :returns (mv (prefix character-listp :hyp (force (character-listp x)))
               (remainder character-listp :hyp (force (character-listp x))))
  (b* (((when (atom x))
        (mv nil x))
       ((mv prefix ?remainder)
        (typo-read-special *typo-special-substrings-chars* x))
       ((when prefix)
        ;; Stop early because a special is coming next.
        (mv nil x))
       ((unless (vl-typo-lowercase-p (car x)))
        (mv nil x))
       ((mv prefix remainder) (typo-read-lowercase-part (cdr x))))
    (mv (cons (car x) prefix) remainder))
  ///
  (defthm true-listp-of-typo-read-lowercase-part
    (true-listp (mv-nth 0 (typo-read-lowercase-part x)))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm typo-read-lowercase-car-under-iff
    (implies (not (mv-nth 0 (typo-read-special *typo-special-substrings-chars* x)))
             (iff (mv-nth 0 (typo-read-lowercase-part x))
                  (vl-typo-lowercase-p (car x)))))

  (defthm acl2-count-of-typo-read-lowercase-weak
    (<= (acl2-count (mv-nth 1 (typo-read-lowercase-part x)))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-typo-read-lowercase-strong
    (implies (mv-nth 0 (typo-read-lowercase-part x))
             (< (acl2-count (mv-nth 1 (typo-read-lowercase-part x)))
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear))))


(define typo-read-uppercase-part
  :short "Read as many uppercase characters as we can."
  ((x character-listp))
  :returns (mv (prefix character-listp :hyp (force (character-listp x)))
               (remainder character-listp :hyp (force (character-listp x))))
  (b* (((when (atom x))
        (mv nil x))
       ((unless (vl-typo-uppercase-p (car x)))
        (mv nil x))
       ((mv prefix remainder)
        (typo-read-uppercase-part (cdr x))))
    (mv (cons (car x) prefix) remainder))
  ///
  (defthm true-listp-of-typo-read-uppercase-part
    (true-listp (mv-nth 0 (typo-read-uppercase-part x)))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm typo-read-uppercase-under-iff
    (iff (mv-nth 0 (typo-read-uppercase-part x))
         (vl-typo-uppercase-p (car x))))

  (defthm acl2-count-of-typo-read-uppercase-weak
    (<= (acl2-count (mv-nth 1 (typo-read-uppercase-part x)))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-typo-read-uppercase-strong
    (implies (mv-nth 0 (typo-read-uppercase-part x))
             (< (acl2-count (mv-nth 1 (typo-read-uppercase-part x)))
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear))))


(define typo-read-part
  :short "Read the first \"part\" of a wire name."
  ((x character-listp))
  :returns (mv (prefix character-listp :hyp (force (character-listp x)))
               (remainder character-listp :hyp (force (character-listp x))))
  (b* (((when (atom x))
        (mv nil nil))
       ((mv prefix remainder)
        (typo-read-special *typo-special-substrings-chars* x))
       ((when prefix)
        ;; Found a special.  Make it its own part.
        (mv prefix remainder))
       ((when (vl-typo-lowercase-p (car x)))
        ;; Part starts with lowercase.  Read as much in lowercase
        ;; as we possibly can.
        (typo-read-lowercase-part x))
       ((unless (vl-typo-uppercase-p (car x)))
        ;; Just completely skip any punctuation stuff.
        (typo-read-part (cdr x)))
       ((when (atom (cdr x)))
        ;; One uppercase character all by itself gets its own part.
        (mv (list (car x)) (cdr x)))
       ((when (vl-typo-lowercase-p (second x)))
        ;; One uppercase character followed by one lowercase.  Read as much
        ;; lowercase as we can from the cdr, and turn it into a part.
        (b* (((mv prefix remainder) (typo-read-lowercase-part (cdr x))))
          (mv (cons (car x) prefix) remainder)))
       ((unless (vl-typo-uppercase-p (second x)))
        ;; Some single uppercase character followed by punctuation or
        ;; something, just return the one char.
        (mv (list (car x)) (cdr x)))
       ;; Else, at least two uppercase characters.  Read as much uppercase as
       ;; we can.
       ((mv prefix remainder) (typo-read-uppercase-part x))
       ((when (atom remainder))
        ;; Nothing follows, so it's just one part.
        (mv prefix remainder))
       ((unless (vl-typo-lowercase-p (car remainder)))
        ;; Either some underscore or other punctuation character follows.  Just
        ;; take this.
        (mv prefix remainder)))
    ;; Finally, it's at least two uppercase chars followed by a lowercase char.
    ;; Remove the last char we read and leave it with the remainder.
    (mv (butlast prefix 1)
        (append (last prefix) remainder)))
  ///
  (defthm true-listp-of-typo-read-part
    (true-listp (mv-nth 0 (typo-read-part x)))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (disable (force)))))

  (local (defthm crock
           (equal (acl2-count (mv-nth 1 (typo-read-uppercase-part x)))
                  (- (acl2-count x)
                     (acl2-count (mv-nth 0 (typo-read-uppercase-part x)))))
           :hints(("Goal" :in-theory (enable typo-read-uppercase-part
                                             acl2-count)))))

  (local (defthm crock2
           (equal (equal 0 (acl2-count (mv-nth 0 (typo-read-uppercase-part x))))
                  (not (mv-nth 0 (typo-read-uppercase-part x))))
           :hints(("Goal" :in-theory (enable typo-read-uppercase-part
                                             acl2-count)))))

  (defthm acl2-count-of-typo-read-part-weak
    (<= (acl2-count (mv-nth 1 (typo-read-part x)))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-typo-read-part-strong
    (implies (mv-nth 0 (typo-read-part x))
             (< (acl2-count (mv-nth 1 (typo-read-part x)))
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear))))


(define typo-partition
  :short "Fully partition a wire name."
  ((x character-listp))
  :returns (parts character-list-listp :hyp :fguard)
  (b* (((when (atom x))
        nil)
       ((mv prefix remainder)
        (typo-read-part x))
       ((unless prefix)
        nil))
    (cons prefix (typo-partition remainder)))
  ///
  (defthm true-listp-of-typo-partition
    (true-listp (typo-partition x))
    :rule-classes :type-prescription))

#||
;; Some simple test cases.

(typo-partition (coerce "mmSnoopDataValid_CX_P" 'list))
(typo-partition (coerce "mmSnopDataValid_CX_P" 'list))
(typo-partition (coerce "STPCLKB" 'list))
(typo-partition (coerce "rrT0McTm1PdgClr_P" 'list))
(typo-partition (coerce "orvHi" 'list))
(typo-partition (coerce "x1I3_ReadGflags_X" 'list))
(typo-partition (coerce "rnRomEnSel_A" 'list))
(typo-partition (coerce "matchb39_6b" 'list))
(typo-partition (coerce "bcDWCBAEnt_C0_P" 'list))
||#

(define typo-partitioning-alist
  :short "Build an alist mapping strings to their partitionings."
  ((x string-listp))
  :returns (al alistp)
  (if (atom x)
      nil
    (cons (cons (car x)
                (typo-partition (explode (car x))))
          (typo-partitioning-alist (cdr x))))
  ///
  (defthm vl-string-keys-p-of-typo-partitioning-alist
    (implies (force (string-listp x))
             (vl-string-keys-p (typo-partitioning-alist x))))

  (defthm vl-character-list-values-p-of-typo-partitioning-alist
    (vl-character-list-list-values-p (typo-partitioning-alist x))))


(define vl-typo-count-mismatches (x y)
  :short "Given two same-length partitionings, determine how many of their
  pieces are mismatched."
  :guard (same-lengthp x y)
  (cond ((atom x)
         0)
        ((equal (car x) (car y))
         (vl-typo-count-mismatches (cdr x) (cdr y)))
        (t
         (+ 1 (vl-typo-count-mismatches (cdr x) (cdr y))))))


(define vl-typo-first-mismatch (x y)
  :short "Given two same-length partitionings, return their first mismatch as a
  pair."
  :guard (same-lengthp x y)
  (cond ((atom x)
         nil)
        ((equal (car x) (car y))
         (vl-typo-first-mismatch (cdr x) (cdr y)))
        (t
         (cons (car x) (car y))))
  ///
  (defthm character-list-p-of-vl-typo-first-mismatch-1
    (implies (and (character-list-listp x)
                  (character-list-listp y))
             (character-listp (car (vl-typo-first-mismatch x y)))))

  (defthm character-list-p-of-vl-typo-first-mismatch-2
    (implies (and (character-list-listp x)
                  (character-list-listp y))
             (character-listp (cdr (vl-typo-first-mismatch x y))))))

(defval *typo-numbers*
  '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))

(define typo-numbers ()
  *typo-numbers*
  ///
  (in-theory (disable (:executable-counterpart typo-numbers)))
  (defthm setp-of-typo-numbers
    (setp (typo-numbers))))


(define typo-mismatch-plausibly-typo-p
  :short "X and Y are single pieces that are mismatched.  Do they satisfy our
  criteria for being considered \"possibly a typo\"?"
  ((x character-listp)
   (y character-listp))
  (and (consp x)
       (consp y)
       ;; Require the first character to agree.
       (str::ichareqv (car x) (car y))
       ;; Require at least two non-digit characters are present in both
       ;; strings.  This is kind of silly but acts as a filter to prevent
       ;; things like "St0" and "Sf0" from being considered typos.
       (<= 2 (cardinality (difference (intersect (mergesort x) (mergesort y))
                                      (typo-numbers))))
       ;; Don't call it a typo if adding a B or b to either side makes them
       ;; equal.
       (not (or (equal (append x (list #\b)) y)
                (equal (append x (list #\B)) y)
                (equal x (append y (list #\b)))
                (equal x (append y (list #\B)))))
       ;; Same for Q and q.
       (not (or (equal (append x (list #\q)) y)
                (equal (append x (list #\Q)) y)
                (equal x (append y (list #\q)))
                (equal x (append y (list #\Q)))))
       (let ((xlast (car (last x)))
             (ylast (car (last y))))
         (and
          ;; Don't consider it a typo if they are the same except that they end
          ;; with different numbers, e.g., "foo1 is not a typo of foo2."
          (not (and (same-lengthp x y)
                    (equal (butlast x 1) (butlast y 1))
                    (and (vl-typo-number-p xlast)
                         (vl-typo-number-p ylast))))
          ;; Don't consider it a typo if they are the same except that one has
          ;; an extra number at the end, e.g., "foo is not a typo of foo2."
          (not (and (equal (butlast x 1) y)
                    (vl-typo-number-p xlast)))
          (not (and (equal (butlast y 1) x)
                    (vl-typo-number-p ylast)))))))

(define typo-partitions-plausibly-typo-p
  :short "X and Y are whole-partitionings.  Do they satisfy our criteria
          for being considered \"possibly a typo\"?"
  ((x character-list-listp)
   (y character-list-listp))

; First criteria: they have the same length.

  (and (same-lengthp x y)
       (or

; Possible typo 1: the parts lists are equal (differ only by how the
; parts follow one another.

        (equal x y)

; Possible typo 2: the parts lists have exactly one difference, and
; the mismatch is considered plausibly a typo.

        (and (= (vl-typo-count-mismatches x y) 1)
             (let ((mismatch (vl-typo-first-mismatch x y)))
               (typo-mismatch-plausibly-typo-p (car mismatch)
                                               (cdr mismatch)))))))


;; (typo-partitions-plausibly-typo-p
;;  (typo-partition (coerce "rnRomEnSel_A" 'list))
;;  (typo-partition (coerce "rnRomEnSelA" 'list)))

;; (typo-partitions-plausibly-typo-p
;;  (typo-partition (coerce "rnRomEnSel_A" 'list))
;;  (typo-partition (coerce "rnRomEnableSelA" 'list)))

;; (typo-partitions-plausibly-typo-p
;;  (typo-partition (coerce "rnRomEnSel_A" 'list))
;;  (typo-partition (coerce "rnRomEnSel_B" 'list)))

(define typo-find-plausible-typos1
  :short "Walk down the partitioning alist and gather the names of all signals
          that Part might be a typo for."
  ((part  character-list-listp "Partitioning of a single wire.")
   (alist alistp               "Partitioning alist for a list of wires."))
  :guard (and (vl-string-keys-p alist)
              (vl-character-list-list-values-p alist))
  :returns (plausible-typos string-listp :hyp (force (vl-string-keys-p alist)))
  (cond ((atom alist)
         nil)
        ((typo-partitions-plausibly-typo-p part (cdar alist))
         (cons (caar alist)
               (typo-find-plausible-typos1 part (cdr alist))))
        (t
         (typo-find-plausible-typos1 part (cdr alist)))))

(define typo-detect-aux
  :short "We build an alist that might associate some of the wires to the
          lists of wires we think they could be typos of."
  ((strs string-listp "A list of strings, generally the \"implicit wires\" for
                       a module.")
   (alist alistp      "A partitioning alist, generally constructed from the
                       \"explicit wires\" for the module."))
  :guard (and (vl-string-keys-p alist)
              (vl-character-list-list-values-p alist))
  :returns (typo-alist alistp)
  (b* (((when (atom strs))
        nil)
       (name1      (car strs))
       ((when (or (str::substrp "SDN" name1)
                  (str::substrp "SDF" name1)))
        ;; Some primitive modules have SDN/SDF and these look close
        ;; enough alike that they cause a lot of problems, so suppress
        ;; typo warnings about these particular substrings.
        (typo-detect-aux (cdr strs) alist))
       (partition1 (typo-partition (explode name1)))
       (typos1     (typo-find-plausible-typos1 partition1 alist))
       ((when typos1)
        (cons (cons name1 typos1)
              (typo-detect-aux (cdr strs) alist))))
    (typo-detect-aux (cdr strs) alist))
  ///
  (defthm vl-string-keys-p-of-typo-detect-aux
    (implies (force (string-listp strs))
             (vl-string-keys-p (typo-detect-aux strs alist))))

  (defthm vl-string-list-values-p-of-typo-detect-aux
    (implies (force (vl-string-keys-p alist))
             (vl-string-list-values-p (typo-detect-aux strs alist)))))


(define typo-detect
  :short "Build an alist associating any \"bad\" wires with any \"good\" wires
   that they may be typos for."
  ((bad string-listp  "Names of wires we think are somehow bad.  It could be,
                       e.g., all of the implicit wires in a module, or all of
                       the implicit wires that are only partly used, etc.")
   (good string-listp "Names of all the wires we think are somehow good; e.g.,
                       declared, used, etc."))
  :returns (alist alistp)
  ;; Note: consider removing any good wires from bad, and any bad wires from
  ;; good.  E.g.,
  ;;(let* ((bad*  (mergesort bad))
  ;;       (good* (mergesort good))
  ;;       (bad   (difference bad* good*))
  ;;       (good  (difference good* bad*)))
  (typo-detect-aux bad (typo-partitioning-alist good))
  ///
  (defthm vl-string-keys-p-of-typo-detect
    (implies (force (string-listp bad))
             (vl-string-keys-p (typo-detect bad good))))

  (defthm vl-string-list-values-p-of-typo-detect
    (implies (force (string-listp good))
             (vl-string-list-values-p (typo-detect bad good)))))


