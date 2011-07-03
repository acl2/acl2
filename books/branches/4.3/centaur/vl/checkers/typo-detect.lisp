; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "../util/defs")
(include-book "../util/string-alists")
(include-book "../util/character-list-listp")
(include-book "../loader/lexer-utils")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))



(defxdoc typo-detection
  :parents (use-set)

  :short "We try to detect possible typos in wire names."

  :long "<p>Verilog implementations allow the use of implicit wires.  Because
of this, a typo in a wire name might go undetected.  As part of our @(see
use-set) analysis, we now try to detect wires that might be typos.</p>

<p>How do we know whether a wire name is actually misspelled, and is not simply
some implicit wire that a logic designer is using?  It is not clear that there
is any hard and fast way to tell.  Our goal, then, is to develop a heuristic
method to identify as many typos as possible (and as few non-typos as
possible).</p>

<p>Here is our approach at a high level.</p>

<ul>

<li>First, we will only consider wires that are not explicitly defined, since
these wires seem to be the obvious starting place to look for typos.  Note that
it is quite easy to identify these wires, e.g., see @(see
vl-module-implicitwires), and the transformation @(see make-implicit-wires)
which adds declarations to the modules to make these wires explicit.</li>

<li>Next, we will only consider the subset of these wires that are either
unused or unset, per our ordinary @(see use-set) analysis.  The idea behind
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
pieces right.  For instance, if I am trying to write <tt>rnRomEnSel_A</tt>, I
might forget the abbreviations used and type something like
<tt>rnRomEnableSel_A</tt>, or forget the underscore and type
<tt>rnRomEnSelA</tt>, or miscapitalize and type something like
<tt>rnRomEnsel_A</tt>.</p>

<p>So, our first move is to split up the wire names into lists of pieces.
Then, we can compare signal names on a piece-by-piece basis.  To carry out this
partitioning, we adopt the following strategy:</p>

<ul>
<li>Consider numbers as lowercase characters.</li>

<li>We split into pieces upon encountering any underscore or other
non-alphanumeric characters, and these special characters are simply dropped.
For instance, given a name like <tt>rnRomEnSel_A</tt>, we will split into
<tt>rnRomEnSel</tt> and <tt>A</tt>.</li>

<li>We split on every transition from a lowercase character to an uppercase
character.  For instance, in <tt>rnRomEnSel_A</tt>, this rule leads us to split
into <tt>rn</tt>, <tt>Rom</tt>, <tt>En</tt>, and <tt>Sel_A</tt> (which is
further split into <tt>Sel</tt> and <tt>A</tt> by the previous rule).</li>

<li>If we see two uppercase characters followed by a lowercase character, we
split between the uppercase characters.  For instance, in
<tt>bcDWCBAEnt_C0_P</tt>, this rule leads us to split between <tt>bcDWCBA</tt>
and <tt>Ent_C0_P</tt> (which are further split by the previous rules into
<tt>bc</tt>, <tt>DWCBA</tt>, <tt>Ent</tt>, <tt>C0</tt>, and <tt>P</tt>.</li>
</ul>


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
<tt>bcDWCBAEnt_C0_P</tt> to be a typo of <tt>bcDWCBAEnt_D0_P</tt>.</li>

<li>We additionally require that adding a trailing <tt>b</tt> or <tt>B</tt>
to either name does not cause them to become identical.</li>

<li>Finally, if the pieces have the same length, and are identical except that
they end with distinct numbers, we reject the match.  This is intended to
prevent matching between signals like <tt>bcDWCBAEnt_C0_P</tt> and
<tt>bcDWCBAEnt_C1_P</tt>.</li>

</ul>
")

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
        ))


(defconst *typo-special-substrings-chars*
  (coerce-to-chars-list *typo-special-substrings*))

(defsection typo-read-special

  (defund typo-read-special (substrings x)
    (declare (xargs :guard (and (character-list-listp substrings)
                                (character-listp x))))
    (cond ((atom substrings)
           (mv nil x))
          ((str::iprefixp (car substrings) x)
           (let ((len (mbe :logic (len (car substrings))
                           :exec (length (car substrings)))))
             (mv (take len x)
                 (nthcdr len x))))
          (t
           (typo-read-special (cdr substrings) x))))

  (local (in-theory (enable typo-read-special)))

  (defthm true-listp-of-typo-read-special
    (true-listp (mv-nth 0 (typo-read-special substrings x)))
    :rule-classes :type-prescription)

  (local (defthm lemma
           (implies (str::iprefixp a b)
                    (<= (len a) (len b)))
           :rule-classes ((:rewrite) (:linear))
           :hints(("Goal" :in-theory (enable str::iprefixp)))))

  (defthm typo-read-special-basics
    (implies (force (character-listp x))
             (and (character-listp (mv-nth 0 (typo-read-special substrings x)))
                  (character-listp (mv-nth 1 (typo-read-special substrings x))))))

  (defthm acl2-count-of-typo-read-special-weak
    (<= (acl2-count (mv-nth 1 (typo-read-special substrings x)))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-typo-read-special-strong
    (implies (mv-nth 0 (typo-read-special substrings x))
             (< (acl2-count (mv-nth 1 (typo-read-special substrings x)))
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear))))



(defsection typo-read-lowercase-part

  (defund typo-read-lowercase-part (x)
    ;; Read as many lowercase characters as possible, but stop early if a
    ;; special is encountered.
    "Returns (MV PREFIX REMAINDER)"
    (declare (xargs :guard (character-listp x)))
    (if (atom x)
        (mv nil x)
      (b* (((mv prefix ?remainder)
            (typo-read-special *typo-special-substrings-chars* x)))
          (cond
           (prefix ;; Stop early because a special is coming next.
            (mv nil x))
           ((vl-typo-lowercase-p (car x))
            (mv-let (prefix remainder)
                    (typo-read-lowercase-part (cdr x))
                    (mv (cons (car x) prefix)
                        remainder)))
           (t
            (mv nil x))))))

  (local (in-theory (enable typo-read-lowercase-part)))

  (defthm true-listp-of-typo-read-lowercase-part
    (true-listp (mv-nth 0 (typo-read-lowercase-part x)))
    :rule-classes :type-prescription)

  (defthm typo-read-lowercase-car-under-iff
    (implies (not (mv-nth 0 (typo-read-special *typo-special-substrings-chars* x)))
             (iff (mv-nth 0 (typo-read-lowercase-part x))
                  (vl-typo-lowercase-p (car x)))))

  (defthm typo-read-lowercase-part-basics
    (implies (character-listp x)
             (and (character-listp (mv-nth 0 (typo-read-lowercase-part x)))
                  (character-listp (mv-nth 1 (typo-read-lowercase-part x))))))

  (defthm acl2-count-of-typo-read-lowercase-weak
    (<= (acl2-count (mv-nth 1 (typo-read-lowercase-part x)))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear)))

  (defthm acl2-count-of-typo-read-lowercase-strong
    (implies (mv-nth 0 (typo-read-lowercase-part x))
             (< (acl2-count (mv-nth 1 (typo-read-lowercase-part x)))
                (acl2-count x)))
    :rule-classes ((:rewrite) (:linear))))


(defsection typo-read-uppercase-part

  (defund typo-read-uppercase-part (x)
    ;; Read as many uppercase characters as we can.
    "Returns (MV PREFIX REMAINDER)"
    (declare (xargs :guard (character-listp x)))
    (cond ((atom x)
           (mv nil x))
          ((vl-typo-uppercase-p (car x))
           (mv-let (prefix remainder)
                   (typo-read-uppercase-part (cdr x))
                   (mv (cons (car x) prefix)
                       remainder)))
          (t
           (mv nil x))))

  (local (in-theory (enable typo-read-uppercase-part)))

  (defthm true-listp-of-typo-read-uppercase-part
    (true-listp (mv-nth 0 (typo-read-uppercase-part x)))
    :rule-classes :type-prescription)

  (defthm typo-read-uppercase-part-basics
    (implies (character-listp x)
             (and (character-listp (mv-nth 0 (typo-read-uppercase-part x)))
                  (character-listp (mv-nth 1 (typo-read-uppercase-part x))))))

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



(defsection typo-read-part

  (defund typo-read-part (x)
    ;; Read the first "part" of a wire name.
    "Returns (MV PREFIX REMAINDER)"
    (declare (xargs :guard (character-listp x)))
    (if (atom x)
        (mv nil nil)
      (b* (((mv prefix remainder)
            (typo-read-special *typo-special-substrings-chars* x)))
          (cond
           (prefix
            ;; Found a special.  Make it its own part.
            (mv prefix remainder))
           ((vl-typo-lowercase-p (car x))
            ;; Part starts with lowercase.  Read as much in lowercase
            ;; as we possibly can.
            (typo-read-lowercase-part x))
           ((not (vl-typo-uppercase-p (car x)))
            ;; Just completely skip any punctuation stuff.
            (typo-read-part (cdr x)))
           (t
            (cond ((atom (cdr x))
                   ;; One uppercase character all by itself gets its own part.
                   (mv (list (car x)) (cdr x)))
                  ((vl-typo-lowercase-p (second x))
                   ;; One uppercase character followed by one lowercase.  Read
                   ;; as much lowercase as we can from the cdr, and turn it
                   ;; into a part.
                   (mv-let (prefix remainder)
                           (typo-read-lowercase-part (cdr x))
                           (mv (cons (car x) prefix) remainder)))
                  ((vl-typo-uppercase-p (second x))
                   ;; At least two uppercase characters.  Read as much uppercase
                   ;; as we can.
                   (mv-let (prefix remainder)
                           (typo-read-uppercase-part x)
                           (cond ((atom remainder)
                                  ;; Nothing follows, so it's just one part.
                                  (mv prefix remainder))
                                 ((not (vl-typo-lowercase-p (car remainder)))
                                  ;; Either some underscore or other punctuation
                                  ;; character follows.  Just take this.
                                  (mv prefix remainder))
                                 (t
                                  ;; Finally, it's at least two uppercase chars
                                  ;; followed by a lowercase char.  Remove the
                                  ;; last char we read and leave it with the
                                  ;; remainder.
                                  (mv (butlast prefix 1)
                                      (append (last prefix) remainder))))))
                  (t
                   ;; Some single uppercase character followed by punctuation
                   ;; or something, just return the one char.
                   (mv (list (car x)) (cdr x)))))))))

  (local (in-theory (enable typo-read-part)))

  (defthm true-listp-of-typo-read-part
    (true-listp (mv-nth 0 (typo-read-part x)))
    :rule-classes :type-prescription)

  (defthm typo-read-part-basics
    (implies (character-listp x)
             (and (character-listp (mv-nth 0 (typo-read-part x)))
                  (character-listp (mv-nth 1 (typo-read-part x))))))

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



(defsection typo-partition

  (defund typo-partition (x)
    ;; Fully partition a wire name.
    "Returns a character-list-listp"
    (declare (xargs :guard (character-listp x)))
    (if (atom x)
        nil
      (mv-let (prefix remainder)
              (typo-read-part x)
              (if (not prefix)
                  nil
                (cons prefix (typo-partition remainder))))))

  (local (in-theory (enable typo-partition)))

  (defthm true-listp-of-typo-partition
    (true-listp (typo-partition x))
    :rule-classes :type-prescription)

  (defthm character-list-listp-of-typo-partition
    (implies (force (character-listp x))
             (character-list-listp (typo-partition x)))))


;; Some simple test cases.

;; (typo-partition (coerce "mmSnoopDataValid_CX_P" 'list))
;; (typo-partition (coerce "mmSnopDataValid_CX_P" 'list))
;; (typo-partition (coerce "STPCLKB" 'list))
;; (typo-partition (coerce "rrT0McTm1PdgClr_P" 'list))
;; (typo-partition (coerce "orvHi" 'list))
;; (typo-partition (coerce "x1I3_ReadGflags_X" 'list))
;; (typo-partition (coerce "rnRomEnSel_A" 'list))
;; (typo-partition (coerce "matchb39_6b" 'list))
;; (typo-partition (coerce "bcDWCBAEnt_C0_P" 'list))


(defsection typo-partitioning-alist

  (defund typo-partitioning-alist (x)
    ;; Build an alist mapping strings to their partitionings.
    (declare (xargs :guard (string-listp x)))
    (if (atom x)
        nil
      (cons (cons (car x)
                  (typo-partition (coerce (car x) 'list)))
            (typo-partitioning-alist (cdr x)))))

  (local (in-theory (enable typo-partitioning-alist)))

  (defthm alistp-of-typo-partitioning-alist
    (alistp (typo-partitioning-alist x)))

  (defthm vl-string-keys-p-of-typo-partitioning-alist
    (implies (force (string-listp x))
             (vl-string-keys-p (typo-partitioning-alist x))))

  (defthm vl-character-list-values-p-of-typo-partitioning-alist
    (vl-character-list-list-values-p (typo-partitioning-alist x))))



(defund vl-typo-count-mismatches (x y)
  ;; Given two same-length partitionings, determine how many of their pieces are mismatched.
  (declare (xargs :guard (same-lengthp x y)))
  (cond ((atom x)
         0)
        ((equal (car x) (car y))
         (vl-typo-count-mismatches (cdr x) (cdr y)))
        (t
         (+ 1 (vl-typo-count-mismatches (cdr x) (cdr y))))))



(defsection vl-typo-first-mismatch

  (defund vl-typo-first-mismatch (x y)
    ;; Given two same-length partitionings, return their first mismatch as a pair.
    (declare (xargs :guard (same-lengthp x y)))
    (cond ((atom x)
           nil)
          ((equal (car x) (car y))
           (vl-typo-first-mismatch (cdr x) (cdr y)))
          (t
           (cons (car x) (car y)))))

  (local (in-theory (enable vl-typo-first-mismatch)))

  (defthm character-list-p-of-vl-typo-first-mismatch-1
    (implies (and (character-list-listp x)
                  (character-list-listp y))
             (character-listp (car (vl-typo-first-mismatch x y)))))

  (defthm character-list-p-of-vl-typo-first-mismatch-2
    (implies (and (character-list-listp x)
                  (character-list-listp y))
             (character-listp (cdr (vl-typo-first-mismatch x y))))))



(defsection typo-numbers

  (defconst *typo-numbers*
    '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9))

  (defund typo-numbers ()
    (declare (xargs :guard t))
    *typo-numbers*)

  (in-theory (disable (:executable-counterpart typo-numbers)))

  (defthm setp-of-typo-numbers
    (setp (typo-numbers))
    :hints(("Goal" :in-theory (enable typo-numbers)))))



(defund typo-mismatch-plausibly-typo-p (x y)
  ;; X and Y are single pieces that are mismatched.  Do they satisfy
  ;; our criteria for being considered "possibly a typo"?
  (declare (xargs :guard (and (character-listp x)
                              (character-listp y))))
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
                    (vl-typo-number-p ylast))))))
  )

(defund typo-partitions-plausibly-typo-p (x y)
  ;; X and Y are whole-partitionings.  Do they satisfy our criteria
  ;; for being considered "possibly a typo"?
  (declare (xargs :guard (and (character-list-listp x)
                              (character-list-listp y))))

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

(defsection typo-find-plausible-typos1

  (defund typo-find-plausible-typos1 (part alist)
    ;; Part is the partitioning of a single wire.  Alist is a partitioning
    ;; alist for a list of wires.  Walk down the partitioning alist and
    ;; gather the names of all signals that Part might be a typo for.
    (declare (xargs :guard (and (character-list-listp part)
                                (alistp alist)
                                (vl-string-keys-p alist)
                                (vl-character-list-list-values-p alist))))
    (cond ((atom alist)
           nil)
          ((typo-partitions-plausibly-typo-p part (cdar alist))
           (cons (caar alist)
                 (typo-find-plausible-typos1 part (cdr alist))))
          (t
           (typo-find-plausible-typos1 part (cdr alist)))))

  (local (in-theory (enable typo-find-plausible-typos1)))

  (defthm string-listp-of-typo-find-plausible-typos1
    (implies (force (vl-string-keys-p alist))
             (string-listp (typo-find-plausible-typos1 part alist)))))



(defsection typo-detect-aux

  (defund typo-detect-aux (strs alist)
    ;; Strs is a list of strings, generally the "implicit wires" for a module;
    ;; Alist is a partitioning alist, generally constructed from the "explicit
    ;; wires."
    ;;
    ;; We build an alist that might associate some of the wires in strs to the
    ;; lists of wires we think they could be typos of.
    (declare (xargs :guard (and (string-listp strs)
                                (alistp alist)
                                (vl-string-keys-p alist)
                                (vl-character-list-list-values-p alist))))
    (if (atom strs)
        nil
      (let* ((name1      (car strs))
             (partition1 (typo-partition (coerce name1 'list)))
             (typos1     (typo-find-plausible-typos1 partition1 alist)))
        (if typos1
            (cons (cons name1 typos1)
                  (typo-detect-aux (cdr strs) alist))
          (typo-detect-aux (cdr strs) alist)))))

  (local (in-theory (enable typo-detect-aux)))

  (defthm alistp-of-typo-detect-aux
    (alistp (typo-detect-aux strs alist)))

  (defthm vl-string-keys-p-of-typo-detect-aux
    (implies (force (string-listp strs))
             (vl-string-keys-p (typo-detect-aux strs alist))))

  (defthm vl-string-list-values-p-of-typo-detect-aux
    (implies (force (vl-string-keys-p alist))
             (vl-string-list-values-p (typo-detect-aux strs alist)))))


(defsection typo-detect

  (defund typo-detect (bad good)
    ;; Bad is a string list that names any wires we think are somehow bad.  It
    ;; could be, e.g., all of the implicit wires in a module, or all of the
    ;; implicit wires that are only partly used, etc.  Good is a string list that
    ;; names all the wires we think are somehow good; e.g., declared, used, etc.
    ;; We build an alist associating some wires from Bad with the wires in Good
    ;; that they may be typos of.
    (declare (xargs :guard (and (string-listp bad)
                                (string-listp good))))

    ;; Note: consider removing any good wires from bad, and any bad wires from
    ;; good.  E.g.,
    ;(let* ((bad*  (mergesort bad))
    ;       (good* (mergesort good))
    ;       (bad   (difference bad* good*))
    ;       (good  (difference good* bad*)))
      (typo-detect-aux bad (typo-partitioning-alist good)))

  (local (in-theory (enable typo-detect)))

  (defthm alistp-of-typo-detect
    (alistp (typo-detect bad good)))

  (defthm vl-string-keys-p-of-typo-detect
    (implies (force (string-listp bad))
             (vl-string-keys-p (typo-detect bad good))))

  (defthm vl-string-list-values-p-of-typo-detect
    (implies (force (string-listp good))
             (vl-string-list-values-p (typo-detect bad good)))))


