; (ld "fast.lisp" :ld-pre-eval-print t)
; (certify-book "fast")

; A Proof of the Correctness of the Boyer-Moore Fast String Searching Algorithm
; by J Strother Moore and Matt Martinez
; May 2008

; ---------------------------------------------------------------------------
; Summmary

; In this book we define the Boyer-Moore fast string searching algorithm and
; prove it correct.  The original Boyer-Moore algorithm is described in

;  "A Fast String Searching Algorithm," R.S. Boyer and J S. Moore, Communications
;  of the Association for Computing Machinery, 20(10), 1977, pp. 762-772.

; In that version, two arrays were used, called delta1 and delta2.  The skip
; was the maximum of those two arrays.  Here we deal with an improvement of the
; original algorithm in which only one array, called delta, is used and it
; insures a skip that is never shorter than the maximum of delta1 and delta2
; and is often greater than either.  A key fact about the original algorithm is
; that preprocessing can be done in linear time in the length, k, of the
; pattern plus linear time in the alphabet size, a.  We do not worry about
; preprocessing time, but the naive way of setting up our delta has complexity
; a*k^2.

; Roughly speaking the algorithm has three main parts: preprocessing, the loop
; which skips ahead by the contents of an array, and a wrapper which enters the
; loop with the right arguments, including the array set up by the
; preprocessing.  The loop is not, in general, total -- that is, it does not
; terminate for arbitrary values of the array.  Therefore, we cannot define the
; loop with the general array as an argument.  Instead, we define the loop to
; skip ahead by the value computed by a function, delta, of the character just
; read, an index into the pattern, and the pattern.  We prove this loop is
; total and admit it; then we define the wrapper that calls it appropriately.
; The loop is called ``fast-loop'' and the wrapper is called is called ``fast''.

; At no point in the execution of the algorithm is an array used.  But we define
; the preprocessing anyway and we prove that indexing into the 2-dimensional array
; it computes returns the appropriate value of delta.

; To prove correctness we define the naive string searching algorithm, which we
; name ``correct'', and prove that ``fast'' is equivalent to ``correct''.

; These pieces -- the preprocessing to produce an array, a total recursive
; function that implements the algorithm in terms of the individually computed
; values of delta, and the proof of the correctness of the algorithm -- can be
; used to prove that code is correct.  We do that in another book.

; ---------------------------------------------------------------------------
; Preamble

; This book relies on a collection of utility lemmas about firstn, nthcdr, and other
; basic list processing functions.

(in-package "ACL2")
(include-book "utilities")

; ---------------------------------------------------------------------------
; The Obviously Correct String Searching Algorithm

; We start by defining the obviously correct string searching algorithm.  The
; fundamental notion is that of an ``exact match,'' the equality of
; corresponding characters from the two strings at a given alignment.

(defun xmatch (pat j txt i)
  (declare (xargs :measure (nfix (- (length pat) j))))
  (cond ((not (natp j)) nil)
        ((>= j (length pat)) t)
        ((>= i (length txt)) nil)
        ((equal (char pat j)
                (char txt i))
         (xmatch pat (+ 1 j)
                 txt (+ 1 i)))
        (t nil)))

; The correct algorithm just looks for the first xmatch of pat in txt, by
; trying them all starting at 0.

(defun correct-loop (pat txt i)
  (declare (xargs :measure (nfix (- (length txt) i))))
  (cond ((not (natp i)) nil)
        ((>= i (length txt)) nil)
        ((xmatch pat 0 txt i) i)
        (t (correct-loop pat txt (+ 1 i)))))

(defun correct (pat txt)
  (correct-loop pat txt 0))

; One might think the empty pat can always be found at location 0 of txt.
; However, this algorithm always return either a legal index into txt (where
; the first match with pat occurs) or else it returns nil.  Since 0 is not a
; legal index into the empty txt, the algorithm returns nil when both pat and
; txt are empty.

; ---------------------------------------------------------------------------
; The Boyer-Moore Algorithm -- Preprocessing

; We assume the reader is familiar with the Boyer-Moore algorithm.  In this
; section we show the preprocessing.

; We follow the convention that if a variable's name ends in the character "~"
; the variable ranges over lists.  We explain later.  The reader might want to
; pronounce "pat~" as "pat prime".  We cannot use pat' as a variable in ACL2.

; First we define the amount, delta, by which you can skip.  It is defined in
; terms of the first "pseudo match" you find for dt~ in pat~, where dt~ is the
; list of characters discovered in the txt before the algorithm encountered the
; unequal characters that caused it to skip ahead.  "Pmatch" stands for "pseudo
; match" and allows dt~ to "fall off" the left end of pat~ and still match, in
; the sense that (A B C D E) pseudo matches (C D E F G).

; Note that pseudo-xmatch is defined on lists, not strings.  We discuss this
; issue in more detail below.  But every string has a unique list counterpart
; and some functions are more naturally defined with lists.  Mathematically,
; the notion that one string, pat of length n, matches at location i in another
; string txt is really just an equality: the substring of length n starting at
; location i in txt IS pat.  We didn't implement xmatch that way because it
; would require constructing the various substrings as objects, which is
; inefficient.  It is more efficient to just compare corresponding characters.
; But the code we're about to write is used only in the preprocessing.  This is
; only meant to specify what the array contains, not necessarily how it is
; computed.  So here it is more natural to use the "mathematical" notion of
; match.  But if we're doing that -- if we're in the business of constructing
; substrings of strings -- it is easier to deal with lists.

(defun pmatch (dt~ pat~ j)
  (declare (xargs :guard (and (true-listp dt~)
                              (true-listp pat~)
                              (integerp j))))
  (if (< j 0)
      (equal (firstn (len (nthcdr (- j) dt~)) pat~)
             (nthcdr (- j) dt~))
    (equal (firstn (len dt~) (nthcdr j pat~))
           dt~)))
  
; ``X marks the spot.''  The function x computes the right most position (to
; the left of j) at which dt~ occurs in pat~.  For  example, 
;               0 1 2 3 4 5 6 7 8
; (x '(a b c) '(a b c a b c x b c) 6) = 3

; If we have just discovered dt in txt upon reading txt[i], we want to slide
; pat so that the character at x in pat is aligned with the one at i in txt.

(defun x (dt~ pat~ j)
  (declare (xargs :measure (+ 1 (nfix (+ (len dt~) j)))
                  :guard (and (true-listp dt~)
                              (true-listp pat~)
                              (integerp j))))
  (cond ((or (not (integerp j))
             (not (true-listp dt~)))
         0)
        ((pmatch dt~ pat~ j) j)
        (t (x dt~ pat~ (- j 1)))))

; This computes how much to increment i to align the discovered text with the
; pat at x and then shift i further to align with the end of pat in that new
; alignment.

(defun delta (v j pat)
  (declare (xargs :guard (and (characterp v)
                              (natp j)
                              (stringp pat))))
  (let* ((pat~ (coerce pat 'list))
         (dt~ (cons v (nthcdr (+ j 1) pat~))))
    (+ (- (len pat~) 1) (- (x dt~ pat~ (- j 1))))))


; Now we set up an "array", really a list of lists.  There will be 256 rows,
; one for each of the ASCII codes.  Each row will have n entries, where n is
; the length of pat.  At row c and column j we will store (delta c' j pat),
; where c' is the character corresponding to ASCII code c.

; Note: The "j" in the code below runs between 1 and (length pat) and we store in
; column j-1.

(defun setup-delta1-row (c j pat row)
  (if (zp j)
      row
    (setup-delta1-row c
                      (- j 1)
                      pat
                      (cons (delta (code-char c) (- j 1) pat) row))))

(defun setup-delta (c pat ans)
  (if (zp c)
      ans
    (setup-delta (- c 1)
                 pat
                 (cons (setup-delta1-row (- c 1) (length pat) pat nil)
                       ans))))

(defun preprocess (pat)
  (setup-delta 256 pat nil))

(defun index2 (array c j)
  (nth j (nth c array)))

; For example, consider the pattern 

; j =   01234567
; pat = EABCDABC

; Note that the substring ABC occurs in it twice, once starting at j=1 and
; again starting at j=5.  In its first occurrence, it is preceded by E and in
; its second it is preceded by D.

; Here is the 2-dimensional array computed by preprocess.  Most of the rows are
; identical because most of the ASCII characters do not occur in the pattern.

; j =     0  1  2  3  4  5  6  7      ; ASCII code (char)
;                                     ; for row
;      ((15 14 13 12 11 10  9  8)     ;   0
;       (15 14 13 12 11 10  9  8)     ;   1
;       ...                           ; ...
;       (15 14 13 12 11 10  9  8)     ;  63 (?)
;       (15 14 13 12 11 10  9  8)     ;  64 (@)
;       (15 14 13 12 11  6  9  2)     ;  65 (A)
;       (15 14 13 12 11 10  5  1)     ;  66 (B)
;       (15 14 13 12 11 10  9  4)     ;  67 (C)
;       (15 14 13 12 11 10  9  3)     ;  68 (D)
;       (15 14 13 12  7 10  9  7)     ;  69 (E)
;       (15 14 13 12 11 10  9  8)     ;  70 (F)
;       ...                           ; ...
;       (15 14 13 12 11 10  9  8)     ; 255
;       )

; Below we show several examples of the use of the array.  Suppose pat and txt
; are aligned as shown and we are reading the character at txt position i.
; Suppose we read an F (ASCII code 70).  This is suggested in the display
; below.

; j   =      01234567
; pat =      EABCDABC
; txt = xxxxxxxxxxxxFxxxxxxxxxxxxx
; i =               |

; Then we index the array with (index2 array 70 7), since the corresponding
; character in pat is at j=7.  The array's contents is 8, which means we can
; skip ahead by 8 (i.e., increment i by 8) to produce this alignment:


; pat =              EABCDABC
; txt = xxxxxxxxxxxxFxxxxxxxxxxxx
; i =                       |

; Suppose instead we are in this alignment:

; j   =      01234567
; pat =      EABCDABC
; txt = xxxxxxxxxEABCxxxxxxxxxxxxx
; i =            |   

; That is, we have matched the ABC at the end of pat with the corresponding
; characters of txt and now read txt at i and get an E (ASCII 69).  Then 
; (index array 69 4) = 7, so we increment i by 7 and get:

; pat =          EABCDABC
; txt = xxxxxxxxxEABCxxxxxxxxxxxxx
; i =                   |

; This shifts the pattern forward to align the discovered text, "EABC", with
; its right-most occurrence in pat.

; ---------------------------------------------------------------------------
; A Total Recursive Function that Performs the Boyer-Moore Search

; Fast will be defined in terms of fast-loop, which is like boyer-moore-loop
; but (a) checks for all the preconditions we assume and (b) uses delta
; directly instead of an array.  To prove that fast-loop terminates, we need
; some theorems:

(defthm integerp-delta
  (implies (integerp j)
           (integerp (delta v j pat)))
  :rule-classes :type-prescription)

(defthm x-mono
  (implies (and (true-listp dt~)
                (integerp j))
           (<= (x dt~ pat~ j) j))
  :rule-classes :linear)

; This is the key one.  It shows that delta is big enough to make sure the
; pattern monotonically shifts to the right.

(defthm delta-very-positive
  (implies (and (stringp pat)
                (natp j)
                (< j (length pat))
                (not (equal v (char pat j))))
           (<= (- (length pat) j)
               (delta v j pat)))
  :rule-classes :linear)

; (The truth is we do not need integerp-delta and delta-very-positive until we
; get to the penultimate lemma about fast-loop and correct-loop at the string
; level.  If we did, we'd have to disable delta here since it is non-recursive.
; For now, we just leave delta enabled and prove these two results as needed
; from the defun of delta and x-mono.  But when we disable delta to stay at the
; string level, we'll need those two.)

; To prove that a function terminates we show a measure that decreases as the
; function recurs.  Our measure is a lexicographic combination of two natural
; numbers.  The first measures how far the right-hand of the pattern is from
; the right-hand end of the text.  The second is how far down the pattern we've
; matched.  When we shift the pattern, the first number decreases.  When we
; leave the pattern in place and decrement j as we match right-to-left, the
; second number decreases.

(defun measure (pat j txt i)
  (declare (xargs :guard (and (stringp pat)
                              (integerp j)
                              (<= -1 j)
                              (stringp txt)
                              (integerp i)
                              (<= j i))))
  (llist (- (+ (length txt) (length pat)) ; first component
            (+ i (- (length pat) j) -1))
         (+ j 1)))                        ; second component


; ---------------------------------------------------------------------------
; Aside: This is a hack to print some trace output when the algorithm runs.
; Note that it prints only for short pat and txt.  That is because we want the
; printing to fit neatly on a line.  When the strings get "too long" it runs
; anyway, but it doesn't print trace output.

(defun show-config (pat j txt i)
  (declare (xargs :guard (and (stringp pat)
                              (integerp j)
                              (<= -1 j)
                              (stringp txt)
                              (integerp i)
                              (<= j i))))
  (cond
   ((> (+ (length pat)
          (length txt))
       55)
    nil)
   (t
    (cw "~%~
     pat:~t4~s0~t5j=~x1~%~
     txt: ~s2~t5i=~x3~%~
        ~t6|~t5m=~x7~%"

        pat ; 0
        j ; 1
        txt ; 2
        i ; 3
        (+ 5 (- i j))         ; 4 tab position for pat
        61                    ; 5 tab position for j= and i=
        (+ 5 i)               ; 6 tab position for | marker
        (measure pat j txt i) ; 7 measure that is supposed to decrease
        ))))
; ---------------------------------------------------------------------------

; Here is the runnable, terminating, version of the Boyer-Moore loop.  We'll
; prove that in a moment.  First we admit it and prove that it terminates.
; Then we'll prove it is equal to boyer-moore-loop under certain conditions.

(defun fast-loop (pat j txt i)
  (declare (xargs :measure (measure pat j txt i)
                  :well-founded-relation l<
                  :guard (and (stringp pat)
                              (integerp j)
                              (<= -1 j)
                              (< j (length pat))
                              (stringp txt)
                              (integerp i)
                              (<= j i))))
  (prog2$
   (show-config pat j txt i)
   (cond
    ((not (and (stringp pat)
               (integerp j)
               (stringp txt)
               (integerp i)
               (<= -1 j)
               (< j (length pat))
               (<= j i)))
     nil)
    ((< j 0)
     (+ 1 i))
    ((<= (length txt) i)
     nil)
    ((equal (char pat j) (char txt i))
     (fast-loop pat (- j 1) txt (- i 1)))
    (t (fast-loop pat
                  (- (length pat) 1)
                  txt
                  (+ i (delta (char txt i)
                              j
                              pat)))))))

; Here is the Boyer-Moore algorithm, which doesn't actually precompute all
; possible deltas but just computes the ones it needs, every time it needs one.

(defun fast (pat txt)
  (declare (xargs :guard (and (stringp pat)
                              (stringp txt))))
  (if (equal pat "")
      (if (equal txt "")
          nil
        0)
    (fast-loop pat
               (- (length pat) 1)
               txt
               (- (length pat) 1))))

; This function terminates.  All the subroutines in it were proved to
; terminate.

; ---------------------------------------------------------------------------
; Proving That the Preprocessing is Correct

; Now we prove that preprocessing is correct and causes the index2 expression
; used in boyer-moore-loop to produce delta when array is (preprocess pat).

(defthm car-nthcdr-setup-delta1-row
  (implies (natp maxpat)
           (equal (car (nthcdr j (setup-delta1-row c maxpat pat ans)))
                  (if (natp j)
                      (if (< j maxpat)
                          (delta (code-char c) j pat)
                        (nth (- j maxpat) ans))
                    (if (zp maxpat)
                        (car ans)
                      (delta (code-char c) 0 pat))))))

  
(defthm car-nthcdr-setup-delta
  (implies (natp maxchar)
           (equal (car (nthcdr c (setup-delta maxchar pat ans)))
                  (if (natp c)
                      (if (< c maxchar)
                          (setup-delta1-row c (length pat) pat nil)
                        (nth (- c maxchar) ans))
                    (if (zp maxchar)
                        (car ans)
                      (setup-delta1-row 0 (length pat) pat nil))))))

(defthm preprocess-correct
  (implies (and (stringp pat)
                (characterp v)
                (natp j)
                (< j (length pat)))
           (equal (index2 (preprocess pat) (char-code v) j)
                  (delta v j pat))))

(in-theory (disable preprocess index2))

; ---------------------------------------------------------------------------
; Our Basic Proof Strategy

; For any theorem about strings there is a corresponding theorem about
; true-lists of characters.  In fact, because we almost never use the fact that
; there are only a finite number of characters, for any theorem about strings
; there is almost always a corresponding theorem about true-lists.

; Of particular interest is the fact that if you have a string pat then you can
; convert it to a unique true-list of characters with (coerce pat 'list).  Many
; string processing functions are defined in terms of their list processing
; counterparts.  For example, if pat is a string, then (length pat) is (len
; (coerce pat 'list)) and the jth character of pat, i.e., (char pat j), is
; defined to be (nth j (coerce pat 'list)).  So, a theorem about a stringp pat
; that talks about length and char might be proved by proving the corresponding
; theorem about a true-listp pat~ that talks about len and nth.  Instantiating
; the latter, replacing pat~ with (coerce pat 'list), proves the former.

; In this file, the variables pat and txt range over strings and the variables
; pat~ and txt~ range over lists.

; We call len the "list level counterpart" of length.  Similarly, pat~ is the
; "list level counterpart" of pat.

; There are two "great ideas" in our proof strategy.

; The first is that xmatch has a list level counterpart that can be expressed
; entirely with equality and the familiar functions firstn and nthcdr.  Firstn
; returns the first n elements of a list and nthcdr returns all but the first
; n elements of a list.

; Let pat and txt be strings and let pat~ and txt~ be their list level
; counterparts.  Let n be the length of pat (i.e., the len of pat~).  Then the
; list level counterpart of (xmatch pat j txt i) is
;
; (equal (firstn n
;                (nthcdr i txt'))
;        (nthcdr j pat'))

; That is the xmatch holds iff the first n elements of the sublist of txt'
; starting at i is equal to the sublist of pat' starting at j.  This "trades"
; xmatch for an equality between two list expressions in terms of firstn and
; nthcdr.

; Here is the formal statement of this first great strategy.

(defthm xmatch-trade
  (implies (and (stringp pat)
                (stringp txt)
                (natp j)
                (natp i))
           (equal (xmatch pat j txt i)
                  (equal (firstn (len (nthcdr j (coerce pat 'list)))
                                 (nthcdr i (coerce txt 'list)))
                         (nthcdr j (coerce pat 'list))))))

; As long as this lemma is active, xmatch expressions will be traded for firstn
; and nthcdr equalities.  We will disable this lemma when we no longer want
; that to happen.

; The second great idea is that we can prove things about firstn and nthcdr
; by what ACL2 calls "destructor elimination."  See the lemma
; firstn-nthcdr-elim in utilities, which states that

; (implies (and (natp n)
;               (< n (len x)))
;          (equal (append (firstn n x) (nthcdr n x)) x)).

; The strategy is as follows.

;   Suppose you have a list x and some index n into it.  Suppose you
;   you want to prove something about (firstn n x) and/or (nthcdr n x),
;   such as:

;   (implies (and (true-listp x)
;                 (natp n)
;                 (< n (len x)))
;            (p n (firstn n x) (nthcdr n x) x))

;   Then you can prove instead:

;   (implies (and (true-listp a)
;                 (< 0 (len b))
;                 (true-listp b))
;            (p (len a) a b (append a b)))

;   because if you prove the latter, you can instantiate it, replacing a by
;   (firstn n x) and b by (nthcdr n x) and use facts in the utilities book to
;   recover the former.  The key fact is, of course, firstn-nthcdr-elim.

; This strategy "trades" firstn and nthcdr for append!  The utilities book not
; only implements this strategy but contains a lot of theorems to simplify
; firstn, nthcdr, and append expressions.  In the interests of canonicalizing
; everything, utilities also rewrites (nth i x) to (car (nthcdr i x)).


; ---------------------------------------------------------------------------
; The Proof Plan

; We want to prove that fast is correct, i.e.,

; (defthm fast-is-correct
;   (implies (and (stringp pat)
;                 (stringp txt))
;            (equal (fast pat txt)
;                   (correct pat txt))))

; from which it will follow that boyer-moore is correct.  Below we sketch the
; proof.

; The plan has some special markers in it (*** 1 ***), (*** 2 ***), etc.
; These markers help you locate the corresponding steps in the ACL2 proof in
; the next section.

; Proof Plan

; To prove fast-is-correct (*** 1 ***), we need to prove that the two loops are
; equivalent, i.e., that

; (equal (fast-loop pat j txt i)
;        (correct-loop pat txt (- i j)))

; under suitable hypotheses.  The main hypothesis is that pat starting at j+1
; matches txt starting at i+1.  The actual theorem we prove is called
; fast-loop-is-correct-loop below (*** 2 ***).

; The difference expression above reflects the fact that the j and i in the
; fast-loop term point to the right end of the current alignment while the
; index in correct-loop points to the left end.

; To prove this we'll do an induction to unwind fast-loop.  There will be two
; inductive cases, one where we're backing up because the corresponding
; characters were identical and one where we're skipping forward by delta.  We
; discuss the skipping forward case.

; The inductive step in that case will look something like this:

; (implies (and ...
;               (not (equal (char pat j) (char txt i)))    ; [hyp 1]
;               ...
;               (equal (fast-loop pat j' txt i')           ; [hyp 2]
;                      (correct-loop pat txt (- i' j')))
;               ...)
;          (equal (fast-loop pat j txt i)                  ; [concl]
;                 (correct-loop pat txt (- i j))))
          
; where [hyp 1] specifies the case we're in (we've found mismatched chars) and
; [hyp 2] is the inductive hypothesis, where we've assumed the formula for j
; replaced by j' and i replaced by i'.

; The values of j' and i' are just those that are used in the recursive
; call of fast-loop in this case:

; j' = (- (length pat) 1)
; i' = (+ i (delta (char txt i) j pat))

; The conclusion, [concl], equates fast-loop to correct-loop.  But the
; fast-loop call will expand under the [hyp 1] case analysis and become
; (fast-loop pat j' txt i').  Note that this is the term [hyp2] mentions.
; Then we will use the induction hypothesis, [hyp2], and produce a new 
; conclusion of the form:

;          (equal (correct-loop pat txt (- i' j'))
;                 (correct-loop pat txt (- i j)))

; So the proof about fast-loop is EASY if we can prove this lemma about
; correct-loop!  The actual lemma is called crux below (*** 3 ***).  If we
; substitute in the values of j' and i' and do a little arithmetic we see the
; main idea:

; [crux]:
 
; (equal (correct-loop pat txt
;                      (+ 1 i
;                         (- (length pat))
;                         (delta (char txt i) j pat)))
;        (correct-loop pat txt
;                      (- i j)))

; Of course, crux has all sorts of hypotheses, the main two being that (a) pat
; starting at j+1 matches txt starting at i+1 and (b) the characters at pat[j]
; and txt[i] are different.

; Think of the 3rd argument of correct-loop being the index of a proposed
; alignment of pat and txt.  Correct-loop just tests whether there is a match
; there and if not, moves the proposed alignment down by 1.  Crux tells us that
; we can shift down by a larger amount than 1 without missing a match.

; That's the crux of the Boyer-Moore algorithm.

; The main lesson is that we can do the proof of the equivalence of fast-loop
; and correct-loop with one standard induction on fast-loop, if we can prove
; that correct-loop allows the same big skips that fast-loop does.  This will
; take some clever reasoning about matches, mismatched characters, and delta.
; We'd like to do that reasoning at the list level, not the string level.

; So to prove crux (which is about strings) we will jump to its list level
; counterpart, which is called crux~ (*** 4 ***).  But to even state the lemma
; at the list level we need a recursive function on lists that is the
; list-level correspondent of the string-level correct-loop.

; We call that function correct-loop~ (*** 5 ***) and we prove that it is the
; list-level counterpart of correct-loop in (*** 6 ***).  If you look at [crux]
; and think about how to jump into the list world, we'll replace correct-loop
; by correct-loop~, pat by pat~ txt by txt~ and length by len.  But we also
; have to deal with the delta and char expressions, which operate on strings.
; Fortunately, char just becomes nth after we coerce txt to a list and delta
; can be expanded to be expressed in terms of x, which deals with lists
; already.

; So with those transformations we get: 

; [crux~]:

; (equal
;  (correct-loop~ pat~ txt~
;                 (+ i
;                    (- (x
;                        (cons (car (nthcdr i txt~)) (nthcdr j (cdr pat~)))
;                        pat~
;                        (+ -1 j)))))
;  (correct-loop~ pat~ txt~
;                 (+ i (- j))))

; This may look ugly but it's exactly the list-level counterpart of the crux of
; the algorithm.

; So how do you prove that correct-loop~ allows jumps to alignment x?

; The answer is really simple:

; First, correct-loop~ allows jumps by ANY amount -- provided no matches are
; skipped!  To state this we need to invent a list-level predicate that says
; there are no matches between here and there.  That predicate is called clear
; (*** 7 ***) and the basic idea is formalized as clear-implies-skip (*** 8
; ***).

; Second, we have to prove that there are no matches in the region jumped over
; when we shift the pattern to the x alignment.  That is proved in clear-x 
; (*** 9 ***).

; We cannot find a good way ``code'' these lemmas, clear-implies-skip and
; clear-x, that will allow ACL2 to use them automatically as rewrite rules and
; prove crux~.  So we prove crux~ by an explicit hint that instantiates the two
; lemmas.

; "Q.E.D."  -- But this is just the plan!


; ---------------------------------------------------------------------------
; The ACL2 Proof

; Below we carry out the proof plan.  The numbers appear in different order
; because ACL2 proofs are presented bottom up and our proof was more or less
; top down.  We don't provide many comments because the numbering and plan
; pretty much say all there is to say.

(defun correct-loop~ (pat~ txt~ i)                     ; (*** 5 ***)
  (declare (xargs :measure (nfix (- (len txt~) i))))
  (cond ((not (natp i)) nil)
        ((>= i (len txt~)) nil)
        ((equal (firstn (len pat~) (nthcdr i txt~))
                pat~)
         i)
        (t (correct-loop~ pat~ txt~ (+ 1 i)))))

(defthm correct-loop-trade                             ; (*** 6 ***)
  (implies (and (stringp pat)
                (stringp txt))
           (equal (correct-loop pat txt i)
                  (correct-loop~ (coerce pat 'list)
                                 (coerce txt 'list)
                                 i))))

(defun clear (pat~ txt~ k n)                           ; (*** 7 ***)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) t)
        ((equal (firstn (len pat~) (nthcdr k txt~))
                pat~)
         nil)
        (t (clear pat~ txt~ (+ k 1) (- n 1)))))

; Next is one of the two lemmas in our decomposition of crux~.  It is not
; stated as a rewrite rule because in actual fact when the lemma is used k,
; below, becomes (- i j) and the (+ k n) becomes a difference expression.

(defthm clear-implies-skip                             ; (*** 8 ***)
  (implies (and (natp k)
                (< k (len txt~))
                (natp n)
                (clear pat~ txt~ k n))
           (equal (correct-loop~ pat~ txt~ (+ k n))
                  (correct-loop~ pat~ txt~ k)))
  :rule-classes nil)

; The next lemma, clear-x, is the other half of our decomposition.  The trick
; to stating it is how one writes dt, the discovered text.  Technically, it is
; txt[i] consed onto the tail end of pat starting at j+1.  But this (a) hides
; it relation to txt -- dt is in fact just a certain substring of txt starting
; at i -- and (b) is a function of j.  But to prove the theorem below we must
; induct on j.  We cannot tolerate dt being a function of the induction
; variable.  So we have to generalize the theorem and not deal with the actual
; dt but with some arbitrary substring of txt of d characters.  But this
; introduction of d and the separation of dt from pat (now it is just a piece
; of txt) makes this lemma unuseful as a rewrite rule in crux~.

(defthm clear-x                                        ; (*** 9 ***)
  (implies (and (true-listp pat~)
                (true-listp txt~)
                (consp pat~)
                (natp i)
                (natp d)
                (<= (+ i d) (len txt~))
                (integerp j)
                (natp (- i j))
                (natp (+ j d))
                (<= (+ j d) (len pat~)))
           (clear pat~
                  txt~
                  (- i j)
                  (- j (x (firstn d (nthcdr i txt~)) pat~ j))))
  :rule-classes nil)

(defthm crux~                                          ; (*** 4 ***)
  (implies (and (true-listp pat~)
                (true-listp txt~)
                (integerp j)
                (<= -1 j)
                (integerp i)
                (<= -1 i)
                (<= 0 j)
                (< i (len txt~))
                (not (equal (nth j pat~) (nth i txt~)))
                (consp pat~)
                (<= 0 (len pat~))
                (< j (len pat~))
                (<= j i)
                (equal (firstn (len (nthcdr (+ 1 j) pat~))
                               (nthcdr (+ 1 i) txt~))
                       (nthcdr (+ 1 j) pat~)))
           (equal
            (correct-loop~
             pat~ txt~
             (+ i
                (- (x (cons (car (nthcdr i txt~)) (cdr (nthcdr j pat~)))
                      pat~ (+ -1 j)))))
            (correct-loop~ pat~ txt~ (+ i (- j)))))

; Note: Recall the plan: You can skip over any distance if you know there are
; no matches in the region and we know there are no matches in the region
; scanned by x.  We could not find a way to express the two lemmas
; (numbers 8 and 9 above) to make ACL2 just use them automatically.  So we
; literally provide ACL2 with the required instantiations of them below.

  :hints
  (("Goal"
    :use
    ((:instance
      clear-x
      (d (- (len pat~) j)))
    
     (:instance
      clear-implies-skip
      (pat~ pat~)
      (txt~ txt~)
      (k (+ i (- j)))
      (n
       (+ j
          (- (x (cons (nth i txt~) (nthcdr j (cdr pat~)))
                pat~ (+ -1 j))))))))))

(defthm crux                                           ; (*** 3 ***)
  (implies (and (stringp pat)
                (stringp txt)
                (integerp j)
                (<= -1 j)
                (integerp i)
                (<= -1 i)
                (<= 0 j)
                (< i (length txt))
                (not (equal (char pat j)
                            (char txt i)))
                (not (equal pat ""))
                (< j (length pat))
                (<= j i)
                (xmatch pat (+ 1 j) txt (+ 1 i)))
           (equal (correct-loop pat txt
                             (+ 1 i (- (length pat))
                                (delta (char txt i) j pat)))
                  (correct-loop pat txt (+ i (- j))))))


; Note: The plan calls for us to ascend to the string level now and prove that
; fast-loop is correct-loop by a routine fast-loop induction.  The plan left
; out two things that come up in trying to carry out that proof.

; This first lemma, below, says that (xmatch pat j txt i) always succeeds if j
; is (length pat).  Recall that the equivalence of fast-loop and correct-loop
; has the hypothesis that pat starting at j+1 matches txt starting at i+1.  But
; when we slide the pattern down, j becomes (- (length pat) 1).  That is, the
; "pre-matched" part of the pattern becomes empty.  This theorem lets us detach
; the induction hypothesis in that case.

(defthm empty-xmatch
  (implies (and (stringp pat)
                (stringp txt)
                (natp i))
           (xmatch pat (length pat) txt i)))

; The next lemma says that correct-loop fails if the pat overhangs the right
; end of the txt.  The fast loop stops under this condition, but the correct
; loop keeps going until the left end of the pat is past the end of txt.  This
; lemma tells us correct-loop could stop early.

(defthm early-termination
  (implies (and (natp k)
                (stringp pat)
                (stringp txt)
                (<= (length txt) (+ k (- (length pat) 1))))
           (not (correct-loop pat txt k))))

; Now we want to do everything else at the string level.  So we disable the
; rules that are driving us down to the list level.

(in-theory (disable xmatch-trade
                    correct-loop-trade
                    delta
                    length
                    char))

; So now we're at the string level again and we're almost done!  Here we do a routine
; fast-loop induction and appeal to crux:

(defthm fast-loop-is-correct-loop                      ; (*** 2 ***)
  (implies (and (stringp pat)
                (integerp j)
                (stringp txt)
                (integerp i)
                (<= -1 j)
                (< j (length pat))
                (<= j i)
                (not (equal pat ""))
                (xmatch pat (+ j 1) txt (+ i 1)))
           (equal (fast-loop pat j txt i)
                  (correct-loop pat txt (- i j)))))

; And now we're done.

(defthm fast-is-correct                                ; (*** 1 ***)
  (implies (and (stringp pat)
                (stringp txt))
           (equal (fast pat txt)
                  (correct pat txt))))

; Q.E.D.
