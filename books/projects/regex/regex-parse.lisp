; Copyright (C) 2004, Regents of the University of Texas
; Written by Sol Swords
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")
; cert_param: (non-acl2r)

(include-book "regex-parse-bracket")
(include-book "regex-parse-brace")

(set-ignore-ok t)

(defun valid-repeat (reg)
  (declare (xargs :guard (or (not reg)
                             (regex-p reg))))
  (and reg
       (pattern-match reg
         ((r-end) nil)
         ((r-begin) nil)
         (& t))))


;; Each of these macros is for a construct that occurs in both
;; the basic and extended regexp parsers in exactly the same form
;; except for the name of the function in the recursive call.
;; Writing them as macros avoids repeating the code.
;; The variables str, prev1, prev2, opts, prev, and eprev
;; are defined in the calling function:
;; str - the string we're operating on
;; prev1 - the immediately preceding regexp; if the current character
;;         is (or begins) a repetition operator, prev1 is what it
;;         modifies
;; prev2 - the rest of the regexp that comes before prev1
;; prev - prev2 and prev1 (when they both exist) concatenated together;
;;        prev1 alone if prev2 does not exist; nil if prev1 does not exist
;; eprev - prev2 and prev2 (when they both exist) concatenated together;
;;        prev1 alone if prev2 does not exist; empty if prev1 does not exist
;; opts - parsing options

(defmacro parse-* (parsefun)
  `(if (valid-repeat prev1)
       (,parsefun str
                  (1+ idx)
                  (r-repeat prev1 0 -1)
                  prev2
                  brcount
                  opts)
           ;; If * is the first character in a subexpression
           ;; grep puts "any" as the inner regexp
     (if (parse-options-strict-repeat opts)
         (mv "* doesn't follow a repeating regex" idx brcount)
       (,parsefun str
                  (1+ idx)
                  (r-repeat (r-any) 0 -1)
                  prev
                  brcount
                  opts))))



(defmacro parse-? (parsefun)
  ;; repeat 0 or 1 times
  `(if (valid-repeat prev1)
       (,parsefun str (1+ idx)
                  (r-repeat prev1 0 1)
                  prev2
                  brcount
                  opts)
     (if (parse-options-strict-repeat opts)
         (mv "? doesn't follow a regex" idx brcount)
       (,parsefun str (1+ idx) (r-repeat (r-any) 0 1) prev brcount opts))))



(defmacro parse-+ (parsefun)
  ;; repeat one to infinity times
  `(if (valid-repeat prev1)
      (,parsefun str (1+ idx)
                 (r-repeat prev1 1 -1)
                 prev2
                 brcount
                 opts)
     (if (parse-options-strict-repeat opts)
         (mv "+ doesn't follow a regex" idx brcount)
       (,parsefun str (1+ idx) (r-repeat (r-any) 1 -1) prev brcount opts))))


(defmacro parse-text (parsefun)
  `(,parsefun str (1+ idx) (r-exact (char str idx)) prev brcount opts))

(defmacro parse-{ (parsefun)
  ;; Grep's behavior with malformed brace expressions is to treat the
  ;; braces as normal characters; this is our behavior when
  ;; parse-options-strict-brace is off.  When on, we return an error.
  ;; When a brace begins a regexp (following a ^, $, (, or starting the pattern)
  ;; grep treats it as a repeated anychar; this is our behavior when
  ;; parse-options-strict-repeat is off.  When on, if parse-options-strict-brace is off
  ;; we consider the brace to be text; otherwise we return an error.
  `(let* ((valid (valid-repeat prev1))
          (prevr (if valid
                     prev1
                   (r-any))))
     (if (and (not valid)
              (parse-options-strict-brace opts))
         (if (parse-options-strict-repeat opts)
             (mv "Brace expression has no operand" idx brcount)
           (parse-text ,parsefun))
       (mv-let (brace rest) (parse-brace str (1+ idx) prevr opts)
               (if (stringp brace)
                   (if (parse-options-strict-brace opts)
                       (mv brace rest brcount) ;; error
                     (parse-text ,parsefun))
                 ;; The parse was good and either prev1 is valid or
                 ;; parse-options-strict-brace is not set so we use the brace parse.
                 (if (mbt (> rest idx))
                     (,parsefun str rest brace prev2 brcount opts)
                   (mv "impossible error" idx brcount)))))))


(defmacro parse-paren (parsefun)
  ;; Parse the inner expression, (xx check for the matching paren,)
  ;; then combine the resulting
  ;; regexes to form prev1, combine prev1 and 2 to form prev2,
  ;; and continue parsing.
  ;; Insert grouping symbol for use with backrefs.
  `(mv-let (inner rem new-brcount)
           (,parsefun str (1+ idx) nil nil (1+ brcount) opts)
           (if (stringp inner) ;; catch error
               (mv inner rem brcount)
             (if (and (parse-options-strict-paren opts)
                      (or (string-index-end rem str)
                          (not (equal (char str rem) #\) ))))
                 ;; Paren does not match and strict parens are on
                 (mv "Mismatched parens" idx new-brcount)
;;             (if (or (equal (char str rem) #\) ) (not (parse-options-strict-paren opts)))
                 ;; Paren matches or strict parens are not on
               (if (string-index-end rem str)
                   (let ((idx rem))
                     (parse-end))
                 (if (mbt (> (1+ rem) idx))
                     (,parsefun str (1+ rem)
                                (r-group inner (1+ brcount))
                                prev
                                new-brcount
                                opts)
                   (mv "impossible error" idx new-brcount))))

             )))

(defmacro parse-[ (parsefun)
  `(mv-let (brac rest) (parse-bracket str (1+ idx))
           (if (stringp brac)
               (mv brac idx brcount)
             (if (> rest idx)
                 (,parsefun str rest (r-charset brac) prev brcount opts)
               (mv "impossible error: bracket" rest brcount)))))


(defmacro parse-disjunct (parsefun)
  ;; Concat prev1 and prev2, parse the rest, and
  ;; return the disjunction.
  `(mv-let (regex rem brcount)
          (,parsefun str (1+ idx) nil nil brcount opts)
          (if (stringp regex) ;; catch error
              (mv regex rem brcount)
            (mv (r-disjunct eprev regex) rem brcount))))


(defmacro parse-backslash (parsefun elseaction)
  ;; In a context where the previous character in str is a backslash,
  ;; check whether the next character is a digit.  If so insert a
  ;; backref; if not execute elseaction.
  `(let ((idx (1+ idx)))
     (if (string-index-end idx str)
         (mv "Error: unfinished escape" idx brcount)
       (let ((n (get-digit-char (char str idx))))
         (if n
             (,parsefun str (1+ idx) (r-backref n) prev brcount opts)
           ,elseaction)))))


(defmacro parse-$ (parsefun)
         ;; End of string
         ;; If this occurs in the middle of a concatenation it'll just fail;
         ;; we won't check if it occurs in an appropriate place for now.
  `(,parsefun str (1+ idx) (r-end) prev brcount opts))


(defmacro parse-^ (parsefun)
  ;; Beginning of string
  ;; We'll allow it syntactically a lot of places where it'll just cause
  ;; unconditional failure.
  `(,parsefun str (1+ idx) (r-begin) prev brcount opts))

(defmacro parse-. (parsefun)
  ;; Concat prev1 and prev2 and continue parsing with
  ;; prev1 as 'any.
  `(,parsefun str (1+ idx) (r-any) prev brcount opts))

(defmacro parse-end ()
  ;; Concat prev1 and prev2 and return str as-is
  ;; so that the outer parser matches the paren.
  ;; The driver for this function should check the
  ;; second return value in order to catch extra right parens.
  `(mv eprev idx brcount))

(defun ere-parse (str idx prev1 prev2 brcount opts)
  (declare (xargs
            :measure (string-index-measure idx str)
            :guard (and (stringp str)
                        (natp idx)
                        (parse-opts-p opts)
                        (or (not prev1)
                            (regex-p prev1))
                        (or (not prev2)
                            (regex-p prev2))
                        (or (not prev2)
                            prev1)
                        (natp brcount))
            :verify-guards nil
            ))
  ;; Set up correct bindings for the macro calls
  (let* ((prev (if prev2
                   (r-concat prev2 prev1)
                 prev1))
         (eprev (if prev prev (r-empty))))
    (if (string-index-end idx str)
        (parse-end)
      (case (char str idx)
        (#\$
         (parse-$ ere-parse))
        (#\^
         (parse-^ ere-parse))
        (#\*
         (parse-* ere-parse))
        (#\?
         (parse-? ere-parse))
        (#\+
         (parse-+ ere-parse))
        (#\[
         (parse-[ ere-parse))
        (#\{
         (parse-{ ere-parse))
        (#\(
         (parse-paren ere-parse))
        (#\|
         (parse-disjunct ere-parse))
        (#\.
         (parse-. ere-parse))
        (#\)
         (parse-end))
        (#\\
         (parse-backslash
          ere-parse
          (parse-text ere-parse)))
        (otherwise
         (parse-text ere-parse))))))



(defthm ere-parse-integer
  (implies (integerp idx)
           (integerp (mv-nth 1 (ere-parse str idx prev1 prev2 brcount opts))))
  :rule-classes (:rewrite :type-prescription))

(defthm ere-parse-index
  (implies (and (stringp str)
                (indexp idx str))
           (<= (mv-nth 1 (ere-parse str idx prev1 prev2 brcount opts))
               (length str)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (disable length))))

(defthm ere-parse-rest-len
  (implies (integerp idx)
           (<= idx
               (mv-nth 1 (ere-parse str idx prev1 prev2 brcount opts))))
  :rule-classes (:rewrite :linear))

(defthm ere-parse-brcount-increasing
  (<= brcount (mv-nth 2 (ere-parse str idx prev1 prev2 brcount opts)))
  :rule-classes (:rewrite :linear))

(defthm ere-parse-brcount-integer
  (implies (integerp brcount)
           (integerp (mv-nth 2 (ere-parse str idx prev1 prev2 brcount opts))))
  :rule-classes (:rewrite :type-prescription))

(defthm ere-parse-regex
  (implies (and (force (and (stringp str)
                            (natp idx)
                            (parse-opts-p opts)
                            (or (not prev1)
                                (regex-p prev1))
                            (or (not prev2)
                                (regex-p prev2))
                            (or (not prev2)
                                prev1)
                            (integerp brcount)
                            (<= 0 brcount)))
                (case-split (not (stringp
                                  (mv-nth 0 (ere-parse
                                        str idx prev1 prev2 brcount opts))))))
           (regex-p (mv-nth 0 (ere-parse str idx prev1 prev2 brcount opts))))
  :rule-classes
  (:rewrite
   (:forward-chaining
    :trigger-terms ((mv-nth 0 (ere-parse str idx prev1 prev2 brcount opts))))))

(defthm ere-parse-nonnil
  (mv-nth 0 (ere-parse str idx prev1 prev2 brcount opts))
  :hints (("Goal" :in-theory (disable ere-parse-regex))))


(verify-guards ere-parse :otf-flg t)







(defun bre-parse (str idx prev1 prev2 brcount opts)
  (declare (xargs
            :measure (string-index-measure idx str)
            :guard (and (stringp str)
                        (natp idx)
                        (parse-opts-p opts)
                        (or (not prev1)
                            (regex-p prev1))
                        (or (not prev2)
                            (regex-p prev2))
                        (or (not prev2)
                            prev1)
                        (natp brcount))
            :verify-guards nil
            ))

  ;; Set up correct bindings for the macro calls
  (let* ((prev (if prev2
                   (r-concat prev2 prev1)
                 prev1))
         (eprev (if prev prev (r-empty))))
    (if (string-index-end idx str)
        (parse-end)
      (case (char str idx)
        (#\*
         (parse-* bre-parse))
        (#\[
         (parse-[ bre-parse))
        (#\$
         (parse-$ bre-parse))
        (#\^
         (parse-^ bre-parse))
        (#\.
         (parse-. bre-parse))
        (#\\
         (parse-backslash
          bre-parse
          (case (char str idx)
            (#\?
             (parse-? bre-parse))
            (#\+
             (parse-+ bre-parse))
            (#\{
             (parse-{ bre-parse))
            (#\(
             (parse-paren bre-parse))
            (#\|
             (parse-disjunct bre-parse))
            (#\)
             (parse-end))
            (otherwise
             (parse-text bre-parse)))))
      (otherwise
         (parse-text bre-parse))))))




(defthm bre-parse-integer
  (implies (integerp idx)
           (integerp (mv-nth 1 (bre-parse str idx prev1 prev2 brcount opts))))
  :rule-classes (:rewrite :type-prescription))

(defthm bre-parse-index
  (implies (and (stringp str)
                (indexp idx str))
           (<= (mv-nth 1 (bre-parse str idx prev1 prev2 brcount opts))
               (length str)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (disable length))
          ("Subgoal *1/11" :expand (:free (prev1 prev2)
                                    (bre-parse str idx nil prev2 brcount opts)))))

(defthm bre-parse-rest-len
  (implies (integerp idx)
           (<= idx
               (mv-nth 1 (bre-parse str idx prev1 prev2 brcount opts))))
  :rule-classes (:rewrite :linear))

(defthm bre-parse-brcount-increasing
  (<= brcount (mv-nth 2 (bre-parse str idx prev1 prev2 brcount opts)))
  :rule-classes (:rewrite :linear))

(defthm bre-parse-brcount-integer
  (implies (integerp brcount)
           (integerp (mv-nth 2 (bre-parse str idx prev1 prev2 brcount opts))))
  :rule-classes (:rewrite :type-prescription))

(defthm bre-parse-regex
  (implies (and (force (and (stringp str)
                            (natp idx)
                            (parse-opts-p opts)
                            (or (not prev1)
                                (regex-p prev1))
                            (or (not prev2)
                                (regex-p prev2))
                            (or (not prev2)
                                prev1)
                            (integerp brcount)
                            (<= 0 brcount)))
                (case-split (not (stringp
                                  (mv-nth 0 (bre-parse
                                        str idx prev1 prev2 brcount opts))))))
           (regex-p (mv-nth 0 (bre-parse str idx prev1 prev2 brcount opts))))
  :rule-classes
  (:rewrite
   (:forward-chaining
    :trigger-terms ((mv-nth 0 (bre-parse str idx prev1 prev2 brcount opts))))))

(defthm bre-parse-nonnil
  (mv-nth 0 (bre-parse str idx prev1 prev2 brcount opts))
  :hints (("Goal" :in-theory (disable bre-parse-regex))))


(verify-guards bre-parse :otf-flg t)

(defun fixed-string-parse (str idx prev1 prev2 brcount opts)
  (declare (xargs
            :measure (string-index-measure idx str)
            :guard (and (stringp str)
                        (natp idx)
                        (parse-opts-p opts)
                        (or (not prev1)
                            (regex-p prev1))
                        (or (not prev2)
                            (regex-p prev2))
                        (or (not prev2)
                            prev1)
                        (natp brcount))
            :verify-guards nil
            ))
  ;; Set up correct bindings for the macro calls
  (let* ((prev (if prev2
                   (r-concat prev2 prev1)
                 prev1))
         (eprev (if prev prev (r-empty))))
    (if (string-index-end idx str)
        (parse-end)
      (parse-text fixed-string-parse))))

(defthm fixed-string-parse-integer
  (implies (integerp idx)
           (integerp (mv-nth 1 (fixed-string-parse str idx prev1 prev2 brcount opts))))
  :rule-classes (:rewrite :type-prescription))

(defthm fixed-string-parse-index
  (implies (and (stringp str)
                (indexp idx str))
           (<= (mv-nth 1 (fixed-string-parse str idx prev1 prev2 brcount opts))
               (length str)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (disable length))))

(defthm fixed-string-parse-rest-len
  (implies (integerp idx)
           (<= idx
               (mv-nth 1 (fixed-string-parse str idx prev1 prev2 brcount opts))))
  :rule-classes (:rewrite :linear))

(defthm fixed-string-parse-brcount-increasing
  (<= brcount (mv-nth 2 (fixed-string-parse str idx prev1 prev2 brcount opts)))
  :rule-classes (:rewrite :linear))

(defthm fixed-string-parse-brcount-integer
  (implies (integerp brcount)
           (integerp (mv-nth 2 (fixed-string-parse str idx prev1 prev2 brcount opts))))
  :rule-classes (:rewrite :type-prescription))

(defthm fixed-string-parse-regex
  (implies (and (force (and (stringp str)
                            (natp idx)
                            (parse-opts-p opts)
                            (or (not prev1)
                                (regex-p prev1))
                            (or (not prev2)
                                (regex-p prev2))
                            (or (not prev2)
                                prev1)
                            (integerp brcount)
                            (<= 0 brcount)))
                (case-split (not (stringp
                                  (mv-nth 0 (fixed-string-parse
                                        str idx prev1 prev2 brcount opts))))))
           (regex-p (mv-nth 0 (fixed-string-parse str idx prev1 prev2 brcount opts))))
  :rule-classes
  (:rewrite
   (:forward-chaining
    :trigger-terms ((mv-nth 0 (fixed-string-parse str idx prev1 prev2 brcount opts))))))

(defthm fixed-string-parse-nonnil
  (mv-nth 0 (fixed-string-parse str idx prev1 prev2 brcount opts))
  :hints (("Goal" :in-theory (disable fixed-string-parse-regex))))


(verify-guards fixed-string-parse :otf-flg t)

(defun append-concats (left right)
  (declare (xargs :guard (and (regex-p left)
                              (regex-p right))))
  (if (r-concat-p left)
      (r-concat (r-concat-left left)
                (append-concats (r-concat-right left) right))
    (r-concat left right)))

(defun post-parse-optimize (regex)
  ;; Recursively descend, consolidating repeats when possible.
  ;; This gets rid of the worst problems associated with multiple repeats;
  ;; a further solution is to remove duplicats when running repeats.
  ;; Also right-associate concats.
  (declare (xargs :guard (regex-p regex)
                  :verify-guards nil
                  :measure (acl2-count regex)))
  (pattern-match
   regex
   ((r-concat left right)
    (let ((left (post-parse-optimize left))
          (right (post-parse-optimize right)))
      (append-concats left right)))
   ((r-disjunct left right)
     (r-disjunct
      (post-parse-optimize left)
      (post-parse-optimize right)))
   ((r-group reg n)
    (r-group (post-parse-optimize reg) n))
   ((r-repeat reg min max)
     (let ((inner (post-parse-optimize reg)))
       (pattern-match
        inner
        ((r-repeat inreg inmin inmax)
         (<= inmin 1)
         (r-repeat
          inreg
          (* min inmin)
          (if (or (< max 0)  (< inmax 0))
              -1
            (* max inmax))))
        (& (r-repeat inner min max)))))
   (& regex)))


(local (defthm integerp-*
          (implies (and (integerp a)
                        (integerp b))
                   (integerp (* a b)))))

(defthm post-parse-optimize-regex-p
  (implies (force (regex-p regex))
           (regex-p (post-parse-optimize regex)))
  :rule-classes
  (:rewrite
   (:forward-chaining :trigger-terms ((post-parse-optimize regex)))))


(local (defthm integerp-rationalp
          (implies (integerp x)
                   (rationalp x))))

(verify-guards post-parse-optimize)





(defun regex-do-parse (str opts)
  (declare (xargs :guard (and (stringp str)
                              (parse-opts-p opts))))
  (mv-let (regex rest brefs)
          (case (parse-options-type opts)
            (ere
             (ere-parse str 0 nil nil 0 opts))
            (bre
             (bre-parse str 0 nil nil 0 opts))
            (fixed
             (fixed-string-parse str 0 nil nil 0 opts))
            (otherwise (mv "bad opts" nil nil)))
          (declare (ignore brefs))
          (if (and (not (string-index-end rest str))
                   (parse-options-strict-paren opts))
              "EPAREN"
            (if (stringp regex) regex
              (post-parse-optimize regex)))))

(defthm regex-do-parse-type
  (implies (and (force (and (stringp str)
                            (parse-opts-p opts)))
                (case-split (not (stringp (regex-do-parse str opts)))))
           (regex-p (regex-do-parse str opts))))

(in-theory (disable regex-do-parse))

