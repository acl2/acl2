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
; Original authors:  Sol Swords & Jared Davis  ({sswords,jared}@centtech.com)

(in-package "ACL2")

(include-book "regex-parse")
(include-book "regex-exec")
(include-book "std/strings/case-conversion" :dir :system)
(include-book "std/util/define" :dir :system)
(local (include-book "tools/mv-nth" :dir :system))
(local (include-book "std/testing/assert-bang" :dir :system))

(defxdoc regex
  :parents (projects)
  :short "Regular expression library for ACL2"
  :long "<p>This library is modeled after the regular expression parsing
         functionality of GNU grep.  While the code is mostly considered to be
         complete enough for now, we invite those who wish to improve the
         documentation to go ahead and do so.  As of March 2013, this library
         is compliant with 579 of the 646 GNU grep regression suite tests (see
         book projects/regex/regex-tests for those tests).</p>

         <p>To start using the regex library, include book
         <tt>projects/regex/regex-ui</tt>.</p>

         <p>This library supports \"Basic\", \"Extended\", and \"Fixed\"
         regular expressions (see @(see parse-options)).  Although some
         implementations of GNU Grep support \"Perl\" regular expressions, we
         do not yet implement them.  If a user is motivated to provide such an
         extension, they should feel free to do so.</p>

         <p>This library does not currently support features like [[:digit:]] and
         [[:alpha:]].  A workaround for this is specifying the expansion of
         these named classes, respectively, as in [0-9] and [a-zA-Z].</p>

         <p>See <a
         href=\"http://www.gnu.org/software/grep/manual/grep.html#Regular-Expressions\">
         GNU Grep Regular Expressions</a> for more information on these regular
         expressions.</p>")

; Future implementor's note: An appropriate place to add named classes
; (:digit:, :alpha:, etc.) might be in regex-parse-bracket.lisp.

(local (in-theory (enable length-equiv length)))

; Some prepwork for the admission of do-regex-match-precomp and do-regex-match:

(local (defthm l0
         (implies (not (mv-nth 0 (match-regex-fun regex str untrans-str n)))
                  (not (mv-nth 1 (match-regex-fun regex str untrans-str n))))
         :hints(("Goal" :in-theory (enable match-regex-fun)))))

(local (defthm l1
         (implies (and (stringp str)
                       (stringp untrans-str))
                  (equal (stringp (mv-nth 1 (match-regex-fun regex str untrans-str n)))
                         (if (mv-nth 0 (match-regex-fun regex str untrans-str n))
                             t
                           nil)))
         :hints(("Goal" :in-theory (enable match-regex-fun mv-nth)))))

(local (defthm l2
         (implies (and (stringp str)
                       (stringp untrans-str))
                  (or (stringp (mv-nth 1 (match-regex-fun regex str untrans-str n)))
                      (not (mv-nth 1 (match-regex-fun regex str untrans-str n)))))
         :rule-classes :type-prescription))

(local (defthm stringp-of-get-backref-string
         (implies (stringp str)
                  (stringp (get-backref-string br str)))))

(defun string-or-nil-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (or (stringp (car x))
             (not (car x)))
         (string-or-nil-listp (cdr x)))))

(defthmd nth-of-string-or-nil-listp
  (implies (and (string-or-nil-listp x)
                (nth n x))
           (stringp (nth n x))))

(local (defthm string-or-nil-listp-of-resolve-backrefs
         (implies (stringp str)
                  (string-or-nil-listp (resolve-backrefs brlist str)))))

(local (defthm string-or-nil-listp-of-cdr
         (implies (string-or-nil-listp x)
                  (string-or-nil-listp (cdr x)))))

(local (defthm string-or-nil-listp-of-match-regex-at-char-backrefs
         (implies (stringp untrans-str)
                  (string-or-nil-listp (mv-nth 2 (match-regex-at-char regex str untrans-str idx))))
         :hints(("Goal" :in-theory (enable match-regex-at-char)))))

(local (defthm string-or-nil-listp-of-match-regex-fun
         (implies (stringp untrans-str)
                  (string-or-nil-listp
                   (mv-nth 2 (match-regex-fun regex str untrans-str idx))))
         :hints(("Goal" :in-theory (enable match-regex-fun)))))

(local (defthm string-or-nil-listp-of-match-regex
         (implies (stringp untrans-str)
                  (string-or-nil-listp
                   (mv-nth 2 (match-regex regex str untrans-str))))
         :hints(("Goal" :in-theory (enable match-regex-fun)))))

(local (defthm true-listp-of-match-regex-at-char
         (true-listp (mv-nth 2 (match-regex-at-char regex str untrans-str n)))
         :rule-classes :type-prescription
         :hints(("Goal" :in-theory (enable match-regex-at-char)))))

(local (defthm true-listp-of-match-regex-string
         (true-listp (mv-nth 2 (match-regex-fun regex str untrans-str n)))
         :rule-classes :type-prescription
         :hints(("Goal" :in-theory (enable match-regex-fun)))))

(define do-regex-match-precomp
  ((str stringp "String to test")
   (regex regex-p "Regular expression specifying the pattern to find")
   (opts parse-opts-p "Options for test.  <br />

                       BOZO: state and explain the possible options.  Possible
                       options might include
                       <tt>:b</tt>/<tt>:e</tt>/<tt>:f</tt> for
                       basic/extended/fixed, <tt>:i</tt> for case-insensitive,
                       <tt>:full</tt> for something, etc."))
  :short "Test whether a given string matches a given regular expression"
  :long "Intended for use during macroexpansion, as occurs in @(see B*)."
  :parents (regex)
  :returns (mv (whole (or (stringp whole)
                          (not whole))
                      "The portion of <tt>str</tt> that matches the pattern
                       provided by <tt>regex</tt>.  <tt>Nil</tt> if there is
                       not a match."
                      :rule-classes :type-prescription)
               (substrs true-listp
                        "List of substrings that match parenthesized
                         subexpressions of the pattern (when applicable).
                         <tt>Nil</tt> if there is not a match."
                        :rule-classes :type-prescription))
  (b* ((str (mbe :logic (if (stringp str) str "")
                 :exec str))
       (transstr (if (parse-options-case-insensitive opts)
                     (str::downcase-string str)
                   str))
       ((mv ?matchp whole substrs)
        (match-regex regex transstr str)))
    (mv whole substrs))
  ///
  (defthm string-or-nil-listp-of-do-regex-match-precomp-substrs
    (string-or-nil-listp (mv-nth 1 (do-regex-match-precomp str regex opts)))))

(define do-regex-match
  ((str stringp "String to test")
   (pat stringp "String representing the pattern to find")
   (opts parse-opts-p "Options for test.  <br />

                       BOZO: state and explain the possible options.  Possible
                       options might include
                       <tt>:b</tt>/<tt>:e</tt>/<tt>:f</tt> for
                       basic/extended/fixed, <tt>:i</tt> for case-insensitive,
                       <tt>:full</tt> for something, etc."))
  :short "Test whether a given string matches a given regular expression"
  :long "<p>Intended for use in the dynamically compiled case.</p>



<p>As examples:</p>

@({
 (do-regex-match \"cdeAbfdEfDeghIj\"
                 \"cdeabfdefdeghij\"
                (parse-options 'fixed ; type
                                nil  ; not strict-paren
                                nil  ; not strict-brace
                                nil  ; not strict-repeat
                                t    ; case-insensitive
                                ))
})

<p>returns <tt>(mv nil \"cdeAbfdEfDeghIj\" nil)</tt>, </p>

@({
 (do-regex-match \"cdeAbfdEfDeghIj\"
                 \"ab([def]*)\\1([gh])\"
                 (parse-options 'fixed nil nil nil t))
})

<p>returns <tt>(mv nil nil nil)</tt>, and </p>

@({
 (do-regex-match \"cdeAbfdEfDeghIj\"
                 \"ab([def]*)\\1([gh])\"
                 (parse-options 'ere nil nil nil t))
})

<p>returns <tt>(mv nil \"AbfdEfDeg\" (\"fdE\" \"g\"))</tt>.</p>"

  :parents (regex)
  :returns (mv (error-msg (or (stringp error-msg)
                              (not error-msg))
                          "Error message"
                          :rule-classes :type-prescription)
                (whole (or (stringp whole)
                           (not whole))
                       "The portion of <tt>str</tt> that matches the pattern
                        provided by <tt>pat</tt>.  <tt>Nil</tt> if there is not
                        a match."
                       :rule-classes :type-prescription)
                (substrs true-listp
                         "List of substrings that match parenthesized
                          subexpressions of the pattern (when applicable).
                          <tt>Nil</tt> if there is not a match."
                        :rule-classes :type-prescription))
  (b* ((str (mbe :logic (if (stringp str) str "") :exec str))
       (pat (mbe :logic (if (stringp pat) pat "") :exec pat))
       (pat (if (parse-options-case-insensitive opts)
                (str::downcase-string pat)
              pat))
       (regex (regex-do-parse pat opts))
       ((when (stringp regex))
        (mv regex nil nil))
       ((mv whole substrs)
        (do-regex-match-precomp str regex opts)))
    (mv nil whole substrs))
  ///
  (defthm string-or-nil-listp-of-do-regex-match-substrs
    (string-or-nil-listp (mv-nth 2 (do-regex-match str regex opts)))))

;; We also want to know that the substrings are strings or NIL.  Since we're
;; going to lay down Nths bindings, I'll write these in terms of Nth.

(local (defthm c0
         (implies (string-or-null-listp x)
                  (equal (stringp (nth n x))
                         (if (nth n x)
                             t
                           nil)))))

(local (defthm c1
         (implies (string-or-null-listp x)
                  (equal (stringp (car x))
                         (if (car x)
                             t
                           nil)))))

(in-theory (enable do-regex-match do-regex-match-precomp))

;; BOZO: it would be nice to merge the following into the above define calls.

(defthm type-of-nth-of-do-regex-match-precomp-substrings
  ;; Lemma for the precompiled case
  (or (stringp (nth n (mv-nth 1 (do-regex-match-precomp str regex opts))))
      (not (nth n (mv-nth 1 (do-regex-match-precomp str regex opts)))))
  :rule-classes :type-prescription)

(defthm type-of-car-do-regex-match-precomp-substrings
  ;; We prove the CAR lemma also, since if case Nth is enabled then
  ;; (nth 0 substrings) can turn into (car substrings) before our lemma
  ;; about nth matches.
  (or (stringp (car (mv-nth 1 (do-regex-match-precomp str regex opts))))
      (not (car (mv-nth 1 (do-regex-match-precomp str regex opts)))))
  :rule-classes :type-prescription)


(defthm type-of-nth-of-do-regex-match-substrings
  ;; Lemma for the dynamically compiled case
  (or (stringp (nth n (mv-nth 2 (do-regex-match str regex opts))))
      (not (nth n (mv-nth 2 (do-regex-match str regex opts)))))
  :rule-classes :type-prescription)

(defthm type-of-car-of-do-regex-match-substrings
  ;; Lemma for the dynamically compiled case
  (or (stringp (car (mv-nth 2 (do-regex-match str regex opts))))
      (not (car (mv-nth 2 (do-regex-match str regex opts)))))
  :rule-classes :type-prescription)

;; That *should* be enough for guards, as long as you're not trying to prove
;; something about the actual strings you're matching.  But that'd be crazy,
;; right?
(in-theory (disable do-regex-match do-regex-match-precomp))

; examples
(local (assert! (mv-let (error-msg whole substrs)
                  (do-regex-match "cdeAbfdEfDeghIj"
                                  "ab([def]*)\\1([gh])"
                                  (parse-options 'ere ; type
                                                 nil  ; not strict-paren
                                                 nil  ; not strict-brace
                                                 nil  ; not strict-repeat
                                                 t    ; case-insensitive
                                                 ))
                  (and (not error-msg)
                       (equal whole "AbfdEfDeg")
                       (equal substrs '("fdE" "g"))))))

(local (assert! (mv-let (error-msg whole substrs)
                  (do-regex-match "cdeAbfdEfDeghIj"
                                  "ab([def]*)\\1([gh])"
                                  (parse-options 'fixed ; type
                                                 nil  ; not strict-paren
                                                 nil  ; not strict-brace
                                                 nil  ; not strict-repeat
                                                 t    ; case-insensitive
                                                 ))
                  (and (not error-msg)
                       (not whole)
                       (not substrs)))))

(local (assert! (mv-let (error-msg whole substrs)
                  (do-regex-match "cdeAbfdEfDeghIj"
                                  "cdeabfdefdeghij"
                                  (parse-options 'fixed ; type
                                                 nil  ; not strict-paren
                                                 nil  ; not strict-brace
                                                 nil  ; not strict-repeat
                                                 t    ; case-insensitive
                                                 ))
                  (and (not error-msg)
                       (equal whole "cdeAbfdEfDeghIj")
                       (not substrs)))))

(def-b*-binder match
  :parents (b*-binders regex)
  :short "@(see b*) binder for regular expression matching."
  :long "<p>Match a string against a regular expression and optionally bind the
matching portion to a variable and the substring matches to other
variables.</p>

<p>The way to tell if the string matched is to check whether the variable for
the full match is set to a non-nil value (which then must be a string).</p>

<p>Syntax:</p>
@({
 (b* (((match my-regex
              :e                ;; extended regex (default), or :b for basic, :f for fixed string
              :i                ;; denotes case insensitive match
              :full matchvar    ;; (optional) bind matchvar to the substring matching the full regex
              :substrs (a b)    ;; (optional) bind a and b to the substring matches (ordered)
              :error-msg errvar ;; (optional) bind any error message from parsing the regex to errvar
           )
        string-to-match)
       ((unless matchvar)
         ;; did not match
        ...))
     (list matchvar a b))
 })

<p>If my-regex is a literal string, then the regular expression will be parsed
at macroexpansion time, and matching will be done at runtime with @(see
do-regex-match-precomp); otherwise, the parsing and matching are both done at
runtime with @(see do-regex-match).  The @(':error-msg') option only makes
sense in the second case, because the errors only come from regular expression
parsing; if the regular expression is parsed at macroexpansion time, then any
error from that parsing becomes a hard error during macroexpansion.</p>"
  :decls ((declare (xargs :guard (and (consp forms)
                                      (not (cdr forms))
                                      (true-listp args)))))
  :body
  (b* ((string (car forms)) ;; string to match against the pattern
       (pat (car args))
       (options (cdr args))
       (regex-type
        (b* ((bre (member :b args))
             (ere (member :e args))
             (fixed (member :f args))
             ((when (> (+ (if bre 1 0)
                          (if ere 1 0)
                          (if fixed 1 0))
                       1))
              (er hard? 'patbind-match
                  "more than one regex type argument supplied"))
             ((when bre) 'bre)
             ((when fixed) 'fixed))
          'ere))
       (regex-opts (parse-options
                    regex-type nil nil nil (consp (member :i options))))
       (call (if (stringp pat)
                 (b* ((pat (if (parse-options-case-insensitive regex-opts)
                               (str::downcase-string pat)
                             pat))
                      (regex (regex-do-parse pat regex-opts))
                      ((when (stringp regex))
                       (er hard? 'patbind-match
                           "Regex parse error: ~s0~%" regex)))
                   `(do-regex-match-precomp ,string ',regex ',regex-opts))
               `(do-regex-match ,string ,pat ',regex-opts)))
       (full-var (cadr (member :full options)))
       (substr-vars (cadr (member :substrs options)))
       (error-msg (cadr (member :error-msg options))))
    `(b* ((,(if (stringp pat)
               `(mv ,(or full-var '&)
                    ,(if substr-vars
                         `(nths . ,substr-vars)
                       '&))
              `(mv ,(or error-msg '&)
                   ,(or full-var '&)
                   ,(if substr-vars
                         `(nths . ,substr-vars)
                       '&)))
           ,call))
       ,rest-expr)))

;; Examples
(local
 (make-event
  (b* ((res1-ok
        (equal

         (b* (((match "ab([def]*)\\1([gh])" :i
                      :full f
                      :substrs (a b))
               "cdeAbfdEfDeghIj"))
           (list a b f))

         '("fdE" "g" "AbfdEfDeg")))
       (res2-ok
        (equal

         (b* ((pattern "ab([def]*)\\1([gh])")
              (string "cdeAbfdEfDeghIj")
              ((match  pattern :i
                       :full f
                       :substrs (a b)
                       :error-msg e)
               string))
           (list e a b f))

         '(NIL "fdE" "g" "AbfdEfDeg")))

       (res3-ok
        (equal

         ;; using recursive binders
         (b* ((pattern "ab([def]*)\\1([gh])")
              (string "cdeAbfdEfDeghIj")
              ((match  pattern :i
                       :full ?f                ;; ignorable
                       :substrs ((the string a) ;; type
                                 &)             ;; not bound
                       ;; error msg not present
                       )
               string))
           (list a f))

         '("fdE" "AbfdEfDeg"))))


    (if (and res1-ok res2-ok res3-ok)
        '(value-triple :ok)
      (er hard? 'regex-ui
          "One of the tests failed~%")))))



;; some kind of test to make sure guards verify and we know these variables
;; are strings or NIL.

(local (defun f (x)
         (declare (type string x)
; Added by Matt K. for tau change 11/2012 that pays attention to enabled status
; of runes:
                  (xargs :guard-hints
                         (("Goal"
                           :in-theory
                           (enable (:executable-counterpart regex-p)
                                   (:executable-counterpart parse-opts-p))))))
         (b* (((match "([A-Z]+)_([0-9]+)"
                      :full f
                      :substrs (word num)) x))
           (list f word num))))

(local (defthm first-of-f
         (or (stringp (car (f x)))
             (not (car (f x))))
         :rule-classes :type-prescription))

(local (defthm second-of-f
         (or (stringp (second (f x)))
             (not (second (f x))))
         :rule-classes :type-prescription))

(local (defthm third-of-f
         (or (stringp (third (f x)))
             (not (third (f x))))
         :rule-classes :type-prescription))

(local (assert! (equal (f "FOO_37") (list "FOO_37" "FOO" "37"))))
(local (assert! (equal (f "FOO_37_abc") (list "FOO_37" "FOO" "37"))))
(local (assert! (equal (f "abc_FOO_37_abc") (list "FOO_37" "FOO" "37"))))


(define string-keyed-alist-p (x)
  :parents (undocumented)
  :short "Recognizer for alists whose keys are strings.  Used to implement and
          extend @(see regex-get)."
  :guard t
  (cond ((atom x)
         (null x))
        (t
         (and (consp (car x))
              (stringp (caar x))
              (string-keyed-alist-p (cdr x))))))

(local (in-theory (enable string-keyed-alist-p)))

(define regex-get
  ((str stringp "String to lookup")
   (alist string-keyed-alist-p "Alistp where keys are regular expressions in
                                string form and the values are of an
                                unspecified type"))
  :returns (key-value-pair (equal (consp key-value-pair)
                                  (if key-value-pair t nil))
                           "Matching regular expression paired with its value.
                            Nil if no entry is found.  Note that this is an
                            exact match, which is different from the
                            functionality of grep, which returns substrings
                            that match."
                           :hyp :fguard)
  :parents (regex)
  :short "Lookup a string in the regular expression alist."
  :long "<p>Warning: this is likely to be a pretty slow way of doing things --
         but we currently have no experimental evidence that indicates whether
         this performance is unacceptable.  If you're looking for a place to
         suspect of bad performance, this could be a good place to start.</p>

         <p>It is likely that the user will want to use <tt>regex-get</tt> to
         implement a function that returns a value of a specific type.  Here,
         we show a couple events that we needed to provide to prove that our
         wrapper for <tt>regex-get</tt> returns an <tt>acl2-number-listp</tt>.
         We expect that users in similar situations will need comparable
         lemmas.

         Such composability is similar to the approach available and documented
         in the book <tt>defexec/other-apps/records/records</tt>.</p>

         <p>We now begin our approach.  First we setup an alist to serve as our
         regex dictionary:</p>

@({
 (include-book \"std/util/defalist\" :dir :system)

 (std::defalist dictionary-p (x)
   :key (stringp x)
   :val (acl2-number-listp x)
   :true-listp t)
})

        <p>Next we establish two lemmas that help us specify the return type
        for what will be our use of regex-get:</p>

@({
 (include-book \"projects/regex/regex-ui\" :dir :system)

 (defthm dictionary-p-is-string-keyed-alist-p
   (implies (dictionary-p x)
            (string-keyed-alist-p x))
   :hints ((\"Goal\" :in-theory (enable string-keyed-alist-p))))

 (defthm regex-get-of-dictionary-p-returns-terminal-list-p
   (implies (and (stringp x)
                 (dictionary-p dict))
            (acl2-number-listp (cdr (regex-get x dict))))
   :hints ((\"Goal\" :in-theory (enable regex-get))))
})

        <p>Which enables ACL2 to admit our lookup function:</p>

@({
 (include-book \"std/util/define\" :dir :system)

 (define dictionary-lookup ((key stringp)
                            (dictionary dictionary-p))
   :returns (ans (acl2-number-listp ans)
                 \"The list of integers associated with the given key\"
                 :hyp :fguard)
   (let ((val (regex-get key dictionary)))
     (if (consp val)
         (cdr val)
       nil))) ; return value in the atom case is chosen by user
})
"

  (if (atom alist)
      nil ; no answer
    (mv-let (err whole substrs)
      (do-regex-match str
                      (caar alist)
                      (parse-options 'ere
                                     nil nil nil
                                     nil)) ; case sensitive
      (declare (ignore substrs))
      (cond (err (er hard? 'regex-get err))
            ((equal str whole) (car alist))
            (t (regex-get str (cdr alist)))))))

(local
(defconst *regex-alist*
  '(("abcd" . 1)
    ("[ab]*" . 2))))

(local
 (assert!
  (and (equal (cdr (regex-get "abcd" *regex-alist*))
              1)
       (equal (cdr (regex-get "ab" *regex-alist*))
              2)
       (equal (cdr (regex-get "abab" *regex-alist*))
              2))))
