; Copyright (C) 2012 Centaur Technology
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
; Original authors:  Sol Swords & Jared Davis  ({sswords,jared}@centtech.com)

(in-package "ACL2")

(include-book "regex-parse")
(include-book "regex-exec")
(include-book "str/case-conversion" :dir :system)
(include-book "cutil/define" :dir :system)
(local (include-book "tools/mv-nth" :dir :system))
(local (include-book "misc/assert" :dir :system))

(defxdoc regex
  :short "Regular expression library for ACL2"
  :long "This library is modeled after the regular expression parsing
         functionality of GNU grep.  While the code is mostly considered to be
         complete enough for now, we invite those who wish to improve the
         documentation to go ahead and do so.  As of March 2013, this library
         is compliant with 579 of the 646 GNU grep regression suite tests (see
         book regex/regex-tests for those tests).

         To start using the regex library, include book
         <tt>regex/regex-ui</tt>.")

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
    (mv whole substrs)))

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
    (mv nil whole substrs)))

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
  (declare (xargs :guard (and (consp forms) (not (cdr forms))
                              (true-listp args))))
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


