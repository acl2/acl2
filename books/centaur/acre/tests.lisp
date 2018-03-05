; Centaur regular expression library
; Copyright (C) 2014 Centaur Technology
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

(in-package "ACRE")

(include-book "top")

;; bozo, copied from vl/util/defs
(define maybe-string-fix ((x acl2::maybe-stringp))
  :returns (xx acl2::maybe-stringp)
  :hooks nil
  (mbe :logic (and x (lstrfix x))
       :exec x)
  ///
  (defthm maybe-string-fix-when-maybe-stringp
    (implies (acl2::maybe-stringp x)
             (equal (maybe-string-fix x) x)))

  (defthm maybe-string-fix-under-iff
    (iff (maybe-string-fix x) x))

  (fty::deffixtype maybe-string :pred acl2::maybe-stringp :fix maybe-string-fix
    :equiv maybe-string-equiv :define t :forward t)

  (defrefinement maybe-string-equiv str::streqv
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable str::streqv))))))

(fty::defalist backref-matches :val-type maybe-string :true-listp t)

(defprod regex-test
  ((pattern stringp :rule-classes :type-prescription)
   (str     stringp :rule-classes :type-prescription)
   (match   maybe-string :rule-classes :type-prescription)
   (backrefs backref-matches-p))
  :layout :list)

(define test-backrefs ((x backref-matches-p)
                       (match matchresult-p)
                       (test regex-test-p))
  :guard (matchresult-in-bounds match)
  (b* (((when (atom x)) t)
       ((unless (mbt (consp (car x))))
        (test-backrefs (cdr x) match test))
       ((matchresult match))
       ((cons key val) (car x))
       (substr (matchresult->captured-substr key match))
       ((unless val)
        (if substr
            (b* (((regex-test test)))
              (raise "Regex #{\"\"\"~s0\"\"\"} was expected to match string ~
                       #{\"\"\"~s1\"\"\"} without matching capture group ~x2, ~
                       but it matched substring #{\"\"\"~s3\"\"\"}"
                     test.pattern test.str key substr))
          (test-backrefs (cdr x) match test)))
       ((unless substr)
        (b* (((regex-test test)))
          (raise "Regex #{\"\"\"~s0\"\"\"} was expected to match string ~
                  #{\"\"\"~s1\"\"\"} and match capture group ~x2 to substring ~
                  #{\"\"\"~s3\"\"\"}, but there was no match for that capture ~
                  group."
                 test.pattern test.str key val)))
       ((unless (equal val substr))
        (b* (((regex-test test)))
          (raise "Regex #{\"\"\"~s0\"\"\"} was expected to match string ~
                  #{\"\"\"~s1\"\"\"} and match capture group ~x2 to substring ~
                  #{\"\"\"~s3\"\"\"}, but that capture group instead matched ~
                  #{\"\"\"~s4\"\"\"}."
                 test.pattern test.str key val substr))))
    (test-backrefs (cdr x) match test)))

(define test-regex ((x regex-test-p))
  (b* (((regex-test x))
       ((mv err match) (parse-and-match-regex x.pattern x.str))
       ((when err) (raise "Regex ~s0: Parse error: ~s1" x.pattern err))
       ((matchresult match))
       ((unless x.match)
        (if match.matchedp
            (raise "Regex #{\"\"\"~s0\"\"\"} unexpectedly matched string #{\"\"\"~s1\"\"\"}" x.pattern x.str)
          t))
       ((unless match.matchedp)
        (raise "Regex #{\"\"\"~s0\"\"\"} was expected to match string #{\"\"\"~s1\"\"\"} but did not" x.pattern x.str))
       ((unless (equal x.match match.matched-substr))
        (raise "Regex #{\"\"\"~s0\"\"\"} was expected to match string #{\"\"\"~s1\"\"\"} ~
                with full match #{\"\"\"~s2\"\"\"}, but the match was #{\"\"\"~s3\"\"\"}"
               x.pattern x.str x.match match.matched-substr)))
    (test-backrefs x.backrefs match x)))

(deflist regex-testlist :elt-type regex-test :true-listp t)

(define test-regexlist ((x regex-testlist-p))
  (if (atom x)
      t
    (and (test-regex (car x))
         (test-regexlist (cdr x)))))
       

;; Add more tests!
(defconst *regex-tests*
;     pattern                 str           match             backrefs
  '((#{"""ab"""}                     #{"""cabc"""}        #{"""ab"""}              ())
    (#{"""ab"""}                     #{"""cAbc"""}        ()                       ())
    (#{"""a|b"""}                    #{"""cabc"""}        #{"""a"""}               ())
    (#{"""a*b"""}                    #{"""cbc"""}         #{"""b"""}               ())
    (#{"""a*b"""}                    #{"""cabc"""}        #{"""ab"""}              ())
    (#{"""a*b"""}                    #{"""caabc"""}       #{"""aab"""}             ())
    (#{"""a+b"""}                    #{"""cbc"""}         ()                       ())
    (#{"""a+b"""}                    #{"""cabc"""}        #{"""ab"""}              ())
    (#{"""a+b"""}                    #{"""caabc"""}       #{"""aab"""}             ())
    (#{"""(?i:ab)"""}                #{"""cAbc"""}        #{"""Ab"""}              ())
    (#{"""(?i:a(?^i:b))"""}          #{"""cAbc"""}        #{"""Ab"""}              ())
    (#{"""(?i:a(?^i:b))"""}          #{"""cABc"""}        ()                       ())
    (#{"""a(b)c"""}                  #{"""cabcd"""}       #{"""abc"""}             ((1 . #{"""b"""})))
    (#{"""a(?:b)c"""}                #{"""cabcd"""}       #{"""abc"""}             ((1 . nil)))
    (#{"""a(?<foo>b)c"""}            #{"""cabcd"""}       #{"""abc"""}             ((1 . #{"""b"""})
                                                                                    (#{"""foo"""} . #{"""b"""})))
    (#{"""a(b)(?=c)"""}              #{"""cabcd"""}       #{"""ab"""}              ((1 . #{"""b"""})))
    (#{"""a(bc)(?=c)"""}             #{"""cabcd"""}       ()                       ())
    (#{"""a([bc]*)(?=c)"""}          #{"""cabcd"""}       #{"""ab"""}              ((1 . #{"""b"""})))
    (#{"""a([bc]*)(?=d)"""}          #{"""cabcd"""}       #{"""abc"""}             ((1 . #{"""bc"""})))
    (#{"""a(b)(?=c)([cd]*)"""}       #{"""cabcd"""}       #{"""abcd"""}            ((1 . #{"""b"""})
                                                                                    (2 . #{"""cd"""})))
    (#{"""a(b)(?=d)([cd]*)"""}       #{"""cabcd"""}       ()                       ())
    (#{"""a(b)(?!d)([cd]*)"""}       #{"""cabcd"""}       #{"""abcd"""}            ((1 . #{"""b"""})
                                                                                    (2 . #{"""cd"""})))
    (#{"""a(b)(?!c)([cd]*)"""}       #{"""cabcd"""}       ()                       ())
    (#{"""a([bc]*)(?<=b)([cd]*)"""}  #{"""cabcd"""}       #{"""abcd"""}            ((1 . #{"""b"""})
                                                                                    (2 . #{"""cd"""})))
    (#{"""a([bc]*)(?<=c)([cd]*)"""}  #{"""cabcd"""}       #{"""abcd"""}            ((1 . #{"""bc"""})
                                                                                    (2 . #{"""d"""})))
    (#{"""a([bc]*+)(?<=b)([cd]*)"""} #{"""cabcd"""}       ()                       ())
    (#{"""a([bc]*+)(?<=c)([cd]*)"""} #{"""cabcd"""}       #{"""abcd"""}            ((1 . #{"""bc"""})
                                                                                    (2 . #{"""d"""})))
    (#{"""a([bc]*+)(?<!c)([cd]*)"""} #{"""cabcd"""}       ()                       ())
    (#{"""a([bc]*+)(?<!b)([cd]*)"""} #{"""cabcd"""}       #{"""abcd"""}            ((1 . #{"""bc"""})
                                                                                    (2 . #{"""d"""})))
    (#{"""
     a  ([bc]*+)
     (? < ! b) # commentary
     ([c  d]*)
     """}                            #{"""cabcd"""}       #{"""abcd"""}            ((1 . #{"""bc"""})
                                                                                    (2 . #{"""d"""})))
    (#{"""."""}                      #{"""cabdd"""}       #{"""c"""}               ())
    (#{""".b"""}                     #{"""cabdd"""}       #{"""ab"""}              ())
    (#{"""^.b"""}                    #{"""cabdd"""}       ()                       ())
    (#{"""^.a"""}                    #{"""cabdd"""}       #{"""ca"""}              ())
    (#{"""\^.a"""}                   #{"""cabdd"""}       ()                       ())
    (#{"""\^.d"""}                   #{"""c^bdd"""}       #{"""^bd"""}             ())
    (#{"""d.$"""}                    #{"""cdadb"""}       #{"""db"""}              ())
    (#{"""b.$"""}                    #{"""cdadb"""}       ()                       ())
    (#{"""d.\$"""}                   #{"""cdadb"""}       ()                       ())
    (#{"""d.\$"""}                   #{"""cda$b"""}       #{"""da$"""}             ())))

(assert-event (test-regexlist *regex-tests*))


    
    

