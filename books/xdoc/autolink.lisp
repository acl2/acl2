; XDOC Documentation System for ACL2
; Copyright (C) 2009-2015 Centaur Technology
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


; autolink.lisp -- automatically insert links into pretty-printed s-expressions

(in-package "XDOC")
(include-book "fmt-to-str")
(include-book "names")
(include-book "std/strings/printtree-concat" :dir :system)
(local (include-book "std/testing/assert-bang" :dir :system))
(set-state-ok t)
(program)


; Convention: X is a string we are traversing, N is our current position in the
; string, and XL is the length of the string.  The imagined guard is:
;
;  (declare (xargs :guard (and (stringp x)
;                              (natp n)
;                              (natp xl)
;                              (= xl (length x))
;                              (<= n xl))))
;
; We could do a lot of this in logic mode, but there doesn't seem to be much
; point to that.

(defun error-context (x n xl) ;; ==> STRING
  ;; Tries to show what text is near an error.
  (declare (type string x))
  (b* ((min (nfix (- n 40)))
       (max (min (+ n 20) xl)))
    (subseq x min max)))

(defun skip-past-ws (x n xl) ;; ==> N-PRIME
  (declare (type string x))
  (cond ((eql xl n)
         n)
        ((member (char x n) '(#\Space #\Tab #\Newline #\Page))
         (skip-past-ws x (+ 1 n) xl))
        (t
         n)))


; What a pain.  We have to implement a symbol parser.

(defun parse-symbol-name-part (x n xl
                                 bar-escape-p        ; have we read an opening bar?
                                 slash-escape-p      ; have we just read a backslash?
                                 some-chars-p        ; have we read any chars at all yet?
                                 nice-error-msg-p    ; do we care about nice error msgs?
                                 acc)
  ;; ==> (MV ERROR NAME N-PRIME)
  (declare (type string x))

; This tries to read just one part of a symbol name (i.e., the package part,
; or the name part.)

  (b* (((when (= xl n))
        ;; End of string?  Error if we were escaped, or if we have not actually
        ;; read some characters yet.  Otherwise, it was okay.
        (b* ((result (str::rchars-to-string acc))
             ((when (or bar-escape-p slash-escape-p (not some-chars-p)))
              (mv (if nice-error-msg-p
                      (str::cat "Near " (error-context x n xl)
                                ": unexpected end of string while reading symbol.  "
                                "Characters read so far: " result)
                    "Symbol Parse Error")
                  result n)))
          (mv nil result n)))

       (n+1  (+ n 1))
       (char (char x n))

       ((when slash-escape-p)
        ;; Slash escape is on, so just add next char verbatim and turn off
        ;; slash escape.
        (parse-symbol-name-part x n+1 xl bar-escape-p nil t nice-error-msg-p (cons char acc)))

       ((when (eql char #\|))
        ;; Bar just toggles bar-escaped-ness.
        (parse-symbol-name-part x n+1 xl (not bar-escape-p) nil t nice-error-msg-p acc))

       ((when (eql char #\\))
        ;; Slash starts a slash-escape.
        (parse-symbol-name-part x n+1 xl bar-escape-p t t nice-error-msg-p acc))

       ((when bar-escape-p)
        ;; Bar-escape is on and not a special char.  Read verbatim through it's
        ;; turned off.
        (parse-symbol-name-part x n+1 xl t nil t nice-error-msg-p (cons char acc)))

       ((when (member char '(#\Space #\( #\) #\Newline #\Tab #\Page #\: #\, #\' #\`)))
        ;; Whitespace, paren, colon, comma, quote, backquote, outside of a bar
        ;; escape; end of symbol.  We can stop as long as we've actually read
        ;; some characters.
        (if some-chars-p
            (mv nil (str::rchars-to-string acc) n)
          (mv (if nice-error-msg-p
                  (str::cat "Near " (error-context x n xl)
                            ": expected to read some part of a symbol, but found "
                            (implode (list char)) ".")
                "Symbol Parse Error")
              "" n)))

       ((when (or (and (char<= #\a char) (char<= char #\z))))
        ;; lowercase letters outside of bar escape get capitalized
        (parse-symbol-name-part x n+1 xl nil nil t nice-error-msg-p
                                (cons (acl2::char-upcase char) acc))))

    ;; Otherwise add the char verbatim
    (parse-symbol-name-part x n+1 xl nil nil t nice-error-msg-p (cons char acc))))

(defun parse-symbol (x n xl
                       base-pkg ; default package to intern into
                       kpa      ; (known-package-alist state)
                       nice-error-msg-p)
  ;; ==> (MV ERROR SYMBOL N-PRIME)
  (declare (type string x))

; This extends parse-symbol-name-part to read both parts.  We support keywords,
; etc.  This is definitely not going to handle everything in Common Lisp, but
; whatever.

  (b* (((when (= xl n))
        (mv (if nice-error-msg-p
                (str::cat "Near " (error-context x n xl)
                          ": end of string while trying to parse a symbol.")
              "Symbol Parse Error")
            nil n))
       (char (char x n))

       ((when (eql char #\:))
        ;; Starts with a colon.  Maybe it's keyword symbol?
        (b* (((mv error name n)
              (parse-symbol-name-part x (+ n 1) xl nil nil nil nice-error-msg-p nil)))
          (if error
              (mv error nil n)
            (mv nil (intern-in-package-of-symbol name :keyword) n))))

       ;; Could start with a package name, or with the symbol name (for symbols
       ;; in the base pkg). Either way, we need to read a symbol name part.
       ((mv error part1 n)
        (parse-symbol-name-part x n xl nil nil nil nice-error-msg-p nil))
       ((when error)
        (mv error nil n))

       ((when (and (< (+ n 1) xl)
                   (eql (char x n) #\:)
                   (eql (char x (+ n 1)) #\:)))
        ;; Found "::" after the first part, so it's a package name.
        (b* (((unless (assoc-equal part1 kpa))
              (mv (if nice-error-msg-p
                      (str::cat "Near " (error-context x n xl)
                                ": not a known package: " part1 ".")
                    "Symbol Parse Error")
                  nil n))
             ((mv error part2 n)
              (parse-symbol-name-part x (+ n 2) xl nil nil nil nice-error-msg-p nil))
             ((when error)
              (mv error nil n))
             ;; Things look pretty good here.  One weird thing we will try to
             ;; detect is if there are extra colons, e.g., foo::bar::baz should
             ;; be disallowed.  We really want a whitespace or paren or quote
             ;; or something
             ((when (and (< n xl)
                         (eql (char x n) #\:)))
              (mv (if nice-error-msg-p
                      (str::cat "Near " (error-context x n xl)
                                ": Three layers of colons in symbol name?")
                    "Symbol Parse Error")
                  nil n)))
          (mv nil (intern$ part2 part1) n)))

       ;; Didn't find a :: after part1.
       ((when (and (< n xl)
                   (eql (char x n) #\:)))
        (mv (if nice-error-msg-p
                (str::cat "Near " (error-context x n xl)
                          ": Lone colon after symbol name?")
              "Symbol Parse Error")
            nil n)))

    ;; We seem to have an okay package name, but no ::, so put it into the base
    ;; package.
    (mv nil (intern-in-package-of-symbol part1 base-pkg) n)))

(encapsulate
  ()
  (logic) ;; since otherwise local stuff gets skipped

  (local
   (defun test (x expect-errmsg expect-result expect-n-prime)
     (declare (xargs :mode :program))
     (b* ((known-pkgs (pairlis$ '("KEYWORD" "ACL2" "XDOC") nil))
          ((mv errmsg result n-prime)
           (parse-symbol x 0 (length x) 'acl2::foo known-pkgs t)))
       (cw "Errmsg: Found ~x0, expected ~x1~%" errmsg expect-errmsg)
       (cw "Result: Found ~x0, expected ~x1~%" result expect-result)
       (cw "N-prime: Found ~x0, expected ~x1~%" n-prime expect-n-prime)
       (and (or (iff errmsg expect-errmsg) (cw "Errmsg failed!~%"))
            (or expect-errmsg
                (equal result expect-result)
                (cw "Result failed!~%"))
            (or expect-errmsg
                (equal n-prime expect-n-prime)
                (cw "N-Prime failed!~%"))))))

  (local
   (progn
     ;; Things that should work
     (assert! (test "foo" nil 'acl2::foo 3))
     (assert! (test "bar" nil 'acl2::bar 3))
     (assert! (test "acl2::bar)" nil 'acl2::bar 9))
     (assert! (test "xdoc::bar)" nil 'xdoc::bar 9))
     (assert! (test "xdoc::|foo|)" nil 'xdoc::|foo| 11))
     (assert! (test "xdoc::bar12 " nil 'xdoc::bar12 11))

     (assert! (test ":foo)" nil :foo 4))
     (assert! (test ":|foo|)" nil :|foo| 6))
     (assert! (test ":||" nil :|| 3))
     (assert! (test "acl2::bar|:|)" nil 'acl2::bar|:| 12))

     ;; Things that should fail
     (assert! (test ":" t nil nil))     ;; lone colon, not ok
     (assert! (test "||:" t nil nil))   ;; ending colon, not ok
     (assert! (test "::|foo|)" t nil nil)) ;; starting colons w/o pkgname, not ok
     (assert! (test "acl2:::bar)" t nil nil)) ;; three colons, not ok
     (assert! (test "acl2::bar:" t nil nil))  ;; extra colon, not ok

     ;; Uh... bug?  feature?
     (assert! (test "123" nil 'acl2::|123| 3)))))




(defun autolink-and-encode (x n xl baseidx topics base-pkg kpa acc) ;; ==> ACC

; Main routine for autolinking and HTML encoding s-expressions.  X typically
; has a pretty-printed S-expression that we want to turn into an XDOC <code>
; segment.  TOPICS is a fast alist whose keys are the known topic names, for
; fast lookups of whether a symbol is a topic.
;
; We walk over the string and look for symbols following open-parens; this
; limitation is meant to reduce the amount of symbol parsing we have to do and
; should be good enough to insert links to function calls.  Whenever we find a
; symbol that is a documented topic, we insert a link to it.  We also HTML
; encode the string in the process.

; The baseidx here points to the character after the last special element.
; When we see normal characters, we don't accumulate anything, but when we
; either reach the end of the string or something special we'll add the entire
; sequence since the baseidx.

  (b* (((when (int= n xl))
        (str::pcat acc (subseq x baseidx n)))
       (char1 (char x n))
       ((when (eql char1 #\<)) ;; --> "&lt;" in reverse
        (autolink-and-encode x (+ 1 n) xl (+ 1 n) topics base-pkg kpa
                             (str::pcat acc (subseq x baseidx n) "&lt;")))
       ((when (eql char1 #\>)) ;; --> "&gt;" in reverse
        (autolink-and-encode x (+ 1 n) xl (+ 1 n) topics base-pkg kpa
                             (str::pcat acc (subseq x baseidx n) "&gt;")))
       ((when (eql char1 #\&)) ;; --> "&amp;" in reverse
        (autolink-and-encode x (+ 1 n) xl (+ 1 n) topics base-pkg kpa
                             (str::pcat acc (subseq x baseidx n) "&amp;")))
       ((when (eql char1 #\")) ;; --> "&quot;" in reverse
        (autolink-and-encode x (+ 1 n) xl (+ 1 n) topics base-pkg kpa
                             (str::pcat acc (subseq x baseidx n) "&quot;")))
       ((unless (eql char1 #\())
        ;; Anything else except an open paren, we aren't going to do anything
        ;; special with.  This way we don't have to call parse-symbol most of
        ;; the time.
        (autolink-and-encode x (+ 1 n) xl baseidx topics base-pkg kpa acc))

       ;; (acc (cons char1 acc))
       ((mv err symbol n-prime) (parse-symbol x (+ 1 n) xl base-pkg kpa nil))

       ((when err)
        ;; Failed to parse a valid symbol after it, so that's fine, maybe we hit
        ;; a quoted thing like '((1 . 2)) or whatever.  Just keep going.
        (autolink-and-encode x (+ 1 n) xl baseidx topics base-pkg kpa acc))

       (look (hons-get symbol topics))
       ((unless look)
        ;; Nope, not a documented topic, so that's fine, just leave the paren
        ;; there and keep on encoding things without inserting a link.
        (autolink-and-encode x (+ 1 n) xl baseidx topics base-pkg kpa acc))

       ;; Finally, the interesting case.  We just found something like
       ;; "(append".  We want to convert this into, e.g.,
       ;; (<see topic='[url-for-append]'>append</see>
       ;; and then keep going with our encoding.
       (acc
        ;; <see topic="
        (str::pcat acc
                   ;; Includes everything from the base index up to and including the open paren.
                   (subseq x baseidx (+ 1 n))
                   "<see topic=\""))
       (acc (file-name-mangle symbol acc))
       (acc
        ;; ">
        (str::pcat acc "\">"))
       ;; Subtle: normally the "xl" argument should be the length of the string
       ;; here, but we only want to encode the part of the name that we read.
       ;; So, use the new N-PRIME returned by the symbol parser for the XL part
       ;; to stop early.
       (acc (simple-html-encode-str x (+ 1 n) n-prime acc))
       (acc
        ;; </see>
        (str::pcat acc "</see>")))
    ;; Finally recur...
    (autolink-and-encode x n-prime xl n-prime topics base-pkg kpa acc)))

(encapsulate
  ()
  (logic)

  (local (defun test (str expect)
           (declare (xargs :mode :program))
           (b* ((topics '(acl2::f g h foo bar baz + - xdoc::top1 xdoc::top2)) ;; just for testing
                (alist  (make-fast-alist (pairlis$ topics nil)))
                (known-pkgs (pairlis$ '("ACL2" "KEYWORD" "XDOC") nil))
                (acc    (autolink-and-encode str 0 (length str) 0 alist 'acl2::foo known-pkgs nil))
                (-      (fast-alist-free alist))
                (result (str::printtree->str acc)))
             (or (equal result expect)
                 (cw "Result: ~x0~%" result)
                 (cw "Expected: ~x0~%" expect)))))

  (local
   (progn

     (assert! (test "foo"
                    ;; -->
                    "foo"))

     (assert! (test "foo & bar"
                    ;; -->
                    "foo &amp; bar"))

     (assert! (test "foo & bar <baz>"
                    ;; -->
                    "foo &amp; bar &lt;baz&gt;"))

     (assert! (test "(foo (+ 1 2))"
                    ;; note that foo doesn't get processed: xdoc::foo is among the topics, but
                    ;; since the base-pkg is acl2, the foo here is acl2::foo.
                    "(foo (<see topic=\"COMMON-LISP_____B2\">+</see> 1 2))"))

     (assert! (test "(xdoc::foo (f 1 2))"
                    ;; -->
                    "(<see topic=\"XDOC____FOO\">xdoc::foo</see> (<see topic=\"ACL2____F\">f</see> 1 2))")))))


(defun xml-ppr-obj-aux
  (x          ; object to pretty-print
   topics-fal ; fast alist binding all xdoc topic names to [irrelevant]
   base-pkg   ; base package to print from
   state
   acc)
  (b* ((kpa (known-package-alist state))
       (str (fmt-to-str x base-pkg))
       (acc (autolink-and-encode str 0 (length str) 0 topics-fal base-pkg kpa acc)))
    acc))

(defun xml-ppr-obj-fn (x topics-fal base-pkg state)
  (str::printtree->str
   (xml-ppr-obj-aux x topics-fal base-pkg state nil)))

(defmacro xml-ppr-obj (x &key
                         (state 'state)
                         (topics-fal 'nil)
                         (base-pkg   ''acl2::foo))
  `(b* ((acc (xml-ppr-obj-aux ,x ,topics-fal ,base-pkg ,state nil))
        (ret (str::printtree->str acc)))
     ret))

(local
 (progn
   (assert! (equal (xml-ppr-obj '(f 1 2)
                                :topics-fal (make-fast-alist '((f . nil))))
                   "(<see topic=\"XDOC____F\">xdoc::f</see> 1 2)"))

   (assert! (equal (xml-ppr-obj '(f 1 2)
                                :topics-fal (make-fast-alist '((f . nil)))
                                :base-pkg 'xdoc::foo)
                   "(<see topic=\"XDOC____F\">f</see> 1 2)"))))
