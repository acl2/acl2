; XDOC Constructors -- Tests
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc-constructors")
(include-book "testing")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *newline* (coerce (list #\Newline) 'string))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (xdoc::textp ""))

(assert! (xdoc::textp "for now this is a synonym of STRINGP"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (xdoc::text "a string") "a string")

(assert-equal (xdoc::text "just identity for now") "just identity for now")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (xdoc::app) "")

(assert-equal (xdoc::app "one") "one")

(assert-equal (xdoc::app "one" "two" "three") "onetwothree")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (xdoc::topapp) "")

(assert-equal (xdoc::topapp "one") "one")

(assert-equal (xdoc::topapp "one" "two" "three") "onetwothree")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (xdoc::tag "tag" "some text")
              "<tag>some text</tag>

")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (xdoc::h1 "some text")
              "<h1>some text</h1>

")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (xdoc::h2 "some text")
              "<h2>some text</h2>

")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (xdoc::h3 "some text")
              "<h3>some text</h3>

")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (xdoc::h4 "some text")
              "<h4>some text</h4>

")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (xdoc::h5 "some text")
              "<h5>some text</h5>

")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (xdoc::p "some text")
              "<p>some text</p>

")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (xdoc::p*)
              "<p></p>

")

(assert-equal (xdoc::p*
               (xdoc::p "one")
               (xdoc::p "two")
               (xdoc::p "three"))
              "<p><p>one</p>

<p>two</p>

<p>three</p>

</p>

")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (xdoc::li "some text")
              "<li>some text</li>

")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (xdoc::li*)
              "<li></li>

")

(assert-equal (xdoc::li*
               (xdoc::p "one")
               (xdoc::p "two")
               (xdoc::p "three"))
              "<li><p>one</p>

<p>two</p>

<p>three</p>

</li>

")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (xdoc::ul)
              "<ul></ul>

")

(assert-equal (xdoc::ul
               (xdoc::li "one")
               (xdoc::li "two")
               (xdoc::li "three"))
              "<ul><li>one</li>

<li>two</li>

<li>three</li>

</ul>

")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (xdoc::ol)
              "<ol></ol>

")

(assert-equal (xdoc::ol
               (xdoc::li "one")
               (xdoc::li "two")
               (xdoc::li "three"))
              "<ol><li>one</li>

<li>two</li>

<li>three</li>

</ol>

")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (xdoc::blockquote "some text")
              "<blockquote>some text</blockquote>

")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (xdoc::code)
              "@({
})

")

(assert-equal (xdoc::code "line 1"
                          "line 2"
                          "line 3")
              "@({
line 1
line 2
line 3
})

")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (xdoc::desc
               "name of the thing"
               (xdoc::p "description of the thing")
               (xdoc::p "more description of the thing"))
              "<p>name of the thing</p>

<blockquote><p>description of the thing</p>

<p>more description of the thing</p>

</blockquote>

")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (xdoc::img "ref/to/image") "<img src=\"ref/to/image\"/>")
