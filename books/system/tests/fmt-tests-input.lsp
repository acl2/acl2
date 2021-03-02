; Copyright (C) 2020, Regents of the University of Texas and ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; At some point this might become a book based on run-script.  But that will
; require some changes, since cw prints to standard output, which isn't going
; into the log file.  For now, you could evaluate the forms in this file as
; follows, for example:

; (ld "fmt-tests-input.lsp" :ld-pre-eval-print t)

; We want "~ " to print a space.  But if we are already passed the
; fmt-soft-right-margin at that point, then that's a fine place to print a
; newline, just as for " ".  We started doing that in 12/2020.  Note that
; unlike a normal space (" "), we do print that space; it goes after the
; newline.  We print subsequent spaces too, of course; so the first "b" should
; be in column 3.
(cw "~f0~   bbb~%"
    (make-list 9 :initial-element 'aaaaaaa))

; Same output as above -- the space before "~ " is dropped before the newline.
(cw "~f0 ~   bbb~%"
    (make-list 9 :initial-element 'aaaaaaa))

; The first "b" is now in column 2, because we break on the first space.
(cw "~f0 ~  bbb~%"
    (make-list 9 :initial-element 'aaaaaaa))

; The first "b" is now in column 0.
(cw "~f0   bbb~%"
    (make-list 9 :initial-element 'aaaaaaa))

; In this version, the break occurs after the "~ " is processed.  So we get a
; space printed after the list, at the end of the line, but no spaces on the
; next line in front of "bbb".
(cw "~f0~   bbb~%"
    (make-list 8 :initial-element 'aaaaaaa))

(set-fmt-hard-right-margin 10 state)

; Period is printed just after right parenthesis in all four of these.  But
; that was not the case for the last one until 12/2020.
(fmx "~x0.~|Yes.~%" '(ab d gh)) ; s-expr/period fits on one line
(fmx "~x0.~|Yes.~%" '(ab de gh)) ; s-expr/period fits on two lines
(fmx "~@0.~|Yes.~%" (msg "~x0" '(ab d gh))) ; s-expr/period fits on one line
(fmx "~@0.~|Yes.~%" (msg "~x0" '(ab de gh))) ; s-expr/period fits on two lines

; These are similar to the four tests just above, but this time we start
; pretty-printing after column 0.
(fmx "a~x0.~|Yes.~%" '(b d gh)) ; s-expr/period fits on one line
(fmx "a~x0.~|Yes.~%" '(b de gh)) ; s-expr/period fits on one line
(fmx "a~x0.~|Yes.~%" '(b de ghi)) ; s-expr/period fits on two lines
(fmx "a~@0.~|Yes.~%" (msg "~x0" '(b d gh))) ; s-expr/period fits on one line
(fmx "a~@0.~|Yes.~%" (msg "~x0" '(b de gh))) ; s-expr/period fits on one line
(fmx "a~@0.~|Yes.~%" (msg "~x0" '(b de ghi))) ; s-expr/period fits on two lines

; Don't lose the spaces.
(fmx "~@0  ab" "hello~|")

; Avoid putting "." in column 0 starting 12/2020.
(fmx "~#0~[~x0~/~x0~]." '(ab de gh)) ; s-expr/period fits on two lines

; Respect space after ~y rather than eliminating it.  Thanks to Alessandro
; Coglio and Eric Smith for this example.
(cw " ~y0 ~y1~%" "one" "two")

; The following shows an anomaly before 12/2020.  The first seemed right; it
; should be fine to print a final right parenthesis in column 9 when the
; fmt-hard-right-margin is 10.  But the second was timid about that, breaking
; into two lines.  Starting in 12/2020 both print on a single line.
(fmx "~x0" '(abc defg)) ; printed on a single line
(fmx "a~x0" '(bc defg)) ; formerly printed on two lines

(set-fmt-soft-right-margin 10 state)

; Before 12/2020, this printed a comma in column 0.  The problem was that the
; ~x0 directive didn't see that the ~@1 directive is empty.  (With "~@1"
; omitted, the problem went away.)  Now we print the comma at the end of the
; line with the "a"s.
(fmx "~x0~@1, more~%"
     'aaaaaaaaaa
     "")

(set-fmt-soft-right-margin *fmt-soft-right-margin-default* state)
(set-fmt-hard-right-margin *fmt-hard-right-margin-default* state)

; Future work: Not only keep the comma on the line with the list, but also
; avoid a space in column 0 after the newline.  (Implementation hint: change pn
; arguments of fmt0 etc. to be either char as before, or else (char . nspaces).
; So char is equivalent to (char . 0).)
(fmx "~@0, this line should start in column 0.~%"
     (msg "For list ~x0"
          (make-list '30)))

