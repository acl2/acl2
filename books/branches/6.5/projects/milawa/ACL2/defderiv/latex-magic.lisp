; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "../utilities/top")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; LaTeX doesn't do a good job of automatically splitting formulas across
;; lines.  Probably they think everyone is typesetting their own formulas by
;; hand and so there isn't much need.  But we want to typeset formulas that
;; occur in patterns, which may need to span multiple lines.  So, we want to be
;; able to automatically split up our formulas across lines.
;;
;; To do this in an acceptable way, we need to be able to tell how wide parts
;; of a formula will be.  This is tricky since there are variable-width fonts,
;; special symbols, and subscripts involved.
;;
;; Apparently the LaTeX fonts come with tfm files that have this sort of
;; information in them, but I don't know much about the LaTeX internals and I
;; didn't find much information about how to extract this sort of data.  So,
;; I am eyeballing it.
;;
;; I used xdvi and zoomed in as far as it would go, then measured ten
;; characters wide in the various fonts with kruler to come up with the below
;; estimates.  I also measured a 1-inch horizontal line, and it was 600 pixels.
;; Ten such lines would be 6000 pixels, so each width unit in these tables is
;; about 1/6000 of an inch.  I call these units "twips" even though that term
;; means something else in typography.
;;
;; There's certainly some error, but hopefully because of the zooming it won't
;; be off by much.  And, it only needs to be close.

(defconst *dd.twips-per-inch*  6000)

(defun dd.inches-to-twips (x)
  (declare (xargs :mode :program :guard (ACL2::rationalp x)))
  (ACL2::round (ACL2::* x *dd.twips-per-inch*) 1))

(defun dd.twips-to-inches (x)
  ;; We approximate to 1/100 of an inch and return the string "?.??in"
  (declare (xargs :mode :program :guard (natp x)))
  (let* ((hundreths (ACL2::floor x 60))
         (units     (ACL2::floor hundreths 100))
         (remainder (- hundreths (ACL2::* 100 units))))
    (ACL2::concatenate 'ACL2::string
                       (ACL2::coerce (ACL2::explode-atom units 10) 'ACL2::string)
                       "."
                       (ACL2::coerce (ACL2::explode-atom remainder 10) 'ACL2::string)
                       "in")))

(defconst *dd.tt-width*    510)  ;; any \texttt{...} character
(defconst *dd.quad-width*  960)  ;; a \quad
(defconst *dd.qquad-width* 1920) ;; a \qquad
(defconst *dd.vee-width*   1130) ;; a \vee and its surrounding space
(defconst *dd.equal-width* 1340) ;; an = and its surrounding space
(defconst *dd.neq-width*   1340) ;; an \neq and its surrounding space
(defconst *dd.neg-width*   655)  ;; a \neg and its surrounding space
(defconst *dd.paren-width* 370)  ;; a ( or ) in regular font

;; These approximate the widths of regular LaTeX characters
(defconst *dd.normal-widths*
  '((#\a . 490) (#\b . 540) (#\c . 430) (#\d . 540) (#\e . 430)
    (#\f . 290) (#\g . 490) (#\h . 540) (#\i . 270) (#\j . 290)
    (#\k . 510) (#\l . 270) (#\m . 810) (#\n . 540) (#\o . 510)
    (#\p . 540) (#\q . 515) (#\r . 375) (#\s . 380) (#\t . 375)
    (#\u . 540) (#\v . 515) (#\w . 705) (#\x . 515) (#\y . 515)
    (#\z . 430)
    (#\A . 730) (#\B . 685) (#\C . 700) (#\D . 740) (#\E . 660)
    (#\F . 635) (#\G . 760) (#\H . 730) (#\I . 375) (#\J . 500)
    (#\K . 755) (#\L . 605) (#\M . 890) (#\N . 730) (#\O . 755)
    (#\P . 660) (#\Q . 755) (#\R . 720) (#\S . 535) (#\T . 705)
    (#\U . 730) (#\V . 730) (#\W . 1005) (#\X . 725) (#\Y . 730)
    (#\Z . 890)
    (#\1 . 490) (#\2 . 500) (#\3 . 500) (#\4 . 490) (#\5 . 500)
    (#\6 . 500) (#\7 . 505) (#\8 . 495) (#\9 . 495) (#\0 . 495)
    (#\Space . 325) (#\* . 480) (#\. . 270) (#\, . 270)
    ))

;; These approximate the widths of \mathit{...} characters
(defconst *dd.mathit-normal-widths*
  '((#\a . 500) (#\b . 440) (#\c . 400) (#\d . 500) (#\e . 400)
    (#\f . 320) (#\g . 450) (#\h . 500) (#\i . 300) (#\j . 310)
    (#\k . 450) (#\l . 300) (#\m . 800) (#\n . 550) (#\o . 450)
    (#\p . 500) (#\q . 450) (#\r . 410) (#\s . 400) (#\t . 330)
    (#\u . 530) (#\v . 450) (#\w . 650) (#\x . 450) (#\y . 470)
    (#\z . 400)
    (#\A . 710) (#\B . 690) (#\C . 700) (#\D . 730) (#\E . 660)
    (#\F . 640) (#\G . 755) (#\H . 730) (#\I . 380) (#\J . 520)
    (#\K . 755) (#\L . 610) (#\M . 880) (#\N . 730) (#\O . 740)
    (#\P . 660) (#\Q . 740) (#\R . 705) (#\S . 550) (#\T . 700)
    (#\U . 730) (#\V . 730) (#\W . 980) (#\X . 730) (#\Y . 735)
    (#\Z . 600)
    (#\1 . 490) (#\2 . 500) (#\3 . 500) (#\4 . 490) (#\5 . 500)
    (#\6 . 500) (#\7 . 505) (#\8 . 495) (#\9 . 495) (#\0 . 495)
    (#\( . 370) (#\) . 370)))

;; These approximate the widths of subscript characters within
;; a \mathit{...}
(defconst *dd.mathit-subscript-widths*
  '((#\a . 360) (#\b . 320) (#\c . 290) (#\d . 360) (#\e . 295)
    (#\f . 230) (#\g . 330) (#\h . 360) (#\i . 215) (#\j . 220)
    (#\k . 330) (#\l . 215) (#\m . 580) (#\n . 400) (#\o . 325)
    (#\p . 360) (#\q . 325) (#\r . 300) (#\s . 285) (#\t . 235)
    (#\u . 380) (#\v . 325) (#\w . 465) (#\x . 330) (#\y . 340)
    (#\z . 290)
    (#\A . 520) (#\B . 500) (#\C . 510) (#\D . 535) (#\E . 480)
    (#\F . 460) (#\G . 545) (#\H . 535) (#\I . 280) (#\J . 375)
    (#\K . 550) (#\L . 450) (#\M . 640) (#\N . 530) (#\O . 540)
    (#\P . 480) (#\Q . 540) (#\R . 520) (#\S . 400) (#\T . 510)
    (#\U . 530) (#\V . 535) (#\W . 715) (#\X . 530) (#\Y . 535)
    (#\Z . 440)
    (#\1 . 355) (#\2 . 360) (#\3 . 360) (#\4 . 355) (#\5 . 360)
    (#\6 . 360) (#\7 . 367) (#\8 . 360) (#\9 . 360) (#\0 . 360)
    (#\( . 270) (#\) . 270)))

(defun dd.tt-twips (len)
  (declare (xargs :mode :program))
  (ACL2::* len *dd.tt-width*))

(defun dd.normal-twips (char)
  (declare (xargs :mode :program))
  (let ((lookup (lookup char *dd.normal-widths*)))
    (if lookup
        (cdr lookup)
      (ACL2::er hard 'dd.normal-twips
                "No width known for normal character: ~x0~%" char))))

(defun dd.mathit-twips (char)
  (declare (xargs :mode :program))
  (let ((lookup (lookup char *dd.mathit-normal-widths*)))
    (if lookup
        (cdr lookup)
      (ACL2::er hard 'dd.mathit-twips
                "No width known for mathit character: ~x0~%" char))))

(defun dd.mathit-subscript-twips (char)
  (declare (xargs :mode :program))
  (let ((lookup (lookup char *dd.mathit-subscript-widths*)))
    (if lookup
        (cdr lookup)
      (ACL2::er hard 'dd.mathit-subscript-twips
                "No width known for mathit subscript character: ~x0~%" char))))

