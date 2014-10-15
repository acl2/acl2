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

;; car-cdr-untranslate.lisp
;;
;; This file just sets up some "untranslate patterns" which trick ACL2 into
;; printing (second x), (third x), (fourth x), etc., instead of (cadr x),
;; (caddr x), and (cadddr x) during proof attempts.  This yields much more
;; readable output, in my opinion.
;;
;; BOZO I thought about submitting this book to the ACL2 distribution as a
;; "misc" book, but even if we do that we won't be able to just include it
;; because we need to use MILAWA::first instead of ACL2::first, etc.

(in-package "MILAWA")

(include-book "misc/untranslate-patterns" :dir :system)

(ACL2::add-untranslate-pattern (car ?x)
                               (first ?x))

(ACL2::add-untranslate-pattern (car (car ?x))
                               (first (first ?x)))

(ACL2::add-untranslate-pattern (car (cdr ?x))
                               (second ?x))

(ACL2::add-untranslate-pattern (car (car (cdr ?x)))
                               (first (second ?x)))

(ACL2::add-untranslate-pattern (car (cdr (car (cdr ?x))))
                               (second (second ?x)))

(ACL2::add-untranslate-pattern (car (cdr (car ?x)))
                               (second (first ?x)))

(ACL2::add-untranslate-pattern (car (cdr (cdr ?x)))
                               (third ?x))

(ACL2::add-untranslate-pattern (car (car (cdr (cdr ?x))))
                               (first (third ?x)))

(ACL2::add-untranslate-pattern (car (cdr (car (cdr (cdr ?x)))))
                               (second (third ?x)))

(ACL2::add-untranslate-pattern (car (cdr (cdr (car (cdr (cdr ?x))))))
                               (second (third ?x)))

(ACL2::add-untranslate-pattern (car (cdr (cdr (car (cdr ?x)))))
                               (third (second ?x)))

(ACL2::add-untranslate-pattern (car (cdr (cdr (car ?x))))
                               (third (first ?x)))

(ACL2::add-untranslate-pattern (car (cdr (cdr (cdr ?x))))
                               (fourth ?x))

(ACL2::add-untranslate-pattern (car (car (cdr (cdr (cdr ?x)))))
                               (first (fourth ?x)))

(ACL2::add-untranslate-pattern (car (cdr (car (cdr (cdr (cdr ?x))))))
                               (second (fourth ?x)))

(ACL2::add-untranslate-pattern (car (cdr (cdr (car (cdr (cdr (cdr ?x)))))))
                               (third (fourth ?x)))

(ACL2::add-untranslate-pattern (car (cdr (cdr (cdr (car (cdr (cdr (cdr ?x))))))))
                               (fourth (fourth ?x)))

(ACL2::add-untranslate-pattern (car (cdr (cdr (cdr (car (cdr (cdr ?x)))))))
                               (fourth (third ?x)))

(ACL2::add-untranslate-pattern (car (cdr (cdr (cdr (car (cdr ?x))))))
                               (fourth (second ?x)))

(ACL2::add-untranslate-pattern (car (cdr (cdr (cdr (car ?x)))))
                               (fourth (first ?x)))

(ACL2::add-untranslate-pattern (first (cdr ?x))
                               (second ?x))

(ACL2::add-untranslate-pattern (first (cdr (cdr ?x)))
                               (third ?x))

(ACL2::add-untranslate-pattern (first (cdr (cdr (cdr ?x))))
                               (fourth ?x))

(ACL2::optimize-untranslate-patterns)