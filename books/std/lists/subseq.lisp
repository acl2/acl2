; Lemmas about subseq functions
; Copyright (C) 2013 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(include-book "list-defuns")
(local (include-book "take"))

(defsection subseq-list
  :parents (std/lists subseq)
  :short "Lemmas about @(see subseq-list) available in the @(see std/lists)
library."

  :long "<p>ACL2's built-in @('subseq-list') function is used in the definition
of @('subseq').  It has a somewhat reasonable definition in terms of @(see take)
and @(see nthcdr).</p>

@(def subseq-list)

<p>Unfortunately @('subseq-list') doesn't properly @(see nfix) its @('start')
argument, so in the logic, when @('start') is a negative number, we can end up
doing a longer @('take'), which is kind of appalling and somewhat reduces our
ability to write nice rules about @('subseq-list').</p>

<p>It is often pretty reasonable to just leave @('subseq-list') enabled.</p>"

  (defthm len-of-subseq-list
    (equal (len (subseq-list x start end))
           (nfix (- end start))))

  (defthm consp-of-subseq-list
    (equal (consp (subseq-list x start end))
           (posp (- end start))))

  (defthm subseq-list-under-iff
    (iff (subseq-list x start end)
         (posp (- end start))))

  (defthm subseq-list-of-list-fix
    (equal (subseq-list (list-fix x) start end)
           (subseq-list x start end)))

  (defcong list-equiv equal (subseq-list x start end) 1)

  (defthm subseq-list-starting-from-zero
    ;; BOZO.  It'd be nicer to prove this about (subseq-list x start n) whenever
    ;; (zp start).  Unfortunately SUBSEQ-LIST doesn't properly NFIX its START
    ;; argument.  Instead, in the logic, when START is a negative number, we end
    ;; up doing a longer TAKE, which is sort of appalling.
    (equal (subseq-list x 0 n)
           (take n x))
    :hints(("Goal" :in-theory (enable subseq-list))))

  (defthm subseq-list-of-len
    ;; BOZO.  Similarly this rule needs a natp hyp and we can't just get away
    ;; from it using something like NFIX.  The problem is again that if N is,
    ;; say, a negative number, then we can do a larger take.
    (implies (natp n)
             (equal (subseq-list x n (len x))
                    (nthcdr n (list-fix x))))
    :hints(("Goal" :in-theory (enable take))))

; We could strengthen the above rules by turning them into something like (take
; n (append x (repeat (- start) nil))) in the negative case, but that is
; probably nothing anyone would expect to see or should ever try to reason
; about.

  )
