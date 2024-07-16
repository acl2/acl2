; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
; Copyright 2024 Intel Corp.
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

(in-package "AIGNET")

(include-book "centaur/fty/bitstruct" :dir :system)


(defsection gatesimp

  (define gatesimp-level-p (x)
    (and (natp x) (<= x 4))
    ///
    (define gatesimp-level-fix ((x gatesimp-level-p))
      :returns (new-x gatesimp-level-p)
      (mbe :logic (if (gatesimp-level-p x) x 4)
           :exec x)
      ///
      (defret gatesimp-level-fix-when-gatesimp-level-p
        (implies (gatesimp-level-p x) (equal new-x x)))

      (fty::deffixtype gatesimp-level :pred gatesimp-level-p :fix gatesimp-level-fix :equiv gatesimp-level-equiv
        :define t))

    (defthm gatesimp-level-p-compound-recognizer
      (implies (gatesimp-level-p x)
               (natp x))
      :rule-classes :compound-recognizer))

  (local (defthm unsigned-byte-p-when-gatesimp-level-p
           (implies (gatesimp-level-p x)
                    (unsigned-byte-p 3 x))
           :hints(("Goal" :in-theory (enable gatesimp-level-p unsigned-byte-p)))))

  (local (defthm bound-when-gatesimp-level-p
           (implies (gatesimp-level-p x)
                    (<= x 4))
           :hints(("Goal" :in-theory (enable gatesimp-level-p unsigned-byte-p)))))

  (define gatesimp-xor-mode-p (x)
    (and (natp x) (<= x 2))
    ///
    (define gatesimp-xor-mode-fix ((x gatesimp-xor-mode-p))
      :returns (new-x gatesimp-xor-mode-p)
      (mbe :logic (if (gatesimp-xor-mode-p x) x 2)
           :exec x)
      ///
      (defret gatesimp-xor-mode-fix-when-gatesimp-xor-mode-p
        (implies (gatesimp-xor-mode-p x) (equal new-x x)))

      (fty::deffixtype gatesimp-xor-mode :pred gatesimp-xor-mode-p :fix gatesimp-xor-mode-fix :equiv gatesimp-xor-mode-equiv
        :define t))

    (defthm gatesimp-xor-mode-p-compound-recognizer
      (implies (gatesimp-xor-mode-p x)
               (natp x))
      :rule-classes :compound-recognizer))

  (local (defthm unsigned-byte-p-when-gatesimp-xor-mode-p
           (implies (gatesimp-xor-mode-p x)
                    (unsigned-byte-p 2 x))
           :hints(("Goal" :in-theory (enable gatesimp-xor-mode-p unsigned-byte-p)))))

  (local (defthm bound-when-gatesimp-xor-mode-p
           (implies (gatesimp-xor-mode-p x)
                    (<= x 2))
           :hints(("Goal" :in-theory (enable gatesimp-xor-mode-p unsigned-byte-p)))))

  (fty::fixtype-to-bitstruct gatesimp-level :width 3)
  (fty::fixtype-to-bitstruct gatesimp-xor-mode :width 2)

  (fty::defbitstruct gatesimp
  :parents (aignet-construction)
  :short "Structure encoding AIGNET construction settings for how much to try to
          simplify and whether to use hashing"
  :long "<p>A simple bit-encoded triple of @('level'), @('hashp'), and @('xor-mode').</p>

<p>The @('level') field is a value between 0 and 4 inclusive, determining how
hard to work to simplify new nodes.  The numbers corresponding to the levels of
simplification found in the paper:</p>
<blockquote>
R. Brummayer and A. Biere.  Local two-level And-Inverter Graph minimization
without blowup.  Proc. MEMCIS 6 (2006): 32-38,
</blockquote>

<p>The @('xor-mode') field is a value between 0 and 2 inclusive, determining
whether to use XOR nodes:</p>
<ul>
<li>If 2, XOR nodes can be created using @(see aignet-hash-xor) and
additionally, if the @('level') is 3 or greater, derived when creating the AND
of two nodes of the form @('(not (and a b))'), @('(not (and (not a) (not
b)))').</li>
<li>If 1, XOR nodes will be created when calling @(see aignet-hash-xor), but
not derived from existing AND gates.</li>
<li>If 0, no XOR nodes will be used even when calling @(see aignet-hash-xor),
instead implementing the function using AND gates.</li>
</ul>

<p>The @('hashp') field is a Boolean and determines whether structural hashing
is used.</p>

<p>To construct a gatesimp object, use either the constructor function
@('gatesimp') or the macro @('make-gatesimp'), with the usual conventions of
product types produced by @(see fty::defprod) and @(see fty::defbitstruct).</p>"

    ((hashp booleanp :default t)
     (level gatesimp-level :default 4)
     (xor-mode gatesimp-xor-mode :default 2)))

  (defthm gatesimp->level-bound
    (<= (gatesimp->level x) 4)
    :rule-classes (:rewrite :linear))

  (defthm gatesimp->xor-mode-bound
    (<= (gatesimp->xor-mode x) 2)
    :rule-classes (:rewrite :linear))

  (make-event
   `(define default-gatesimp ()
      :enabled t
      ;; not inlined, so it can be redefined
      ',(make-gatesimp))))
