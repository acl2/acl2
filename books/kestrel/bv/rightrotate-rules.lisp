; BV Library: Rules about leftrotate
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "rightrotate")
(include-book "rightrotate32")
(include-book "bvxor")
(include-book "bitxor")
(include-book "bitand")
(include-book "bitor")
(include-book "trim")
(include-book "bv-syntax")
(local (include-book "bvcat-rules"))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))

(defthm rightrotate32-trim-arg1
  (implies (and (syntaxp (term-should-be-trimmed '5 amt 'non-arithmetic))
                (natp amt))
           (equal (rightrotate32 amt val)
                  (rightrotate32 (trim 5 amt) val)))
  :hints (("Goal" :in-theory (enable trim))))

;for this not to loop, we must simplify things like (bvchop 5 (bvplus 32 x y)) ??
(defthm rightrotate32-trim-arg1-all
  (implies (and (syntaxp (term-should-be-trimmed '5 amt 'all))
                (natp amt))
           (equal (rightrotate32 amt val)
                  (rightrotate32 (trim 5 amt) val)))
  :hints (("Goal" :in-theory (enable trim))))
