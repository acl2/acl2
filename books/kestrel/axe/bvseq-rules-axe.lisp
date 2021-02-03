; Axe rules about BV sequences
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "known-booleans")
(include-book "kestrel/bv-lists/all-all-unsigned-byte-p" :dir :system)
(include-book "kestrel/bv-lists/bvxor-list" :dir :system)
(include-book "kestrel/typed-lists-light/items-have-len" :dir :system)
(include-book "kestrel/typed-lists-light/all-true-listp" :dir :system)
(include-book "kestrel/lists-light/prefixp" :dir :system) ;drop?
(include-book "kestrel/utilities/defopeners" :dir :system)

(add-known-boolean all-unsigned-byte-p)
(add-known-boolean items-have-len)
(add-known-boolean all-true-listp)
(add-known-boolean all-all-unsigned-byte-p)
(add-known-boolean prefixp) ;move?
(add-known-boolean all-integerp)

;TODO: I forgot the extra parens around the claim, and it treated AND as one claim and so on...
;use def-constant-opener?
(defopeners bvxor-list :hyps ((and (syntaxp (quotep x)) (syntaxp (quotep y)))))
