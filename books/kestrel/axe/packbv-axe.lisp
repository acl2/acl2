; Axe rules about BV packing
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

;; todo: rename this file to packbv-rules-axe

(include-book "axe-syntax") ;for work-hard
(include-book "kestrel/bv-lists/packbv" :dir :system)
(include-book "kestrel/bv-lists/map-packbv" :dir :system)
(include-book "kestrel/bv-lists/bv-array-read" :dir :system)
(local (include-book "kestrel/bv/rules" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(include-book "kestrel/utilities/def-constant-opener" :dir :system)

;defforall could do this?
;this is a bit tricky because of what bv-array-read does to its index..
(defthm bv-array-read-of-map-packbv
  (implies (and (work-hard (< index len)) ;would like to drop this
                (natp index)
                (natp len))
           (equal (bv-array-read width len index (map-packbv itemcount itemsize items-lst))
                  ;fixme use bv-array-read in the conclusion? wrong type?
                  (bvchop width (packbv itemcount itemsize (nth index items-lst)))))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (bv-array-read ;LIST::NTH-OF-CONS ;LIST::NTH-WITH-LARGE-INDEX
                                   ceiling-of-lg
                                     ) (;UNSIGNED-BYTE-P-OF-+-OF-MINUS-ALT ;looped
                                        )))))

(def-constant-opener map-packbv)
