; Compare our library to the Unicode books
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "code-point-to-utf-8-chars")
(include-book "unicode/utf8-encode" :dir :system)
(include-book "kestrel/typed-lists-light/map-char-code" :dir :system)
(local (include-book "kestrel/bv/logand" :dir :system))
(local (include-book "kestrel/bv/logior" :dir :system))
(local (include-book "kestrel/arithmetic-light/ash" :dir :system))

;; Show that our encoding into chars is compatible with the unicode books' encoding into bytes
(thm
 (implies (and (natp code-point)
               (<= code-point #x10FFFF))
          (equal (uchar=>utf8 code-point)
                 (map-char-code (code-point-to-utf-8-chars code-point))))
 :hints (("Goal" :in-theory (enable code-point-to-utf-8-chars uchar=>utf8))))
