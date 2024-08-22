; Encode a code point as UTF-8 chars
;
; Copyright (C) 2021-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/hex-char-to-val" :dir :system)
(include-book "kestrel/typed-lists-light/map-code-char" :dir :system)
(local (include-book "kestrel/arithmetic-light/ash" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))
(local (include-book "kestrel/bv/logior" :dir :system))
(local (include-book "kestrel/bv/logand" :dir :system))

;; Returns a list of bytes that encodes the CODE-POINT in UTF-8.
;; We could first convert to a list of bytes and then to a list of chars, at the cost of more consing.
(defund code-point-to-utf-8-bytes (code-point)
  (declare (xargs :guard (and (natp code-point)
                              (<= code-point #x10FFFF))
                  :split-types t)
           (type (integer 0 #x10FFFF) code-point))
  (cond ((<= code-point #x007F) ; 7 bits of data
         (list code-point       ; 0xxxxxxx (no masking needed)
               ))
        ((<= code-point #x07FF)                        ; 11 bits of data
         (list (logior #b11000000 (ash code-point -6)) ;110xxxxx for top 5 bits
               (logior #b10000000 (logand #b111111 code-point)) ;10xxxxxx for low 6 bits
               ))
        ((<= code-point #xFFFF)                         ; 16 bits of data
         (list (logior #b11100000 (ash code-point -12)) ;1110xxxx for top 4 bits
               (logior #b10000000 (logand #b111111 (ash code-point -6))) ;10xxxxxx for 6 middle bits
               (logior #b10000000 (logand #b111111 code-point)) ;10xxxxxx for low 6 bits
               ))
        (t                                               ; 21 bits of data
          (list (logior #b11110000 (ash code-point -18)) ;11110xxx for top 3 bits
                (logior #b10000000 (logand #b111111 (ash code-point -12))) ;10xxxxxx for next 6 bits
                (logior #b10000000 (logand #b111111 (ash code-point -6))) ;10xxxxxx for next 6 bits
                (logior #b10000000 (logand #b111111 code-point)) ;10xxxxxx for low 6 bits
                ))))

(defthm byte-listp-of-code-point-to-utf-8-bytes
  (implies (and (natp code-point)
                (<= code-point #x10FFFF))
           (byte-listp (code-point-to-utf-8-bytes code-point)))
  :hints (("Goal" :in-theory (enable code-point-to-utf-8-bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a list of chars that encodes the CODE-POINT in UTF-8.
;; See code-point-to-utf-8-chars-alt-def below, but that definition involves more consing.
(defund code-point-to-utf-8-chars (code-point)
  (declare (xargs :guard (and (natp code-point)
                              (<= code-point #x10FFFF))
                  :split-types t)
           (type (integer 0 #x10FFFF) code-point))
  (cond ((<= code-point #x007F)       ; 7 bits of data
         (list (code-char code-point) ; 0xxxxxxx (no masking needed)
               ))
        ((<= code-point #x07FF) ; 11 bits of data
         (list (code-char (logior #b11000000 (ash code-point -6))) ;110xxxxx for top 5 bits
               (code-char (logior #b10000000 (logand #b111111 code-point))) ;10xxxxxx for low 6 bits
               ))
        ((<= code-point #xFFFF) ; 16 bits of data
         (list (code-char (logior #b11100000 (ash code-point -12))) ;1110xxxx for top 4 bits
               (code-char (logior #b10000000 (logand #b111111 (ash code-point -6)))) ;10xxxxxx for 6 middle bits
               (code-char (logior #b10000000 (logand #b111111 code-point))) ;10xxxxxx for low 6 bits
               ))
        (t ; 21 bits of data
          (list (code-char (logior #b11110000 (ash code-point -18))) ;11110xxx for top 3 bits
                (code-char (logior #b10000000 (logand #b111111 (ash code-point -12)))) ;10xxxxxx for next 6 bits
                (code-char (logior #b10000000 (logand #b111111 (ash code-point -6)))) ;10xxxxxx for next 6 bits
                (code-char (logior #b10000000 (logand #b111111 code-point))) ;10xxxxxx for low 6 bits
                ))))

(defthm character-listp-of-code-point-to-utf-8-chars
  (character-listp (code-point-to-utf-8-chars code-point))
  :hints (("Goal" :in-theory (enable code-point-to-utf-8-chars))))

;; This would let us do all the reasoning about code-point-to-utf-8-bytes.
;; Also provides a sanity check comparing the 2 definitions.
(defthmd code-point-to-utf-8-chars-alt-def
  (equal (code-point-to-utf-8-chars code-point)
         (map-code-char (code-point-to-utf-8-bytes code-point)))
  :hints (("Goal" :in-theory (enable code-point-to-utf-8-bytes
                                     code-point-to-utf-8-chars
                                     map-code-char))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund code-point-to-utf-8-string (code-point)
  (declare (xargs :guard (and (natp code-point)
                              (<= code-point #x10FFFF))
                  :split-types t)
           (type (integer 0 #x10FFFF) code-point))
  (coerce (code-point-to-utf-8-chars code-point) 'string))

;; Helpful for printing the result readably
(defthm stringp-of-code-point-to-utf-8-string
  (stringp (code-point-to-utf-8-string code-point))
  :hints (("Goal" :in-theory (enable code-point-to-utf-8-string))))

;; (equal (code-point-to-utf-8-string #x263a) "☺")
