; Centaur regular expression library
; Copyright (C) 2014 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACRE")

(include-book "types")
(include-book "std/strings/cat" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/strings/hex" :dir :system)
(include-book "std/strings/octal" :dir :system)
(include-book "std/util/defenum" :dir :system)
(include-book "std/strings/strprefixp" :dir :system)
(include-book "std/strings/strpos" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(local (include-book "std/lists/take" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (xdoc::set-default-parents acre-internals))

(local (in-theory (disable take (tau-system) nth)))

(local (Defthm explode-of-str-fix
         (equal (acl2::explode (acl2::str-fix x))
                (acl2::explode x))))

(local (defthm my-characterp-nth
         (implies (and (character-listp x)
                       (< (nfix i) (len x)))
                  (characterp (nth i x)))
         :hints(("Goal" :in-theory (enable nth)))))

(local (defthm character-listp-cdr
         (implies (character-listp x)
                  (character-listp (cdr x)))))



(define charset-range ((x characterp)
                       (y characterp))
  :guard (<= (char-code x) (char-code y))
  :measure (nfix (- (char-code y) (char-code x)))
  :returns (chars character-listp)
  :prepwork ((local (defthm char-codes-not-equal
                      (implies (and (characterp x) (characterp y)
                                    (not (equal x y)))
                               (not (equal (char-code x) (char-code y))))
                      :hints (("goal" :use ((:instance code-char-char-code-is-identity (c x))
                                            (:instance code-char-char-code-is-identity (c y)))
                               :in-theory (disable code-char-char-code-is-identity))))))
  (b* ((x (mbe :logic (acl2::char-fix x) :exec x))
       ((when (mbe :logic (zp (- (char-code y) (char-code x)))
                   :exec (eql x y)))
        (list x))
       (next (code-char (+ 1 (char-code x)))))
    (cons x (charset-range next y))))

(define parse-hex-charcode ((x stringp) (index natp))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (char characterp)
               (new-index natp :rule-classes :type-prescription))
  :guard-hints (("goal" :in-theory (enable str::hex-digit-chars-value)))
  (b* ((index (lnfix index))
       ((unless (< (+ 1 index) (strlen x)))
        (mv "String ended within hex charcode" (code-char 0) index))
       (hex0 (char x index))
       (hex1 (char x (+ 1 index)))
       ((unless (and (str::hex-digit-char-p hex0)
                     (str::hex-digit-char-p hex1)))
        (mv "Malformed hex charcode" (code-char 0) index))
       (val (str::hex-digit-chars-value (list hex0 hex1))))
    (mv nil (code-char val) (+ 2 index)))
  ///
  (defret new-index-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (defret new-index-of-<fn>-strong
    (implies (not err)
             (< (nfix index) new-index))
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :rule-classes :linear))

(define parse-octal-charcode ((x stringp) (index natp))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (char characterp)
               (new-index natp :rule-classes :type-prescription))
  :guard-hints (("goal" :in-theory (enable str::oct-digit-chars-value)))
  (b* ((index (lnfix index))
       ((unless (< (+ 2 index) (strlen x)))
        (mv "String ended within octal charcode" (code-char 0) index))
       (octal0 (char x index))
       (octal1 (char x (+ 1 index)))
       (octal2 (char x (+ 2 index)))
       ((unless (and (str::oct-digit-char-p octal0)
                     (str::oct-digit-char-p octal1)
                     (str::oct-digit-char-p octal2)))
        (mv "Malformed octal charcode" (code-char 0) index))
       (val (str::oct-digit-chars-value (list octal0 octal1 octal2)))
       ((when (<= 256 val))
        (mv "Octal charcodes greater than 256 not supported" (code-char 0) index)))
    (mv nil (code-char val) (+ 3 index)))
  ///
  (defret new-index-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (defret new-index-of-<fn>-strong
    (implies (not err)
             (< (nfix index) new-index))
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :rule-classes :linear))


(define parse-charset-atom ((x stringp) (index natp))
  :guard (<= index (strlen x))
  ;; charset_atom =  non_backslash_non_closebracket_char
  ;;                 \\
  ;;                 \n
  ;;                 \t
  ;;                 \r
  ;;                 \f
  ;;                 \]
  ;;                 \-
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (char characterp)
               (new-index natp :rule-classes :type-prescription))
  (b* ((x (lstrfix x))
       (index (lnfix index))
       ((unless (< index (strlen x)))
        (mv "String ended inside charset" (code-char 0) index))
       (char1 (char x index))
       (index (+ 1 index))
       ((when (eql char1 #\]))
        (mv "End of charset" (code-char 0) index))
       ((unless (eql char1 #\\))
        (mv nil char1 index))
       ((unless (< index (strlen x)))
        (mv "String ended inside charset" (code-char 0) index))
       (char2 (char x index))
       (index (+ 1 index)))
    (case char2
      ((#\\ #\] #\-) (mv nil char2 index))
      (#\n (mv nil #\Newline index))
      (#\t (mv nil #\Tab index))
      (#\r (mv nil #\Return index))
      (#\f (mv nil #\Page index))
      (#\o (parse-octal-charcode x index))
      (#\x (parse-hex-charcode x index))
      (t (mv (str::cat "Unrecognized escape sequence in charset: " (coerce (list char1 char2) 'string))
             (code-char 0) index))))
  ///
  (defret new-index-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (defret new-index-of-<fn>-strong
    (implies (not err)
             (< (nfix index) new-index))
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :rule-classes :linear))


(define parse-charset-set ((x stringp) (index natp))
  :guard (<= index (strlen x))
  ;; charset_set =  \w | \d | \s | \h | \v
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (char character-listp)
               (new-index natp :rule-classes :type-prescription))
  (b* ((x (lstrfix x))
       (index (lnfix index))
       ((unless (< index (strlen x)))
        (mv "String ended inside charset" nil index))
       (char1 (char x index))
       ((unless (eql char1 #\\))
        (mv "No match" nil index))
       (index (+ 1 index))
       ((unless (< index (strlen x)))
        (mv "String ended inside charset" nil index))
       (char2 (char x index))
       (index (+ 1 index)))
    (case char2
      (#\w (mv nil (cons #\_
                         (append (charset-range #\a #\z)
                                 (charset-range #\A #\Z)
                                 (charset-range #\0 #\9)))
               index))
      (#\d (mv nil (charset-range #\0 #\9) index))
      (#\s (mv nil '(#\Space #\Tab #\Newline #\Page #\Return) index))
      (#\h (mv nil '(#\Space #\Tab) index))
      (#\v (mv nil '(#\Newline #\Page #\Return) index))
      (t (mv (str::cat "Unrecognized escape sequence in charset: " (coerce (list char1 char2) 'string))
             nil index))))
  ///
  (defret new-index-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (defret new-index-of-<fn>-strong
    (implies (not err)
             (< (nfix index) new-index))
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :rule-classes :linear))


(define parse-charset-elem ((x stringp) (index natp))
  ;; charset_elem = charset_set
  ;;                charset_atom - charset_atom
  ;;                charset_atom
  :guard (<= index (strlen x))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (chars character-listp)
               (new-index natp :rule-classes :type-prescription))
  (b* (((mv err set new-index) (parse-charset-set x index))
       ((unless err) (mv nil set new-index))
       ((mv err char1 index) (parse-charset-atom x index))
       ((when err) (mv err nil index))
       ((unless (< index (strlen x)))
        (mv "String ended inside charset" nil index))
       (dash (char x index))
       ((unless (eql dash #\-))
        (mv nil (list char1) index))
       ((mv err char2 index) (parse-charset-atom x (+ 1 index)))
       ((when err) (mv err nil index))
       ((when (< (char-code char2) (char-code char1)))
        (mv "Invalid range" nil index)))
    (mv nil (charset-range char1 char2) index))
  ///
  (defret new-index-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (defret new-index-of-<fn>-strong
    (implies (not err)
             (< (nfix index) new-index))
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :rule-classes :linear))

(define parse-charset-aux ((x stringp) (index natp))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (chars character-listp)
               (new-index natp :rule-classes :type-prescription))
  :guard (<= index (strlen x))
  :measure (nfix (- (strlen x) (nfix index)))
  :prepwork ((local (defthm true-listp-when-character-listp
                      (implies (character-listp x)
                               (true-listp x)))))
 ;; cset_elems = ""
 ;;              cset_elem cset_elems

  (b* (((when (mbe :logic (zp (- (strlen x) (nfix index)))
                   :exec (eql (strlen x) index)))
        (mv "String ended inside charset" nil (lnfix index)))
       (x (lstrfix x))
       (index (lnfix index))
       (char1 (char x index))
       ((when (eql char1 #\]))
        (mv nil nil (+ 1 index)))
       ((mv err chars index) (parse-charset-elem x index))
       ((when err) (mv err nil index))
       ((mv err rest index) (parse-charset-aux x index))
       ((when err) (mv err nil index)))
    (mv nil (append chars rest) index))
  ///
  (defret new-index-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (defret new-index-of-<fn>-strong
    (implies (not err)
             (< (nfix index) new-index))
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :rule-classes :linear))

(define parse-charset ((x stringp)
                             (index natp)) ;; after the [
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (pat (implies (not err) (regex-p pat)))
               (new-index natp :rule-classes :type-prescription))
  (b* ((x (lstrfix x))
       (index (lnfix index))
       ((when (<= (strlen x) index))
        (mv "String ended inside charset" nil index))
       ((mv negp index)
        (if (eql (char x index) #\^)
            (mv t (+ 1 index))
          (mv nil index)))
       ((when (<= (strlen x) index))
        (mv "String ended inside charset" nil index))
       ((mv err chars last-index) ;; last-index is past close bracket if no error
        (parse-charset-aux x index))
       ((when err) (mv err nil last-index)))
    (mv nil (regex-charset (coerce chars 'string) negp) last-index))
  ///
  (defret new-index-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (defret new-index-of-<fn>-strong
    (implies (not err)
             (< (nfix index) new-index))
    :hints (("goal" :expand ((parse-charset-aux x index))))
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :rule-classes :linear))


(define parse-range ((x stringp)
                           (index natp)) ;; after the {
  :guard (<= index (strlen x))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (min natp :rule-classes :type-prescription)
               (max acl2::maybe-natp :rule-classes :type-prescription)
               (new-index natp :rule-classes :type-prescription))
  :prepwork ((local (defthm len-of-nthcdr
                      (implies (force (<= (nfix n) (len x)))
                               (equal (len (nthcdr n x))
                                      (- (len x) (nfix n))))
                      :hints(("Goal" :in-theory (enable nthcdr)))))
             (local (in-theory (disable len nthcdr))))
  (b* ((x (lstrfix x))
       (index (lnfix index))
       ((when (eql index (strlen x)))
        (mv "String ended inside range expression (start)" 0 0 index))
       ((mv min len1) (str::parse-nat-from-string x 0 0 index (strlen x)))
       (index (+ len1 index))
       ((when (eql index (strlen x)))
        (mv "String ended inside range expression (after min index)" 0 0 index))
       (nextchar (char x index))
       ((when (eql nextchar #\}))
        (mv nil min min (+ 1 index)))
       ((unless (eql nextchar #\,))
        (mv "Malformed range -- expecting comma" 0 0 index))
       (index (+ 1 index))
       ((when (eql index (strlen x)))
        (mv "String ended inside range expression (after comma)" 0 0 index))
       ((mv val2 len2) (str::parse-nat-from-string x 0 0 index (strlen x)))
       (max (and (not (eql len2 0)) val2))
       (index (+ len2 index))
       ((when (eql index (strlen x)))
        (mv "String ended inside range expression (after max index)" 0 0 index))
       (nextchar (char x index))
       ((unless (eql nextchar #\}))
        (mv "Malformed range -- expecting close brace" 0 0 index)))
    (mv nil min max (+ 1 index)))
  ///
  (defret new-index-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (defret new-index-of-<fn>-strong
    (implies (not err)
             (< (nfix index) new-index))
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :rule-classes :linear))



(define parse-repeatbase ((x stringp)
                          (index natp))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (min natp :rule-classes :type-prescription)
               (max maybe-natp :rule-classes :type-prescription)
               (new-index natp :rule-classes :type-prescription))
  :guard (<= index (strlen x))
  ;; repeatbase = *
  ;;              +
  ;;              ?
  ;;              {min}
  ;;              {min,}
  ;;              {min,max}
  (b* ((index (lnfix index))
       ((when (<= (strlen x) index))
        (mv "End of string when parsing repeatbase" 0 0 index))
       (char (char x index)))
    (case char
      (#\* (mv nil 0 nil (+ 1 index)))
      (#\+ (mv nil 1 nil (+ 1 index)))
      (#\? (mv nil 0 1   (+ 1 index)))
      (#\{ (b* (((mv err min max new-index) (parse-range x (+ 1 index)))
                ((when err) (mv err 0 0 index)))
             (mv nil min max new-index)))
      (t (mv "Not a repeatbase" 0 0 (lnfix index)))))
  ///
  (defret new-index-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (defret new-index-of-<fn>-strong
    (implies (not err)
             (< (nfix index) new-index))
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :rule-classes :linear)

  (defret no-change-of-<fn>
    (implies err
             (equal new-index (nfix index)))))


(defenum repeatmod-p (:? :+ nil))

(define parse-repeatmod ((x stringp)
                         (index natp))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (repeatmod repeatmod-p)
               (new-index natp :rule-classes :type-prescription))
  :guard (<= index (strlen x))
  ;; repeatmod = ?      (nongreedy)
  ;;             +      (nonbacktracking)
  (b* ((index (lnfix index))
       ((when (<= (strlen x) index))
        (mv "End of string when parsing repeatmod" nil index))
       (char (char x index)))
    (case char
      (#\? (mv nil :? (+ 1 index)))
      (#\+ (mv nil :+ (+ 1 index)))
      (t (mv "Not a repeatmod" nil index))))
  ///
  (defret new-index-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (defret new-index-of-<fn>-strong
    (implies (not err)
             (< (nfix index) new-index))
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :rule-classes :linear)

  (defret no-change-of-<fn>
    (implies err
             (equal new-index (nfix index)))))


(define parse-repeatop ((x stringp)
                        (index natp))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (min natp :rule-classes :type-prescription)
               (max maybe-natp :rule-classes :type-prescription)
               (repeatmod repeatmod-p)
               (new-index natp :rule-classes :type-prescription))
  :guard (<= index (strlen x))
  (b* (((mv err min max index) (parse-repeatbase x index))
       ((when err) (mv err 0 0 nil index))
       ((mv err repeatmod index) (parse-repeatmod x index))
       ((when err) (mv nil min max nil index)))
    (mv nil min max repeatmod index))
  ///
  (defret new-index-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (defret new-index-of-<fn>-strong
    (implies (not err)
             (< (nfix index) new-index))
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :rule-classes :linear)

  (defret no-change-of-<fn>
    (implies err
             (equal new-index (nfix index)))))





(define match-string-at ((target stringp)
                         (x stringp)
                         (index natp))
  :returns (mv (matchedp booleanp :rule-classes :type-prescription)
               (new-index natp :rule-classes :type-prescription))
  :guard (<= index (strlen x))
  :prepwork ((local (in-theory (disable (force)))))
  (b* ((match (str::strprefixp-impl (lstrfix target)
                                     (lstrfix x)
                                     0 (lnfix index)
                                     (strlen target)
                                     (strlen x))))
    (if match
        (mv t (+ (strlen target) (lnfix index)))
      (mv nil (lnfix index))))
  ///

  (local (include-book "std/lists/nthcdr" :dir :system))

  (defret new-index-less-than-length-of-<fn>
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index
                 (len (acl2::explode x))))
    :hints (("goal" :use ((:instance acl2::len-when-prefixp
                           (x (acl2::Explode target))
                           (y (nthcdr index (acl2::explode x)))))
             :in-theory (disable acl2::len-when-prefixp)))
    :rule-classes :linear)

  (defret new-index-increasing-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (defret new-index-increasing-strong-of-<fn>
    (implies (and matchedp (not (equal 0 (strlen target))))
             (< (nfix index) new-index))
    :rule-classes :linear)

  (defret no-change-of-<fn>
    (implies (not matchedp)
             (equal new-index (lnfix index))))

  (defret measure-decr-of-match-string-at
    (<= (nfix (+ (len (acl2::explode x)) (- new-index)))
        (nfix (+ (- (nfix index)) (len (acl2::explode x)))))
    :hints(("Goal" :in-theory (e/d (nfix) (match-string-at
                                           new-index-increasing-of-match-string-at))
            :use new-index-increasing-of-match-string-at))
    :rule-classes :linear)

  (defret index-lte-len-when-match-string-at-nonempty
    (implies (and matchedp (not (equal 0 (strlen target))))
             (<= (nfix index) (len (acl2::explode x))))
    :rule-classes :forward-chaining)

  (defret new-index-less-than-length-of-<fn>-when-matched-nonempty
    (implies (and matchedp (not (equal 0 (strlen target))))
             (<= new-index
                 (len (acl2::explode x))))
    :hints (("goal" :use ((:instance new-index-less-than-length-of-match-string-at)
                          (:instance index-lte-len-when-match-string-at-nonempty))
             :in-theory (disable new-index-less-than-length-of-match-string-at
                                 index-lte-len-when-match-string-at-nonempty
                                 match-string-at)))
    :rule-classes :linear)

  (defret measure-decr-of-match-string-at-strong
    (implies (and matchedp (not (equal 0 (strlen target))))
             (< (nfix (+ (len (acl2::explode x)) (- new-index)))
                (nfix (+ (- (nfix index)) (len (acl2::explode x))))))
    :hints(("Goal" :in-theory (e/d (nfix) (match-string-at
                                           new-index-increasing-strong-of-match-string-at))
            :use (new-index-increasing-strong-of-match-string-at
                  index-lte-len-when-match-string-at-nonempty)))
    :rule-classes :linear))

(acl2::def-b*-binder when-match-string
  :body
  (b* ((target (first acl2::args))
       ((unless (stringp target))
        (er hard? 'match-string "Target must be a string"))
       (x (or (second acl2::args) 'x))
       (index (or (third acl2::args) 'index)))
    `(b* (((mv matchedp index) (match-string-at ,target ,x ,index))
          ((when matchedp) . ,acl2::forms))
       ,acl2::rest-expr)))

(acl2::def-b*-binder unless-match-string
  :body
  (b* ((target (first acl2::args))
       ((unless (stringp target))
        (er hard? 'match-string "Target must be a string"))
       (x (or (second acl2::args) 'x))
       (index (or (third acl2::args) 'index)))
    `(b* (((mv matchedp index) (match-string-at ,target ,x ,index))
          ((unless matchedp) . ,acl2::forms))
       ,acl2::rest-expr)))



(define get-charset ((str stringp))
  :returns (pat (implies pat (regex-p pat)))
  (b* (((mv err charset &) (parse-charset (str::cat (lstrfix str) "]") 0))
       ((when err) (raise "Error parsing charset: ~x0 -- ~s1" (lstrfix str) err)))
    charset))

(defmacro defcharset (letter str)
  `(table charset-table ,letter (get-charset ,str)))

(defcharset #\w "\\w")
(defcharset #\W "^\\w")
(defcharset #\d "\\d")
(defcharset #\D "^\\d")
(defcharset #\s "\\s")
(defcharset #\S "^\\s")
(defcharset #\h "\\h")
(defcharset #\H "^\\h")
(defcharset #\v "\\v")
(defcharset #\V "^\\v")

(make-event
 `(defconst *charset-table* ',(table-alist 'charset-table (w state))))

(define charset-char-regex ((x))
  :returns (pat (implies pat (regex-p pat)))
  (cdr (assoc x *charset-table*)))


;; backref = \ digit
;;           \g digit
;;           \g{number}
;;           \g{name}
;;           \k{name}
;;           \k<name>
;;           \k'name'


(define find-substr ((target stringp)
                     (x stringp)
                     (index natp))
  :returns (pos maybe-natp :rule-classes :type-prescription)
  :guard (<= index (strlen x))
  :prepwork ((local (in-theory (disable (force)))))
  (str::strpos-fast (lstrfix target)
                    (lstrfix x)
                    (lnfix index)
                    (strlen target)
                    (strlen x))
  ///
  (local (defthm listpos-bound
           (implies (acl2::listpos x y)
                    (<= (acl2::listpos x y) (- (len y) (len x))))
           :hints(("Goal" :in-theory (enable acl2::listpos)))
           :rule-classes :linear))

  (local (include-book "std/lists/nthcdr" :dir :system))

  (defret new-index-of-<fn>
    (implies pos
             (<= (nfix index) pos))
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (and pos
                  (<= (nfix index) (len (acl2::explode x))))
             (<= pos (- (len (acl2::explode x)) (len (acl2::explode target)))))
    :rule-classes :linear))

(define parse-k-backref ((x stringp)
                         (index natp))
  :guard (<= index (strlen x))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (pat (implies (not err) (regex-p pat)))
               (new-index natp :rule-classes :type-prescription))
;;           \k{name}
;;           \k<name>
;;           \k'name'
  (b* ((index (lnfix index))
       ((when (<= (strlen x) (lnfix index)))
        (mv "EOS parsing \\k backref" nil index))
       (char (char x index))
       (end-delim (case char
                    (#\{ "}")
                    (#\< ">")
                    (#\' "'")
                    (t nil)))
       ((unless end-delim)
        (mv "Bad delimiter in \\k backref" nil index))
       (idx (find-substr end-delim x index))
       ((unless idx)
        (mv "Unclosed name in \\k capture form" nil index))
       (name (subseq x index idx))
       (index (+ 1 idx)))
    (mv nil (regex-backref name) index))
  ///

  (defret new-index-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (defret new-index-of-<fn>-strong
    (implies (not err)
             (< (nfix index) new-index))
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :rule-classes :linear)

  (defret no-change-of-<fn>
    (implies err
             (equal new-index (nfix index)))))

(define parse-g-backref ((x stringp)
                         (index natp))
  :guard (<= index (strlen x))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (pat (implies (not err) (regex-p pat)))
               (new-index natp :rule-classes :type-prescription))
;;           \g digit
;;           \g{number}
;;           \g{name}
  (b* ((index (lnfix index))
       ((when (<= (strlen x) (lnfix index)))
        (mv "EOS parsing \\g backref" nil index))
       (char (char x index))
       ((when (str::dec-digit-char-p char))
        (b* (((mv val len) (str::parse-nat-from-string x 0 0 index (strlen x)))
             (index (+ index len)))
          (mv nil (regex-backref val) index)))
       (index (+ 1 index))
       ((unless (eql char #\{))
        (mv "Bad delimiter in \\g backref" nil index))
       (idx (find-substr "}" x index))
       ((unless idx)
        (mv "Unclosed name in \\g capture form" nil index))
       (name (subseq x index idx))
       ((mv val len) (str::parse-nat-from-string name 0 0 0 (strlen name)))
       ((when (eql len (strlen name)))
        (mv nil (regex-backref val) (+ 1 idx))))
    (mv nil (regex-backref name) (+ 1 idx)))
  ///

  (defret new-index-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (local (in-theory (enable nth)))

  (local (defthm len-of-take-leading-dec-digit-chars-when-car-dec-digit-char-p
           (implies (str::dec-digit-char-p (car x))
                    (< 0 (len (str::take-leading-dec-digit-chars x))))
           :hints(("Goal" :in-theory (enable str::take-leading-dec-digit-chars)))
           :rule-classes :linear))

  (local (defthm len-of-take-leading-dec-digit-chars-upper-bound
           (<= (len (str::take-leading-dec-digit-chars x)) (len x))
           :hints(("Goal" :in-theory (enable str::take-leading-dec-digit-chars)))
           :rule-classes :linear))


  (local (include-book "std/lists/nthcdr" :dir :system))
  ;; (local (defthm car-of-nthcdr
  ;;          (equal (car (nthcdr n x)) (nth n x))))

  (defret new-index-of-<fn>-strong
    (implies (not err)
             (< (nfix index) new-index))
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :rule-classes :linear))

(define parse-primitive ((x stringp)
                         (index natp))
  :guard (<= index (strlen x))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
               (pat (implies (not err) (regex-p pat)))
               (new-index natp :rule-classes :type-prescription))
  ;; primitive = character
  ;;             .
  ;;             [ characterclass ]
  ;;             [ ^ characterclass ]
  ;;             ^
  ;;             $
  ;;             backref
  ;;             \ metacharacter       (escape)
  ;;             \ charsetchar

  (b* ((index (lnfix index))
       ((when (<= (strlen x) (lnfix index)))
        (mv "EOS parsing primitive" nil index))
       (char (char x index))
       (index (+ 1 index)))
    (case char
      (#\. (mv nil (regex-charset "" t) index))
      (#\^ (mv nil (regex-start) index))
      (#\$ (mv nil (regex-end) index))
      (#\[ (parse-charset x index))
      (#\\
       (b* (((when (<= (strlen x) (lnfix index)))
             (mv "EOS after backslash" nil index))
            (char (char x index))
            (charset (charset-char-regex char))
            ((when charset)
             (mv nil charset (+ 1 index)))
            ((when (str::dec-digit-char-p char))
             (b* (((mv val len) (str::parse-nat-from-string x 0 0 index (strlen x)))
                  (index (+ index len)))
               (mv nil (regex-backref val) index)))
            (index (+ 1 index)))
         (case char
           (#\n (mv nil (regex-exact (coerce '(#\Newline) 'string)) index))
           (#\t (mv nil (regex-exact (coerce '(#\Tab) 'string)) index))
           (#\r (mv nil (regex-exact (coerce '(#\Return) 'string)) index))
           (#\f (mv nil (regex-exact (coerce '(#\Page) 'string)) index))
           (#\o (b* (((mv err char index) (parse-octal-charcode x index))
                     ((when err) (mv err nil index)))
                  (mv nil (regex-exact (coerce (list char) 'string)) index)))
           (#\x (b* (((mv err char index) (parse-hex-charcode x index))
                     ((when err) (mv err nil index)))
                  (mv nil (regex-exact (coerce (list char) 'string)) index)))
           ((#\\ #\^ #\. #\$ #\| #\( #\) #\[ #\] #\* #\+ #\? #\{ #\})
            (mv nil (regex-exact (coerce (list char) 'string)) index))
           (#\g ;; various forms of backref
            (parse-g-backref x index))
           (#\k ;; other forms of backref
            (parse-k-backref x index))
           (t (mv (str::cat "Unrecognized escape: \\" (coerce (list char) 'string)) nil index)))))
      ((#\| #\( #\) #\] #\* #\+ #\? #\{ #\})
       (mv "Found metacharacter while parsing primitive" nil index))
      (t (mv nil (regex-exact (coerce (list char) 'string)) index))))
  ///

  (defret new-index-of-<fn>
    (<= (nfix index) new-index)
    :rule-classes :linear)

  (local (defthm len-of-take-leading-dec-digit-chars-when-car-dec-digit-char-p
           (implies (str::dec-digit-char-p (car x))
                    (< 0 (len (str::take-leading-dec-digit-chars x))))
           :hints(("Goal" :in-theory (enable str::take-leading-dec-digit-chars)))
           :rule-classes :linear))

  (local (defthm len-of-take-leading-dec-digit-chars-upper-bound
           (<= (len (str::take-leading-dec-digit-chars x)) (len x))
           :hints(("Goal" :in-theory (enable str::take-leading-dec-digit-chars)))
           :rule-classes :linear))


  (local (include-book "std/lists/nthcdr" :dir :system))
  ;; (local (defthm car-of-nthcdr
  ;;          (equal (car (nthcdr n x)) (nth n x))))

  (local (Defthm len-of-cdr
           (implies (consp x)
                    (equal (len (cdr x))
                           (+ -1 (len x))))))

  (defret new-index-of-<fn>-strong
    (implies (not err)
             (< (nfix index) new-index))
    :rule-classes :linear)

  (defret new-index-of-<fn>-less-than-length
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :rule-classes :linear))



(defines parse-regex-rec
  :prepwork ((local (in-theory (disable not))))
  (define parse-regex-rec ((x stringp)
                           (index natp)
                           (br-index natp))
    :verify-guards nil
    :guard (<= index (strlen x))
    :measure (list (- (strlen x) (nfix index))  10)
    :well-founded-relation acl2::nat-list-<
    :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
                 (regex (implies (not err) (regex-p regex)))
                 (new-index natp :rule-classes :type-prescription)
                 (new-br-index natp :rule-classes :type-prescription))
    ;; regex = concat
    ;;         concat | regex
    (b* (((mv concat new-index br-index) (parse-concat-rec x index br-index))
         ((unless (mbt (<= (lnfix index) (nfix new-index))))
          (mv "Impossible" nil new-index br-index))
         (index new-index)
         ((unless-match-string "|" x index)
          (mv nil concat index br-index))
         ((mv err rest index br-index) (parse-regex-rec x index br-index))
         ((when err)
          (mv err nil index br-index)))
      (mv nil (regex-disjunct2 concat rest) index br-index)))

  (define parse-concat-rec ((x stringp)
                            (index natp)
                            (br-index natp))
    :guard (<= index (strlen x))
    :measure (list (- (strlen x) (nfix index)) 9)
    ;; No errors!
    :returns (mv (regex regex-p)
                 (new-index natp :rule-classes :type-prescription)
                 (new-br-index natp :rule-classes :type-prescription))
    ;; concat = ""           (empty)
    ;;          repeat concat
    (b* (((mv err repeat new-index new-br-index) (parse-repeat-rec x index br-index))
         ((when err) (mv (regex-exact "") (lnfix index) (lnfix br-index)))
         ((unless (mbt (and (< (lnfix index) (nfix new-index))
                            (< (lnfix index) (strlen x)))))
          ;; Impossible
          (mv (regex-exact "") (lnfix index) (lnfix br-index)))
         (index new-index)
         (br-index new-br-index)
         ((mv rest new-index new-br-index) (parse-concat-rec x index br-index)))
      (mv (regex-concat2 repeat rest) new-index new-br-index)))


  (define parse-repeat-rec ((x stringp)
                            (index natp)
                            (br-index natp))
    :guard (<= index (strlen x))
    :measure (list (- (strlen x) (nfix index)) 8)
    :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
                 (regex (implies (not err) (regex-p regex)))
                 (new-index natp :rule-classes :type-prescription)
                 (new-br-index natp :rule-classes :type-prescription))
    ;; repeat = atom
    ;;          atom repeatop
    (b* (((mv err atom index br-index) (parse-atom-rec x index br-index))
         ((when err) (mv err nil index br-index))
         ((mv err min max repeatmod index) (parse-repeatop x index))
         ((when err)
          (mv nil atom index br-index)))
      (mv nil
          (case repeatmod
            (:? (regex-reverse-pref (make-regex-repeat :pat (regex-reverse-pref atom) :min min :max max)))
            (:+ (regex-no-backtrack (make-regex-repeat :pat atom :min min :max max)))
            (t  (make-regex-repeat :pat atom :min min :max max)))
          index br-index)))

  (define parse-atom-rec ((x stringp)
                          (index natp)
                          (br-index natp))
    :guard (<= index (strlen x))
    :measure (list (- (strlen x) (nfix index)) 7)
    :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
                 (regex (implies (not err) (regex-p regex)))
                 (new-index natp :rule-classes :type-prescription)
                 (new-br-index natp :rule-classes :type-prescription))
    ;; atom = group
    ;;        primitive
    (b* ((index (lnfix index))
         ((when-match-string "(" x index)
          (parse-group-rec x index br-index))
         ((mv err result new-index) (parse-primitive x index)))
      (mv err result new-index (lnfix br-index))))

  (define parse-group-rec ((x stringp)
                           (index natp)
                           (br-index natp))
    :guard (<= index (strlen x))
    :measure (list (- (strlen x) (nfix index)) 20)
    :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription)
                 (regex (implies (not err) (regex-p regex)))
                 (new-index natp :rule-classes :type-prescription)
                 (new-br-index natp :rule-classes :type-prescription))
;; group = ( regex )
;;         (?: regex )           (noncapturing)
;;         (?i: regex )          (noncapturing, case insensitive)
;;         (?^i: regex )         (noncapturing, case sensitive)
;;         (?<name> regex )
;;         (?= regex )           (zero-length lookahead)
;;         (?! regex )           (zero-length lookahead, negated)
;;         (?<= regex )          (zero-length lookbehind, regex must be constant width)
;;         (?<! regex )          (zero-length lookbehind, regex must be constant width, negated)
    ;; Open paren has already been read.
    (b* ((br-index (lnfix br-index))
         ((when-match-string "?:" x index)
          ;; Noncapturing group.
          (b* (((mv err pat index br-index)
                (parse-regex-rec x index br-index))
               ((when err) (mv err nil index br-index))
               ((unless-match-string ")" x index)
                (mv "Expected close paren to finish group" nil index br-index)))
            (mv nil pat index br-index)))
         ((when-match-string "?i:" x index)
          ;; Noncapturing, case-insensitive
          (b* (((mv err pat index br-index)
                (parse-regex-rec x index br-index))
               ((when err) (mv err nil index br-index))
               ((unless-match-string ")" x index)
                (mv "Expected close paren to finish group" nil index br-index)))
            (mv nil (regex-case-sens pat t) index br-index)))
         ((when-match-string "?^i:" x index)
          ;; Noncapturing, case-sensitive
          (b* (((mv err pat index br-index)
                (parse-regex-rec x index br-index))
               ((when err) (mv err nil index br-index))
               ((unless-match-string ")" x index)
                (mv "Expected close paren to finish group" nil index br-index)))
            (mv nil (regex-case-sens pat nil) index br-index)))
         ((when-match-string "?=" x index)
          ;; Zero-length lookahead
          (b* (((mv err pat index br-index)
                (parse-regex-rec x index br-index))
               ((when err) (mv err nil index br-index))
               ((unless-match-string ")" x index)
                (mv "Expected close paren to finish group" nil index br-index)))
            (mv nil (regex-zerolength pat 0 nil) index br-index)))
         ((when-match-string "?!" x index)
          ;; Zero-length lookahead, negated
          (b* (((mv err pat index br-index)
                (parse-regex-rec x index br-index))
               ((when err) (mv err nil index br-index))
               ((unless-match-string ")" x index)
                (mv "Expected close paren to finish group" nil index br-index)))
            (mv nil (regex-zerolength pat 0 t) index br-index)))
         ((when-match-string "?<=" x index)
          ;; Zero-length lookbehind
          (b* (((mv err pat index br-index)
                (parse-regex-rec x index br-index))
               ((when err) (mv err nil index br-index))
               ((unless-match-string ")" x index)
                (mv "Expected close paren to finish group" nil index br-index))
               (width (regex-constant-width pat))
               ((unless width)
                (mv "Lookbehind regex must have constant width" nil index br-index)))
            (mv nil (regex-zerolength pat width nil) index br-index)))
         ((when-match-string "?<!" x index)
          ;; Zero-length lookbehind, negated
          (b* (((mv err pat index br-index)
                (parse-regex-rec x index br-index))
               ((when err) (mv err nil index br-index))
               ((unless-match-string ")" x index)
                (mv "Expected close paren to finish group" nil index br-index))
               (width (regex-constant-width pat))
               ((unless width)
                (mv "Lookbehind regex must have constant width" nil index br-index)))
            (mv nil (regex-zerolength pat width t) index br-index)))
         ((when-match-string "?<" x index)
          (b* ((idx (find-substr ">" x index))
               ((unless idx)
                (mv "Unclosed name in ?< capture form" nil index br-index))
               (name (subseq x index idx))
               (index (+ 1 idx))
               ;; Note: Perl indexes named capture groups.
               (my-br-index br-index)
               ((mv err pat index br-index) (parse-regex-rec x index (+ 1 (lnfix br-index))))
               ((when err) (mv err nil index br-index))
               ((unless-match-string ")" x index)
                (mv "Expected close paren to finish group" nil index br-index)))
            (mv nil (regex-group (regex-group pat name) my-br-index) index br-index)))

         ;; Otherwise, default capture group.
         (my-br-index br-index)
         ((mv err pat index br-index)
          (parse-regex-rec x index (+ 1 (lnfix br-index))))
         ((when err) (mv err nil index br-index))
         ((unless-match-string ")" x index)
          (mv "Expected close paren to finish group" nil index br-index)))
      (mv nil (regex-group pat my-br-index) index br-index)))
  ///
  (local
   (make-event
    `(defconst *parse-regex-fns*
       ',(acl2::getpropc 'parse-regex-rec 'acl2::recursivep nil (w state)))))

  (local (make-event `(in-theory (disable . ,*parse-regex-fns*))))

  (local (defun parse-regex-mr-fns (name body hints rule-classes fns)
           (if (atom fns)
               nil
             (cons `(defret ,name
                      ,body :hints ,hints :rule-classes ,rule-classes :fn ,(car fns))
                   (parse-regex-mr-fns name body hints rule-classes (cdr fns))))))

  (local (defun parse-regex-mutual-recursion (name body hints rule-classes omit)
           `(defret-mutual ,name
              ,@(parse-regex-mr-fns name body hints rule-classes
                                    (set-difference-eq *parse-regex-fns* omit))
              :skip-others t)))

  (defmacro def-parse-regex-thm (name body &key hints rule-classes omit)
    `(make-event (parse-regex-mutual-recursion ',name ',body ',hints ',rule-classes ',omit)))

  (def-parse-regex-thm new-index-nondecr-of-<fn>
    (<= (nfix index) new-index)
    :hints ('(:expand <call>))
    :rule-classes :linear)

  (def-parse-regex-thm new-index-incr-of-<fn>
    (implies (not err)
             (< (nfix index) new-index))
    :hints ('(:expand <call>))
    :rule-classes :linear
    :omit (parse-regex-rec parse-concat-rec))

  (def-parse-regex-thm new-index-upper-bound-of-<fn>
    (implies (<= (nfix index) (len (acl2::explode x)))
             (<= new-index (len (acl2::explode x))))
    :hints ('(:expand <call>))
    :rule-classes :linear)

  (local (defret index-less-than-length-when-parse-repeat-rec-no-error
           (implies (and (not err)
                         (natp index)
                         (<= index (len (acl2::explode x))))
                    (< index (len (acl2::explode x))))
           :hints (("goal" :use ((:instance new-index-incr-of-parse-repeat-rec))
                    :in-theory (disable new-index-incr-of-parse-repeat-rec)))
           :rule-classes :forward-chaining
           :fn parse-repeat-rec))

  (verify-guards parse-regex-rec)

  (fty::deffixequiv-mutual parse-regex-rec))


(define parse-regex ((x stringp))
  :returns (mv (err acl2::maybe-stringp)
               (pat (implies (not err) (regex-p pat))))
  (b* (((mv err regex index ?br-index) (parse-regex-rec x 0 1))
       ((when err) (mv err nil))
       ((when (< index (strlen x)))
        (mv (str::cat "Regex parsing didn't consume the whole string: Remaining: "
                      (subseq x index nil))
            nil)))
    (mv nil regex)))

(define preproc-legible-aux ((x stringp) (index natp) (acc character-listp))
  :guard (<= index (strlen x))
  :measure (nfix (- (strlen x) (nfix index)))
  :prepwork ((local (in-theory (disable member reverse str::consp-of-explode nth))))
  :returns (new-x stringp :rule-classes :type-prescription
                  :hints(("Goal" :in-theory (enable reverse))))
  (b* (((when (mbe :logic (zp (- (strlen x) (nfix index)))
                   :exec (eql index (strlen x))))
        (mbe :logic (reverse (coerce (make-character-list acc) 'string))
             :exec (reverse (coerce acc 'string))))
       (x (lstrfix x))
       (index (lnfix index))
       (char (char x index))
       ((when (member char '(#\Newline #\Space #\Tab #\Return #\Page)))
        (preproc-legible-aux x (+ 1 index) acc))
       ((when (eql char #\#))
        ;; skip until newline
        (b* ((index (find-substr (coerce '(#\Newline) 'string) x index))
             ((unless index) ;; done
              (reverse (coerce acc 'string))))
          (preproc-legible-aux x (+ 1 index) acc)))
       ((unless (and (eql char #\\)
                     (< (+ 1 index) (strlen x))))
        (preproc-legible-aux x (+ 1 index) (cons char acc)))
       (char2 (char x (+ 1 index)))
       ((when (member (char x (+ 1 index)) '(#\Newline #\Space #\Tab #\Return #\Page #\#)))
        (preproc-legible-aux x (+ 2 index) (cons char2 acc))))
    (preproc-legible-aux x (+ 2 index) (cons char2 (cons char acc))))
  ///
  (fty::deffixequiv preproc-legible-aux
    :hints (("goal" :induct t :expand ((:free (acc) (preproc-legible-aux x index acc))
                                       (:free (acc) (preproc-legible-aux (acl2::str-fix x) index acc))
                                       (:free (acc) (preproc-legible-aux x (nfix index) acc)))))))

(define preproc-legible ((x stringp))
  :returns (new-x stringp :rule-classes :type-prescription)
  (preproc-legible-aux x 0 nil))

(define parse ((pat stringp "The string to parse as a regular expression.")
               &key
               ((legible booleanp "Option to preprocess away non-escaped whitespace
                                   and Perl-style @('#') comments")
                't))
  :returns (mv (err acl2::maybe-stringp :rule-classes :type-prescription
                    "Parse error message")
               (regex (implies (not err) (regex-p regex))
                      "Regular expression object, if no error."))
  :parents (acre)
  :short "Parse a pattern string into a regular expression object."
  (b* ((preproc-pat (if legible (preproc-legible pat) (lstrfix pat))))
    (parse-regex preproc-pat)))
