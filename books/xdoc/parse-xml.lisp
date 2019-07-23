; XDOC Documentation System for ACL2
; Copyright (C) 2009-2015 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "XDOC")
(include-book "autolink")
(set-state-ok t)
(program)

; (PARSE-XML X) --> (MV ERR TOKENS)
;
; This is an extremely primitive XML lexer.  It is incomplete, doesn't support
; unicode, and probably is dead wrong as far as the XML standard is concerned.
; But, it's adequate for XDOC stuff.
;
; X should be an XML-formatted string (with no preprocessor stuff).  We break
; it into a list of tokens, which may be any of the following:
;
;    (:OPEN STR ALIST LOC) represents <tag [... atts ...]>
;
;       - STR is a string that is the tag name, e.g., "p" for <p>
;
;       - ALIST is an alist of the attribute.  Each entry is either:
;            (KEY-STR . VAL-STR)   for ordinary key="val" style atts
;            (KEY-STR . NIL)       for value-free atts like <hr noshade>
;
;       - LOC is semantically irrelevant.  It's the location of this
;         open token in the string, which can be useful for better
;         error messages about unbalanced strings.
;
;    (:CLOSE STR) represents </tag>
;
;       - STR is a string that is the tag name, e.g., "p" for </p>
;
;    (:TEXT STR) represents ordinary text
;
;       - STR is the contents of the text.  This is ordinary text with no
;         embedded tags or entities.
;
;    (:ENTITY TYPE) represents entities like &amp;
;
;      - TYPE is :AMP, :LT, :GT, :APOS, :NBSP, :NDASH, :MDASH, :RARR, LSQUO, RSQUO, LDQUO, or RDQUO

(defun opentok-p (x) (eq (first x) :OPEN))
(defun opentok-name (x) (second x))
(defun opentok-atts (x) (third x))
(defun opentok-loc (x) (fourth x))

(defun closetok-p (x) (eq (first x) :CLOSE))
(defun closetok-name (x) (second x))

(defun entitytok-p (x) (eq (first x) :ENTITY))
(defun entitytok-type (x) (second x))

(defun texttok-p (x) (eq (first x) :TEXT))
(defun mcflatten (x acc)
  (if (atom x)
      (cons x acc)
    (mcflatten (car x) (mcflatten (cdr x) acc))))
(defun texttok-texttree (x) (second x))
(defun texttok-text (x)
  (let ((tree (texttok-texttree x)))
    (if (atom tree) ;; optimization
        tree
      (str::fast-string-append-lst (mcflatten (texttok-texttree x) nil)))))

(defconst *nls* (coerce (list #\Newline) 'string))

(defun read-until (x n xl stop-chars acc)
  ;; Accumulate chars until one of the stop-chars is seen
  "Returns (MV FOUNDP N ACC)"
  (b* (((when (>= n xl))
        (mv nil n acc))
       (char-n (char x n))
       ((when (member char-n stop-chars))
        (mv t n acc)))
    (read-until x (+ 1 n) xl stop-chars (cons char-n acc))))

(defun read-name-aux (x n xl acc)
  ;; For attribute/tag names.  We just expect alphanumeric characters.  This is
  ;; probably horribly wrong as far as the XML spec is concerned, but should be
  ;; reasonable for all the tag and attribute names in xdoc.
  "Returns (MV N ACC)"
  (b* (((when (>= n xl))
        (mv n acc))
       (char-n (char x n))
       ((when (or (and (char<= #\a char-n) (char<= char-n #\z))
                  (and (char<= #\Z char-n) (char<= char-n #\Z))
                  (and (char<= #\0 char-n) (char<= char-n #\9))
                  (eql char-n #\_)
                  (eql char-n #\-)
                  ))
        (read-name-aux x (+ 1 n) xl (cons char-n acc))))
    (mv n acc)))

(defun read-name (x n xl)
  ;; Try to read an attribute/tag name at the current spot.
  "Returns (MV ERR N NAME-STR)"
  (b* (((mv n rchars)
        (read-name-aux x n xl nil))
       ((unless (consp rchars))
        (mv (str::cat "Expected a name, but found unexpected character "
                      (coerce (list (char x n)) 'string) *nls*
                      "Nearby text: {" (error-context x n xl) "}" *nls*)
            n nil))
       (str (str::rchars-to-string rchars)))
    (mv nil n str)))

(defun read-attrval (x n xl)
  ;; Try to read "value" or 'value' at the current spot.
  "Returns (MV ERR N VAL-STR)"
  (b* ((saved-n n)
       (quote-char (char x n))
       ((unless (or (eql quote-char #\")
                    (eql quote-char #\')))
        (mv (str::cat "Expected value to start with a quote, but found "
                      (coerce (list (char x n)) 'string) *nls*
                      "Nearby text: {" (error-context x n xl) "}" *nls*)
            n nil))
       (n (+ 1 n)) ;; eat the quote-char
       ((mv found-endp n chars)
        (read-until x n xl (list quote-char) nil))
       ((unless found-endp)
        (mv (str::cat "Attribute value never ends." *nls*
                      "Nearby text: {" (error-context x saved-n xl) "}" *nls*)
            n nil))
       (n (+ n 1)) ;; eat the closing quote-char
       (val-str (str::rchars-to-string chars)))
    (mv nil n val-str)))

(defun read-tag-attributes (x n xl tag-start-n atts)
  ;; Assumes "<foo" and perhaps some attributes have just been read.
  ;; Reads through the closing > or />, setting CLOSEP=T if we read />
  ;; as in <br/>.
  "Returns (MV ERR N ATTS CLOSEP)"
  (b* ((n (skip-past-ws x n xl))
       ((when (>= n xl))
        (mv (str::cat "Tag never closes." *nls*
                      "Nearby text: {" (error-context x tag-start-n xl) "}" *nls*)
            n nil nil))
       ((when (eql (char x n) #\>))
        ;; End of tag via >
        (mv nil (+ 1 n) atts nil))
       ((when (eql (char x n) #\/))
        ;; It had better be />.
        (b* ((n (+ 1 n))
             ((unless (and (< n xl)
                           (eql (char x n) #\>)))
              (mv (str::cat "Stray / in tag." *nls*
                            "Nearby text: {" (error-context x tag-start-n xl) "}" *nls*)
                  n nil nil)))
          (mv nil (+ 1 n) atts t)))
       ;; We should now be at the start of some new attribute.
       ((mv err n key1) (read-name x n xl))
       ((when err)
        (mv err n nil nil))
       (n (skip-past-ws x n xl))
       ((when (>= n xl))
        (mv (str::cat "Tag never closes." *nls*
                      "Nearby text: {" (error-context x tag-start-n xl) "}" *nls*)
            n nil nil))
       ((unless (eql (char x n) #\=))
        ;; I guess this is okay for things like "noshade" that don't have an
        ;; associated value.
        (read-tag-attributes x n xl tag-start-n (acons key1 nil atts)))
       (n (+ n 1)) ;; eat the =
       (n (skip-past-ws x n xl))
       ((mv err n val1) (read-attrval x n xl))
       ((when err)
        (mv err n nil nil)))
    (read-tag-attributes x n xl tag-start-n (acons key1 val1 atts))))

(defun read-close-tag (x n xl)
  ;; Assumes </ has just been read.
  ;; Reads through the closing >.
  "Returns (MV ERR N TOKEN-LIST)"
  (b* ((saved-n n)
       (n (skip-past-ws x n xl))
       ((mv err n name) (read-name x n xl))
       ((when err)
        (mv err n nil))
       (n (skip-past-ws x n xl))
       ((unless (and (< n xl)
                     (eql (char x n) #\>)))
        (mv (str::cat "Invalid closing tag." *nls*
                      "Nearby text: {" (error-context x saved-n xl) "}" *nls*)
            n nil))
       (n (+ 1 n)) ;; eat the final >
       (close (list :CLOSE name)))
    (mv nil n (list close))))

(defun skip-declaration (x n xl start-n)
  ;; Read through ?>
  "Returns (MV ERR N NIL)"
  (b* (((when (>= (+ 1 n) xl))
        (mv (str::cat "<? ... ?> declaration never closes." *nls*
                      "Nearby text: {" (error-context x start-n xl) "}" *nls*)
            n nil))
       ((unless (and (eql (char x n) #\?)
                     (eql (char x (+ n 1)) #\>)))
        (skip-declaration x (+ n 1) xl start-n)))
    (mv nil (+ n 2) nil)))

(defun skip-entity-stuff (x n xl start-n)
  ;; Read through ]>
  "Returns (MV ERR N NIL)"
  (b* (((when (>= (+ 1 n) xl))
        (mv (str::cat "<! ... ]> declaration never closes." *nls*
                      "Nearby text: {" (error-context x start-n xl) "}" *nls*)
            n nil))
       ((unless (and (eql (char x n) #\])
                     (eql (char x (+ n 1)) #\>)))
        (skip-entity-stuff x (+ n 1) xl start-n)))
    (mv nil (+ n 2) nil)))

(defun read-tag (x n xl)
  ;; Assumes (char x n) is "<"
  "Returns (MV ERR N TOKEN-LIST)"
  (b* ((tag-start-n n)
       (n (+ 1 n))
       (n (skip-past-ws x n xl))
       ((when (>= n xl))
        (mv (str::cat "Tag never closes." *nls*
                      "Nearby text: {" (error-context x tag-start-n xl) "}" *nls*)
            n nil))
       ((when (eql (char x n) #\?))
        (skip-declaration x n xl tag-start-n))
       ((when (eql (char x n) #\!))
        (skip-entity-stuff x n xl tag-start-n))
       ((when (eql (char x n) #\/))
        (read-close-tag x (+ 1 n) xl))
       ;; Else, it's an opening tag.  This should be its name.
       ((mv err n name)
        (read-name x n xl))
       ((when err)
        (mv err n nil))
       ((mv err n atts closep)
        (read-tag-attributes x n xl tag-start-n nil))
       ((when err)
        (mv err n nil))
       (open (list :OPEN name (reverse atts) tag-start-n))
       ((when (not closep))
        (mv nil n (list open)))
       (close (list :CLOSE name)))
    (mv nil n (list open close))))

(defun read-entity (x n xl)
  ;; Assumes (char x n) is "&"
  "Returns (MV ERR N TOK)"
  (b* ((saved-n n)
       (n (+ 1 n)) ;; eat the &
       ((mv foundp n rchars)
        (read-until x n xl (list #\;) nil))
       ((unless foundp)
        (mv (str::cat "Entity does not have a closing semicolon." *nls*
                      "Nearby text: {" (error-context x saved-n xl) "}" *nls*)
            n nil))
       (n (+ 1 n)) ;; eat the ;
       (str (str::rchars-to-string rchars))
       ((when (equal str "amp"))  (mv nil n '(:ENTITY :AMP)))
       ((when (equal str "lt"))   (mv nil n '(:ENTITY :LT)))
       ((when (equal str "gt"))   (mv nil n '(:ENTITY :GT)))
       ((when (equal str "quot")) (mv nil n '(:ENTITY :QUOT)))
       ((when (equal str "apos")) (mv nil n '(:ENTITY :APOS)))
       ((when (equal str "nbsp")) (mv nil n '(:ENTITY :NBSP)))
       ((when (equal str "ndash")) (mv nil n '(:ENTITY :NDASH)))
       ((when (equal str "mdash")) (mv nil n '(:ENTITY :MDASH)))
       ((when (equal str "rarr")) (mv nil n '(:ENTITY :RARR)))
       ((when (equal str "lsquo")) (mv nil n '(:ENTITY :LSQUO)))
       ((when (equal str "rsquo")) (mv nil n '(:ENTITY :RSQUO)))
       ((when (equal str "ldquo")) (mv nil n '(:ENTITY :LDQUO)))
       ((when (equal str "rdquo")) (mv nil n '(:ENTITY :RDQUO)))
       )
    (mv (str::cat "Unsupported entity: &" str ";" *nls*
                  "Nearby text: {" (error-context x saved-n xl) "}" *nls*)
        n nil)))

(defun parse-xml-aux (x n xl acc)
  "Returns (MV ERR TOKENS)"
  (b* (((when (>= n xl))
        (mv nil acc))
       (char-n (char x n))
       ((when (eql char-n #\<))
        ;; Open/closing tag
        (b* (((mv err n token-list) (read-tag x n xl))
             ((when err)
              (mv err nil))
             (acc (revappend token-list acc)))
          (parse-xml-aux x n xl acc)))
       ((when (eql char-n #\&))
        ;; Entity
        (b* (((mv err n token) (read-entity x n xl))
             ((when err)
              (mv err nil)))
          (parse-xml-aux x n xl (cons token acc))))
       ((when (eql char-n #\>))
        (mv (str::cat "Stray end-of-tag character '>'" *nls*
                      "Nearby text: {" (error-context x n xl) "}" *nls*)
            nil))
       ;; Otherwise, plain text.
       ((mv ?foundp n rchars)
        (read-until x n xl '(#\< #\& #\>) nil))
       (token (list :TEXT (str::rchars-to-string rchars))))
    (parse-xml-aux x n xl (cons token acc))))


; Basic tag balance checking with nice error reporting


(defun entitytok-as-entity (x)
  (case (entitytok-type x)
    (:AMP   "&amp;")
    (:LT    "&lt;")
    (:GT    "&gt;")
    (:QUOT  "&quot;")
    (:APOS  "&apos;")
    (:NBSP  "&nbsp;")
    (:NDASH "&ndash;")
    (:MDASH "&mdash;")
    (:RARR  "&rarr;")
    (:LSQUO "&lsquo;")
    (:RSQUO "&rsquo;")
    (:LDQUO "&ldquo;")
    (:RDQUO "&rdquo;")))

(defun entitytok-as-plaintext (x)
  (case (entitytok-type x)
    (:AMP   "&")
    (:LT    "<")
    (:GT    ">")
    (:QUOT  "\"")
    (:APOS  "'")
    (:NBSP  " ")
    (:NDASH "--")
    (:MDASH "---")
    (:RARR  "-->")
    (:LSQUO "`")
    (:RSQUO "'")
    (:LDQUO "``")
    (:RDQUO "''")))

(defun flatten-token-for-errormsg (x)
  (cond ((opentok-p x)
         (str::cat "<" (opentok-name x)
                   (if (opentok-atts x) " [...]>" ">")))
        ((closetok-p x)
         (str::cat "</" (closetok-name x) ">"))
        ((entitytok-p x)
         (entitytok-as-entity x))
        ((texttok-p x)
         (texttok-text x))
        (t
         (er hard? 'flatten-token-for-errormsg "Invalid token ~x0" x))))

(defun flatten-tokens-for-errormsg (x)
  (if (atom x)
      ""
    (str::cat (flatten-token-for-errormsg (car x))
              (flatten-tokens-for-errormsg (cdr x)))))


(defun nearby-text (index str)
  (let* ((strlen (length str))
         (start index)
         (stop   (min strlen (+ index 60))))
    (str::cat (substitute #\Space #\Newline (subseq str start stop))
              (if (equal stop strlen) "" "..."))))

(defun open-tag-backtrace-entry (orig-str open-tok)
  (declare (type string orig-str))
  (let* ((n          (opentok-loc open-tok))
         (name       (opentok-name open-tok))
         (name-len   (length name))
         (spaces-len (max 0 (- 6 name-len)))
         (pad        (coerce (make-list spaces-len :initial-element #\Space) 'string))
         (nearby     (nearby-text n orig-str)))
    (str::cat "   <" name "> " pad nearby *nls*)))

(defun open-tags-backtrace (orig-str open-tags)
  (if (atom open-tags)
      ""
    (str::cat (open-tag-backtrace-entry orig-str (car open-tags))
              (open-tags-backtrace orig-str (cdr open-tags)))))

(defun find-tag-imbalance (x open-tags loc)
  "Returns (MV ERROR/NIL LOC/NIL STILL-OPEN-TAGS/NIL)"
  (b* (((when (atom x))
        (if open-tags
            (mv (str::cat (opentok-name (car open-tags)) " tag is never closed.")
                loc open-tags)
          (mv nil nil nil)))
       ((when (opentok-p (car x)))
        (find-tag-imbalance (cdr x) (cons (car x) open-tags) (+ 1 loc)))
       ((when (closetok-p (car x)))
        (b* ((close-name (closetok-name (car x)))
             ((unless (consp open-tags))
              (mv (str::cat "Found </" close-name "> with no matching opening tag.")
                  loc open-tags))
             (open-name (opentok-name (car open-tags)))
             ((unless (equal close-name open-name))
              (mv (str::cat "Found <" open-name "> with mismatched </" close-name ">.")
                  loc open-tags)))
          (find-tag-imbalance (cdr x) (cdr open-tags) (+ 1 loc)))))
    (find-tag-imbalance (cdr x) open-tags (+ 1 loc))))

(defun parse-xml (x)
  (declare (type string x))
  (b* (((mv err rtokens) (parse-xml-aux x 0 (length x) nil))
       ((when err)
        (mv err nil))
       (tokens (reverse rtokens))
       ((mv err loc open-tags) (find-tag-imbalance tokens nil 0))
       ((when err)
        (b* (((when (not loc))
              (mv err nil))
             (back-one  (max 0 (- loc 4)))
             (start-ctx (nthcdr back-one tokens))
             (context   (take (min 8 (len start-ctx)) start-ctx))
             (nearby    (flatten-tokens-for-errormsg context)))
          (mv (str::cat err *nls* "Nearby text: {" nearby "}" *nls* *nls*
                        (if open-tags
                            (str::cat "Open tags stack:" *nls*
                                      (open-tags-backtrace x (reverse open-tags)))
                          ""))
              nil))))
    (mv err tokens)))
