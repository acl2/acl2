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
; Mods to merge-text (and callers) made 5/2016 by Matt Kaufmann.

(in-package "XDOC")
(include-book "prepare-topic")
(include-book "spellcheck")
(include-book "word-wrap")
(include-book "defxdoc-raw") ; for xdoc::all-xdoc-topics
(include-book "std/strings/fast-cat" :dir :system)
(set-state-ok t)
(program)


; Implements the :xdoc command for printing xdoc topics to the terminal.
;
; The basic approach is:
;   1. preprocess the topic using the ordinary preprocessor (see save.lisp)
;   2. parse the resulting xml string into a list of tokens (see parse-xml.lisp)
;   3. transform the token list into reasonably nice plain-text
;   4. print the text to the terminal
;
; Loading this file does not require a ttag.  However, actually using the :xdoc
; command incurs a ttag by loading the defxdoc-raw book.  Of course, this is
; typically not a problem since you only use :xdoc in interactive sessions, and
; not while certifying books.



; MERGE-TEXT eats any "throwaway tags" that we can't support in a terminal,
; normalizes whitespace throughout text nodes, and merges any adjacent text
; nodes.

(defconst *throwaway-tags*
  ;; We leave "img" and "icon" in this list even thouggh we process them in
  ;; merge-text below, because we don't want to process </img> or </icon>.
  (list "b" "i" "u" "tt" "v" "em" "color" "sf" "box" "img" "icon"
        "page"
        ;; We'll just render mathfrag formulas without any special marks
        "mathfrag"
        ))

(defun topic-to-rendered (topic topic-to-rendered-table)

; E.g., (topic-to-rendered "ACL2____About_02Types" <table>)
; = "About_Types", where <table> is
; (cdr (acl2::f-get-global 'topic-to-rendered-pair state)).
; Note that rendered does not have a package prefix.

  (cdr (hons-get (intern topic "ACL2") topic-to-rendered-table)))

(defun text-matches-mangle (text mangle topic-to-rendered-table)

; Text is xdoc source text ending with text of the form "[topic" (with a
; closing right bracket not included, but implicit) and mangle is corresponding
; mangled text.  We return:

; t, if it's appropriate to render the text as "[topic]";
; (list "[topic']"), if it's appropriate to render the text as "[topic']";
; "topic'", if it's appropriate to render the text as "topic (see [topic']);
; nil otherwise.

; Examples:

; ; Simple example:
;   (text-matches-mangle "See [nth" "COMMON-LISP____NTH" <table>)
;   = t

; ; More challenging -- need to unmangle the topic,
; ; which might come from
; ; "<p>See <see topic='@(url <<)'>discussion of double-lt</see>.</p>":
;   (text-matches-mangle "See [discussion of double-lt" "ACL2_____C3_C3" <table>)
;   = "<<"

;   (text-matches-mangle
;    "We assume you've read about [rewriting"
;    "ACL2____LOGIC-KNOWLEDGE-TAKEN-FOR-GRANTED-REWRITING"
;    <table>)
;   = "LOGIC-KNOWLEDGE-TAKEN-FOR-GRANTED-REWRITING"

; Note that the one just above could come from processing the xdoc string:

;   "<p>We assume you've read about <see topic='@(url
;    LOGIC-KNOWLEDGE-TAKEN-FOR-GRANTED-REWRITING)'>rewriting</see>.</p>"

; As the examples above illustrate, we return t when it's appropriate to print
; [topic], else a one-element list ("foo::topic"), else a string when the topic
; reference is to that string, but nil when we can't find the topic or (though
; perhaps impossible) can't find the expected bracket.

; Unfortunately, we don't handle everything -- we just try to handle almost
; everything and to do something reasonable in any case.  Consider the
; following:

;   (defxdoc foo
;     :parents (acl2)
;     :long "<p>See <see topic='@(url <<)'>double-lt</see>.</p>")

; Then :doc foo gives us "See double-lt.", because we can't retrieve the <<
; from its mangled URL -- unless we first evaluate (include-book
; "misc/total-order" :dir :system).  Then we get this, as desired.

;    See double-lt (see [<<]).

  (let* ((bracket-posn (search "[" text :from-end t))
         (start (and bracket-posn
                     (1+ bracket-posn)))
         (rendered (and start ; optimization
                        (topic-to-rendered mangle topic-to-rendered-table))))
    (cond
     ((or (null start) (null rendered))
      nil)
     (t
      (let* ((text-topic0 (subseq text start (length text)))
             (acl2-prefix-posn (search "acl2::" text-topic0 :test 'char-equal))
             (text-topic ; transform acl2::foo into foo

; We take measures to deal with the case that text-topic0 has an "acl2" prefix,
; e.g., "acl2::foo" or "ACL2::foo".  We don't hit that issue when printing the
; manual; we only hit it when printing documentation at the terminal.  That's
; because, for example @(see acl2::foo) somehow doesn't generate acl2::foo when
; the defxdoc form is submitted in the "ACL2" package, as it is when generating
; the acl2-doc manual.  Rather than figure out how to deal with that in the
; preprocessor or some other earlier place (and carefully, since we don't want
; to mess up the online manual, where defxdoc forms are submitted in their
; original package), we handle it here.

              (if acl2-prefix-posn
                  (subseq text-topic0 6 (length text-topic0))
                text-topic0)))
        (cond
         ((string-equal rendered text-topic)
          (if acl2-prefix-posn ; then return cleaned-up text-topic
              (list text-topic)
            t))
         (t
          (let ((posn (search "::" rendered)))
            (cond
             ((and posn
                   (string-equal (subseq rendered (+ posn 2) (length rendered))

; We could probably use text-topic here and below, and get the same result,
; since presumably rendered does not have an "acl2::" prefix.

                                 text-topic0))
              (list (concatenate 'string
                                 (acl2::string-downcase
                                  (subseq rendered 0 (+ posn 2)))
                                 text-topic0)))
             (t rendered))))))))))

(defun fix-close-see (str bracket-posn match)

; Match is either a string, a list containing a string, or nil, as returned by
; text-matches-mangle.

  (cond ((null bracket-posn) str)
        ((null match) ; remove the bracket
         (concatenate 'string
                      (subseq str 0 bracket-posn)
                      (subseq str (1+ bracket-posn) (length str))))
        ((stringp match)
         (concatenate 'string
                      (subseq str 0 bracket-posn)
                      (subseq str (1+ bracket-posn) (length str))
                      " (see ["
                      match
                      "])"))
        (t ; match is a one-element list containing the desired string
         (assert$ (consp match)
                  (concatenate 'string
                               (subseq str 0 (1+ bracket-posn))
                               (car match)
                               "]")))))

; This variable can be modified here or by the user.  It is an alist so that
; for every tag TAG for which <TAG>...</TAG> is to be replaced by text TEXT,
; the alist contains the entry (TAG . TEXT).
(make-event (pprogn (f-put-global 'xdoc-tag-elide-alist
                                  '(("stv" . "{STV display}"))
                                  state)
                    (value '(value-triple t)))
            :check-expansion t)

(defun skip-to-close (tag x)
  (cond ((atom x)
         x)
        (t (b* ((tok1 (car x))
                (name (and (closetok-p tok1)
                           (closetok-name tok1))))
             (cond ((equal name tag)
                    (cdr x))
                   (t (skip-to-close tag (cdr x))))))))

(defun translate-entities-to-plaintext-aux (x n xl acc)
  "Returns (MV ERR ACC)"
  (b* (((when (>= n xl))
        (mv nil acc))
       (char1 (char x n))
       ((when (eql char1 #\&))
        (b* (((mv err n tok)
              (read-entity x n xl))
             ((when err)
              (mv err nil))
             (plaintext (entitytok-as-plaintext tok))
             (acc (str::revappend-chars plaintext acc)))
          (translate-entities-to-plaintext-aux x n xl acc)))
       (acc (cons char1 acc)))
    (translate-entities-to-plaintext-aux x (+ 1 n) xl acc)))

(defun translate-entities-to-plaintext (x)
  "Returns (MV ERR PLAINTEXT-STR)"
  (b* (((mv err acc)
        (translate-entities-to-plaintext-aux x 0 (length x) nil)))
    (mv err (str::rchars-to-string acc))))

(defun translate-att-to-plaintext (ctx x)
  (b* (((mv err text) (translate-entities-to-plaintext x))
       ((when err)
        (er hard? 'translate-att-to-plaintext "Error in ~s0: ~s1~%" ctx err)
        ""))
    text))

(defun merge-text (x acc codes href topic-to-rendered-table
                     xdoc-tag-elide-alist)
  ;; CODES is number of open <code> tags -- we don't normalize whitespace
  ;; within them, but entities still get converted.
  (b* (((when (atom x))
        acc)
       (tok1 (car x))
       (rest (cdr x))
       ((when (opentok-p tok1))
        (b* ((name (opentok-name tok1))
             (codes (if (equal name "code")
                        (+ 1 codes)
                      codes)))
          (cond ((equal name "img")
                 (b* ((tok  (list :TEXT "{IMAGE}")))
                   (merge-text (cons tok rest) acc codes href
                               topic-to-rendered-table
                               xdoc-tag-elide-alist)))
                ((equal name "icon")
                 (b* ((tok  (list :TEXT "{ICON}")))
                   (merge-text (cons tok rest) acc codes href
                               topic-to-rendered-table
                               xdoc-tag-elide-alist)))
                ((member-equal name *throwaway-tags*)
                 (merge-text rest acc codes nil topic-to-rendered-table
                             xdoc-tag-elide-alist))
                ((equal name "a")
                 (b* ((href (cdr (assoc-equal "href" (opentok-atts tok1))))
                      (tok  (list :TEXT (str::cat "{"))))
                   (merge-text (cons tok rest) acc codes href
                               topic-to-rendered-table
                               xdoc-tag-elide-alist)))
                ((equal name "see")
                 (b* ((href (or
; It's probably rare or impossible to have a <see> within an <a href...>, but
; if that happens then we just keep the existing href, expecting that when we
; close <see> we will not do the desired optimization of simply printing
; [nice-topic-name].
                             href
                             (cdr (assoc-equal "topic"
                                               (opentok-atts tok1)))))
                      (tok  (list :TEXT "[")))
                   (merge-text (cons tok rest) acc codes href
                               topic-to-rendered-table
                               xdoc-tag-elide-alist)))
                ((equal name "srclink")
                 (b* ((tok  (list :TEXT "<")))
                   (merge-text (cons tok rest) acc codes href
                               topic-to-rendered-table
                               xdoc-tag-elide-alist)))
                (t
                 (let ((pair (assoc-equal name xdoc-tag-elide-alist)))
                   (cond
                    (pair (b* ((tok (list :TEXT (cdr pair))))
                            (merge-text (cons tok (skip-to-close name x))
                                        acc codes href
                                        topic-to-rendered-table
                                        xdoc-tag-elide-alist)))
                    (t (merge-text rest (cons tok1 acc) codes href
                                   topic-to-rendered-table
                                   xdoc-tag-elide-alist))))))))
       ((when (closetok-p tok1))
        (b* ((name  (closetok-name tok1))
             (codes (if (equal name "code")
                        (- 1 codes)
                      codes)))
          (cond ((member-equal name *throwaway-tags*)
                 (merge-text rest acc codes href topic-to-rendered-table
                             xdoc-tag-elide-alist))
                ((member-equal name '("see"))
                 (b* ((text (texttok-text (car acc)))
                      (bracket-posn (search "[" text :from-end t))
                      (match
                       (assert$
                        bracket-posn
                        (and href
                             (consp acc)
                             (texttok-p (car acc))
                             (text-matches-mangle text href
                                                  topic-to-rendered-table)))))
                   (cond
                    ((eq match t)
                     (let ((tok (list :TEXT "]")))
                       (merge-text (cons tok rest) acc codes nil
                                   topic-to-rendered-table
                                   xdoc-tag-elide-alist)))
                    (t (merge-text
                        rest
                        (cons (list :text
                                    (fix-close-see text bracket-posn match))
                              (cdr acc))
                        codes nil topic-to-rendered-table
                        xdoc-tag-elide-alist)))))
                ((member-equal name '("a"))
                 (let* ((href-plain (if href
                                        (translate-att-to-plaintext 'href href)
                                      ""))
                        (tok (list :TEXT (str::cat " | " href-plain "}"))))
                   (merge-text (cons tok rest) acc codes nil
                               topic-to-rendered-table
                               xdoc-tag-elide-alist)))
                ((equal name "srclink")
                 (let ((tok (list :TEXT ">")))
                   (merge-text (cons tok rest) acc codes href
                               topic-to-rendered-table
                               xdoc-tag-elide-alist)))
                (t
                 (merge-text rest (cons tok1 acc) codes href
                             topic-to-rendered-table
                             xdoc-tag-elide-alist)))))
       (tok1
        ;; Goofy.  Convert any entities into ordinary text.  Normalize
        ;; whitespace for any non-code tokens.
        (cond ((entitytok-p tok1)
               (list :TEXT (entitytok-as-plaintext tok1)))
              ((zp codes)
               ;; NOT in a <code> block, so normalize ws.
               (list :TEXT (normalize-whitespace (texttok-text tok1))))
              (t
               ;; Inside a <code> block, so don't touch ws.
               tok1)))
       ((unless (texttok-p (car acc)))
        (merge-text rest (cons tok1 acc) codes href topic-to-rendered-table
                    xdoc-tag-elide-alist))

       (merged-tok (list :TEXT (cons (texttok-texttree (car acc))
                                     (texttok-texttree tok1)))))
    (merge-text rest (cons merged-tok (cdr acc)) codes href
                topic-to-rendered-table
                xdoc-tag-elide-alist)))

(defun has-tag-above (tag open-tags)
  (if (atom open-tags)
      nil
    (or (equal tag (opentok-name (car open-tags)))
        (has-tag-above tag (cdr open-tags)))))

(defun get-indent-level (open-tags)
  (b* (((when (atom open-tags))
        0)
       (name (opentok-name (car open-tags)))
       ((when (member-equal name '("h1" "h2" "h3")))
        0)
       ((when (member-equal name '("p" "short" "h4" "h5" "index_entry")))
        (+ 2 (get-indent-level (cdr open-tags))))
       ((when (member-equal name '("index_body")))
        (+ 4 (get-indent-level (cdr open-tags))))
       ((when (member-equal name '("ol" "ul")))
        ;; Note: the bullet is put into the indented space, so in practice
        ;; an indent-level of 6 is more like an indent-level of 3.
        (if (has-tag-above "li" open-tags)
            (+ 4 (get-indent-level (cdr open-tags)))
          (+ 6 (get-indent-level (cdr open-tags)))))
       ((when (equal name "dt"))
        (+ 4 (get-indent-level (cdr open-tags))))
       ((when (equal name "dd"))
        (+ 6 (get-indent-level (cdr open-tags))))
       ((when (equal name "code"))
        (+ 4 (get-indent-level (cdr open-tags))))
       ((when (equal name "math"))
        (+ 4 (get-indent-level (cdr open-tags))))
       ((when (equal name "blockquote"))
        (+ 4 (get-indent-level (cdr open-tags))))
       ((when (member-equal name '("table")))
        (+ 4 (get-indent-level (cdr open-tags)))))
    (get-indent-level (cdr open-tags))))

(defun get-list-type (open-tags)
  (b* (((when (atom open-tags))
        ;; arbitrary default
        :bulleted)
       (name (opentok-name (car open-tags)))
       ((when (equal name "ol"))
        :numbered)
       ((when (equal name "ul"))
        :bulleted))
    (get-list-type (cdr open-tags))))

(defun auto-indent (acc open-tags)
  (append (make-list (get-indent-level open-tags)
                     :initial-element #\Space)
          acc))

(defun maybe-newline (acc)
  ;; Make sure there is a newline at the start of acc.
  (b* ((acc (remove-spaces-from-front acc))
       (acc (if (or (atom acc)
                    (eql (car acc) #\Newline))
                acc
              (cons #\Newline acc))))
    acc))

(defun maybe-doublespace (acc)
  ;; Make sure there are two newlines at the start of acc.
  (b* ((acc (remove-spaces-from-front acc))
       ((when (atom acc))
        ;; Nothing at all, don't insert anything
        acc)
       ((unless (eql (car acc) #\Newline))
        ;; No newlines at all -- insert two of them.
        (list* #\Newline #\Newline acc))
       ;; At least one newline.  Let's eat it and see what's further on.
       (acc (remove-spaces-from-front (cdr acc)))
       ((when (atom acc))
        ;; Nothing at all, don't insert anything.
        acc)
       ((unless (eql (car acc) #\Newline))
        ;; No second newline.  So since we've eaten the only newline
        ;; there was, insert two newlines.
        (list* #\Newline #\Newline acc)))
  ;; Found the second newline, so just restore the first one.
  (cons #\Newline acc)))

(defun maybe-triplespace (acc)
  ;; Make sure there are three newlines at the start of acc.
  (b* ((acc (remove-spaces-from-front acc))
       ((when (atom acc)) acc)
       ((unless (eql (car acc) #\Newline))
        (list* #\Newline #\Newline #\Newline acc))

       ;; Eat newline #1
       (acc (remove-spaces-from-front (cdr acc)))
       ((when (atom acc)) acc)
       ((unless (eql (car acc) #\Newline))
        (list* #\Newline #\Newline #\Newline acc))

       ;; Eat newline #2
       (acc (remove-spaces-from-front (cdr acc)))
       ((when (atom acc)) acc)
       ((unless (eql (car acc) #\Newline))
        (list* #\Newline #\Newline #\Newline acc)))

    (list* #\Newline #\Newline acc)))

(defun prepend-each-line (spaces x n xl acc)
  (b* (((when (>= n xl))
        acc)
       (char-n (char x n))
       ((unless (eql char-n #\Newline))
        (prepend-each-line spaces x (+ 1 n) xl (cons char-n acc)))
       ;; Else, a newline.  delete trailing whitespace
       (acc (remove-spaces-from-front acc))
       (acc (cons #\Newline acc))
       (acc (append spaces acc)))
    (prepend-each-line spaces x (+ 1 n) xl acc)))

(defun tokens-to-terminal
  (tokens    ;; the tokens to print
   wrap-col  ;; the goal column for word-wrap
   open-tags ;; currently open tags
   list-nums ;; stack of current element numbers for list printing
   acc       ;; accumulator for output characters (in reverse order)
   )
  (b* (((when (atom tokens))
        acc)
       (tok1 (car tokens))
       (rest (cdr tokens))

       ((when (opentok-p tok1))
        (b* ((name (opentok-name tok1))
             (open-tags (cons tok1 open-tags))
             (list-nums (cond
                         ((member-equal name '("ol" "ul"))
                          (cons 0 list-nums))
                         ((equal name "li")
                          (cons (+ 1 (nfix (car list-nums)))
                                (cdr list-nums)))
                         (t
                          list-nums)))
             (acc (cond
                   ;; ((equal name "parent")
                   ;;  (b* ((acc (maybe-newline acc))
                   ;;       (acc (str::revappend-chars "Parent: " acc)))
                   ;;    acc))
                   ((equal name "li")
                    (b* ((bullet (if (eq (get-list-type open-tags) :bulleted)
                                     "* "
                                   (str::cat (str::nat-to-dec-string (nfix (car list-nums))) ". ")))
                         (bullet-len (length bullet))
                         (desired    (get-indent-level open-tags))
                         (spaces  (make-list (nfix (- desired bullet-len))
                                             :initial-element #\Space))
                         (acc     (maybe-newline acc))
                         (acc     (append spaces acc))
                         (acc     (str::revappend-chars bullet acc)))
                      acc))
                   ((member-equal name '("h4" "h5" "p" "li" "dt" "dd" "br"
                                         "index_head" "index_body" "blockquote"))
                    ;; This kind of tag has some level of indenting associated
                    ;; with it, so make sure we indent over to the right level.
                    (auto-indent (maybe-newline acc) open-tags))
                   ((member-equal name '("code" "math" "short" "long"))
                    (auto-indent (maybe-doublespace acc) open-tags))
                   ((member-equal name '("h1" "h2" "h3"))
                    (auto-indent (maybe-triplespace acc) open-tags))
                   ((member-equal name '("table"))
                    (auto-indent (maybe-newline acc) open-tags))
                   ((equal name "index")
                    (b* ((atts  (opentok-atts tok1))
                         (title (cdr (assoc-equal "title" atts)))
                         (title (if (stringp title) title "??? title ???"))
                         (acc   (maybe-triplespace acc))
                         (acc   (str::revappend-chars title acc))
                         (acc   (maybe-doublespace acc)))
                      acc))
                   (t
                    acc))))
          (tokens-to-terminal rest wrap-col open-tags list-nums acc)))

       ((when (closetok-p tok1))
        (b* ((name (closetok-name tok1))
             (open-tags (cdr open-tags))
             (list-nums (if (member-equal name '("ol" "ul"))
                            (cdr list-nums)
                          list-nums))
             (acc (cond
                   ((member-equal name '("h1" "h2" "h3" "h4" "h5" "p" "dl" "ul" "ol"
                                         "short" "code" "math" "index" "index_body"
                                         "blockquote" "table"))
                    (auto-indent (maybe-doublespace acc) open-tags))
                   ((member-equal name '("li" "dd" "dt" "index_head" "tr"))
                    (auto-indent (maybe-newline acc) open-tags))
                   ((member-equal name '("td" "th"))
                    (list* #\Space #\Space #\| #\Tab acc))
                   (t
                    acc))))
          (tokens-to-terminal rest wrap-col open-tags list-nums acc)))

       ;; Else, it should be a text token.
       ;; We assume we are already indented to the right level.
       ;; BOZO handle <code> correctly.
       (text (texttok-text tok1))

       (codep (has-tag-above "code" open-tags))
       (level (get-indent-level open-tags))
       (acc (if codep
                (b* ((len (length text))
                     (starts-with-newline-p (and (> len 0)
                                                 (eql (char text 0) #\Newline)))
                     (start-from (if starts-with-newline-p
                                     1
                                   0)))
                  (prepend-each-line (make-list level :initial-element #\Space)
                                     text start-from (length text) acc))
              (let ((wrapped (word-wrap-paragraph text level wrap-col)))
                (str::revappend-chars wrapped acc)))))
    (tokens-to-terminal rest wrap-col open-tags list-nums acc)))


(defun revappend-full-symbol (sym ans)
  (b* ((ans (str::revappend-chars (symbol-package-name sym) ans))
       (ans (str::revappend-chars "::" ans))
       (ans (str::revappend-chars (symbol-name sym) ans)))
    ans))

(defun revappend-parents (parents ans)
  (b* (((when (atom parents))
        ans)
       ((when (atom (cdr parents)))
        (revappend-full-symbol (car parents) ans))
       (ans (revappend-full-symbol (car parents) ans))
       (ans (if (consp (cddr parents))
                (str::revappend-chars ", " ans)
              (str::revappend-chars " and " ans))))
    (revappend-parents (cdr parents) ans)))

(defun render-sym (sym)
  (let ((str (symbol-name sym)))
    (if (eq (intern str "ACL2") sym)
        (rendered-name str)
      (concatenate 'string
                   (symbol-package-name sym)
                   "::"
                   (rendered-name str)))))

(defun acl2-broken-links-alist-to-rendered-table-init (alist acc)
  (cond ((endp alist) acc)
        (t (acl2-broken-links-alist-to-rendered-table-init
            (cdr alist)
            (acons (intern (url (caar alist)) "ACL2")
                   (render-sym (caar alist))
                   acc)))))

(defun topic-to-rendered-table-init-1 (table acc)

; E.g., given the :name |About Types| in table (which is the cdr of the value
; of state global 'xdoc::topic-to-rendered-pair), map the symbol
; acl2::|ACL2____About_02Types| to the string "About_Types".

  (cond ((endp table) acc)
        (t (topic-to-rendered-table-init-1
            (cdr table)
            (let ((name (cdr (assoc-eq :name (car table)))))
              (acons (intern (url name) "ACL2")
                     (render-sym name)
                     acc))))))

(defun topic-to-rendered-table-init (state)
  (let ((pair (and (acl2::f-boundp-global 'topic-to-rendered-pair
                                          state)
                   (acl2::f-get-global 'topic-to-rendered-pair
                                       state))))
    (acl2::er-let*
     ((table (all-xdoc-topics state)))
     (cond ((equal (car pair) table)
            (value (cdr pair)))
           (t (prog2$ (and pair (fast-alist-free (cdr pair)))

; Skip the broken-links-alist if it's not defined.

                      (let* ((cval (acl2::defined-constant
                                    'acl2::*acl2-broken-links-alist* (w state)))
                             (alist0
                              (assert$
                               (or (null cval)
                                   (quotep cval))
                               (acl2-broken-links-alist-to-rendered-table-init
                                (unquote cval) nil)))
                             (fal
                              (make-fast-alist (topic-to-rendered-table-init-1
                                                table alist0)))
                             (state
                              (f-put-global 'topic-to-rendered-pair
                                            (cons table fal)
                                            state)))
                        (value fal))))))))

(defun topic-to-text (x all-topics state)
  "Returns (MV TEXT STATE)"
  (b* ((name (cdr (assoc :name x)))
;       (- (cw "Preprocessing...~%"))
       ;; Use NIL as the topics-fal as a simple way to suppress autolinks...
       (topics-fal (topics-fal all-topics))
       ((mv text state)
        (preprocess-topic
         (acons :parents nil x) ;; horrible hack so we can control this better
         all-topics topics-fal
         t ;; disable-autolinking to avoid auto links in text-mode code
         state))
       (- (fast-alist-free topics-fal))
;       (- (cw "Text is ~x0.~%" text))
;       (- (cw "Parsing xml...~%"))
       ((mv err tokens) (parse-xml text))
;       (- (cw "Checking result...~%"))
       ((when err)
        ;; Don't consult XDOC-VERBOSE-P here.  The user has explicitly asked to
        ;; be shown this topic but we can't show it to them.  They need to be
        ;; told why.
        (mv (str::cat "Error displaying xdoc topic: " *nls* *nls* err *nls* *nls*)
            state))
;       (- (cw "Tokens are ~x0.~%" tokens))
;       (- (cw "Merging tokens...~%"))
       ((mv err topic-to-rendered-table state)
        (topic-to-rendered-table-init state))
       ((when err)
        (mv (str::cat "Error displaying xdoc topic: " *nls* *nls* err *nls* *nls*)
            state))
       (merged-tokens
        (reverse (merge-text tokens nil 0 nil
                             topic-to-rendered-table
                             (f-get-global 'xdoc-tag-elide-alist state))))
;       (- (cw "Merged tokens are ~x0.~%" merged-tokens))
       (terminal (str::rchars-to-string
                  (tokens-to-terminal merged-tokens 70 nil nil nil)))

       (ans nil)
       (ans (str::revappend-chars (symbol-package-name name) ans))
       (ans (str::revappend-chars "::" ans))
       (ans (str::revappend-chars (symbol-name name) ans))
       (from  (cdr (assoc :from x)))
       (ans (if from
                (b* ((ans (str::revappend-chars " -- " ans))
                     (ans (str::revappend-chars from ans))
                     (ans (cons #\Newline ans)))
                  ans)
              ans))
       (parents (cdr (assoc :parents x)))
       (ans (if parents
                (b* ((ans (str::revappend-chars "Parents: " ans))
                     (ans (revappend-parents parents ans))
                     (ans (list* #\Newline #\. ans)))
                  ans)
              ans))
       (ans (cons #\Newline ans))
       (ans (str::revappend-chars terminal ans))
       (ans (cons #\Newline ans)))
    (mv (str::rchars-to-string ans) state)))

(defun display-topic (x all-topics state)
  (b* (((mv text state) (topic-to-text x all-topics state))
       (state (princ$ text *standard-co* state)))
    state))


; We previously tried to see if there was an acl2 doc topic.  But now that we
; have a fast importer from acl2 documentation, we just run (import-acl2doc)
; before calling colon-xdoc-fn, so we should only need to look in the xdoc
; database.

; Until we hijacked the :doc command, I didn't feel so bad about XDOC not
; trying very hard to tell you about related topics.  But now at least sort of
; try to do something.  See spellcheck.lisp for the basic gist.  Eventually
; we could extend this to include other search features.

;; (defun skip-through-close-long (xml-tokens)
;;   (cond ((atom xml-tokens)
;;          nil)
;;         ((equal (car xml-tokens) '(:CLOSE "long"))
;;          (cdr xml-tokens))
;;         (t
;;          (skip-through-close-long (cdr xml-tokens)))))

;; (defun eliminate-long (xml-tokens)
;;   (cond ((atom xml-tokens)
;;          nil)
;;         ((and (consp (car xml-tokens))
;;               (eq (first (car xml-tokens)) :OPEN)
;;               (equal (second (car xml-tokens)) "long"))
;;          (skip-through-close-long xml-tokens))
;;         (t
;;          (cons (car xml-tokens)
;;                (eliminate-long (cdr xml-tokens))))))

(defun summarize-nearby-topic (x state)
  (b* ((name     (cdr (assoc :name x)))
       (base-pkg (cdr (assoc :base-pkg x)))
       (short    (cdr (assoc :short x)))
;       (- (cw "Preprocessing...~%"))
       ;; Use NIL as the topics-fal as a simple way to suppress autolinks...
       ((mv short-acc state) (preprocess-main short name
                                              nil nil ;; no topics-fal, just keep it simple
                                              base-pkg
                                              state
                                              nil ;; accumulator
                                              ))
       (short (str::printtree->str short-acc))
;       (- (cw "Text is ~x0.~%" text))
;       (- (cw "Parsing xml...~%"))
       ((mv err tokens) (parse-xml short))

;       (- (cw "Checking result...~%"))
       ((when err)
        (cw "Error summarizing xdoc topic:~%~%")
        (b* ((state (princ$ err *standard-co* state))
             (state (newline *standard-co* state))
             (state (newline *standard-co* state)))
          state))
;       (- (cw "Tokens are ~x0.~%" tokens))
;       (- (cw "Merging tokens...~%"))
       ((mv err topic-to-rendered-table state)
        (topic-to-rendered-table-init state))
       ((when err) ; impossible?
        (cw "Error summarizing xdoc topic:~%~%")
        (b* ((state (princ$ err *standard-co* state))
             (state (newline *standard-co* state))
             (state (newline *standard-co* state)))
          state))
       (merged-tokens
        (reverse (merge-text tokens nil 0 nil
                             topic-to-rendered-table
                             (f-get-global 'xdoc-tag-elide-alist state))))
;       (- (cw "Merged tokens are ~x0.~%" merged-tokens))
       (terminal (str::rchars-to-string (tokens-to-terminal merged-tokens 70 nil nil nil)))
       (state (princ$ "    " *standard-co* state))
       (state (princ$ (symbol-package-name name) *standard-co* state))
       (state (princ$ "::" *standard-co* state))
       (state (princ$ (symbol-name name) *standard-co* state))
       (state (newline *standard-co* state))
       (state (princ$ (str::prefix-lines terminal "      ") *standard-co* state))
       (state (newline *standard-co* state)))
    state))

(defun summarize-nearby-topics (x state)
  (if (atom x)
      state
    (pprogn (summarize-nearby-topic (car x) state)
            (summarize-nearby-topics (cdr x) state))))

(defun find-topics (names all-topics)
  (if (atom names)
      nil
    (cons (find-topic (car names) all-topics)
          (find-topics (cdr names) all-topics))))

(defun all-topic-names (topics)
  (if (atom topics)
      nil
    (cons (cdr (assoc :name (car topics)))
          (all-topic-names (cdr topics)))))

(defun suggest-alternatives (name all-topics state)
  (declare (xargs :guard (symbolp name)))
  (b* ((topic-names (all-topic-names all-topics))
       (suggestions (xdoc-autocorrect name topic-names))
       (- (cw "~%Argh!  No documentation for ~s0::~s1.~%" (symbol-package-name name)
              (symbol-name name)))
       ((unless suggestions)
        state)
       ;; Otherwise, suggestions is at most five other topics.
       (- (if (eql (len suggestions) 1)
              (cw "Hrmn, maybe you wanted this one:~%~%")
            (cw "Hrmn, maybe you wanted one of these:~%~%")))
       (suggested-topics (find-topics suggestions all-topics))
       (state (summarize-nearby-topics suggested-topics state))
       (state (newline *standard-co* state)))
    state))


(defun colon-xdoc-fn (name all-topics state)
  (declare (xargs :guard (symbolp name)))
  (b* ((xdoc-entry (find-topic name all-topics))

       ((when (not xdoc-entry))
        (let ((state (suggest-alternatives name all-topics state)))
          (value :invisible)))

       (state (display-topic xdoc-entry all-topics state)))
    (value :invisible)))

#|
(include-book
 "centaur/vl/parsetree" :dir :system)

(colon-xdoc-fn 'modulep (get-xdoc-table (w state)) state)
(colon-xdoc-fn 'module->name (get-xdoc-table (w state)) state)
(colon-xdoc-fn 'all-equal (get-xdoc-table (w state)) state)
(colon-xdoc-fn 'cons (get-xdoc-table (w state)) state)

|#
