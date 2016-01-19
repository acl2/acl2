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
(include-book "prepare-topic")
(include-book "spellcheck")
(include-book "word-wrap")
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

(defun merge-text (x acc codes href)
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
                   (merge-text (cons tok rest) acc codes href)))
                ((equal name "icon")
                 (b* ((tok  (list :TEXT "{ICON}")))
                   (merge-text (cons tok rest) acc codes href)))
                ((member-equal name *throwaway-tags*)
                 (merge-text rest acc codes nil))
                ((equal name "a")
                 (b* ((href (cdr (assoc-equal "href" (opentok-atts tok1))))
                      (tok  (list :TEXT (str::cat "{"))))
                   (merge-text (cons tok rest) acc codes href)))
                ((equal name "see")
                 (b* ((tok  (list :TEXT "[")))
                   (merge-text (cons tok rest) acc codes href)))
                ((equal name "srclink")
                 (b* ((tok  (list :TEXT "<")))
                   (merge-text (cons tok rest) acc codes href)))
                (t
                 (merge-text rest (cons tok1 acc) codes href)))))
       ((when (closetok-p tok1))
        (b* ((name  (closetok-name tok1))
             (codes (if (equal name "code")
                        (- 1 codes)
                      codes)))
          (cond ((member-equal name *throwaway-tags*)
                 (merge-text rest acc codes href))
                ((member-equal name '("see"))
                 (let ((tok (list :TEXT "]")))
                   (merge-text (cons tok rest) acc codes href)))
                ((member-equal name '("a"))
                 (let ((tok (list :TEXT (str::cat " | " (or href "") "}"))))
                   (merge-text (cons tok rest) acc codes href)))
                ((equal name "srclink")
                 (let ((tok (list :TEXT ">")))
                   (merge-text (cons tok rest) acc codes href)))
                (t
                 (merge-text rest (cons tok1 acc) codes href)))))
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
        (merge-text rest (cons tok1 acc) codes href))

       (merged-tok (list :TEXT (str::cat (texttok-text (car acc))
                                         (texttok-text tok1)))))
    (merge-text rest (cons merged-tok (cdr acc)) codes href)))


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
                                   (str::cat (str::natstr (nfix (car list-nums))) ". ")))
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
       (merged-tokens (reverse (merge-text tokens nil 0 nil)))
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
                                              nil ;; no topics-fal, just keep it simple
                                              base-pkg
                                              state
                                              nil ;; accumulator
                                              ))
       (short (str::rchars-to-string short-acc))
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
       (merged-tokens (reverse (merge-text tokens nil 0 nil)))
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
