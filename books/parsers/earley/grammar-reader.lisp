; ACL2 Parser for Java
; Copyright (C) 2013 Battelle Memorial Institute
;
; Contact:
;  David Rager, ragerdl@cs.utexas.edu
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: David Rager <ragerdl@cs.utexas.edu>

(in-package "ACL2")

;(include-book "std/util/defaggregate" :dir :system)
(include-book "std/util/deflist" :dir :system)
;(include-book "std/util/bstar" :dir :system)
(include-book "std/strings/top" :dir :system)
(include-book "std/io/base" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "misc/with-waterfall-parallelism" :dir :system)

(include-book "object-representations")
(include-book "strings")
(include-book "read-line")
;(include-book "read-file-to-char-list")
(include-book "read-file-characters-no-error")

;(include-book "unicode/read-file-characters" :dir :system)

;; The context free grammar representation is a hashtable keyed on non-terminal
;; symbols. For each symbol there is a list of productions/rules for that
;; symbol. The productions take the form of a ordered list of symbols.
;;
;; The non-terminal symbols are represented as strings.


;; The lexicon is the representation of all terminal symbols (words in the
;; language). It is a hashtable keyed on word. For each word there is a list
;; of "terminal" structures that are different semantic mappings of the word.


;;;; Backus-Naur Form grammar reader functions
;;;;------------------------------------------

(with-waterfall-parallelism
(define read-next-bnf-lexeme1 ((file-input character-listp)
                               (keep-newline booleanp)
                               (whitespace character-listp)
                               (lexeme stringp))
  :returns (mv (lexeme stringp :hyp :fguard)
               (eof-p booleanp :hyp :fguard)
               (new-file-input character-listp :hyp :fguard))
  ;:assert (stringp booleanp character-listp)
  :verify-guards t
  :parents (earley-parser)

  (if (atom file-input)
      (mv lexeme t nil)
    (mv-let (char new-file-input)
      (mv (car file-input) (cdr file-input))
      (cond ;; If the char is an '=' and the rest of the lexeme is already
       ;; "::" -> Return lexeme
       ((and (equal char #\=) (equal lexeme "::"))
        (mv (string-append lexeme (string char)) nil new-file-input))
       ;; If the char is an '>' and lexeme starts with an '<' ->
       ;; Return lexeme
       ((and (equal char #\>)
             (< 0 (length lexeme)) ; for guard of following car THISMAKESNOSENSE
             (equal (car (str::firstn-chars 1 lexeme)) #\<))
        (mv (string-append lexeme (string char)) nil new-file-input))
       ;; If the char is '|' it is in it self a complete lexeme
       ((and (equal char #\|) (equal (length lexeme) 0))
        (mv (string-append lexeme (string char)) nil new-file-input))
       ;; Newlines are also (or may be) complete lexemes
       ((and (equal char #\Newline)
             (equal (length lexeme) 0)
             keep-newline)
        (mv (string-append lexeme (string char)) nil new-file-input))
       ;; If the char is whitespace, and lexeme is empty ->
       ;; Do nothing, just continue with the next char
       ((and (member-equal char whitespace)
             (equal (length lexeme) 0))
        (read-next-bnf-lexeme1 new-file-input keep-newline whitespace lexeme))
       (t (read-next-bnf-lexeme1 new-file-input keep-newline whitespace
                                 (string-append lexeme (string char)))))))))

(with-waterfall-parallelism
(defthm read-next-bnf-lexeme1-termination-weak
  (<= (acl2-count (mv-nth 2 (read-next-bnf-lexeme1 file-input keep-newline
                                                   whitespace lexeme)))
      (acl2-count file-input))
  :hints (("Goal" :in-theory (enable read-next-bnf-lexeme1)))
  :rule-classes (:rewrite :linear)))

(with-waterfall-parallelism
(defthm read-next-bnf-lexeme1-termination-strong
  (implies (not (mv-nth 1 (read-next-bnf-lexeme1 file-input keep-newline
                                                 whitespace lexeme)))
           (< (acl2-count (mv-nth 2 (read-next-bnf-lexeme1 file-input keep-newline
                                                           whitespace lexeme)))
              (acl2-count file-input)))
  :hints (("Goal" :in-theory (enable read-next-bnf-lexeme1)))
  :rule-classes (:rewrite :linear)))

;; (local
;;  (defthm file-measure-of-read-next-bnf-lexeme1-weak
;;    (implies
;;     (and (character-listp file-input)
;;          (booleanp keep-newline)
;;          (character-listp whitespace)
;;          (stringp lexeme))
;;     (<= (file-measure channel
;;                       (mv-nth 2 (read-next-bnf-lexeme1 channel keep-newline
;;                                                        whitespace lexeme state)))
;;         (file-measure channel state)))
;;     :hints (("Goal" :induct t :in-theory (e/d
;;                                           (read-next-bnf-lexeme1)
;;                                           (file-measure mv-nth))))


(define read-next-bnf-lexeme ((file-input character-listp)
                              (keep-newline booleanp)) ; keep-newline should be nil if not specified
;  "Reads and returns the next Backus-Naur lexeme from file."
  :returns (mv (lexeme stringp ; (if lexeme (stringp lexeme) t)
                       :hyp :fguard
                       "Empty string if ")
               (eof-p booleanp :hyp :fguard
                      "Whether read-next-bnf-lexeme has reached the end of ~
                       the file")
               (new-file-input character-listp :hyp :fguard
                               "Remaining portion of file input"))
  :parents (earley-parser)
  ;:assert (stringp booleanp character-listp)
  (let ((whitespace (list #\Space #\Tab))
        ;; (lexeme "") ; not used
        )
    (mv-let
      (lexeme eof-p new-file-input)
      (read-next-bnf-lexeme1 file-input
                             keep-newline
                             (if keep-newline
                                 whitespace
                               (cons #\Newline whitespace))
                             "")
          (mv (str-trim (list #\< #\>) lexeme)
              eof-p
              new-file-input))))

(defthm read-next-bnf-lexeme-termination-weak
  (<= (acl2-count (mv-nth 2 (read-next-bnf-lexeme file-input keep-newline)))
      (acl2-count file-input))
  :hints (("Goal" :in-theory (enable read-next-bnf-lexeme)))
  :rule-classes (:rewrite :linear))

(with-waterfall-parallelism
 (defthm read-next-bnf-lexeme-termination-strong
   (implies (not (mv-nth 1 (read-next-bnf-lexeme file-input keep-newline)))
            (< (acl2-count (mv-nth 2 (read-next-bnf-lexeme file-input keep-newline)))
               (acl2-count file-input)))
   :hints (("Goal" :in-theory (enable read-next-bnf-lexeme)))
   :rule-classes (:rewrite :linear)))


(define read-next-bnf-production1 ((file-input character-listp)
                                   (keep-newline booleanp)
                                   (production string-list-p)
                                   (lexeme-cache string-list-p))
  :returns (mv (productions string-list-p :hyp :fguard)
               (remaining-file-input character-listp :hyp :fguard)
               (lexeme-cache string-list-p :hyp :fguard))
  :parents (earley-parser)
    (mv-let (lexeme eof-p new-file-input)
    (read-next-bnf-lexeme file-input keep-newline) ; make sure I account for this in translation
    (cond ((or (equal lexeme "") eof-p) ; check used to be for (null lexeme) - SOURCE OF RUNTIME BUG
           (mv (reverse production) new-file-input lexeme-cache))
          ;; If we just read a "::=" and there already is one in the
          ;; production -> Push it and last lexeme onto cache instead of
          ;; production
          ((and (equal lexeme "::=")
                (member-equal lexeme production))
           (let* ((lexeme-cache (cons lexeme lexeme-cache))
                  (lexeme-cache (cons (car production) lexeme-cache))
                  (production (cdr production)))
             (mv (rev production) new-file-input lexeme-cache)))
          (t (let ((production (cons lexeme production)))
               (read-next-bnf-production1 new-file-input keep-newline
                                          production lexeme-cache))))))

(defthm read-next-bnf-production1-weak
  (<= (acl2-count (mv-nth 1 (read-next-bnf-production1 file-input keep-newline
                                                       production lexeme-cache)))
      (acl2-count file-input))
  :hints (("Goal" :in-theory (enable read-next-bnf-production1)))
  :rule-classes (:rewrite :linear))


(defthm read-next-bnf-production1-strong
  (implies (and (character-listp file-input)
                (booleanp keep-newline)
                (string-list-p production)
                ;(state-p state)
                (string-list-p lexeme-cache)
                (< (len production)
                   (len (mv-nth 0 (read-next-bnf-production1 file-input keep-newline
                                                             production lexeme-cache)))))
           (< (acl2-count (mv-nth 1 (read-next-bnf-production1 file-input keep-newline
                                                               production lexeme-cache)))
              (acl2-count file-input)))
  :hints (("Goal" :in-theory (enable read-next-bnf-production1)))
  :rule-classes (:rewrite :linear))

(define fix-production ((lexeme-cache string-list-p)
                        (production string-list-p))
  :returns (productions string-list-p "New list of production strings" :hyp
                        :guard)
  :parents (earley-parser)
  ;:assert string-list-p
  (append (rev lexeme-cache) production)

  ///

  (defthm fix-production-preserves-string-list-p
    (implies (and (string-listp x)
                  (string-listp y))
             (string-listp (fix-production x y))))
  (defthm fix-production-length
    (implies (string-listp x)
             (equal (len (fix-production x nil))
                    (len x))))
  (defthm fix-production-of-nil
    (equal (fix-production x nil)
           (rev x))))

; To figure out how important the lexeme-cache is, I could call
; my-f-put-global/my-f-get-global and trace those.  Would need to run on more
; complicated examples.  Having a functional model that doesn't involve state
; would be a nice improvement.

; I did the above and found that it was used a small amount, even in our small
; example.  Too bad.

(defmacro string-list-p-alias (x)
  `(string-list-p ,x))

(define read-next-bnf-production ((file-input character-listp)
                                  (keep-newline booleanp)
                                  ;(state state-p)
                                  (lexeme-cache string-list-p)
                                  )
  "Reads and returns the next Backus-Naur production from file."
;  :guard (and (boundp-global 'lexeme-cache state)
;              (string-list-p (get-global 'lexeme-cache state)))
  :returns (mv (productions string-list-p :hyp :fguard)
               (remaining-file-input character-listp :hyp :fguard)
 ;              (state state-p :hyp :fguard)
               (lexeme-cache string-list-p :hyp :fguard))
  :parents (earley-parser)
  ;:assert (string-list-p character-listp string-list-p-alias)
; Seems to be working when compared with CL trace output.
  (let (;(lexeme-cache (f-get-global 'lexeme-cache state)) ; silly
        (production nil))                                 ; silly
    ;; If there is anything in the cache, pop it off and add it to production
    ;; (read-next-bnf-production-cache lexeme-cache lexeme-cache production)
    (let* ((production (fix-production lexeme-cache production)) ; silly but it's part of the original code
           ;(state (f-put-global 'lexeme-cache nil state))
           (lexeme-cache nil) ; just integrated its value above
           )
      (read-next-bnf-production1 file-input keep-newline production lexeme-cache))))

(defthm read-next-bnf-production-weak
  (<= (acl2-count (mv-nth 1 (read-next-bnf-production file-input keep-newline
                                                      lexeme-cache)))
      (acl2-count file-input))
  :hints (("Goal" :in-theory (enable read-next-bnf-production)))
  :rule-classes (:rewrite :linear))

(defthm read-next-bnf-production-strong-works
  (implies (and (character-listp file-input)
                (booleanp keep-newline)
                (string-list-p production)
                (string-list-p lexeme-cache)
                (< (len (rev lexeme-cache)) ; production
                   (len (mv-nth 0 (read-next-bnf-production1
                                   file-input keep-newline
                                   (rev lexeme-cache)
                                   nil)))))
           (< (acl2-count (mv-nth 1 (read-next-bnf-production file-input keep-newline
                                                              lexeme-cache)))
              (acl2-count file-input)))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (read-next-bnf-production)
                                  (read-next-bnf-production1-strong)))
          ("Goal'" :use ((:instance read-next-bnf-production1-strong
                                    (production (rev lexeme-cache))
                                    (lexeme-cache nil)))))
  :rule-classes (:rewrite :linear))

#|
(i-am-here)

(defthm read-next-bnf-production-strong
  (implies (and (character-listp file-input)
            (booleanp keep-newline)
            (string-list-p production)
            (string-list-p lexeme-cache)
            (mv-nth 0 (read-next-bnf-production file-input keep-newline lexeme-cache)))
           (< (acl2-count (mv-nth 1 (read-next-bnf-production file-input keep-newline
                                                              lexeme-cache)))
              (acl2-count file-input)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (read-next-bnf-production)
                           (read-next-bnf-production1-strong
                            read-next-bnf-production1)))
          ("Goal'" :use ((:instance read-next-bnf-production1-strong
                                    (production (rev lexeme-cache))
                                    (lexeme-cache nil)))))
  :otf-flg t
  :rule-classes (:rewrite :linear))
|#

(define inject-expansions! ((target-list string-list-p)
                            (expansion string-list-p)
                            (rules rule-list-p)
                            (production (and (string-list-p production)
                                             (consp production))))
  :returns (rules rule-list-p :hyp :fguard)
  :parents (earley-parser)
  ;:assert rule-list-p
  (cond
   ;; No more expansions -> Inject last one
   ((atom target-list) ; was null in cl impl
    (let ((curr-val (cdr (hons-get (car production) rules))))
      (hons-shrink-alist
       (hons-acons (car production)
                   (cons expansion curr-val)
                   rules)
       nil)))
   ;; More expansion -> Inject current and continue
   ((equal (first target-list) "|")
    (let* ((curr-val (cdr (hons-get (car production) rules)))
           (rules (hons-shrink-alist
                   (hons-acons (car production)
                               (cons expansion curr-val)
                               rules)
                   nil)
                   ))
      (inject-expansions! (cdr target-list) nil #|expansion|# rules production)))
   ;; Expansion not ended -> Collect rest of expansion
   (t
    (inject-expansions! (cdr target-list)
                        (append expansion (list (first target-list)))
                        rules
                        production)))
  :prepwork
  ((skip-proofs ; unsound but doing for now. Commented hyps will be needed eventually
    (defthm read-next-bnf-production-strong
      (implies (and ;; (character-listp file-input)
                ;; (booleanp keep-newline)
                ;; (string-list-p production)
                ;; (string-list-p lexeme-cache)
                (mv-nth 0 (read-next-bnf-production file-input keep-newline lexeme-cache)))
               (< (acl2-count (mv-nth 1 (read-next-bnf-production file-input keep-newline
                                                                  lexeme-cache)))
                  (acl2-count file-input)))
      :hints (("Goal" :do-not-induct t
               :in-theory (e/d (read-next-bnf-production)
                               (read-next-bnf-production1-strong)))
              ("Goal'" :use ((:instance read-next-bnf-production1-strong
                                        (production (rev lexeme-cache))
                                        (lexeme-cache nil)))))
      :rule-classes (:rewrite :linear))))

)

(define load-bnf-grammar2 ((file-input character-listp)
                           (rules rule-list-p)
                           (lexeme-cache string-list-p))
  :returns (mv (rules rule-list-p :hyp :fguard)
               (lexeme-cache string-list-p :hyp :fguard))
  ;:assert (rule-list-p string-list-p)
  :parents (earley-parser)
  (mv-let (production new-file-input lexeme-cache)

; could use a flag other than production to indicate termination

    (read-next-bnf-production file-input nil lexeme-cache)
    (cond ((atom production) ; used to be null but should be fine
           (mv rules lexeme-cache))
          ((atom (cdr production))
           (prog2$ (er hard? 'load-bnf-grammar2

; Ee could try changing the above "hard?" to "hard", and after proving a lemma
; about read-next-bnf-production, prove that this branch is unreachable.

                       "Programming error: production should have been either ~
                        nil or a list of at least length two, but was ~x0"
                       production)
                   (mv rules lexeme-cache)))
          (t (let ((rules (inject-expansions! (cddr production) nil rules production)))
               (load-bnf-grammar2 new-file-input rules lexeme-cache))))))

(define load-bnf-grammar1 ((file-input character-listp))
  :returns (grammar grammar-p :hyp :fguard)
  ;:assert grammar-p
  :parents (earley-parser)
  (mv-let (rules lexeme-cache)

; For each production in the BNF file, create a list of possible ordered symbol
; sequences (list of strings) that is a legal expression for the symbol.

    (load-bnf-grammar2 file-input nil nil)
    (declare (ignore lexeme-cache))
    (let ((rules (hons-shrink-alist rules nil)))
      (make-grammar :rules rules))))

(define load-bnf-grammar ((filename stringp)
                          (state state-p))
  "Reads a grammar on Backus-Naur form into the representation of the context
   free grammar(CFG)."
  :returns (mv (grammar grammar-p :hyp :fguard)
               (state state-p :hyp :fguard))
  :parents (earley-parser)
  (mv-let (file-input state)
    (read-file-characters-no-error filename state)
    (let ((grammar (load-bnf-grammar1 file-input)))
      (mv grammar state))))

;;;; Lexicon functions
;;;;------------------
;;;; Reads a dictionary on the form:
;;;;
;;;; <word> :class <class> :gender <gender>
;;;;
;;;; into a hashtable of lists of word instances and
;;;; a list of word classes (part of speech).

;; (defn keyword-string-pair-p (x)
;;   (and (consp x)
;;        (keywordp (car x))
;;        (stringp (cdr x))))

;; (std::deflist keyword-string-pair-list-p (x)
;;   (keyword-string-pair-p x)
;;   :elementp-of-nil nil
;;   :true-listp t)

(std::defalist keyword-string-pair-list-p (x)
  :key (keywordp x)
  :val (stringp x)
  :true-listp t
  :parents (earley-parser))

(local
 (defthm lemma1
   (implies (and ; (force (character-listp chars)) ; Matt K. mod
                 (force (stringp str))
                 (not (member-symbol-name str
                                          (pkg-imports "KEYWORD"))))
            (equal (symbol-package-name
                    (intern-in-package-of-symbol str
                                                 :a-random-symbol-for-intern))
                   "KEYWORD"))))

(local
 (defthm lemma2
   (implies (and ; (force (character-listp chars)) ; Matt K. mod
                 (force (stringp str))
                 (not (member-symbol-name str
                                          nil)))
            (equal (symbol-package-name
                    (intern-in-package-of-symbol str
                                                 :a-random-symbol-for-intern))
                   "KEYWORD"))))

(local
 (include-book "std/basic/intern-in-package-of-symbol" :dir :system))

(defthm run-pkg-imports-on-keyword
  (equal (pkg-imports "KEYWORD")
         nil))

(local
 (defun double-cdr (x)
   (if (atom x)
       nil
     (double-cdr (cddr x)))))

(defn even-string-list-p (x)
  (cond ((atom x)
         (null x))
        (t (and (stringp (car x))
                (consp (cdr x))
                (stringp (cadr x))
                (even-string-list-p (cddr x))))))

(defthm even-string-list-p-implies-string-list-p
  (implies (even-string-list-p x)
           (string-list-p x))
  :rule-classes :forward-chaining)



(define read-lexicon-line-options ((strings even-string-list-p))
  :measure (len strings)
  :returns (ans keyword-string-pair-list-p :hyp :fguard)
  :parents (earley-parser)
  (cond ((atom strings)
         nil)
        ((member-symbol-name (str-trim '(#\:)
                                       (str::upcase-string (car strings)))
                             (pkg-imports "KEYWORD"))
         (er hard? 'read-lexicon-line-options
             "The lexicon string cannot be converted to a keyword symbol ~
              because it already exists in the keyword package (this would ~
              not be a problem if this symbol had not been imported from ~
              another package).  Offending string is: ~x0"
             (str-trim '(#\:)
                       (str::upcase-string (car strings)))))
        (t (cons (cons (intern (str-trim '(#\:)
                                         (str::upcase-string (car strings)))
                               "KEYWORD")
                       (cadr strings))
                 (read-lexicon-line-options (cddr strings))))))



(local
 (defthm read-lexicon-line-subgoal-4-a
   (implies (and (alistp lst)
                 (assoc-equal x lst))
            (consp (assoc-equal x lst)))))

(local
 (defthm read-lexicon-line-subgoal-4-b
   (implies (even-string-list-p (cdr (str::strtok (mv-nth 0 (read-line! file-input))
                                                  '(#\space))))

            (alistp (READ-LEXICON-LINE-OPTIONS
                     (CDR (STR::STRTOK (MV-NTH 0 (READ-LINE! FILE-INPUT))
                                       '(#\Space))))))))

;; (local
;;  (defthm read-lexicon-line-subgoal-4
;;    (implies
;;     (and
;;      (character-listp file-input)
;;      (mv-nth 0 (read-line! file-input))
;;      (not (equal (mv-nth 0 (read-line! file-input))
;;                  ""))
;;      (consp (str::strtok (mv-nth 0 (read-line! file-input))
;;                          '(#\space)))
;;      (stringp (car (str::strtok (mv-nth 0 (read-line! file-input))
;;                                 '(#\space))))
;;      (even-string-list-p (cdr (str::strtok (mv-nth 0 (read-line! file-input))
;;                                            '(#\space))))
;;      (not
;;       (consp
;;        (assoc-equal
;;         :class (read-lexicon-line-options
;;                 (cdr (str::strtok (mv-nth 0 (read-line! file-input))
;;                                   '(#\space))))))))
;;     (not (assoc-equal
;;           :class (read-lexicon-line-options
;;                   (cdr (str::strtok (mv-nth 0 (read-line! file-input))
;;                                     '(#\space)))))))))

;; (local
;;  (defthm member-assoc-equivalence-1-A
;;    (implies (alistp lst)
;;             (iff (member key (strip-cars lst))
;;                  (assoc key lst)
;;                  ))))

;; (local
;;  (defthm member-assoc-equivalence-1-B
;;    (implies (alistp lst)
;;             (iff (assoc key lst)
;;                  (member key (strip-cars lst))))))


;; (local
;;  (defthm member-assoc-equivalence-2
;;    (implies (and (alistp lst) (cdr (assoc key lst)))
;;             (member key (strip-cars lst)))))

(local
 (defthm read-lexicon-line-subgoal-3-lemma
   (implies (and (alistp lst)
                 (keyword-string-pair-list-p lst)
                 (assoc-equal key lst))
            (stringp (cdr (assoc-equal key lst))))))

;; (local
;;  (defthm read-lexicon-line-subgoal3
;;    (implies
;;     (and
;;      (character-listp file-input)
;;      (mv-nth 0 (read-line! file-input))
;;      (not (equal (mv-nth 0 (read-line! file-input))
;;                  ""))
;;      (consp (str::strtok (mv-nth 0 (read-line! file-input))
;;                          '(#\space)))
;;      (stringp (car (str::strtok (mv-nth 0 (read-line! file-input))
;;                                 '(#\space))))
;;      (even-string-list-p (cdr (str::strtok (mv-nth 0 (read-line! file-input))
;;                                            '(#\space))))
;;      (cdr (assoc-equal
;;            :class (read-lexicon-line-options
;;                    (cdr (str::strtok (mv-nth 0 (read-line! file-input))
;;                                      '(#\space)))))))
;;     (stringp
;;      (cdr (assoc-equal
;;            :class (read-lexicon-line-options
;;                    (cdr (str::strtok (mv-nth 0 (read-line! file-input))
;;                                      '(#\space))))))))))

(define read-lexicon-line ((file-input character-listp))
   "Read a line from the given file, and return the corresponding terminal."
   ;; Parse a line from the file
   :returns (mv (terminal (implies terminal (terminal-p terminal)))
                (remaining-file-input character-listp :hyp :fguard))
   :parents (earley-parser)
   (mv-let (line new-file-input)
     (read-line! file-input)
     (cond ((or (null line) (equal line ""))
            (mv nil new-file-input))
           (t
            (b* ((words ;(remove-equal ""  ; remove call is unnecessary
                  (str::strtok line '(#\Space))) ;)
                 ((unless (and (consp words) (stringp (car words))))
                  (mv (er hard? 'read-lexicon-line
                          "Read-lexicon-line does not accept empty lines")
                      new-file-input))
                 (string (first words))
                 ( ;(when (and (consp (cdr words)) (atom (cddr words))))
                  (unless (even-string-list-p (cdr words)))
                  (mv (er hard? 'read-lexicon-line
                          "Read-lexicon-line given lexicon input line that ~
                          doesn't have _pairs_ (not in the lisp sense) of ~
                          options and values.  Input line is:~% ~x0"
                          (cdr words))
                      new-file-input))
                 (options (read-lexicon-line-options (cdr words))))
              ;; Create the word object
              (mv (make-terminal :word string ; the regex would be read in here
                                 :class (str-trim '(#\< #\>)
                                                  (or (cdr (assoc :class
                                                                  options))
                                                      ""))
                                 :gender (cdr (assoc :gender options)))
                  new-file-input)))))
   ///


   ;; (local
   ;;  (defthm dumb-lemma
   ;;    (implies (and (character-listp x) x)
   ;;             (< 0 (length x)))))


   (defthm read-lexicon-line-weak
     (<= (acl2-count (mv-nth 1 (read-lexicon-line file-input)))
         (acl2-count file-input))
     :rule-classes (:rewrite :linear))


   (encapsulate
    ()
    (local
; Provides us with the following, necessary for read-lexicon-line-strong

;;; (implies (and (stringp x)
;;;        n       (not (equal x "")))
;;;          (< 0 (length x)))))

     ;; [Jared]: removed newline to un-fool dependency scanner
     (include-book "std/strings/arithmetic" :dir :system))

    (defthm read-lexicon-line-strong
      (implies (and
                (mv-nth 0 (read-lexicon-line file-input))
                (force (character-listp
; Could possibly be removed if we did more sophisticated reasoning for
; read-line
                        file-input)))
               (< (acl2-count (mv-nth 1 (read-lexicon-line file-input)))
                  (acl2-count file-input)))
      :hints (("Goal" :in-theory (enable read-lexicon-line))
              ("Goal'''" :in-theory (e/d (read-lexicon-line)
                                         (read-line!-strong))
               :use ((:instance read-line!-strong))))
      :rule-classes (:rewrite :linear))))

;; (local
;;  (defthm load-lexicon1-lemma
;;    (implies (and (stringp word)
;;                  (lexicon-p lexicon)
;;                  (terminal-p terminal))
;;             (lexicon-p (hons-acons word
;;                                    (hons terminal
;;                                          (cdr (hons-get word lexicon-p)))
;;                                    lexicon)))
;;    :hints (("Goal" :in-theory (enable lexicon-p terminal-p)))))

;; (local
;;  (defthm load-lexicon1-lemmaaaa
;;    (implies (and (dictionary-p dictionary)
;;                  (stringp word))
;;             (terminal-list-p (hons-assoc-equal word
;;                                               dictionary)))))

(defthm load-lexicon1-lemma
  (implies
   (and (character-listp file-input)
        (string-list-p part-of-speech-list)
        (dictionary-p dictionary)
        (mv-nth 0 (read-lexicon-line file-input)))
   (terminal-p (mv-nth 0 (read-lexicon-line file-input)))))

(define load-lexicon1 ((dictionary dictionary-p)
                       (part-of-speech-list string-list-p)
                       (file-input character-listp))
  :returns (mv (dictionary dictionary-p :hyp :fguard)
               (part-of-speech-list string-list-p :hyp :fguard)
               (remaining-file-input character-listp :hyp :fguard))
  :parents (earley-parser)
  (if (mbe :logic (not (character-listp file-input))
           :exec nil)
      (mv dictionary part-of-speech-list file-input)
    (mv-let (terminal new-file-input)
      (read-lexicon-line file-input)
      (cond ((null terminal) ; source of a bug, what if the lex file contains a blank line?,
             (mv dictionary part-of-speech-list new-file-input))
            (t
             (b* ((word (terminal->word terminal))
                  (curr-terminal-list (cdr (hons-get word dictionary)))) ; source of bug?, "working" version doesn't call cdr, but it's "correctly" needed for the proof to go through
               (load-lexicon1 (hons-acons word
                                          (hons terminal curr-terminal-list)
                                          dictionary)
                              (cons (terminal->class terminal)
                                    part-of-speech-list)
                              new-file-input)))))))

(define load-lexicon ((filename stringp)
                      (state state-p))
  :returns (mv (lexicon lexicon-p :hyp :fguard)
               (state state-p :hyp :fguard))
  :parents (earley-parser)
  (let ((dictionary nil) ; use a hashtable
        (part-of-speech-list nil))
    (mv-let (file-input state)
      (read-file-characters-no-error filename state)
      (mv-let (dictionary part-of-speech-list new-file-input)
        (load-lexicon1 dictionary part-of-speech-list file-input)
        (declare (ignore new-file-input))
        (mv (make-lexicon :dictionary dictionary
                          :part-of-speech part-of-speech-list)
            state)))))
