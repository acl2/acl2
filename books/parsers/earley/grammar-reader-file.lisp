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

;(include-book "cutil/defaggregate" :dir :system)
(include-book "cutil/deflist" :dir :system)
;(include-book "tools/bstar" :dir :system)
(include-book "str/top" :dir :system)
;;(include-book "system/io" :dir :system)
(include-book "std/io/top" :dir :system)
(include-book "cutil/define" :dir :system)
(include-book "parallel/with-waterfall-parallelism" :dir :system)

(include-book "object-representations")
(include-book "strings")
(include-book "read-line")

;; The context free grammar representation is a hashtable keyed on non-terminal
;; symbols. For each symbol there is a list of productions/rules for that
;; symbol. The productions take the form of a ordered list of symbols.
;;
;; The non-terminal symbols are represented as strings.


;; The lexicon is the representation of all terminal symbols (words in the 
;; language). It is a hashtable keyed on word. For each word there is a list
;; of "terminal" structures that are different semantic mappings of the word. 

;; (local
;;  (defthm file-measure-lemma2
;;    (<= (FILE-MEASURE CHANNEL t)
;;        (FILE-MEASURE CHANNEL STATE))
;;    :hints (("Goal" :in-theory (enable file-measure)))
;;    :rule-classes (:rewrite :linear)))

;; (local
;;  (defthm file-measure-lemma
;;    (<= (FILE-MEASURE CHANNEL NIL)
;;        (FILE-MEASURE CHANNEL STATE))
;;    :hints (("Goal" :in-theory (enable file-measure)))
;;    :rule-classes (:rewrite :linear)))

;;;; Backus-Naur Form grammar reader functions
;;;;------------------------------------------
(define read-next-bnf-lexeme1 ((channel symbolp)
                               (keep-newline booleanp)
                               (whitespace character-listp)
                               (lexeme stringp)
                               (state state-p))
; returns (mv lexeme eof-p state)
  :returns (mv (lexeme stringp :hyp :fguard)
               (eof-p booleanp :hyp :fguard)
               (state state-p :hyp :fguard))
     
  :measure (file-measure channel state)
  :guard (OPEN-INPUT-CHANNEL-P CHANNEL
                               :CHARACTER STATE)
  :stobjs (state)
  :verify-guards t
  
  (mv-let (char state)
    (read-char$ channel state)
    (cond ((null char)
           (mv lexeme t state))
          ;; If the char is an '=' and the rest of the lexeme is already
          ;; "::" -> Return lexeme
          ((and (equal char #\=) (equal lexeme "::"))
           (mv (string-append lexeme (string char)) nil state))
          ;; If the char is an '>' and lexeme starts with an '<' ->
          ;; Return lexeme
          ((and (equal char #\>) 
                (consp lexeme) ; for guard of following car
                (equal (car (str::firstn-chars 1 lexeme)) #\<))
           (mv (string-append lexeme (string char)) nil state))
          ;; If the char is '|' it is in it self a complete lexeme
          ((and (equal char #\|) (equal (length lexeme) 0))
           (mv (string-append lexeme (string char)) nil state))
          ;; Newlines are also (or may be) complete lexemes
          ((and (equal char #\Newline) 
                (equal (length lexeme) 0)
                keep-newline)
           (mv (string-append lexeme (string char)) nil state))
          ;; If the char is whitespace, and lexeme is empty ->
          ;; Do nothing, just continue with the next char
          ((and (member-equal char whitespace)
                (equal (length lexeme) 0))
           (read-next-bnf-lexeme1 channel keep-newline whitespace lexeme state))
          (t (read-next-bnf-lexeme1 channel keep-newline whitespace
                                    (string-append lexeme (string char)) state)))))



;; (local
;;  (defthm |file-measure-of-read-next-bnf-lexeme1-weak subgoal *1/6|
;;    (implies
;;     (and
;;      (not (null (mv-nth 0 (read-char$ channel state))))
;;      (not (and (equal (mv-nth 0 (read-char$ channel state)) #\=)
;;                (equal lexeme "::")))
;;      (not (and (equal (mv-nth 0 (read-char$ channel state)) #\>)
;;                (consp lexeme)
;;                (equal (car (str::firstn-chars 1 lexeme)) #\<)))
;;      (not (and (equal (mv-nth 0 (read-char$ channel state)) #\|)
;;                (equal (length lexeme) 0)))
;;      (not (and (equal (mv-nth 0 (read-char$ channel state)) #\newline)
;;                (equal (length lexeme) 0)
;;                keep-newline))
;;      (and (member-equal (mv-nth 0 (read-char$ channel state)) whitespace)
;;           (equal (length lexeme) 0))
;;      (implies (and (symbolp channel)
;;                    (booleanp keep-newline)
;;                    (character-listp whitespace)
;;                    (stringp lexeme)
;;                    (state-p (mv-nth 1 (read-char$ channel state)))
;;                    (open-input-channel-p channel
;;                                          :character (mv-nth 1 (read-char$ channel state))))
;;               (<= (file-measure channel
;;                                 (mv-nth 1
;;                                         (read-next-bnf-lexeme1 channel keep-newline whitespace lexeme
;;                                                                (mv-nth 1 (read-char$ channel state)))))
;;                   (file-measure channel
;;                                 (mv-nth 1 (read-char$ channel state))))))
;;     (implies (and (symbolp channel)
;;                   (booleanp keep-newline)
;;                   (character-listp whitespace)
;;                   (stringp lexeme)
;;                   (state-p state)
;;                   (open-input-channel-p channel
;;                                         :character state))
;;              (<= (file-measure channel
;;                                (mv-nth
;;                                 1
;;                                 (read-next-bnf-lexeme1 channel
;;                                                        keep-newline whitespace lexeme state)))
;;                  (file-measure channel state))))
;;    :hints (("Goal" :expand ((:free (keep-newline whitespace lexeme)
;;                                    (read-next-bnf-lexeme1 channel
;;                                                           keep-newline
;;                                                           whitespace lexeme
;;                                                           state)))))))

;; (local
;;  (defthm
;;    |file-measure-of-read-next-bnf-lexeme1-weak subgoal *1/7|
;;    (implies
;;     (and
;;      (not (null (mv-nth 0 (read-char$ channel state))))
;;      (not (and (equal (mv-nth 0 (read-char$ channel state))
;;                       #\=)
;;                (equal lexeme "::")))
;;      (not (and (equal (mv-nth 0 (read-char$ channel state))
;;                       #\>)
;;                (consp lexeme)
;;                (equal (car (str::firstn-chars 1 lexeme))
;;                       #\<)))
;;      (not (and (equal (mv-nth 0 (read-char$ channel state))
;;                       #\|)
;;                (equal (length lexeme) 0)))
;;      (not (and (equal (mv-nth 0 (read-char$ channel state))
;;                       #\newline)
;;                (equal (length lexeme) 0)
;;                keep-newline))
;;      (not (and (member-equal (mv-nth 0 (read-char$ channel state))
;;                              whitespace)
;;                (equal (length lexeme) 0)))
;;      (implies
;;       (and
;;        (symbolp channel)
;;        (booleanp keep-newline)
;;        (character-listp whitespace)
;;        (stringp
;;         (string-append lexeme
;;                        (string (mv-nth 0 (read-char$ channel state)))))
;;        (state-p (mv-nth 1 (read-char$ channel state)))
;;        (open-input-channel-p
;;         channel
;;         :character (mv-nth 1 (read-char$ channel state))))
;;       (<=
;;        (file-measure
;;         channel
;;         (mv-nth
;;          1
;;          (read-next-bnf-lexeme1
;;           channel keep-newline whitespace
;;           (string-append lexeme
;;                          (string (mv-nth 0 (read-char$ channel state))))
;;           (mv-nth 1 (read-char$ channel state)))))
;;        (file-measure channel
;;                      (mv-nth 1 (read-char$ channel state))))))
;;     (implies
;;      (and (symbolp channel)
;;           (booleanp keep-newline)
;;           (character-listp whitespace)
;;           (stringp lexeme)
;;           (state-p state)
;;           (open-input-channel-p channel
;;                                 :character state))
;;      (<=
;;       (file-measure
;;        channel
;;        (mv-nth
;;         1
;;         (read-next-bnf-lexeme1 channel
;;                                keep-newline whitespace lexeme state)))
;;       (file-measure channel state))))
;;    :hints (("Goal" :expand ((:free (keep-newline whitespace lexeme)
;;                                    (read-next-bnf-lexeme1 channel
;;                                                           keep-newline
;;                                                           whitespace lexeme
;;                                                           state)))))))

(local
 (defthm file-measure-of-read-next-bnf-lexeme1-weak
   (implies 
    (and (symbolp channel)
         (booleanp keep-newline)
         (character-listp whitespace)
         (stringp lexeme)
         (state-p state)
         (open-input-channel-p channel :character state))
    (<= (file-measure channel
                      (mv-nth 2 (read-next-bnf-lexeme1 channel keep-newline
                                                       whitespace lexeme state)))
        (file-measure channel state)))
    :hints (("Goal" :induct t :in-theory (e/d
                                          (read-next-bnf-lexeme1)
                                          (file-measure mv-nth))))
    :rule-classes (:rewrite :linear)))

#|
(local 
 (defthm file-measure-lemma4-strong
   (implies (consp x)
            (< 0 (len x)))
   :rule-classes :linear))
      
(local
 (defthm file-measure-lemma4
   (implies (and (force (state-p state))
                 (CDDR (ASSOC-EQUAL CHANNEL (CAR STATE))))
            (< (FILE-MEASURE CHANNEL t)
               (FILE-MEASURE CHANNEL STATE)))
   :hints (("Goal" :in-theory (enable file-measure)))
   :rule-classes (:rewrite :linear)))))

(local
 (defthm file-measure-lemma3
   (implies (and (force (state-p state))
                 (CDDR (ASSOC-EQUAL CHANNEL (CAR STATE))))
            (< (FILE-MEASURE CHANNEL NIL)
               (FILE-MEASURE CHANNEL STATE)))
   :hints (("Goal" :in-theory (enable file-measure)))
   :rule-classes (:rewrite :linear)))

(defthm yet-another-lemma
  (implies (mv-nth 0 (read-char$ channel state))
           (CDDR (ASSOC-EQUAL CHANNEL (CAR STATE))))
  :hints (("Goal" :in-theory (enable read-char$))))

(defthm another-lemma
  (implies (and (equal (mv-nth 0 (read-char$ channel state))
                       #\newline)
                (equal (len (coerce lexeme 'list)) 0)
                keep-newline (symbolp channel)
                (booleanp keep-newline)
                (character-listp whitespace)
                (stringp lexeme)
                (state-p state)
                (open-input-channel-p1 channel
                                       :character state)
                (coerce (append (coerce lexeme 'list)
                                '(#\newline))
                        'string))
           (< (file-measure channel nil)
              (file-measure channel state)))
  :hints (("Goal" :in-theory (enable file-measure))))

(DEFTHM |FILE-MEASURE-OF-READ-NEXT-BNF-LEXEME1-STRONG Subgoal *1/6|
  (IMPLIES (AND (NOT (NULL (MV-NTH 0 (READ-CHAR$ CHANNEL STATE))))
                (NOT (AND (EQUAL (MV-NTH 0 (READ-CHAR$ CHANNEL STATE))
                                 #\=)
                          (EQUAL LEXEME "::")))
                (NOT (AND (EQUAL (MV-NTH 0 (READ-CHAR$ CHANNEL STATE))
                                 #\>)
                          (CONSP LEXEME)
                          (EQUAL (CAR (STR::FIRSTN-CHARS 1 LEXEME))
                                 #\<)))
                (NOT (AND (EQUAL (MV-NTH 0 (READ-CHAR$ CHANNEL STATE))
                                 #\|)
                          (EQUAL (LENGTH LEXEME) 0)))
                (NOT (AND (EQUAL (MV-NTH 0 (READ-CHAR$ CHANNEL STATE))
                                 #\Newline)
                          (EQUAL (LENGTH LEXEME) 0)
                          KEEP-NEWLINE))
                (AND (MEMBER-EQUAL (MV-NTH 0 (READ-CHAR$ CHANNEL STATE))
                                   WHITESPACE)
                     (EQUAL (LENGTH LEXEME) 0))
                (IMPLIES (AND (SYMBOLP CHANNEL)
                              (BOOLEANP KEEP-NEWLINE)
                              (CHARACTER-LISTP WHITESPACE)
                              (STRINGP LEXEME)
                              (STATE-P (MV-NTH 1 (READ-CHAR$ CHANNEL STATE)))
                              (OPEN-INPUT-CHANNEL-P
                               CHANNEL
                               :CHARACTER (MV-NTH 1 (READ-CHAR$ CHANNEL STATE)))
                              (NOT
                               (MV-NTH
                                1
                                (READ-NEXT-BNF-LEXEME1 CHANNEL KEEP-NEWLINE WHITESPACE LEXEME
                                                       (MV-NTH 1 (READ-CHAR$ CHANNEL STATE))))))
                         (<
                          (FILE-MEASURE
                           CHANNEL
                           (MV-NTH
                            2
                            (READ-NEXT-BNF-LEXEME1 CHANNEL KEEP-NEWLINE WHITESPACE LEXEME
                                                   (MV-NTH 1 (READ-CHAR$ CHANNEL STATE)))))
                          (FILE-MEASURE CHANNEL
                                        (MV-NTH 1 (READ-CHAR$ CHANNEL STATE))))))
           (IMPLIES
            (AND
             (SYMBOLP CHANNEL)
             (BOOLEANP KEEP-NEWLINE)
             (CHARACTER-LISTP WHITESPACE)
             (STRINGP LEXEME)
             (STATE-P STATE)
             (OPEN-INPUT-CHANNEL-P CHANNEL
                                   :CHARACTER STATE)
             (NOT
              (MV-NTH
               1
               (READ-NEXT-BNF-LEXEME1 CHANNEL
                                      KEEP-NEWLINE WHITESPACE LEXEME STATE))))
            (<
             (FILE-MEASURE
              CHANNEL
              (MV-NTH
               2
               (READ-NEXT-BNF-LEXEME1 CHANNEL
                                      KEEP-NEWLINE WHITESPACE LEXEME STATE)))
             (FILE-MEASURE CHANNEL STATE))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d () (file-measure))))

;  :otf-flg t
  :RULE-CLASSES NIL)


(DEFTHM |FILE-MEASURE-OF-READ-NEXT-BNF-LEXEME1-STRONG Subgoal *1/7|
  (IMPLIES
   (AND
    (NOT (NULL (MV-NTH 0 (READ-CHAR$ CHANNEL STATE))))
    (NOT (AND (EQUAL (MV-NTH 0 (READ-CHAR$ CHANNEL STATE))
                     #\=)
              (EQUAL LEXEME "::")))
    (NOT (AND (EQUAL (MV-NTH 0 (READ-CHAR$ CHANNEL STATE))
                     #\>)
              (CONSP LEXEME)
              (EQUAL (CAR (STR::FIRSTN-CHARS 1 LEXEME))
                     #\<)))
    (NOT (AND (EQUAL (MV-NTH 0 (READ-CHAR$ CHANNEL STATE))
                     #\|)
              (EQUAL (LENGTH LEXEME) 0)))
    (NOT (AND (EQUAL (MV-NTH 0 (READ-CHAR$ CHANNEL STATE))
                     #\Newline)
              (EQUAL (LENGTH LEXEME) 0)
              KEEP-NEWLINE))
    (NOT (AND (MEMBER-EQUAL (MV-NTH 0 (READ-CHAR$ CHANNEL STATE))
                            WHITESPACE)
              (EQUAL (LENGTH LEXEME) 0)))
    (IMPLIES
     (AND
      (SYMBOLP CHANNEL)
      (BOOLEANP KEEP-NEWLINE)
      (CHARACTER-LISTP WHITESPACE)
      (STRINGP
       (STRING-APPEND LEXEME
                      (STRING (MV-NTH 0 (READ-CHAR$ CHANNEL STATE)))))
      (STATE-P (MV-NTH 1 (READ-CHAR$ CHANNEL STATE)))
      (OPEN-INPUT-CHANNEL-P
       CHANNEL
       :CHARACTER (MV-NTH 1 (READ-CHAR$ CHANNEL STATE)))
      (NOT
       (MV-NTH
        1
        (READ-NEXT-BNF-LEXEME1
         CHANNEL KEEP-NEWLINE WHITESPACE
         (STRING-APPEND LEXEME
                        (STRING (MV-NTH 0 (READ-CHAR$ CHANNEL STATE))))
         (MV-NTH 1 (READ-CHAR$ CHANNEL STATE))))))
     (<
      (FILE-MEASURE
       CHANNEL
       (MV-NTH
        2
        (READ-NEXT-BNF-LEXEME1
         CHANNEL KEEP-NEWLINE WHITESPACE
         (STRING-APPEND LEXEME
                        (STRING (MV-NTH 0 (READ-CHAR$ CHANNEL STATE))))
         (MV-NTH 1 (READ-CHAR$ CHANNEL STATE)))))
      (FILE-MEASURE CHANNEL
                    (MV-NTH 1 (READ-CHAR$ CHANNEL STATE))))))
   (IMPLIES
    (AND
     (SYMBOLP CHANNEL)
     (BOOLEANP KEEP-NEWLINE)
     (CHARACTER-LISTP WHITESPACE)
     (STRINGP LEXEME)
     (STATE-P STATE)
     (OPEN-INPUT-CHANNEL-P CHANNEL
                           :CHARACTER STATE)
     (NOT
      (MV-NTH
       1
       (READ-NEXT-BNF-LEXEME1 CHANNEL
                              KEEP-NEWLINE WHITESPACE LEXEME STATE))))
    (<
     (FILE-MEASURE
      CHANNEL
      (MV-NTH
       2
       (READ-NEXT-BNF-LEXEME1 CHANNEL
                              KEEP-NEWLINE WHITESPACE LEXEME STATE)))
     (FILE-MEASURE CHANNEL STATE))))
  :RULE-CLASSES NIL)


(local
 (defthm file-measure-of-read-next-bnf-lexeme1-strong
   (implies 
    (and (symbolp channel)
         (booleanp keep-newline)
         (character-listp whitespace)
         (stringp lexeme)
         (state-p state)
         (open-input-channel-p channel :character state)
         (not
          (mv-nth 1 (read-next-bnf-lexeme1 channel keep-newline
                                          whitespace lexeme state)))
         ;; (stringp 
         ;;  (mv-nth 0 (read-next-bnf-lexeme1 channel keep-newline
         ;;                                  whitespace lexeme state)))
         ;; (< 0
         ;;    (length (mv-nth 0 (read-next-bnf-lexeme1 channel keep-newline
         ;;                                             whitespace lexeme
         ;;                                             state))))
         )
    (< (file-measure channel
                     (mv-nth 2 (read-next-bnf-lexeme1 channel keep-newline
                                                      whitespace lexeme state)))
       (file-measure channel state)))
   :hints (("Goal" :induct t :in-theory (e/d
                                         (read-next-bnf-lexeme1)
                                         (file-measure mv-nth state-p)))
           ("Subgoal *1/7" :by nil) ;; :expand ((:free (keep-newline whitespace lexeme)
                                    ;;        (read-next-bnf-lexeme1 channel
                                    ;;                               keep-newline
                                    ;;                               whitespace lexeme
                                    ;;                              state))))
           ("Subgoal *1/6" :by nil ;; :expand ((:free (keep-newline whitespace lexeme)
                                   ;;         (read-next-bnf-lexeme1 channel
                                   ;;                                keep-newline
                                   ;;                                whitespace lexeme
                                   ;;                                state)))))
            )
           ("Subgoal *1/1" :expand ((:free (keep-newline whitespace lexeme)
                                           (read-next-bnf-lexeme1 channel 
                                                                  keep-newline
                                                                  whitespace lexeme state))))
           )
   :rule-classes (:rewrite :linear)))
|#


(define read-next-bnf-lexeme ((channel symbolp)
                              (keep-newline booleanp)
                              state) ; keep-newline should be nil if not specified
;  "Reads and returns the next Backus-Naur lexeme from file."
  :guard (open-input-channel-p channel :character state)
  :returns (mv (lexeme "String or nil") ; (equal lexeme (if lexeme (stringp lexeme) t)) :hyp :fguard)
               (eof-p booleanp :hyp :fguard "Whether read-next-bnf-lexeme has ~
                                             reached the end of the file")
               (state "ACL2 state"))
  :stobjs (state)
  (let ((whitespace (list #\Space #\Tab))
        ;; (lexeme "") ; not used
        )

    (mv-let 
      (lexeme eof-p state)
      (read-next-bnf-lexeme1 channel 
                             keep-newline 
                             (if keep-newline 
                                 whitespace
                               (cons #\Newline whitespace))
                             ""
                             state)
      (if (> (length lexeme) 0) 
          (mv (str-trim (list #\< #\>) lexeme) 
              eof-p ; (assert$ (not eof-p) eof-p)
              state)
        (mv nil eof-p state)))))

(local
 (defthm file-measure-of-read-next-bnf-lexeme-weak
   (implies 
    (and (symbolp channel)
         (booleanp keep-newline)
         (state-p state)
         (open-input-channel-p channel :character state))
    (<= (file-measure channel
                      (mv-nth 2 (read-next-bnf-lexeme channel keep-newline state)))
        (file-measure channel state)))
    :hints (("Goal" ;:induct t 
             :in-theory (e/d
                         (read-next-bnf-lexeme)
                         (file-measure mv-nth))))
    :rule-classes (:rewrite :linear)))


(skip-proofs ; termination fails (beyond too probably)
(define read-next-bnf-production1 ((channel symbolp)
                                   (keep-newline booleanp)
                                   (production string-list-p) 
                                   (state state-p))
   :measure (file-measure channel state)
   :hints (("Goal" :induct t
            :in-theory (e/d () 
                            (file-measure mv-nth))))
   :returns (mv (productions string-list-p)
                (state state-p))
   (let ((lexeme-cache (f-get-global 'lexeme-cache state)))
     (mv-let (lexeme eof-p state)
       (read-next-bnf-lexeme channel keep-newline state) ; make sure I account for this in translation
       (cond ((or (null lexeme) eof-p)
              (mv (reverse production) #|eof-p|# state))
             ;; If we just read a "::=" and there already is one in the
             ;; production -> Push it and last lexeme onto cache instead of
             ;; production
             ((and (equal lexeme "::=")
                   (member lexeme production))
              (let* ((lexeme-cache (cons lexeme lexeme-cache))
                     (lexeme-cache (cons (car production) lexeme-cache))
                     (production (cdr production))
                     (state (f-put-global 'lexeme-cache lexeme-cache state)))
                (mv (reverse production) #|eof-p|# state)))
             (t (let ((production (cons lexeme production)))
                  (read-next-bnf-production1 channel keep-newline production state))))))))

(local
 (defthm file-measure-of-read-next-bnf-production-weak
   (<= (file-measure channel (mv-nth 1 (read-next-bnf-production1 channel
                                                                  keep-newline
                                                                  production 
                                                                  state)))
       (file-measure channel state))
   :hints (("Goal" :in-theory (enable file-measure read-next-bnf-production1)))
   :rule-classes (:rewrite :linear)))

(define fix-production ((lexeme-cache string-list-p)
                        (production string-list-p))
  :returns (productions string-list-p "New list of production strings" :hyp :guard)
  (append (reverse lexeme-cache) production))

(define read-next-bnf-production ((channel symbolp)
                                  (keep-newline booleanp)
                                  (state state-p))
  "Reads and returns the next Backus-Naur production from file."
  :guard (and (BOUNDP-GLOBAL 'LEXEME-CACHE STATE)
              (STRING-LIST-P (GET-GLOBAL 'LEXEME-CACHE STATE)))
  :returns (mv (productions string-list-p)
               (state state-p))
  :stobjs (state)
; Seems to be working when compared with CL trace output.
  (let ((lexeme-cache (f-get-global 'lexeme-cache state)) ; silly
        (production nil)) ; silly
    ;; If there is anything in the cache, pop it off and add it to production
    ;; (read-next-bnf-production-cache lexeme-cache lexeme-cache production)
    (let* ((production (fix-production lexeme-cache production)) ; silly but it's part of the original code
           (state (f-put-global 'lexeme-cache nil state)))
      (read-next-bnf-production1 channel keep-newline production state))))


(cutil::deflist string-list-list-p (x)
  (string-list-p x)
  :elementp-of-nil t
  :true-listp t)

;; (defn rule-p (rule)
;;   (and (consp rule)
;;        (stringp (car rule)) ; like "S", "NP", and "VP"
;;        (string-list-list-p (cdr rule))))

;; (defn rule-list-p (lst)
;; ; Rules 
;;   (cond ((atom lst)
;;          (null lst))
;;         (t 
;;          (and (rule-p (car lst))
;;               (rule-list-p (cdr lst))))))

(cutil::defalist rule-list-p (x)
  :key (stringp x)
  :val (string-list-list-p x)
  :true-listp t)

;; (local
;;  (defthm append-string-lists-lemma
;;    (implies (and (string-list-p x)
;;                  (string-list-p y))
;;             (string-list-p (append x y)))))

;; (defthm rule-list-p-lemma
;;   (implies (rule-list-p rules)
;;            (rule-list-p (hons-shrink-alist rules nil))))
;;   :hints (("Goal" :in-theory (enable hons-shrink-alist)))))

;; (defthm rule-list-p-lemma
;;   (implies (rule-list-p rules)
;;            (RULE-LIST-P
;;             (HONS-SHRINK-ALIST RULES
;;                                (LIST (LIST* (CAR PRODUCTION)
;;                                             EXPANSION
;;                                             (CDR (HONS-ASSOC-EQUAL (CAR PRODUCTION)
;;                                                                    RULES))))))))
;; (thm 
;;  (IMPLIES (AND (STRING-LIST-P PRODUCTION)
;;                (TRUE-LISTP PRODUCTION)
;;                (RULE-LIST-P RULES)
;;                (STRING-LIST-P EXPANSION)
;;                (TRUE-LISTP EXPANSION)
;;                (STRING-LIST-P TARGET-LIST) 
;;                (CONSP TARGET-LIST)
;;                (TRUE-LISTP TARGET-LIST)
;;                (EQUAL (CAR TARGET-LIST) "|") 
;;                (STRINGP (CAR TARGET-LIST)))
;;           (CONSP PRODUCTION)))


(define inject-expansions! ((target-list string-list-p)
                            (expansion string-list-p)
                            (rules rule-list-p)
                            (production (and (string-list-p production)
                                             (consp production))))
  :returns (rules rule-list-p :hyp :fguard)
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
                        production))))

(local
 (defthm file-measure-of-read-next-bnf-production-weak
   (<= (file-measure channel (mv-nth 1 (read-next-bnf-production channel nil state)))
       (file-measure channel state))
   :hints (("Goal" :in-theory (enable file-measure read-next-bnf-production)))
   :rule-classes (:rewrite :linear)))

(local
 (defthm file-measure-of-read-next-bnf-production-strong
   (implies (mv-nth 0 (read-next-bnf-production channel asdf state))
            (< (file-measure channel (mv-nth 1 (read-next-bnf-production
                                                channel asdf state)))
               (file-measure channel state)))
   :hints (("Goal" :in-theory (enable file-measure read-next-bnf-production)))
   :rule-classes (:rewrite :linear)))


(skip-proofs
(define load-bnf-grammar1 ((channel symbolp)
                            rules 
                            state)
  :guard (open-input-channel-p channel :character state)
  :stobjs (state)
  :measure (file-measure channel state) ; this file-measure is non-sense for this functions
   (mv-let (production state) ; could use a flag other than production to indicate termination
     (read-next-bnf-production channel nil state)
     (cond ((null production)
            (mv rules state))
           (t (let ((rules (inject-expansions! (cddr production) nil rules production)))
                (load-bnf-grammar1 channel rules state)))))))

; admits once make-grammar is defined
(defun load-bnf-grammar (pathname state)
  "Reads a grammar on Backus-Naur form into the representation of the context 
   free grammar(CFG)."
  (let ((rules nil)) ; hash table
    ;; For each production in the BNF file, create a list of possible ordered
    ;; symbol sequences (list of strings) that is a legal expression for the
    ;; symbol
    (mv-let (channel state)
      (open-input-channel pathname :character state)
      (mv-let (rules state)
        (load-bnf-grammar1 channel rules state)
        (let ((rules (hons-shrink-alist rules nil)))
          (mv (make-grammar :rules rules) state))))))


;;;; Lexicon functions
;;;;------------------
;;;; Reads a dictionary on the form:
;;;;
;;;; <word> :class <class> :gender <gender>
;;;;
;;;; into a hashtable of lists of word instances and 
;;;; a list of word classes (part of speech).


;; (defun read-lexicon-line-comparer (words)
;;   (declare (xargs :guard (word-list-p words)
;;                   :verify-guards nil))
;;   (cond ((atom words)
;;          nil)
;;         (t (let ((word (car words)))
;;              (cons (if (equal (char word 0) #\:)
;;                        (intern word "ACL2")
;;                      word)
;;                    (read-lexicon-line-comparer (cdr words)))))))

(cutil::deflist string-list-p (x)
  (stringp x)
  :elementp-of-nil nil
  :true-listp t)

(set-verify-guards-eagerness 0)

(defun read-lexicon-line-options (strings)
  (declare (xargs :guard (and (string-list-p strings)
                              (evenp (len strings)))
                  :measure (len strings)))
  (cond ((atom strings)
         nil)
        (t (cons (cons (intern (str-trim '(#\:)
                                         (str::upcase-string (car strings)))
                               "KEYWORD")
                       (cadr strings))
                 (read-lexicon-line-options (cddr strings))))))

(defun read-lexicon-line (channel state)
  "Read a line from the given file, and return the corresponding terminal."
  ;; Parse a line from the file
  (mv-let (line state)
    (read-line$ channel state)
    (cond ((or (null line) (equal line ""))
           (mv nil state))
          (t 
           (let* ((words (remove "" (str::strtok line '(#\Space))))
                  (string (first words))
                  (options (read-lexicon-line-options (cdr words))))
             ;; Create the word object
             (mv (make-terminal :word string
                                :class (str-trim '(#\< #\>) 
                                                 (or (cdr (assoc :class
                                                                 options))
                                                     ""))
                                :gender (cdr (assoc :gender options)))
                 state))))))

(skip-proofs
 (defun load-lexicon1 (lexicon part-of-speech-list channel state)
   (declare (xargs :guard (and ;(state-p1 state)
                           (symbolp channel)
                           (open-input-channel-p channel
                                                 :character state))
                   :verify-guards nil
                   :measure (file-measure channel state)))

   (mv-let (terminal state)
     (read-lexicon-line channel state) 
     (cond ((null terminal) ; source of a bug, what if the lex file contains a blank line?
            (mv lexicon part-of-speech-list state))
           (t 
            (b* ((word (terminal->word terminal))
                 (curr-terminal-list (cdr (hons-get word lexicon))))
                
              (load-lexicon1 (hons-acons word 
                                         (hons terminal curr-terminal-list) ; this could be a bug, if it turns out that a word can only be associated with one terminal, but that's not the case
                                         lexicon)
                             (cons (terminal->class terminal)
                                   part-of-speech-list)
                             channel state)))))))


(defun load-lexicon (filename state)
  (let ((lexicon nil) ; use a hashtable
        (part-of-speech-list nil))
    (mv-let (channel state)
      (open-input-channel filename :character state)
      (mv-let (lexicon part-of-speech-list state)
        (load-lexicon1 lexicon part-of-speech-list channel state)
        (mv (make-lexicon :dictionary lexicon
                          :part-of-speech part-of-speech-list)
            state)))))

  
