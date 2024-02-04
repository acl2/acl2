;(acl2::begin-book t :ttags :all)
(in-package "ACL2")
(include-book "centaur/fty/top" :dir :system)

(include-book "centaur/fty/basetypes" :dir :system :ttags :all)
(include-book "std/io/top" :dir :system)


(include-book "arithmetic-5/top" :dir :system)
(include-book "std/lists/top" :dir :system)
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags
              ((:ccg)) :load-compiled-file nil)

;(include-book "acl2s/mode-acl2s-dependencies" :dir :system :ttags :all)

(include-book "acl2s/base-theory" :dir :system :ttags :all)

(include-book "acl2s/ccg/ccg" :dir :system :ttags :all)
(include-book "acl2s/custom" :dir :system :ttags :all)
(acl2s-common-settings)

;(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))

; Matt K. mod: Avoid ACL2(p) error.
(set-waterfall-parallelism nil)

(defthm subseq-character-list3
  (implies
   (and
   (character-listp contents)
   (natp index)
   (subseq contents index NIL)
   )
   (character-listp  (subseq contents index  NIL)
  )

  )
  :hints (("Goal" :in-theory (enable                (:COMPOUND-RECOGNIZER NATP-COMPOUND-RECOGNIZER)
        (:DEFINITION LENGTH)
        (:DEFINITION NATP)
        (:DEFINITION SUBSEQ)
        (:FORWARD-CHAINING CHARACTER-LISTP-FORWARD-TO-EQLABLE-LISTP)
        (:FORWARD-CHAINING EQLABLE-LISTP-FORWARD-TO-ATOM-LISTP)
        (:REWRITE LIST-FIX-WHEN-TRUE-LISTP)
        (:REWRITE ACL2S::NTHCDR-CHARACTER-LISTP-SIG)
        (:REWRITE SUBSEQ-LIST-OF-LEN)
        (:TYPE-PRESCRIPTION CHARACTER-LISTP)
        (:TYPE-PRESCRIPTION EQLABLE-LISTP))
)))


;;Helper Functions and types

;Parse function outputs are stored in an ast object with a string type and value (parse result)
(fty::defprod ast-obj
   ((type stringp :default "")
   (value any-p :default "" )
   ))


; Helper function to check if a parse succeeded
(defun ast-obj-null (obj)
  (declare (xargs :guard (and
                           T
                            )))
  (if (ast-obj-p obj)
   (equal (ast-obj->type obj) "null")
   T
   )
  )
(defthm ast-not-null-correct-type
  (implies
   (not (ast-obj-null obj))
   (ast-obj-p obj)
   )
  )
;Combines 2 asts into a sequence, or concatenates the second ast to an  ast sequence
(defund combine2-ast-objs (res1 res2)
  (declare (xargs :guard (and
                            (ast-obj-p res1)
                            (ast-obj-p res2)
                            )))
  (if (and (not (ast-obj-null res1)) (not (ast-obj-null res2)))
    (if (and (equal (ast-obj->type  res1) "sequence") (true-listp (ast-obj->value  res1)))
      (ast-obj "sequence" (append (ast-obj->value res1)  res2))
    (ast-obj "sequence" (list  res1 res2))
    )
    (ast-obj "null" NIL )
  )
  )
(defthm combine2-ast-objs-ast-obj
  (ast-obj-p (combine2-ast-objs res1 res2))
    :hints (("Goal" :in-theory (enable combine2-ast-objs)))
)
(defthm combine2-ast-objs-not-null
  (implies
   (or
   (ast-obj-null ast1)
   (ast-obj-null ast2)
   )
   (ast-obj-null (combine2-ast-objs ast1 ast2))
  )
     :hints (("Goal" :in-theory (enable combine2-ast-objs)))
  )
(defthm combine2-ast-objs-not-null2
  (implies
   (and
  (not  (ast-obj-null ast1))
  (not  (ast-obj-null ast2))
   )
 (not  (ast-obj-null (combine2-ast-objs ast1 ast2)))
  )
     :hints (("Goal" :in-theory (enable combine2-ast-objs)))
  )

(defund index-of-subseq (seq1 seq2)
  (declare (xargs :guard (and (true-listp seq1)
                              ;(consp seq1)
                              (true-listp seq2))))
  (if (endp seq2)
      nil ; seq1 cannot occur, since seq1 is non-empty
    (if (prefixp seq1 seq2)
        0 ; seq1 is within seq2 at position 0
      (let ((res (index-of-subseq seq1 (rest seq2))))
        (and res
             (+ 1 res))))))

;Functions as replacement for search
(defthm index-of-subseq-self
  (implies (consp (double-rewrite seq))
           (equal (index-of-subseq seq seq)
                  0))
  :hints (("Goal"  :in-theory (enable index-of-subseq ))))

(defthm <-of-index-of-subseq-and-len
  (implies (index-of-subseq seq1 seq2)
           (< (index-of-subseq seq1 seq2) (len seq2)))
  :hints (("Goal" :in-theory (enable index-of-subseq))))

(defthm not-index-of-subseq-when-of-len-and-len
  (implies (< (len seq2) (len seq1))
           (not (index-of-subseq seq1 seq2)))
  :hints (("Goal" :in-theory (enable index-of-subseq))))

(defthm subseq-greater-0
  (implies (index-of-subseq seq1 seq2)
           (<= 0 (index-of-subseq seq1 seq2))
           )
  :hints (("Goal" :in-theory (enable index-of-subseq))))


(defund index-of-subseq-from-end (seq1 seq2)
    (declare  (xargs :guard (and (true-listp seq1)
                              (true-listp seq2))))
    (if (and (index-of-subseq (reverse seq1) (reverse seq2)) (< 0 (len seq1)) seq2)
     ( -  ( - (len seq2) (index-of-subseq (reverse seq1) (reverse seq2)) ) (len seq1))
      NIL
      )
  )

(defthm <-of-index-of-subseq-from-end-and-len
  (implies (and (index-of-subseq-from-end seq1 seq2)
                )
           (<= (index-of-subseq-from-end seq1 seq2) (len seq2)))
  :hints (("Goal" :in-theory (enable index-of-subseq-from-end))))

(defthm <-of-index-of-subseq-from-end-and-len2
  (implies (index-of-subseq-from-end seq1 seq2)
           (<= ( + (len seq1) (index-of-subseq-from-end seq1 seq2) ) (len seq2)))
  :hints (("Goal" :in-theory (enable index-of-subseq-from-end))))

(defun digit-charlist-p (list)
     (declare (xargs :guard  (character-listp list)
                     :measure (len list)
                 ;  :hints (("Goal" :hands-off (digit-char-p)))
              ))
     (if ( < 0 (len list))
       (and (digit-char-p (car list)) (digit-charlist-p (cdr list)))
       T
       )
  )

(defund convert-charlist-to-natural-helper (list)
   (declare (xargs :guard (and (character-listp list)
                               )
                   :measure (list)
;                     :guard-hints (("Goal" :hands-off (digit)))
                   )
            )
   (if (and (consp list) (digit-charlist-p list))
       (+  (digit-char-p (car list)) (* 10 (convert-charlist-to-natural-helper (cdr list ))) )
        0
     )
  )

(defthm convert-charlist-base-nat
   (natp (convert-charlist-to-natural-helper contents))
     :hints (("Goal" :in-theory (enable convert-charlist-to-natural-helper)))
    )

(defund convert-charlist-to-natural (list)
   (declare (xargs :guard (and (character-listp list)
                               )))
   (convert-charlist-to-natural-helper (reverse list))

   )
(defthm convert-charlist-nat
   (natp (convert-charlist-to-natural contents))
        :hints (("Goal" :in-theory (enable convert-charlist-to-natural)))
    )



(defun index-of-first-non-digit (contents)
  (declare (xargs :guard
                           (character-listp contents)
                            ))
  (if (< 0 (length contents) )
    (if (digit-char-p (car contents))
      (+ 1 (index-of-first-non-digit (cdr contents)))
       0
      )
      0
    )
  )







(defthm index-of-first-non-digit-len2
   ;(implies (natp (index-of-first-non-digit contents))
            (<= (index-of-first-non-digit contents) (len contents))
    ;        )
  )


  (defthm subseq-character-list2
  (implies
   (and
   (character-listp contents)
   (subseq contents 0 (index-of-first-non-digit contents))
   )
   (character-listp  (subseq contents 0 (index-of-first-non-digit contents)))
  )
    :hints (("Goal" :in-theory (enable index-of-first-non-digit
                                               (:DEFINITION ASSOC-EQUAL)
        (:DEFINITION CHARACTER-LISTP)
        (:DEFINITION INDEX-OF-FIRST-NON-DIGIT)
        (:DEFINITION LENGTH)
        (:DEFINITION NOT)
        (:DEFINITION OUR-DIGIT-CHAR-P)
        (:DEFINITION SUBSEQ)
        (:DEFINITION SYNP)
        (:ELIM CAR-CDR-ELIM)
        (:EXECUTABLE-COUNTERPART <)
        (:EXECUTABLE-COUNTERPART ASSOC-EQUAL)
        (:EXECUTABLE-COUNTERPART BINARY-+)
        (:EXECUTABLE-COUNTERPART CAR)
        (:EXECUTABLE-COUNTERPART CDR)
        (:EXECUTABLE-COUNTERPART CHARACTER-LISTP)
        (:EXECUTABLE-COUNTERPART CHARACTERP)
        (:EXECUTABLE-COUNTERPART CONS)
        (:EXECUTABLE-COUNTERPART CONSP)
        (:EXECUTABLE-COUNTERPART NOT)
        (:EXECUTABLE-COUNTERPART OUR-DIGIT-CHAR-P)
        (:EXECUTABLE-COUNTERPART TAU-SYSTEM)
        (:FORWARD-CHAINING CHARACTER-LISTP-FORWARD-TO-EQLABLE-LISTP)
        (:FORWARD-CHAINING EQLABLE-LISTP-FORWARD-TO-ATOM-LISTP)
        (:INDUCTION CHARACTER-LISTP)
        (:INDUCTION INDEX-OF-FIRST-NON-DIGIT)
        (:REWRITE |(+ 0 x)|)
        (:REWRITE |(+ c (+ d x))|)
        (:REWRITE |(+ y (+ x z))|)
        (:REWRITE |(< 0 (len x))|)
        (:REWRITE ACL2S::CONS-CHARACTER-LISTP-SIG)
        (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP)
        (:REWRITE REDUCE-ADDITIVE-CONSTANT-<)
        (:REWRITE SUBSEQ-LIST-STARTING-FROM-ZERO)
        (:REWRITE TAKE-OF-1)
        (:REWRITE TAKE-OF-CONS)
        (:REWRITE TAKE-UNDER-IFF)
        (:REWRITE ZP-OPEN)
        (:TYPE-PRESCRIPTION CHARACTER-LISTP)
        (:TYPE-PRESCRIPTION EQLABLE-LISTP)
        (:TYPE-PRESCRIPTION INDEX-OF-FIRST-NON-DIGIT)
        (:TYPE-PRESCRIPTION LENGTH))
                                       ))
  )
(defthm take-charcter-list
  (IMPLIES (CHARACTER-LISTP CONTENTS)
         (CHARACTER-LISTP (TAKE (INDEX-OF-FIRST-NON-DIGIT CONTENTS)
                                CONTENTS)))

  )
(defthm index-of-first-non-digit-len2
   ;(implies (natp (index-of-first-non-digit contents))
            (<= (index-of-first-non-digit contents) (len contents))
    ;        )
  )
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; BASE PARSING FUNCTIONS ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;PARSE STRING ;;;;;;;;;;;;;;;;;;;;;;
;Parse a string at the start of the characterlist, and return (cons (ast-obj "string" string) remainder ) if the string is at the start, or ((ast-obj "null") contents) otherwise
(defund parse-string (string contents )
  (declare (xargs :guard (and (stringp string)
                              (character-listp contents))))
  (if (and (prefixp (explode string) contents) (character-listp (subseq contents (length (explode string)) NIL)))
     (cons (ast-obj "string" string) (subseq contents (length (explode string)) NIL))
    (cons (ast-obj "null" "") contents)
    )
  )
(defthm parse-string-cons
  (consp (parse-string string contents))
  )

(defthm parse-string-ast
  (ast-obj-p  (car (parse-string string contents)) )
   :hints (("Goal" :in-theory (enable parse-string)))
  )


(defthm parse-string-charlist
  (implies
   (character-listp contents)
  (character-listp (cdr (parse-string string contents)) )
  )
  :hints (("Goal" :in-theory (enable parse-string)))
  )

;;;;;;;;;;;;;;;;PARSE CHAR ;;;;;;;;;;;;;;;;;;;;;;;;
(defund parse-char (char contents)
   (declare (xargs :guard (and
                           (character-listp contents)
                           (characterp char)
                            )))
   (if (> (length contents) 0)
     (if (equal (car contents) char)
       (cons (ast-obj "char" (car contents)) (cdr contents))
       (cons (ast-obj "null" "") contents)
       )
     (cons (ast-obj "null" "") contents)
     )
  )

(defthm parse-char-cons
    (consp (parse-char char contents))

  )
(defthm parse-char-ast
   (ast-obj-p  (car (parse-char char contents)) )
           :hints (("Goal" :in-theory (enable parse-char)))
  )
(defthm parse-char-charlist
    (implies
      (character-listp contents)
      (character-listp  (cdr (parse-char char contents)) )
             )
               :hints (("Goal" :in-theory (enable parse-char)))
    )


;Return the string up to the string in form ((ast-obj "before-str" prefix) remainder), or ((ast-obj "null" ) contents) if string is not found
(defund parse-until-string-non-incl (string contents)
  (declare (xargs :guard (and
                           (character-listp contents)

                            (stringp string)
                            )))
  ;(if (and (natp  (index-of-subseq (explode string) contents)) (character-listp (subseq contents (index-of-subseq (explode string) contents) NIL) ) (<=  (index-of-subseq (explode string) contents)  (len contents)))
  (if (natp  (index-of-subseq (explode string) contents))
  (if (<=  (index-of-subseq (explode string) contents)  (len contents))
  (if (character-listp (subseq contents (index-of-subseq (explode string) contents) NIL))
  ;  (if  (and (<=  (index-of-subseq (explode string) contents)  (len contents)) (character-listp contents) (character-listp (subseq contents (index-of-subseq (explode string) contents) NIL)) )
    (cons (ast-obj "before-str" (implode (subseq contents 0 (index-of-subseq (explode string) contents))) )
            (subseq contents (index-of-subseq (explode string) contents) NIL))
      ;  (cons (ast-obj "null" "") contents)
        (cons (ast-obj "null" "") contents)
        )
        (cons (ast-obj "null" "") contents)
        )
    ;)
   (cons (ast-obj "null" "") contents)
    )

)

(defthm parse-until-string-non-incl-cons
  (implies (parse-until-string-non-incl string contents)
    (consp (parse-until-string-non-incl string contents))
    )
  )
(defthm parse-until-string-non-incl-ast
    (implies (parse-until-string-non-incl string contents)
             (ast-obj-p  (car (parse-until-string-non-incl string contents)) )
             )
               :hints (("Goal" :in-theory (enable parse-until-string-non-incl)))
  )
(defthm parse-until-string-non-incl-charlist
    (implies
     (and
     (parse-until-string-non-incl string contents)
      (character-listp contents)
      )
             (character-listp  (cdr (parse-until-string-non-incl string contents)) )
             )
                    :hints (("Goal" :in-theory (enable parse-until-string-non-incl)

                                             ))
  )

;Return all characters including the entire string to be searched, or ((ast-obj "null" ) contents) if string is not found
(defund parse-until-string (string contents)
  (declare (xargs :guard (and
                           (character-listp contents)

                            (stringp string)
                            )))
  (if (natp  (index-of-subseq (explode string) contents))
    (if  (and (<=  (+ (len (explode string )) (index-of-subseq (explode string) contents) ) (len contents)) (character-listp contents))
    (if (character-listp (subseq contents ( + (len (explode string)) (index-of-subseq (explode string) contents) ) NIL))
    (cons (ast-obj "until-str" (implode (subseq contents 0 (+ (len (explode string)) (index-of-subseq (explode string) contents))) ))
            (subseq contents ( + (len (explode string)) (index-of-subseq (explode string) contents) ) NIL))
                   (cons (ast-obj "null" "") contents)
            )
        (cons (ast-obj "null" "") contents)
    )
   (cons (ast-obj "null" "") contents)
    )

)



(defthm parse-until-string-cons

    (consp (parse-until-string string contents))

  )
(defthm parse-until-string-ast
   (ast-obj-p  (car (parse-until-string string contents)) )
                   :hints (("Goal" :in-theory (enable parse-until-string)))
  )
(defthm parse-until-string-charlist
    (implies
      (character-listp contents)
    (character-listp  (cdr (parse-until-string string contents)) )
             )
                       :hints (("Goal" :in-theory (enable parse-until-string)))
  )


;;;;;;;;;;;;;;;;;;PARSE WORD ;;;;;;;;;;;;;;;;;;;
(defund parse-word (contents)
   (declare (xargs :guard
                           (character-listp contents)
                            ))
  (parse-until-string-non-incl " " contents)
  )

(defthm parse-word-cons

    (consp (parse-word contents))

  )
(defthm parse-word-ast
   (ast-obj-p  (car (parse-word contents)) )
                      :hints (("Goal" :in-theory (enable parse-word)))
  )
(defthm parse-word-charlist
    (implies
      (character-listp contents)
      (character-listp  (cdr (parse-word contents)) )

             )
                          :hints (("Goal" :in-theory (enable parse-word)))
    )


 (defthm subseq-character-list4
  (implies
   (and
   (character-listp contents)
   (subseq contents 0 n)
   (natp n)
   (<= n (length contents))
   )
   (character-listp  (subseq contents 0 n))
  )
  )
;;;;;;;;;;;;;;;;;PARSE N CHARS ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;Return n characters as a list off the start of the characterlist, or (ast-obj "null") contents) if not enough characters


(defund parse-n-chars (n contents)
   (declare (xargs :guard (and
                           (character-listp contents)
                            (natp n)
                              )
                   ))
   (if (and (<= n (length contents)) (character-listp (subseq contents n NIL)))
     (cons (ast-obj  "charlist"  (subseq contents 0 n))
         (subseq contents n NIL))
      (cons (ast-obj "null" "") contents)
     )
  )
(defthm parse-n-chars-ast
  (ast-obj-p  (car (parse-n-chars n contents)) )
  :hints (("Goal" :in-theory (enable parse-n-chars)))
  )

(defthm parse-n-chars-charlist
  (implies
   (and
   (character-listp contents)
   (natp n)
   )
  (character-listp  (cdr (parse-n-chars n contents)) )
  )
    :hints (("Goal" :in-theory (enable parse-n-chars)))
  )



;;;;;;;;;;;;;;;;;PARSE STRING FROM END;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defund parse-string-from-end (string contents)
   (declare (xargs :guard (and (stringp string)
                               string
                                (character-listp contents)

                              )
                     :guard-hints (("Goal" :in-theory (disable index-of-subseq-from-end)))
                   ))
   (if (natp (index-of-subseq-from-end (explode string) contents))
   (if (character-listp (subseq contents ( +  (index-of-subseq-from-end (explode string) contents )
                                                                          (length (explode string)) ) NIL ))
     (cons (ast-obj "before-last-instance" string ) (subseq contents ( +  (index-of-subseq-from-end (explode string) contents )
                                                                          (length (explode string)) ) NIL )
                          )
                           (cons (ast-obj "null" "") contents)
                           )
       (cons (ast-obj "null" "") contents)
       )
  )



(defthm parse-string-from-end-cons
  (implies (parse-string-from-end string contents)
    (consp (parse-string-from-end string contents))
    )
  )
(defthm parse-string-from-end-ast
    (implies (parse-string-from-end string contents)
             (ast-obj-p  (car (parse-string-from-end string contents)) )
             )
    :hints (("Goal" :in-theory (enable parse-string-from-end)))
  )
(defthm parse-string-from-end-charlist
    (implies
     (and
     (parse-string-from-end string contents)
      (character-listp contents)
      )
             (character-listp  (cdr (parse-string-from-end string contents)) )
             )
      :hints (("Goal" :in-theory (enable parse-string-from-end)))
)

;;;;;;;;;;;;PARSE NUMBER ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defund parse-number-helper (contents)
      (declare (xargs :guard
                           (character-listp contents)
                              :guard-hints (("Goal" :hands-off (subseq)))
                            ))

   (if  (natp (convert-charlist-to-natural (subseq contents 0 (index-of-first-non-digit contents))))
    (convert-charlist-to-natural (subseq contents 0 (index-of-first-non-digit contents)))
    0
    )
  )
(defthm parse-number-helper-admits
  (parse-number-helper contents)
  )
(defthm index-of-first-non-digit-greater-zero
            (<= 0 (index-of-first-non-digit contents))
  )


(defthm parse-number-helper-natp
  (natp (parse-number-helper contents))
  )
;;;Returns the remainder after parsing the number
(defund parse-number-helper-remainder (contents)
      (declare (xargs :guard
                           (character-listp contents)
                              :guard-hints (("Goal" :hands-off (subseq)))
                            ))
  (if (and (natp (index-of-first-non-digit contents))(<=  (index-of-first-non-digit contents) (len contents))(character-listp (subseq contents (index-of-first-non-digit contents) NIL)) )
    (subseq contents (index-of-first-non-digit contents) NIL)
    (list )
    )
 ;    NIL

  )


(defthm parse-number-helper-remainder-charlist
  (implies
    (character-listp contents)
  (character-listp (parse-number-helper-remainder contents))
  )
   :hints (("Goal" :in-theory (enable parse-number-helper-remainder)))
  )
(defund parse-number (contents)
    (declare (xargs :guard
                           (character-listp contents)
                            ))

      (if (and (< 0 (length contents)) (digit-char-p (car contents)))
        (cons (ast-obj "number" (parse-number-helper contents))
            (parse-number-helper-remainder contents))
        (cons (ast-obj "null" "") contents)
      )

    )
(defthm parse-number-cons
  ;(implies
   ;(parse-trailer-part2 contents)
   (consp (parse-number contents))
 ; )
  )

(defthm parse-number-ast-obj

   (ast-obj-p (car (parse-number contents)) )
     :hints (("Goal" :in-theory (and (enable parse-number) )))
  )


(defthm parse-parse-number-charlist
    (implies
      (character-listp contents)
      (character-listp  (cdr (parse-number contents)) )
             )
     :hints (("Goal" :in-theory (and (enable parse-number) )))
    )
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;; COMPOSITE FUNCTION EXAMPLES ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;PDF HEADER ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun parse-header (contents)
  (declare (xargs :guard
                           (character-listp contents)

            :guard-hints (("Goal" :hands-off (parse-string parse-number parse-char )))
            )
           )
  (let* ((res1 (parse-string "%PDF-" contents))
         (res2 (parse-number (cdr res1)))
         (res3 (parse-char #\. (cdr res2)))
         (res4 (parse-number (cdr res3)))
         (res5 (parse-char #\Newline (cdr res4)))
         (ast1 (combine2-ast-objs (car res1) (car res2)))
         (ast2 (combine2-ast-objs ast1 (car res3)))
         (ast3 (combine2-ast-objs ast2 (car res4)))
         (ast4 (combine2-ast-objs ast3 (car res5)))
         )
       (if (and (not (ast-obj-null (car res1))) (character-listp (cdr res1)) )

                (if (and  (not (ast-obj-null (car res2)))(character-listp (cdr res2)) )
                     (if (and  (not (ast-obj-null (car res3)))(character-listp (cdr res3)))
                       (if (and  (not (ast-obj-null (car res4)))(character-listp (cdr res4)))
                         (if (and  (not (ast-obj-null (car res4)))(character-listp (cdr res4)))
                           (cons ast4 (cdr res5))
                           (cons (ast-obj "null" NIL) contents)
                           )
                         (cons (ast-obj "null" NIL) contents)
                         )
                   (cons (ast-obj "null" NIL) contents)
                  )
                 (cons (ast-obj "null" NIL) contents)
                )
                (cons (ast-obj "null" NIL) contents)
                )
             )
  )
(defthm parse-header-cons
  (consp (parse-header contents))
  )
(defthm parse-header-ast
 (ast-obj-p (car (parse-header contents)))
 :hints (("Goal" :in-theory (enable parse-header)))
  )
(defthm parse-header-characterlist
  (implies
   (character-listp contents)
 (character-listp (cdr (parse-header contents)))

  )
   :hints (("Goal" :in-theory (enable parse-header)))
  )


;;;;;;;;;;;;;;;;;;;;;;;;PDF XREF ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defund parse-option-char (char1 char2 contents)
  (declare (xargs :guard
                  (and
                           (character-listp contents)
                            (characterp char1)
                            (characterp char2)
                           )))
  (let ((res1 (parse-char char1 contents))
        (res2 (parse-char char2 contents))
        )
    (if (not (ast-obj-null (car res1)))
      res1
      res2
      )
    )

  )

(defthm parse-option-cons
  (consp (parse-option-char char1 char2 contents))
  )
(defthm parse-option-ast
 (ast-obj-p (car (parse-option-char char1 char2 contents)))
 :hints (("Goal" :in-theory (enable parse-option-char)))
  )
(defthm parse-option-characterlist
  (implies
   (character-listp contents)
 (character-listp (cdr (parse-option-char char1 char2 contents)))

  )
   :hints (("Goal" :in-theory (enable parse-option-char)))
  )



(defund parse-xref-sequence (contents)
  (declare (xargs :guard
                           (character-listp contents)

            :guard-hints (("Goal" :hands-off (parse-number parse-char parse-option-char  )))
            )
           )
  (let* ((res1 (parse-number contents))
         (res2 (parse-char #\Space (cdr res1)))
         (res3 (parse-number (cdr res2)))
         (res4 (parse-char #\Space (cdr res3)))
         (res5 (parse-option-char #\n #\f (cdr res4)))
         (res6 (parse-char #\Newline (cdr res5)))
         (ast1 (combine2-ast-objs (car res1) (car res2)))
         (ast2 (combine2-ast-objs ast1 (car res3)))
         (ast3 (combine2-ast-objs ast2 (car res4)))
         (ast4 (combine2-ast-objs ast3 (car res5)))
         (ast5 (combine2-ast-objs ast4 (car res6)))
         )
       (if (and (not (ast-obj-null (car res1))) (character-listp (cdr res1)) )

                (if (and  (not (ast-obj-null (car res2)))(character-listp (cdr res2)) )
                     (if (and  (not (ast-obj-null (car res3)))(character-listp (cdr res3)))
                       (if (and  (not (ast-obj-null (car res4)))(character-listp (cdr res4)))
                        (if (and  (not (ast-obj-null (car res5)))(character-listp (cdr res5)))
                           (if (and  (not (ast-obj-null (car res6)))(character-listp (cdr res6)))
                             (cons ast5 (cdr res6))
                             (cons (ast-obj "null" NIL) contents)
                              )
                           (cons (ast-obj "null" NIL) contents)
                           )

                         (cons (ast-obj "null" NIL) contents)
                         )
                      (cons (ast-obj "null" NIL) contents)
                  )
                 (cons (ast-obj "null" NIL) contents)
                )
                (cons (ast-obj "null" NIL) contents)
                )
             )
  )

(defthm parse-xref-sequence-cons
  (consp (parse-xref-sequence contents))
  )

(defthm parse-xref-sequence-ast
  (ast-obj-p (car (parse-xref-sequence contents)))
    :hints (("Goal"  :in-theory (and (enable parse-xref-sequence) )))
  )

  (defthm parse-xref-sequence-characterlist
    (implies
     (character-listp contents)
  (character-listp (cdr (parse-xref-sequence contents)))
  )
    :hints (("Goal"  :in-theory (and (enable parse-xref-sequence) )))
  )

(defund parse-xref-entry-repetition (prefix contents )
    (declare (xargs :guard
                         (and  (character-listp contents)
                           )

             )
             )


 (let ((res1 (parse-xref-sequence contents) ))
    (if (ast-obj-p prefix)
      (if (character-listp contents)

        (if  (< 0  (len contents) )
          (if (and (not (ast-obj-null (car res1))) (< (len (cdr res1)) (len contents)))
            (parse-xref-entry-repetition (combine2-ast-objs prefix (car res1) ) (cdr res1) )
            (cons prefix contents)
            )
          (cons prefix contents)
          )
              (cons (ast-obj "null" NIL) contents)
              )
            (cons (ast-obj "null" NIL) contents)
     )
    )

  )

(defthm parse-xref-entry-repetition-cons
  (consp (parse-xref-entry-repetition prefix contents))
  )

(defthm parse-xref-entry-repetition-ast
  (ast-obj-p (car (parse-xref-entry-repetition prefix contents)))
    :hints (("Goal"  :in-theory (and (enable parse-xref-entry-repetition) )))
  )

  (defthm parse-xref-entry-repetition-characterlist
    (implies
     (character-listp contents)
  (character-listp (cdr (parse-xref-entry-repetition prefix contents)))
  )
    :hints (("Goal"  :in-theory (and (enable parse-xref-entry-repetition) )))
  )



(defun parse-xref-section (contents)
  (declare (xargs :guard
                           (character-listp contents)

            :guard-hints (("Goal" :hands-off (parse-number parse-char parse-string parse-xref-entry-repetition  )))
            )
           )
  (let* ((res1 (parse-string "xref" contents))
         (res2 (parse-char #\Newline (cdr res1)))
         (res3 (parse-char #\0 (cdr res2)))
         (res4 (parse-char #\Space (cdr res3)))
         (res5 (parse-number (cdr res4)))
         (res6 (parse-char #\Newline (cdr res5)))
         (ast1 (combine2-ast-objs (car res1) (car res2)))
         (ast2 (combine2-ast-objs ast1 (car res3)))
         (ast3 (combine2-ast-objs ast2 (car res4)))
         (ast4 (combine2-ast-objs ast3 (car res5)))
         (ast5 (combine2-ast-objs ast4 (car res6)))
         (res7 (parse-xref-entry-repetition ast5 (cdr res6)))

         )
      (if (and (not (ast-obj-null (car res1))) (character-listp (cdr res1)) )

                (if (and  (not (ast-obj-null (car res2)))(character-listp (cdr res2)) )
                     (if (and  (not (ast-obj-null (car res3)))(character-listp (cdr res3)))
                       (if (and  (not (ast-obj-null (car res4)))(character-listp (cdr res4)))
                        (if (and  (not (ast-obj-null (car res5)))(character-listp (cdr res5)))
                           (if (and  (not (ast-obj-null (car res6)))(character-listp (cdr res6)))
                              (if (and  (not (ast-obj-null (car res7)))(character-listp (cdr res7)))
                                 res7
                                  (cons (ast-obj "null" NIL) contents)
                                )
                             (cons (ast-obj "null" NIL) contents)
                              )
                           (cons (ast-obj "null" NIL) contents)
                           )

                         (cons (ast-obj "null" NIL) contents)
                         )
                      (cons (ast-obj "null" NIL) contents)
                  )
                 (cons (ast-obj "null" NIL) contents)
                )
                (cons (ast-obj "null" NIL) contents)
                )
             )
  )


(defthm parse-xref-section-cons
  (consp (parse-xref-section contents))
  )
(defthm parse-xref-section-ast
 (ast-obj-p (car (parse-xref-section contents)))
 :hints (("Goal" :in-theory (enable parse-xref-section)))
  )
(defthm parse-xref-section-characterlist
  (implies
   (character-listp contents)
 (character-listp (cdr (parse-xref-section contents)))

  )
   :hints (("Goal" :in-theory (enable parse-xref-section)))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; PDF OBJECTS ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defund parse-char-optional (char contents)
   (declare (xargs :guard
                   (and
                           (character-listp contents)
                            (characterp char)
                            )
                            )
            )
   (let ((res (parse-char char contents))
         )
     (if (not (ast-obj-null (car res)))
       res
       (cons (ast-obj "optional-char" "") contents)
       )
  )
   )
(defthm  parse-char-optional-cons

   (consp ( parse-char-optional char contents))

  )


(defthm  parse-char-optional-ast
   (ast-obj-p  (car ( parse-char-optional char contents)) )

       :hints (("Goal" :in-theory (and (enable  parse-char-optional) )))
  )
(defthm  parse-char-optional-charlist
    (implies
      (character-listp contents)
      (character-listp  (cdr ( parse-char-optional char contents)) )
             )
           :hints (("Goal" :in-theory (and (enable  parse-char-optional) )))
    )


(defun parse-object-entry (contents)
     (declare (xargs :guard
                           (character-listp contents)
                      :guard-hints (("Goal" :hands-off (parse-string combine2-ast-objs parse-until-string parse-char-optional  parse-number parse-char )  ))
                            )
            )
       (let* ((res1 (parse-number contents))
         (res2 (parse-char #\Space (cdr res1)))
         (res3 (parse-number (cdr res2)))
         (res4 (parse-char #\Space (cdr res3)))
         (res5 (parse-string "obj" (cdr res4)))
         (res6 (parse-char-optional #\Space (cdr res5)))
         (res7 (parse-char-optional #\Newline (cdr res6)))
         (res8 (parse-until-string "endobj" (cdr res7)))
         (res9 (parse-char-optional #\Newline (cdr res8)))
         (ast1 (combine2-ast-objs (car res1) (car res2)))
         (ast2 (combine2-ast-objs ast1 (car res3)))
         (ast3 (combine2-ast-objs ast2 (car res4)))
         (ast4 (combine2-ast-objs ast3 (car res5)))
         (ast5 (combine2-ast-objs ast4 (car res6)))
         (ast6 (combine2-ast-objs ast5 (car res7)))
         (ast7 (combine2-ast-objs ast6 (car res8)))
         (ast8 (combine2-ast-objs ast7 (car res9)))
        )
                 (if (and (not (ast-obj-null (car res1))) (character-listp (cdr res1)) )

                (if (and  (not (ast-obj-null (car res2)))(character-listp (cdr res2)) )
                     (if (and  (not (ast-obj-null (car res3)))(character-listp (cdr res3)))
                       (if (and  (not (ast-obj-null (car res4)))(character-listp (cdr res4)))
                           (if (and  (not (ast-obj-null (car res5)))(character-listp (cdr res5)))
                               (if (and  (not (ast-obj-null (car res6)))(character-listp (cdr res6)))
                                 (if (and  (not (ast-obj-null (car res7)))(character-listp (cdr res7)))
                                   (if (and  (not (ast-obj-null (car res8)))(character-listp (cdr res8)))
                                     (if (and  (not (ast-obj-null (car res8)))(character-listp (cdr res8)))
                                       (cons ast8 (cdr res9))
                                       (cons (ast-obj "null" NIL) contents)
                                     )

                                     (cons (ast-obj "null" NIL) contents)
                                     )

                                   (cons (ast-obj "null" NIL) contents)
                                   )

                             (cons (ast-obj "null" NIL) contents)
                             )

                          (cons (ast-obj "null" NIL) contents)
                          )
                         (cons (ast-obj "null" NIL) contents)
                         )
                   (cons (ast-obj "null" NIL) contents)
                  )
                 (cons (ast-obj "null" NIL) contents)
                )
                (cons (ast-obj "null" NIL) contents)
                )
         )
  )



(defund parse-objects (prefix contents )
    (declare (xargs :guard
                         (and  (character-listp contents)
                           )
                            )
             )
  (let ((res1 (parse-object-entry contents) ))
    (if (ast-obj-p prefix)
      (if (character-listp contents)

        (if  (< 0  (len contents) )
          (if (and (not (ast-obj-null (car res1))) (< (len (cdr res1)) (len contents)))
            (parse-objects (combine2-ast-objs prefix (car res1) ) (cdr res1) )
            (cons prefix contents)
            )
          (cons prefix contents)
          )
              (cons (ast-obj "null" NIL) contents)
              )
            (cons (ast-obj "null" NIL) contents)
     )
    )
  )

(defthm parse-objects-cons
  (consp (parse-objects prefix contents))
  )

(defthm parse-objects-ast
  (ast-obj-p (car (parse-objects prefix contents)))
    :hints (("Goal"  :in-theory (and (enable parse-objects) )))
  )

(defthm parse-objects-characterlist
    (implies
     (character-listp contents)
  (character-listp (cdr (parse-objects prefix contents)))
  )
    :hints (("Goal"  :in-theory (and (enable parse-objects) )))
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;PDF TRAILER ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund parse-until-option (string1 string2 contents)
    (declare (xargs :guard (and
                           (character-listp contents)
                           (stringp string2)
                            (stringp string1)
                            )))
    (let* ((res1 (parse-until-string-non-incl string1 contents) )
           (res2 (parse-until-string-non-incl string2 contents) )
  )
  (if (not (ast-obj-null (car res1)))
    (if (not (ast-obj-null (car res2)))
      ;select which leaves a longer remainder
      (if (< (len (cdr res1)) (len (cdr res2)))
        res2
        res1
      )
    res1
    )
    res2
  )
    )
)

(defthm  parse-until-option-cons
   (consp ( parse-until-option string1 string2 contents))
  )


(defthm  parse-until-option-ast
   (ast-obj-p  (car (parse-until-option string1 string2 contents)) )

       :hints (("Goal" :in-theory (enable parse-until-option))))

(defthm  parse-until-option-charlist
    (implies
      (character-listp contents)
      (character-listp  (cdr ( parse-until-option string1 string2 contents)) )
             )
:hints (("Goal" :in-theory (enable parse-until-option))))

(defun parse-trailer-entry (contents)
  (declare (xargs :guard
                           (character-listp contents)
                   :guard-hints (("Goal" :hands-off (parse-char parse-word parse-until-option)))
                            ))
  (let* ((res1 (parse-char #\/ contents) )
         (res2 (parse-word (cdr res1)))
         (res3 (parse-until-option "/" ">>" (cdr res1) ))
         (ast1  (combine2-ast-objs (car res1) (car res2)))
         (ast2  (combine2-ast-objs ast1 (car res3)))
               )
    (if (and (not (ast-obj-null (car res1))) (character-listp (cdr res1)))
      (if (and (not (ast-obj-null (car res2)))  (character-listp (cdr res2)))
        (if (and (not (ast-obj-null (car res3)))  (character-listp (cdr res3)))
          (cons ast2 (cdr res3))
          (cons (ast-obj "null" NIL) contents)
          )
          (cons (ast-obj "null" NIL) contents)
          )
        (cons (ast-obj "null" NIL) contents)
      )

  )
  )
(defthm  parse-trailer-entry-cons
   (consp ( parse-trailer-entry contents))
  )


(defthm  parse-trailer-entry-ast
   (ast-obj-p  (car (parse-trailer-entry contents)) )

       :hints (("Goal" :in-theory (enable parse-trailer-entry))))

(defthm  parse-trailer-entry-charlist
    (implies
      (character-listp contents)
      (character-listp  (cdr ( parse-trailer-entry contents)) )
             )
:hints (("Goal" :in-theory (enable parse-trailer-entry))))


(defund parse-trailer-entry-repetition (prefix contents )
    (declare (xargs :guard
                         (and  (character-listp contents)
                           )
                            )
             )
  (let ((res1 (parse-trailer-entry contents) ))
    (if (ast-obj-p prefix)
      (if (character-listp contents)

        (if  (< 0  (len contents) )
          (if (and (not (ast-obj-null (car res1))) (< (len (cdr res1)) (len contents)))
            (parse-trailer-entry-repetition (combine2-ast-objs prefix (car res1) ) (cdr res1) )
            (cons prefix contents)
            )
          (cons prefix contents)
          )
              (cons (ast-obj "null" NIL) contents)
              )
            (cons (ast-obj "null" NIL) contents)
     )
    )
  )

(defthm parse-trailer-entry-repetition-cons
  (consp (parse-trailer-entry-repetition prefix contents))
  )

(defthm parse-trailer-entry-repetition-ast
  (ast-obj-p (car (parse-trailer-entry-repetition prefix contents)))
    :hints (("Goal"  :in-theory (and (enable parse-trailer-entry-repetition) )))
  )

(defthm parse-trailer-entry-repetition-characterlist
    (implies
     (character-listp contents)
  (character-listp (cdr (parse-trailer-entry-repetition prefix contents)))
  )
    :hints (("Goal"  :in-theory (and (enable parse-trailer-entry-repetition) )))
  )
(defund parse-trailer-dictionary (contents)
  (declare (xargs :guard
                           (character-listp contents)
                             :guard-hints (("Goal" :hands-off (parse-string parse-char combine2-ast-objs parse-trailer-entry-repetition)))
                            ))
     (let*
        ((res1 (parse-string "<<" contents ))
        (res2 (parse-trailer-entry-repetition (car res1) (cdr res1)))
        (res3 (parse-string ">>" (cdr res2) ))
        (res4 (parse-char #\Newline (cdr res3)))
        (ast1 (combine2-ast-objs (car res2) (car res3)))
        (ast2 (combine2-ast-objs ast1 (car res4)))
        )
           (if (and (not (ast-obj-null (car res1))) (character-listp (cdr res1)))
      (if (and (not (ast-obj-null (car res2)))  (character-listp (cdr res2)))
        (if (and (not (ast-obj-null (car res3)))  (character-listp (cdr res3)))
          (if (and (not (ast-obj-null (car res4)))  (character-listp (cdr res4)))
            (cons ast2 (cdr res4))
            (cons (ast-obj "null" NIL) contents)
          )
            (cons (ast-obj "null" NIL) contents)
          )
          (cons (ast-obj "null" NIL) contents)
          )
        (cons (ast-obj "null" NIL) contents)
      )
  )
  )
(defthm parse-trailer-dictionary-cons
  (consp (parse-trailer-dictionary contents))
  )

(defthm parse-trailer-dictionary-ast
  (ast-obj-p (car (parse-trailer-dictionary contents)))
    :hints (("Goal"  :in-theory (and (enable parse-trailer-dictionary) )))
  )

(defthm parse-trailer-dictionary-characterlist
    (implies
     (character-listp contents)
  (character-listp (cdr (parse-trailer-dictionary contents)))
  )
    :hints (("Goal"  :in-theory (and (enable parse-trailer-dictionary) )))
  )
(defund parse-trailer (contents)
  (declare (xargs :guard
                           (character-listp contents)
                             :guard-hints (("Goal" :hands-off (parse-string parse-char combine2-ast-objs parse-trailer-dictionary)))
                            ))
   (let* ((res1 (parse-string "trailer" contents) )
         (res2 (parse-char #\Space (cdr res1)))
         (res3 (parse-trailer-dictionary (cdr res2) ))
         (res4 (parse-string "startxref" (cdr res3)) )
         (res5 (parse-char #\Newline (cdr res4)) )
         (res6 (parse-number (cdr res5) ))
         (res7 (parse-char #\Newline  (cdr res6  ) ))
         (res8 (parse-string "%%EOF"  (cdr res7  ) ))
         (ast1 (combine2-ast-objs (car res1) (car res2)))
         (ast2 (combine2-ast-objs ast1 (car res3)))
         (ast3 (combine2-ast-objs ast2 (car res4)))
         (ast4 (combine2-ast-objs ast3 (car res5)))
         (ast5 (combine2-ast-objs ast4 (car res6)))
         (ast6 (combine2-ast-objs ast5 (car res7)))
         (ast7 (combine2-ast-objs ast6 (car res8)))
     )
     (if (and (not (ast-obj-null (car res1))) (character-listp (cdr res1)))
       (if (and  (not (ast-obj-null (car res2)))(character-listp (cdr res2)))
          (if (and  (not (ast-obj-null (car res3)))(character-listp (cdr res3)))
            (if (and  (not (ast-obj-null (car res4)))(character-listp (cdr res4)))
              (if (and  (not (ast-obj-null (car res5)))(character-listp (cdr res5)))
                (if (and  (not (ast-obj-null (car res6)))(character-listp (cdr res6)))
                  (if (and  (not (ast-obj-null (car res7)))(character-listp (cdr res7)))
                    (if (and  (not (ast-obj-null (car res8)))(character-listp (cdr res8)))
                      (cons ast7 (cdr res8))
                      (cons (ast-obj "null" NIL) contents)
            )
                    (cons (ast-obj "null" NIL) contents)
            )
                  (cons (ast-obj "null" NIL) contents)
            )
                (cons (ast-obj "null" NIL) contents)
            )
                  (cons (ast-obj "null" NIL) contents)
            )
       (cons (ast-obj "null" NIL) contents)
       )
        (cons (ast-obj "null" NIL) contents)
       )
       (cons (ast-obj "null" NIL) contents)
            )
  )
   )
(defthm parse-trailer-cons
  (consp (parse-trailer contents))
  )

(defthm parse-trailer-ast
  (ast-obj-p (car (parse-trailer contents)))
    :hints (("Goal"  :in-theory (and (enable parse-trailer) )))
  )

  (defthm parse-trailer-characterlist
    (implies
     (character-listp contents)
  (character-listp (cdr (parse-trailer contents)))
  )
    :hints (("Goal"  :in-theory (and (enable parse-trailer) )))
  )
 ;;;;;;;;;;;;;;;; PARSE PDF ;;;;;;;;;;;;;;;;;;;;;;;
 (defun parse-pdf (contents)
   (declare (xargs :guard
                           (character-listp contents)
                             :guard-hints (("Goal" :hands-off (parse-header parse-objects parse-xref-section parse-trailer)))
                            ))
   (let* ((res1 (parse-header contents) )
         (res2 (parse-objects (car res1) (cdr res1)))
         (res3 (parse-xref-section (cdr res2) ))
         (res4 (parse-trailer (cdr res3)) )
         (ast1 (combine2-ast-objs (car res2) (car res3)))
         (ast2 (combine2-ast-objs ast1 (car res4)))
         )
    (if (and (not (ast-obj-null (car res1))) (character-listp (cdr res1)))
       (if (and  (not (ast-obj-null (car res2)))(character-listp (cdr res2)))
          (if (and  (not (ast-obj-null (car res3)))(character-listp (cdr res3)))
            (if (and  (not (ast-obj-null (car res4)))(character-listp (cdr res4)))
              (cons ast2 (cdr res4))
              (cons (ast-obj "null" NIL) contents)
              )
              (cons (ast-obj "null" NIL) contents)
              )
              (cons (ast-obj "null" NIL) contents)
              )
                     (cons (ast-obj "null" NIL) contents)
              )
    )


   )
