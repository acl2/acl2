; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

;; ===================================================================
; We want a custom package because I'm stubborn and want the symbols read-line,
; parse-natural1, parse-natural, and parse-integer.
(defpkg "PROOF-PARSER-ITP13"
  (set-difference-eq (union-eq *acl2-exports*
                               *common-lisp-symbols-from-main-lisp-package*
                               '(b*))
                     '(read-line
                       parse-natural1
                       parse-natural
                       parse-integer)))

(in-package "PROOF-PARSER-ITP13")

(include-book "tools/bstar" :dir :system)

(program)

(defttag t)

(remove-untouchable acl2::create-state t)

(set-state-ok t)

;; ========================== Line Readers ===========================

; (channel state) -> (mv bool:eof [char]:char-list state)
(defun read-line (channel state)
  (mv-let (char state)
          (read-char$ channel state)
          (case char
            ('nil (mv t nil state)) ; EOF
            (#\Newline (mv nil (list #\Newline) state))
            (otherwise
             (mv-let (eof char-list state)
                     (read-line channel state)
                     (mv eof (cons char char-list) state))))))

; (channel state) -> (mv bool:eof state)
(defun skip-line (channel state)
  (mv-let (eof char-list state)
          (read-line channel state)
          (declare (ignore char-list))
          (mv eof state)))

;; ; (channel state) -> (mv bool:eof [char]:char-list state)
;; (defun read-line (channel state)
;;   (b*
;;    (((mv char state) (read-char$ channel state))
;;     ((if (equal char nil)) (mv t nil state)) ; EOF
;;     ((if (equal char #\Newline) (mv nil (list #\Newline) state)))
;;     ((mv eof char-list state) (read-line channel state)))
;;    (mv eof (cons char char-list) state)))

;; ; (channel state) -> (mv bool:eof state)
;; (defun skip-line (channel state)
;;   (b*
;;    (((mv eof & state) (read-line channel state)))
;;    (mv eof state)))


;; ======================== Whitespace Parser ========================

; ([char]:char-list) -> [char]:char-list
(defun trim-leading-whitespace (char-list)
  (if (atom char-list)
      nil
    (case (car char-list)
      ((#\Space #\Newline #\Tab) (trim-leading-whitespace (cdr char-list)))
      (otherwise
       (let ((ascii-code (char-code (car char-list))))
         (if (and (<= 33 ascii-code)
                  (<= ascii-code 126))
             char-list
           'unknown-char-code-in-trim-leading-whitespace))))))


;; ========================= Number Parsers ==========================

; (char:char) -> char(0-9/nil):digit
(defun char-to-number (char)
  (let ((char (- (char-code char) 48)))
    (if (and (<= 0 char)
             (<= char 9))
        char
      nil)))

; ([char]:char-list) -> (mv natural:num natural:exp [char]:char-list)
(defun parse-natural1 (char-list)
  (if (atom char-list)
      (mv 0 0 nil)
    (let ((digit (char-to-number (car char-list))))
      (if digit
          (mv-let (num exp char-list)
                  (parse-natural1 (cdr char-list))
                  (mv (+ (* digit (expt 10 exp)) num) (1+ exp) char-list))
        (mv 0 0 char-list)))))

; ([char]:char-list) -> (mv bool:fail natural:num [char]:char-list)
(defun parse-natural (char-list)
  (cond
   ((atom char-list) (mv t 0 char-list))
   ((not (char-to-number (car char-list))) (mv t 0 char-list))
   (t
    (mv-let (num exp char-list)
            (parse-natural1 char-list)
            (declare (ignore exp))
            (mv nil num char-list)))))

; ([char]:char-list) -> (mv bool:fail integer:num [char]:char-list)
(defun parse-integer (char-list)
  (if (atom char-list)
      (mv t 0 char-list)
    (let* ((signp (equal (car char-list) #\-))
           (sign-mult (if signp -1 1))
           (char-list (if signp (cdr char-list) char-list)))
      (mv-let (fail num new-char-list)
              (parse-natural char-list)
              (if fail
                  (mv t 0 new-char-list)
                (mv nil (* sign-mult num) new-char-list))))))


;; ========================= String Checker ==========================

; ([char]:char-list string:string) -> (mv bool:fail [char]:char-list)
(defun check-string (char-list string)
  (if (atom char-list)
      (mv t nil)
    (if (<= (length string) 0)
        (mv nil char-list)
      (if (equal (car char-list)
                 (char string 0))
          (check-string (cdr char-list)
                        (coerce (cdr (coerce string 'list)) 'string))
        (mv t nil)))))


;; ======================== Meta-Info Parser =========================

; ([char]:char-list) -> (mv bool:fail
;                           integer:num-vars
;                           integer:num-clauses)
(defun parse-meta-info (char-list)
  (b*
   ((char-list (trim-leading-whitespace char-list))
    ((mv fail char-list) (check-string char-list "rat"))
    ((if fail) (mv t 0 0))
    (char-list (trim-leading-whitespace char-list))
    ((mv fail num-vars char-list) (parse-integer char-list))
    ((if fail) (mv t 0 0))
    (char-list (trim-leading-whitespace char-list))
    ((mv fail num-clauses ?char-list) (parse-integer char-list))
    ((if fail) (mv t 0 0))
    )
   (mv nil num-vars num-clauses)))


;; ========================== Clause Parser ==========================

(defun parse-clause (char-list)
  (b* ((char-list (trim-leading-whitespace char-list))
       ((when (atom char-list)) (mv t nil))
       ((mv fail lit char-list) (parse-integer char-list))
       ((when fail) (mv t nil))
       ((when (equal lit 0)) (mv nil nil))
       ((mv fail clause) (parse-clause char-list)))
      (mv fail (cons lit clause))))

       

;; ========================== Proof Parser ==========================

; (channel state) -> (mv bool:fail [[integer]]:clause-list state)
(defun parse-clause-loop (channel state)
  (b*
   (((mv eof char-list state) (read-line channel state))
    ((mv fail clause) (parse-clause char-list))
    ;((if fail) (mv (not eof) nil state)) ; ????
    ((if fail)
     (b* ();(- (cw "Parse-clause failed.  EOF=~p0.~%" eof)))
         (mv (not eof) nil state)))
    ;((if eof) (mv nil (list clause) state))
    ((if eof)
     (b* ();(- (cw "EOF reached naturally.~%")))
         (mv nil (list clause) state)))
    ;(- (cw "~p0~%" clause))
    ;(- (cw "."))
    ((mv fail clause-list state) (parse-clause-loop channel state))
    )
   (mv fail (cons clause clause-list) state)))


; (channel state) -> (mv bool:eof state)
(defun parse-comment-loop (channel state)
  (let ((char (peek-char$ channel state)))
    (case char
      ('nil (mv t state)) ; EOF
      (#\c (mv-let (eof state)
                   (skip-line channel state)
                   (if eof
                       (mv t state)
                     (parse-comment-loop channel state))))
      (otherwise
       (mv nil state)))))


; (string:filename state) -> (mv bool:fail
;                                integer:num-vars
;                                integer:num-clauses
;                                [[integer]]:clause-list
;                                state)
(defun parse-unsat-proof-with-state (filename state)
  (b*
   (((mv channel state) (open-input-channel filename :character state))
    ((mv eof state) (parse-comment-loop channel state))
    ((if eof) (mv 'comment-loop-fail nil nil nil state))
    ((mv eof char-list state) (read-line channel state))
    ((if eof) (mv 'meta-info-read-line-fail nil nil nil state))
    ((mv fail num-vars num-clauses) (parse-meta-info char-list))
    ((if fail) (mv 'meta-info-fail nil nil nil state))
    ((mv fail clause-list state) (parse-clause-loop channel state))
    )
   (mv fail num-vars num-clauses clause-list state)))

;; ===================================================================

; The functions above will all be in the package "PROOF-PARSER".  The final
; function parse-unsat-proof will be in the "ACL2" package.
(in-package "ACL2")

; (string:filename) -> (mv bool:fail
;                          integer:num-vars
;                          integer:num-clauses
;                          [[integer]]:clause-list)
(defun parse-unsat-proof (filename)
  (with-local-state
   (mv-let (fail num-vars num-clauses clause-list state)
           (PROOF-PARSER::parse-unsat-proof-with-state filename state)
           (mv fail num-vars num-clauses clause-list))))


(logic)



#||

(acl2::parse-unsat-proof "rat-1")

(NIL 8 9
     ((1 2)
      (3 4)
      (5 6)
      (-1 -3)
      (-1 -5)
      (-3 -5)
      (-2 -4)
      (-2 -6)
      (-4 -6)
      (7 -1)
      (7 -5 -2)
      (-7 1 5)
      (-7 1 2)
      (8 -3)
      (8 -5 -4)
      (-8 3 5)
      (-8 3 4)
      (7)
      (8)
      (-7 -8 2)
      (-7 -8)
      NIL))

||#
