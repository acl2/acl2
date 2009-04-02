

;; Regular expression execution engine
;;
;; This file defines a function match-regex which executes a regex
;; in the parse-tree format defined in regex-defs.lisp and produced
;; by the parser in regex-parse.lisp.  Proper input to match-regex
;; is such a regex and an "input string" as defined in input-list.lisp:
;; that is, either a pure character list or the symbol 'beg (denoting the
;; beginning of the string) consed to a character list.
;; match-regex returns, as posix demands, the longest matching string
;; of the matches which begin at the earliest location in the input string.
;;
;; Finer control over regex execution can be obtained by calling the macro
;; run-regex with a parsed regex, an input string, and a list of backrefs
;; (which should be empty for the initial call unless you're trying to do
;; something very clever.)




(in-package "ACL2")

(include-book "regex-defs")

(include-book "input-list")


;;(include-book "arithmetic-3/bind-free/top" :dir :system)


;; Character set support (brackets)

;; Does char match the given charset element elt -
;; either equal or within the range.
(defun in-charset-elt (char elt)
  (declare (xargs :guard (and (characterp char)
                              (charset-memberp elt))))
  (cond ((characterp elt)
         (equal char elt))
        (t (and (equal (car elt) 'range)
                (char>= char (range-start elt))
                (char<= char (range-end elt))))))


;; Is char a member of charset.
;; We are unnecessarily flexible with nots
;; but so far it doesn't matter.
(defun in-charset (char charset)
  (declare (xargs :guard (and (characterp char)
                              (charsetp charset))))
  (if (atom charset)
      nil
    (if (equal (car charset) 'not)
        (not (in-charset char (cdr charset)))
      (or (in-charset-elt char (car charset))
          (in-charset char (cdr charset))))))


(in-theory (disable in-charset))

;; Backref support

;; The input is il, a set of strings with associated backref lists
;; representing the remainders after matching something, and orig,
;; the string before having matched that thing.  We extract the
;; matched portion of orig for each remainder string and cons it onto
;; that string's backref list.
(defun store-backrefs (il str orig-pos posn)
  (declare (xargs :guard (and (stringp str)
                              (input-listp il str)
                              (indexp orig-pos str)
                              (natp posn)
                              (>= (min-idx-il il str) orig-pos))
                  :verify-guards nil))
  (if (atom il)
      il
    (let* ((newidx (caar il))
           (oldbr (cdar il)))
      (set-insert-equal
       (cons newidx
             (update-nth posn (cons orig-pos newidx)
                         oldbr))
       (store-backrefs (cdr il) str orig-pos posn)))))


;; Add-backrefs produces an input list
(defthm store-backrefs-input-list
  (implies (and (input-listp il str)
                (indexp orig str)
                (natp posn)
                (>= (min-idx-il il str) orig))
           (input-listp (store-backrefs il str orig posn) str)))

(defthm store-backrefs-pseudo-il
  (implies (and (pseudo-input-listp il)
                (natp orig)
                (natp posn))
           (pseudo-input-listp (store-backrefs il str orig posn))))
                

;; (defthm store-backrefs-true-listp
;;   (implies (true-listp il)
;;            (true-listp (store-backrefs il str orig posn))))

(verify-guards store-backrefs)


(defthm store-backrefs-min-idx
  (equal (min-idx-il (store-backrefs il str orig posn) str)
         (min-idx-il il str))
  :hints (("Goal" :in-theory (enable set-insert-equal))))

;;(in-theory (disable store-backrefs))
;; (defthm store-backrefs-max-len-il
;;   (equal (max-len-il (store-backrefs il orig posn))
;;          (max-len-il il))
;;   :hints (("Goal" :in-theory (enable set-insert-equal))))


;; (defthm is-suffix-store-backrefs
;;   (iff (is-suffix-input-listp (store-backrefs il orig posn) str)
;;        (is-suffix-input-listp il str)))


;; ;; Replaces every entry's backref list with the given one
;; (defun replace-backrefs (il backrefs)
;;   (declare (xargs :guard (and (input-listp il)
;;                               (backref-listp backrefs))))
;;   (if (atom il)
;;       nil
;;     (cons (cons (caar il) backrefs)
;;           (replace-backrefs (cdr il) backrefs))))


;; (defthm replace-backrefs-input-list
;;   (implies (and (input-listp il)
;;                 (backref-listp backrefs))
;;            (input-listp (replace-backrefs il backrefs))))
                
;; (defthm replace-backrefs-max-len-il
;;   (equal (max-len-il (replace-backrefs il backrefs))
;;          (max-len-il il)))
  

;; If a prefix of the string starting at ind matches 
;; the part of the string delimited by br, return the index of
;; the remainder of the string.
;; Otherwise, return nil.
(defun check-backref (str ind br)
  (declare (xargs :guard (and (stringp str)
                              (indexp ind str)
                              (backrefp br str))))
  (let ((end (+ ind (cdr br) (- (car br)))))
    (if (and (<= end (length str))
             (equal (subseq str (car br) (cdr br))
                    (subseq str ind end)))
        end
      nil)))

                
;; check-backref returns in input string on a match
(defthm check-backref-indexp
  (implies (and (indexp ind str)
                (backrefp br str)
                (check-backref str ind br))
           (indexp (check-backref str ind br) str)))

;; it never returns a longer string than it's given
(defthm check-backref-greater
  (implies (and (backrefp br str)
                (indexp ind str)
                (check-backref str ind br))
           (<= ind (check-backref str ind br)))
  :rule-classes (:rewrite :linear))

;; (defthm is-suffix-check-backrefs
;;            (is-suffix (car (check-backref str br)) str))

;; (defthm is-suffix-check-backrefs-2
;;   (implies (is-suffix str1 str)
;;            (is-suffix (car (check-backref str1 br)) str)))

;; We are going to define a four-way "mutual recursion"
;; (a single defun with flags denoting the function to execute)
;; to execute regex parse trees on character lists (or input-strings.)
;; We define the measures and guards for each function:

;; measures
(defun run-regex-measure (regex str index)
  `((3 . ,(regex-measure regex))
    (2 . ,(+ 1 (nfix (- (length str) index)))) 
    . 0))

(defun run-regex-list-measure (regex str ilist)
  `((3 . ,(regex-measure regex))
    (2 . ,(+ 2 (nfix (- (length str) (min-idx-il ilist str)))))
    . ,(len ilist)))

(defun run-repeat-measure (regex str index min)
  `((3 . ,(regex-measure regex))
    (2 . ,(+ 2 (nfix (- (length str) index))))
    (1 . ,(+ 1 (* 2 (nfix min))))
    . 0))

(defun run-repeat-list-measure (regex str ilist min)
  `((3 . ,(regex-measure regex))
    (2 . ,(+ 2 (nfix (- (length str) (min-idx-il ilist str)))))
    (1 . ,(+ 2 (* 2 (nfix min))))
    . ,(len ilist)))







;; (defun run-n-times-measure (regex str n)
;;   `((3 . ,(1+ (acl2-count regex)))
;;     (2 . ,(+ 2 (len str)))
;;     (1 . ,(+ 1 (* 2 (nfix n))))
;;     . 0))

;; (defun run-n-list-measure (regex ilist n)
;;   `((3 . ,(1+ (acl2-count regex)))
;;     (2 . ,(+ 2 (max-len-il ilist)))
;;     (1 . ,(+ 2 (* 2 (nfix n))))
;;     . ,(len ilist)))

;; (defun run-star-measure (regex str n)
;;   (declare (ignore n))
;;   `((3 . ,(1+ (acl2-count regex))) 
;;     (2 . ,(+ 2 (len str))) 
;;     . 0))

;; (defun run-star-list-measure (regex ilist n)
;;   (declare (ignore n))
;;   `((3 . ,(1+ (acl2-count regex))) 
;;     (2 . ,(+ 2 (max-len-il ilist)))
;;     . ,(len ilist)))

;; Measure for the entire faux-mutual-recursion



;;     (run-n-times (run-n-times-measure regex str n))
;;     (run-n-list (run-n-list-measure regex ilist n))
;;     (run-star (run-star-measure regex str n))
;;     (run-star-list (run-star-list-measure regex ilist n))
;;     (otherwise 0)))

;; Guards (we group these differently since some functions
;; have some input parameters in common)
(defun reg-str-br-guard (regex str index backrefs)
  (declare (xargs :guard t))
  (and (regex-p regex)
       (stringp str)
       (indexp index str)
       (backref-listp backrefs str)))

(defun reg-ilist-guard (regex str ilist)
  (declare (xargs :guard t))
  (and (regex-p regex)
       (stringp str)
       (input-listp ilist str)))

(defun repeat-guard (min max)
  (declare (xargs :guard t))
  (and (integerp min)
       (integerp max)))

(defun run-regex-m-r-guard (regex str index backrefs ilist min max fun)
  (declare (xargs :guard t))  
  (and (symbolp fun)
       (case fun
         (run-regex (reg-str-br-guard regex str index backrefs))
         (run-regex-list (or (atom ilist)
                             (reg-ilist-guard regex str ilist)))
         (run-repeat (and (reg-str-br-guard regex str index backrefs)
                          (repeat-guard min max)))
         (run-repeat-list (or (atom ilist)
                              (and (reg-ilist-guard regex str ilist)
                                   (repeat-guard min max)))))))


(defun run-regex-m-r-measure (regex str index backrefs ilist min max fun)
  (if (run-regex-m-r-guard regex str index backrefs ilist min max fun)
      (case fun
        (run-regex (run-regex-measure regex str index))
        (run-regex-list (if (atom ilist)
                            0
                          (run-regex-list-measure regex str ilist)))
        (run-repeat (run-repeat-measure regex str index min))
        (run-repeat-list (if (atom ilist)
                             0
                           (run-repeat-list-measure regex str ilist min)))
        (otherwise 0))
    0))
;;          (run-n-times (and (reg-str-br-guard regex str backrefs)
;;                            (natp n)))
;;          (run-n-list (and (reg-ilist-guard regex ilist)
;;                           (natp n)))
;;          (run-star (and (reg-str-br-guard regex str backrefs)
;;                         (integerp n)))
;;          (run-star-list (and (reg-ilist-guard regex ilist)
;;                              (integerp n))))))

(local (defthm integerp-+
         (implies (and (integerp a)
                       (integerp b))
                  (integerp (+ a b)))))

(local (defthm integerp--
         (implies (integerp a)
                  (integerp (- a)))))

(defthm o-p-regex-measure
  (o-p (run-regex-m-r-measure regex str index backrefs ilist min max fun)))



;; Macros so we don't have to list irrelevant parameters in each call
(defmacro run-regex (regex str index backrefs)
  `(run-regex-m-r ,regex ,str ,index ,backrefs nil nil nil 'run-regex))

(defmacro run-regex-list (regex str ilist)
  `(run-regex-m-r ,regex ,str nil nil ,ilist nil nil 'run-regex-list))

(defmacro run-repeat (regex str index backrefs min max)
  `(run-regex-m-r ,regex ,str ,index ,backrefs ,nil ,min ,max 'run-repeat))

(defmacro run-repeat-list (regex str ilist min max)
  `(run-regex-m-r ,regex ,str nil nil ,ilist ,min ,max 'run-repeat-list))

;; This defines the "mutual recursion" of the four functions defined as macros
;; above.  Unfortunately most theorems must be proved about this function
;; directly since func must be a variable in the induction.
(defun run-regex-m-r (regex str index backrefs ilist min max func)
  (declare (xargs :measure 
                  (run-regex-m-r-measure regex str index backrefs 
                                         ilist min max func)
                  :guard 
                  (run-regex-m-r-guard regex str index backrefs 
                                       ilist min max func)
                  :verify-guards nil
                  ))

  (if (mbt (run-regex-m-r-guard regex str index backrefs ilist min max func))

      (case func


        (run-regex
         ;; run-regex
         ;; Given a regex structure and a string (as a list of characters)
         ;; checks whether the regex can be satisfied by the string
         ;; (starting strictly at the beginning),
         ;; and returns a list consisting of, for each place where the regex can
         ;; successfully terminate, the suffix of the string starting at that point.

         ;; In order to support backrefs we'll return a list of pairs of
         ;; first the unmatched remainder of the string
         ;; and an alist of backrefs.
         (pattern-match 
          regex

          ((r-concat left right)
           ;; Concatenation:
           ;; A regexp can successfully terminate in multiple places in the input string
           ;; so at each possible termination of the first regexp the second must be checked.
           (run-regex-list right str (run-regex left str index backrefs)))

          ((r-disjunct left right)
           ;; Simply return the possible suffixes for the first in the disjunction
           ;; concatenated with the possible suffixes for the second.
           (set-union-equal (run-regex left str index backrefs) 
                            (run-regex right str index backrefs)))

          ((r-exact c)
           ;; If the next character in the string matches, return the cdr
           ;; otherwise nil
           ;; Check for beginning
           (if (and (< index (length str))
                    (equal c (char str index)))
               (list (cons (1+ index) backrefs))
             nil))

          ((r-any)
           ;; fail if the string is empty, otherwise match the first
           ;; real character in the string.
           (if (< index (length str))
               (list (cons (1+ index) backrefs))
             nil))

          ((r-empty)
           ;; Match the empty string.  For example, ".?" parses to
           ;; (disjunct (empty) (any)).
           (list (cons index backrefs)))

          ((r-nomatch)
           ;; Does not match anything.
           nil)

          ((r-end)
           ;; Match the end of the string.
           (if (= index (length str))
               (list (cons index backrefs)) 
             nil))

          ((r-begin)
           ;; Match the beginning of the string
           ;; Grep allows multiple ^'s in a row all matching the beginning
           ;; of the string; one can do things like "^a*(^b|c)" which matches
           ;; b, c, or aaac, but not ab. 
           (if (= index 0)
               (list (cons index backrefs))
             nil))

          ((r-repeat reg min max)
           ;; * ? + or {}.  Match a regex repeatedly until the match fails
           ;; or the max number of repetitions is reached.  If the min number
           ;; of repetitions isn't reached then fail.
        
           ;; run-repeat does not return matches of length 0, but if min is 0 or
           ;; less the empty match should be included.
           (let* ((repeat (run-repeat reg str index backrefs min max)))
             (if (zp (nfix min))
                 (set-insert-equal
                  (cons index backrefs) repeat)
               repeat)))
                  
          ((r-charset s)
           ;; Match to a set of characters
           ;; In the future things like [:alpha:] [:alnum:] etc will go here
           (if (< index (length str))
               (if (in-charset (char str index) s)
                   (list (cons (1+ index) backrefs))
                 nil)
             nil))

          ((r-group reg gid)
           ;; Store the matches to the inner regex as backrefs
           (store-backrefs (run-regex reg str index backrefs)
                           str index gid))

          ((r-backref brid)
           ;; Match to the contents of a previously matched grouping
           (let ((br (nth brid backrefs)))
             (if br 
                 (let ((newind (check-backref str index br)))
                   (if newind
                       (list (cons newind backrefs))
                     nil))
               nil)))
          (& '(bad-input))))

    


        (run-regex-list
         ;; run-regex-list
         ;; Matches the regex against the list of strings, returning the list of
         ;; suffixes of matches against all of them.
         (if (atom ilist) nil
           ;;       (remove-duplicates-equal
           (set-union-equal (run-regex regex str (caar ilist) (cdar ilist)) 
                            (run-regex-list regex str (cdr ilist)))))
    
    
    
        (run-repeat
         ;; Match the regex between min and max times.  If max is ever negative,
         ;; don't limit the number of times matched (hence check only whether
         ;; max equals zero, not (zp).
     
         ;; If we're at the max number of times, quit
         (cond
          ((and (= max 0) ;;(or (= max 0) (atom str))
                (zp (nfix min))) `((,index . ,backrefs)))
          ;; ((or (= max 0) (atom str))         nil)
          (t (let* ((suffixes (run-regex regex str index backrefs)))
               ;; dealing with the minimum required number of repetitions is
               ;; a bit complicated.  min <= 1 means we accept suffixes as
               ;; valid matches themselves.  min <= 0 means we don't keep
               ;; matching on matches to the empty string.
               (if (zp (nfix min))
                   (let ((short-suff ;; (remove-duplicates-equal 
                          ;; If we're past the min number of repetitions,
                          ;; we don't need to keep matching on empty matches
                          (remove-all-longer-equal-il suffixes index)))
                     ;; We've matched the required number of times
                     ;; so return the suffixes along with the results of running more
                     ;;               (remove-duplicates-equal
                     (if (>= index (length str))
                         suffixes
                       (set-union-equal suffixes
                                        (run-repeat-list regex str short-suff 
                                                         min (1- max)))))
                 (if (mbt (>= (min-idx-il suffixes str) index))
                     (let ((val 
                            (run-repeat-list regex str suffixes (1- min) (1- max))))
                       (if (<= min 1)
                           ;; everything in suffixes has the required number
                           ;; of matches so they are valid return values
                           ;;(remove-duplicates-equal
                           (set-union-equal suffixes val)
                         ;; We haven't yet matched the required number of times
                         ;; so just match against the suffixes again,
                         ;; don't return them directly
                         val)) 
                   nil))))))
    
    
        (run-repeat-list
         (if (atom ilist)
             nil
           ;;(remove-duplicates-equal
           (set-union-equal (run-repeat regex str (caar ilist) (cdar ilist) min max)
                            (run-repeat-list regex str (cdr ilist) min max))))
    
        (otherwise '(bad-input)))
    '(bad-input)))




;; Theorems about the return values of the run-regex clique.
;; We ultimately want to verify the guards of run-regex-m-r
;; and to verify that it always returns an input-list.
;; To do that we first actually need to know that it never returns
;; a string longer than the ones it's given.

;; (defthm run-regex-max-len
;;   (and (implies (or (equal fun 'run-regex)
;;                     (equal fun 'run-repeat))
;;                 (<= (max-len-il 
;;                      (run-regex-m-r regex str backrefs strlist min max fun))
;;                     (len str)))
;;        (implies (or (equal fun 'run-regex-list)
;;                     (equal fun 'run-repeat-list))
;;                 (<= (max-len-il 
;;                      (run-regex-m-r regex str backrefs strlist min max fun))
;;                     (max-len-il strlist))))
;;   :hints (("Goal" :induct (run-regex-m-r regex str backrefs strlist min max fun)))
;;   :rule-classes 
;;   (:rewrite
;;    (:linear
;;     :trigger-terms 
;;     ((max-len-il (run-regex-m-r regex str backrefs strlist min max fun))))))



;; (defthm run-regex-bad-input
;;   (implies (run-regex-m-r-guard regex str index backrefs 
;;                                 ilist min max fun)
;;            (not (set-member-equal 
;;                  'bad-input 
;;                  (run-regex-m-r regex str index backrefs ilist min max fun)))))



;; (defthm run-regex-pseudo-input-list
;;   (and (implies (and (run-regex-m-r-guard regex str index backrefs 
;;                                           ilist min max fun)
;;                      (or (equal fun 'run-regex)
;;                          (equal fun 'run-repeat)))
;;                 (pseudo-input-listp 
;;                  (run-regex-m-r regex str index backrefs ilist min max fun)))
;;        (implies (and (run-regex-m-r-guard regex str index backrefs 
;;                                           ilist min max fun)
;;                      (or (equal fun 'run-regex-list)
;;                          (equal fun 'run-repeat-list)))
;;                 (pseudo-input-listp 
;;                  (run-regex-m-r regex str index backrefs ilist min max fun))))
;;   :hints (("Goal" :in-theory (enable input-list-eltp))))




(local
 (defthm run-regex-suffixes-induct
   (implies (and (natp lowidx)
                 (<= lowidx (length str))
                 (run-regex-m-r-guard regex str idx backrefs 
                                      ilist min max fun))
            (and (implies (and (or (equal fun 'run-regex)
                                   (equal fun 'run-repeat))
                               (natp idx)
                               (<= lowidx idx))
                          (and
                           (<= lowidx
                              (min-idx-il 
                               (run-regex-m-r regex str idx backrefs ilist
                                              min max fun) str))
                           (<= idx
                              (min-idx-il 
                               (run-regex-m-r regex str idx backrefs ilist
                                              min max fun) str))
                           (input-listp 
                            (run-regex-m-r regex str idx backrefs ilist
                                           min max fun)str)))
                 (implies (and (or (equal fun 'run-regex-list)
                                   (equal fun 'run-repeat-list))
                               (<= lowidx (min-idx-il ilist str)))
                          (and 
                           (<= lowidx
                               (min-idx-il
                                (run-regex-m-r regex str idx backrefs ilist 
                                               min max fun) str))
                           (<= (min-idx-il ilist str)
                               (min-idx-il
                                (run-regex-m-r regex str idx backrefs ilist 
                                               min max fun) str))
                           (input-listp
                            (run-regex-m-r regex str idx backrefs ilist 
                                               min max fun) str)))))
   :hints (("Goal" 
            :induct (run-regex-m-r regex str idx backrefs ilist min max fun)))))


(defthm run-regex-suffixes
  (and
   (implies 
    (reg-str-br-guard regex str idx backrefs)
    (<= idx (min-idx-il (run-regex regex str idx backrefs) str)))
   (implies 
    (and (reg-str-br-guard regex str idx backrefs)
         (repeat-guard min max))
    (<= idx (min-idx-il (run-repeat regex str idx  backrefs min max) str)))
   (implies
    (reg-ilist-guard regex str ilist)
    (<= (min-idx-il ilist str)
        (min-idx-il (run-regex-list regex str ilist) str)))
   (implies
    (and (reg-ilist-guard regex str ilist)
         (repeat-guard min max))
    (<= (min-idx-il ilist str)
        (min-idx-il (run-repeat-list regex str ilist min max) str))))
  :hints (("Goal" :do-not-induct t))
  :rule-classes (:rewrite :linear))




;; (defthm run-regex-max-len1
;;   (and
;;    (<= (max-len-il (run-regex regex str backrefs)) (len str))
;;    (<= (max-len-il (run-repeat regex str backrefs min max)) (len str)))
;;   :rule-classes (:rewrite :linear))

;; (defthm run-regex-max-len2
;;   (and
;;    (<= (max-len-il (run-regex-list regex strlist)) (max-len-il strlist))
;;    (<= (max-len-il (run-repeat-list regex strlist min max))
;;        (max-len-il strlist)))
;;   :rule-classes (:rewrite :linear))



(defthm run-regex-input-list
  (implies
   (run-regex-m-r-guard regex str index backrefs ilist min max fun)
   (input-listp 
    (run-regex-m-r regex str index backrefs ilist min max fun) str)))


(defthm run-regex-pseudo-input-list
  (implies
   (run-regex-m-r-guard regex str index backrefs ilist min max fun)
   (pseudo-input-listp 
    (run-regex-m-r regex str index backrefs ilist min max fun)))
  :hints (("Goal" :in-theory (enable input-list-eltp)
           :use (:instance input-listp-pseudo
                           (x (run-regex-m-r regex str index backrefs ilist min
                                             max fun))))))

;; (defthm run-regex-true-list
;;   (true-listp (run-regex-m-r regex str idx backrefs strlist min max fun))
;;   :rule-classes
;;   (:rewrite
;;    (:forward-chaining
;;     :trigger-terms ((run-regex-m-r regex str idx backrefs strlist min max fun)))))



                     
                

;; Finally
(verify-guards run-regex-m-r)


(defun resolve-backrefs (brlist str)
  (declare (xargs :guard (and (stringp str)
                              (backref-listp brlist str))))
  (if (atom brlist)
      nil
    (let ((rest (resolve-backrefs (cdr brlist) str)))
      (if (car brlist)
          (cons (get-backref-string (car brlist) str) rest)
        (cons nil rest)))))

;; Run-regex etc.  all return a list consisting of the suffix of the string
;; after having chopped off the matching portion.  We want to be able to
;; return a yes-no answer about whether we have a match (easy) or else
;; the actual matching portion of the input string.
;; Posix says the best match is the longest of the matches that begin earliest.

;; Driver for run-regex which follows the posix prescription of
;; looking for the longest match of those that begin at the earliest point
;; in the string.
;; Regex should be a parsed regex tree and str should be a character list
;; including the initial 'beg.

(defun string-untrans-guard (str untrans-str)
  (declare (xargs :guard t))
  (and (stringp str)
       (stringp untrans-str)
       (length-equiv str untrans-str)))

(defun match-regex-at-char (regex str untrans-str idx)
  (declare (xargs :guard (and (regex-p regex)
                              (string-untrans-guard str untrans-str)
                              (indexp idx str))))
  (let ((result (run-regex regex str idx nil)))
    (if (consp result)
        (let* ((longest (longest-il result))
               (matchstr (subseq untrans-str idx (car longest)))
               (backrefs (resolve-backrefs (cdr longest) untrans-str)))
          (mv t matchstr (if backrefs (cdr backrefs) nil)))
      (mv nil nil nil))))

(defun match-regex-fun (regex str untrans-str idx)
  (declare (xargs :guard (and (regex-p regex)
                              (string-untrans-guard str untrans-str)
                              (indexp idx str))
                  :measure (string-index-measure idx str)))
  (if (string-index-past-end idx str)
      (mv nil nil nil)
    (mv-let (havematch matchstr brs)
            (match-regex-at-char regex str untrans-str idx)
            (if havematch
                (mv havematch matchstr brs)
              (if (= idx (length str))
                  (mv nil nil nil)
                (match-regex-fun regex str untrans-str (1+ idx)))))))


(defun match-regex (regex str untrans-str)
  (declare (xargs :guard (and (regex-p regex)
                              (string-untrans-guard str untrans-str))))
  (match-regex-fun regex str untrans-str 0))


(defthm match-regex-at-char-string
  (implies (and
                (stringp untrans-str)
                (car (match-regex-at-char regex str untrans-str n)))
           (stringp (mv-nth 1 (match-regex-at-char regex str untrans-str n)))))

(defun string-or-null-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (equal x nil)
    (and (or (null (car x))
             (stringp (car x)))
         (string-or-null-listp (cdr x)))))

(defthm resolve-backrefs-strlist
  (implies (stringp str)
           (string-or-null-listp (resolve-backrefs brlist str))))

(defthm string-or-null-listp-cdr
  (implies (string-or-null-listp x)
           (string-or-null-listp (cdr x))))

(defthm match-regex-at-char-strlist
  (implies (and (stringp str)
                (stringp untrans-str))
           (string-or-null-listp 
            (mv-nth 2 (match-regex-at-char regex str untrans-str n)))))

(in-theory (disable match-regex-at-char))

(defthm match-regex-string
  (implies (and (stringp str)
                (stringp untrans-str)
                (car (match-regex-fun regex str untrans-str n)))
           (stringp (mv-nth 1 (match-regex-fun regex str untrans-str n)))))

(defthm match-regex-strlist
  (implies (and (stringp str)
                (stringp untrans-str))
           (string-or-null-listp 
            (mv-nth 2 (match-regex-fun regex str untrans-str n)))))

(in-theory (disable match-regex-fun))









