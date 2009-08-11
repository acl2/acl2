; The SEQW Macro Language, Examples
; Copyright (C) 2008 Centaur Technology
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "ACL2")
(include-book "seqw")
(set-verify-guards-eagerness 2)

; Before reading these examples, see seq-examples.lsp.  

; We begin by altering our matching functions so that we cause warnings when
; matching even integers, and when matching strings that begin with "a", which
; we call "bad strings."

(defun match-int (lst warnings)
  (cond ((not (consp lst))
         (mv "Error: expecting int but found end of list." nil lst warnings))
        ((not (integerp (car lst)))
         (mv "Error: integer expected." nil lst warnings))
        (t
         (mv nil (car lst) (cdr lst) (if (evenp (car lst))
                                         (cons (list "Warning: even integer matched: ~x0.~%" (car lst))
                                               warnings)
                                       warnings)))))

(defun bad-stringp (x)
  (and (stringp x)
       (< 0 (length x))
       (equal (char x 0) #\a)))

(defun match-string (lst warnings)
  (cond ((not (consp lst))
         (mv "Error: expecting string but found end of list." nil lst warnings))
        ((not (stringp (car lst)))
         (mv "Error: string expected." nil lst warnings))
        (t
         (mv nil (car lst) (cdr lst) 
             (if (bad-stringp (car lst))
                 (cons (list "Warning: bad string matched: ~x0.~%" (car lst))
                       warnings)
               warnings)))))

(defun match-three-ints (lst warnings)
  (seqw lst warnings
        (a := (match-int lst warnings))
        (b := (match-int lst warnings))
        (c := (match-int lst warnings))
        (return (list (cons 'a a)
                      (cons 'b b)
                      (cons 'c c)))))

;; Success:  val is (a . 1) (b . 2) (c . 3), warning about 2.
(match-three-ints '(1 2 3) nil)

;; Failure: "2" is not an integer.
(match-three-ints '(1 "2" 3) nil)




; This requires that the list beings with an integer, and furthermore if a
; string follows the integer, then there must be three strings after the
; integer.  Notice how we can refer to the variables b, c, and d even if the
; "when" branch is not followed -- implicitly, all the variables in a SEQ
; program are bound to nil to begin with.

(defun match-int-then-maybe-three-strings (lst warnings)
  (seqw lst warnings
        (a := (match-int lst warnings))
        (when (and (consp lst)
                   (stringp (car lst)))
          (b := (match-string lst warnings))
          (c := (match-string lst warnings))
          (d := (match-string lst warnings)))
       (return (list (list :a a)
                     (list :b b)
                     (list :c c)
                     (list :d d)))))

; Fail, not even an int:
(match-int-then-maybe-three-strings nil nil)    

; Fail, not even an int.
(match-int-then-maybe-three-strings '("1") nil) 

; Works, one int is okay.  No warnings.
(match-int-then-maybe-three-strings '(1) nil)

; Works, one int is okay, leaves 2 in lst.  No warnings.
(match-int-then-maybe-three-strings '(1 2) nil)

; Fail, if a string is there, we need three strings.  No warnings.
(match-int-then-maybe-three-strings '(1 "foo") nil)

; Works, an int and 3 strings.  Warning about arf.
(match-int-then-maybe-three-strings '(1 "foo" "arf" "baz") nil)

; Works, an int and 3 strings; leaves 2 3 4 in the lst.
; Warning about arf.
(match-int-then-maybe-three-strings '(1 "foo" "aar" "baz" 2 3 4) nil)



(defun match-int-list (lst warnings)
  (seqw lst warnings
        (first := (match-int lst warnings))
        (when (consp lst)
          (rest := (match-int-list lst warnings)))
        (return (cons first rest))))
            
(match-int-list nil nil)                 ;; fail, need at least one int
(match-int-list '(1 2 3 4) nil)          ;; works, warnings about 2 and 4
(match-int-list '(1 2 3 4 "five") nil)   ;; fail, not all integers, warnings about 2 and 4



; Here's another way to match a non-empty list of integers, which also uses
; an "early return" in the unless block.

(defun match-int-list2 (lst warnings)
  (seqw lst warnings
       (first := (match-int lst warnings))
       (unless (consp lst)
         (return (list first)))
       (rest := (match-int-list2 lst warnings))
       (return (cons first rest))))

(match-int-list2 nil nil)               ;; fail, need at least one int
(match-int-list2 '(1 2 3 4) nil)        ;; works, warnings about 2 and 4
(match-int-list2 '(1 2 3 4 "five") nil) ;; fail, not all integers, warnings about 2 and 4



; And here's a variant that permits an empty list.  Early returns are nice
; for avoiding nested whens, etc.

(defun match-ints (lst warnings)
  (seqw lst warnings
        (when (atom lst)
          (return nil))
        (first := (match-int lst warnings))
        (rest := (match-ints lst warnings))
        (return (cons first rest))))

(match-ints nil nil)                ;; works
(match-ints '(1 2 3) nil)           ;; works, warning about 2
(match-ints '(1 2 3 "four") nil)    ;; fail, not all integers, warning about 2



; And here's a tail-recursive variant that accumulates the integers into acc
; in reverse, then reverses them at the end.

(defun tr-match-ints (lst warnings acc)
  (declare (xargs :guard (true-listp acc)))
  (seqw lst warnings
        (when (atom lst)
          (return (reverse acc)))
        (a := (match-int lst warnings))
        (return-raw (tr-match-ints lst warnings (cons a acc)))))

(tr-match-ints nil nil nil)                ;; works
(tr-match-ints '(1 2 3) nil nil)           ;; works, warning about 2
(tr-match-ints '(1 2 3 "four") nil nil)    ;; fail, not all integers, warning about 2

#||
; stack overflows on my Lisp
; segfaults on gcl, watch out.
(comp 'match-ints)
(mv-let (erp val lst warnings)
        (match-ints (make-list 10000000 :initial-element 0) nil)
        (declare (ignore val lst warnings))
        erp)
||#

; does not stack overflow on my Lisp
(comp 'tr-match-ints)
(mv-let (erp val lst warnings)
        (tr-match-ints (make-list 10000000 :initial-element 0) nil nil)
        (declare (ignore erp val lst))
        (len warnings))


; And here's a function that reads as many ints as it can.
(defun match-front-ints (lst warnings)
  (seqw lst warnings
        (unless (and (consp lst)
                     (integerp (car lst)))
          (return nil))
        (a := (match-int lst warnings))
        (b := (match-front-ints lst warnings))
        (return (cons a b))))

(match-front-ints nil nil)                ;; fine, no ints
(match-front-ints '("foo" 1 2 3) nil)     ;; fine, but no front ints
(match-front-ints '(1 2 3 "foo" 4 5) nil) ;; fine, but only matches 1 2 3, warning about 2



; Now let's try backtracking.  We'll write a function that either reads "int
; int string", or "string string int", or fails.

(defun match-iis-or-ssi (lst warnings)
  (seqw-backtrack lst warnings
                  ;; Option 1: Read int, int, string.
                  ((i1 := (match-int lst warnings))
                   (i2 := (match-int lst warnings))
                   (str := (match-string lst warnings))
                   (return (list :OPTION-1 i1 i2 str)))
                 ;; Option 2: Read string, string, int.
                  ((s1 := (match-string lst warnings))
                   (s2 := (match-string lst warnings))
                   (int := (match-int lst warnings))
                   (return (list :OPTION-2 s1 s2 int)))))

(match-iis-or-ssi '(1 2 "arf" 4 5 6) nil)  ;; works, option 1, warns about 2 and arf
(match-iis-or-ssi '("arf" "bar" 1 9) nil)  ;; works, option 2, warns about arf
(match-iis-or-ssi '(1 "foo" 2 2 4) nil)    ;; fails
