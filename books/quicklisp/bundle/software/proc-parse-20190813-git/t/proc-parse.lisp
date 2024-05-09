(in-package :cl-user)
(defpackage proc-parse-test
  (:use :cl
        :proc-parse
        :prove)
  (:shadowing-import-from :proc-parse
                          :skip))
(in-package :proc-parse-test)

(plan 17)

(defmacro with-vector-parsing-test ((target) &body body)
  `(progn
     (subtest "with-string-parsing"
       (with-string-parsing (,target)
         (flet ((is-current (char &optional desc)
                  (is (current) char desc :test #'char=)))
           ,@body)))
     (subtest "with-octets-parsing"
       (with-octets-parsing (,(babel:string-to-octets target))
         (flet ((is-current (char &optional desc)
                  (is (current) (char-code char) desc :test #'=)))
           ,@body)))))

(subtest "current"
  (subtest "with-vector-parsing"
    (with-vector-parsing ("a")
      (is (current) #\a)))
  (with-vector-parsing-test ("a")
    (is-current #\a
                "can return the current character.")))

(defmacro test-peek ((target) &body body)
  `(progn
     (subtest "with-vector-parsing"
       (with-vector-parsing (,target) ,@body))
     (subtest "with-string-parsing"
       (with-string-parsing (,target) ,@body))
     (subtest "with-octets-parsing"
       (with-octets-parsing (,(babel:string-to-octets target)) ,@body))))

(subtest "peek"
  (test-peek ("a") (is (peek) nil))
  (test-peek ("a") (is (peek :eof-value 'yes) 'yes))
  (subtest "with-vector-parsing"
    (with-vector-parsing ("abcd")
      (advance)
      (is (peek) #\c)))
  (subtest "with-vector-parsing"
    (with-vector-parsing ("abcdefg" :end 5)
      (match "abc")
      (is (peek :eof-value 'yes) #\e)))
  (subtest "with-vector-parsing"
    (with-vector-parsing ("abcdefg" :end 5)
      (match "abcd")
      (is (peek :eof-value 'yes) 'yes))))

(subtest "advance"
  (with-vector-parsing-test ("ab")
    (advance)
    (is-current #\b
                "can increment the current position.")
    (advance)
    (fail "won't be executed after EOF")))

(subtest "advance*"
  (with-vector-parsing-test ("ab")
    (advance*)
    (is-current #\b
                "can increment the current position.")
    (ok (not (advance*))
        "doesn't raise the eof error without rest characters.")))

(subtest "skip"
  (with-vector-parsing-test ("ab")
    (skip #\a)
    (is-current #\b
                "can skip the spcified character.")
    (is-error (skip #\c)
              'match-failed
              "can raise the match-failed error with unmatched character.")))

(subtest "skip*"
  (with-vector-parsing-test ("aaabbb")
    (skip* #\a)
    (is-current #\b
                "can skip some spcified character.")
    (ok (not (skip* #\c))
        "doesn't raise the match-failed error with unmatched character.")
    (is-current #\b
                "doesn't skip any characters when unmatched character spcified.")))

(subtest "skip+"
  (with-vector-parsing-test ("aaabbb")
    (skip+ #\a)
    (is-current #\b
                "can skip some spcified character.")
    (is-error (skip+ #\c)
              'match-failed
              "can raise the match-failed error with unmatched character.")))

(subtest "skip?"
  (with-vector-parsing-test ("ab")
    (skip? #\a)
    (is-current #\b
                "can skip the spcified character.")
    (ok (not (skip? #\c))
        "doesn't raise the match-failed error with unmatched character.")
    (is-current #\b
                "doesn't skip any characters when unmatched character spcified.")))

(subtest "skip-until"
  (subtest "with-vector-parsing"
    (with-vector-parsing ("aaab")
      (skip-until (lambda (c) (char/= c #\a)))
      (is (current)
          #\b
          "can skip until form returns T.")
      (skip-until (lambda (c) (char/= c #\c)))
      (is (current)
          #\b
          "can skip until eof.")))
  (subtest "with-string-parsing"
    (with-string-parsing ("aaab")
      (skip-until (lambda (c) (char/= c #\a)))
      (is (current)
          #\b
          "can skip until form returns T.")
      (skip-until (lambda (c) (char/= c #\c)))
      (is (current)
          #\b
          "can skip until eof.")))
  (subtest "with-octets-parsing"
    (with-octets-parsing ((babel:string-to-octets "aaab"))
      (skip-until (lambda (b) (/= b (char-code #\a))))
      (is (current) (char-code #\b)
          "can skip until form returns T.")
      (skip-until (lambda (b) (/= b (char-code #\c))))
      (is (current) (char-code #\b)
          "can skip until eof."))))

(subtest "skip-while"
  (subtest "with-vector-parsing"
    (with-vector-parsing ("aaab")
      (skip-while (lambda (c) (char= c #\a)))
      (is (current)
          #\b
          "can skip when form returns T.")
      (skip-while (lambda (c) (char= c #\b)))
      (is (current)
          #\b
          "can skip until eof.")))
  (subtest "with-string-parsing"
    (with-string-parsing ("aaab")
      (skip-while (lambda (c) (char= c #\a)))
      (is (current)
          #\b
          "can skip when form returns T.")
      (skip-while (lambda (c) (char= c #\b)))
      (is (current)
          #\b
          "can skip until eof.")))
  (subtest "with-octets-parsing"
    (with-octets-parsing ((babel:string-to-octets "aaab"))
      (skip-while (lambda (b) (= b (char-code #\a))))
      (is (current) (char-code #\b)
          "can skip when form returns T.")
      (skip-while (lambda (b) (= b (char-code #\b))))
      (is (current) (char-code #\b)
          "can skip until eof."))))

(defun alpha-char-byte-p (byte)
  (or (<= (char-code #\a) byte (char-code #\z))
      (<= (char-code #\A) byte (char-code #\Z))))

(subtest "bind"
  (subtest "with-vector-parsing"
    (with-vector-parsing ("aaab")
      (bind (str1 (skip-while (lambda (c) (char= c #\a))))
        (is str1
            "aaa"
            "can bind string with form."))
      (bind (str2 (skip-while (lambda (c) (char= c #\b))))
        (is str2
            "b"
            "can bind string until eof.")))
    (with-vector-parsing ("a123")
      (skip-while alpha-char-p)
      (bind (num (skip-until alpha-char-p))
        (is num "123" "can bind even when reached to EOF"))))
  (subtest "with-string-parsing"
    (with-string-parsing ("aaab")
      (bind (str1 (skip-while (lambda (c) (char= c #\a))))
        (is str1
            "aaa"
            "can bind string with form."))
      (bind (str2 (skip-while (lambda (c) (char= c #\b))))
        (is str2
            "b"
            "can bind string until eof.")))
    (with-string-parsing ("a123")
      (skip-while alpha-char-p)
      (bind (num (skip-until alpha-char-p))
        (is num "123" "can bind even when reached to EOF"))))
  (subtest "with-octets-parsing"
    (with-octets-parsing ((babel:string-to-octets "aaab"))
      (bind (bytes1 (skip-while (lambda (b) (= b (char-code #\a)))))
        (is bytes1
            (babel:string-to-octets "aaa")
            "can bind octets with form."
            :test #'equalp))
      (bind (bytes2 (skip-while (lambda (b) (= b (char-code #\b)))))
        (is bytes2
            (babel:string-to-octets "b")
            "can bind octets until eof."
            :test #'equalp)))
    (with-octets-parsing ((babel:string-to-octets "a123"))
      (skip-while alpha-char-byte-p)
      (bind (num (skip-until alpha-char-byte-p))
        (is num (babel:string-to-octets "123")
            "can bind even when reached to EOF"
            :test #'equalp)))))

(subtest "match"
  (with-vector-parsing-test ("abc")
    (match "cd" "ab")
    (is-current #\c
                "can skip the matched one of specified strings.")
    (is-error (match "e" "fg")
              'match-failed
              "can raise the match-failed error with unmatched strings.")))

(subtest "match-i"
  (with-vector-parsing-test ("ABC")
    (match-i "cd" "ab")
    (is-current #\C
                "can skip the case-insensitively matched one of specified strings.")
    (is-error (match-i "e")
              'match-failed
              "can raise the match-failed error with case-insensitively unmatched strings.")))

(subtest "match?"
  (with-vector-parsing-test ("abc")
    (match? "ab")
    (is-current #\c
                "can skip the matched one of specified strings.")
    (match? "de")
    (is-current #\c
                "doesn't raise the match-failed error with unmatched strings.")))

(subtest "match-case"
  (with-vector-parsing-test ("abc")
    (is (match-case
         ("a" 0)
         ("b" 1))
        0
        "can return the value the body form of the matched case returns.")
    (is (match-case
         ("c" 0)
         (otherwise 1))
        1
        "can return the value the otherwise form returns.")
    (is-error (match-case
               ("c"))
              'match-failed
              "can raise the match-failed error with unmatched cases.")
    (is (match-case
         ("bc" 0))
        0
        "can return the value the body form of the matched case returns even thogh eof.")))

(subtest "match-i-case"
  (with-vector-parsing-test ("ABC")
    (is (match-i-case
         ("a" 0)
         ("b" 1))
        0
        "can return the value the body form of the case-insensitively matched case returns.")
    (is (match-i-case
         ("c" 0)
         (otherwise 1))
        1
        "can return the value the otherwise form returns.")
    (is-error (match-i-case
               ("c"))
              'match-failed
              "can raise the match-failed error with case-insensitively unmatched cases.")
    (is (match-i-case
         ("bc" 0))
        0
        "can return the value the body form of the matched case returns even thogh eof.")))

(subtest "declaration of types"
  (let ((str "LISP"))
    (declare (type simple-string str))
    (with-vector-parsing (str)
      (is (current) #\L))))

(finalize)
