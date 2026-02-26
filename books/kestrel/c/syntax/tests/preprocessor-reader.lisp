; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../preprocessor-reader")

(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test mapping of bytes to characters and positions.

(defmacro test-bytes-to-chars+poss (&key
                                    input
                                    chars ; expected
                                    poss ; expected
                                    (std '17)
                                    (gcc 'nil)
                                    (clang 'nil)
                                    (fail 'nil))
  `(assert!
    (b* ((version (case ,std
                    (17 (cond (,gcc (c::version-c17+gcc))
                              (,clang (c::version-c17+clang))
                              (t (c::version-c17))))
                    (23 (cond (,gcc (c::version-c23+gcc))
                              (,clang (c::version-c23+clang))
                              (t (c::version-c23))))))
         (ienv (change-ienv (ienv-default) :version version))
         ((mv erp chars poss) (read-chars+positions ,input ienv)))
      (if ,fail
          (and erp (not (cw "~@0" erp)))
        (and (not erp)
             (equal chars ,chars)
             (equal poss ,poss))))))

(defmacro pos (line column)
  `(position ,line ,column))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-bytes-to-chars+poss
 :input nil ; empty file
 :chars nil
 :poss (list (position 1 0)))

(test-bytes-to-chars+poss
 :input '(0) ; disallowed character 0
 :fail t)

(test-bytes-to-chars+poss
 :input '(32 65) ; SP A
 :chars '(32 65)
 :poss (list (pos 1 0) (pos 1 1) (pos 1 2)))

(test-bytes-to-chars+poss
 :input '(10 65) ; LF A
 :chars '(10 65)
 :poss (list (pos 1 0) (pos 2 0) (pos 2 1)))

(test-bytes-to-chars+poss
 :input '(13 65) ; CR A
 :chars '(13 65)
 :poss (list (pos 1 0) (pos 2 0) (pos 2 1)))

(test-bytes-to-chars+poss
 :input '(13 10 65) ; CR LF A
 :chars '(13 10 65)
 :poss (list (pos 1 0) (pos 1 0) (pos 2 0) (pos 2 1)))

(test-bytes-to-chars+poss
 :input '(255) ; disallowed byte 255
 :fail t)

(test-bytes-to-chars+poss
 :input (acl2::string=>nats "??=A")
 :chars (acl2::string=>nats "#A")
 :poss (list (pos 1 0) (pos 1 3) (pos 1 4)))

(test-bytes-to-chars+poss
 :input (acl2::string=>nats "??(A")
 :chars (acl2::string=>nats "[A")
 :poss (list (pos 1 0) (pos 1 3) (pos 1 4)))

(test-bytes-to-chars+poss
 :input (acl2::string=>nats "??/A")
 :chars (list (char-code #\\) (char-code #\A))
 :poss (list (pos 1 0) (pos 1 3) (pos 1 4)))

(test-bytes-to-chars+poss
 :input (acl2::string=>nats "??)A")
 :chars (acl2::string=>nats "]A")
 :poss (list (pos 1 0) (pos 1 3) (pos 1 4)))

(test-bytes-to-chars+poss
 :input (acl2::string=>nats "??'A")
 :chars (acl2::string=>nats "^A")
 :poss (list (pos 1 0) (pos 1 3) (pos 1 4)))

(test-bytes-to-chars+poss
 :input (acl2::string=>nats "??<A")
 :chars (acl2::string=>nats "{A")
 :poss (list (pos 1 0) (pos 1 3) (pos 1 4)))

(test-bytes-to-chars+poss
 :input (acl2::string=>nats "??!A")
 :chars (acl2::string=>nats "|A")
 :poss (list (pos 1 0) (pos 1 3) (pos 1 4)))

(test-bytes-to-chars+poss
 :input (acl2::string=>nats "??>A")
 :chars (acl2::string=>nats "}A")
 :poss (list (pos 1 0) (pos 1 3) (pos 1 4)))

(test-bytes-to-chars+poss
 :input (acl2::string=>nats "??-A")
 :chars (acl2::string=>nats "~A")
 :poss (list (pos 1 0) (pos 1 3) (pos 1 4)))

(test-bytes-to-chars+poss
 :input (acl2::string=>nats "??a")
 :chars (acl2::string=>nats "??a")
 :poss (list (pos 1 0) (pos 1 1) (pos 1 2) (pos 1 3)))

(test-bytes-to-chars+poss
 :input (acl2::string=>nats "?a")
 :chars (acl2::string=>nats "?a")
 :poss (list (pos 1 0) (pos 1 1) (pos 1 2)))

(test-bytes-to-chars+poss
 :input (acl2::string=>nats "??")
 :chars (acl2::string=>nats "??")
 :poss (list (pos 1 0) (pos 1 1) (pos 1 2)))

(test-bytes-to-chars+poss
 :input (acl2::string=>nats "?")
 :chars (acl2::string=>nats "?")
 :poss (list (pos 1 0) (pos 1 1)))

(test-bytes-to-chars+poss
 :input (list (char-code #\\))
 :chars (list (char-code #\\))
 :poss (list (pos 1 0) (pos 1 1)))

(test-bytes-to-chars+poss
 :input (list (char-code #\a) (char-code #\\))
 :chars (list (char-code #\a) (char-code #\\))
 :poss (list (pos 1 0) (pos 1 1) (pos 1 2)))

(test-bytes-to-chars+poss
 :input (list (char-code #\\) 10) ; \ LF
 :chars nil
 :poss (list (pos 2 0)))

(test-bytes-to-chars+poss
 :input (list 65 (char-code #\\) 10) ; A \ LF
 :chars (list 65) ; A
 :poss (list (pos 1 0) (pos 2 0)))

(test-bytes-to-chars+poss
 :input (list (char-code #\\) 10 66) ; \ LF B
 :chars (list 66) ; B
 :poss (list (pos 2 0) (pos 2 1)))

(test-bytes-to-chars+poss
 :input (list 65 (char-code #\\) 10 66) ; A \ LF B
 :chars (list 65 66) ; A B
 :poss (list (pos 1 0) (pos 2 0) (pos 2 1)))

(test-bytes-to-chars+poss
 :input (list (char-code #\\) 13) ; \ CR
 :chars nil
 :poss (list (pos 2 0)))

(test-bytes-to-chars+poss
 :input (list 65 (char-code #\\) 13) ; A \ CR
 :chars (list 65) ; A
 :poss (list (pos 1 0) (pos 2 0)))

(test-bytes-to-chars+poss
 :input (list (char-code #\\) 13 66) ; \ CR B
 :chars (list 66) ; B
 :poss (list (pos 2 0) (pos 2 1)))

(test-bytes-to-chars+poss
 :input (list 65 (char-code #\\) 13 66) ; A \ CR B
 :chars (list 65 66) ; A B
 :poss (list (pos 1 0) (pos 2 0) (pos 2 1)))

(test-bytes-to-chars+poss
 :input (list (char-code #\\) 13 10) ; \ CR LF
 :chars nil
 :poss (list (pos 2 0)))

(test-bytes-to-chars+poss
 :input (list 65 (char-code #\\) 13 10) ; A \ CR LF
 :chars (list 65) ; A
 :poss (list (pos 1 0) (pos 2 0)))

(test-bytes-to-chars+poss
 :input (list (char-code #\\) 13 10 66) ; \ CR LF B
 :chars (list 66) ; B
 :poss (list (pos 2 0) (pos 2 1)))

(test-bytes-to-chars+poss
 :input (list 65 (char-code #\\) 13 10 66) ; A \ CR LF B
 :chars (list 65 66) ; A B
 :poss (list (pos 1 0) (pos 2 0) (pos 2 1)))

(test-bytes-to-chars+poss
 :input (list (char-code #\\) (char-code #\n)) ; \ n
 :chars (list (char-code #\\) (char-code #\n)) ; \ n
 :poss (list (pos 1 0) (pos 1 1) (pos 1 2)))

(test-bytes-to-chars+poss
 ;; 2-byte UTF-8 encoding of Greek capital letter sigma
 :input (acl2::string=>nats "Σ")
 :chars (list #x03a3)
 :poss (list (pos 1 0) (pos 1 1)))

(test-bytes-to-chars+poss
 ;; invalid 2-byte UTF-8 encoding of 0
 :input (list #b11000000 #b10000000)
 :fail t)

(test-bytes-to-chars+poss
 ;; 3-byte UTF-8 encoding of anticlockwise top semicircle arrow
 :input (acl2::string=>nats "↺")
 :chars (list #x21ba)
 :poss (list (pos 1 0) (pos 1 1)))

(test-bytes-to-chars+poss
 ;; disallowed 3-byte UTF-8 encoding
 :input (list #b11100010 #b10000000 #b10101010) ; 202Ah
 :fail t)

(test-bytes-to-chars+poss
 ;; invalid 3-byte UTF-8 encoding of 0
 :input (list #b11100000 #b10000000 #b10000000)
 :fail t)

(test-bytes-to-chars+poss
 ;; 4-byte UTF-8 encoding of musical symbol eighth note
 :input (acl2::string=>nats "𝅘𝅥𝅮")
 :chars (list #x1d160)
 :poss (list (pos 1 0) (pos 1 1)))

(test-bytes-to-chars+poss
 ;; invalid 4-byte UTF-8 encoding of 0
 :input (list #b11110000 #b10000000 #b10000000 #b10000000)
 :fail t)

(test-bytes-to-chars+poss
 ;; invalid 4-byte UTF-8 encoding of 1FFFFFh
 :input (list #b11110111 #b10111111 #b10111111 #b10111111)
 :fail t)
