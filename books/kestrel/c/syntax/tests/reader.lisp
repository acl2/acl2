; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../reader")

(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "std/testing/assert-bang-stobj" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test reading and unreading of characters.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert!-stobj ; empty file
 (b* ((parstate (init-parstate nil nil parstate))
      (pstate0 (to-parstate$ parstate))
      ((mv erp char? pos parstate) (read-char parstate)))
   (mv (and (not erp)
            (not char?)
            (equal pos (position 1 0)) ; just past end of (empty) file
            (equal (to-parstate$ parstate)
                   pstate0))
       parstate))
 parstate)

(assert!-stobj ; disallowed character 0
 (b* ((parstate (init-parstate (list 0) nil parstate))
      ((mv erp & & parstate) (read-char parstate))
      (- (cw "~@0" erp)))
   (mv erp parstate))
 parstate)

(assert!-stobj ; character 32
 (b* ((parstate (init-parstate (list 32 1 2 3) nil parstate))
      (pstate0 (to-parstate$ parstate))
      ((mv erp char? pos parstate) (read-char parstate)))
   (mv (and (not erp)
            (equal char? 32)
            (equal pos (position 1 0))
            (equal (to-parstate$ parstate)
                   (change-parstate$
                    pstate0
                    :bytes (list 1 2 3)
                    :position (position 1 1)
                    :chars-read (list (char+position 32 (position 1 0))))))
       parstate))
 parstate)

(assert!-stobj ; line feed
 (b* ((parstate (init-parstate (list 10 1 2 3) nil parstate))
      (pstate0 (to-parstate$ parstate))
      ((mv erp char? pos parstate) (read-char parstate)))
   (mv (and (not erp)
            (equal char? 10)
            (equal pos (position 1 0))
            (equal (to-parstate$ parstate)
                   (change-parstate$
                    pstate0
                    :bytes (list 1 2 3)
                    :position (position 2 0)
                    :chars-read (list (char+position 10 (position 1 0))))))
       parstate))
 parstate)

(assert!-stobj ; carriage return
 (b* ((parstate (init-parstate (list 13 1 2 3) nil parstate))
      (pstate0 (to-parstate$ parstate))
      ((mv erp char? pos parstate) (read-char parstate)))
   (mv (and (not erp)
            (equal char? 10)
            (equal pos (position 1 0))
            (equal (to-parstate$ parstate)
                   (change-parstate$
                    pstate0
                    :bytes (list 1 2 3)
                    :position (position 2 0)
                    :chars-read (list (char+position 10 (position 1 0))))))
       parstate))
 parstate)

(assert!-stobj ; carriage return + line feed
 (b* ((parstate (init-parstate (list 13 10 1 2 3) nil parstate))
      (pstate0 (to-parstate$ parstate))
      ((mv erp char? pos parstate) (read-char parstate)))
   (mv (and (not erp)
            (equal char? 10)
            (equal pos (position 1 0))
            (equal (to-parstate$ parstate)
                   (change-parstate$
                    pstate0
                    :bytes (list 1 2 3)
                    :position (position 2 0)
                    :chars-read (list (char+position 10 (position 1 0))))))
       parstate))
 parstate)

(assert!-stobj ; disallowed byte 255
 (b* ((parstate (init-parstate (list 255) nil parstate))
      ((mv erp & & parstate) (read-char parstate))
      (- (cw "~@0" erp)))
   (mv erp parstate))
 parstate)

(assert!-stobj ; 2-byte UTF-8 encoding of Greek capital letter sigma
 (b* ((parstate (init-parstate (acl2::string=>nats "Σ") nil parstate))
      (pstate0 (to-parstate$ parstate))
      ((mv erp char? pos parstate) (read-char parstate)))
   (mv (and (not erp)
            (equal char? #x03a3)
            (equal pos (position 1 0))
            (equal (to-parstate$ parstate)
                   (change-parstate$
                    pstate0
                    :bytes nil
                    :position (position 1 1)
                    :chars-read (list (char+position #x03a3 (position 1 0))))))
       parstate))
 parstate)

(assert!-stobj ; invalid 2-byte UTF-8 encoding of 0
 (b* ((parstate (init-parstate (list #b11000000 #b10000000) nil parstate))
      ((mv erp & & parstate) (read-char parstate))
      (- (cw "~@0" erp)))
   (mv erp parstate))
 parstate)

(assert!-stobj ; 3-byte UTF-8 encoding of anticlockwise top semicircle arrow
 (b* ((parstate (init-parstate (acl2::string=>nats "↺") nil parstate))
      (pstate0 (to-parstate$ parstate))
      ((mv erp char? pos parstate) (read-char parstate)))
   (mv (and (not erp)
            (equal char? #x21ba)
            (equal pos (position 1 0))
            (equal (to-parstate$ parstate)
                   (change-parstate$
                    pstate0
                    :bytes nil
                    :position (position 1 1)
                    :chars-read (list (char+position #x21ba (position 1 0))))))
       parstate))
 parstate)

(assert!-stobj ; disallowed 3-byte UTF-8 encoding
 (b* ((parstate (init-parstate (list #b11100010 #b10000000 #b10101010) ; 202Ah
                               nil
                               parstate))
      ((mv erp & & parstate) (read-char parstate))
      (- (cw "~@0" erp)))
   (mv erp parstate))
 parstate)

(assert!-stobj ; invalid 3-byte UTF-8 encoding of 0
 (b* ((parstate (init-parstate (list #b11100000 #b10000000 #b10000000)
                               nil
                               parstate))
      ((mv erp & & parstate) (read-char parstate))
      (- (cw "~@0" erp)))
   (mv erp parstate))
 parstate)

(assert!-stobj ; 4-byte UTF-8 encoding of musical symbol eighth note
 (b* ((parstate (init-parstate (acl2::string=>nats "𝅘𝅥𝅮") nil parstate))
      (pstate0 (to-parstate$ parstate))
      ((mv erp char? pos parstate) (read-char parstate)))
   (mv (and (not erp)
            (equal char? #x1d160)
            (equal pos (position 1 0))
            (equal (to-parstate$ parstate)
                   (change-parstate$
                    pstate0
                    :bytes nil
                    :position (position 1 1)
                    :chars-read (list (char+position #x1d160 (position 1 0))))))
       parstate))
 parstate)

(assert!-stobj ; invalid 4-byte UTF-8 encoding of 0
 (b* ((parstate (init-parstate (list #b11110000 #b10000000 #b10000000 #b10000000)
                               nil
                               parstate))
      ((mv erp & & parstate) (read-char parstate))
      (- (cw "~@0" erp)))
   (mv erp parstate))
 parstate)

(assert!-stobj ; invalid 4-byte UTF-8 encoding of 1FFFFFh
 (b* ((parstate (init-parstate
                 (list #b11110111 #b10111111 #b10111111 #b10111111)
                 nil
                 parstate))
      ((mv erp & & parstate) (read-char parstate))
      (- (cw "~@0" erp)))
   (mv erp parstate))
 parstate)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert!-stobj
 (b* ((parstate (init-parstate (list 65 66 67) nil parstate)) ; A B C
      (pstate0 (to-parstate$ parstate))
      ((mv erp1 char-a pos-a parstate) (read-char parstate))
      (pstate1 (to-parstate$ parstate))
      ((mv erp2 char-b pos-b parstate) (read-char parstate))
      (pstate2 (to-parstate$ parstate))
      (parstate (unread-char parstate))
      (pstate3 (to-parstate$ parstate))
      ((mv erp4 char-b2 pos-b2 parstate) (read-char parstate))
      (pstate4 (to-parstate$ parstate))
      ((mv erp5 char-c pos-c parstate) (read-char parstate))
      (pstate5 (to-parstate$ parstate))
      ((mv erp6 char-eof pos-eof parstate) (read-char parstate))
      (pstate6 (to-parstate$ parstate)))
   (mv (and (not erp1)
            (not erp2)
            (not erp4)
            (not erp5)
            (not erp6)
            (equal char-a 65)
            (equal char-b 66)
            (equal char-b2 66)
            (equal char-c 67)
            (equal char-eof nil)
            (equal pos-a (position 1 0))
            (equal pos-b (position 1 1))
            (equal pos-b2 (position 1 1))
            (equal pos-c (position 1 2))
            (equal pos-eof (position 1 3))
            (equal pstate1
                   (change-parstate$
                    pstate0
                    :bytes (list 66 67)
                    :position (position 1 1)
                    :chars-read (list (char+position 65 (position 1 0)))))
            (equal pstate2
                   (change-parstate$
                    pstate1
                    :bytes (list 67)
                    :position (position 1 2)
                    :chars-read (list (char+position 66 (position 1 1))
                                      (char+position 65 (position 1 0)))))
            (equal pstate3
                   (change-parstate$
                    pstate2
                    :chars-read (list (char+position 65 (position 1 0)))
                    :chars-unread (list (char+position 66 (position 1 1)))))
            (equal pstate4
                   (change-parstate$
                    pstate3
                    :chars-read (list (char+position 66 (position 1 1))
                                      (char+position 65 (position 1 0)))
                    :chars-unread nil))
            (equal pstate5
                   (change-parstate$
                    pstate4
                    :bytes nil
                    :position (position 1 3)
                    :chars-read (list (char+position 67 (position 1 2))
                                      (char+position 66 (position 1 1))
                                      (char+position 65 (position 1 0)))))
            (equal pstate6
                   pstate5))
       parstate))
 parstate)

(assert!-stobj
 (b* ((parstate (init-parstate (list 65 10 66) nil parstate)) ; A LF B
      (pstate0 (to-parstate$ parstate))
      ((mv erp1 char-a pos-a parstate) (read-char parstate))
      (pstate1 (to-parstate$ parstate))
      ((mv erp2 char-nl pos-nl parstate) (read-char parstate))
      (pstate2 (to-parstate$ parstate))
      (parstate (unread-chars 2 parstate))
      (pstate3 (to-parstate$ parstate))
      ((mv erp4 char-a2 pos-a2 parstate) (read-char parstate))
      (pstate4 (to-parstate$ parstate))
      ((mv erp5 char-nl2 pos-nl2 parstate) (read-char parstate))
      (pstate5 (to-parstate$ parstate))
      (parstate (unread-char parstate))
      (pstate6 (to-parstate$ parstate))
      ((mv erp7 char-nl3 pos-nl3 parstate) (read-char parstate))
      (pstate7 (to-parstate$ parstate))
      ((mv erp8 char-b pos-b parstate) (read-char parstate))
      (pstate8 (to-parstate$ parstate))
      ((mv erp9 char-eof pos-eof parstate) (read-char parstate))
      (pstate9 (to-parstate$ parstate)))
   (mv (and (not erp1)
            (not erp2)
            (not erp4)
            (not erp5)
            (not erp7)
            (not erp8)
            (not erp9)
            (equal char-a 65)
            (equal char-nl 10)
            (equal char-a2 65)
            (equal char-nl2 10)
            (equal char-nl3 10)
            (equal char-b 66)
            (equal char-eof nil)
            (equal pos-a (position 1 0))
            (equal pos-a2 (position 1 0))
            (equal pos-nl (position 1 1))
            (equal pos-nl2 (position 1 1))
            (equal pos-nl3 (position 1 1))
            (equal pos-b (position 2 0))
            (equal pos-eof (position 2 1))
            (equal pstate1
                   (change-parstate$
                    pstate0
                    :bytes (list 10 66)
                    :position (position 1 1)
                    :chars-read (list (char+position 65 (position 1 0)))))
            (equal pstate2
                   (change-parstate$
                    pstate1
                    :bytes (list 66)
                    :position (position 2 0)
                    :chars-read (list (char+position 10 (position 1 1))
                                      (char+position 65 (position 1 0)))))
            (equal pstate3
                   (change-parstate$
                    pstate2
                    :chars-read nil
                    :chars-unread (list (char+position 65 (position 1 0))
                                        (char+position 10 (position 1 1)))))
            (equal pstate4
                   (change-parstate$
                    pstate3
                    :chars-read (list (char+position 65 (position 1 0)))
                    :chars-unread (list (char+position 10 (position 1 1)))))
            (equal pstate5
                   (change-parstate$
                    pstate4
                    :chars-read (list (char+position 10 (position 1 1))
                                      (char+position 65 (position 1 0)))
                    :chars-unread nil))
            (equal pstate6
                   (change-parstate$
                    pstate5
                    :chars-read (list (char+position 65 (position 1 0)))
                    :chars-unread (list (char+position 10 (position 1 1)))))
            (equal pstate7
                   (change-parstate$
                    pstate6
                    :chars-read (list (char+position 10 (position 1 1))
                                      (char+position 65 (position 1 0)))
                    :chars-unread nil))
            (equal pstate8
                   (change-parstate$
                    pstate7
                    :bytes nil
                    :position (position 2 1)
                    :chars-read (list (char+position 66 (position 2 0))
                                      (char+position 10 (position 1 1))
                                      (char+position 65 (position 1 0)))))
            (equal pstate9
                   pstate8))
       parstate))
 parstate)
