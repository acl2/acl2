; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../parser-states")

(include-book "kestrel/utilities/strings/strings-codes" :dir :system)
(include-book "std/testing/assert-bang-stobj" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test operations on positions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (equal (position-init)
        (position 1 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (equal (position-inc-column 1 (position 1 0))
        (position 1 1)))

(assert-event
 (equal (position-inc-column 1 (position 7 17))
        (position 7 18)))

(assert-event
 (equal (position-inc-column 8 (position 7 17))
        (position 7 25)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (equal (position-inc-line 1 (position 1 0))
        (position 2 0)))

(assert-event
 (equal (position-inc-line 1 (position 20 0))
        (position 21 0)))

(assert-event
 (equal (position-inc-line 1 (position 20 44))
        (position 21 0)))

(assert-event
 (equal (position-inc-line 10 (position 20 44))
        (position 30 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test operations on spans.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (equal (span-join (span (position 5 13) (position 5 17))
                   (span (position 5 20) (position 5 23)))
        (span (position 5 13) (position 5 23))))

(assert-event
 (equal (span-join (span (position 2 0) (position 2 10))
                   (span (position 4 10) (position 6 29)))
        (span (position 2 0) (position 6 29))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test simple operations on parser states.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test-init-parstate (list gcc)
  `(assert!-stobj
    (b* ((parstate (init-parstate ,list ,gcc parstate)))
      (mv (and (equal (parstate->bytes parstate) ,list)
               (equal (parstate->position parstate) (irr-position))
               (equal (parstate->chars-length parstate) (len ,list))
               (equal (parstate->chars-read parstate) 0)
               (equal (parstate->chars-unread parstate) 0)
               (equal (parstate->tokens-read parstate) 0)
               (equal (parstate->tokens-unread parstate) 0)
               (equal (parstate->gcc parstate) ,gcc)
               (equal (parstate->size parstate) (len ,list)))
          parstate))
    parstate))

(test-init-parstate nil nil)

(test-init-parstate nil t)

(test-init-parstate (list 1) nil)

(test-init-parstate (list 1) t)

(test-init-parstate (list 1 2 3) nil)

(test-init-parstate (list 1 2 3) t)

(test-init-parstate (acl2::string=>nats "abc") nil)

(test-init-parstate (acl2::string=>nats "abc") t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert!-stobj
 (b* ((parstate (init-parstate nil nil parstate)))
   (mv (equal (parsize parstate) 0)
       parstate))
 parstate)

(assert!-stobj
 (b* ((parstate (init-parstate nil t parstate)))
   (mv (equal (parsize parstate) 0)
       parstate))
 parstate)

(assert!-stobj
 (b* ((parstate (init-parstate (list 72 99 21) nil parstate)))
   (mv (equal (parsize parstate) 3)
       parstate))
 parstate)

(assert!-stobj
 (b* ((parstate (init-parstate (list 72 99 21) t parstate)))
   (mv (equal (parsize parstate) 3)
       parstate))
 parstate)
