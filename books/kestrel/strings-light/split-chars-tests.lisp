; Tests of split-chars
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "split-chars")

;; simple test
(assert-event
 (mv-let (foundp before after)
   (split-chars '(#\A #\B #\C #\D #\E) #\D)
   (and foundp
        (equal before '(#\A #\B #\C))
        (equal after '(#\E)))))

;; test where the given character does not appear in the list
(assert-event
 (mv-let (foundp before after)
   (split-chars '(#\A #\B #\C #\D #\E) #\Z)
   (and (not foundp)
        (equal before '(#\A #\B #\C #\D #\E))
        (equal after nil))))

;; test where the given character appears multiple times
;; note that we use the *first* occurrence.
(assert-event
 (mv-let (foundp before after)
   (split-chars '(#\A #\B #\C #\D #\E #\D #\E #\F #\G #\H) #\D)
   (and foundp
        (equal before '(#\A #\B #\C))
        (equal after '(#\E #\D #\E #\F #\G #\H)))))

;; test where the given character appears at the beginning
(assert-event
 (mv-let (foundp before after)
   (split-chars '(#\D #\E #\F #\G #\H) #\D)
   (and foundp
        (equal before nil)
        (equal after '(#\E #\F #\G #\H)))))

;; test where the given character appears at the end
(assert-event
 (mv-let (foundp before after)
   (split-chars '(#\A #\B #\C #\D) #\D)
   (and foundp
        (equal before '(#\A #\B #\C))
        (equal after nil))))

;; test where the given character is the entire list
(assert-event
 (mv-let (foundp before after)
   (split-chars '(#\D) #\D)
   (and foundp
        (equal before nil)
        (equal after nil))))

;; test with the empty list
(assert-event
 (mv-let (foundp before after)
   (split-chars nil #\D)
   (and (not foundp)
        (equal before nil)
        (equal after nil))))
