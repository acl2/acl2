; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2026 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "dialects")

(include-book "kestrel/fty/character-set" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ basic-characters
  :parents (character-sets)
  :short "Basic source and execution characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see character-sets) first.")
   (xdoc::p
    "Although [C17] and [C23] do not prescribe ASCII, or any superset of it,
     the basic characters [C17:5.2.1] [C23:5.3.1]
     bear a natural correspondence with certain ASCII characters.
     Here we define the sets of those ASCII characters,
     one for source characters and one for execution characters.
     Each set depends on the C standard."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ascii-basic-source-chars ((std standardp))
  :returns (chars character-setp)
  :short "ASCII characters corresponding to the basic source characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "These differ slightly based on the C standard:
     C23 adds three characters to C17
     [C17:5.2.1/3] [C23:5.3.1]."))
  (b* ((upletters (str::explode "ABCDEFGHIJKLMNOPQRSTUVWXYZ"))
       (loletters (str::explode "abcdefghijklmnopqrstuvwxyz"))
       (digits (str::explode "0123456789"))
       (graphics-c17-and-c23 (str::explode "!\"#%&'()*+,-./:;<=>?[\\]^_{|}~"))
       (graphics-c23-only (str::explode "@$`"))
       (space-and-controls (list #\Space ; space
                                 #\Tab ; horizontal tab
                                 (code-char 11) ; vertical tab
                                 #\Page)) ; form feed
       (c17-all (append upletters
                        loletters
                        digits
                        graphics-c17-and-c23
                        space-and-controls))
       (c23-all (append c17-all
                        graphics-c23-only))
       (all (standard-case std :c17 c17-all :c23 c23-all)))
    (set::mergesort all))

  ///

  (defruled digits-in-ascii-basic-source-chars
    (set::subset '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
                 (ascii-basic-source-chars std))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ascii-basic-exec-chars ((std standardp))
  :returns (chars character-setp)
  :short "ASCII characters corresponding to the basic execution characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the source character ones plus a few more control characters:
     the null character [C17:5.2.1/2] [C23:5.3.1],
     and characters representing
     alert, backspace, carriage return, and new line
     [C17:5.2.1/3] [C23:5.3.1]."))
  (b* ((extra-chars (list (code-char 0) ; null character
                          (code-char 7) ; alert
                          (code-char 8) ; backspace
                          #\Return ; carriage return
                          #\Newline))) ; line feed
    (set::union (ascii-basic-source-chars std)
                (set::mergesort extra-chars)))

  ///

  (defrule ascii-basic-exec-chars-subset-ascii-basic-source-chars
    (set::subset (ascii-basic-source-chars std)
                 (ascii-basic-exec-chars std)))

  (defruled digits-in-ascii-basic-exec-chars
    (set::subset '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
                 (ascii-basic-exec-chars std))
    :enable (digits-in-ascii-basic-source-chars
             set::expensive-rules)))
