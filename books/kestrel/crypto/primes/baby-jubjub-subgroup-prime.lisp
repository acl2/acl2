; Primes Library: Subgroup prime for the twisted Edwards curve "Baby Jubjub".
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Eric McCarthy (mccarthy@kestrel.edu)
; Contributing Authors: Alessandro Coglio (coglio@kestrel.edu)
;                       Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Baby Jubjub is defined by Barry Whitehat:
;; https://github.com/barryWhiteHat/baby_jubjub

;; This files proves primality of the order of the largest subgroup
;; of the twisted Edwards curve "Baby Jubjub".

;; For primality of the base field in which "Baby Jubjub" is defined,
;; see bn-254-group-prime.lisp

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PRIMES")

(include-book "kestrel/number-theory/defprime" :dir :system)

(defprime baby-jubjub-subgroup-prime
  2736030358979909402780800718157159386076813972158567259200215660948447373041

  ;; Pratt certificate for the twisted Edwards curve "Baby Jubjub".
  (31 (2 3 5 11 17 967 32151195060611136810608359 178259130663561045147472537592047227885001)
    (4 1 1 2 1 1 1 1)
    (() () () () () ()
     ;; 32151195060611136810608359
     (3 (2 3 4139 431548080059745198929)
        (1 2 1 1)
        (() () ()
         ;; 431548080059745198929
         (3 (2 7 19 202795150404015601)
            (4 1 1 1)
            (() () ()
             ;; 202795150404015601
            (7 (2 3 5 19 349 25485742523)
               (4 1 2 1 1 1)
               (() () () () ()
                ;; 25485742523
                (2 (2 43189 295049)
                   (1 1 1)
                   (() () ()))))))))
     ;; 178259130663561045147472537592047227885001
     (14 (2 3 5 6323 336157 1863691091902891838383581623)
        (3 2 4 1 1 1)
        (() () () () ()
         ;; 1863691091902891838383581623
         (5 (2 33409 27892051421815855583579)
            (1 1 1)
            (() ()
             ;; 27892051421815855583579
             (2 (2 23 521 27743 513749 81654569)
                (1 1 1 1 1 1)
                (() () () () ()
                 ;; 81654569
                 (3 (2 10206821)
                    (3 1)
                    (()
                     ;; 10206821
                     (2 (2 5 13 37 1061)
                      (2 1 1 1 1)
                      (() () () () ())))))))))))))
