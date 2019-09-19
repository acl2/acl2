; Hierarchical Deterministic Wallet -- Tests
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "HDWALLET")

(include-book "wallet-executable")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Basic regression tests.

(defconst *entropy* "00112233445566778899aabbccddeeff")

(defconst *passphrase* "pass")

(defconst *mnemonic*
  "abandon math mimic master filter design carbon crystal rookie group knife young")

(defconst *init-stat*
  '(:state
    ((:priv
      (46591580287395788487867920456363669515598233796151645823528698776250359043219
       (242 120 150 90 62 241 52 221 108 5 151 224
            193 192 136 210 101 49 252 83 133 155
            63 166 198 113 184 159 1 254 144 121)))
     0 0 (0 0 0 0)
     (NIL (2147483692)
          (2147483692 2147483708)
          (2147483692 2147483708 2147483648)
          (2147483692 2147483708 2147483648 0)))
    0))

(assert-event
 (mv-let (error? mnemonic stat?)
   (init-from-entropy *entropy* *passphrase*)
   (and (equal error? nil)
        (equal mnemonic *mnemonic*)
        (equal stat? *init-stat*))))

(assert-event
 (mv-let (error? stat?)
   (init-from-mnemonic *mnemonic* *passphrase*)
   (and (equal error? nil)
        (equal stat? *init-stat*))))

(defconst *address-0*
  '(226 193 44 207 29 100 116 12 120 128 255 161 80 166 11 157 118 121 187 105))

;; The wallet command "next-key" prints out the address in this convenient form.
(defconst *address-0-bighexstring*
  "E2C12CCF1D64740C7880FFA150A60B9D7679BB69")

(assert-event
 (equal *address-0*
        (hexstring=>ubyte8s *address-0-bighexstring*)))

(defconst *stat-0*
  '(:state
    ((:priv
      (46591580287395788487867920456363669515598233796151645823528698776250359043219
       (242 120 150 90 62 241 52 221 108 5 151 224
            193 192 136 210 101 49 252 83 133 155
            63 166 198 113 184 159 1 254 144 121)))
     0 0 (0 0 0 0)
     (NIL (2147483692)
          (2147483692 2147483708)
          (2147483692 2147483708 2147483648)
          (2147483692 2147483708 2147483648 0)
          (2147483692 2147483708 2147483648 0 0)))
    1))

(assert-event
 (mv-let (error? index address stat)
   (next-key *init-stat*)
   (and (equal error? nil)
        (equal index 0)
        (equal address *address-0*)
        (equal stat *stat-0*))))

(defconst *nonce* "50")

(defconst *gas-price* "4")

(defconst *gas-limit* "1000")

(defconst *to* "0011223344556677889900112233445566778899")

(defconst *value* "1000000")

(defconst *data* "abababab")

(defconst *signed-transaction-0*
  '(248 102
        50 4 130 3 232 148 0 17 34 51 68 85 102
        119 136 153 0 17 34 51 68 85 102 119 136
        153 131 15 66 64 132 171 171 171 171 38
        160 155 243 216 179 255 20 237 19 17 161
        32 253 253 129 118 3 67 95 114 252 131
        255 38 249 173 189 181 206 38 233 200
        140 160 125 50 105 202 31 7 106 162 253
        156 153 1 185 16 178 192 105 123 3 253
        37 84 1 101 17 209 19 80 73 97 145 36))

(assert-event
 (mv-let (error? signed-transaction)
   (sign *nonce* *gas-price* *gas-limit* *to* *value* *data* "0" *stat-0*)
   (and (equal error? nil)
        (equal signed-transaction *signed-transaction-0*))))

(defconst *address-1*
  '(88 133 87 238 125 118 70 35 87 7 171 39 94 41 209 203 55 88 21 80))

(defconst *stat-1*
  '(:state
    ((:priv
      (46591580287395788487867920456363669515598233796151645823528698776250359043219
       (242 120 150 90 62 241 52 221 108 5 151 224
            193 192 136 210 101 49 252 83 133 155
            63 166 198 113 184 159 1 254 144 121)))
     0 0 (0 0 0 0)
     (NIL (2147483692)
          (2147483692 2147483708)
          (2147483692 2147483708 2147483648)
          (2147483692 2147483708 2147483648 0)
          (2147483692 2147483708 2147483648 0 0)
          (2147483692 2147483708 2147483648 0 1)))
    2))

(assert-event
 (mv-let (error? index address stat)
     (next-key *stat-0*)
   (and (equal error? nil)
        (equal index 1)
        (equal address *address-1*)
        (equal stat *stat-1*))))

#|

These can be run from the ACL2 shell:

(wallet *command-name-init-from-entropy* *entropy* *passphrase*)

(delete-file$ *stat-filepath* state)

(wallet *command-name-init-from-mnemonic* *mnemonic* *passphrase*)

(wallet *command-name-next-key*)

(wallet
 *command-name-sign* *nonce* *gas-price* *gas-limit* *to* *value* *data* "0")

(delete-file$ *stat-filepath* state)

|#
