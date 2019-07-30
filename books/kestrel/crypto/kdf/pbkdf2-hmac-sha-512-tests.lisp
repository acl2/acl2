; KDF Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Eric McCarthy (mccarthy@kestrel.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

(in-package "KDF")

(include-book "pbkdf2-hmac-sha-512")


;; for assert-equal
(include-book "../../utilities/testing")


;;; --------------------------------
;;; trezor pbkdf2 test vectors

#||
Bitcoin-oriented test vectors.

https://github.com/bitcoin/bips/blob/master/bip-0039.mediawiki
states:

    ...
    To create a binary seed from the mnemonic, we use the PBKDF2 function with a
    mnemonic sentence (in UTF-8 NFKD) used as the password and the
    string "mnemonic" + passphrase (again in UTF-8 NFKD) used as the salt. The
    iteration count is set to 2048 and HMAC-SHA512 is used as the pseudo-random
    function. The length of the derived key is 512 bits (= 64 bytes).
    ...
    Test vectors
    The test vectors include input entropy, mnemonic and seed. The passphrase
    "TREZOR" is used for all vectors.

    https://github.com/trezor/python-mnemonic/blob/master/vectors.json

    Also see
    https://github.com/bip32JP/bip32JP.github.io/blob/master/test_JP_BIP39.json

    (Japanese wordlist test with heavily normalized symbols as passphrase)
||#

;;; Note, the above json file of English-wordlist-based test vectors
;;; contains 24 tests, but this spec is slow to execute.
;;; Here we run two of the tests.

(acl2::assert-equal
  (pbkdf2-hmac-sha-512-from-strings "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about" "mnemonicTREZOR" 2048 64)
              (acl2::unpackbv 64 8 #xc55257c360c07c72029aebc1b53c05ed0362ada38ead3e3e9efa3708e53495531f09a6987599d18264c1e1c92f2cf141630c7a3c4ab7c81b2f001698e7463b04))

(acl2::assert-equal
  (pbkdf2-hmac-sha-512-from-strings "legal winner thank year wave sausage worth useful legal winner thank yellow"  "mnemonicTREZOR" 2048 64)
  (acl2::unpackbv 64 8 #x2e8905819b8723fe2c1d161860e5ee1830318dbf49a83bd451cfb8440c28bd6fa457fe1296106559a3c80937a1c1069be3a3a5bd381ee6260e8d9739fce1f607))


;;; --------------------------------
;;; Anti-weakpasswords pbkdf2 test vectors

#||
This person claims their test vectors have worked on
identical results across 7 implementations using 5 different languages.
  https://stackoverflow.com/questions/5130513/pbkdf2-hmac-sha2-test-vectors
  https://github.com/Anti-weakpasswords/PBKDF2-Test-Vectors/releases

They have test vectors for pbkdf2-hmac-sha-512-from-strings as well as
..-sha-384, ..-sha-256, ..-sha-224, ..-sha-1, ..-md5

Format:
Password Salt Iterations Outputbytes SHA-512-0xResultInHex

password salt 1 64 867F70CF1ADE02CFF3752599A3A53DC4AF34C7A669815AE5D513554E1C8CF252C02D470A285A0501BAD999BFE943C08F050235D7D68B1DA55E63F73B60A57FCE
password salt 2 64 E1D9C16AA681708A45F5C7C4E215CEB66E011A2E9F0040713F18AEFDB866D53CF76CAB2868A39B9F7840EDCE4FEF5A82BE67335C77A6068E04112754F27CCF4E
password salt 4096 64 D197B1B33DB0143E018B12F3D1D1479E6CDEBDCC97C5C0F87F6902E072F457B5143F30602641B3D55CD335988CB36B84376060ECD532E039B742A239434AF2D5
passwordPASSWORDpassword saltSALTsaltSALTsaltSALTsaltSALTsalt 4096 64 8C0511F4C6E597C6AC6315D8F0362E225F3C501495BA23B868C005174DC4EE71115B59F9E60CD9532FA33E0F75AEFE30225C583A186CD82BD4DAEA9724A3D3B8
||#

(acl2::assert-equal
 (pbkdf2-hmac-sha-512-from-strings "password" "salt" 1 64)
 (acl2::unpackbv 64 8 #x867F70CF1ADE02CFF3752599A3A53DC4AF34C7A669815AE5D513554E1C8CF252C02D470A285A0501BAD999BFE943C08F050235D7D68B1DA55E63F73B60A57FCE))

(acl2::assert-equal
 (pbkdf2-hmac-sha-512-from-strings "password" "salt" 2 64)
 (acl2::unpackbv 64 8 #xE1D9C16AA681708A45F5C7C4E215CEB66E011A2E9F0040713F18AEFDB866D53CF76CAB2868A39B9F7840EDCE4FEF5A82BE67335C77A6068E04112754F27CCF4E))

(acl2::assert-equal
 (pbkdf2-hmac-sha-512-from-strings "password" "salt" 4096 64)
 (acl2::unpackbv 64 8 #xD197B1B33DB0143E018B12F3D1D1479E6CDEBDCC97C5C0F87F6902E072F457B5143F30602641B3D55CD335988CB36B84376060ECD532E039B742A239434AF2D5))

(acl2::assert-equal
 (pbkdf2-hmac-sha-512-from-strings "passwordPASSWORDpassword" "saltSALTsaltSALTsaltSALTsaltSALTsalt" 4096 64)
 (acl2::unpackbv 64 8 #x8C0511F4C6E597C6AC6315D8F0362E225F3C501495BA23B868C005174DC4EE71115B59F9E60CD9532FA33E0F75AEFE30225C583A186CD82BD4DAEA9724A3D3B8))

