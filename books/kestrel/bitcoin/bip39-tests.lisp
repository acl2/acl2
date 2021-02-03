; Bitcoin Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Eric McCarthy (mccarthy@kestrel.edu)
;          Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BITCOIN")

(include-book "bip39")

;; Attach the executable pieces needed to run bip39 calculations.
(include-book "kestrel/crypto/attachments/sha-256" :dir :system)
(include-book "kestrel/crypto/attachments/pbkdf2-hmac-sha-512" :dir :system)

(include-book "kestrel/utilities/strings/hexstrings" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)

(defconst *bip39-tests*
	  '(
	    ;; Format:
            ;; (entropy: hexstring, mnemonic: string, passphrase: string, seed: hexstring)
  	    ;;
	    ;; Three tests from "Mastering Ethereum" by Antonopoulos & Wood:
            ;; Table 5-2
	    ;; https://github.com/ethereumbook/ethereumbook/blob/develop/05wallets.asciidoc#mnemonic_128_no_pass
	    ("0c1e24e5917779d297e14d45f14e1a1a"
             "army van defense carry jealous true garbage claim echo media make crunch"
             ""
             "5b56c417303faa3fcba7e57400e120a0ca83ec5a4fc9ffba757fbe63fbd77a89a1a3be4c67196f57c39a88b76373733891bfaba16ed27a813ceed498804c0570")
            ;;
            ;; Table 5-3
            ;; https://github.com/ethereumbook/ethereumbook/blob/develop/05wallets.asciidoc#mnemonic_128_w_pass
            ("0c1e24e5917779d297e14d45f14e1a1a"
             "army van defense carry jealous true garbage claim echo media make crunch"
             "SuperDuperSecret"
             "3b5df16df2157104cfdd22830162a5e170c0161653e3afe6c88defeefb0818c793dbb28ab3ab091897d0715861dc8a18358f80b79d49acf64142ae57037d1d54")
            ;;
            ;; Table 5-4
            ;; https://github.com/ethereumbook/ethereumbook/blob/develop/05wallets.asciidoc#mnemonic_256_no_pass
            ("2041546864449caff939d32d574753fe684d3c947c3346713dd8423e74abcf8c"
             "cake apple borrow silk endorse fitness top denial coil riot stay wolf luggage oxygen faint major edit measure invite love trap field dilemma oblige"
             ""
             "3269bce2674acbd188d4f120072b13b088a0ecf87c6e4cae41657a0bb78f5315b33b3a04356e53d062e55f1e0deaa082df8d487381379df848a6ad7e98798404")
            ;;
            ;; Additional tests using website https://iancoleman.io/bip39/
            ;; as an oracle.  Two random tests for each supported entropy length,
            ;; one without passphrase and one with passphrase "SuperSecret".
            ;;
            ;; Generate random entropy suitable for 12-word mnemonic from
            ;; https://iancoleman.io/bip39/
            ("9d13bb75e3f4dcf3727fbbd581faaaee"
             "other oven talent side evidence keen size wash stereo average primary syrup"
             ""
             "78cd8eedba10cccf13027f1b998f61558cc3578c11f0e5270b2d001ea2532495d69d35841b52eb8006a19241d5cf6d3132701931b930398ccb59bc4f2b7caf3f")
            ;;
            ;; Same as above but with passphrase "SuperSecret"
            ("9d13bb75e3f4dcf3727fbbd581faaaee"
             "other oven talent side evidence keen size wash stereo average primary syrup"
             "SuperSecret"
             "18abb3d67acf9f4546cf7a9fd074d0f296cdf61774b6e3132762fae8bc9eac75401b992138a6f82ff3ca4ad0cb5727d8eaeb44cc11be4a3fb8eb3dc1c99e2109")
            ;;
            ;; Generate random entropy suitable for 15-word mnemonic from
            ;; https://iancoleman.io/bip39/
            ("8e3d065a7f3eef97a0412adfa1800b514659fae1"
             "mixed trial notable wrist upon slim library census text army actress penalty grain word maple"
             ""
             "346f5332af1ff599e7bbeb2e8cd58adfc98f0662d0085cea23ca3b0e82b0418de3d42810e2384e7f79bbac0aaf4989a9c436579ba7ac4a4ca81423ba58c753ac")
            ;;
            ;; Same as above but with passphrase "SuperSecret"
            ("8e3d065a7f3eef97a0412adfa1800b514659fae1"
             "mixed trial notable wrist upon slim library census text army actress penalty grain word maple"
             "SuperSecret"
             "0a7f63dcd93f083eda39b18695c48cb33bf6adce4a7017360998427e9919ed55a5867eac5425f45ba668ffd9d18c4cea031254eff304329afb97407efb34970a")
            ;;
            ;; Generate random entropy suitable for 18-word mnemonic from
            ;; https://iancoleman.io/bip39/
            ("a682af781dd674cbb8cbd8084941f065a86fa769ffb68f13"
             "pledge betray task desert guard grape tobacco kitchen analyst energy lab slender manage squirrel pony walnut monitor organ"
             ""
             "8c4c7768795b5de4b29b0eb69c18be42b8191d66f74088329884ff4e54a93d73e8b2e0ec687a4ab5507910557c01e28589c9375294266a343e1c12a924333d50")
            ;;
            ;; Same as above but with passphrase "SuperSecret"
            ("a682af781dd674cbb8cbd8084941f065a86fa769ffb68f13"
             "pledge betray task desert guard grape tobacco kitchen analyst energy lab slender manage squirrel pony walnut monitor organ"
             "SuperSecret"
             "bc8c48f606c4256940519e537cab2c8dc56be249d66c9959f88c2db05626c2f2298897deadd7d73659fe656642eded6e4150996bcc9acd17fc12b8b77b7a4794")
            ;;
            ;; Generate random entropy suitable for 21-word mnemonic from
            ;; https://iancoleman.io/bip39/
            ("df21412322148208ccafdd6c80f4171eae1f6f87ad5e595cf46e1788"
             "tennis anxiety emotion during else afford crawl wing hold amateur alarm diary tiger result burger profit flock tray breeze congress load"
             ""
             "dcdd18262f44b94493ecec82559dc6aeaeaa89e4d8fb4b7342627312971b7cdc39b5347dbf3df1a18a5789da357d4c6ecdaa55bf691bead26b7c6d09fe867581")
            ;;
            ;; Same as above but with passphrase "SuperSecret"
            ("df21412322148208ccafdd6c80f4171eae1f6f87ad5e595cf46e1788"
             "tennis anxiety emotion during else afford crawl wing hold amateur alarm diary tiger result burger profit flock tray breeze congress load"
             "SuperSecret"
             "120e1fd0f4b02bb4322c2ddc0c40a5d8058ebf59fc4e6c3a6a7ba4d9954664e4917bdf354413c68ca7bb6eab5610c41bb20ef9cb8ed3bfa132ab22e5d117d121")
            ;;
            ;; Generate random entropy suitable for 24-word mnemonic from
            ;; https://iancoleman.io/bip39/
            ("7328967f1cebf2d29e3135f80f015780cb2db1dde1eacded7bb4be91cb9e5bc4"
             "industry dwarf panther degree sand harsh juice chase way job field account ready suggest jealous diary social hint unfold large bronze song humor negative"
             ""
             "294da272e7e699cf88f8d1b541db455550d5735670990c159cb25a3c7c80e5339353f9331a79db2b9d2fedadf1c0103e990ccf88f8ce89e1869804ed639a5ca9")
            ;;
            ;; Same as above but with passphrase "SuperSecret"
            ("7328967f1cebf2d29e3135f80f015780cb2db1dde1eacded7bb4be91cb9e5bc4"
             "industry dwarf panther degree sand harsh juice chase way job field account ready suggest jealous diary social hint unfold large bronze song humor negative"
             "SuperSecret"
             "942fd83503236e0f61cf74e85ad18ae6132e994b0a3c22184b3e4f760f301035765ca0ce8033794a819da5cdca7a7a59205093bc5bb4cd7d7acd1819f5e9e924")
            ))

(defun run-bip39-test (test-item)
  (and (string-listp test-item)
       (equal (len test-item) 4)
       (b* (
            ((list entropy-hexstring expected-mnemonic-words
                   passphrase expected-seed-hexstring)
             test-item)
            ;; entropy argument to bip39-entropy-to-mnemonic
            ;; is a list of bits
            (entropy (acl2::ungroup-bendian 2 8 (acl2::hexstring=>ubyte8s entropy-hexstring)))
            (mnemonic (bip39-entropy-to-mnemonic entropy))
            ((unless (equal mnemonic expected-mnemonic-words))
              nil) ; early failure
            (seed (bip39-mnemonic-to-seed mnemonic passphrase)) ; byte list
            (expected-seed-bytelist (acl2::hexstring=>ubyte8s expected-seed-hexstring))
            )
         (equal seed expected-seed-bytelist))))

(defun run-bip39-tests (test-items)
  (if (null test-items)
      t
    (let* ((item (car test-items))
           (result (run-bip39-test item)))
      (and
       (if (null result)
           (prog2$ (cw "This test failed: ~p0" item)
                   nil)
         t)
       (run-bip39-tests (cdr test-items))))))

;; Note, this took 226 seconds to run.
(assert! (run-bip39-tests *bip39-tests*))
