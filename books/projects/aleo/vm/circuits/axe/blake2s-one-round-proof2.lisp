; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

;; STATUS: Complete but needs cleanup

(include-book "blake2s-one-round-r1cs")
(include-book "support-blake2s")
(include-book "kestrel/axe/r1cs/lift-r1cs" :dir :system)
(include-book "kestrel/axe/r1cs/axe-rules-r1cs" :dir :system)
(include-book "kestrel/axe/r1cs/axe-prover-r1cs" :dir :system)
(include-book "kestrel/crypto/r1cs/gadgets/boolean-alt-rules" :dir :system)
(include-book "kestrel/crypto/r1cs/gadgets/xor-rules" :dir :system)
;(include-book "kestrel/axe/dag-info" :dir :system)
(include-book "kestrel/axe/conjoin-term-with-dag" :dir :system)
(include-book "kestrel/bv-lists/bits-to-bytes-little" :dir :system)
(include-book "kestrel/bv-lists/bits-to-bytes2" :dir :system)
(include-book "kestrel/bv-lists/bits-to-bytes-little2" :dir :system)
(include-book "kestrel/bv/rules7" :dir :system)
(include-book "kestrel/bv/rules9" :dir :system)
(include-book "projects/bls12-377-curves/primes/bls12-377-prime" :dir :system)
;(include-book "kestrel/prime-fields/bv-rules" :dir :system)
(include-book "kestrel/prime-fields/fe-listp-fast" :dir :system)
(include-book "kestrel/lists-light/cons" :dir :system)
(include-book "blake2s-one-round-spec-openers")

;; Lift the R1CS:
(local
 (r1cs::lift-r1cs *blake2s-one-round-r1cs-lifted*
                      *blake2s-one-round-vars*
                      *blake2s-one-round-constraints*
                      8444461749428370424248824938781546531375899335154063827935233455917409239041
                      :monitor '()
                      :remove-rules '(pfield::neg-of-mul-when-constant ;makes it harder to move terms to the other side?
                                      pfield::equal-of-add-of-add-of-neg-arg2-arg2 ;for now, to try to combine more stuff
                                      pfield::add-commutative-2-axe
                                      pfield::add-commutative-axe)
                      :extra-rules '(pfield::introduce-bitp-alt-2-alt
                                     pfield::introduce-bitp-alt-2
                                     primes::primep-of-bls12-377-scalar-field-prime-constant)
                      ;; :print t
                      ;; :count-hits t
                      ))

;; The spec for one round of blake2s, with an empty key supplied and a 32-byte hash produced:
(defun blake2s1round-no-key (|Aux0| |Aux1| |Aux2| |Aux3| |Aux4|
                             |Aux5| |Aux6| |Aux7| |Aux8| |Aux9|
                             |Aux10| |Aux11| |Aux12| |Aux13| |Aux14|
                             |Aux15| |Aux16| |Aux17| |Aux18| |Aux19|
                             |Aux20| |Aux21| |Aux22| |Aux23| |Aux24|
                             |Aux25| |Aux26| |Aux27| |Aux28| |Aux29|
                             |Aux30| |Aux31| |Aux32| |Aux33| |Aux34|
                             |Aux35| |Aux36| |Aux37| |Aux38| |Aux39|
                             |Aux40| |Aux41| |Aux42| |Aux43| |Aux44|
                             |Aux45| |Aux46| |Aux47| |Aux48| |Aux49|
                             |Aux50| |Aux51| |Aux52| |Aux53| |Aux54|
                             |Aux55| |Aux56| |Aux57| |Aux58| |Aux59|
                             |Aux60| |Aux61| |Aux62| |Aux63| |Aux64|
                             |Aux65| |Aux66| |Aux67| |Aux68| |Aux69|
                             |Aux70| |Aux71| |Aux72| |Aux73| |Aux74|
                             |Aux75| |Aux76| |Aux77| |Aux78| |Aux79|
                             |Aux80| |Aux81| |Aux82| |Aux83| |Aux84|
                             |Aux85| |Aux86| |Aux87| |Aux88| |Aux89|
                             |Aux90| |Aux91| |Aux92| |Aux93| |Aux94|
                             |Aux95| |Aux96| |Aux97| |Aux98| |Aux99|
                             |Aux100| |Aux101| |Aux102| |Aux103|
                             |Aux104| |Aux105| |Aux106| |Aux107|
                             |Aux108| |Aux109| |Aux110| |Aux111|
                             |Aux112| |Aux113| |Aux114| |Aux115|
                             |Aux116| |Aux117| |Aux118| |Aux119|
                             |Aux120| |Aux121| |Aux122| |Aux123|
                             |Aux124| |Aux125| |Aux126| |Aux127|
                             |Aux128| |Aux129| |Aux130| |Aux131|
                             |Aux132| |Aux133| |Aux134| |Aux135|
                             |Aux136| |Aux137| |Aux138| |Aux139|
                             |Aux140| |Aux141| |Aux142| |Aux143|
                             |Aux144| |Aux145| |Aux146| |Aux147|
                             |Aux148| |Aux149| |Aux150| |Aux151|
                             |Aux152| |Aux153| |Aux154| |Aux155|
                             |Aux156| |Aux157| |Aux158| |Aux159|
                             |Aux160| |Aux161| |Aux162| |Aux163|
                             |Aux164| |Aux165| |Aux166| |Aux167|
                             |Aux168| |Aux169| |Aux170| |Aux171|
                             |Aux172| |Aux173| |Aux174| |Aux175|
                             |Aux176| |Aux177| |Aux178| |Aux179|
                             |Aux180| |Aux181| |Aux182| |Aux183|
                             |Aux184| |Aux185| |Aux186| |Aux187|
                             |Aux188| |Aux189| |Aux190| |Aux191|
                             |Aux192| |Aux193| |Aux194| |Aux195|
                             |Aux196| |Aux197| |Aux198| |Aux199|
                             |Aux200| |Aux201| |Aux202| |Aux203|
                             |Aux204| |Aux205| |Aux206| |Aux207|
                             |Aux208| |Aux209| |Aux210| |Aux211|
                             |Aux212| |Aux213| |Aux214| |Aux215|
                             |Aux216| |Aux217| |Aux218| |Aux219|
                             |Aux220| |Aux221| |Aux222| |Aux223|
                             |Aux224| |Aux225| |Aux226| |Aux227|
                             |Aux228| |Aux229| |Aux230| |Aux231|
                             |Aux232| |Aux233| |Aux234| |Aux235|
                             |Aux236| |Aux237| |Aux238| |Aux239|
                             |Aux240| |Aux241| |Aux242| |Aux243|
                             |Aux244| |Aux245| |Aux246| |Aux247|
                             |Aux248| |Aux249| |Aux250| |Aux251|
                             |Aux252| |Aux253| |Aux254| |Aux255|
                             |Aux256| |Aux257| |Aux258| |Aux259|
                             |Aux260| |Aux261| |Aux262| |Aux263|
                             |Aux264| |Aux265| |Aux266| |Aux267|
                             |Aux268| |Aux269| |Aux270| |Aux271|
                             |Aux272| |Aux273| |Aux274| |Aux275|
                             |Aux276| |Aux277| |Aux278| |Aux279|
                             |Aux280| |Aux281| |Aux282| |Aux283|
                             |Aux284| |Aux285| |Aux286| |Aux287|
                             |Aux288| |Aux289| |Aux290| |Aux291|
                             |Aux292| |Aux293| |Aux294| |Aux295|
                             |Aux296| |Aux297| |Aux298| |Aux299|
                             |Aux300| |Aux301| |Aux302| |Aux303|
                             |Aux304| |Aux305| |Aux306| |Aux307|
                             |Aux308| |Aux309| |Aux310| |Aux311|
                             |Aux312| |Aux313| |Aux314| |Aux315|
                             |Aux316| |Aux317| |Aux318| |Aux319|
                             |Aux320| |Aux321| |Aux322| |Aux323|
                             |Aux324| |Aux325| |Aux326| |Aux327|
                             |Aux328| |Aux329| |Aux330| |Aux331|
                             |Aux332| |Aux333| |Aux334| |Aux335|
                             |Aux336| |Aux337| |Aux338| |Aux339|
                             |Aux340| |Aux341| |Aux342| |Aux343|
                             |Aux344| |Aux345| |Aux346| |Aux347|
                             |Aux348| |Aux349| |Aux350| |Aux351|
                             |Aux352| |Aux353| |Aux354| |Aux355|
                             |Aux356| |Aux357| |Aux358| |Aux359|
                             |Aux360| |Aux361| |Aux362| |Aux363|
                             |Aux364| |Aux365| |Aux366| |Aux367|
                             |Aux368| |Aux369| |Aux370| |Aux371|
                             |Aux372| |Aux373| |Aux374| |Aux375|
                             |Aux376| |Aux377| |Aux378| |Aux379|
                             |Aux380| |Aux381| |Aux382| |Aux383|
                             |Aux384| |Aux385| |Aux386| |Aux387|
                             |Aux388| |Aux389| |Aux390| |Aux391|
                             |Aux392| |Aux393| |Aux394| |Aux395|
                             |Aux396| |Aux397| |Aux398| |Aux399|
                             |Aux400| |Aux401| |Aux402| |Aux403|
                             |Aux404| |Aux405| |Aux406| |Aux407|
                             |Aux408| |Aux409| |Aux410| |Aux411|
                             |Aux412| |Aux413| |Aux414| |Aux415|
                             |Aux416| |Aux417| |Aux418| |Aux419|
                             |Aux420| |Aux421| |Aux422| |Aux423|
                             |Aux424| |Aux425| |Aux426| |Aux427|
                             |Aux428| |Aux429| |Aux430| |Aux431|
                             |Aux432| |Aux433| |Aux434| |Aux435|
                             |Aux436| |Aux437| |Aux438| |Aux439|
                             |Aux440| |Aux441| |Aux442| |Aux443|
                             |Aux444| |Aux445| |Aux446| |Aux447|
                             |Aux448| |Aux449| |Aux450| |Aux451|
                             |Aux452| |Aux453| |Aux454| |Aux455|
                             |Aux456| |Aux457| |Aux458| |Aux459|
                             |Aux460| |Aux461| |Aux462| |Aux463|
                             |Aux464| |Aux465| |Aux466| |Aux467|
                             |Aux468| |Aux469| |Aux470| |Aux471|
                             |Aux472| |Aux473| |Aux474| |Aux475|
                             |Aux476| |Aux477| |Aux478| |Aux479|
                             |Aux480| |Aux481| |Aux482| |Aux483|
                             |Aux484| |Aux485| |Aux486| |Aux487|
                             |Aux488| |Aux489| |Aux490| |Aux491|
                             |Aux492| |Aux493| |Aux494| |Aux495|
                             |Aux496| |Aux497| |Aux498| |Aux499|
                             |Aux500| |Aux501| |Aux502| |Aux503|
                             |Aux504| |Aux505| |Aux506| |Aux507|
                             |Aux508| |Aux509| |Aux510| |Aux511|)
  (blake::blake2s (acl2::bits-to-bytes-little (list |Aux0| |Aux1| |Aux2| |Aux3| |Aux4|
                                                    |Aux5| |Aux6| |Aux7| |Aux8| |Aux9|
                                                    |Aux10| |Aux11| |Aux12| |Aux13| |Aux14|
                                                    |Aux15| |Aux16| |Aux17| |Aux18| |Aux19|
                                                    |Aux20| |Aux21| |Aux22| |Aux23| |Aux24|
                                                    |Aux25| |Aux26| |Aux27| |Aux28| |Aux29|
                                                    |Aux30| |Aux31| |Aux32| |Aux33| |Aux34|
                                                    |Aux35| |Aux36| |Aux37| |Aux38| |Aux39|
                                                    |Aux40| |Aux41| |Aux42| |Aux43| |Aux44|
                                                    |Aux45| |Aux46| |Aux47| |Aux48| |Aux49|
                                                    |Aux50| |Aux51| |Aux52| |Aux53| |Aux54|
                                                    |Aux55| |Aux56| |Aux57| |Aux58| |Aux59|
                                                    |Aux60| |Aux61| |Aux62| |Aux63| |Aux64|
                                                    |Aux65| |Aux66| |Aux67| |Aux68| |Aux69|
                                                    |Aux70| |Aux71| |Aux72| |Aux73| |Aux74|
                                                    |Aux75| |Aux76| |Aux77| |Aux78| |Aux79|
                                                    |Aux80| |Aux81| |Aux82| |Aux83| |Aux84|
                                                    |Aux85| |Aux86| |Aux87| |Aux88| |Aux89|
                                                    |Aux90| |Aux91| |Aux92| |Aux93| |Aux94|
                                                    |Aux95| |Aux96| |Aux97| |Aux98| |Aux99|
                                                    |Aux100| |Aux101| |Aux102| |Aux103|
                                                    |Aux104| |Aux105| |Aux106| |Aux107|
                                                    |Aux108| |Aux109| |Aux110| |Aux111|
                                                    |Aux112| |Aux113| |Aux114| |Aux115|
                                                    |Aux116| |Aux117| |Aux118| |Aux119|
                                                    |Aux120| |Aux121| |Aux122| |Aux123|
                                                    |Aux124| |Aux125| |Aux126| |Aux127|
                                                    |Aux128| |Aux129| |Aux130| |Aux131|
                                                    |Aux132| |Aux133| |Aux134| |Aux135|
                                                    |Aux136| |Aux137| |Aux138| |Aux139|
                                                    |Aux140| |Aux141| |Aux142| |Aux143|
                                                    |Aux144| |Aux145| |Aux146| |Aux147|
                                                    |Aux148| |Aux149| |Aux150| |Aux151|
                                                    |Aux152| |Aux153| |Aux154| |Aux155|
                                                    |Aux156| |Aux157| |Aux158| |Aux159|
                                                    |Aux160| |Aux161| |Aux162| |Aux163|
                                                    |Aux164| |Aux165| |Aux166| |Aux167|
                                                    |Aux168| |Aux169| |Aux170| |Aux171|
                                                    |Aux172| |Aux173| |Aux174| |Aux175|
                                                    |Aux176| |Aux177| |Aux178| |Aux179|
                                                    |Aux180| |Aux181| |Aux182| |Aux183|
                                                    |Aux184| |Aux185| |Aux186| |Aux187|
                                                    |Aux188| |Aux189| |Aux190| |Aux191|
                                                    |Aux192| |Aux193| |Aux194| |Aux195|
                                                    |Aux196| |Aux197| |Aux198| |Aux199|
                                                    |Aux200| |Aux201| |Aux202| |Aux203|
                                                    |Aux204| |Aux205| |Aux206| |Aux207|
                                                    |Aux208| |Aux209| |Aux210| |Aux211|
                                                    |Aux212| |Aux213| |Aux214| |Aux215|
                                                    |Aux216| |Aux217| |Aux218| |Aux219|
                                                    |Aux220| |Aux221| |Aux222| |Aux223|
                                                    |Aux224| |Aux225| |Aux226| |Aux227|
                                                    |Aux228| |Aux229| |Aux230| |Aux231|
                                                    |Aux232| |Aux233| |Aux234| |Aux235|
                                                    |Aux236| |Aux237| |Aux238| |Aux239|
                                                    |Aux240| |Aux241| |Aux242| |Aux243|
                                                    |Aux244| |Aux245| |Aux246| |Aux247|
                                                    |Aux248| |Aux249| |Aux250| |Aux251|
                                                    |Aux252| |Aux253| |Aux254| |Aux255|
                                                    |Aux256| |Aux257| |Aux258| |Aux259|
                                                    |Aux260| |Aux261| |Aux262| |Aux263|
                                                    |Aux264| |Aux265| |Aux266| |Aux267|
                                                    |Aux268| |Aux269| |Aux270| |Aux271|
                                                    |Aux272| |Aux273| |Aux274| |Aux275|
                                                    |Aux276| |Aux277| |Aux278| |Aux279|
                                                    |Aux280| |Aux281| |Aux282| |Aux283|
                                                    |Aux284| |Aux285| |Aux286| |Aux287|
                                                    |Aux288| |Aux289| |Aux290| |Aux291|
                                                    |Aux292| |Aux293| |Aux294| |Aux295|
                                                    |Aux296| |Aux297| |Aux298| |Aux299|
                                                    |Aux300| |Aux301| |Aux302| |Aux303|
                                                    |Aux304| |Aux305| |Aux306| |Aux307|
                                                    |Aux308| |Aux309| |Aux310| |Aux311|
                                                    |Aux312| |Aux313| |Aux314| |Aux315|
                                                    |Aux316| |Aux317| |Aux318| |Aux319|
                                                    |Aux320| |Aux321| |Aux322| |Aux323|
                                                    |Aux324| |Aux325| |Aux326| |Aux327|
                                                    |Aux328| |Aux329| |Aux330| |Aux331|
                                                    |Aux332| |Aux333| |Aux334| |Aux335|
                                                    |Aux336| |Aux337| |Aux338| |Aux339|
                                                    |Aux340| |Aux341| |Aux342| |Aux343|
                                                    |Aux344| |Aux345| |Aux346| |Aux347|
                                                    |Aux348| |Aux349| |Aux350| |Aux351|
                                                    |Aux352| |Aux353| |Aux354| |Aux355|
                                                    |Aux356| |Aux357| |Aux358| |Aux359|
                                                    |Aux360| |Aux361| |Aux362| |Aux363|
                                                    |Aux364| |Aux365| |Aux366| |Aux367|
                                                    |Aux368| |Aux369| |Aux370| |Aux371|
                                                    |Aux372| |Aux373| |Aux374| |Aux375|
                                                    |Aux376| |Aux377| |Aux378| |Aux379|
                                                    |Aux380| |Aux381| |Aux382| |Aux383|
                                                    |Aux384| |Aux385| |Aux386| |Aux387|
                                                    |Aux388| |Aux389| |Aux390| |Aux391|
                                                    |Aux392| |Aux393| |Aux394| |Aux395|
                                                    |Aux396| |Aux397| |Aux398| |Aux399|
                                                    |Aux400| |Aux401| |Aux402| |Aux403|
                                                    |Aux404| |Aux405| |Aux406| |Aux407|
                                                    |Aux408| |Aux409| |Aux410| |Aux411|
                                                    |Aux412| |Aux413| |Aux414| |Aux415|
                                                    |Aux416| |Aux417| |Aux418| |Aux419|
                                                    |Aux420| |Aux421| |Aux422| |Aux423|
                                                    |Aux424| |Aux425| |Aux426| |Aux427|
                                                    |Aux428| |Aux429| |Aux430| |Aux431|
                                                    |Aux432| |Aux433| |Aux434| |Aux435|
                                                    |Aux436| |Aux437| |Aux438| |Aux439|
                                                    |Aux440| |Aux441| |Aux442| |Aux443|
                                                    |Aux444| |Aux445| |Aux446| |Aux447|
                                                    |Aux448| |Aux449| |Aux450| |Aux451|
                                                    |Aux452| |Aux453| |Aux454| |Aux455|
                                                    |Aux456| |Aux457| |Aux458| |Aux459|
                                                    |Aux460| |Aux461| |Aux462| |Aux463|
                                                    |Aux464| |Aux465| |Aux466| |Aux467|
                                                    |Aux468| |Aux469| |Aux470| |Aux471|
                                                    |Aux472| |Aux473| |Aux474| |Aux475|
                                                    |Aux476| |Aux477| |Aux478| |Aux479|
                                                    |Aux480| |Aux481| |Aux482| |Aux483|
                                                    |Aux484| |Aux485| |Aux486| |Aux487|
                                                    |Aux488| |Aux489| |Aux490| |Aux491|
                                                    |Aux492| |Aux493| |Aux494| |Aux495|
                                                    |Aux496| |Aux497| |Aux498| |Aux499|
                                                    |Aux500| |Aux501| |Aux502| |Aux503|
                                                    |Aux504| |Aux505| |Aux506| |Aux507|
                                                    |Aux508| |Aux509| |Aux510| |Aux511|))
                  nil ; no key
                  32))

(acl2::prove-implication-with-r1cs-prover
 ;; Assumes that the r1cs holds and every var is a field element:
 (acl2::conjoin-term-with-dag!
  (pfield::gen-fe-listp-assumption (acl2::dag-vars *blake2s-one-round-r1cs-lifted*)
                           ''8444461749428370424248824938781546531375899335154063827935233455917409239041)
  *blake2s-one-round-r1cs-lifted*)
 ;; Shows that the outputs are correctly computed from the inputs:
 '(equal (blake2s1round-no-key |Aux0| |Aux1| |Aux2| |Aux3| |Aux4| |Aux5| |Aux6| |Aux7| |Aux8| |Aux9|
                               |Aux10| |Aux11| |Aux12| |Aux13| |Aux14| |Aux15| |Aux16| |Aux17| |Aux18| |Aux19|
                               |Aux20| |Aux21| |Aux22| |Aux23| |Aux24| |Aux25| |Aux26| |Aux27| |Aux28| |Aux29|
                               |Aux30| |Aux31| |Aux32| |Aux33| |Aux34| |Aux35| |Aux36| |Aux37| |Aux38| |Aux39|
                               |Aux40| |Aux41| |Aux42| |Aux43| |Aux44| |Aux45| |Aux46| |Aux47| |Aux48| |Aux49|
                               |Aux50| |Aux51| |Aux52| |Aux53| |Aux54| |Aux55| |Aux56| |Aux57| |Aux58| |Aux59|
                               |Aux60| |Aux61| |Aux62| |Aux63| |Aux64| |Aux65| |Aux66| |Aux67| |Aux68| |Aux69|
                               |Aux70| |Aux71| |Aux72| |Aux73| |Aux74| |Aux75| |Aux76| |Aux77| |Aux78| |Aux79|
                               |Aux80| |Aux81| |Aux82| |Aux83| |Aux84| |Aux85| |Aux86| |Aux87| |Aux88| |Aux89|
                               |Aux90| |Aux91| |Aux92| |Aux93| |Aux94| |Aux95| |Aux96| |Aux97| |Aux98| |Aux99|
                               |Aux100| |Aux101| |Aux102| |Aux103| |Aux104| |Aux105| |Aux106| |Aux107|
                               |Aux108| |Aux109| |Aux110| |Aux111| |Aux112| |Aux113| |Aux114| |Aux115|
                               |Aux116| |Aux117| |Aux118| |Aux119| |Aux120| |Aux121| |Aux122| |Aux123|
                               |Aux124| |Aux125| |Aux126| |Aux127| |Aux128| |Aux129| |Aux130| |Aux131|
                               |Aux132| |Aux133| |Aux134| |Aux135| |Aux136| |Aux137| |Aux138| |Aux139|
                               |Aux140| |Aux141| |Aux142| |Aux143| |Aux144| |Aux145| |Aux146| |Aux147|
                               |Aux148| |Aux149| |Aux150| |Aux151| |Aux152| |Aux153| |Aux154| |Aux155|
                               |Aux156| |Aux157| |Aux158| |Aux159| |Aux160| |Aux161| |Aux162| |Aux163|
                               |Aux164| |Aux165| |Aux166| |Aux167| |Aux168| |Aux169| |Aux170| |Aux171|
                               |Aux172| |Aux173| |Aux174| |Aux175| |Aux176| |Aux177| |Aux178| |Aux179|
                               |Aux180| |Aux181| |Aux182| |Aux183| |Aux184| |Aux185| |Aux186| |Aux187|
                               |Aux188| |Aux189| |Aux190| |Aux191| |Aux192| |Aux193| |Aux194| |Aux195|
                               |Aux196| |Aux197| |Aux198| |Aux199| |Aux200| |Aux201| |Aux202| |Aux203|
                               |Aux204| |Aux205| |Aux206| |Aux207| |Aux208| |Aux209| |Aux210| |Aux211|
                               |Aux212| |Aux213| |Aux214| |Aux215| |Aux216| |Aux217| |Aux218| |Aux219|
                               |Aux220| |Aux221| |Aux222| |Aux223| |Aux224| |Aux225| |Aux226| |Aux227|
                               |Aux228| |Aux229| |Aux230| |Aux231| |Aux232| |Aux233| |Aux234| |Aux235|
                               |Aux236| |Aux237| |Aux238| |Aux239| |Aux240| |Aux241| |Aux242| |Aux243|
                               |Aux244| |Aux245| |Aux246| |Aux247| |Aux248| |Aux249| |Aux250| |Aux251|
                               |Aux252| |Aux253| |Aux254| |Aux255| |Aux256| |Aux257| |Aux258| |Aux259|
                               |Aux260| |Aux261| |Aux262| |Aux263| |Aux264| |Aux265| |Aux266| |Aux267|
                               |Aux268| |Aux269| |Aux270| |Aux271| |Aux272| |Aux273| |Aux274| |Aux275|
                               |Aux276| |Aux277| |Aux278| |Aux279| |Aux280| |Aux281| |Aux282| |Aux283|
                               |Aux284| |Aux285| |Aux286| |Aux287| |Aux288| |Aux289| |Aux290| |Aux291|
                               |Aux292| |Aux293| |Aux294| |Aux295| |Aux296| |Aux297| |Aux298| |Aux299|
                               |Aux300| |Aux301| |Aux302| |Aux303| |Aux304| |Aux305| |Aux306| |Aux307|
                               |Aux308| |Aux309| |Aux310| |Aux311| |Aux312| |Aux313| |Aux314| |Aux315|
                               |Aux316| |Aux317| |Aux318| |Aux319| |Aux320| |Aux321| |Aux322| |Aux323|
                               |Aux324| |Aux325| |Aux326| |Aux327| |Aux328| |Aux329| |Aux330| |Aux331|
                               |Aux332| |Aux333| |Aux334| |Aux335| |Aux336| |Aux337| |Aux338| |Aux339|
                               |Aux340| |Aux341| |Aux342| |Aux343| |Aux344| |Aux345| |Aux346| |Aux347|
                               |Aux348| |Aux349| |Aux350| |Aux351| |Aux352| |Aux353| |Aux354| |Aux355|
                               |Aux356| |Aux357| |Aux358| |Aux359| |Aux360| |Aux361| |Aux362| |Aux363|
                               |Aux364| |Aux365| |Aux366| |Aux367| |Aux368| |Aux369| |Aux370| |Aux371|
                               |Aux372| |Aux373| |Aux374| |Aux375| |Aux376| |Aux377| |Aux378| |Aux379|
                               |Aux380| |Aux381| |Aux382| |Aux383| |Aux384| |Aux385| |Aux386| |Aux387|
                               |Aux388| |Aux389| |Aux390| |Aux391| |Aux392| |Aux393| |Aux394| |Aux395|
                               |Aux396| |Aux397| |Aux398| |Aux399| |Aux400| |Aux401| |Aux402| |Aux403|
                               |Aux404| |Aux405| |Aux406| |Aux407| |Aux408| |Aux409| |Aux410| |Aux411|
                               |Aux412| |Aux413| |Aux414| |Aux415| |Aux416| |Aux417| |Aux418| |Aux419|
                               |Aux420| |Aux421| |Aux422| |Aux423| |Aux424| |Aux425| |Aux426| |Aux427|
                               |Aux428| |Aux429| |Aux430| |Aux431| |Aux432| |Aux433| |Aux434| |Aux435|
                               |Aux436| |Aux437| |Aux438| |Aux439| |Aux440| |Aux441| |Aux442| |Aux443|
                               |Aux444| |Aux445| |Aux446| |Aux447| |Aux448| |Aux449| |Aux450| |Aux451|
                               |Aux452| |Aux453| |Aux454| |Aux455| |Aux456| |Aux457| |Aux458| |Aux459|
                               |Aux460| |Aux461| |Aux462| |Aux463| |Aux464| |Aux465| |Aux466| |Aux467|
                               |Aux468| |Aux469| |Aux470| |Aux471| |Aux472| |Aux473| |Aux474| |Aux475|
                               |Aux476| |Aux477| |Aux478| |Aux479| |Aux480| |Aux481| |Aux482| |Aux483|
                               |Aux484| |Aux485| |Aux486| |Aux487| |Aux488| |Aux489| |Aux490| |Aux491|
                               |Aux492| |Aux493| |Aux494| |Aux495| |Aux496| |Aux497| |Aux498| |Aux499|
                               |Aux500| |Aux501| |Aux502| |Aux503| |Aux504| |Aux505| |Aux506| |Aux507|
                               |Aux508| |Aux509| |Aux510| |Aux511|)
         (acl2::bits-to-bytes-little (list |Output0| |Output1| |Output2| |Output3| |Output4| |Output5| |Output6| |Output7| |Output8| |Output9|
                                           |Output10| |Output11| |Output12| |Output13| |Output14| |Output15| |Output16| |Output17| |Output18| |Output19|
                                           |Output20| |Output21| |Output22| |Output23| |Output24| |Output25| |Output26| |Output27| |Output28| |Output29|
                                           |Output30| |Output31| |Output32| |Output33| |Output34| |Output35| |Output36| |Output37| |Output38| |Output39|
                                           |Output40| |Output41| |Output42| |Output43| |Output44| |Output45| |Output46| |Output47| |Output48| |Output49|
                                           |Output50| |Output51| |Output52| |Output53| |Output54| |Output55| |Output56| |Output57| |Output58| |Output59|
                                           |Output60| |Output61| |Output62| |Output63| |Output64| |Output65| |Output66| |Output67| |Output68| |Output69|
                                           |Output70| |Output71| |Output72| |Output73| |Output74| |Output75| |Output76| |Output77| |Output78| |Output79|
                                           |Output80| |Output81| |Output82| |Output83| |Output84| |Output85| |Output86| |Output87| |Output88| |Output89|
                                           |Output90| |Output91| |Output92| |Output93| |Output94| |Output95| |Output96| |Output97| |Output98| |Output99|
                                           |Output100| |Output101| |Output102| |Output103| |Output104| |Output105| |Output106| |Output107|
                                           |Output108| |Output109| |Output110| |Output111| |Output112| |Output113| |Output114| |Output115|
                                           |Output116| |Output117| |Output118| |Output119| |Output120| |Output121| |Output122| |Output123|
                                           |Output124| |Output125| |Output126| |Output127| |Output128| |Output129| |Output130| |Output131|
                                           |Output132| |Output133| |Output134| |Output135| |Output136| |Output137| |Output138| |Output139|
                                           |Output140| |Output141| |Output142| |Output143| |Output144| |Output145| |Output146| |Output147|
                                           |Output148| |Output149| |Output150| |Output151| |Output152| |Output153| |Output154| |Output155|
                                           |Output156| |Output157| |Output158| |Output159| |Output160| |Output161| |Output162| |Output163|
                                           |Output164| |Output165| |Output166| |Output167| |Output168| |Output169| |Output170| |Output171|
                                           |Output172| |Output173| |Output174| |Output175| |Output176| |Output177| |Output178| |Output179|
                                           |Output180| |Output181| |Output182| |Output183| |Output184| |Output185| |Output186| |Output187|
                                           |Output188| |Output189| |Output190| |Output191| |Output192| |Output193| |Output194| |Output195|
                                           |Output196| |Output197| |Output198| |Output199| |Output200| |Output201| |Output202| |Output203|
                                           |Output204| |Output205| |Output206| |Output207| |Output208| |Output209| |Output210| |Output211|
                                           |Output212| |Output213| |Output214| |Output215| |Output216| |Output217| |Output218| |Output219|
                                           |Output220| |Output221| |Output222| |Output223| |Output224| |Output225| |Output226| |Output227|
                                           |Output228| |Output229| |Output230| |Output231| |Output232| |Output233| |Output234| |Output235|
                                           |Output236| |Output237| |Output238| |Output239| |Output240| |Output241| |Output242| |Output243|
                                           |Output244| |Output245| |Output246| |Output247| |Output248| |Output249| |Output250| |Output251|
                                           |Output252| |Output253| |Output254| |Output255|)))
 :no-splitp t
 :monitor '(pfield::equal-of-0-and-add-of-add-of-neg-lemma)
; :print t
 ;; todo: the tool should build the alist:
 ;; todo: better to use a custom instantiate-hyp function:
 ;; some of these may be needed only for ground proofs:
 :interpreted-function-alist (acl2::make-interpreted-function-alist '(add sub neg pfield::pos-fix ;todo: use an r1cs version of instantiate-hyp and drop these
                                                                          bvcat acl2::logapp
                                                                      ash acl2::expt2$inline acl2::loghead$inline acl2::imod$inline integer-range-p power-of-2p
                                                                      unsigned-byte-p getbit slice acl2::logtail$inline acl2::ifloor$inline bitnot
                                                                      bvnot lognot bitxor bvshr bvshl true-list-fix
                                                                      blake::iv blake::sigma)
                                                                    (w state))
 :global-rules '(acl2::integerp-of-bvcat
                 acl2::integerp-of-bitxor
                 acl2::integerp-of-bvxor
                 acl2::integerp-of-bvnot
                 pfield::integerp-of-add
                 pfield::integerp-of-mul
                 pfield::integerp-of-neg
                 ;; fep rules:
                 pfield::fep-of-mod ;todo: more fep rules?
                 pfield::fep-of-add
                 pfield::fep-of-mul
                 pfield::fep-of-neg
                 pfield::fep-of-bitxor
                 pfield::fep-of-bvcat
                 pfield::fep-of-bvxor
                 pfield::fep-of-bvchop
                 ;; rules to remove mod (todo: perhaps avoid introducing it):
                 pfield::neg-of-mod
                 pfield::add-of-mod-arg1
                 pfield::add-of-mod-arg2
                 pfield::mul-of-mod-arg1
                 pfield::mul-of-mod-arg1
                 ;; booleanp rules:
                 (acl2::booleanp-rules)
                 pfield::booleanp-of-fe-listp
                 ;; bitp rules:
                 acl2::bitp-of-bitxor
                 acl2::bitp-of-getbit
                 ;; acl2::bitp-of-bvchop-of-1 ; drop?
                 ;; fe-listp stuff:
                 pfield::fep-when-fe-listp-and-memberp
                 acl2::memberp-of-append-with-key-first-half-axe
                 acl2::memberp-of-append-with-key-second-half-axe
                 acl2::memberp-of-cons ;todo: make a faster version for axe
                 ;;misc rules:
                 primes::primep-of-bls12-377-scalar-field-prime-constant ;use more?
                 acl2::equal-same
                 pfield::add-of-0-arg1
                 pfield::neg-of-0
                 pfield::add-associative-when-constant ; at least move constants forward, so they can be combined
                 pfield::add-of-add-combine-constants
                 pfield::equal-of-add-combine-constants
                 pfield::add-commutative-when-constant
                 pfield::add-commutative-2-when-constant
                 acl2::ifix-when-integerp
                 pfield::mod-of-ifix-when-fep ; which rules introduce this?
                 acl2::if-of-nil-becomes-booland
                 acl2::slice-becomes-bvchop
                 ACL2::BVCHOP-OF-BVCAT-SAME
                 ACL2::BVCAT-OF-BVCHOP-LOW
                 ACL2::BVCAT-OF-BVCHOP-high
                 )
 :rule-lists '( ;;First, solve and subsitute using all the bitxor and bitnot constraints.  Requires several rounds of substitution:
               ( ;; These introduce BITXOR (not all of these are used):
                pfield::bitxor-constraint-intro
                pfield::bitxor-constraint-intro-alt
                pfield::bitxor-constraint-intro-b
                pfield::bitxor-constraint-intro-b-alt
                pfield::bitxor-constraint-intro-2
                pfield::bitxor-constraint-intro-2-alt
                pfield::bitxor-constraint-intro-2b
                pfield::bitxor-constraint-intro-2b-alt
                ;; These 2 introduce BITNOT (e.g., for output vars):
                pfield::equal-of-1-and-add-when-bitp-arg1
                pfield::equal-of-1-and-add-when-bitp-arg2)

               ;; Next, introduce bitxors and bvcats and lift negs:
               (;;(acl2::unsigned-byte-p-rules)
                ACL2::UNSIGNED-BYTE-P-OF-BVCHOP
                ACL2::UNSIGNED-BYTE-P-OF-BVCAT ;;ACL2::UNSIGNED-BYTE-P-OF-BVCAT-ALL-CASES ;dangerous if bvcat is left associated?
                ACL2::UNSIGNED-BYTE-P-OF-SLICE-GEN
                ACL2::UNSIGNED-BYTE-P-OF-GETBIT
                ACL2::UNSIGNED-BYTE-P-OF-BVIF-GEN
                ACL2::UNSIGNED-BYTE-P-OF-BVAND
                ACL2::UNSIGNED-BYTE-P-OF-BVOR-GEN
                ACL2::UNSIGNED-BYTE-P-OF-BVXOR-GEN
                ACL2::UNSIGNED-BYTE-P-OF-BVNOT
                ACL2::UNSIGNED-BYTE-P-OF-BITAND
                ACL2::UNSIGNED-BYTE-P-OF-BITOR
                ACL2::UNSIGNED-BYTE-P-OF-BITXOR
                ACL2::UNSIGNED-BYTE-P-OF-BITNOT
                ACL2::UNSIGNED-BYTE-P-OF-BVPLUS
                ACL2::UNSIGNED-BYTE-P-OF-BVMINUS-GEN-BETTER
                ACL2::UNSIGNED-BYTE-P-OF-BVUMINUS
                ACL2::UNSIGNED-BYTE-P-OF-BVMULT
                ACL2::UNSIGNED-BYTE-P-OF-BVDIV
                ACL2::UNSIGNED-BYTE-P-OF-BVMOD-GEN
                ACL2::UNSIGNED-BYTE-P-OF-SBVREM
                ACL2::UNSIGNED-BYTE-P-OF-SBVDIV
                ACL2::UNSIGNED-BYTE-P-OF-BVSX
                ACL2::UNSIGNED-BYTE-P-OF-REPEATBIT
                ACL2::UNSIGNED-BYTE-P-OF-LEFTROTATE32
                ACL2::UNSIGNED-BYTE-P-OF-LEFTROTATE
                ACL2::UNSIGNED-BYTE-P-OF-RIGHTROTATE32
                ACL2::UNSIGNED-BYTE-P-OF-RIGHTROTATE
                ACL2::UNSIGNED-BYTE-P-OF-BV-ARRAY-READ-GEN


                pfield::mul-of-power-of-2-when-bitp ; introduces bvcat
                pfield::mul-of-negative-power-of-2-when-bitp ; introduces BVCAT of BITNOT, for when we are not lifting negs above adds
                ;; add-of-neg-of-mul-of-power-of-2-other ; introduce bvcat of bitnot
                pfield::add-of-bvcat-1-of-0-and-add-of-bvcat-1-of-0-extra ; combine the bvcats
                pfield::add-of-bvcat-and-add-of-bvcat-combine-interloper-gen
                ;; these are for when one argument fits into the zeroes of the other:
                pfield::add-of-bvcat-of-0-when-unsigned-byte-p-arg1
                pfield::add-of-bvcat-of-0-when-unsigned-byte-p-arg2
                pfield::add-of-bvcat-of-0-when-unsigned-byte-p-arg1-bitp ; for lowsize=1
                pfield::add-of-bvcat-of-0-when-unsigned-byte-p-arg2-bitp ; for lowsize=1
                pfield::add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra
                pfield::add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special ; for lowsize=1
                pfield::add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-alt
                pfield::add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special-alt
                acl2::bvcat-associative-helper ;; not the usual rule, since we want to expose the low zeros
                ;; acl2::bvcat-combine-constants-old ;; not the usual rule
                pfield::add-of-neg-of-when-bitp ;; turn the NEG into a BITNOT, with an extra added constant
                ;; Lift nots above bvcats:
                acl2::bvcat-of-bvnot-and-bvnot
                acl2::bvcat-of-bitnot-and-bvnot
                acl2::bvcat-of-bvnot-and-bitnot
                acl2::bvcat-of-bitnot-and-bitnot
                pfield::add-of-bvnot-becomes-add-of-neg ;why?
                ;; Unroll bits-to-bytes-little, which is used in the conclusion:
                acl2::bits-to-bytes-little-base
                acl2::bits-to-bytes-little-unroll
                acl2::bits-to-byte-little
                (acl2::list-rules)
                acl2::true-list-fix-of-cons ;add to list-rules?
                acl2::consp-of-nthcdr
                acl2::len-of-nthcdr
                acl2::nthcdr-of-nthcdr
                (acl2::base-rules)
                ;;for running tests:
                ;;acl2::equal-of-cons-when-quotep
                ;;acl2::bvcat-equal-rewrite-constant
                ;;acl2::bvchop-of-1-when-bitp
                ;;acl2::bvchop-of-bvcat-cases ; dangerous?
                ;;acl2::equal-of-cons-and-cons ;rewrites the top equality
                )

               ;; Next, move the negs:
               (pfield::equal-of-0-and-add-of-add-of-add-of-neg-lemma
                pfield::equal-of-0-and-add-of-add-of-add-of-neg-lemma-alt
                pfield::equal-of-0-and-add-of-add-of-neg-lemma
                pfield::equal-of-0-and-add-of-neg-arg1
                pfield::equal-of-0-and-add-of-neg-arg2
                (pfield::prime-field-proof-rules) ;whoa! has add-commutative
                pfield::equal-of-add-of-add-of-neg-arg2-arg2
                ;; pfield::mod-of-add
                ;;if-of-t-and-nil-when-booleanp
                acl2::mod-when-<
                acl2::bvcat-numeric-bound
                ;;not-<-of-bvcat-and-0
                acl2::rationalp-when-integerp
                pfield::equal-of-constant-and-add-of-neg-arg1
                pfield::equal-of-constant-and-add-of-neg-arg2
                ;; also lift nots and constant xors out of cats:
                acl2::bvcat-of-bvxor-low-when-quotep
                acl2::bvcat-of-bvxor-high-when-quotep
                acl2::bvcat-of-bitxor-low-when-quotep
                acl2::bvcat-of-bitxor-high-when-quotep
                acl2::bvcat-of-bitnot-low
                acl2::bvcat-of-bitnot-high
                acl2::bvcat-of-bvnot-low
                acl2::bvcat-of-bvnot-high
                acl2::bvxor-combine-constants
                ;; maybe these won't blow up if we do them here:
                acl2::bitxor-commutative-increasing-axe
                acl2::bitxor-commutative-2-increasing-axe
                acl2::bitxor-associative
                ;; hope we get lucky and can lift the xors out of the cats and have things pair up right:
                acl2::bvcat-of-bitxor-and-bitxor
                acl2::bvcat-of-bitxor-and-bvxor
                acl2::bvcat-of-bvxor-and-bitxor
                acl2::bvcat-of-bvxor-and-bvxor)

               ;;Now blast the equated bvcats, since the prover only substitutes for variables:
               (acl2::bvcat-equal-rewrite
                acl2::bvcat-equal-rewrite-alt
                ;acl2::bvchop-of-bvcat-cases ;could be dangerous, esp if bvcat is left associated?
                (acl2::unsigned-byte-p-rules)
                bvchop-of-1-when-bitp
                acl2::bvchop-1-becomes-getbit
                ;; why these?:
                ;; acl2::bvcat-of-getbit-and-getbit-adjacent
                ;; acl2::bvcat-of-slice-and-slice-adjacent
                ;; acl2::bvcat-of-getbit-and-slice-adjacent
                ;; acl2::bvcat-of-slice-and-getbit-adjacent
                acl2::getbit-of-bvchop
                acl2::getbit-of-slice-gen ;todo: generalize the (integerp x)
                acl2::getbit-of-slice
                acl2::slice-of-slice
                acl2::getbit-of-0-when-bitp
                pfield::unsigned-byte-p-of-add
                pfield::equal-of-neg-solve
                pfield::equal-of-neg-solve-alt
                pfield::add-commutative-axe
                pfield::equal-of-add-combine-constants
                pfield::equal-of-constant-and-add-of-neg-arg1
                pfield::equal-of-constant-and-add-of-neg-arg2
                acl2::bvcat-of-bitnot-low
                acl2::bvcat-of-bitnot-high
                acl2::bvcat-of-bvnot-low
                acl2::bvcat-of-bvnot-high
                ;acl2::bvcat-of-bvxor-high-when-quotep
                ;acl2::bvcat-of-bvxor-low-when-quotep
                acl2::slice-becomes-getbit
                ;; handle remaining adds:
                add-of-constant-normalize-to-fep
                pfield::add-becomes-bvplus-34
                pfield::add-becomes-bvplus-33
                acl2::slice-of-bvplus-tighten-to-32
                acl2::getbit-of-bvplus-tighten-to-32
                acl2::bvplus-of-bvplus-trim-to-32-arg1
                acl2::bvplus-of-bvplus-trim-to-32-arg2
                acl2::bvxor-combine-constants
                ;; acl2::bvcat-of-getbit-and-getbit-adjacent-2-left-assoc
                ;; acl2::bvcat-of-getbit-and-slice-adjacent-2-left-assoc
                ;; acl2::bvcat-of-slice-and-slice-adjacent-2-left-assoc
                ;; acl2::bvcat-of-slice-and-getbit-adjacent-2-left-assoc
                ;; reconstruct the rotates:
                ;; bvcat-becomes-rightrotate
                ;; acl2::bvcat-becomes-rightrotate-2
                ;; acl2::bvcat-31-of-getbit-31-becomes-rightrotate
                acl2::bvcat-associative-helper ; needed for the left-assoc rules above
                )
               ;;new:
               (acl2::bvcat-of-getbit-and-getbit-adjacent
                acl2::bvcat-of-slice-and-slice-adjacent
                acl2::bvcat-of-getbit-and-slice-adjacent
                acl2::bvcat-of-slice-and-getbit-adjacent
                acl2::bvcat-of-getbit-and-getbit-adjacent-2-left-assoc
                acl2::bvcat-of-getbit-and-slice-adjacent-2-left-assoc
                acl2::bvcat-of-slice-and-slice-adjacent-2-left-assoc
                acl2::bvcat-of-slice-and-getbit-adjacent-2-left-assoc
                acl2::bvcat-of-getbit-and-x-adjacent
                acl2::bvcat-becomes-rightrotate-2 ; may not fire?
                ACL2::BVCAT-OF-SLICE-SAME-BECOMES-RIGHTROTATE
                acl2::bvcat-31-of-getbit-31-becomes-rightrotate

                )

               ;; now open the spec and finish the proof:
               (blake2s1round-no-key
                (acl2::list-rules)
                acl2::true-list-fix-of-cons
                acl2::consp-of-nthcdr
                acl2::len-of-nthcdr
                acl2::nthcdr-of-nthcdr
                (acl2::base-rules)
                blake::blake2s
                blake::d-blocks
                blake::pad-data-bytes
                blake::bytes-to-blocks-base-2
                blake::bytes-to-blocks-unroll
                ;; acl2::consp-when-len-equal
                ;; acl2::consp-when-len-equal-alt
                ;;endp
                blake::bytes-to-block
                blake::bytes-to-words-base
                blake::bytes-to-words-unroll
                ;; acl2::nthcdr-when-equal-of-len
                blake::bytes-to-word
                blake::blake2s-main
                blake::f
                blake::f-loop-1-base
                blake::f-loop-1-unroll
                blake::f-loop-2-base
                blake::f-loop-2-unroll
                blake::loop1-base
                blake::loop1-unroll
                blake::wordxor
                blake::g
                blake::rot-word
                acl2::nth-of-nthcdr
                blake::len-of-bytes-to-blocks
                blake::sigma
                blake::iv
                blake::words-to-bytes-base
                blake::words-to-bytes-unroll
                blake::word-to-bytes
                acl2::mod-of-+-of-4294967296
                acl2::bvplus-of-+-arg2
                acl2::bvplus-of-+-arg3
                acl2::update-nth-of-update-nth-same
                acl2::cdr-of-update-nth
                acl2::car-of-update-nth
                acl2::bvshl-of-0-arg2
                acl2::bvplus-combine-constants
                (acl2::type-rules)
                acl2::bits-to-bytes-little-base
                acl2::bits-to-bytes-little-unroll
                acl2::bits-to-byte-little
                ;; more rules to try to complete the proof:
                acl2::equal-of-cons-and-cons ;rewrites the top equality
                add-of-constant-normalize-to-fep
                ;; why do we have to tighten these terms?:
                acl2::slice-of-bvxor-tighten
                acl2::bvxor-of-bvxor-tighten
                acl2::bvxor-of-bvxor-tighten-alt
                acl2::slice-becomes-bvchop
                ACL2::BVXOR-OF-CONSTANT-CHOP-ARG2 ;acl2::bvxor-of-constant-trim-arg1
                acl2::bvchop-identity
                acl2::bvxor-of-bvchop-same-arg1
                acl2::bvxor-of-bvchop-same-arg2
                acl2::bvcat-of-bvchop-low
                acl2::bvcat-of-bvchop-high
                (acl2::unsigned-byte-p-rules)
                ;; these 3 could be risky:
                acl2::bvplus-associative
                acl2::bvplus-commutative-increasing-axe
                acl2::bvplus-commutative-2-increasing-axe
                ;; these 3 could be risky:
                acl2::bvxor-associative
                acl2::bvxor-commutative-axe
                acl2::bvxor-commutative-2-axe
                acl2::bvcat-associative-helper
                acl2::bvplus-trim-leading-constant
                acl2::rightrotate-becomes-leftrotate ;stp translation supports leftrotate32
                acl2::leftrotate-becomes-leftrotate32 ;stp translation supports leftrotate32
                ;; acl2::leftrotate32-of-bvxor-32-when-constant ;trying just for constants, for now
                acl2::leftrotate32-of-bvxor-32
                acl2::leftrotate32-of-leftrotate32
                acl2::leftrotate32-of-0-arg1
                acl2::bvcat-31-of-getbit-31-becomes-rightrotate
                acl2::slice-of-bvxor ;try
                acl2::bvxor-combine-constants
                acl2::bvxor-cancel
                acl2::slice-of-leftrotate32 ; or restrict to nice cases?
                acl2::slice-becomes-getbit
                acl2::bvxor-of-leftrotate32-trim-8-arg1
                acl2::bvxor-of-leftrotate32-trim-8-arg2
                acl2::trim-of-leftrotate32)
               ))
