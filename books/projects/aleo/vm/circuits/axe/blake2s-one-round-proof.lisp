; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

;; This file contains a proof of the one-round Blake2s R1CS.  The proof
;; involves bit-blasting everything.

;; STATUS: Complete but needs cleanup

(include-book "blake2s-one-round-r1cs")
(include-book "support-blake2s")
(include-book "kestrel/axe/r1cs/lift-r1cs" :dir :system)
(include-book "kestrel/axe/r1cs/axe-rules-r1cs" :dir :system)
(include-book "kestrel/axe/r1cs/axe-prover-r1cs" :dir :system)
(include-book "kestrel/crypto/r1cs/gadgets/boolean-alt-rules" :dir :system)
(include-book "kestrel/crypto/r1cs/gadgets/xor-rules" :dir :system)
;(include-book "kestrel/axe/dag-info" :dir :system)
(include-book "kestrel/axe/make-conjunction-dag" :dir :system)
(include-book "kestrel/bv/rules7" :dir :system)
(include-book "kestrel/bv/rules9" :dir :system)
(include-book "kestrel/bv/rules6" :dir :system)
(include-book "kestrel/bv-lists/bits-to-bytes-little" :dir :system)
(include-book "kestrel/bv-lists/bits-to-bytes2" :dir :system)
(include-book "kestrel/bv-lists/bits-to-bytes-little2" :dir :system)
(include-book "projects/bls12-377-curves/primes/bls12-377-prime" :dir :system)
(include-book "kestrel/lists-light/cons" :dir :system)
(include-book "blake2s-one-round-spec-openers")
(include-book "kestrel/prime-fields/fe-listp-fast" :dir :system)

;todo: do more idiom introduction here?  but we need the assumptons, like bitp facts..
;maybe the funny idiom is xoring with a constant...
;does this put in all the bitp constraints?  maybe so...  need fep assumptions for that...
(local
 (r1cs::lift-r1cs *blake-r1cs-lifted* ; name of the constant that will hold the result
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

;; The spec function: Take the 512 input bits, pack them into bytes, and call
;; the spec function blake::blake2s on the bytes.
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


;; tricky issues:
;; - 8-bit vs 9-bit sums (carrry)
;; - no variable actually contains the sum, so can't subst for vars
;; - whether to turn bvplus into add or add into bvplus
;; - whether we need to assume FEP for all the vars... i am seeing (equal <expr> (mod (ifix <var>) p))
;; - it looks like we are applying a mask to extrat certain bits?

;; TODO: A smaller version
;; TODO: Look at source
;; TODO: Ask about the pattern of positive and negative coeffs

;; Need FEP assuptions. plan: introduce all-fep.
;; faster: binary-tree of keyed appends.  axe-syntaxp rule if the var name is symbol-< the key, backchain to showing that it's in the left branch, else the right branch.
;; will need a new axe-syntax function.  will need to generalize prove-basic to macro that generates a prover.

;todo: make an R1CS calculator: given values for the inputs (even if it has to "solve" a bit, e.g., if we give them in packed form)...
;; this solves the xor constraints (we need fep assumptions to solve all of them to the form var=...)
;; (acl2::prove-implication-with-r1cs-prover (acl2::make-conjunction-dag! (acl2::make-term-into-dag-basic!
;;                                                                         ;; TODO: Go back to this:
;;                                                                         ;; (pfield::gen-fe-listp-assumption (acl2::dag-vars *blake-r1cs-lifted*) ; todo: wrong package: *blake2s-one-round-vars*
;;                                                                         ;;                          ''8444461749428370424248824938781546531375899335154063827935233455917409239041)
;;                                                                         ;todo: tool should translate this assumptions?
;;                                                                         `(acl2::booland ,(pfield::gen-fe-listp-assumption (acl2::dag-vars *blake-r1cs-lifted*) ; todo: wrong package: *blake2s-one-round-vars*
;;                                                                                                                   ''8444461749428370424248824938781546531375899335154063827935233455917409239041)
;;                                                                                         ;;Are the r1cs vars all bits?  assuming that, in a single assumption, might speed things up a lot...
;;                                                                                         ;; this removes lots of bitp constraints, to keep the set small:
;;                                                                                         ;; TODO: Remove this:
;;                                                                                         ;; todo: i had just booland instead of acl2::booland -- should be a more clear error
;;                                                                                         (acl2::booland ,(gen-bit-listp-assumption (acl2::dag-vars *blake-r1cs-lifted*))
;;                                                                                                  ;; todo: drop:
;;                                                                                                  (equal '(0 0 0 0 0 0 0 0
;;                                                                                                             0 0 0 0 0 0 0 0
;;                                                                                                             0 0 0 0 0 0 0 0
;;                                                                                                             0 0 0 0 0 0 0 0
;;                                                                                                             0 0 0 0 0 0 0 0
;;                                                                                                             0 0 0 0 0 0 0 0
;;                                                                                                             0 0 0 0 0 0 0 0
;;                                                                                                             0 0 0 0 0 0 0 0)
;;                                                                                                         (acl2::bits-to-bytes-little ,(acl2::make-cons-nest '( acl2::|Aux0| acl2::|Aux1| acl2::|Aux2| acl2::|Aux3| acl2::|Aux4|
;;                                                                                                                                                              acl2::|Aux5| acl2::|Aux6| acl2::|Aux7| acl2::|Aux8| acl2::|Aux9|
;;                                                                                                                                                              acl2::|Aux10| acl2::|Aux11| acl2::|Aux12| acl2::|Aux13| acl2::|Aux14|
;;                                                                                                                                                              acl2::|Aux15| acl2::|Aux16| acl2::|Aux17| acl2::|Aux18| acl2::|Aux19|
;;                                                                                                                                                              acl2::|Aux20| acl2::|Aux21| acl2::|Aux22| acl2::|Aux23| acl2::|Aux24|
;;                                                                                                                                                              acl2::|Aux25| acl2::|Aux26| acl2::|Aux27| acl2::|Aux28| acl2::|Aux29|
;;                                                                                                                                                              acl2::|Aux30| acl2::|Aux31| acl2::|Aux32| acl2::|Aux33| acl2::|Aux34|
;;                                                                                                                                                              acl2::|Aux35| acl2::|Aux36| acl2::|Aux37| acl2::|Aux38| acl2::|Aux39|
;;                                                                                                                                                              acl2::|Aux40| acl2::|Aux41| acl2::|Aux42| acl2::|Aux43| acl2::|Aux44|
;;                                                                                                                                                              acl2::|Aux45| acl2::|Aux46| acl2::|Aux47| acl2::|Aux48| acl2::|Aux49|
;;                                                                                                                                                              acl2::|Aux50| acl2::|Aux51| acl2::|Aux52| acl2::|Aux53| acl2::|Aux54|
;;                                                                                                                                                              acl2::|Aux55| acl2::|Aux56| acl2::|Aux57| acl2::|Aux58| acl2::|Aux59|
;;                                                                                                                                                              acl2::|Aux60| acl2::|Aux61| acl2::|Aux62| acl2::|Aux63| acl2::|Aux64|
;;                                                                                                                                                              acl2::|Aux65| acl2::|Aux66| acl2::|Aux67| acl2::|Aux68| acl2::|Aux69|
;;                                                                                                                                                              acl2::|Aux70| acl2::|Aux71| acl2::|Aux72| acl2::|Aux73| acl2::|Aux74|
;;                                                                                                                                                              acl2::|Aux75| acl2::|Aux76| acl2::|Aux77| acl2::|Aux78| acl2::|Aux79|
;;                                                                                                                                                              acl2::|Aux80| acl2::|Aux81| acl2::|Aux82| acl2::|Aux83| acl2::|Aux84|
;;                                                                                                                                                              acl2::|Aux85| acl2::|Aux86| acl2::|Aux87| acl2::|Aux88| acl2::|Aux89|
;;                                                                                                                                                              acl2::|Aux90| acl2::|Aux91| acl2::|Aux92| acl2::|Aux93| acl2::|Aux94|
;;                                                                                                                                                              acl2::|Aux95| acl2::|Aux96| acl2::|Aux97| acl2::|Aux98| acl2::|Aux99|
;;                                                                                                                                                              acl2::|Aux100| acl2::|Aux101| acl2::|Aux102| acl2::|Aux103|
;;                                                                                                                                                              acl2::|Aux104| acl2::|Aux105| acl2::|Aux106| acl2::|Aux107|
;;                                                                                                                                                              acl2::|Aux108| acl2::|Aux109| acl2::|Aux110| acl2::|Aux111|
;;                                                                                                                                                              acl2::|Aux112| acl2::|Aux113| acl2::|Aux114| acl2::|Aux115|
;;                                                                                                                                                              acl2::|Aux116| acl2::|Aux117| acl2::|Aux118| acl2::|Aux119|
;;                                                                                                                                                              acl2::|Aux120| acl2::|Aux121| acl2::|Aux122| acl2::|Aux123|
;;                                                                                                                                                              acl2::|Aux124| acl2::|Aux125| acl2::|Aux126| acl2::|Aux127|
;;                                                                                                                                                              acl2::|Aux128| acl2::|Aux129| acl2::|Aux130| acl2::|Aux131|
;;                                                                                                                                                              acl2::|Aux132| acl2::|Aux133| acl2::|Aux134| acl2::|Aux135|
;;                                                                                                                                                              acl2::|Aux136| acl2::|Aux137| acl2::|Aux138| acl2::|Aux139|
;;                                                                                                                                                              acl2::|Aux140| acl2::|Aux141| acl2::|Aux142| acl2::|Aux143|
;;                                                                                                                                                              acl2::|Aux144| acl2::|Aux145| acl2::|Aux146| acl2::|Aux147|
;;                                                                                                                                                              acl2::|Aux148| acl2::|Aux149| acl2::|Aux150| acl2::|Aux151|
;;                                                                                                                                                              acl2::|Aux152| acl2::|Aux153| acl2::|Aux154| acl2::|Aux155|
;;                                                                                                                                                              acl2::|Aux156| acl2::|Aux157| acl2::|Aux158| acl2::|Aux159|
;;                                                                                                                                                              acl2::|Aux160| acl2::|Aux161| acl2::|Aux162| acl2::|Aux163|
;;                                                                                                                                                              acl2::|Aux164| acl2::|Aux165| acl2::|Aux166| acl2::|Aux167|
;;                                                                                                                                                              acl2::|Aux168| acl2::|Aux169| acl2::|Aux170| acl2::|Aux171|
;;                                                                                                                                                              acl2::|Aux172| acl2::|Aux173| acl2::|Aux174| acl2::|Aux175|
;;                                                                                                                                                              acl2::|Aux176| acl2::|Aux177| acl2::|Aux178| acl2::|Aux179|
;;                                                                                                                                                              acl2::|Aux180| acl2::|Aux181| acl2::|Aux182| acl2::|Aux183|
;;                                                                                                                                                              acl2::|Aux184| acl2::|Aux185| acl2::|Aux186| acl2::|Aux187|
;;                                                                                                                                                              acl2::|Aux188| acl2::|Aux189| acl2::|Aux190| acl2::|Aux191|
;;                                                                                                                                                              acl2::|Aux192| acl2::|Aux193| acl2::|Aux194| acl2::|Aux195|
;;                                                                                                                                                              acl2::|Aux196| acl2::|Aux197| acl2::|Aux198| acl2::|Aux199|
;;                                                                                                                                                              acl2::|Aux200| acl2::|Aux201| acl2::|Aux202| acl2::|Aux203|
;;                                                                                                                                                              acl2::|Aux204| acl2::|Aux205| acl2::|Aux206| acl2::|Aux207|
;;                                                                                                                                                              acl2::|Aux208| acl2::|Aux209| acl2::|Aux210| acl2::|Aux211|
;;                                                                                                                                                              acl2::|Aux212| acl2::|Aux213| acl2::|Aux214| acl2::|Aux215|
;;                                                                                                                                                              acl2::|Aux216| acl2::|Aux217| acl2::|Aux218| acl2::|Aux219|
;;                                                                                                                                                              acl2::|Aux220| acl2::|Aux221| acl2::|Aux222| acl2::|Aux223|
;;                                                                                                                                                              acl2::|Aux224| acl2::|Aux225| acl2::|Aux226| acl2::|Aux227|
;;                                                                                                                                                              acl2::|Aux228| acl2::|Aux229| acl2::|Aux230| acl2::|Aux231|
;;                                                                                                                                                              acl2::|Aux232| acl2::|Aux233| acl2::|Aux234| acl2::|Aux235|
;;                                                                                                                                                              acl2::|Aux236| acl2::|Aux237| acl2::|Aux238| acl2::|Aux239|
;;                                                                                                                                                              acl2::|Aux240| acl2::|Aux241| acl2::|Aux242| acl2::|Aux243|
;;                                                                                                                                                              acl2::|Aux244| acl2::|Aux245| acl2::|Aux246| acl2::|Aux247|
;;                                                                                                                                                              acl2::|Aux248| acl2::|Aux249| acl2::|Aux250| acl2::|Aux251|
;;                                                                                                                                                              acl2::|Aux252| acl2::|Aux253| acl2::|Aux254| acl2::|Aux255|
;;                                                                                                                                                              acl2::|Aux256| acl2::|Aux257| acl2::|Aux258| acl2::|Aux259|
;;                                                                                                                                                              acl2::|Aux260| acl2::|Aux261| acl2::|Aux262| acl2::|Aux263|
;;                                                                                                                                                              acl2::|Aux264| acl2::|Aux265| acl2::|Aux266| acl2::|Aux267|
;;                                                                                                                                                              acl2::|Aux268| acl2::|Aux269| acl2::|Aux270| acl2::|Aux271|
;;                                                                                                                                                              acl2::|Aux272| acl2::|Aux273| acl2::|Aux274| acl2::|Aux275|
;;                                                                                                                                                              acl2::|Aux276| acl2::|Aux277| acl2::|Aux278| acl2::|Aux279|
;;                                                                                                                                                              acl2::|Aux280| acl2::|Aux281| acl2::|Aux282| acl2::|Aux283|
;;                                                                                                                                                              acl2::|Aux284| acl2::|Aux285| acl2::|Aux286| acl2::|Aux287|
;;                                                                                                                                                              acl2::|Aux288| acl2::|Aux289| acl2::|Aux290| acl2::|Aux291|
;;                                                                                                                                                              acl2::|Aux292| acl2::|Aux293| acl2::|Aux294| acl2::|Aux295|
;;                                                                                                                                                              acl2::|Aux296| acl2::|Aux297| acl2::|Aux298| acl2::|Aux299|
;;                                                                                                                                                              acl2::|Aux300| acl2::|Aux301| acl2::|Aux302| acl2::|Aux303|
;;                                                                                                                                                              acl2::|Aux304| acl2::|Aux305| acl2::|Aux306| acl2::|Aux307|
;;                                                                                                                                                              acl2::|Aux308| acl2::|Aux309| acl2::|Aux310| acl2::|Aux311|
;;                                                                                                                                                              acl2::|Aux312| acl2::|Aux313| acl2::|Aux314| acl2::|Aux315|
;;                                                                                                                                                              acl2::|Aux316| acl2::|Aux317| acl2::|Aux318| acl2::|Aux319|
;;                                                                                                                                                              acl2::|Aux320| acl2::|Aux321| acl2::|Aux322| acl2::|Aux323|
;;                                                                                                                                                              acl2::|Aux324| acl2::|Aux325| acl2::|Aux326| acl2::|Aux327|
;;                                                                                                                                                              acl2::|Aux328| acl2::|Aux329| acl2::|Aux330| acl2::|Aux331|
;;                                                                                                                                                              acl2::|Aux332| acl2::|Aux333| acl2::|Aux334| acl2::|Aux335|
;;                                                                                                                                                              acl2::|Aux336| acl2::|Aux337| acl2::|Aux338| acl2::|Aux339|
;;                                                                                                                                                              acl2::|Aux340| acl2::|Aux341| acl2::|Aux342| acl2::|Aux343|
;;                                                                                                                                                              acl2::|Aux344| acl2::|Aux345| acl2::|Aux346| acl2::|Aux347|
;;                                                                                                                                                              acl2::|Aux348| acl2::|Aux349| acl2::|Aux350| acl2::|Aux351|
;;                                                                                                                                                              acl2::|Aux352| acl2::|Aux353| acl2::|Aux354| acl2::|Aux355|
;;                                                                                                                                                              acl2::|Aux356| acl2::|Aux357| acl2::|Aux358| acl2::|Aux359|
;;                                                                                                                                                              acl2::|Aux360| acl2::|Aux361| acl2::|Aux362| acl2::|Aux363|
;;                                                                                                                                                              acl2::|Aux364| acl2::|Aux365| acl2::|Aux366| acl2::|Aux367|
;;                                                                                                                                                              acl2::|Aux368| acl2::|Aux369| acl2::|Aux370| acl2::|Aux371|
;;                                                                                                                                                              acl2::|Aux372| acl2::|Aux373| acl2::|Aux374| acl2::|Aux375|
;;                                                                                                                                                              acl2::|Aux376| acl2::|Aux377| acl2::|Aux378| acl2::|Aux379|
;;                                                                                                                                                              acl2::|Aux380| acl2::|Aux381| acl2::|Aux382| acl2::|Aux383|
;;                                                                                                                                                              acl2::|Aux384| acl2::|Aux385| acl2::|Aux386| acl2::|Aux387|
;;                                                                                                                                                              acl2::|Aux388| acl2::|Aux389| acl2::|Aux390| acl2::|Aux391|
;;                                                                                                                                                              acl2::|Aux392| acl2::|Aux393| acl2::|Aux394| acl2::|Aux395|
;;                                                                                                                                                              acl2::|Aux396| acl2::|Aux397| acl2::|Aux398| acl2::|Aux399|
;;                                                                                                                                                              acl2::|Aux400| acl2::|Aux401| acl2::|Aux402| acl2::|Aux403|
;;                                                                                                                                                              acl2::|Aux404| acl2::|Aux405| acl2::|Aux406| acl2::|Aux407|
;;                                                                                                                                                              acl2::|Aux408| acl2::|Aux409| acl2::|Aux410| acl2::|Aux411|
;;                                                                                                                                                              acl2::|Aux412| acl2::|Aux413| acl2::|Aux414| acl2::|Aux415|
;;                                                                                                                                                              acl2::|Aux416| acl2::|Aux417| acl2::|Aux418| acl2::|Aux419|
;;                                                                                                                                                              acl2::|Aux420| acl2::|Aux421| acl2::|Aux422| acl2::|Aux423|
;;                                                                                                                                                              acl2::|Aux424| acl2::|Aux425| acl2::|Aux426| acl2::|Aux427|
;;                                                                                                                                                              acl2::|Aux428| acl2::|Aux429| acl2::|Aux430| acl2::|Aux431|
;;                                                                                                                                                              acl2::|Aux432| acl2::|Aux433| acl2::|Aux434| acl2::|Aux435|
;;                                                                                                                                                              acl2::|Aux436| acl2::|Aux437| acl2::|Aux438| acl2::|Aux439|
;;                                                                                                                                                              acl2::|Aux440| acl2::|Aux441| acl2::|Aux442| acl2::|Aux443|
;;                                                                                                                                                              acl2::|Aux444| acl2::|Aux445| acl2::|Aux446| acl2::|Aux447|
;;                                                                                                                                                              acl2::|Aux448| acl2::|Aux449| acl2::|Aux450| acl2::|Aux451|
;;                                                                                                                                                              acl2::|Aux452| acl2::|Aux453| acl2::|Aux454| acl2::|Aux455|
;;                                                                                                                                                              acl2::|Aux456| acl2::|Aux457| acl2::|Aux458| acl2::|Aux459|
;;                                                                                                                                                              acl2::|Aux460| acl2::|Aux461| acl2::|Aux462| acl2::|Aux463|
;;                                                                                                                                                              acl2::|Aux464| acl2::|Aux465| acl2::|Aux466| acl2::|Aux467|
;;                                                                                                                                                              acl2::|Aux468| acl2::|Aux469| acl2::|Aux470| acl2::|Aux471|
;;                                                                                                                                                              acl2::|Aux472| acl2::|Aux473| acl2::|Aux474| acl2::|Aux475|
;;                                                                                                                                                              acl2::|Aux476| acl2::|Aux477| acl2::|Aux478| acl2::|Aux479|
;;                                                                                                                                                              acl2::|Aux480| acl2::|Aux481| acl2::|Aux482| acl2::|Aux483|
;;                                                                                                                                                              acl2::|Aux484| acl2::|Aux485| acl2::|Aux486| acl2::|Aux487|
;;                                                                                                                                                              acl2::|Aux488| acl2::|Aux489| acl2::|Aux490| acl2::|Aux491|
;;                                                                                                                                                              acl2::|Aux492| acl2::|Aux493| acl2::|Aux494| acl2::|Aux495|
;;                                                                                                                                                              acl2::|Aux496| acl2::|Aux497| acl2::|Aux498| acl2::|Aux499|
;;                                                                                                                                                              acl2::|Aux500| acl2::|Aux501| acl2::|Aux502| acl2::|Aux503|
;;                                                                                                                                                              acl2::|Aux504| acl2::|Aux505| acl2::|Aux506| acl2::|Aux507|
;;                                                                                                                                                              acl2::|Aux508| acl2::|Aux509| acl2::|Aux510| acl2::|Aux511|))))))
;;                                                                         nil)
;;                                                                        *blake-r1cs-lifted*)
;;                                           '(equal (blake2s1round-no-key acl2::|Aux0| acl2::|Aux1| acl2::|Aux2| acl2::|Aux3| acl2::|Aux4|
;;                                                                         acl2::|Aux5| acl2::|Aux6| acl2::|Aux7| acl2::|Aux8| acl2::|Aux9|
;;                                                                         acl2::|Aux10| acl2::|Aux11| acl2::|Aux12| acl2::|Aux13| acl2::|Aux14|
;;                                                                         acl2::|Aux15| acl2::|Aux16| acl2::|Aux17| acl2::|Aux18| acl2::|Aux19|
;;                                                                         acl2::|Aux20| acl2::|Aux21| acl2::|Aux22| acl2::|Aux23| acl2::|Aux24|
;;                                                                         acl2::|Aux25| acl2::|Aux26| acl2::|Aux27| acl2::|Aux28| acl2::|Aux29|
;;                                                                         acl2::|Aux30| acl2::|Aux31| acl2::|Aux32| acl2::|Aux33| acl2::|Aux34|
;;                                                                         acl2::|Aux35| acl2::|Aux36| acl2::|Aux37| acl2::|Aux38| acl2::|Aux39|
;;                                                                         acl2::|Aux40| acl2::|Aux41| acl2::|Aux42| acl2::|Aux43| acl2::|Aux44|
;;                                                                         acl2::|Aux45| acl2::|Aux46| acl2::|Aux47| acl2::|Aux48| acl2::|Aux49|
;;                                                                         acl2::|Aux50| acl2::|Aux51| acl2::|Aux52| acl2::|Aux53| acl2::|Aux54|
;;                                                                         acl2::|Aux55| acl2::|Aux56| acl2::|Aux57| acl2::|Aux58| acl2::|Aux59|
;;                                                                         acl2::|Aux60| acl2::|Aux61| acl2::|Aux62| acl2::|Aux63| acl2::|Aux64|
;;                                                                         acl2::|Aux65| acl2::|Aux66| acl2::|Aux67| acl2::|Aux68| acl2::|Aux69|
;;                                                                         acl2::|Aux70| acl2::|Aux71| acl2::|Aux72| acl2::|Aux73| acl2::|Aux74|
;;                                                                         acl2::|Aux75| acl2::|Aux76| acl2::|Aux77| acl2::|Aux78| acl2::|Aux79|
;;                                                                         acl2::|Aux80| acl2::|Aux81| acl2::|Aux82| acl2::|Aux83| acl2::|Aux84|
;;                                                                         acl2::|Aux85| acl2::|Aux86| acl2::|Aux87| acl2::|Aux88| acl2::|Aux89|
;;                                                                         acl2::|Aux90| acl2::|Aux91| acl2::|Aux92| acl2::|Aux93| acl2::|Aux94|
;;                                                                         acl2::|Aux95| acl2::|Aux96| acl2::|Aux97| acl2::|Aux98| acl2::|Aux99|
;;                                                                         acl2::|Aux100| acl2::|Aux101| acl2::|Aux102| acl2::|Aux103|
;;                                                                         acl2::|Aux104| acl2::|Aux105| acl2::|Aux106| acl2::|Aux107|
;;                                                                         acl2::|Aux108| acl2::|Aux109| acl2::|Aux110| acl2::|Aux111|
;;                                                                         acl2::|Aux112| acl2::|Aux113| acl2::|Aux114| acl2::|Aux115|
;;                                                                         acl2::|Aux116| acl2::|Aux117| acl2::|Aux118| acl2::|Aux119|
;;                                                                         acl2::|Aux120| acl2::|Aux121| acl2::|Aux122| acl2::|Aux123|
;;                                                                         acl2::|Aux124| acl2::|Aux125| acl2::|Aux126| acl2::|Aux127|
;;                                                                         acl2::|Aux128| acl2::|Aux129| acl2::|Aux130| acl2::|Aux131|
;;                                                                         acl2::|Aux132| acl2::|Aux133| acl2::|Aux134| acl2::|Aux135|
;;                                                                         acl2::|Aux136| acl2::|Aux137| acl2::|Aux138| acl2::|Aux139|
;;                                                                         acl2::|Aux140| acl2::|Aux141| acl2::|Aux142| acl2::|Aux143|
;;                                                                         acl2::|Aux144| acl2::|Aux145| acl2::|Aux146| acl2::|Aux147|
;;                                                                         acl2::|Aux148| acl2::|Aux149| acl2::|Aux150| acl2::|Aux151|
;;                                                                         acl2::|Aux152| acl2::|Aux153| acl2::|Aux154| acl2::|Aux155|
;;                                                                         acl2::|Aux156| acl2::|Aux157| acl2::|Aux158| acl2::|Aux159|
;;                                                                         acl2::|Aux160| acl2::|Aux161| acl2::|Aux162| acl2::|Aux163|
;;                                                                         acl2::|Aux164| acl2::|Aux165| acl2::|Aux166| acl2::|Aux167|
;;                                                                         acl2::|Aux168| acl2::|Aux169| acl2::|Aux170| acl2::|Aux171|
;;                                                                         acl2::|Aux172| acl2::|Aux173| acl2::|Aux174| acl2::|Aux175|
;;                                                                         acl2::|Aux176| acl2::|Aux177| acl2::|Aux178| acl2::|Aux179|
;;                                                                         acl2::|Aux180| acl2::|Aux181| acl2::|Aux182| acl2::|Aux183|
;;                                                                         acl2::|Aux184| acl2::|Aux185| acl2::|Aux186| acl2::|Aux187|
;;                                                                         acl2::|Aux188| acl2::|Aux189| acl2::|Aux190| acl2::|Aux191|
;;                                                                         acl2::|Aux192| acl2::|Aux193| acl2::|Aux194| acl2::|Aux195|
;;                                                                         acl2::|Aux196| acl2::|Aux197| acl2::|Aux198| acl2::|Aux199|
;;                                                                         acl2::|Aux200| acl2::|Aux201| acl2::|Aux202| acl2::|Aux203|
;;                                                                         acl2::|Aux204| acl2::|Aux205| acl2::|Aux206| acl2::|Aux207|
;;                                                                         acl2::|Aux208| acl2::|Aux209| acl2::|Aux210| acl2::|Aux211|
;;                                                                         acl2::|Aux212| acl2::|Aux213| acl2::|Aux214| acl2::|Aux215|
;;                                                                         acl2::|Aux216| acl2::|Aux217| acl2::|Aux218| acl2::|Aux219|
;;                                                                         acl2::|Aux220| acl2::|Aux221| acl2::|Aux222| acl2::|Aux223|
;;                                                                         acl2::|Aux224| acl2::|Aux225| acl2::|Aux226| acl2::|Aux227|
;;                                                                         acl2::|Aux228| acl2::|Aux229| acl2::|Aux230| acl2::|Aux231|
;;                                                                         acl2::|Aux232| acl2::|Aux233| acl2::|Aux234| acl2::|Aux235|
;;                                                                         acl2::|Aux236| acl2::|Aux237| acl2::|Aux238| acl2::|Aux239|
;;                                                                         acl2::|Aux240| acl2::|Aux241| acl2::|Aux242| acl2::|Aux243|
;;                                                                         acl2::|Aux244| acl2::|Aux245| acl2::|Aux246| acl2::|Aux247|
;;                                                                         acl2::|Aux248| acl2::|Aux249| acl2::|Aux250| acl2::|Aux251|
;;                                                                         acl2::|Aux252| acl2::|Aux253| acl2::|Aux254| acl2::|Aux255|
;;                                                                         acl2::|Aux256| acl2::|Aux257| acl2::|Aux258| acl2::|Aux259|
;;                                                                         acl2::|Aux260| acl2::|Aux261| acl2::|Aux262| acl2::|Aux263|
;;                                                                         acl2::|Aux264| acl2::|Aux265| acl2::|Aux266| acl2::|Aux267|
;;                                                                         acl2::|Aux268| acl2::|Aux269| acl2::|Aux270| acl2::|Aux271|
;;                                                                         acl2::|Aux272| acl2::|Aux273| acl2::|Aux274| acl2::|Aux275|
;;                                                                         acl2::|Aux276| acl2::|Aux277| acl2::|Aux278| acl2::|Aux279|
;;                                                                         acl2::|Aux280| acl2::|Aux281| acl2::|Aux282| acl2::|Aux283|
;;                                                                         acl2::|Aux284| acl2::|Aux285| acl2::|Aux286| acl2::|Aux287|
;;                                                                         acl2::|Aux288| acl2::|Aux289| acl2::|Aux290| acl2::|Aux291|
;;                                                                         acl2::|Aux292| acl2::|Aux293| acl2::|Aux294| acl2::|Aux295|
;;                                                                         acl2::|Aux296| acl2::|Aux297| acl2::|Aux298| acl2::|Aux299|
;;                                                                         acl2::|Aux300| acl2::|Aux301| acl2::|Aux302| acl2::|Aux303|
;;                                                                         acl2::|Aux304| acl2::|Aux305| acl2::|Aux306| acl2::|Aux307|
;;                                                                         acl2::|Aux308| acl2::|Aux309| acl2::|Aux310| acl2::|Aux311|
;;                                                                         acl2::|Aux312| acl2::|Aux313| acl2::|Aux314| acl2::|Aux315|
;;                                                                         acl2::|Aux316| acl2::|Aux317| acl2::|Aux318| acl2::|Aux319|
;;                                                                         acl2::|Aux320| acl2::|Aux321| acl2::|Aux322| acl2::|Aux323|
;;                                                                         acl2::|Aux324| acl2::|Aux325| acl2::|Aux326| acl2::|Aux327|
;;                                                                         acl2::|Aux328| acl2::|Aux329| acl2::|Aux330| acl2::|Aux331|
;;                                                                         acl2::|Aux332| acl2::|Aux333| acl2::|Aux334| acl2::|Aux335|
;;                                                                         acl2::|Aux336| acl2::|Aux337| acl2::|Aux338| acl2::|Aux339|
;;                                                                         acl2::|Aux340| acl2::|Aux341| acl2::|Aux342| acl2::|Aux343|
;;                                                                         acl2::|Aux344| acl2::|Aux345| acl2::|Aux346| acl2::|Aux347|
;;                                                                         acl2::|Aux348| acl2::|Aux349| acl2::|Aux350| acl2::|Aux351|
;;                                                                         acl2::|Aux352| acl2::|Aux353| acl2::|Aux354| acl2::|Aux355|
;;                                                                         acl2::|Aux356| acl2::|Aux357| acl2::|Aux358| acl2::|Aux359|
;;                                                                         acl2::|Aux360| acl2::|Aux361| acl2::|Aux362| acl2::|Aux363|
;;                                                                         acl2::|Aux364| acl2::|Aux365| acl2::|Aux366| acl2::|Aux367|
;;                                                                         acl2::|Aux368| acl2::|Aux369| acl2::|Aux370| acl2::|Aux371|
;;                                                                         acl2::|Aux372| acl2::|Aux373| acl2::|Aux374| acl2::|Aux375|
;;                                                                         acl2::|Aux376| acl2::|Aux377| acl2::|Aux378| acl2::|Aux379|
;;                                                                         acl2::|Aux380| acl2::|Aux381| acl2::|Aux382| acl2::|Aux383|
;;                                                                         acl2::|Aux384| acl2::|Aux385| acl2::|Aux386| acl2::|Aux387|
;;                                                                         acl2::|Aux388| acl2::|Aux389| acl2::|Aux390| acl2::|Aux391|
;;                                                                         acl2::|Aux392| acl2::|Aux393| acl2::|Aux394| acl2::|Aux395|
;;                                                                         acl2::|Aux396| acl2::|Aux397| acl2::|Aux398| acl2::|Aux399|
;;                                                                         acl2::|Aux400| acl2::|Aux401| acl2::|Aux402| acl2::|Aux403|
;;                                                                         acl2::|Aux404| acl2::|Aux405| acl2::|Aux406| acl2::|Aux407|
;;                                                                         acl2::|Aux408| acl2::|Aux409| acl2::|Aux410| acl2::|Aux411|
;;                                                                         acl2::|Aux412| acl2::|Aux413| acl2::|Aux414| acl2::|Aux415|
;;                                                                         acl2::|Aux416| acl2::|Aux417| acl2::|Aux418| acl2::|Aux419|
;;                                                                         acl2::|Aux420| acl2::|Aux421| acl2::|Aux422| acl2::|Aux423|
;;                                                                         acl2::|Aux424| acl2::|Aux425| acl2::|Aux426| acl2::|Aux427|
;;                                                                         acl2::|Aux428| acl2::|Aux429| acl2::|Aux430| acl2::|Aux431|
;;                                                                         acl2::|Aux432| acl2::|Aux433| acl2::|Aux434| acl2::|Aux435|
;;                                                                         acl2::|Aux436| acl2::|Aux437| acl2::|Aux438| acl2::|Aux439|
;;                                                                         acl2::|Aux440| acl2::|Aux441| acl2::|Aux442| acl2::|Aux443|
;;                                                                         acl2::|Aux444| acl2::|Aux445| acl2::|Aux446| acl2::|Aux447|
;;                                                                         acl2::|Aux448| acl2::|Aux449| acl2::|Aux450| acl2::|Aux451|
;;                                                                         acl2::|Aux452| acl2::|Aux453| acl2::|Aux454| acl2::|Aux455|
;;                                                                         acl2::|Aux456| acl2::|Aux457| acl2::|Aux458| acl2::|Aux459|
;;                                                                         acl2::|Aux460| acl2::|Aux461| acl2::|Aux462| acl2::|Aux463|
;;                                                                         acl2::|Aux464| acl2::|Aux465| acl2::|Aux466| acl2::|Aux467|
;;                                                                         acl2::|Aux468| acl2::|Aux469| acl2::|Aux470| acl2::|Aux471|
;;                                                                         acl2::|Aux472| acl2::|Aux473| acl2::|Aux474| acl2::|Aux475|
;;                                                                         acl2::|Aux476| acl2::|Aux477| acl2::|Aux478| acl2::|Aux479|
;;                                                                         acl2::|Aux480| acl2::|Aux481| acl2::|Aux482| acl2::|Aux483|
;;                                                                         acl2::|Aux484| acl2::|Aux485| acl2::|Aux486| acl2::|Aux487|
;;                                                                         acl2::|Aux488| acl2::|Aux489| acl2::|Aux490| acl2::|Aux491|
;;                                                                         acl2::|Aux492| acl2::|Aux493| acl2::|Aux494| acl2::|Aux495|
;;                                                                         acl2::|Aux496| acl2::|Aux497| acl2::|Aux498| acl2::|Aux499|
;;                                                                         acl2::|Aux500| acl2::|Aux501| acl2::|Aux502| acl2::|Aux503|
;;                                                                         acl2::|Aux504| acl2::|Aux505| acl2::|Aux506| acl2::|Aux507|
;;                                                                         acl2::|Aux508| acl2::|Aux509| acl2::|Aux510| acl2::|Aux511|)
;;                                                   (acl2::bits-to-bytes-little (list acl2::|Aux2352| acl2::|Aux2353| acl2::|Aux2354| acl2::|Aux2355|
;;                                                                                     acl2::|Aux2356| acl2::|Aux2357| acl2::|Aux2358| acl2::|Aux2359|
;;                                                                                     acl2::|Aux2360| acl2::|Aux2361| acl2::|Aux2362| acl2::|Aux2363|
;;                                                                                     acl2::|Aux2364| acl2::|Aux2365| acl2::|Aux2366| acl2::|Aux2367|
;;                                                                                     acl2::|Aux2368| acl2::|Aux2369| acl2::|Aux2370| acl2::|Aux2371|
;;                                                                                     acl2::|Aux2372| acl2::|Aux2373| acl2::|Aux2374| acl2::|Aux2375|
;;                                                                                     acl2::|Aux2376| acl2::|Aux2377| acl2::|Aux2378| acl2::|Aux2379|
;;                                                                                     acl2::|Aux2380| acl2::|Aux2381| acl2::|Aux2382| acl2::|Aux2383|
;;                                                                                     acl2::|Aux2384| acl2::|Aux2385| acl2::|Aux2386| acl2::|Aux2387|
;;                                                                                     acl2::|Aux2388| acl2::|Aux2389| acl2::|Aux2390| acl2::|Aux2391|
;;                                                                                     acl2::|Aux2392| acl2::|Aux2393| acl2::|Aux2394| acl2::|Aux2395|
;;                                                                                     acl2::|Aux2396| acl2::|Aux2397| acl2::|Aux2398| acl2::|Aux2399|
;;                                                                                     acl2::|Aux2400| acl2::|Aux2401| acl2::|Aux2402| acl2::|Aux2403|
;;                                                                                     acl2::|Aux2404| acl2::|Aux2405| acl2::|Aux2406| acl2::|Aux2407|
;;                                                                                     acl2::|Aux2408| acl2::|Aux2409| acl2::|Aux2410| acl2::|Aux2411|
;;                                                                                     acl2::|Aux2412| acl2::|Aux2413| acl2::|Aux2414| acl2::|Aux2415|
;;                                                                                     acl2::|Aux2416| acl2::|Aux2417| acl2::|Aux2418| acl2::|Aux2419|
;;                                                                                     acl2::|Aux2420| acl2::|Aux2421| acl2::|Aux2422| acl2::|Aux2423|
;;                                                                                     acl2::|Aux2424| acl2::|Aux2425| acl2::|Aux2426| acl2::|Aux2427|
;;                                                                                     acl2::|Aux2428| acl2::|Aux2429| acl2::|Aux2430| acl2::|Aux2431|
;;                                                                                     acl2::|Aux2432| acl2::|Aux2433| acl2::|Aux2434| acl2::|Aux2435|
;;                                                                                     acl2::|Aux2436| acl2::|Aux2437| acl2::|Aux2438| acl2::|Aux2439|
;;                                                                                     acl2::|Aux2440| acl2::|Aux2441| acl2::|Aux2442| acl2::|Aux2443|
;;                                                                                     acl2::|Aux2444| acl2::|Aux2445| acl2::|Aux2446| acl2::|Aux2447|
;;                                                                                     acl2::|Aux2448| acl2::|Aux2449| acl2::|Aux2450| acl2::|Aux2451|
;;                                                                                     acl2::|Aux2452| acl2::|Aux2453| acl2::|Aux2454| acl2::|Aux2455|
;;                                                                                     acl2::|Aux2456| acl2::|Aux2457| acl2::|Aux2458| acl2::|Aux2459|
;;                                                                                     acl2::|Aux2460| acl2::|Aux2461| acl2::|Aux2462| acl2::|Aux2463|
;;                                                                                     acl2::|Aux2464| acl2::|Aux2465| acl2::|Aux2466| acl2::|Aux2467|
;;                                                                                     acl2::|Aux2468| acl2::|Aux2469| acl2::|Aux2470| acl2::|Aux2471|
;;                                                                                     acl2::|Aux2472| acl2::|Aux2473| acl2::|Aux2474| acl2::|Aux2475|
;;                                                                                     acl2::|Aux2476| acl2::|Aux2477| acl2::|Aux2478| acl2::|Aux2479|
;;                                                                                     acl2::|Aux2480| acl2::|Aux2481| acl2::|Aux2482| acl2::|Aux2483|
;;                                                                                     acl2::|Aux2484| acl2::|Aux2485| acl2::|Aux2486| acl2::|Aux2487|
;;                                                                                     acl2::|Aux2488| acl2::|Aux2489| acl2::|Aux2490| acl2::|Aux2491|
;;                                                                                     acl2::|Aux2492| acl2::|Aux2493| acl2::|Aux2494| acl2::|Aux2495|
;;                                                                                     acl2::|Aux2496| acl2::|Aux2497| acl2::|Aux2498| acl2::|Aux2499|
;;                                                                                     acl2::|Aux2500| acl2::|Aux2501| acl2::|Aux2502| acl2::|Aux2503|
;;                                                                                     acl2::|Aux2504| acl2::|Aux2505| acl2::|Aux2506| acl2::|Aux2507|
;;                                                                                     acl2::|Aux2508| acl2::|Aux2509| acl2::|Aux2510| acl2::|Aux2511|
;;                                                                                     acl2::|Aux2512| acl2::|Aux2513| acl2::|Aux2514| acl2::|Aux2515|
;;                                                                                     acl2::|Aux2516| acl2::|Aux2517| acl2::|Aux2518| acl2::|Aux2519|
;;                                                                                     acl2::|Aux2520| acl2::|Aux2521| acl2::|Aux2522| acl2::|Aux2523|
;;                                                                                     acl2::|Aux2524| acl2::|Aux2525| acl2::|Aux2526| acl2::|Aux2527|
;;                                                                                     acl2::|Aux2528| acl2::|Aux2529| acl2::|Aux2530| acl2::|Aux2531|
;;                                                                                     acl2::|Aux2532| acl2::|Aux2533| acl2::|Aux2534| acl2::|Aux2535|
;;                                                                                     acl2::|Aux2536| acl2::|Aux2537| acl2::|Aux2538| acl2::|Aux2539|
;;                                                                                     acl2::|Aux2540| acl2::|Aux2541| acl2::|Aux2542| acl2::|Aux2543|
;;                                                                                     acl2::|Aux2544| acl2::|Aux2545| acl2::|Aux2546| acl2::|Aux2547|
;;                                                                                     acl2::|Aux2548| acl2::|Aux2549| acl2::|Aux2550| acl2::|Aux2551|
;;                                                                                     acl2::|Aux2552| acl2::|Aux2553| acl2::|Aux2554| acl2::|Aux2555|
;;                                                                                     acl2::|Aux2556| acl2::|Aux2557| acl2::|Aux2558| acl2::|Aux2559|
;;                                                                                     acl2::|Aux2560| acl2::|Aux2561| acl2::|Aux2562| acl2::|Aux2563|
;;                                                                                     acl2::|Aux2564| acl2::|Aux2565| acl2::|Aux2566| acl2::|Aux2567|
;;                                                                                     acl2::|Aux2568| acl2::|Aux2569| acl2::|Aux2570| acl2::|Aux2571|
;;                                                                                     acl2::|Aux2572| acl2::|Aux2573| acl2::|Aux2574| acl2::|Aux2575|
;;                                                                                     acl2::|Aux2576| acl2::|Aux2577| acl2::|Aux2578| acl2::|Aux2579|
;;                                                                                     acl2::|Aux2580| acl2::|Aux2581| acl2::|Aux2582| acl2::|Aux2583|
;;                                                                                     acl2::|Aux2584| acl2::|Aux2585| acl2::|Aux2586| acl2::|Aux2587|
;;                                                                                     acl2::|Aux2588| acl2::|Aux2589| acl2::|Aux2590| acl2::|Aux2591|
;;                                                                                     acl2::|Aux2592| acl2::|Aux2593| acl2::|Aux2594| acl2::|Aux2595|
;;                                                                                     acl2::|Aux2596| acl2::|Aux2597| acl2::|Aux2598| acl2::|Aux2599|
;;                                                                                     acl2::|Aux2600| acl2::|Aux2601| acl2::|Aux2602| acl2::|Aux2603|
;;                                                                                     acl2::|Aux2604| acl2::|Aux2605| acl2::|Aux2606| acl2::|Aux2607|)))
;;                                           ;'(blake2s1round acl2::|Aux2607 '99)
;;                                           :monitor '(;;add-of-neg-of-mul-of-power-of-2-other
;;                                                      ;;add-of-mul-of-power-of-2-other
;;                                                      ;;equal-of-0-and-add-of-add-of-add-of-neg-lemma
;;                                                      ;;acl2::getbit-of-0-when-bitp
;;                                                      ;;acl2::bitp-when-bit-listp-and-memberp
;;                                                      ;;add-becomes-bvplus
;;                                                      ;;equal-of-0-and-add-of-neg

;;                                                      )
;;                                           ;; todo: the tool should build the alist:
;;                                           ;; todo: better to use a custom instantiate-hyp function:
;;                                           :interpreted-function-alist (acl2::make-interpreted-function-alist '(neg pfield::add pfield::pos-fix ACL2::BVCAT acl2::logapp ash ACL2::EXPT2$INLINE ACL2::LOGHEAD$INLINE ACL2::IMOD$INLINE INTEGER-RANGE-P ACL2::POWER-OF-2P fep unsigned-byte-p acl2::getbit acl2::slice ACL2::LOGTAIL$INLINE ACL2::IFLOOR$INLINE acl2::bitnot)
;;                                                                                                              (w state))
;;                                           :rule-lists '( ;; first, introduce bvcats and lift negs.  keep the spec closed to keep the dag small for now.
;;                                                         ( ;acl2::mimcsponge-1-1-0k-holdsp
;;                                                          (acl2::lookup-rules)
;;                                                          (acl2::booleanp-rules)
;;                                                          (acl2::unsigned-byte-p-rules)
;;                                                          acl2::implies-opener
;;                                                          ;;bvcat-intro-4-2-simple
;;                                                          ;;bvcat-intro-4-2
;;                                                          pfield::add-of-mod-arg1
;;                                                          pfield::add-of-mod-arg2
;;                                                          pfield::mul-of-mod-arg1
;;                                                          pfield::mul-of-mod-arg1
;;                                                          acl2::integerp-of-bvcat
;;                                                          acl2::integerp-of-bitxor
;;                                                          acl2::integerp-of-bvnot
;;                                                          pfield::integerp-of-add
;;                                                          pfield::integerp-of-mul
;;                                                          pfield::integerp-of-neg
;;                                                          add-of-bvcat-of-add-of-mul-combine ; gen the bvcat?  or consider associating the other way?
;;                                                          add-of-bvcat-of-add-of-mul-combine-simp-alt ;instead of having simp on this name, use -extra on the other
;;                                                          add-of-bvcat-of-add-of-mul-combine-simp ;instead of having simp on this name, use -extra on the other
;;                                                          mul-of---arg1
;;                                                          pfield::mul-when-constant-becomes-neg-of-mul
;;                                                          ;;pfield::neg-when-constant-arg1
;;                                                          ;;move-negation-1
;;                                                          add-of-mul-of-2-becomes-bvcat
;;                                                          add-of-add-of-mul-of-2-becomes-add-of-bvcat
;;                                                          ;; pfield::add-of-neg-and-neg ; may cause problems?
;;                                                          pfield::neg-of-mod
;;                                                          ;; bitxor-constraint-intro
;;                                                          ;; bitxor-constraint-intro-alt
;;                                                          ;; these have the right form:
;;                                                          bitxor-constraint-intro
;;                                                          bitxor-constraint-intro-alt
;;                                                          bitxor-constraint-intro-b
;;                                                          bitxor-constraint-intro-b-alt
;;                                                          bitxor-constraint-intro-2
;;                                                          bitxor-constraint-intro-2-alt
;;                                                          bitxor-constraint-intro-2b
;;                                                          bitxor-constraint-intro-2b-alt
;;                                                          pfield::fep-of-mod ;todo: more fep rules?
;;                                                          pfield::fep-of-bitxor
;;                                                          primes::primep-of-bls12-377-scalar-field-prime-constant ;use more?
;;                                                          pfield::fep-when-fe-listp-and-memberp
;;                                                          acl2::memberp-of-append-with-key-first-half-axe
;;                                                          acl2::memberp-of-append-with-key-second-half-axe
;;                                                          ACL2::MEMBERP-OF-CONS ;todo: make a faster version for axe
;;                                                          not-of-if-of-nil-arg3-when-booleans
;;                                                          acl2::booleanp-of-booland
;;                                                          pfield::booleanp-of-fe-listp
;;                                                          acl2::equal-same
;;                                                          mod-of-ifix-when-fep
;;                                                          ACL2::BOOLOR-OF-NIL-ARG2
;;                                                          ACL2::BOOL-FIX-WHEN-BOOLEANP
;;                                                          BITP-OF-BITXOR
;;                                                          bitp-when-equal-1
;;                                                          bitp-when-equal-2
;;                                                          ;; rules to deal with XORing with a constant (expressed in bit-blasted form with some negative coefficients)
;;                                                          ;add-of-add-of-neg-of-mul-of-2
;;                                                          ;;add-of-bvxor-of-add-of-of-mul-of-constant
;;                                                          ;;add-of-bvxor-of-add-of-neg-of-mul-of-constant
;;                                                          ;; These put in bvcats, sometimes with bitnots:
;;                                                          r1cs::add-of-mul-of-power-of-2-other ; introduce bvcat
;;                                                          r1cs::add-of-neg-of-mul-of-power-of-2-other ; introduce bvcat of bitnot
;;                                                          r1cs::add-of-bvcat-1-of-0-and-add-of-bvcat-1-of-0-extra ; combine the bvcats
;;                                                          ;; these are for when one argument fits into the zeroes of the other:
;;                                                          r1cs::add-of-add-of-bvcat-of-0-when-unsigned-byte-p
;;                                                          r1cs::add-of-add-of-bvcat-of-0-when-unsigned-byte-p-special ; for lowsize=1
;;                                                          r1cs::add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra
;;                                                          r1cs::add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special ; for lowsize=1
;;                                                          r1cs::add-of-add-of-bvcat-of-0-when-unsigned-byte-p-alt
;;                                                          r1cs::add-of-add-of-bvcat-of-0-when-unsigned-byte-p-special-alt
;;                                                          r1cs::add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-alt
;;                                                          r1cs::add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special-alt
;;                                                          add-commute-constant
;;                                                          acl2::bvcat-associative-helper ;; not the usual rule, since we want to expose the low zeros
;;                                                          acl2::bvcat-combine-constants-old ;; not the usual rule
;;                                                          pfield::add-of-add-combine-constants
;;                                                          add-of-neg-of-when-bitp
;;                                                          pfield::add-of-0-arg1
;;                                                          acl2::bitp-when-bit-listp-and-memberp ;; maybe drop
;;                                                          acl2::if-of-nil-becomes-booland
;;                                                          neg-of-mul-of-power-of-2 ;for when we are not lifting negs above adds
;;                                                          pfield::add-associative-when-constant ; at least move constants forward, so they can be combined
;;                                                          add-of-bvcat-and-add-of-bvcat-combine-interloper-gen
;;                                                          acl2::bvcat-of-bvnot-and-bvnot
;;                                                          acl2::bvcat-of-bitnot-and-bvnot
;;                                                          acl2::bvcat-of-bvnot-and-bitnot
;;                                                          acl2::bvcat-of-bitnot-and-bitnot
;;                                                          pfield::add-of-bvnot-becomes-add-of-neg
;;                                                          PFIELD::FEP-OF-ADD
;;                                                          pfield::fep-of-bvcat
;;                                                          PFIELD::FEP-OF-BVChop)
;;                                                         ;; Next, move the negs
;;                                                         (equal-of-0-and-add-of-add-of-add-of-neg-lemma
;;                                                          equal-of-0-and-add-of-add-of-neg-lemma
;;                                                          equal-of-0-and-add-of-neg-arg1
;;                                                          (pfield::prime-field-proof-rules)
;;                                                          PFIELD::EQUAL-OF-ADD-OF-ADD-OF-NEG-ARG2-ARG2
;;                                                          ACL2::IFIX-WHEN-INTEGERP
;;                                                          PFIELD::INTEGERP-OF-ADD
;;                                                          PFIELD::NEG-OF-0
;;                                                          PFIELD::MOD-OF-ADD
;;                                                          ;;IF-OF-T-AND-NIL-WHEN-BOOLEANP
;;                                                          (ACL2::BOOLEANP-RULES)
;;                                                          ACL2::INTEGERP-OF-BVCAT
;;                                                          ACL2::MOD-WHEN-<
;;                                                          ACL2::BVCAT-NUMERIC-BOUND
;;                                                          ;not-<-of-bvcat-and-0
;;                                                          ACL2::RATIONALP-WHEN-INTEGERP
;;                                                          PFIELD::EQUAL-OF-0-AND-ADD-OF-NEG-arg2
;;                                                          pfield::fep-of-bvcat
;;                                                          PFIELD::FEP-OF-BVCHOP)
;;                                                         ;; ;; now, deal with the additions
;;                                                         ;; (acl2::adding-8-idiom
;;                                                         ;;  acl2::adding-8-idiom-alt
;;                                                         ;;  acl2::bitp-of-getbit
;;                                                         ;;  (acl2::unsigned-byte-p-rules)
;;                                                         ;; Now blast the equated bvcats, since the prover only substitutes for variables:
;;                                                         (acl2::bvcat-equal-rewrite
;;                                                          acl2::bvcat-equal-rewrite-alt
;;                                                          acl2::bvchop-of-bvcat-cases
;;                                                          (acl2::unsigned-byte-p-rules)
;;                                                          acl2::if-of-nil-becomes-booland ;shouldn't be needed to avoid splits?
;;                                                          (acl2::booleanp-rules)
;;                                                          acl2::bitp-of-getbit
;;                                                          acl2::bitp-of-bvchop-of-1
;;                                                          bvchop-of-1-when-bitp
;;                                                          acl2::slice-becomes-getbit
;;                                                          acl2::bvchop-1-becomes-getbit
;;                                                          acl2::bvcat-of-getbit-and-getbit-adjacent
;;                                                          acl2::bvcat-of-slice-and-slice-adjacent
;;                                                          acl2::bvcat-of-getbit-and-slice-adjacent
;;                                                          acl2::bvcat-of-slice-and-getbit-adjacent
;;                                                          acl2::getbit-of-bvchop
;;                                                          acl2::getbit-of-slice-gen
;;                                                          acl2::getbit-of-slice
;;                                                          ACL2::SLICE-OF-SLICE
;;                                                          acl2::getbit-of-0-when-bitp
;;                                                          acl2::bitp-when-bit-listp-and-memberp ; since the bitp hyps ot rewritten to T above using the bit-listp hyp
;;                                                          acl2::memberp-of-append-with-key-first-half-axe
;;                                                          acl2::memberp-of-append-with-key-second-half-axe
;;                                                          ACL2::MEMBERP-OF-CONS ;todo: make a faster version for axe
;;                                                          acl2::equal-same
;;                                                          PFIELD::FEP-OF-MUL
;;                                                          unsigned-byte-p-of-add)

;;                                                         ;; Now replace field operations with BV operations:
;;                                                         (add-becomes-bvplus-33 ;tried first
;;                                                          add-becomes-bvplus-34
;;                                                          getbit-of-bvplus-tighten-to-32
;;                                                          slice-of-bvplus-tighten-to-32
;;                                                          bvchop-of-bvplus-tighten-to-32
;;                                                          getbit-of-add-becomes-getbit-of-bvplus-32
;;                                                          bvplus-of-bvplus-trim-to-32-arg1
;;                                                          bvplus-of-bvplus-trim-to-32-arg2
;;                                                          acl2::slice-becomes-bvchop
;;                                                          acl2::bvchop-of-bvplus-same
;;                                                          (acl2::unsigned-byte-p-rules)
;;                                                          bvcat-of-slice-tighten
;;                                                          ;;ACL2::BVCAT-TRIM-ARG1-DAG-ALL
;;                                                          ;;ACL2::BVCAT-TRIM-ARG2-DAG-ALL
;;                                                          ;;(acl2::trim-rules)
;;                                                          ;;(acl2::trim-helper-rules)
;;                                                          bvcat-of-bvxor-low-when-quotep
;;                                                          bvcat-of-bvxor-high-when-quotep
;;                                                          bvcat-of-bitxor-low-when-quotep
;;                                                          bvcat-of-bitxor-high-when-quotep
;;                                                          bvcat-of-bitnot-low
;;                                                          bvcat-of-bvnot-low
;;                                                          bvcat-of-bitnot-high
;;                                                          BVCAT-OF-BVNOT-HIGH
;;                                                          ACL2::BVCAT-OF-GETBIT-AND-GETBIT-ADJACENT
;;                                                          ACL2::BVCAT-OF-SLICE-AND-SLICE-ADJACENT
;;                                                          ACL2::BVCAT-OF-GETBIT-AND-SLICE-ADJACENT
;;                                                          ACL2::BVCAT-OF-SLICE-AND-GETBIT-ADJACENT
;;                                                          ACL2::SLICE-BECOMES-BVCHOP
;;                                                          ACL2::BVCHOP-OF-BVPLUS-SAME
;;                                                          ACL2::BVCAT-OF-BVCHOP-LOW
;;                                                          ACL2::BVCAT-OF-BVCHOP-high
;;                                                          ACL2::BVCAT-OF-GETBIT-AND-X-ADJACENT-2
;;                                                          ACL2::BVCAT-OF-GETBIT-AND-X-ADJACENT
;;                                                          ACL2::BVCAT-OF-SLICE-AND-X-ADJACENT-2
;;                                                          ACL2::BVCAT-OF-SLICE-AND-X-ADJACENT
;;                                                          acl2::equal-same
;;                                                          ACL2::BVXOR-COMBINE-CONSTANTS)
;;                                                         ;re-assocate the bvs:
;;                                                         (acl2::bvcat-associative ; also re-associate bvcats back to the normal form
;;                                                          ACL2::BVCAT-OF-GETBIT-AND-GETBIT-ADJACENT
;;                                                          ACL2::BVCAT-OF-SLICE-AND-SLICE-ADJACENT
;;                                                          ACL2::BVCAT-OF-GETBIT-AND-SLICE-ADJACENT
;;                                                          ACL2::BVCAT-OF-SLICE-AND-GETBIT-ADJACENT
;;                                                          ACL2::SLICE-BECOMES-BVCHOP
;;                                                          ACL2::BVCHOP-OF-BVPLUS-SAME
;;                                                          ACL2::BVCAT-OF-BVCHOP-LOW
;;                                                          ACL2::BVCAT-OF-BVCHOP-high
;;                                                          ACL2::BVCAT-OF-GETBIT-AND-X-ADJACENT-2
;;                                                          ACL2::BVCAT-OF-GETBIT-AND-X-ADJACENT
;;                                                          ACL2::BVCAT-OF-SLICE-AND-X-ADJACENT-2
;;                                                          ACL2::BVCAT-OF-SLICE-AND-X-ADJACENT
;;                                                          bvcat-of-slice-same-becomes-rightrotate
;;                                                          bvcat-of-bitxor-and-bitxor-adjacent-bits
;;                                                          bvcat-of-bitxor-and-bvxor-adjacent-bits-alt
;;                                                          bvcat-of-bitxor-and-bvxor-adjacent-bits
;;                                                          bvcat-of-bitxor-and-bvxor-adjacent-bits-alt
;;                                                          bvcat-of-bvxor-and-bvxor-adjacent-bits
;;                                                          bvcat-of-bvxor-and-bvxor-adjacent-bits-alt
;;                                                          ACL2::BVPLUS-COMMUTE-CONSTANT
;;                                                          ACL2::BVPLUS-ASSOCIATIVE
;;                                                          )
;;                                                         ;; now open the spec:
;;                                                         (;BLAKE2S1ROUND-NO-KEY
;;                                                          ACL2::BITS-TO-BYTES-little-BASE
;;                                                          ACL2::BITS-TO-BYTES-little-UNROLL
;;                                                          ACL2::BITS-TO-BYTE-little
;;                                                          (acl2::list-rules)
;;                                                          ACL2::TRUE-LIST-FIX-OF-CONS ;add to list-rules?
;;                                                          ACL2::CONSP-OF-NTHCDR
;;                                                          acl2::len-of-nthcdr
;;                                                          acl2::nthcdr-of-nthcdr
;;                                                          (acl2::base-rules)
;;                                                          BLAKE::BLAKE2S
;;                                                          BLAKE::D-BLOCKS
;;                                                          BLAKE::PAD-DATA-BYTES
;;                                                          BLAKE::BYTES-TO-BLOCKS-BASE-2
;;                                                          BLAKE::BYTES-TO-BLOCKS-UNROLL
;;                                                          ACL2::CONSP-WHEN-LEN-EQUAL
;;                                                          ACL2::CONSP-WHEN-LEN-EQUAL-alt
;;                                                          ;;endp
;;                                                          BLAKE::BYTES-TO-BLOCK
;;                                                          BLAKE::BYTES-TO-WORDS-BASE
;;                                                          BLAKE::BYTES-TO-WORDS-UNROLL
;;                                                          ;; ACL2::NTHCDR-WHEN-EQUAL-OF-LEN
;;                                                          BLAKE::BYTES-TO-WORD
;;                                                          BLAKE::BLAKE2S-MAIN
;;                                                          BLAKE::F
;;                                                          BLAKE::LOOP1-BASE
;;                                                          BLAKE::LOOP1-UNROLL
;;                                                          BLAKE::LOOP2-BASE
;;                                                          BLAKE::LOOP2-UNROLL
;;                                                          BLAKE::LOOP3-BASE
;;                                                          BLAKE::LOOP3-UNROLL
;;                                                          BLAKE::WORDXOR
;;                                                          blake::g
;;                                                          BLAKE::ROT-WORD
;;                                                          ACL2::NTH-OF-NTHCDR
;;                                                          BLAKE::LEN-OF-BYTES-TO-BLOCKS
;;                                                          blake::sigma
;;                                                          BLAKE::IV
;;                                                          BLAKE::WORDS-TO-BYTES-BASE
;;                                                          BLAKE::WORDS-TO-BYTES-UNROLL
;;                                                          BLAKE::WORD-TO-BYTES
;;                                                          acl2::mod-of-+-of-4294967296
;;                                                          ACL2::BVPLUS-OF-+-ARG2
;;                                                          ACL2::BVPLUS-OF-+-ARG3
;;                                                          ACL2::UPDATE-NTH-OF-UPDATE-NTH-SAME
;;                                                          ACL2::CDR-OF-UPDATE-NTH
;;                                                          ACL2::CAR-OF-UPDATE-NTH
;;                                                          ACL2::BVSHL-OF-0-ARG2
;;                                                          ACL2::BVSHR-CONSTANT-OPENER
;;                                                          ACL2::slice-CONSTANT-OPENER
;;                                                          ACL2::LOGTAIL$INLINE-CONSTANT-OPENER
;;                                                          ACL2::EXPT2$INLINE
;;                                                          ACL2::ifloor$INLINE
;;                                                          ACL2::BVPLUS-COMBINE-CONSTANTS
;;                                                          (acl2::type-rules)
;;                                                          BLAKE::BVPLUS-INTRO
;;                                                          ACL2::EQUAL-OF-CONS-AND-CONS ;rewrites the top equality
;;                                                          ACL2::BVXOR-BLAST ; to match the r1cs (todo: instead, try to lift the r1cs more)
;;                                                          ACL2::SLICE-OF-BVCAT-GEN
;;                                                          ACL2::GETBIT-OF-BVCAT-ALL
;;                                                          ACL2::BVXOR-1-BECOMES-BITXOR
;;                                                          ACL2::BITXOR-OF-1-BECOMES-BITNOT-ARG1
;;                                                          ACL2::BITXOR-OF-1-BECOMES-BITNOT-ARG2
;;                                                          ACL2::GETBIT-OF-BITXOR-ALL-CASES
;;                                                          ACL2::BVCHOP-IDENTITY-AXE ; didn't always work?
;;                                                          ACL2::BVCHOP-IDENTITY
;;                                                          ACL2::SLICE-BECOMES-GETBIT
;;                                                          ACL2::BITXOR-OF-0-ARG1
;;                                                          ACL2::BITXOR-OF-0-ARG2
;;                                                          (acl2::unsigned-byte-p-rules)
;;                                                          ACL2::GETBIT-IDENTITY
;;                                                          ACL2::GETBIT-IDENTITY-AXE ; why didn't this always work?

;;                                                          ;;could be bad:
;;                                                          ACL2::BVPLUS-ASSOCIATIVE
;;                                                          acl2::bvplus-commutative-2-increasing-axe ;ACL2::BVPLUS-COMMUTATIVE-2-AXE
;;                                                          acl2::bvplus-commutative-increasing-axe ;ACL2::BVPLUS-COMMUTATIVE-AXE
;;                                                          ACL2::BITXOR-ASSOCIATIVE
;;                                                          ACL2::BITXOR-ASSOCIATIVE
;;                                                          ACL2::BITXOR-COMMUTATIVE-2-INCREASING-AXE
;;                                                          ACL2::BITXOR-COMMUTATIVE-INCREASING-AXE

;;                                                          ACL2::RIGHTROTATE-OPEN-WHEN-CONSTANT-SHIFT-AMOUNT
;;                                                          ACL2::BITXOR-OF-SLICE-ARG2
;;                                                          ACL2::BITXOR-OF-SLICE-ARG1
;;                                                          acl2::getbit-of-slice
;;                                                          ACL2::BITXOR-WHEN-CONSTANT-IS-NOT-USB-ARG1
;;                                                          ACL2::BITXOR-WHEN-CONSTANT-IS-NOT-USB-ARG2
;;                                                          ACL2::BITXOR-OF-BVCAT-IRREL-ARG1
;;                                                          ACL2::BITXOR-OF-BVCAT-IRREL-ARG2
;;                                                          acl2::bvcat-associative
;;                                                          ACL2::BITXOR-OF-BVCHOP-ARG1
;;                                                          ACL2::BITXOR-OF-BVCHOP-ARG2
;;                                                          acl2::getbit-of-bvchop
;;                                                          ACL2::BITXOR-OF-BITNOT-ARG1
;;                                                          ACL2::BITXOR-OF-BITNOT-ARG2

;;                                                          ;;for running tests:
;;                                                          ACL2::EQUAL-OF-CONS-when-quotep
;;                                                          ACL2::BVCAT-EQUAL-REWRITE-CONSTANT
;;                                                          ACL2::BVCHOP-of-1-when-bitp
;;                                                          acl2::bitp-when-bit-listp-and-memberp ;; maybe drop
;;                                                          acl2::memberp-of-append-with-key-first-half-axe
;;                                                          acl2::memberp-of-append-with-key-second-half-axe
;;                                                          ACL2::MEMBERP-OF-CONS ;todo: make a faster version for axe
;;                                                          acl2::equal-same
;;                                                          )

;;                                                         ;; (;blake-spec
;;                                                         ;;  ACL2::BVCAT-OF-GETBIT-AND-GETBIT-ADJACENT
;;                                                         ;;  ACL2::BVCAT-OF-SLICE-AND-SLICE-ADJACENT
;;                                                         ;;  ACL2::BVCAT-OF-GETBIT-AND-SLICE-ADJACENT
;;                                                         ;;  ACL2::BVCAT-OF-SLICE-AND-GETBIT-ADJACENT
;;                                                         ;;  ACL2::SLICE-BECOMES-BVCHOP
;;                                                         ;;  ACL2::BVCHOP-OF-BVPLUS-SAME
;;                                                         ;;  ACL2::BVCAT-OF-BVCHOP-LOW
;;                                                         ;;  ACL2::BVCAT-OF-BVCHOP-high
;;                                                         ;;  ACL2::BVCAT-OF-GETBIT-AND-X-ADJACENT-2
;;                                                         ;;  ACL2::BVCAT-OF-GETBIT-AND-X-ADJACENT
;;                                                         ;;  ACL2::BVCAT-OF-SLICE-AND-X-ADJACENT-2
;;                                                         ;;  ACL2::BVCAT-OF-SLICE-AND-X-ADJACENT
;;                                                         ;;  acl2::equal-same)
;;                                                         ))

;; could simplify ACL2::UNSIGNED-BYTE-P-OF-BVCAT-ALL-CASES

(acl2::prove-implication-with-r1cs-prover
 ;; Assumes that the r1cs holds and every var is a field element:
 (acl2::make-conjunction-dag! (acl2::make-term-into-dag-basic!
                               ;;todo: tool should translate this assumption?
                               (pfield::gen-fe-listp-assumption (acl2::dag-vars *blake-r1cs-lifted*)
                                                        ''8444461749428370424248824938781546531375899335154063827935233455917409239041)
                               nil)
                              *blake-r1cs-lifted*)
 ;; Shows that the outputs are correctly computed from the inputs:
 '(equal (blake2s1round-no-key |Aux0| |Aux1| |Aux2| |Aux3| |Aux4|
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
         (acl2::bits-to-bytes-little (list |Output0| |Output1| |Output2| |Output3| |Output4|
                                           |Output5| |Output6| |Output7| |Output8| |Output9|
                                           |Output10| |Output11| |Output12| |Output13| |Output14|
                                           |Output15| |Output16| |Output17| |Output18| |Output19|
                                           |Output20| |Output21| |Output22| |Output23| |Output24|
                                           |Output25| |Output26| |Output27| |Output28| |Output29|
                                           |Output30| |Output31| |Output32| |Output33| |Output34|
                                           |Output35| |Output36| |Output37| |Output38| |Output39|
                                           |Output40| |Output41| |Output42| |Output43| |Output44|
                                           |Output45| |Output46| |Output47| |Output48| |Output49|
                                           |Output50| |Output51| |Output52| |Output53| |Output54|
                                           |Output55| |Output56| |Output57| |Output58| |Output59|
                                           |Output60| |Output61| |Output62| |Output63| |Output64|
                                           |Output65| |Output66| |Output67| |Output68| |Output69|
                                           |Output70| |Output71| |Output72| |Output73| |Output74|
                                           |Output75| |Output76| |Output77| |Output78| |Output79|
                                           |Output80| |Output81| |Output82| |Output83| |Output84|
                                           |Output85| |Output86| |Output87| |Output88| |Output89|
                                           |Output90| |Output91| |Output92| |Output93| |Output94|
                                           |Output95| |Output96| |Output97| |Output98| |Output99|
                                           |Output100| |Output101| |Output102| |Output103|
                                           |Output104| |Output105| |Output106| |Output107|
                                           |Output108| |Output109| |Output110| |Output111|
                                           |Output112| |Output113| |Output114| |Output115|
                                           |Output116| |Output117| |Output118| |Output119|
                                           |Output120| |Output121| |Output122| |Output123|
                                           |Output124| |Output125| |Output126| |Output127|
                                           |Output128| |Output129| |Output130| |Output131|
                                           |Output132| |Output133| |Output134| |Output135|
                                           |Output136| |Output137| |Output138| |Output139|
                                           |Output140| |Output141| |Output142| |Output143|
                                           |Output144| |Output145| |Output146| |Output147|
                                           |Output148| |Output149| |Output150| |Output151|
                                           |Output152| |Output153| |Output154| |Output155|
                                           |Output156| |Output157| |Output158| |Output159|
                                           |Output160| |Output161| |Output162| |Output163|
                                           |Output164| |Output165| |Output166| |Output167|
                                           |Output168| |Output169| |Output170| |Output171|
                                           |Output172| |Output173| |Output174| |Output175|
                                           |Output176| |Output177| |Output178| |Output179|
                                           |Output180| |Output181| |Output182| |Output183|
                                           |Output184| |Output185| |Output186| |Output187|
                                           |Output188| |Output189| |Output190| |Output191|
                                           |Output192| |Output193| |Output194| |Output195|
                                           |Output196| |Output197| |Output198| |Output199|
                                           |Output200| |Output201| |Output202| |Output203|
                                           |Output204| |Output205| |Output206| |Output207|
                                           |Output208| |Output209| |Output210| |Output211|
                                           |Output212| |Output213| |Output214| |Output215|
                                           |Output216| |Output217| |Output218| |Output219|
                                           |Output220| |Output221| |Output222| |Output223|
                                           |Output224| |Output225| |Output226| |Output227|
                                           |Output228| |Output229| |Output230| |Output231|
                                           |Output232| |Output233| |Output234| |Output235|
                                           |Output236| |Output237| |Output238| |Output239|
                                           |Output240| |Output241| |Output242| |Output243|
                                           |Output244| |Output245| |Output246| |Output247|
                                           |Output248| |Output249| |Output250| |Output251|
                                           |Output252| |Output253| |Output254| |Output255|)))
 :NO-SPLITP t
 :monitor '()
 ;; todo: the tool should build the alist:
 ;; todo: better to use a custom instantiate-hyp function:
 ;; some of these may be needed only for ground proofs:
 :interpreted-function-alist (acl2::make-interpreted-function-alist '(neg pfield::add pfield::pos-fix ACL2::BVCAT acl2::logapp ash ACL2::EXPT2$INLINE ACL2::LOGHEAD$INLINE ACL2::IMOD$INLINE INTEGER-RANGE-P ACL2::POWER-OF-2P fep unsigned-byte-p acl2::getbit acl2::slice ACL2::LOGTAIL$INLINE ACL2::IFLOOR$INLINE acl2::bitnot sub acl2::bvnot lognot acl2::bitxor ACL2::POWER-OF-2P)
                                                                    (w state))
 :global-rules '(pfield::add-of-add-combine-constants
                 ;; booleanp rules:
                 (acl2::booleanp-rules)
                 pfield::booleanp-of-fe-listp
                acl2::integerp-of-bvcat
                acl2::integerp-of-bitxor
                acl2::integerp-of-bvxor
                acl2::integerp-of-bvnot
                pfield::integerp-of-add
                pfield::integerp-of-mul
                 pfield::integerp-of-neg
                 ;; new:
                 ;;ACL2::NOT-OF-BOOLAND
                 acl2::bvchop-of-bvcat-cases
                 )
 :rule-lists '( ;; first, introduce bvcats and lift negs.  keep the spec closed to keep the dag small for now.
               ( ;acl2::mimcsponge-1-1-0k-holdsp
                (acl2::lookup-rules)
                (acl2::booleanp-rules)
                (acl2::unsigned-byte-p-rules)
                acl2::implies-opener
                ;;bvcat-intro-4-2-simple
                ;;bvcat-intro-4-2
                pfield::add-of-mod-arg1 ;todo: might be faster to use the rule variants that do not introduce mod
                pfield::add-of-mod-arg2
                pfield::mul-of-mod-arg1
                pfield::mul-of-mod-arg1
                add-of-bvcat-of-add-of-mul-combine ; gen the bvcat?  or consider associating the other way?
                add-of-bvcat-of-add-of-mul-combine-simp-alt ;instead of having simp on this name, use -extra on the other
                add-of-bvcat-of-add-of-mul-combine-simp ;instead of having simp on this name, use -extra on the other
                mul-of---arg1
                pfield::mul-when-constant-becomes-neg-of-mul
                ;;pfield::neg-when-constant-arg1
                ;;move-negation-1
                add-of-mul-of-2-becomes-bvcat
                add-of-add-of-mul-of-2-becomes-add-of-bvcat
                ;; pfield::add-of-neg-and-neg ; may cause problems?
                pfield::neg-of-mod
                ;; bitxor-constraint-intro
                ;; bitxor-constraint-intro-alt
                ;; these have the right form:
                pfield::bitxor-constraint-intro
                pfield::bitxor-constraint-intro-alt
                pfield::bitxor-constraint-intro-b
                pfield::bitxor-constraint-intro-b-alt
                pfield::bitxor-constraint-intro-2
                pfield::bitxor-constraint-intro-2-alt
                pfield::bitxor-constraint-intro-2b
                pfield::bitxor-constraint-intro-2b-alt
                pfield::fep-of-mod ;todo: more fep rules?
                pfield::fep-of-bitxor
                primes::primep-of-bls12-377-scalar-field-prime-constant ;use more?
                pfield::fep-when-fe-listp-and-memberp
                acl2::memberp-of-append-with-key-first-half-axe
                acl2::memberp-of-append-with-key-second-half-axe
                ACL2::MEMBERP-OF-CONS ;todo: make a faster version for axe
                acl2::not-of-if-of-nil-arg3-when-booleans
                acl2::booleanp-of-booland
                pfield::booleanp-of-fe-listp
                acl2::equal-same
                pfield::mod-of-ifix-when-fep
                ACL2::BOOLOR-OF-NIL-ARG2
                ACL2::BOOL-FIX-WHEN-BOOLEANP
                acl2::BITP-OF-BITXOR
;bitp-when-equal-1 ;can loop (restrict to known forms?)
;bitp-when-equal-2 ;can loop (restrict to known forms?)
                ;; rules to deal with XORing with a constant (expressed in bit-blasted form with some negative coefficients)
;add-of-add-of-neg-of-mul-of-2
                ;;add-of-bvxor-of-add-of-of-mul-of-constant
                ;;add-of-bvxor-of-add-of-neg-of-mul-of-constant
                ;; These put in bvcats, sometimes with bitnots:
                pfield::add-of-mul-of-power-of-2-other ; introduce bvcat
                pfield::add-of-neg-of-mul-of-power-of-2-other ; introduce bvcat of bitnot
                pfield::add-of-bvcat-1-of-0-and-add-of-bvcat-1-of-0-extra ; combine the bvcats
                ;; these are for when one argument fits into the zeroes of the other:
                pfield::add-of-bvcat-of-0-when-unsigned-byte-p-arg1
                pfield::add-of-bvcat-of-0-when-unsigned-byte-p-arg2
                pfield::add-of-bvcat-of-0-when-unsigned-byte-p-arg1-bitp ; for lowsize=1
                pfield::add-of-bvcat-of-0-when-unsigned-byte-p-arg2-bitp ; for lowsize=1
                pfield::add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra
                pfield::add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special ; for lowsize=1
                pfield::add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-alt
                pfield::add-of-add-of-bvcat-of-0-when-unsigned-byte-p-with-extra-special-alt
                pfield::add-commutative-when-constant
                pfield::add-commutative-2-when-constant
                acl2::bvcat-associative-helper ;; not the usual rule, since we want to expose the low zeros
                acl2::bvcat-combine-constants-old ;; not the usual rule
                pfield::add-of-add-combine-constants
                pfield::add-of-neg-of-when-bitp
                pfield::add-of-0-arg1
                ;; acl2::bitp-when-bit-listp-and-memberp ;; maybe drop
                acl2::if-of-nil-becomes-booland
                pfield::neg-of-mul-of-power-of-2 ;for when we are not lifting negs above adds
                pfield::add-associative-when-constant ; at least move constants forward, so they can be combined
                pfield::add-of-bvcat-and-add-of-bvcat-combine-interloper-gen
                acl2::bvcat-of-bvnot-and-bvnot
                acl2::bvcat-of-bitnot-and-bvnot
                acl2::bvcat-of-bvnot-and-bitnot
                acl2::bvcat-of-bitnot-and-bitnot
                pfield::add-of-bvnot-becomes-add-of-neg
                PFIELD::FEP-OF-ADD
                pfield::fep-of-bvcat
                PFIELD::FEP-OF-BVChop
                ACL2::BITS-TO-BYTES-little-BASE
                ACL2::BITS-TO-BYTES-little-UNROLL
                ACL2::BITS-TO-BYTE-little
                (acl2::list-rules)
                ACL2::TRUE-LIST-FIX-OF-CONS ;add to list-rules?
                ACL2::CONSP-OF-NTHCDR
                acl2::len-of-nthcdr
                acl2::nthcdr-of-nthcdr
                (acl2::base-rules)
                ;; BLAKE::BLAKE2S
                ;; BLAKE::D-BLOCKS
                ;; BLAKE::PAD-DATA-BYTES
                ;; BLAKE::BYTES-TO-BLOCKS-BASE-2
                ;; BLAKE::BYTES-TO-BLOCKS-UNROLL
                ;; ACL2::CONSP-WHEN-LEN-EQUAL
                ;; ACL2::CONSP-WHEN-LEN-EQUAL-alt
                ;; ;;endp
                ;; BLAKE::BYTES-TO-BLOCK
                ;; BLAKE::BYTES-TO-WORDS-BASE
                ;; BLAKE::BYTES-TO-WORDS-UNROLL
                ;; ;; ACL2::NTHCDR-WHEN-EQUAL-OF-LEN
                ;; BLAKE::BYTES-TO-WORD
                ;; BLAKE::BLAKE2S-MAIN
                ;; BLAKE::F
                ;; BLAKE::LOOP1-BASE
                ;; BLAKE::LOOP1-UNROLL
                ;; BLAKE::LOOP2-BASE
                ;; BLAKE::LOOP2-UNROLL
                ;; BLAKE::LOOP3-BASE
                ;; BLAKE::LOOP3-UNROLL
                ;; BLAKE::WORDXOR
                ;; blake::g
                ;; BLAKE::ROT-WORD
                ;; ACL2::NTH-OF-NTHCDR
                ;; BLAKE::LEN-OF-BYTES-TO-BLOCKS
                ;; blake::sigma
                ;; BLAKE::IV
                ;; BLAKE::WORDS-TO-BYTES-BASE
                ;; BLAKE::WORDS-TO-BYTES-UNROLL
                ;; BLAKE::WORD-TO-BYTES
                ;; acl2::mod-of-+-of-4294967296
                ;; ACL2::BVPLUS-OF-+-ARG2
                ;; ACL2::BVPLUS-OF-+-ARG3
                ;; ACL2::UPDATE-NTH-OF-UPDATE-NTH-SAME
                ;; ACL2::CDR-OF-UPDATE-NTH
                ;; ACL2::CAR-OF-UPDATE-NTH
                ;; ACL2::BVSHL-OF-0-ARG2
                ;; ACL2::BVSHR-CONSTANT-OPENER
                ;; ACL2::slice-CONSTANT-OPENER
                ;; ACL2::LOGTAIL$INLINE-CONSTANT-OPENER
                ;; ACL2::EXPT2$INLINE
                ;; ACL2::ifloor$INLINE
                ;; ACL2::BVPLUS-COMBINE-CONSTANTS
                ;; (acl2::type-rules)
                ;; BLAKE::BVPLUS-INTRO
                ;; ACL2::EQUAL-OF-CONS-AND-CONS ;rewrites the top equality
                ;; ACL2::BVXOR-BLAST ; to match the r1cs (todo: instead, try to lift the r1cs more)
                ;; ACL2::SLICE-OF-BVCAT-GEN
                ;; ACL2::GETBIT-OF-BVCAT-ALL
                ;; ACL2::BVXOR-1-BECOMES-BITXOR
                ;; ACL2::BITXOR-OF-1-BECOMES-BITNOT-ARG1
                ;; ACL2::BITXOR-OF-1-BECOMES-BITNOT-ARG2
                ;; ACL2::GETBIT-OF-BITXOR-ALL-CASES
                ;; ACL2::BVCHOP-IDENTITY-AXE ; didn't always work?
                ;; ACL2::BVCHOP-IDENTITY
                ;; ACL2::SLICE-BECOMES-GETBIT
                ;; ACL2::BITXOR-OF-0-ARG1
                ;; ACL2::BITXOR-OF-0-ARG2
                ;; (acl2::unsigned-byte-p-rules)
                ;; ACL2::GETBIT-IDENTITY
                ;; ACL2::GETBIT-IDENTITY-AXE ; why didn't this always work?

                ;; ;;could be bad:
                ;; ACL2::BVPLUS-ASSOCIATIVE
                ;; acl2::bvplus-commutative-2-increasing-axe ;ACL2::BVPLUS-COMMUTATIVE-2-AXE
                ;; acl2::bvplus-commutative-increasing-axe ;ACL2::BVPLUS-COMMUTATIVE-AXE
                ;; ACL2::BITXOR-ASSOCIATIVE
                ;; ACL2::BITXOR-ASSOCIATIVE
                ;; ACL2::BITXOR-COMMUTATIVE-2-INCREASING-AXE
                ;; ACL2::BITXOR-COMMUTATIVE-INCREASING-AXE

                ;; ACL2::RIGHTROTATE-OPEN-WHEN-CONSTANT-SHIFT-AMOUNT
                ;; ACL2::BITXOR-OF-SLICE-ARG2
                ;; ACL2::BITXOR-OF-SLICE-ARG1
                ;; acl2::getbit-of-slice
                ;; ACL2::BITXOR-WHEN-CONSTANT-IS-NOT-USB-ARG1
                ;; ACL2::BITXOR-WHEN-CONSTANT-IS-NOT-USB-ARG2
                ;; ACL2::BITXOR-OF-BVCAT-IRREL-ARG1
                ;; ACL2::BITXOR-OF-BVCAT-IRREL-ARG2
                ;; acl2::bvcat-associative
                ;; ACL2::BITXOR-OF-BVCHOP-ARG1
                ;; ACL2::BITXOR-OF-BVCHOP-ARG2
                ;; acl2::getbit-of-bvchop
                ;; ACL2::BITXOR-OF-BITNOT-ARG1
                ;; ACL2::BITXOR-OF-BITNOT-ARG2

; todo: given the constant inputs, why are we not done at this point?
                ;;for running tests:
                ACL2::EQUAL-OF-CONS-when-quotep
                ACL2::BVCAT-EQUAL-REWRITE-CONSTANT
                ACL2::BVCHOP-of-1-when-bitp
                ;; acl2::bitp-when-bit-listp-and-memberp ;; maybe drop
                acl2::memberp-of-append-with-key-first-half-axe
                acl2::memberp-of-append-with-key-second-half-axe
                ACL2::MEMBERP-OF-CONS ;todo: make a faster version for axe
                acl2::equal-same
                ACL2::EQUAL-OF-CONS-AND-CONS ;rewrites the top equality
                pfield::EQUAL-OF-1-AND-ADD-WHEN-BITP-ARG1
                pfield::EQUAL-OF-1-AND-ADD-WHEN-BITP-ARG2
                PFIELD::EQUAL-OF-ADD-COMBINE-CONSTANTS
                )
               ;; Next, move the negs
               (pfield::equal-of-0-and-add-of-add-of-add-of-neg-lemma
                pfield::equal-of-0-and-add-of-add-of-add-of-neg-lemma-alt
                pfield::equal-of-0-and-add-of-add-of-neg-lemma
                pfield::equal-of-0-and-add-of-neg-arg1
                (pfield::prime-field-proof-rules)
                PFIELD::EQUAL-OF-ADD-OF-ADD-OF-NEG-ARG2-ARG2
                ACL2::IFIX-WHEN-INTEGERP
                PFIELD::NEG-OF-0
                PFIELD::MOD-OF-ADD
                ;;IF-OF-T-AND-NIL-WHEN-BOOLEANP
                (ACL2::BOOLEANP-RULES)
                ACL2::MOD-WHEN-<
                ACL2::BVCAT-NUMERIC-BOUND
;not-<-of-bvcat-and-0
                ACL2::RATIONALP-WHEN-INTEGERP
                PFIELD::EQUAL-OF-0-AND-ADD-OF-NEG-arg2
                pfield::fep-of-bvcat
                PFIELD::FEP-OF-BVCHOP
                pfield::equal-of-constant-and-add-of-neg-arg1
                pfield::equal-of-constant-and-add-of-neg-arg2)
               ;; ;; now, deal with the additions
               ;; (acl2::adding-8-idiom
               ;;  acl2::adding-8-idiom-alt
               ;;  acl2::bitp-of-getbit
               ;;  (acl2::unsigned-byte-p-rules)
               ;; Now blast the equated bvcats, since the prover only substitutes for variables:
               (acl2::bvcat-equal-rewrite
                acl2::bvcat-equal-rewrite-alt
                (acl2::unsigned-byte-p-rules)
                acl2::if-of-nil-becomes-booland ;shouldn't be needed to avoid splits?
                (acl2::booleanp-rules)
                acl2::bitp-of-getbit
                acl2::bitp-of-bvchop-of-1
                bvchop-of-1-when-bitp

                acl2::bvchop-1-becomes-getbit
                acl2::bvcat-of-getbit-and-getbit-adjacent
                acl2::bvcat-of-slice-and-slice-adjacent
                acl2::bvcat-of-getbit-and-slice-adjacent
                acl2::bvcat-of-slice-and-getbit-adjacent
                acl2::getbit-of-bvchop
                acl2::getbit-of-slice-gen
                acl2::getbit-of-slice
                ACL2::SLICE-OF-SLICE
                acl2::getbit-of-0-when-bitp
                ;; acl2::bitp-when-bit-listp-and-memberp ; since the bitp hyps ot rewritten to T above using the bit-listp hyp
                acl2::memberp-of-append-with-key-first-half-axe
                acl2::memberp-of-append-with-key-second-half-axe
                ACL2::MEMBERP-OF-CONS ;todo: make a faster version for axe
                acl2::equal-same
                PFIELD::FEP-OF-MUL
                pfield::unsigned-byte-p-of-add
                pfield::add-of-0-arg1 ;where do we want this?
                PFIELD::FEP-OF-NEG
                PFIELD::EQUAL-OF-NEG-SOLVE
                PFIELD::EQUAL-OF-NEG-SOLVE-alt
                pfield::fep-of-bvcat
                PFIELD::ADD-COMMUTATIVE-AXE
                PFIELD::EQUAL-OF-ADD-COMBINE-CONSTANTS
                pfield::equal-of-constant-and-add-of-neg-arg1
                pfield::equal-of-constant-and-add-of-neg-arg2
                )
               ;; now open the spec:
               (BLAKE2S1ROUND-NO-KEY
                (acl2::list-rules)
                ACL2::TRUE-LIST-FIX-OF-CONS
                ACL2::CONSP-OF-NTHCDR
                acl2::len-of-nthcdr
                acl2::nthcdr-of-nthcdr
                (acl2::base-rules)
                BLAKE::BLAKE2S
                BLAKE::D-BLOCKS
                BLAKE::PAD-DATA-BYTES
                BLAKE::BYTES-TO-BLOCKS-BASE-2
                BLAKE::BYTES-TO-BLOCKS-UNROLL
                ;;ACL2::CONSP-WHEN-LEN-EQUAL
                ;;ACL2::CONSP-WHEN-LEN-EQUAL-alt
                ;;endp
                BLAKE::BYTES-TO-BLOCK
                BLAKE::BYTES-TO-WORDS-BASE
                BLAKE::BYTES-TO-WORDS-UNROLL
                ;; ACL2::NTHCDR-WHEN-EQUAL-OF-LEN
                BLAKE::BYTES-TO-WORD
                BLAKE::BLAKE2S-MAIN
                BLAKE::F
                BLAKE::f-LOOP-1-BASE
                BLAKE::f-LOOP-1-UNROLL
                BLAKE::f-LOOP-2-BASE
                BLAKE::f-LOOP-2-UNROLL
                BLAKE::LOOP1-BASE
                BLAKE::LOOP1-UNROLL
                BLAKE::WORDXOR
                blake::g
                BLAKE::ROT-WORD
                ACL2::NTH-OF-NTHCDR
                BLAKE::LEN-OF-BYTES-TO-BLOCKS
                blake::sigma
                BLAKE::IV
                BLAKE::WORDS-TO-BYTES-BASE
                BLAKE::WORDS-TO-BYTES-UNROLL
                BLAKE::WORD-TO-BYTES
                acl2::mod-of-+-of-4294967296
                ACL2::BVPLUS-OF-+-ARG2
                ACL2::BVPLUS-OF-+-ARG3
                ACL2::UPDATE-NTH-OF-UPDATE-NTH-SAME
                ACL2::CDR-OF-UPDATE-NTH
                ACL2::CAR-OF-UPDATE-NTH
                ACL2::BVSHL-OF-0-ARG2
                ACL2::BVSHR-CONSTANT-OPENER
                ACL2::slice-CONSTANT-OPENER
                ACL2::LOGTAIL$INLINE-CONSTANT-OPENER
                ACL2::EXPT2$INLINE
                ACL2::ifloor$INLINE
                ACL2::BVPLUS-COMBINE-CONSTANTS
                (acl2::type-rules)
                ACL2::BITS-TO-BYTES-little-BASE
                ACL2::BITS-TO-BYTES-little-UNROLL
                ACL2::BITS-TO-BYTE-little

                ;; more rules to try to complete the proof:
                ACL2::EQUAL-OF-CONS-AND-CONS ;rewrites the top equality
                ADD-OF-CONSTANT-NORMALIZE-TO-FEP
                )
               ;; handle remaining adds, bit-blast, etc.:
               (pfield::ADD-BECOMES-BVPLUS-34
                pfield::ADD-BECOMES-BVPLUS-33
                (acl2::unsigned-byte-p-rules)
                (acl2::trim-helper-rules)
                ACL2::BVCAT-EQUAL-REWRITE-ALT
                ACL2::BVCAT-EQUAL-REWRITE
                acl2::getbit-of-slice-gen
                acl2::getbit-of-slice
                ACL2::BVCHOP-OF-SLICE-BOTH
                acl2::slice-becomes-getbit
                ACL2::GETBIT-OF-BVXOR
                ACL2::SLICE-OF-BVXOR
                ACL2::BVCHOP-OF-BVXOR
                ACL2::BVXOR-OF-CONSTANT-CHOP-ARG2 ;acl2::bvxor-of-constant-trim-arg1
                ACL2::BVXOR-1-BECOMES-BITXOR
                ACL2::BITXOR-OF-1-BECOMES-BITNOT-ARG1
                ACL2::BITNOT-TRIM-axe-ALL
                ACL2::BITXOR-OF-SLICE-ARG2           ;use trim rules?
                ACL2::BITXOR-OF-SLICE-ARG1           ;use trim rules?
                ACL2::RIGHTROTATE-BECOMES-LEFTROTATE ;try to do it without this?
                ACL2::BVCHOP-IDENTITY
                ACL2::GETBIT-OF-LEFTROTATE-SIMPLE
                ACL2::BITXOR-OF-0-ARG1
                ACL2::SLICE-OF-LEFTROTATE
                ACL2::BITXOR-TRIM-ARG1-axe-ALL
                ACL2::BITXOR-TRIM-ARG2-axe-ALL
                ACL2::SLICE-OF-SLICE
                acl2::GETBIT-OF-BVPLUS-TIGHTEN-TO-32
                acl2::SLICE-OF-BVPLUS-TIGHTEN-TO-32
                ACL2::GETBIT-OF-BVCAT-ALL
                ACL2::SLICE-OF-BVCAT-GEN
                ACL2::BITXOR-OF-BITNOT-ARG1
                ACL2::BITXOR-OF-BITNOT-ARG2
                ACL2::BVCAT-ASSOCIATIVE-GEN
                ACL2::BVXOR-ASSOCIATIVE
                ACL2::BitXOR-ASSOCIATIVE
                ACL2::BITNOT-OF-BITNOT
                acl2::EQUAL-OF-BITNOT-AND-BITNOT
                ACL2::GETBIT-IDENTITY
                ACL2::SLICE-BECOMES-BVCHOP
                ACL2::BVPLUS-ASSOCIATIVE
                ACL2::BVPLUS-TRIM-ARG2-axe-all
                ACL2::BVPLUS-TRIM-ARG3-axe-all
                ACL2::BVPLUS-OF-0-arg2
                ACL2::BVXOR-COMBINE-CONSTANTS
                acl2::BVPLUS-OF-BVPLUS-TRIM-TO-32-ARG1
                acl2::BVPLUS-OF-BVPLUS-TRIM-TO-32-ARG2
                ACL2::BVCHOP-1-BECOMES-GETBIT
                ACL2::BVNOT-BLAST
                ACL2::LEFTROTATE-OPEN-WHEN-CONSTANT-SHIFT-AMOUNT ;maybe
                ACL2::BVCAT-BLAST-HIGH
                ACL2::BVCAT-BLAST-low
                (acl2::type-rules)
                ACL2::BVNOT-1-BECOMES-BITNOT-BETTER
                ACL2::GETBIT-TRIM-axe-ALL ;aggressive
                ACL2::SLICE-TRIM-axe-ALL      ;aggressive
                ACL2::GETBIT-OF-0-WHEN-BITP
                ACL2::BVCAT-TRIM-ARG2-axe-ALL
                ACL2::BVCAT-TRIM-ARG4-axe-ALL
                ACL2::BVPLUS-1-BECOMES-BITXOR
                ACL2::BVPLUS-COMMUTATIVE-2-INCREASING-AXE
                ACL2::BVPLUS-COMMUTATIVE-INCREASING-AXE
                ACL2::BITXOR-COMMUTATIVE-2-INCREASING-AXE
                ACL2::BITXOR-COMMUTATIVE-INCREASING-AXE
                acl2::equal-same
                ACL2::BITP-OF-GETBIT
                ;;new:
                ACL2::IF-OF-NIL-BECOMES-BOOLAND
                ACL2::GETBIT-OF-BVPLUS
                )))
