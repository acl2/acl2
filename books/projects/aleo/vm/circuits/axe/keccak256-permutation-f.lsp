; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Note, this file is dependent on
; ../samples/sha3-samples.lisp,
; which is now tracked by git lfs.
; See ../samples/README.md for more information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "support")
(include-book "../samples/sha3-component-samples") ;drop?
(include-book "../samples/sha3-samples")
(include-book "kestrel/axe/unroll-spec" :dir :system) ;drop?
(include-book "kestrel/axe/unroll-spec-basic" :dir :system) ;drop?

;; (aleo::p1cs (aleo::keccak256-permutation-f--constraints))

(acl2::defopeners sha3::keccak-p-aux)
(acl2::defopeners sha3::map-plane-to-bit-string)
(acl2::defopeners acl2::ungroup)
(acl2::defopeners sha3::iota-aux)
(acl2::defopeners sha3::rc-aux)
(acl2::defopeners sha3::theta-d-lane)


;; todo: update
(defconst *permutation-f-input-vars*
  (acl2::make-var-name-range '|w| 1 1600))

;; first, let's just try to get the spec lifted:

(defthm acl2::update-nth-of-0-and-cons
  (equal (update-nth 0 x (cons a b))
         (cons x b)))

;; This shows a rule set that can efficiently unroll the spec:
;; (make-event
;;   ;; todo: suppress non-pure warnings
;;   `(acl2::unroll-spec-basic *foo* '(sha3::keccak-f 1600 (list ,@*permutation-f-input-vars*))
;;                        :print nil
;;                       ;; :interpreted-function-alist
;;                       ;; (acl2::make-interpreted-function-alist
;;                       ;;   '(neg pfield::add pfield::pos-fix BVCAT acl2::logapp ash ACL2::EXPT2$INLINE ACL2::LOGHEAD$INLINE ACL2::IMOD$INLINE INTEGER-RANGE-P POWER-OF-2P fep unsigned-byte-p getbit slice ACL2::LOGTAIL$INLINE ACL2::IFLOOR$INLINE bitnot sub bvnot lognot bitxor POWER-OF-2P ACL2::BVSHR ACL2::BVSHL TRUE-LIST-FIX
;;                       ;;     acl2::booland
;;                       ;;     acl2::bitxor$
;;                       ;;     sha3::rc
;;                       ;;     sha3::rc-aux
;;                       ;;     update-nth
;;                       ;;     sha3::iota-aux
;;                       ;;     )
;;                       ;;   (w state))
;;                             :normalize-xors nil
;;                             :memoizep nil
;;                       :rules '(;spec-permutation-f
;;                                ;;rnd-with-rc
;;                                ;;iota-with-rc
;;                                sha3::iota
;;                                sha3::iota-aux2-base sha3::iota-aux2-unroll
;;                                sha3::iota-aux-base sha3::iota-aux-unroll
;;                                sha3::get-lane
;;                                sha3::set-lane
;;                                sha3::nth-bit
;;                                sha3::update-bit
;;                                sha3::update-nth-bit
;;                                sha3::update-nth-lane
;;                                sha3::update-nth-plane
;;                                sha3::chi
;;                                sha3::chi-planes-base sha3::chi-planes-unroll
;;                                sha3::chi-lanes-base sha3::chi-lanes-unroll
;;                                sha3::chi-lane-base sha3::chi-lane-unroll
;;                                sha3::theta
;;                                sha3::theta-planes-base sha3::theta-planes-unroll
;;                                sha3::theta-lanes-base sha3::theta-lanes-unroll
;;                                sha3::theta-lane-base sha3::theta-lane-unroll
;;                                sha3::theta-d-lanes-base sha3::theta-d-lanes-unroll
;;                                sha3::theta-d-lane-base sha3::theta-d-lane-unroll
;;                                sha3::theta-d
;;                                sha3::theta-c
;;                                sha3::theta-c-lanes-base sha3::theta-c-lanes-unroll
;;                                sha3::theta-c-lane-base sha3::theta-c-lane-unroll
;;                                sha3::rho
;;                                sha3::rho-aux-aux-base sha3::rho-aux-aux-unroll
;;                                sha3::rho-aux-base sha3::rho-aux-unroll
;;                                sha3::pi-fn
;;                                sha3::pi-planes-base sha3::pi-planes-unroll
;;                                sha3::pi-lanes-base sha3::pi-lanes-unroll
;;                                acl2::bitxor$ ; todo: add these 2 to a basic rule set
;;                                acl2::bitand$
;;                                sha3::a sha3::nth-lane sha3::nth-plane sha3::nth-bit
;;                                sha3::bit-string-to-plane
;;                                sha3::bits-to-state-array
;;                                sha3::map-bit-string-to-plane-base
;;                                sha3::map-bit-string-to-plane-unroll
;;                                acl2::group-base
;;                                ;acl2::group-unroll
;;                                acl2::atom
;;                                acl2::consp-of-cons
;;                                acl2::nthcdr-of-cons
;;                                acl2::firstn-base-1 acl2::firstn-base-2 ; combine these?
;;                                ;acl2::firstn-unroll
;;                                acl2::endp
;;                                acl2::car-cons acl2::cdr-cons
;;                                acl2::nth-of-cons-constant-version
;;                                ;;acl2::equal-of-cons-and-cons
;;                                ;;acl2::bitxor-commutative-2-increasing-axe
;;                                ;;acl2::bitxor-associative
;;                                acl2::bitxor-of-1-becomes-bitnot-arg2
;;                                ;;acl2::update-nth-base acl2::update-nth-unroll ; since we have a cons nest on one side an update-nth on the other side
;;                                ;;acl2::nth-update-nth-safe
;;                                ;acl2::bitxor-of-bitnot-arg1
;;                                ;acl2::bitxor-of-bitnot-arg2
;;                                sha3::keccak-f
;;                                sha3::keccak-p
;;                                sha3::keccak-p-aux-base
;;                                sha3::keccak-p-aux-unroll
;;                                sha3::rnd
;;                                sha3::state-array-to-bits
;;                                sha3::map-plane-to-bit-string-base
;;                                sha3::map-plane-to-bit-string-unroll
;;                                sha3::plane-to-bit-string
;;                                acl2::ungroup-base
;;                                acl2::ungroup-unroll
;;                                acl2::take-of-0
;;                                acl2::take-of-cons-when-posp
;;                                ;acl2::take-opener-when-not-zp
;;                                acl2::append-of-cons
;;                                acl2::append-of-nil-arg1
;;                                ;;acl2::equal-of-cons-and-cons
;;                                sha3::rc
;;                                sha3::rc-aux-base sha3::rc-aux-unroll
;;                                ;;acl2::bitxor-of-0-arg2
;;                                acl2::nth-update-nth-safe ; instead of opening update-nth...
;;                                acl2::update-nth-of-cons
;;                                acl2::update-nth-of-update-nth-same
;;                                acl2::update-nth-of-0-and-cons
;;                                acl2::take-of-append
;;                                acl2::len-of-cons
;;                                acl2::append-to-nil
;;                                acl2::bitxor-of-0-arg2
;;                                acl2::group-of-cons
;;                                acl2::firstn-becomes-take
;;                                acl2::getbit-of-0-when-bitp
;;                                acl2::bitp-of-bitxor
;;                                )))

;; These are from the special final constraint added by Eric M to show the output bits
(defconst *permutation-f-output-vars*
  '(|w158208| |w158209| |w158210| |w158211|
    |w158212| |w158213| |w158214| |w158215|
    |w158216| |w158217| |w158218| |w158219|
    |w158220| |w158221| |w158222| |w158223|
    |w158224| |w158225| |w158226| |w158227|
    |w158228| |w158229| |w158230| |w158231|
    |w158232| |w158233| |w158234| |w158235|
    |w158236| |w158237| |w158238| |w158239|
    |w158240| |w158241| |w158242| |w158243|
    |w158244| |w158245| |w158246| |w158247|
    |w158248| |w158249| |w158250| |w158251|
    |w158252| |w158253| |w158254| |w158255|
    |w158256| |w158257| |w158258| |w158259|
    |w158260| |w158261| |w158262| |w158263|
    |w158264| |w158265| |w158266| |w158267|
    |w158268| |w158269| |w158270| |w158271|
    |w155200| |w155201| |w155202| |w155203|
    |w155204| |w155205| |w155206| |w155207|
    |w155208| |w155209| |w155210| |w155211|
    |w155212| |w155213| |w155214| |w155215|
    |w155216| |w155217| |w155218| |w155219|
    |w155220| |w155221| |w155222| |w155223|
    |w155224| |w155225| |w155226| |w155227|
    |w155228| |w155229| |w155230| |w155231|
    |w155232| |w155233| |w155234| |w155235|
    |w155236| |w155237| |w155238| |w155239|
    |w155240| |w155241| |w155242| |w155243|
    |w155244| |w155245| |w155246| |w155247|
    |w155248| |w155249| |w155250| |w155251|
    |w155252| |w155253| |w155254| |w155255|
    |w155256| |w155257| |w155258| |w155259|
    |w155260| |w155261| |w155262| |w155263|
    |w155328| |w155329| |w155330| |w155331|
    |w155332| |w155333| |w155334| |w155335|
    |w155336| |w155337| |w155338| |w155339|
    |w155340| |w155341| |w155342| |w155343|
    |w155344| |w155345| |w155346| |w155347|
    |w155348| |w155349| |w155350| |w155351|
    |w155352| |w155353| |w155354| |w155355|
    |w155356| |w155357| |w155358| |w155359|
    |w155360| |w155361| |w155362| |w155363|
    |w155364| |w155365| |w155366| |w155367|
    |w155368| |w155369| |w155370| |w155371|
    |w155372| |w155373| |w155374| |w155375|
    |w155376| |w155377| |w155378| |w155379|
    |w155380| |w155381| |w155382| |w155383|
    |w155384| |w155385| |w155386| |w155387|
    |w155388| |w155389| |w155390| |w155391|
    |w155456| |w155457| |w155458| |w155459|
    |w155460| |w155461| |w155462| |w155463|
    |w155464| |w155465| |w155466| |w155467|
    |w155468| |w155469| |w155470| |w155471|
    |w155472| |w155473| |w155474| |w155475|
    |w155476| |w155477| |w155478| |w155479|
    |w155480| |w155481| |w155482| |w155483|
    |w155484| |w155485| |w155486| |w155487|
    |w155488| |w155489| |w155490| |w155491|
    |w155492| |w155493| |w155494| |w155495|
    |w155496| |w155497| |w155498| |w155499|
    |w155500| |w155501| |w155502| |w155503|
    |w155504| |w155505| |w155506| |w155507|
    |w155508| |w155509| |w155510| |w155511|
    |w155512| |w155513| |w155514| |w155515|
    |w155516| |w155517| |w155518| |w155519|
    |w155584| |w155585| |w155586| |w155587|
    |w155588| |w155589| |w155590| |w155591|
    |w155592| |w155593| |w155594| |w155595|
    |w155596| |w155597| |w155598| |w155599|
    |w155600| |w155601| |w155602| |w155603|
    |w155604| |w155605| |w155606| |w155607|
    |w155608| |w155609| |w155610| |w155611|
    |w155612| |w155613| |w155614| |w155615|
    |w155616| |w155617| |w155618| |w155619|
    |w155620| |w155621| |w155622| |w155623|
    |w155624| |w155625| |w155626| |w155627|
    |w155628| |w155629| |w155630| |w155631|
    |w155632| |w155633| |w155634| |w155635|
    |w155636| |w155637| |w155638| |w155639|
    |w155640| |w155641| |w155642| |w155643|
    |w155644| |w155645| |w155646| |w155647|
    |w155712| |w155713| |w155714| |w155715|
    |w155716| |w155717| |w155718| |w155719|
    |w155720| |w155721| |w155722| |w155723|
    |w155724| |w155725| |w155726| |w155727|
    |w155728| |w155729| |w155730| |w155731|
    |w155732| |w155733| |w155734| |w155735|
    |w155736| |w155737| |w155738| |w155739|
    |w155740| |w155741| |w155742| |w155743|
    |w155744| |w155745| |w155746| |w155747|
    |w155748| |w155749| |w155750| |w155751|
    |w155752| |w155753| |w155754| |w155755|
    |w155756| |w155757| |w155758| |w155759|
    |w155760| |w155761| |w155762| |w155763|
    |w155764| |w155765| |w155766| |w155767|
    |w155768| |w155769| |w155770| |w155771|
    |w155772| |w155773| |w155774| |w155775|
    |w155840| |w155841| |w155842| |w155843|
    |w155844| |w155845| |w155846| |w155847|
    |w155848| |w155849| |w155850| |w155851|
    |w155852| |w155853| |w155854| |w155855|
    |w155856| |w155857| |w155858| |w155859|
    |w155860| |w155861| |w155862| |w155863|
    |w155864| |w155865| |w155866| |w155867|
    |w155868| |w155869| |w155870| |w155871|
    |w155872| |w155873| |w155874| |w155875|
    |w155876| |w155877| |w155878| |w155879|
    |w155880| |w155881| |w155882| |w155883|
    |w155884| |w155885| |w155886| |w155887|
    |w155888| |w155889| |w155890| |w155891|
    |w155892| |w155893| |w155894| |w155895|
    |w155896| |w155897| |w155898| |w155899|
    |w155900| |w155901| |w155902| |w155903|
    |w155968| |w155969| |w155970| |w155971|
    |w155972| |w155973| |w155974| |w155975|
    |w155976| |w155977| |w155978| |w155979|
    |w155980| |w155981| |w155982| |w155983|
    |w155984| |w155985| |w155986| |w155987|
    |w155988| |w155989| |w155990| |w155991|
    |w155992| |w155993| |w155994| |w155995|
    |w155996| |w155997| |w155998| |w155999|
    |w156000| |w156001| |w156002| |w156003|
    |w156004| |w156005| |w156006| |w156007|
    |w156008| |w156009| |w156010| |w156011|
    |w156012| |w156013| |w156014| |w156015|
    |w156016| |w156017| |w156018| |w156019|
    |w156020| |w156021| |w156022| |w156023|
    |w156024| |w156025| |w156026| |w156027|
    |w156028| |w156029| |w156030| |w156031|
    |w156096| |w156097| |w156098| |w156099|
    |w156100| |w156101| |w156102| |w156103|
    |w156104| |w156105| |w156106| |w156107|
    |w156108| |w156109| |w156110| |w156111|
    |w156112| |w156113| |w156114| |w156115|
    |w156116| |w156117| |w156118| |w156119|
    |w156120| |w156121| |w156122| |w156123|
    |w156124| |w156125| |w156126| |w156127|
    |w156128| |w156129| |w156130| |w156131|
    |w156132| |w156133| |w156134| |w156135|
    |w156136| |w156137| |w156138| |w156139|
    |w156140| |w156141| |w156142| |w156143|
    |w156144| |w156145| |w156146| |w156147|
    |w156148| |w156149| |w156150| |w156151|
    |w156152| |w156153| |w156154| |w156155|
    |w156156| |w156157| |w156158| |w156159|
    |w156224| |w156225| |w156226| |w156227|
    |w156228| |w156229| |w156230| |w156231|
    |w156232| |w156233| |w156234| |w156235|
    |w156236| |w156237| |w156238| |w156239|
    |w156240| |w156241| |w156242| |w156243|
    |w156244| |w156245| |w156246| |w156247|
    |w156248| |w156249| |w156250| |w156251|
    |w156252| |w156253| |w156254| |w156255|
    |w156256| |w156257| |w156258| |w156259|
    |w156260| |w156261| |w156262| |w156263|
    |w156264| |w156265| |w156266| |w156267|
    |w156268| |w156269| |w156270| |w156271|
    |w156272| |w156273| |w156274| |w156275|
    |w156276| |w156277| |w156278| |w156279|
    |w156280| |w156281| |w156282| |w156283|
    |w156284| |w156285| |w156286| |w156287|
    |w156352| |w156353| |w156354| |w156355|
    |w156356| |w156357| |w156358| |w156359|
    |w156360| |w156361| |w156362| |w156363|
    |w156364| |w156365| |w156366| |w156367|
    |w156368| |w156369| |w156370| |w156371|
    |w156372| |w156373| |w156374| |w156375|
    |w156376| |w156377| |w156378| |w156379|
    |w156380| |w156381| |w156382| |w156383|
    |w156384| |w156385| |w156386| |w156387|
    |w156388| |w156389| |w156390| |w156391|
    |w156392| |w156393| |w156394| |w156395|
    |w156396| |w156397| |w156398| |w156399|
    |w156400| |w156401| |w156402| |w156403|
    |w156404| |w156405| |w156406| |w156407|
    |w156408| |w156409| |w156410| |w156411|
    |w156412| |w156413| |w156414| |w156415|
    |w156480| |w156481| |w156482| |w156483|
    |w156484| |w156485| |w156486| |w156487|
    |w156488| |w156489| |w156490| |w156491|
    |w156492| |w156493| |w156494| |w156495|
    |w156496| |w156497| |w156498| |w156499|
    |w156500| |w156501| |w156502| |w156503|
    |w156504| |w156505| |w156506| |w156507|
    |w156508| |w156509| |w156510| |w156511|
    |w156512| |w156513| |w156514| |w156515|
    |w156516| |w156517| |w156518| |w156519|
    |w156520| |w156521| |w156522| |w156523|
    |w156524| |w156525| |w156526| |w156527|
    |w156528| |w156529| |w156530| |w156531|
    |w156532| |w156533| |w156534| |w156535|
    |w156536| |w156537| |w156538| |w156539|
    |w156540| |w156541| |w156542| |w156543|
    |w156608| |w156609| |w156610| |w156611|
    |w156612| |w156613| |w156614| |w156615|
    |w156616| |w156617| |w156618| |w156619|
    |w156620| |w156621| |w156622| |w156623|
    |w156624| |w156625| |w156626| |w156627|
    |w156628| |w156629| |w156630| |w156631|
    |w156632| |w156633| |w156634| |w156635|
    |w156636| |w156637| |w156638| |w156639|
    |w156640| |w156641| |w156642| |w156643|
    |w156644| |w156645| |w156646| |w156647|
    |w156648| |w156649| |w156650| |w156651|
    |w156652| |w156653| |w156654| |w156655|
    |w156656| |w156657| |w156658| |w156659|
    |w156660| |w156661| |w156662| |w156663|
    |w156664| |w156665| |w156666| |w156667|
    |w156668| |w156669| |w156670| |w156671|
    |w156736| |w156737| |w156738| |w156739|
    |w156740| |w156741| |w156742| |w156743|
    |w156744| |w156745| |w156746| |w156747|
    |w156748| |w156749| |w156750| |w156751|
    |w156752| |w156753| |w156754| |w156755|
    |w156756| |w156757| |w156758| |w156759|
    |w156760| |w156761| |w156762| |w156763|
    |w156764| |w156765| |w156766| |w156767|
    |w156768| |w156769| |w156770| |w156771|
    |w156772| |w156773| |w156774| |w156775|
    |w156776| |w156777| |w156778| |w156779|
    |w156780| |w156781| |w156782| |w156783|
    |w156784| |w156785| |w156786| |w156787|
    |w156788| |w156789| |w156790| |w156791|
    |w156792| |w156793| |w156794| |w156795|
    |w156796| |w156797| |w156798| |w156799|
    |w156864| |w156865| |w156866| |w156867|
    |w156868| |w156869| |w156870| |w156871|
    |w156872| |w156873| |w156874| |w156875|
    |w156876| |w156877| |w156878| |w156879|
    |w156880| |w156881| |w156882| |w156883|
    |w156884| |w156885| |w156886| |w156887|
    |w156888| |w156889| |w156890| |w156891|
    |w156892| |w156893| |w156894| |w156895|
    |w156896| |w156897| |w156898| |w156899|
    |w156900| |w156901| |w156902| |w156903|
    |w156904| |w156905| |w156906| |w156907|
    |w156908| |w156909| |w156910| |w156911|
    |w156912| |w156913| |w156914| |w156915|
    |w156916| |w156917| |w156918| |w156919|
    |w156920| |w156921| |w156922| |w156923|
    |w156924| |w156925| |w156926| |w156927|
    |w156992| |w156993| |w156994| |w156995|
    |w156996| |w156997| |w156998| |w156999|
    |w157000| |w157001| |w157002| |w157003|
    |w157004| |w157005| |w157006| |w157007|
    |w157008| |w157009| |w157010| |w157011|
    |w157012| |w157013| |w157014| |w157015|
    |w157016| |w157017| |w157018| |w157019|
    |w157020| |w157021| |w157022| |w157023|
    |w157024| |w157025| |w157026| |w157027|
    |w157028| |w157029| |w157030| |w157031|
    |w157032| |w157033| |w157034| |w157035|
    |w157036| |w157037| |w157038| |w157039|
    |w157040| |w157041| |w157042| |w157043|
    |w157044| |w157045| |w157046| |w157047|
    |w157048| |w157049| |w157050| |w157051|
    |w157052| |w157053| |w157054| |w157055|
    |w157120| |w157121| |w157122| |w157123|
    |w157124| |w157125| |w157126| |w157127|
    |w157128| |w157129| |w157130| |w157131|
    |w157132| |w157133| |w157134| |w157135|
    |w157136| |w157137| |w157138| |w157139|
    |w157140| |w157141| |w157142| |w157143|
    |w157144| |w157145| |w157146| |w157147|
    |w157148| |w157149| |w157150| |w157151|
    |w157152| |w157153| |w157154| |w157155|
    |w157156| |w157157| |w157158| |w157159|
    |w157160| |w157161| |w157162| |w157163|
    |w157164| |w157165| |w157166| |w157167|
    |w157168| |w157169| |w157170| |w157171|
    |w157172| |w157173| |w157174| |w157175|
    |w157176| |w157177| |w157178| |w157179|
    |w157180| |w157181| |w157182| |w157183|
    |w157248| |w157249| |w157250| |w157251|
    |w157252| |w157253| |w157254| |w157255|
    |w157256| |w157257| |w157258| |w157259|
    |w157260| |w157261| |w157262| |w157263|
    |w157264| |w157265| |w157266| |w157267|
    |w157268| |w157269| |w157270| |w157271|
    |w157272| |w157273| |w157274| |w157275|
    |w157276| |w157277| |w157278| |w157279|
    |w157280| |w157281| |w157282| |w157283|
    |w157284| |w157285| |w157286| |w157287|
    |w157288| |w157289| |w157290| |w157291|
    |w157292| |w157293| |w157294| |w157295|
    |w157296| |w157297| |w157298| |w157299|
    |w157300| |w157301| |w157302| |w157303|
    |w157304| |w157305| |w157306| |w157307|
    |w157308| |w157309| |w157310| |w157311|
    |w157376| |w157377| |w157378| |w157379|
    |w157380| |w157381| |w157382| |w157383|
    |w157384| |w157385| |w157386| |w157387|
    |w157388| |w157389| |w157390| |w157391|
    |w157392| |w157393| |w157394| |w157395|
    |w157396| |w157397| |w157398| |w157399|
    |w157400| |w157401| |w157402| |w157403|
    |w157404| |w157405| |w157406| |w157407|
    |w157408| |w157409| |w157410| |w157411|
    |w157412| |w157413| |w157414| |w157415|
    |w157416| |w157417| |w157418| |w157419|
    |w157420| |w157421| |w157422| |w157423|
    |w157424| |w157425| |w157426| |w157427|
    |w157428| |w157429| |w157430| |w157431|
    |w157432| |w157433| |w157434| |w157435|
    |w157436| |w157437| |w157438| |w157439|
    |w157504| |w157505| |w157506| |w157507|
    |w157508| |w157509| |w157510| |w157511|
    |w157512| |w157513| |w157514| |w157515|
    |w157516| |w157517| |w157518| |w157519|
    |w157520| |w157521| |w157522| |w157523|
    |w157524| |w157525| |w157526| |w157527|
    |w157528| |w157529| |w157530| |w157531|
    |w157532| |w157533| |w157534| |w157535|
    |w157536| |w157537| |w157538| |w157539|
    |w157540| |w157541| |w157542| |w157543|
    |w157544| |w157545| |w157546| |w157547|
    |w157548| |w157549| |w157550| |w157551|
    |w157552| |w157553| |w157554| |w157555|
    |w157556| |w157557| |w157558| |w157559|
    |w157560| |w157561| |w157562| |w157563|
    |w157564| |w157565| |w157566| |w157567|
    |w157632| |w157633| |w157634| |w157635|
    |w157636| |w157637| |w157638| |w157639|
    |w157640| |w157641| |w157642| |w157643|
    |w157644| |w157645| |w157646| |w157647|
    |w157648| |w157649| |w157650| |w157651|
    |w157652| |w157653| |w157654| |w157655|
    |w157656| |w157657| |w157658| |w157659|
    |w157660| |w157661| |w157662| |w157663|
    |w157664| |w157665| |w157666| |w157667|
    |w157668| |w157669| |w157670| |w157671|
    |w157672| |w157673| |w157674| |w157675|
    |w157676| |w157677| |w157678| |w157679|
    |w157680| |w157681| |w157682| |w157683|
    |w157684| |w157685| |w157686| |w157687|
    |w157688| |w157689| |w157690| |w157691|
    |w157692| |w157693| |w157694| |w157695|
    |w157760| |w157761| |w157762| |w157763|
    |w157764| |w157765| |w157766| |w157767|
    |w157768| |w157769| |w157770| |w157771|
    |w157772| |w157773| |w157774| |w157775|
    |w157776| |w157777| |w157778| |w157779|
    |w157780| |w157781| |w157782| |w157783|
    |w157784| |w157785| |w157786| |w157787|
    |w157788| |w157789| |w157790| |w157791|
    |w157792| |w157793| |w157794| |w157795|
    |w157796| |w157797| |w157798| |w157799|
    |w157800| |w157801| |w157802| |w157803|
    |w157804| |w157805| |w157806| |w157807|
    |w157808| |w157809| |w157810| |w157811|
    |w157812| |w157813| |w157814| |w157815|
    |w157816| |w157817| |w157818| |w157819|
    |w157820| |w157821| |w157822| |w157823|
    |w157888| |w157889| |w157890| |w157891|
    |w157892| |w157893| |w157894| |w157895|
    |w157896| |w157897| |w157898| |w157899|
    |w157900| |w157901| |w157902| |w157903|
    |w157904| |w157905| |w157906| |w157907|
    |w157908| |w157909| |w157910| |w157911|
    |w157912| |w157913| |w157914| |w157915|
    |w157916| |w157917| |w157918| |w157919|
    |w157920| |w157921| |w157922| |w157923|
    |w157924| |w157925| |w157926| |w157927|
    |w157928| |w157929| |w157930| |w157931|
    |w157932| |w157933| |w157934| |w157935|
    |w157936| |w157937| |w157938| |w157939|
    |w157940| |w157941| |w157942| |w157943|
    |w157944| |w157945| |w157946| |w157947|
    |w157948| |w157949| |w157950| |w157951|
    |w158016| |w158017| |w158018| |w158019|
    |w158020| |w158021| |w158022| |w158023|
    |w158024| |w158025| |w158026| |w158027|
    |w158028| |w158029| |w158030| |w158031|
    |w158032| |w158033| |w158034| |w158035|
    |w158036| |w158037| |w158038| |w158039|
    |w158040| |w158041| |w158042| |w158043|
    |w158044| |w158045| |w158046| |w158047|
    |w158048| |w158049| |w158050| |w158051|
    |w158052| |w158053| |w158054| |w158055|
    |w158056| |w158057| |w158058| |w158059|
    |w158060| |w158061| |w158062| |w158063|
    |w158064| |w158065| |w158066| |w158067|
    |w158068| |w158069| |w158070| |w158071|
    |w158072| |w158073| |w158074| |w158075|
    |w158076| |w158077| |w158078| |w158079|
    |w158144| |w158145| |w158146| |w158147|
    |w158148| |w158149| |w158150| |w158151|
    |w158152| |w158153| |w158154| |w158155|
    |w158156| |w158157| |w158158| |w158159|
    |w158160| |w158161| |w158162| |w158163|
    |w158164| |w158165| |w158166| |w158167|
    |w158168| |w158169| |w158170| |w158171|
    |w158172| |w158173| |w158174| |w158175|
    |w158176| |w158177| |w158178| |w158179|
    |w158180| |w158181| |w158182| |w158183|
    |w158184| |w158185| |w158186| |w158187|
    |w158188| |w158189| |w158190| |w158191|
    |w158192| |w158193| |w158194| |w158195|
    |w158196| |w158197| |w158198| |w158199|
    |w158200| |w158201| |w158202| |w158203|
    |w158204| |w158205| |w158206| |w158207|
    ))

;; (make-event
;;   ;; todo: suppress non-pure warnings
;;   `(acl2::unroll-spec-basic *foo* '(equal (list ,@*permutation-f-output-vars*)
;;                                     (sha3::keccak-f 1600 (list ,@*permutation-f-input-vars*)))
;;                       :print t
;;                       ;; :interpreted-function-alist
;;                       ;; (acl2::make-interpreted-function-alist
;;                       ;;   '(neg pfield::add pfield::pos-fix BVCAT acl2::logapp ash ACL2::EXPT2$INLINE ACL2::LOGHEAD$INLINE ACL2::IMOD$INLINE INTEGER-RANGE-P POWER-OF-2P fep unsigned-byte-p getbit slice ACL2::LOGTAIL$INLINE ACL2::IFLOOR$INLINE bitnot sub bvnot lognot bitxor POWER-OF-2P ACL2::BVSHR ACL2::BVSHL TRUE-LIST-FIX
;;                       ;;     acl2::booland
;;                       ;;     acl2::bitxor$
;;                       ;;     sha3::rc
;;                       ;;     sha3::rc-aux
;;                       ;;     update-nth
;;                       ;;     sha3::iota-aux
;;                       ;;     )
;;                       ;;   (w state))
;;                       :normalize-xors nil
;;                       :rules '(;spec-permutation-f
;;                                ;;rnd-with-rc
;;                                ;;iota-with-rc
;;                                sha3::iota
;;                                sha3::iota-aux2-base sha3::iota-aux2-unroll
;;                                sha3::iota-aux-base sha3::iota-aux-unroll
;;                                sha3::get-lane
;;                                sha3::set-lane
;;                                sha3::nth-bit
;;                                sha3::update-bit
;;                                sha3::update-nth-bit
;;                                sha3::update-nth-lane
;;                                sha3::update-nth-plane
;;                                sha3::chi
;;                                sha3::chi-planes-base sha3::chi-planes-unroll
;;                                sha3::chi-lanes-base sha3::chi-lanes-unroll
;;                                sha3::chi-lane-base sha3::chi-lane-unroll
;;                                sha3::theta
;;                                sha3::theta-planes-base sha3::theta-planes-unroll
;;                                sha3::theta-lanes-base sha3::theta-lanes-unroll
;;                                sha3::theta-lane-base sha3::theta-lane-unroll
;;                                sha3::theta-d-lanes-base sha3::theta-d-lanes-unroll
;;                                sha3::theta-d-lane-base sha3::theta-d-lane-unroll
;;                                sha3::theta-d
;;                                sha3::theta-c
;;                                sha3::theta-c-lanes-base sha3::theta-c-lanes-unroll
;;                                sha3::theta-c-lane-base sha3::theta-c-lane-unroll
;;                                sha3::rho
;;                                sha3::rho-aux-aux-base sha3::rho-aux-aux-unroll
;;                                sha3::rho-aux-base sha3::rho-aux-unroll
;;                                sha3::pi-fn
;;                                sha3::pi-planes-base sha3::pi-planes-unroll
;;                                sha3::pi-lanes-base sha3::pi-lanes-unroll
;;                                acl2::bitxor$ ; todo: add these 2 to a basic rule set
;;                                acl2::bitand$
;;                                sha3::a sha3::nth-lane sha3::nth-plane sha3::nth-bit
;;                                sha3::bit-string-to-plane
;;                                sha3::bits-to-state-array
;;                                sha3::map-bit-string-to-plane-base
;;                                sha3::map-bit-string-to-plane-unroll
;;                                acl2::group-base acl2::group-unroll
;;                                acl2::atom
;;                                acl2::consp-of-cons
;;                                acl2::nthcdr-of-cons
;;                                acl2::firstn-base-1 acl2::firstn-base-2 ; combine these?
;;                                acl2::firstn-unroll
;;                                acl2::endp
;;                                acl2::car-cons acl2::cdr-cons
;;                                acl2::nth-of-cons-constant-version
;;                  ;acl2::equal-of-cons-and-cons
;;                  ;acl2::bitxor-commutative-2-increasing-axe
;;                  ;acl2::bitxor-associative
;;                                acl2::bitxor-of-1-becomes-bitnot-arg2
;;                  ;acl2::update-nth-base acl2::update-nth-unroll ; since we have a cons nest on one side an update-nth on the other side
;;                  ;;acl2::nth-update-nth-safe
;;                                acl2::bitxor-of-bitnot-arg1
;;                                acl2::bitxor-of-bitnot-arg2
;;                                sha3::keccak-f
;;                                sha3::keccak-p
;;                                sha3::keccak-p-aux-base
;;                                sha3::keccak-p-aux-unroll
;;                                sha3::rnd
;;                                sha3::state-array-to-bits
;;                                sha3::map-plane-to-bit-string-base sha3::map-plane-to-bit-string-unroll
;;                                sha3::plane-to-bit-string
;;                                acl2::ungroup-base
;;                                acl2::ungroup-unroll
;;                                acl2::take-of-0
;;                                acl2::take-opener-when-not-zp
;;                                acl2::append-of-cons
;;                                acl2::append-of-nil-arg1
;;                  ;acl2::equal-of-cons-and-cons
;;                                sha3::rc
;;                                sha3::rc-aux-base sha3::rc-aux-unroll
;;                  ;acl2::bitxor-of-0-arg2
;;                                acl2::nth-update-nth-safe ; instead of opening update-nth...
;;                                acl2::update-nth-of-cons
;;                                acl2::len-of-cons
;;                                )
;;                       ))

;; ;todo:
;; (make-event
;;   `(acl2::unroll-spec *foo* '(equal (list ,@*permutation-f-output-vars*)
;;                               (sha3::keccak-f 1600 (list ,@*permutation-f-input-vars*)))
;;                       :print t
;;                       ;; :interpreted-function-alist
;;                       ;; (acl2::make-interpreted-function-alist
;;                       ;;   '(neg pfield::add pfield::pos-fix BVCAT acl2::logapp ash ACL2::EXPT2$INLINE ACL2::LOGHEAD$INLINE ACL2::IMOD$INLINE INTEGER-RANGE-P POWER-OF-2P fep unsigned-byte-p getbit slice ACL2::LOGTAIL$INLINE ACL2::IFLOOR$INLINE bitnot sub bvnot lognot bitxor POWER-OF-2P ACL2::BVSHR ACL2::BVSHL TRUE-LIST-FIX
;;                       ;;     acl2::booland
;;                       ;;     acl2::bitxor$
;;                       ;;     sha3::rc
;;                       ;;     sha3::rc-aux
;;                       ;;     update-nth
;;                       ;;     sha3::iota-aux
;;                       ;;     )
;;                       ;;   (w state))
;;                       :normalize-xors nil
;;                       :rules '(;spec-permutation-f
;;                                ;;rnd-with-rc
;;                                ;;iota-with-rc
;;                                sha3::iota
;;                                sha3::iota-aux2-base sha3::iota-aux2-unroll
;;                                sha3::iota-aux-base sha3::iota-aux-unroll
;;                                sha3::get-lane
;;                                sha3::set-lane
;;                                sha3::nth-bit
;;                                sha3::update-bit
;;                                sha3::update-nth-bit
;;                                sha3::update-nth-lane
;;                                sha3::update-nth-plane
;;                                sha3::chi
;;                                sha3::chi-planes-base sha3::chi-planes-unroll
;;                                sha3::chi-lanes-base sha3::chi-lanes-unroll
;;                                sha3::chi-lane-base sha3::chi-lane-unroll
;;                                sha3::theta
;;                                sha3::theta-planes-base sha3::theta-planes-unroll
;;                                sha3::theta-lanes-base sha3::theta-lanes-unroll
;;                                sha3::theta-lane-base sha3::theta-lane-unroll
;;                                sha3::theta-d-lanes-base sha3::theta-d-lanes-unroll
;;                                sha3::theta-d-lane-base sha3::theta-d-lane-unroll
;;                                sha3::theta-d
;;                                sha3::theta-c
;;                                sha3::theta-c-lanes-base sha3::theta-c-lanes-unroll
;;                                sha3::theta-c-lane-base sha3::theta-c-lane-unroll
;;                                ;sha3::rho
;;                                sha3::rho-aux-aux-base sha3::rho-aux-aux-unroll
;;                                sha3::rho-aux-base sha3::rho-aux-unroll
;;                                sha3::pi-fn
;;                                sha3::pi-planes-base sha3::pi-planes-unroll
;;                                sha3::pi-lanes-base sha3::pi-lanes-unroll
;;                                acl2::bitxor$ ; todo: add these 2 to a basic rule set
;;                                acl2::bitand$
;;                                sha3::a sha3::nth-lane sha3::nth-plane sha3::nth-bit
;;                                sha3::bit-string-to-plane
;;                                sha3::bits-to-state-array
;;                                sha3::map-bit-string-to-plane-base
;;                                sha3::map-bit-string-to-plane-unroll
;;                                acl2::group-base acl2::group-unroll
;;                                acl2::atom
;;                                acl2::consp-of-cons
;;                                acl2::nthcdr-of-cons
;;                                acl2::firstn-base-1 acl2::firstn-base-2 ; combine these?
;;                                acl2::firstn-unroll
;;                                acl2::endp
;;                                acl2::car-cons acl2::cdr-cons
;;                                acl2::nth-of-cons-constant-version
;;                  ;acl2::equal-of-cons-and-cons
;;                  ;acl2::bitxor-commutative-2-increasing-axe
;;                  ;acl2::bitxor-associative
;;                                acl2::bitxor-of-1-becomes-bitnot-arg2
;;                  ;acl2::update-nth-base acl2::update-nth-unroll ; since we have a cons nest on one side an update-nth on the other side
;;                  ;;acl2::nth-update-nth-safe
;;                                acl2::bitxor-of-bitnot-arg1
;;                                acl2::bitxor-of-bitnot-arg2
;;                                sha3::keccak-f
;;                                sha3::keccak-p
;;                                sha3::keccak-p-aux-base
;;                                sha3::keccak-p-aux-unroll
;;                                sha3::rnd
;;                                sha3::state-array-to-bits
;;                                sha3::map-plane-to-bit-string-base sha3::map-plane-to-bit-string-unroll
;;                                sha3::plane-to-bit-string
;;                                acl2::ungroup-base
;;                                acl2::ungroup-unroll
;;                                acl2::take-of-0
;;                                acl2::take-opener-when-not-zp
;;                                acl2::append-of-cons
;;                                acl2::append-of-nil-arg1
;;                  ;acl2::equal-of-cons-and-cons
;;                                sha3::rc
;;                                sha3::rc-aux-base sha3::rc-aux-unroll
;;                  ;acl2::bitxor-of-0-arg2
;;                                acl2::nth-update-nth-safe ; instead of opening update-nth...
;;                                acl2::update-nth-of-cons
;;                                )
;;                       ))



;; The claim to prove.  This says that the output vars are correct wrt the input vars.
(make-event
  `(defun spec-permutation-f (,@*permutation-f-input-vars* ,@*permutation-f-output-vars*)
     (declare (xargs ;; :guard (and ,@(acl2::make-bitp-claims *permutation-f-input-vars*)
                     ;;             ,@(acl2::make-bitp-claims *permutation-f-output-vars*)
                     ;;             ) ; todo: put back
                :verify-guards nil ; todo put back
                :guard-hints (("Goal" :do-not '(preprocess) :in-theory (e/d (acl2::unsigned-byte-p-becomes-bitp)
                                                                            (bitp acl2::bitp-becomes-unsigned-byte-p))))))
     (equal (list ,@*permutation-f-output-vars*)
            (sha3::keccak-f 1600 (list ,@*permutation-f-input-vars*)))))

;; Lift the R1CS into logic (but do not solve the constraints yet):
(local
  (r1cs::lift-r1cs *keccak256-permutation-f*
                   (r1cs-constraint-list-vars (aleo::keccak256-permutation-f--constraints))
                   ;; todo: only include the constraints that we need?
                   (aleo::keccak256-permutation-f--constraints)
                   8444461749428370424248824938781546531375899335154063827935233455917409239041
                   :remove-rules '(pfield::neg-of-mul-when-constant ;makes it harder to move terms to the other side?
                                   pfield::equal-of-add-of-add-of-neg-arg2-arg2 ;for now, to try to combine more stuff
                                   pfield::add-commutative-2-axe
                                   pfield::add-commutative-axe)
                   :extra-rules '(bitp-idiom
                                  pfield::introduce-bitp-alt-2-alt
                                  pfield::introduce-bitp-alt-2
                                  primes::primep-of-bls12-377-scalar-field-prime-constant
                                  ;; acl2::bool-fix-when-booleanp
                                  acl2::booleanp-of-bitp
                                  ;;pfield::mul-of-2
                                  bitxor-idiom-1
                                  bitxor-idiom-2
                                  bitxor-idiom-1-alt
                                  bitxor-idiom-2-alt
                                  bitnot-idiom-1
                                  ;; bitnot-idiom-2 ; todo
                                  )))


;; Assumes:
;; 1. The R1CS holds
;; 2. x0 is the constant 1
;; 3. All the vars are field elements
;; Proves that the spec (spec-permutation-f) holds.
(acl2::prove-implication-with-r1cs-prover
  (acl2::make-conjunction-dag! (acl2::make-term-into-dag-basic! '(equal |x0| '1) ; x0 is always equal to 1 !
                                                                nil)
                               (acl2::make-conjunction-dag! (acl2::make-term-into-dag-basic!
                                                              ;; todo: tool could translate the fe-listp assumption
                                                              (pfield::gen-fe-listp-assumption (acl2::dag-vars *keccak256-permutation-f*)
                                                                                               ''8444461749428370424248824938781546531375899335154063827935233455917409239041)
                                                              nil)
                                                            *keccak256-permutation-f*))
  `(spec-permutation-f ,@*permutation-f-input-vars* ,@*permutation-f-output-vars*)
  :tactic '(:seq (:rep :rewrite-top :subst) :rewrite)
  :print :brief
  :no-splitp t
 ;; todo: the tool should build the alist:
 ;; todo: better to use a custom instantiate-hyp function:
  ;; some of these may be needed only for ground proofs:
  :interpreted-function-alist
  (acl2::make-interpreted-function-alist
    '(neg pfield::add pfield::pos-fix BVCAT acl2::logapp ash ACL2::EXPT2$INLINE ACL2::LOGHEAD$INLINE ACL2::IMOD$INLINE INTEGER-RANGE-P POWER-OF-2P fep unsigned-byte-p getbit slice ACL2::LOGTAIL$INLINE ACL2::IFLOOR$INLINE bitnot sub bvnot lognot bitxor POWER-OF-2P ACL2::BVSHR ACL2::BVSHL TRUE-LIST-FIX
      acl2::booland
      acl2::bitxor$
      sha3::rc
      sha3::rc-aux
      update-nth
      sha3::iota-aux
      )
    (w state))
  :extra-global-rules *global-proof-rules*
  :no-print-fns '(fe-listp)
  :rule-lists '(;;First, solve and subsitute using all the bitxor and bitnot constraints.  Requires several rounds of substitution:
                (;; These introduce BITXOR (not all of these are used):
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
                 pfield::equal-of-1-and-add-when-bitp-arg2
                 bitxor-idiom-1
                 bitxor-idiom-2
                 bitxor-idiom-1-alt
                 bitxor-idiom-2-alt
                 bitnot-idiom-1
                 bitnot-idiom-2
                 bitand-idiom-1
                 ;; needed to relieve hyps when rewriting top-level constraints
                 bitp-of-add-of-1-and-neg
                 bitp-of-add-of-neg-and-1
                 bitp-of-mul
                 )
                ;; open the spec:
                (spec-permutation-f
                  ;;rnd-with-rc
                  ;;iota-with-rc
                  sha3::iota
                  sha3::iota-aux2-base sha3::iota-aux2-unroll
                  sha3::iota-aux-base sha3::iota-aux-unroll
                  sha3::get-lane
                  sha3::set-lane
                  sha3::nth-bit
                  sha3::update-bit
                  sha3::update-nth-bit
                  sha3::update-nth-lane
                  sha3::update-nth-plane
                  sha3::chi
                  sha3::chi-planes-base sha3::chi-planes-unroll
                  sha3::chi-lanes-base sha3::chi-lanes-unroll
                  sha3::chi-lane-base sha3::chi-lane-unroll
                  sha3::theta
                  sha3::theta-planes-base sha3::theta-planes-unroll
                  sha3::theta-lanes-base sha3::theta-lanes-unroll
                  sha3::theta-lane-base sha3::theta-lane-unroll
                  sha3::theta-d-lanes-base sha3::theta-d-lanes-unroll
                  sha3::theta-d-lane-base sha3::theta-d-lane-unroll
                  sha3::theta-d
                  sha3::theta-c
                  sha3::theta-c-lanes-base sha3::theta-c-lanes-unroll
                  sha3::theta-c-lane-base sha3::theta-c-lane-unroll
                  sha3::rho
                  sha3::rho-aux-aux-base sha3::rho-aux-aux-unroll
                  sha3::rho-aux-base sha3::rho-aux-unroll
                  sha3::pi-fn
                  sha3::pi-planes-base sha3::pi-planes-unroll
                  sha3::pi-lanes-base sha3::pi-lanes-unroll
                  acl2::bitxor$ ; todo: add these 2 to a basic rule set
                  acl2::bitand$
                  sha3::a sha3::nth-lane sha3::nth-plane sha3::nth-bit
                  sha3::bit-string-to-plane
                  sha3::bits-to-state-array
                  sha3::map-bit-string-to-plane-base
                  sha3::map-bit-string-to-plane-unroll
                  acl2::group-base
                               ;acl2::group-unroll
                  acl2::atom
                  acl2::consp-of-cons
                  acl2::nthcdr-of-cons
                  acl2::firstn-base-1 acl2::firstn-base-2 ; combine these?
                               ;acl2::firstn-unroll
                  acl2::endp
                  acl2::car-cons acl2::cdr-cons
                  acl2::nth-of-cons-constant-version
                               ;;acl2::equal-of-cons-and-cons
                               ;;acl2::bitxor-commutative-2-increasing-axe
                               ;;acl2::bitxor-associative
                  acl2::bitxor-of-1-becomes-bitnot-arg2
                               ;;acl2::update-nth-base acl2::update-nth-unroll ; since we have a cons nest on one side an update-nth on the other side
                               ;;acl2::nth-update-nth-safe
                               ;acl2::bitxor-of-bitnot-arg1
                               ;acl2::bitxor-of-bitnot-arg2
                  sha3::keccak-f
                  sha3::keccak-p
                  sha3::keccak-p-aux-base
                  sha3::keccak-p-aux-unroll
                  sha3::rnd
                  sha3::state-array-to-bits
                  sha3::map-plane-to-bit-string-base
                  sha3::map-plane-to-bit-string-unroll
                  sha3::plane-to-bit-string
                  acl2::ungroup-base
                  acl2::ungroup-unroll
                  acl2::take-of-0
                  acl2::take-of-cons-when-posp
                               ;acl2::take-opener-when-not-zp
                  acl2::append-of-cons
                  acl2::append-of-nil-arg1
                               ;;acl2::equal-of-cons-and-cons
                  sha3::rc
                  sha3::rc-aux-base sha3::rc-aux-unroll
                               ;;acl2::bitxor-of-0-arg2
                  acl2::nth-update-nth-safe ; instead of opening update-nth...
                  acl2::update-nth-of-cons
                  acl2::update-nth-of-update-nth-same
                  acl2::update-nth-of-0-and-cons
                  acl2::take-of-append
                  acl2::len-of-cons
                  acl2::append-to-nil
                  acl2::bitxor-of-0-arg2
                  acl2::group-of-cons
                  acl2::firstn-becomes-take
                  acl2::getbit-of-0-when-bitp
                  acl2::bitp-of-bitxor
                  )
                ;; try to normalize the xors:
                (acl2::bitxor-commutative-increasing-axe
                  acl2::bitxor-commutative-2-increasing-axe
                  acl2::bitxor-associative)

;; (
;;                  spec-permutation-f
;;                  ;rnd-with-rc
;;                  ;iota-with-rc
;;                  sha3::iota
;;                  sha3::iota-aux2-base sha3::iota-aux2-unroll
;;                  sha3::iota-aux-base sha3::iota-aux-unroll
;;                  sha3::get-lane
;;                  sha3::set-lane
;;                  sha3::nth-bit
;;                  sha3::update-bit
;;                  sha3::update-nth-bit
;;                  sha3::update-nth-lane
;;                  sha3::update-nth-plane
;;                  sha3::chi
;;                  sha3::chi-planes-base sha3::chi-planes-unroll
;;                  sha3::chi-lanes-base sha3::chi-lanes-unroll
;;                  sha3::chi-lane-base sha3::chi-lane-unroll
;;                  sha3::theta
;;                  sha3::theta-planes-base sha3::theta-planes-unroll
;;                  sha3::theta-lanes-base sha3::theta-lanes-unroll
;;                  sha3::theta-lane-base sha3::theta-lane-unroll
;;                  sha3::theta-d-lanes-base sha3::theta-d-lanes-unroll
;;                  sha3::theta-d-lane-base sha3::theta-d-lane-unroll
;;                  sha3::theta-d
;;                  sha3::theta-c
;;                  sha3::theta-c-lanes-base sha3::theta-c-lanes-unroll
;;                  sha3::theta-c-lane-base sha3::theta-c-lane-unroll
;;                  sha3::rho
;;                  sha3::rho-aux-aux-base sha3::rho-aux-aux-unroll
;;                  sha3::rho-aux-base sha3::rho-aux-unroll
;;                  sha3::pi-fn
;;                  sha3::pi-planes-base sha3::pi-planes-unroll
;;                  sha3::pi-lanes-base sha3::pi-lanes-unroll
;;                  acl2::bitxor$ ; todo: add these 2 to a basic rule set
;;                  acl2::bitand$
;;                  sha3::a sha3::nth-lane sha3::nth-plane sha3::nth-bit
;;                  sha3::bit-string-to-plane
;;                  sha3::bits-to-state-array
;;                  sha3::map-bit-string-to-plane-base
;;                  sha3::map-bit-string-to-plane-unroll
;;                  acl2::group-base acl2::group-unroll
;;                  acl2::atom
;;                  acl2::consp-of-cons
;;                  acl2::nthcdr-of-cons
;;                  acl2::firstn-base-1 acl2::firstn-base-2 acl2::firstn-unroll
;;                  acl2::endp
;;                  acl2::car-cons acl2::cdr-cons
;;                  acl2::nth-of-cons-constant-version
;;                  ;acl2::equal-of-cons-and-cons
;;                  ;acl2::bitxor-commutative-2-increasing-axe
;;                  ;acl2::bitxor-associative
;;                  acl2::bitxor-of-1-becomes-bitnot-arg2
;;                  ;acl2::update-nth-base acl2::update-nth-unroll ; since we have a cons nest on one side an update-nth on the other side
;;                  ;;acl2::nth-update-nth-safe
;;                  acl2::bitxor-of-bitnot-arg1
;;                  acl2::bitxor-of-bitnot-arg2
;;                  sha3::keccak-f
;;                  sha3::keccak-p
;;                  sha3::keccak-p-aux-base
;;                  sha3::keccak-p-aux-unroll
;;                  sha3::rnd
;;                  sha3::state-array-to-bits
;;                  ;sha3::map-plane-to-bit-string-base
;;                  ;sha3::map-plane-to-bit-string-unroll
;;                  sha3::plane-to-bit-string
;;                  acl2::ungroup-base
;;                  acl2::ungroup-unroll
;;                  acl2::take-opener-when-not-zp
;;                  acl2::append-of-cons
;;                  acl2::append-of-nil-arg1
;;                  acl2::take-of-0
;;                  ;acl2::equal-of-cons-and-cons
;;                  sha3::rc
;;                  ;sha3::rc-aux-base sha3::rc-aux-unroll
;;                  ;acl2::bitxor-of-0-arg2
;;                  acl2::nth-update-nth-safe ; instead of opening update-nth...
;;                  )
))
