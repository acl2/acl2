; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/portcullis" :dir :system)
(include-book "std/portcullis" :dir :system)
(include-book "../portcullis")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "ALEOBFT-PROPOSALS"
    (append (set-difference-eq *std-pkg-symbols*
                               '(block
                                 char
                                 check-type
                                 closure
                                 compile
                                 event
                                 function
                                 functionp
                                 import
                                 lexp
                                 make-package
                                 package
                                 packagep
                                 parse-integer
                                 pprint-indent
                                 program
                                 type
                                 typep
                                 value
                                 values))
            '(any
              any-p
              assert-equal
              bebits=>nat
              bit-list-fix
              bit-listp
              bfix
              bool
              boolean-list-fix
              boolean-resultp
              character-list-resultp
              character-resultp
              define-sk
              defmacro+
              defund-sk
              defxdoc+
              e/d*
              enable*
              impossible
              int
              integers-from-to
              integer-resultp
              lebits=>nat
              lnfix
              logext
              loghead
              lookup-equal
              maybe-msgp
              maybe-natp
              maybe-pseudo-event-formp
              maybe-string-fix
              maybe-string-resultp
              maybe-stringp
              msg-listp
              nat
              nat-list
              nat-list-fix
              nat-list-resultp
              nat-option
              nat-optionp
              nat-option-fix
              nat-option-list
              nat-option-listp
              nat-option-resultp
              nat-option-list-resultp
              nati-case
              nati-finite
              nati-finite->get
              nati-infinity
              natoption/natoptionlist-case
              natoption/natoptionlist-one
              natoption/natoptionlist-list
              natoption/natoptionlist-resultp
              nat-resultp
              nat-setp
              nat/natlist-case
              nat/natlist-one
              nat/natlist-list
              nat/natlist-resultp
              nat=>bebits
              nat=>lebits
              nat=>lebits*
              nats=>string
              packn-pos
              pos
              pos-fix
              pos-list
              pos-listp
              pos-setp
              pos-set->=-pos
              pos-set-max
              prefixp
              pseudo-event-formp
              return-raw
              sbyte8
              sbyte16
              sbyte32
              sbyte64
              sbyte128
              sbyte8p
              sbyte16p
              sbyte32p
              sbyte64p
              sbyte128p
              seq
              seq-backtrack
              str-fix
              string-list-resultp
              string-resultp
              string-stringlist-alistp
              string=>nats
              ubyte8
              ubyte16
              ubyte32
              ubyte64
              ubyte128
              ubyte8p
              ubyte16p
              ubyte32p
              ubyte64p
              ubyte128p
              unsigned-byte-listp
              fty::info
              fty::okf
              fty::reserr
              fty::reserrf
              fty::reserrf-push
              fty::reserrp
              fty::reserr-option
              fty::reserr-optionp
              fty::stack
              str::string-list
              std::deffixer
              std::defret-mutual
              aleobft::lists-noforkp)))
