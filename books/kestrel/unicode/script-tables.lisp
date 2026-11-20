; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "runs")

(include-book "xdoc/alter" :dir :system) ; for XDOC::WITHOUT-XDOC

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ script-tables
  :parents (tables)
  :short "The values of the @('Script') property,
          and tables of runs of code points
          that have the same script or the same script extensions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('Script') property assigns to every code point
     one script, such as @('Latin') or @('Greek') [UAX #24].
     Three of its values are not scripts in the ordinary sense:
     @('Common'), for the characters that several scripts use,
     such as digits and punctuation;
     @('Inherited'), for the combining marks
     that take the script of the character they apply to;
     and @('Unknown'), which is the value of the code points
     that are unassigned, private-use, noncharacters or surrogates.")
   (xdoc::p
    "The @('Script_Extensions') property assigns to every code point
     a set of scripts: the scripts that the character is used with.
     For most code points it is the set of the one script
     that the @('Script') property gives.")
   (xdoc::p
    "Each value has a long name, such as @('Latin'),
     which the file @('Scripts.txt')
     of the Unicode Character Database uses,
     and a four-letter code, such as @('Latn'),
     which the file @('ScriptExtensions.txt') uses.
     The code is the one that ISO 15924 gives to the script.
     Both are in the file @('PropertyValueAliases.txt').")
   (xdoc::p
    "The type of the values is defined from one table,
     @('*script-table*'), which has the code and the long name
     of every script of every supported version of Unicode.
     A script that a later version adds
     has no code points in the earlier versions.
     The book of each generated table checks the table
     against the file @('PropertyValueAliases.txt') of its version.")
   (xdoc::p
    "Both properties are represented as lists of @(see runs)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection script-table
  :short "The codes and the long names of the scripts."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each entry of the table is the four-letter code of a script
     and its long name,
     as in the file @('PropertyValueAliases.txt')
     of the Unicode Character Database,
     in the order of that file, which is the order of the codes.
     The table has the scripts of Unicode 18.0.0;
     no script of an earlier supported version is missing from it.")
   (xdoc::p
    "The type @(tsee script) has one value for each entry.
     The keyword of the value, and the name of its constructor,
     come from the long name:
     the entry of @('Old_Hungarian') gives the value
     @('(script-old-hungarian)'), of kind @(':old-hungarian').
     The functions here compute those names from the table,
     for the macros that define the type and the functions on it."))

  (defconst *script-table*
    '(("Adlm" "Adlam")
    ("Aghb" "Caucasian_Albanian")
    ("Ahom" "Ahom")
    ("Arab" "Arabic")
    ("Armi" "Imperial_Aramaic")
    ("Armn" "Armenian")
    ("Avst" "Avestan")
    ("Bali" "Balinese")
    ("Bamu" "Bamum")
    ("Bass" "Bassa_Vah")
    ("Batk" "Batak")
    ("Beng" "Bengali")
    ("Berf" "Beria_Erfe")
    ("Bhks" "Bhaiksuki")
    ("Bopo" "Bopomofo")
    ("Brah" "Brahmi")
    ("Brai" "Braille")
    ("Bugi" "Buginese")
    ("Buhd" "Buhid")
    ("Cakm" "Chakma")
    ("Cans" "Canadian_Aboriginal")
    ("Cari" "Carian")
    ("Cham" "Cham")
    ("Cher" "Cherokee")
    ("Chrs" "Chorasmian")
    ("Copt" "Coptic")
    ("Cpmn" "Cypro_Minoan")
    ("Cprt" "Cypriot")
    ("Cyrl" "Cyrillic")
    ("Deva" "Devanagari")
    ("Diak" "Dives_Akuru")
    ("Dogr" "Dogra")
    ("Dsrt" "Deseret")
    ("Dupl" "Duployan")
    ("Egyp" "Egyptian_Hieroglyphs")
    ("Elba" "Elbasan")
    ("Elym" "Elymaic")
    ("Ethi" "Ethiopic")
    ("Gara" "Garay")
    ("Geor" "Georgian")
    ("Glag" "Glagolitic")
    ("Gong" "Gunjala_Gondi")
    ("Gonm" "Masaram_Gondi")
    ("Goth" "Gothic")
    ("Gran" "Grantha")
    ("Grek" "Greek")
    ("Gujr" "Gujarati")
    ("Gukh" "Gurung_Khema")
    ("Guru" "Gurmukhi")
    ("Hang" "Hangul")
    ("Hani" "Han")
    ("Hano" "Hanunoo")
    ("Hatr" "Hatran")
    ("Hebr" "Hebrew")
    ("Hira" "Hiragana")
    ("Hluw" "Anatolian_Hieroglyphs")
    ("Hmng" "Pahawh_Hmong")
    ("Hmnp" "Nyiakeng_Puachue_Hmong")
    ("Hrkt" "Katakana_Or_Hiragana")
    ("Hung" "Old_Hungarian")
    ("Ital" "Old_Italic")
    ("Java" "Javanese")
    ("Jurc" "Jurchen")
    ("Kali" "Kayah_Li")
    ("Kana" "Katakana")
    ("Kawi" "Kawi")
    ("Khar" "Kharoshthi")
    ("Khmr" "Khmer")
    ("Khoj" "Khojki")
    ("Kits" "Khitan_Small_Script")
    ("Knda" "Kannada")
    ("Krai" "Kirat_Rai")
    ("Kthi" "Kaithi")
    ("Lana" "Tai_Tham")
    ("Laoo" "Lao")
    ("Latn" "Latin")
    ("Lepc" "Lepcha")
    ("Limb" "Limbu")
    ("Lina" "Linear_A")
    ("Linb" "Linear_B")
    ("Lisu" "Lisu")
    ("Lyci" "Lycian")
    ("Lydi" "Lydian")
    ("Mahj" "Mahajani")
    ("Maka" "Makasar")
    ("Mand" "Mandaic")
    ("Mani" "Manichaean")
    ("Marc" "Marchen")
    ("Medf" "Medefaidrin")
    ("Mend" "Mende_Kikakui")
    ("Merc" "Meroitic_Cursive")
    ("Mero" "Meroitic_Hieroglyphs")
    ("Mlym" "Malayalam")
    ("Modi" "Modi")
    ("Mong" "Mongolian")
    ("Mroo" "Mro")
    ("Mtei" "Meetei_Mayek")
    ("Mult" "Multani")
    ("Mymr" "Myanmar")
    ("Nagm" "Nag_Mundari")
    ("Nand" "Nandinagari")
    ("Narb" "Old_North_Arabian")
    ("Nbat" "Nabataean")
    ("Newa" "Newa")
    ("Nkoo" "Nko")
    ("Nshu" "Nushu")
    ("Ogam" "Ogham")
    ("Olck" "Ol_Chiki")
    ("Onao" "Ol_Onal")
    ("Orkh" "Old_Turkic")
    ("Orya" "Oriya")
    ("Osge" "Osage")
    ("Osma" "Osmanya")
    ("Ougr" "Old_Uyghur")
    ("Palm" "Palmyrene")
    ("Pauc" "Pau_Cin_Hau")
    ("Pcun" "Proto_Cuneiform")
    ("Perm" "Old_Permic")
    ("Phag" "Phags_Pa")
    ("Phli" "Inscriptional_Pahlavi")
    ("Phlp" "Psalter_Pahlavi")
    ("Phnx" "Phoenician")
    ("Plrd" "Miao")
    ("Prti" "Inscriptional_Parthian")
    ("Rjng" "Rejang")
    ("Rohg" "Hanifi_Rohingya")
    ("Runr" "Runic")
    ("Samr" "Samaritan")
    ("Sarb" "Old_South_Arabian")
    ("Saur" "Saurashtra")
    ("Seal" "Seal")
    ("Sgnw" "SignWriting")
    ("Shaw" "Shavian")
    ("Shrd" "Sharada")
    ("Sidd" "Siddham")
    ("Sidt" "Sidetic")
    ("Sind" "Khudawadi")
    ("Sinh" "Sinhala")
    ("Sogd" "Sogdian")
    ("Sogo" "Old_Sogdian")
    ("Sora" "Sora_Sompeng")
    ("Soyo" "Soyombo")
    ("Sund" "Sundanese")
    ("Sunu" "Sunuwar")
    ("Sylo" "Syloti_Nagri")
    ("Syrc" "Syriac")
    ("Tagb" "Tagbanwa")
    ("Takr" "Takri")
    ("Tale" "Tai_Le")
    ("Talu" "New_Tai_Lue")
    ("Taml" "Tamil")
    ("Tang" "Tangut")
    ("Tavt" "Tai_Viet")
    ("Tayo" "Tai_Yo")
    ("Telu" "Telugu")
    ("Tfng" "Tifinagh")
    ("Tglg" "Tagalog")
    ("Thaa" "Thaana")
    ("Thai" "Thai")
    ("Tibt" "Tibetan")
    ("Tirh" "Tirhuta")
    ("Tnsa" "Tangsa")
    ("Todr" "Todhri")
    ("Tols" "Tolong_Siki")
    ("Toto" "Toto")
    ("Tutg" "Tulu_Tigalari")
    ("Ugar" "Ugaritic")
    ("Vaii" "Vai")
    ("Vith" "Vithkuqi")
    ("Wara" "Warang_Citi")
    ("Wcho" "Wancho")
    ("Xpeo" "Old_Persian")
    ("Xsux" "Cuneiform")
    ("Yezi" "Yezidi")
    ("Yiii" "Yi")
    ("Zanb" "Zanabazar_Square")
    ("Zinh" "Inherited")
    ("Zyyy" "Common")
    ("Zzzz" "Unknown")))

  (defun script-table-keyword (name)
    (declare (xargs :mode :program))
    (intern (acl2::string-upcase (acl2::substitute #\- #\_ name)) "KEYWORD"))

  (defun script-table-constructor (name)
    (declare (xargs :mode :program))
    (intern-in-package-of-symbol
     (concatenate 'string
                  "SCRIPT-"
                  (acl2::string-upcase (acl2::substitute #\- #\_ name)))
     'script))

  (defun script-table-sum-cases (table)
    (declare (xargs :mode :program))
    (if (endp table)
        nil
      (cons (list (script-table-keyword (second (car table))) nil)
            (script-table-sum-cases (cdr table)))))

  (defun script-table-case-args (table codep)
    (declare (xargs :mode :program))
    (if (endp table)
        nil
      (list* (script-table-keyword (second (car table)))
             (if codep (first (car table)) (second (car table)))
             (script-table-case-args (cdr table) codep))))

  (defun script-table-constructors (table)
    (declare (xargs :mode :program))
    (if (endp table)
        nil
      (cons (cons (first (car table))
                  (script-table-constructor (second (car table))))
            (script-table-constructors (cdr table)))))

  (defun script-table-calls (table)
    (declare (xargs :mode :program))
    (if (endp table)
        nil
      (cons (list (script-table-constructor (second (car table))))
            (script-table-calls (cdr table)))))

  (defun script-table-items (table)
    (declare (xargs :mode :program))
    (if (endp table)
        nil
      (cons `(xdoc::li ,(concatenate
                         'string
                         "@('" (first (car table)) "'), @('"
                         (second (car table)) "'): @('("
                         (acl2::string-downcase
                          (symbol-name
                           (script-table-constructor (second (car table)))))
                         ")')."))
            (script-table-items (cdr table))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro def-script-type ()
  `(xdoc::without-xdoc
    (fty::deftagsum script
      ,@(script-table-sum-cases *script-table*)
      :pred script-p)))

(def-script-type)

(defmacro def-script-topic ()
  `(defxdoc script
     :parents (script-tables)
     :short "Fixtype of the values of the @('Script') property."
     :long
     (xdoc::topstring
      (xdoc::p
       "There is one value for each entry of @('*script-table*'):
        see @(see script-table) for how the values are named.
        The values, with their four-letter codes first,
        their long names second, and their constructors third, are:")
      (xdoc::ul ,@(script-table-items *script-table*))
      (xdoc::p
       "@('Katakana_Or_Hiragana') is a value
        that no code point has in the supported versions,
        in either property.")
      (xdoc::p
       "The type is introduced with @(tsee fty::deftagsum).
        The constructors have no arguments.
        The recognizer of the type is @('script-p'),
        its fixer is @('script-fix'),
        and its equivalence is @('script-equiv').
        The function @('script-kind')
        returns the keyword of a value, such as @(':latin'),
        and the macro @('script-case')
        distinguishes the values by their keywords.")
      (xdoc::p
       "These functions and macros
        have no documentation topics of their own.
        @(tsee fty::deftagsum) generates 543 topics for this type,
        three of them for each value,
        and none of them would say more than this topic does.
        So we turn them off, with @('xdoc::without-xdoc')."))))

(def-script-topic)

;;;;;;;;;;;;;;;;;;;;

(defmacro def-script-code ()
  `(define script-code ((script script-p))
     :returns (code stringp)
     :short "The four-letter code of a script."
     :long
     (xdoc::topstring
      (xdoc::p
       "This is the short name of the value
        in the file @('PropertyValueAliases.txt')
        of the Unicode Character Database,
        which is the code of the script in ISO 15924."))
     (script-case script ,@(script-table-case-args *script-table* t))
     :hooks (:fix)))

(def-script-code)

;;;;;;;;;;;;;;;;;;;;

(defmacro def-script-name ()
  `(define script-name ((script script-p))
     :returns (name stringp)
     :short "The long name of a script."
     :long
     (xdoc::topstring
      (xdoc::p
       "This is the long name of the value
        in the file @('PropertyValueAliases.txt')
        of the Unicode Character Database,
        with underscores between its words, as in that file."))
     (script-case script ,@(script-table-case-args *script-table* nil))
     :hooks (:fix)))

(def-script-name)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist script-list
  :short "Fixtype of lists of scripts."
  :elt-type script
  :true-listp t
  :elementp-of-nil nil
  :pred script-listp)

;;;;;;;;;;;;;;;;;;;;

(defmacro def-script-values ()
  `(define script-values ()
     :returns (scripts script-listp)
     :short "The values of the @('Script') property."
     :long
     (xdoc::topstring
      (xdoc::p
       "They are in the order of @('*script-table*').
        Every value is in the list, once."))
     (list ,@(script-table-calls *script-table*))

     ///

     (defrule no-duplicatesp-equal-of-script-values
       (no-duplicatesp-equal (script-values)))

     (defrule member-equal-of-script-fix-and-values
       (member-equal (script-fix script) (script-values))
       :use (:instance script-kind-possibilities (x script))
       :disable (script-values
                 script-kind-possibilities))

     (defrulel script-p-when-member-equal-of-values
       (implies (member-equal script (script-values))
                (script-p script))
       :enable member-equal)

     (in-theory (disable (:e script-values)))

     (defrule member-equal-of-script-values
       (iff (member-equal script (script-values))
            (script-p script))
       :disable (script-values
                 member-equal-of-script-fix-and-values)
       :use member-equal-of-script-fix-and-values)))

(def-script-values)

;;;;;;;;;;;;;;;;;;;;

(define script-table-agrees-p ((entries true-listp))
  :returns (yes/no booleanp)
  :short "Check that each of the given pairs of a code and a long name
          is an entry of the table of the scripts."
  :long
  (xdoc::topstring
   (xdoc::p
    "The book of each generated table calls this
     on the pairs of the file @('PropertyValueAliases.txt') of its version.
     So a script that is missing from @('*script-table*'),
     or whose code or name is not written there as in the file,
     stops the certification of that book."))
  (or (endp entries)
      (and (member-equal (car entries) *script-table*)
           (script-table-agrees-p (cdr entries))))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruns script
  :property "Script"
  :value-type script
  :value-pred script-p
  :value-fix script-fix
  :default (script-unknown))

;;;;;;;;;;;;;;;;;;;;

(defruns script-extensions
  :property "Script_Extensions"
  :value-type script-list
  :value-pred script-listp
  :value-fix script-list-fix
  :default (list (script-unknown))
  :elements t
  :element-pred script-p
  :element-fix script-fix)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection script-run-table
  :short "Write a list of runs of @('Script')
          or of @('Script_Extensions') compactly."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each run of @('Script') is written
     as the minimum code point, the maximum code point,
     and the four-letter code of the script, as a string
     (see @(tsee script-code)).
     Each run of @('Script_Extensions') is written
     as the two code points
     followed by the codes of the scripts of the set:")
   (xdoc::codeblock
    "(script-run-table"
    " (#x0041 #x005A \"Latn\")"
    " (#x005B #x0060 \"Zyyy\"))"
    ""
    "(script-extensions-run-table"
    " (#x0041 #x005A \"Latn\")"
    " (#x3001 #x3003 \"Bopo\" \"Hang\" \"Hani\" \"Hira\" \"Kana\" \"Yiii\"))")
   (xdoc::p
    "See @(see run-tables) for what these expand to."))

  (defmacro def-script-constructors ()
    `(defconst *script-constructors*
       ',(script-table-constructors *script-table*)))

  (def-script-constructors)

  (defmacro script-run-table (&rest entries)
    `(list ,@(run-table-forms entries
                              :value
                              *script-constructors*
                              'script-run
                              'script-run-table)))

  (defmacro script-extensions-run-table (&rest entries)
    `(list ,@(run-table-forms entries
                              :elements
                              *script-constructors*
                              'script-extensions-run
                              'script-extensions-run-table))))
