// Unicode Library
//
// Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
//
// License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
//
// Author: Eric McCarthy (bendyarm on GitHub)

//! Write what the Unicode crates that rustc uses say about every code point,
//! in the format of ../../dump.lisp, for comparison with the ACL2 library.
//!
//! This one source file is built by one Cargo package for each version of
//! Unicode (v16.0.0, v17.0.0 and so on, in this directory), which pins the
//! versions of the crates that implement that version of Unicode.  Usage:
//!
//!     oracle VERSION code-points > FILE
//!     oracle VERSION pairs PAIRS-FILE
//!     oracle VERSION stream-safe STREAM-SAFE-FILE
//!     oracle VERSION display-order
//!
//! VERSION, e.g. 16.0.0, must be the version of Unicode that the crates
//! implement; the program stops if a crate says otherwise.
//!
//! The first form writes a header line and one line for each code point.
//! Each column is named `property@crate`.  A surrogate is not a `char`,
//! so its fields are all `!`, which means "cannot say".
//! Besides the crates that rustc uses, the columns come from
//! unicode-script (Script and Script_Extensions), unicode-bidi (Bidi_Class)
//! and unicode-security (Identifier_Status), for the versions of Unicode
//! for which those crates have a release, and from the emoji status of
//! unicode-properties.
//!
//! The second form reads a file written by DUMP-PAIRS of ../../dump.lisp,
//! with lines `first second composite nfc...` (composite is `-` if the two
//! code points do not compose), and checks each line against
//! unicode-normalization.  It exits with status 1 if any line differs.
//!
//! The third form reads a file written by DUMP-STREAM-SAFE of
//! ../../dump.lisp, with lines `sequence > result`, and checks that the
//! result is what the stream_safe iterator of unicode-normalization gives
//! for the sequence.  It exits with status 1 if any line differs.
//!
//! The fourth form, which needs unicode-bidi, tests a claim that the
//! library makes and does not prove, because it does not have the Unicode
//! Bidirectional Algorithm: a text with no character of the six classes
//! that RIGHT-TO-LEFT-CODE-POINT-P of ../../../skeleton.lisp recognizes
//! is displayed, in a paragraph from left to right, in the order in which
//! it is stored.  See the function display_order.

use std::io::{self, BufRead, BufWriter, Write};
use unicode_normalization::char::{canonical_combining_class, compose};
use unicode_normalization::UnicodeNormalization;

const USAGE: &str = "usage: oracle VERSION code-points \
                     | oracle VERSION pairs FILE \
                     | oracle VERSION stream-safe FILE \
                     | oracle VERSION display-order";

fn die(message: &str) -> ! {
    eprintln!("oracle: error: {message}");
    std::process::exit(2)
}

fn parse_version(s: &str) -> (u64, u64, u64) {
    let parts: Vec<u64> = s
        .split('.')
        .map(|p| p.parse().unwrap_or_else(|_| die("bad version")))
        .collect();
    if parts.len() != 3 {
        die("the version must be written in full, like 16.0.0");
    }
    (parts[0], parts[1], parts[2])
}

fn check_version(name: &str, actual: (u64, u64, u64), expected: (u64, u64, u64)) {
    if actual != expected {
        die(&format!(
            "{name} implements Unicode {}.{}.{}, not {}.{}.{}",
            actual.0, actual.1, actual.2, expected.0, expected.1, expected.2
        ));
    }
    eprintln!(
        "oracle: {name} implements Unicode {}.{}.{}",
        actual.0, actual.1, actual.2
    );
}

/// The set of the code points that match a Unicode property class,
/// according to regex-syntax.
#[cfg(feature = "have-regex-syntax")]
fn regex_syntax_set(property: &str) -> Vec<bool> {
    use regex_syntax::hir::{Class, HirKind};
    let pattern = format!(r"\p{{{property}}}");
    let hir = regex_syntax::Parser::new()
        .parse(&pattern)
        .unwrap_or_else(|e| die(&format!("regex-syntax: {e}")));
    let mut set = vec![false; 0x110000];
    match hir.kind() {
        HirKind::Class(Class::Unicode(class)) => {
            for range in class.iter() {
                for cp in (range.start() as u32)..=(range.end() as u32) {
                    set[cp as usize] = true;
                }
            }
        }
        _ => die("regex-syntax: not a Unicode class"),
    }
    set
}

fn join(chars: impl Iterator<Item = char>) -> String {
    chars
        .map(|c| (c as u32).to_string())
        .collect::<Vec<_>>()
        .join(" ")
}

fn flag(b: bool) -> &'static str {
    if b {
        "1"
    } else {
        "0"
    }
}

/// The two-letter abbreviation of a General_Category of unicode-properties,
/// from the name of the variant.
fn general_category_abbreviation(c: char) -> &'static str {
    use unicode_properties::UnicodeGeneralCategory;
    let name = format!("{:?}", c.general_category());
    match name.as_str() {
        "UppercaseLetter" => "Lu",
        "LowercaseLetter" => "Ll",
        "TitlecaseLetter" => "Lt",
        "ModifierLetter" => "Lm",
        "OtherLetter" => "Lo",
        "NonspacingMark" => "Mn",
        "SpacingMark" => "Mc",
        "EnclosingMark" => "Me",
        "DecimalNumber" => "Nd",
        "LetterNumber" => "Nl",
        "OtherNumber" => "No",
        "ConnectorPunctuation" => "Pc",
        "DashPunctuation" => "Pd",
        "OpenPunctuation" => "Ps",
        "ClosePunctuation" => "Pe",
        "InitialPunctuation" => "Pi",
        "FinalPunctuation" => "Pf",
        "OtherPunctuation" => "Po",
        "MathSymbol" => "Sm",
        "CurrencySymbol" => "Sc",
        "ModifierSymbol" => "Sk",
        "OtherSymbol" => "So",
        "SpaceSeparator" => "Zs",
        "LineSeparator" => "Zl",
        "ParagraphSeparator" => "Zp",
        "Control" => "Cc",
        "Format" => "Cf",
        "Surrogate" => "Cs",
        "PrivateUse" => "Co",
        "Unassigned" => "Cn",
        _ => die(&format!("unicode-properties: unknown category {name}")),
    }
}

/// The four-letter code of a script according to unicode-script.
/// The crate gives the empty string as the code of the script Unknown,
/// whose code in PropertyValueAliases.txt is Zzzz.
#[cfg(feature = "have-unicode-script")]
fn script_code(script: unicode_script::Script) -> &'static str {
    if script == unicode_script::Script::Unknown {
        "Zzzz"
    } else {
        script.short_name()
    }
}

/// The Script_Extensions of a character according to unicode-script,
/// as the four-letter codes of the scripts in the order of the codes.
/// The crate has special values for the sets of one script that are
/// Common, Inherited and Unknown.
#[cfg(feature = "have-unicode-script")]
fn script_extension_codes(c: char) -> String {
    use unicode_script::{Script, UnicodeScript};
    let extension = c.script_extension();
    if extension.is_common() {
        return script_code(Script::Common).to_string();
    }
    if extension.is_inherited() {
        return script_code(Script::Inherited).to_string();
    }
    if extension.is_empty() {
        return script_code(Script::Unknown).to_string();
    }
    let mut codes: Vec<&str> = extension.iter().map(script_code).collect();
    codes.sort_unstable();
    codes.join(" ")
}

/// The augmented script set of a character (UTS #39, Section 5.1)
/// according to unicode-security: ALL, or the four-letter codes of the
/// scripts, in the order of the codes, and then those of Hanb, Jpan and
/// Kore that the set has.  The crate does not have the writing system
/// Hntl, which UTS #39 has from Unicode 18.0.0 on.  And for a character
/// whose Script_Extensions is the one script Unknown, the crate has the
/// empty set; we write Zzzz, the code of that script.
#[cfg(feature = "have-unicode-security")]
fn augmented_script_set_codes(c: char) -> String {
    use unicode_security::mixed_script::AugmentedScriptSet;
    let set = AugmentedScriptSet::from(c);
    if set.is_all() {
        return "ALL".to_string();
    }
    if set.is_empty() {
        return script_code(unicode_script::Script::Unknown).to_string();
    }
    let mut codes: Vec<&str> = set.base.iter().map(script_code).collect();
    codes.sort_unstable();
    if set.hanb {
        codes.push("Hanb");
    }
    if set.jpan {
        codes.push("Jpan");
    }
    if set.kore {
        codes.push("Kore");
    }
    codes.join(" ")
}

/// The skeleton of a string according to unicode-security, as code
/// points in decimal separated by spaces.  Up to its version for
/// Unicode 16.0.0, the crate does not remove the default ignorable code
/// points; from its version for Unicode 18.0.0 on, it does, and this
/// is the internal skeleton of UTS #39, Section 4.
#[cfg(feature = "have-unicode-security")]
fn skeleton_code_points(s: &str) -> String {
    unicode_security::skeleton(s)
        .map(|c| (c as u32).to_string())
        .collect::<Vec<_>>()
        .join(" ")
}

/// The Bidi_Class of a character according to unicode-bidi, or `!` (not
/// compared) for an unassigned code point.  For those, the crate does not
/// follow the defaults of DerivedBidiClass.txt everywhere: in its version
/// for Unicode 16.0.0 it gives L where the default is BN (noncharacters
/// and unassigned default ignorable code points), and R to some of the
/// unassigned code points whose default is AL.
#[cfg(feature = "have-unicode-bidi")]
fn bidi_class_abbreviation(c: char) -> String {
    use unicode_properties::{GeneralCategory, UnicodeGeneralCategory};
    if c.general_category() == GeneralCategory::Unassigned {
        return "!".to_string();
    }
    format!("{:?}", unicode_bidi::bidi_class(c))
}

fn code_points(out: &mut impl Write) -> io::Result<()> {
    let mut columns = vec![
        "xids@unicode-ident",
        "xidc@unicode-ident",
        "rustc_id_start@rustc_lexer",
        "rustc_id_continue@rustc_lexer",
        "rustc_whitespace@rustc_lexer",
        "ccc@unicode-normalization",
        "nfd@unicode-normalization",
        "nfc@unicode-normalization",
        "nfkd@unicode-normalization",
        "nfkc@unicode-normalization",
        "gc@unicode-properties",
        "emoji_status@unicode-properties",
        "wspace@std",
    ];
    if cfg!(feature = "have-unicode-script") {
        columns.extend(["sc@unicode-script", "scx@unicode-script"]);
    }
    if cfg!(feature = "have-unicode-bidi") {
        columns.push("bc@unicode-bidi");
    }
    if cfg!(feature = "have-unicode-security") {
        columns.push("idst@unicode-security");
        columns.push("ass_no_hntl@unicode-security");
        if cfg!(feature = "unicode-security-removes-default-ignorables") {
            columns.push("skel@unicode-security");
            columns.push("skelm@unicode-security");
        } else {
            columns.push("skelk@unicode-security");
        }
    }
    if cfg!(feature = "have-unicode-xid") {
        columns.extend(["xids@unicode-xid", "xidc@unicode-xid"]);
    }
    if cfg!(feature = "have-regex-syntax") {
        columns.extend([
            "xids@regex-syntax",
            "xidc@regex-syntax",
            "pws@regex-syntax",
            "bidic@regex-syntax",
            "di@regex-syntax",
            "vs@regex-syntax",
            "jc@regex-syntax",
            "nchar@regex-syntax",
            "dep@regex-syntax",
            "pcm@regex-syntax",
            "psyn@regex-syntax",
            "ids@regex-syntax",
            "idc@regex-syntax",
            "emoji@regex-syntax",
            "epres@regex-syntax",
            "emod@regex-syntax",
            "ebase@regex-syntax",
            "ecomp@regex-syntax",
            "extpict@regex-syntax",
            "ri@regex-syntax",
            "wspace@regex-syntax",
        ]);
    }
    #[cfg(feature = "have-regex-syntax")]
    let sets = [
        regex_syntax_set("XID_Start"),
        regex_syntax_set("XID_Continue"),
        regex_syntax_set("Pattern_White_Space"),
        regex_syntax_set("Bidi_Control"),
        regex_syntax_set("Default_Ignorable_Code_Point"),
        regex_syntax_set("Variation_Selector"),
        regex_syntax_set("Join_Control"),
        regex_syntax_set("Noncharacter_Code_Point"),
        regex_syntax_set("Deprecated"),
        regex_syntax_set("Prepended_Concatenation_Mark"),
        regex_syntax_set("Pattern_Syntax"),
        regex_syntax_set("ID_Start"),
        regex_syntax_set("ID_Continue"),
        regex_syntax_set("Emoji"),
        regex_syntax_set("Emoji_Presentation"),
        regex_syntax_set("Emoji_Modifier"),
        regex_syntax_set("Emoji_Modifier_Base"),
        regex_syntax_set("Emoji_Component"),
        regex_syntax_set("Extended_Pictographic"),
        regex_syntax_set("Regional_Indicator"),
        regex_syntax_set("White_Space"),
    ];

    writeln!(out, "#cp;{}", columns.join(";"))?;
    for cp in 0..=0x10FFFFu32 {
        let Some(c) = char::from_u32(cp) else {
            writeln!(out, "{cp}{}", ";!".repeat(columns.len()))?;
            continue;
        };
        write!(
            out,
            "{cp};{};{};{};{};{};{};{};{};{};{};{};{:?};{}",
            flag(unicode_ident::is_xid_start(c)),
            flag(unicode_ident::is_xid_continue(c)),
            flag(ra_ap_rustc_lexer::is_id_start(c)),
            flag(ra_ap_rustc_lexer::is_id_continue(c)),
            flag(ra_ap_rustc_lexer::is_whitespace(c)),
            canonical_combining_class(c),
            join(std::iter::once(c).nfd()),
            join(std::iter::once(c).nfc()),
            join(std::iter::once(c).nfkd()),
            join(std::iter::once(c).nfkc()),
            general_category_abbreviation(c),
            unicode_properties::UnicodeEmoji::emoji_status(c),
            flag(c.is_whitespace()),
        )?;
        #[cfg(feature = "have-unicode-script")]
        write!(
            out,
            ";{};{}",
            script_code(unicode_script::UnicodeScript::script(&c)),
            script_extension_codes(c),
        )?;
        #[cfg(feature = "have-unicode-bidi")]
        write!(out, ";{}", bidi_class_abbreviation(c))?;
        #[cfg(feature = "have-unicode-security")]
        {
            use unicode_security::GeneralSecurityProfile;
            write!(out, ";{}", flag(c.identifier_allowed()))?;
            write!(out, ";{}", augmented_script_set_codes(c))?;
            write!(out, ";{}", skeleton_code_points(&c.to_string()))?;
            #[cfg(feature = "unicode-security-removes-default-ignorables")]
            {
                let marked: String =
                    ['a', c, '\u{301}', '\u{327}'].iter().collect();
                write!(out, ";{}", skeleton_code_points(&marked))?;
            }
        }
        #[cfg(feature = "have-unicode-xid")]
        write!(
            out,
            ";{};{}",
            flag(unicode_xid::UnicodeXID::is_xid_start(c)),
            flag(unicode_xid::UnicodeXID::is_xid_continue(c)),
        )?;
        #[cfg(feature = "have-regex-syntax")]
        for set in &sets {
            write!(out, ";{}", flag(set[cp as usize]))?;
        }
        writeln!(out)?;
    }
    Ok(())
}

fn pairs(path: &str) -> io::Result<bool> {
    let file = std::fs::File::open(path)?;
    let (mut lines, mut skipped, mut differences) = (0u64, 0u64, 0u64);
    for line in io::BufReader::new(file).lines() {
        let line = line?;
        if line.starts_with('#') {
            continue;
        }
        lines += 1;
        let fields: Vec<&str> = line.split(' ').collect();
        if fields.len() < 4 {
            die(&format!("bad line: {line}"));
        }
        let cp = |s: &str| -> Option<char> {
            char::from_u32(s.parse().unwrap_or_else(|_| die("bad number")))
        };
        let (Some(first), Some(second)) = (cp(fields[0]), cp(fields[1])) else {
            skipped += 1;
            continue;
        };
        let composite = match compose(first, second) {
            Some(c) => (c as u32).to_string(),
            None => "-".to_string(),
        };
        let nfc = join([first, second].into_iter().nfc());
        if composite != fields[2] || nfc != fields[3..].join(" ") {
            differences += 1;
            if differences <= 20 {
                println!("DIFFERENT: {line} (here: {composite} {nfc})");
            }
        }
    }
    println!(
        "pairs@unicode-normalization: {lines} pairs, \
         {skipped} skipped (surrogates), {differences} different"
    );
    Ok(differences == 0)
}

fn stream_safe(path: &str) -> io::Result<bool> {
    let file = std::fs::File::open(path)?;
    let (mut lines, mut skipped, mut differences) = (0u64, 0u64, 0u64);
    for line in io::BufReader::new(file).lines() {
        let line = line?;
        if line.starts_with('#') {
            continue;
        }
        lines += 1;
        let Some((sequence, result)) = line.split_once(" > ") else {
            die(&format!("bad line: {line}"));
        };
        let cp = |s: &str| -> Option<char> {
            char::from_u32(s.parse().unwrap_or_else(|_| die("bad number")))
        };
        let chars: Option<Vec<char>> = sequence.split(' ').map(cp).collect();
        let Some(chars) = chars else {
            skipped += 1;
            continue;
        };
        let here = join(chars.into_iter().stream_safe());
        if here != result {
            differences += 1;
            if differences <= 20 {
                println!("DIFFERENT: {line} (here: {here})");
            }
        }
    }
    println!(
        "stream-safe@unicode-normalization: {lines} sequences, \
         {skipped} skipped (surrogates), {differences} different"
    );
    Ok(differences == 0)
}

/// The explicit directional formatting characters.  They are default
/// ignorable, so the skeleton of UTS #39 removes them: the test below
/// compares the order of the other characters.
#[cfg(feature = "have-unicode-bidi")]
const EXPLICIT_FORMATTING: [char; 9] = [
    '\u{202A}', '\u{202B}', '\u{202C}', '\u{202D}', '\u{202E}', '\u{2066}',
    '\u{2067}', '\u{2068}', '\u{2069}',
];

/// Count the strings of 1 to MAX characters of ALPHABET, containing MUST
/// if it is given, that unicode-bidi displays, in a paragraph from left to
/// right, with their characters other than the explicit formatting ones
/// in another order than the one in which they are stored.
/// Return the number of strings, the number displayed in another order,
/// and the first of those with its display.
#[cfg(feature = "have-unicode-bidi")]
fn count_reordered(
    alphabet: &[char],
    must: Option<char>,
    max: usize,
) -> (u64, u64, Option<(String, String)>) {
    use unicode_bidi::{BidiInfo, Level};
    let kept = |s: &str| -> Vec<char> {
        s.chars().filter(|c| !EXPLICIT_FORMATTING.contains(c)).collect()
    };
    let (mut total, mut reordered, mut first) = (0u64, 0u64, None);
    for len in 1..=max {
        let mut digits = vec![0usize; len];
        'strings: loop {
            let s: String = digits.iter().map(|&i| alphabet[i]).collect();
            if must.map_or(true, |m| s.contains(m)) {
                total += 1;
                let info = BidiInfo::new(&s, Some(Level::ltr()));
                let para = &info.paragraphs[0];
                let shown = info.reorder_line(para, para.range.clone());
                if info.paragraphs.len() != 1 || kept(&shown) != kept(&s) {
                    reordered += 1;
                    first.get_or_insert((s.clone(), shown.into_owned()));
                }
            }
            for k in (0..len).rev() {
                digits[k] += 1;
                if digits[k] < alphabet.len() {
                    continue 'strings;
                }
                digits[k] = 0;
            }
            break;
        }
    }
    (total, reordered, first)
}

/// Test, with unicode-bidi, the claim about RIGHT-TO-LEFT-FREE-P of
/// ../../../skeleton.lisp.  The alphabet has twenty characters of sixteen
/// of the seventeen classes that the predicate allows; the seventeenth is
/// B, the paragraph separators, which only cut a text into paragraphs.
/// Every string of up to six of them must be displayed in the order in
/// which it is stored; and for each of the six classes that the predicate
/// excludes, some string of up to four characters with one character of
/// that class added to the alphabet must be displayed in another order.
#[cfg(feature = "have-unicode-bidi")]
fn display_order() -> bool {
    use unicode_bidi::BidiClass::*;
    let allowed = [
        ('a', L), ('b', L), ('1', EN), (' ', WS), ('!', ON), ('(', ON),
        (')', ON), ('+', ES), ('%', ET), (',', CS), ('\u{301}', NSM),
        ('\u{200B}', BN), ('\u{1}', BN), ('\t', S), ('\u{202A}', LRE),
        ('\u{202D}', LRO), ('\u{2066}', LRI), ('\u{2068}', FSI),
        ('\u{202C}', PDF), ('\u{2069}', PDI),
    ];
    let excluded = [
        ('\u{5D0}', R), ('\u{627}', AL), ('\u{663}', AN), ('\u{202B}', RLE),
        ('\u{202E}', RLO), ('\u{2067}', RLI),
    ];
    for (c, class) in allowed.iter().chain(excluded.iter()) {
        if unicode_bidi::bidi_class(*c) != *class {
            die("a character of the test is not of the expected class");
        }
    }
    let show = |s: &str| -> String {
        s.chars()
            .map(|c| format!("{:04X}", c as u32))
            .collect::<Vec<_>>()
            .join(" ")
    };
    let mut ok = true;
    let alphabet: Vec<char> = allowed.iter().map(|(c, _)| *c).collect();
    let (total, reordered, first) = count_reordered(&alphabet, None, 6);
    println!(
        "display-order@unicode-bidi: {total} strings without \
         R, AL, AN, RLE, RLO, RLI: {reordered} displayed in another order"
    );
    if let Some((s, shown)) = first {
        println!("    {} is displayed as {}", show(&s), show(&shown));
        ok = false;
    }
    for (c, class) in excluded {
        let mut with = alphabet.clone();
        with.push(c);
        let (total, reordered, first) = count_reordered(&with, Some(c), 4);
        println!(
            "display-order@unicode-bidi: {total} strings with {class:?}: \
             {reordered} displayed in another order"
        );
        match first {
            Some((s, shown)) => {
                println!("    {} is displayed as {}", show(&s), show(&shown))
            }
            None => ok = false,
        }
    }
    ok
}

fn main() -> io::Result<()> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        die(USAGE);
    }
    let version = parse_version(&args[1]);

    let (a, b, c) = unicode_normalization::UNICODE_VERSION;
    check_version(
        "unicode-normalization",
        (a as u64, b as u64, c as u64),
        version,
    );
    #[cfg(feature = "have-unicode-ident-version")]
    {
        let (a, b, c) = unicode_ident::UNICODE_VERSION;
        check_version("unicode-ident", (a as u64, b as u64, c as u64), version);
    }
    #[cfg(feature = "have-unicode-xid")]
    {
        let (a, b, c) = unicode_xid::UNICODE_VERSION;
        check_version("unicode-xid", (a, b, c), version);
    }
    check_version(
        "unicode-properties",
        unicode_properties::UNICODE_VERSION,
        version,
    );
    #[cfg(feature = "have-unicode-script")]
    check_version("unicode-script", unicode_script::UNICODE_VERSION, version);
    #[cfg(feature = "have-unicode-bidi")]
    check_version("unicode-bidi", unicode_bidi::UNICODE_VERSION, version);
    #[cfg(feature = "have-unicode-security")]
    check_version(
        "unicode-security",
        unicode_security::UNICODE_VERSION,
        version,
    );

    match (args[2].as_str(), args.len()) {
        ("code-points", 3) => {
            let stdout = io::stdout();
            let mut out = BufWriter::new(stdout.lock());
            code_points(&mut out)?;
            out.flush()
        }
        ("pairs", 4) => {
            if !pairs(&args[3])? {
                std::process::exit(1);
            }
            Ok(())
        }
        ("stream-safe", 4) => {
            if !stream_safe(&args[3])? {
                std::process::exit(1);
            }
            Ok(())
        }
        #[cfg(feature = "have-unicode-bidi")]
        ("display-order", 3) => {
            if !display_order() {
                std::process::exit(1);
            }
            Ok(())
        }
        _ => die(USAGE),
    }
}
