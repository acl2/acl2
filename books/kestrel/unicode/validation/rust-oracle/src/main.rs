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
//! This one source file is built by two Cargo packages, v16.0.0 and v17.0.0
//! in this directory, which pin the versions of the crates that implement
//! that version of Unicode.  Usage:
//!
//!     oracle VERSION code-points > FILE
//!     oracle VERSION pairs PAIRS-FILE
//!
//! VERSION, e.g. 16.0.0, must be the version of Unicode that the crates
//! implement; the program stops if a crate says otherwise.
//!
//! The first form writes a header line and one line for each code point.
//! Each column is named `property@crate`.  A surrogate is not a `char`,
//! so its fields are all `!`, which means "cannot say".
//!
//! The second form reads a file written by DUMP-PAIRS of ../../dump.lisp,
//! with lines `first second composite nfc...` (composite is `-` if the two
//! code points do not compose), and checks each line against
//! unicode-normalization.  It exits with status 1 if any line differs.

use std::io::{self, BufRead, BufWriter, Write};
use unicode_normalization::char::{canonical_combining_class, compose};
use unicode_normalization::UnicodeNormalization;

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
    ];
    if cfg!(feature = "have-unicode-xid") {
        columns.extend(["xids@unicode-xid", "xidc@unicode-xid"]);
    }
    if cfg!(feature = "have-regex-syntax") {
        columns.extend([
            "xids@regex-syntax",
            "xidc@regex-syntax",
            "pws@regex-syntax",
            "bidic@regex-syntax",
        ]);
    }
    #[cfg(feature = "have-regex-syntax")]
    let sets = [
        regex_syntax_set("XID_Start"),
        regex_syntax_set("XID_Continue"),
        regex_syntax_set("Pattern_White_Space"),
        regex_syntax_set("Bidi_Control"),
    ];

    writeln!(out, "#cp;{}", columns.join(";"))?;
    for cp in 0..=0x10FFFFu32 {
        let Some(c) = char::from_u32(cp) else {
            writeln!(out, "{cp}{}", ";!".repeat(columns.len()))?;
            continue;
        };
        write!(
            out,
            "{cp};{};{};{};{};{};{};{};{};{};{}",
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
        )?;
        #[cfg(feature = "have-unicode-xid")]
        write!(
            out,
            ";{};{}",
            flag(unicode_xid::UnicodeXID::is_xid_start(c)),
            flag(unicode_xid::UnicodeXID::is_xid_continue(c)),
        )?;
        #[cfg(feature = "have-regex-syntax")]
        write!(
            out,
            ";{};{};{};{}",
            flag(sets[0][cp as usize]),
            flag(sets[1][cp as usize]),
            flag(sets[2][cp as usize]),
            flag(sets[3][cp as usize]),
        )?;
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

fn main() -> io::Result<()> {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        die("usage: oracle VERSION code-points | oracle VERSION pairs FILE");
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
        _ => die("usage: oracle VERSION code-points | oracle VERSION pairs FILE"),
    }
}
