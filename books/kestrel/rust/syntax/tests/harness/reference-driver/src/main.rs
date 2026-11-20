// Rust Library
//
// Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
//
// License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
//
// Author: Eric McCarthy (bendyarm on GitHub)

//! Run test inputs through the Rust Reference's interpreter of its own
//! lexical grammar (`tools/parser` in rust-lang/reference).
//!
//! usage: reference-driver TESTSDIR OUTDIR [CATEGORY...]
//!
//! TESTSDIR holds the files written by gen_tests.py, each a list of
//! {"id": str, "text": str}.  For each of them (or each named category),
//! OUTDIR gets a file mapping each id to
//! {"ok": bool, "n": int or null, "errs": [str], "toks": [[start, end, name]]}:
//! "ok" and "n" as in run_rustc.py (n = number of top-level token trees,
//! a doc comment counting as the tokens of its attribute), and "toks" the
//! tokens with their code-point offsets in the input (end exclusive).
//!
//! The interpreter treats the start of its input as the start of a file
//! (byte order mark, shebang, frontmatter), while run_rustc.py puts each
//! input in the middle of one.  So each input goes in after a `;` and a
//! line feed, which are then left out of the results.  CR LF pairs are
//! replaced by LF and a line feed is appended, as to_acl2.py does.

use diagnostics::Diagnostics;
use parser::coverage::Coverage;
use std::collections::BTreeMap;
use std::panic::{AssertUnwindSafe, catch_unwind};

const PREFIX: &str = ";\n";

fn run_one(grammar: &grammar::Grammar, text: &str) -> serde_json::Value {
    let src = format!("{PREFIX}{}\n", text.replace("\r\n", "\n"));
    let mut coverage = Coverage::default();
    let result = catch_unwind(AssertUnwindSafe(|| {
        parser::lexer::tokenize(grammar, &mut coverage, &src)
    }));
    let tokens = match result {
        Err(_) => return reject("panic in the interpreter".to_string()),
        Ok(Err(e)) => return reject(e.message),
        Ok(Ok(ts)) => ts.tokens,
    };
    // As the Reference's checker does: a reserved or invalid token is an error.
    if let Some(t) = tokens
        .iter()
        .find(|t| t.name == "RESERVED_TOKEN" || t.name.starts_with("INVALID_"))
    {
        return reject(format!("invalid token {}", t.name));
    }
    let cp = |byte: usize| src[..byte].chars().count() - PREFIX.chars().count();
    let mut toks = Vec::new();
    let (mut n, mut depth) = (0usize, 0usize);
    // Skip the `;` of the prefix; drop comments that are not doc comments.
    for t in tokens.iter().skip(1) {
        let name = t.name.as_str();
        if matches!(name, "LINE_COMMENT" | "BLOCK_COMMENT") {
            continue;
        }
        let s = &src[t.range.clone()];
        toks.push(serde_json::json!([cp(t.range.start), cp(t.range.end), name]));
        let trees = match name {
            "OUTER_LINE_DOC" | "OUTER_BLOCK_DOC" => 2,
            "INNER_LINE_DOC" | "INNER_BLOCK_DOC" => 3,
            _ => 1,
        };
        match s {
            ")" | "]" | "}" => depth -= 1,
            _ => {
                if depth == 0 {
                    n += trees;
                }
                if matches!(s, "(" | "[" | "{") {
                    depth += 1;
                }
            }
        }
    }
    serde_json::json!({"ok": true, "n": n, "errs": [], "toks": toks})
}

fn reject(message: String) -> serde_json::Value {
    serde_json::json!({"ok": false, "n": null, "errs": [message], "toks": []})
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: reference-driver TESTSDIR OUTDIR [CATEGORY...]");
        std::process::exit(2);
    }
    let (tests_dir, out_dir, cats) = (&args[1], &args[2], &args[3..]);
    std::fs::create_dir_all(out_dir).unwrap();
    // The interpreter reports its panics through the result; keep stderr quiet.
    std::panic::set_hook(Box::new(|_| {}));
    let mut diag = Diagnostics::new();
    let grammar = grammar::load_grammar_with_frontmatter(&mut diag);
    let mut names: Vec<String> = std::fs::read_dir(tests_dir)
        .unwrap()
        .filter_map(|e| e.ok()?.file_name().into_string().ok())
        .filter(|f| f.ends_with(".json"))
        .filter(|f| cats.is_empty() || cats.iter().any(|c| *f == format!("{c}.json")))
        .collect();
    names.sort();
    for name in names {
        let tests: Vec<serde_json::Value> =
            serde_json::from_str(&std::fs::read_to_string(format!("{tests_dir}/{name}")).unwrap())
                .unwrap();
        let mut out = BTreeMap::new();
        let mut accepted = 0;
        for t in &tests {
            let r = run_one(&grammar, t["text"].as_str().unwrap());
            if r["ok"] == true {
                accepted += 1;
            }
            out.insert(t["id"].as_str().unwrap().to_string(), r);
        }
        std::fs::write(
            format!("{out_dir}/{name}"),
            serde_json::to_string(&out).unwrap(),
        )
        .unwrap();
        println!("{name}: {} tests, {accepted} accepted", tests.len());
    }
}
