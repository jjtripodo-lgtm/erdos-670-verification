#!/usr/bin/env python3
"""Conservative exact pretty-type comparison; no universe renaming is guessed."""
import argparse
import hashlib
import json
from pathlib import Path


def load(path):
    found = {}
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        row = json.loads(line)
        key = row.get("key", row.get("name"))
        if not isinstance(key, str) or not isinstance(row.get("typePretty"), str) or key in found:
            raise ValueError("Missing/duplicate key or pretty type in " + str(path))
        found[key] = row["typePretty"]
    return found


def compare(original, staged, pairs):
    if not isinstance(pairs, list) or not pairs:
        raise ValueError("An explicit nonempty original/staged pairing is required")
    results = []
    seen = set()
    for pair in pairs:
        old, new = pair["original"], pair["staged"]
        if (old, new) in seen:
            raise ValueError("Duplicate pairing")
        seen.add((old, new))
        if old not in original or new not in staged:
            raise ValueError("Missing type evidence for pairing: " + str(pair))
        results.append({"original": old, "staged": new,
                        "exact_pretty_type_equal": original[old] == staged[new],
                        "original_type": original[old], "staged_type": staged[new]})
    return {"status": "EXACT_TYPE_TEXT_EQUAL" if all(r["exact_pretty_type_equal"] for r in results) else "BLOCKED_TYPE_TEXT_DIFF",
            "comparison": "byte-exact pretty-printed types with matched pp options; no automatic alpha-normalization",
            "universe_only_differences": "not automatically accepted; require separate verified alpha-equivalence review",
            "remaining_gates": ["exact transformed-text compilation", "every stub and solution covered", "axiom/sorry audits", "own-target import exclusion"],
            "upload_ready": False, "pairs": results}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--original", type=Path, required=True)
    ap.add_argument("--staged", type=Path, required=True)
    ap.add_argument("--pairs", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    if args.output.resolve() in {p.resolve() for p in (args.original,args.staged,args.pairs)}:
        raise ValueError("Refusing to overwrite an input")
    result = compare(load(args.original),load(args.staged),json.loads(args.pairs.read_text()))
    result["input_sha256"] = {k:hashlib.sha256(getattr(args,k).read_bytes()).hexdigest() for k in ("original","staged","pairs")}
    args.output.write_text(json.dumps(result,indent=2)+"\n")
    print(result["status"])
    return 0 if result["status"] == "EXACT_TYPE_TEXT_EQUAL" else 2


if __name__ == "__main__":
    raise SystemExit(main())
