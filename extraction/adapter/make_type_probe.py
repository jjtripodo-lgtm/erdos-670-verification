#!/usr/bin/env python3
"""Write one inert Lean type probe per generated module; never runs Lean."""
import argparse
import json
from pathlib import Path


def conservative_name(value):
    return bool(value) and all(part and (part[0].isascii() and (part[0].isalpha() or part[0] == "_")) and
          all(c.isascii() and (c.isalnum() or c == "_") for c in part) for part in value.split("."))


def render(module, name, key):
    if not conservative_name(module) or not conservative_name(name):
        raise ValueError("Only explicit conservative public module/declaration names are accepted")
    return f'''-- Generated probe, not executed. Import only one solution module per process.
import {module}
import Lean
set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
set_option pp.proofs true
open Lean
run_meta do
  let env ← getEnv
  let name := {json.dumps(name)}.toName
  let some ci := env.find? name | throwError "Requested generated declaration is absent"
  let ty ← Lean.Meta.ppExpr ci.type
  IO.println (Json.mkObj [("name", Json.str name.toString),
    ("key", Json.str {json.dumps(key)}),
    ("typePretty", Json.str ty.pretty)]).compress
'''


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--import-module", required=True)
    ap.add_argument("--name", required=True)
    ap.add_argument("--key", required=True, help="unique pair key, e.g. Sol_Target::solution")
    ap.add_argument("--output", type=Path, required=True)
    args=ap.parse_args()
    if args.output.exists():
        raise ValueError("Refusing to overwrite an existing probe")
    args.output.write_text(render(args.import_module,args.name,args.key))
    print("Probe prepared; Lean/type comparison not run")


if __name__ == "__main__":
    main()
