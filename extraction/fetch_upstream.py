#!/usr/bin/env python3
"""Fetch two hash-pinned official analysis tools for ephemeral, documented use."""
import argparse
import hashlib
from pathlib import Path
from urllib.request import urlopen

PIN = "78989800ba0b3149ee34205257025bd0f617e8ef"
FILES = {
    "extract_decl_graph.lean": "e421a1d7bb1847697de699ecc6e9d66a1e47fb17c876e627fd665c4ad68db622",
    "extract_sketch_info.lean": "e0a9164a476c61b6da70592e3c7e8f4267910ac3d433d9fd13e6ccca7b7e801b",
}
MAX_BYTES = 1024 * 1024


def fetch(output):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    for name, expected in FILES.items():
        url = f"https://raw.githubusercontent.com/prove2me/prove2me_workspace/{PIN}/scripts/{name}"
        with urlopen(url, timeout=60) as response:
            data = response.read(MAX_BYTES + 1)
        if len(data) > MAX_BYTES:
            raise ValueError("Pinned tool exceeds the fixed download budget")
        if hashlib.sha256(data).hexdigest() != expected:
            raise ValueError("Pinned upstream tool hash differs: " + name)
        data.decode("utf-8")
        (output / name).write_bytes(data)
        print(f"Verified ephemeral tool: {name} sha256={expected}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    fetch(parser.parse_args().output)
