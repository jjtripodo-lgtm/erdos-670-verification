#!/usr/bin/env bash
set -euo pipefail
platform="${1:?platform}"
prefix="${2:?installation parent}"
case "$platform" in
  palomar)
    version=4.35.0-rc2
    sha=b67d0e0ba959fc74e186f1b44aebca32d6ecb6a28f8e9a029fc4e9f73398a049
    ;;
  prove2me)
    version=4.33.1
    sha=890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235
    ;;
  *) exit 2 ;;
esac
mkdir -p "$prefix"
archive="$prefix/lean-$version-linux.tar.zst"
curl --fail --location --retry 3 --proto '=https' --tlsv1.2 \
  --output "$archive" \
  "https://github.com/leanprover/lean4/releases/download/v$version/lean-$version-linux.tar.zst"
echo "$sha  $archive" | sha256sum --check
tar --zstd -xf "$archive" -C "$prefix"
# This archive was created by this step, and is no longer needed after extraction.
rm "$archive"
"$prefix/lean-$version-linux/bin/lean" --version
echo "$prefix/lean-$version-linux/bin" >> "$GITHUB_PATH"
