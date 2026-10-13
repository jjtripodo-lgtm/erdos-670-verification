#!/usr/bin/env bash
# Same release and build flags as PalomarSubmission at
# d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44/scripts/install_bwrap.sh.
# Deliberately does not install an AppArmor profile or change kernel settings.
set -euo pipefail
prefix="${1:?usage: install_bwrap.sh ABSOLUTE_INSTALL_DIRECTORY}"
[[ "$prefix" = /* && "$prefix" != *[[:space:]]* ]]
mkdir -p "$prefix"
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
curl --fail --location --silent --show-error --proto '=https' --tlsv1.2 \
  --output "$work/bubblewrap.tar.xz" \
  https://github.com/containers/bubblewrap/releases/download/v0.12.0/bubblewrap-0.12.0.tar.xz
echo "9760d007363e3abba7c747489910f9f82d9fca53ba3bd3282e396fa3c97a3314  $work/bubblewrap.tar.xz" | sha256sum --check
tar -xJf "$work/bubblewrap.tar.xz" -C "$work"
(
  cd "$work/bubblewrap-0.12.0"
  meson setup build -Dselinux=disabled -Dman=disabled -Dbash_completion=disabled \
    -Dzsh_completion=disabled -Dtests=false
  ninja -C build
)
install -m 0755 "$work/bubblewrap-0.12.0/build/bwrap" "$prefix/bwrap"
"$prefix/bwrap" --version
# Match the sensitive namespace/mount parts of Lake's own sandbox before
# downloading Lean or Mathlib. A failure stops the job; there is no fallback.
"$prefix/bwrap" --ro-bind / / --tmpfs /home --tmpfs /root \
  --tmpfs /run/user --tmpfs /tmp --dir /tmp/home --dev /dev --proc /proc \
  --clearenv --setenv HOME /tmp/home --unshare-all --die-with-parent \
  --new-session --chdir / -- /usr/bin/true
