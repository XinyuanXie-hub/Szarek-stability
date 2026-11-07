#!/usr/bin/env bash
set -euo pipefail
# Rebuild the isolated-network compatibility executable locally. This script
# never installs system packages, patches checkers, or runs unsandboxed proofs.
record_dir=$(cd -- "$(dirname -- "$0")" && pwd)
build_dir=${1:-"$record_dir/build"}
mkdir -p "$build_dir"
cd "$build_dir"
if [[ -e source ]]; then
  echo 'Choose a fresh build directory (source already exists).' >&2
  exit 1
fi
git clone --depth 1 --branch v0.12.0 https://github.com/containers/bubblewrap.git source
[[ $(git -C source rev-parse HEAD) == 2a76602a8c71f36c1527cf9fc3417d9149822e0c ]]
curl -fL 'https://deb.debian.org/debian/pool/main/libc/libcap2/libcap-dev_2.75-10+deb13u1+b3_amd64.deb' -o cap-dev.deb
curl -fL 'https://deb.debian.org/debian/pool/main/libs/libselinux/libselinux1-dev_3.8.1-1_amd64.deb' -o selinux-dev.deb
sha256sum -c <<'HASHES'
795983cf2cbc2e12e9440383d701229966c35bc40712ccbfd03e5c93d9af619d  cap-dev.deb
0107595c65dd5cfe7ce3643d400e7b2be2c2528bcd110ad5af8605711a858921  selinux-dev.deb
HASHES
dpkg-deb -x cap-dev.deb deps
dpkg-deb -x selinux-dev.deb deps
cd source
cat > config.h <<'CONFIG'
#define PACKAGE_STRING "bubblewrap 0.12.0"
#define HAVE_SELINUX 1
#define HAVE_SELINUX_2_3 1
CONFIG
git apply --check "$record_dir/no-loopback.patch"
git apply "$record_dir/no-loopback.patch"
gcc -D_GNU_SOURCE -O2 -fPIE -pie -fstack-protector-strong \
  -D_FORTIFY_SOURCE=3 -Wl,-z,relro,-z,now -I. -I../deps/usr/include \
  bubblewrap.c bind-mount.c network.c utils.c chroot_realpath.c safe_openat.c \
  -Wl,-l:libcap.so.2 -Wl,-l:libselinux.so.1 -o ../bwrap-no-loopback
printf 'Built sandbox executable: %s/bwrap-no-loopback\n' "$(cd .. && pwd)"
