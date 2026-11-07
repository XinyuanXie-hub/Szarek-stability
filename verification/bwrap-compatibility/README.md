# Task-local bubblewrap compatibility build

This is an execution-environment compatibility aid, not a modification of the
Lean comparator, any proof checker, the theorem targets, or the submitted config.

## Provenance

- Source: https://github.com/containers/bubblewrap , annotated release tag v0.12.0.
- Source commit: `2a76602a8c71f36c1527cf9fc3417d9149822e0c`.
- Header packages (extracted locally, not installed):
  - https://deb.debian.org/debian/pool/main/libc/libcap2/libcap-dev_2.75-10+deb13u1+b3_amd64.deb
  - https://deb.debian.org/debian/pool/main/libs/libselinux/libselinux1-dev_3.8.1-1_amd64.deb
- Dynamically linked to the environment's existing libcap.so.2 and libselinux.so.1.
- Source config.h defines PACKAGE_STRING="bubblewrap 0.12.0", HAVE_SELINUX=1,
  HAVE_SELINUX_2_3=1. No assumed-kernel feature is enabled.
- Compiler used: gcc (Debian 14.2.0-19) 14.2.0.
- SHA256SUMS records downloaded header-package and observed binary hashes.
  The small evidence bundle omits those packages, executables, and the source
  checkout. `build.sh` downloads the pinned sources and headers into a fresh
  directory and reconstructs the patched executable. Compiler differences can
  change binary hashes; the source diff and package hashes remain pinned.

## Exact change and security rationale

The entire tracked source diff is in no-loopback.patch: replace the call to
loopback_setup() with a no-op. That call appears only after raw_clone() has
successfully created the requested namespaces. CLONE_NEWNET remains mandatory
when --unshare-net or --unshare-all is selected. raw_clone() failure remains fatal.
No namespace flags, mounts, capability dropping, no-new-privileges settings,
seccomp handling, SELinux handling, environment handling or child command are changed.

Upstream loopback_setup() uses NETLINK_ROUTE to assign loopback addresses and set
IFF_UP. The environment rejects that socket type. Leaving this setup out leaves
loopback DOWN inside the fresh isolated network namespace, which permits fewer
network operations than upstream's isolated-but-active-loopback mode. There is
no --share-net substitution and no unsandboxed command fallback. The comparator
continues to supply all original arguments and command definitions.

The comparator supports COMPARATOR_BWRAP as a documented executable override.
Point that variable at the absolute path to bwrap-no-loopback in this directory.
Dependency fetch steps which the comparator already marks network=true retain
their original --share-net behavior; this build changes nothing for those steps.
Untrusted proof build/export steps retain the fresh network namespace.

## Build

The same sources/flags were used for bwrap-stock before the one-line change and
bwrap-no-loopback afterward. Commands from source/:

```sh
gcc -D_GNU_SOURCE -O2 -fPIE -pie -fstack-protector-strong \
  -D_FORTIFY_SOURCE=3 -Wl,-z,relro,-z,now -I. -I../deps/usr/include \
  bubblewrap.c bind-mount.c network.c utils.c chroot_realpath.c safe_openat.c \
  -Wl,-l:libcap.so.2 -Wl,-l:libselinux.so.1 -o ../bwrap-no-loopback
```

## Observed isolation checks

validation.json contains captured results for both binaries using the comparator's
read-only-root/home-covers/proc/dev/clear-environment/unshare-all arguments.

- Same-source stock build reproduced NETLINK_ROUTE EPERM and exited 1.
- Patched build exited 0; parent and child network namespace identifiers differ.
- Child /proc/net/dev contains only lo; ioctl confirms flags=8 and IFF_UP=false.
- Child /proc/net/route is empty. No network connections were attempted.
- Child CapPrm=0, CapEff=0, NoNewPrivs=1.
- /home and /root are empty covered mounts.
- Creating a file in the read-only project fails with EROFS (errno 30).
- Creating a file in the explicitly private /tmp succeeds.

These checks support preserving the comparator's isolation while avoiding an
unnecessary network-configuration syscall. They do not replace the comparator
run or certify its result; the parent task records the full run separately.
