#!/usr/bin/env bash
#SBATCH --job-name=ntime-bwrap
#SBATCH --account=commons
#SBATCH --partition=commons
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=4
#SBATCH --mem=4G
#SBATCH --time=00:30:00
#SBATCH --output=/scratch/cjh16/ntime-dspace/logs/bwrap-%j.out
#SBATCH --error=/scratch/cjh16/ntime-dspace/logs/bwrap-%j.err
# Build a current bubblewrap (the system's 0.4.1 lacks --clearenv) with a static libcap.
set -euxo pipefail
module load GCCcore/13.2.0 Meson/1.2.3 Ninja/1.11.1
P=/scratch/cjh16/ntime-dspace/tools
mkdir -p "$P/src" "$P/lib/pkgconfig" "$P/include/sys"
cd "$P/src"
curl -sSfL https://mirrors.edge.kernel.org/pub/linux/libs/security/linux-privs/libcap2/libcap-2.70.tar.xz -o libcap.tar.xz
rm -rf libcap-2.70 && tar xf libcap.tar.xz
make -C libcap-2.70/libcap libcap.a GOLANG=no
cp libcap-2.70/libcap/libcap.a "$P/lib/"
cp libcap-2.70/libcap/include/sys/capability.h "$P/include/sys/"
cat > "$P/lib/pkgconfig/libcap.pc" <<PC
prefix=$P
Name: libcap
Description: POSIX capabilities (static)
Version: 2.70
Libs: -L$P/lib -lcap
Cflags: -I$P/include
PC
curl -sSfL https://github.com/containers/bubblewrap/releases/download/v0.11.0/bubblewrap-0.11.0.tar.xz -o bwrap.tar.xz
rm -rf bubblewrap-0.11.0 && tar xf bwrap.tar.xz
cd bubblewrap-0.11.0
PKG_CONFIG_PATH="$P/lib/pkgconfig" meson setup build --prefix="$P" -Dman=disabled -Dselinux=disabled \
  -Dtests=false -Dbash_completion=disabled -Dzsh_completion=disabled
ninja -C build install
"$P/bin/bwrap" --version
"$P/bin/bwrap" --clearenv --ro-bind / / --dev /dev --proc /proc /usr/bin/true && echo BWRAP_CLEARENV_OK
