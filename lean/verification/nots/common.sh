# Shared environment for the NOTS jobs.
export ELAN_HOME=/scratch/cjh16/ntime-dspace/elan
export PATH="$ELAN_HOME/bin:$ELAN_HOME/toolchains/leanprover--lean4---v4.36.0-rc2/bin:$PATH"
unset LD_PRELOAD
export XALT_SKIP=1
module load git/2.42.0 2>/dev/null || true
echo "host=$(hostname) start=$(date -u +%FT%TZ) job=${SLURM_JOB_ID:-none}"
lean --version
