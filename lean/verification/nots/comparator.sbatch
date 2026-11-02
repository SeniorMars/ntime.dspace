#!/usr/bin/env bash
#SBATCH --job-name=ntime-comparator
#SBATCH --account=commons
#SBATCH --partition=commons
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=160G
#SBATCH --time=23:00:00
#SBATCH --output=/scratch/cjh16/ntime-dspace/logs/comparator-%j.out
#SBATCH --error=/scratch/cjh16/ntime-dspace/logs/comparator-%j.err
# Sandboxed (bwrap) Comparator run in a fresh copy: builds challenge and solution
# inside the sandbox, compares statements, checks axioms, replays with all kernels.
set -uo pipefail
source /scratch/cjh16/ntime-dspace/scripts/common.sh
# Use the locally built bubblewrap 0.11 (system bwrap 0.4.1 lacks --clearenv).
export PATH="/scratch/cjh16/ntime-dspace/tools/bin:$PATH"
# The sandbox clears LD_LIBRARY_PATH, which the git module needs; this wrapper restores it for git only.
export PATH="/scratch/cjh16/ntime-dspace/tools/gitwrap:$PATH"
echo "git: $(command -v git) $(git --version)"
echo "bwrap: $(command -v bwrap) $(bwrap --version)"
cd /scratch/cjh16/ntime-dspace/cmp/lean
lake exe cache get || exit 1
echo "=== main check (--paranoid) ==="
time lake comparator --paranoid --config comparator.json; main=$?
echo "main_exit=$main"
echo "=== negative control: changed statement (must fail) ==="
lake comparator --config comparator-wrong.json; wrong=$?
echo "wrong_exit=$wrong"
echo "=== negative control: sorry proof (must fail) ==="
lake comparator --config comparator-sorry.json; sorryc=$?
echo "sorry_exit=$sorryc"
echo "done $(date -u +%FT%TZ)"
[ "$main" -eq 0 ] && [ "$wrong" -ne 0 ] && [ "$sorryc" -ne 0 ]
