#!/usr/bin/env bash
#SBATCH --job-name=ntime-build
#SBATCH --account=commons
#SBATCH --partition=commons
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=16
#SBATCH --mem=160G
#SBATCH --time=16:00:00
#SBATCH --output=/scratch/cjh16/ntime-dspace/logs/build-%j.out
#SBATCH --error=/scratch/cjh16/ntime-dspace/logs/build-%j.err
# Clean build of the final theorem's closure from source (Mathlib from its cache).
set -euo pipefail
source /scratch/cjh16/ntime-dspace/scripts/common.sh
cd /scratch/cjh16/ntime-dspace/build/lean
lake exe cache get
time lake build NtimeChallenge NtimeChallengeWrong NtimeDspace.Final NtimeDspace.Checks.FinalAxioms
echo "build done $(date -u +%FT%TZ)"
