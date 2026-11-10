/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/
import NtimeDspace.Cross.Theorem

-- upstream: local-only (a guard for the Comparator configs)

/-!
# The theorems Comparator checks are exposed by `NtimeDspace.Cross.Theorem`

`NtimeDspace.Cross.Theorem` is the solution module of a Comparator config. This file imports nothing else and names
every theorem the config lists, so the build fails if the module stops exposing one of them (for
example, if an import that only re-exports a theorem is removed).
-/

#check @NtimeDspace.Crossing.ntime_decidable_sqrtLog
#check @NtimeDspace.Crossing.ntime_ssubset_dspace
#check @NtimeDspace.Crossing.ntime_subset_dspace_sqrtLog
