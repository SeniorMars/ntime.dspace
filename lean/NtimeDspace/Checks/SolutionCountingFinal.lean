/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/
import NtimeDspace.Cross.CountingFinal

-- upstream: local-only (a guard for the Comparator configs)

/-!
# The theorems Comparator checks are exposed by `NtimeDspace.Cross.CountingFinal`

`NtimeDspace.Cross.CountingFinal` is the solution module of a Comparator config. This file imports nothing else and names
every theorem the config lists, so the build fails if the module stops exposing one of them (for
example, if an import that only re-exports a theorem is removed).
-/

#check @NtimeDspace.Crossing.bptime_subset_dspace_sqrtLog_general
#check @NtimeDspace.Crossing.exists_dspace_linear_ntime_lower_bound_general
#check @NtimeDspace.Crossing.ntime_decidable_sqrtLog_general
#check @NtimeDspace.Crossing.ntime_mul_sqrtLog_subset_dspace_general
#check @NtimeDspace.Crossing.ntime_ssubset_dspace_general
#check @NtimeDspace.Crossing.ntime_ssubset_nspace_general
#check @NtimeDspace.Crossing.ntime_subset_dspace_sqrtLog_general
#check @NtimeDspace.Crossing.pptime_subset_dspace_sqrtLog_general
