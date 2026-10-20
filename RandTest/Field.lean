import Rand.Field

example : Rand.Goldilocks.p = 2^64 - 2^32 + 1 := by norm_num [Rand.Goldilocks.p]
example : ((2^32 - 1 : ℕ) : Rand.F) * ((2^32 - 1 : ℕ) : Rand.F) = (((2^32-1)*(2^32-1) : ℕ) : Rand.F) := by push_cast; ring
example : ((2^32 - 1 : ℕ) : Rand.F).val = 2^32 - 1 := Rand.val_natCast_of_lt (by norm_num [Rand.Goldilocks.p])
