import Mathlib
#check @tendsto_pow_atTop_nhds_zero_of_lt_one
#check @norm_pow_le'
#check @one_lt_pow₀
#check @one_lt_inv₀
#check @Real.rpow_le_rpow_of_exponent_le
#check @Real.rpow_inv_rpow
#check @Real.mul_rpow
#check @Real.rpow_le_rpow
#check @Filter.eventually_ge_atTop
#check @Real.rpow_neg
#check @Real.inv_rpow
#check @Real.logb_self_eq_one
example {R : Type*} [NormedRing R] : IsBoundedSMul R R := inferInstance
