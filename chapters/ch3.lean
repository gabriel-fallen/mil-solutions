-- Chapter 3: Logic

import Mathlib.Tactic
import Mathlib.Data.Real.Basic


-- Section 1
section ImpAndForAll

theorem my_lemma4:
    ∀ {x y ε : ℝ}, 0 < ε -> ε <= 1 -> |x| < ε -> |y| < ε -> |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := abs_mul x y
    _ <= |x| * ε := mul_le_mul_of_nonneg_left (le_of_lt ylt) (abs_nonneg x)
    _ < 1 * ε := (mul_lt_mul_right (c := 1) epos).mpr (lt_of_le_of_lt' ele1 xlt)
    _ = ε := one_mul ε

end ImpAndForAll
