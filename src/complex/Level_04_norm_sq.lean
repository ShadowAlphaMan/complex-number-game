/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard.
Thanks: Imperial College London, leanprover-community
-/

-- Import levels 1 to 3
import complex.Level_03_conj

/-! 

# Level 4: Norms

Define `norm_sq : ℂ → ℝ` by defining `norm_sq(z)` to be
`re(z)*re(z)+im(z)*im(z)` and see what you can prove about it.

-/

namespace complex

/-- The real number which is the squared norm of z -/
def norm_sq (z : ℂ) : ℝ := sorry

/-! ## Behaviour with respect to 0, 1 and I -/

@[simp] lemma norm_sq_zero : norm_sq 0 = 0 := sorry
@[simp] lemma norm_sq_one : norm_sq 1 = 1 := sorry
@[simp] lemma norm_sq_I : norm_sq I = 1 := sorry

/-! ## Behaviour with respect to *, + and - -/

@[simp] lemma norm_sq_mul (z w : ℂ) : norm_sq (z * w) = norm_sq z * norm_sq w :=
sorry

lemma norm_sq_add (z w : ℂ) : norm_sq (z + w) =
  norm_sq z + norm_sq w + 2 * (z * conj w).re :=
sorry

@[simp] lemma norm_sq_neg (z : ℂ) : norm_sq (-z) = norm_sq z :=
sorry

/-! ## Behaviour with respect to `conj` -/

@[simp] lemma norm_sq_conj (z : ℂ) : norm_sq (conj z) = norm_sq z :=
sorry

/-! ## Behaviour with respect to real numbers` -/

@[simp] lemma norm_sq_of_real (r : ℝ) : norm_sq r = r * r :=
sorry

theorem mul_conj (z : ℂ) : z * conj z = norm_sq z :=
sorry

/-! ## Behaviour with respect to real 0, ≤, < and so on -/

-- Warning: you will have to know something about Lean's API for
-- real numbers to solve these ones. If you turn the statements about
-- complex numbers into statements about real numbers, you'll find
-- they're of the form "prove $$x^2+y^2\geq0$$" with `x` and `y` real.

lemma norm_sq_nonneg (z : ℂ) : 0 ≤ norm_sq z := sorry

@[simp] lemma norm_sq_eq_zero {z : ℂ} : norm_sq z = 0 ↔ z = 0 :=
sorry

@[simp] lemma norm_sq_pos {z : ℂ} : 0 < norm_sq z ↔ z ≠ 0 :=
sorry

lemma re_sq_le_norm_sq (z : ℂ) : z.re * z.re ≤ norm_sq z :=
sorry

lemma im_sq_le_norm_sq (z : ℂ) : z.im * z.im ≤ norm_sq z :=
sorry

end complex
