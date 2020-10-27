/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard.
Thanks: Imperial College London, leanprover-community
-/

-- Import levels 1 to 3
import complex.your_solutions.Level_03_conj

/-! 

# Level 4: Norms

Define `norm_sq : ℂ → ℝ` by defining `norm_sq(z)` to be
`re(z)*re(z)+im(z)*im(z)` and see what you can prove about it.

-/

namespace complex

/-- The real number which is the squared norm of z -/
def norm_sq (z : ℂ) : ℝ := z.re * z.re + z.im * z.im

/-! ## Behaviour with respect to 0, 1 and I -/

@[simp] lemma norm_sq_zero : norm_sq 0 = 0 := begin
  unfold norm_sq,
  simp,
end
@[simp] lemma norm_sq_one : norm_sq 1 = 1 := begin
  unfold norm_sq,
  simp,
end
@[simp] lemma norm_sq_I : norm_sq I = 1 := begin
  unfold norm_sq,
  simp,
end

/-! ## Behaviour with respect to *, + and - -/

@[simp] lemma norm_sq_mul (z w : ℂ) : norm_sq (z * w) = norm_sq z * norm_sq w :=
begin
  unfold norm_sq,
  simp,
  ring,
end

lemma norm_sq_add (z w : ℂ) : norm_sq (z + w) =
  norm_sq z + norm_sq w + 2 * (z * conj w).re :=
begin
  unfold norm_sq,
  simp,
  ring,
end

@[simp] lemma norm_sq_neg (z : ℂ) : norm_sq (-z) = norm_sq z :=
begin
  unfold norm_sq,
  have h_re : (-z).re = -z.re,
  cases z,
  simp,
  have h_im : (-z).im = -z.im,
  cases z,
  simp,
  rw h_re,
  rw h_im,
  simp,
end

/-! ## Behaviour with respect to `conj` -/

@[simp] lemma norm_sq_conj (z : ℂ) : norm_sq (conj z) = norm_sq z :=
begin
  unfold conj,
  unfold norm_sq,
  simp,
end

/-! ## Behaviour with respect to real numbers` -/

@[simp] lemma norm_sq_of_real (r : ℝ) : norm_sq r = r * r :=
begin
  unfold norm_sq,
  simp,
end

theorem mul_conj (z : ℂ) : z * conj z = norm_sq z :=
begin
  ext; simp,
  unfold norm_sq,
  rw mul_comm,
  simp,
end

/-! ## Behaviour with respect to real 0, ≤, < and so on -/

-- Warning: you will have to know something about Lean's API for
-- real numbers to solve these ones. If you turn the statements about
-- complex numbers into statements about real numbers, you'll find
-- they're of the form "prove $$x^2+y^2\geq0$$" with `x` and `y` real.

lemma norm_sq_nonneg (z : ℂ) : 0 ≤ norm_sq z := begin
  unfold norm_sq,
  have h_re: z.re * z.re ≥ 0,
  exact mul_self_nonneg z.re,
  have h_im: z.im * z.im ≥ 0,
  exact mul_self_nonneg z.im,
  exact add_nonneg h_re h_im,
end

@[simp] lemma norm_sq_eq_zero {z : ℂ} : norm_sq z = 0 ↔ z = 0 :=
begin
  unfold norm_sq,
  have h_re: z.re * z.re ≥ 0,
  exact mul_self_nonneg z.re,
  have h_im: z.im * z.im ≥ 0,
  exact mul_self_nonneg z.im,
  split;
  intros,
  have h_re1 : z.re * z.re = 0,
  linarith,
  have h_im1 : z.im * z.im = 0,
  linarith,
  have h_re2 : z.re = 0,
  exact zero_eq_mul_self.mp (eq.symm h_re1),
  have h_im2 : z.im = 0,
  exact zero_eq_mul_self.mp (eq.symm h_im1),
  ext; simp; assumption,
  cases a,
  simp,
end

@[simp] lemma norm_sq_pos {z : ℂ} : 0 < norm_sq z ↔ z ≠ 0 :=
begin
  have h : 0 < z.norm_sq <-> ¬ ¬ 0 < z.norm_sq,
  simp,
  rw h,
  apply not_congr,
  rw <-norm_sq_eq_zero,
  split;
  intros,
  simp at a,
  have b : 0 ≤ norm_sq z,
  exact norm_sq_nonneg z,
  exact le_antisymm a b,
  rw a,
  simp,  
end

lemma re_sq_le_norm_sq (z : ℂ) : z.re * z.re ≤ norm_sq z :=
begin
  unfold norm_sq,
  simp,
  exact mul_self_nonneg z.im,
end

lemma im_sq_le_norm_sq (z : ℂ) : z.im * z.im ≤ norm_sq z :=
begin
  unfold norm_sq,
  simp,
  exact mul_self_nonneg z.re,
end

end complex
