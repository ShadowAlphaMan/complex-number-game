/-
Copyright (c) 2020 The Xena project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kevin Buzzard
Thanks: Imperial College London, leanprover-community
-/

-- import levels 1 and 2
import complex.your_solutions.Level_02_I

/-! # Level 3: Complex conjugation -/

namespace complex

-- First complete the definition using `complex.mk` or `⟨x, y⟩` notation

/-- The complex conjugate of a complex number -/
def conj (z : ℂ) : ℂ := ⟨z.re, -z.im⟩

-- Now prove how it interacts with everything else

/-! ## Real and imaginary parts -/

@[simp] lemma conj_re (z : ℂ) : re(conj z) = re(z) := begin
    unfold conj,
end
@[simp] lemma conj_im (z : ℂ) : im(conj z) = -im(z) := begin
    unfold conj,
end

/-! ## Behaviour with respect to 0, 1 and I -/

@[simp] lemma conj_zero : conj 0 = 0 := begin
    ext;
    simp,
end
@[simp] lemma conj_one : conj 1 = 1 := begin
    ext; simp,
end
@[simp] lemma conj_I : conj I = -I := begin
    ext; simp,
end
@[simp] lemma conj_neg_I : conj (-I) = I := begin ext; simp, end

/-! ## Behaviour with respect to +, - and * -/

@[simp] lemma conj_add (z w : ℂ) : conj (z + w) = conj z + conj w :=
begin
    ext; simp,
    apply add_comm,
end

@[simp] lemma conj_neg (z : ℂ) : conj (-z) = -conj z := begin
    ext; simp,
end



@[simp] lemma conj_mul (z w : ℂ) : conj (z * w) = conj z * conj w :=
begin
    ext; simp,
    apply add_comm,
end

/-! ## Behaviour with respect to real numbers -/

@[simp] lemma conj_of_real (r : ℝ) : conj r = r := begin
    ext; simp,
end

lemma im_eq_zero_of_eq_conj {z : ℂ} : conj z = z → im z = 0 := begin
    cases z,
    unfold conj,
    simp,
    exact eq_zero_of_neg_eq,
end

lemma eq_conj_iff_real {z : ℂ} : conj z = z ↔ ∃ r : ℝ, z = r :=
begin
    unfold conj,
    split;
    intros,
    use z.re,
    ext,
    simp,
    rw im_eq_zero_of_eq_conj,
    simp,
    exact a,
    cases a,
    rw a_h,
    ext;
    simp,
end

lemma eq_conj_iff_re {z : ℂ} : conj z = z ↔ (z.re : ℂ) = z :=
begin
    rw eq_conj_iff_real,
    split;
    intros,
    cases a,
    rw a_h,
    simp,
    use z.re,
    symmetry,
    exact a,
end

theorem add_conj (z : ℂ) : z + conj z = (2 * z.re : ℝ) :=
begin
    ext; simp,
    exact bit0_eq_two_mul z.re,
    left,
    exact add_zero (1:ℂ).im,
end


/-! ## Properties of the `conj` map -/

@[simp] lemma conj_conj (z : ℂ) : conj (conj z) = z :=
begin
    unfold conj, simp,
end

lemma conj_inj {z w : ℂ} : conj z = conj w ↔ z = w :=
begin
    unfold conj, simp,
    rw ext_iff,
end

@[simp] lemma conj_eq_zero {z : ℂ} : conj z = 0 ↔ z = 0 :=
begin
    unfold conj,
    rw ext_iff,
    rw ext_iff,
    simp,
end

/-

A ring homomorphism in Lean is the following collection
of data: a map, and the proof that it commutes with
the ring structures in the obvious way. Here we observe
that the work we've done is enough to define the
ring homomorphism complex conjugation.

-/

/-- the ring homomorphism complex conjugation -/
def Conj : ℂ →+* ℂ :=
{ to_fun := conj,
  map_zero' := conj_zero,
  map_one' := conj_one,
  map_add' := conj_add,
  map_mul' := conj_mul
}

-- Two optional lemmas which computer scientists like,
-- giving us easy access to some basic properties
-- of conj

open function

lemma conj_involutive : involutive conj := begin
    unfold involutive,
    apply conj_conj,
end

lemma conj_bijective : bijective conj := begin
    have h : involutive conj -> bijective conj,
    exact involutive.bijective,
    exact h conj_involutive,
end

end complex
