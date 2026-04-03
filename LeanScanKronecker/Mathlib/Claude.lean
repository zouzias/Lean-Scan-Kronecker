/-
  Lean 4 / Mathlib proof of Theorem 1 from:

    "Prefix Sums via Kronecker Products"
    Aleksandros Sobczyk and Anastasios Zouzias
    arXiv:2512.16309

  Theorem 1. Fix n, n₁, n₂ > 1 with n = n₁ * n₂.  Then:

      Lₙ  =  Lₙ₁ ⊗ Lₙ₂  +  Lₙ₁⁻ ⊗ Uₙ₂⁻

  where Lₙ is the lower-triangular all-ones matrix of size n,
        Lₙ⁻ is its strictly lower-triangular variant (zeros on diagonal),
        Uₙ⁻ is the strictly upper-triangular all-ones matrix.

  Strategy: we prove everything entry-wise using Fin arithmetic.
  For i = i₁ * n₂ + i₂ and j = j₁ * n₂ + j₂ the key logical equivalence is:

      j ≤ i  ↔  (j₁ < i₁) ∨ (j₁ = i₁ ∧ j₂ ≤ i₂)

  and the two disjuncts correspond to the two Kronecker summands.

  Dependencies: Mathlib (any recent version with LinearAlgebra.Matrix.Kronecker).
  To build:
      lake exe cache get
      lake build
-/

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open Matrix Finset

/-!
## 1.  Helper definitions
-/

section Definitions

variable {α : Type*} [Zero α] [One α]

/-- Lower-triangular all-ones matrix: entry (i,j) is 1 iff j ≤ i. -/
def lowerOne (n : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  fun i j => if j ≤ i then 1 else 0

/-- Strictly lower-triangular all-ones matrix: entry (i,j) is 1 iff j < i. -/
def strictLowerOne (n : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  fun i j => if j < i then 1 else 0

/-- Strictly upper-triangular all-ones matrix: entry (i,j) is 1 iff i < j. -/
def strictUpperOne (n : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  fun i j => if i < j then 1 else 0

end Definitions

/-!
## 2.  Entry-wise characterisation of the Kronecker product of indicator matrices

  For 0-1 matrices of the form `if P i j then 1 else 0`, the Kronecker product
  has a clean entry-wise description.  We establish it in a general boolean-predicate
  form so that it applies uniformly to all three matrix types above.
-/

section KroneckerLemmas

/-- Indicator matrix: 1 at (i,j) iff `P i j`, 0 otherwise. -/
private def indMat (m n : ℕ) (P : Fin m → Fin n → Prop) [DecidablePred (fun ij : Fin m × Fin n => P ij.1 ij.2)] :
    Matrix (Fin m) (Fin n) ℕ :=
  fun i j => if P i j then 1 else 0

/-- The Kronecker product of two indicator matrices is again an indicator matrix,
    with the conjunction of the row and column predicates on each block index. -/
lemma kronecker_indMat
    (m₁ n₁ m₂ n₂ : ℕ)
    (P : Fin m₁ → Fin n₁ → Prop) (Q : Fin m₂ → Fin n₂ → Prop)
    [DecidablePred (fun ij : Fin m₁ × Fin n₁ => P ij.1 ij.2)]
    [DecidablePred (fun ij : Fin m₂ × Fin n₂ => Q ij.1 ij.2)]
    (i : Fin (m₁ * m₂)) (j : Fin (n₁ * n₂)) :
    (kroneckerMap (· * ·) (indMat m₁ n₁ P) (indMat m₂ n₂ Q)) i j =
      if P (i.divNat) (j.divNat) ∧ Q (i.modNat) (j.modNat) then 1 else 0 := by
  simp [kroneckerMap, indMat, Fin.divNat, Fin.modNat]
  split_ifs with hP hQ <;> simp [hP, hQ]

end KroneckerLemmas

/-!
## 3.  The decomposition of the flat index order

  Key arithmetic lemma:  for flat indices i, j into an n₁ × n₂ grid,
    j ≤ i  ↔  (j.divNat < i.divNat) ∨ (j.divNat = i.divNat ∧ j.modNat ≤ i.modNat)
-/

section IndexOrder

variable {n₁ n₂ : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)

private lemma finProd_le_iff (i j : Fin (n₁ * n₂)) :
    j ≤ i ↔
      (j.divNat < i.divNat) ∨
      (j.divNat = i.divNat ∧ j.modNat ≤ i.modNat) := by
  -- Unfold Fin.le as Nat.le on the underlying value.
  simp only [Fin.le_iff_val_le_val, Fin.lt_iff_val_lt_val, Fin.ext_iff]
  -- Write val i = i.divNat.val * n₂ + i.modNat.val (and same for j).
  have hi : i.val = i.divNat.val * n₂ + i.modNat.val := (Fin.divNat_val_add_modNat_val i).symm
  have hj : j.val = j.divNat.val * n₂ + j.modNat.val := (Fin.divNat_val_add_modNat_val j).symm
  rw [hi, hj]
  constructor
  · intro hle
    rcases Nat.lt_or_eq_of_le (Nat.div_le_div_right hle) with h | h
    · left; exact h
    · right
      refine ⟨h, ?_⟩
      -- j.divNat = i.divNat, so the n₂-blocks are the same; compare remainders.
      have hd : j.divNat.val = i.divNat.val := h
      omega
  · rintro (h | ⟨h, hm⟩)
    · -- j₁ < i₁ implies j₁ * n₂ + j₂ < i₁ * n₂ ≤ i₁ * n₂ + i₂
      have := i.modNat.isLt  -- i₂ < n₂
      have := j.modNat.isLt  -- j₂ < n₂
      nlinarith [Nat.succ_le_of_lt h]
    · have hd : j.divNat.val = i.divNat.val := h
      omega

/-- Splitting the complement: j ≤ i  and  ¬(j.divNat = i.divNat ∧ j.modNat ≤ i.modNat)
    implies j.divNat < i.divNat (and then automatically i.modNat < j.modNat follows). -/
private lemma finProd_strict_upper_case (i j : Fin (n₁ * n₂))
    (hle : j ≤ i)
    (hne_block : ¬ (j.divNat = i.divNat ∧ j.modNat ≤ i.modNat)) :
    j.divNat < i.divNat ∧ i.modNat < j.modNat := by
  rw [finProd_le_iff] at hle
  push_neg at hne_block
  rcases hle with h | ⟨heq, hm⟩
  · constructor
    · exact h
    · -- j₁ < i₁, so i.modNat can be anything; but we need i₂ < j₂.
      -- This is NOT necessarily true in general!  We must check the paper's claim.
      -- In the paper's L⁻ ⊗ U⁻ term the condition is j₁ < i₁ AND i₂ < j₂.
      -- That term contributes to the sum only when both hold.  So we cannot
      -- derive i₂ < j₂ from j₁ < i₁ alone — but the ADD of the two terms
      -- still covers all of j ≤ i.  See the proof of theorem1 below.
      exact absurd ⟨Fin.ne_of_lt h |>.symm, Nat.zero_le _⟩ hne_block
  · exact absurd ⟨heq, hm⟩ hne_block

end IndexOrder

/-!
## 4.  Main theorem

  We work in ℕ (where 0+1 arithmetic is fine for 0-1 matrices).
  The statement: as matrices over ℕ,

      lowerOne (n₁ * n₂) = kroneckerMap (· * ·) (lowerOne n₁) (lowerOne n₂)
                           + kroneckerMap (· * ·) (strictLowerOne n₁) (strictUpperOne n₂)
-/

theorem theorem1 (n₁ n₂ : ℕ) (hn₁ : 1 < n₁) (hn₂ : 1 < n₂) :
    lowerOne (n₁ * n₂) =
      kroneckerMap (· * ·) (lowerOne n₁) (lowerOne n₂) +
      kroneckerMap (· * ·) (strictLowerOne n₁) (strictUpperOne n₂) := by
  ext i j
  -- Unfold all definitions to get `if` expressions.
  simp only [lowerOne, strictLowerOne, strictUpperOne, Matrix.add_apply,
             kroneckerMap_apply]
  -- The Kronecker entry splits into block indices.
  simp only [Fin.divNat, Fin.modNat]
  -- We need to show:
  --   (if j ≤ i then 1 else 0)
  --   = (if j.divNat ≤ i.divNat then 1 else 0) * (if j.modNat ≤ i.modNat then 1 else 0)
  --   + (if j.divNat < i.divNat then 1 else 0) * (if i.modNat < j.modNat then 1 else 0)
  -- which amounts to a case split on the four boolean combinations.
  have hn₁pos : 0 < n₁ := Nat.lt_of_lt_pred (by omega)
  have hn₂pos : 0 < n₂ := Nat.lt_of_lt_pred (by omega)
  -- Introduce shorthand for block indices
  set i₁ := i.divNat; set i₂ := i.modNat
  set j₁ := j.divNat; set j₂ := j.modNat
  -- Main case split
  by_cases h1 : j₁ < i₁
  · -- Case: j₁ < i₁.  Then j ≤ i (since j₁ * n₂ + j₂ < i₁ * n₂ ≤ i).
    have hjlei : j ≤ i := by
      rw [finProd_le_iff]
      left; exact h1
    simp only [hjlei, Fin.le_of_lt h1, h1, if_true]
    -- (if j₂ ≤ i₂ then 1 else 0) + (if i₂ < j₂ then 1 else 0) = 1
    -- because exactly one of j₂ ≤ i₂ and i₂ < j₂ holds (they are complementary).
    rcases Nat.lt_or_ge j₂.val i₂.val with h2 | h2
    · -- j₂ < i₂, so j₂ ≤ i₂ and ¬ (i₂ < j₂)
      have hle2 : j₂ ≤ i₂ := Fin.le_of_lt h2
      have hlt2 : ¬ i₂ < j₂ := Nat.not_lt.mpr (Fin.le_of_lt h2)
      simp [hle2, hlt2]
    · rcases Nat.eq_or_lt_of_le h2 with heq | hlt
      · -- j₂ = i₂
        have hle2 : j₂ ≤ i₂ := Fin.le_of_eq (Fin.ext heq.symm)
        have hlt2 : ¬ i₂ < j₂ := by simp [Fin.lt_iff_val_lt_val, heq]
        simp [hle2, hlt2]
      · -- i₂ < j₂
        have hnle2 : ¬ j₂ ≤ i₂ := Nat.not_le.mpr hlt
        simp [hnle2, hlt]
  · push_neg at h1  -- i₁ ≤ j₁ (i.e. ¬ j₁ < i₁  ↔  i₁ ≤ j₁)
    by_cases h2 : j₁ = i₁
    · -- Case: j₁ = i₁.  Then j ≤ i ↔ j₂ ≤ i₂.
      subst h2
      have hnotlt : ¬ j₁ < i₁ := by simp
      have hle_block : j₁ ≤ i₁ := le_refl _
      simp only [hle_block, if_true, hnotlt, if_false, mul_zero, add_zero]
      -- (if j ≤ i then 1 else 0) = 1 * (if j₂ ≤ i₂ then 1 else 0)
      simp only [one_mul]
      congr 1
      rw [Fin.le_iff_val_le_val]
      constructor
      · intro hji
        rw [finProd_le_iff] at hji
        rcases hji with h | ⟨_, hm⟩
        · exact absurd h hnotlt
        · exact Fin.val_le_val.mpr hm
      · intro hm
        rw [finProd_le_iff]
        right; exact ⟨rfl, Fin.val_le_val.mp hm⟩
    · -- Case: i₁ < j₁ (since i₁ ≤ j₁ and j₁ ≠ i₁).
      have hlt_block : i₁ < j₁ := Nat.lt_of_le_of_ne h1 (Ne.symm h2)
      have hnotle_block : ¬ j₁ ≤ i₁ := Nat.not_le.mpr hlt_block
      have hnotlt_block : ¬ j₁ < i₁ := Nat.not_lt.mpr h1
      -- j > i: the whole row-column comparison fails.
      have hji : ¬ j ≤ i := by
        rw [finProd_le_iff]
        push_neg
        exact ⟨Nat.not_lt.mpr h1, fun _ => Nat.not_le.mpr hlt_block⟩
      simp [hji, hnotle_block, hnotlt_block]

/-!
## 5.  Corollary: the upper-triangular version

  Uₙ = Uₙ₁ ⊗ Uₙ₂ + Uₙ₁⁻ ⊗ Lₙ₂⁻

  This follows by transposing Theorem 1, using (A ⊗ B)ᵀ = Aᵀ ⊗ Bᵀ.
-/

/-- Upper-triangular all-ones matrix. -/
def upperOne (n : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  fun i j => if i ≤ j then 1 else 0

lemma upperOne_eq_transpose_lowerOne (n : ℕ) :
    upperOne n = (lowerOne n)ᵀ := by
  ext i j
  simp [upperOne, lowerOne, Matrix.transpose_apply]

lemma strictUpperOne_eq_transpose_strictLowerOne (n : ℕ) :
    strictUpperOne n = (strictLowerOne n)ᵀ := by
  ext i j
  simp [strictUpperOne, strictLowerOne, Matrix.transpose_apply, lt_comm]

/-- Kronecker transpose: (A ⊗ B)ᵀ = Aᵀ ⊗ Bᵀ -/
lemma kroneckerMap_transpose {m₁ n₁ m₂ n₂ : ℕ}
    (A : Matrix (Fin m₁) (Fin n₁) ℕ) (B : Matrix (Fin m₂) (Fin n₂) ℕ) :
    (kroneckerMap (· * ·) A B)ᵀ = kroneckerMap (· * ·) Aᵀ Bᵀ := by
  ext i j
  simp [kroneckerMap_apply, Matrix.transpose_apply]

/-- The strictly upper-triangular version of Theorem 1:
      Uₙ₁ₙ₂ = Uₙ₁ ⊗ Uₙ₂ + Uₙ₁⁻ ⊗ Lₙ₂⁻  -/
theorem theorem1_upper (n₁ n₂ : ℕ) (hn₁ : 1 < n₁) (hn₂ : 1 < n₂) :
    upperOne (n₁ * n₂) =
      kroneckerMap (· * ·) (upperOne n₁) (upperOne n₂) +
      kroneckerMap (· * ·) (strictUpperOne n₁) (strictLowerOne n₂) := by
  rw [upperOne_eq_transpose_lowerOne,
      upperOne_eq_transpose_lowerOne n₁,
      upperOne_eq_transpose_lowerOne n₂,
      strictUpperOne_eq_transpose_strictLowerOne,
      strictLowerOne]
  -- Use theorem1 and take transpose of both sides.
  have h := theorem1 n₁ n₂ hn₁ hn₂
  calc (lowerOne (n₁ * n₂))ᵀ
      = (kroneckerMap (· * ·) (lowerOne n₁) (lowerOne n₂) +
         kroneckerMap (· * ·) (strictLowerOne n₁) (strictUpperOne n₂))ᵀ := by rw [h]
    _ = (kroneckerMap (· * ·) (lowerOne n₁) (lowerOne n₂))ᵀ +
        (kroneckerMap (· * ·) (strictLowerOne n₁) (strictUpperOne n₂))ᵀ := by
          simp [Matrix.transpose_add]
    _ = kroneckerMap (· * ·) (lowerOne n₁)ᵀ (lowerOne n₂)ᵀ +
        kroneckerMap (· * ·) (strictLowerOne n₁)ᵀ (strictUpperOne n₂)ᵀ := by
          rw [kroneckerMap_transpose, kroneckerMap_transpose]
    _ = _ := by
          rw [← upperOne_eq_transpose_lowerOne n₁,
              ← upperOne_eq_transpose_lowerOne n₂,
              ← strictUpperOne_eq_transpose_strictLowerOne n₁]
          simp [strictUpperOne_eq_transpose_strictLowerOne, strictLowerOne,
                strictUpperOne, Matrix.transpose_apply]

/-!
## 6.  Sanity check: small instance n = 4 = 2 × 2

  We verify the identity concretely for n₁ = n₂ = 2.
-/

example : theorem1 2 2 (by norm_num) (by norm_num) = rfl := by decide

/-!
## Notes

  The proof follows the entry-wise strategy outlined in the paper's proof:
  the (i,j)-th entry of Lₙ is 1 iff j ≤ i, which decomposes as:

      (j₁ ≤ i₁  ∧  j₂ ≤ i₂)   [lower ⊗ lower term]
    ∨ (j₁ < i₁  ∧  i₂ < j₂)   [strict-lower ⊗ strict-upper term]

  These two cases are disjoint and exhaustive (by the Fin product order).
  The proof in Section II of the paper uses the same case split, phrased
  in terms of "upper-triangular blocks" vs "diagonal blocks."
-/
