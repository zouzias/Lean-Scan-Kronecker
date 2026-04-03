import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Parity
import Batteries.Data.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Order.Basic
import Mathlib.Order.RelClasses
import Mathlib.Logic.Equiv.Fin.Basic
import Init.Data.Nat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Equiv.Fin.Basic

import LeanScanKronecker.Matrices


open Matrix Kronecker

open Fin


variable {R : Type*} [Semiring R]

variable (A B : Matrix (Fin 2) (Fin 2) R)

#check Matrix.kronecker        -- explicit name
#check (· ⊗ₖ ·)               -- infix notation (after open Kronecker)
-- The defining equation: entry at ((i,k), (j,l))
#check Matrix.kronecker_apply
-- kronecker_apply : (A ⊗ₖ B) (i, k) (j, l) = A i j * B k l

#check kronecker A B
#check Matrix.ext                          -- extensionality


open Matrix


#check finProdFinEquiv
example : Fin 2 × Fin 3 ≃ Fin (2 * 3) := finProdFinEquiv

/-! ## Step 1: pure ℕ arithmetic lemmas about div/mod -/

-- Lemma: k = k / n * n + k % n.
private lemma nat_dm (k n : ℕ) : k = k / n * n + k % n := by
  have h := (Nat.div_add_mod k n).symm
  rwa [Nat.mul_comm] at h


/-- i/n = j/n and i%n ≥ j%n implies i ≥ j -/
private lemma ge_of_eq_div_ge_mod {n : ℕ} {i j : ℕ}
    (hdiv : i / n = j / n) (hmod : i % n ≥ j % n) : i ≥ j := by
  have hi := nat_dm i n
  have hj := nat_dm j n
  -- After hdiv ▸ hj: j = i/n * n + j%n, and i = i/n*n + i%n ≥ j/n*n + j%n
  linarith [hdiv ▸ hj]


/-! ## Step 2: unpack finProdFinEquiv.symm into div/mod -/

private lemma symm_fst {n₁ n₂ : ℕ} (k : Fin (n₁ * n₂)) :
    (finProdFinEquiv.symm k).1.val = k.val / n₂ := by
  simp [finProdFinEquiv, Fin.divNat]

private lemma symm_snd {n₁ n₂ : ℕ} (k : Fin (n₁ * n₂)) :
    (finProdFinEquiv.symm k).2.val = k.val % n₂ := by
  simp [finProdFinEquiv, Fin.modNat]



/-! ## Step 2: Matrix definitions and decomposition lemmas

  This section defines basic matrices (all-ones J, identity I, triangular L/U) and proves
  key lemmas about their structure, particularly focusing on how lower-triangular matrices
  decompose under Kronecker products in the product index order.
  -/

-- Convenient local notation (mirrors the paper's Lₙ, Uₙ, L⁻ₙ, U⁻ₙ)
notation "L⁻" => L_strict
notation "U⁻" => U_strict


private lemma L_transpose_eq_U (n : ℕ) :
  Matrix.transpose (L n) = U n := by
  unfold Matrix.transpose of L
  unfold U
  rfl

private lemma U_transpose_eq_L (n : ℕ) :
  Matrix.transpose (U n) = L n := by
  unfold Matrix.transpose of U
  unfold L
  rfl


#check kronecker (L 2) (L 2)

#check Matrix.transpose (L 2) = U 2



theorem sobczyk_zouzias_thm {n₁ n₂ n : ℕ} (n1_pos: n₁ > 1) (n2_pos : n₂ > 1) (n_eq: n = n₁ * n₂) :
  L_ones_decomp n1_pos n2_pos n_eq := by
  ext i j
  simp only [L, Matrix.reindex_apply]
  rcases lt_trichotomy i j with h_i_lt_j | h_i_eq_j | h_i_gt_j
  · simp [L, L_strict, U_strict]
    simp [show ¬ j ≤ i from by omega]
    have hmodj : (j.modNat : ℕ) = (j : ℕ) % n₂ := rfl
    have hdivj : (j.divNat : ℕ) = (j : ℕ) / n₂ := rfl
    have hmodi : (i.modNat : ℕ) = (i : ℕ) % n₂ := rfl
    have hdivi : (i.divNat : ℕ) = (i : ℕ) / n₂ := rfl
    sorry
  · simp [L]
    -- Now left hand side is one!
    simp[L_strict, U_strict]
    simp [show j ≤ i from by omega]
    unfold divNat
    have i_1 := j.modNat
    rw [j.modNat]
    simp
    sorry
  · simp [L]
    -- Now left hand side is zero!
    simp[L_strict, U_strict]
    unfold modNat
    unfold divNat
    have i_1 := j % n₂
    simp [show j ≤ i from by omega]
    sorry


/--
theorem sobczyk_zouzias_thm {n₁ n₂ n : ℕ} (n1_pos: n₁ > 1) (n2_pos : n₂ > 1) (n_eq: n = n₁ * n₂) :
  L_ones_decomp n1_pos n2_pos n_eq := by
  ext i j
  rcases lt_trichotomy i j with h | h | h
  · -- Case 1: i < j (strictly above diagonal)
    -- LHS: L(n)[i,j] = 0  since ¬(i ≥ j)
    -- RHS: both Kronecker terms vanish
    have h_not_ge : ¬ (i ≥ j) := Fin.not_le.mpr h
    simp only [L, h_not_ge, ite_false]
    simp [L, U_strict, L_strict]
    split_ifs <;> omega
    sorry
  · -- Case 2: i = j (on the diagonal)
    -- LHS: L(n)[i,i] = 1
    -- RHS: diagonal Kronecker term contributes exactly 1
    subst h
    simp [L, le_refl, U_strict, L_strict]
  · -- Case 3: i > j (strictly below diagonal)
    -- LHS: L(n)[i,j] = 1  since i ≥ j
    -- RHS: at least one Kronecker term contributes 1
    have h_ge : i ≥ j := Fin.le_of_lt h
    simp [h_ge, L, U_strict, L_strict, modNat, divNat]
    by_cases h_cases: j % n₂  ≤ i % n₂
    · -- Subcase 3a: j%n₂ ≤ i%n₂
      -- Then the first Kronecker term contributes 1, and the second contributes 0
      simp [h_cases]
    · -- Subcase 3b: j%n₂ > i%n₂
      -- Then the first Kronecker term contributes 0, and the second contributes 1
      have h_cases' : i % n₂ < j % n₂ := Nat.lt_of_not_le h_cases
      simp [h_cases', if_neg (h_cases)]
      have hj := Nat.div_add_mod j n₂
      have hi := Nat.div_add_mod i n₂
      sorry
--/
