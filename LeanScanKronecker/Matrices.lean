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
import Mathlib.LinearAlgebra.Matrix.Block

open Matrix Kronecker

open Fin

variable {n : ℕ} {R : Type*} [Semiring R]


section Definitions

variable (A B : Matrix (Fin n) (Fin n) R)

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

/-- All-ones matrix: Jₙ(i,j) = 1 for all i j -/
def J (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun _ _ => 1

/-- Identity matrix -/
def I (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i == j then 1 else 0

-- Lower triangular all-ones matrix
def L (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i ≥ j then 1 else 0

-- Upper triangular all-ones matrix
def U (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i ≤ j then 1 else 0

-- Strictly lower triangular all-ones matrix
def L_strict (n : ℕ) : Matrix (Fin n) (Fin n) ℤ  :=
  fun i j => if i > j then 1 else 0

-- Strictly upper triangular all-ones matrix
def U_strict (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if i < j then 1 else 0

end Definitions

def IsUpperTriangular₁ (M : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ i j : Fin n, i > j → M i j = 0

/-- Predicate 2: using Mathlib's BlockTriangular with the identity block assignment.
    `BlockTriangular M id` says: b j < b i → M i j = 0, i.e. j < i → M i j = 0. -/
def IsUpperTriangular2 (M : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  M.BlockTriangular id

/-! ## Step 2: Lemmata of Kronecker matrices -/


/-- U(n₁) ⊗ U(n₂) is upper-triangular in the product order:
    entry (i₁,i₂),(j₁,j₂) is 1 iff i₁ ≤ j₁ and i₂ ≤ j₂ -/
lemma U_kron_U_upper_part_is_one (n₁ n₂ : ℕ)
    (i j : Fin n₁) (k l : Fin n₂)
    (h1 : i ≤ j) (h2 : k ≤ l) :
    (U n₁ ⊗ₖ U n₂) (i, k) (j, l) = 1 := by
  simp [U, h1, h2]

lemma L_kron_L_lower_part_is_one (n₁ n₂ : ℕ)
    (i j : Fin n₁) (k l : Fin n₂)
    (h1 : i ≥ j) (h2 : k ≥ l) :
    (L n₁ ⊗ₖ L n₂) (i, k) (j, l) = 1 := by
  simp [L, h1, h2]

/-- U(n₁) ⊗ U(n₂) is zero outside the upper-triangular region   -/
lemma U_kron_U_zero (n₁ n₂ : ℕ)
    (i j : Fin n₁) (k l : Fin n₂)
    (lower_part : ¬(i ≤ j) ∨ ¬(k ≤ l)) :
    (U n₁ ⊗ₖ U n₂) (i, k) (j, l) = 0 := by
  simp only [kronecker_apply, U]
  rcases lower_part with h | h <;> simp [h]

lemma L_strict_transpose_eq_U_strict (n : ℕ) : (L_strict n)ᵀ = U_strict n := by
  ext i j
  simp [Matrix.transpose_apply, L_strict, U_strict, gt_iff_lt]

lemma U_strict_transpose_eq_L_strict (n : ℕ) : (U_strict n)ᵀ = L_strict n := by
  ext i j
  simp [Matrix.transpose_apply, L_strict, U_strict, gt_iff_lt]


/-- Uₙ = Iₙ + U⁻ₙ  (split diagonal from strict upper part) -/
lemma U_eq_I_add_U_strict (n : ℕ) :
    U n = I n + U_strict n := by
  ext i j
  simp only [U]
  -- Goal: (if i ≤ j then 1 else 0) = (if i == j then 1 else 0) + (if i < j then 1 else 0)
  -- Note: I uses `==` (BEq / decidable equality), U and U_strict use `≤` and `<`
  rcases lt_trichotomy i j with h | h | h
  · -- i < j : LHS = 1,  I-term = 0  (i ≠ j),  U_strict-term = 1
    have hne  : ¬ (i == j) := by simp [Fin.ext_iff, Nat.ne_of_lt h]
    have hle  : i ≤ j      := Nat.le_of_lt h
    simp [hle]
    unfold I
    unfold U_strict
    simp [h, hne]
  · -- i = j : LHS = 1,  I-term = 1  (i == j is true),  U_strict-term = 0
    subst h
    simp [I, U_strict]
  · -- i > j : LHS = 0,  I-term = 0  (i ≠ j),  U_strict-term = 0
    have hne  : ¬ (i == j) := by simp [Fin.ext_iff, Nat.ne_of_gt h]
    have hnle : ¬ (i ≤ j)  := Nat.not_le.mpr h
    have hnlt : ¬ (i < j)  := Nat.not_lt.mpr (Nat.le_of_lt h)
    simp [hnle, U_strict, I, hne, hnlt]

/-- J = U + L_strict  (all-ones = upper-tri + strict-lower-tri) -/
lemma J_eq_U_add_L_strict (n : ℕ) :
    J n = U n + L_strict n := by
  ext i j
  simp only [J]
  by_cases h : i ≤ j
  · unfold U
    unfold L_strict
    simp [h]
  · unfold U
    unfold L_strict
    simp [h]


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



def L_ones_decomp {n₁ n₂ : ℕ} (n1_pos: n₁ > 1) (n2_pos : n₂ > 1) : Prop :=
   L (n₁ * n₂) = Matrix.reindex
      finProdFinEquiv
      finProdFinEquiv ((kronecker (L n₁) (L n₂)) + (kronecker (L_strict n₁) (U_strict n₂)))


---abbrev kron_flatten :=
---  Matrix.reindex finProdFinEquiv finProdFinEquiv

abbrev kron_flat {R : Type*} {n₁ n₂ : ℕ} (A : Matrix (Fin n₁ × Fin n₂) (Fin n₁ × Fin n₂) R)
: Matrix (Fin (n₁ * n₂)) (Fin (n₁ * n₂)) R :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv A

def L_ones_decomp_flat (n₁ n₂ : Nat) : Prop :=
   L (n₁ * n₂) = kron_flat ((kronecker (L n₁) (L n₂)) + (kronecker (L_strict n₁) (U_strict n₂)))
