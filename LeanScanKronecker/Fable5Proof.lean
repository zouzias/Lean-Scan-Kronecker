/-
====================================================================
  Prefix Sums via Kronecker Products — Theorem 1, formalized in Lean 4.

  Reference:
    A. Sobczyk, A. Zouzias, "Prefix Sums via Kronecker Products",
    arXiv:2512.16309, Section II, Theorem 1.

  Statement (Eq. (4) of the paper).  For n = n1 * n2:

      L_n = L_{n1} ⊗ L_{n2} + L⁻_{n1} ⊗ U⁻_{n2}
          = I_{n1} ⊗ L_{n2} + L⁻_{n1} ⊗ 1_{n2} 1_{n2}ᵀ ,

  and, equivalently,

      U_n = U_{n1} ⊗ U_{n2} + U⁻_{n1} ⊗ L⁻_{n2} ,

  where L_s (resp. U_s) is the s×s lower (resp. upper) triangular
  all-ones matrix, L⁻_s = L_s − I_s and U⁻_s = U_s − I_s are their
  strict versions, and ⊗ is the Kronecker product.

  The Lean proof follows the paper's proof step by step:

    Step (a).  Reduce Eq. (4) to Eq. (5),
                  U_n = U_{n1} ⊗ 1 1ᵀ − I_{n1} ⊗ L⁻_{n2},
               via the algebraic chain of the paper:
                  U ⊗ 1 1ᵀ − I ⊗ L⁻
                = U ⊗ (U + L⁻) − I ⊗ L⁻        (1 1ᵀ = U + L⁻)
                = U ⊗ U + (U − I) ⊗ L⁻          (bilinearity of ⊗)
                = U ⊗ U + U⁻ ⊗ L⁻.
                                             (`eq5_rhs` below)
    Step (b).  Prove Eq. (5) entrywise, exactly as in the paper:
               the upper-triangular part of the RHS is all ones,
               its off-diagonal strictly-lower blocks vanish, and
               its diagonal n2×n2 blocks are 1 1ᵀ − L⁻ = U_{n2}.
                                             (`eq5` below)
    Step (c).  Obtain the L-versions by transposition, using
               (A ⊗ B)ᵀ = Aᵀ ⊗ Bᵀ and Lᵀ = U.
                                             (`theorem1_L` below)

  Indexing.  A Kronecker product is naturally indexed by pairs:
  (A ⊗ B)[(i₁,i₂),(j₁,j₂)] = A[i₁,j₁] · B[i₂,j₂], where the pair
  (i₁,i₂) stands for the flat row index n₂·i₁ + i₂ (block-major, as
  in the block picture [aᵢⱼ B] of the paper).  We therefore state the
  identities over the index set `Fin n1 × Fin n2`, on which L_n and
  U_n become `Lblock` / `Ublock`: triangularity with respect to the
  lexicographic order, i.e. the order induced by the flat index.
  The final section constructs the explicit order isomorphism
  `encode : Fin n1 × Fin n2 → Fin (n1*n2)` (with inverse `decode`)
  and restates Theorem 1 verbatim for the flat matrix `L (n1*n2)`
  (`theorem1_flat`, `theorem1_flat'`).

  Entries live in ℤ; the identities hold verbatim over any
  commutative ring (ℤ is the initial one, so nothing is lost).

  The file is self-contained: it compiles with plain Lean 4
  (tested with Lean 4.21.0), no Mathlib required.
====================================================================
-/

namespace KroneckerPrefixSum

/-! ### Matrices, Kronecker products, triangular all-ones matrices -/

/-- Square integer matrices indexed by `α`. -/
abbrev Mat (α : Type) : Type := α → α → Int

instance {α : Type} : Add (Mat α) := ⟨fun A B i j => A i j + B i j⟩
instance {α : Type} : Sub (Mat α) := ⟨fun A B i j => A i j - B i j⟩

@[simp] theorem add_apply {α : Type} (A B : Mat α) (i j : α) :
    (A + B) i j = A i j + B i j := rfl

@[simp] theorem sub_apply {α : Type} (A B : Mat α) (i j : α) :
    (A - B) i j = A i j - B i j := rfl

/-- Transpose. -/
def transpose {α : Type} (A : Mat α) : Mat α := fun i j => A j i

/-- Kronecker product.  The row index `(i₁, i₂)` corresponds to the flat
row index `n₂ * i₁ + i₂` (block-major), matching the block matrix
`[a_{i,j} • B]` of the paper. -/
def kron {α β : Type} (A : Mat α) (B : Mat β) : Mat (α × β) :=
  fun i j => A i.1 j.1 * B i.2 j.2

/-- `L n`: the lower triangular all-ones matrix `L_n`. -/
def L (n : Nat) : Mat (Fin n) := fun i j => if j.val ≤ i.val then 1 else 0

/-- `U n`: the upper triangular all-ones matrix `U_n`. -/
def U (n : Nat) : Mat (Fin n) := fun i j => if i.val ≤ j.val then 1 else 0

/-- `Lm n`: the strictly lower triangular all-ones matrix `L⁻_n = L_n - I_n`. -/
def Lm (n : Nat) : Mat (Fin n) := fun i j => if j.val < i.val then 1 else 0

/-- `Um n`: the strictly upper triangular all-ones matrix `U⁻_n = U_n - I_n`. -/
def Um (n : Nat) : Mat (Fin n) := fun i j => if i.val < j.val then 1 else 0

/-- `Id n`: the identity matrix `I_n`. -/
def Id (n : Nat) : Mat (Fin n) := fun i j => if i.val = j.val then 1 else 0

/-- `J n`: the all-ones matrix `1_n 1_nᵀ`. -/
def J (n : Nat) : Mat (Fin n) := fun _ _ => 1

/-- `L_{n₁·n₂}` viewed on pair indices: the entry at `((i₁,i₂),(j₁,j₂))` is `1`
iff the flat column index `n₂·j₁+j₂` is at most the flat row index
`n₂·i₁+i₂`, i.e. iff `(j₁,j₂) ≤ (i₁,i₂)` lexicographically.
(`L_encode` below proves that this is literally `L (n1*n2)` transported
along the flat-index bijection.) -/
def Lblock (n1 n2 : Nat) : Mat (Fin n1 × Fin n2) :=
  fun i j =>
    if j.1.val < i.1.val ∨ (j.1.val = i.1.val ∧ j.2.val ≤ i.2.val) then 1 else 0

/-- `U_{n₁·n₂}` on pair indices (transpose of `Lblock`). -/
def Ublock (n1 n2 : Nat) : Mat (Fin n1 × Fin n2) :=
  fun i j =>
    if i.1.val < j.1.val ∨ (i.1.val = j.1.val ∧ i.2.val ≤ j.2.val) then 1 else 0

/-! ### Decompositions of the all-ones matrix

In the first equality of the paper's proof, "we decomposed the all-ones
matrix into its upper triangular and strictly lower triangular all-ones
parts":  `1 1ᵀ = U + L⁻`.  We also record the analogous splittings
`1 1ᵀ = L + U⁻`, `L = I + L⁻` and `U − I = U⁻` used in the algebra. -/

theorem J_eq_U_add_Lm (n : Nat) : J n = U n + Lm n := by
  funext i j
  simp only [J, U, Lm, add_apply]
  by_cases h1 : i.val ≤ j.val <;> by_cases h2 : j.val < i.val <;>
    simp [h1, h2] <;> omega

theorem J_eq_L_add_Um (n : Nat) : J n = L n + Um n := by
  funext i j
  simp only [J, L, Um, add_apply]
  by_cases h1 : j.val ≤ i.val <;> by_cases h2 : i.val < j.val <;>
    simp [h1, h2] <;> omega

theorem L_eq_Id_add_Lm (n : Nat) : L n = Id n + Lm n := by
  funext i j
  simp only [L, Id, Lm, add_apply]
  by_cases h1 : j.val ≤ i.val <;> by_cases h2 : i.val = j.val <;>
      by_cases h3 : j.val < i.val <;>
    simp [h1, h2, h3, Nat.lt_irrefl, Nat.le_refl] <;> omega

theorem U_sub_Id_eq_Um (n : Nat) : U n - Id n = Um n := by
  funext i j
  simp only [U, Id, Um, sub_apply]
  by_cases h1 : i.val ≤ j.val <;> by_cases h2 : i.val = j.val <;>
      by_cases h3 : i.val < j.val <;>
    simp [h1, h2, h3, Nat.lt_irrefl, Nat.le_refl] <;> omega

/-! ### Bilinearity of the Kronecker product, pointwise matrix algebra

These play the role of the "Kronecker properties" from [Neu69] that the
paper's proof invokes to "rearrange terms". -/

theorem kron_add_left {α β : Type} (A B : Mat α) (C : Mat β) :
    kron (A + B) C = kron A C + kron B C := by
  funext i j
  simp only [kron, add_apply]
  exact Int.add_mul _ _ _

theorem kron_add_right {α β : Type} (A : Mat α) (B C : Mat β) :
    kron A (B + C) = kron A B + kron A C := by
  funext i j
  simp only [kron, add_apply]
  exact Int.mul_add _ _ _

theorem kron_sub_left {α β : Type} (A B : Mat α) (C : Mat β) :
    kron (A - B) C = kron A C - kron B C := by
  funext i j
  simp only [kron, sub_apply]
  exact Int.sub_mul _ _ _

theorem mat_add_sub {α : Type} (X Y Z : Mat α) :
    (X + Y) - Z = X + (Y - Z) := by
  funext i j
  simp only [add_apply, sub_apply]
  omega

theorem mat_add_assoc {α : Type} (X Y Z : Mat α) :
    X + Y + Z = X + (Y + Z) := by
  funext i j
  simp only [add_apply]
  omega

/-! ### Step (a): the right-hand side of Eq. (5) equals `U ⊗ U + U⁻ ⊗ L⁻`

This is the displayed chain of equalities in the paper's proof:

    U_{n1} ⊗ 1 1ᵀ − I_{n1} ⊗ L⁻_{n2}
      = U_{n1} ⊗ (U_{n2} + L⁻_{n2}) − I_{n1} ⊗ L⁻_{n2}
      = U_{n1} ⊗ U_{n2} + (U_{n1} − I_{n1}) ⊗ L⁻_{n2}
      = U_{n1} ⊗ U_{n2} + U⁻_{n1} ⊗ L⁻_{n2}.
-/

theorem eq5_rhs (n1 n2 : Nat) :
    kron (U n1) (J n2) - kron (Id n1) (Lm n2)
      = kron (U n1) (U n2) + kron (Um n1) (Lm n2) := by
  calc
    kron (U n1) (J n2) - kron (Id n1) (Lm n2)
        = kron (U n1) (U n2 + Lm n2) - kron (Id n1) (Lm n2) := by
          rw [← J_eq_U_add_Lm]
    _   = (kron (U n1) (U n2) + kron (U n1) (Lm n2)) - kron (Id n1) (Lm n2) := by
          rw [kron_add_right]
    _   = kron (U n1) (U n2) + (kron (U n1) (Lm n2) - kron (Id n1) (Lm n2)) :=
          mat_add_sub _ _ _
    _   = kron (U n1) (U n2) + kron (U n1 - Id n1) (Lm n2) := by
          rw [kron_sub_left]
    _   = kron (U n1) (U n2) + kron (Um n1) (Lm n2) := by
          rw [U_sub_Id_eq_Um]

/-! ### Step (b): Eq. (5) itself,  `U_n = U_{n1} ⊗ 1 1ᵀ − I_{n1} ⊗ L⁻_{n2}`

Proved entrywise, following the paper's two-part argument:

  * upper-triangular part (block column ≥ block row): `I ⊗ L⁻` is
    strictly lower triangular by construction while every entry of
    the upper part of `U ⊗ 1 1ᵀ` is one, so the difference is one;
  * strictly-lower part: off-diagonal lower blocks of both Kronecker
    summands vanish, and each diagonal n₂×n₂ block equals
    `1 1ᵀ − L⁻_{n2} = U_{n2}`.

In the formal proof the "block position" case split is
`i₁ < j₁  /  i₁ = j₁  /  i₁ > j₁`, and the inner-index split handles
the diagonal blocks. -/

theorem eq5 (n1 n2 : Nat) :
    kron (U n1) (J n2) - kron (Id n1) (Lm n2) = Ublock n1 n2 := by
  funext i j
  simp only [kron, sub_apply, U, J, Id, Lm, Ublock]
  by_cases h0 : i.1.val ≤ j.1.val <;>
    by_cases h1 : i.1.val < j.1.val <;>
      by_cases h2 : i.1.val = j.1.val <;>
        by_cases h3 : j.2.val < i.2.val <;>
          by_cases h4 : i.2.val ≤ j.2.val <;>
    simp [h0, h1, h2, h3, h4, Nat.lt_irrefl, Nat.le_refl] <;> omega

/-! ### Theorem 1, U-version:  `U_n = U_{n1} ⊗ U_{n2} + U⁻_{n1} ⊗ L⁻_{n2}` -/

theorem theorem1_U (n1 n2 : Nat) :
    Ublock n1 n2 = kron (U n1) (U n2) + kron (Um n1) (Lm n2) :=
  (eq5 n1 n2).symm.trans (eq5_rhs n1 n2)

/-! ### Step (c): transposition

`(A ⊗ B)ᵀ = Aᵀ ⊗ Bᵀ` ([Neu69, Eq. 2.4]) and transposition swaps the
L- and U-matrices.  All of these are definitional equalities here. -/

theorem transpose_kron {α β : Type} (A : Mat α) (B : Mat β) :
    transpose (kron A B) = kron (transpose A) (transpose B) := rfl

theorem transpose_add {α : Type} (A B : Mat α) :
    transpose (A + B) = transpose A + transpose B := rfl

theorem transpose_U (n : Nat) : transpose (U n) = L n := rfl
theorem transpose_L (n : Nat) : transpose (L n) = U n := rfl
theorem transpose_Um (n : Nat) : transpose (Um n) = Lm n := rfl
theorem transpose_Lm (n : Nat) : transpose (Lm n) = Um n := rfl
theorem transpose_Id (n : Nat) : transpose (Id n) = Id n := by
  funext i j
  simp only [transpose, Id]
  by_cases h : i.val = j.val
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (fun hh => h hh.symm), if_neg h]
theorem transpose_Ublock (n1 n2 : Nat) :
    transpose (Ublock n1 n2) = Lblock n1 n2 := rfl

/-! ### Theorem 1, Eq. (4):  `L_n = L_{n1} ⊗ L_{n2} + L⁻_{n1} ⊗ U⁻_{n2}` -/

theorem theorem1_L (n1 n2 : Nat) :
    Lblock n1 n2 = kron (L n1) (L n2) + kron (Lm n1) (Um n2) := by
  have h := congrArg transpose (theorem1_U n1 n2)
  rw [transpose_Ublock, transpose_add, transpose_kron, transpose_kron,
      transpose_U n1, transpose_U n2, transpose_Um n1, transpose_Lm n2] at h
  exact h

/-! ### Theorem 1, Eq. (4), second form:
`L_n = I_{n1} ⊗ L_{n2} + L⁻_{n1} ⊗ 1_{n2} 1_{n2}ᵀ`

Obtained from the first form by splitting `L_{n1} = I + L⁻` and
recombining `L_{n2} + U⁻_{n2} = 1 1ᵀ`. -/

theorem theorem1_L' (n1 n2 : Nat) :
    Lblock n1 n2 = kron (Id n1) (L n2) + kron (Lm n1) (J n2) := by
  calc
    Lblock n1 n2
        = kron (L n1) (L n2) + kron (Lm n1) (Um n2) := theorem1_L n1 n2
    _   = kron (Id n1 + Lm n1) (L n2) + kron (Lm n1) (Um n2) := by
          rw [← L_eq_Id_add_Lm]
    _   = kron (Id n1) (L n2) + kron (Lm n1) (L n2) + kron (Lm n1) (Um n2) := by
          rw [kron_add_left]
    _   = kron (Id n1) (L n2) + (kron (Lm n1) (L n2) + kron (Lm n1) (Um n2)) :=
          mat_add_assoc _ _ _
    _   = kron (Id n1) (L n2) + kron (Lm n1) (L n2 + Um n2) := by
          rw [← kron_add_right]
    _   = kron (Id n1) (L n2) + kron (Lm n1) (J n2) := by
          rw [← J_eq_L_add_Um]

/-! ### The flat index set `Fin (n1 * n2)`

`Lblock`/`Ublock` above are `L_n`/`U_n` written on pair indices.  Here we
make this precise: `encode (i₁,i₂) = n₂·i₁ + i₂` is a bijection
`Fin n1 × Fin n2 → Fin (n1·n2)` transporting the lexicographic order to
the natural order (`encode_le`), so that Theorem 1 can be stated for the
honest flat matrix `L (n1*n2)` (`theorem1_flat`, `theorem1_flat'`). -/

section FlatIndex

variable {n1 n2 : Nat}

/-- The block-major flat index: `encode (i₁, i₂) = n₂ * i₁ + i₂`. -/
def encode (p : Fin n1 × Fin n2) : Fin (n1 * n2) :=
  ⟨n2 * p.1.val + p.2.val, by
    have h1 : n2 * (p.1.val + 1) = n2 * p.1.val + n2 := Nat.mul_succ n2 p.1.val
    have h2 : n2 * (p.1.val + 1) ≤ n2 * n1 :=
      Nat.mul_le_mul (Nat.le_refl n2) p.1.isLt
    have h3 : n2 * n1 = n1 * n2 := Nat.mul_comm n2 n1
    have h4 := p.2.isLt
    omega⟩

/-- Comparison of flat indices is the lexicographic comparison of the
block/offset pairs.  (This is where `b, d < n₂` is used.) -/
theorem flat_le_iff {a b c d : Nat} (hb : b < n2) (hd : d < n2) :
    n2 * a + b ≤ n2 * c + d ↔ a < c ∨ (a = c ∧ b ≤ d) := by
  constructor
  · intro h
    cases Nat.lt_trichotomy a c with
    | inl hac => exact Or.inl hac
    | inr hac =>
      cases hac with
      | inl hac =>
        subst hac
        exact Or.inr ⟨rfl, by omega⟩
      | inr hac =>
        exfalso
        have h1 : n2 * (c + 1) ≤ n2 * a := Nat.mul_le_mul (Nat.le_refl n2) hac
        have h2 : n2 * (c + 1) = n2 * c + n2 := Nat.mul_succ n2 c
        omega
  · intro h
    cases h with
    | inl hac =>
      have h1 : n2 * (a + 1) ≤ n2 * c := Nat.mul_le_mul (Nat.le_refl n2) hac
      have h2 : n2 * (a + 1) = n2 * a + n2 := Nat.mul_succ n2 a
      omega
    | inr hac =>
      cases hac with
      | intro h1 h2 =>
        subst h1
        omega

/-- Under `encode`, the natural order of `Fin (n1*n2)` is the
lexicographic order on `Fin n1 × Fin n2`. -/
theorem encode_le (p q : Fin n1 × Fin n2) :
    (encode p).val ≤ (encode q).val ↔
      p.1.val < q.1.val ∨ (p.1.val = q.1.val ∧ p.2.val ≤ q.2.val) :=
  flat_le_iff p.2.isLt q.2.isLt

/-- Inverse of `encode`: division with remainder by `n₂`. -/
def decode (hn2 : 0 < n2) (k : Fin (n1 * n2)) : Fin n1 × Fin n2 :=
  (⟨k.val / n2, by
      have h1 : k.val < n1 * n2 := k.isLt
      have h2 : k.val / n2 < n1 := Nat.div_lt_of_lt_mul (by
        have h3 : n1 * n2 = n2 * n1 := Nat.mul_comm n1 n2
        omega)
      exact h2⟩,
   ⟨k.val % n2, Nat.mod_lt _ hn2⟩)

theorem encode_decode (hn2 : 0 < n2) (k : Fin (n1 * n2)) :
    encode (decode hn2 k) = k := by
  apply Fin.ext
  show n2 * (k.val / n2) + k.val % n2 = k.val
  exact Nat.div_add_mod k.val n2

theorem decode_encode (hn2 : 0 < n2) (p : Fin n1 × Fin n2) :
    decode hn2 (encode p) = p := by
  have hdiv : (n2 * p.1.val + p.2.val) / n2 = p.1.val := by
    rw [Nat.mul_add_div hn2, Nat.div_eq_of_lt p.2.isLt, Nat.add_zero]
  have hmod : (n2 * p.1.val + p.2.val) % n2 = p.2.val := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt p.2.isLt]
  have h1 : (decode hn2 (encode p)).1 = p.1 := Fin.ext hdiv
  have h2 : (decode hn2 (encode p)).2 = p.2 := Fin.ext hmod
  calc
    decode hn2 (encode p)
        = ((decode hn2 (encode p)).1, (decode hn2 (encode p)).2) := rfl
    _   = (p.1, p.2) := by rw [h1, h2]
    _   = p := rfl

/-- `Lblock` really is `L (n1*n2)` read through the flat-index map. -/
theorem L_encode (p q : Fin n1 × Fin n2) :
    L (n1 * n2) (encode p) (encode q) = Lblock n1 n2 p q := by
  simp only [L, Lblock, encode_le]

/-- **Theorem 1** for the flat matrix `L_{n1·n2}`, entrywise:

  `L_{n1·n2}[n₂i₁+i₂, n₂j₁+j₂]
     = L_{n1}[i₁,j₁]·L_{n2}[i₂,j₂] + L⁻_{n1}[i₁,j₁]·U⁻_{n2}[i₂,j₂]`. -/
theorem theorem1_flat (p q : Fin n1 × Fin n2) :
    L (n1 * n2) (encode p) (encode q)
      = L n1 p.1 q.1 * L n2 p.2 q.2 + Lm n1 p.1 q.1 * Um n2 p.2 q.2 := by
  rw [L_encode]
  exact congrFun (congrFun (theorem1_L n1 n2) p) q

/-- **Theorem 1** for the flat matrix, at arbitrary indices
`i j : Fin (n1*n2)` (decomposed as `i = n₂·i₁ + i₂` by `decode`).
Together with `encode_decode`/`decode_encode` this covers every entry
of `L (n1*n2)`. -/
theorem theorem1_flat' (hn2 : 0 < n2) (i j : Fin (n1 * n2)) :
    L (n1 * n2) i j
      = L n1 (decode hn2 i).1 (decode hn2 j).1
          * L n2 (decode hn2 i).2 (decode hn2 j).2
        + Lm n1 (decode hn2 i).1 (decode hn2 j).1
            * Um n2 (decode hn2 i).2 (decode hn2 j).2 := by
  have h := theorem1_flat (n1 := n1) (n2 := n2) (decode hn2 i) (decode hn2 j)
  rwa [encode_decode, encode_decode] at h

end FlatIndex

/-! ### Sanity checks on a small instance (n = 6 = 2·3) -/

example : Lblock 2 3 (⟨1, by omega⟩, ⟨0, by omega⟩) (⟨0, by omega⟩, ⟨2, by omega⟩) = 1 := by
  decide

example :
    (kron (L 2) (L 3) + kron (Lm 2) (Um 3))
        (⟨1, by omega⟩, ⟨0, by omega⟩) (⟨0, by omega⟩, ⟨2, by omega⟩) = 1 := by
  decide

end KroneckerPrefixSum
