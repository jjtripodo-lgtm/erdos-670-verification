module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.SourceOperatorBridge
public import Erdos488.Geometry.SeparatedDistances.Parameters

@[expose] public section

/-! Universal scalar gates for the actual #670 source macro offset. -/

open scoped BigOperators Matrix

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- A finite harmonic estimate, anchored at 34000 and advanced by the exact
successor identity; no improper integral or numerical sampling is used. -/
theorem source_harmonic_linear_bound {m : ℕ} (hm : 34000 ≤ m) :
    (harmonic m : ℝ) ≤ (m : ℝ) / 2000 := by
  induction m, hm using Nat.le_induction with
  | base =>
      have h := Erdos488.Geometry.SeparatedDistances.harmonic_le_seventeen_of_le_50000
        (n := 34000) (by norm_num)
      have hval : ((34000 : ℕ) : ℝ) / 2000 = 17 := by norm_num
      rw [hval]
      exact h
  | succ m hm ih =>
      have hden : (2000 : ℝ) ≤ (m+1 : ℕ) := by
        exact_mod_cast (show 2000 ≤ m+1 by omega)
      have hrecip : ((m+1 : ℕ) : ℝ)⁻¹ ≤ (1/2000 : ℝ) := by
        have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2000) hden
        simpa only [one_div] using hh
      rw [harmonic_succ]
      push_cast
      push_cast at hrecip
      linarith

/-- The ceiling source offset retains its sharp quadratic lower bound. -/
theorem sourceOffset_ge_quadratic (m : ℕ) :
    (m : ℝ) * ((m : ℝ)-1) / 64 ≤ (sourceOffset m : ℝ) := by
  have h := Nat.le_ceil ((m : ℝ)*((m : ℝ)-1)/64)
  simpa only [sourceOffset] using h

theorem sourceOffset_ge_macro_count (m : ℕ) (hm : 34000 ≤ m) :
    (m : ℝ) ≤ (sourceOffset m : ℝ) := by
  have h := sourceOffset_ge_fivehundred_m m hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  linarith

theorem sourceOffset_ge_harmonic_reserve (m : ℕ) (hm : 34000 ≤ m) :
    16384 * (harmonic m : ℝ) ^ 2 ≤ (sourceOffset m : ℝ) := by
  have hmR : (34000 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hH0 : (0 : ℝ) ≤ harmonic m := by
    exact_mod_cast (show (0 : ℚ) ≤ harmonic m by
      unfold harmonic
      positivity)
  have hH := source_harmonic_linear_bound hm
  have hHsq : (harmonic m : ℝ) ^ 2 ≤ ((m : ℝ)/2000) ^ 2 := by
    nlinarith
  have hK := sourceOffset_ge_quadratic m
  have hm_sq : (34000 : ℝ)*m ≤ (m : ℝ)^2 := by
    nlinarith [mul_nonneg hm0 (by linarith : (0 : ℝ) ≤ (m : ℝ)-34000)]
  nlinarith [hHsq]

/-- The literal off-diagonal flattening radius uses twice the physical
private-radius square divided by the macro-step square. -/
noncomputable def sourceFlatteningRadius (m k : ℕ) : ℝ :=
  2 * (sourceRadius m k) ^ 2 /
    (sourceMacroStep (k : ℝ)) ^ 2

theorem sourceFlatteningRadius_eq (m k : ℕ) (hk : 0 < k) :
    sourceFlatteningRadius m k =
      35000 * (m : ℝ) ^ 2 / ((9/8 : ℝ) ^ 6) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  unfold sourceFlatteningRadius sourceMacroStep
  rw [sourceRadius_square]
  field_simp
  ring

theorem sourceFlatteningRadius_le_offset (m k : ℕ)
    (hm : 34000 ≤ m) (hk : 0 < k) :
    sourceFlatteningRadius m k ≤ (sourceOffset m : ℝ) ^ 2 / 16 := by
  rw [sourceFlatteningRadius_eq m k hk]
  have hmR : (34000 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hconst : (35000 : ℝ) / ((9/8 : ℝ) ^ 6) ≤
      (33999 : ℝ) ^ 2 / (64 ^ 2 * 16) := by norm_num
  have hconstmul := mul_le_mul_of_nonneg_right hconst (sq_nonneg (m : ℝ))
  have hsq : (33999 : ℝ) ^ 2 ≤ ((m : ℝ)-1) ^ 2 := by
    nlinarith [sq_nonneg ((m : ℝ)-34000)]
  have hsqmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg (m : ℝ))
  have hK := sourceOffset_ge_quadratic m
  have hK0 : 0 ≤ (m : ℝ)*((m : ℝ)-1)/64 := by
    apply div_nonneg (mul_nonneg hm0 (by linarith)) (by norm_num)
  have hKsq : ((m : ℝ)*((m : ℝ)-1)/64)^2 ≤
      (sourceOffset m : ℝ)^2 := by
    nlinarith [hK]
  calc
    35000 * (m : ℝ)^2 / (9/8 : ℝ)^6 =
        (35000 / (9/8 : ℝ)^6) * (m : ℝ)^2 := by ring
    _ ≤ (33999 : ℝ)^2 / (64^2*16) * (m : ℝ)^2 := hconstmul
    _ = ((m : ℝ)^2 * (33999 : ℝ)^2) / (64^2*16) := by ring
    _ ≤ ((m : ℝ)^2 * ((m : ℝ)-1)^2) / (64^2*16) := by
      nlinarith only [hsqmul]
    _ = ((m : ℝ)*((m : ℝ)-1)/64)^2/16 := by ring
    _ ≤ (sourceOffset m : ℝ)^2/16 := by nlinarith only [hKsq]

/-- Every scalar premise of the source macro-operator theorem follows from
the original universal parameter range. -/
theorem source_macro_operator_scalar_gates (m k : ℕ)
    (hm : 34000 ≤ m) (hk : 2 ≤ k) :
    10 ≤ (sourceOffset m : ℝ) ∧
    16384 * (harmonic m : ℝ) ^ 2 ≤ (sourceOffset m : ℝ) ∧
    (m : ℝ) ≤ (sourceOffset m : ℝ) ∧
    sourceFlatteningRadius m k ≤ (sourceOffset m : ℝ) ^ 2 / 16 := by
  refine ⟨?_, sourceOffset_ge_harmonic_reserve m hm,
    sourceOffset_ge_macro_count m hm,
    sourceFlatteningRadius_le_offset m k hm (by omega)⟩
  have h := sourceOffset_lower m hm
  linarith

/-- For every source macro size and cluster size, the actual rational/fine/
coarse coefficient operator has a same-index residual Gram factor. This is
the universal source-operator bridge; the later distance-class and all-n
configuration assembly is a separate proof obligation. -/
theorem source_actual_operator_completion_universal {n k : ℕ}
    (hm : 34000 ≤ n+2) (hk : 2 ≤ k) :
    ∃ p : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)),
    ∃ B : Fin (n+2) → EuclideanSpace ℝ (Fin (n+1)),
    ∃ F G : Fin (n+1) → EuclideanSpace ℝ (Fin (n+1)),
    ∃ V : Matrix (Fin (n+2) × Fin 5) (Fin (n+2) × Fin 5) ℝ,
      (∀ i j, ‖p j-p i‖ ^ 2 =
        offDiagonalShift (colexSqData (m:=n+1)
          (sourceOffset (n+2) : ℝ))
          (sourceFlatteningRadius (n+2) k) i j) ∧
      (∀ A J, inner ℝ (p A-p J) (B A) =
        sourceQuadraticPotential k A J) ∧
      (∀ i a, inner ℝ (p i.succ-p i.castSucc) (F a) =
        fineIncidence (n+1) (sourceOffset (n+2) : ℝ) i a) ∧
      (∀ i a, inner ℝ (p i.succ-p i.castSucc) (G a) =
        coarseIncidence (n+1) (sourceOffset (n+2) : ℝ) i a) ∧
      (sourceActiveMatrix k B F G)ᵀ * (sourceActiveMatrix k B F G) +
        Vᵀ * V =
        Matrix.diagonal (fun q : Fin (n+2) × Fin 5 =>
          trigWeight (sourceReserve0 (n+2) k)
            (sourceReserve1 (n+2) k)
            (sourceReserve0 (n+2) k) q.2) := by
  obtain ⟨hK, hlarge, hmacro, hr⟩ :=
    source_macro_operator_scalar_gates (n+2) k hm hk
  have hnK : (n+1 : ℕ) ≤ (sourceOffset (n+2) : ℝ) := by
    have hh : ((n+1 : ℕ) : ℝ) ≤ (n+2 : ℕ) := by
      exact_mod_cast (show n+1 ≤ n+2 by omega)
    linarith
  exact source_actual_operator_completion (by omega) hm hk hK hlarge
    (sourceFlatteningRadius (n+2) k) hr hnK

end Erdos488.Geometry.SeparatedDistances.FixedDimension
