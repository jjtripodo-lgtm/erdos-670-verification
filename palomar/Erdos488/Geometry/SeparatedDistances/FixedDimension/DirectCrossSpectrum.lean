module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.SpectrumSeparation

@[expose] public section

/-! Derivative-free cross-spectrum ordering, adopting JRL PR 3002.
No adjacent quotient-error Lipschitz estimate or physical local-step H is used.
All geometric inputs are visible as scalar square identities and pointwise errors. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Exact cancellation of the coarse digit from a fine squared increment. -/
theorem cross_fine_polarization (ν α β₀ β₁ : ℝ) :
    ((ν+α+β₁)^2-2*α*β₁)-((ν+α+β₀)^2-2*α*β₀) =
      (β₁-β₀)*(2*ν+β₁+β₀) := by ring

/-- The symmetric coarse squared-increment identity. -/
theorem cross_coarse_polarization (ν α₀ α₁ β : ℝ) :
    ((ν+α₁+β)^2-2*α₁*β)-((ν+α₀+β)^2-2*α₀*β) =
      (α₁-α₀)*(2*ν+α₁+α₀) := by ring

/-- The polynomial form of the fine guard propagates to every larger baseline. -/
theorem direct_fine_guard_propagates (g ν₀ ν b A E : ℝ)
    (hg : 1 ≤ g) (hν : ν₀ ≤ ν) (hguard : ν₀+A+E ≤ g*(ν₀-b)) :
    ν+A+E ≤ g*(ν-b) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hg) (sub_nonneg.mpr hν)]

/-- A unit fine gap follows directly from squares and endpoint upper bounds. -/
theorem polarized_fine_gap (ν b A E g β₀ β₁ D₀ D₁ : ℝ)
    (hg : 0 ≤ g) (hν : b ≤ ν) (hβ₀ : -b ≤ β₀) (hβ₁ : -b ≤ β₁)
    (hβ : g ≤ β₁-β₀) (hD₀ : 0 ≤ D₀) (hD₁ : 0 < D₁)
    (hu₀ : D₀ ≤ ν+A+E) (hu₁ : D₁ ≤ ν+A+E)
    (hsq : D₁^2-D₀^2=(β₁-β₀)*(2*ν+β₁+β₀))
    (hguard : ν+A+E ≤ g*(ν-b)) : 1 ≤ D₁-D₀ := by
  have hfactor : 2*(ν-b) ≤ 2*ν+β₁+β₀ := by linarith
  have hprod := mul_le_mul hβ hfactor
    (show 0 ≤ 2*(ν-b) by linarith) (show 0 ≤ β₁-β₀ by linarith)
  have hsum : 0 < D₁+D₀ := by linarith
  have hmul : 1*(D₁+D₀) ≤ (D₁-D₀)*(D₁+D₀) := by nlinarith
  exact (mul_le_mul_iff_of_pos_right hsum).1 hmul

/-- Two pointwise errors suffice for the coarse carry; no k*Flip term is needed. -/
theorem direct_carry_guard (s c r fstar E coarse₀ coarse₁ fine₀ fineLast e₀ e₁ : ℝ)
    (hc : s*c*r ≤ coarse₁-coarse₀) (hf : fineLast-fine₀ ≤ 2*s*fstar)
    (he₀ : |e₀| ≤ E) (he₁ : |e₁| ≤ E)
    (hguard : 1 ≤ s*(c*r-2*fstar)-2*E) :
    1 ≤ (coarse₁+fine₀+e₁)-(coarse₀+fineLast+e₀) := by
  have h₀ := (abs_le.mp he₀).2
  have h₁ := (abs_le.mp he₁).1
  nlinarith

/-- Complete derivative-free cross-spectrum theorem, for every distinct triple.
The exact metric square and absolute error bound are explicit inputs. -/
theorem direct_cross_spectrum_separated
    (D : ℕ → ℕ → ℕ → ℝ) (ν f : ℕ → ℝ) (M k : ℕ) (hk : 0 < k)
    (s c r fstar E S νmin : ℝ) (hs : 0 ≤ s) (hc : 0 ≤ c)
    (hν : ∀ a, a < M → νmin ≤ ν a) (hνmin : s*fstar ≤ νmin)
    (hf : ∀ i, i < k → |f i| ≤ fstar)
    (hstep : ∀ i, i+1 < k → r ≤ f (i+1)-f i)
    (hbase : ∀ a, a+1 < M → S ≤ ν (a+1)-ν a)
    (hpos : ∀ a, a < M → ∀ i, i < k → ∀ j, j < k → 0 < D a i j)
    (hsquare : ∀ a, a < M → ∀ i, i < k → ∀ j, j < k →
      (D a i j)^2=(ν a+s*c*f i+s*f j)^2-2*(s*c*f i)*(s*f j))
    (herror : ∀ a, a < M → ∀ i, i < k → ∀ j, j < k →
      |D a i j-(ν a+s*c*f i+s*f j)| ≤ E)
    (hfine₁ : 1 ≤ s*r)
    (hfine₂ : νmin+s*(c+1)*fstar+E ≤ s*r*(νmin-s*fstar))
    (hcarry : 1 ≤ s*(c*r-2*fstar)-2*E)
    (hmacro : 1 ≤ S-2*(s*(c+1)*fstar)-2*E) :
    ∀ a i j b u v, a < M → i < k → j < k → b < M → u < k → v < k →
      (a,i,j) ≠ (b,u,v) → 1 ≤ |D a i j-D b u v| := by
  have hpert (i j : ℕ) (hi : i < k) (hj : j < k) :
      |s*c*f i+s*f j| ≤ s*(c+1)*fstar := by
    obtain ⟨hli,hui⟩ := abs_le.mp (hf i hi)
    obtain ⟨hlj,huj⟩ := abs_le.mp (hf j hj)
    have h₀ := mul_le_mul_of_nonneg_left hli (mul_nonneg hs hc)
    have h₁ := mul_le_mul_of_nonneg_left hui (mul_nonneg hs hc)
    have h₂ := mul_le_mul_of_nonneg_left hlj hs
    have h₃ := mul_le_mul_of_nonneg_left huj hs
    apply abs_le.mpr
    constructor <;> nlinarith
  have hupper (a i j : ℕ) (ha : a < M) (hi : i < k) (hj : j < k) :
      D a i j ≤ ν a+s*(c+1)*fstar+E := by
    have h₀ := (abs_le.mp (hpert i j hi hj)).2
    have h₁ := (abs_le.mp (herror a ha i hi j hj)).2
    linarith
  have hFine : ∀ a, a < M → ∀ i, i < k → ∀ j, j+1 < k →
      1 ≤ D a i (j+1)-D a i j := by
    intro a ha i hi j hj
    have hj₀ : j < k := by omega
    have hβ := mul_le_mul_of_nonneg_left (hstep j hj) hs
    have hβ₀ := mul_le_mul_of_nonneg_left (abs_le.mp (hf j hj₀)).1 hs
    have hβ₁ := mul_le_mul_of_nonneg_left (abs_le.mp (hf (j+1) hj)).1 hs
    apply polarized_fine_gap (ν a) (s*fstar) (s*(c+1)*fstar) E (s*r)
      (s*f j) (s*f (j+1)) (D a i j) (D a i (j+1))
      (by linarith) (hνmin.trans (hν a ha))
      (by nlinarith) (by nlinarith) (by nlinarith)
      (hpos a ha i hi j hj₀).le (hpos a ha i hi (j+1) hj)
      (hupper a i j ha hi hj₀) (hupper a i (j+1) ha hi hj)
    · rw [hsquare a ha i hi (j+1) hj, hsquare a ha i hi j hj₀]
      exact cross_fine_polarization _ _ _ _
    · exact direct_fine_guard_propagates _ _ _ _ _ _ hfine₁ (hν a ha) hfine₂
  have hCarry : ∀ a, a < M → ∀ i, i+1 < k →
      1 ≤ D a (i+1) 0-D a i (k-1) := by
    intro a ha i hi
    have hi₀ : i < k := by omega
    have hlast : k-1 < k := by omega
    have h₀ := mul_le_mul_of_nonneg_left (hstep i hi) (mul_nonneg hs hc)
    have h₁ := mul_le_mul_of_nonneg_left (abs_le.mp (hf 0 hk)).1 hs
    have h₂ := mul_le_mul_of_nonneg_left (abs_le.mp (hf (k-1) hlast)).2 hs
    have he₀ := (abs_le.mp (herror a ha i hi₀ (k-1) hlast)).2
    have he₁ := (abs_le.mp (herror a ha (i+1) hi 0 hk)).1
    nlinarith
  have hMacro : ∀ a, a+1 < M → 1 ≤ D (a+1) 0 0-D a (k-1) (k-1) := by
    intro a ha
    have ha₀ : a < M := by omega
    have hlast : k-1 < k := by omega
    have h₀ := (abs_le.mp (hpert 0 0 hk hk)).1
    have h₁ := (abs_le.mp (hpert (k-1) (k-1) hlast hlast)).2
    have he₀ := (abs_le.mp (herror a ha₀ (k-1) hlast (k-1) hlast)).2
    have he₁ := (abs_le.mp (herror (a+1) ha 0 hk 0 hk)).1
    have hb := hbase a ha
    nlinarith
  intro a i j b u v ha hi hj hb hu hv hne
  exact three_digit_all_pairs_separated D M k hk hFine hCarry hMacro ha hi hj hb hu hv hne

/-- The exact fine universal rational certificate from the new source. -/
theorem direct_fine_rational_certificate :
    (1 : ℝ) < 15719289303849634494315/14027497163657672321024 := by norm_num

/-- The carry envelope clears one for every nonnegative k, not just sampled sizes. -/
theorem direct_carry_rational_certificate (k : ℝ) (hk : 0 ≤ k) :
    1 < 9/8+k*(13009148140329/95880445804544) := by nlinarith

/-- The macro envelope clears one uniformly in every nonnegative k. -/
theorem direct_macro_rational_certificate (k : ℝ) (hk : 0 ≤ k) :
    1 < 9/8+k*(52668618975/374532991424)+k^2*(81/512) := by nlinarith

end Erdos488.Geometry.SeparatedDistances.FixedDimension
