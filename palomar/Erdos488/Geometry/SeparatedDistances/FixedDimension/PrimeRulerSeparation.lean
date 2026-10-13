module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.PrimeRuler

@[expose] public section

/-! Exact integer-ruler layer. Unlike a residue-only statement, these theorems
refer to the actual differences of the explicit ruler positions. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- The unscaled deterministic integer ruler. The geometric candidate uses 3 times this. -/
def primeRuler (p k A i : ℕ) : ℤ :=
  4 * (p : ℤ) * (i : ℤ) + ((i^2 + 2*k*A*i) % p : ℕ)

/-- A positive-lag difference, kept in the integers so subtraction never truncates. -/
def primeRulerGap (p k A i δ : ℕ) : ℤ :=
  primeRuler p k A (i + δ) - primeRuler p k A i

/-- Every actual ruler difference lies in its strict lag window. -/
theorem primeRulerGap_window (p k A i δ : ℕ) (hp : 0 < p) :
    (4 * (δ : ℤ) - 1) * p < primeRulerGap p k A i δ ∧
      primeRulerGap p k A i δ < (4 * (δ : ℤ) + 1) * p := by
  have h₀ : (0 : ℤ) ≤ ((i^2 + 2*k*A*i) % p : ℕ) := by positivity
  have h₁ : (0 : ℤ) ≤ (((i+δ)^2 + 2*k*A*(i+δ)) % p : ℕ) := by positivity
  have h₂ : (((i^2 + 2*k*A*i) % p : ℕ) : ℤ) < p := by
    exact_mod_cast Nat.mod_lt _ hp
  have h₃ : ((((i+δ)^2 + 2*k*A*(i+δ)) % p : ℕ) : ℤ) < p := by
    exact_mod_cast Nat.mod_lt _ hp
  dsimp [primeRulerGap, primeRuler]
  push_cast at *
  constructor <;> nlinarith

/-- Strictly positive lags give positive actual ruler gaps. -/
theorem primeRulerGap_pos (p k A i δ : ℕ) (hp : 0 < p) (hδ : 0 < δ) :
    0 < primeRulerGap p k A i δ := by
  have hw := (primeRulerGap_window p k A i δ hp).1
  have hδ' : (1 : ℤ) ≤ δ := by exact_mod_cast hδ
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  nlinarith

/-- Different lag windows are strictly ordered, with a gap greater than 2p. -/
theorem primeRulerGap_different_lag (p k A B i j δ ε : ℕ)
    (hp : 0 < p) (hδε : δ < ε) :
    2 * (p : ℤ) < primeRulerGap p k B j ε - primeRulerGap p k A i δ := by
  have h₀ := (primeRulerGap_window p k A i δ hp).2
  have h₁ := (primeRulerGap_window p k B j ε hp).1
  have hδε' : (δ : ℤ) + 1 ≤ ε := by exact_mod_cast hδε
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  nlinarith

/-- The actual ruler difference has exactly the stated quadratic residue. -/
theorem primeRulerGap_residue (p k A i δ : ℕ) :
    primeRulerGap p k A i δ % (p : ℤ) =
      ((δ * (2*i + δ + 2*k*A) : ℕ) : ℤ) % (p : ℤ) := by
  have hpoly : (((i+δ)^2 + 2*k*A*(i+δ) : ℕ) : ℤ) -
      ((i^2 + 2*k*A*i : ℕ) : ℤ) = ((δ*(2*i+δ+2*k*A) : ℕ) : ℤ) := by
    push_cast
    ring
  calc
    primeRulerGap p k A i δ % (p : ℤ) =
        ((((i+δ)^2 + 2*k*A*(i+δ) : ℕ) : ℤ) -
          ((i^2 + 2*k*A*i : ℕ) : ℤ)) % (p : ℤ) := by
      simp [primeRulerGap, primeRuler, Int.add_emod, Int.sub_emod,
        Int.mul_emod, Int.natCast_emod]
    _ = _ := congrArg (fun z : ℤ => z % (p : ℤ)) hpoly

/-- Equal same-lag *actual* gaps force the same cluster and starting index. -/
theorem primeRulerGap_same_lag_injective (p m k δ A B i j : ℕ)
    (hp : p.Prime) (hδ : 0 < δ) (hδp : δ < p) (hsize : 2*m*k < p)
    (hA : A < m) (hB : B < m) (hi : i+δ < k) (hj : j+δ < k)
    (heq : primeRulerGap p k A i δ = primeRulerGap p k B j δ) : A = B ∧ i = j := by
  have hmod := congrArg (fun z : ℤ => z % (p : ℤ)) heq
  rw [primeRulerGap_residue, primeRulerGap_residue] at hmod
  have hnat : (δ*(2*i+δ+2*k*A)) % p = (δ*(2*j+δ+2*k*B)) % p := by
    exact_mod_cast hmod
  exact same_lag_residue_injective p m k δ A B i j hp hδ hδp hsize hA hB hi hj hnat

/-- Exhaustive uniqueness of all positive actual ruler gaps, across all clusters.
Different lags use disjoint windows; equal lags use prime cancellation. -/
theorem primeRulerGap_injective (p m k δ ε A B i j : ℕ)
    (hp : p.Prime) (hδ : 0 < δ) (hε : 0 < ε) (hδp : δ < p) (hεp : ε < p)
    (hsize : 2*m*k < p) (hA : A < m) (hB : B < m)
    (hi : i+δ < k) (hj : j+ε < k)
    (heq : primeRulerGap p k A i δ = primeRulerGap p k B j ε) :
    A = B ∧ i = j ∧ δ = ε := by
  have hδε : δ = ε := by
    rcases lt_trichotomy δ ε with hlt | he | hgt
    · have h := primeRulerGap_different_lag p k A B i j δ ε hp.pos hlt
      rw [heq] at h
      have hp' : (0 : ℤ) < p := by exact_mod_cast hp.pos
      omega
    · exact he
    · have h := primeRulerGap_different_lag p k B A j i ε δ hp.pos hgt
      rw [heq] at h
      have hp' : (0 : ℤ) < p := by exact_mod_cast hp.pos
      omega
  subst ε
  obtain ⟨hAB,hij⟩ := primeRulerGap_same_lag_injective p m k δ A B i j
    hp hδ hδp hsize hA hB hi hj heq
  exact ⟨hAB,hij,rfl⟩

/-- Useful coarse window: each positive-lag gap lies strictly between 3pδ and 5pδ. -/
theorem primeRulerGap_linear_bounds (p k A i δ : ℕ) (hp : 0 < p) (hδ : 0 < δ) :
    3 * (p : ℤ) * δ < primeRulerGap p k A i δ ∧
      primeRulerGap p k A i δ < 5 * (p : ℤ) * δ := by
  obtain ⟨h₀,h₁⟩ := primeRulerGap_window p k A i δ hp
  have hδ' : (1 : ℤ) ≤ δ := by exact_mod_cast hδ
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  constructor <;> nlinarith

/-- The actual t=3 ruler has gaps separated by at least 3 as real numbers.
This is across all macro clusters, not just within an individual ruler. -/
theorem scaled_primeRulerGap_separated (p m k δ ε A B i j : ℕ)
    (hp : p.Prime) (hδ : 0 < δ) (hε : 0 < ε) (hδp : δ < p) (hεp : ε < p)
    (hsize : 2*m*k < p) (hA : A < m) (hB : B < m)
    (hi : i+δ < k) (hj : j+ε < k) (hne : ¬ (A = B ∧ i = j ∧ δ = ε)) :
    3 ≤ |3 * (primeRulerGap p k A i δ : ℝ) - 3 * (primeRulerGap p k B j ε : ℝ)| := by
  have hg : primeRulerGap p k A i δ ≠ primeRulerGap p k B j ε := by
    intro h
    exact hne (primeRulerGap_injective p m k δ ε A B i j
      hp hδ hε hδp hεp hsize hA hB hi hj h)
  have habs : (0 : ℤ) < |primeRulerGap p k A i δ - primeRulerGap p k B j ε| :=
    abs_pos.mpr (sub_ne_zero.mpr hg)
  have habs' : (1 : ℤ) ≤ |primeRulerGap p k A i δ - primeRulerGap p k B j ε| := by omega
  have hreal : (1 : ℝ) ≤ |(primeRulerGap p k A i δ : ℝ) -
      (primeRulerGap p k B j ε : ℝ)| := by exact_mod_cast habs'
  rw [← mul_sub, abs_mul]
  norm_num
  linarith

end Erdos488.Geometry.SeparatedDistances.FixedDimension
