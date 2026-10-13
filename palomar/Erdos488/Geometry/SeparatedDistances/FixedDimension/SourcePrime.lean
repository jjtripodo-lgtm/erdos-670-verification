module

public import Mathlib.NumberTheory.Bertrand
public import Mathlib.Tactic

@[expose] public section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Bertrand gives the strict two-sided source ruler-prime interval.
The upper endpoint is excluded because it is a composite multiple of two. -/
theorem source_ruler_prime_exists (m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    ∃ p : ℕ, p.Prime ∧ 2*m*k < p ∧ p < 4*m*k := by
  have hn : 2*m*k ≠ 0 := by positivity
  obtain ⟨p,hp,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (2*m*k) hn
  have hhi' : p ≤ 4*m*k := by nlinarith
  have hne : p ≠ 4*m*k := by
    intro heq
    have hdiv : 2 ∣ p := ⟨2*m*k,by nlinarith⟩
    have htwo : 2=p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 hdiv
    have hmk : 0 < m*k := Nat.mul_pos hm hk
    nlinarith
  exact ⟨p,hp,hlo,lt_of_le_of_ne hhi' hne⟩

end Erdos488.Geometry.SeparatedDistances.FixedDimension
