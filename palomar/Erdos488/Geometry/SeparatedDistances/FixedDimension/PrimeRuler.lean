module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic

@[expose] public section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Same-lag residues distinguish the cluster and the initial local index.
The sharper `i + δ < k` endpoint condition is retained explicitly. -/
theorem same_lag_residue_injective
    (p m k δ A B i j : ℕ) (hp : p.Prime) (hδ : 0 < δ) (hδp : δ < p)
    (hsize : 2*m*k < p) (hA : A < m) (hB : B < m)
    (hi : i+δ < k) (hj : j+δ < k)
    (heq : (δ*(2*i+δ+2*k*A)) % p = (δ*(2*j+δ+2*k*B)) % p) :
    A=B ∧ i=j := by
  have hcop : p.Coprime δ := hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hδ hδp)
  have hmod : 2*i+δ+2*k*A ≡ 2*j+δ+2*k*B [MOD p] :=
    Nat.ModEq.cancel_left_of_coprime hcop heq
  have hleft : 2*i+δ+2*k*A < p := by
    have hh := Nat.mul_le_mul_left (2*k) (show A+1 ≤ m by omega)
    nlinarith
  have hright : 2*j+δ+2*k*B < p := by
    have hh := Nat.mul_le_mul_left (2*k) (show B+1 ≤ m by omega)
    nlinarith
  have hbracket := hmod.eq_of_lt_of_lt hleft hright
  have hab : A=B := by
    rcases lt_trichotomy A B with hab | hab | hab
    · have hh := Nat.mul_le_mul_left k (show A+1 ≤ B by omega)
      nlinarith
    · exact hab
    · have hh := Nat.mul_le_mul_left k (show B+1 ≤ A by omega)
      nlinarith
  exact ⟨hab, by subst B; omega⟩

end Erdos488.Geometry.SeparatedDistances.FixedDimension
