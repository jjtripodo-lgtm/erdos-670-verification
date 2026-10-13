module

public import Erdos488.Geometry.SeparatedDistances.Defs
public import Mathlib.Tactic

@[expose] public section

namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Every non-diagonal unordered edge has an increasing representative. -/
theorem edge_has_increasing_representative {ι : Type*} [LinearOrder ι] (e : Edge ι) :
    ∃ i j : ι, i < j ∧ e.val = s(i,j) := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.inductionOn with
  | hf i j =>
    have hij : i ≠ j := by simpa only [Sym2.mk_isDiag_iff] using he
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact ⟨i,j,hij,rfl⟩
    · exact ⟨j,i,hji,Sym2.eq_swap⟩

/-- Increasing representatives of the same unordered edge coincide componentwise. -/
theorem increasing_edge_representative_unique {ι : Type*} [LinearOrder ι]
    {i j k l : ι} (hij : i < j) (hkl : k < l) (heq : s(i,j) = s(k,l)) :
    i = k ∧ j = l := by
  rcases Sym2.eq_iff.mp heq with h | ⟨rfl,rfl⟩
  · exact h
  · exact False.elim (lt_asymm hij hkl)

/-- A genuinely unordered Sym2 bridge: canonical increasing endpoint comparisons
suffice for the repository's publication-facing separation definition. -/
theorem separatedConfiguration_of_increasing_pairs
    {ι E : Type*} [LinearOrder ι] [PseudoMetricSpace E] (p : ι → E)
    (hgap : ∀ i j k l : ι, i < j → k < l → (i,j) ≠ (k,l) →
      1 ≤ |dist (p i) (p j)-dist (p k) (p l)|) : SeparatedConfiguration p := by
  intro e f hef
  obtain ⟨i,j,hij,he⟩ := edge_has_increasing_representative e
  obtain ⟨k,l,hkl,hf⟩ := edge_has_increasing_representative f
  have hne : (i,j) ≠ (k,l) := by
    intro h
    apply hef
    apply Subtype.ext
    rw [he,hf]
    rcases Prod.mk.inj h with ⟨rfl,rfl⟩
    rfl
  simpa only [he,hf,edgeDistance,Sym2.lift_mk] using hgap i j k l hij hkl hne

/-- Zero must be excluded independently of edge-to-edge separation. -/
theorem minimum_distance_of_increasing_pairs
    {ι E : Type*} [LinearOrder ι] [PseudoMetricSpace E] (p : ι → E)
    (hmin : ∀ i j : ι, i < j → 1 ≤ dist (p i) (p j)) :
    ∀ i j, i ≠ j → 1 ≤ dist (p i) (p j) := by
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hmin i j hij
  · simpa only [dist_comm] using hmin j i hji

/-- The independently proved minimum distance implies injectivity. -/
theorem injective_of_unit_minimum_distance
    {ι E : Type*} [PseudoMetricSpace E] (p : ι → E)
    (hmin : ∀ i j, i ≠ j → 1 ≤ dist (p i) (p j)) : Function.Injective p := by
  intro i j heq
  by_contra hne
  have h := hmin i j hne
  rw [heq,dist_self] at h
  norm_num at h

end Erdos488.Geometry.SeparatedDistances.FixedDimension
