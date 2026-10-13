module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.UnorderedEdgeSeparation

@[expose] public section

/-! Exhaustive genuinely unordered cluster-edge classification and assembly.
Local separation, canonical cross separation and mixed band isolation are
explicit inputs; this module constructs no Gram matrix or scalar certificate. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Each non-diagonal edge is either local with increasing local endpoints,
or cross-cluster with increasing macro endpoints. -/
theorem cluster_edge_cases {α β : Type*} [LinearOrder α] [LinearOrder β]
    (e : Edge (α × β)) :
    (∃ A i j, i < j ∧ e.val=s((A,i),(A,j))) ∨
      (∃ A B i j, A < B ∧ e.val=s((A,i),(B,j))) := by
  obtain ⟨e,he⟩ := e
  induction e using Sym2.inductionOn with
  | hf x y =>
    obtain ⟨A,i⟩ := x
    obtain ⟨B,j⟩ := y
    by_cases hAB : A=B
    · subst B
      have hij : i ≠ j := by
        intro h
        subst j
        exact he (Sym2.mk_isDiag_iff.mpr rfl)
      rcases lt_or_gt_of_ne hij with hij | hji
      · exact Or.inl ⟨A,i,j,hij,rfl⟩
      · exact Or.inl ⟨A,j,i,hji,Sym2.eq_swap⟩
    · rcases lt_or_gt_of_ne hAB with hAB | hBA
      · exact Or.inr ⟨A,B,i,j,hAB,rfl⟩
      · exact Or.inr ⟨B,A,j,i,hBA,Sym2.eq_swap⟩

/-- All four combinations of unordered edge classes are checked. -/
theorem separatedConfiguration_of_cluster_gaps
    {α β E : Type*} [LinearOrder α] [LinearOrder β] [PseudoMetricSpace E]
    (p : α × β → E)
    (hlocal : ∀ A i j B u v, i < j → u < v → (A,i,j) ≠ (B,u,v) →
      1 ≤ |dist (p (A,i)) (p (A,j))-dist (p (B,u)) (p (B,v))|)
    (hcross : ∀ A B i j C D u v, A < B → C < D → (A,B,i,j) ≠ (C,D,u,v) →
      1 ≤ |dist (p (A,i)) (p (B,j))-dist (p (C,u)) (p (D,v))|)
    (hmixed : ∀ A i j B C u v, i < j → B < C →
      1 ≤ dist (p (B,u)) (p (C,v))-dist (p (A,i)) (p (A,j))) :
    SeparatedConfiguration p := by
  intro e f hef
  have hval : e.val ≠ f.val := fun h => hef (Subtype.ext h)
  rcases cluster_edge_cases e with ⟨A,i,j,hij,he⟩ | ⟨A,B,i,j,hAB,he⟩
  · rcases cluster_edge_cases f with ⟨B,u,v,huv,hf⟩ | ⟨B,C,u,v,hBC,hf⟩
    · have hne : (A,i,j) ≠ (B,u,v) := by
        intro h
        have hA : A=B := congrArg Prod.fst h
        have hi : i=u := congrArg (fun q => q.2.1) h
        have hj : j=v := congrArg (fun q => q.2.2) h
        apply hval
        simpa only [he,hf,hA,hi,hj]
      simpa only [he,hf,edgeDistance,Sym2.lift_mk] using hlocal A i j B u v hij huv hne
    · have h := (hmixed A i j B C u v hij hBC).trans
        (le_abs_self (dist (p (B,u)) (p (C,v))-dist (p (A,i)) (p (A,j))))
      rw [abs_sub_comm] at h
      simpa only [he,hf,edgeDistance,Sym2.lift_mk] using h
  · rcases cluster_edge_cases f with ⟨C,u,v,huv,hf⟩ | ⟨C,D,u,v,hCD,hf⟩
    · have h := (hmixed C u v A B i j huv hAB).trans (le_abs_self _)
      simpa only [he,hf,edgeDistance,Sym2.lift_mk] using h
    · have hne : (A,B,i,j) ≠ (C,D,u,v) := by
        intro h
        have hA : A=C := congrArg Prod.fst h
        have hB : B=D := congrArg (fun q => q.2.1) h
        have hi : i=u := congrArg (fun q => q.2.2.1) h
        have hj : j=v := congrArg (fun q => q.2.2.2) h
        apply hval
        simpa only [he,hf,hA,hB,hi,hj]
      simpa only [he,hf,edgeDistance,Sym2.lift_mk] using hcross A B i j C D u v hAB hCD hne

/-- The two nonzero-distance classes must each clear zero independently. -/
theorem cluster_minimum_distance
    {α β E : Type*} [LinearOrder α] [LinearOrder β] [PseudoMetricSpace E]
    (p : α × β → E)
    (hlocal : ∀ A i j, i < j → 1 ≤ dist (p (A,i)) (p (A,j)))
    (hcross : ∀ A B i j, A < B → 1 ≤ dist (p (A,i)) (p (B,j))) :
    ∀ x y, x ≠ y → 1 ≤ dist (p x) (p y) := by
  rintro ⟨A,i⟩ ⟨B,j⟩ hxy
  by_cases hAB : A=B
  · subst B
    have hij : i ≠ j := by intro h; subst j; exact hxy rfl
    rcases lt_or_gt_of_ne hij with h | h
    · exact hlocal A i j h
    · simpa only [dist_comm] using hlocal A j i h
  · rcases lt_or_gt_of_ne hAB with h | h
    · exact hcross A B i j h
    · simpa only [dist_comm] using hcross B A j i h

end Erdos488.Geometry.SeparatedDistances.FixedDimension
