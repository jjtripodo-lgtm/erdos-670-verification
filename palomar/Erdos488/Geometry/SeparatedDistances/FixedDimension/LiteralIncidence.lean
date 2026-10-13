module

public import Erdos488.Geometry.SeparatedDistances.FixedDimension.TriangularBounds
public import Erdos488.Geometry.SeparatedDistances.FixedDimension.GeometricPotential

@[expose] public section

open scoped BigOperators Matrix
open Matrix
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

noncomputable def finePotential {n : ℕ} (K : ℝ) (a : Fin n) (v : Fin (n+1)) : ℝ :=
  if v.val < a.val+1 then K+(Nat.choose (a.val+1) 2:ℝ)+v.val+1 else 0
noncomputable def coarsePotential {n : ℕ} (K : ℝ) (a : Fin n) (v : Fin (n+1)) : ℝ :=
  if a.val < v.val then K+(Nat.choose v.val 2:ℝ)+a.val+1 else 0

/-- Literal fine potential differences give the diagonal minus strict upper ones. -/
theorem finePotential_incidence {n : ℕ} (K : ℝ) (i a : Fin n) :
    (pathIncidence n *ᵥ finePotential K a) i =
      (if i=a then colexANat K (i.val+1) else 0) -
      (if i.val < a.val then 1 else 0) := by
  rw [pathIncidence_mulVec_eq]
  simp only [finePotential, Fin.val_castSucc, Fin.val_succ]
  by_cases h : i=a
  · subst a
    simp [colexANat,Nat.choose_succ_succ]
    ring
  · have hv : i.val ≠ a.val := fun e => h (Fin.ext e)
    by_cases hia : i.val < a.val
    · have h₁ : i.val < a.val+1 := by omega
      have h₂ : i.val+1<a.val+1 := by omega
      simp only [h,h₁,h₂,hia,if_pos,if_false,Nat.cast_add,Nat.cast_one]
      ring
    · have h₁ : ¬ i.val < a.val+1 := by omega
      have h₂ : ¬ i.val+1<a.val+1 := by omega
      simp [h,h₁,h₂,hia]

/-- Literal coarse potential differences give minus diagonal and strict lower ramp. -/
theorem coarsePotential_incidence {n : ℕ} (K : ℝ) (i a : Fin n) :
    (pathIncidence n *ᵥ coarsePotential K a) i =
      -(if i=a then colexANat K (i.val+1) else 0) -
      (if a.val < i.val then (i.val:ℝ) else 0) := by
  rw [pathIncidence_mulVec_eq]
  simp only [coarsePotential, Fin.val_castSucc, Fin.val_succ]
  by_cases h : i=a
  · subst a
    simp [colexANat,Nat.choose_succ_succ]
    ring
  · have hv : i.val ≠ a.val := fun e => h (Fin.ext e)
    by_cases hai : a.val < i.val
    · have h₂ : a.val < i.val+1 := by omega
      have hc : Nat.choose (i.val+1) 2 = Nat.choose i.val 2+i.val := by
        simpa [Nat.add_comm] using Nat.choose_succ_succ i.val 1
      simp only [h,h₂,hai,if_pos,if_false,hc,Nat.cast_add,Nat.cast_one,neg_zero]
      ring
    · have h₂ : ¬ a.val < i.val+1 := by omega
      simp [h,h₂,hai]


noncomputable def fineIncidence (n : ℕ) (K : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i a => (pathIncidence n *ᵥ finePotential K a) i
noncomputable def coarseIncidence (n : ℕ) (K : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i a => (pathIncidence n *ᵥ coarsePotential K a) i

lemma fineIncidence_normalized {n : ℕ} {K : ℝ} (hK : 0 < K) (x : Fin n → ℝ) (i : Fin n) :
    (fineIncidence n K *ᵥ x) i / colexANat K (i.val+1) =
      x i-(fineTriangle n (fun j => colexANat K (j.val+1)) *ᵥ x) i := by
  have hp := ne_of_gt (colex_triangle_positive hK i.val)
  have hfi : fineIncidence n K = fun i a => (if i=a then colexANat K (i.val+1) else 0) - (if i.val < a.val then 1 else 0) := by
    ext i a
    exact finePotential_incidence K i a
  rw [hfi]
  simp only [Matrix.mulVec,dotProduct,
    sub_mul,ite_mul,zero_mul,Finset.sum_sub_distrib,sub_div,Finset.sum_div]
  simp only [ite_div,zero_div,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  rw [mul_div_cancel_left₀ _ hp]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  unfold fineTriangle
  split_ifs <;> simp <;> ring

lemma coarseIncidence_normalized {n : ℕ} {K : ℝ} (hK : 0 < K) (x : Fin n → ℝ) (i : Fin n) :
    (coarseIncidence n K *ᵥ x) i / colexANat K (i.val+1) =
      -(x i+(coarseTriangle n (fun j => colexANat K (j.val+1)) *ᵥ x) i) := by
  have hp := ne_of_gt (colex_triangle_positive hK i.val)
  have hci : coarseIncidence n K = fun i a => -(if i=a then colexANat K (i.val+1) else 0) - (if a.val < i.val then (i.val:ℝ) else 0) := by
    ext i a
    exact coarsePotential_incidence K i a
  rw [hci]
  simp only [Matrix.mulVec,dotProduct,
    sub_mul,neg_mul,ite_mul,zero_mul,Finset.sum_sub_distrib,Finset.sum_neg_distrib,
    sub_div,neg_div,Finset.sum_div]
  simp only [ite_div,zero_div,Finset.sum_ite_eq,Finset.mem_univ,if_true]
  rw [mul_div_cancel_left₀ _ hp]
  have hs : (∑ a : Fin n, (if a.val < i.val then (i.val:ℝ)*x a else 0)/colexANat K (i.val+1)) =
      ∑ a, coarseTriangle n (fun j => colexANat K (j.val+1)) i a*x a := by
    apply Finset.sum_congr rfl
    intro a ha
    unfold coarseTriangle
    split_ifs <;> simp <;> ring
  simp only [ite_div,zero_div] at hs
  rw [hs]
  ring

/-- Exact universal normalized incidence budgets for the literal vertex potentials. -/
theorem literal_fine_coarse_incidence_bounds {n : ℕ} {K : ℝ}
    (hK : 0 < K) (hn : (n:ℝ) ≤ K) (x : Fin n → ℝ) :
    (∑ i, ((fineIncidence n K *ᵥ x) i / colexANat K (i.val+1))^2) ≤ 4*∑ i, x i^2 ∧
    (∑ i, ((coarseIncidence n K *ᵥ x) i / colexANat K (i.val+1))^2) ≤ 25*∑ i, x i^2 := by
  simp_rw [fineIncidence_normalized hK,coarseIncidence_normalized hK,neg_sq]
  exact colex_fine_coarse_full_bounds hK hn x

end Erdos488.Geometry.SeparatedDistances.FixedDimension
