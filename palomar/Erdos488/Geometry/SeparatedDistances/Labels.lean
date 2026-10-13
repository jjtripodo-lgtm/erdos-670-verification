module

public import Erdos488.Geometry.SeparatedDistances.Defs
public import Mathlib.Tactic

@[expose] public section

namespace Erdos488.Geometry.SeparatedDistances

/-- Colex labels for the edges ending at `j` form the expected consecutive block. -/
theorem colexLabel_eq (i j : ℕ) :
    colexLabel i j = Nat.choose j 2 + i + 1 := rfl

/-- The first colex label in column `j`. -/
theorem colexLabel_zero (j : ℕ) :
    colexLabel 0 j = Nat.choose j 2 + 1 := by simp [colexLabel]

/-- Successive smaller endpoints give successive labels. -/
theorem colexLabel_succ (i j : ℕ) :
    colexLabel (i + 1) j = colexLabel i j + 1 := by
  simp [colexLabel, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- The final edge in colex column `j` has label `choose (j+1) 2`. -/
theorem colexLabel_last (j : ℕ) (hj : 1 ≤ j) :
    colexLabel (j - 1) j = Nat.choose (j + 1) 2 := by
  rw [colexLabel, Nat.choose_succ_succ]
  simp only [Nat.choose_one_right, Nat.succ_eq_add_one]
  norm_num
  omega

/-- Colex labels are positive. -/
theorem colexLabel_pos (i j : ℕ) : 0 < colexLabel i j := by
  simp [colexLabel]

/-- Inside one colex column, labels are injective in the smaller endpoint. -/
theorem colexLabel_injective_left (j : ℕ) : Function.Injective (fun i => colexLabel i j) := by
  intro i k h
  simp only [colexLabel] at h
  omega

/-- A fixed colex column is exactly its consecutive binomial interval. -/
theorem colexLabel_column_exact (j : ℕ) :
    (Finset.range j).image (fun i => colexLabel i j) =
      Finset.Icc (Nat.choose j 2 + 1) (Nat.choose (j + 1) 2) := by
  have hchoose : Nat.choose (j + 1) 2 = Nat.choose j 2 + j := by
    rw [Nat.choose_succ_succ]
    simp only [Nat.choose_one_right, Nat.succ_eq_add_one]
    norm_num
    omega
  ext x
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [hchoose]
    simp only [colexLabel]
    omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨x - (Nat.choose j 2 + 1), ?_, ?_⟩
    · rw [hchoose] at hhi
      omega
    · simp only [colexLabel]
      omega

/-- Across all columns below `n`, colex labels are exactly `1, ..., choose n 2`. -/
theorem colexLabel_range_exact (n : ℕ) :
    (Finset.range n).biUnion
        (fun j => (Finset.range j).image (fun i => colexLabel i j)) =
      Finset.Icc 1 (Nat.choose n 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.range_add_one, Finset.biUnion_insert]
      · rw [ih, colexLabel_column_exact]
        ext x
        simp only [Finset.mem_union, Finset.mem_Icc]
        rw [Nat.choose_succ_succ]
        simp only [Nat.choose_one_right, Nat.succ_eq_add_one]
        norm_num
        omega

/-- The first label in the hybrid seed block of gap `δ`. -/
def hybridGapStart (r δ : ℕ) : ℕ :=
  (δ - 1) * r - Nat.choose δ 2 + 1

/-- The final label in the hybrid seed block of gap `δ`. -/
def hybridGapEnd (r δ : ℕ) : ℕ :=
  hybridGapStart r δ + (r - δ) - 1

/-- The hybrid formula restricted to one seed gap is affine in the smaller endpoint. -/
theorem hybridLabel_seed_gap {r δ i : ℕ} (hi : i < r - δ) :
    hybridLabel r i (i + δ) = hybridGapStart r δ + i := by
  have hj : i + δ < r := by omega
  simp only [hybridLabel, hj, if_true, Nat.add_sub_cancel_left, hybridGapStart]
  rw [Nat.choose_two_right]
  omega

/-- A fixed hybrid seed gap is exactly one consecutive interval of labels. -/
theorem hybridLabel_gap_exact {r δ : ℕ} (hδr : δ < r) :
    (Finset.range (r - δ)).image (fun i => hybridLabel r i (i + δ)) =
      Finset.Icc (hybridGapStart r δ)
        (hybridGapEnd r δ) := by
  ext x
  simp only [hybridGapEnd]
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [hybridLabel_seed_gap hi]
    omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨x - hybridGapStart r δ, ?_, ?_⟩
    · omega
    · rw [hybridLabel_seed_gap (by omega)]
      omega

/-- Consecutive seed-gap blocks meet without a missing label. -/
theorem hybridGapStart_succ {r δ : ℕ} (hδ : 1 ≤ δ) (hδr : δ < r) :
    hybridGapStart r (δ + 1) = hybridGapStart r δ + (r - δ) := by
  have hchoose : Nat.choose (δ + 1) 2 = Nat.choose δ 2 + δ := by
    rw [Nat.choose_succ_succ]
    simp only [Nat.choose_one_right, Nat.succ_eq_add_one]
    norm_num
    omega
  have hbound : Nat.choose δ 2 ≤ (δ - 1) * r := by
    rw [Nat.choose_two_right]
    calc
      δ * (δ - 1) / 2 ≤ δ * (δ - 1) := Nat.div_le_self _ _
      _ ≤ (δ - 1) * r := by nlinarith
  have hmul : δ * r = (δ - 1) * r + r := by
    conv_lhs =>
      rw [show δ = (δ - 1) + 1 by omega]
    simp [Nat.add_mul]
  simp only [hybridGapStart, Nat.add_sub_cancel]
  rw [hchoose]
  omega

/-- The first seed-gap block starts at label one. -/
theorem hybridGapStart_one (r : ℕ) : hybridGapStart r 1 = 1 := by
  simp [hybridGapStart]

/-- Consecutive seed-gap intervals are adjacent. -/
theorem hybridGapStart_succ_eq_end_add_one {r δ : ℕ}
    (hδ : 1 ≤ δ) (hδr : δ + 1 < r) :
    hybridGapStart r (δ + 1) = hybridGapEnd r δ + 1 := by
  rw [hybridGapStart_succ hδ (by omega)]
  simp only [hybridGapEnd]
  omega

/-- The first `m` hybrid seed gaps fill one initial interval. -/
theorem hybrid_seed_gaps_through_exact {r m : ℕ} (hm : 1 ≤ m) (hmr : m < r) :
    (Finset.Icc 1 m).biUnion
        (fun δ => (Finset.range (r - δ)).image
          (fun i => hybridLabel r i (i + δ))) =
      Finset.Icc 1 (hybridGapEnd r m) := by
  induction m with
  | zero => omega
  | succ m ih =>
      by_cases hm0 : m = 0
      · subst m
        simp [hybridLabel_gap_exact (show 1 < r by omega), hybridGapStart_one,
          hybridGapEnd]
      · have hmpos : 1 ≤ m := by omega
        have hmr' : m < r := by omega
        rw [← Finset.insert_Icc_right_eq_Icc_add_one (show 1 ≤ m + 1 by omega),
          Finset.biUnion_insert]
        · rw [ih hmpos hmr', hybridLabel_gap_exact hmr]
          have hend : hybridGapStart r (m + 1) ≤ hybridGapEnd r (m + 1) := by
            simp only [hybridGapEnd]
            omega
          have hadj := hybridGapStart_succ_eq_end_add_one
            (r := r) (δ := m) hmpos (by omega)
          have hbridge : hybridGapEnd r m + 1 ≤ hybridGapEnd r (m + 1) := by
            omega
          ext x
          simp only [Finset.mem_union, Finset.mem_Icc]
          omega

/-- Twice a binomial coefficient `choose q 2` is the consecutive product. -/
theorem two_mul_choose_two (q : ℕ) :
    2 * Nat.choose q 2 = q * (q - 1) := by
  rw [Nat.choose_two_right, Nat.mul_comm 2,
    Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self q)]

/-- The final seed-gap block ends at `choose r 2`. -/
theorem hybridGapEnd_last {r : ℕ} (hr : 2 ≤ r) :
    hybridGapEnd r (r - 1) = Nat.choose r 2 := by
  have hrform : r = (r - 1) + 1 := by omega
  have hchoose : Nat.choose r 2 = Nat.choose (r - 1) 2 + (r - 1) := by
    conv_lhs => rw [hrform]
    rw [Nat.choose_succ_succ]
    simp only [Nat.choose_one_right, Nat.succ_eq_add_one]
    norm_num
    omega
  have hdouble := two_mul_choose_two (r - 1)
  have hmul : (r - 2) * r = (r - 1) * (r - 2) + (r - 2) := by
    calc
      (r - 2) * r = (r - 2) * ((r - 1) + 1) := by rw [← hrform]
      _ = (r - 2) * (r - 1) + (r - 2) := by simp [Nat.mul_add]
      _ = (r - 1) * (r - 2) + (r - 2) := by rw [Nat.mul_comm (r - 2)]
  have hbound : Nat.choose (r - 1) 2 ≤ (r - 2) * r := by
    calc
      Nat.choose (r - 1) 2 ≤ 2 * Nat.choose (r - 1) 2 := by omega
      _ = (r - 1) * (r - 2) := hdouble
      _ ≤ (r - 2) * r := by omega
  have hsub : r - 1 - 1 = r - 2 := by omega
  rw [hsub] at hdouble
  have hrdiff : r - (r - 1) = 1 := by omega
  have hdecomp :
      (r - 2) * r = Nat.choose (r - 1) 2 + (Nat.choose (r - 1) 2 + (r - 2)) := by
    calc
      (r - 2) * r = (r - 1) * (r - 2) + (r - 2) := hmul
      _ = 2 * Nat.choose (r - 1) 2 + (r - 2) := by rw [hdouble]
      _ = Nat.choose (r - 1) 2 + (Nat.choose (r - 1) 2 + (r - 2)) := by omega
  have hcalc :
      (r - 2) * r - Nat.choose (r - 1) 2 + 1 = Nat.choose r 2 := by
    rw [hdecomp, Nat.add_sub_cancel_left, hchoose]
    omega
  simp only [hybridGapEnd, hybridGapStart]
  rw [hsub, hrdiff]
  simpa using hcalc

/-- The labels on all seed edges are exactly `1, ..., choose r 2`. -/
theorem hybrid_seed_labels_exact {r : ℕ} (hr : 2 ≤ r) :
    (Finset.Icc 1 (r - 1)).biUnion
        (fun δ => (Finset.range (r - δ)).image
          (fun i => hybridLabel r i (i + δ))) =
      Finset.Icc 1 (Nat.choose r 2) := by
  rw [hybrid_seed_gaps_through_exact (show 1 ≤ r - 1 by omega)
    (show r - 1 < r by omega), hybridGapEnd_last hr]

/-- Colex columns from `r` onward fill the interval after `choose r 2`. -/
theorem colex_tail_labels_exact {r n : ℕ} :
    (Finset.Icc r (n - 1)).biUnion
        (fun j => (Finset.range j).image (fun i => colexLabel i j)) =
      Finset.Icc (Nat.choose r 2 + 1) (Nat.choose n 2) := by
  ext x
  constructor
  · intro hx
    simp only [Finset.mem_biUnion, Finset.mem_Icc] at hx
    obtain ⟨j, ⟨hrj, hjn⟩, hxcol⟩ := hx
    have hxblock : x ∈ Finset.Icc (Nat.choose j 2 + 1) (Nat.choose (j + 1) 2) := by
      rw [← colexLabel_column_exact]
      exact hxcol
    have hxbounds := Finset.mem_Icc.mp hxblock
    have hlow : Nat.choose r 2 + 1 ≤ x := by
      exact (Nat.add_le_add_right (Nat.choose_le_choose 2 hrj) 1).trans hxbounds.1
    have hjpos : 0 < j := by
      by_contra h
      have : j = 0 := by omega
      subst j
      simp at hxcol
    have hjlt : j < n := by omega
    have hxglobal : x ∈
        (Finset.range n).biUnion
          (fun k => (Finset.range k).image (fun i => colexLabel i k)) := by
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hjlt, hxcol⟩
    rw [colexLabel_range_exact] at hxglobal
    exact Finset.mem_Icc.mpr ⟨hlow, (Finset.mem_Icc.mp hxglobal).2⟩
  · intro hx
    have hxbounds := Finset.mem_Icc.mp hx
    have hxglobal : x ∈
        (Finset.range n).biUnion
          (fun k => (Finset.range k).image (fun i => colexLabel i k)) := by
      rw [colexLabel_range_exact]
      exact Finset.mem_Icc.mpr ⟨by omega, hxbounds.2⟩
    obtain ⟨j, hjn, hxcol⟩ := Finset.mem_biUnion.mp hxglobal
    have hjlt : j < n := Finset.mem_range.mp hjn
    have hrj : r ≤ j := by
      by_contra hnot
      have hjr : j + 1 ≤ r := by omega
      have hxblock : x ∈ Finset.Icc (Nat.choose j 2 + 1) (Nat.choose (j + 1) 2) := by
        rw [← colexLabel_column_exact]
        exact hxcol
      have hxblockbounds := Finset.mem_Icc.mp hxblock
      have hupper : x ≤ Nat.choose r 2 :=
        hxblockbounds.2.trans (Nat.choose_le_choose 2 hjr)
      omega
    simp only [Finset.mem_biUnion, Finset.mem_Icc]
    exact ⟨j, ⟨hrj, by omega⟩, hxcol⟩

/-- The colex tail begins exactly one after the last hybrid seed label. -/
theorem hybrid_tail_first_eq_seed_last_add_one (r : ℕ) :
    colexLabel 0 r = Nat.choose r 2 + 1 := colexLabel_zero r

/-- Seed and tail together use every label `1, ..., choose n 2` exactly as a set. -/
theorem hybrid_labels_exact {r n : ℕ} (hr : 2 ≤ r) (hrn : r ≤ n) :
    ((Finset.Icc 1 (r - 1)).biUnion
        (fun δ => (Finset.range (r - δ)).image
          (fun i => hybridLabel r i (i + δ)))) ∪
      ((Finset.Icc r (n - 1)).biUnion
        (fun j => (Finset.range j).image (fun i => hybridLabel r i j))) =
      Finset.Icc 1 (Nat.choose n 2) := by
  rw [hybrid_seed_labels_exact hr]
  have htail :
      (Finset.Icc r (n - 1)).biUnion
          (fun j => (Finset.range j).image (fun i => hybridLabel r i j)) =
        Finset.Icc (Nat.choose r 2 + 1) (Nat.choose n 2) := by
    calc
      _ = (Finset.Icc r (n - 1)).biUnion
          (fun j => (Finset.range j).image (fun i => colexLabel i j)) := by
            apply Finset.biUnion_congr rfl
            intro j hj
            apply Finset.image_congr
            intro i hi
            simp [hybridLabel, Nat.not_lt.mpr (Finset.mem_Icc.mp hj).1]
      _ = _ := colex_tail_labels_exact
  rw [htail]
  ext x
  simp only [Finset.mem_union, Finset.mem_Icc]
  have hchoose : Nat.choose r 2 ≤ Nat.choose n 2 := Nat.choose_le_choose 2 hrn
  omega

/-- On the tail, the hybrid label is definitionally the colex label. -/
theorem hybridLabel_of_le {r i j : ℕ} (h : r ≤ j) :
    hybridLabel r i j = colexLabel i j := by
  simp [hybridLabel, Nat.not_lt.mpr h]

/-- The first gap in the seed has the simple row-major label `i+1`. -/
theorem hybridLabel_gap_one {r i : ℕ} (h : i + 1 < r) :
    hybridLabel r i (i + 1) = i + 1 := by
  simp [hybridLabel, h]

end Erdos488.Geometry.SeparatedDistances
