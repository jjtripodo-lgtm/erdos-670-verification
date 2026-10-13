module

public import Mathlib.Tactic

@[expose] public section

/-! The finite ordering layer only. No Euclidean realization or local-distance
geometry is assumed proved by this file. Every scalar guard is explicit. -/
namespace Erdos488.Geometry.SeparatedDistances.FixedDimension

/-- Sum adjacent unit gaps over a bounded natural index interval. -/
theorem bounded_step_sum (f : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ i, i + 1 < N → 1 ≤ f (i + 1) - f i) :
    ∀ i j, i ≤ j → j < N → (j : ℝ) - (i : ℝ) ≤ f j - f i := by
  intro i j
  induction j with
  | zero =>
      intro hij _
      have hi : i = 0 := by omega
      subst i
      simp
  | succ j ih =>
      intro hij hj
      by_cases h : i ≤ j
      · have h1 := ih h (by omega)
        have h2 := hstep j hj
        push_cast
        linarith
      · have hi : i = j + 1 := by omega
        subst i
        simp

/-- Adjacent unit gaps imply weak monotonicity, including equal endpoints. -/
theorem bounded_step_mono (f : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ i, i + 1 < N → 1 ≤ f (i + 1) - f i)
    {i j : ℕ} (hij : i ≤ j) (hj : j < N) : f i ≤ f j := by
  have h := bounded_step_sum f N hstep i j hij hj
  have hc : (i : ℝ) ≤ j := by exact_mod_cast hij
  linarith

/-- A nonempty chain of adjacent unit gaps has gap at least one. -/
theorem bounded_step_gap (f : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ i, i + 1 < N → 1 ≤ f (i + 1) - f i)
    {i j : ℕ} (hij : i < j) (hj : j < N) : 1 ≤ f j - f i := by
  have h := bounded_step_sum f N hstep i j (by omega) hj
  have hc : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
  linarith

/-- Fine-digit gaps and last-to-first carries order the entire rectangular block.
The carry hypothesis is on the last fine digit, not on equal fine digits. -/
theorem rectangular_lex_gap (F : ℕ → ℕ → ℝ) (M k : ℕ) (hk : 0 < k)
    (hfine : ∀ a, a < M → ∀ b, b + 1 < k → 1 ≤ F a (b + 1) - F a b)
    (hcarry : ∀ a, a + 1 < M → 1 ≤ F (a + 1) 0 - F a (k - 1))
    {a b a' b' : ℕ} (ha : a < M) (hb : b < k) (ha' : a' < M) (hb' : b' < k)
    (hlex : a < a' ∨ (a = a' ∧ b < b')) : 1 ≤ F a' b' - F a b := by
  have hrow (c : ℕ) (hc : c < M) {i j : ℕ} (hij : i ≤ j) (hj : j < k) :
      F c i ≤ F c j := bounded_step_mono (F c) k (hfine c hc) hij hj
  have hfirst : ∀ c, c + 1 < M → 1 ≤ F (c + 1) 0 - F c 0 := by
    intro c hc
    have h1 := hrow c (by omega) (show 0 ≤ k - 1 by omega) (by omega)
    have h2 := hcarry c hc
    linarith
  rcases hlex with haa | ⟨rfl, hbb⟩
  · have h1 := hrow a ha (show b ≤ k - 1 by omega) (by omega)
    have h2 := hcarry a (by omega)
    have h3 := bounded_step_mono (fun c => F c 0) M hfirst
      (show a + 1 ≤ a' by omega) ha'
    have h4 := hrow a' ha' (show 0 ≤ b' by omega) hb'
    linarith
  · exact bounded_step_gap (F a) k (hfine a ha) hbb hb'

/-- All distinct cells, not just adjacent cells, are separated. -/
theorem rectangular_all_pairs_separated (F : ℕ → ℕ → ℝ) (M k : ℕ) (hk : 0 < k)
    (hfine : ∀ a, a < M → ∀ b, b + 1 < k → 1 ≤ F a (b + 1) - F a b)
    (hcarry : ∀ a, a + 1 < M → 1 ≤ F (a + 1) 0 - F a (k - 1))
    {a b a' b' : ℕ} (ha : a < M) (hb : b < k) (ha' : a' < M) (hb' : b' < k)
    (hne : (a,b) ≠ (a',b')) : 1 ≤ |F a b - F a' b'| := by
  by_cases hlex : a < a' ∨ (a = a' ∧ b < b')
  · have h := rectangular_lex_gap F M k hk hfine hcarry ha hb ha' hb' hlex
    have habs := le_abs_self (F a' b' - F a b)
    rw [abs_sub_comm] at habs
    linarith
  · have hrev : a' < a ∨ (a' = a ∧ b' < b) := by
      have hn : a ≠ a' ∨ b ≠ b' := by
        by_contra h
        push Not at h
        exact hne (by rcases h with ⟨rfl,rfl⟩; rfl)
      omega
    have h := rectangular_lex_gap F M k hk hfine hcarry ha' hb' ha hb hrev
    exact h.trans (le_abs_self _)

/-- The scalar fine-digit guard, retaining an explicit adjacent error difference. -/
theorem fine_step_guard (s r Flip f₀ f₁ e₀ e₁ : ℝ)
    (hf : s*r ≤ f₁-f₀) (he : |e₁-e₀| ≤ Flip)
    (hguard : 1 ≤ s*r-Flip) : 1 ≤ (f₁+e₁)-(f₀+e₀) := by
  have h := (abs_le.mp he).1
  linarith

/-- The scalar carry guard uses a full k-step error budget. -/
theorem carry_step_guard (s c r fstar Flip coarse₀ coarse₁ fine₀ fineLast e₀ e₁ : ℝ)
    (k : ℕ) (hc : s*c*r ≤ coarse₁-coarse₀)
    (hf : fineLast-fine₀ ≤ 2*s*fstar) (he : |e₁-e₀| ≤ k*Flip)
    (hguard : 1 ≤ s*(c*r-2*fstar)-k*Flip) :
    1 ≤ (coarse₁+fine₀+e₁)-(coarse₀+fineLast+e₀) := by
  have h := (abs_le.mp he).1
  nlinarith

/-- Macro blocks stay separate after both endpoint perturbations and errors. -/
theorem macro_step_guard (S A E base₀ base₁ perturb₀ perturb₁ error₀ error₁ : ℝ)
    (hbase : S ≤ base₁-base₀) (hp₀ : |perturb₀| ≤ A) (hp₁ : |perturb₁| ≤ A)
    (he₀ : |error₀| ≤ E) (he₁ : |error₁| ≤ E) (hguard : 1 ≤ S-2*A-2*E) :
    1 ≤ (base₁+perturb₁+error₁)-(base₀+perturb₀+error₀) := by
  rcases abs_le.mp hp₀ with ⟨_,hp₀⟩
  rcases abs_le.mp hp₁ with ⟨hp₁,_⟩
  rcases abs_le.mp he₀ with ⟨_,he₀⟩
  rcases abs_le.mp he₁ with ⟨he₁,_⟩
  linarith

/-- A rectangular block has its first and last entries as genuine extrema. -/
theorem rectangular_endpoints (F : ℕ → ℕ → ℝ) (M k : ℕ) (hM : 0 < M) (hk : 0 < k)
    (hfine : ∀ a, a < M → ∀ b, b + 1 < k → 1 ≤ F a (b + 1) - F a b)
    (hcarry : ∀ a, a + 1 < M → 1 ≤ F (a + 1) 0 - F a (k - 1))
    {a b : ℕ} (ha : a < M) (hb : b < k) :
    F 0 0 ≤ F a b ∧ F a b ≤ F (M - 1) (k - 1) := by
  constructor
  · by_cases hz : a = 0 ∧ b = 0
    · rcases hz with ⟨rfl,rfl⟩; rfl
    · have hlex : 0 < a ∨ (0 = a ∧ 0 < b) := by omega
      have h := rectangular_lex_gap F M k hk hfine hcarry hM hk ha hb hlex
      linarith
  · by_cases hz : a = M - 1 ∧ b = k - 1
    · rcases hz with ⟨rfl,rfl⟩; rfl
    · have hlex : a < M-1 ∨ (a = M-1 ∧ b < k-1) := by omega
      have h := rectangular_lex_gap F M k hk hfine hcarry ha hb (by omega) (by omega) hlex
      linarith

/-- Ordered macro, coarse, and fine digits: all distinct triples are separated.
The proof exhausts equal/different macro blocks and both inner digit cases. -/
theorem three_digit_all_pairs_separated (D : ℕ → ℕ → ℕ → ℝ) (M k : ℕ) (hk : 0 < k)
    (hfine : ∀ a, a < M → ∀ i, i < k → ∀ j, j+1 < k →
      1 ≤ D a i (j+1)-D a i j)
    (hcarry : ∀ a, a < M → ∀ i, i+1 < k →
      1 ≤ D a (i+1) 0-D a i (k-1))
    (hmacro : ∀ a, a+1 < M → 1 ≤ D (a+1) 0 0-D a (k-1) (k-1))
    {a i j b u v : ℕ} (ha : a < M) (hi : i < k) (hj : j < k)
    (hb : b < M) (hu : u < k) (hv : v < k)
    (hne : (a,i,j) ≠ (b,u,v)) : 1 ≤ |D a i j-D b u v| := by
  have hend (c : ℕ) (hc : c < M) (x y : ℕ) (hx : x < k) (hy : y < k) :=
    rectangular_endpoints (D c) k k hk hk (hfine c hc) (hcarry c hc) hx hy
  have hfirst : ∀ c, c+1 < M → 1 ≤ D (c+1) 0 0-D c 0 0 := by
    intro c hc
    have h₀ := (hend c (by omega) 0 0 hk hk).2
    have h₁ := hmacro c hc
    linarith
  have hordered : ∀ c x y d z w, c < M → x < k → y < k → d < M → z < k → w < k →
      c < d → 1 ≤ D d z w-D c x y := by
    intro c x y d z w hc hx hy hd hz hw hcd
    have h₀ := (hend c hc x y hx hy).2
    have h₁ := hmacro c (by omega)
    have h₂ := bounded_step_mono (fun c => D c 0 0) M hfirst (show c+1 ≤ d by omega) hd
    have h₃ := (hend d hd z w hz hw).1
    linarith
  rcases lt_trichotomy a b with hab | hab | hab
  · have h := hordered a i j b u v ha hi hj hb hu hv hab
    have ht := le_abs_self (D b u v-D a i j)
    rw [abs_sub_comm] at ht
    linarith
  · subst b
    have hne' : (i,j) ≠ (u,v) := by
      intro h
      apply hne
      rcases Prod.mk.inj h with ⟨rfl,rfl⟩
      rfl
    exact rectangular_all_pairs_separated (D a) k k hk (hfine a ha) (hcarry a ha)
      hi hj hu hv hne'
  · exact (hordered b u v a i j hb hu hv ha hi hj hab).trans (le_abs_self _)

/-- The local/cross guard bounds actual scalar lengths, including their errors. -/
theorem local_cross_scalar_guard (loc cross R Tmin E : ℝ)
    (hl : loc ≤ 2*R) (hc : Tmin-E ≤ cross) (hg : 2*R+1 ≤ Tmin-E) :
    1 ≤ cross-loc := by linarith

/-- Exhaustive assembly for two disjoint families. The mixed cases are both
checked; this does not assert that a geometric configuration has been built. -/
theorem two_family_all_pairs_separated {ι κ : Type*} (L : ι → ℝ) (C : κ → ℝ)
    (hL : ∀ x y, x ≠ y → 1 ≤ |L x-L y|)
    (hC : ∀ x y, x ≠ y → 1 ≤ |C x-C y|)
    (hLC : ∀ x y, 1 ≤ C y-L x) :
    ∀ x y : ι ⊕ κ, x ≠ y → 1 ≤ |Sum.elim L C x-Sum.elim L C y| := by
  intro x y hxy
  cases x with
  | inl x =>
    cases y with
    | inl y => exact hL x y (by intro h; subst y; exact hxy rfl)
    | inr y =>
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [abs_sub_comm]
      exact (hLC x y).trans (le_abs_self _)
  | inr x =>
    cases y with
    | inl y => exact (hLC y x).trans (le_abs_self _)
    | inr y => exact hC x y (by intro h; subst y; exact hxy rfl)

end Erdos488.Geometry.SeparatedDistances.FixedDimension
