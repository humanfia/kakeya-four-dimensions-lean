-- Ported from this tree's o018 branch x0052 (session x0052), commit 82e5b5c26a09, file Submission/Obl/k4_framework_from_matching_clustering_conic/RetainedEdge/ScalarClosure.lean;
-- only the namespace and module paths were renamed to o071's.
import Submission.Obl.k4_retained_edge_planar_rigidity.RetainedEdge.CellRuzsa

/-!
# Scalar closure of a common pair (paper Lemma 7.3, second half)

Let `E, F` be finite planar sets with `N(E), N(F)` between `L/K^a` and `K^a L`, `N(E - F) ≤ K^a L`,
and let `ℛ` be a finite set of ratios `t` with `|t|, |t⁻¹| ≤ K` and `N(E - t F) ≤ K^a L`. The
Ruzsa triangle inequality bounds `N(p E - E)` and `N(p F - E)` for every product `p` of `n`
ratios; Ruzsa covering and Plünnecke then bound the occupied cells of
`∑ᵢ (cᵢ E + dᵢ F)` whenever every coefficient is a sum of `k` such products, with a common
dilation `R⁻ⁿ` (`R ≥ 1`). This is paper display `re:scalar-support` for the generated coefficients
of Lemma 7.4. Here `N(X)` is the number of occupied cells of mesh `h`.
-/

namespace Submission.Obl.k4_retained_edge_planar_rigidity

open scoped Pointwise

noncomputable section

/-- The standing hypotheses of the scalar closure. -/
structure ClosureData (h K L : ℝ) (a : ℕ) (E F : Finset (ℝ × ℝ)) (ℛ : Finset ℝ) : Prop where
  one_le_K : 1 ≤ K
  L_pos : 0 < L
  E_lower : L / K ^ a ≤ (cells h E).card
  E_upper : ((cells h E).card : ℝ) ≤ K ^ a * L
  F_lower : L / K ^ a ≤ (cells h F).card
  EF : ((cells h (E - F)).card : ℝ) ≤ K ^ a * L
  ratio_ne : ∀ t ∈ ℛ, t ≠ 0
  ratio_le : ∀ t ∈ ℛ, |t| ≤ K
  ratio_inv_le : ∀ t ∈ ℛ, |t⁻¹| ≤ K
  EtF : ∀ t ∈ ℛ, ((cells h (E - t • F)).card : ℝ) ≤ K ^ a * L

namespace ClosureData

variable {h K L : ℝ} {a : ℕ} {E F : Finset (ℝ × ℝ)} {ℛ : Finset ℝ}

theorem Kpow_pos (D : ClosureData h K L a E F ℛ) (e : ℕ) : 0 < K ^ e :=
  pow_pos (lt_of_lt_of_le one_pos D.one_le_K) e

theorem E_pos (D : ClosureData h K L a E F ℛ) : 0 < ((cells h E).card : ℝ) :=
  lt_of_lt_of_le (div_pos D.L_pos (D.Kpow_pos a)) D.E_lower

theorem F_pos (D : ClosureData h K L a E F ℛ) : 0 < ((cells h F).card : ℝ) :=
  lt_of_lt_of_le (div_pos D.L_pos (D.Kpow_pos a)) D.F_lower

theorem two_abs_add_two_le (D : ClosureData h K L a E F ℛ) {c : ℝ} (hc : |c| ≤ K) :
    2 * |c| + 2 ≤ 4 * K := by
  have := D.one_le_K; linarith

/-- `N(E - E) ≤ 2¹⁰ K^{3a} L`. -/
theorem EE (D : ClosureData h K L a E F ℛ) :
    ((cells h (E - E)).card : ℝ) ≤ 2 ^ 10 * K ^ (3 * a) * L := by
  have hr := cells_ruzsa h E F E
  have hFE : ((cells h (F - E)).card : ℝ) ≤ 4 * K ^ a * L := by
    have := card_cells_sub_comm_le h E F
    have h2 : ((cells h (F - E)).card : ℝ) ≤ (cells h (E - F)).card * 4 := by exact_mod_cast this
    nlinarith [D.EF]
  have hF := D.F_lower
  have hKa := D.Kpow_pos a
  have hL := D.L_pos
  have hNEE : (0 : ℝ) ≤ (cells h (E - E)).card := by positivity
  have hEF0 : (0 : ℝ) ≤ (cells h (E - F)).card := by positivity
  -- N(E-E) * N(F) ≤ 256 * (K^a L) * (4 K^a L)
  have step : ((cells h (E - E)).card : ℝ) * (L / K ^ a) ≤ 256 * (K ^ a * L) * (4 * K ^ a * L) := by
    calc ((cells h (E - E)).card : ℝ) * (L / K ^ a) ≤ (cells h (E - E)).card * (cells h F).card :=
          mul_le_mul_of_nonneg_left hF hNEE
      _ ≤ 256 * (cells h (E - F)).card * (cells h (F - E)).card := hr
      _ ≤ 256 * (K ^ a * L) * (4 * K ^ a * L) := by
          gcongr
          · exact D.EF
  have e1 : (2 : ℝ) ^ 10 * K ^ (3 * a) * L = (256 * (K ^ a * L) * (4 * K ^ a * L)) / (L / K ^ a) := by
    field_simp
    ring
  rw [e1, le_div_iff₀ (div_pos hL hKa)]
  exact step

end ClosureData

theorem le_div_of_mul_le_lower {x y B ℓ : ℝ} (hℓ : 0 < ℓ) (hy : ℓ ≤ y) (hx : 0 ≤ x)
    (hxy : x * y ≤ B) : x ≤ B / ℓ := by
  rw [le_div_iff₀ hℓ]
  exact le_trans (mul_le_mul_of_nonneg_left hy hx) hxy

theorem card_cells_smul_sub_le (h c : ℝ) (U V : Finset (ℝ × ℝ)) :
    ((cells h (c • U - c • V)).card : ℝ) ≤ (2 * |c| + 2) ^ 2 * (cells h (U - V)).card := by
  calc ((cells h (c • U - c • V)).card : ℝ) ≤ (cells h (c • (U - V))).card := by
        exact_mod_cast Finset.card_le_card (cells_mono (smul_sub_finset_subset c U V))
    _ ≤ (2 * |c| + 2) ^ 2 * (cells h (U - V)).card := card_cells_smul_le h c _

theorem card_cells_smul_lower {h c : ℝ} (hc : c ≠ 0) (U : Finset (ℝ × ℝ)) {B : ℝ}
    (hB : 2 * |c⁻¹| + 2 ≤ B) :
    ((cells h U).card : ℝ) / B ^ 2 ≤ (cells h (c • U)).card := by
  have h1 := card_cells_le_smul (h := h) hc U
  have h0 : 0 < 2 * |c⁻¹| + 2 := by positivity
  have hB0 : 0 < B := lt_of_lt_of_le h0 hB
  rw [div_le_iff₀ (by positivity)]
  calc ((cells h U).card : ℝ) ≤ (2 * |c⁻¹| + 2) ^ 2 * (cells h (c • U)).card := h1
    _ ≤ B ^ 2 * (cells h (c • U)).card := by gcongr
    _ = (cells h (c • U)).card * B ^ 2 := by ring

namespace ClosureData

variable {h K L : ℝ} {a : ℕ} {E F : Finset (ℝ × ℝ)} {ℛ : Finset ℝ}

/-- `N(t E - E) ≤ 2¹⁸ K^{3a+4} L` for a ratio `t`. -/
theorem tE (D : ClosureData h K L a E F ℛ) {t : ℝ} (ht : t ∈ ℛ) :
    ((cells h (t • E - E)).card : ℝ) ≤ 2 ^ 18 * K ^ (3 * a + 4) * L := by
  have hK := D.one_le_K
  have hKa := D.Kpow_pos a
  have hL := D.L_pos
  have hr := cells_ruzsa h (t • E) (t • F) E
  have h1 : ((cells h (t • E - t • F)).card : ℝ) ≤ (4 * K) ^ 2 * (K ^ a * L) := by
    calc ((cells h (t • E - t • F)).card : ℝ) ≤ (2 * |t| + 2) ^ 2 * (cells h (E - F)).card :=
          card_cells_smul_sub_le h t E F
      _ ≤ (4 * K) ^ 2 * (K ^ a * L) := by
          gcongr
          · exact D.two_abs_add_two_le (D.ratio_le t ht)
          · exact D.EF
  have h2 : ((cells h (t • F - E)).card : ℝ) ≤ 4 * (K ^ a * L) := by
    have := card_cells_sub_comm_le h E (t • F)
    have h' : ((cells h (t • F - E)).card : ℝ) ≤ (cells h (E - t • F)).card * 4 := by
      exact_mod_cast this
    nlinarith [D.EtF t ht]
  have h3 : (L / K ^ a) / (4 * K) ^ 2 ≤ ((cells h (t • F)).card : ℝ) := by
    calc (L / K ^ a) / (4 * K) ^ 2 ≤ ((cells h F).card : ℝ) / (4 * K) ^ 2 := by
          gcongr; exact D.F_lower
      _ ≤ ((cells h (t • F)).card : ℝ) :=
          card_cells_smul_lower (D.ratio_ne t ht) F (D.two_abs_add_two_le (D.ratio_inv_le t ht))
  have hpos : 0 < (L / K ^ a) / (4 * K) ^ 2 := by positivity
  have key := le_div_of_mul_le_lower hpos h3 (by positivity)
    (hr.trans (by gcongr : 256 * ((cells h (t • E - t • F)).card : ℝ) *
      (cells h (t • F - E)).card ≤ 256 * ((4 * K) ^ 2 * (K ^ a * L)) * (4 * (K ^ a * L))))
  calc ((cells h (t • E - E)).card : ℝ)
      ≤ 256 * ((4 * K) ^ 2 * (K ^ a * L)) * (4 * (K ^ a * L)) / ((L / K ^ a) / (4 * K) ^ 2) := key
    _ = 2 ^ 18 * K ^ (3 * a + 4) * L := by
        field_simp
        ring

/-- The multiplier for one more ratio in a product. -/
def M1 (K : ℝ) (a : ℕ) : ℝ := 2 ^ 34 * K ^ (4 * a + 8)

/-- One more ratio in front of a product. -/
theorem prod_step (D : ClosureData h K L a E F ℛ) {t : ℝ} (ht : t ∈ ℛ) (p : ℝ) :
    ((cells h ((t * p) • E - E)).card : ℝ) ≤ M1 K a * (cells h (p • E - E)).card := by
  have hK := D.one_le_K
  have hKa := D.Kpow_pos a
  have hL := D.L_pos
  have hr := cells_ruzsa h ((t * p) • E) (t • E) E
  have h1 : ((cells h ((t * p) • E - t • E)).card : ℝ) ≤
      (4 * K) ^ 2 * (cells h (p • E - E)).card := by
    rw [← smul_smul_finset]
    calc ((cells h (t • p • E - t • E)).card : ℝ) ≤
          (2 * |t| + 2) ^ 2 * (cells h (p • E - E)).card := card_cells_smul_sub_le h t _ E
      _ ≤ (4 * K) ^ 2 * (cells h (p • E - E)).card := by
          gcongr; exact D.two_abs_add_two_le (D.ratio_le t ht)
  have h2 := D.tE ht
  have h3 : (L / K ^ a) / (4 * K) ^ 2 ≤ ((cells h (t • E)).card : ℝ) := by
    calc (L / K ^ a) / (4 * K) ^ 2 ≤ ((cells h E).card : ℝ) / (4 * K) ^ 2 := by
          gcongr; exact D.E_lower
      _ ≤ ((cells h (t • E)).card : ℝ) :=
          card_cells_smul_lower (D.ratio_ne t ht) E (D.two_abs_add_two_le (D.ratio_inv_le t ht))
  have hpos : 0 < (L / K ^ a) / (4 * K) ^ 2 := by positivity
  have key := le_div_of_mul_le_lower hpos h3 (by positivity)
    (hr.trans (by gcongr : 256 * ((cells h ((t * p) • E - t • E)).card : ℝ) *
      (cells h (t • E - E)).card ≤ 256 * ((4 * K) ^ 2 * (cells h (p • E - E)).card) *
        (2 ^ 18 * K ^ (3 * a + 4) * L)))
  calc ((cells h ((t * p) • E - E)).card : ℝ)
      ≤ 256 * ((4 * K) ^ 2 * (cells h (p • E - E)).card) * (2 ^ 18 * K ^ (3 * a + 4) * L) /
          ((L / K ^ a) / (4 * K) ^ 2) := key
    _ = M1 K a * (cells h (p • E - E)).card := by
        rw [M1]
        field_simp
        ring

/-- Products of `n` ratios: the bound on `N(p E - E)` and the size of `p`. -/
theorem prod_bound (D : ClosureData h K L a E F ℛ) :
    ∀ (n : ℕ) (T : Fin n → ℝ), (∀ j, T j ∈ ℛ) →
      ((cells h ((∏ j, T j) • E - E)).card : ℝ) ≤ M1 K a ^ n * (2 ^ 10 * K ^ (3 * a) * L) ∧
      (∏ j, T j) ≠ 0 ∧ |∏ j, T j| ≤ K ^ n ∧ |(∏ j, T j)⁻¹| ≤ K ^ n := by
  intro n
  induction n with
  | zero =>
    intro T _
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul, pow_zero, one_mul, abs_one,
      inv_one, le_refl, and_true, ne_eq, one_ne_zero, not_false_eq_true]
    exact D.EE
  | succ n ih =>
    intro T hT
    obtain ⟨hb, hne, hle, hinv⟩ := ih (fun j => T j.succ) (fun j => hT j.succ)
    rw [Fin.prod_univ_succ]
    have hK := D.one_le_K
    have hM : 0 ≤ M1 K a := by rw [M1]; positivity
    refine ⟨?_, mul_ne_zero (D.ratio_ne _ (hT 0)) hne, ?_, ?_⟩
    · calc ((cells h ((T 0 * ∏ j : Fin n, T j.succ) • E - E)).card : ℝ)
          ≤ M1 K a * (cells h ((∏ j : Fin n, T j.succ) • E - E)).card := D.prod_step (hT 0) _
        _ ≤ M1 K a * (M1 K a ^ n * (2 ^ 10 * K ^ (3 * a) * L)) := by gcongr
        _ = M1 K a ^ (n + 1) * (2 ^ 10 * K ^ (3 * a) * L) := by ring
    · rw [abs_mul, pow_succ']
      exact mul_le_mul (D.ratio_le _ (hT 0)) hle (abs_nonneg _) (by positivity)
    · rw [mul_inv, abs_mul, pow_succ']
      exact mul_le_mul (D.ratio_inv_le _ (hT 0)) hinv (abs_nonneg _) (by positivity)

/-- `N(p F - E)` for a product `p` of `n` ratios. -/
theorem prodF_bound (D : ClosureData h K L a E F ℛ) (n : ℕ) (T : Fin n → ℝ) (hT : ∀ j, T j ∈ ℛ) :
    ((cells h ((∏ j, T j) • F - E)).card : ℝ) ≤
      2 ^ 18 * K ^ (4 * n + 2 * a) * (M1 K a ^ n * (2 ^ 10 * K ^ (3 * a) * L)) := by
  obtain ⟨hb, hne, hle, hinv⟩ := D.prod_bound n T hT
  set p := ∏ j, T j
  have hK := D.one_le_K
  have hKa := D.Kpow_pos a
  have hKn : 1 ≤ K ^ n := one_le_pow₀ hK
  have hL := D.L_pos
  have hr := cells_ruzsa h (p • F) (p • E) E
  have hFE : ((cells h (F - E)).card : ℝ) ≤ 4 * (K ^ a * L) := by
    have := card_cells_sub_comm_le h E F
    have h' : ((cells h (F - E)).card : ℝ) ≤ (cells h (E - F)).card * 4 := by exact_mod_cast this
    nlinarith [D.EF]
  have h1 : ((cells h (p • F - p • E)).card : ℝ) ≤ (4 * K ^ n) ^ 2 * (4 * (K ^ a * L)) := by
    calc ((cells h (p • F - p • E)).card : ℝ) ≤ (2 * |p| + 2) ^ 2 * (cells h (F - E)).card :=
          card_cells_smul_sub_le h p F E
      _ ≤ (4 * K ^ n) ^ 2 * (4 * (K ^ a * L)) := by
          gcongr
          · linarith
  have h3 : (L / K ^ a) / (4 * K ^ n) ^ 2 ≤ ((cells h (p • E)).card : ℝ) := by
    calc (L / K ^ a) / (4 * K ^ n) ^ 2 ≤ ((cells h E).card : ℝ) / (4 * K ^ n) ^ 2 := by
          gcongr; exact D.E_lower
      _ ≤ ((cells h (p • E)).card : ℝ) := card_cells_smul_lower hne E (by linarith)
  have hpos : 0 < (L / K ^ a) / (4 * K ^ n) ^ 2 := by positivity
  have key := le_div_of_mul_le_lower hpos h3 (by positivity)
    (hr.trans (by gcongr : 256 * ((cells h (p • F - p • E)).card : ℝ) *
      (cells h (p • E - E)).card ≤ 256 * ((4 * K ^ n) ^ 2 * (4 * (K ^ a * L))) *
        (M1 K a ^ n * (2 ^ 10 * K ^ (3 * a) * L))))
  calc ((cells h (p • F - E)).card : ℝ)
      ≤ 256 * ((4 * K ^ n) ^ 2 * (4 * (K ^ a * L))) * (M1 K a ^ n * (2 ^ 10 * K ^ (3 * a) * L)) /
          ((L / K ^ a) / (4 * K ^ n) ^ 2) := key
    _ = 2 ^ 18 * K ^ (4 * n + 2 * a) * (M1 K a ^ n * (2 ^ 10 * K ^ (3 * a) * L)) := by
        field_simp
        ring


/-- The bound on `N(p X - E) / L` for a product `p` of `n` ratios and `X = E` or `X = F`. -/
def Bn (K : ℝ) (a n : ℕ) : ℝ := 2 ^ 18 * K ^ (4 * n + 2 * a) * (M1 K a ^ n * (2 ^ 10 * K ^ (3 * a)))

theorem Bn_nonneg (D : ClosureData h K L a E F ℛ) (n : ℕ) : 0 ≤ Bn K a n := by
  have := D.one_le_K
  unfold Bn M1; positivity

theorem prodE_le_Bn (D : ClosureData h K L a E F ℛ) (n : ℕ) (T : Fin n → ℝ) (hT : ∀ j, T j ∈ ℛ) :
    ((cells h ((∏ j, T j) • E - E)).card : ℝ) ≤ Bn K a n * L := by
  have hb := (D.prod_bound n T hT).1
  have hK := D.one_le_K
  have hL := D.L_pos
  have h1 : (1 : ℝ) ≤ 2 ^ 18 * K ^ (4 * n + 2 * a) := by
    have : (1 : ℝ) ≤ K ^ (4 * n + 2 * a) := one_le_pow₀ hK
    nlinarith
  have hM : 0 ≤ M1 K a ^ n * (2 ^ 10 * K ^ (3 * a) * L) := by unfold M1; positivity
  calc ((cells h ((∏ j, T j) • E - E)).card : ℝ) ≤ M1 K a ^ n * (2 ^ 10 * K ^ (3 * a) * L) := hb
    _ ≤ 2 ^ 18 * K ^ (4 * n + 2 * a) * (M1 K a ^ n * (2 ^ 10 * K ^ (3 * a) * L)) :=
        le_mul_of_one_le_left hM h1
    _ = Bn K a n * L := by unfold Bn; ring

theorem prodF_le_Bn (D : ClosureData h K L a E F ℛ) (n : ℕ) (T : Fin n → ℝ) (hT : ∀ j, T j ∈ ℛ) :
    ((cells h ((∏ j, T j) • F - E)).card : ℝ) ≤ Bn K a n * L := by
  have := D.prodF_bound n T hT
  calc ((cells h ((∏ j, T j) • F - E)).card : ℝ) ≤
      2 ^ 18 * K ^ (4 * n + 2 * a) * (M1 K a ^ n * (2 ^ 10 * K ^ (3 * a) * L)) := this
    _ = Bn K a n * L := by unfold Bn; ring

end ClosureData

theorem smul_sum_finset_subset {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (X : Finset (ℝ × ℝ)) : (∑ l ∈ s, f l) • X ⊆ ∑ l ∈ s, f l • X := by
  induction s using Finset.induction_on with
  | empty =>
    intro z hz
    obtain ⟨x, -, rfl⟩ := Finset.mem_smul_finset.mp hz
    simp only [Finset.sum_empty, zero_smul]
    exact Finset.mem_zero.mpr rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_smul_finset.mp hz
    rw [add_smul]
    exact Finset.add_mem_add (Finset.smul_mem_smul_finset hx)
      (ih (Finset.smul_mem_smul_finset hx))

theorem sum_finset_subset_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (A B : ι → Finset (ℝ × ℝ)) (hAB : ∀ i ∈ s, A i ⊆ B i) : ∑ i ∈ s, A i ⊆ ∑ i ∈ s, B i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact Finset.add_subset_add (hAB a (Finset.mem_insert_self a s))
      (ih fun i hi => hAB i (Finset.mem_insert_of_mem hi))

/-- The product dilates entering a generated coefficient set. -/
def genDilates {m k n : ℕ} (T S : Fin m → Fin k → Fin n → ℝ) (E F : Finset (ℝ × ℝ)) :
    Fin m × Fin k × Bool → Finset (ℝ × ℝ)
  | (i, l, true) => (∏ j, T i l j) • E
  | (i, l, false) => (∏ j, S i l j) • F

theorem generated_subset {m k n : ℕ} {R : ℝ} (T S : Fin m → Fin k → Fin n → ℝ)
    (E F : Finset (ℝ × ℝ)) :
    ∑ i, ((∑ l, ∏ j, T i l j / R) • E + (∑ l, ∏ j, S i l j / R) • F) ⊆
      (R⁻¹ ^ n) • ∑ α, genDilates T S E F α := by
  classical
  have hprod : ∀ (U : Fin n → ℝ), ∏ j, U j / R = R⁻¹ ^ n * ∏ j, U j := by
    intro U
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      div_eq_mul_inv, mul_comm, inv_pow]
  have hsplit : ∑ α, genDilates T S E F α =
      ∑ i, (∑ l, (∏ j, T i l j) • E + ∑ l, (∏ j, S i l j) • F) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Fintype.sum_bool]
    rfl
  rw [hsplit, Finset.smul_sum]
  refine sum_finset_subset_sum _ _ _ fun i _ => ?_
  rw [smul_add, Finset.smul_sum, Finset.smul_sum]
  refine Finset.add_subset_add ?_ ?_
  · calc (∑ l, ∏ j, T i l j / R) • E ⊆ ∑ l, (∏ j, T i l j / R) • E := smul_sum_finset_subset _ _ _
      _ = ∑ l, R⁻¹ ^ n • (∏ j, T i l j) • E := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hprod, smul_smul_finset]
  · calc (∑ l, ∏ j, S i l j / R) • F ⊆ ∑ l, (∏ j, S i l j / R) • F := smul_sum_finset_subset _ _ _
      _ = ∑ l, R⁻¹ ^ n • (∏ j, S i l j) • F := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hprod, smul_smul_finset]

namespace ClosureData

variable {h K L : ℝ} {a : ℕ} {E F : Finset (ℝ × ℝ)} {ℛ : Finset ℝ}

/-- The cover-count constant of the scalar closure. -/
def closureConst (K : ℝ) (a m k n : ℕ) : ℝ :=
  16 * ((16 * Bn K a n * K ^ a) ^ (m * (k * 2)) * (2 ^ 14 * K ^ (4 * a)) ^ (2 * (m * (k * 2))) *
    (4 * K ^ a) * (((m * (k * 2) : ℕ) : ℝ) + 1) ^ 2)

/-- **Scalar closure** (paper Lemma 7.3, display `re:scalar-support`, for the generated
coefficients of Lemma 7.4): every sum `∑ᵢ (cᵢ E + dᵢ F)` whose coefficients are sums of `k`
products of `n` ratios, each divided by `R ≥ 1`, occupies at most `closureConst K a m k n * L`
cells. -/
theorem generated_card_le (D : ClosureData h K L a E F ℛ) (m k n : ℕ) {R : ℝ} (hR : 1 ≤ R)
    (T S : Fin m → Fin k → Fin n → ℝ) (hT : ∀ i l j, T i l j ∈ ℛ) (hS : ∀ i l j, S i l j ∈ ℛ) :
    ((cells h (∑ i, ((∑ l, ∏ j, T i l j / R) • E + (∑ l, ∏ j, S i l j / R) • F))).card : ℝ) ≤
      closureConst K a m k n * L := by
  classical
  have hK := D.one_le_K
  have hL := D.L_pos
  have hKa := D.Kpow_pos a
  set Y := cells h (-E) with hYdef
  have hEpos := D.E_pos
  have hE_le_Y : ((cells h E).card : ℝ) ≤ 4 * Y.card := by
    have := card_cells_neg_le h (-E)
    rw [neg_neg] at this
    have h' : ((cells h E).card : ℝ) ≤ Y.card * 4 := by exact_mod_cast this
    linarith
  have hYlow : L / (4 * K ^ a) ≤ (Y.card : ℝ) := by
    have h1 := D.E_lower
    rw [div_le_iff₀ (by positivity)]
    calc L = L / K ^ a * K ^ a := by field_simp
      _ ≤ (cells h E).card * K ^ a := by gcongr
      _ ≤ 4 * Y.card * K ^ a := by gcongr
      _ = Y.card * (4 * K ^ a) := by ring
  have hYpos : 0 < (Y.card : ℝ) := lt_of_lt_of_le (by positivity) hYlow
  have hYne : Y.Nonempty := Finset.card_pos.mp (by exact_mod_cast hYpos)
  have hYup : (Y.card : ℝ) ≤ 4 * K ^ a * L := by
    have := card_cells_neg_le h E
    have h' : (Y.card : ℝ) ≤ (cells h E).card * 4 := by exact_mod_cast this
    nlinarith [D.E_upper]
  have hYY : ((Y - Y).card : ℝ) / Y.card ≤ 2 ^ 14 * K ^ (4 * a) := by
    have h1 := card_sub_cells_le h (-E) (-E)
    rw [neg_sub_neg] at h1
    have h1' : ((Y - Y).card : ℝ) ≤ (cells h (E - E)).card * 4 := by exact_mod_cast h1
    have h2 := D.EE
    rw [div_le_iff₀ hYpos]
    calc ((Y - Y).card : ℝ) ≤ 2 ^ 10 * K ^ (3 * a) * L * 4 := by nlinarith
      _ = 2 ^ 14 * K ^ (4 * a) * (L / (4 * K ^ a)) := by
          rw [show 4 * a = 3 * a + a by ring, pow_add]
          field_simp
          ring
      _ ≤ 2 ^ 14 * K ^ (4 * a) * Y.card := by gcongr
  have hBn := D.Bn_nonneg n
  set Λ := 16 * Bn K a n * K ^ a with hΛ
  have hcov : ∀ α ∈ (Finset.univ : Finset (Fin m × Fin k × Bool)),
      ((cells h (genDilates T S E F α) + Y).card : ℝ) ≤ Λ * Y.card := by
    intro α _
    have hN : ((cells h (genDilates T S E F α - E)).card : ℝ) ≤ Bn K a n * L := by
      obtain ⟨i, l, b⟩ := α
      cases b
      · exact D.prodF_le_Bn n (S i l) (hS i l)
      · exact D.prodE_le_Bn n (T i l) (hT i l)
    have h1 := card_add_cells_le h (genDilates T S E F α) (-E)
    rw [← sub_eq_add_neg] at h1
    have h1' : ((cells h (genDilates T S E F α) + Y).card : ℝ) ≤
        (cells h (genDilates T S E F α - E)).card * 4 := by exact_mod_cast h1
    have hL' : L ≤ 4 * K ^ a * Y.card := by
      have := hYlow
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    calc ((cells h (genDilates T S E F α) + Y).card : ℝ)
        ≤ (cells h (genDilates T S E F α - E)).card * 4 := h1'
      _ ≤ Bn K a n * L * 4 := by gcongr
      _ ≤ Bn K a n * (4 * K ^ a * Y.card) * 4 := by gcongr
      _ = Λ * Y.card := by rw [hΛ]; ring
  have hsum := card_cells_sum_le h hYne (genDilates T S E F) Finset.univ Λ hcov
  have hcard : (Finset.univ : Finset (Fin m × Fin k × Bool)).card = m * (k * 2) := by
    simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  rw [hcard] at hsum
  have hsub := generated_subset (R := R) T S E F
  have hRn : |R⁻¹ ^ n| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hR)
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; positivity
  calc ((cells h (∑ i, ((∑ l, ∏ j, T i l j / R) • E + (∑ l, ∏ j, S i l j / R) • F))).card : ℝ)
      ≤ (cells h ((R⁻¹ ^ n) • ∑ α, genDilates T S E F α)).card := by
        exact_mod_cast Finset.card_le_card (cells_mono hsub)
    _ ≤ (2 * |R⁻¹ ^ n| + 2) ^ 2 * (cells h (∑ α, genDilates T S E F α)).card :=
        card_cells_smul_le h _ _
    _ ≤ 16 * (Λ ^ (m * (k * 2)) * (((Y - Y).card : ℝ) / Y.card) ^ (2 * (m * (k * 2))) * Y.card *
          (((m * (k * 2) : ℕ) : ℝ) + 1) ^ 2) := by
        have h16 : (2 * |R⁻¹ ^ n| + 2) ^ 2 ≤ 16 := by nlinarith [abs_nonneg (R⁻¹ ^ n)]
        calc (2 * |R⁻¹ ^ n| + 2) ^ 2 * ((cells h (∑ α, genDilates T S E F α)).card : ℝ)
            ≤ 16 * (cells h (∑ α, genDilates T S E F α)).card := by gcongr
          _ ≤ _ := by gcongr
    _ ≤ 16 * (Λ ^ (m * (k * 2)) * (2 ^ 14 * K ^ (4 * a)) ^ (2 * (m * (k * 2))) *
          (4 * K ^ a * L) * (((m * (k * 2) : ℕ) : ℝ) + 1) ^ 2) := by
        gcongr
    _ = closureConst K a m k n * L := by
        rw [closureConst, hΛ]; ring

end ClosureData

end

end Submission.Obl.k4_retained_edge_planar_rigidity
