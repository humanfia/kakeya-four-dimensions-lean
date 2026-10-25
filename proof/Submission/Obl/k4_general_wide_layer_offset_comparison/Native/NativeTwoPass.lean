-- Adapted from this LOT tree, obligation o254, branch x0898, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/NativeTwoPass.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0864, commit abc1113588ce6b9e412a59326ea88392111ccb7e,
   Submission/Obl/k4_finite_projected_horizontal_candidates/NativeTwoPass.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.NativeMeshLow
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

/-!
# Native sheets of subpower radius: two passes

The first pass (`native_sheets_pass` at the crude cell cap `H₀`, a fixed power) gives native
sheets that are `(K H₀)^n`-Lipschitz on balls of radius `(K H₀)^(-n)`. On a much finer mesh
`δ₁` the native values of the points of one cell and one branch therefore lie within `65 K⁹ a`
of each other, so the native-bin caps (`B δ₁³` per cell and native bin of width `a`) bound the
cell mass of the retained law by `552 K⁹ B δ₁³` (`mass_le_bins`). The second pass at this
refined cap gives radius `≥ (K B)^(-n)` and bound `≤ (K B)^n`, subpower when `K` and `B` are.
-/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Metric Set MvPolynomial ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- Points of one set whose values on each branch differ by at most `D` occupy at most
`2 (2m+1)` bins of width `a`, `m = ⌈D/a⌉ + 1`. -/
theorem mass_le_bins {Ω : Type*} [MeasurableSpace Ω] (lam : Measure Ω) (G : Set Ω)
    (f : Ω → ℝ) (br : Ω → Bool) {a D : ℝ} (ha : 0 < a) (hD : 0 ≤ D)
    (hclose : ∀ ω ∈ G, ∀ ω' ∈ G, br ω = br ω' → |f ω - f ω'| ≤ D)
    (Bcap : ℝ≥0∞) (hcap : ∀ x₀ : ℤ, lam {ω | ⌊f ω / a⌋ = x₀} ≤ Bcap) :
    lam G ≤ ((2 * (2 * (⌈D / a⌉₊ + 1) + 1) : ℕ) : ℝ≥0∞) * Bcap := by
  classical
  set m : ℕ := ⌈D / a⌉₊ + 1 with hm
  let ref : Bool → Finset ℤ := fun s =>
    if h : ∃ ω, ω ∈ G ∧ br ω = s then
      Finset.Icc (⌊f h.choose / a⌋ - m) (⌊f h.choose / a⌋ + m) else ∅
  let X₀ : Finset ℤ := Finset.univ.biUnion ref
  have hcard : X₀.card ≤ 2 * (2 * m + 1) := by
    refine (Finset.card_biUnion_le).trans ?_
    have : ∀ s : Bool, (ref s).card ≤ 2 * m + 1 := by
      intro s
      simp only [ref]
      split_ifs
      · rw [Int.card_Icc]; omega
      · simp
    calc ∑ s : Bool, (ref s).card ≤ ∑ _s : Bool, (2 * m + 1) := Finset.sum_le_sum fun s _ => this s
      _ = 2 * (2 * m + 1) := by simp
  have hsub : G ⊆ ⋃ x₀ ∈ X₀, {ω | ⌊f ω / a⌋ = x₀} := by
    intro ω hω
    have h : ∃ ω', ω' ∈ G ∧ br ω' = br ω := ⟨ω, hω, rfl⟩
    obtain ⟨hG', hbr'⟩ := h.choose_spec
    have hd := hclose ω hω h.choose hG' hbr'.symm
    have hfl : |(⌊f ω / a⌋ : ℝ) - ⌊f h.choose / a⌋| < D / a + 1 := by
      have h1 := Int.floor_le (f ω / a)
      have h2 := Int.lt_floor_add_one (f ω / a)
      have h3 := Int.floor_le (f h.choose / a)
      have h4 := Int.lt_floor_add_one (f h.choose / a)
      have h5 : |f ω / a - f h.choose / a| ≤ D / a := by
        rw [← sub_div, abs_div, abs_of_pos ha]; exact div_le_div_of_nonneg_right hd ha.le
      rw [abs_lt]; rw [abs_le] at h5; constructor <;> linarith
    have hmD : D / a + 1 ≤ (m : ℝ) := by
      rw [hm]; push_cast; linarith [Nat.le_ceil (D / a)]
    have hint : |⌊f ω / a⌋ - ⌊f h.choose / a⌋| ≤ (m : ℤ) := by
      have : ((|⌊f ω / a⌋ - ⌊f h.choose / a⌋| : ℤ) : ℝ) < m := by
        push_cast; linarith
      exact_mod_cast this.le
    simp only [mem_iUnion, mem_setOf_eq, exists_prop]
    refine ⟨⌊f ω / a⌋, ?_, rfl⟩
    simp only [X₀, Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨br ω, ?_⟩
    simp only [ref, dif_pos h, Finset.mem_Icc]
    rw [abs_le] at hint
    constructor <;> linarith [hint.1, hint.2]
  calc lam G ≤ lam (⋃ x₀ ∈ X₀, {ω | ⌊f ω / a⌋ = x₀}) := measure_mono hsub
    _ ≤ ∑ x₀ ∈ X₀, lam {ω | ⌊f ω / a⌋ = x₀} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _x₀ ∈ X₀, Bcap := Finset.sum_le_sum fun x₀ _ => hcap x₀
    _ = (X₀.card : ℝ≥0∞) * Bcap := by simp
    _ ≤ ((2 * (2 * m + 1) : ℕ) : ℝ≥0∞) * Bcap := by gcongr

/-- Variation of a bounded holomorphic sheet between its center and a nearby real point. -/
theorem sheet_near_lip {g : EuclideanSpace ℂ (Fin 3) → ℂ} {c : EuclideanSpace ℝ (Fin 3)}
    {ρ V : ℝ} (hρ : 0 < ρ) (hd : DifferentiableOn ℂ g (ball (emb c) (4 * ρ)))
    (hb : ∀ z ∈ ball (emb c) (4 * ρ), ‖g z‖ ≤ V) (x : EuclideanSpace ℝ (Fin 3))
    (hx : ‖x - c‖ ≤ ρ) :
    ‖g (emb x) - g (emb c)‖ ≤ 4 * V / ρ * ‖x - c‖ := by
  set f : EuclideanSpace ℂ (Fin 3) → ℂ := fun v => g (emb c + (ρ : ℂ) • v) with hf
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hmem : ∀ v : EuclideanSpace ℂ (Fin 3), ‖v‖ < 4 → emb c + (ρ : ℂ) • v ∈ ball (emb c) (4 * ρ) := by
    intro v hv
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hρ]
    nlinarith
  have hfd : DifferentiableOn ℂ f (ball 0 4) := by
    intro v hv
    rw [mem_ball, dist_zero_right] at hv
    have h1 : DifferentiableAt ℂ (fun v : EuclideanSpace ℂ (Fin 3) => emb c + (ρ : ℂ) • v) v := by
      fun_prop
    exact ((hd.differentiableAt (isOpen_ball.mem_nhds (hmem v hv))).comp v h1).differentiableWithinAt
  have hfb : ∀ v : EuclideanSpace ℂ (Fin 3), ‖v‖ ≤ 2 → ‖f v‖ ≤ V := fun v hv =>
    hb _ (hmem v (by linarith))
  set y : EuclideanSpace ℂ (Fin 3) := (ρ⁻¹ : ℂ) • (emb x - emb c) with hy
  have hyn : ‖y‖ = ‖x - c‖ / ρ := by
    rw [hy, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, ← emb_sub,
      norm_emb]
    field_simp
  have hy1 : ‖y‖ ≤ 1 := by rw [hyn, div_le_one hρ]; exact hx
  have h := Submission.Obl.k4_algebraic_real_jet_comparison.holomorphic_inner_lipschitz hfd hfb
    (x := 0) (y := y) (by simp) hy1
  have hfy : f y = g (emb x) := by
    simp only [hf, hy, smul_smul, mul_inv_cancel₀ hρc, one_smul, add_sub_cancel]
  have hf0 : f 0 = g (emb c) := by simp [hf]
  rw [hfy, hf0, sub_zero, hyn] at h
  calc ‖g (emb x) - g (emb c)‖ ≤ 4 * V * (‖x - c‖ / ρ) := h
    _ = 4 * V / ρ * ‖x - c‖ := by ring

/-- Two points of one cell are close. -/
theorem norm_sub_le_of_cell {u v : Fin 3 → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (h : (fun i => ⌊u i / δ⌋) = fun i => ⌊v i / δ⌋) : ‖toEuc u - toEuc v‖ ≤ 2 * δ := by
  have hi : ∀ i, |u i - v i| ≤ 2 * δ / 2 := by
    intro i
    have := abs_sub_lt_of_floor_eq hδ (congrFun h i)
    linarith
  have := norm_toEuc_le (x := fun i => u i - v i) (s := 2 * δ) (by linarith) hi
  have heq : toEuc u - toEuc v = toEuc (fun i => u i - v i) := by
    ext i; simp [toEuc]
  rw [heq]; exact this

set_option maxHeartbeats 8000000 in
/-- **Native sheets of subpower radius.** -/
theorem native_sheets_two_pass :
    ∃ α β : ℕ, 1 ≤ β ∧ ∀ (A : ℕ) (K H₀ B a δ₀ δ₁ : ℝ), 2 ≤ K → 1 ≤ H₀ → 1 ≤ B → 0 < a → a ≤ 1 →
      0 < δ₀ → 0 < δ₁ → (K * H₀) ^ (α * A + β) * δ₀ ≤ 1 →
      (K * H₀) ^ (α * A + β) * δ₁ ≤ a → (K * B) ^ (α * A + β) * δ₁ ≤ 1 →
      ∀ (F S : MvPolynomial (Fin 4) ℝ), F.totalDegree ≤ 2 → S.totalDegree ≤ 2 →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (lam : Measure Ω), IsProbabilityMeasure lam →
      ∀ (u : Ω → Fin 3 → ℝ) (w : Ω → ℝ), Measurable u → Measurable w →
      (∀ q : Fin 3 → ℤ, lam {ω | (fun i => ⌊u ω i / δ₀⌋) = q} ≤ ENNReal.ofReal (H₀ * δ₀ ^ 3)) →
      (∀ (q : Fin 3 → ℤ) (x₀ : ℤ), lam {ω | (fun i => ⌊u ω i / δ₁⌋) = q ∧
          ⌊eval (Fin.snoc (u ω) (w ω)) S / a⌋ = x₀} ≤ ENNReal.ofReal (B * δ₁ ^ 3)) →
      (∀ᵐ ω ∂lam, NChart K a F S (u ω) (w ω)) →
      ∃ (ρ : ℝ) (R : MvPolynomial (Fin 4) ℂ) (g : Bool → EuclideanSpace ℂ (Fin 3) → ℂ)
        (E : Set Ω),
        ((K * B) ^ (α * A + β))⁻¹ ≤ ρ ∧ ρ ≤ 1 ∧ R ≠ 0 ∧ R.totalDegree ≤ 4 ∧ MeasurableSet E ∧
        lam E ≤ ENNReal.ofReal (((K * H₀) ^ A)⁻¹ + ((K * B) ^ A)⁻¹) ∧
        ∀ᵐ ω ∂lam, ω ∉ E →
          SheetOn R (g (branch F (u ω) (w ω))) (toEuc (u ω)) (4 * ρ)
            ((K * B) ^ (α * A + β)) ∧
          |eval (Fin.snoc (u ω) (w ω)) S -
            (g (branch F (u ω) (w ω)) (emb (toEuc (u ω)))).re| ≤ 32 * K ^ 9 * a := by
  obtain ⟨αp, βp, hβp, hpass₀⟩ := native_sheets_pass
  refine ⟨20 * αp, 20 * αp + 20 * βp + 3, by omega, ?_⟩
  intro A K H₀ B a δ₀ δ₁ hK hH₀ hB ha ha1 hδ₀ hδ₁ hm₀ hm₁ hm₂ F S hF hS Ω _ lam hprob u w hu hw
    hcap₀ hcapS hgood
  obtain ⟨np, hnp_def⟩ : ∃ np : ℕ, np = αp * (A + 1) + βp := ⟨_, rfl⟩
  have hnp : 1 ≤ np := by rw [hnp_def]; exact hβp.trans (Nat.le_add_left _ _)
  have hpass := hpass₀ (A + 1)
  rw [← hnp_def] at hpass
  have hn_eq : 20 * αp * A + (20 * αp + 20 * βp + 3) = 20 * np + 3 := by rw [hnp_def]; ring
  rw [hn_eq] at hm₀ hm₁ hm₂ ⊢
  clear hn_eq hpass₀
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  obtain ⟨X, hXdef⟩ : ∃ X, X = K * H₀ := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = K * B := ⟨_, rfl⟩
  have hX2 : 2 ≤ X := by rw [hXdef]; nlinarith
  have hY2 : 2 ≤ Y := by rw [hYdef]; nlinarith
  have hX1 : 1 ≤ X := by linarith
  have hY1 : 1 ≤ Y := by linarith
  rw [← hXdef] at hm₀ hm₁
  rw [← hYdef] at hm₂
  -- first pass
  have hm0' : (K * H₀) ^ np * δ₀ ≤ 1 := by
    rw [← hXdef]
    exact le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hX1 (by omega)) hδ₀.le) hm₀
  obtain ⟨ρ₀, R₀, g₀, E₀, hρ₀, hρ₀1, -, -, hE₀m, hE₀, hae₀⟩ :=
    hpass K H₀ a δ₀ hK hH₀ ha ha1 hδ₀ hm0' F S hF hS Ω lam hprob u w hu hcap₀ hgood
  rw [← hXdef] at hρ₀ hE₀ hae₀
  have hρ₀pos : 0 < ρ₀ := lt_of_lt_of_le (by positivity) hρ₀
  -- a measurable good set
  obtain ⟨T, hTae, hTm, hT⟩ := (hgood.and hae₀).exists_measurable_mem
  have hTc : lam Tᶜ = 0 := hTae
  set G := T ∩ E₀ᶜ with hGdef
  have hGm : MeasurableSet G := hTm.inter hE₀m.compl
  have hGc : lam Gᶜ ≤ ENNReal.ofReal ((X ^ (A + 1))⁻¹) := by
    have hsub : Gᶜ ⊆ Tᶜ ∪ E₀ := by
      intro ω hω
      rw [hGdef, compl_inter, compl_compl] at hω; exact hω
    calc lam Gᶜ ≤ lam (Tᶜ ∪ E₀) := measure_mono hsub
      _ ≤ lam Tᶜ + lam E₀ := measure_union_le _ _
      _ = lam E₀ := by rw [hTc, zero_add]
      _ ≤ _ := hE₀
  have hhalf : ENNReal.ofReal ((X ^ (A + 1))⁻¹) ≤ 2⁻¹ := by
    have h1 : (X ^ (A + 1))⁻¹ ≤ 2⁻¹ := by
      apply inv_anti₀ (by norm_num)
      calc (2 : ℝ) ≤ X := hX2
        _ = X ^ 1 := (pow_one X).symm
        _ ≤ X ^ (A + 1) := pow_le_pow_right₀ hX1 (by omega)
    calc ENNReal.ofReal ((X ^ (A + 1))⁻¹) ≤ ENNReal.ofReal 2⁻¹ := ENNReal.ofReal_le_ofReal h1
      _ = 2⁻¹ := by rw [ENNReal.ofReal_inv_of_pos (by norm_num)]; simp
  have hGhalf : 2⁻¹ ≤ lam G := by
    by_contra hlt
    rw [not_le] at hlt
    have hsum := measure_add_measure_compl hGm (μ := lam)
    rw [measure_univ] at hsum
    have : lam G + lam Gᶜ < 2⁻¹ + 2⁻¹ := ENNReal.add_lt_add_of_lt_of_le (by simp) hlt (hGc.trans hhalf)
    rw [hsum, ENNReal.inv_two_add_inv_two] at this
    exact lt_irrefl _ this
  have hG0 : lam G ≠ 0 := by
    intro h; rw [h] at hGhalf; exact absurd hGhalf (by simp)
  have hGtop : lam G ≠ ⊤ := measure_ne_top lam G
  have hinvG : (lam G)⁻¹ ≤ 2 := by
    rw [ENNReal.inv_le_iff_inv_le]; exact hGhalf
  -- points of `G`
  have hGpt : ∀ ω ∈ G, NChart K a F S (u ω) (w ω) ∧
      SheetOn R₀ (g₀ (branch F (u ω) (w ω))) (toEuc (u ω)) (4 * ρ₀) (X ^ np) ∧
      |eval (Fin.snoc (u ω) (w ω)) S - (g₀ (branch F (u ω) (w ω)) (emb (toEuc (u ω)))).re| ≤
        32 * K ^ 9 * a := by
    intro ω hω
    obtain ⟨h1, h2⟩ := hT ω hω.1
    exact ⟨h1, h2 hω.2⟩
  -- the fine mesh resolves the first-pass sheets
  have hδρ : 2 * δ₁ ≤ ρ₀ := by
    have h1 : X ^ (20 * np + 3) * δ₁ ≤ 1 := hm₁.trans ha1
    have h2 : 2 * X ^ np ≤ X ^ (20 * np + 3) := by
      calc 2 * X ^ np ≤ X * X ^ np := mul_le_mul_of_nonneg_right hX2 (by positivity)
        _ = X ^ (np + 1) := by ring
        _ ≤ X ^ (20 * np + 3) := pow_le_pow_right₀ hX1 (by omega)
    have h3 : 2 * δ₁ ≤ (X ^ np)⁻¹ := by
      rw [← one_div, le_div_iff₀ (by positivity)]
      calc 2 * δ₁ * X ^ np = δ₁ * (2 * X ^ np) := by ring
        _ ≤ δ₁ * X ^ (20 * np + 3) := mul_le_mul_of_nonneg_left h2 hδ₁.le
        _ = X ^ (20 * np + 3) * δ₁ := by ring
        _ ≤ 1 := h1
    exact h3.trans hρ₀
  have hlipδ : 4 * X ^ np / ρ₀ * (2 * δ₁) ≤ a := by
    have h1 : 4 * X ^ np / ρ₀ ≤ 4 * X ^ np * X ^ np := by
      rw [div_le_iff₀ hρ₀pos]
      have : 1 ≤ X ^ np * ρ₀ := by
        have h := mul_le_mul_of_nonneg_left hρ₀ (by positivity : (0 : ℝ) ≤ X ^ np)
        rwa [mul_inv_cancel₀ (by positivity)] at h
      nlinarith [pow_pos (by linarith : (0 : ℝ) < X) np]
    have h2 : 8 * X ^ np * X ^ np ≤ X ^ (20 * np + 3) := by
      calc 8 * X ^ np * X ^ np ≤ X ^ 3 * X ^ np * X ^ np := by
            gcongr; nlinarith [pow_le_pow_left₀ (by norm_num) hX2 3]
        _ = X ^ (2 * np + 3) := by ring
        _ ≤ X ^ (20 * np + 3) := pow_le_pow_right₀ hX1 (by omega)
    calc 4 * X ^ np / ρ₀ * (2 * δ₁) ≤ 4 * X ^ np * X ^ np * (2 * δ₁) := by gcongr
      _ = 8 * X ^ np * X ^ np * δ₁ := by ring
      _ ≤ X ^ (20 * np + 3) * δ₁ := by gcongr
      _ ≤ a := hm₁
  have hclose : ∀ (q : Fin 3 → ℤ), ∀ ω ∈ G ∩ {ω | (fun i => ⌊u ω i / δ₁⌋) = q},
      ∀ ω' ∈ G ∩ {ω | (fun i => ⌊u ω i / δ₁⌋) = q},
      branch F (u ω) (w ω) = branch F (u ω') (w ω') →
      |eval (Fin.snoc (u ω) (w ω)) S - eval (Fin.snoc (u ω') (w ω')) S| ≤ 65 * K ^ 9 * a := by
    intro q ω hω ω' hω' hbr
    obtain ⟨-, ⟨hd₀, -, hb₀, -⟩, he⟩ := hGpt ω hω.1
    obtain ⟨-, -, he'⟩ := hGpt ω' hω'.1
    rw [← hbr] at he'
    have hcell : (fun i => ⌊u ω' i / δ₁⌋) = fun i => ⌊u ω i / δ₁⌋ := by
      rw [show (fun i => ⌊u ω' i / δ₁⌋) = q from hω'.2, show (fun i => ⌊u ω i / δ₁⌋) = q from hω.2]
    have hnear := norm_sub_le_of_cell hδ₁ hcell
    have hlip := sheet_near_lip hρ₀pos hd₀ hb₀ (toEuc (u ω')) (hnear.trans hδρ)
    have hlip' : ‖g₀ (branch F (u ω) (w ω)) (emb (toEuc (u ω'))) -
        g₀ (branch F (u ω) (w ω)) (emb (toEuc (u ω)))‖ ≤ a :=
      hlip.trans ((mul_le_mul_of_nonneg_left hnear (by positivity)).trans hlipδ)
    have hre := Complex.abs_re_le_norm (g₀ (branch F (u ω) (w ω)) (emb (toEuc (u ω'))) -
      g₀ (branch F (u ω) (w ω)) (emb (toEuc (u ω))))
    rw [Complex.sub_re] at hre
    have hK9 : a ≤ K ^ 9 * a := by
      have : (1 : ℝ) ≤ K ^ 9 := one_le_pow₀ hK1
      nlinarith
    calc |eval (Fin.snoc (u ω) (w ω)) S - eval (Fin.snoc (u ω') (w ω')) S|
        ≤ |eval (Fin.snoc (u ω) (w ω)) S - (g₀ (branch F (u ω) (w ω)) (emb (toEuc (u ω)))).re| +
          |(g₀ (branch F (u ω) (w ω)) (emb (toEuc (u ω')))).re -
            (g₀ (branch F (u ω) (w ω)) (emb (toEuc (u ω)))).re| +
          |eval (Fin.snoc (u ω') (w ω')) S -
            (g₀ (branch F (u ω) (w ω)) (emb (toEuc (u ω')))).re| := by
          set A₁ := eval (Fin.snoc (u ω) (w ω)) S
          set B₁ := (g₀ (branch F (u ω) (w ω)) (emb (toEuc (u ω)))).re
          set D₁ := (g₀ (branch F (u ω) (w ω)) (emb (toEuc (u ω')))).re
          set C₁ := eval (Fin.snoc (u ω') (w ω')) S
          have t1 := abs_sub_le A₁ B₁ C₁
          have t2 := abs_sub_le B₁ D₁ C₁
          have t3 : |B₁ - D₁| = |D₁ - B₁| := abs_sub_comm B₁ D₁
          have t4 : |D₁ - C₁| = |C₁ - D₁| := abs_sub_comm D₁ C₁
          linarith
      _ ≤ 32 * K ^ 9 * a + a + 32 * K ^ 9 * a := by
          gcongr
          · exact hre.trans hlip'
      _ ≤ 65 * K ^ 9 * a := by linarith
  -- the refined caps
  set H₁ : ℝ := 540 * K ^ 9 * B with hH₁
  have hH₁1 : 1 ≤ H₁ := by
    rw [hH₁]
    have : (1 : ℝ) ≤ K ^ 9 := one_le_pow₀ hK1
    nlinarith
  have hcell_meas : ∀ q : Fin 3 → ℤ, MeasurableSet {ω | (fun i => ⌊u ω i / δ₁⌋) = q} := by
    intro q
    exact measurableSet_eq_fun (by fun_prop) measurable_const
  have hSmeas : Measurable fun ω => eval (Fin.snoc (u ω) (w ω)) S := by
    have h1 : Measurable fun ω => (Fin.snoc (u ω) (w ω) : Fin 4 → ℝ) := by
      rw [measurable_pi_iff]
      intro i
      induction i using Fin.lastCases with
      | last =>
        have : (fun ω => (Fin.snoc (u ω) (w ω) : Fin 4 → ℝ) (Fin.last 3)) = w := by
          funext ω; exact Fin.snoc_last _ _
        rw [this]; exact hw
      | cast j =>
        have : (fun ω => (Fin.snoc (u ω) (w ω) : Fin 4 → ℝ) (Fin.castSucc j)) = fun ω => u ω j := by
          funext ω; exact Fin.snoc_castSucc _ _ _
        rw [this]; exact (measurable_pi_apply j).comp hu
    exact (MvPolynomial.continuous_eval S).measurable.comp h1
  have hGcap : ∀ q : Fin 3 → ℤ, lam (G ∩ {ω | (fun i => ⌊u ω i / δ₁⌋) = q}) ≤
      ENNReal.ofReal (270 * K ^ 9 * B * δ₁ ^ 3) := by
    intro q
    set C := {ω | (fun i => ⌊u ω i / δ₁⌋) = q} with hC
    have hb := mass_le_bins (lam.restrict C) (G ∩ C)
      (fun ω => eval (Fin.snoc (u ω) (w ω)) S) (fun ω => branch F (u ω) (w ω)) ha
      (by positivity : (0 : ℝ) ≤ 65 * K ^ 9 * a) (hclose q) (ENNReal.ofReal (B * δ₁ ^ 3)) (by
        intro x₀
        rw [Measure.restrict_apply' (hcell_meas q)]
        refine le_trans (measure_mono ?_) (hcapS q x₀)
        intro ω hω
        exact ⟨hω.2, hω.1⟩)
    rw [Measure.restrict_apply' (hcell_meas q), inter_assoc, inter_self] at hb
    refine hb.trans ?_
    have hceil : ((⌈65 * K ^ 9 * a / a⌉₊ : ℕ) : ℝ) ≤ 65 * K ^ 9 + 1 := by
      rw [show 65 * K ^ 9 * a / a = 65 * K ^ 9 by field_simp]
      exact (Nat.ceil_lt_add_one (by positivity)).le
    have hN : ((2 * (2 * (⌈65 * K ^ 9 * a / a⌉₊ + 1) + 1) : ℕ) : ℝ) ≤ 270 * K ^ 9 := by
      push_cast
      have : (1 : ℝ) ≤ K ^ 9 := one_le_pow₀ hK1
      nlinarith
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc ((2 * (2 * (⌈65 * K ^ 9 * a / a⌉₊ + 1) + 1) : ℕ) : ℝ) * (B * δ₁ ^ 3)
        ≤ 270 * K ^ 9 * (B * δ₁ ^ 3) := by gcongr
      _ = 270 * K ^ 9 * B * δ₁ ^ 3 := by ring
  -- the conditioned law
  set lam₁ := cond lam G with hlam₁
  haveI : IsProbabilityMeasure lam₁ := cond_isProbabilityMeasure_of_finite hG0 hGtop
  have hcap₁ : ∀ q : Fin 3 → ℤ, lam₁ {ω | (fun i => ⌊u ω i / δ₁⌋) = q} ≤
      ENNReal.ofReal (H₁ * δ₁ ^ 3) := by
    intro q
    rw [hlam₁, cond_apply hGm]
    calc (lam G)⁻¹ * lam (G ∩ {ω | (fun i => ⌊u ω i / δ₁⌋) = q})
        ≤ 2 * ENNReal.ofReal (270 * K ^ 9 * B * δ₁ ^ 3) := by gcongr; exact hGcap q
      _ = ENNReal.ofReal (H₁ * δ₁ ^ 3) := by
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num), hH₁]
          ring_nf
  have hgood₁ : ∀ᵐ ω ∂lam₁, NChart K a F S (u ω) (w ω) := cond_absolutelyContinuous.ae_le hgood
  -- second pass
  have hKH₁ : K * H₁ ≤ Y ^ 20 := by
    rw [hH₁, hYdef]
    have h540 : (540 : ℝ) ≤ K ^ 10 := by
      have : (2 : ℝ) ^ 10 ≤ K ^ 10 := pow_le_pow_left₀ (by norm_num) hK 10
      norm_num at this ⊢; linarith
    have hB20 : B ≤ B ^ 20 := le_self_pow₀ hB (by norm_num)
    calc K * (540 * K ^ 9 * B) = 540 * K ^ 10 * B := by ring
      _ ≤ K ^ 10 * K ^ 10 * B ^ 20 := by gcongr
      _ = (K * B) ^ 20 := by ring
  have hKH₁1 : 1 ≤ K * H₁ := by nlinarith
  have hYKH₁ : Y ≤ K * H₁ := by
    rw [hYdef, hH₁]
    have : (1 : ℝ) ≤ 540 * K ^ 9 := by
      have : (1 : ℝ) ≤ K ^ 9 := one_le_pow₀ hK1
      linarith
    nlinarith
  have hm₁' : (K * H₁) ^ np * δ₁ ≤ 1 := by
    have h1 : (K * H₁) ^ np ≤ Y ^ (20 * np + 3) := by
      calc (K * H₁) ^ np ≤ (Y ^ 20) ^ np := pow_le_pow_left₀ (by linarith) hKH₁ np
        _ = Y ^ (20 * np) := by rw [← pow_mul]
        _ ≤ Y ^ (20 * np + 3) := pow_le_pow_right₀ hY1 (by omega)
    exact le_trans (mul_le_mul_of_nonneg_right h1 hδ₁.le) hm₂
  obtain ⟨ρ₁, R₁, g₁, E₁, hρ₁, hρ₁1, hR₁, hR₁d, hE₁m, hE₁, hae₁⟩ :=
    hpass K H₁ a δ₁ hK hH₁1 ha ha1 hδ₁ hm₁' F S hF hS Ω lam₁ inferInstance u w hu hcap₁ hgood₁
  have hpowY : (K * H₁) ^ np ≤ Y ^ (20 * np + 3) := by
    calc (K * H₁) ^ np ≤ (Y ^ 20) ^ np := pow_le_pow_left₀ (by linarith) hKH₁ np
      _ = Y ^ (20 * np) := by rw [← pow_mul]
      _ ≤ Y ^ (20 * np + 3) := pow_le_pow_right₀ hY1 (by omega)
  -- transfer from the conditioned law
  have htrans : ∀ {P : Ω → Prop}, (∀ᵐ ω ∂lam₁, P ω) → ∀ᵐ ω ∂lam, ω ∈ G → P ω := by
    intro P h
    have habs : lam.restrict G ≪ lam₁ := by
      rw [hlam₁]
      exact Measure.absolutelyContinuous_smul (ENNReal.inv_ne_zero.mpr hGtop)
    exact (ae_restrict_iff' hGm).mp (habs.ae_le h)
  refine ⟨ρ₁, R₁, g₁, Gᶜ ∪ E₁, ?_, hρ₁1, hR₁, hR₁d, hGm.compl.union hE₁m, ?_, ?_⟩
  · rw [← hYdef]
    refine le_trans ?_ hρ₁
    exact inv_anti₀ (by positivity) hpowY
  · rw [← hXdef, ← hYdef]
    have hGE : lam (G ∩ E₁) ≤ ENNReal.ofReal ((Y ^ A)⁻¹) := by
      have h1 : lam₁ E₁ = (lam G)⁻¹ * lam (G ∩ E₁) := cond_apply hGm lam E₁
      have h2 : lam (G ∩ E₁) = lam G * lam₁ E₁ := by
        rw [h1, ← mul_assoc, ENNReal.mul_inv_cancel hG0 hGtop, one_mul]
      have h3 : lam G ≤ 1 := prob_le_one
      have h4 : ((K * H₁) ^ (A + 1))⁻¹ ≤ (Y ^ A)⁻¹ := by
        apply inv_anti₀ (by positivity)
        calc Y ^ A ≤ (K * H₁) ^ A := pow_le_pow_left₀ (by linarith) hYKH₁ A
          _ ≤ (K * H₁) ^ (A + 1) := pow_le_pow_right₀ hKH₁1 (by omega)
      calc lam (G ∩ E₁) = lam G * lam₁ E₁ := h2
        _ ≤ 1 * lam₁ E₁ := by gcongr
        _ = lam₁ E₁ := one_mul _
        _ ≤ ENNReal.ofReal (((K * H₁) ^ (A + 1))⁻¹) := hE₁
        _ ≤ ENNReal.ofReal ((Y ^ A)⁻¹) := ENNReal.ofReal_le_ofReal h4
    have hX : ((X ^ (A + 1))⁻¹) ≤ (X ^ A)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ hX1 (by omega))
    have hsub : Gᶜ ∪ E₁ ⊆ Gᶜ ∪ (G ∩ E₁) := by
      intro ω hω
      by_cases hωG : ω ∈ G
      · rcases hω with h | h
        · exact absurd hωG h
        · exact Or.inr ⟨hωG, h⟩
      · exact Or.inl hωG
    calc lam (Gᶜ ∪ E₁) ≤ lam (Gᶜ ∪ (G ∩ E₁)) := measure_mono hsub
      _ ≤ lam Gᶜ + lam (G ∩ E₁) := measure_union_le _ _
      _ ≤ ENNReal.ofReal ((X ^ (A + 1))⁻¹) + ENNReal.ofReal ((Y ^ A)⁻¹) := add_le_add hGc hGE
      _ ≤ ENNReal.ofReal ((X ^ A)⁻¹) + ENNReal.ofReal ((Y ^ A)⁻¹) := by
          gcongr
      _ = ENNReal.ofReal ((X ^ A)⁻¹ + (Y ^ A)⁻¹) :=
          (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  · rw [← hYdef]
    filter_upwards [htrans hae₁] with ω hω hωE
    rw [Set.mem_union, not_or, Set.mem_compl_iff, not_not] at hωE
    obtain ⟨hs, he⟩ := hω hωE.1 hωE.2
    exact ⟨hs.mono hpowY, he⟩

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
