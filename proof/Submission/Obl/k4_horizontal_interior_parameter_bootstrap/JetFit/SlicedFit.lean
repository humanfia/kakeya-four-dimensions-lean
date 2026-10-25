import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit.SlicedPlanar

/-!
Moved from o217 (branch x0763, same author, session x0763 = x0931), namespace changed.
# The sliced fit

`sliced_fit` is paper Proposition 5.4, "Fitting one row component", for the sliced model
(`SlicedData`, `SlicedHyp`): with the starting time, heavy starting bin, light time bins,
quadrant and occupied cells, the planar input puts the time graph near a line; the line is a
graph over time of slope at most `6K+1`, and translating back gives `φ` within `(12K+2) p` of
an affine function on a set of active times of measure at least `p^ε/(5 C₀ K₁)`
(paper: "We therefore obtain at least `p^{ε-1}/K` time bins near one line in the graph of
`φ₁` ... `|T_I| ≥ H p^ε/K`").

The explicit smallness hypotheses on `K` (powers of `δ = p/(8K)`) hold for subpower `K` and small
`p`; their asymptotic packaging is done where the sliced fit is applied.
-/

open MeasureTheory Set Metric

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

variable {Ω : Type*} [MeasurableSpace Ω]

theorem actSet_sub {D : SlicedData Ω} {p K d : ℝ} (H : SlicedHyp D p K d) {u : ℝ}
    (hu : u ∈ actSet D) : u ∈ Icc (0:ℝ) 1 := by
  have hne : D.ν {l | (l, u) ∈ D.E} ≠ 0 := (hu : 0 < D.ν {l | (l, u) ∈ D.E}).ne'
  obtain ⟨l, hl⟩ := nonempty_of_measure_ne_zero hne
  exact H.E01 _ hl

/-- The time graph of the representatives is slack-Lipschitz. -/
theorem timeGraph_lip {D : SlicedData Ω} {p K d : ℝ} (H : SlicedHyp D p K d) (hp : 0 < p)
    (hK : 1 ≤ K) {u₀ s₁ s₂ : ℝ} (hs₁ : s₁ = 1 ∨ s₁ = -1) (hs₂ : s₂ = 1 ∨ s₂ = -1)
    (U : Set ℝ) (hU : U ⊆ Icc (0:ℝ) 1) :
    ∀ τ ∈ {τ : ℝ | ∃ u ∈ U, τ = 1 / (4 * K) * s₁ * (u - u₀)},
    ∀ τ' ∈ {τ : ℝ | ∃ u ∈ U, τ = 1 / (4 * K) * s₁ * (u - u₀)},
      |1 / (4 * K) * s₂ * (D.φ u₀ - D.φ (u₀ + s₁ * τ / (1 / (4 * K)))) -
        1 / (4 * K) * s₂ * (D.φ u₀ - D.φ (u₀ + s₁ * τ' / (1 / (4 * K))))| ≤
      2 * K * (|τ - τ'| + p / (8 * K)) := by
  have hK0 : 0 < K := by linarith
  set lam : ℝ := 1 / (4 * K) with hlam
  have hlam0 : 0 < lam := by positivity
  have hback : ∀ u : ℝ, u₀ + s₁ * (lam * s₁ * (u - u₀)) / lam = u := by
    intro u; rcases hs₁ with h | h <;> subst h <;> field_simp <;> ring
  have hδlam : 2 * (p / (8 * K)) = lam * p := by rw [hlam]; field_simp; ring
  rintro τ ⟨u, hu, rfl⟩ τ' ⟨u', hu', rfl⟩
  rw [hback, hback]
  have e1 : lam * s₂ * (D.φ u₀ - D.φ u) - lam * s₂ * (D.φ u₀ - D.φ u') =
      lam * s₂ * (D.φ u' - D.φ u) := by ring
  have e2 : lam * s₁ * (u - u₀) - lam * s₁ * (u' - u₀) = lam * s₁ * (u - u') := by ring
  rw [e1, e2, abs_mul, abs_mul, abs_mul, abs_mul, abs_sign hs₁, abs_sign hs₂, abs_of_pos hlam0]
  simp only [mul_one]
  have hφ := H.φlip _ (hU hu') _ (hU hu)
  rw [abs_sub_comm u'] at hφ
  calc lam * |D.φ u' - D.φ u| ≤ lam * (K * (|u - u'| + p)) := mul_le_mul_of_nonneg_left hφ hlam0.le
    _ = K * (lam * |u - u'|) + K * (lam * p) := by ring
    _ = K * (lam * |u - u'|) + K * (2 * (p / (8 * K))) := by rw [hδlam]
    _ ≤ 2 * K * (lam * |u - u'| + p / (8 * K)) := by
        have : 0 ≤ K * (lam * |u - u'|) := by positivity
        nlinarith

set_option maxHeartbeats 2000000 in
/-- **The sliced fit** (paper Proposition 5.4, "Fitting one row component"): for the sliced
model at scale `p`, the row `φ` is within `(12K+2) p` of an affine function of slope at most
`6K+1` on a set of active times of measure at least `p^ε / (5 C₀ K₁)`. -/
theorem sliced_fit {ε d : ℝ} (hε : 0 < ε) (hd : 0 ≤ d) (hd1 : d < 1) (hεd : ε + d < 1) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧ ∀ (p K : ℝ), 0 < p → p ≤ 1 → 1 ≤ K → p / (8 * K) ≤ δ₀ →
      5 * (8 * K + 5) ≤ (p / (8 * K)) ^ (-η) →
      3 * (4 * K) ^ 2 * (4 * K + 2) < (p / (8 * K)) ^ (-η * (1 - ε - d)) →
      27 * 179712 * K ^ 16 * p ^ 3 * (p / (8 * K)) ^ (η - 3) ≤ 1 →
      10 * ((4 * (2 * K) + 5) * (8 * (2 * K) + 9)) * (p / (8 * K)) ≤ (p / (8 * K)) ^ ε →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (D : SlicedData Ω), SlicedHyp D p K d →
      ∃ σ c : ℝ, |σ| ≤ 6 * K + 1 ∧ ∃ T : Set ℝ, MeasurableSet T ∧ T ⊆ actSet D ∧
        ENNReal.ofReal (p ^ ε / (5 * ((4 * (2 * K) + 5) * (8 * (2 * K) + 9)) * (36864 * K ^ 16)))
          ≤ volume T ∧
        ∀ u ∈ T, |D.φ u - (c + σ * u)| ≤ (12 * K + 2) * p := by
  obtain ⟨η, δ₀, hη, hδ₀, hSNL⟩ := sliced_nearLine hε hd hεd
  refine ⟨η, δ₀, hη, hδ₀, ?_⟩
  intro p K hp hp1 hK hδδ₀ hA hB hDc hC Ω _ D H
  have hK0 : 0 < K := by linarith
  set lam : ℝ := 1 / (4 * K) with hlam
  have hlam0 : 0 < lam := by positivity
  set δ : ℝ := p / (8 * K) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδlam : 2 * δ = lam * p := by rw [hδ, hlam]; field_simp; ring
  have hδp : δ ≤ p := by rw [hδ, div_le_iff₀ (by positivity)]; nlinarith
  set K₁ : ℝ := 36864 * K ^ 16 with hK₁
  have hK₁0 : 0 < K₁ := by positivity
  set C₀ : ℝ := (4 * (2 * K) + 5) * (8 * (2 * K) + 9) with hC₀
  have hC₀0 : 0 < C₀ := by positivity
  obtain ⟨u₀, hu₀, hmass⟩ := exists_start_time H hK
  obtain ⟨β₀, s₁, s₂, hs₁, hs₂, Occ, hOcc, hne⟩ :=
    many_occupied_cells H hp hp1 hK hd hd1.le hu₀ hmass
  have hOccpos : 0 < Occ.card := by
    by_contra h0; push Not at h0
    have : Occ.card = 0 := Nat.le_zero.1 h0
    rw [this] at hOcc; simp at hOcc; linarith
  obtain ⟨c₀, hc₀⟩ := Finset.card_pos.1 hOccpos
  obtain ⟨x₀, -⟩ := hne c₀ hc₀
  haveI : Nonempty ((Ω × Ω) × ℝ) := ⟨x₀⟩
  choose! xpt hxpt using hne
  have hNL := hSNL p K hp hp1 hK hδδ₀ hA hB hDc D H u₀ s₁ s₂ β₀ K₁ Occ xpt hu₀ hs₁ hs₂ hOcc hxpt
  set g : ℝ → ℝ := fun τ => lam * s₂ * (D.φ u₀ - D.φ (u₀ + s₁ * τ / lam)) with hg
  set Tτ : Set ℝ := {τ : ℝ | ∃ c ∈ Occ, τ = lam * s₁ * ((xpt c).2 - u₀)} with hTτ
  have hu01 : ∀ c ∈ Occ, (xpt c).2 ∈ Icc (0:ℝ) 1 := fun c hc =>
    H.E01 _ (hxpt c hc).1.1.1.1.1.1
  have hquad : ∀ c ∈ Occ, 0 ≤ s₁ * ((xpt c).2 - u₀) ∧ 0 ≤ s₂ * (D.φ u₀ - D.φ (xpt c).2) :=
    fun c hc => (hxpt c hc).1.2
  have hgood : ∀ c ∈ Occ, ⌊(xpt c).2 / p⌋ ∈ goodIdx D p K₁ := fun c hc => (hxpt c hc).1.1.2
  have hT01 : ∀ τ ∈ Tτ, 0 ≤ τ ∧ τ ≤ 1 := by
    rintro τ ⟨c, hc, rfl⟩
    have h1 := (hquad c hc).1
    have hu := hu01 c hc
    have hb : s₁ * ((xpt c).2 - u₀) ≤ 1 := by
      rcases hs₁ with h | h <;> subst h <;> linarith [hu.1, hu.2, hu₀.1, hu₀.2]
    have hlam1 : lam ≤ 1 := by rw [hlam, div_le_one (by positivity)]; linarith
    constructor
    · rw [mul_assoc]; positivity
    · calc lam * s₁ * ((xpt c).2 - u₀) = lam * (s₁ * ((xpt c).2 - u₀)) := by ring
        _ ≤ 1 * 1 := mul_le_mul hlam1 hb h1 zero_le_one
        _ = 1 := by ring
  have hgLip : ∀ τ ∈ Tτ, ∀ τ' ∈ Tτ, |g τ - g τ'| ≤ 2 * K * (|τ - τ'| + δ) := by
    rintro τ ⟨c, hc, rfl⟩ τ' ⟨c', hc', rfl⟩
    exact timeGraph_lip H hp hK hs₁ hs₂ {u | ∃ c ∈ Occ, (xpt c).2 = u}
      (by rintro u ⟨c, hc, rfl⟩; exact hu01 c hc) _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩ _ ⟨_, ⟨c', hc', rfl⟩, rfl⟩
  obtain ⟨σ', c', hσ', J, hJ, hJpt⟩ := affine_of_nearLine (T := Tτ) (g := g) (K := 2 * K)
    (δ := δ) (ε := ε) (by linarith) hδ0 hT01 hgLip hC hNL
  choose! τJ hτJ using hJpt
  have hτJ' : ∀ j ∈ J, ∃ c ∈ Occ, τJ j = lam * s₁ * ((xpt c).2 - u₀) := fun j hj => (hτJ j hj).1
  choose! cJ hcJ using hτJ'
  set uJ : ℕ → ℝ := fun j => (xpt (cJ j)).2 with huJ
  set I : Finset ℤ := J.image (fun j => ⌊uJ j / p⌋) with hI
  set T : Set ℝ := ⋃ i ∈ I, actSet D ∩ {u | ⌊u / p⌋ = i} with hT
  refine ⟨-(s₁ * s₂ * σ'), D.φ u₀ - s₂ * c' / lam + s₁ * s₂ * σ' * u₀, ?_, T, ?_, ?_, ?_, ?_⟩
  · rw [abs_neg, abs_mul, abs_mul, abs_sign hs₁, abs_sign hs₂]; linarith
  · exact Finset.measurableSet_biUnion _ (fun i _ => (measurableSet_actSet H).inter
      ((Int.measurable_floor.comp (measurable_id.div_const p)) (measurableSet_singleton i)))
  · intro u hu
    obtain ⟨i, -, hui⟩ := mem_iUnion₂.1 hu
    exact hui.1
  · -- the measure of the fitted times
    have hdisj : (↑I : Set ℤ).PairwiseDisjoint (fun i => actSet D ∩ {u | ⌊u / p⌋ = i}) := by
      intro i _ i' _ hii'
      refine Set.disjoint_left.2 ?_
      rintro u ⟨-, hu⟩ ⟨-, hu'⟩
      exact hii' (hu.symm.trans hu')
    have hmeasT : volume T = ∑ i ∈ I, volume (actSet D ∩ {u | ⌊u / p⌋ = i}) :=
      measure_biUnion_finset hdisj (fun i _ => (measurableSet_actSet H).inter
        ((Int.measurable_floor.comp (measurable_id.div_const p)) (measurableSet_singleton i)))
    have hgoodI : ∀ i ∈ I, ENNReal.ofReal (p / K₁) ≤ volume (actSet D ∩ {u | ⌊u / p⌋ = i}) := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
      exact hgood _ (hcJ j hj).1
    -- fibers of `j ↦ ⌊u_j / p⌋` have at most five elements
    have hτ0 : ∀ j ∈ J, 0 ≤ τJ j := fun j hj => (hT01 _ (hτJ j hj).1).1
    have hfib : ∀ i ∈ I, (J.filter (fun j => ⌊uJ j / p⌋ = i)).card ≤ 5 := by
      intro i hi
      obtain ⟨j₀, hj₀, rfl⟩ := Finset.mem_image.1 hi
      have hsub : J.filter (fun j => ⌊uJ j / p⌋ = ⌊uJ j₀ / p⌋) ⊆ Finset.Icc (j₀ - 2) (j₀ + 2) := by
        intro j hj
        obtain ⟨hjJ, hjeq⟩ := Finset.mem_filter.1 hj
        -- same `p`-bin
        have hclose : |uJ j - uJ j₀| < p := by
          have a1 := Int.floor_le (uJ j / p); have a2 := Int.lt_floor_add_one (uJ j / p)
          have a3 := Int.floor_le (uJ j₀ / p); have a4 := Int.lt_floor_add_one (uJ j₀ / p)
          rw [hjeq] at a1 a2
          rw [le_div_iff₀ hp] at a1 a3; rw [div_lt_iff₀ hp] at a2 a4
          rw [abs_lt]; constructor <;> nlinarith
        have hτeq : ∀ j ∈ J, τJ j = lam * s₁ * (uJ j - u₀) := fun j hj => (hcJ j hj).2
        have hτclose : |τJ j / δ - τJ j₀ / δ| < 2 := by
          rw [hτeq j hjJ, hτeq j₀ hj₀, ← sub_div]
          have : lam * s₁ * (uJ j - u₀) - lam * s₁ * (uJ j₀ - u₀) = lam * s₁ * (uJ j - uJ j₀) := by
            ring
          rw [this, abs_div, abs_of_pos hδ0, div_lt_iff₀ hδ0, abs_mul, abs_mul, abs_sign hs₁,
            mul_one, abs_of_pos hlam0]
          calc lam * |uJ j - uJ j₀| < lam * p := mul_lt_mul_of_pos_left hclose hlam0
            _ = 2 * δ := hδlam.symm
        have hj1 := (hτJ j hjJ).2.1
        have hj2 := (hτJ j₀ hj₀).2.1
        have e1 := Nat.floor_le (div_nonneg (hτ0 j hjJ) hδ0.le)
        have e2 := Nat.lt_floor_add_one (τJ j / δ)
        have e3 := Nat.floor_le (div_nonneg (hτ0 j₀ hj₀) hδ0.le)
        have e4 := Nat.lt_floor_add_one (τJ j₀ / δ)
        rw [hj1] at e1 e2; rw [hj2] at e3 e4
        have hlt1 : (j : ℝ) < (j₀ : ℝ) + 3 := by linarith [(abs_lt.1 hτclose).2]
        have hlt2 : (j₀ : ℝ) < (j : ℝ) + 3 := by linarith [(abs_lt.1 hτclose).1]
        have hlt1' : j < j₀ + 3 := by exact_mod_cast hlt1
        have hlt2' : j₀ < j + 3 := by exact_mod_cast hlt2
        rw [Finset.mem_Icc]; omega
      calc (J.filter (fun j => ⌊uJ j / p⌋ = ⌊uJ j₀ / p⌋)).card ≤ (Finset.Icc (j₀ - 2) (j₀ + 2)).card :=
            Finset.card_le_card hsub
        _ ≤ 5 := by rw [Nat.card_Icc]; omega
    have hJI : J.card ≤ 5 * I.card := Finset.card_le_mul_card_image J 5 hfib
    -- combine
    rw [hmeasT]
    calc ENNReal.ofReal (p ^ ε / (5 * C₀ * K₁)) ≤ ENNReal.ofReal ((I.card : ℝ) * (p / K₁)) := by
          apply ENNReal.ofReal_le_ofReal
          have hpe : p ^ ε = p ^ (ε - 1) * p := by
            rw [← Real.rpow_add_one hp.ne']; ring_nf
          have hδe : p ^ (ε - 1) ≤ δ ^ (ε - 1) := Real.rpow_le_rpow_of_nonpos hδ0 hδp (by linarith)
          have hJR : (J.card : ℝ) ≤ 5 * I.card := by exact_mod_cast hJI
          have h1 : p ^ (ε - 1) ≤ 5 * I.card * C₀ := by
            calc p ^ (ε - 1) ≤ δ ^ (ε - 1) := hδe
              _ ≤ J.card * C₀ := hJ
              _ ≤ 5 * I.card * C₀ := by gcongr
          rw [hpe, div_le_iff₀ (by positivity)]
          have : (I.card : ℝ) * (p / K₁) * (5 * C₀ * K₁) = 5 * I.card * C₀ * p := by
            field_simp
          rw [this]
          exact mul_le_mul_of_nonneg_right h1 hp.le
      _ = I.card * ENNReal.ofReal (p / K₁) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      _ = ∑ _i ∈ I, ENNReal.ofReal (p / K₁) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ I, volume (actSet D ∩ {u | ⌊u / p⌋ = i}) := Finset.sum_le_sum hgoodI
  · -- the affine fit on the fitted times
    intro u hu
    obtain ⟨i, hi, hua, hui⟩ := mem_iUnion₂.1 hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hi
    have hcj := (hcJ j hj).1
    have hτj := hτJ j hj
    have hτeq : τJ j = lam * s₁ * (uJ j - u₀) := (hcJ j hj).2
    have hu1 := actSet_sub H hua
    have huj := hu01 _ hcj
    -- `g` at the representative
    have hback : u₀ + s₁ * (lam * s₁ * (uJ j - u₀)) / lam = uJ j := by
      rcases hs₁ with h | h <;> subst h <;> field_simp <;> ring
    have hgj : g (τJ j) = lam * s₂ * (D.φ u₀ - D.φ (uJ j)) := by
      simp only [hg]; rw [hτeq, hback]
    have hfitj : |D.φ (uJ j) - ((D.φ u₀ - s₂ * c' / lam + s₁ * s₂ * σ' * u₀) +
        -(s₁ * s₂ * σ') * uJ j)| ≤ (4 * K + 1) * p := by
      have heq : D.φ (uJ j) - ((D.φ u₀ - s₂ * c' / lam + s₁ * s₂ * σ' * u₀) +
          -(s₁ * s₂ * σ') * uJ j) = -(s₂ / lam) * (g (τJ j) - (c' + σ' * τJ j)) := by
        rw [hgj, hτeq]
        rcases hs₂ with h | h <;> subst h <;> field_simp <;> ring
      rw [heq, abs_mul, abs_neg, abs_div, abs_sign hs₂, abs_of_pos hlam0]
      calc 1 / lam * |g (τJ j) - (c' + σ' * τJ j)| ≤ 1 / lam * ((4 * (2 * K) + 2) * δ) :=
            mul_le_mul_of_nonneg_left hτj.2.2 (by positivity)
        _ = (4 * K + 1) * p := by rw [hlam, hδ]; field_simp; ring
    have hclose : |u - uJ j| < p := by
      have a1 := Int.floor_le (u / p); have a2 := Int.lt_floor_add_one (u / p)
      have a3 := Int.floor_le (uJ j / p); have a4 := Int.lt_floor_add_one (uJ j / p)
      rw [hui] at a1 a2
      rw [le_div_iff₀ hp] at a1 a3; rw [div_lt_iff₀ hp] at a2 a4
      rw [abs_lt]; constructor <;> nlinarith
    have hφ : |D.φ u - D.φ (uJ j)| ≤ 2 * K * p := by
      calc |D.φ u - D.φ (uJ j)| ≤ K * (|u - uJ j| + p) := H.φlip _ hu1 _ huj
        _ ≤ K * (p + p) := by gcongr
        _ = 2 * K * p := by ring
    have hσb : |(-(s₁ * s₂ * σ')) * (uJ j - u)| ≤ (6 * K + 1) * p := by
      rw [abs_mul, abs_neg, abs_mul, abs_mul, abs_sign hs₁, abs_sign hs₂, abs_sub_comm]
      simp only [one_mul]
      exact mul_le_mul (by linarith) hclose.le (abs_nonneg _) (by linarith)
    have : D.φ u - ((D.φ u₀ - s₂ * c' / lam + s₁ * s₂ * σ' * u₀) + -(s₁ * s₂ * σ') * u) =
        (D.φ u - D.φ (uJ j)) + (D.φ (uJ j) - ((D.φ u₀ - s₂ * c' / lam + s₁ * s₂ * σ' * u₀) +
          -(s₁ * s₂ * σ') * uJ j)) + (-(s₁ * s₂ * σ')) * (uJ j - u) := by ring
    rw [this]
    calc _ ≤ |D.φ u - D.φ (uJ j)| + |D.φ (uJ j) - ((D.φ u₀ - s₂ * c' / lam + s₁ * s₂ * σ' * u₀) +
          -(s₁ * s₂ * σ') * uJ j)| + |(-(s₁ * s₂ * σ')) * (uJ j - u)| := abs_add_three _ _ _
      _ ≤ 2 * K * p + (4 * K + 1) * p + (6 * K + 1) * p := by gcongr
      _ = (12 * K + 2) * p := by ring

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

end
