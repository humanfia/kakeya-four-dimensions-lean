import Mathlib
import Submission.Lib.K4QuadSheetMatching.Lines
import Submission.Lib.K4QuadSheetMatching.Slicing
-- Adapted from: here:o078 (session x0262, branch x0262 of o078).

/-!
# Local matching of quadratic sheets (version 1 of the paper's Corollary 3.4)

Two lists of quadratic sheets on the unit square, of sizes at most `R^{d₀ + ε₀}`, bounded by
`R^{ε₀}`, cannot carry a pair law of mass `≥ R^{-ε₀}` whose colour marginals have densities at
most `R^{ε₀} π`, on whose events the two sheets agree to `R^{-1+ε₀}` while their difference is
at least `R^{-ε₀}` somewhere on the square. The proof selects a large jet direction, slices the
pair law along it and applies two-colour matching (the frozen input, o015) to the restricted
one-variable quadratics.
-/

namespace Submission.Lib.K4QuadSheetMatching

open MeasureTheory Set
open scoped ENNReal

/-- The two-colour matching statement, exactly as frozen (o015). -/
def TwoColorStatement : Prop :=
  ∀ (D J : ℕ), 1 ≤ D → D < J → ∀ d : ℝ, 0 ≤ d → d < 1 → ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
    ∀ N : ℝ, N₀ ≤ N → ∀ (n₁ n₂ : ℕ) (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
      (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (μ : MeasureTheory.Measure ((Fin n₁ × Fin n₂) × ℝ)),
      (n₁ : ℝ) ≤ N ^ (d + η) → (n₂ : ℝ) ≤ N ^ (d + η) →
      (∀ i : Fin n₁, ContDiffOn ℝ (J + 1) (f₁ i) (Set.Ioo (-1 : ℝ) 2)) →
      (∀ i : Fin n₂, ContDiffOn ℝ (J + 1) (f₂ i) (Set.Ioo (-1 : ℝ) 2)) →
      (∀ (i : Fin n₁) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |iteratedDeriv j (f₁ i) t| ≤ N ^ η) →
      (∀ (i : Fin n₂) (j : ℕ), j ≤ J + 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |iteratedDeriv j (f₂ i) t| ≤ N ^ η) →
      (∀ i : Fin n₁, 0 ≤ π₁ i) → (∀ i : Fin n₂, 0 ≤ π₂ i) →
      (∑ i : Fin n₁, π₁ i) = 1 → (∑ i : Fin n₂, π₂ i) = 1 →
      MeasureTheory.IsProbabilityMeasure μ →
      (∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E →
        μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₁ i) * MeasureTheory.volume E) →
      (∀ (i : Fin n₂) (E : Set ℝ), MeasurableSet E →
        μ {p | p.1.2 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (N ^ η * π₂ i) * MeasureTheory.volume E) →
      ¬ μ {p | p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ |f₁ p.1.1 p.2 - f₂ p.1.2 p.2| ≤ N ^ (-1 + η) ∧
        ∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧
          N ^ (-η) ≤ |iteratedDeriv j (f₁ p.1.1) p.2 - iteratedDeriv j (f₂ p.1.2) p.2|}ᶜ = 0

lemma continuous_jetq (e : Fin 6 → ℝ) (k : Fin 5) :
    Continuous (fun z : ℝ × ℝ => jetq e z.1 z.2 k) := by
  fin_cases k <;> simp [jetq, qdt, qdy, qdtt, qdyy, qddd] <;> fun_prop

lemma continuous_qev (c : Fin 6 → ℝ) : Continuous (fun z : ℝ × ℝ => qev c z.1 z.2) := by
  unfold qev; fun_prop

/-- Pigeonhole for finite sums of extended reals. -/
lemma exists_sum_ge_div {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ≥0∞) (X : ℝ≥0∞)
    (h : X ≤ ∑ i ∈ s, f i) : ∃ i ∈ s, X / s.card ≤ f i := by
  by_contra hcon
  push Not at hcon
  have hlt : ∑ i ∈ s, f i < ∑ _i ∈ s, X / s.card := ENNReal.sum_lt_sum_of_nonempty hs hcon
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  have hc : (s.card : ℝ≥0∞) ≠ 0 := by simpa using hs.card_pos.ne'
  rw [ENNReal.mul_div_cancel hc (ENNReal.natCast_ne_top _)] at hlt
  exact absurd (h.trans_lt hlt) (lt_irrefl _)

/-- **Local matching of quadratic sheets.** -/
theorem quad_sheet_matching (hTC : TwoColorStatement) {d₀ : ℝ} (hd0 : 0 ≤ d₀) (hd1 : d₀ < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
    ∀ (n₁ n₂ : ℕ) (c₁ : Fin n₁ → Fin 6 → ℝ) (c₂ : Fin n₂ → Fin 6 → ℝ)
      (π₁ : Fin n₁ → ℝ) (π₂ : Fin n₂ → ℝ) (ρ : Fin n₁ × Fin n₂ → Measure (ℝ × ℝ)),
    (∀ ι, IsFiniteMeasure (ρ ι)) →
    (n₁ : ℝ) ≤ R ^ (d₀ + ε₀) → (n₂ : ℝ) ≤ R ^ (d₀ + ε₀) →
    (∀ i, ∀ z ∈ unitSq, |qev (c₁ i) z.1 z.2| ≤ R ^ ε₀) →
    (∀ j, ∀ z ∈ unitSq, |qev (c₂ j) z.1 z.2| ≤ R ^ ε₀) →
    (∀ i, 0 ≤ π₁ i) → (∀ j, 0 ≤ π₂ j) → ∑ i, π₁ i = 1 → ∑ j, π₂ j = 1 →
    (∀ i (B : Set (ℝ × ℝ)), MeasurableSet B →
      ∑ j, ρ (i, j) B ≤ ENNReal.ofReal (R ^ ε₀ * π₁ i) * volume B) →
    (∀ j (B : Set (ℝ × ℝ)), MeasurableSet B →
      ∑ i, ρ (i, j) B ≤ ENNReal.ofReal (R ^ ε₀ * π₂ j) * volume B) →
    ENNReal.ofReal (R ^ (-ε₀)) ≤ ∑ ι, ρ ι univ →
    (∀ ι, ∀ᵐ z ∂ρ ι, z ∈ unitSq ∧
      |qev (c₁ ι.1) z.1 z.2 - qev (c₂ ι.2) z.1 z.2| ≤ R ^ (-1 + ε₀) ∧
      ∃ w ∈ unitSq, R ^ (-ε₀) ≤ |qev (c₁ ι.1) w.1 w.2 - qev (c₂ ι.2) w.1 w.2|) →
    False := by
  obtain ⟨η, hη, N₀, hN₀, hTC'⟩ := hTC 2 3 (by norm_num) (by norm_num) d₀ hd0 hd1
  set ε₀ := min (η / 4) (1 / 8) with hε₀
  have hε₀pos : 0 < ε₀ := lt_min (by positivity) (by norm_num)
  have hε₀η : ε₀ ≤ η / 4 := min_le_left _ _
  have hε₀8 : ε₀ ≤ 1 / 8 := min_le_right _ _
  refine ⟨ε₀, hε₀pos, max (max N₀ 4) ((3000 : ℝ) ^ (2 / η)), le_trans (by norm_num)
    ((le_max_right N₀ 4).trans (le_max_left _ _)), ?_⟩
  intro R hR n₁ n₂ c₁ c₂ π₁ π₂ ρ hρfin hn₁ hn₂ hb₁ hb₂ hπ₁ hπ₂ hs₁ hs₂ hm₁ hm₂ hmass hgood
  -- numerical consequences of `R ≥ R₀`
  have hRN : N₀ ≤ R := (le_max_left _ _).trans ((le_max_left _ _).trans hR)
  have hR4 : (4 : ℝ) ≤ R := (le_max_right _ _).trans ((le_max_left _ _).trans hR)
  have hR0 : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hRη : (3000 : ℝ) ≤ R ^ (η / 2) := by
    have h := (le_max_right (max N₀ 4) ((3000 : ℝ) ^ (2 / η))).trans hR
    calc (3000 : ℝ) = ((3000 : ℝ) ^ (2 / η)) ^ (η / 2) := by
          rw [← Real.rpow_mul (by norm_num)]; field_simp; simp
      _ ≤ R ^ (η / 2) := Real.rpow_le_rpow (by positivity) h (by positivity)
  have hpow : ∀ a b : ℝ, a ≤ b → R ^ a ≤ R ^ b := fun a b h => Real.rpow_le_rpow_of_exponent_le hR1 h
  have hRpos : ∀ a : ℝ, 0 < R ^ a := fun a => Real.rpow_pos_of_pos hR0 a
  have hmul : ∀ a b : ℝ, R ^ a * R ^ b = R ^ (a + b) := fun a b => (Real.rpow_add hR0 a b).symm
  have hR3000 : ∀ a : ℝ, a ≤ η / 2 → 3000 * R ^ a ≤ R ^ η := by
    intro a ha
    calc 3000 * R ^ a ≤ R ^ (η / 2) * R ^ (η / 2) :=
          mul_le_mul hRη (hpow _ _ ha) (hRpos _).le (hRpos _).le
      _ = R ^ η := by rw [hmul]; ring_nf
  -- Step A: a jet quantity carrying a fifth of the mass
  set e : Fin n₁ × Fin n₂ → Fin 6 → ℝ := fun ι => c₁ ι.1 - c₂ ι.2 with he
  set S : Fin n₁ × Fin n₂ → Fin 5 → Set (ℝ × ℝ) :=
    fun ι k => {z | R ^ (-ε₀) / 10 ≤ jetq (e ι) z.1 z.2 k} with hS
  have hSm : ∀ ι k, MeasurableSet (S ι k) := fun ι k =>
    measurableSet_le measurable_const (continuous_jetq (e ι) k).measurable
  have hthr : R ^ (-ε₀) / 10 ≤ (R ^ (-ε₀) - R ^ (-1 + ε₀)) / 5 := by
    have h3 : 2 ≤ R ^ (1 - 2 * ε₀) := by
      calc (2 : ℝ) = (4 : ℝ) ^ (1 / 2 : ℝ) := by
            rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
        _ ≤ R ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hR4 (by norm_num)
        _ ≤ R ^ (1 - 2 * ε₀) := hpow _ _ (by linarith)
    have h2 : 2 * R ^ (-1 + ε₀) ≤ R ^ (-ε₀) := by
      have : R ^ (-ε₀) = R ^ (-1 + ε₀) * R ^ (1 - 2 * ε₀) := by rw [hmul]; ring_nf
      rw [this]
      nlinarith [hRpos (-1 + ε₀)]
    linarith
  have hcover : ∀ ι, ∀ᵐ z ∂ρ ι, ∃ k, z ∈ S ι k := by
    intro ι
    filter_upwards [hgood ι] with z hz
    obtain ⟨hzu, hval, w, hw, hwv⟩ := hz
    obtain ⟨k, hk⟩ := exists_large_jet (e ι) (t₀ := z.1) (y₀ := z.2) (t := w.1) (y := w.2)
      (θ := R ^ (-1 + ε₀)) (r := R ^ (-ε₀)) hzu hw
      (by rw [qev_sub]; exact hval) (by rw [qev_sub]; exact hwv)
    exact ⟨k, hthr.trans hk⟩
  have hsumS : ∀ ι, ρ ι univ ≤ ∑ k, ρ ι (S ι k) := by
    intro ι
    have hnull : ρ ι (⋃ k, S ι k)ᶜ = 0 := by
      have := hcover ι
      rw [ae_iff] at this
      refine measure_mono_null (fun z hz => ?_) this
      simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hz
      simp only [Set.mem_ofPred_eq, not_exists]
      exact hz
    calc ρ ι univ ≤ ρ ι (⋃ k, S ι k) + ρ ι (⋃ k, S ι k)ᶜ := measure_univ_le_add_compl _
      _ = ρ ι (⋃ k, S ι k) := by rw [hnull, add_zero]
      _ ≤ ∑ k, ρ ι (S ι k) := measure_iUnion_fintype_le _ _
  have hsum2 : ENNReal.ofReal (R ^ (-ε₀)) ≤ ∑ k : Fin 5, ∑ ι, ρ ι (S ι k) := by
    calc _ ≤ ∑ ι, ρ ι univ := hmass
      _ ≤ ∑ ι, ∑ k, ρ ι (S ι k) := Finset.sum_le_sum (fun ι _ => hsumS ι)
      _ = ∑ k, ∑ ι, ρ ι (S ι k) := Finset.sum_comm
  obtain ⟨k, -, hk⟩ := exists_sum_ge_div Finset.univ Finset.univ_nonempty _ _ hsum2
  rw [Finset.card_univ, Fintype.card_fin] at hk
  -- Step B: transverse coordinates adapted to the jet
  set L := jetLine k with hL
  set ρ' : Fin n₁ × Fin n₂ → Measure (ℝ × ℝ) :=
    fun ι => Measure.map L.Q ((ρ ι).restrict (S ι k)) with hρ'
  have hρ'fin : ∀ ι, IsFiniteMeasure (ρ' ι) := fun ι => by rw [hρ']; infer_instance
  have hρ'apply : ∀ ι B, MeasurableSet B → ρ' ι B = ρ ι (L.Q ⁻¹' B ∩ S ι k) := by
    intro ι B hB
    rw [hρ', Measure.map_apply L.hQm hB, Measure.restrict_apply (L.hQm hB)]
  have hvolQ : ∀ B, MeasurableSet B → volume (L.Q ⁻¹' B) = volume B := fun B hB =>
    L.hQ.measure_preimage hB.nullMeasurableSet
  have h1' : ∀ i (B : Set (ℝ × ℝ)), MeasurableSet B →
      ∑ j, ρ' (i, j) B ≤ ENNReal.ofReal (R ^ ε₀ * π₁ i) * volume B := by
    intro i B hB
    calc ∑ j, ρ' (i, j) B = ∑ j, ρ (i, j) (L.Q ⁻¹' B ∩ S (i, j) k) :=
          Finset.sum_congr rfl (fun j _ => hρ'apply _ B hB)
      _ ≤ ∑ j, ρ (i, j) (L.Q ⁻¹' B) :=
          Finset.sum_le_sum (fun j _ => measure_mono Set.inter_subset_left)
      _ ≤ ENNReal.ofReal (R ^ ε₀ * π₁ i) * volume (L.Q ⁻¹' B) := hm₁ i _ (L.hQm hB)
      _ = _ := by rw [hvolQ B hB]
  have h2' : ∀ j (B : Set (ℝ × ℝ)), MeasurableSet B →
      ∑ i, ρ' (i, j) B ≤ ENNReal.ofReal (R ^ ε₀ * π₂ j) * volume B := by
    intro j B hB
    calc ∑ i, ρ' (i, j) B = ∑ i, ρ (i, j) (L.Q ⁻¹' B ∩ S (i, j) k) :=
          Finset.sum_congr rfl (fun i _ => hρ'apply _ B hB)
      _ ≤ ∑ i, ρ (i, j) (L.Q ⁻¹' B) :=
          Finset.sum_le_sum (fun i _ => measure_mono Set.inter_subset_left)
      _ ≤ ENNReal.ofReal (R ^ ε₀ * π₂ j) * volume (L.Q ⁻¹' B) := hm₂ j _ (L.hQm hB)
      _ = _ := by rw [hvolQ B hB]
  set G0 : Fin n₁ × Fin n₂ → Set (ℝ × ℝ) := fun ι => {z | z ∈ unitSq ∧
    |qev (c₁ ι.1) z.1 z.2 - qev (c₂ ι.2) z.1 z.2| ≤ R ^ (-1 + ε₀) ∧
    R ^ (-ε₀) / 10 ≤ jetq (e ι) z.1 z.2 k} with hG0
  have hG0m : ∀ ι, MeasurableSet (G0 ι) := by
    intro ι
    show MeasurableSet (unitSq ∩ ({z : ℝ × ℝ | |qev (c₁ ι.1) z.1 z.2 - qev (c₂ ι.2) z.1 z.2| ≤
      R ^ (-1 + ε₀)} ∩ {z : ℝ × ℝ | R ^ (-ε₀) / 10 ≤ jetq (e ι) z.1 z.2 k}))
    refine (measurableSet_Icc.prod measurableSet_Icc).inter ((measurableSet_le ?_ measurable_const).inter
      (measurableSet_le measurable_const (continuous_jetq (e ι) k).measurable))
    exact ((continuous_qev _).sub (continuous_qev _)).abs.measurable
  set Good : Fin n₁ × Fin n₂ → Set (ℝ × ℝ) := fun ι => (fun p : ℝ × ℝ => L.P p.1 p.2) ⁻¹' G0 ι
    with hGood
  have hGoodm : ∀ ι, MeasurableSet (Good ι) := fun ι => L.hPm (hG0m ι)
  have hQGood : ∀ ι z, L.Q z ∈ Good ι ↔ z ∈ G0 ι := by
    intro ι z
    simp only [hGood, Set.mem_preimage]
    rw [L.hPQ z]
  have hG : ∀ ι, ρ' ι (Good ι)ᶜ = 0 := by
    intro ι
    rw [hρ'apply ι _ (hGoodm ι).compl]
    have := hgood ι
    rw [ae_iff] at this
    refine measure_mono_null (fun z hz => ?_) this
    obtain ⟨hzG, hzS⟩ := hz
    simp only [Set.mem_preimage, Set.mem_compl_iff, hQGood] at hzG
    simp only [Set.mem_ofPred_eq]
    intro ⟨hzu, hval, _⟩
    exact hzG ⟨hzu, hval, hzS⟩
  have hsupp : ∀ ι, ρ' ι {z | z.1 ∉ Icc (-1 : ℝ) 1} = 0 := by
    intro ι
    rw [hρ'apply ι {z : ℝ × ℝ | z.1 ∉ Icc (-1 : ℝ) 1}
      (by exact (measurableSet_Icc.preimage measurable_fst).compl)]
    have := hgood ι
    rw [ae_iff] at this
    refine measure_mono_null (fun z hz => ?_) this
    obtain ⟨hzQ, _⟩ := hz
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hzQ
    simp only [Set.mem_ofPred_eq]
    intro ⟨hzu, _⟩
    exact hzQ (L.hrange z hzu)
  have hm5 : (0 : ℝ) < R ^ (-ε₀) / 5 := by have := hRpos (-ε₀); positivity
  have hmass' : ENNReal.ofReal (R ^ (-ε₀) / 5) ≤ ∑ ι, ρ' ι univ := by
    have : ∀ ι, ρ' ι univ = ρ ι (S ι k) := fun ι => by
      rw [hρ'apply ι _ MeasurableSet.univ, Set.preimage_univ, Set.univ_inter]
    simp_rw [this]
    calc ENNReal.ofReal (R ^ (-ε₀) / 5) = ENNReal.ofReal (R ^ (-ε₀)) / 5 := by
          rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
      _ ≤ _ := hk
  -- Step C: a heavy good slice
  obtain ⟨ζ, hζ, σ, hσfin, hσmass, hσ1, hσ2, hσgood⟩ :=
    exists_good_slice ρ' π₁ π₂ h1' h2' Good hGoodm hG hsupp hm5 hmass'
  -- Step D: the one-variable law and two-colour matching
  set T : ℝ≥0∞ := ∑ ι, σ ι univ with hT
  have hTlow : ENNReal.ofReal (R ^ (-ε₀) / 5 / 4) ≤ T := hσmass
  have hTpos : (0 : ℝ) < R ^ (-ε₀) / 5 / 4 := by positivity
  have hT0 : T ≠ 0 := by
    intro h; rw [h] at hTlow
    exact absurd (ENNReal.ofReal_pos.mpr hTpos) (not_lt.mpr hTlow)
  have hTtop : T ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun ι _ => measure_ne_top _ _)
  set ν₀ : Measure ((Fin n₁ × Fin n₂) × ℝ) := ∑ ι, Measure.map (fun s => (ι, s)) (σ ι) with hν₀
  have hν₀apply : ∀ A, MeasurableSet A → ν₀ A = ∑ ι, σ ι {s | (ι, s) ∈ A} := by
    intro A hA
    rw [hν₀, Measure.finsetSum_apply]
    refine Finset.sum_congr rfl (fun ι _ => ?_)
    rw [Measure.map_apply measurable_prodMk_left hA]; rfl
  set μ : Measure ((Fin n₁ × Fin n₂) × ℝ) := T⁻¹ • ν₀ with hμ
  have hμprob : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    rw [hμ, Measure.smul_apply, hν₀apply _ MeasurableSet.univ, smul_eq_mul]
    simp only [Set.mem_univ, Set.ofPred_true]
    exact ENNReal.inv_mul_cancel hT0 hTtop
  -- the inverse mass loss
  have hTinv : T⁻¹ ≤ ENNReal.ofReal (20 * R ^ ε₀) := by
    have h20 : ENNReal.ofReal (20 * R ^ ε₀) = (ENNReal.ofReal (R ^ (-ε₀) / 5 / 4))⁻¹ := by
      rw [← ENNReal.ofReal_inv_of_pos hTpos]
      congr 1
      rw [Real.rpow_neg hR0.le]; field_simp; ring
    rw [h20]
    exact ENNReal.inv_le_inv.mpr hTlow
  have hloss : ∀ x : ℝ, 0 ≤ x → T⁻¹ * ENNReal.ofReal (R ^ ε₀ * x) ≤ ENNReal.ofReal (R ^ η * x) := by
    intro x hx
    calc T⁻¹ * ENNReal.ofReal (R ^ ε₀ * x) ≤ ENNReal.ofReal (20 * R ^ ε₀) * ENNReal.ofReal (R ^ ε₀ * x) := by
          gcongr
      _ = ENNReal.ofReal (20 * (R ^ ε₀ * R ^ ε₀) * x) := by
          rw [← ENNReal.ofReal_mul (by have := hRpos ε₀; positivity)]; ring_nf
      _ ≤ ENNReal.ofReal (R ^ η * x) := by
          apply ENNReal.ofReal_le_ofReal
          apply mul_le_mul_of_nonneg_right _ hx
          rw [hmul]
          have := hR3000 (ε₀ + ε₀) (by linarith)
          linarith [hRpos (ε₀ + ε₀)]
  have hmarg1 : ∀ (i : Fin n₁) (E : Set ℝ), MeasurableSet E →
      μ {p | p.1.1 = i ∧ p.2 ∈ E} ≤ ENNReal.ofReal (R ^ η * π₁ i) * volume E := by
    intro i E hE
    have hA : MeasurableSet {p : (Fin n₁ × Fin n₂) × ℝ | p.1.1 = i ∧ p.2 ∈ E} :=
      ((measurableSet_singleton i).preimage (measurable_fst.comp measurable_fst)).inter
        (hE.preimage measurable_snd)
    rw [hμ, Measure.smul_apply, hν₀apply _ hA, smul_eq_mul]
    have hsum : ∑ ι, σ ι {s | (ι, s) ∈ {p : (Fin n₁ × Fin n₂) × ℝ | p.1.1 = i ∧ p.2 ∈ E}} =
        ∑ j, σ (i, j) E := by
      rw [Fintype.sum_prod_type]
      simp only [Set.mem_ofPred_eq]
      rw [Finset.sum_eq_single i]
      · simp
      · intro i' _ hi'
        refine Finset.sum_eq_zero (fun j _ => ?_)
        have : {s : ℝ | i' = i ∧ s ∈ E} = ∅ := by ext s; simp [hi']
        rw [this, measure_empty]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hsum]
    calc T⁻¹ * ∑ j, σ (i, j) E ≤ T⁻¹ * (ENNReal.ofReal (R ^ ε₀ * π₁ i) * volume E) := by
          gcongr; exact hσ1 i E hE
      _ = T⁻¹ * ENNReal.ofReal (R ^ ε₀ * π₁ i) * volume E := by ring
      _ ≤ ENNReal.ofReal (R ^ η * π₁ i) * volume E := by gcongr; exact hloss _ (hπ₁ i)
  have hmarg2 : ∀ (j : Fin n₂) (E : Set ℝ), MeasurableSet E →
      μ {p | p.1.2 = j ∧ p.2 ∈ E} ≤ ENNReal.ofReal (R ^ η * π₂ j) * volume E := by
    intro j E hE
    have hA : MeasurableSet {p : (Fin n₁ × Fin n₂) × ℝ | p.1.2 = j ∧ p.2 ∈ E} :=
      ((measurableSet_singleton j).preimage (measurable_snd.comp measurable_fst)).inter
        (hE.preimage measurable_snd)
    rw [hμ, Measure.smul_apply, hν₀apply _ hA, smul_eq_mul]
    have hsum : ∑ ι, σ ι {s | (ι, s) ∈ {p : (Fin n₁ × Fin n₂) × ℝ | p.1.2 = j ∧ p.2 ∈ E}} =
        ∑ i, σ (i, j) E := by
      rw [Fintype.sum_prod_type]
      simp only [Set.mem_ofPred_eq]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finset.sum_eq_single j]
      · simp
      · intro j' _ hj'
        have : {s : ℝ | j' = j ∧ s ∈ E} = ∅ := by ext s; simp [hj']
        rw [this, measure_empty]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [hsum]
    calc T⁻¹ * ∑ i, σ (i, j) E ≤ T⁻¹ * (ENNReal.ofReal (R ^ ε₀ * π₂ j) * volume E) := by
          gcongr; exact hσ2 j E hE
      _ = T⁻¹ * ENNReal.ofReal (R ^ ε₀ * π₂ j) * volume E := by ring
      _ ≤ ENNReal.ofReal (R ^ η * π₂ j) * volume E := by gcongr; exact hloss _ (hπ₂ j)
  -- the restricted sheets
  set f₁ : Fin n₁ → ℝ → ℝ := fun i s => qev (c₁ i) (L.P ζ s).1 (L.P ζ s).2 with hf₁
  set f₂ : Fin n₂ → ℝ → ℝ := fun j s => qev (c₂ j) (L.P ζ s).1 (L.P ζ s).2 with hf₂
  have hderiv : ∀ c : Fin 6 → ℝ, (∀ z ∈ unitSq, |qev c z.1 z.2| ≤ R ^ ε₀) →
      ContDiffOn ℝ (3 + 1) (fun s => qev c (L.P ζ s).1 (L.P ζ s).2) (Ioo (-1 : ℝ) 2) ∧
      ∀ j : ℕ, j ≤ 3 + 1 → ∀ t ∈ Icc (0 : ℝ) 1,
        |iteratedDeriv j (fun s => qev c (L.P ζ s).1 (L.P ζ s).2) t| ≤ R ^ η := by
    intro c hc
    obtain ⟨A, B, C, hABC⟩ := L.hform c ζ
    rw [hABC]
    refine ⟨by apply ContDiff.contDiffOn; fun_prop, fun j hj t ht => ?_⟩
    have hM : ∀ s ∈ Icc (0 : ℝ) 1, |A + B * s + C * s ^ 2| ≤ 108 * R ^ ε₀ := by
      intro s hs
      have := qev_ext_bound hc (L.P ζ s) (L.hext ζ hζ s hs)
      have e : qev c (L.P ζ s).1 (L.P ζ s).2 = A + B * s + C * s ^ 2 := congrFun hABC s
      rw [← e]; exact this
    calc |iteratedDeriv j (fun s => A + B * s + C * s ^ 2) t| ≤ 26 * (108 * R ^ ε₀) :=
          abs_iteratedDeriv_quad1_le hM j (by omega) t ht
      _ ≤ R ^ η := by
          have := hR3000 ε₀ (by linarith)
          nlinarith [hRpos ε₀]
  have hn₁' : (n₁ : ℝ) ≤ R ^ (d₀ + η) := hn₁.trans (hpow _ _ (by linarith))
  have hn₂' : (n₂ : ℝ) ≤ R ^ (d₀ + η) := hn₂.trans (hpow _ _ (by linarith))
  have hTCapp := hTC' R hRN n₁ n₂ f₁ f₂ π₁ π₂ μ hn₁' hn₂'
    (fun i => (hderiv (c₁ i) (hb₁ i)).1) (fun j => (hderiv (c₂ j) (hb₂ j)).1)
    (fun i j hj t ht => (hderiv (c₁ i) (hb₁ i)).2 j hj t ht)
    (fun i j hj t ht => (hderiv (c₂ i) (hb₂ i)).2 j hj t ht)
    hπ₁ hπ₂ hs₁ hs₂ hμprob hmarg1 hmarg2
  apply hTCapp
  -- every slice point that is good for the plane law is good for matching
  set B' : Set ((Fin n₁ × Fin n₂) × ℝ) := {p | (ζ, p.2) ∉ Good p.1} with hB'
  have hB'm : MeasurableSet B' := by
    have : B' = ⋃ ι : Fin n₁ × Fin n₂, ({ι} : Set (Fin n₁ × Fin n₂)) ×ˢ {s : ℝ | (ζ, s) ∉ Good ι} := by
      ext p; simp [hB']
    rw [this]
    exact MeasurableSet.iUnion (fun ι => (measurableSet_singleton ι).prod
      ((hGoodm ι).preimage measurable_prodMk_left).compl)
  have hB'0 : μ B' = 0 := by
    rw [hμ, Measure.smul_apply, hν₀apply _ hB'm, smul_eq_mul]
    have : ∑ ι, σ ι {s | (ι, s) ∈ B'} = 0 := by
      refine Finset.sum_eq_zero (fun ι _ => ?_)
      exact hσgood ι
    rw [this, mul_zero]
  refine measure_mono_null (fun p hp => ?_) hB'0
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hp
  simp only [hB', Set.mem_ofPred_eq]
  intro hgoodp
  apply hp
  obtain ⟨hPu, hval, hjet⟩ := hgoodp
  refine ⟨L.hs ζ p.2 hPu, ?_, L.ord, L.hord1, L.hord2, ?_⟩
  · exact hval.trans (hpow _ _ (by linarith))
  · have hj := L.hjet (c₁ p.1.1) (c₂ p.1.2) ζ p.2
    rw [hj]
    refine le_trans ?_ hjet
    have h10 : 10 * R ^ (-η) ≤ R ^ (-ε₀) := by
      have := hR3000 (η - ε₀ - η / 2) (by linarith)
      have e1 : R ^ (-ε₀) = R ^ (-η) * R ^ (η - ε₀) := by rw [hmul]; ring_nf
      rw [e1]
      have e2 : R ^ (η - ε₀) = R ^ (η - ε₀ - η / 2) * R ^ (η / 2) := by rw [hmul]; ring_nf
      have : 10 ≤ R ^ (η - ε₀) := by
        rw [e2]
        have h1 : 1 ≤ R ^ (η - ε₀ - η / 2) := Real.one_le_rpow hR1 (by linarith)
        nlinarith [hRη]
      nlinarith [hRpos (-η)]
    linarith

/-- **Matching in one group** (the form used in the terminal extension). Sheets within
`M R^{ε₀}` of a reference sheet `c₀` on the unit square, every index carrying marginal mass at
least `φ` in the group, colour-marginal densities at most `Θ` with `Θ ≤ R^{ε₀} φ`, at most
`R^{d₀+ε₀}` indices per colour: then the group cannot be supported on pairs whose sheets agree to
`M R^{-1+ε₀}` at the base point but differ by at least `M R^{-ε₀}` on the square. -/
theorem quad_group_matching (hTC : TwoColorStatement) {d₀ : ℝ} (hd0 : 0 ≤ d₀) (hd1 : d₀ < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ (M Θ φ : ℝ), 0 < M → 0 < φ →
    Θ ≤ R ^ ε₀ * φ →
    ∀ (n₁ n₂ : ℕ) (c₀ : Fin 6 → ℝ) (c₁ : Fin n₁ → Fin 6 → ℝ) (c₂ : Fin n₂ → Fin 6 → ℝ)
      (ρ : Fin n₁ × Fin n₂ → Measure (ℝ × ℝ)),
    (∀ ι, IsFiniteMeasure (ρ ι)) →
    (n₁ : ℝ) ≤ R ^ (d₀ + ε₀) → (n₂ : ℝ) ≤ R ^ (d₀ + ε₀) →
    (∀ i, ∀ z ∈ unitSq, |qev (c₁ i) z.1 z.2 - qev c₀ z.1 z.2| ≤ M * R ^ ε₀) →
    (∀ j, ∀ z ∈ unitSq, |qev (c₂ j) z.1 z.2 - qev c₀ z.1 z.2| ≤ M * R ^ ε₀) →
    (∀ i (B : Set (ℝ × ℝ)), MeasurableSet B → ∑ j, ρ (i, j) B ≤ ENNReal.ofReal Θ * volume B) →
    (∀ j (B : Set (ℝ × ℝ)), MeasurableSet B → ∑ i, ρ (i, j) B ≤ ENNReal.ofReal Θ * volume B) →
    (∀ i, ENNReal.ofReal φ ≤ ∑ j, ρ (i, j) univ) →
    (∀ j, ENNReal.ofReal φ ≤ ∑ i, ρ (i, j) univ) →
    (∀ ι, ∀ᵐ z ∂ρ ι, z ∈ unitSq ∧
      |qev (c₁ ι.1) z.1 z.2 - qev (c₂ ι.2) z.1 z.2| ≤ M * R ^ (-1 + ε₀) ∧
      ∃ w ∈ unitSq, M * R ^ (-ε₀) ≤ |qev (c₁ ι.1) w.1 w.2 - qev (c₂ ι.2) w.1 w.2|) →
    (0 < n₁) → False := by
  obtain ⟨ε₁, hε₁, R₁, hR₁, hmain⟩ := quad_sheet_matching hTC hd0 hd1
  refine ⟨ε₁ / 2, by positivity, max R₁ 4, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro R hR M Θ φ hM hφ hΘ n₁ n₂ c₀ c₁ c₂ ρ hρfin hn₁ hn₂ hb₁ hb₂ hm₁ hm₂ hf₁ hf₂ hgood hn₁pos
  have hR1 : 1 ≤ R := le_trans (by norm_num) ((le_max_right _ _).trans hR)
  have hR0 : 0 < R := by linarith
  have hRR₁ : R₁ ≤ R := (le_max_left _ _).trans hR
  have hpow : ∀ a b : ℝ, a ≤ b → R ^ a ≤ R ^ b := fun a b h => Real.rpow_le_rpow_of_exponent_le hR1 h
  have hRpos : ∀ a : ℝ, 0 < R ^ a := fun a => Real.rpow_pos_of_pos hR0 a
  -- normalized sheets: subtract the reference and divide by `M`
  set e₁ : Fin n₁ → Fin 6 → ℝ := fun i => M⁻¹ • (c₁ i - c₀) with he₁
  set e₂ : Fin n₂ → Fin 6 → ℝ := fun j => M⁻¹ • (c₂ j - c₀) with he₂
  have hqe : ∀ (c : Fin 6 → ℝ) (t y : ℝ), qev (M⁻¹ • (c - c₀)) t y = (qev c t y - qev c₀ t y) / M := by
    intro c t y; simp only [qev, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; field_simp; ring
  have hdiff : ∀ i j (t y : ℝ), qev (e₁ i) t y - qev (e₂ j) t y = (qev (c₁ i) t y - qev (c₂ j) t y) / M := by
    intro i j t y; rw [he₁, he₂]; simp only; rw [hqe, hqe]; field_simp; ring
  -- the total mass and uniform weights
  set m : ℝ≥0∞ := ∑ ι, ρ ι univ with hm
  have hmfin : m ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun ι _ => measure_ne_top _ _)
  have hn₁m : ENNReal.ofReal ((n₁ : ℝ) * φ) ≤ m := by
    calc ENNReal.ofReal ((n₁ : ℝ) * φ) = ∑ _i : Fin n₁, ENNReal.ofReal φ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      _ ≤ ∑ i, ∑ j, ρ (i, j) univ := Finset.sum_le_sum (fun i _ => hf₁ i)
      _ = m := by rw [hm, Fintype.sum_prod_type]
  have hn₂pos : 0 < n₂ := by
    by_contra h
    push Not at h
    have h0 : n₂ = 0 := by omega
    subst h0
    have : m = 0 := by rw [hm]; simp
    rw [this] at hn₁m
    have := ENNReal.ofReal_eq_zero.mp (le_antisymm hn₁m bot_le)
    have : (0 : ℝ) < (n₁ : ℝ) * φ := by positivity
    linarith
  have hn₂m : ENNReal.ofReal ((n₂ : ℝ) * φ) ≤ m := by
    calc ENNReal.ofReal ((n₂ : ℝ) * φ) = ∑ _j : Fin n₂, ENNReal.ofReal φ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      _ ≤ ∑ j, ∑ i, ρ (i, j) univ := Finset.sum_le_sum (fun j _ => hf₂ j)
      _ = m := by rw [hm, Fintype.sum_prod_type, Finset.sum_comm]
  have hm0 : m ≠ 0 := by
    intro h; rw [h] at hn₁m
    have := ENNReal.ofReal_eq_zero.mp (le_antisymm hn₁m bot_le)
    have : (0 : ℝ) < (n₁ : ℝ) * φ := by positivity
    linarith
  set ρn : Fin n₁ × Fin n₂ → Measure (ℝ × ℝ) := fun ι => m⁻¹ • ρ ι with hρn
  have hρnfin : ∀ ι, IsFiniteMeasure (ρn ι) := fun ι => by
    refine ⟨?_⟩
    rw [hρn]; simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hm0)) (measure_lt_top _ _)
  have hn₁r : (0 : ℝ) < n₁ := by exact_mod_cast hn₁pos
  have hn₂r : (0 : ℝ) < n₂ := by exact_mod_cast hn₂pos
  have hminv : ∀ (k : ℝ), 0 < k → ENNReal.ofReal (k * φ) ≤ m →
      m⁻¹ * ENNReal.ofReal Θ ≤ ENNReal.ofReal (R ^ ε₁ * (1 / k)) := by
    intro k hk hkm
    have h1 : m⁻¹ ≤ ENNReal.ofReal (1 / (k * φ)) := by
      rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_one, one_div]
      exact ENNReal.inv_le_inv.mpr hkm
    calc m⁻¹ * ENNReal.ofReal Θ ≤ ENNReal.ofReal (1 / (k * φ)) * ENNReal.ofReal (R ^ (ε₁ / 2) * φ) := by
          gcongr
      _ = ENNReal.ofReal (R ^ (ε₁ / 2) * (1 / k)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; field_simp
      _ ≤ ENNReal.ofReal (R ^ ε₁ * (1 / k)) := by
          apply ENNReal.ofReal_le_ofReal
          exact mul_le_mul_of_nonneg_right (hpow _ _ (by linarith)) (by positivity)
  refine hmain R hRR₁ n₁ n₂ e₁ e₂ (fun _ => 1 / (n₁ : ℝ)) (fun _ => 1 / (n₂ : ℝ)) ρn hρnfin
    (hn₁.trans (hpow _ _ (by linarith))) (hn₂.trans (hpow _ _ (by linarith))) ?_ ?_
    (fun _ => by positivity) (fun _ => by positivity) ?_ ?_ ?_ ?_ ?_ ?_
  · intro i z hz
    rw [he₁]; simp only; rw [hqe, abs_div, abs_of_pos hM, div_le_iff₀ hM]
    calc _ ≤ M * R ^ (ε₁ / 2) := hb₁ i z hz
      _ ≤ R ^ ε₁ * M := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hpow _ _ (by linarith)) hM.le
  · intro j z hz
    rw [he₂]; simp only; rw [hqe, abs_div, abs_of_pos hM, div_le_iff₀ hM]
    calc _ ≤ M * R ^ (ε₁ / 2) := hb₂ j z hz
      _ ≤ R ^ ε₁ * M := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hpow _ _ (by linarith)) hM.le
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  · intro i B hB
    simp only [hρn, Measure.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    calc m⁻¹ * ∑ j, ρ (i, j) B ≤ m⁻¹ * (ENNReal.ofReal Θ * volume B) := by gcongr; exact hm₁ i B hB
      _ = m⁻¹ * ENNReal.ofReal Θ * volume B := by ring
      _ ≤ ENNReal.ofReal (R ^ ε₁ * (1 / (n₁ : ℝ))) * volume B := by
          gcongr; exact hminv _ hn₁r hn₁m
  · intro j B hB
    simp only [hρn, Measure.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    calc m⁻¹ * ∑ i, ρ (i, j) B ≤ m⁻¹ * (ENNReal.ofReal Θ * volume B) := by gcongr; exact hm₂ j B hB
      _ = m⁻¹ * ENNReal.ofReal Θ * volume B := by ring
      _ ≤ ENNReal.ofReal (R ^ ε₁ * (1 / (n₂ : ℝ))) * volume B := by
          gcongr; exact hminv _ hn₂r hn₂m
  · simp only [hρn, Measure.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, ← hm, ENNReal.inv_mul_cancel hm0 hmfin]
    exact ENNReal.ofReal_le_one.mpr (Real.rpow_le_one_of_one_le_of_nonpos hR1 (by linarith))
  · intro ι
    have := hgood ι
    rw [hρn]
    refine (Measure.ae_smul_measure this _).mono ?_
    rintro z ⟨hz, hval, w, hw, hwv⟩
    refine ⟨hz, ?_, w, hw, ?_⟩
    · rw [hdiff, abs_div, abs_of_pos hM, div_le_iff₀ hM]
      calc _ ≤ M * R ^ (-1 + ε₁ / 2) := hval
        _ ≤ R ^ (-1 + ε₁) * M := by
            rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hpow _ _ (by linarith)) hM.le
    · rw [hdiff, abs_div, abs_of_pos hM, le_div_iff₀ hM]
      calc R ^ (-ε₁) * M ≤ M * R ^ (-(ε₁ / 2)) := by
            rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hpow _ _ (by linarith)) hM.le
        _ ≤ _ := hwv

end Submission.Lib.K4QuadSheetMatching
