import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet.Support

/-!
# Summing the groups

At the reading time `ts`, every occupied group whose normalized labeled mass (after removing
its light `p₀`-cells) is `≥ μ₀` receives a heavy window of residual slopes from
`group_heavy_slope`. The union `L₀` of these windows carries prior mass comparable to the
total normalized mass of the trajectories labeled at `ts` (`dense_slope_lines`):

`ofReal (m₁/H) ≤ ofReal (4 C₁ C₂ / f) ν(L₀) + ofReal (NG ((2K/p₀ + 2)² f + μ₀))`,

where `m₁ ≤ ∫_{labeled at ts} durT`, `NG` bounds the number of occupied groups, and every
trajectory of `L₀` is labeled at `ts` and has its residual slope within `w' + V` of the
center `κ g` of its group `g`.
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The number of occupied groups allowed by `occupied_groups`. -/
def groupCount (K d H : ℝ) : ℝ := (2 * (2 * K + 2 * K ^ 2) + 2) * (K * (1 / H) ^ d) * (2 * ⌈K⌉₊ + 3)

/-- A uniform bound for the prior mass of one group. -/
def groupMass (K d H : ℝ) : ℝ := (2 * K / H + 2) ^ 2 * ((2 * K + 1) + 4 * K + 2) * (K * H ^ (2 + d))

/-- The prior mass of one group. -/
theorem groupSet_mass_le {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ}
    {E : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ} (h : Data ν y β γ E F d K ζ) (hK : 0 ≤ K)
    {E' : Set (Ω × ℝ)} (hE'E : E' ⊆ E) {t₀ ts H : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) (hζH : ζ ≤ H)
    (hts0 : ts - t₀ ∈ Icc (0 : ℝ) H) (g : ℤ) :
    ν (groupSet E' y β γ F t₀ ts H g) ≤ ENNReal.ofReal (groupMass K d H) := by
  refine slab_absCap h hK (t := ts) (q := H) (σ := 2 * K) (ω := (2 * K + 1) * H)
    (y00 := -K) (y10 := -K) (s₀ := g * H - K * H) hζH hH1 hH (by positivity) (by positivity)
    _ (fun l hl => ?_) |>.trans (le_of_eq ?_)
  · obtain ⟨hlE, hg⟩ := hl
    have hy0 := abs_le.mp (h.bound_y l 0)
    have hy1 := abs_le.mp (h.bound_y l 1)
    have b1 := Int.floor_le (baseVal y β γ F t₀ ts l / H)
    have b2 := Int.lt_floor_add_one (baseVal y β γ F t₀ ts l / H)
    rw [hg, le_div_iff₀ hH] at b1
    rw [hg, div_lt_iff₀ hH] at b2
    have hdiff : |scal y β γ F l ts - baseVal y β γ F t₀ ts l| ≤ K * H := by
      have : scal y β γ F l ts - baseVal y β γ F t₀ ts l = (ts - t₀) * γ l := by
        unfold scal baseVal xbar; ring
      rw [this, abs_mul, mul_comm]
      exact mul_le_mul (h.bound_γ l) (by rw [abs_le]; constructor <;> linarith [hts0.1, hts0.2])
        (abs_nonneg _) hK
    have hd := abs_le.mp hdiff
    refine ⟨hE'E hlE, by linarith, by linarith, by linarith, by linarith, by linarith, by nlinarith⟩
  · unfold groupMass
    congr 1
    field_simp

/-- The heavy part of a group misses at most `#cells · f` of prior mass. -/
theorem heavyPart_compl_le {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {S : Set Ω}
    (hS : MeasurableSet S) (hy : Measurable y) {K p₀ f : ℝ} (hp₀ : 0 < p₀) (hK : 0 ≤ K)
    (hf : 0 ≤ f) (hyb : ∀ l i, |y l i| ≤ K) :
    ν (S \ heavyPart ν S y p₀ f) ≤ ENNReal.ofReal ((2 * K / p₀ + 2) ^ 2 * f) := by
  classical
  set cells := (floorRange p₀ (-K) (2 * K)) ×ˢ (floorRange p₀ (-K) (2 * K))
  have hcell : ∀ l, yCell y p₀ l ∈ cells := by
    intro l
    have h0 := abs_le.mp (hyb l 0)
    have h1 := abs_le.mp (hyb l 1)
    exact Finset.mem_product.mpr ⟨floor_mem_floorRange hp₀ (by linarith) (by linarith),
      floor_mem_floorRange hp₀ (by linarith) (by linarith)⟩
  set light := cells.filter (fun c => ν (S ∩ {l' | yCell y p₀ l' = c}) < ENNReal.ofReal f)
  have hsub : S \ heavyPart ν S y p₀ f ⊆ ⋃ c ∈ light, S ∩ {l' | yCell y p₀ l' = c} := by
    intro l ⟨hlS, hlh⟩
    have : ¬ ENNReal.ofReal f ≤ ν (S ∩ {l' | yCell y p₀ l' = yCell y p₀ l}) := fun h' =>
      hlh ⟨hlS, h'⟩
    exact mem_iUnion₂.mpr ⟨yCell y p₀ l, Finset.mem_filter.mpr ⟨hcell l, not_le.mp this⟩,
      hlS, rfl⟩
  calc ν (S \ heavyPart ν S y p₀ f) ≤ ∑ c ∈ light, ν (S ∩ {l' | yCell y p₀ l' = c}) :=
        (measure_mono hsub).trans (measure_biUnion_finset_le _ _)
    _ ≤ ∑ _c ∈ light, ENNReal.ofReal f :=
        Finset.sum_le_sum (fun c hc => (Finset.mem_filter.mp hc).2.le)
    _ ≤ ∑ _c ∈ cells, ENNReal.ofReal f :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = ENNReal.ofReal (cells.card * f) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ ENNReal.ofReal ((2 * K / p₀ + 2) ^ 2 * f) := by
        apply ENNReal.ofReal_le_ofReal
        apply mul_le_mul_of_nonneg_right _ hf
        rw [Finset.card_product, Nat.cast_mul, sq]
        have h1 := card_floorRange_le (a := -K) hp₀ (by linarith : (0:ℝ) ≤ 2 * K)
        exact mul_le_mul h1 h1 (Nat.cast_nonneg _) (by positivity)

/-- The normalized labels of a group, as a measure of its prior restriction. -/
theorem groupLabels_restrict_mass (ν : Measure Ω) [SFinite ν] {E : Set (Ω × ℝ)}
    (hE : MeasurableSet E) {T : Set ℝ} (hT : MeasurableSet T) {t₀ H : ℝ} (hH : 0 < H)
    (hTsub : T ⊆ Icc t₀ (t₀ + H)) {G G0 : Set Ω} (hG : MeasurableSet G)
    (hG0 : MeasurableSet G0) (hGG0 : G ⊆ G0) :
    ((ν.restrict G0).prod volume) (groupLabels E T t₀ H G) =
      ENNReal.ofReal H⁻¹ * ∫⁻ l in G, durIn E T l ∂ν := by
  rw [groupLabels_mass (ν.restrict G0) hE hT hH hTsub hG, Measure.restrict_restrict hG,
    inter_eq_left.mpr hGG0]

/-- Durations inside `T` are at most `|T| ≤ H`. -/
theorem durIn_le {E : Set (Ω × ℝ)} {T : Set ℝ} {t₀ H : ℝ} (hTsub : T ⊆ Icc t₀ (t₀ + H))
    (hH : 0 ≤ H) (l : Ω) : durIn E T l ≤ ENNReal.ofReal H := by
  unfold durIn
  calc volume {t | t ∈ T ∧ (l, t) ∈ E} ≤ volume (Icc t₀ (t₀ + H)) :=
        measure_mono (fun t ht => hTsub ht.1)
    _ = ENNReal.ofReal H := by rw [Real.volume_Icc]; ring_nf

/-- The dense set of trajectories with slope windows. -/
theorem dense_slope_lines {ν : Measure Ω} [IsProbabilityMeasure ν] {y : Ω → Fin 2 → ℝ}
    {β γ : Ω → ℝ} {E : Set (Ω × ℝ)} {F : ℝ → Fin 2 → ℝ} {d K ζ : ℝ}
    (h : Data ν y β γ E F d K ζ) (hK : 1 ≤ K) (hd : 0 ≤ d) (hζ0 : 0 ≤ ζ)
    {E' : Set (Ω × ℝ)} (hE' : MeasurableSet E') (hE'E : E' ⊆ E)
    {t₀ H : ℝ} (hH : 0 < H) (hH1 : H ≤ 1) (hζH : ζ ≤ H)
    {T : Set ℝ} (hT : MeasurableSet T) (hTsub : T ⊆ Icc t₀ (t₀ + H)) (hT01 : T ⊆ Icc 0 1)
    {a A : Fin 2 → ℝ} {Efit KA : ℝ} (hEfit : 0 ≤ Efit) (hKA : 0 ≤ KA)
    (hfit : ∀ t ∈ T, ∀ i, |F t i - (a i + (t - t₀) * A i)| ≤ Efit) (hA : ∀ i, |A i| ≤ KA)
    {ts : ℝ} (hts : ts ∈ T) {p₀ f μ₀ w' : ℝ} (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1)
    (hζq : ζ ≤ H * p₀) (hr1 : 2 * (4 * K ^ 2 + K + 1) * H ≤ 1)
    (hf : 0 < f) (hμ₀ : 0 < μ₀) (hw' : 0 < w')
    (hbig : 8 * (cnt1 K d p₀ * cap2 K d H p₀) ≤ μ₀)
    (hfarN : cnt1 K d p₀ * (2 * (p₀ + 2 * (4 * K * Efit / H)) / w') * groupMass K d H ^ 2 <
      μ₀ ^ 2 / 2) :
    ∃ (L₀ : Set Ω) (κ : ℤ → ℝ), MeasurableSet L₀ ∧ (∀ l ∈ L₀, (l, ts) ∈ E') ∧
      (∀ l ∈ L₀, |resSlope y γ A l - κ ⌊baseVal y β γ F t₀ ts l / H⌋| ≤
        w' + slopeVar K KA H p₀ ζ) ∧
      ENNReal.ofReal H⁻¹ * ∫⁻ l, {l | (l, ts) ∈ E'}.indicator (durIn E' T) l ∂ν ≤
        ENNReal.ofReal (4 * (cnt1 K d p₀ * cap2 K d H p₀) / f) * ν L₀ +
        ENNReal.ofReal (groupCount K d H * ((2 * K / p₀ + 2) ^ 2 * f + μ₀)) := by
  classical
  have hK0 : 0 ≤ K := by linarith
  have htsT := hTsub hts
  have hts0 : ts - t₀ ∈ Icc (0 : ℝ) H := ⟨by linarith [htsT.1], by linarith [htsT.2]⟩
  obtain ⟨Gs, hGs, hGsmem⟩ := occupied_groups h hK0 hH hζH hH1 (hT01 hts) hts0
  set C := cnt1 K d p₀ * cap2 K d H p₀ with hCdef
  have hC : 0 < C := by
    rw [hCdef]; unfold cnt1 cap2
    have : 0 < 4 * K ^ 2 + K + 1 := by positivity
    positivity
  set V := slopeVar K KA H p₀ ζ with hVdef
  let G0 : ℤ → Set Ω := fun g => groupSet E' y β γ F t₀ ts H g
  let Gh : ℤ → Set Ω := fun g => heavyPart ν (G0 g) y p₀ f
  let Mp : ℤ → ENNReal := fun g =>
    ((ν.restrict (G0 g)).prod volume) (groupLabels E' T t₀ H (Gh g))
  have hG0m : ∀ g, MeasurableSet (G0 g) := fun g =>
    measurableSet_groupSet hE' h.measurable_y h.measurable_β h.measurable_γ F t₀ ts H g
  have hGhm : ∀ g, MeasurableSet (Gh g) := fun g =>
    measurableSet_heavyPart ν (hG0m g) h.measurable_y p₀ f
  have hkm : Measurable (resSlope y γ A) := by
    have hγm := h.measurable_γ
    have hy0m : Measurable fun l => y l 0 := (measurable_pi_apply 0).comp h.measurable_y
    have hy1m : Measurable fun l => y l 1 := (measurable_pi_apply 1).comp h.measurable_y
    unfold resSlope; fun_prop
  have hMpfin : ∀ g, Mp g ≠ ⊤ := by
    intro g
    refine ne_top_of_le_ne_top (b := ENNReal.ofReal H⁻¹ * ν (Gh g) * ENNReal.ofReal H) ?_ ?_
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
        ENNReal.ofReal_ne_top
    · show ((ν.restrict (G0 g)).prod volume) (groupLabels E' T t₀ H (Gh g)) ≤ _
      rw [groupLabels_restrict_mass ν hE' hT hH hTsub (hGhm g) (hG0m g) inter_subset_left,
        mul_assoc]
      gcongr
      calc ∫⁻ l in Gh g, durIn E' T l ∂ν ≤ ∫⁻ _l in Gh g, ENNReal.ofReal H ∂ν :=
            setLIntegral_mono measurable_const (fun l _ => durIn_le hTsub hH.le l)
        _ = ν (Gh g) * ENNReal.ofReal H := by rw [setLIntegral_const, mul_comm]
  -- good groups and their windows
  let good : Finset ℤ := Gs.filter (fun g => ENNReal.ofReal μ₀ ≤ Mp g)
  have hwin : ∀ g ∈ good, ∃ κ : ℝ, ENNReal.ofReal (f * (Mp g).toReal / (4 * C)) ≤
      ν (Gh g ∩ {l | |resSlope y γ A l - κ| ≤ w' + V}) := by
    intro g hg
    have hgood := (Finset.mem_filter.mp hg).2
    set M₀ := (Mp g).toReal with hM₀def
    have hμM : μ₀ ≤ M₀ := by
      rw [hM₀def]
      exact (ENNReal.ofReal_le_iff_le_toReal (hMpfin g)).mp hgood
    have hM₀ : 0 < M₀ := hμ₀.trans_le hμM
    have hgm := groupSet_mass_le h hK0 hE'E hH hH1 hζH hts0 g (ν := ν)
    have := group_heavy_slope h hK hd hζ0 hE' hE'E hH hζH hT hTsub hEfit hKA hfit hA hts g
      (m := f * M₀ / (4 * C)) (M₀ := M₀) hp₀ hp₀1 hζq hr1 hf (by positivity) hM₀ hw'
      (by rw [hM₀def]; exact ENNReal.ofReal_toReal_le)
      (by
        have e : f * M₀ / (4 * C) / f = M₀ / (4 * C) := by field_simp
        rw [← hCdef, e]
        have : C * (M₀ / (4 * C)) = M₀ / 4 := by field_simp
        nlinarith)
      (by
        calc ENNReal.ofReal (cnt1 K d p₀) * (ENNReal.ofReal (2 * (p₀ + 2 * (4 * K * Efit / H)) / w') *
              ν (groupSet E' y β γ F t₀ ts H g) ^ 2)
            ≤ ENNReal.ofReal (cnt1 K d p₀) * (ENNReal.ofReal (2 * (p₀ + 2 * (4 * K * Efit / H)) / w') *
              ENNReal.ofReal (groupMass K d H) ^ 2) := by gcongr
          _ = ENNReal.ofReal (cnt1 K d p₀ * (2 * (p₀ + 2 * (4 * K * Efit / H)) / w') *
              groupMass K d H ^ 2) := by
              have h1 : 0 ≤ cnt1 K d p₀ := by unfold cnt1; positivity
              have h2 : 0 ≤ 2 * (p₀ + 2 * (4 * K * Efit / H)) / w' := by positivity
              have h3 : 0 ≤ groupMass K d H := by unfold groupMass; positivity
              rw [← ENNReal.ofReal_pow h3, ← ENNReal.ofReal_mul h2, ← ENNReal.ofReal_mul h1]
              congr 1; ring
          _ < ENNReal.ofReal (μ₀ ^ 2 / 2) := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hfarN
          _ ≤ ENNReal.ofReal (M₀ ^ 2 / 2) := by
              apply ENNReal.ofReal_le_ofReal
              have : μ₀ ^ 2 ≤ M₀ ^ 2 := pow_le_pow_left₀ hμ₀.le hμM 2
              linarith)
    exact this
  choose κ' hκ' using hwin
  let κ : ℤ → ℝ := fun g => if hg : g ∈ good then κ' g hg else 0
  let L₀ : Set Ω := ⋃ g ∈ good, (Gh g ∩ {l | |resSlope y γ A l - κ g| ≤ w' + V})
  have hwinm : ∀ g, MeasurableSet (Gh g ∩ {l | |resSlope y γ A l - κ g| ≤ w' + V}) := fun g =>
    (hGhm g).inter (measurableSet_le ((hkm.sub_const _).abs) measurable_const)
  refine ⟨L₀, κ, Finset.measurableSet_biUnion _ (fun g _ => hwinm g), ?_, ?_, ?_⟩
  · intro l hl
    obtain ⟨g, -, hlg, -⟩ := mem_iUnion₂.mp hl
    exact hlg.1.1
  · intro l hl
    obtain ⟨g, -, hlg, hlw⟩ := mem_iUnion₂.mp hl
    have : ⌊baseVal y β γ F t₀ ts l / H⌋ = g := hlg.1.2
    rw [this]
    exact hlw
  · -- the labeled trajectories at `ts` split into the occupied groups
    set lc : ℝ := (2 * K / p₀ + 2) ^ 2 * f with hlc
    have hW : {l | (l, ts) ∈ E'} = ⋃ g ∈ Gs, G0 g := by
      ext l
      simp only [mem_ofPred_eq, mem_iUnion, exists_prop]
      constructor
      · intro hl; exact ⟨_, hGsmem l (hE'E hl), hl, rfl⟩
      · rintro ⟨g, -, hl, -⟩; exact hl
    have hdisj : (↑Gs : Set ℤ).PairwiseDisjoint G0 := by
      intro g _ g' _ hgg'
      refine Set.disjoint_left.mpr ?_
      rintro l ⟨-, h1⟩ ⟨-, h2⟩
      exact hgg' (h1.symm.trans h2)
    have hWm : MeasurableSet {l : Ω | (l, ts) ∈ E'} := measurable_prodMk_right hE'
    rw [lintegral_indicator hWm, hW, lintegral_biUnion_finset hdisj (fun g _ => hG0m g),
      Finset.mul_sum]
    -- each group: heavy part plus light loss
    have hgroup : ∀ g ∈ Gs, ENNReal.ofReal H⁻¹ * ∫⁻ l in G0 g, durIn E' T l ∂ν ≤
        Mp g + ENNReal.ofReal lc := by
      intro g _
      have hsplit : G0 g = Gh g ∪ (G0 g \ Gh g) := (union_diff_cancel inter_subset_left).symm
      have hdm : MeasurableSet (G0 g \ Gh g) := (hG0m g).diff (hGhm g)
      rw [hsplit, lintegral_union hdm disjoint_sdiff_right, mul_add]
      gcongr
      · exact le_of_eq (groupLabels_restrict_mass ν hE' hT hH hTsub (hGhm g) (hG0m g)
          inter_subset_left).symm
      · calc ENNReal.ofReal H⁻¹ * ∫⁻ l in G0 g \ Gh g, durIn E' T l ∂ν
            ≤ ENNReal.ofReal H⁻¹ * ∫⁻ _l in G0 g \ Gh g, ENNReal.ofReal H ∂ν :=
              mul_le_mul_of_nonneg_left (setLIntegral_mono measurable_const
                (fun l _ => durIn_le hTsub hH.le l)) bot_le
          _ = ν (G0 g \ Gh g) := by
              rw [setLIntegral_const, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
                inv_mul_cancel₀ hH.ne', ENNReal.ofReal_one, one_mul]
          _ ≤ ENNReal.ofReal lc :=
              heavyPart_compl_le (hG0m g) h.measurable_y hp₀ hK0 hf.le h.bound_y
    -- good groups give their windows, bad groups are light
    have hgood_le : ∀ g ∈ good, Mp g ≤ ENNReal.ofReal (4 * C / f) *
        ν (Gh g ∩ {l | |resSlope y γ A l - κ g| ≤ w' + V}) := by
      intro g hg
      have hκg : κ g = κ' g hg := by simp only [κ, hg, dif_pos]
      rw [hκg]
      calc Mp g = ENNReal.ofReal (4 * C / f) * ENNReal.ofReal (f * (Mp g).toReal / (4 * C)) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            have : 4 * C / f * (f * (Mp g).toReal / (4 * C)) = (Mp g).toReal := by
              field_simp
            rw [this, ENNReal.ofReal_toReal (hMpfin g)]
        _ ≤ _ := by gcongr; exact hκ' g hg
    have hbad : ∀ g ∈ Gs.filter (fun g => ¬ ENNReal.ofReal μ₀ ≤ Mp g), Mp g ≤ ENNReal.ofReal μ₀ :=
      fun g hg => (not_le.mp (Finset.mem_filter.mp hg).2).le
    have hL₀ : ∑ g ∈ good, ν (Gh g ∩ {l | |resSlope y γ A l - κ g| ≤ w' + V}) = ν L₀ := by
      rw [measure_biUnion_finset]
      · intro g _ g' _ hgg'
        refine Set.disjoint_left.mpr ?_
        rintro l ⟨⟨⟨-, h1⟩, -⟩, -⟩ ⟨⟨⟨-, h2⟩, -⟩, -⟩
        exact hgg' (h1.symm.trans h2)
      · intro g _; exact hwinm g
    have hcard : (Gs.card : ENNReal) * ENNReal.ofReal (lc + μ₀) ≤
        ENNReal.ofReal (groupCount K d H * (lc + μ₀)) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      unfold groupCount
      exact hGs
    calc ∑ g ∈ Gs, ENNReal.ofReal H⁻¹ * ∫⁻ l in G0 g, durIn E' T l ∂ν
        ≤ ∑ g ∈ Gs, (Mp g + ENNReal.ofReal lc) := Finset.sum_le_sum hgroup
      _ = ∑ g ∈ good, Mp g + ∑ g ∈ Gs.filter (fun g => ¬ ENNReal.ofReal μ₀ ≤ Mp g), Mp g +
            ∑ _g ∈ Gs, ENNReal.ofReal lc := by
          rw [Finset.sum_add_distrib, Finset.sum_filter_add_sum_filter_not]
      _ ≤ ENNReal.ofReal (4 * C / f) * ν L₀ + ∑ _g ∈ Gs, ENNReal.ofReal μ₀ +
            ∑ _g ∈ Gs, ENNReal.ofReal lc := by
          gcongr
          · rw [← hL₀, Finset.mul_sum]; exact Finset.sum_le_sum hgood_le
          · exact (Finset.sum_le_sum hbad).trans
              (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
      _ = ENNReal.ofReal (4 * C / f) * ν L₀ + (Gs.card : ENNReal) * ENNReal.ofReal (lc + μ₀) := by
          rw [add_assoc, ← Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
            ENNReal.ofReal_add (by positivity) hμ₀.le, add_comm (ENNReal.ofReal μ₀)]
      _ ≤ ENNReal.ofReal (4 * C / f) * ν L₀ + ENNReal.ofReal (groupCount K d H * (lc + μ₀)) := by
          gcongr

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

end
