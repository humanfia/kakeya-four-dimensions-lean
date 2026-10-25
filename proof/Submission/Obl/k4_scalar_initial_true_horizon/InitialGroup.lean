import Submission.Obl.k4_scalar_initial_true_horizon.InitialCollision
import Submission.Obl.k4_scalar_initial_true_horizon.InitialLebesgue
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.MassBounds

/-!
# Bad mass of one group by Cauchy–Schwarz on grid cells

For one time block and one hidden-bin window, the incidence mass `Y` of a family of
"bad" trajectories is split into grid cells of side `δ`.  Cells whose original
(full-law) mass in the window is at least `c₀ δ²` are few, by the original mass budget
`M`; Cauchy–Schwarz and the planar collision bound control the bad mass in them.  The
bad mass in the other cells lies in observations whose own grid square is light.
-/

namespace Submission.Obl.k4_scalar_initial_true_horizon

open MeasureTheory Set Filter Topology
open scoped ENNReal
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction
  (Coeff spatial hidden obsL measurable_obsL measurable_spatial measurable_hidden)

/-- Cauchy–Schwarz with the counting measure. -/
theorem sq_sum_le_card_mul_sum_sq {ι : Type*} (F : Finset ι) (x : ι → ℝ) :
    (∑ i ∈ F, x i) ^ 2 ≤ (F.card : ℝ) * ∑ i ∈ F, x i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq F x (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul] at h
  linarith

/-- From `Y ≤ X + Z` and `X² ≤ Θ Y` deduce `Y ≤ 4Θ + 2Z`. -/
theorem quadratic_absorb {X Y Z Θ : ℝ} (hX : 0 ≤ X) (hZ : 0 ≤ Z) (hΘ : 0 ≤ Θ)
    (hY : Y ≤ X + Z) (hsq : X ^ 2 ≤ Θ * Y) : Y ≤ 4 * Θ + 2 * Z := by
  rcases le_or_gt X Z with h | h
  · linarith
  · have hY2 : Y ≤ 2 * X := by linarith
    have hXpos : 0 < X := lt_of_le_of_lt hZ h
    have : X ^ 2 ≤ Θ * (2 * X) := hsq.trans (mul_le_mul_of_nonneg_left hY2 hΘ)
    have hX2 : X ≤ 2 * Θ := by nlinarith
    linarith

/-- The time cells of an aligned block. -/
def tCell (t₀ δ : ℝ) (i : ℕ) : Set ℝ := Ico (t₀ + i * δ) (t₀ + (i + 1) * δ)

theorem tCell_disjoint {t₀ δ : ℝ} (hδ : 0 < δ) :
    Pairwise (fun i j : ℕ => Disjoint (tCell t₀ δ i) (tCell t₀ δ j)) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro t hti htj
  simp only [tCell, mem_Ico] at hti htj
  rcases lt_or_gt_of_ne hij with h | h
  · have : ((i : ℝ) + 1) ≤ j := by exact_mod_cast h
    nlinarith
  · have : ((j : ℝ) + 1) ≤ i := by exact_mod_cast h
    nlinarith

theorem tCell_diam {t₀ δ : ℝ} (i : ℕ) : ∀ t ∈ tCell t₀ δ i, ∀ t' ∈ tCell t₀ δ i, |t - t'| < δ := by
  intro t ht t' ht'
  simp only [tCell, mem_Ico] at ht ht'
  rw [abs_lt]; constructor <;> nlinarith

theorem volume_tCell {t₀ δ : ℝ} (hδ : 0 < δ) (i : ℕ) :
    volume (tCell t₀ δ i) = ENNReal.ofReal δ := by
  rw [tCell, Real.volume_Ico]; congr 1; ring

theorem tCell_subset {t₀ δ : ℝ} (hδ : 0 < δ) {R i : ℕ} (hi : i < R) :
    tCell t₀ δ i ⊆ Icc t₀ (t₀ + R * δ) := by
  intro t ht
  simp only [tCell, mem_Ico] at ht
  have : ((i : ℝ) + 1) ≤ R := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  constructor <;> nlinarith

/-- The grid square of an observation inside an aligned block is a product of a time cell
and a space cell. -/
theorem gridSquare_obs_eq {δ : ℝ} (hδ : 0 < δ) (j₀ : ℤ) (i : ℕ) (i' : ℤ) {t y : ℝ}
    (ht : t ∈ tCell (j₀ * δ) δ i) (hy : y ∈ yCell δ i') :
    gridSquare δ ![t, y] = {z | z 0 ∈ tCell (j₀ * δ) δ i ∧ z 1 ∈ yCell δ i'} := by
  have hft : ⌊t / δ⌋ = j₀ + i := by
    rw [Int.floor_eq_iff]
    simp only [tCell, mem_Ico] at ht
    push_cast
    constructor
    · rw [le_div_iff₀ hδ]; nlinarith
    · rw [div_lt_iff₀ hδ]; nlinarith
  have hfy : ⌊y / δ⌋ = i' := by
    rw [Int.floor_eq_iff]
    simp only [yCell, mem_Ico] at hy
    constructor
    · rw [le_div_iff₀ hδ]; exact hy.1
    · rw [div_lt_iff₀ hδ]; exact hy.2
  ext z
  simp only [gridSquare, Set.mem_pi, mem_univ, true_implies, mem_ofPred_eq]
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hft, hfy] at h0 h1
    push_cast at h0
    refine ⟨?_, h1⟩
    simp only [tCell, mem_Ico]
    constructor <;> nlinarith [h0.1, h0.2]
  · rintro ⟨h0, h1⟩ k
    fin_cases k
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, hft]
      simp only [tCell, mem_Ico] at h0
      push_cast
      constructor <;> nlinarith [h0.1, h0.2]
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, hfy]
      exact h1

/-- Incidences whose base point lies in the time cell `i` and the space cell `i'`. -/
def incCell (t₀ δ : ℝ) (Q : ℕ × ℤ) : Set (Coeff × ℝ) :=
  {p | p.2 ∈ tCell t₀ δ Q.1 ∧ spatial p.1 p.2 ∈ yCell δ Q.2}

theorem measurableSet_incCell (t₀ δ : ℝ) (Q : ℕ × ℤ) : MeasurableSet (incCell t₀ δ Q) :=
  (measurable_snd measurableSet_Ico).inter (measurable_spatial measurableSet_Ico)

theorem incCell_disjoint {t₀ δ : ℝ} (hδ : 0 < δ) {Q Q' : ℕ × ℤ} (h : Q ≠ Q') :
    Disjoint (incCell t₀ δ Q) (incCell t₀ δ Q') := by
  rw [Set.disjoint_left]
  rintro p ⟨h1, h2⟩ ⟨h1', h2'⟩
  by_cases hq : Q.1 = Q'.1
  · have hq2 : Q.2 ≠ Q'.2 := fun h2eq => h (Prod.ext hq h2eq)
    exact Set.disjoint_left.mp (yCell_disjoint hδ hq2) h2 h2'
  · exact Set.disjoint_left.mp (tCell_disjoint hδ hq) h1 h1'

/-- Incidence mass in one grid cell is at most the integrated occupation time. -/
theorem incCell_mass_le (ν : Measure Coeff) (E : Set (Coeff × ℝ)) (BL : Set Coeff)
    (hBL : MeasurableSet BL) (Ib : Set ℝ) (hIb : MeasurableSet Ib) (t₀ δ : ℝ) (Q : ℕ × ℤ) :
    ((ν.prod volume).restrict E) ((BL ×ˢ Ib) ∩ incCell t₀ δ Q) ≤
      ∫⁻ l, cellTime (fun l : Coeff => l.2 0) (fun l => l.2 1) (tCell t₀ δ Q.1)
        (yCell δ Q.2) l ∂(ν.restrict BL) := by
  have hm : MeasurableSet ((BL ×ˢ Ib) ∩ incCell t₀ δ Q) :=
    (hBL.prod hIb).inter (measurableSet_incCell t₀ δ Q)
  calc ((ν.prod volume).restrict E) ((BL ×ˢ Ib) ∩ incCell t₀ δ Q)
      ≤ (ν.prod volume) ((BL ×ˢ Ib) ∩ incCell t₀ δ Q) := Measure.restrict_le_self _
    _ = ∫⁻ l, volume (Prod.mk l ⁻¹' ((BL ×ˢ Ib) ∩ incCell t₀ δ Q)) ∂ν :=
        Measure.prod_apply hm
    _ = ∫⁻ l, BL.indicator (fun l => volume (Prod.mk l ⁻¹' ((BL ×ˢ Ib) ∩
          incCell t₀ δ Q))) l ∂ν := by
        apply lintegral_congr
        intro l
        by_cases hl : l ∈ BL
        · rw [Set.indicator_of_mem hl]
        · rw [Set.indicator_of_notMem hl]
          have : Prod.mk l ⁻¹' ((BL ×ˢ Ib) ∩ incCell t₀ δ Q) = ∅ := by
            ext t; simp [hl]
          rw [this, measure_empty]
    _ = ∫⁻ l in BL, volume (Prod.mk l ⁻¹' ((BL ×ˢ Ib) ∩ incCell t₀ δ Q)) ∂ν :=
        lintegral_indicator hBL _
    _ ≤ ∫⁻ l in BL, cellTime (fun l : Coeff => l.2 0) (fun l => l.2 1) (tCell t₀ δ Q.1)
          (yCell δ Q.2) l ∂ν := by
        apply lintegral_mono
        intro l
        apply measure_mono
        rintro t ⟨_, ht1, ht2⟩
        exact ⟨ht1, ht2⟩

/-- Long trajectories: the prior mass is controlled by the incidence mass. -/
theorem prior_le_of_long (ν : Measure Coeff) (E : Set (Coeff × ℝ)) (hE : MeasurableSet E)
    (BL : Set Coeff) (hBL : MeasurableSet BL) (Ib : Set ℝ) (hIb : MeasurableSet Ib) {θ : ℝ}
    (hlong : ∀ l ∈ BL, ENNReal.ofReal θ ≤ volume {t ∈ Ib | (l, t) ∈ E}) :
    ENNReal.ofReal θ * ν BL ≤ ((ν.prod volume).restrict E) (BL ×ˢ Ib) := by
  rw [Measure.restrict_apply (hBL.prod hIb), Measure.prod_apply ((hBL.prod hIb).inter hE)]
  calc ENNReal.ofReal θ * ν BL = ∫⁻ l in BL, ENNReal.ofReal θ ∂ν := by
        rw [setLIntegral_const, mul_comm]
    _ ≤ ∫⁻ l in BL, volume (Prod.mk l ⁻¹' (BL ×ˢ Ib ∩ E)) ∂ν := by
        apply setLIntegral_mono' hBL
        intro l hl
        refine (hlong l hl).trans (measure_mono ?_)
        rintro t ⟨ht, htE⟩
        exact ⟨⟨hl, ht⟩, htE⟩
    _ ≤ ∫⁻ l, volume (Prod.mk l ⁻¹' (BL ×ˢ Ib ∩ E)) ∂ν := setLIntegral_le_lintegral _ _

/-- **Bad mass of one group.**  `Y ≤ 4 (C₁/(c₀ φ₀ q)) M + 2 Z`, where `Y` is the incidence
mass of the bad trajectories `BL` in the block, `M` the original mass of the block in the
hidden-bin window, and `Z` the part of `Y` whose observations have light grid squares. -/
theorem group_bad_mass_le
    (ν : Measure Coeff) [IsFiniteMeasure ν] (E : Set (Coeff × ℝ)) (hE : MeasurableSet E)
    (f : (Fin 2 → ℝ) × ℤ → ℝ≥0∞) (a : ℝ)
    (hlaw : Measure.map (obsL a) ((ν.prod volume).restrict E) =
      (volume.prod Measure.count).withDensity f)
    (BL : Set Coeff) (hBL : MeasurableSet BL)
    {δ φ₀ c₀ C₁ Ybd : ℝ} (hδ : 0 < δ) (hφ₀ : 0 < φ₀) (hc₀ : 0 < c₀) (hC₁ : 0 ≤ C₁)
    (j₀ : ℤ) (R : ℕ) (hR : 0 < R) (m₁ m₂ : ℤ)
    (hwin : ∀ l ∈ BL, ∀ t ∈ Ico (j₀ * δ) (j₀ * δ + R * δ), ⌊hidden l t / a⌋ ∈ Icc m₁ m₂)
    (hbdd : ∀ l ∈ BL, ∀ t ∈ Ico (j₀ * δ) (j₀ * δ + R * δ), |spatial l t| ≤ Ybd)
    (hlong : ∀ l ∈ BL, ENNReal.ofReal (φ₀ * (R * δ)) ≤
      volume {t ∈ Ico (j₀ * δ) (j₀ * δ + R * δ) | (l, t) ∈ E})
    (hcoll : ∑ i ∈ Finset.range R, ∑' i' : ℤ,
        (∫⁻ l, cellTime (fun l : Coeff => l.2 0) (fun l => l.2 1) (tCell (j₀ * δ) δ i)
          (yCell δ i') l ∂(ν.restrict BL)) ^ 2 ≤
        ENNReal.ofReal δ * (ν.restrict BL) univ * ENNReal.ofReal (C₁ * δ)) :
    (((ν.prod volume).restrict E) (BL ×ˢ Ico (j₀ * δ) (j₀ * δ + R * δ))).toReal ≤
      4 * (C₁ / (c₀ * φ₀ * (R * δ)) *
        (((ν.prod volume).restrict E) {p | p.2 ∈ Ico (j₀ * δ) (j₀ * δ + R * δ) ∧
          ⌊hidden p.1 p.2 / a⌋ ∈ Icc m₁ m₂}).toReal) +
      2 * (((ν.prod volume).restrict E) ((BL ×ˢ Ico (j₀ * δ) (j₀ * δ + R * δ)) ∩
        obsL a ⁻¹' lowCells ((volume.prod Measure.count).withDensity f) δ c₀)).toReal := by
  classical
  set μa := (ν.prod volume).restrict E with hμa
  set t₀ : ℝ := j₀ * δ with ht₀
  set q : ℝ := R * δ with hq
  set Ib : Set ℝ := Ico t₀ (t₀ + q) with hIb
  set lam := (volume.prod Measure.count).withDensity f with hlam
  have hq0 : 0 < q := by rw [hq]; exact mul_pos (by exact_mod_cast hR) hδ
  have hIbm : MeasurableSet Ib := measurableSet_Ico
  -- finiteness of the block masses
  have hfinBlock : ∀ S : Set (Coeff × ℝ), S ⊆ univ ×ˢ Ib → μa S ≠ ⊤ := by
    intro S hS
    refine ne_top_of_le_ne_top ?_ ((Measure.restrict_le_self _).trans
      (measure_mono hS))
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) (by rw [hIb, Real.volume_Ico]; simp)
  -- the strip and window
  set strip : Set (Coeff × ℝ) := {p | p.2 ∈ Ib ∧ ⌊hidden p.1 p.2 / a⌋ ∈ Icc m₁ m₂} with hstrip
  set win : Set (Coeff × ℝ) := {p | ⌊hidden p.1 p.2 / a⌋ ∈ Icc m₁ m₂} with hwinset
  have hwinm : MeasurableSet win :=
    ((measurable_hidden.div_const a).floor) (measurableSet_Icc)
  -- grid cells
  set Y' : ℤ := ⌈Ybd / δ⌉ with hY'
  set idx : Finset (ℕ × ℤ) := Finset.range R ×ˢ Finset.Icc (-Y' - 1) Y' with hidx
  set lamG : ℕ × ℤ → ℝ≥0∞ := fun Q => μa (incCell t₀ δ Q ∩ win) with hlamG
  set F : Finset (ℕ × ℤ) := idx.filter (fun Q => ENNReal.ofReal (c₀ * δ ^ 2) ≤ lamG Q) with hF
  set lowSet : Set (Coeff × ℝ) := obsL a ⁻¹' lowCells lam δ c₀ with hlowSet
  have hlowm : MeasurableSet lowSet :=
    measurable_obsL a (measurableSet_lowCells lam hδ c₀)
  -- cells of the block
  have hcellQ : ∀ p ∈ BL ×ˢ Ib, ∃ Q ∈ idx, p ∈ incCell t₀ δ Q := by
    rintro ⟨l, t⟩ ⟨hl, ht⟩
    have ht' : t ∈ Ico t₀ (t₀ + q) := ht
    refine ⟨((⌊t / δ⌋ - j₀).toNat, ⌊spatial l t / δ⌋), ?_, ?_⟩
    · have hfl1 : j₀ ≤ ⌊t / δ⌋ := by
        rw [Int.le_floor, le_div_iff₀ hδ]; rw [ht₀] at ht'; exact ht'.1
      have hfl2 : ⌊t / δ⌋ < j₀ + R := by
        rw [Int.floor_lt, div_lt_iff₀ hδ]; push_cast
        rw [ht₀, hq] at ht'; nlinarith [ht'.2]
      have hy := hbdd l hl t ht
      simp only [hidx, Finset.mem_product, Finset.mem_range, Finset.mem_Icc]
      have hlo : -Y' ≤ ⌊spatial l t / δ⌋ := by
        have h1 : ⌊-(Ybd / δ)⌋ ≤ ⌊spatial l t / δ⌋ := by
          apply Int.floor_mono
          rw [neg_le, ← neg_div]; apply div_le_div_of_nonneg_right _ hδ.le
          linarith [neg_abs_le (spatial l t)]
        rwa [Int.floor_neg] at h1
      have hhi : ⌊spatial l t / δ⌋ ≤ Y' := by
        have h1 : ⌊spatial l t / δ⌋ ≤ ⌊Ybd / δ⌋ := by
          apply Int.floor_mono
          apply div_le_div_of_nonneg_right _ hδ.le
          exact (le_abs_self _).trans hy
        exact h1.trans (Int.floor_le_ceil _)
      refine ⟨by omega, by omega, hhi⟩
    · constructor
      · simp only [tCell, mem_Ico]
        have hfl1 : j₀ ≤ ⌊t / δ⌋ := by
          rw [Int.le_floor, le_div_iff₀ hδ]; rw [ht₀] at ht'; exact ht'.1
        have hcast : ((((⌊t / δ⌋ - j₀).toNat : ℕ) : ℤ) : ℝ) = (⌊t / δ⌋ : ℝ) - j₀ := by
          rw [Int.toNat_of_nonneg (by omega)]; push_cast; ring
        have hcast' : (((⌊t / δ⌋ - j₀).toNat : ℕ) : ℝ) = (⌊t / δ⌋ : ℝ) - j₀ := by
          exact_mod_cast hcast
        rw [hcast', ht₀]
        have h1 := Int.floor_le (t / δ)
        have h2 := Int.lt_floor_add_one (t / δ)
        rw [le_div_iff₀ hδ] at h1
        rw [div_lt_iff₀ hδ] at h2
        constructor <;> nlinarith
      · exact mem_yCell_floor hδ _
  -- (a) splitting the bad mass
  have hsplit : μa (BL ×ˢ Ib) ≤ ∑ Q ∈ F, μa ((BL ×ˢ Ib) ∩ incCell t₀ δ Q) +
      μa ((BL ×ˢ Ib) ∩ lowSet) := by
    have hsub : BL ×ˢ Ib ⊆ (⋃ Q ∈ F, (BL ×ˢ Ib) ∩ incCell t₀ δ Q) ∪ ((BL ×ˢ Ib) ∩ lowSet) := by
      intro p hp
      obtain ⟨Q, hQ, hpQ⟩ := hcellQ p hp
      by_cases hQF : Q ∈ F
      · exact Or.inl (mem_biUnion hQF ⟨hp, hpQ⟩)
      · right
        refine ⟨hp, ?_⟩
        have hlt : lamG Q < ENNReal.ofReal (c₀ * δ ^ 2) := by
          simp only [hF, Finset.mem_filter, not_and, not_le] at hQF
          exact hQF hQ
        show lam (gridSquare δ (obsL a p).1 ×ˢ {(obsL a p).2}) < ENNReal.ofReal (c₀ * δ ^ 2)
        refine lt_of_le_of_lt ?_ hlt
        have hgs : gridSquare δ (obsL a p).1 = {z | z 0 ∈ tCell t₀ δ Q.1 ∧ z 1 ∈ yCell δ Q.2} := by
          rw [ht₀]
          exact gridSquare_obs_eq hδ j₀ Q.1 Q.2 hpQ.1 hpQ.2
        have hmeasG : MeasurableSet (gridSquare δ (obsL a p).1 ×ˢ {(obsL a p).2}) :=
          (measurableSet_gridSquare δ _).prod (measurableSet_singleton _)
        rw [← hlaw, Measure.map_apply (measurable_obsL a) hmeasG]
        apply measure_mono
        intro p' hp'
        simp only [mem_preimage, mem_prod, hgs, mem_ofPred_eq, mem_singleton_iff] at hp'
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · simpa [obsL] using hp'.1.1
        · simpa [obsL] using hp'.1.2
        · show ⌊hidden p'.1 p'.2 / a⌋ ∈ Icc m₁ m₂
          have h2 : ⌊hidden p'.1 p'.2 / a⌋ = ⌊hidden p.1 p.2 / a⌋ := by
            simpa [obsL] using hp'.2
          rw [h2]
          exact hwin p.1 hp.1 p.2 hp.2
    calc μa (BL ×ˢ Ib) ≤ μa ((⋃ Q ∈ F, (BL ×ˢ Ib) ∩ incCell t₀ δ Q) ∪ ((BL ×ˢ Ib) ∩ lowSet)) :=
          measure_mono hsub
      _ ≤ μa (⋃ Q ∈ F, (BL ×ˢ Ib) ∩ incCell t₀ δ Q) + μa ((BL ×ˢ Ib) ∩ lowSet) :=
          measure_union_le _ _
      _ ≤ ∑ Q ∈ F, μa ((BL ×ˢ Ib) ∩ incCell t₀ δ Q) + μa ((BL ×ˢ Ib) ∩ lowSet) := by
          gcongr
          exact measure_biUnion_finset_le _ _
  -- (c) counting good cells
  have hcount : (F.card : ℝ) * (c₀ * δ ^ 2) ≤ (μa strip).toReal := by
    have hle : ∑ Q ∈ F, lamG Q ≤ μa strip := by
      rw [hlamG]
      rw [← measure_biUnion_finset]
      · apply measure_mono
        intro p hp
        simp only [mem_iUnion] at hp
        obtain ⟨Q, hQF, hpQ, hpw⟩ := hp
        have hQidx : Q ∈ idx := (Finset.mem_filter.mp hQF).1
        have hQR : Q.1 < R := by
          simp only [hidx, Finset.mem_product, Finset.mem_range] at hQidx; exact hQidx.1
        refine ⟨?_, hpw⟩
        have := tCell_subset (t₀ := t₀) hδ hQR hpQ.1
        refine ⟨this.1, ?_⟩
        have h2 : p.2 < t₀ + (Q.1 + 1) * δ := hpQ.1.2
        have : ((Q.1 : ℝ) + 1) ≤ R := by exact_mod_cast hQR
        rw [hq]; nlinarith
      · intro Q _ Q' _ hQQ'
        exact Disjoint.mono inter_subset_left inter_subset_left (incCell_disjoint hδ hQQ')
      · intro Q _
        exact (measurableSet_incCell t₀ δ Q).inter hwinm
    have hstripfin : μa strip ≠ ⊤ := hfinBlock _ (fun p hp => ⟨mem_univ _, hp.1⟩)
    have hge : (F.card : ℝ≥0∞) * ENNReal.ofReal (c₀ * δ ^ 2) ≤ ∑ Q ∈ F, lamG Q := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun Q hQ => (Finset.mem_filter.mp hQ).2
    have := hge.trans hle
    have h2 : ((F.card : ℝ≥0∞) * ENNReal.ofReal (c₀ * δ ^ 2)).toReal ≤ (μa strip).toReal :=
      ENNReal.toReal_mono hstripfin this
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by positivity)] at h2
  -- (d) collision bound for the good cells
  set G : ℕ × ℤ → ℝ≥0∞ := fun Q => ∫⁻ l, cellTime (fun l : Coeff => l.2 0) (fun l => l.2 1)
    (tCell t₀ δ Q.1) (yCell δ Q.2) l ∂(ν.restrict BL) with hG
  have hxle : ∀ Q, μa ((BL ×ˢ Ib) ∩ incCell t₀ δ Q) ≤ G Q := fun Q =>
    incCell_mass_le ν E BL hBL Ib hIbm t₀ δ Q
  have hsumG : ∑ Q ∈ F, G Q ^ 2 ≤ ENNReal.ofReal δ * (ν.restrict BL) univ *
      ENNReal.ofReal (C₁ * δ) := by
    refine le_trans ?_ hcoll
    calc ∑ Q ∈ F, G Q ^ 2 ≤ ∑ Q ∈ idx, G Q ^ 2 :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = ∑ i ∈ Finset.range R, ∑ i' ∈ Finset.Icc (-Y' - 1) Y', G (i, i') ^ 2 := by
          rw [hidx, Finset.sum_product]
      _ ≤ ∑ i ∈ Finset.range R, ∑' i' : ℤ, G (i, i') ^ 2 := by
          gcongr with i hi
          exact ENNReal.sum_le_tsum _
  -- (e) long trajectories
  have hlongBL : ENNReal.ofReal (φ₀ * q) * ν BL ≤ μa (BL ×ˢ Ib) :=
    prior_le_of_long ν E hE BL hBL Ib hIbm hlong
  -- pass to reals
  have hYfin : μa (BL ×ˢ Ib) ≠ ⊤ := hfinBlock _ (prod_mono (subset_univ _) subset_rfl)
  have hxfin : ∀ Q, μa ((BL ×ˢ Ib) ∩ incCell t₀ δ Q) ≠ ⊤ := fun Q =>
    hfinBlock _ (inter_subset_left.trans (prod_mono (subset_univ _) subset_rfl))
  have hZfin : μa ((BL ×ˢ Ib) ∩ lowSet) ≠ ⊤ :=
    hfinBlock _ (inter_subset_left.trans (prod_mono (subset_univ _) subset_rfl))
  set Yr := (μa (BL ×ˢ Ib)).toReal with hYr
  set Zr := (μa ((BL ×ˢ Ib) ∩ lowSet)).toReal with hZr
  set Mr := (μa strip).toReal with hMr
  set x : ℕ × ℤ → ℝ := fun Q => (μa ((BL ×ˢ Ib) ∩ incCell t₀ δ Q)).toReal with hx
  set Xr := ∑ Q ∈ F, x Q with hXr
  have hνBLfin : ν BL ≠ ⊤ := measure_ne_top _ _
  have hYsplit : Yr ≤ Xr + Zr := by
    have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨ENNReal.sum_ne_top.mpr fun Q _ => hxfin Q, hZfin⟩) hsplit
    rwa [ENNReal.toReal_add (ENNReal.sum_ne_top.mpr fun Q _ => hxfin Q) hZfin,
      ENNReal.toReal_sum fun Q _ => hxfin Q] at h
  have hGfin : ∀ Q ∈ F, G Q ≠ ⊤ := by
    intro Q _
    rw [hG]
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := δ))
      (measure_ne_top (ν.restrict BL) univ)) ?_
    calc ∫⁻ l, cellTime (fun l : Coeff => l.2 0) (fun l => l.2 1) (tCell t₀ δ Q.1)
          (yCell δ Q.2) l ∂(ν.restrict BL)
        ≤ ∫⁻ _l, ENNReal.ofReal δ ∂(ν.restrict BL) := by
          apply lintegral_mono
          intro l
          exact (measure_mono (fun t ht => ht.1)).trans (volume_tCell hδ Q.1).le
      _ = ENNReal.ofReal δ * (ν.restrict BL) univ := lintegral_const _
  have hsq_x : ∑ Q ∈ F, x Q ^ 2 ≤ δ * (ν BL).toReal * (C₁ * δ) := by
    have h1 : ∑ Q ∈ F, x Q ^ 2 ≤ ∑ Q ∈ F, (G Q).toReal ^ 2 := by
      apply Finset.sum_le_sum
      intro Q hQ
      have := ENNReal.toReal_mono (hGfin Q hQ) (hxle Q)
      exact pow_le_pow_left₀ ENNReal.toReal_nonneg this 2
    have h2 : ∑ Q ∈ F, (G Q).toReal ^ 2 = (∑ Q ∈ F, G Q ^ 2).toReal := by
      rw [ENNReal.toReal_sum (fun Q hQ => ENNReal.pow_ne_top (hGfin Q hQ))]
      simp [ENNReal.toReal_pow]
    have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (measure_ne_top _ _)) ENNReal.ofReal_ne_top) hsumG
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hδ.le,
      ENNReal.toReal_ofReal (by positivity), Measure.restrict_apply_univ] at h3
    linarith
  have hνBL : φ₀ * q * (ν BL).toReal ≤ Yr := by
    have h := ENNReal.toReal_mono hYfin hlongBL
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h
  have hcard : (F.card : ℝ) ≤ Mr / (c₀ * δ ^ 2) := by
    rw [le_div_iff₀ (by positivity)]; exact hcount
  have hXsq : Xr ^ 2 ≤ (C₁ / (c₀ * φ₀ * q) * Mr) * Yr := by
    have hCS := sq_sum_le_card_mul_sum_sq F x
    have hM0 : 0 ≤ Mr := ENNReal.toReal_nonneg
    have hsx0 : 0 ≤ ∑ Q ∈ F, x Q ^ 2 := Finset.sum_nonneg fun Q _ => sq_nonneg _
    calc Xr ^ 2 ≤ (F.card : ℝ) * ∑ Q ∈ F, x Q ^ 2 := hCS
      _ ≤ Mr / (c₀ * δ ^ 2) * (δ * (ν BL).toReal * (C₁ * δ)) := by
          apply mul_le_mul hcard hsq_x hsx0 (by positivity)
      _ = C₁ / c₀ * Mr * (ν BL).toReal := by field_simp
      _ ≤ C₁ / c₀ * Mr * (Yr / (φ₀ * q)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [le_div_iff₀ (by positivity)]; linarith
      _ = (C₁ / (c₀ * φ₀ * q) * Mr) * Yr := by field_simp
  have hX0 : 0 ≤ Xr := Finset.sum_nonneg fun Q _ => ENNReal.toReal_nonneg
  have hres := quadratic_absorb hX0 ENNReal.toReal_nonneg (by positivity) hYsplit hXsq
  calc Yr ≤ 4 * (C₁ / (c₀ * φ₀ * q) * Mr) + 2 * Zr := hres
    _ = _ := rfl

end Submission.Obl.k4_scalar_initial_true_horizon
