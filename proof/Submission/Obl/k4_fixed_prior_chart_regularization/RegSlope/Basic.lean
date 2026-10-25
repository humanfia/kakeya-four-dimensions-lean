-- Adapted from LOT tree g-oai-074, obligation o245, session x0854, commit 3602b8f657fd9f9293587a9dd3e1bdba2451d373.
-- Source: Submission/Obl/k4_horizontal_interior_parameter_bootstrap/RegSlope/Basic.lean.
import Submission.Obl.k4_fixed_prior_chart_regularization.Regularization

/-!
# Slope regularization: basic tools

Floors at one width, the removal of short trajectories, and the selection of one bin per cell
followed by a residue class of cells (`select_bin_class`): a measurable cell map `Z` into
`ℤ⁴` and a bin map `g` with at most `P` bins present in each cell give a subset of mass
`≥ μ A / (16 P)` on which points of neighbouring cells lie in one cell and one bin.
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_fixed_prior_chart_regularization.RegSlope

open FirstJet

theorem abs_sub_lt_of_floor_eq {a b s : ℝ} (hs : 0 < s) (h : ⌊a / s⌋ = ⌊b / s⌋) :
    |a - b| < s := by
  have h1 := Int.floor_le (a / s)
  have h2 := Int.lt_floor_add_one (a / s)
  have h3 := Int.floor_le (b / s)
  have h4 := Int.lt_floor_add_one (b / s)
  rw [h] at h1 h2
  have : |a / s - b / s| < 1 := by rw [abs_lt]; constructor <;> linarith
  rwa [← sub_div, abs_div, abs_of_pos hs, div_lt_one hs] at this

theorem floor_sub_le_one {a b s : ℝ} (hs : 0 < s) (h : |a - b| ≤ s) :
    |⌊a / s⌋ - ⌊b / s⌋| ≤ 1 := by
  have h1 := Int.floor_le (a / s)
  have h2 := Int.lt_floor_add_one (a / s)
  have h3 := Int.floor_le (b / s)
  have h4 := Int.lt_floor_add_one (b / s)
  have hab : |a / s - b / s| ≤ 1 := by
    rw [← sub_div, abs_div, abs_of_pos hs, div_le_one hs]; exact h
  rw [abs_le] at hab
  have e1 : ((⌊a / s⌋ - ⌊b / s⌋ : ℤ) : ℝ) > -2 := by push_cast; linarith [hab.1]
  have e2 : ((⌊a / s⌋ - ⌊b / s⌋ : ℤ) : ℝ) < 2 := by push_cast; linarith [hab.2]
  have e1' : (⌊a / s⌋ - ⌊b / s⌋ : ℤ) > -2 := by exact_mod_cast e1
  have e2' : (⌊a / s⌋ - ⌊b / s⌋ : ℤ) < 2 := by exact_mod_cast e2
  rw [abs_le]; constructor <;> omega

theorem floor_ne_of_le_abs {a b s : ℝ} (hs : 0 < s) (h : s ≤ |a - b|) : ⌊a / s⌋ ≠ ⌊b / s⌋ :=
  fun he => absurd (abs_sub_lt_of_floor_eq hs he) (not_lt.mpr h)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The labeled duration of a trajectory. -/
def duration (E : Set (Ω × ℝ)) (l : Ω) : ENNReal := volume {t | (l, t) ∈ E}

theorem measurable_duration {E : Set (Ω × ℝ)} (hE : MeasurableSet E) :
    Measurable (duration E) :=
  measurable_measure_prodMk_left hE

/-- The trajectories of labeled duration `≥ δ`. -/
def longLabels (E : Set (Ω × ℝ)) (δ : ℝ) : Set Ω := {l | ENNReal.ofReal δ ≤ duration E l}

theorem measurableSet_longLabels {E : Set (Ω × ℝ)} (hE : MeasurableSet E) (δ : ℝ) :
    MeasurableSet (longLabels E δ) :=
  measurableSet_le measurable_const (measurable_duration hE)

/-- Removing the trajectories of labeled duration `< δ` costs at most `δ`. -/
theorem short_labels_mass {ν : Measure Ω} [IsProbabilityMeasure ν] {E : Set (Ω × ℝ)}
    (hE : MeasurableSet E) (δ : ℝ) :
    (ν.prod volume) (E ∩ (longLabels E δ)ᶜ ×ˢ univ) ≤ ENNReal.ofReal δ := by
  have hΛ := measurableSet_longLabels hE δ
  rw [Measure.prod_apply (hE.inter (hΛ.compl.prod MeasurableSet.univ))]
  calc ∫⁻ l, volume (Prod.mk l ⁻¹' (E ∩ (longLabels E δ)ᶜ ×ˢ univ)) ∂ν
      ≤ ∫⁻ _l, ENNReal.ofReal δ ∂ν := by
        refine lintegral_mono (fun l => ?_)
        by_cases hl : l ∈ longLabels E δ
        · have : Prod.mk l ⁻¹' (E ∩ (longLabels E δ)ᶜ ×ˢ univ) = ∅ := by
            ext t; simp [hl]
          rw [this, measure_empty]; exact bot_le
        · have hsl : Prod.mk l ⁻¹' (E ∩ (longLabels E δ)ᶜ ×ˢ univ) = {t | (l, t) ∈ E} := by
            ext t; simp [hl]
          rw [hsl]
          simp only [longLabels, mem_setOf_eq, not_le] at hl
          exact hl.le
    _ = ENNReal.ofReal δ := by rw [lintegral_const, measure_univ, mul_one]

/-- A countable partition of a measurable set by the fibres of a measurable map. -/
theorem measure_eq_tsum_fibres {X ι : Type*} [MeasurableSpace X] [MeasurableSpace ι]
    [Countable ι] [MeasurableSingletonClass ι] (μ : Measure X) {B : Set X}
    (hB : MeasurableSet B) {Z : X → ι} (hZ : Measurable Z) :
    μ B = ∑' z, μ (B ∩ Z ⁻¹' {z}) := by
  rw [← measure_iUnion]
  · congr 1; ext x; simp
  · intro i j hij
    exact Set.disjoint_left.mpr fun x hx hx' => hij (hx.2.symm.trans hx'.2)
  · intro z; exact hB.inter (hZ (measurableSet_singleton z))

/-- One bin per cell: if at most `P` bins occur in every cell, keeping in each cell the
heaviest bin keeps a `1/P` fraction of the mass. -/
theorem select_bin {X ι : Type*} [MeasurableSpace X] [MeasurableSpace ι] [Countable ι]
    [MeasurableSingletonClass ι] (μ : Measure X) {A : Set X} (hA : MeasurableSet A)
    {Z : X → ι} (hZ : Measurable Z) {g : X → ℤ} (hg : Measurable g) (P : ℕ)
    (hP : ∀ z, ∃ T : Finset ℤ, T.card ≤ P ∧ ∀ x ∈ A, Z x = z → g x ∈ T) :
    ∃ A₁ ⊆ A, MeasurableSet A₁ ∧ μ A ≤ P * μ A₁ ∧
      ∀ x ∈ A₁, ∀ x' ∈ A₁, Z x = Z x' → g x = g x' := by
  classical
  choose T hTcard hTmem using hP
  -- the heaviest bin of each cell
  have hbest : ∀ z, ∃ b : ℤ, ∀ b' ∈ T z,
      μ (A ∩ Z ⁻¹' {z} ∩ g ⁻¹' {b'}) ≤ μ (A ∩ Z ⁻¹' {z} ∩ g ⁻¹' {b}) := by
    intro z
    rcases (T z).eq_empty_or_nonempty with h | h
    · exact ⟨0, by simp [h]⟩
    · obtain ⟨b, -, hb⟩ := (T z).exists_max_image (fun b => μ (A ∩ Z ⁻¹' {z} ∩ g ⁻¹' {b})) h
      exact ⟨b, hb⟩
  choose best hbest using hbest
  set A₁ : Set X := A ∩ ⋃ z, Z ⁻¹' {z} ∩ g ⁻¹' {best z} with hA₁def
  have hA₁m : MeasurableSet A₁ :=
    hA.inter (MeasurableSet.iUnion fun z =>
      (hZ (measurableSet_singleton z)).inter (hg (measurableSet_singleton _)))
  have hmem : ∀ x, x ∈ A₁ ↔ x ∈ A ∧ g x = best (Z x) := by
    intro x
    simp only [hA₁def, mem_inter_iff, mem_iUnion, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hx, z, hz, hgz⟩; exact ⟨hx, hz ▸ hgz⟩
    · rintro ⟨hx, hgx⟩; exact ⟨hx, Z x, rfl, hgx⟩
  refine ⟨A₁, inter_subset_left, hA₁m, ?_, ?_⟩
  · rw [measure_eq_tsum_fibres μ hA hZ, measure_eq_tsum_fibres μ hA₁m hZ,
      ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun z => ?_
    have hfib : A₁ ∩ Z ⁻¹' {z} = A ∩ Z ⁻¹' {z} ∩ g ⁻¹' {best z} := by
      ext x
      simp only [mem_inter_iff, hmem, mem_preimage, mem_singleton_iff]
      constructor
      · rintro ⟨⟨hx, hgx⟩, hz⟩; exact ⟨⟨hx, hz⟩, hz ▸ hgx⟩
      · rintro ⟨⟨hx, hz⟩, hgx⟩; exact ⟨⟨hx, hz ▸ hgx⟩, hz⟩
    rw [hfib]
    calc μ (A ∩ Z ⁻¹' {z}) ≤ μ (⋃ b ∈ T z, A ∩ Z ⁻¹' {z} ∩ g ⁻¹' {b}) := by
          apply measure_mono
          intro x hx
          simp only [mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff]
          exact ⟨g x, hTmem z x hx.1 hx.2, ⟨hx.1, hx.2⟩, rfl⟩
      _ ≤ ∑ b ∈ T z, μ (A ∩ Z ⁻¹' {z} ∩ g ⁻¹' {b}) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _b ∈ T z, μ (A ∩ Z ⁻¹' {z} ∩ g ⁻¹' {best z}) :=
          Finset.sum_le_sum fun b hb => hbest z b hb
      _ = (T z).card * μ (A ∩ Z ⁻¹' {z} ∩ g ⁻¹' {best z}) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ P * μ (A ∩ Z ⁻¹' {z} ∩ g ⁻¹' {best z}) := by
          gcongr; exact_mod_cast hTcard z
  · intro x hx x' hx' hZZ
    rw [(hmem x).1 hx |>.2, (hmem x').1 hx' |>.2, hZZ]

/-- A residue class of cells modulo two: points of neighbouring retained cells share their cell. -/
theorem select_class {X : Type*} [MeasurableSpace X] (μ : Measure X) {A : Set X}
    (hA : MeasurableSet A) {Z : X → Fin 4 → ℤ} (hZ : Measurable Z) :
    ∃ A₂ ⊆ A, MeasurableSet A₂ ∧ μ A ≤ 16 * μ A₂ ∧
      ∀ x ∈ A₂, ∀ x' ∈ A₂, (∀ i, |Z x i - Z x' i| ≤ 1) → Z x = Z x' := by
  classical
  set cls : X → Fin 4 → ℤ := fun x i => Z x i % 2 with hcls
  have hclsm : Measurable cls := by
    have : Measurable (fun v : Fin 4 → ℤ => fun i => v i % 2) := measurable_of_countable _
    exact this.comp hZ
  set S : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => ({0, 1} : Finset ℤ) with hSdef
  have hScard : S.card = 16 := by
    rw [hSdef, Fintype.card_piFinset]; simp
  have hclsS : ∀ x, cls x ∈ S := by
    intro x
    rw [hSdef, Fintype.mem_piFinset]
    intro i
    simp only [hcls, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hne : S.Nonempty := Finset.card_pos.mp (by rw [hScard]; norm_num)
  obtain ⟨σ, -, hσ⟩ := S.exists_max_image (fun σ => μ (A ∩ cls ⁻¹' {σ})) hne
  refine ⟨A ∩ cls ⁻¹' {σ}, inter_subset_left, hA.inter (hclsm (measurableSet_singleton σ)),
    ?_, ?_⟩
  · calc μ A ≤ μ (⋃ τ ∈ S, A ∩ cls ⁻¹' {τ}) :=
          measure_mono fun x hx => mem_biUnion (hclsS x) ⟨hx, rfl⟩
      _ ≤ ∑ τ ∈ S, μ (A ∩ cls ⁻¹' {τ}) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _τ ∈ S, μ (A ∩ cls ⁻¹' {σ}) := Finset.sum_le_sum fun τ hτ => hσ τ hτ
      _ = 16 * μ (A ∩ cls ⁻¹' {σ}) := by rw [Finset.sum_const, nsmul_eq_mul, hScard]; norm_num
  · intro x hx x' hx' hnear
    funext i
    have h1 : cls x = σ := hx.2
    have h2 : cls x' = σ := hx'.2
    have h3 : Z x i % 2 = Z x' i % 2 := by
      have := congrFun (h1.trans h2.symm) i
      simpa [hcls] using this
    have h4 := hnear i
    rw [abs_le] at h4
    omega

/-- One bin per cell and a residue class of cells. -/
theorem select_bin_class {X : Type*} [MeasurableSpace X] (μ : Measure X) {A : Set X}
    (hA : MeasurableSet A) {Z : X → Fin 4 → ℤ} (hZ : Measurable Z) {g : X → ℤ}
    (hg : Measurable g) (P : ℕ)
    (hP : ∀ z, ∃ T : Finset ℤ, T.card ≤ P ∧ ∀ x ∈ A, Z x = z → g x ∈ T) :
    ∃ A' ⊆ A, MeasurableSet A' ∧ μ A ≤ 16 * P * μ A' ∧
      ∀ x ∈ A', ∀ x' ∈ A', (∀ i, |Z x i - Z x' i| ≤ 1) → g x = g x' := by
  obtain ⟨A₁, hA₁A, hA₁m, hA₁μ, hA₁g⟩ := select_bin μ hA hZ hg P hP
  obtain ⟨A₂, hA₂A, hA₂m, hA₂μ, hA₂Z⟩ := select_class μ hA₁m hZ
  refine ⟨A₂, hA₂A.trans hA₁A, hA₂m, ?_, fun x hx x' hx' h =>
    hA₁g x (hA₂A hx) x' (hA₂A hx') (hA₂Z x hx x' hx' h)⟩
  calc μ A ≤ P * μ A₁ := hA₁μ
    _ ≤ P * (16 * μ A₂) := by gcongr
    _ = 16 * P * μ A₂ := by ring

end Submission.Obl.k4_fixed_prior_chart_regularization.RegSlope

end
