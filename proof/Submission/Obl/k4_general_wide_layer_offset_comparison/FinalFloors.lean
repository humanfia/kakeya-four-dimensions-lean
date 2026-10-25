import Submission.Lib.K4FinalLawSelection

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Renew all colors against one final original submeasure. Every surviving
entry has positive current mass and its reference floor under that same law. -/
theorem simultaneous_colored_floors {Ω C : Type*} [MeasurableSpace Ω] [Fintype C]
    (n : C → ℕ) (E : ∀ a, Fin (n a) → Set Ω)
    (hE : ∀ a i, MeasurableSet (E a i))
    (w : ∀ a, Fin (n a) → ℝ≥0∞) (μ : Measure Ω)
    (hcover : ∀ a, ∀ᵐ p ∂μ, ∃ i, p ∈ E a i) :
    ∃ (lam : Measure Ω) (keep : ∀ a, Finset (Fin (n a))),
      lam ≤ μ ∧ μ univ ≤ lam univ + ∑ a, ∑ i, w a i ∧
      (∀ a i, i ∈ keep a → 0 < lam (E a i) ∧ w a i ≤ lam (E a i)) ∧
      (∀ a, ∀ᵐ p ∂lam, ∃ i ∈ keep a, p ∈ E a i) := by
  classical
  let I := Σ a : C, Fin (n a)
  obtain ⟨lam, hlam, hloss, hfloors⟩ :=
    Submission.Lib.K4FinalLawSelection.exists_simultaneous_floor_measure
      (Finset.univ : Finset I) (fun i => E i.1 i.2) (fun i => hE i.1 i.2)
      (fun i => w i.1 i.2) μ
  let keep : ∀ a, Finset (Fin (n a)) := fun a =>
    Finset.univ.filter (fun i => 0 < lam (E a i))
  refine ⟨lam, keep, hlam, ?_, ?_, ?_⟩
  · simpa only [I, Fintype.sum_sigma] using hloss
  · intro a i hi
    have hpos := (Finset.mem_filter.mp hi).2
    refine ⟨hpos, ?_⟩
    rcases hfloors ⟨a, i⟩ (Finset.mem_univ _) with hz | hh
    · exact (hpos.ne' hz).elim
    · exact hh
  · intro a
    have htrace : ∀ᵐ p ∂lam, ∀ i : Fin (n a), p ∈ E a i → 0 < lam (E a i) := by
      apply ae_all_iff.mpr
      intro i
      by_cases hi : lam (E a i) = 0
      · have hn : ∀ᵐ p ∂lam, p ∉ E a i := by
          rw [ae_iff]
          simpa only [not_not, Set.ofPred_mem_eq] using hi
        filter_upwards [hn] with p hp
        exact fun hpi => (hp hpi).elim
      · exact Filter.Eventually.of_forall fun _ _ => pos_iff_ne_zero.mpr hi
    filter_upwards [(hcover a).filter_mono (ae_mono hlam), htrace] with p hp ht
    obtain ⟨i, hi⟩ := hp
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht i hi⟩, hi⟩

/-- A bounded deletion cost retains half of an original positive mass floor. -/
theorem half_mass_of_loss_budget {Ω : Type*} [MeasurableSpace Ω]
    (μ lam : Measure Ω) [IsFiniteMeasure μ] (hlam : lam ≤ μ)
    {mass loss : ℝ} (hmass : 0 ≤ mass) (hloss : 0 ≤ loss)
    (hm : ENNReal.ofReal mass ≤ μ univ)
    (hbudget : μ univ ≤ lam univ + ENNReal.ofReal loss)
    (hsmall : loss ≤ mass / 2) :
    ENNReal.ofReal (mass / 2) ≤ lam univ := by
  have hlamtop : lam univ ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top μ _) (hlam univ)
  have hμreal : mass ≤ (μ univ).toReal := by
    simpa only [ENNReal.toReal_ofReal hmass] using ENNReal.toReal_mono
      (measure_ne_top μ univ) hm
  have hreal : (μ univ).toReal ≤ (lam univ).toReal + loss := by
    have hfin : lam univ + ENNReal.ofReal loss ≠ ⊤ := by
      exact ENNReal.add_ne_top.mpr ⟨hlamtop, ENNReal.ofReal_ne_top⟩
    have hh := ENNReal.toReal_mono hfin hbudget
    simpa only [ENNReal.toReal_add hlamtop ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hloss] using hh
  calc
    ENNReal.ofReal (mass / 2) ≤ ENNReal.ofReal (lam univ).toReal :=
      ENNReal.ofReal_le_ofReal (by linarith)
    _ = lam univ := ENNReal.ofReal_toReal hlamtop

/-- Two colors with bounded original reference sums can be pruned together.
The final measure keeps half the incoming mass and supplies every retained
entry with its own original reference divided by `4 * H * R`. -/
theorem two_color_final_floors {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (n : Fin 2 → ℕ) (E : ∀ a, Fin (n a) → Set Ω)
    (hE : ∀ a i, MeasurableSet (E a i))
    (ref : ∀ a, Fin (n a) → ℝ≥0∞)
    (hcover : ∀ a, ∀ᵐ p ∂μ, ∃ i, p ∈ E a i)
    {H R : ℝ} (hH : 0 < H) (hR : 0 < R)
    (hmass : ENNReal.ofReal H⁻¹ ≤ μ univ)
    (href : ∀ a, (∑ i, ref a i) ≤ ENNReal.ofReal R) :
    ∃ (lam : Measure Ω) (keep : ∀ a, Finset (Fin (n a))),
      lam ≤ μ ∧ ENNReal.ofReal ((2 * H)⁻¹) ≤ lam univ ∧
      (∀ a i, i ∈ keep a → 0 < lam (E a i) ∧
        ENNReal.ofReal ((4 * H * R)⁻¹) * ref a i ≤ lam (E a i)) ∧
      (∀ a, (∑ i ∈ keep a, ref a i) ≤ ENNReal.ofReal R) ∧
      (∀ a, ∀ᵐ p ∂lam, ∃ i ∈ keep a, p ∈ E a i) := by
  classical
  let δ : ℝ := (4 * H * R)⁻¹
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hscaled : (∑ a, ∑ i, ENNReal.ofReal δ * ref a i) ≤
      ENNReal.ofReal (H⁻¹ / 2) := by
    simp_rw [← Finset.mul_sum]
    calc
      _ = ENNReal.ofReal δ * (∑ a, ∑ i, ref a i) := by rw [Finset.mul_sum]
      _ ≤ ENNReal.ofReal δ * (ENNReal.ofReal R + ENNReal.ofReal R) := by
        apply mul_le_mul_right _ _
        rw [Fin.sum_univ_two]
        exact add_le_add (href 0) (href 1)
      _ = ENNReal.ofReal (H⁻¹ / 2) := by
        rw [← ENNReal.ofReal_add hR.le hR.le, ← ENNReal.ofReal_mul hδ]
        congr 1
        dsimp [δ]
        field_simp
        ring
  obtain ⟨lam, keep, hlam, hloss, hfloor, hcov⟩ :=
    simultaneous_colored_floors n E hE (fun a i => ENNReal.ofReal δ * ref a i) μ hcover
  have hm : ENNReal.ofReal (H⁻¹ / 2) ≤ lam univ :=
    half_mass_of_loss_budget μ lam hlam (by positivity) (by positivity) hmass
      (hloss.trans (add_le_add le_rfl hscaled)) le_rfl
  refine ⟨lam, keep, hlam, ?_, hfloor, ?_, hcov⟩
  · convert hm using 1
    congr 1
    field_simp
  · intro a
    exact (Finset.sum_le_univ_sum_of_nonneg (fun _ => zero_le)).trans (href a)

end

end Submission.Obl.k4_general_wide_layer_offset_comparison
