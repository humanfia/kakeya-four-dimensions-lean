/- Adapted from: here:o223
   (x0927; countable-cell threshold extends x0775). -/
import Mathlib
import Submission.Lib.K4ContactAffine.VelocityBins

/-!+# Original cell caps and a region with three actual witnesses

The source events may overlap and the cell family may be countably infinite.
The mass threshold is charged to cell volume, retaining the original joint
velocity numerator. This avoids constructing a finite table of occupied codes.

The threshold argument extends the finite-cell construction of session x0775,
`here:o223`, `OccupiedVelocityWitnesses.lean` (branch x0775, commit 8db598e6).
-/

namespace Submission.Lib.K4ContactAffine

open Set MeasureTheory

/-- Three actual witnesses in any prescribed conull set follow from the
original floor-bin ceilings. -/
theorem three_witnesses_from_bins {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A G : Set Ω) (v : Ω → ℝ) {η : ℝ} (hη : 0 < η)
    (cap : ENNReal)
    (hbin : ∀ a : ℤ, μ {p | p ∈ A ∧ ⌊v p / η⌋ = a} ≤ cap)
    (hG : ∀ᵐ p ∂μ, p ∈ G) (hmass : 6 * cap < μ A) :
    ∃ p₀ p₁ p₂ : Ω, (p₀ ∈ A ∧ p₀ ∈ G) ∧ (p₁ ∈ A ∧ p₁ ∈ G) ∧
      (p₂ ∈ A ∧ p₂ ∈ G) ∧ η < |v p₀ - v p₁| ∧ η < |v p₀ - v p₂| ∧
        η < |v p₁ - v p₂| := by
  have hthin (w : ℝ) : μ ((A ∩ G) ∩ {p | |v p - w| ≤ η}) ≤ 3 * cap := by
    exact (measure_mono (show (A ∩ G) ∩ {p | |v p - w| ≤ η} ⊆
      A ∩ {p | |v p - w| ≤ η} from fun p hp => ⟨hp.1.1, hp.2⟩)).trans
      (interval_cap_of_floor_bin_cap
        μ A v hη cap hbin w)
  have hmass' : 3 * cap + 3 * cap < μ (A ∩ G) := by
    rw [measure_inter_conull (ae_iff.mp hG)]
    convert hmass using 1; ring
  obtain ⟨p₀, hp₀, p₁, hp₁, p₂, hp₂, h₀₁, h₀₂, h₁₂⟩ :=
    Submission.Lib.K4HorizontalCoercivity.exists_three_velocity_witnesses
      μ (A ∩ G) v η (3 * cap) hthin hmass'
  exact ⟨p₀, p₁, p₂, hp₀, hp₁, hp₂, h₀₁, h₀₂, h₁₂⟩

/-- A countable disjoint family of base cells with summable reference volume
has a measurable occupied region of volume at least `m/(2β)`. Each point of
that region has three actual good witnesses in its original source event.
Only the original pure and joint cell caps are used. -/
theorem occupied_region_of_countable_caps {Ω Y ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Y] [Countable ι]
    (μ : Measure Ω) (baseMeasure : Measure Y) (events : ι → Set Ω) (cells : ι → Set Y)
    (hdisj : Pairwise (fun i j => Disjoint (cells i) (cells j)))
    (hmeas : ∀ i, MeasurableSet (cells i))
    {m β V η : ℝ} (hm : 0 < m) (hβ : 0 < β) (hV : 0 < V) (hη : 0 < η)
    (hvol : ∑' i, baseMeasure (cells i) ≤ ENNReal.ofReal V)
    (hmass : ENNReal.ofReal m ≤ μ univ)
    (hcover : ∀ᵐ p ∂μ, ∃ i, p ∈ events i)
    (hcap : ∀ i, μ (events i) ≤ ENNReal.ofReal β * baseMeasure (cells i))
    (v : Ω → ℝ) (pmax : ENNReal)
    (hbin : ∀ (i : ι) (a : ℤ),
      μ {p | p ∈ events i ∧ ⌊v p / η⌋ = a} ≤
        ENNReal.ofReal β * baseMeasure (cells i) * pmax)
    (hsmall : 6 * ENNReal.ofReal β * pmax < ENNReal.ofReal (m / (2 * V)))
    (G : Set Ω) (hG : ∀ᵐ p ∂μ, p ∈ G) :
    ∃ E : Set Y, MeasurableSet E ∧ E ⊆ ⋃ i, cells i ∧
      ENNReal.ofReal (m / (2 * β)) ≤ baseMeasure E ∧
      ∀ x ∈ E, ∃ i, x ∈ cells i ∧ ∃ p₀ p₁ p₂ : Ω,
        (p₀ ∈ events i ∧ p₀ ∈ G) ∧ (p₁ ∈ events i ∧ p₁ ∈ G) ∧
        (p₂ ∈ events i ∧ p₂ ∈ G) ∧
        η < |v p₀ - v p₁| ∧ η < |v p₀ - v p₂| ∧ η < |v p₁ - v p₂| := by
  classical
  let τ := ENNReal.ofReal (m / (2 * V))
  let keep : ι → Prop := fun i => τ * baseMeasure (cells i) ≤ μ (events i) ∧ μ (events i) ≠ 0
  let part : ι → Set Y := fun i => if keep i then cells i else ∅
  let E : Set Y := ⋃ i, part i
  have hpart (i : ι) : MeasurableSet (part i) := by
    dsimp only [part]
    split_ifs
    · exact hmeas i
    · exact MeasurableSet.empty
  have hparts : Pairwise (fun i j => Disjoint (part i) (part j)) := by
    intro i j hij
    dsimp only [part]
    split_ifs
    · exact hdisj hij
    all_goals simp
  have hEvol : baseMeasure E = ∑' i, baseMeasure (part i) := measure_iUnion hparts hpart
  have hτV : τ * ENNReal.ofReal V = ENNReal.ofReal (m / 2) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ m / (2 * V))]
    congr 1
    field_simp
  have htotal : ENNReal.ofReal m ≤ ENNReal.ofReal β * baseMeasure E + ENNReal.ofReal (m / 2) := by
    calc
      ENNReal.ofReal m ≤ μ univ := hmass
      _ ≤ μ (⋃ i, events i) := by
        apply measure_mono_ae
        filter_upwards [hcover] with p hp
        exact fun _ => mem_iUnion.mpr hp
      _ ≤ ∑' i, μ (events i) := measure_iUnion_le events
      _ ≤ ∑' i, (ENNReal.ofReal β * baseMeasure (part i) + τ * baseMeasure (cells i)) := by
        apply ENNReal.tsum_le_tsum
        intro i
        by_cases hi : keep i
        · rw [show part i = cells i from ite_eq_left hi]
          exact (hcap i).trans (le_add_of_nonneg_right (bot_le))
        · rw [show part i = ∅ from ite_eq_right hi, measure_empty, mul_zero, zero_add]
          by_cases hz : μ (events i) = 0
          · simp only [hz, zero_le]
          · exact (lt_of_not_ge (fun hle => hi ⟨hle, hz⟩)).le
      _ = ENNReal.ofReal β * (∑' i, baseMeasure (part i)) + τ * (∑' i, baseMeasure (cells i)) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      _ ≤ ENNReal.ofReal β * baseMeasure E + ENNReal.ofReal (m / 2) := by
        rw [← hEvol, ← hτV]
        exact add_le_add le_rfl (mul_le_mul' le_rfl hvol)
  have hhalf : ENNReal.ofReal (m / 2) ≤ ENNReal.ofReal β * baseMeasure E := by
    apply ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top
    calc
      ENNReal.ofReal (m / 2) + ENNReal.ofReal (m / 2) = ENNReal.ofReal m := by
        rw [← ENNReal.ofReal_add (by positivity : 0 ≤ m / 2) (by positivity : 0 ≤ m / 2)]
        congr 1
        ring
      _ ≤ _ := htotal
  have hvolume : ENNReal.ofReal (m / (2 * β)) ≤ baseMeasure E := by
    rw [show m / (2 * β) = (m / 2) / β by ring, ENNReal.ofReal_div_of_pos hβ,
      ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hβ)) ENNReal.ofReal_ne_top]
    simpa only [mul_comm] using hhalf
  refine ⟨E, MeasurableSet.iUnion hpart, ?_, hvolume, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    by_cases hk : keep i
    · exact mem_iUnion.mpr ⟨i, by simpa only [part, ite_eq_left hk] using hi⟩
    · simp only [part, ite_eq_right hk, mem_empty_iff_false] at hi
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    have hk : keep i := by
      by_contra hn
      simp only [part, ite_eq_right hn, mem_empty_iff_false] at hi
    have hxi : x ∈ cells i := by simpa only [part, ite_eq_left hk] using hi
    obtain ⟨hfloor, hnonzero⟩ := hk
    have hv0 : baseMeasure (cells i) ≠ 0 := by
      intro hv
      exact hnonzero (le_antisymm (by simpa only [hv, mul_zero] using hcap i) bot_le)
    have hvtop : baseMeasure (cells i) ≠ ⊤ := by
      exact ne_of_lt ((ENNReal.le_tsum i).trans hvol |>.trans_lt ENNReal.ofReal_lt_top)
    let cap := ENNReal.ofReal β * baseMeasure (cells i) * pmax
    have hheavy : 6 * cap < μ (events i) := by
      calc
        _ = (6 * ENNReal.ofReal β * pmax) * baseMeasure (cells i) := by dsimp [cap]; ring
        _ < τ * baseMeasure (cells i) := (ENNReal.mul_lt_mul_iff_left hv0 hvtop).mpr hsmall
        _ ≤ _ := hfloor
    obtain ⟨p₀, p₁, p₂, hp₀, hp₁, hp₂, h₀₁, h₀₂, h₁₂⟩ :=
      three_witnesses_from_bins μ (events i) G v hη cap (hbin i) hG hheavy
    exact ⟨i, hxi, p₀, p₁, p₂, hp₀, hp₁, hp₂, h₀₁, h₀₂, h₁₂⟩

end Submission.Lib.K4ContactAffine
