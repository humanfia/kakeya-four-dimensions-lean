-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceParts

/-!
# The unpruned prepared set of a parent

From any measurable set `G` (e.g. the residual of the parent's world, cut by density masks),
`exists_prepared_set` keeps its part in the open block of a parent `a`, off the finitely many
dyadic block endpoints of the path: the fields `S_meas`, `S_open`, `S_end` of `SourceParts`,
losing nothing of `G ∩ counted a`. `packet_le_counted` compares the parent packet with its
counted set (`packet ≤ κ² counted`), so a density of `G` in the counted set gives the room
`m τ packet(a) < mass(S₁)` of `SourceParts.mass`.

Written by x0891 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set

noncomputable section

section Path

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

/-- The dyadic block endpoints of all labels of a path. -/
def PathData.blockEnds {W : ℕ} (p : PathData W) : Set ℝ :=
  ⋃ b : Fin p.C, {(p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b),
    ((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)}

omit hp in
theorem PathData.blockEnds_finite {W : ℕ} (p : PathData W) : p.blockEnds.Finite :=
  Set.finite_iUnion fun _ => (Set.finite_singleton _).insert _

omit hp in
/-- Incidences at block endpoint times are null. -/
theorem blockEnds_null {W : ℕ} (p : PathData W) (μ₀ : Measure Trajectory) [IsFiniteMeasure μ₀] :
    (μ₀.prod volume) (univ ×ˢ p.blockEnds) = 0 := by
  rw [Measure.prod_prod, (p.blockEnds_finite).measure_zero, mul_zero]

include hp

/-- **The unpruned prepared set of a parent.** -/
theorem exists_prepared_set (a : Fin p.C) {G : Set Incidence} (hGm : MeasurableSet G)
    [IsFiniteMeasure (ν (p.world a))] :
    ∃ S₁ ⊆ G, MeasurableSet S₁ ∧
      S₁ ⊆ p.assigned a ×ˢ Ioo ((p.bin a : ℝ) / (2 : ℝ) ^ p.T (p.lev a))
        (((p.bin a : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev a)) ∧
      (∀ z ∈ S₁, ∀ b : Fin p.C, z.2 ≠ (p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b) ∧
        z.2 ≠ ((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b)) ∧
      ((ν (p.world a)).prod volume) (G ∩ p.counted a) ≤
        ((ν (p.world a)).prod volume) S₁ := by
  set Z : Set Incidence := univ ×ˢ p.blockEnds with hZ
  set S₁ := (G ∩ p.assigned a ×ˢ Ioo ((p.bin a : ℝ) / (2 : ℝ) ^ p.T (p.lev a))
    (((p.bin a : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev a))) \ Z with hS₁
  have hZm : MeasurableSet Z := MeasurableSet.univ.prod (p.blockEnds_finite).measurableSet
  have hZ0 : ((ν (p.world a)).prod volume) Z = 0 := blockEnds_null p _
  refine ⟨S₁, fun z hz => hz.1.1, ?_, fun z hz => hz.1.2, ?_, ?_⟩
  · exact (hGm.inter ((hp.assigned_measurable a).prod measurableSet_Ioo)).diff hZm
  · intro z hz b
    have hz2 : z.2 ∉ p.blockEnds := fun h => hz.2 ⟨mem_univ _, h⟩
    refine ⟨fun h => hz2 (mem_iUnion.mpr ⟨b, by rw [h]; exact mem_insert _ _⟩),
      fun h => hz2 (mem_iUnion.mpr ⟨b, by rw [h]; exact mem_insert_of_mem _ rfl⟩)⟩
  · have hsub : G ∩ p.counted a ⊆ S₁ ∪ Z := by
      intro z hz
      by_cases hzZ : z.2 ∈ p.blockEnds
      · exact Or.inr ⟨mem_univ _, hzZ⟩
      · left
        have hs := hp.counted_support a z hz.2
        have hlo : z.2 ≠ (p.bin a : ℝ) / (2 : ℝ) ^ p.T (p.lev a) := fun h =>
          hzZ (mem_iUnion.mpr ⟨a, by rw [h]; exact mem_insert _ _⟩)
        have hhi : z.2 ≠ ((p.bin a : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev a) := fun h =>
          hzZ (mem_iUnion.mpr ⟨a, by rw [h]; exact mem_insert_of_mem _ rfl⟩)
        refine ⟨⟨hz.1, hs.2.1, lt_of_le_of_ne hs.2.2.1.1 (Ne.symm hlo),
          lt_of_le_of_ne hs.2.2.1.2 hhi⟩, fun h => hzZ h.2⟩
    calc ((ν (p.world a)).prod volume) (G ∩ p.counted a)
        ≤ ((ν (p.world a)).prod volume) (S₁ ∪ Z) := measure_mono hsub
      _ ≤ ((ν (p.world a)).prod volume) S₁ + ((ν (p.world a)).prod volume) Z :=
          measure_union_le _ _
      _ = ((ν (p.world a)).prod volume) S₁ := by rw [hZ0, add_zero]

/-- The parent packet is at most `κ²` times its counted set. -/
theorem packet_le_counted (hNk : 0 < Nk) (a : Fin p.C) :
    ((ν (p.world a)).prod volume) (p.packet a) ≤
      ENNReal.ofReal (p.κ ^ 2) * ((ν (p.world a)).prod volume) (p.counted a) := by
  obtain ⟨hsat, hprior⟩ := hp.saturation a
  have hκ := hp.one_le_slack
  have hκ0 : (0 : ℝ) < p.κ := by linarith
  have hT : (0 : ℝ) < (2 : ℝ) ^ p.T (p.lev a) := by positivity
  have hX0 : 0 ≤ Nk ^ (-f (p.r (p.lev a))) * |(p.frame a).det| :=
    mul_nonneg (Real.rpow_nonneg hNk.le _) (abs_nonneg _)
  have hlen : ((p.bin a : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev a) -
      (p.bin a : ℝ) / (2 : ℝ) ^ p.T (p.lev a) = ((2 : ℝ) ^ p.T (p.lev a))⁻¹ := by
    field_simp
    ring
  unfold PathData.packet
  rw [Measure.prod_prod, Real.volume_Icc, hlen]
  calc (ν (p.world a)) (p.assigned a) * ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev a))⁻¹
      ≤ ENNReal.ofReal (p.κ * Nk ^ (-f (p.r (p.lev a))) * |(p.frame a).det|) *
          ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev a))⁻¹ := mul_le_mul' hprior le_rfl
    _ = ENNReal.ofReal (p.κ ^ 2) * ENNReal.ofReal (Nk ^ (-f (p.r (p.lev a))) *
          |(p.frame a).det| / ((2 : ℝ) ^ p.T (p.lev a) * p.κ)) := by
        rw [← ENNReal.ofReal_mul (by rw [mul_assoc]; exact mul_nonneg hκ0.le hX0),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
    _ ≤ ENNReal.ofReal (p.κ ^ 2) * ((ν (p.world a)).prod volume) (p.counted a) :=
        mul_le_mul' le_rfl hsat

/-- The counted set of a label has positive finite mass. -/
theorem counted_toReal_pos (hNk : 0 < Nk) (a : Fin p.C) [IsFiniteMeasure (ν (p.world a))] :
    0 < (((ν (p.world a)).prod volume) (p.counted a)).toReal := by
  have hsat := (hp.saturation a).1
  have hκ := hp.one_le_slack
  have hdet : 0 < |(p.frame a).det| := abs_pos.mpr (hp.chart a).1
  have hpos : 0 < Nk ^ (-f (p.r (p.lev a))) * |(p.frame a).det| /
      ((2 : ℝ) ^ p.T (p.lev a) * p.κ) := by
    apply div_pos (mul_pos (Real.rpow_pos_of_pos hNk _) hdet)
    exact mul_pos (by positivity) (by linarith)
  have hsub : p.counted a ⊆ p.packet a := fun z hz =>
    ⟨(hp.counted_support a z hz).2.1, (hp.counted_support a z hz).2.2.1⟩
  have hfin : ((ν (p.world a)).prod volume) (p.counted a) ≠ ⊤ :=
    ne_top_of_le_ne_top (packet_ne_top (p.world a) a) (measure_mono hsub)
  apply ENNReal.toReal_pos _ hfin
  exact (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hpos) hsat).ne'

/-- **Room for the floor** from a density `c > m τ κ²` of `G` in the parent's counted set. -/
theorem room_of_density (hNk : 0 < Nk) (a : Fin p.C) [IsFiniteMeasure (ν (p.world a))]
    {G S₁ : Set Incidence} {c τ : ℝ} (hτ : 0 ≤ τ) (hc : (m : ℝ) * τ * p.κ ^ 2 < c)
    (hG : ENNReal.ofReal c * ((ν (p.world a)).prod volume) (p.counted a) ≤
      ((ν (p.world a)).prod volume) (G ∩ p.counted a))
    (hS₁ : ((ν (p.world a)).prod volume) (G ∩ p.counted a) ≤
      ((ν (p.world a)).prod volume) S₁)
    (hS₁a : S₁ ⊆ p.packet a) :
    (m : ℝ) * τ * (((ν (p.world a)).prod volume) (p.packet a)).toReal <
      (((ν (p.world a)).prod volume) S₁).toReal := by
  set μ := (ν (p.world a)).prod (volume : Measure ℝ) with hμ
  have hκ := hp.one_le_slack
  have hc0 : 0 < c := lt_of_le_of_lt (by positivity) hc
  have hcnt := counted_toReal_pos hp hNk a
  have hsub : p.counted a ⊆ p.packet a := fun z hz =>
    ⟨(hp.counted_support a z hz).2.1, (hp.counted_support a z hz).2.2.1⟩
  have hfinc : μ (p.counted a) ≠ ⊤ :=
    ne_top_of_le_ne_top (packet_ne_top (p.world a) a) (measure_mono hsub)
  have hfinS : μ S₁ ≠ ⊤ := ne_top_of_le_ne_top (packet_ne_top (p.world a) a) (measure_mono hS₁a)
  have hpk : (μ (p.packet a)).toReal ≤ p.κ ^ 2 * (μ (p.counted a)).toReal := by
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinc)
      (packet_le_counted hp hNk a)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h
  have hGS : c * (μ (p.counted a)).toReal ≤ (μ S₁).toReal := by
    have h := ENNReal.toReal_mono hfinS (hG.trans hS₁)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0.le] at h
  have hmτ : 0 ≤ (m : ℝ) * τ := by positivity
  calc (m : ℝ) * τ * (μ (p.packet a)).toReal
      ≤ (m : ℝ) * τ * (p.κ ^ 2 * (μ (p.counted a)).toReal) :=
        mul_le_mul_of_nonneg_left hpk hmτ
    _ = (m : ℝ) * τ * p.κ ^ 2 * (μ (p.counted a)).toReal := by ring
    _ < c * (μ (p.counted a)).toReal := mul_lt_mul_of_pos_right hc hcnt
    _ ≤ (μ S₁).toReal := hGS

/-- **Room for the floor** in the form of `SourceSelectionSpec`, from a density
`c₀ > m τ κ²` of `G` in the parent's counted set. -/
theorem room_of_counted_density (hNk : 0 < Nk) (a : Fin p.C) [IsFiniteMeasure (ν (p.world a))]
    {G : Set Incidence} {c τ : ℝ} (hτ : 0 ≤ τ) (hc : (m : ℝ) * τ * p.κ ^ 2 < c)
    (hG : ENNReal.ofReal c * ((ν (p.world a)).prod volume) (p.counted a) ≤
      ((ν (p.world a)).prod volume) (G ∩ p.counted a)) :
    (m : ℝ) * τ * (((ν (p.world a)).prod volume) (p.packet a)).toReal <
      (((ν (p.world a)).prod volume) (G ∩ p.counted a)).toReal :=
  room_of_density hp hNk a hτ hc hG le_rfl (fun z hz =>
    ⟨(hp.counted_support a z hz.2).2.1, (hp.counted_support a z hz.2).2.2.1⟩)

end Path

end

end Submission.Obl.k4_finite_affine_parent_sources
