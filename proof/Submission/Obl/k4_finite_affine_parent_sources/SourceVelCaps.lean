-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.SourceComponents
import Submission.Obl.k4_finite_affine_parent_sources.PathHistories

/-!
# Per-label velocity caps from an end-level numerator

`SourceData.velCaps_of_end_numerator` proves `D.VelCaps` (the per-label velocity caps of
`SourceSelectionSpec`) from a numerator bound at one END level `e` below every model label:
for every label `h` of level `e` descending from the parent,

  `(ν × vol) (S ∩ counted h ∩ {model velocity bin = v₀}) ≤ C · (ν × vol)(packet h) · π(bin v₀)`.

A model label's incidences in `S` are counted by its end-level descendants (terminal ancestors,
`S` avoids block endpoints), whose packets fill at most its own packet (`desc_packets_le`);
`muE` then turns the packet `ν(A) 2^-T` into `2^-relT ν_model(A)`.

Written by x0891 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set
open Submission.Obl.k4_finite_forest_width_selection

noncomputable section

section Path

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- The packets of the descendants of `b` at one level fill at most the packet of `b`. -/
theorem desc_packets_le (b : Fin p.C) (i : ℕ) :
    ∑ h ∈ Finset.univ.filter (fun h => p.lev h = i ∧ p.lev b ≤ p.lev h ∧
        forestAncestor p.lev p.par h (p.lev b) = b),
      ((ν (p.world b)).prod volume) (p.packet h) ≤
      ((ν (p.world b)).prod volume) (p.packet b) := by
  set s := Finset.univ.filter (fun h => p.lev h = i ∧ p.lev b ≤ p.lev h ∧
    forestAncestor p.lev p.par h (p.lev b) = b) with hs
  have hmem : ∀ h ∈ s, p.lev h = i ∧ p.lev b ≤ p.lev h ∧
      forestAncestor p.lev p.par h (p.lev b) = b := fun h hh => (Finset.mem_filter.mp hh).2
  have hworld : ∀ h ∈ s, p.world h = p.world b := by
    intro h hh
    have hw := (hp.ancestor h (p.lev b) (hmem h hh).2.1).2.1
    rw [(hmem h hh).2.2] at hw
    exact hw.symm
  rw [← measure_biUnion_finset₀]
  · apply measure_mono
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨h, hh, hzh⟩ := hz
    exact packet_subset_of_desc hp (hmem h hh).2.1 (hmem h hh).2.2 hzh
  · intro h hh h' hh' hne
    exact packet_aedisjoint hp (p.world b) hne ((hmem h hh).1.trans (hmem h' hh').1.symm)
      (hworld h hh) (hworld h' hh')
  · intro h _
    exact (packet_measurable hp h).nullMeasurableSet

end Path

namespace SourceData

variable {W : ℕ} {p : PathData W}

section Valid

variable {m Mp Dp : ℕ} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- **Per-label velocity caps from an end-level numerator.** -/
theorem velCaps_of_end_numerator (D : SourceData p) (n : ℕ) (unit : ℝ) {e : ℕ} {C : ℝ}
    [IsFiniteMeasure (ν D.w₀)]
    (hSo : D.S ⊆ p.assigned D.parent ×ˢ Ioo D.t₀ (D.t₀ + D.q₀))
    (hterm : D.S ⊆ TerminalInc W p.C m p.lev p.world p.counted D.w₀)
    (hSend : ∀ z ∈ D.S, ∀ b : Fin p.C, z.2 ≠ (p.bin b : ℝ) / (2 : ℝ) ^ p.T (p.lev b) ∧
      z.2 ≠ ((p.bin b : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev b))
    (hge : ∀ s, D.i₀ ≤ D.depth s) (he : e < m)
    (hdepth_le : ∀ s : ℝ, (n : ℝ)⁻¹ ≤ s → s ≤ 1 → D.depth s ≤ e)
    (hC0 : 0 ≤ C) (hCK : C ≤ D.K)
    (hnum : ∀ h : Fin p.C, p.lev h = e → p.world h = D.w₀ →
      forestAncestor p.lev p.par h D.i₀ = D.parent →
      ∀ v : ℝ, (n : ℝ)⁻¹ ≤ v → v ≤ n → ∀ v₀ : ℤ,
        ((ν D.w₀).prod volume) (D.S ∩ p.counted h ∩
          {z | ⌊(D.stage Nk L unit ν B).b z.1 3 / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀}) ≤
        ENNReal.ofReal C * ((ν D.w₀).prod volume) (p.packet h) *
          D.π {w : ℝ | ⌊w / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀}) :
    D.VelCaps n unit Nk L ν B := by
  intro s hs1 hs2 i v v₀ hv1 hv2
  set w := (Nk ^ (unit * L)) ^ (-v) with hw
  set V : Set Trajectory := {l | ⌊(D.stage Nk L unit ν B).b l 3 / w⌋ = v₀} with hV
  have hbm : Measurable (D.stage Nk L unit ν B).b := (D.frame Nk B).measurable_eb
  have hVm : MeasurableSet V :=
    measurableSet_eq_fun (Int.measurable_floor.comp
      (((measurable_pi_apply 3).comp hbm).div_const w)) measurable_const
  set μ₀ := (ν D.w₀).prod (volume : Measure ℝ) with hμ₀
  have hlev : p.lev (D.old s i) = D.depth s := D.old_level s i
  obtain ⟨hwb, -⟩ := D.old_world s i
  have hY : {z : Incidence | z.1 ∈ p.assigned (D.old s i) ∧
      z.2 ∈ IS (D.relT s) (D.relBin s i) ∧
      ⌊(D.stage Nk L unit ν B).b z.1 3 / w⌋ = v₀} =
      (p.assigned (D.old s i) ∩ V) ×ˢ IS (D.relT s) (D.relBin s i) := by
    ext z
    simp only [mem_ofPred_eq, mem_prod, mem_inter_iff, hV]
    tauto
  have hYm : MeasurableSet ((p.assigned (D.old s i) ∩ V) ×ˢ IS (D.relT s) (D.relBin s i)) :=
    ((hp.assigned_measurable _).inter hVm).prod measurableSet_Icc
  have hpre : tnorm D.t₀ D.q₀ ⁻¹' ((p.assigned (D.old s i) ∩ V) ×ˢ
      IS (D.relT s) (D.relBin s i)) = p.packet (D.old s i) ∩ {z | z.1 ∈ V} := by
    rw [← D.tnorm_preimage_label hp hSo s (hge s) i]
    ext z
    simp only [mem_preimage, mem_prod, mem_inter_iff, mem_ofPred_eq, tnorm]
    tauto
  -- the end-level descendants of the model label
  set Ef := Finset.univ.filter (fun h => p.lev h = e ∧ p.lev (D.old s i) ≤ p.lev h ∧
    forestAncestor p.lev p.par h (p.lev (D.old s i)) = D.old s i) with hEf
  have hcover : p.packet (D.old s i) ∩ {z | z.1 ∈ V} ∩ D.S ⊆
      ⋃ h ∈ Ef, (D.S ∩ p.counted h ∩ {z | z.1 ∈ V}) := by
    intro z hz
    obtain ⟨⟨hzP, hzV⟩, hzS⟩ := hz
    obtain ⟨old, hold, hwold, hzold⟩ := hterm hzS
    have hem : e ≤ p.lev old := by rw [hold]; omega
    obtain ⟨hhl, hhw, hhc⟩ := hp.ancestor old e hem
    set h := forestAncestor p.lev p.par old e with hh
    have hbe : p.lev (D.old s i) ≤ e := by rw [hlev]; exact hdepth_le s hs1 hs2
    have hbo : p.lev (D.old s i) ≤ p.lev old := hbe.trans hem
    have hio : z.2 ∈ Ioo ((p.bin (D.old s i) : ℝ) / (2 : ℝ) ^ p.T (p.lev (D.old s i)))
        (((p.bin (D.old s i) : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev (D.old s i))) :=
      ⟨lt_of_le_of_ne hzP.2.1 (hSend z hzS _).1.symm,
        lt_of_le_of_ne hzP.2.2 (hSend z hzS _).2⟩
    have hanc : forestAncestor p.lev p.par old (p.lev (D.old s i)) = D.old s i :=
      hp.ancestor_eq_of_interior hbo (hwold.trans hwb.symm) hzold hzP.1 hio
    have hcomp : forestAncestor p.lev p.par h (p.lev (D.old s i)) = D.old s i := by
      rw [hh, forestAncestor_comp p.lev p.par (fun b hb => (hp.parent b hb).1) old hbe hem,
        hanc]
    simp only [Set.mem_iUnion]
    refine ⟨h, ?_, ⟨hzS, hhc hzold⟩, hzV⟩
    rw [hEf, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hhl, by rw [hhl]; exact hbe, hcomp⟩
  -- the numerator on each end-level descendant
  have hEfnum : ∀ h ∈ Ef, μ₀ (D.S ∩ p.counted h ∩ {z | z.1 ∈ V}) ≤
      ENNReal.ofReal C * μ₀ (p.packet h) *
        D.π {x : ℝ | ⌊x / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀} := by
    intro h hh
    obtain ⟨hhe, hbh, hhb⟩ := (Finset.mem_filter.mp hh).2
    have hwh : p.world h = D.w₀ := by
      have := (hp.ancestor h (p.lev (D.old s i)) hbh).2.1
      rw [hhb] at this
      exact this.symm.trans hwb
    have hi₀b : D.i₀ ≤ p.lev (D.old s i) := by rw [hlev]; exact hge s
    have hpar : forestAncestor p.lev p.par h D.i₀ = D.parent := by
      rw [← forestAncestor_comp p.lev p.par (fun b hb => (hp.parent b hb).1) h hi₀b hbh, hhb]
      exact D.old_ancestor hp hSo s (hge s) i
    exact hnum h hhe hwh hpar v hv1 hv2 v₀
  -- the packet of the model label
  have hpk : ∑ h ∈ Ef, μ₀ (p.packet h) ≤ μ₀ (p.packet (D.old s i)) := by
    have h := desc_packets_le hp (D.old s i) e
    rw [hwb] at h
    exact h
  have hmass : μ₀ (p.packet (D.old s i) ∩ {z | z.1 ∈ V} ∩ D.S) ≤
      ENNReal.ofReal C * D.π {x : ℝ | ⌊x / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀} *
        μ₀ (p.packet (D.old s i)) :=
    calc μ₀ (p.packet (D.old s i) ∩ {z | z.1 ∈ V} ∩ D.S)
        ≤ ∑ h ∈ Ef, μ₀ (D.S ∩ p.counted h ∩ {z | z.1 ∈ V}) :=
          (measure_mono hcover).trans (measure_biUnion_finset_le _ _)
      _ ≤ ∑ h ∈ Ef, ENNReal.ofReal C * μ₀ (p.packet h) *
            D.π {x : ℝ | ⌊x / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀} :=
          Finset.sum_le_sum hEfnum
      _ = ENNReal.ofReal C * D.π {x : ℝ | ⌊x / ((Nk ^ (unit * L)) ^ (-v))⌋ = v₀} *
            ∑ h ∈ Ef, μ₀ (p.packet h) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun h _ => ?_
          ring
      _ ≤ _ := mul_le_mul' le_rfl hpk
  -- normalisation by `muE` and `nuE`
  have hμeq : (D.stage Nk L unit ν B).μ = muE (ν D.w₀) (p.assigned D.parent) D.t₀ D.q₀ D.S :=
    rfl
  have hνeq : (D.stage Nk L unit ν B).ν = nuE (ν D.w₀) (p.assigned D.parent) := rfl
  rw [hμeq, hνeq, hY, muE_apply _ _ _ _ _ hYm, hpre]
  have hq₀ : 0 < D.q₀ := by unfold q₀; positivity
  have hsub := D.old_assigned_subset hp hSo s (hge s) i
  have hnu : nuE (ν D.w₀) (p.assigned D.parent) (p.assigned (D.old s i)) =
      (ν D.w₀ (p.assigned D.parent))⁻¹ * ν D.w₀ (p.assigned (D.old s i)) := by
    rw [nuE, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply (hp.assigned_measurable _),
      Set.inter_eq_left.mpr hsub]
  have hTle : p.T D.i₀ ≤ p.T (p.lev (D.old s i)) := by
    rw [hlev]; exact (D.old_bin_div hp hSo s (hge s) i).1
  have hlen : ((p.bin (D.old s i) : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev (D.old s i)) -
      (p.bin (D.old s i) : ℝ) / (2 : ℝ) ^ p.T (p.lev (D.old s i)) =
      ((2 : ℝ) ^ p.T (p.lev (D.old s i)))⁻¹ := by
    field_simp
    ring
  have hpkt : μ₀ (p.packet (D.old s i)) = ν D.w₀ (p.assigned (D.old s i)) *
      ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev (D.old s i)))⁻¹) := by
    rw [hμ₀, PathData.packet, Measure.prod_prod, Real.volume_Icc, hlen]
  have hratio : ((2 : ℝ) ^ p.T (p.lev (D.old s i)))⁻¹ * D.q₀⁻¹ =
      (2 : ℝ) ^ (-(D.relT s : ℤ)) := by
    have hrel : D.relT s = p.T (p.lev (D.old s i)) - p.T D.i₀ := by
      rw [hlev]; rfl
    have h2 : (2 : ℝ) ^ p.T (p.lev (D.old s i)) =
        (2 : ℝ) ^ (p.T (p.lev (D.old s i)) - p.T D.i₀) * (2 : ℝ) ^ p.T D.i₀ := by
      rw [← pow_add, Nat.sub_add_cancel hTle]
    rw [hrel, zpow_neg, zpow_natCast, h2, q₀, inv_inv]
    field_simp
  have hγ : ν D.w₀ (p.assigned D.parent) ≠ ⊤ := measure_ne_top _ _
  calc (ENNReal.ofReal D.q₀ * ν D.w₀ (p.assigned D.parent))⁻¹ *
        μ₀ (p.packet (D.old s i) ∩ {z | z.1 ∈ V} ∩ D.S)
      ≤ (ENNReal.ofReal D.q₀ * ν D.w₀ (p.assigned D.parent))⁻¹ *
          (ENNReal.ofReal C * D.π {x : ℝ | ⌊x / w⌋ = v₀} *
            (ν D.w₀ (p.assigned (D.old s i)) *
              ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev (D.old s i)))⁻¹))) := by
        rw [← hpkt]
        exact mul_le_mul' le_rfl hmass
    _ = ENNReal.ofReal (C * (((2 : ℝ) ^ p.T (p.lev (D.old s i)))⁻¹ * D.q₀⁻¹)) *
          ((ν D.w₀ (p.assigned D.parent))⁻¹ * ν D.w₀ (p.assigned (D.old s i))) *
          D.π {x : ℝ | ⌊x / w⌋ = v₀} := by
        rw [ENNReal.mul_inv (Or.inr hγ) (Or.inl ENNReal.ofReal_ne_top),
          ENNReal.ofReal_mul hC0, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_inv_of_pos hq₀]
        ring
    _ ≤ ENNReal.ofReal (D.K * (2 : ℝ) ^ (-(D.relT s : ℤ))) *
          ((ν D.w₀ (p.assigned D.parent))⁻¹ * ν D.w₀ (p.assigned (D.old s i))) *
          D.π {x : ℝ | ⌊x / w⌋ = v₀} := by
        rw [hratio]
        gcongr
    _ = _ := by rw [hnu]

end Valid

end SourceData

end

end Submission.Obl.k4_finite_affine_parent_sources
