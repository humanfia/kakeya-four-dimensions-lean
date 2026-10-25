-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.StrongBroadResidual, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/StrongBroadResidual.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SaturatedDichotomy
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeBroadResidual

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SaturatedDichotomy

open MeasureTheory Set
open ParentSource ParentSource.Native

noncomputable section

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
    {F : PaletteFamily Q i stop a A θ} (P : PaletteStripSaturation F r fraction)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

/-- Saturation removes every narrow state. The only subsequent positive
loss is fine-state retention, so the original mass remains above the
threshold used by the frozen narrow alternative. -/
theorem remaining_broad_strong (hd : d.Valid)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (hi : i < m) (hstop : stop < m) (hfraction : 0 < fraction)
    (hbuffer : ENNReal.ofReal (11 * p.κ⁻¹ / 32) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (Q.residual w))
    (hfull : ENNReal.ofReal (15 / 16 : ℝ) ≤ Q.law
      (labelledSupport (Q.packetFamilyResidual i (Q.selectedCoarseFamily F.active F.U))))
    (hcap : Q.law (labelledSupport P.captureResidual) ≤ ENNReal.ofReal (9 / 22 : ℝ)) :
    ∃ R : BroadResidual (remainingPalette P hp (remaining_mass P hfull hcap)) r (2 * fraction),
      ENNReal.ofReal (71 * p.κ⁻¹ / 512) ≤
        ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (R.residual w) := by
  classical
  let F' := remainingPalette P hp (remaining_mass P hfull hcap)
  let source := Q.selectedCoarseFamily F'.active F'.U
  let fail := Q.fineRetentionOmissions F'.active F'.code stop F'.U
    (ENNReal.ofReal (1 / 8 : ℝ))
  have hcode (b : Fin p.C) (hb : F'.active b) :=
    And.intro (F'.packet b hb) (And.intro (F'.coarse_positive b hb) (F'.posterior b hb))
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hmk (b : Fin p.C) : Measurable (Prod.mk (p.γ b) : Ev → Fin (d.W k) × Ev) :=
    measurable_const.prodMk measurable_id
  have hsource (b : Fin p.C) : MeasurableSet (source b) := by
    by_cases hb : F'.active b
    · simpa only [source, PreparedAngularPath.selectedCoarseFamily, ite_eq_left hb] using
        (F'.measurable_U b hb).preimage (hmk b)
    · simp only [source, PreparedAngularPath.selectedCoarseFamily, ite_eq_right hb]
      exact MeasurableSet.empty
  obtain ⟨hfailmeas, _, _, hfail, _⟩ := Q.fine_retention_omission_bounds hd hp hHE hH i hi
    F'.active F'.code stop hcode F'.U F'.measurable_U F'.subset_coarse
      (ENNReal.ofReal (1 / 8 : ℝ))
  let Full := labelledSupport (Q.packetFamilyResidual i source)
  let Omit := labelledSupport (Q.packetFamilyResidual i fail)
  let D := Full \ Omit
  have hFullmeas : MeasurableSet Full := measurableSet_labelledSupport _
    (Q.measurableSet_packetFamilyResidual i source hsource)
  have hOmitmeas : MeasurableSet Omit := measurableSet_labelledSupport _
    (Q.measurableSet_packetFamilyResidual i fail hfailmeas)
  have hD : MeasurableSet D := hFullmeas.diff hOmitmeas
  have hkeep : ENNReal.ofReal (71 / 176 : ℝ) ≤ Q.law D := by
    have hcover : Full ⊆ D ∪ Omit := by
      intro z hz
      by_cases ho : z ∈ Omit
      · exact Or.inr ho
      · exact Or.inl ⟨hz, ho⟩
    have hbound : ENNReal.ofReal (71 / 176 : ℝ) + ENNReal.ofReal (1 / 8 : ℝ) ≤
        Q.law D + ENNReal.ofReal (1 / 8 : ℝ) := by
      calc
        _ = ENNReal.ofReal (93 / 176 : ℝ) := by
          rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          norm_num
        _ ≤ Q.law Full := remaining_mass_strong P hfull hcap
        _ ≤ Q.law D + Q.law Omit := (measure_mono hcover).trans (measure_union_le _ _)
        _ ≤ _ := add_le_add le_rfl hfail
    exact ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top hbound
  let J₀ := fun w => Q.residual w ∩ {x | (w, x) ∈ D}
  let J := F'.coding.cleanResidual J₀
  have hJ₀meas (w : Fin (d.W k)) : MeasurableSet (J₀ w) :=
    (Q.residual_measurable w).inter (hD.preimage (measurable_const.prodMk measurable_id))
  have hJ₀H (w : Fin (d.W k)) : J₀ w ⊆ H w :=
    inter_subset_left.trans ((Q.residual_subset w).trans (Q.base_subset w))
  have hκ : 0 < p.κ := zero_lt_one.trans_le hp.1
  have htop := ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ⊤)
    (Q.original_total_le_one hd hHE)
  rw [labelledResidual_univ] at htop
  have hmass₀ := prepared_cut_original_floor (fun w => (d.ν k w).prod volume) (d.ω k)
    Q.residual D hD (by positivity : 0 < 11 * p.κ⁻¹ / 32) htop hbuffer hkeep
  have hmass : ENNReal.ofReal (71 * p.κ⁻¹ / 512) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (J w) := by
    simpa only [J, F'.coding.cleanResidual_original_mass hp,
      show (11 * p.κ⁻¹ / 32) * (71 / 176) = 71 * p.κ⁻¹ / 512 by ring] using hmass₀
  refine ⟨{
    residual := J
    measurable := F'.coding.cleanResidual_measurable hF J₀ hJ₀meas
    subset_H := fun w x hx => hJ₀H w hx.1.1
    mass := ?_
    witness := ?_
  }, hmass⟩
  · exact (ENNReal.ofReal_le_ofReal (by
      have : 0 ≤ p.κ⁻¹ := inv_nonneg.mpr hκ.le
      nlinarith only [this] : (p.κ⁻¹ / 8) * ((1 / 2) / 2) ≤ 71 * p.κ⁻¹ / 512)).trans hmass
  · intro w x hx
    have hx₀ : x ∈ J₀ w := hx.1.1
    have hterminal : x ∈ p.terminalCoverage m w := by
      obtain ⟨t, ht, htw, hxt⟩ := hH w (hJ₀H w hx₀)
      exact ⟨t, ⟨ht, htw⟩, hxt⟩
    obtain ⟨f, hf, hfw, hfcode, hxf⟩ := hp.pointwise_fine_packet_witness F'.coding stop hstop
      w x hx.2 hx.1.2 hterminal
    obtain ⟨b, hbi, hbw, hxb⟩ := hx₀.2.1
    have hb : F'.active b := by
      by_contra hn
      simp only [source, PreparedAngularPath.selectedCoarseFamily, ite_eq_right hn,
        mem_empty_iff_false] at hxb
    have hxU : (p.γ b, x) ∈ F'.U b := by
      simpa only [source, PreparedAngularPath.selectedCoarseFamily, ite_eq_left hb,
        mem_preimage] using hxb
    have hFb : x ∈ p.F b := ((hcode b hb).1 _ (F'.subset_coarse b hb hxU)).2
    have hcodefine : finitePacketHistory p.lev p.γ p.F stop (p.γ b, x) = F'.coding.code f := by
      simpa only [hbw] using hfcode
    refine ⟨b, hbi, hbw, hFb, hb, hxU, f, hf, hfw, hxf, ?_, ?_⟩
    · exact P.remaining_not_narrow hfraction b hb (F'.coding.code f)
    · intro he
      apply hx₀.2.2
      refine ⟨b, hbi, hbw, ?_⟩
      simpa only [fail, PreparedAngularPath.fineRetentionOmissions, ite_eq_left hb,
        mem_preimage, mem_inter_iff, hcodefine] using (show (p.γ b, x) ∈ F'.U b ∧
          F'.coding.code f ∈ fineRetentionFailures (Q.coarseLaw (p.lev b) (F'.code b))
            (finitePacketHistory p.lev p.γ p.F stop) (F'.U b) (ENNReal.ofReal (1 / 8 : ℝ)) from
              ⟨hxU, he⟩)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SaturatedDichotomy
