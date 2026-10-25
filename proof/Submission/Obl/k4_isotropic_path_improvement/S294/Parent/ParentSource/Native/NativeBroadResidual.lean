-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativeBroadResidual, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativeBroadResidual.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativeBroadResidual.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeBroadResidual.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/NativeBroadResidual.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeFineRetention
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeFinePacketBridge
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.FinePaletteDomination

/-! A small intrinsic narrow alternative leaves an actual substantial
ORIGINAL residual in positive broad fine states with explicit retention. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

noncomputable def PreparedAngularPath.selectedCoarseFamily (_Q : PreparedAngularPath d k p m H u τ) (active : Fin p.C → Prop)
    (U : Fin p.C → Set (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ)))
    (b : Fin p.C) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) := by
  classical
  exact if active b then Prod.mk (p.γ b) ⁻¹' U b else ∅

theorem PreparedAngularPath.broad_residual_of_small_narrow (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (q : PacketCoding p (d.ν k)) (stop : ℕ) (hstop : stop < m)
    (i : ℕ) (hi : i < m) (active : Fin p.C → Prop) (code : Fin p.C → ℕ)
    (hcode : ∀ b, active b →
      (∀ z ∈ Q.coarseSupport (p.lev b) (code b), z.1 = p.γ b ∧ z.2 ∈ p.F b) ∧
      Q.law (Q.coarseSupport (p.lev b) (code b)) ≠ 0 ∧
      (Q.coarseLaw (p.lev b) (code b)).map Prod.snd = ProbabilityTheory.cond (Q.currentParentLaw b) univ)
    (U : Fin p.C → Set (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ)))
    (hU : ∀ b, active b → MeasurableSet (U b))
    (hUC : ∀ b, active b → U b ⊆ Q.coarseSupport (p.lev b) (code b))
    {mass fraction r α : ℝ} (hmass : 0 ≤ mass) (hα : 0 < α) (hαbudget : α ≤ mass / 4)
    (hfull : ENNReal.ofReal mass ≤ Q.law
      (labelledSupport (Q.packetFamilyResidual i (Q.selectedCoarseFamily active U))))
    (hbad : Q.law (labelledSupport (Q.packetFamilyResidual i
      (Q.badHistoryFamily active code stop (Q.intrinsicNarrowStates code stop U r fraction)))) ≤
        ENNReal.ofReal (mass / 4)) :
    ∃ J : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ),
      (∀ γ, MeasurableSet (J γ)) ∧ (∀ γ, J γ ⊆ H γ) ∧
      ENNReal.ofReal ((p.κ⁻¹ / 8) * (mass / 2)) ≤
        ∑ γ, ENNReal.ofReal (d.ω k γ) * ((d.ν k γ).prod volume) (J γ) ∧
      ∀ γ x, x ∈ J γ → ∃ b, p.lev b = i ∧ p.γ b = γ ∧ x ∈ p.F b ∧ active b ∧
        (p.γ b, x) ∈ U b ∧ ∃ f,
          p.lev f = stop ∧ p.γ f = γ ∧ x ∈ p.packetWitness m stop γ f ∧
          q.code f ∉ Q.intrinsicNarrowStates code stop U r fraction b ∧
          q.code f ∉ fineRetentionFailures (Q.coarseLaw (p.lev b) (code b))
            (finitePacketHistory p.lev p.γ p.F stop) (U b) (ENNReal.ofReal α) := by
  classical
  let Bad := Q.intrinsicNarrowStates code stop U r fraction
  let source := Q.selectedCoarseFamily active U
  let bad := Q.badHistoryFamily active code stop Bad
  let fail := Q.fineRetentionOmissions active code stop U (ENNReal.ofReal α)
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hS := measurableSet_labelledSupport Q.residual Q.residual_measurable
  have hhist := measurable_finitePacketHistory p.lev p.γ p.F hF stop
  have hmk (b : Fin p.C) : Measurable (Prod.mk (p.γ b) :
      ((ℕ × (Fin 6 → ℝ)) × ℝ) → Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ)) :=
    measurable_const.prodMk measurable_id
  have hsource (b : Fin p.C) : MeasurableSet (source b) := by
    by_cases hb : active b
    · simpa only [source, selectedCoarseFamily, ite_eq_left hb] using
        (hU b hb).preimage (hmk b)
    · simp only [source, selectedCoarseFamily, ite_eq_right hb]
      exact MeasurableSet.empty
  have hbadmeas (b : Fin p.C) : MeasurableSet (bad b) := by
    by_cases hb : active b
    · have hC : MeasurableSet (Q.coarseSupport (p.lev b) (code b)) :=
        hS.inter (measurableSet_eq_fun (measurable_finitePacketHistory p.lev p.γ p.F hF _) measurable_const)
      simpa only [bad, PreparedAngularPath.badHistoryFamily, ite_eq_left hb] using
        (hC.inter (hhist (Set.to_countable (Bad b)).measurableSet)).preimage
          (hmk b)
    · simp only [bad, PreparedAngularPath.badHistoryFamily, ite_eq_right hb]
      exact MeasurableSet.empty
  obtain ⟨hfailmeas, _, _, hfail, _⟩ := Q.fine_retention_omission_bounds hd hp hHE hH i hi
    active code stop hcode U hU hUC (ENNReal.ofReal α)
  let Full := labelledSupport (Q.packetFamilyResidual i source)
  let Omit := labelledSupport (Q.packetFamilyResidual i bad) ∪
    labelledSupport (Q.packetFamilyResidual i fail)
  let D := Full \ Omit
  have hFullmeas : MeasurableSet Full := measurableSet_labelledSupport _
    (Q.measurableSet_packetFamilyResidual i source hsource)
  have hOmitmeas : MeasurableSet Omit :=
    (measurableSet_labelledSupport _ (Q.measurableSet_packetFamilyResidual i bad hbadmeas)).union
      (measurableSet_labelledSupport _ (Q.measurableSet_packetFamilyResidual i fail hfailmeas))
  have hD : MeasurableSet D := hFullmeas.diff hOmitmeas
  have hOmit : Q.law Omit ≤ ENNReal.ofReal (mass / 2) := by
    calc
      _ ≤ Q.law (labelledSupport (Q.packetFamilyResidual i bad)) +
          Q.law (labelledSupport (Q.packetFamilyResidual i fail)) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (mass / 4) + ENNReal.ofReal α := add_le_add hbad hfail
      _ ≤ ENNReal.ofReal (mass / 4) + ENNReal.ofReal (mass / 4) :=
        add_le_add le_rfl (ENNReal.ofReal_le_ofReal hαbudget)
      _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  have hkeep : ENNReal.ofReal (mass / 2) ≤ Q.law D := by
    simpa only [Finset.univ_unique, Finset.sum_singleton, one_mul] using
      mixture_remove_half (fun _ : Unit => Q.law) (fun _ => 1) (fun _ => Full) (fun _ => Omit)
        hmass (by simpa using hfull) (by simpa using hOmit)
  let J₀ := fun γ => Q.residual γ ∩ {x | (γ, x) ∈ D}
  let J := q.cleanResidual J₀
  have hJ₀meas (γ : Fin (d.W k)) : MeasurableSet (J₀ γ) :=
    (Q.residual_measurable γ).inter (hD.preimage (measurable_const.prodMk measurable_id))
  have hJ₀H (γ : Fin (d.W k)) : J₀ γ ⊆ H γ :=
    inter_subset_left.trans ((Q.residual_subset γ).trans (Q.base_subset γ))
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one hp.1
  have htop := ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ∞) (Q.original_total_le_one hd hHE)
  rw [labelledResidual_univ] at htop
  have hJ₀mass := prepared_cut_original_floor (fun γ => (d.ν k γ).prod volume) (d.ω k)
    Q.residual D hD (by positivity : 0 < p.κ⁻¹ / 8) htop Q.original_mass hkeep
  refine ⟨J, (q.cleanResidual_measurable hF J₀ hJ₀meas), ?_, ?_, ?_⟩
  · intro γ x hx
    exact hJ₀H γ hx.1.1
  · simpa only [J, q.cleanResidual_original_mass hp] using hJ₀mass
  · intro γ x hx
    have hx₀ : x ∈ J₀ γ := hx.1.1
    have hterminal : x ∈ p.terminalCoverage m γ := by
      obtain ⟨t, ht, htγ, hxt⟩ := hH γ (hJ₀H γ hx₀)
      exact ⟨t, ⟨ht, htγ⟩, hxt⟩
    obtain ⟨f, hf, hfγ, hfcode, hxf⟩ := hp.pointwise_fine_packet_witness q stop hstop γ x
      hx.2 hx.1.2 hterminal
    obtain ⟨b, hbi, hbγ, hxb⟩ := hx₀.2.1
    have hb : active b := by
      by_contra hn
      simp only [source, selectedCoarseFamily, ite_eq_right hn, mem_empty_iff_false] at hxb
    have hxU : (p.γ b, x) ∈ U b := by
      simpa only [source, selectedCoarseFamily, ite_eq_left hb, mem_preimage] using hxb
    have hFb : x ∈ p.F b := ((hcode b hb).1 _ (hUC b hb hxU)).2
    have hcodefine : finitePacketHistory p.lev p.γ p.F stop (p.γ b, x) = q.code f := by
      simpa only [hbγ] using hfcode
    refine ⟨b, hbi, hbγ, hFb, hb, hxU, f, hf, hfγ, hxf, ?_, ?_⟩
    · intro he
      apply hx₀.2.2
      apply Or.inl
      refine ⟨b, hbi, hbγ, ?_⟩
      simpa only [bad, PreparedAngularPath.badHistoryFamily, ite_eq_left hb,
        mem_preimage, mem_inter_iff, hcodefine] using
          (show (p.γ b, x) ∈ Q.coarseSupport (p.lev b) (code b) ∧ q.code f ∈ Bad b from
            ⟨hUC b hb hxU, he⟩)
    · intro he
      apply hx₀.2.2
      apply Or.inr
      refine ⟨b, hbi, hbγ, ?_⟩
      simpa only [fail, PreparedAngularPath.fineRetentionOmissions, ite_eq_left hb,
        mem_preimage, mem_inter_iff, hcodefine] using (show (p.γ b, x) ∈ U b ∧
          q.code f ∈ fineRetentionFailures (Q.coarseLaw (p.lev b) (code b))
            (finitePacketHistory p.lev p.γ p.F stop) (U b) (ENNReal.ofReal α) from ⟨hxU, he⟩)

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
