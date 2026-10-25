-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.FineOriginalPosterior, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/FineOriginalPosterior.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/FineOriginalPosterior.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/FineOriginalPosterior.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.FineOriginalSource

/-! Exact recovery of the original fine incidence law after dropping the
fixed world label. Both the global and coarse normalizers cancel. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A : ℝ} {θ : ENNReal}
  (F : PaletteFamily Q i stop a A θ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

theorem PaletteFamily.fine_original_event_measurable
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (b f : Fin p.C) (hb : F.active b) (V : Set (EuclideanSpace ℝ (Fin 2))) (hV : MeasurableSet V) :
    MeasurableSet (F.fineOriginalEvent b f V) :=
  (hp.measurableSet_packetWitness stop (p.γ b) f).inter
    (((F.measurable_U b hb).preimage measurable_prodMk_left).inter
      (hV.preimage (p.measurable_normalizedVelocity b)))

theorem PaletteFamily.fine_original_source_ae
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (b : Fin p.C) (hb : F.active b) (f : Fin p.C) (hf : p.lev f = stop)
    (hfγ : p.γ f = p.γ b) :
    (Q.residual (p.γ b) ∩ {x | finitePacketHistory p.lev p.γ p.F stop (p.γ b, x) = F.coding.code f ∧
      (p.γ b, x) ∈ F.U b}) =ᵐ[(d.ν k (p.γ b)).prod volume] F.fineOriginalEvent b f univ := by
  let D := {z | finitePacketHistory p.lev p.γ p.F stop z = F.coding.code f ∧ z ∈ F.U b}
  have hcode := F.coding.ae_core (p.γ b)
  have hunique := hp.ae_packet_unique (p.γ b)
  have heq : (Q.residual (p.γ b) ∩ {x | (p.γ b, x) ∈ D}) =ᵐ[(d.ν k (p.γ b)).prod volume]
      F.fineOriginalEvent b f univ := by
    filter_upwards [hcode, hunique] with x hxcode hxunique
    apply propext
    constructor
    · intro hx
      have hxF : x ∈ p.F f := (hxcode f hfγ).mp (by simpa only [hf] using hx.2.1)
      have hterminal : x ∈ p.terminalCoverage m (p.γ b) := by
        obtain ⟨t, ht, htγ, hxt⟩ := hH _ (Q.base_subset _ (Q.residual_subset _ hx.1))
        exact ⟨t, ⟨ht, htγ⟩, hxt⟩
      have hxW : x ∈ p.packetWitness m stop (p.γ b) f := by
        rw [PathData.packetWitness, ite_eq_left (show p.lev f = stop ∧ p.γ f = p.γ b from ⟨hf, hfγ⟩)]
        exact ⟨⟨hxF, hxunique⟩, hterminal⟩
      exact ⟨hxW, hx.2.2, mem_univ _⟩
    · intro hx
      have hxC := F.subset_coarse b hb hx.2.1
      have hxF : x ∈ p.F f := by
        have hmem : (x ∈ p.F f ∧ packetUnique p.lev p.γ p.F (p.γ b) x) ∧
            x ∈ p.terminalCoverage m (p.γ b) := by
          simpa only [PathData.packetWitness, ite_eq_left (show p.lev f = stop ∧ p.γ f = p.γ b from ⟨hf, hfγ⟩),
            mem_inter_iff, mem_ofPred_eq] using hx.1
        exact hmem.1.1
      have hxhist := F.coding.code_eq_of_mem_core (p.γ b) hxcode f hfγ hxF
      rw [hf] at hxhist
      exact ⟨hxC.1, hxhist, hx.2.1⟩
  exact heq

theorem PaletteFamily.fine_original_posterior (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (b : Fin p.C) (hb : F.active b) (f : Fin p.C) (hf : p.lev f = stop)
    (hfγ : p.γ f = p.γ b) :
    (F.fineLaw b (F.coding.code f)).map Prod.snd =
      ProbabilityTheory.cond ((d.ν k (p.γ b)).prod volume) (F.fineOriginalEvent b f univ) := by
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one hp.1
  let := Q.probability hd hHE hκ
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  let C := Q.coarseSupport (p.lev b) (F.code b)
  let D := {z | finitePacketHistory p.lev p.γ p.F stop z = F.coding.code f ∧ z ∈ F.U b}
  have hC : MeasurableSet C := (measurableSet_labelledSupport Q.residual Q.residual_measurable).inter
    (measurableSet_eq_fun (measurable_finitePacketHistory p.lev p.γ p.F hF _) measurable_const)
  have hD : MeasurableSet D :=
    (measurableSet_eq_fun (measurable_finitePacketHistory p.lev p.γ p.F hF _) measurable_const).inter
      (F.measurable_U b hb)
  have hDC : D ⊆ C := fun _ hz => F.subset_coarse b hb hz.2
  have hflatten : F.fineLaw b (F.coding.code f) = ProbabilityTheory.cond Q.law D := by
    change ProbabilityTheory.cond (ProbabilityTheory.cond Q.law C) D = _
    rw [ProbabilityTheory.cond_cond_eq_cond_inter hC hD Q.law, inter_eq_right.mpr hDC]
  have htotal := ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ∞) (Q.original_total_le_one hd hHE)
  have hposterior := prepared_world_posterior (fun w => (d.ν k w).prod volume) (d.ω k)
    Q.residual D hD (p.γ b) (fun z hz => (F.packet b hb z (hDC hz)).1)
    (F.weight_positive b hb) htotal
  change (ProbabilityTheory.cond Q.law D).map Prod.snd =
    ProbabilityTheory.cond ((d.ν k (p.γ b)).prod volume)
      (Q.residual (p.γ b) ∩ {x | (p.γ b, x) ∈ D}) at hposterior
  rw [hflatten, hposterior]
  have heq := F.fine_original_source_ae hp hH b hb f hf hfγ
  change (Q.residual (p.γ b) ∩ {x | (p.γ b, x) ∈ D}) =ᵐ[(d.ν k (p.γ b)).prod volume]
    F.fineOriginalEvent b f univ at heq
  simp only [ProbabilityTheory.cond, measure_congr heq, Measure.restrict_congr_set heq]

/-- Multiplying out the selected fine probability recovers ORIGINAL
product-law mass exactly, on the same packet and selected incidence set. -/
theorem PaletteFamily.fine_velocity_original_mass (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (b : Fin p.C) (hb : F.active b) (f : Fin p.C) (hf : p.lev f = stop)
    (hfγ : p.γ f = p.γ b) (V : Set (EuclideanSpace ℝ (Fin 2))) (hV : MeasurableSet V) :
    F.fineVelocityLaw b (F.coding.code f) V *
        ((d.ν k (p.γ b)).prod volume) (F.fineOriginalEvent b f univ) =
      ((d.ν k (p.γ b)).prod volume) (F.fineOriginalEvent b f V) := by
  have hVm := p.measurable_normalizedVelocity b
  have hmap : F.fineVelocityLaw b (F.coding.code f) =
      ((F.fineLaw b (F.coding.code f)).map Prod.snd).map (p.normalizedVelocity b) :=
    (Measure.map_map hVm measurable_snd).symm
  rw [hmap, F.fine_original_posterior hd hp hHE hH b hb f hf hfγ, Measure.map_apply hVm hV]
  have hD := F.fine_original_event_measurable hp b f hb univ MeasurableSet.univ
  have hsub : F.fineOriginalEvent b f univ ⊆ Q.residual (p.γ b) :=
    fun _ hx => (F.subset_coarse b hb hx.2.1).1
  have htop : ((d.ν k (p.γ b)).prod volume) (F.fineOriginalEvent b f univ) ≠ ∞ :=
    ne_top_of_le_ne_top (by simp : (1 : ENNReal) ≠ ∞)
      ((measure_mono hsub).trans (Q.world_mass_le_one hd hHE (p.γ b)))
  rw [ProbabilityTheory.cond_mul_eq_inter' hD htop]
  congr 1
  ext x
  simp only [fineOriginalEvent, mem_inter_iff, mem_ofPred_eq, mem_univ, and_true, mem_preimage]
  tauto

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
