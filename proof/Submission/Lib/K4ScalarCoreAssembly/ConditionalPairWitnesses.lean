/-
Adapted from: here:o062
Original proof: o062/x0212, 71f65b82, Submission/Obl/k4_scalar_mesh_projection/ConditionalPairWitnesses.lean.
Original law, observed physical palettes and witness rows remain unnormalized.
-/

import Submission.Lib.K4ScalarCoreTools.Finalization.FinitePaletteFreeze
import Submission.Lib.K4ScalarSwitching.PathDomination
import Submission.Lib.K4ScalarActualSwitching.OriginalBaseArea
import Submission.Lib.K4ScalarCoreAssembly.Support

namespace Submission.Lib.K4ScalarCoreAssembly

open Submission.Lib.K4ScalarCoreTools.Finalization
open Submission.Lib.K4ScalarCoreTools.Simulation.Switching
open Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching
open Submission.Lib.K4ScalarActualSwitching
open Submission.Lib.K4ScalarSwitching.Switching

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

/-- Two actual source witnesses at a common original state, with the
specified pair of rounded control codes. -/
def originalPairWitness {Ω Q C : Type*} (A : Set Ω) (state : Ω → Q)
    (code : Ω → C) (c : C × C) (q : Q) : Prop :=
  ∃ a ∈ A, ∃ b ∈ A,
    state a = q ∧ state b = q ∧ code a = c.1 ∧ code b = c.2

/-- Fix a pair of palette codes while keeping an original source set.
The two witnesses come from actual independent conditional draws at the
same state. The retained set includes all original controls at its
selected states; its mass loss is independent of individual code masses. -/
theorem exists_original_state_pair_witnesses {Ω Q C : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSpace C]
    [Countable Q] [MeasurableSingletonClass Q]
    [Countable C] [MeasurableSingletonClass C]
    (μ : Measure Ω) [IsFiniteMeasure μ] (hμ : μ univ ≠ 0)
    (A : Set Ω) (hA : MeasurableSet A) (hμA : ∀ᵐ ω ∂μ, ω ∈ A)
    (state : Ω → Q) (hstate : Measurable state)
    (code : Ω → C) (hcode : Measurable code)
    (κ : Kernel Ω Ω) [IsMarkovKernel κ]
    (π : Measure C) [IsProbabilityMeasure π]
    (K : ℝ) (hK : 0 < K) (R : Set (C × C))
    (hsupport : ∀ᵐ ω ∂μ, ∀ᵐ a ∂κ ω, a ∈ A ∧ state a = state ω)
    (hcap : ∀ᵐ ω ∂μ, (κ ω).map code ≤ ENNReal.ofReal K • π)
    (hbad : ∀ᵐ ω ∂μ, ((κ ω).prod (κ ω))
      {z | (code z.1, code z.2) ∉ R} ≤ 1 / 2) :
    ∃ c ∈ R, ∃ W : Set Ω, MeasurableSet W ∧ W ⊆ A ∧
      ENNReal.ofReal (1 / (2 * K^2)) * μ univ ≤ μ W ∧
      ∀ ω ∈ W, originalPairWitness A state code c (state ω) := by
  classical
  have hR : MeasurableSet R := (Set.to_countable R).measurableSet
  have : IsMarkovKernel (κ.map code) := Kernel.IsMarkovKernel.map κ hcode
  let P : Kernel Ω (C × C) := (κ.map code) ×ₖ (κ.map code)
  have hP (ω : Ω) : P ω = ((κ ω).prod (κ ω)).map (Prod.map code code) := by
    dsimp only [P]
    simp only [Kernel.prod_apply, Kernel.map_apply _ hcode]
    exact Measure.map_prod_map _ _ hcode hcode
  have hPcap : ∀ᵐ ω ∂μ, P ω ≤ ENNReal.ofReal (K^2) • π.prod π := by
    filter_upwards [hcap] with ω hω
    have hh := Measure.prod_mono hω hω
    simp only [P, Kernel.prod_apply, Kernel.map_apply _ hcode]
    apply hh.trans_eq
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      ← ENNReal.ofReal_mul hK.le, pow_two]
  have hWmeas : MeasurableSet
      {z : (C × C) × Q | originalPairWitness A state code z.1 z.2} :=
    (Set.to_countable _).measurableSet
  have hPwitness : ∀ᵐ ω ∂μ, ∀ᵐ c ∂P ω,
      originalPairWitness A state code c (state ω) := by
    filter_upwards [hsupport] with ω hω
    rw [hP]
    apply (ae_map_iff (hcode.prodMap hcode).aemeasurable
      ((Set.to_countable _).measurableSet)).mpr
    have ha : ∀ᵐ z ∂(κ ω).prod (κ ω), z.1 ∈ A ∧ state z.1 = state ω :=
      (Measure.quasiMeasurePreserving_fst (μ := κ ω) (ν := κ ω)).ae hω
    have hb : ∀ᵐ z ∂(κ ω).prod (κ ω), z.2 ∈ A ∧ state z.2 = state ω :=
      (Measure.quasiMeasurePreserving_snd (μ := κ ω) (ν := κ ω)).ae hω
    filter_upwards [ha, hb] with z hz₁ hz₂
    exact ⟨z.1, hz₁.1, z.2, hz₂.1, hz₁.2, hz₂.2, rfl, rfl⟩
  let θ := μ ⊗ₘ P
  let H : Set (Ω × (C × C)) :=
    {z | z.1 ∈ A ∧ originalPairWitness A state code z.2 (state z.1)}
  have hH : MeasurableSet H :=
    (hA.preimage measurable_fst).inter
      (hWmeas.preimage (measurable_snd.prodMk (hstate.comp measurable_fst)))
  have hθH : ∀ᵐ z ∂θ, z ∈ H := by
    apply (Measure.ae_compProd_iff hH).mpr
    filter_upwards [hμA, hPwitness] with ω hω hω'
    filter_upwards [hω'] with c hc
    exact ⟨hω, hc⟩
  let B : Set (Ω × (C × C)) := Prod.snd ⁻¹' Rᶜ
  have hB : MeasurableSet B := hR.compl.preimage measurable_snd
  have hθB : θ B ≤ (1 / 2) * μ univ := by
    rw [Measure.compProd_apply hB]
    calc
      _ ≤ ∫⁻ _ : Ω, (1 / 2 : ENNReal) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hbad] with ω hω
        change P ω Rᶜ ≤ 1 / 2
        rw [hP, Measure.map_apply (hcode.prodMap hcode) hR.compl]
        exact hω
      _ = (1 / 2) * μ univ := by simp
  let E : Set (Ω × (C × C)) := H ∩ Bᶜ
  have hE : MeasurableSet E := hH.inter hB.compl
  have hEq : θ E = θ Bᶜ := by
    apply measure_congr
    filter_upwards [hθH] with z hz
    simp only [E, Set.mem_inter_iff, hz, true_and]
  have hbudget : μ univ ≤ θ E + (1 / 2) * μ univ := by
    calc
      μ univ = θ Bᶜ + θ B := by
        rw [add_comm, measure_add_measure_compl hB]
        exact Measure.compProd_apply_univ.symm
      _ ≤ θ E + (1 / 2) * μ univ := by rw [hEq]; exact add_le_add le_rfl hθB
  have hhalf : μ univ / 2 ≤ θ E :=
    Submission.Lib.K4ScalarActualSwitching.half_mass_of_small_relative_loss
      (μ univ) (θ E) (1 / 2) (measure_ne_top _ _) le_rfl hbudget
  have hθdom : θ ≤ ENNReal.ofReal (K^2) • μ.prod (π.prod π) := by
    simpa only [one_mul] using
      Submission.Lib.K4ScalarSwitching.history_compProd_le_ae
        μ μ (π.prod π) P 1 (ENNReal.ofReal (K^2)) (by simp) hPcap
  let law := (θ.restrict E).map Prod.swap
  let S : Set ((C × C) × Ω) := Prod.swap ⁻¹' E
  have hS : MeasurableSet S := hE.preimage measurable_swap
  have hlawdom : law ≤ ENNReal.ofReal (K^2) • (π.prod π).prod μ := by
    calc
      law ≤ (ENNReal.ofReal (K^2) • μ.prod (π.prod π)).map Prod.swap :=
        Measure.map_mono (Measure.restrict_le_self.trans hθdom) measurable_swap
      _ = ENNReal.ofReal (K^2) • (π.prod π).prod μ := by
        rw [Measure.map_smul _ measurable_swap.aemeasurable, Measure.prod_swap]
  have hlawmass : ENNReal.ofReal ((1 / 2 : ℝ) * (μ univ).toReal) ≤ law S := by
    have hs : Prod.swap ⁻¹' S = E := by ext z; rfl
    rw [Measure.map_apply measurable_swap hS, hs, Measure.restrict_apply hE,
      Set.inter_self, ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
    have hehalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    rw [hehalf]
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using hhalf
  have hgood : ∀ z ∈ S, z.1 ∈ R := by
    intro z hz
    exact not_not.mp hz.2
  obtain ⟨c, hc, hW, hfloor, _⟩ := Submission.Lib.K4ScalarCoreTools.Finalization.exists_finite_original_palette_section
    (π.prod π) μ law S R (K^2) ((1 / 2 : ℝ) * (μ univ).toReal)
    (sq_pos_of_pos hK)
    (mul_pos (by norm_num) (ENNReal.toReal_pos hμ (measure_ne_top _ _)))
    hS hlawdom hlawmass hgood
  refine ⟨c, hc, Prod.mk c ⁻¹' S, hW, ?_, ?_, ?_⟩
  · intro ω hω
    exact hω.1.1
  · have hratio : ((1 / 2 : ℝ) * (μ univ).toReal) / K^2 =
        (1 / (2 * K^2)) * (μ univ).toReal := by ring
    rw [hratio, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_toReal (measure_ne_top _ _)] at hfloor
    exact hfloor
  · intro ω hω
    exact hω.1.2

end Submission.Lib.K4ScalarCoreAssembly
