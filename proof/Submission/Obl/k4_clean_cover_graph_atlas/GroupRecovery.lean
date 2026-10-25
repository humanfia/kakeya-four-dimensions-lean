-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/GroupRecovery.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.SheetPacket
import Submission.Obl.k4_clean_cover_graph_atlas.SheetBinSupport
import Submission.Obl.k4_clean_cover_graph_atlas.ProjectionBand
import Submission.Obl.k4_clean_cover_graph_atlas.DensityVersions

namespace Submission.Obl.k4_clean_cover_graph_atlas

open Set MeasureTheory Finset
open Submission.Lib.K4OriginalLists

/-- Constants fixed before the finite packet, its original laws, and its matching scale. -/
structure GroupParameters where
  order : ℕ
  directions : Finset Real3
  lower : ℝ
  upper : ℕ → ℝ
  remezScale : ℝ
  remezExponent : ℝ
  epsilon : ℝ
  radius : ℝ
  order_pos : 1 ≤ order
  directions_unit : ∀ v ∈ directions, ‖v‖ = 1
  lower_pos : 0 < lower
  upper_pos : ∀ m, 0 < upper m
  remezScale_one : 1 ≤ remezScale
  remezExponent_one : 1 ≤ remezExponent
  epsilon_pos : 0 < epsilon
  radius_two : 2 ≤ radius

abbrev GroupJetIndex (params : GroupParameters) := params.directions × Fin (params.order + 1)

noncomputable def groupJetWidth (params : GroupParameters) (R M ε : ℝ) : GroupJetIndex params → ℝ :=
  fun i => params.upper i.2.val * (M * R ^ (-ε))

/-- The full one-group recovery interface, stated using only original component laws
and source fits. Real density versions and posterior pair laws are constructed internally. -/
def GroupRecovery (D : ℕ) (d₀ : ℝ) (params : GroupParameters) : Prop :=
  ∀ R M ε : ℝ, params.radius ≤ R → 0 < M → 0 < ε → ε ≤ params.epsilon →
  ∀ (n : ℕ) (f : Fin n → RealSheet D) (f₀ : RealSheet D),
  ∀ {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z],
  ∀ (ρ : Measure X) [SigmaFinite ρ] (μ : Fin n → Measure Z) [∀ a, IsFiniteMeasure (μ a)],
  ∀ (O : Z → X), Measurable O → (∀ a, (μ a).map O ≪ ρ) →
  ∀ (base : X → Real3), Measurable base → ∀ (bin : X → ℤ), Measurable bin →
  ∀ (hidden : Z → ℝ) (δ ηfine ηold θ H m lam : ℝ),
    0 < n → 0 < ηfine → 0 < ηold → 0 < θ → θ ≤ 1 → 0 < H → 0 < lam →
    (n : ℝ) ≤ R ^ (d₀ + ε) →
    (∑ a, μ a univ) ≤ ENNReal.ofReal lam → (n : ℝ) * H ≤ lam * R ^ ε →
    (∀ a, (μ a).map (base ∘ O) ≤ ENNReal.ofReal H • volume) →
    (∀ a, ENNReal.ofReal m ≤ μ a univ) →
    ENNReal.ofReal θ * volume (Metric.closedBall (0 : Real3) (1 / 2)) ≤ ENNReal.ofReal (m / H) →
    params.remezScale * (params.remezExponent * θ ^ (-params.remezExponent) * (ηfine + ηold)) ≤
      M * R ^ ε →
    2 * ηfine + δ ≤ M * R ^ (-1 + ε) →
    (∀ a, ∀ᵐ z ∂μ a,
      ‖base (O z)‖ ≤ (1 : ℝ) / 2 ∧
      δ * (bin (O z) : ℝ) ≤ hidden z ∧ hidden z ≤ δ * ((bin (O z) : ℝ) + 1) ∧
      |hidden z - ((f a).f (emb (base (O z)))).re| ≤ ηfine ∧
      |hidden z - (f₀.f (emb (base (O z)))).re| ≤ ηold) →
    let jet := fun a => directionalJets params.directions params.order (f a).f
    let width := groupJetWidth params R M ε
    ∃ L : X → Finset (binLabels width jet), MeasurableLists L ∧
      (∀ x, (L x).card ≤ 7 ^ Fintype.card (GroupJetIndex params)) ∧
      ((∑ a, μ a univ) ≤ (∑ a, μ a {z | mergedLabel width jet a ∈ L (O z)}) +
        ENNReal.ofReal (lam * R ^ (-ε))) ∧
      ∀ a (x : Real3), ‖x‖ ≤ (1 : ℝ) / 2 →
        ‖(f a).f (emb x) -
          (f (binRepresentative width jet (mergedLabel width jet a))).f (emb x)‖ ≤
            (∑ i, width i) / params.lower

/-- Local matching and sheet Remez give one-group recovery directly for original
incidence laws. Its constants are independent of the selected component masses. -/
theorem exists_group_recovery (h : localGraph) (hr : algebraicRemez) (D : ℕ) (d₀ : ℝ)
    (hd₀ : 0 ≤ d₀) (hd₀1 : d₀ < 1) :
    ∃ params : GroupParameters, GroupRecovery D d₀ params := by
  obtain ⟨Krem, Crem, hKrem, hCrem, hremez⟩ := exists_original_mass_sheet_band hr D
  obtain ⟨K, hK, V, hV, c, hc, B, hB, ε₀, hε₀, R₀, hR₀, hpacket⟩ :=
    original_sheet_packet_lists h D d₀ hd₀ hd₀1
  let params : GroupParameters := {
    order := K
    directions := V
    lower := c
    upper := B
    remezScale := Krem
    remezExponent := Crem
    epsilon := ε₀
    radius := R₀
    order_pos := hK
    directions_unit := hV
    lower_pos := hc
    upper_pos := hB
    remezScale_one := hKrem
    remezExponent_one := hCrem
    epsilon_pos := hε₀
    radius_two := hR₀ }
  refine ⟨params, ?_⟩
  intro R M ε hR hM hε hεbound n f f₀ X Z _ _ ρ _ μ _ O hO hAC base hb bin hbin
    hidden δ ηfine ηold θ H m lam hn hηfine hηold hθ hθ1 hH hlam hcount htotal hbudget hcap hfloor
    hθmass hbandbudget hwidth hfit
  let S (a : Fin n) : Set X := {o | ‖base o‖ ≤ (1 : ℝ) / 2 ∧
    δ * (bin o : ℝ) - ηfine ≤ ((f a).f (emb (base o))).re ∧
    ((f a).f (emb (base o))).re ≤ δ * ((bin o : ℝ) + 1) + ηfine}
  have hS (a : Fin n) : MeasurableSet (S a) :=
    measurableSet_sheet_bin_bounds (f a) base hb bin hbin δ ηfine
  have hsupport (a : Fin n) : ((μ a).map O) (S a)ᶜ = 0 := by
    rw [Measure.map_apply hO (hS a).compl]
    have hae : ∀ᵐ z ∂μ a, O z ∈ S a := by
      filter_upwards [hfit a] with z hz
      obtain ⟨hhalf, hlo, hhi, hnear, _⟩ := hz
      obtain ⟨hnlo, hnhi⟩ := abs_le.mp hnear
      exact ⟨hhalf, by linarith, by linarith⟩
    exact ae_iff.mp hae
  choose p hpmeas hpint hpnonneg hplaw hppos using fun a =>
    exists_real_density_supported ((μ a).map O) ρ (hAC a) (S a) (hS a) (hsupport a)
  have hband (a : Fin n) (x : Real3) (hx : ‖x‖ ≤ 1) :
      ‖(f a).f (emb x) - f₀.f (emb x)‖ ≤ M * R ^ ε := by
    let νa := (μ a).map (base ∘ O)
    let E : Set Real3 := {x | ‖x‖ ≤ (1 : ℝ) / 2 ∧
      ‖(f a).f (emb x) - f₀.f (emb x)‖ ≤ ηfine + ηold}
    have hE : MeasurableSet E := measurableSet_sheet_agreement (f a) f₀ (ηfine + ηold)
    have hEsupport : νa Eᶜ = 0 := by
      dsimp only [νa]
      rw [Measure.map_apply (hb.comp hO) hE.compl]
      have hae : ∀ᵐ z ∂μ a, base (O z) ∈ E := by
        filter_upwards [hfit a] with z hz
        obtain ⟨hhalf, _, _, hnear, htrue⟩ := hz
        exact ⟨hhalf, sheet_gap_of_real_fits (f a) f₀ _ (by linarith) (hidden z) hnear htrue⟩
      exact ae_iff.mp hae
    have hmass : ENNReal.ofReal m ≤ νa univ := by
      dsimp only [νa]
      rw [Measure.map_apply (hb.comp hO) MeasurableSet.univ, preimage_univ]
      exact hfloor a
    exact (hremez (f a) f₀ νa H m θ (ηfine + ηold) hH hθ hθ1 (add_pos hηfine hηold)
      (hcap a) hEsupport hmass hθmass x hx).trans hbandbudget
  have hpfit (a : Fin n) : ∀ᵐ o ∂ρ, 0 < p a o →
      ‖base o‖ ≤ (1 : ℝ) / 2 ∧
      δ * (bin o : ℝ) - ηfine ≤ ((f a).f (emb (base o))).re ∧
      ((f a).f (emb (base o))).re ≤ δ * ((bin o : ℝ) + 1) + ηfine :=
    Filter.Eventually.of_forall fun o ho => hppos a o ho
  have hpair := posterior_base_support_of_sheet_bins f ρ (fun o a => p a o) hpmeas
    (fun o a => hpnonneg a o) base hb bin δ ηfine (M * R ^ (-1 + ε)) hwidth hpfit
  exact hpacket R M ε hR hM hε hεbound n f (fun x => f₀.f (emb x))
    ρ (fun o a => p a o) hpmeas hpint (fun o a => hpnonneg a o) μ O hO hplaw base hb
    lam H hn hlam hcount hband htotal hbudget hcap hpair

end Submission.Obl.k4_clean_cover_graph_atlas
