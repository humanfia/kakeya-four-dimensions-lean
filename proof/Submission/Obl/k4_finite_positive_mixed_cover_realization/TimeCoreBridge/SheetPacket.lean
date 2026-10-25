-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/SheetPacket.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/SheetPacket.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.CommonPacket
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.HalfballJets

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MeasureTheory Set Finset
open Submission.Lib.K4OriginalLists

/-- One fixed jet system supplies original-observation lists and a representative sheet
for every retained bin. The only mass loss is the local graph matching error. -/
theorem original_sheet_packet_lists (h : localGraph) (D : ℕ) (d₀ : ℝ)
    (hd₀ : 0 ≤ d₀) (hd₀1 : d₀ < 1) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ V : Finset Real3, (∀ v ∈ V, ‖v‖ = 1) ∧
      ∃ c : ℝ, 0 < c ∧ ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧
      ∀ R M ε : ℝ, R₀ ≤ R → 0 < M → 0 < ε → ε ≤ ε₀ →
      ∀ (n : ℕ) (f : Fin n → RealSheet D) (f₀ : Real3 → ℂ),
      ∀ {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z],
      ∀ (ρ : Measure X) (p : X → Fin n → ℝ),
      (∀ a, Measurable (fun x => p x a)) → (∀ a, Integrable (fun x => p x a) ρ) →
      (∀ x a, 0 ≤ p x a) →
      ∀ (μ : Fin n → Measure Z) (O : Z → X), Measurable O →
      (∀ a, ρ.withDensity (fun x => ENNReal.ofReal (p x a)) = (μ a).map O) →
      ∀ (base : X → Real3), Measurable base → ∀ lam H : ℝ,
      0 < n → 0 < lam → (n : ℝ) ≤ R ^ (d₀ + ε) →
      (∀ i (x : Real3), ‖x‖ ≤ 1 → ‖(f i).f (emb x) - f₀ x‖ ≤ M * R ^ ε) →
      (∑ a, μ a univ) ≤ ENNReal.ofReal lam → (n : ℝ) * H ≤ lam * R ^ ε →
      (∀ a, (μ a).map (base ∘ O) ≤ ENNReal.ofReal H • volume) →
      posteriorBasePairLaw ρ p base {q | ‖q.2‖ ≤ (1 : ℝ) / 2 ∧
        ‖(f q.1.1).f (emb q.2) - (f q.1.2).f (emb q.2)‖ ≤ M * R ^ (-1 + ε)}ᶜ = 0 →
      let jet := fun a => directionalJets V K (f a).f
      let width : (V × Fin (K + 1)) → ℝ := fun i => B i.2.val * (M * R ^ (-ε))
      ∃ L : X → Finset (binLabels width jet), MeasurableLists L ∧
        (∀ x, (L x).card ≤ 7 ^ Fintype.card (V × Fin (K + 1))) ∧
        ((∑ a, μ a univ) ≤ (∑ a, μ a {z | mergedLabel width jet a ∈ L (O z)}) +
          ENNReal.ofReal (lam * R ^ (-ε))) ∧
        ∀ a (x : Real3), ‖x‖ ≤ (1 : ℝ) / 2 →
          ‖(f a).f (emb x) -
            (f (binRepresentative width jet (mergedLabel width jet a))).f (emb x)‖ ≤
              (∑ i, width i) / c := by
  obtain ⟨K, hK, V, hV, c, hc, B, hB, hcompare⟩ := exists_halfball_directional_jet_system D
  obtain ⟨ε₀, hε₀, R₀, hR₀, hpacket⟩ := common_cap_packet_lists h D d₀ hd₀ hd₀1
  refine ⟨K, hK, V, hV, c, hc, B, hB, ε₀, hε₀, R₀, hR₀, ?_⟩
  intro R M ε hR hM hε hεbound n f f₀ X Z _ _ ρ p hpmeas hpint hp
    μ O hO hlaw base hb lam H hn hlam hcount hband htotal hbudget hcap hsupport
  let jet := fun a => directionalJets V K (f a).f
  let width : (V × Fin (K + 1)) → ℝ := fun i => B i.2.val * (M * R ^ (-ε))
  have hRpos : 0 < R := by linarith
  have hA : 0 < M * R ^ (-ε) := mul_pos hM (Real.rpow_pos_of_pos hRpos _)
  have hw (i : V × Fin (K + 1)) : 0 < width i := mul_pos (hB i.2.val) hA
  have hjet a b (hclose : ∀ x : Real3, ‖x‖ ≤ (1 : ℝ) / 2 →
      ‖(f a).f (emb x) - (f b).f (emb x)‖ ≤ M * R ^ (-ε)) :
      ∀ i, |jet a i - jet b i| ≤ width i :=
    (hcompare (f a) (f b)).2 _ hA hclose
  obtain ⟨L, hL, hLc, hmass⟩ := hpacket R M ε hR hM hε hεbound n f f₀ jet width hw hjet
    ρ p hpmeas hpint hp μ O hO hlaw base hb lam H hn hlam hcount hband htotal hbudget hcap hsupport
  refine ⟨L, hL, hLc, hmass, ?_⟩
  intro a x hx
  exact sheet_bin_representative_bound hc f width hw
    (fun a b => (hcompare (f a) (f b)).1) a x hx

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
