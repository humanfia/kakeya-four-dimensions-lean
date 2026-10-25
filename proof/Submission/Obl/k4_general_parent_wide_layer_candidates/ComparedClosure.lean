import Submission.Obl.k4_general_parent_wide_layer_candidates.ComparedInterface
import Submission.Obl.k4_general_parent_wide_layer_candidates.Lists.Cofinal
import Submission.Obl.k4_general_parent_wide_layer_candidates.Lists.Preparation
import Submission.Obl.k4_general_parent_wide_layer_candidates.Lists.Apply

namespace Submission.Obl.k4_general_parent_wide_layer_candidates

open Filter

noncomputable section

/-- The remaining native-signal preparation, independently of projected
layers. The multiplier is fixed before any subsequence is requested. -/
def NativeConfinementCore : Prop :=
  ∀ (α : Type) [MeasurableSpace α] (p : Parent α), p.Valid →
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ r v m, p.ListExponents r v m → Λ * m ≤ p.U →
      p.DeepConfinement r v m

/-- Compared original slices and native deep confinement close the exact
candidate principle. The scale cap precedes the wide-layer subsequence. -/
theorem core_of_compared_layers (hcompare : ComparedLayerCore)
    (hlists : ComparedListCore) (hconf : NativeConfinementCore) : Core := by
  intro hscalar hmatching α _ p hp hwide
  obtain ⟨ΛA, hΛA, hlists⟩ := hlists α p hp
  obtain ⟨ΛB, hΛB, hconf⟩ := hconf α p hp
  have hsum : 0 < ΛA + ΛB := add_pos hΛA hΛB
  obtain ⟨τ, hτ, r, u, v, m, hexp, hmU, samples⟩ :=
    hcompare hmatching α p hp hwide (p.U / (ΛA + ΛB)) (div_pos hp.depth_pos hsum)
  have hτtop : Tendsto τ atTop atTop := hτ.tendsto_atTop
  have hpτ : (p.reindex τ).Valid := Parent.Valid.reindex p hp hτtop
  have hm0 : 0 ≤ m := by
    obtain ⟨hr, hv, _, hm, _, _⟩ := hexp.1
    linarith
  have htotal : (ΛA + ΛB) * m ≤ p.U := by
    rw [le_div_iff₀ hsum] at hmU
    linarith
  have hΛAm : ΛA * m ≤ p.U := by nlinarith [mul_nonneg hΛB.le hm0]
  have hΛBm : ΛB * m ≤ p.U := by nlinarith [mul_nonneg hΛA.le hm0]
  have hdeep := (hconf r v m hexp.1 hΛBm).reindex hτtop
  have frames : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      Nonempty ((p.reindex τ).ListFrame k r v m ε) := by
    intro ε hε
    obtain ⟨δ, hδ, hprepare⟩ := hlists r u v m hexp hΛAm ε hε
    filter_upwards [samples δ hδ, hτtop.eventually hprepare] with k hs hk
    obtain ⟨H, hH, hKH, hHN, hs⟩ := hs
    have hs' : Nonempty (p.ComparedSample (τ k) r u v m H) :=
      hs.map (Parent.ComparedSample.fromReindex p)
    exact (hk H hH hKH hHN hs').map (Parent.ListFrame.toReindex p)
  have hready := (p.reindex τ).scalarReadiness_of_lists hpτ hexp.1 frames hdeep
  exact Parent.candidates_of_reindex p hτtop
    ((p.reindex τ).candidates_of_readiness hscalar hpτ hready)

end
end Submission.Obl.k4_general_parent_wide_layer_candidates
