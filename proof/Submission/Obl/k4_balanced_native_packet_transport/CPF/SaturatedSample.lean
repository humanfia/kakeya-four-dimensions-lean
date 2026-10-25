/-
Adapted from this LOT tree, o105, session x0351, commit 2ab1efa2599f805c9c42d7bd390982a163d519ba,
Submission/Obl/k4_critical_path_framework/SaturatedSample.lean (namespace Submission.Obl.k4_critical_path_framework renamed to
Submission.Obl.k4_balanced_native_packet_transport.CPF).
-/
/- Shared from this LOT obligation o105, session x0548, commit 9d59cc18efc1,
   Submission/Obl/k4_critical_path_framework/SaturatedSample.lean. Earlier provenance is retained below. -/
import Submission.Obl.k4_balanced_native_packet_transport.CPF.SaturatedLabels

namespace Submission.Obl.k4_balanced_native_packet_transport.CPF

open MeasureTheory
open scoped ENNReal

/-- A true atlas whose labels are known at its own depth and whose full original
assigned priors satisfy the saturated upper bound. -/
def Atlas.SaturatedAt {p : Data} {k : ℕ} (a : Atlas p k) (M D : ℕ) (r : ℝ) : Prop :=
  a.TrueAt M D r ∧
  (∀ b, p.ν k (a.γ b) (a.A b) ≤
    ENNReal.ofReal (a.κ * p.N k ^ (-p.f r) * |Matrix.det (a.Q b)|)) ∧
  ∃ lst : Fin (p.W k) → Observation → Finset (Fin a.C),
    (∀ γ o, ((lst γ o).card : ℝ) ≤ a.κ) ∧
    (∀ b q, q ∈ a.F b → b ∈ lst (a.γ b) (obs (p.B k (a.γ b)) (δ (p.N k) r) q)) ∧
    ∀ γ b, MeasurableSet {o | b ∈ lst γ o}

theorem saturated_atlas_of_crossing_loss {p : Data} (hp : p.Valid)
    {k M D M' D' : ℕ} {r H κ' Hprior θ : ℝ}
    (a : Atlas p k) (ha : a.TrueAt M D r)
    (hM : M ≤ M') (hD : D ≤ D') (h4 : 4 ≤ D') (hκ : 1 ≤ a.κ)
    (hκ' : 2 * a.κ ≤ κ')
    (bins : Fin (p.W k) → Finset ℤ) (m : ℕ) (hmesh : 4 * a.κ ^ 2 ≤ (m : ℝ))
    (hH : 0 ≤ H) (hHκ : H ≤ κ') (hHprior : 0 ≤ Hprior)
    (hfmt : ∀ b, p.N k ^ M + (a.C : ℝ) * ((bins (a.γ b)).card * (5 + 4 * m)) ≤ p.N k ^ M')
    (hbin : ∀ b q, q ∈ a.F b →
      (obs (p.B k (a.γ b)) (δ (p.N k) r) q).2 ∈ bins (a.γ b))
    (hlost : 2 * a.crossingLostMass r bins m H +
      a.deletedMass (a.saturatedLabels Hprior θ) ≤ ENNReal.ofReal (2 * a.κ)⁻¹)
    (hsat : 2 * Hprior * θ * crossingFactor a.κ ≤ κ' * p.N k ^ (-p.f r)) :
    ∃ a' : Atlas p k, a'.T = a.T ∧ a'.κ = κ' ∧ a'.SaturatedAt M' D' r := by
  obtain ⟨a', lst, hT, hκout, htrue, hcard, hlist, hlabels, hmeas⟩ :=
    true_atlas_of_crossing_loss hp a ha hM hD h4 hκ hκ' bins m hmesh hH hHκ hfmt hbin
      (a.saturatedLabels Hprior θ) hlost
  refine ⟨a', hT, hκout, htrue, ?_, lst, ?_, hlist, hmeas⟩
  · intro b
    obtain ⟨b₀, hb₀, hγ, hA, hQ⟩ := hlabels b
    rw [hγ, hA, hQ, hκout]
    exact (a.saturated_prior_bound hHprior b₀ hb₀).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hsat (abs_nonneg _)))
  · simpa only [hκout] using hcard

end Submission.Obl.k4_balanced_native_packet_transport.CPF
