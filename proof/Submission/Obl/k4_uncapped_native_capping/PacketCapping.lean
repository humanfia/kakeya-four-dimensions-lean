import Submission.Obl.k4_uncapped_native_capping.UncappedPacket
import Submission.Obl.k4_uncapped_native_capping.PreparedCaps

namespace Submission.Obl.k4_uncapped_native_capping

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion
noncomputable section

/-- Apply the common original density masks to every provisional packet.
All original arrays, budgets, readers and reference measures are retained;
the restricted laws now obey every frozen scalar cap. -/
theorem PacketData.cap_restrictOriginal
    {p : UWE.Problem} {S η : ℝ} (hp : p.Valid S η) (hL : p.L = 1)
    (k : ℕ) (R V : Finset ℝ)
    (hR : ∀ r ∈ R, 0 ≤ r ∧ r ≤ p.L)
    (hV : ∀ u ∈ V, 0 < u ∧ u ≤ η * p.L)
    {s U ε τ ξ χ loss d m h : ℝ} {M D : ℕ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hε : 0 < ε) (hτ : 0 ≤ τ)
    (hRgrid : UWE.coarseDepthGrid s ε ⊆ R)
    (hVgrid : ∀ u ∈ UWE.coarseDepthGrid U ε, 0 < u → u ∈ V)
    (hloss : 0 ≤ loss) (hlossχ : loss ≤ χ / 48)
    (hslack : χ / 4 + 3 * τ + (1 + S) * ε + 2 * ξ ≤ χ)
    (hconstant : 25600 ≤ p.N k ^ (χ / 8))
    (hprofile : ∀ r, 0 ≤ r → r ≤ s → d * r - ξ ≤ p.f r - p.f 0)
    {pack : PacketData (p.W k)}
    (hg : pack.Geometry (p.N k) (p.K k) (p.ω k) (p.ν k) (p.E k) (p.P k) (p.B k)
      M D loss h)
    (ha : pack.ProvisionalAnalysis (p.N k) χ d s m (S / 2) U
      (p.ω k) (p.ν k) (p.P k) (p.B k))
    (hc : pack.CappingGeometry (p.N k) loss U (p.f 0) ξ (p.ν k)) :
    (pack.restrictOriginal (fun w => (UWE.densityPreparationBad p S R V τ k w)ᶜ)).Analysis
      (p.N k) χ d s m (S / 2) U (p.ω k) (p.ν k) (p.P k) (p.B k) := by
  let good : Fin (p.W k) → Set Inc :=
    fun w => (UWE.densityPreparationBad p S R V τ k w)ᶜ
  have hgood : ∀ w, MeasurableSet (good w) :=
    fun w => (hp.measurableSet_densityPreparationBad R V hR hV τ k w).compl
  have hnew := ha.restrictOriginal good
  apply hnew.with_caps
  intro a
  obtain ⟨e, n, β, heq, he, hn, hen, hfull, hnormal⟩ := hc.physical a
  subst e
  obtain ⟨hQ, hcu, hQbig, hQsmall, hP, hPcoeff, hA, hF, hfmt, hassign, hmem, hex⟩ :=
    hg.charts a
  apply prepared_native_law_caps hp hL k (pack.γ a) R V hR hV hs hs1 hε hτ hRgrid hVgrid
    hloss hlossχ hslack hconstant hprofile (pack.A a) (pack.F a) hF
    (fun z hz => (hmem z hz).1) (pack.Q a) hQ (pack.c a) (pack.u a)
    (pack.t₀ a) pack.q (pack.offset a) (by unfold PacketData.q; positivity)
    (pack.tangent a) (hc.tangent_time a) hg.ambient
    (fun z hz => ((hassign z.1 (hmem z hz).2.1).2.2 z.2 (hmem z hz).2.2.1).1)
    hfull n he hn hen β (fun z hz => hnormal z.1 (hmem z hz).2.1) (hc.prior_lower a)
    ((pack.restrictOriginal good).law a) (hnew.assignment_support a) (hnew.regular a)
  have hh := ha.restrictOriginal_domination good hgood a
  rw [show pack.expand a = (fun z : Inc => (z.1, pack.t₀ a + pack.q * z.2)) from rfl] at hh
  simpa only [good, PacketData.budget, inter_comm] using hh

end
end Submission.Obl.k4_uncapped_native_capping
