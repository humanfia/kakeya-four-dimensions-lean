import Submission.Obl.k4_raw_localized_native_systems.C.NativeCoefficients
import Submission.Obl.k4_raw_localized_native_systems.C.PacketSystem

/-
Adapted from this LOT tree, o178, session x0596, `OriginalAtlasStage.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory Filter MvPolynomial
open Submission.Lib.K4XInterface
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The geometric interface's retained mass supplies the regular original
atlas mass too, by its explicit unchanged-law domination. -/
theorem PacketSample.to_projected {p : Data} {k M D : ℕ}
    {loss h χ d s m S U : ℝ} (hp : Valid p) (hL : p.L = 1)
    (hsample : PacketSample false (p.N k) (p.K k) (p.W k) (p.ω k) (p.ν k)
      (p.E k) (p.P k) (p.B k) M D loss h χ d s m S U) :
    Nonempty (ProjectedPackets p k M D loss h χ d s m S U) := by
  classical
  obtain ⟨T, C, γ, j, center, velocity, Q, A, F, lst, offset, tangent,
    law, base, signal, hK, hT, hC, hdisj, hlst, hlstm, hcharts, hcoords,
    hbudget, hproj, hmass, hcert⟩ := hsample
  let a : Atlas p k := ⟨T, C, γ, j, center, velocity, Q, fun b => p.P k (γ b), A, F, lst⟩
  have hdom (b : Fin C) : packetBudget a b • Measure.map (packetExpand a b) (law b) ≤
      ((p.ν k (γ b)).prod volume).restrict (F b) := (hproj b).2.2.2.2.2.2
  have htotal (b : Fin C) : packetBudget a b * law b Set.univ ≤
      ((p.ν k (γ b)).prod volume) (F b) := by
    have hh := hdom b Set.univ
    simpa only [Measure.smul_apply, smul_eq_mul,
      Measure.map_apply (packetExpand_measurable a b) MeasurableSet.univ,
      Set.preimage_univ, Measure.restrict_apply_univ] using hh
  have hmass' : ENNReal.ofReal ((p.N k ^ loss)⁻¹) ≤
      ∑ b, ENNReal.ofReal (p.ω k (γ b)) * ((p.ν k (γ b)).prod volume) (F b) := by
    rw [← Real.rpow_neg (hp.scale_pos k).le]
    apply hmass.trans
    apply Finset.sum_le_sum
    intro b _
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (htotal b) zero_le
  refine ⟨{
    atlas := a
    known := ⟨⟨hC, hdisj, ?_, hmass'⟩, hlst⟩
    list_measurable := hlstm
    time := hT
    native := fun _ => rfl
    offset := offset
    tangent := tangent
    coordinate_bound := hcoords
    prior := fun b => (p.ν k (γ b) (A b))⁻¹ • (p.ν k (γ b)).restrict (A b)
    law := law
    base := base
    signal := signal
    projected := ?_
    base_measurable := fun b => (hproj b).2.2.1
    signal_measurable := fun b => (hproj b).2.2.2.1
    observed_signal := ?_
    assignment_support := fun b => (hproj b).2.2.2.2.2.1
    original_domination := hdom
    retained_mass := hmass }⟩
  · simpa only [hL] using hcharts
  · intro b
    simpa [nativeCoeff_eq_clipped, packetCoeff, packetStart, packetTimeLength, a] using (hproj b).1
  · intro b
    simpa only [nativeCoeff_eq_clipped, packetObservation, hL, packetCoeff, packetExpand,
      packetStart, packetTimeLength, a, gobs, obs, gδ, δ, gx, x] using (hproj b).2.2.2.2.1

theorem PacketAvailable.to_packetSystem
    {ds kr S η s m U χ h t : ℝ}
    (hprep : PacketAvailable false ds kr S η s m U χ h t) :
    ∃ p : Data, Near ds kr S η t p ∧ ProjectedPacketSystem p h χ ds s m (S / 2) U := by
  obtain ⟨N, K, d, W, ω, ν, E, P, B, f, g, G, hp, hd, hH, M, D, hprep⟩ := hprep
  let p : Data := ⟨N, K, 1, d, S, η, W, ω, ν, E, P, B, f, g, G⟩
  refine ⟨p, ⟨hp, rfl, rfl, rfl, hd, hH⟩, M, D, fun loss hloss => ?_⟩
  exact (hprep loss hloss).mono (fun k hk => hk.to_projected (p := p) hp rfl)

/-- The full scalar-to-original-atlas stage of Section 10.  All parameters
that determine formats are fixed before requesting the original atlas slack. -/
theorem originalAtlasStage : OriginalAtlasStatement := by
  intro hQ ds kr S η hds hds1 hkr hS hprep
  obtain ⟨s, m, U, hs, hs1, hsm, hU, hUm, hprep⟩ := hprep
  obtain ⟨c, hc, hcs, χ, hχ, hrec⟩ :=
    hQ.packets_to_known hds hds1 hs hs1 hsm (by positivity : 0 < S / 2) hU hUm
  let r : ℝ := c / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := by have := hcs.trans_le (min_le_right s 1); dsimp [r]; linarith
  refine ⟨r, hr, hr1, fun t ht => ?_⟩
  obtain ⟨p, hp, hpack⟩ :=
    (hprep χ (kr * c / 4) t hχ (by positivity) ht).to_packetSystem
  obtain ⟨hv, hL, hSp, hηp, hd, hH⟩ := hp
  have hknown := hrec p (kr * c / 4) hv hpack
  refine ⟨p.N, p.K, p.d, p.W, p.ω, p.ν, p.E, p.P, p.B, p.f, p.g, p.G,
    ?_, hd, ?_, ?_⟩
  · simpa only [Valid, hL, hSp, hηp] using hv
  · simpa only [Horizon, hL] using hH
  · obtain ⟨M, D, hknown⟩ := hknown
    refine ⟨M, D, fun ε hε => (hknown ε hε).mono ?_⟩
    rintro k ⟨κ, hκ, hKκ, hκε, a, hT, ⟨hC, hdisj, hcharts, hmass⟩, hlst⟩
    refine ⟨κ, hκ, hKκ, hκε, a.T, a.C, a.γ, a.j, a.c, a.u, a.Q, a.R, a.A,
      a.F, a.lst, ?_, hC, hdisj, hlst, ?_, ?_⟩
    · have heq : kr * r / 2 = kr * c / 4 := by dsimp [r]; ring
      simpa only [heq] using hT
    · simpa only [hL] using hcharts
    · exact hmass

end
end Submission.Obl.k4_raw_localized_native_systems.C
