import Submission.Obl.k4_unbounded_geometric_packet_reduction.LocalizationInterfaces

namespace Submission.Obl.k4_unbounded_geometric_packet_reduction
open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion
noncomputable section
set_option maxRecDepth 8192
local instance (p : Prop) : Decidable p := Classical.propDecidable p

private lemma floor_window {a σ : ℝ} {j : ℤ} (hσ : 0 < σ)
    (h : ⌊a / σ⌋ = j) : |a - (j : ℝ) * σ| ≤ σ := by
  have hl := Int.floor_le (a / σ)
  have hu := Int.lt_floor_add_one (a / σ)
  rw [h] at hl hu
  have hl' := (le_div_iff₀ hσ).mp hl
  have hu' := (div_lt_iff₀ hσ).mp hu
  apply abs_le.mpr
  constructor <;> nlinarith
private lemma floor_distance {a b σ : ℝ} (hσ : 0 < σ)
    (h : ⌊a / σ⌋ = ⌊b / σ⌋) : |a - b| ≤ σ := by
  have hl := (le_div_iff₀ hσ).mp (Int.floor_le (a / σ))
  have hu := (div_lt_iff₀ hσ).mp (Int.lt_floor_add_one (a / σ))
  have hl' := (le_div_iff₀ hσ).mp (Int.floor_le (b / σ))
  have hu' := (div_lt_iff₀ hσ).mp (Int.lt_floor_add_one (b / σ))
  rw [h] at hl hu
  apply abs_le.mpr
  constructor <;> nlinarith

/-- A mesh cell is contained in a window of its mesh width. -/
theorem WindowCertificate.to_support {N χ d s m : ℝ} {C : ℕ}
    {R : Fin C → ENNReal} {μ : Fin C → Measure Inc}
    {b : Fin C → Traj → Fin 5 → ℝ} (hN : 0 < N)
    (h : WindowCertificate N χ d s m C R μ b) :
    SupportCertificate N χ d s m C R μ b := by
  classical
  obtain ⟨J, w, Λ, P, S, tag, A, z, hw, htwo, he, ha, hdom, hsignal, hcount, hclose⟩ := h
  refine ⟨J, w, Λ, P, S, tag, A, z, hw, htwo, he, ha, hdom, hsignal, ?_, ?_⟩
  · intro a q
    apply le_trans _ (hcount a ((q 0 : ℝ) * N ^ (-m)) ((q 1 : ℝ) * N ^ (-m)))
    exact_mod_cast Finset.card_le_card (show
      (Finset.univ.filter (fun e => ∃ p ∈ A a,
        scalarZ (b a p.1) p.2 (N ^ (-m)) = q ∧ tag a p = e)) ⊆
      (Finset.univ.filter (fun e => ∃ p ∈ A a,
        |p.2 - (q 0 : ℝ) * N ^ (-m)| ≤ N ^ (-m) ∧
        |scalarY (b a p.1) p.2 - (q 1 : ℝ) * N ^ (-m)| ≤ N ^ (-m) ∧
        tag a p = e)) from by
      intro e he
      obtain ⟨p, hp, hq, htag⟩ := (Finset.mem_filter.mp he).2
      have ht : ⌊p.2 / N ^ (-m)⌋ = q 0 := by
        simpa [scalarZ] using congrFun hq 0
      have hy : ⌊scalarY (b a p.1) p.2 / N ^ (-m)⌋ = q 1 := by
        simpa [scalarZ] using congrFun hq 1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, p, hp,
        floor_window (Real.rpow_pos_of_pos hN _) ht,
        floor_window (Real.rpow_pos_of_pos hN _) hy, htag⟩)
  · intro a p hp p' hp' htag hq
    have ht : ⌊p.2 / N ^ (-m)⌋ = ⌊p'.2 / N ^ (-m)⌋ := by
      simpa [scalarZ] using congrFun hq 0
    have hy : ⌊scalarY (b a p.1) p.2 / N ^ (-m)⌋ =
        ⌊scalarY (b a p'.1) p'.2 / N ^ (-m)⌋ := by
      simpa [scalarZ] using congrFun hq 1
    exact hclose a p hp p' hp' htag
      (floor_distance (Real.rpow_pos_of_pos hN _) ht)
      (floor_distance (Real.rpow_pos_of_pos hN _) hy)

/-- Balanced output forgets its stronger window certificate and bookkeeping. -/
theorem NativeSystemSample.to_packet {N K : ℝ} {W : ℕ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Traj} {E : Fin W → Set Inc}
    {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    {M D : ℕ} {a₀ w loss h χ d s m S U : ℝ} (hN : 0 < N)
    (hs : NativeSystemSample true N K W ω ν E P B M D a₀ w loss h χ d s m S U) :
    PacketSample true N K W ω ν E P B M D loss h χ d s m S U := by
  rcases hs with ⟨T, C, γ, j, c, u, Q, A, F, lst, offset, tangent, law, base, signal,
    hK, hT, hC, hdisj, hlst, hlmeas, hchart, hcoord, hR, hlaw, hmass, hcert, hextra⟩
  exact ⟨T, C, γ, j, c, u, Q, A, F, lst, offset, tangent, law, base, signal,
    hK, hT, hC, hdisj, hlst, hlmeas, hchart, hcoord, hR, hlaw, hmass,
    hcert.to_support hN⟩

theorem NativeSystemAvailable.to_packet {ds kr S η s m U χ w h t : ℝ}
    (hs : NativeSystemAvailable true ds kr S η s m U χ w h t) :
    PacketAvailable true ds kr S η s m U χ h t := by
  obtain ⟨N, K, d, W, ω, ν, E, P, B, f, g, G, hv, hd, hH, a₀, M, D, ha, hs⟩ := hs
  refine ⟨N, K, d, W, ω, ν, E, P, B, f, g, G, hv, hd, hH, M, D, ?_⟩
  intro loss hloss
  exact (hs loss hloss).mono fun k hk => hk.to_packet (lt_of_lt_of_le (by norm_num) (hv.1 k))

theorem BalancedAvailability.to_packets {ds kr S η : ℝ}
    (hs : BalancedAvailability ds kr S η) : PacketAvailability true ds kr S η := by
  obtain ⟨s, m, U, hs, hs1, hsm, hU, hUm, hp⟩ := hs
  exact ⟨s, m, U, hs, hs1, hsm, hU, hUm,
    fun χ h t hχ hh ht => (hp χ h t hχ hh ht).to_packet⟩

theorem preparation_of_localization_balance (hl : LocalizationStatement)
    (hb : BalancedTransportStatement) : PreparationStatement := by
  intro hI ds kr S η hS hη hes hn
  exact (hb hI ds kr S η hS hη hes (hl hI ds kr S η hS hη hes hn)).to_packets

end
end Submission.Obl.k4_unbounded_geometric_packet_reduction
