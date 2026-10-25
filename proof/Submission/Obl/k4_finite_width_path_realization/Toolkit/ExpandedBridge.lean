/- Adapted from same-tree o119, session x0401, commit 19d6f4b3eda81f6d7228948a9996d889733ab672,
   Submission/Obl/k4_finite_width_critical_contradiction/ExpandedBridge.lean (namespace renamed; any
   earlier provenance is kept below). -/
import Submission.Obl.k4_finite_width_path_realization.Toolkit.Expanded

/-! Exact bridges from the frozen lambda expressions to complete problem data. -/

namespace Submission.Obl.k4_finite_width_path_realization

open MeasureTheory Filter

theorem expandedTerminal_iff (p : Data) (h : ℝ) :
    ExpandedTerminal p.N p.K p.L p.W p.ω p.ν p.E p.B p.f h ↔ Terminal p h := by
  simp only [Terminal, terminalAt_iff_expanded, ExpandedTerminal]

theorem narrowTerminalAt_iff_expanded (p : Data) (M D : ℕ) (h w ε : ℝ) (k : ℕ) :
    NarrowTerminalAt p M D h w ε k ↔
      ∃ κ : ℝ, 1 ≤ κ ∧ p.K k ≤ κ ∧ κ ≤ p.N k ^ ε ∧
      ∃ T C : ℕ, ∃ (γ : Fin C → Fin (p.W k)) (j : Fin C → Fin (2 ^ T))
      (c u : Fin C → Spatial) (Q : Fin C → Frame) (R : Fin C → Test)
      (A : Fin C → Set Trajectory) (F : Fin C → Set Incidence),
      (2 : ℝ) ^ T ≤ p.N k ^ (h + ε) ∧
      (∀ b, |Matrix.det (Q b)| * (4 : ℝ) ^ T ≤ p.N k ^ (-w + ε)) ∧
      (C : ℝ) ≤ p.N k ^ M ∧
      (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧
      (∀ b, Chart (p.N k) M D κ T (j b : ℝ) p.L (p.B k (γ b)) (p.E k (γ b))
        (c b) (u b) (Q b) (R b) (A b) (F b)
        (ENNReal.ofReal (p.N k ^ (-p.f p.L) * |Matrix.det (Q b)| /
          ((2 : ℝ) ^ T * κ)) ≤ ((p.ν k (γ b)).prod volume) (F b))) ∧
      ENNReal.ofReal κ⁻¹ ≤ ∑ b, ENNReal.ofReal (p.ω k (γ b)) *
        ((p.ν k (γ b)).prod volume) (F b) := by
  constructor
  · rintro ⟨a, hκ, hK, hε, hT, hwidth, hC, hdis, hcharts, hmass⟩
    exact ⟨a.κ, hκ, hK, hε, a.T, a.C, a.γ, a.j, a.c, a.u, a.Q, a.R,
      a.A, a.F, hT, hwidth, hC, hdis, hcharts, hmass⟩
  · rintro ⟨κ, hκ, hK, hε, T, C, γ, j, c, u, Q, R, A, F,
      hT, hwidth, hC, hdis, hcharts, hmass⟩
    exact ⟨⟨κ, T, C, γ, j, c, u, Q, R, A, F⟩,
      hκ, hK, hε, hT, hwidth, hC, hdis, hcharts, hmass⟩

theorem expandedNarrowTerminal_iff (p : Data) (h w : ℝ) :
    ExpandedNarrowTerminal p.N p.K p.L p.W p.ω p.ν p.E p.B p.f h w ↔
      NarrowTerminal p h w := by
  simp only [NarrowTerminal, narrowTerminalAt_iff_expanded, ExpandedNarrowTerminal]

theorem horizon_eq_expanded (p : Data) :
    horizon p = ExpandedHorizon p.N p.K p.L p.W p.ω p.ν p.E p.B p.f := by
  unfold horizon ExpandedHorizon
  congr 1
  ext h
  exact (expandedTerminal_iff p h).symm

theorem expandedExtremalSetup_to_named {ds rate S η : ℝ}
    (hes : ExpandedExtremalSetup ds rate S η) : ExtremalSetup ds rate S η := by
  obtain ⟨hds, hds1, hrate, hrate1, happrox, hupper, hprofile⟩ := hes
  refine ⟨hds, hds1, hrate, hrate1, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨N, K, d, W, ω, ν, E, P, B, f, g, G, hp, hd, hH⟩ := happrox t ht
    let p : Data := ⟨N, K, 1, d, S, η, W, ω, ν, E, P, B, f, g, G⟩
    refine ⟨⟨p, hp⟩, rfl, rfl, rfl, hd, ?_⟩
    change rate - t < horizon p
    rw [horizon_eq_expanded]
    exact hH
  · intro t ht
    obtain ⟨a, ha, hbound⟩ := hupper t ht
    refine ⟨a, ha, fun p hS hη hd => ?_⟩
    rw [horizon_eq_expanded]
    apply hbound p.1.N p.1.K p.1.L p.1.d p.1.W p.1.ω p.1.ν p.1.E
      p.1.P p.1.B p.1.f p.1.g p.1.G _ hd
    simpa only [Data.Valid, hS, hη] using p.2
  · intro t ht
    obtain ⟨a, ha, hlinear⟩ := hprofile t ht
    refine ⟨a, ha, fun p hS hη hd hH => ?_⟩
    rw [horizon_eq_expanded] at hH
    apply hlinear p.1.N p.1.K p.1.L p.1.d p.1.W p.1.ω p.1.ν p.1.E
      p.1.P p.1.B p.1.f p.1.g p.1.G _ hd hH
    simpa only [Data.Valid, hS, hη] using p.2

theorem expandedBoundedWidth_to_named {ds rate S η : ℝ}
    (hbw : ExpandedBoundedWidth ds rate S η) : BoundedWidth ds rate S η := by
  obtain ⟨a, w, ha, hw, hprobs⟩ := hbw
  refine ⟨a, w, ha, hw, fun t ht => ?_⟩
  obtain ⟨N, K, d, W, ω, ν, E, P, B, f, g, G, hp, hd, hH, hnt⟩ := hprobs t ht
  let p : Data := ⟨N, K, 1, d, S, η, W, ω, ν, E, P, B, f, g, G⟩
  refine ⟨⟨p, hp⟩, ⟨rfl, rfl, rfl, hd, ?_⟩, ?_⟩
  · change rate - t < horizon p
    rw [horizon_eq_expanded]
    exact hH
  · exact fun hn => hnt ((expandedNarrowTerminal_iff p (rate + a) w).mpr hn)

end Submission.Obl.k4_finite_width_path_realization
