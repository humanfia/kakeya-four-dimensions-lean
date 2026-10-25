/- Adapted from this LOT tree, o105, sessions x0351 and x0367,
Submission/Obl/k4_critical_path_framework/Bridge.lean at origin/split/s042. -/
import Submission.Obl.k4_extremal_profile_setup.Horizon
import Submission.Obl.k4_extremal_profile_setup.Expanded

/-! Definitional bridges from the frozen statements to the named predicates. -/

namespace Submission.Obl.k4_extremal_profile_setup

open MeasureTheory Filter

/-- Expanding the record of chart data reproduces the frozen sample conclusion. -/
theorem terminalAt_iff_expanded (p : Data) (M D : ℕ) (h ε : ℝ) (k : ℕ) :
    TerminalAt p M D h ε k ↔
      ∃ κ : ℝ, 1 ≤ κ ∧ p.K k ≤ κ ∧ κ ≤ p.N k ^ ε ∧
      ∃ T C : ℕ, ∃ (γ : Fin C → Fin (p.W k)) (j : Fin C → Fin (2 ^ T))
      (c u : Fin C → Spatial) (Q : Fin C → Frame) (R : Fin C → Test)
      (A : Fin C → Set Trajectory) (F : Fin C → Set Incidence),
      (2 : ℝ) ^ T ≤ p.N k ^ h ∧ (C : ℝ) ≤ p.N k ^ M ∧
      (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧
      (∀ b, Chart (p.N k) M D κ T (j b : ℝ) p.L (p.B k (γ b)) (p.E k (γ b))
        (c b) (u b) (Q b) (R b) (A b) (F b)
        (ENNReal.ofReal (p.N k ^ (-p.f p.L) * |Matrix.det (Q b)| /
          ((2 : ℝ) ^ T * κ)) ≤ ((p.ν k (γ b)).prod volume) (F b))) ∧
      ENNReal.ofReal κ⁻¹ ≤ ∑ b, ENNReal.ofReal (p.ω k (γ b)) *
        ((p.ν k (γ b)).prod volume) (F b) := by
  constructor
  · rintro ⟨a, hκ, hK, hε, hT, hC, hdis, hcharts, hmass⟩
    exact ⟨a.κ, hκ, hK, hε, a.T, a.C, a.γ, a.j, a.c, a.u, a.Q, a.R,
      a.A, a.F, hT, hC, hdis, hcharts, hmass⟩
  · rintro ⟨κ, hκ, hK, hε, T, C, γ, j, c, u, Q, R, A, F,
      hT, hC, hdis, hcharts, hmass⟩
    exact ⟨⟨κ, T, C, γ, j, c, u, Q, R, A, F⟩,
      hκ, hK, hε, hT, hC, hdis, hcharts, hmass⟩

/-- The initial horizon hypothesis has exactly the named interface. -/
theorem initialHorizon_iff : InitialHorizonExpanded ↔ InitialHorizon := by
  constructor
  · intro hi p hp h hh
    obtain ⟨M, D, hs⟩ := hi p.N p.K p.L p.d p.S p.η p.W p.ω p.ν p.E p.P p.B
      p.f p.g p.G hp h hh
    refine ⟨M, D, fun ε hε => (hs ε hε).mono fun k hk => ?_⟩
    exact (terminalAt_iff_expanded p M D h ε k).mpr hk
  · intro hi N K L d S η W ω ν E P B f g G hp h hh
    let p : Data := ⟨N, K, L, d, S, η, W, ω, ν, E, P, B, f, g, G⟩
    obtain ⟨M, D, hs⟩ := hi p hp h hh
    refine ⟨M, D, fun ε hε => (hs ε hε).mono fun k hk => ?_⟩
    exact (terminalAt_iff_expanded p M D h ε k).mp hk

end Submission.Obl.k4_extremal_profile_setup

namespace Submission.Obl.k4_extremal_profile_setup

theorem terminalExpanded_iff (p : Data) (h : ℝ) :
    TerminalExpanded p.N p.K p.L p.W p.ω p.ν p.E p.B p.f h ↔ Terminal p h := by
  constructor
  · rintro ⟨M, D, hs⟩
    exact ⟨M, D, fun ε hε => (hs ε hε).mono fun k hk =>
      (terminalAt_iff_expanded p M D h ε k).mpr hk⟩
  · rintro ⟨M, D, hs⟩
    exact ⟨M, D, fun ε hε => (hs ε hε).mono fun k hk =>
      (terminalAt_iff_expanded p M D h ε k).mp hk⟩

theorem horizonExpanded_eq (p : Data) :
    HorizonExpanded p.N p.K p.L p.W p.ω p.ν p.E p.B p.f = horizon p := by
  unfold HorizonExpanded horizon
  congr 1
  ext h
  exact terminalExpanded_iff p h

theorem extremalSetup_of_record {ds kr S η : ℝ} (he : ExtremalProfile ds kr S η) :
    ExtremalSetupExpanded ds kr S η := by
  obtain ⟨hds, hds1, hkr, hkr1, hnear, hupper, hlinear⟩ := he
  refine ⟨hds, hds1, hkr, hkr1, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨p, hpL, hpd, hpr⟩ := hnear t ht
    refine ⟨p.1.N, p.1.K, p.1.d, p.1.W, p.1.ω, p.1.ν, p.1.E, p.1.P,
      p.1.B, p.1.f, p.1.g, p.1.G, ?_, hpd, ?_⟩
    · simpa only [Data.Valid, hpL, p.2.2.1, p.2.2.2] using p.2.1
    · have hh : HorizonExpanded p.1.N p.1.K 1 p.1.W p.1.ω p.1.ν p.1.E p.1.B p.1.f =
          horizon p.1 := by
        rw [← hpL]
        exact horizonExpanded_eq p.1
      simpa only [hh] using hpr
  · intro t ht
    obtain ⟨a, ha, hu⟩ := hupper t ht
    refine ⟨a, ha, ?_⟩
    intro N K L d W ω ν E P B f g G hp hd
    let p : Data := ⟨N, K, L, d, S, η, W, ω, ν, E, P, B, f, g, G⟩
    change HorizonExpanded p.N p.K p.L p.W p.ω p.ν p.E p.B p.f ≤ (kr + t) * p.L
    rw [horizonExpanded_eq p]
    exact hu ⟨p, hp, rfl, rfl⟩ hd
  · intro t ht
    obtain ⟨a, ha, hl⟩ := hlinear t ht
    refine ⟨a, ha, ?_⟩
    intro N K L d W ω ν E P B f g G hp hd hH r hr hrL
    let p : Data := ⟨N, K, L, d, S, η, W, ω, ν, E, P, B, f, g, G⟩
    change (kr - a) * p.L < HorizonExpanded p.N p.K p.L p.W p.ω p.ν p.E p.B p.f at hH
    rw [horizonExpanded_eq p] at hH
    exact hl ⟨p, hp, rfl, rfl⟩ hd hH r hr hrL

end Submission.Obl.k4_extremal_profile_setup
