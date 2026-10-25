/- Adapted in part from same-tree o119, x0401, commit 0635e405b51a9c36a0b077a4a0c0cb6e4fb743c4,
   Expanded.lean, InitialBridge.lean and ExpandedBridge.lean in
   Submission/Obl/k4_finite_width_critical_contradiction/.
   The source InitialBridge is adapted from o105, x0351, commit 735310f,
   Submission/Obl/k4_critical_path_framework/Bridge.lean. -/
import Submission.Obl.k4_known_atlas_normalization_composition.Transfer

namespace Submission.Obl.k4_known_atlas_normalization_composition

open MeasureTheory Filter

noncomputable def ExpandedTerminal : (ℕ → ℝ) → (ℕ → ℝ) → ℝ → (W : ℕ → ℕ) → ((k : ℕ) → Fin (W k) → ℝ) → ((k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ((k : ℕ) → Fin (W k) → ℝ) → (ℝ → ℝ) → ℝ → Prop :=
  (fun N K L W ω ν E B f h => ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, ∃ κ : ℝ, 1 ≤ κ ∧ K k ≤ κ ∧ κ ≤ N k ^ ε ∧ ∃ T C' : ℕ, ∃ (γ : Fin (C') → Fin (W k)) (j : Fin (C') → Fin (2 ^ T)) (c u : Fin (C') → EuclideanSpace ℝ (Fin 2)) (Q : Fin (C') → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin (C') → MvPolynomial (Fin 4) ℝ) (A : Fin (C') → Set (ℕ × (Fin 6 → ℝ))) (F : Fin (C') → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)), (2 : ℝ) ^ T ≤ N k ^ h ∧ (C' : ℝ) ≤ N k ^ M ∧ (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧ (∀ b, Chart (N k) M D κ T ((j b : ℕ) : ℝ) L (B k (γ b)) (E k (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) (ENNReal.ofReal (N k ^ (-f L) * |Matrix.det (Q b)| / ((2 : ℝ) ^ T * κ)) ≤ (((ν k (γ b)).prod MeasureTheory.volume) (F b)))) ∧ ENNReal.ofReal ((κ)⁻¹) ≤ ∑ b, ENNReal.ofReal (ω k (γ b)) * (((ν k (γ b)).prod MeasureTheory.volume) (F b)))

noncomputable def ExpandedNarrowTerminal : (ℕ → ℝ) → (ℕ → ℝ) → ℝ → (W : ℕ → ℕ) → ((k : ℕ) → Fin (W k) → ℝ) → ((k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 6 → ℝ))) → ((k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) → ((k : ℕ) → Fin (W k) → ℝ) → (ℝ → ℝ) → ℝ → ℝ → Prop :=
  (fun N K L W ω ν E B f h w => ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, ∃ κ : ℝ, 1 ≤ κ ∧ K k ≤ κ ∧ κ ≤ N k ^ ε ∧ ∃ T C' : ℕ, ∃ (γ : Fin (C') → Fin (W k)) (j : Fin (C') → Fin (2 ^ T)) (c u : Fin (C') → EuclideanSpace ℝ (Fin 2)) (Q : Fin (C') → Matrix (Fin 2) (Fin 2) ℝ) (R : Fin (C') → MvPolynomial (Fin 4) ℝ) (A : Fin (C') → Set (ℕ × (Fin 6 → ℝ))) (F : Fin (C') → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)), (2 : ℝ) ^ T ≤ N k ^ (h + ε) ∧ (∀ b, |Matrix.det (Q b)| * (4 : ℝ) ^ T ≤ N k ^ (-w + ε)) ∧ (C' : ℝ) ≤ N k ^ M ∧ (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧ (∀ b, Chart (N k) M D κ T ((j b : ℕ) : ℝ) L (B k (γ b)) (E k (γ b)) (c b) (u b) (Q b) (R b) (A b) (F b) (ENNReal.ofReal (N k ^ (-f L) * |Matrix.det (Q b)| / ((2 : ℝ) ^ T * κ)) ≤ (((ν k (γ b)).prod MeasureTheory.volume) (F b)))) ∧ ENNReal.ofReal ((κ)⁻¹) ≤ ∑ b, ENNReal.ofReal (ω k (γ b)) * (((ν k (γ b)).prod MeasureTheory.volume) (F b)))

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


/-- The parent input with the literal tuple quantifiers of the frozen theorem. -/
def ExpandedKnown (p : Data) (r h w : ℝ) : Prop :=
  ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
    ∃ κ : ℝ, 1 ≤ κ ∧ κ ≤ p.N k ^ ε ∧ ∃ T C : ℕ,
    ∃ (γ : Fin C → Fin (p.W k)) (j : Fin C → Fin (2 ^ T))
      (c u : Fin C → Spatial) (Q : Fin C → Frame) (R : Fin C → Test)
      (A : Fin C → Set Trajectory) (F : Fin C → Set Incidence)
      (lst : Fin (p.W k) → Observation → Finset (Fin C)),
      (2 : ℝ) ^ T ≤ p.N k ^ (h + ε) ∧
      (∀ b, |Matrix.det (Q b)| * (4 : ℝ) ^ T ≤ p.N k ^ (-w + ε)) ∧
      (C : ℝ) ≤ p.N k ^ M ∧
      (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧
      (∀ γ₁ o, ((lst γ₁ o).card : ℝ) ≤ κ) ∧
      (∀ b, Chart (p.N k) M D κ T (j b : ℝ) r (p.B k (γ b)) (p.E k (γ b))
        (c b) (u b) (Q b) (R b) (A b) (F b)
        (∀ z ∈ F b, b ∈ lst (γ b) (obs (p.B k (γ b)) (δ (p.N k) p.L) z))) ∧
      ENNReal.ofReal κ⁻¹ ≤ ∑ b, ENNReal.ofReal (p.ω k (γ b)) *
        ((p.ν k (γ b)).prod volume) (F b)

theorem expandedKnown_iff (p : Data) (r h w : ℝ) :
    ExpandedKnown p r h w ↔ Known p r h w := by
  constructor
  · rintro ⟨M, D, hs⟩
    refine ⟨M, D, fun ε hε => (hs ε hε).mono fun k hk => ?_⟩
    obtain ⟨κ, hκ, hε, T, C, γ, j, c, u, Q, R, A, F, lst,
      hT, hwidth, hC, hdis, hlist, hcharts, hmass⟩ := hk
    exact ⟨⟨κ, T, C, γ, j, c, u, Q, R, A, F⟩, lst,
      hκ, hε, hT, hwidth, hC, hdis, hlist, hcharts, hmass⟩
  · rintro ⟨M, D, hs⟩
    refine ⟨M, D, fun ε hε => (hs ε hε).mono fun k hk => ?_⟩
    obtain ⟨a, lst, hκ, hε, hT, hwidth, hC, hdis, hlist, hcharts, hmass⟩ := hk
    exact ⟨a.κ, hκ, hε, a.T, a.C, a.γ, a.j, a.c, a.u, a.Q, a.R,
      a.A, a.F, lst, hT, hwidth, hC, hdis, hlist, hcharts, hmass⟩

end Submission.Obl.k4_known_atlas_normalization_composition
