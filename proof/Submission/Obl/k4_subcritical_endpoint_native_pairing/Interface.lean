/- Adapted from this LOT tree, obligation o249, session x0876, commit b00105b82d24db6d8501c6401ba2acd5156b7922,
   Submission/Obl/k4_horizontal_endpoint_three_projections/PairedInterface.lean;
   its accepted o212 data type and original source attributions are retained. -/
import Submission.Obl.k4_subcritical_endpoint_native_pairing.Model

/-! The comparison cut retains the original endpoint families and their full
domains. Only incidence coverage is restricted. In particular, no sliced native
or endpoint mass is used as a reference weight. -/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing

open MeasureTheory Set Filter

noncomputable section

namespace Data

open Submission.Obl.k4_critical_intercept_concentration.Data (I)

variable {α : Type} [MeasurableSpace α] (cfg : Data α)

/-- The native affine graph written in static horizontal parameters at the
original velocity-bin representative. The horizontal atlas makes `F` affine
with hidden coefficient one. -/
def nativeParameter (k : ℕ) (s : ℝ) (i : Fin (cfg.n k s))
    (v t p q : ℝ) : ℝ :=
  -MvPolynomial.eval ![t, p + t * v, q - t * p, 0] (cfg.F k s i)

/-- Simultaneous comparison at the coarse and auxiliary endpoint depths. The
full-time floors refer to `cfg.ρ`, before the comparison law is restricted. -/
def PairedAt (k : ℕ) (M RE s₀ ε : ℝ) : Prop :=
  let depth : Fin 2 → ℝ := ![s₀, 3 * s₀ / 2]
  let χ := cfg.N k ^ (-M)
  ∃ (σ : Measure (α × ℝ)) (nH : Fin 2 → ℕ)
    (AH : (r : Fin 2) → Fin (nH r) → Set α)
    (qH : (r : Fin 2) → Fin (nH r) → Fin 3 → ℤ)
    (hH : (r : Fin 2) → Fin (nH r) → Fin 6 → ℝ)
    (paired : (r : Fin 2) → Fin (nH r) → Fin (cfg.n k (depth r)) → Prop),
    σ ≤ cfg.ρ k ∧ ENNReal.ofReal (cfg.N k ^ (-ε)) ≤ σ univ ∧
    (∀ r, (fun D a : ℝ =>
      (∀ h, MeasurableSet (AH r h)) ∧
      (∀ h h', h ≠ h' → Disjoint (AH r h) (AH r h')) ∧
      (∀ h,
        (∀ l ∈ AH r h, ⌊cfg.b k l 3 / χ⌋ = qH r h 0 ∧
          ⌊cfg.b k l 0 / D⌋ = qH r h 1 ∧ ⌊cfg.b k l 1 / D⌋ = qH r h 2) ∧
        (∀ e, |hH r h e| ≤ cfg.N k ^ RE) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          ∀ p ∈ Icc ((qH r h 1 : ℝ) * D) (((qH r h 1 : ℝ) + 1) * D),
          ∀ q ∈ Icc ((qH r h 2 : ℝ) * D) (((qH r h 2 : ℝ) + 1) * D),
          |predictor (hH r h) t p q| ≤ cfg.N k ^ ε) ∧
        (∀ l ∈ AH r h, ∀ t ∈ Icc (0 : ℝ) 1,
          |(cfg.x k l t) 3 - predictor (hH r h) t (cfg.b k l 0) (cfg.b k l 1)| ≤
            cfg.N k ^ ε * a) ∧
        ENNReal.ofReal (D ^ 2 * a ^ cfg.d / cfg.N k ^ ε) *
          cfg.π k (Ico ((qH r h 0 : ℝ) * χ) (((qH r h 0 : ℝ) + 1) * χ)) ≤
          cfg.ρ k (AH r h ×ˢ Icc (0 : ℝ) 1)) ∧
      (∀ h i, paired r h i →
        ∀ t ∈ I (cfg.T k (depth r)) (cfg.j k (depth r) i),
        ∀ p ∈ Icc ((qH r h 1 : ℝ) * D) (((qH r h 1 : ℝ) + 1) * D),
        ∀ q ∈ Icc ((qH r h 2 : ℝ) * D) (((qH r h 2 : ℝ) + 1) * D),
          |cfg.nativeParameter k (depth r) i ((qH r h 0 : ℝ) * χ) t p q -
            predictor (hH r h) t p q| ≤ cfg.N k ^ ε * a) ∧
      (∀ h (j₀ : Fin (2 ^ cfg.T k (depth r))),
        (Set.ncard {i : Fin (cfg.n k (depth r)) |
          paired r h i ∧ cfg.j k (depth r) i = j₀} : ℝ) ≤ cfg.N k ^ ε))
      (cfg.N k ^ (-2 * cfg.κ * depth r)) (cfg.N k ^ (-depth r))) ∧
    (∀ᵐ p ∂σ, ∀ r : Fin 2, ∃ h i,
      p.1 ∈ AH r h ∧ p.1 ∈ cfg.B k (depth r) i ∧
      p.2 ∈ I (cfg.T k (depth r)) (cfg.j k (depth r) i) ∧ paired r h i)

/-- The comparison conclusion at every positive loss. -/
def PairedReady (M RE s₀ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, cfg.PairedAt k M RE s₀ ε

end Data

end

end Submission.Obl.k4_subcritical_endpoint_native_pairing
