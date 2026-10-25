/- Adapted from this LOT tree, o197, session x0690, Pairing/ProblemDensities.lean (o197 branch x0690,
   refs/merged/o197/x0690); preserving original attributions below. -/
/- Adapted from this LOT tree, o178, session x0596, commit aff0309c5b5be9920172fe7e367c31d64a3a01e3;
   Submission/Obl/k4_unbounded_geometric_packet_reduction/ProblemDensities.lean.
   The original file and its provenance are preserved below. -/
import Submission.Obl.k4_finite_width_output_exclusion.Interfaces
import Submission.Obl.k4_raw_localized_native_systems.Pairing.AngularTransfer

/-!
# Density clauses of a valid exact problem, and angular charging

Accessors for the observation densities `g`, the joint angular densities `G`,
their typicality and the angular cap of a valid problem (o153 `Data`/`Valid`),
and the angular charging estimate: on incidences that are typical at the
terminal depth and good for the angular cap at width `u`, listing at most `m`
velocity bins per terminal observation costs a factor `N^(-S u + 2τ) m`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.Pairing

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The joint terminal observation and velocity bin of an incidence. -/
def jointObs (B Nk L u : ℝ) (q : Point) : Observation × (Fin 2 → ℤ) :=
  (obs B (δ Nk L) q, fun j : Fin 2 => ⌊(v q.1) j / δ Nk u⌋)

/-- The velocity bin of an incidence at angular depth `u`. -/
def velBin (Nk u : ℝ) (q : Point) : Fin 2 → ℤ := fun j : Fin 2 => ⌊(v q.1) j / δ Nk u⌋

theorem measurable_obs' (B a : ℝ) : Measurable (obs B a) := by
  unfold obs x
  fun_prop

theorem measurable_v' : Measurable (v : Line → Plane) := by
  unfold v
  fun_prop

theorem measurable_velBin (Nk u : ℝ) : Measurable (velBin Nk u) := by
  unfold velBin v
  fun_prop

theorem jointObs_eq (B Nk L u : ℝ) :
    jointObs B Nk L u = fun q => (obs B (δ Nk L) q, velBin Nk u q) := rfl

section Accessors

variable {p : Data}

theorem valid_g_spec (hp : Valid p) (k : ℕ) (γ : Fin (p.W k)) {r : ℝ}
    (hr : 0 ≤ r) (hrL : r ≤ p.L) :
    Measurable (p.g k γ r) ∧
      Measure.map (obs (p.B k γ) (δ (p.N k) r)) (selected p k γ) =
        (volume.prod Measure.count).withDensity (p.g k γ r) :=
  hp.2.2.2.2.2.2.2.2.2.1 k γ r hr hrL

theorem valid_G_spec (hp : Valid p) (k : ℕ) (γ : Fin (p.W k)) {u : ℝ}
    (hu : 0 < u) (huη : u ≤ p.η * p.L) :
    Measurable (p.G k γ u) ∧
      Measure.map (jointObs (p.B k γ) (p.N k) p.L u) (selected p k γ) =
        ((volume.prod Measure.count).prod Measure.count).withDensity (p.G k γ u) :=
  hp.2.2.2.2.2.2.2.2.2.2.1 k γ u hu huη

/-- The typicality clause of a valid problem. -/
theorem valid_typical (hp : Valid p) {r τ : ℝ} (hr : 0 ≤ r) (hrL : r ≤ p.L) (hτ : 0 < τ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      (∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ
        {q | p.g k γ r (obs (p.B k γ) (δ (p.N k) r) q) <
              ENNReal.ofReal (p.N k ^ (-p.f r - τ)) ∨
            ENNReal.ofReal (p.N k ^ (-p.f r + τ)) <
              p.g k γ r (obs (p.B k γ) (δ (p.N k) r) q)}) ≤
        ENNReal.ofReal (p.N k ^ (-c)) :=
  hp.2.2.2.2.2.2.2.2.2.2.2.2.1 r τ hr hrL hτ

/-- The angular cap clause of a valid problem. -/
theorem valid_angular (hp : Valid p) {u τ : ℝ} (hu : 0 < u) (huη : u ≤ p.η * p.L)
    (hτ : 0 < τ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      (∑ γ, ENNReal.ofReal (p.ω k γ) * selected p k γ
        {q | ENNReal.ofReal (p.N k ^ (-p.f p.L - p.S * u + τ)) <
          p.G k γ u (jointObs (p.B k γ) (p.N k) p.L u q)}) ≤
        ENNReal.ofReal (p.N k ^ (-c)) :=
  hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2 u τ hu huη hτ

end Accessors

/-- Incidences that are typical at the terminal depth and good for the angular
cap at width `u` (both with tolerance `τ`). -/
def AngGood (p : Data) (k : ℕ) (γ : Fin (p.W k)) (u τ : ℝ) (q : Point) : Prop :=
  p.G k γ u (jointObs (p.B k γ) (p.N k) p.L u q) ≤
      ENNReal.ofReal (p.N k ^ (-p.f p.L - p.S * u + τ)) ∧
    ENNReal.ofReal (p.N k ^ (-p.f p.L - τ)) ≤ p.g k γ p.L (obs (p.B k γ) (δ (p.N k) p.L) q)

theorem rpow_split (N a b : ℝ) (hN : 0 < N) : N ^ (a + b) = N ^ a * N ^ b :=
  Real.rpow_add hN a b

/-- On good incidences the joint density is at most `N^(-S u + 2τ)` times the
pure terminal density. -/
theorem AngGood.G_le {p : Data} {k : ℕ} {γ : Fin (p.W k)} {u τ : ℝ} {q : Point}
    (hN : 0 < p.N k) (hq : AngGood p k γ u τ q) :
    p.G k γ u (jointObs (p.B k γ) (p.N k) p.L u q) ≤
      ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) *
        p.g k γ p.L (obs (p.B k γ) (δ (p.N k) p.L) q) := by
  refine hq.1.trans ?_
  have hsplit : p.N k ^ (-p.f p.L - p.S * u + τ) =
      p.N k ^ (-p.S * u + 2 * τ) * p.N k ^ (-p.f p.L - τ) := by
    rw [← Real.rpow_add hN]; ring_nf
  rw [hsplit, ENNReal.ofReal_mul (Real.rpow_nonneg hN.le _)]
  gcongr
  exact hq.2

/-- **Angular charging for a valid problem.**  Among good incidences of one
world, those whose velocity bin is in a measurable list of at most `m` bins
determined by the terminal observation have mass at most
`N^(-S u + 2τ) * m` times the world's selected mass. -/
theorem angular_listed_le {p : Data} (hp : Valid p) (k : ℕ) (γ : Fin (p.W k))
    {u τ : ℝ} (hu : 0 < u) (huη : u ≤ p.η * p.L)
    (bins : Observation → Finset (Fin 2 → ℤ)) (m : ℕ)
    (hbins : ∀ w, MeasurableSet {o | w ∈ bins o}) (hcard : ∀ o, (bins o).card ≤ m) :
    selected p k γ {q | AngGood p k γ u τ q ∧
        velBin (p.N k) u q ∈ bins (obs (p.B k γ) (δ (p.N k) p.L) q)} ≤
      ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) * m * selected p k γ Set.univ := by
  have hN : 0 < p.N k := hp.scale_pos k
  obtain ⟨hGm, hG⟩ := valid_G_spec hp k γ hu huη
  obtain ⟨hgm, hg⟩ := valid_g_spec hp k γ hp.length_pos.le le_rfl
  have hsub : {q | AngGood p k γ u τ q ∧
        velBin (p.N k) u q ∈ bins (obs (p.B k γ) (δ (p.N k) p.L) q)} ⊆
      {q | p.G k γ u (obs (p.B k γ) (δ (p.N k) p.L) q, velBin (p.N k) u q) ≤
          ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) *
            p.g k γ p.L (obs (p.B k γ) (δ (p.N k) p.L) q) ∧
        velBin (p.N k) u q ∈ bins (obs (p.B k γ) (δ (p.N k) p.L) q)} := by
    intro q hq
    exact ⟨hq.1.G_le hN, hq.2⟩
  refine (measure_mono hsub).trans ?_
  rw [jointObs_eq] at hG
  exact listed_bins_mass_le (selected p k γ) (volume.prod Measure.count)
    (obs (p.B k γ) (δ (p.N k) p.L)) (velBin (p.N k) u) (measurable_obs' _ _)
    (measurable_velBin _ _) (p.G k γ u) (p.g k γ p.L) hGm hgm hG hg _ bins m hbins hcard

end

end Submission.Obl.k4_raw_localized_native_systems.Pairing
