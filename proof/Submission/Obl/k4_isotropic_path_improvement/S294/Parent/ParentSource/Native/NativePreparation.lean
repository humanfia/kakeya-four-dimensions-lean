-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativePreparation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativePreparation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativePreparation.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativePreparation.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/NativePreparation.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PathAngularCut
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PreparedHistoryPackets
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.TerminalAncestry

/-! Uniform preparation from the exact substantial native residual. All
exceptional sets and parent masks precede one probability normalization. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

noncomputable def angularPreparationEpsilon (m : ℕ) (κ : ℝ) : ENNReal :=
  ENNReal.ofReal ((8 * (m : ℝ) * κ ^ 2)⁻¹)

theorem angularPreparationEpsilon_ne_zero {m : ℕ} {κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) :
    angularPreparationEpsilon m κ ≠ 0 := by
  apply ENNReal.ofReal_ne_zero_iff.mpr
  positivity

theorem angularPreparationEpsilon_budget {m : ℕ} {κ : ℝ} (hm : 0 < m) (hκ : 0 < κ) :
    angularPreparationEpsilon m κ * ENNReal.ofReal (m * κ) = ENNReal.ofReal (κ⁻¹ / 8) := by
  have hm' : (m : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hm)
  have hκ' : κ ≠ 0 := hκ.ne'
  rw [angularPreparationEpsilon, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- The actual residual, masks, and unchanged parent angular references used
by the later fixed-law entropy window and velocity strip packing. -/
structure PreparedAngularPath {T : Type*} (d : ProblemData) (k : ℕ)
    (p : PathData (d.W k)) (m : ℕ)
    (H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (u : T → ℝ) (τ : ℝ) where
  base : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)
  mask : Fin (d.W k) → Fin p.C → Set (EuclideanSpace ℝ (Fin 3) × ℤ)
  base_measurable : ∀ w, MeasurableSet (base w)
  base_subset : ∀ w, base w ⊆ H w
  velocity_bound : ∀ w q, q ∈ base w → ∀ j, |v q.1 j| ≤ d.K k
  mask_measurable : ∀ w b, MeasurableSet (mask w b)
  residual_measurable : ∀ w, MeasurableSet (d.pathAngularCut k p base mask w)
  residual_subset : ∀ w, d.pathAngularCut k p base mask w ⊆ base w
  original_mass : ENNReal.ofReal (p.κ⁻¹ / 8) ≤
    ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (d.pathAngularCut k p base mask w)
  parent_domination : ∀ b, (d.μ k (p.γ b)).restrict
    (d.pathAngularCut k p base mask (p.γ b) ∩ p.F b) ≤ d.pathAngularReference k p base mask b
  angular_cap : ∀ t b i, d.pathAngularReference k p base mask b
    {q | (fun j => ⌊v q.1 j / δ (d.N k) (u t)⌋) = i} ≤
      (ENNReal.ofReal (d.N k ^ (-d.S * u t + 2 * τ)) * (angularPreparationEpsilon m p.κ)⁻¹) *
        d.pathAngularReference k p base mask b univ
  pointwise_pure_lower : ∀ w q, q ∈ base w →
    ENNReal.ofReal (d.N k ^ (-d.f d.L - τ)) ≤
      d.g k w d.L (obs (d.B k w) (δ (d.N k) d.L) q)
  pointwise_pure_upper : ∀ w q, q ∈ base w →
    d.g k w d.L (obs (d.B k w) (δ (d.N k) d.L) q) ≤
      ENNReal.ofReal (d.N k ^ (-d.f d.L + τ))
  pointwise_angular_upper : ∀ t w q, q ∈ base w →
    d.G k w (u t) (d.angularObs (u t) k w q) ≤
      ENNReal.ofReal (d.N k ^ (-d.f d.L - d.S * u t + τ))
  base_packet_unique : ∀ w q, q ∈ base w → packetUnique p.lev p.γ p.F w q

def PreparedAngularPath.residual {T : Type*} {d : ProblemData} {k : ℕ}
    {p : PathData (d.W k)} {m : ℕ} {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {u : T → ℝ} {τ : ℝ} (Q : PreparedAngularPath d k p m H u τ) :
    Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) := d.pathAngularCut k p Q.base Q.mask

noncomputable def PreparedAngularPath.law {T : Type*} {d : ProblemData} {k : ℕ}
    {p : PathData (d.W k)} {m : ℕ} {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {u : T → ℝ} {τ : ℝ} (Q : PreparedAngularPath d k p m H u τ) :
    Measure (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ)) :=
  preparedResidualLaw (fun w => (d.ν k w).prod volume) (d.ω k) Q.residual

theorem PathData.Valid.residual_subset_event {W : ℕ} {p : PathData W}
    {Nk L : ℝ} {ω : Fin W → ℝ} {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {f : ℝ → ℝ}
    {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ}
    (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hcover : ∀ w, H w ⊆ {q | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ q ∈ p.F b}) :
    ∀ w, H w ⊆ E w := by
  intro w q hq
  obtain ⟨b, _, hbw, hqb⟩ := hcover w hq
  have hFb := (h.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.2.2.2.1 q hqb
  simpa only [hbw] using hFb.1

/-- The cutoff and path-factor exponent are fixed before the supplied path
and substantial residual. Its prepared law has original mass at least 1/(8κ). -/
theorem ProblemData.Valid.prepare_native_angular_path_exact {T : Type*} [Fintype T]
    {d : ProblemData} (hd : d.Valid) (κ₁ : ℝ) (m : ℕ) (hm : 0 < m)
    (s : ℕ → ℝ) (δ₀ : ℝ) (Mp Dp : ℕ) (u : T → ℝ)
    (hu : ∀ t, 0 < u t ∧ u t ≤ d.η * d.L) (τ : ℝ) (hτ : 0 < τ) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ k in atTop, ∀ p : PathData (d.W k),
      p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ →
      ∀ H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ),
      (∀ w, MeasurableSet (H w)) →
      (∀ w, H w ⊆ {q | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ q ∈ p.F b}) →
      ENNReal.ofReal (p.κ⁻¹ / 2) ≤
        ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (H w) →
      Nonempty (PreparedAngularPath d k p m H u τ) := by
  have hL : 0 < d.L := hd.2.2.2.1
  obtain ⟨σ, hσ, hclean⟩ := hd.cleanup_tests (fun _ : Unit => d.L) u τ hτ
    (fun _ => ⟨hL.le, le_rfl⟩) hu
  refine ⟨σ, hσ, hclean.mono ?_⟩
  intro k hk p hp H hH hcover hmass
  have hHE := hp.residual_subset_event H hcover
  have hnative := hd.clean_native_velocity k H hH
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  let H₀ : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ) := fun w =>
    nativeVelocityResidual H (d.K k) w ∩ {z | packetUnique p.lev p.γ p.F w z}
  have hH₀sub (w : Fin (d.W k)) : H₀ w ⊆ H w :=
    inter_subset_left.trans (hnative.1 w).2.1
  have hH₀ (w : Fin (d.W k)) : MeasurableSet (H₀ w) ∧ H₀ w ⊆ d.E k w :=
    ⟨(hnative.1 w).1.inter (measurableSet_packetUnique p.lev p.γ p.F hF w),
      (hH₀sub w).trans (hHE w)⟩
  have hmass_eq (w : Fin (d.W k)) : ((d.ν k w).prod volume) (H₀ w) =
      ((d.ν k w).prod volume) (H w) := by
    calc
      _ = ((d.ν k w).prod volume) (nativeVelocityResidual H (d.K k) w) := by
        apply measure_congr
        filter_upwards [hp.ae_packet_unique w] with z hz
        simp only [H₀, mem_inter_iff, mem_ofPred_eq, hz, and_true]
      _ = _ := hnative.2 w
  have hmass₀ : ENNReal.ofReal (p.κ⁻¹ / 2) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (H₀ w) := by
    simpa only [hmass_eq] using hmass
  obtain ⟨hbase, hpure, hangular, hmassbase⟩ := hk p.κ hp.1 hp.2.1 H₀ hH₀ hmass₀
  let base := d.pruneTests (fun _ : Unit => d.L) u τ k H₀
  have hbaseE (w : Fin (d.W k)) : base w ⊆ d.E k w := (hbase w).2.trans (hH₀ w).2
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one hp.1
  have hbudget : angularPreparationEpsilon m p.κ * ENNReal.ofReal (m * p.κ) ≤
      ENNReal.ofReal ((p.κ⁻¹ / 4) / 2) := by
    rw [angularPreparationEpsilon_budget hm hκ]
    have heq : p.κ⁻¹ / 8 = (p.κ⁻¹ / 4) / 2 := by ring
    rw [heq]
  have hknown : ∀ w b q, q ∈ base w ∩ (if p.γ b = w then p.F b else ∅) →
      b ∈ terminalAncestorList p m w (obs (d.B k w) (δ (d.N k) d.L) q) := by
    intro w b q hq
    by_cases hb : p.γ b = w
    · have hqb : q ∈ p.F b := by simpa only [ite_eq_left hb] using hq.2
      exact hp.terminalAncestorList_mem w q ((hbase w).2 hq.1).2
        (hcover w (hH₀sub w ((hbase w).2 hq.1))) b hb hqb
    · simp only [ite_eq_right hb, mem_inter_iff, mem_empty_iff_false, and_false] at hq
  obtain ⟨A, hA, hcut, hcutmass, hdom, hcap⟩ := hd.prepare_path_angular_cut_of_list k p κ₁ m s δ₀
    Mp Dp σ hp u hu τ base (fun w => (hbase w).1) hbaseE
    (terminalAncestorList p m) (terminalAncestorList_card p m hp.2.2.2.2.2.1) hknown
    (fun w q hq => (hpure w q hq ()).1) (fun t w q hq => hangular w q hq t)
    (angularPreparationEpsilon m p.κ)
    (angularPreparationEpsilon_ne_zero hm hκ) ENNReal.ofReal_ne_top
    (by positivity) hbudget hmassbase
  refine ⟨{
    base := base
    mask := A
    base_measurable := fun w => (hbase w).1
    base_subset := fun w => (hbase w).2.trans (hH₀sub w)
    velocity_bound := fun w q hq => (hnative.1 w).2.2 q ((hbase w).2 hq).1
    mask_measurable := hA
    residual_measurable := fun w => (hcut w).1
    residual_subset := fun w => (hcut w).2
    original_mass := ?_
    parent_domination := hdom
    angular_cap := hcap
    pointwise_pure_lower := fun w q hq => (hpure w q hq ()).1
    pointwise_pure_upper := fun w q hq => (hpure w q hq ()).2
    pointwise_angular_upper := fun t w q hq => hangular w q hq t
    base_packet_unique := fun w q hq => ((hbase w).2 hq).2 }⟩
  have heq : (p.κ⁻¹ / 4) / 2 = p.κ⁻¹ / 8 := by ring
  simpa only [heq] using hcutmass


/-- The cutoff and path-factor exponent are fixed before the supplied path
and substantial residual. Its prepared law has original mass at least 1/(8κ). -/
theorem ProblemData.Valid.prepare_native_angular_path {T : Type*} [Fintype T]
    {d : ProblemData} (hd : d.Valid) (κ₁ : ℝ) (m : ℕ) (hm : 0 < m)
    (s : ℕ → ℝ) (δ₀ : ℝ) (Mp Dp : ℕ) (u : T → ℝ)
    (hu : ∀ t, 0 < u t ∧ u t ≤ d.η * d.L) (τ : ℝ) (hτ : 0 < τ) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ᶠ k in atTop, ∀ p : PathData (d.W k),
      p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ →
      (∀ i, i < m → p.r i ≤ d.L) →
      ∀ H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ),
      (∀ w, MeasurableSet (H w)) →
      (∀ w, H w ⊆ {q | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ q ∈ p.F b}) →
      ENNReal.ofReal (p.κ⁻¹ / 2) ≤
        ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (H w) →
      Nonempty (PreparedAngularPath d k p m H u τ) := by
  obtain ⟨σ, hσ, hk⟩ := hd.prepare_native_angular_path_exact κ₁ m hm s δ₀ Mp Dp u hu τ hτ
  refine ⟨σ, hσ, hk.mono ?_⟩
  intro k hk p hp _ H hH hcover hmass
  exact hk p hp H hH hcover hmass

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
