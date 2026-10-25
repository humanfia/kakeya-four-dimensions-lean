import Submission.Obl.k4_pair_bin_atlas_assembly.PairChoice
import Submission.Obl.k4_pair_bin_atlas_assembly.RepresentativeDeletion

namespace Submission.Obl.k4_pair_bin_atlas_assembly

open Set MeasureTheory
open scoped ENNReal

namespace PairData

variable {Nk : ℝ} {Wk : ℕ}
    {ωk : Fin Wk → ℝ} {νk : Fin Wk → Measure Trajectory}
    {Ek : Fin Wk → Set Incidence} {Bk : Fin Wk → ℝ}
    {L a h : ℝ} {M D : ℕ} {ε : ℝ}
    (p : PairData Nk Wk ωk νk Ek Bk L a h M D ε)
    {Cs : ℕ} (k : BinKernel Cs)

/-- Original incidence sections after anchor choice, finite source-bin coins,
and shared source-time freezing. -/
structure FrozenPairs (CD : ℝ)
    (eligible : AnchorParameter → Fin p.J → (Fin k.d → ℤ) → Set Trajectory) where
  θ : AnchorParameter
  θ_mem : θ ∈ anchorDomain
  coin : Fin p.m → (Fin k.d → ℤ)
  time : Fin (2 ^ p.T) → ℝ
  time_mem : ∀ b : Fin (2 ^ p.T), time b ∈
    Icc ((b : ℝ) / (2 : ℝ) ^ p.T) (((b : ℝ) + 1) / (2 : ℝ) ^ p.T)
  F : Fin p.m → Set Incidence
  F_measurable : ∀ s, MeasurableSet (F s)
  F_source : ∀ s, ∀ v ∈ F s, (v.1, time (p.timeIndex s)) ∈ p.S s
  F_target : ∀ s, ∀ v ∈ F s, v ∈ Ek (p.world s) ∧ v.2 ∈ p.block s
  F_coin : ∀ s, ∀ v ∈ F s, coin s ∈ p.bins k θ.1 s
  F_representative : ∀ s, ∀ v ∈ F s, ∃ r,
    p.representative (p.bins k θ.1) θ.1 ((Nk ^ a) ^ (-(Cs : ℝ))) (p.frame s) (coin s) = some r ∧
      Nk ^ (-(CD * a)) ≤ |MvPolynomial.eval
        (fun i => p.baseLine s v.1 (time (p.timeIndex s)) i) (disc (p.P r))|
  F_eligible : ∀ s, ∀ v ∈ F s, v.1 ∈ eligible θ (p.frame s) (coin s)
  F_compatible : ∀ s, ∀ v ∈ F s,
    p.neighbourCompatible (p.bins k θ.1) s (coin s) (v.1, (time (p.timeIndex s), v.2))
  F_disjoint : ∀ s s', s ≠ s' → p.world s = p.world s' → p.timeIndex s = p.timeIndex s' →
    Disjoint (F s) (F s')
  mass : p.pairMass p.H ≤
    2 * (∑ s, ENNReal.ofReal (ωk (p.world s)) * p.incidenceLaw s (F s)) +
      ENNReal.ofReal (2 * Nk ^ (-(2 * a))) +
      ENNReal.ofReal (p.κ * (Nk ^ a)⁻¹) * p.pairMass p.H

/-- All selections are made against the original laws. Geometric interpolation
is passed as a pointwise short-bounds-to-eligibility implication. -/
theorem exists_frozenPairs {CD : ℝ}
    (hNk : 0 < Nk) (hA : 2 ≤ Nk ^ a)
    (hν : ∀ w, IsProbabilityMeasure (νk w)) (hω : ∀ w, 0 ≤ ωk w)
    (hsafe : SafeProbability Cs)
    (hAt : k.At Nk a (Submission.Obl.k4_quadratic_atlas_normalization.δ Nk L)
      ((2 : ℝ) ^ p.T) M)
    (hsublevel : SublevelAt Cs CD Nk a)
    (eligible : AnchorParameter → Fin p.J → (Fin k.d → ℤ) → Set Trajectory)
    (heligible : ∀ θ b β, MeasurableSet (eligible θ b β))
    (hlift : ∀ θ ∈ anchorDomain, ∀ (s : Fin p.m) (v : PairPoint), v ∈ p.H s →
      ∀ (β : Fin k.d → ℤ) (r : Fin p.m),
      p.representative (p.bins k θ.1) θ.1 ((Nk ^ a) ^ (-(Cs : ℝ))) (p.frame s) β = some r →
      p.shortBounds k s v (p.P r) → v.1 ∈ eligible θ (p.frame s) β) :
    Nonempty (p.FrozenPairs k CD eligible) := by
  classical
  obtain ⟨θ, hθ, G₀, hG₀, hG₀H, hsafeG₀, hanchor⟩ := p.exists_safe_anchor hsafe hNk hA hν
  have hα : ‖θ.1‖ ≤ 1 / 8 := mem_closedBall_zero_iff.mp hθ.1
  obtain ⟨G₁, hG₁, hG₁G₀, hdisc, hdelete⟩ := p.delete_representative_sublevels
    hNk hω hsublevel (p.bins k θ.1) (fun s => k.card_le Nk a _ (p.P s) θ.1)
    θ.1 hα G₀ hG₀ hG₀H
  have hG₁H (s : Fin p.m) : G₁ s ⊆ p.H s := (hG₁G₀ s).trans (hG₀H s)
  obtain ⟨coin, hcoin, hevent, hchoose⟩ := p.choose_transferred_bins k hNk hAt θ hθ
    (eligible θ) (heligible θ) (hlift θ hθ) G₁ hG₁ hG₁H
    (fun s v hv => hsafeG₀ s v (hG₁G₀ s hv))
  let event : Fin p.m → Set PairPoint := fun s =>
    p.sourcePairEvent (p.bins k θ.1) θ.1 ((Nk ^ a) ^ (-(Cs : ℝ))) (eligible θ) G₁ s (coin s)
  have heventG₁ (s : Fin p.m) : event s ⊆ G₁ s := fun _ hv => hv.1
  have heventH (s : Fin p.m) : event s ⊆ p.H s := (heventG₁ s).trans (hG₁H s)
  obtain ⟨time, htime, hfreeze⟩ := p.freeze_pair_events hν hω event hevent heventH
  let F : Fin p.m → Set Incidence := fun s => pairSection (event s) (time (p.timeIndex s))
  have hF (s : Fin p.m) (v : Incidence) (hv : v ∈ F s) :
      (v.1, (time (p.timeIndex s), v.2)) ∈ event s := hv
  have hFH (s : Fin p.m) (v : Incidence) (hv : v ∈ F s) :
      (v.1, (time (p.timeIndex s), v.2)) ∈ p.H s := heventH s (hF s v hv)
  refine ⟨{
    θ := θ
    θ_mem := hθ
    coin := coin
    time := time
    time_mem := htime
    F := F
    F_measurable := fun s => measurableSet_pairSection (hevent s) _
    F_source := fun s v hv => p.source_mem s (hFH s v hv)
    F_target := ?_
    F_coin := fun s v hv => (hF s v hv).2.1
    F_representative := ?_
    F_eligible := fun s v hv => (hF s v hv).2.2.2.1
    F_compatible := fun s v hv => (hF s v hv).2.2.2.2
    F_disjoint := p.frozen_sections_disjoint event heventH time
    mass := ?_
  }⟩
  · intro s v hv
    exact ⟨((p.pairs s).2 _ (hFH s v hv)).2.2.1, p.target_time s (hFH s v hv)⟩
  · intro s v hv
    obtain ⟨r, hr⟩ := (hF s v hv).2.2.1
    refine ⟨r, hr, ?_⟩
    exact hdisc s (v.1, (time (p.timeIndex s), v.2)) (heventG₁ s (hF s v hv))
      (coin s) (hF s v hv).2.1 r hr
  · have hselected : p.pairMass G₁ ≤
        2 * ∑ s, ENNReal.ofReal (ωk (p.world s)) * p.incidenceLaw s (F s) := by
      apply hchoose.trans
      gcongr
    exact hanchor.trans (add_le_add (hdelete.trans (add_le_add hselected le_rfl)) le_rfl)

end PairData
end Submission.Obl.k4_pair_bin_atlas_assembly
