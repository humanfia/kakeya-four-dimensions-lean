/- Adapted from this LOT tree o105, session x0548, commit 6ab86148e24dd228044f997c2188e8d03c811f1b,
   Submission/Obl/k4_critical_path_framework/NativeListedVelocityMass.lean. -/
import Submission.Obl.k4_raw_localized_native_systems.Deletion.ListedVelocity
import Submission.Obl.k4_raw_localized_native_systems.Window.Witness

namespace Submission.Obl.k4_raw_localized_native_systems.Deletion

open Set MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion
open scoped ENNReal

/-- Under the frozen original law, all short-known velocity-small labels cost
only two one-time density exceptions and the angular decay factor. In
particular the number of packet labels never multiplies an exception. -/
theorem small_velocity_labels_bound {p : Data} (hp : Valid p)
    {k : ℕ} (γ : Fin (p.W k)) {β : Type*} [Fintype β]
    {u κ : ℝ} (hu : 0 < u) (huη : u ≤ p.η * p.L)
    (F : β → Set Point) (lst : Observation → Finset β)
    (hlist : ∀ b, MeasurableSet {o | b ∈ lst o})
    (hcard : ∀ o, ((lst o).card : ℝ) ≤ κ)
    (hknown : ∀ b q, q ∈ F b → b ∈ lst (obs (p.B k γ) (δ (p.N k) p.L) q))
    (hdiam : ∀ b q, q ∈ F b → ∀ q', q' ∈ F b →
      dist (v q.1) (v q'.1) ≤ δ (p.N k) u)
    (c lo hi : ENNReal) (hscale : hi ≤ c * lo) :
    (((p.ν k γ).prod volume).restrict (p.E k γ)) (⋃ b, F b) ≤
      (((p.ν k γ).prod volume).restrict (p.E k γ))
        {q | p.g k γ p.L (obs (p.B k γ) (δ (p.N k) p.L) q) < lo} +
      (((p.ν k γ).prod volume).restrict (p.E k γ))
        {q | hi < p.G k γ u (obs (p.B k γ) (δ (p.N k) p.L) q,
          fun j => ⌊v q.1 j / δ (p.N k) u⌋)} + c * ENNReal.ofReal (16 * κ) := by
  let μ := ((p.ν k γ).prod volume).restrict (p.E k γ)
  let o := obs (p.B k γ) (δ (p.N k) p.L)
  let a : Point → Fin 2 → ℤ := fun q j => ⌊v q.1 j / δ (p.N k) u⌋
  let g := p.g k γ p.L
  let G := p.G k γ u
  have hδ : 0 < δ (p.N k) u := by unfold δ; positivity
  have hv : Measurable (fun q : Point => v q.1) := by unfold v; fun_prop
  obtain ⟨_, _, _, hL, _, _, _, _, ⟨Mb, Db, hb⟩, hobs, hjoint, _⟩ := hp
  have hpure := hobs k γ p.L hL.le le_rfl
  have hang := hjoint k γ u hu huη
  have hraw := listed_small_velocity_mass_le μ (volume.prod Measure.count) o
    (fun q : Point => v q.1) hδ (Submission.Lib.K4ChartLifting.measurable_obs _ _) hv hpure.1 hang.1
    hpure.2 hang.2 F lst hlist hcard hknown hdiam c
  have hmask : μ {q | c * g (o q) < G (o q, a q)} ≤
      μ {q | g (o q) < lo} + μ {q | hi < G (o q, a q)} := by
    apply (measure_mono ?_).trans (measure_union_le _ _)
    intro q hq
    by_cases hlow : g (o q) < lo
    · exact Or.inl hlow
    · right
      apply lt_of_le_of_lt
        (hscale.trans (mul_le_mul' le_rfl (le_of_not_gt hlow))) hq
  have hμ : μ univ ≤ 1 := by
    obtain ⟨hprob, _, _, _, _, _, _, _, hEI, _⟩ := (hb k).2.2.2.1 γ
    letI := hprob
    change ((p.ν k γ).prod volume).restrict (p.E k γ) univ ≤ 1
    rw [Measure.restrict_apply_univ]
    calc
      _ ≤ ((p.ν k γ).prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := measure_mono hEI
      _ = 1 := by rw [Measure.prod_prod]; simp
  have hcost : c * ENNReal.ofReal (16 * κ) * μ univ ≤
      c * ENNReal.ofReal (16 * κ) :=
    (mul_le_mul' (le_refl (c * ENNReal.ofReal (16 * κ))) hμ).trans_eq (mul_one _)
  exact hraw.trans (add_le_add hmask hcost)

end Submission.Obl.k4_raw_localized_native_systems.Deletion
