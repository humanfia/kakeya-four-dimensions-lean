import Submission.Obl.k4_raw_native_atlas_normalization.Sequence
import Submission.Obl.k4_raw_native_atlas_normalization.Kernel.Budget

namespace Submission.Obl.k4_raw_native_atlas_normalization

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

namespace Prepared

variable {p : Data} {r h w : ℝ} (s : Prepared p r h w)

def output : Data where
  N k := p.N (s.φ k)
  K k := 3 * s.loss k
  L := p.L - r
  d := p.d
  S := p.S
  η := p.η
  W k := (s.a k).C
  ω k := (kernelAtlas (s.a k)).normWeight (p.ω (s.φ k)) (p.ν (s.φ k))
  ν k := (kernelAtlas (s.a k)).normPrior (p.ν (s.φ k))
  E k := (kernelAtlas (s.a k)).normEventOf
  P k := (kernelAtlas (s.a k)).normNative (δ (p.N (s.φ k)) r)
  B k := (kernelAtlas (s.a k)).normScale (p.B (s.φ k)) (δ (p.N (s.φ k)) r)
  f _ := 0
  g _ _ _ _ := 0
  G _ _ _ _ := 0

lemma raw (hp : Valid p) (hr : 0 ≤ r) (hrL : r < p.L) : Raw s.output := by
  obtain ⟨Mp, Dp, hs⟩ := samples_of_valid hp
  have hδinv (k : ℕ) : (δ (p.N (s.φ k)) r)⁻¹ ≤ p.N (s.φ k) ^ ⌈r⌉₊ := by
    have hN := hp.scale_pos (s.φ k)
    calc
      _ ≤ (p.N (s.φ k) ^ (-r))⁻¹ :=
        inv_anti₀ (Real.rpow_pos_of_pos hN _) (delta_bounds hN r).1
      _ = p.N (s.φ k) ^ r := by rw [← Real.rpow_neg hN.le, neg_neg]
      _ ≤ p.N (s.φ k) ^ (⌈r⌉₊ : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one _) (Nat.le_ceil _)
      _ = _ := Real.rpow_natCast _ _
  have hsample (k : ℕ) : Kernel.SampleProblem (s.output.N k) (s.output.K k)
      (Mp + 8 * s.M + ⌈r⌉₊ + 20) (max (max Dp s.D) 1) (s.output.W k)
      (s.output.ω k) (s.output.ν k) (s.output.E k) (s.output.P k) (s.output.B k) := by
    have ha := s.known k
    have hprior (b : Fin (s.a k).C) : 0 <
        (p.ν (s.φ k) ((s.a k).γ b) ((s.a k).A b)).toReal :=
      ENNReal.toReal_pos (ne_of_gt (s.prior_pos k b)) (by
        have := (hs (s.φ k)).prob ((s.a k).γ b)
        exact measure_ne_top _ _)
    have hmassc (b : Fin (s.a k).C) : 1 ≤ p.N (s.φ k) ^ s.M *
        (p.ν (s.φ k) ((s.a k).γ b) ((s.a k).A b)).toReal := by
      exact (inv_le_iff_one_le_mul₀ (hprior b)).mp (s.prior_inv k b)
    have hn := Kernel.SampleProblem.normalize (hs (s.φ k)) (kernelAtlas (s.a k))
      (known_geometry ha)
      (fun b l hl => ((ha.1.2.2.1 b).2.2.2.2.2.2.2.2.2.1 l hl).2.2)
      (fun b => (ha.1.2.2.1 b).2.2.2.2.2.2.2.2.2.2.1)
      (fun b => (ha.1.2.2.1 b).2.2.2.2.2.2.2.1)
      (fun b i => ((ha.1.2.2.1 b).2.2.2.2.2.2.2.2.1 i).2)
      (fun b => (ha.1.2.2.1 b).2.2.2.2.1)
      (fun b => (ha.1.2.2.1 b).2.2.2.2.2.1)
      hmassc ha.1.2.2.2 (hp.scale_ge_two _) (s.time_poly k)
      (delta_pos _ _) (Submission.Obl.k4_quadratic_atlas_normalization.delta_le_one
        (hp.scale_ge_one _) hr) (hδinv k) (s.loss_ge k)
    have hexp : Mp + 8 * s.M + ⌈r⌉₊ + 20 = Mp + 7 * s.M + s.M + ⌈r⌉₊ + 20 := by omega
    rw [hexp]
    exact hn
  apply raw_of_samples (p := s.output) (fun k => hp.scale_ge_two (s.φ k))
    (by exact (hp.scale_tendsto.comp s.mono.tendsto_atTop : Tendsto (p.N ∘ s.φ) atTop atTop))
    ?_ (by dsimp [output]; linarith)
    hp.2.2.2.2.1 hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.1 hsample
  constructor
  · intro k
    dsimp [output]
    linarith [s.loss_ge k]
  · intro ε hε
    filter_upwards [s.error_lim.eventually (gt_mem_nhds hε)] with k hk
    exact ((le_max_right _ _).trans (s.bound k)).trans
      (Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one _) hk.le)

lemma certificate (hp : Valid p) (hr : 0 ≤ r) (hrL : r < p.L) :
    Certificate p s.output r h w := by
  obtain ⟨Mp, Dp, hs⟩ := samples_of_valid hp
  let κ : ℕ → ℝ := fun k => max (p.K (s.φ k)) (3 * s.loss k)
  have hloss (k : ℕ) : 0 < s.loss k := by linarith [s.loss_ge k]
  have hκ (k : ℕ) : s.loss k ≤ κ k :=
    le_trans (by linarith [s.loss_ge k]) (le_max_right _ _)
  have hknown (k : ℕ) : (s.a k).KnownAt s.M s.D (κ k) r :=
    known_mono (s.known k) (hp.scale_ge_one _) le_rfl le_rfl (hloss k) (hκ k)
      (fun b => (hp.B_pos _ b).le)
  let θ : (k : ℕ) → Fin (s.a k).C → Trajectory ≃ᵐ Trajectory :=
    fun k b => trajectoryEquiv (s.a k) b ((s.known k).1.2.2.1 b).1
  let Z : ℕ → ℝ := fun k =>
    (kernelAtlas (s.a k)).normZ (p.ω (s.φ k)) (p.ν (s.φ k))
  have hZ (k : ℕ) : 0 < Z k ∧ (s.loss k)⁻¹ ≤ Z k ∧ Z k ≤ 1 := by
    letI : ∀ b, IsProbabilityMeasure (p.ν (s.φ k) b) := (hs (s.φ k)).prob
    have ha := s.known k
    have hsub : ∀ b, ∀ z ∈ (s.a k).F b,
        z.1 ∈ (s.a k).A b ∧ z.2 ∈ Kernel.timeBlock (s.a k).T ((s.a k).j b) :=
      fun b z hz => ⟨((ha.1.2.2.1 b).2.2.2.2.2.2.2.2.2.2.1 z hz).2.1,
        ((ha.1.2.2.1 b).2.2.2.2.2.2.2.2.2.2.1 z hz).2.2.1⟩
    have hzi := (kernelAtlas (s.a k)).normZ_inv_le (p.ω (s.φ k)) (p.ν (s.φ k))
      (hs (s.φ k)).weight_nonneg hsub (hloss k) ha.1.2.2.2
    exact ⟨hzi.1, (inv_le_comm₀ hzi.1 (hloss k)).mp hzi.2,
      (kernelAtlas (s.a k)).normZ_le_one (p.ω (s.φ k)) (p.ν (s.φ k))
        (hs (s.φ k)).weight_nonneg (hs (s.φ k)).weight_sum
        (fun b => (ha.1.2.2.1 b).2.2.2.2.2.2.1) ha.1.2.1⟩
  refine ⟨s.φ, s.M, s.D, κ, (fun k => (s.a k).T), (fun k => (s.a k).C),
    (fun k => (s.a k).γ), (fun k => (s.a k).j), (fun k => (s.a k).c),
    (fun k => (s.a k).u), (fun k => (s.a k).Q), (fun k => (s.a k).R),
    (fun k => (s.a k).A), (fun k => (s.a k).F), (fun k => Equiv.refl _), s.error,
    θ, (fun k => (s.a k).lst), Z, s.mono, (fun _ => rfl), s.raw hp hr hrL,
    rfl, rfl, rfl, rfl, s.error_pos, s.error_le, s.error_lim, ?_,
    (fun k => (s.loss_ge k).trans (hκ k)), (fun k => le_max_left _ _), s.bound,
    s.time, s.width, (fun _ _ _ => rfl), ?_, ?_, s.prior_pos, s.prior_inv,
    (fun _ _ => rfl), ?_, (fun _ _ => rfl), (fun k => (hZ k).1),
    (fun k => (inv_anti₀ (hloss k) (hκ k)).trans (hZ k).2.1),
    (fun k => (hZ k).2.2), ?_, ?_, (fun k => (hknown k).2), ?_⟩
  · intro k
    exact ⟨(hknown k).1.1, (hknown k).1.2.1, (hknown k).1.2.2.1⟩
  · intro k b l t
    exact trajectoryEquiv_planar (s.a k) b _ l t
  · intro k b l t
    exact trajectoryEquiv_hidden (s.a k) b _ l t
  · intro k b z hz
    change ((z.1.1, ((kernelAtlas (s.a k)).frameOf b).denormCoeff z.1.2),
      ((s.a k).j b : ℝ) / (2 : ℝ) ^ (s.a k).T + z.2 / (2 : ℝ) ^ (s.a k).T) ∈ (s.a k).F b
    have hz' : ((z.1.1, ((kernelAtlas (s.a k)).frameOf b).denormCoeff z.1.2),
      ((s.a k).j b : ℝ) / (2 : ℝ) ^ (s.a k).T +
        (1 / (2 : ℝ) ^ (s.a k).T) * z.2) ∈ (s.a k).F b := hz.2.2
    have ht : ((s.a k).j b : ℝ) / (2 : ℝ) ^ (s.a k).T + (1 / (2 : ℝ) ^ (s.a k).T) * z.2 =
        ((s.a k).j b : ℝ) / (2 : ℝ) ^ (s.a k).T + z.2 / (2 : ℝ) ^ (s.a k).T := by ring
    rw [ht] at hz'
    exact hz'
  · intro k
    apply Finset.sum_congr rfl
    intro b _
    dsimp only [kernelAtlas]
    ring
  · intro k b
    dsimp only [output, Kernel.ChartSystem.normWeight, Z, kernelAtlas]
    congr 1
    ring!
  · intro k b z
    exact normalized_test_identity (s.a k) r b z

end Prepared

theorem normalization (p : Data) (hp : Valid p) (r h w : ℝ)
    (hr : 0 ≤ r) (hrL : r < p.L) (hk : Known p r h w) :
    ∃ q : Data, Certificate p q r h w := by
  obtain ⟨s⟩ := prepare_atlases hp hr hk
  exact ⟨s.output, s.certificate hp hr hrL⟩

end
end Submission.Obl.k4_raw_native_atlas_normalization
