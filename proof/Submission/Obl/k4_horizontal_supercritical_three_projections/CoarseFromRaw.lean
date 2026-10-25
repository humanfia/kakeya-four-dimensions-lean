import Submission.Obl.k4_horizontal_supercritical_three_projections.ActiveScalar
import Submission.Obl.k4_horizontal_supercritical_three_projections.FiniteCharts
import Submission.Obl.k4_horizontal_supercritical_three_projections.HeavyCharts
import Submission.Obl.k4_horizontal_supercritical_three_projections.ChartNumerics
import Submission.Obl.k4_horizontal_supercritical_three_projections.CoarseStep

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open Set MeasureTheory Filter
open scoped ENNReal BigOperators
open Submission.Obl.k4_fixed_budget_quadratic_recovery

/-- Apply the scalar theorem to every retained original-prior chart and keep
the whole finite ensemble. All packet floors are restored before any fine slicing. -/
theorem coarse_preparation_of_raw (hmesh : ScalarMeshProjection)
    {α : Type} [MeasurableSpace α]
    (N K : ℕ → ℝ) (d κ s₀ depth e₀ : ℝ)
    (ν : ℕ → Measure α) (μ ρ : ℕ → Measure (α × ℝ)) (π : ℕ → Measure ℝ)
    (b : ℕ → α → Fin 6 → ℝ)
    (hN₂ : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK₁ : ∀ k, 1 ≤ K k)
    (hKsub : ∀ ξ : ℝ, 0 < ξ → ∀ᶠ k in atTop, K k ≤ N k ^ ξ)
    (hd : 0 ≤ d) (hd₁ : d < 1) (hκ : 0 < κ) (hs₀ : 0 < s₀)
    (hslow : s₀ < depth) (hsnear : depth < 3 * s₀ / 2)
    (hlaws : BasicLaws N K ν μ ρ π b)
    (hraw : RawPreparation N K d s₀ (2 * κ * s₀) depth e₀ b μ π)
    {M : ℝ} (hM : 100 * s₀ < M) :
    CoarseProjectionPreparation N K d κ e₀ s₀ depth M b π ρ := by
  classical
  intro τ hτ
  obtain ⟨η, hη, N₀, hN₀, hscalar⟩ := scalar_packets_of_mesh hmesh hd hd₁
    (by linarith : 0 < depth) (by linarith : depth < 20 * s₀)
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
    hs₀ (by linarith : s₀ < 20 * s₀) hτ
  obtain ⟨cut, ξ, η₀, hcut, hξ, hη₀, hcutη, hξη, hcutξ, hsupport, hnum⟩ :=
    exists_chart_selection_exponents N K hN₂ hNt hK₁ hKsub hη hτ
  refine ⟨η₀, hη₀, ?_⟩
  filter_upwards [hraw.1, hraw.2 M hM ξ hξ, hnum, (tendsto_atTop.1 hNt N₀)]
    with k hgood hdata hnum hNk
  intro ζ hζρ hmass
  obtain ⟨hb, hν, hπ, hμdom, hρμ, hμsupp⟩ := hlaws k
  have : IsProbabilityMeasure (ν k) := hν
  have : IsProbabilityMeasure (π k) := hπ
  have hN : 1 ≤ N k := by linarith [hN₂ k]
  have hN₀' : 0 < N k := by linarith
  have hK : 0 < K k := by linarith [hK₁ k]
  have hζμ : ζ ≤ μ k := hζρ.trans hρμ
  have hdom := hζμ.trans hμdom
  have hsupp : ζ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 :=
    le_antisymm ((hζμ _).trans_eq hμsupp) bot_le
  have hmassK : ζ univ ≤ ENNReal.ofReal (K k) := by
    simpa only [Set.mem_univ, Set.ofPred_true, measure_univ, mul_one] using
      incidence_assignment_bound (ν k) ζ univ (ENNReal.ofReal (K k)) hdom hsupp
  have : IsFiniteMeasure ζ := ⟨hmassK.trans_lt ENNReal.ofReal_lt_top⟩
  obtain ⟨hKξ, h10K, hprune, hsuccess⟩ := hnum
  let D := N k ^ (-(2 * κ * s₀))
  let χ := N k ^ (-M)
  let δ := N k ^ (-cut)
  let E := N k ^ (-e₀)
  have hD : 0 < D := Real.rpow_pos_of_pos hN₀' _
  have hD₁ : D ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by nlinarith)
  have hχ : 0 < χ := Real.rpow_pos_of_pos hN₀' _
  have hχ₁ : χ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  have hδ : 0 < δ := Real.rpow_pos_of_pos hN₀' _
  let A : Set α := {l | (∀ e, |b k l e| ≤ 3 * K k) ∧ |b k l 0| ≤ K k ∧
    |b k l 3| ≤ K k ∧ |b k l 4 + b k l 0| ≤ E}
  have hA : MeasurableSet A := by
    have he (e : Fin 6) : Measurable (fun l => b k l e) := (measurable_pi_apply e).comp hb
    have hall : MeasurableSet {l | ∀ e, |b k l e| ≤ 3 * K k} := by
      simpa only [Set.ofPred_forall] using
        MeasurableSet.iInter (fun e => measurableSet_le (he e).abs measurable_const)
    exact hall.inter ((measurableSet_le (he 0).abs measurable_const).inter
      ((measurableSet_le (he 3).abs measurable_const).inter
        (measurableSet_le ((he 4).add (he 0)).abs measurable_const)))
  obtain ⟨C, hC⟩ := finite_bounded_charts (b k) hb (π k) A hA hχ hχ₁ hD hD₁ (hK₁ k)
    (fun _ hl => hl)
  let W := fun i : Fin C.n => chartWeight (π k) χ D (C.q i)
  have hW (i) : 0 ≤ W i := by dsimp [W, chartWeight]; positivity
  have hsub (i) : C.G i ⊆ chartSet (b k) (K k) E D χ (C.q i 1) (C.q i 2) (C.q i 0) := by
    intro l hl
    have hlA := hC.subset i hl
    obtain ⟨hv, hp, hq⟩ := hC.bins i l hl
    exact ⟨hlA.2.1, hlA.2.2.1, hlA.2.2.2, hp, hq, hv⟩
  have hcap (i) : μ k (C.G i ×ˢ univ) ≤ ENNReal.ofReal (N k ^ ξ * W i) :=
    (measure_mono (Set.prod_mono (hsub i) subset_rfl)).trans
      (hdata (C.q i 1) (C.q i 2) (C.q i 0)).1
  obtain ⟨S, hS, hbudget⟩ := select_dense_charts (ν k) ζ (μ k) C.G hC.measurable
    hC.disjoint W hW hK (Real.rpow_pos_of_pos hN₀' ξ) hδ hC.budget hζμ hdom hsupp hcap
  have hfull : ζ {p | ∃ i, p.1 ∈ C.G i} = ζ univ := by
    apply measure_congr
    filter_upwards [ae_mono hζμ hgood] with p hp
    apply propext
    exact ⟨fun _ => mem_univ _, fun _ => hC.cover p.1 hp⟩
  rw [hfull] at hbudget
  have hretained : ENNReal.ofReal (N k ^ (-η₀) / 2) ≤ ζ {p | ∃ i ∈ S, p.1 ∈ C.G i} := by
    apply ENNReal.le_of_add_le_add_right (ENNReal.ofReal_ne_top :
      ENNReal.ofReal (N k ^ (-η₀) / 2) ≠ ⊤)
    calc
      _ = ENNReal.ofReal (N k ^ (-η₀)) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      _ ≤ _ := hmass.trans hbudget
      _ ≤ _ := add_le_add le_rfl (ENNReal.ofReal_le_ofReal hprune)
  let G := fun i : S => C.G i.val
  let q := fun i : S => C.q i.val
  have hG (i : S) : MeasurableSet (G i) := hC.measurable _
  have hνG (i : S) : ν k (G i) ≠ 0 := (hS i.val i.property).1
  have hdisj : Pairwise (fun i j : S => Disjoint (G i) (G j)) := by
    intro i j hij
    exact hC.disjoint _ _ (fun heq => hij (Subtype.ext heq))
  have hpalette (i : S) : 0 < π k (Ico ((q i 0 : ℝ) * χ) (((q i 0 : ℝ) + 1) * χ)) := by
    by_contra hn
    have hz : π k (Ico ((q i 0 : ℝ) * χ) (((q i 0 : ℝ) + 1) * χ)) = 0 :=
      le_antisymm (le_of_not_gt hn) zero_le
    have hWi := (hS i.val i.property).2.1
    change 0 < chartWeight (π k) χ D (q i) at hWi
    simp only [chartWeight, hz, ENNReal.toReal_zero, zero_mul, lt_self_iff_false] at hWi
  have hpackets (i : S) : ∃ F : ScalarPackets (N k) d depth (20 * s₀)
      (chartWeight (π k) χ D (q i) / (ν k (G i)).toReal) τ (chartLaw (ν k) ζ (G i))
      (fun l => Parent.projectedCoefficients ((q i 1 : ℝ) * D) ((q i 2 : ℝ) * D) D (b k l)),
      ∀ j, F.A j ⊆ G i := by
    have hactive := hS i.val i.property
    have hc := active_chart_scalar_bounds hN hKξ hcutη hξη hcutξ hsupport hactive.2.2.2.2.1 hactive.2.2.2.2.2.1
    let bs := fun l => Parent.projectedCoefficients ((q i 1 : ℝ) * D) ((q i 2 : ℝ) * D) D (b k l)
    have hdomη : ζ ≤ ENNReal.ofReal (N k ^ η) • ((ν k).prod volume) := by
      apply hdom.trans
      intro B
      simp only [Measure.smul_apply, smul_eq_mul]
      simpa only [mul_comm] using mul_le_mul_right
        (ENNReal.ofReal_le_ofReal (hKξ.trans hc.2.2.2.2.1)) (((ν k).prod volume) B)
    have hcoeff : ∀ l ∈ G i, ∀ j, |bs l j| ≤ N k ^ η := by
      intro l hl j
      have hlA := hC.subset i.val hl
      obtain ⟨_, hp, hq⟩ := hC.bins i.val l hl
      have h := Parent.projectedCoefficients_bound hD (by linarith [hK₁ k] : 1 ≤ 3 * K k)
        (fine_intercept_error hD hp) (fine_intercept_error hD hq) (hlA.1 2) (hlA.1 5) j
      change |bs l j| ≤ 2 * (3 * K k) at h
      linarith
    have hadm := raw_chart_scalar_admissible hN₀' (ν k) ζ (μ k) (π k) (b k) hb hdata
      (q i 1) (q i 2) (q i 0) (G i) (hG i) (hνG i) (hsub i.val)
      hζμ hdomη hsupp hcoeff hc.2.1 hc.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2
    have hmass' : ENNReal.ofReal (N k ^ (-η)) ≤ chartLaw (ν k) ζ (G i) univ :=
      (ENNReal.ofReal_le_ofReal hc.2.2.2.1).trans hactive.2.2.2.2.2.2
    obtain ⟨F⟩ := hscalar (N k) hNk α (ProbabilityTheory.cond (ν k) (G i))
      (chartLaw (ν k) ζ (G i)) (padCoefficients (G i) bs)
      (chartWeight (π k) χ D (q i) / (ν k (G i)).toReal) hadm hmass'
    let F' := F.trim (hG i) (chartLaw_supported (ν k) ζ (hG i))
      (fun l hl => padCoefficients_eq bs hl)
    exact ⟨F', fun j l hl => hl.2⟩
  choose F hFsub using hpackets
  obtain ⟨L, hL, hpal, hfloor, hcovered⟩ := coarse_layer_of_scalar_ensemble hN hτ.le
    (ν k) ζ (π k) (b k) G q hνG hdisj (fun i => hC.corner i.val)
    (fun i => hC.coordinates i.val) hpalette F hFsub
  refine ⟨L, hL, hpal, hfloor, ?_⟩
  have hcoverS : {p : α × ℝ | ∃ i : S, p.1 ∈ G i} = {p | ∃ i ∈ S, p.1 ∈ C.G i} := by
    ext p
    simp only [G, exists_prop, Subtype.exists]
  have hscalarMass := scalar_ensemble_mass (ν k) ζ G hG hdisj hK
    (Real.rpow_nonneg hN₀'.le (-τ)) hdom hsupp {p | ∃ i, p.1 ∈ L.A i} hcovered
  rw [hcoverS] at hscalarMass
  calc
    _ ≤ ENNReal.ofReal ((N k ^ (-τ) / K k) * (N k ^ (-η₀) / 2)) :=
      ENNReal.ofReal_le_ofReal hsuccess
    _ = ENNReal.ofReal (N k ^ (-τ) / K k) * ENNReal.ofReal (N k ^ (-η₀) / 2) :=
      ENNReal.ofReal_mul (by positivity)
    _ ≤ _ := (mul_le_mul_right hretained _).trans hscalarMass


/-- The generic raw chart interface and scalar premise imply the complete
uniform dense-submeasure physical projection step. -/
theorem raw_single_projection_of_scalar (hmesh : ScalarMeshProjection)
    {α : Type} [MeasurableSpace α]
    (N K : ℕ → ℝ) (d κ s₀ depth e₀ : ℝ)
    (ν : ℕ → Measure α) (μ ρ : ℕ → Measure (α × ℝ)) (π : ℕ → Measure ℝ)
    (b : ℕ → α → Fin 6 → ℝ)
    (hN₂ : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK₁ : ∀ k, 1 ≤ K k)
    (hKsub : ∀ ξ : ℝ, 0 < ξ → ∀ᶠ k in atTop, K k ≤ N k ^ ξ)
    (hd : 0 ≤ d) (hd₁ : d < 1) (hκ : 0 < κ) (hκ₁ : κ ≤ 1) (hs₀ : 0 < s₀)
    (he₀ : 100 * s₀ < e₀) (hslow : s₀ < depth) (hsnear : depth < 3 * s₀ / 2)
    (hlaws : BasicLaws N K ν μ ρ π b)
    (hraw : RawPreparation N K d s₀ (2 * κ * s₀) depth e₀ b μ π) :
    ∀ M : ℝ, 100 * s₀ < M →
      RawSingleProjection N d depth (10 + 8 * s₀) M (2 * κ * s₀) b π ρ := by
  intro M hM
  have hc := coarse_preparation_of_raw hmesh N K d κ s₀ depth e₀ ν μ ρ π b
    hN₂ hNt hK₁ hKsub hd hd₁ hκ hs₀ hslow hsnear hlaws hraw hM
  have hstep := single_projection_of_coarse_of_sequences N K d κ e₀ ν μ ρ π b
    hN₂ hNt hK₁ hKsub hκ hκ₁ hlaws hs₀ he₀ hM hsnear hc
  intro ε hε
  obtain ⟨η, hη, H⟩ := hstep ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [H] with k hk
  intro ζ hζ hm
  obtain ⟨L, ζ', hζ', hm', hcover, hgood⟩ := hk ζ hζ hm
  exact ⟨L.n, L.C, L.q, L.G, ζ', hζ', hm', hcover, hgood⟩

end Submission.Obl.k4_horizontal_supercritical_three_projections
