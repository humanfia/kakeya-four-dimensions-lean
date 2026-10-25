import Submission.Obl.k4_native_calibrated_homogeneous_remainder.CmpPure
import Submission.Obl.k4_remainder_angular_cap_transport.FiniteTransfer
import Submission.Obl.k4_native_calibrated_homogeneous_remainder.Models
set_option autoImplicit false

/-! The angular cap of the calibrated remainder. A coefficient map satisfying the frozen
chart identities is the explicit normalization of accepted o185, so its finite angular
transfer `finite_angular_tail` applies chart by chart; the exact within-world terminal
calibration and the subpower slack turn it into the asymptotic cap with unchanged
`S` and `η`. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder.Cmp

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_finite_width_output_exclusion (x y v δ obs)

local notation "Fr" => Submission.Obl.k4_remainder_angular_cap_transport.Geometry.Frame

/-- The chart frame of o185 for a dyadic block `j` of length `2^-T`. -/
noncomputable def chartFrame (T : ℕ) (j : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) : Fr where
  t₀ := j / (2 : ℝ) ^ T
  q := 1 / (2 : ℝ) ^ T
  c := c
  u := u
  D := Q

/-- Any coefficient map satisfying the frozen chart identities is o185's explicit
normalization. -/
theorem theta_eq_normTraj {θ : Line ≃ᵐ Line} {T : ℕ} {j : ℝ}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    (hθ1 : ∀ l, (θ l).1 = l.1)
    (hy : ∀ l t, y (θ l) t = Matrix.toEuclideanLin Q⁻¹
      (y l (j / (2 : ℝ) ^ T + t / (2 : ℝ) ^ T) - c - (j / (2 : ℝ) ^ T + t / (2 : ℝ) ^ T) • u))
    (hx : ∀ l t, x (θ l) t 3 = x l (j / (2 : ℝ) ^ T + t / (2 : ℝ) ^ T) 3) (l : Line) :
    θ l = (chartFrame T j c u Q).normTraj l := by
  have hv := v_transport (D := (2 : ℝ) ^ T) hy l
  have hy0 := hy l 0
  have hx0 := hx l 0
  have hx1 := hx l 1
  refine Prod.ext (hθ1 l) ?_
  funext e
  have hv0 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hv
  have hv1 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) hv
  have hy00 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hy0
  have hy01 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) hy0
  simp only [toEuclideanLin_apply_two] at hv0 hv1 hy00 hy01
  simp [y, x, v] at hv0 hv1 hy00 hy01 hx0 hx1
  fin_cases e <;>
    simp [Submission.Obl.k4_remainder_angular_cap_transport.Geometry.Frame.normTraj,
      Submission.Obl.k4_remainder_angular_cap_transport.Geometry.Frame.normCoeff, chartFrame]
  · linear_combination hy00
  · linear_combination hy01
  · exact hx0
  · rw [hv0]; ring
  · rw [hv1]; ring
  · linear_combination hx1 - hx0


theorem theta_symm_eq_denormTraj {θ : Line ≃ᵐ Line} {T : ℕ} {j : ℝ}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    (hθ : ∀ l, θ l = (chartFrame T j c u Q).normTraj l) (l' : Line) :
    θ.symm l' = (chartFrame T j c u Q).denormTraj l' := by
  have h1 : (chartFrame T j c u Q).normTraj (θ.symm l') = l' := by
    rw [← hθ]; exact θ.apply_symm_apply l'
  have h2 := (chartFrame T j c u Q).denormTraj_normTraj (by simp [chartFrame])
    (by simpa [chartFrame] using Ne.isUnit hQ) (θ.symm l')
  rw [h1] at h2
  exact h2.symm

open Submission.Obl.k4_finite_width_output_exclusion (Data Atlas chart Valid)

/-- The o185 chart system of a parent atlas. -/
noncomputable def atlasSystem {p : Data} {k : ℕ} (a : Atlas p k) :
    Submission.Obl.k4_remainder_angular_cap_transport.Geometry.ChartSystem (p.W k) a.T where
  count := a.C
  world := a.γ
  block := a.j
  center := a.c
  speed := a.u
  frame := a.Q
  test := a.R
  assignment := a.A
  event := a.F

theorem atlasSystem_frameOf {p : Data} {k : ℕ} (a : Atlas p k) (b : Fin a.C) :
    (atlasSystem a).frameOf b = chartFrame a.T (a.j b : ℝ) (a.c b) (a.u b) (a.Q b) := rfl


section Geometry

open Submission.Obl.k4_native_calibrated_homogeneous_remainder (RemainderGeometry)

variable {p q : Data} {r h w : ℝ} (g : RemainderGeometry p q r h w)

/-- The parts of a parent chart used by the comparisons. -/
theorem chart_parts {Nk : ℝ} {M D : ℕ} {κ : ℝ} {T : ℕ} {j r' Bv : ℝ} {Ev : Set Point}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set Line} {F : Set Point} {ex : Prop}
    (hc : chart Nk M D κ T j r' Bv Ev c u Q R A F ex) :
    Q.det ≠ 0 ∧ (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤ κ / (2 : ℝ) ^ T ∧
      MeasurableSet A ∧ MeasurableSet F ∧
      ∀ z ∈ F, z ∈ Ev ∧ z.1 ∈ A ∧ z.2 ∈ Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T) := by
  obtain ⟨hdet, -, -, hQκ, -, -, hAm, hFm, -, -, hF, -⟩ := hc
  exact ⟨hdet, hQκ, hAm, hFm, fun z hz => ⟨(hF z hz).1, (hF z hz).2.1, (hF z hz).2.2.1⟩⟩

theorem geometry_theta_eq (k : ℕ) (b : Fin (q.W k)) (l : Line) :
    g.θ k b l = ((atlasSystem (g.parent k)).frameOf (g.worlds k b)).normTraj l := by
  rw [atlasSystem_frameOf]
  exact theta_eq_normTraj (g.index_preserved k b) (g.planar_map k b) (g.hidden_map k b) l

theorem geometry_prior_eq (k : ℕ) (b : Fin (q.W k)) :
    q.ν k b = (atlasSystem (g.parent k)).normPrior (p.ν (g.φ k)) (g.worlds k b) := by
  rw [g.conditioned_prior k b]
  have : (g.θ k b : Line → Line) =
      ((atlasSystem (g.parent k)).frameOf (g.worlds k b)).normTraj :=
    funext (geometry_theta_eq g k b)
  rw [this]
  rfl

theorem geometry_event_subset (k : ℕ) (b : Fin (q.W k)) :
    q.E k b ⊆ (atlasSystem (g.parent k)).normEventOf (g.worlds k b) := by
  intro z hz
  obtain ⟨hdet, -, -, -, hF⟩ := chart_parts ((g.parent_valid k).2.2 (g.worlds k b))
  have hθ := geometry_theta_eq g k b
  rw [atlasSystem_frameOf] at hθ
  have hsymm := theta_symm_eq_denormTraj hdet hθ z.1
  have hpull := g.selected_pullback k b z hz
  rw [hsymm] at hpull
  obtain ⟨-, hA, ht⟩ := hF _ hpull
  set T := (g.parent k).T
  set jj : ℝ := ((g.parent k).j (g.worlds k b) : ℝ)
  have hpos : (0 : ℝ) < (2 : ℝ) ^ T := by positivity
  refine ⟨hA, ?_, ?_⟩
  · simp only [Set.mem_Icc] at ht ⊢
    constructor
    · have := ht.1
      rw [div_le_iff₀ hpos, add_mul, div_mul_cancel₀ _ hpos.ne', div_mul_cancel₀ _ hpos.ne'] at this
      linarith
    · have := ht.2
      rw [le_div_iff₀ hpos, add_mul, div_mul_cancel₀ _ hpos.ne', div_mul_cancel₀ _ hpos.ne'] at this
      linarith
  · have key : (((atlasSystem (g.parent k)).frameOf (g.worlds k b)).denormTraj z.1,
        ((atlasSystem (g.parent k)).frameOf (g.worlds k b)).t₀ +
          ((atlasSystem (g.parent k)).frameOf (g.worlds k b)).q * z.2) =
        ((chartFrame T jj ((g.parent k).c (g.worlds k b)) ((g.parent k).u (g.worlds k b))
          ((g.parent k).Q (g.worlds k b))).denormTraj z.1, jj / 2 ^ T + z.2 / 2 ^ T) := by
      rw [atlasSystem_frameOf]
      refine Prod.ext rfl ?_
      simp only [chartFrame]
      ring
    show (((atlasSystem (g.parent k)).frameOf (g.worlds k b)).denormTraj z.1,
        ((atlasSystem (g.parent k)).frameOf (g.worlds k b)).t₀ +
          ((atlasSystem (g.parent k)).frameOf (g.worlds k b)).q * z.2) ∈ (g.parent k).F (g.worlds k b)
    rw [key]
    exact hpull

theorem geometry_normZ_eq (k : ℕ) :
    (atlasSystem (g.parent k)).normZ (p.ω (g.φ k)) (p.ν (g.φ k)) = g.Z k := by
  rw [g.normalizer_sum k]
  simp only [Submission.Obl.k4_remainder_angular_cap_transport.Geometry.ChartSystem.normZ,
    atlasSystem]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem geometry_weight_eq (k : ℕ) (b : Fin (q.W k)) :
    q.ω k b = (atlasSystem (g.parent k)).normWeight (p.ω (g.φ k)) (p.ν (g.φ k))
      (g.worlds k b) := by
  rw [g.world_weights k b]
  simp only [Submission.Obl.k4_remainder_angular_cap_transport.Geometry.ChartSystem.normWeight]
  rw [geometry_normZ_eq g k]
  simp only [atlasSystem]
  ring

end Geometry


section Angular

open Submission.Obl.k4_native_calibrated_homogeneous_remainder (RemainderGeometry)
open Submission.Obl.k4_remainder_angular_cap_transport.Geometry (jobs jointRef)
open Submission.Obl.k4_remainder_angular_cap_transport (finite_angular_tail)

variable {p q : Data} {r h w : ℝ} (g : RemainderGeometry p q r h w)

/-- The joint observation of the frozen statement is o185's `jobs`. -/
theorem jobs_eq (B a du : ℝ) :
    (fun z : Point => ((obs B a) z, fun i : Fin 2 => ⌊(v z.1) i / du⌋)) = jobs B a du := rfl

/-- One sample of the angular transfer: the new weighted tail above `target` is at most
`4 / Z` times the old weighted tail above `θ`. -/
theorem geometry_angular_sample (hp : Valid p) (k : ℕ)
    (hqE : ∀ b, MeasurableSet (q.E k b) ∧ q.E k b ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1)
    (u : ℝ) (hu : 0 < u) (huL : u ≤ p.η * p.L)
    (hqG : ∀ b, Measurable (q.G k b u) ∧
      Measure.map (jobs (q.B k b) (δ (q.N k) q.L) (δ (q.N k) u))
        (((q.ν k b).prod volume).restrict (q.E k b)) = jointRef.withDensity (q.G k b u))
    (θ target : ℝ≥0∞)
    (htarget : ∀ b : Fin (q.W k), ENNReal.ofReal (100 * g.κ k ^ 2) * θ *
      ENNReal.ofReal (|((g.parent k).Q (g.worlds k b)).det| /
        (p.ν (g.φ k) ((g.parent k).γ (g.worlds k b)) ((g.parent k).A (g.worlds k b))).toReal)
        ≤ target) :
    (∑ b, ENNReal.ofReal (q.ω k b) * (((q.ν k b).prod volume).restrict (q.E k b))
        {z | target < q.G k b u (jobs (q.B k b) (δ (q.N k) q.L) (δ (q.N k) u) z)}) ≤
      4 * ENNReal.ofReal (g.Z k)⁻¹ *
        ∑ γ, ENNReal.ofReal (p.ω (g.φ k) γ) * (((p.ν (g.φ k) γ).prod volume).restrict
          (p.E (g.φ k) γ)) {z | θ < p.G (g.φ k) γ u (jobs (p.B (g.φ k) γ)
            (δ (p.N (g.φ k)) p.L) (δ (p.N (g.φ k)) u) z)} := by
  classical
  obtain ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hmodel, hgl, hGl, hprof, htyp, hdc, hcap⟩ := hp
  obtain ⟨M₀, D₀, hmodel⟩ := hmodel
  have hworld : ∀ γ, IsProbabilityMeasure (p.ν (g.φ k) γ) ∧ MeasurableSet (p.E (g.φ k) γ) := by
    intro γ
    obtain ⟨hpr, -, -, -, -, -, -, hE, -⟩ := (hmodel (g.φ k)).2.2.2.1 γ
    exact ⟨hpr, hE⟩
  have : ∀ γ, IsFiniteMeasure (p.ν (g.φ k) γ) := fun γ => by
    have := (hworld γ).1; infer_instance
  have hchart := fun c => chart_parts ((g.parent_valid k).2.2 c)
  have hNk : q.N k = p.N (g.φ k) := g.same_base k
  have hLq : q.L = p.L - r := g.length
  -- widths
  obtain ⟨m, hm0, hm2, hwidth⟩ : ∃ m : ℕ, 0 < m ∧ m ≤ 2 ∧
      δ (p.N (g.φ k)) r * δ (p.N (g.φ k)) (p.L - r) = δ (p.N (g.φ k)) p.L * (m : ℝ) := by
    have hsum : r + (p.L - r) = p.L := by ring
    rcases delta_mul_delta (p.N (g.φ k)) r (p.L - r) with h1 | h1
    · exact ⟨1, by norm_num, by norm_num, by rw [h1, hsum]; simp⟩
    · exact ⟨2, by norm_num, le_rfl, by rw [h1, hsum]; push_cast; ring⟩
  -- the normalized priors are probability measures
  have hprob : ∀ b, IsProbabilityMeasure (q.ν k b) := by
    intro b
    rw [g.conditioned_prior k b]
    have hpos := g.prior_pos k b
    have hfinA : p.ν (g.φ k) ((g.parent k).γ (g.worlds k b)) ((g.parent k).A (g.worlds k b)) ≠ ⊤ :=
      measure_ne_top _ _
    constructor
    rw [Measure.smul_apply, Measure.map_apply (g.θ k b).measurable MeasurableSet.univ,
      Set.preimage_univ, Measure.restrict_apply_univ, smul_eq_mul,
      ENNReal.inv_mul_cancel hpos.ne' hfinA]
  have hfinq : ∀ b, IsFiniteMeasure (((q.ν k b).prod volume).restrict (q.E k b)) := by
    intro b
    have := hprob b
    constructor
    rw [Measure.restrict_apply_univ]
    calc ((q.ν k b).prod volume) (q.E k b)
        ≤ ((q.ν k b).prod volume) (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) := measure_mono (hqE b).2
      _ < ⊤ := by
        rw [Measure.prod_prod, Real.volume_Icc]
        simp
  have hprior : ∀ c : Fin (g.parent k).C, (atlasSystem (g.parent k)).normPrior (p.ν (g.φ k)) c =
      q.ν k ((g.worlds k).symm c) := by
    intro c
    rw [geometry_prior_eq g k ((g.worlds k).symm c), Equiv.apply_symm_apply]
  have hfin₂ : ∀ c : Fin (atlasSystem (g.parent k)).count,
      IsFiniteMeasure ((((atlasSystem (g.parent k)).normPrior (p.ν (g.φ k)) c).prod
        volume).restrict (q.E k ((g.worlds k).symm c))) := by
    intro c
    rw [hprior c]
    exact hfinq ((g.worlds k).symm c)
  have hZ : 0 < (atlasSystem (g.parent k)).normZ (p.ω (g.φ k)) (p.ν (g.φ k)) := by
    rw [geometry_normZ_eq g k]; exact g.normalizer_pos k
  have hpos : ∀ c : Fin (g.parent k).C, 0 < (p.ν (g.φ k) ((atlasSystem (g.parent k)).world c)
      ((atlasSystem (g.parent k)).assignment c)).toReal := by
    intro c
    have h1 := g.prior_pos k ((g.worlds k).symm c)
    rw [Equiv.apply_symm_apply] at h1
    exact ENNReal.toReal_pos h1.ne' (measure_ne_top _ _)
  have hE₂ : ∀ c : Fin (g.parent k).C, q.E k ((g.worlds k).symm c) ⊆ (atlasSystem (g.parent k)).normEventOf c := by
    intro c
    have := geometry_event_subset g k ((g.worlds k).symm c)
    rwa [Equiv.apply_symm_apply] at this
  have hlaw₂ : ∀ c : Fin (g.parent k).C, ((((atlasSystem (g.parent k)).normPrior (p.ν (g.φ k)) c).prod volume).restrict
      (q.E k ((g.worlds k).symm c))).map
        (jobs (p.B (g.φ k) ((atlasSystem (g.parent k)).world c) / δ (p.N (g.φ k)) r)
          (δ (p.N (g.φ k)) (p.L - r)) (δ (p.N (g.φ k)) u)) =
      jointRef.withDensity (q.G k ((g.worlds k).symm c) u) := by
    intro c
    have h1 := (hqG ((g.worlds k).symm c)).2
    rw [g.derivative_unit k ((g.worlds k).symm c), hNk, hLq, Equiv.apply_symm_apply] at h1
    rw [hprior c]
    exact h1
  have htarget' : ∀ c : Fin (g.parent k).C, ENNReal.ofReal (100 * g.κ k ^ 2) * θ *
      ENNReal.ofReal (|((atlasSystem (g.parent k)).frame c).det| /
        (p.ν (g.φ k) ((atlasSystem (g.parent k)).world c)
          ((atlasSystem (g.parent k)).assignment c)).toReal) ≤ target := by
    intro c
    have h1 := htarget ((g.worlds k).symm c)
    rwa [Equiv.apply_symm_apply] at h1
  have key := finite_angular_tail (atlasSystem (g.parent k)) (p.ω (g.φ k)) (p.ν (g.φ k))
    (p.E (g.φ k)) (p.B (g.φ k))
    (hmodel (g.φ k)).2.1 hZ (fun γ => (hworld γ).2) (fun c => (hchart c).1)
    (fun c => (hchart c).2.2.1) (fun c => (hchart c).2.2.2.1) hpos (g.parent_valid k).2.1
    (fun c z hz => (hchart c).2.2.2.2 z hz) (g.κ k) (δ (p.N (g.φ k)) r)
    (δ (p.N (g.φ k)) (p.L - r)) (δ (p.N (g.φ k)) p.L) (δ (p.N (g.φ k)) u) (g.slack_one k)
    (delta_pos _ _).ne' (delta_pos _ _) (fun c => (hchart c).2.1) hm0 hm2 hwidth
    (fun c => q.E k ((g.worlds k).symm c)) hE₂ (fun γ => p.G (g.φ k) γ u)
    (fun c => q.G k ((g.worlds k).symm c) u)
    (fun γ => (hGl (g.φ k) γ u hu huL).1) (fun c => (hqG ((g.worlds k).symm c)).1)
    (fun γ => (hGl (g.φ k) γ u hu huL).2) hlaw₂ θ target htarget'
  rw [geometry_normZ_eq g k] at key
  refine le_trans (le_of_eq ?_) key
  refine Fintype.sum_equiv (g.worlds k) _ _ fun b => ?_
  rw [geometry_weight_eq g k b, hprior ((g.worlds k) b), Equiv.symm_apply_apply,
    g.derivative_unit k b, hNk, hLq]
  rfl

/-- A threshold for real powers. -/
theorem le_rpow_of_root_le {a c N : ℝ} (ha : 0 ≤ a) (hc : 0 < c) (hN : a ^ (1 / c) ≤ N) :
    a ≤ N ^ c := by
  have h0 : 0 ≤ a ^ (1 / c) := Real.rpow_nonneg ha _
  calc a = (a ^ (1 / c)) ^ c := by
        rw [← Real.rpow_mul ha, one_div, inv_mul_cancel₀ hc.ne', Real.rpow_one]
    _ ≤ N ^ c := Real.rpow_le_rpow h0 hN hc.le

/-- **Angular cap of the remainder.** The original angular cap transfers to the
normalized remainder with unchanged `S` and `η`, given the exact within-world terminal
calibration with the subpower slack `κ`. -/
theorem geometry_angular_cap (hp : Valid p) (hr : 0 ≤ r)
    (hqE : ∀ k b, MeasurableSet (q.E k b) ∧ q.E k b ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1)
    (hqG : ∀ k b u, 0 < u → u ≤ q.η * q.L → Measurable (q.G k b u) ∧
      Measure.map (jobs (q.B k b) (δ (q.N k) q.L) (δ (q.N k) u))
        (((q.ν k b).prod volume).restrict (q.E k b)) = jointRef.withDensity (q.G k b u))
    (hcal : ∀ k b, p.N (g.φ k) ^ (-p.f p.L) * |((g.parent k).Q (g.worlds k b)).det| ≤
      g.κ k * (p.ν (g.φ k) ((g.parent k).γ (g.worlds k b))
        ((g.parent k).A (g.worlds k b))).toReal * q.N k ^ (-q.f q.L)) :
    ∀ u τ : ℝ, 0 < u → u ≤ q.η * q.L → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in Filter.atTop,
      (∑ b, ENNReal.ofReal (q.ω k b) * (((q.ν k b).prod volume).restrict (q.E k b))
        {z | ENNReal.ofReal (q.N k ^ (-q.f q.L - q.S * u + τ)) <
          q.G k b u (jobs (q.B k b) (δ (q.N k) q.L) (δ (q.N k) u) z)}) ≤
        ENNReal.ofReal (q.N k ^ (-c)) := by
  intro u τ hu huq hτ
  have hp' := hp
  obtain ⟨hN, hNt, hK, hL, hd, hd1, hS, hη, hmodel, hgl, hGl, hprof, htyp, hdc, hcap⟩ := hp'
  have huL : u ≤ p.η * p.L := by
    rw [g.angular_range, g.length] at huq
    nlinarith
  obtain ⟨c₀, hc₀, hev⟩ := hcap u (τ / 2) hu huL (half_pos hτ)
  refine ⟨c₀ / 2, half_pos hc₀, ?_⟩
  have hφ : Filter.Tendsto g.φ Filter.atTop Filter.atTop := g.increasing.tendsto_atTop
  have hev' := hφ.eventually hev
  have herr : ∀ᶠ k in Filter.atTop, g.error k < min (c₀ / 4) (τ / 12) :=
    (tendsto_order.1 g.error_limit).2 _ (lt_min (by positivity) (by positivity))
  have hbig : ∀ᶠ k in Filter.atTop,
      max ((4 : ℝ) ^ (1 / (c₀ / 4))) ((100 : ℝ) ^ (1 / (τ / 4))) ≤ p.N (g.φ k) :=
    (hNt.comp hφ).eventually_ge_atTop _
  filter_upwards [hev', herr, hbig] with k hk hek hNk
  obtain ⟨M₀, D₀, hmodel'⟩ := hmodel
  have hfinp : ∀ γ, IsFiniteMeasure (p.ν (g.φ k) γ) := fun γ => by
    have := ((hmodel' (g.φ k)).2.2.2.1 γ).1; infer_instance
  set Nk := p.N (g.φ k) with hNkdef
  have hN2 : 2 ≤ Nk := hN _
  have hN0 : 0 < Nk := by linarith
  have hN1 : 1 ≤ Nk := by linarith
  have hqN : q.N k = Nk := g.same_base k
  have hκ1 : 1 ≤ g.κ k := g.slack_one k
  have hκ0 : 0 < g.κ k := by linarith
  have hκN : g.κ k ≤ Nk ^ g.error k := g.slack_bound k
  have h4 : (4 : ℝ) ≤ Nk ^ (c₀ / 4) :=
    le_rpow_of_root_le (by norm_num) (by positivity) ((le_max_left _ _).trans hNk)
  have h100 : (100 : ℝ) ≤ Nk ^ (τ / 4) :=
    le_rpow_of_root_le (by norm_num) (by positivity) ((le_max_right _ _).trans hNk)
  -- the slack is small against both margins
  have hκc : g.κ k ≤ Nk ^ (c₀ / 4) :=
    hκN.trans (Real.rpow_le_rpow_of_exponent_le hN1 ((lt_min_iff.1 hek).1.le))
  have hκτ : g.κ k ≤ Nk ^ (τ / 12) :=
    hκN.trans (Real.rpow_le_rpow_of_exponent_le hN1 ((lt_min_iff.1 hek).2.le))
  have hκ3 : 100 * g.κ k ^ 3 ≤ Nk ^ (τ / 2) := by
    have : g.κ k ^ 3 ≤ Nk ^ (τ / 4) := by
      calc g.κ k ^ 3 ≤ (Nk ^ (τ / 12)) ^ 3 := pow_le_pow_left₀ hκ0.le hκτ 3
        _ = Nk ^ (τ / 4) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
    calc 100 * g.κ k ^ 3 ≤ Nk ^ (τ / 4) * Nk ^ (τ / 4) :=
          mul_le_mul h100 this (by positivity) (by positivity)
      _ = Nk ^ (τ / 2) := by rw [← Real.rpow_add hN0]; congr 1; ring
  -- the target threshold dominates the transported old threshold
  have htarget : ∀ b : Fin (q.W k), ENNReal.ofReal (100 * g.κ k ^ 2) *
      ENNReal.ofReal (Nk ^ (-p.f p.L - p.S * u + τ / 2)) *
      ENNReal.ofReal (|((g.parent k).Q (g.worlds k b)).det| /
        (p.ν (g.φ k) ((g.parent k).γ (g.worlds k b)) ((g.parent k).A (g.worlds k b))).toReal)
        ≤ ENNReal.ofReal (q.N k ^ (-q.f q.L - q.S * u + τ)) := by
    intro b
    set J := |((g.parent k).Q (g.worlds k b)).det|
    set mA := (p.ν (g.φ k) ((g.parent k).γ (g.worlds k b)) ((g.parent k).A (g.worlds k b))).toReal
    have hmA : 0 < mA := ENNReal.toReal_pos (g.prior_pos k b).ne' (measure_ne_top _ _)
    have hJ : 0 ≤ J := abs_nonneg _
    have hc := hcal k b
    rw [hqN] at hc
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), hqN,
      g.angular_rate]
    apply ENNReal.ofReal_le_ofReal
    have e1 : Nk ^ (-p.f p.L - p.S * u + τ / 2) = Nk ^ (-p.f p.L) * Nk ^ (-p.S * u + τ / 2) := by
      rw [← Real.rpow_add hN0]; congr 1; ring
    have e2 : Nk ^ (-q.f q.L - p.S * u + τ) =
        Nk ^ (τ / 2) * Nk ^ (-p.S * u + τ / 2) * Nk ^ (-q.f q.L) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; congr 1; ring
    rw [e1, e2]
    have hpow : 0 < Nk ^ (-p.S * u + τ / 2) := Real.rpow_pos_of_pos hN0 _
    have hf'' : 0 < Nk ^ (-q.f q.L) := Real.rpow_pos_of_pos hN0 _
    calc 100 * g.κ k ^ 2 * (Nk ^ (-p.f p.L) * Nk ^ (-p.S * u + τ / 2)) * (J / mA)
        = 100 * g.κ k ^ 2 * Nk ^ (-p.S * u + τ / 2) * ((Nk ^ (-p.f p.L) * J) / mA) := by ring
      _ ≤ 100 * g.κ k ^ 2 * Nk ^ (-p.S * u + τ / 2) * ((g.κ k * mA * Nk ^ (-q.f q.L)) / mA) := by
          gcongr
      _ = 100 * g.κ k ^ 3 * Nk ^ (-p.S * u + τ / 2) * Nk ^ (-q.f q.L) := by
          field_simp
      _ ≤ Nk ^ (τ / 2) * Nk ^ (-p.S * u + τ / 2) * Nk ^ (-q.f q.L) := by
          gcongr
  have hsample := geometry_angular_sample g hp k (hqE k) u hu huL (fun b => hqG k b u hu huq)
    (ENNReal.ofReal (Nk ^ (-p.f p.L - p.S * u + τ / 2)))
    (ENNReal.ofReal (q.N k ^ (-q.f q.L - q.S * u + τ))) htarget
  have hZκ : (g.Z k)⁻¹ ≤ g.κ k := by
    have := g.normalizer_lower k
    exact (inv_le_comm₀ hκ0 (g.normalizer_pos k)).1 this
  refine hsample.trans ?_
  calc 4 * ENNReal.ofReal (g.Z k)⁻¹ * _ ≤ 4 * ENNReal.ofReal (g.κ k) *
        ENNReal.ofReal (Nk ^ (-c₀)) := by
        gcongr
        exact hk
    _ = ENNReal.ofReal (4 * g.κ k * Nk ^ (-c₀)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
        norm_num
    _ ≤ ENNReal.ofReal (q.N k ^ (-(c₀ / 2))) := by
        rw [hqN]
        apply ENNReal.ofReal_le_ofReal
        calc 4 * g.κ k * Nk ^ (-c₀) ≤ Nk ^ (c₀ / 4) * Nk ^ (c₀ / 4) * Nk ^ (-c₀) := by
              gcongr
          _ = Nk ^ (-(c₀ / 2)) := by
              rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; congr 1; ring

end Angular

end Submission.Obl.k4_native_calibrated_homogeneous_remainder.Cmp
