import Submission.Lib.K4ChartLifting.Bounds
import Submission.Lib.K4ChartLifting.Format
import Submission.Lib.K4ChartLifting.Mass

namespace Submission.Lib.K4ChartLifting

open MeasureTheory MvPolynomial

namespace Frame
variable (F : Frame)

/-- The normalized coefficients as polynomials of degree at most one. -/
noncomputable def normCoeffPoly : Fin 6 → MvPolynomial (Fin 6) ℝ :=
  let a₀ : MvPolynomial (Fin 6) ℝ := X 0 + C F.t₀ * X 3 - C (F.c 0) - C (F.t₀ * F.u 0)
  let a₁ : MvPolynomial (Fin 6) ℝ := X 1 + C F.t₀ * X 4 - C (F.c 1) - C (F.t₀ * F.u 1)
  let b₀ : MvPolynomial (Fin 6) ℝ := X 3 - C (F.u 0)
  let b₁ : MvPolynomial (Fin 6) ℝ := X 4 - C (F.u 1)
  ![C (F.D⁻¹ 0 0) * a₀ + C (F.D⁻¹ 0 1) * a₁,
    C (F.D⁻¹ 1 0) * a₀ + C (F.D⁻¹ 1 1) * a₁,
    X 2 + C F.t₀ * X 5,
    C F.q * (C (F.D⁻¹ 0 0) * b₀ + C (F.D⁻¹ 0 1) * b₁),
    C F.q * (C (F.D⁻¹ 1 0) * b₀ + C (F.D⁻¹ 1 1) * b₁),
    C F.q * X 5]

theorem eval_normCoeffPoly (l : Fin 6 → ℝ) :
    (fun e => eval l (F.normCoeffPoly e)) = F.normCoeff l := by
  funext e
  fin_cases e <;> simp [normCoeffPoly, normCoeff]

theorem totalDegree_normCoeffPoly_le (e : Fin 6) : (F.normCoeffPoly e).totalDegree ≤ 1 := by
  have hX : ∀ i : Fin 6, (X i : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 1 := fun i => deg1_X i
  have ha₀ : (X 0 + C F.t₀ * X 3 - C (F.c 0) - C (F.t₀ * F.u 0) :
      MvPolynomial (Fin 6) ℝ).totalDegree ≤ 1 :=
    deg1_sub (deg1_sub (deg1_add (hX 0) (deg1_C_mul _ (hX 3))) (deg1_C _)) (deg1_C _)
  have ha₁ : (X 1 + C F.t₀ * X 4 - C (F.c 1) - C (F.t₀ * F.u 1) :
      MvPolynomial (Fin 6) ℝ).totalDegree ≤ 1 :=
    deg1_sub (deg1_sub (deg1_add (hX 1) (deg1_C_mul _ (hX 4))) (deg1_C _)) (deg1_C _)
  have hb₀ : (X 3 - C (F.u 0) : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 1 :=
    deg1_sub (hX 3) (deg1_C _)
  have hb₁ : (X 4 - C (F.u 1) : MvPolynomial (Fin 6) ℝ).totalDegree ≤ 1 :=
    deg1_sub (hX 4) (deg1_C _)
  fin_cases e
  · exact deg1_add (deg1_C_mul _ ha₀) (deg1_C_mul _ ha₁)
  · exact deg1_add (deg1_C_mul _ ha₀) (deg1_C_mul _ ha₁)
  · exact deg1_add (hX 2) (deg1_C_mul _ (hX 5))
  · exact deg1_C_mul _ (deg1_add (deg1_C_mul _ hb₀) (deg1_C_mul _ hb₁))
  · exact deg1_C_mul _ (deg1_add (deg1_C_mul _ hb₀) (deg1_C_mul _ hb₁))
  · exact deg1_C_mul _ (hX 5)

/-- The normalized incidence coordinates `(normCoeff x, (x₆ - t₀) / q)` on `ℝ⁷`. -/
noncomputable def normIncPoly : Fin 7 → MvPolynomial (Fin 7) ℝ :=
  Fin.lastCases (C F.q⁻¹ * (X 6 - C F.t₀))
    (fun e => bind₁ (fun j : Fin 6 => (X j.castSucc : MvPolynomial (Fin 7) ℝ))
      (F.normCoeffPoly e))

theorem eval_normIncPoly (x : Fin 7 → ℝ) :
    (fun e => eval x (F.normIncPoly e)) =
      Fin.lastCases ((x 6 - F.t₀) / F.q) (fun e => F.normCoeff (fun j => x j.castSucc) e) := by
  funext e
  refine Fin.lastCases ?_ (fun e => ?_) e
  · rw [normIncPoly, Fin.lastCases_last, Fin.lastCases_last]
    simp [div_eq_inv_mul]
  · simp only [normIncPoly, Fin.lastCases_castSucc, eval_bind₁', eval_X]
    exact congrFun (F.eval_normCoeffPoly (fun j => x j.castSucc)) e

theorem totalDegree_normIncPoly_le (e : Fin 7) : (F.normIncPoly e).totalDegree ≤ 1 := by
  refine Fin.lastCases ?_ (fun e => ?_) e
  · simp only [normIncPoly, Fin.lastCases_last]
    exact deg1_C_mul _ (deg1_sub (deg1_X _) (deg1_C _))
  · simp only [normIncPoly, Fin.lastCases_castSucc]
    exact (totalDegree_bind₁_le_of_le_one _ (fun j => deg1_X _) _).trans
      (F.totalDegree_normCoeffPoly_le e)

end Frame

namespace ChartSystem

/-- The normalization frame of chart `c` of a system with common partition `2 ^ T`. -/
noncomputable def frameOf {W T : ℕ} (s : ChartSystem W T) (c : Fin s.count) : Frame where
  t₀ := ((s.block c : ℕ) : ℝ) / (2 : ℝ) ^ T
  q := 1 / (2 : ℝ) ^ T
  c := s.center c
  u := s.speed c
  D := s.frame c

/-- Lift a child chart system, whose worlds are the charts of `s₀`, back through `s₀`
(paper Lemma 2.13, lifting part). The child tests are multiplied by the parent
thickness `δr`. -/
noncomputable def lift {W T₀ T' : ℕ} (s₀ : ChartSystem W T₀) (E : Fin W → Set Incidence)
    (δr : ℝ) (s' : ChartSystem s₀.count T') : ChartSystem W (T₀ + T') where
  count := s'.count
  world b := s₀.world (s'.world b)
  block b := liftBlock (s₀.block (s'.world b)) (s'.block b)
  center b := (s₀.frameOf (s'.world b)).liftCenter (s'.center b) (s'.speed b)
  speed b := (s₀.frameOf (s'.world b)).liftSpeed (s'.speed b)
  frame b := s₀.frame (s'.world b) * s'.frame b
  test b := (s₀.frameOf (s'.world b)).liftTest δr (s'.test b)
  assignment b := {l | l ∈ s₀.assignment (s'.world b) ∧
    (s₀.frameOf (s'.world b)).normTraj l ∈ s'.assignment b}
  event b := {p | p ∈ E (s₀.world (s'.world b)) ∧ p.1 ∈ s₀.assignment (s'.world b) ∧
    ((s₀.frameOf (s'.world b)).normTraj p.1,
      (p.2 - (s₀.frameOf (s'.world b)).t₀) / (s₀.frameOf (s'.world b)).q) ∈ s'.event b}

theorem frameOf_q_pos {W T : ℕ} (s : ChartSystem W T) (c : Fin s.count) :
    0 < (s.frameOf c).q := by
  simp only [frameOf]; positivity

theorem mem_lift_block {W T₀ T' : ℕ} (s₀ : ChartSystem W T₀) (E : Fin W → Set Incidence)
    (δr : ℝ) (s' : ChartSystem s₀.count T') (b : Fin s'.count) (t : ℝ) :
    t ∈ timeBlock (T₀ + T') ((s₀.lift E δr s').block b) ↔
      (t - (s₀.frameOf (s'.world b)).t₀) / (s₀.frameOf (s'.world b)).q ∈
        timeBlock T' (s'.block b) :=
  mem_timeBlock_liftBlock _ _ t


/-- The pointwise chart conditions of a lifted chart, from those of the child chart. -/
theorem lift_pointwise {W T₀ T' : ℕ} (s₀ : ChartSystem W T₀) (E : Fin W → Set Incidence)
    (δr : ℝ) (s' : ChartSystem s₀.count T')
    {N κ' fL' δ' : ℝ} {M' D' : ℕ} {ω' : Fin s₀.count → ℝ}
    {ν' : Fin s₀.count → Measure Trajectory} {E' : Fin s₀.count → Set Incidence}
    {B' : Fin s₀.count → ℝ} (hs' : s'.Valid N κ' fL' δ' M' D' ω' ν' E' B')
    (hD : ∀ c, IsUnit (s₀.frame c).det) (hδr : 0 < δr)
    (b : Fin s'.count) (l : Trajectory) (hl : l ∈ (s₀.lift E δr s').assignment b) (t : ℝ)
    (ht : t ∈ timeBlock (T₀ + T') ((s₀.lift E δr s').block b)) :
    ‖Matrix.toEuclideanLin (((s₀.lift E δr s').frame b)⁻¹)
        (planarPoint l t - (s₀.lift E δr s').center b - t • (s₀.lift E δr s').speed b)‖ ≤ κ' ∧
    |MvPolynomial.eval (graphPoint l t) ((s₀.lift E δr s').test b)| ≤ κ' * (δr * δ') ∧
    |MvPolynomial.eval (graphPoint l t)
        (MvPolynomial.pderiv (3 : Fin 4) ((s₀.lift E δr s').test b))| ≤
      κ' * (δr * B' (s'.world b)) ∧
    |MvPolynomial.eval (graphPoint l t) (MvPolynomial.pderiv (3 : Fin 4)
        (MvPolynomial.pderiv (3 : Fin 4) ((s₀.lift E δr s').test b)))| ≤
      κ' * (δr * B' (s'.world b)) ^ 2 / (δr * δ') := by
  have hq : (s₀.frameOf (s'.world b)).q ≠ 0 := (s₀.frameOf_q_pos (s'.world b)).ne'
  have hDc : IsUnit (s₀.frameOf (s'.world b)).D.det := hD (s'.world b)
  obtain ⟨_, _, _, _, _, _, _, _, _, hA, _, _⟩ := hs'.2.2.1 b
  have hτ := (s₀.mem_lift_block E δr s' b t).mp ht
  obtain ⟨hgeo, htest, hd1, hd2⟩ :=
    (hA ((s₀.frameOf (s'.world b)).normTraj l) hl.2).2.2 _ hτ
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ‖Matrix.toEuclideanLin ((s₀.frameOf (s'.world b)).D * s'.frame b)⁻¹
      (planarPoint l t - (s₀.frameOf (s'.world b)).liftCenter (s'.center b) (s'.speed b) -
        t • (s₀.frameOf (s'.world b)).liftSpeed (s'.speed b))‖ ≤ κ'
    rw [(s₀.frameOf (s'.world b)).frame_lift hq hDc]
    exact hgeo
  · show |MvPolynomial.eval (graphPoint l t)
      ((s₀.frameOf (s'.world b)).liftTest δr (s'.test b))| ≤ κ' * (δr * δ')
    rw [(s₀.frameOf (s'.world b)).eval_liftTest hq, abs_mul, abs_of_pos hδr]
    calc δr * _ ≤ δr * (κ' * δ') := mul_le_mul_of_nonneg_left htest hδr.le
      _ = κ' * (δr * δ') := by ring
  · show |MvPolynomial.eval (graphPoint l t) (MvPolynomial.pderiv (3 : Fin 4)
      ((s₀.frameOf (s'.world b)).liftTest δr (s'.test b)))| ≤ κ' * (δr * B' (s'.world b))
    rw [(s₀.frameOf (s'.world b)).pderiv_liftTest,
      (s₀.frameOf (s'.world b)).eval_liftTest hq, abs_mul, abs_of_pos hδr]
    calc δr * _ ≤ δr * (κ' * B' (s'.world b)) := mul_le_mul_of_nonneg_left hd1 hδr.le
      _ = κ' * (δr * B' (s'.world b)) := by ring
  · show |MvPolynomial.eval (graphPoint l t) (MvPolynomial.pderiv (3 : Fin 4)
      (MvPolynomial.pderiv (3 : Fin 4)
        ((s₀.frameOf (s'.world b)).liftTest δr (s'.test b))))| ≤
        κ' * (δr * B' (s'.world b)) ^ 2 / (δr * δ')
    rw [(s₀.frameOf (s'.world b)).pderiv_liftTest, (s₀.frameOf (s'.world b)).pderiv_liftTest,
      (s₀.frameOf (s'.world b)).eval_liftTest hq, abs_mul, abs_of_pos hδr]
    calc δr * _ ≤ δr * (κ' * B' (s'.world b) ^ 2 / δ') := mul_le_mul_of_nonneg_left hd2 hδr.le
      _ = κ' * (δr * B' (s'.world b)) ^ 2 / (δr * δ') := by
        field_simp

/-- Properties of the lifted selected incidences, from those of the child. -/
theorem lift_event {W T₀ T' : ℕ} (s₀ : ChartSystem W T₀) (E : Fin W → Set Incidence)
    (δr : ℝ) (s' : ChartSystem s₀.count T')
    {N κ' fL' δ' : ℝ} {M' D' : ℕ} {ω' : Fin s₀.count → ℝ}
    {ν' : Fin s₀.count → Measure Trajectory} {E' : Fin s₀.count → Set Incidence}
    {B' : Fin s₀.count → ℝ} (hs' : s'.Valid N κ' fL' δ' M' D' ω' ν' E' B')
    (hδr : 0 < δr) (b : Fin s'.count) (p : Incidence)
    (hp : p ∈ (s₀.lift E δr s').event b) :
    p ∈ E ((s₀.lift E δr s').world b) ∧ p.1 ∈ (s₀.lift E δr s').assignment b ∧
      p.2 ∈ timeBlock (T₀ + T') ((s₀.lift E δr s').block b) ∧
      δr * B' (s'.world b) / κ' ≤ |MvPolynomial.eval (graphPoint p.1 p.2)
        (MvPolynomial.pderiv (3 : Fin 4) ((s₀.lift E δr s').test b))| := by
  have hq : (s₀.frameOf (s'.world b)).q ≠ 0 := (s₀.frameOf_q_pos (s'.world b)).ne'
  obtain ⟨hpE, hpA, hpF⟩ := hp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hev, _⟩ := hs'.2.2.1 b
  obtain ⟨_, hA', hT', hd⟩ := hev _ hpF
  refine ⟨hpE, ⟨hpA, hA'⟩, (s₀.mem_lift_block E δr s' b p.2).mpr hT', ?_⟩
  show δr * B' (s'.world b) / κ' ≤ |MvPolynomial.eval (graphPoint p.1 p.2)
    (MvPolynomial.pderiv (3 : Fin 4) ((s₀.frameOf (s'.world b)).liftTest δr (s'.test b)))|
  rw [(s₀.frameOf (s'.world b)).pderiv_liftTest, (s₀.frameOf (s'.world b)).eval_liftTest hq,
    abs_mul, abs_of_pos hδr, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hd hδr.le

theorem measurable_normTraj (F : Frame) : Measurable F.normTraj := by
  have hc : Continuous F.normCoeff := by
    have : F.normCoeff = fun l => fun e => MvPolynomial.eval l (F.normCoeffPoly e) := by
      funext l; exact (congrFun (F.eval_normCoeffPoly l) ·) |> funext |>.symm
    rw [this]
    exact continuous_pi fun e => MvPolynomial.continuous_eval _
  exact measurable_fst.prodMk (hc.measurable.comp measurable_snd)

/-- The selected mass of a lifted packet: `m = q ν(A₀) m'`. -/
theorem lift_event_mass {W T₀ T' : ℕ} (s₀ : ChartSystem W T₀) (E : Fin W → Set Incidence)
    (δr : ℝ) (s' : ChartSystem s₀.count T')
    {N κ' fL' δ' : ℝ} {M' D' : ℕ} {ω' : Fin s₀.count → ℝ}
    {ν' : Fin s₀.count → Measure Trajectory} {E' : Fin s₀.count → Set Incidence}
    {B' : Fin s₀.count → ℝ} (hs' : s'.Valid N κ' fL' δ' M' D' ω' ν' E' B')
    (ν : Fin W → Measure Trajectory) [∀ γ, IsFiniteMeasure (ν γ)]
    (hA₀ : ∀ c, MeasurableSet (s₀.assignment c))
    (hν' : ∀ c, ν' c = (ν (s₀.world c) (s₀.assignment c))⁻¹ •
      Measure.map (s₀.frameOf c).normTraj ((ν (s₀.world c)).restrict (s₀.assignment c)))
    (hE' : ∀ c l t, l ∈ s₀.assignment c →
      ((s₀.frameOf c).normTraj l, (t - (s₀.frameOf c).t₀) / (s₀.frameOf c).q) ∈ E' c →
        (l, t) ∈ E (s₀.world c))
    (b : Fin s'.count) :
    ((ν ((s₀.lift E δr s').world b)).prod volume) ((s₀.lift E δr s').event b) =
      ENNReal.ofReal (s₀.frameOf (s'.world b)).q *
        (ν (s₀.world (s'.world b)) (s₀.assignment (s'.world b)) *
          ((ν' (s'.world b)).prod volume) (s'.event b)) := by
  obtain ⟨_, _, _, _, _, _, _, hFm, _, _, hev, _⟩ := hs'.2.2.1 b
  set c := s'.world b
  have hset : (s₀.lift E δr s').event b = {p | p.1 ∈ s₀.assignment c ∧
      ((s₀.frameOf c).normTraj p.1, (p.2 - (s₀.frameOf c).t₀) / (s₀.frameOf c).q) ∈
        s'.event b} := by
    ext p
    constructor
    · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨hE' c p.1 p.2 h1 ((hev _ h2).1), h1, h2⟩
  have hw : (s₀.lift E δr s').world b = s₀.world c := rfl
  rw [hw, hset, prod_lift_apply _ _ (measurable_normTraj _) _ (hA₀ c) _ _
    (s₀.frameOf_q_pos c) _ hFm, hν' c, Measure.prod_smul_left, Measure.smul_apply,
    smul_eq_mul]
  congr 1
  by_cases h0 : ν (s₀.world c) (s₀.assignment c) = 0
  · have : (ν (s₀.world c)).restrict (s₀.assignment c) = 0 := Measure.restrict_eq_zero.mpr h0
    simp [this, h0]
  · rw [← mul_assoc, ENNReal.mul_inv_cancel h0 (measure_ne_top _ _), one_mul]

/-- Format of the slices of a lifted assignment. -/
theorem lift_assignment_format {W T₀ T' : ℕ} (s₀ : ChartSystem W T₀) (E : Fin W → Set Incidence)
    (δr : ℝ) (s' : ChartSystem s₀.count T') (b : Fin s'.count) (i : ℕ) {H₀ H' : ℝ} {D₀ D' : ℕ}
    (h₀ : Fmt H₀ D₀ {x | (i, x) ∈ s₀.assignment (s'.world b)})
    (h' : Fmt H' D' {x | (i, x) ∈ s'.assignment b}) :
    Fmt (H₀ + H') (max D₀ D') {x | (i, x) ∈ (s₀.lift E δr s').assignment b} := by
  have hpre := h'.preimage (s₀.frameOf (s'.world b)).normCoeffPoly
    (s₀.frameOf (s'.world b)).totalDegree_normCoeffPoly_le
  refine (h₀.inter hpre).congr ?_
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, (s₀.frameOf (s'.world b)).eval_normCoeffPoly]
  rfl

/-- Format of the slices of a lifted event. -/
theorem lift_event_format {W T₀ T' : ℕ} (s₀ : ChartSystem W T₀) (E : Fin W → Set Incidence)
    (δr : ℝ) (s' : ChartSystem s₀.count T') (b : Fin s'.count) (i : ℕ) {HE H₀ H' : ℝ}
    {DE D₀ D' : ℕ}
    (hE : Fmt HE DE {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈
      E (s₀.world (s'.world b))})
    (h₀ : Fmt H₀ D₀ {x | (i, x) ∈ s₀.assignment (s'.world b)})
    (h' : Fmt H' D' {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ s'.event b}) :
    Fmt (HE + H₀ + H') (max (max DE D₀) D') {x : Fin 7 → ℝ |
      ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ (s₀.lift E δr s').event b} := by
  have hA := h₀.preimage (fun j : Fin 6 => (MvPolynomial.X j.castSucc : MvPolynomial (Fin 7) ℝ))
    (fun j => deg1_X _)
  have hF := h'.preimage (s₀.frameOf (s'.world b)).normIncPoly
    (s₀.frameOf (s'.world b)).totalDegree_normIncPoly_le
  refine ((hE.inter hA).inter hF).congr ?_
  ext x
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, (s₀.frameOf (s'.world b)).eval_normIncPoly,
    MvPolynomial.eval_X, Fin.lastCases_castSucc]
  have h6 : (6 : Fin 7) = Fin.last 6 := rfl
  rw [h6, Fin.lastCases_last]
  simp only [lift, Set.mem_ofPred_eq, and_assoc]
  rfl

end ChartSystem

theorem liftBlock_inj {T₀ T' : ℕ} {j₀ j₁ : Fin (2 ^ T₀)} {j' j'' : Fin (2 ^ T')}
    (h : liftBlock j₀ j' = liftBlock j₁ j'') : j₀ = j₁ ∧ j' = j'' := by
  have hv : (j₀ : ℕ) * 2 ^ T' + j' = (j₁ : ℕ) * 2 ^ T' + j'' := congrArg Fin.val h
  have hp : 0 < 2 ^ T' := by positivity
  have h1 : ((j₀ : ℕ) * 2 ^ T' + j') / 2 ^ T' = j₀ := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt j'.2, zero_add]
  have h2 : ((j₁ : ℕ) * 2 ^ T' + j'') / 2 ^ T' = j₁ := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt j''.2, zero_add]
  have h3 : ((j₀ : ℕ) * 2 ^ T' + j') % 2 ^ T' = j' := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j'.2]
  have h4 : ((j₁ : ℕ) * 2 ^ T' + j'') % 2 ^ T' = j'' := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j''.2]
  refine ⟨Fin.ext ?_, Fin.ext ?_⟩
  · rw [← h1, ← h2, hv]
  · rw [← h3, ← h4, hv]

namespace ChartSystem

/-- The geometric part of the frozen chart conditions (everything except tests,
selections and masses), at slack `κ`. -/
def Geometry {W T : ℕ} (s : ChartSystem W T) (N κ : ℝ) (M D : ℕ) : Prop :=
  (s.count : ℝ) ≤ N ^ M ∧
  (∀ b b', b ≠ b' → s.world b = s.world b' → s.block b = s.block b' →
    Disjoint (s.assignment b) (s.assignment b')) ∧
  ∀ b, Matrix.det (s.frame b) ≠ 0 ∧ ‖s.center b‖ + ‖s.speed b‖ ≤ N ^ M ∧
    (∑ e : Fin 2, ∑ e' : Fin 2, (|s.frame b e e'| + |(s.frame b)⁻¹ e e'|)) ≤ N ^ M ∧
    (∑ e : Fin 2, ∑ e' : Fin 2, |s.frame b e e'|) ≤ κ / (2 : ℝ) ^ T ∧
    MeasurableSet (s.assignment b) ∧
    (∀ i, PolynomialFormat N M D {x | (i, x) ∈ s.assignment b}) ∧
    (∀ l ∈ s.assignment b, (l.1 : ℝ) ≤ N ^ M ∧ ∀ e, |l.2 e| ≤ N ^ M)

theorem lift_disjoint {W T₀ T' : ℕ} (s₀ : ChartSystem W T₀) (E : Fin W → Set Incidence)
    (δr : ℝ) (s' : ChartSystem s₀.count T')
    (h₀ : ∀ b b', b ≠ b' → s₀.world b = s₀.world b' → s₀.block b = s₀.block b' →
      Disjoint (s₀.assignment b) (s₀.assignment b'))
    (h' : ∀ b b', b ≠ b' → s'.world b = s'.world b' → s'.block b = s'.block b' →
      Disjoint (s'.assignment b) (s'.assignment b'))
    (b b' : Fin s'.count) (hbb : b ≠ b')
    (hw : (s₀.lift E δr s').world b = (s₀.lift E δr s').world b')
    (hbl : (s₀.lift E δr s').block b = (s₀.lift E δr s').block b') :
    Disjoint ((s₀.lift E δr s').assignment b) ((s₀.lift E δr s').assignment b') := by
  obtain ⟨hj₀, hj'⟩ := liftBlock_inj hbl
  by_cases hc : s'.world b = s'.world b'
  · have hd := h' b b' hbb hc hj'
    rw [Set.disjoint_left]
    rintro l ⟨_, hl⟩ ⟨_, hl'⟩
    rw [hc] at hl
    exact Set.disjoint_left.mp hd hl hl'
  · have hd := h₀ _ _ hc hw hj₀
    rw [Set.disjoint_left]
    rintro l ⟨hl, _⟩ ⟨hl', _⟩
    exact Set.disjoint_left.mp hd hl hl'

end ChartSystem
end Submission.Lib.K4ChartLifting

namespace Submission.Lib.K4ChartLifting
open MeasureTheory MvPolynomial

theorem npow_le_npow_of_le {N : ℝ} (hN : 1 ≤ N) {a b : ℕ} (h : a ≤ b) : N ^ a ≤ N ^ b :=
  pow_le_pow_right₀ hN h

theorem frameOf_t₀_div_q {W T : ℕ} (s : ChartSystem W T) (c : Fin s.count) :
    (s.frameOf c).t₀ / (s.frameOf c).q = ((s.block c : ℕ) : ℝ) := by
  simp only [ChartSystem.frameOf]
  field_simp

theorem frameOf_q_inv {W T : ℕ} (s : ChartSystem W T) (c : Fin s.count) :
    (s.frameOf c).q⁻¹ = (2 : ℝ) ^ T := by
  simp [ChartSystem.frameOf]

theorem block_lt_two_pow {T : ℕ} (j : Fin (2 ^ T)) : ((j : ℕ) : ℝ) ≤ (2 : ℝ) ^ T := by
  have : (j : ℕ) ≤ 2 ^ T := j.2.le
  exact_mod_cast this

theorem lift_center_bound {W T₀ : ℕ} (s₀ : ChartSystem W T₀) (c : Fin s₀.count)
    {N : ℝ} {M₀ M' : ℕ} (hN : 2 ≤ N) (hT₀ : (2 : ℝ) ^ T₀ ≤ N ^ M₀)
    (hcu : ‖s₀.center c‖ + ‖s₀.speed c‖ ≤ N ^ M₀)
    (hD : (∑ e : Fin 2, ∑ e' : Fin 2, |s₀.frame c e e'|) ≤ N ^ M₀)
    (c' u' : Plane) (hcu' : ‖c'‖ + ‖u'‖ ≤ N ^ M') :
    ‖(s₀.frameOf c).liftCenter c' u'‖ + ‖(s₀.frameOf c).liftSpeed u'‖ ≤
      N ^ (2 * M₀ + M' + 2) := by
  have hN1 : (1 : ℝ) ≤ N := by linarith
  set S0 := ∑ e : Fin 2, ∑ e' : Fin 2, |s₀.frame c e e'| with hS0def
  have hS00 : 0 ≤ S0 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hDc : ‖Matrix.toEuclideanLin (s₀.frame c) c'‖ ≤ S0 * ‖c'‖ := norm_toEuclideanLin_le _ _
  have hDu : ‖Matrix.toEuclideanLin (s₀.frame c) u'‖ ≤ S0 * ‖u'‖ := norm_toEuclideanLin_le _ _
  have hj := block_lt_two_pow (s₀.block c)
  have hj0 : (0 : ℝ) ≤ ((s₀.block c : ℕ) : ℝ) := Nat.cast_nonneg _
  have h1 : ‖(s₀.frameOf c).liftCenter c' u'‖ ≤
      ‖s₀.center c‖ + S0 * ‖c'‖ + N ^ M₀ * (S0 * ‖u'‖) := by
    simp only [Frame.liftCenter, frameOf_t₀_div_q]
    calc _ ≤ ‖s₀.center c + Matrix.toEuclideanLin (s₀.frameOf c).D c'‖ +
          ‖((s₀.block c : ℕ) : ℝ) • Matrix.toEuclideanLin (s₀.frameOf c).D u'‖ := norm_sub_le _ _
      _ ≤ (‖s₀.center c‖ + ‖Matrix.toEuclideanLin (s₀.frame c) c'‖) +
          ((s₀.block c : ℕ) : ℝ) * ‖Matrix.toEuclideanLin (s₀.frame c) u'‖ := by
          gcongr
          · exact norm_add_le _ _
          · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hj0]; rfl
      _ ≤ _ := by
          gcongr
          · exact hj.trans hT₀
  have h2 : ‖(s₀.frameOf c).liftSpeed u'‖ ≤ ‖s₀.speed c‖ + N ^ M₀ * (S0 * ‖u'‖) := by
    simp only [Frame.liftSpeed, frameOf_q_inv]
    calc _ ≤ ‖s₀.speed c‖ + ‖(2 : ℝ) ^ T₀ • Matrix.toEuclideanLin (s₀.frameOf c).D u'‖ :=
          norm_add_le _ _
      _ = ‖s₀.speed c‖ + (2 : ℝ) ^ T₀ * ‖Matrix.toEuclideanLin (s₀.frame c) u'‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]; rfl
      _ ≤ _ := by gcongr
  have hc' : ‖c'‖ ≤ N ^ M' := by linarith [norm_nonneg u']
  have hu' : ‖u'‖ ≤ N ^ M' := by linarith [norm_nonneg c']
  have hP0 : (0 : ℝ) ≤ N ^ M₀ := by positivity
  have hP' : (0 : ℝ) ≤ N ^ M' := by positivity
  have e1 : S0 * ‖c'‖ ≤ N ^ M₀ * N ^ M' := mul_le_mul hD hc' (norm_nonneg _) hP0
  have e2 : N ^ M₀ * (S0 * ‖u'‖) ≤ N ^ M₀ * (N ^ M₀ * N ^ M') :=
    mul_le_mul_of_nonneg_left (mul_le_mul hD hu' (norm_nonneg _) hP0) hP0
  have k1 : N ^ M₀ ≤ N ^ (2 * M₀ + M') := npow_le_npow_of_le hN1 (by omega)
  have k2 : N ^ M₀ * N ^ M' ≤ N ^ (2 * M₀ + M') := by
    rw [← pow_add]; exact npow_le_npow_of_le hN1 (by omega)
  have k3 : N ^ M₀ * (N ^ M₀ * N ^ M') = N ^ (2 * M₀ + M') := by
    rw [← pow_add, ← pow_add]; ring_nf
  have k4 : N ^ (2 * M₀ + M' + 2) = N ^ (2 * M₀ + M') * N ^ 2 := pow_add _ _ _
  have k5 : (4 : ℝ) ≤ N ^ 2 := by nlinarith
  have hpos : (0 : ℝ) ≤ N ^ (2 * M₀ + M') := by positivity
  rw [k4]
  nlinarith

theorem lift_frame_bounds (D Q : Matrix (Fin 2) (Fin 2) ℝ) {N : ℝ} {M₀ M' : ℕ} (hN : 2 ≤ N)
    (hD : (∑ e : Fin 2, ∑ e' : Fin 2, (|D e e'| + |D⁻¹ e e'|)) ≤ N ^ M₀)
    (hQ : (∑ e : Fin 2, ∑ e' : Fin 2, (|Q e e'| + |Q⁻¹ e e'|)) ≤ N ^ M') :
    (∑ e : Fin 2, ∑ e' : Fin 2, (|(D * Q) e e'| + |(D * Q)⁻¹ e e'|)) ≤
      N ^ (M₀ + M' + 1) := by
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have split : ∀ A : Matrix (Fin 2) (Fin 2) ℝ, (∑ e : Fin 2, ∑ e' : Fin 2,
      (|A e e'| + |A⁻¹ e e'|)) = (∑ e : Fin 2, ∑ e' : Fin 2, |A e e'|) +
        (∑ e : Fin 2, ∑ e' : Fin 2, |A⁻¹ e e'|) := by
    intro A; simp only [Finset.sum_add_distrib]
  rw [split] at hD hQ ⊢
  rw [Matrix.mul_inv_rev]
  have n1 := matrix_l1_mul_le D Q
  have n2 := matrix_l1_mul_le Q⁻¹ D⁻¹
  have p1 : 0 ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |D e e'| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have p2 : 0 ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |D⁻¹ e e'| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have p3 : 0 ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have p4 : 0 ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |Q⁻¹ e e'| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hP : N ^ (M₀ + M' + 1) = N ^ M₀ * N ^ M' * N := by rw [pow_add, pow_add, pow_one]
  rw [hP]
  have hP0 : (0 : ℝ) ≤ N ^ M₀ := by positivity
  have hP' : (0 : ℝ) ≤ N ^ M' := by positivity
  nlinarith [mul_le_mul (show (∑ e : Fin 2, ∑ e' : Fin 2, |D e e'|) ≤ N ^ M₀ by linarith)
      (show (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤ N ^ M' by linarith) p3 hP0,
    mul_le_mul (show (∑ e : Fin 2, ∑ e' : Fin 2, |Q⁻¹ e e'|) ≤ N ^ M' by linarith)
      (show (∑ e : Fin 2, ∑ e' : Fin 2, |D⁻¹ e e'|) ≤ N ^ M₀ by linarith) p2 hP',
    mul_nonneg hP0 hP']

end Submission.Lib.K4ChartLifting

namespace Submission.Lib.K4ChartLifting
open MeasureTheory MvPolynomial

theorem frameOf_substBound_le {W T₀ : ℕ} (s₀ : ChartSystem W T₀) (c : Fin s₀.count)
    {N : ℝ} {M₀ : ℕ} (hN : 2 ≤ N) (hT₀ : (2 : ℝ) ^ T₀ ≤ N ^ M₀)
    (hcu : ‖s₀.center c‖ + ‖s₀.speed c‖ ≤ N ^ M₀)
    (hDinv : (∑ e : Fin 2, ∑ e' : Fin 2, |(s₀.frame c)⁻¹ e e'|) ≤ N ^ M₀) :
    (s₀.frameOf c).substBound ≤ 5 * N ^ (2 * M₀) := by
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hT : (0 : ℝ) < (2 : ℝ) ^ T₀ := by positivity
  have hj := block_lt_two_pow (s₀.block c)
  have hj0 : (0 : ℝ) ≤ ((s₀.block c : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht₀ : |(s₀.frameOf c).t₀| ≤ 1 := by
    simp only [ChartSystem.frameOf]
    rw [abs_of_nonneg (by positivity), div_le_one hT]; exact hj
  have hq : |(s₀.frameOf c).q⁻¹| = (2 : ℝ) ^ T₀ := by
    rw [frameOf_q_inv, abs_of_pos hT]
  have hP0 : (1 : ℝ) ≤ N ^ M₀ := one_le_pow₀ hN1
  have h2M : N ^ (2 * M₀) = N ^ M₀ * N ^ M₀ := by rw [two_mul, pow_add]
  have hS0 : 0 ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |(s₀.frame c)⁻¹ e e'| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold Frame.substBound
  rw [hq]
  have e1 : (2 : ℝ) ^ T₀ * (1 + |(s₀.frameOf c).t₀|) ≤ 2 * N ^ M₀ := by
    nlinarith [abs_nonneg (s₀.frameOf c).t₀]
  have e2 : (∑ e : Fin 2, ∑ e' : Fin 2, |(s₀.frameOf c).D⁻¹ e e'|) *
      (1 + ‖(s₀.frameOf c).c‖ + ‖(s₀.frameOf c).u‖) ≤ N ^ M₀ * (1 + N ^ M₀) := by
    show (∑ e : Fin 2, ∑ e' : Fin 2, |(s₀.frame c)⁻¹ e e'|) *
      (1 + ‖s₀.center c‖ + ‖s₀.speed c‖) ≤ N ^ M₀ * (1 + N ^ M₀)
    apply mul_le_mul hDinv (by linarith) (by positivity) (by positivity)
  nlinarith

theorem lift_coeff_bound {W T₀ : ℕ} (s₀ : ChartSystem W T₀) (c : Fin s₀.count)
    {N : ℝ} {M₀ M' : ℕ} (hN : 2 ≤ N) (hT₀ : (2 : ℝ) ^ T₀ ≤ N ^ M₀)
    (hcu : ‖s₀.center c‖ + ‖s₀.speed c‖ ≤ N ^ M₀)
    (hDinv : (∑ e : Fin 2, ∑ e' : Fin 2, |(s₀.frame c)⁻¹ e e'|) ≤ N ^ M₀)
    {δr : ℝ} (hδr : 0 < δr) (hδr1 : δr ≤ 1) (R : MvPolynomial (Fin 4) ℝ)
    (hR : R.totalDegree ≤ 2) (hRc : ∀ e, |R.coeff e| ≤ N ^ M') (e : Fin 4 →₀ ℕ) :
    |((s₀.frameOf c).liftTest δr R).coeff e| ≤ N ^ (4 * M₀ + M' + 11) := by
  have hN1 : (1 : ℝ) ≤ N := by linarith
  set S := (s₀.frameOf c).substBound
  have hS1 : 1 ≤ S := (s₀.frameOf c).one_le_substBound
  have hS := frameOf_substBound_le s₀ c hN hT₀ hcu hDinv
  have hL1 : coeffL1 R ≤ 81 * N ^ M' := by
    have := coeffL1_le_of_coeff_le R hR (N ^ M') hRc
    norm_num at this
    exact this
  have hpow : S ^ R.totalDegree ≤ S ^ 2 := pow_le_pow_right₀ hS1 hR
  have hS2 : S ^ 2 ≤ 25 * N ^ (4 * M₀) := by
    have : N ^ (4 * M₀) = N ^ (2 * M₀) * N ^ (2 * M₀) := by rw [← pow_add]; ring_nf
    rw [this]; nlinarith
  refine ((s₀.frameOf c).abs_coeff_liftTest_le δr R e).trans ?_
  rw [abs_of_pos hδr]
  have hL0 : 0 ≤ coeffL1 R := coeffL1_nonneg R
  have hP' : (0 : ℝ) ≤ N ^ M' := by positivity
  have h11 : (2048 : ℝ) ≤ N ^ 11 := by
    calc (2048 : ℝ) = 2 ^ 11 := by norm_num
      _ ≤ N ^ 11 := pow_le_pow_left₀ (by norm_num) hN 11
  have hfin : N ^ (4 * M₀ + M' + 11) = N ^ M' * N ^ (4 * M₀) * N ^ 11 := by
    rw [pow_add, pow_add]; ring
  rw [hfin]
  have hP4 : (0 : ℝ) ≤ N ^ (4 * M₀) := by positivity
  calc δr * (coeffL1 R * S ^ R.totalDegree) ≤ 1 * (81 * N ^ M' * (25 * N ^ (4 * M₀))) := by
        apply mul_le_mul hδr1 _ (by positivity) zero_le_one
        exact mul_le_mul hL1 (hpow.trans hS2) (by positivity) (by positivity)
    _ = 2025 * (N ^ M' * N ^ (4 * M₀)) := by ring
    _ ≤ N ^ 11 * (N ^ M' * N ^ (4 * M₀)) := by
        apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = N ^ M' * N ^ (4 * M₀) * N ^ 11 := by ring

end Submission.Lib.K4ChartLifting

namespace Submission.Lib.K4ChartLifting
open MeasureTheory MvPolynomial

theorem lift_floor_real {N fL fL' κ κ' κ₁ q J₀ J' νA : ℝ} {T₀ T' : ℕ}
    (hq : q = 1 / (2 : ℝ) ^ T₀) (hκ' : 0 < κ') (hκ₁ : 0 < κ₁) (hκ : κ' * κ₁ ≤ κ)
    (hJ' : 0 ≤ J') (hνA : 0 ≤ νA) (hN : 0 < N)
    (hfloor : N ^ (-fL) * J₀ ≤ κ₁ * νA * N ^ (-fL')) :
    N ^ (-fL) * (J₀ * J') / ((2 : ℝ) ^ (T₀ + T') * κ) ≤
      q * (νA * (N ^ (-fL') * J' / ((2 : ℝ) ^ T' * κ'))) := by
  have hT₀ : (0 : ℝ) < (2 : ℝ) ^ T₀ := by positivity
  have hT' : (0 : ℝ) < (2 : ℝ) ^ T' := by positivity
  have hκpos : 0 < κ := lt_of_lt_of_le (mul_pos hκ' hκ₁) hκ
  have hNf : 0 < N ^ (-fL') := Real.rpow_pos_of_pos hN _
  rw [hq, pow_add]
  rw [div_le_iff₀ (by positivity)]
  have key : N ^ (-fL) * (J₀ * J') ≤ κ₁ * νA * N ^ (-fL') * J' := by
    calc N ^ (-fL) * (J₀ * J') = (N ^ (-fL) * J₀) * J' := by ring
      _ ≤ (κ₁ * νA * N ^ (-fL')) * J' := mul_le_mul_of_nonneg_right hfloor hJ'
  have h2 : κ₁ * νA * N ^ (-fL') * J' ≤ 1 / (2 : ℝ) ^ T₀ * (νA * (N ^ (-fL') * J' /
      ((2 : ℝ) ^ T' * κ'))) * ((2 : ℝ) ^ T₀ * (2 : ℝ) ^ T' * κ) := by
    have e : 1 / (2 : ℝ) ^ T₀ * (νA * (N ^ (-fL') * J' / ((2 : ℝ) ^ T' * κ'))) *
        ((2 : ℝ) ^ T₀ * (2 : ℝ) ^ T' * κ) = νA * N ^ (-fL') * J' * (κ / κ') := by
      field_simp
    rw [e]
    have : κ₁ ≤ κ / κ' := by rw [le_div_iff₀ hκ']; linarith
    have hX : 0 ≤ νA * N ^ (-fL') * J' := by positivity
    nlinarith
  linarith

end Submission.Lib.K4ChartLifting

namespace Submission.Lib.K4ChartLifting
open MeasureTheory MvPolynomial

namespace ChartSystem

/-- **Lifting a true terminal system through a known atlas** (paper Lemma 2.13,
lifting part, version 2). The child system lives in the normalized worlds of the
atlas `s₀`: its priors are the normalized assigned priors, its events correspond
to the original events, its derivative scales are `B / δr`, and its world weights
are proportional to `ω q ν(A₀)`. Then the lifted system satisfies all the
frozen chart conditions for the original problem, at the composed thickness. -/
theorem lift_valid {W T₀ T' : ℕ} {N κ₀ κ' κ₁ κ fL fL' δr δ' δL ρ Z : ℝ}
    {M₀ D₀ M' D' M D : ℕ}
    (ω : Fin W → ℝ) (ν : Fin W → Measure Trajectory) [∀ γ, IsFiniteMeasure (ν γ)]
    (E : Fin W → Set Incidence) (B : Fin W → ℝ)
    (s₀ : ChartSystem W T₀) (hs₀ : s₀.Geometry N κ₀ M₀ D₀)
    (hEm : ∀ γ, MeasurableSet (E γ))
    (hEf : ∀ γ i, PolynomialFormat N M₀ D₀
      {x : Fin 7 → ℝ | ((i, fun j : Fin 6 => x j.castSucc), x 6) ∈ E γ})
    (ω' : Fin s₀.count → ℝ) (ν' : Fin s₀.count → Measure Trajectory)
    (E' : Fin s₀.count → Set Incidence) (B' : Fin s₀.count → ℝ)
    (hν' : ∀ c, ν' c = (ν (s₀.world c) (s₀.assignment c))⁻¹ •
      Measure.map (s₀.frameOf c).normTraj ((ν (s₀.world c)).restrict (s₀.assignment c)))
    (hE' : ∀ c l t, l ∈ s₀.assignment c →
      ((s₀.frameOf c).normTraj l, (t - (s₀.frameOf c).t₀) / (s₀.frameOf c).q) ∈ E' c →
        (l, t) ∈ E (s₀.world c))
    (hB' : ∀ c, δr * B' c = B (s₀.world c))
    (hω' : ∀ c, ω' c * Z =
      ω (s₀.world c) * ((ν (s₀.world c) (s₀.assignment c)).toReal / (2 : ℝ) ^ T₀))
    (s' : ChartSystem s₀.count T') (hs' : s'.Valid N κ' fL' δ' M' D' ω' ν' E' B')
    (hN : 2 ≤ N) (hT₀ : (2 : ℝ) ^ T₀ ≤ N ^ M₀) (hδr : 0 < δr) (hδr1 : δr ≤ 1)
    (hρ : 1 ≤ ρ) (hδL : 0 < δL) (hδ1 : δr * δ' ≤ ρ * δL) (hδ2 : δL ≤ ρ * (δr * δ'))
    (hZ : 0 < Z) (hκZ : κ' ≤ κ * Z)
    (hfloor : ∀ c, N ^ (-fL) * |(s₀.frame c).det| ≤
      κ₁ * (ν (s₀.world c) (s₀.assignment c)).toReal * N ^ (-fL'))
    (hκ₀ : 1 ≤ κ₀) (hκ' : 1 ≤ κ') (hκ₁ : 1 ≤ κ₁) (hκ : ρ * κ₀ * κ' * κ₁ ≤ κ)
    (hM : 4 * M₀ + M' + 11 ≤ M) (hD : max D₀ D' ≤ D) (hω : ∀ γ, 0 ≤ ω γ)
    (hB : ∀ γ, 0 ≤ B γ) :
    (s₀.lift E δr s').Valid N κ fL δL M D ω ν E B := by
  classical
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hMle : ∀ a, a ≤ M → N ^ a ≤ N ^ M := fun a ha => npow_le_npow_of_le hN1 ha
  have hMle' : ∀ a b : ℕ, a ≤ b → N ^ a ≤ N ^ b := fun a b hab => npow_le_npow_of_le hN1 hab
  have hκ'pos : 0 < κ' := by linarith
  have hρ0 : (0 : ℝ) ≤ ρ := by linarith
  have hρκ' : ρ * κ' ≤ κ := by
    have h1 : ρ * κ' ≤ ρ * κ₀ * κ' := by
      have := mul_le_mul_of_nonneg_left hκ₀ hρ0
      nlinarith
    have h2 : ρ * κ₀ * κ' ≤ ρ * κ₀ * κ' * κ₁ :=
      le_mul_of_one_le_right (by positivity) hκ₁
    linarith
  have hκ'κ : κ' ≤ κ := by nlinarith
  have hκpos : 0 < κ := lt_of_lt_of_le hκ'pos hκ'κ
  obtain ⟨hcount', hdisj', hchart', htotal'⟩ := hs'
  obtain ⟨hcount₀, hdisj₀, hchart₀⟩ := hs₀
  have hD₀ : ∀ c, IsUnit (s₀.frame c).det := fun c => isUnit_iff_ne_zero.mpr (hchart₀ c).1
  have hs'v : s'.Valid N κ' fL' δ' M' D' ω' ν' E' B' := ⟨hcount', hdisj', hchart', htotal'⟩
  have hsplit : ∀ A : Matrix (Fin 2) (Fin 2) ℝ, (∑ e : Fin 2, ∑ e' : Fin 2,
      (|A e e'| + |A⁻¹ e e'|)) = (∑ e : Fin 2, ∑ e' : Fin 2, |A e e'|) +
        (∑ e : Fin 2, ∑ e' : Fin 2, |A⁻¹ e e'|) := by
    intro A; simp only [Finset.sum_add_distrib]
  have hnn : ∀ A : Matrix (Fin 2) (Fin 2) ℝ, 0 ≤ ∑ e : Fin 2, ∑ e' : Fin 2, |A e e'| :=
    fun A => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨?_, ?_, ?_, ?_⟩
  · show (s'.count : ℝ) ≤ N ^ M
    exact hcount'.trans (hMle _ (by omega))
  · exact lift_disjoint s₀ E δr s' hdisj₀ hdisj'
  · intro b
    obtain ⟨hdet₀, hcu₀, hfr₀, hfrκ₀, hAm₀, hAf₀, hAb₀⟩ := hchart₀ (s'.world b)
    obtain ⟨hdet', hcu', hfr', hfrκ', hdeg', hcoef', hAm', hFm', hfmt', hA', hF', hfl'⟩ :=
      hchart' b
    have hD0 : (∑ e : Fin 2, ∑ e' : Fin 2, |s₀.frame (s'.world b) e e'|) ≤ N ^ M₀ := by
      rw [hsplit] at hfr₀; linarith [hnn (s₀.frame (s'.world b))⁻¹]
    have hDi0 : (∑ e : Fin 2, ∑ e' : Fin 2, |(s₀.frame (s'.world b))⁻¹ e e'|) ≤ N ^ M₀ := by
      rw [hsplit] at hfr₀; linarith [hnn (s₀.frame (s'.world b))]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show (s₀.frame (s'.world b) * s'.frame b).det ≠ 0
      rw [Matrix.det_mul]; exact mul_ne_zero hdet₀ hdet'
    · exact (lift_center_bound s₀ (s'.world b) hN hT₀ hcu₀ hD0 _ _ hcu').trans
        (hMle _ (by omega))
    · exact (lift_frame_bounds _ _ hN hfr₀ hfr').trans (hMle _ (by omega))
    · show (∑ e : Fin 2, ∑ e' : Fin 2, |(s₀.frame (s'.world b) * s'.frame b) e e'|) ≤
        κ / (2 : ℝ) ^ (T₀ + T')
      refine (matrix_l1_mul_le _ _).trans ?_
      have hT0 : (0 : ℝ) < (2 : ℝ) ^ T₀ := by positivity
      have hT1 : (0 : ℝ) < (2 : ℝ) ^ T' := by positivity
      calc (∑ e : Fin 2, ∑ e' : Fin 2, |s₀.frame (s'.world b) e e'|) *
            (∑ e : Fin 2, ∑ e' : Fin 2, |s'.frame b e e'|)
          ≤ (κ₀ / (2 : ℝ) ^ T₀) * (κ' / (2 : ℝ) ^ T') :=
            mul_le_mul hfrκ₀ hfrκ' (hnn _) (by positivity)
        _ = κ₀ * κ' / (2 : ℝ) ^ (T₀ + T') := by rw [pow_add]; field_simp
        _ ≤ κ / (2 : ℝ) ^ (T₀ + T') := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            have h1 : κ₀ * κ' ≤ ρ * κ₀ * κ' := by
              have := mul_le_mul_of_nonneg_right hρ (by positivity : (0:ℝ) ≤ κ₀ * κ')
              nlinarith
            have h2 : ρ * κ₀ * κ' ≤ ρ * κ₀ * κ' * κ₁ :=
              le_mul_of_one_le_right (by positivity) hκ₁
            linarith
    · exact ((s₀.frameOf (s'.world b)).totalDegree_liftTest_le δr _).trans hdeg'
    · intro e
      exact (lift_coeff_bound s₀ (s'.world b) hN hT₀ hcu₀ hDi0 hδr hδr1 _ hdeg' hcoef' e).trans
        (hMle _ hM)
    · exact hAm₀.inter ((measurable_normTraj _) hAm')
    · have hG : Measurable (fun p : Incidence => ((s₀.frameOf (s'.world b)).normTraj p.1,
          (p.2 - (s₀.frameOf (s'.world b)).t₀) / (s₀.frameOf (s'.world b)).q)) :=
        ((measurable_normTraj _).comp measurable_fst).prodMk
          ((measurable_snd.sub_const _).div_const _)
      exact (hEm _).inter ((measurable_fst hAm₀).inter (hG hFm'))
    · intro i
      have hp2 : (2 : ℝ) ≤ N ^ 1 := by simpa using hN
      have hMM : N ^ M₀ + N ^ M₀ + N ^ M' ≤ N ^ M := by
        have a1 : N ^ M₀ ≤ N ^ (M - 2) := hMle' M₀ (M - 2) (by omega)
        have a2 : N ^ M' ≤ N ^ (M - 2) := hMle' M' (M - 2) (by omega)
        have a3 : N ^ M = N ^ (M - 2) * N ^ 2 := by rw [← pow_add]; congr 1; omega
        have a4 : (4 : ℝ) ≤ N ^ 2 := by nlinarith
        have a5 : (0 : ℝ) ≤ N ^ (M - 2) := by positivity
        rw [a3]; nlinarith
      have hM2 : N ^ M₀ + N ^ M' ≤ N ^ M := by
        have : (0 : ℝ) ≤ N ^ M₀ := by positivity
        linarith
      refine ⟨?_, ?_⟩
      · exact ((lift_assignment_format s₀ E δr s' b i (hAf₀ i) (hfmt' i).1).mono hM2
          (by omega))
      · exact ((lift_event_format s₀ E δr s' b i (hEf _ i) (hAf₀ i) (hfmt' i).2).mono hMM
          (by omega))
    · intro l hl
      obtain ⟨hl1, hl2⟩ := hAb₀ l hl.1
      refine ⟨hl1.trans (hMle _ (by omega)), fun e => (hl2 e).trans (hMle _ (by omega)),
        fun t ht => ?_⟩
      obtain ⟨g1, g2, g3, g4⟩ :=
        lift_pointwise s₀ E δr s' hs'v hD₀ hδr b l hl t ht
      have hBw : δr * B' (s'.world b) = B (s₀.world (s'.world b)) := hB' _
      have hB0 : 0 ≤ B (s₀.world (s'.world b)) := hB _
      refine ⟨g1.trans hκ'κ, ?_, ?_, ?_⟩
      · refine g2.trans ?_
        calc κ' * (δr * δ') ≤ κ' * (ρ * δL) := mul_le_mul_of_nonneg_left hδ1 hκ'pos.le
          _ = (ρ * κ') * δL := by ring
          _ ≤ κ * δL := mul_le_mul_of_nonneg_right hρκ' hδL.le
      · rw [hBw] at g3
        exact g3.trans (mul_le_mul_of_nonneg_right hκ'κ hB0)
      · rw [hBw] at g4
        refine g4.trans ?_
        have hdd : 0 < δr * δ' := by
          by_contra h
          have h' := le_of_not_gt h
          nlinarith
        rw [div_le_div_iff₀ hdd hδL]
        have hB2 : 0 ≤ B (s₀.world (s'.world b)) ^ 2 := sq_nonneg _
        calc κ' * B (s₀.world (s'.world b)) ^ 2 * δL
            ≤ κ' * B (s₀.world (s'.world b)) ^ 2 * (ρ * (δr * δ')) :=
              mul_le_mul_of_nonneg_left hδ2 (by positivity)
          _ = (ρ * κ') * B (s₀.world (s'.world b)) ^ 2 * (δr * δ') := by ring
          _ ≤ κ * B (s₀.world (s'.world b)) ^ 2 * (δr * δ') := by
              apply mul_le_mul_of_nonneg_right _ hdd.le
              exact mul_le_mul_of_nonneg_right hρκ' hB2
    · intro p hp
      obtain ⟨e1, e2, e3, e4⟩ := lift_event s₀ E δr s' hs'v hδr b p hp
      refine ⟨e1, e2, e3, ?_⟩
      have hBw : δr * B' (s'.world b) = B (s₀.world (s'.world b)) := hB' _
      rw [hBw] at e4
      refine le_trans ?_ e4
      exact div_le_div_of_nonneg_left (hB _) hκ'pos hκ'κ
    · have hmass := lift_event_mass s₀ E δr s' hs'v ν
        (fun c => (hchart₀ c).2.2.2.2.1) hν' hE' b
      rw [hmass]
      have hνA : ν (s₀.world (s'.world b)) (s₀.assignment (s'.world b)) =
          ENNReal.ofReal (ν (s₀.world (s'.world b)) (s₀.assignment (s'.world b))).toReal :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      have hq : (s₀.frameOf (s'.world b)).q = 1 / (2 : ℝ) ^ T₀ := rfl
      have hκκ : κ' * κ₁ ≤ κ := by
        have h1 : 1 ≤ ρ * κ₀ := one_le_mul_of_one_le_of_one_le hρ hκ₀
        have h2 : κ' * κ₁ ≤ ρ * κ₀ * (κ' * κ₁) :=
          le_mul_of_one_le_left (by positivity) h1
        linarith [show ρ * κ₀ * (κ' * κ₁) = ρ * κ₀ * κ' * κ₁ by ring]
      have hreal := lift_floor_real (fL := fL) (fL' := fL') (J₀ := |(s₀.frame (s'.world b)).det|)
        (J' := |(s'.frame b).det|) (T₀ := T₀) (T' := T') hq hκ'pos (by linarith) hκκ
        (abs_nonneg _) ENNReal.toReal_nonneg hNpos (hfloor (s'.world b))
      have hlhs : (s₀.lift E δr s').frame b = s₀.frame (s'.world b) * s'.frame b := rfl
      rw [hlhs, Matrix.det_mul, abs_mul]
      calc ENNReal.ofReal (N ^ (-fL) * (|(s₀.frame (s'.world b)).det| * |(s'.frame b).det|) /
            ((2 : ℝ) ^ (T₀ + T') * κ))
          ≤ ENNReal.ofReal ((s₀.frameOf (s'.world b)).q *
              ((ν (s₀.world (s'.world b)) (s₀.assignment (s'.world b))).toReal *
                (N ^ (-fL') * |(s'.frame b).det| / ((2 : ℝ) ^ T' * κ')))) :=
            ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal (s₀.frameOf (s'.world b)).q *
              (ν (s₀.world (s'.world b)) (s₀.assignment (s'.world b)) *
                ENNReal.ofReal (N ^ (-fL') * |(s'.frame b).det| / ((2 : ℝ) ^ T' * κ'))) := by
            rw [ENNReal.ofReal_mul (s₀.frameOf_q_pos _).le, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
              ← hνA]
        _ ≤ _ := by gcongr
  · -- total selected mass
    have hterm : ∀ b : Fin s'.count,
        ENNReal.ofReal (ω ((s₀.lift E δr s').world b)) *
          ((ν ((s₀.lift E δr s').world b)).prod volume) ((s₀.lift E δr s').event b) =
        ENNReal.ofReal Z * (ENNReal.ofReal (ω' (s'.world b)) *
          ((ν' (s'.world b)).prod volume) (s'.event b)) := by
      intro b
      rw [lift_event_mass s₀ E δr s' hs'v ν (fun c => (hchart₀ c).2.2.2.2.1) hν' hE' b]
      have hνA : ν (s₀.world (s'.world b)) (s₀.assignment (s'.world b)) =
          ENNReal.ofReal (ν (s₀.world (s'.world b)) (s₀.assignment (s'.world b))).toReal :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      have hω'0 : 0 ≤ ω' (s'.world b) := by
        have h := hω' (s'.world b)
        have : 0 ≤ ω' (s'.world b) * Z := by
          rw [h]; exact mul_nonneg (hω _) (by positivity)
        exact nonneg_of_mul_nonneg_left this hZ
      have hq : (s₀.frameOf (s'.world b)).q = 1 / (2 : ℝ) ^ T₀ := rfl
      have hw : (s₀.lift E δr s').world b = s₀.world (s'.world b) := rfl
      rw [hw, hνA, ← mul_assoc, ← mul_assoc, ← mul_assoc,
        ← ENNReal.ofReal_mul (hω _),
        ← ENNReal.ofReal_mul (mul_nonneg (hω _) (s₀.frameOf_q_pos _).le),
        ← ENNReal.ofReal_mul hZ.le]
      congr 2
      rw [hq, mul_comm Z, hω' (s'.world b)]
      ring
    show ENNReal.ofReal κ⁻¹ ≤ ∑ b : Fin s'.count,
      ENNReal.ofReal (ω ((s₀.lift E δr s').world b)) *
        ((ν ((s₀.lift E δr s').world b)).prod volume) ((s₀.lift E δr s').event b)
    rw [Finset.sum_congr rfl (fun b _ => hterm b), ← Finset.mul_sum]
    calc ENNReal.ofReal κ⁻¹ ≤ ENNReal.ofReal Z * ENNReal.ofReal κ'⁻¹ := by
          rw [← ENNReal.ofReal_mul hZ.le]
          apply ENNReal.ofReal_le_ofReal
          rw [← div_eq_mul_inv, le_div_iff₀ hκ'pos]
          calc κ⁻¹ * κ' ≤ κ⁻¹ * (κ * Z) :=
                mul_le_mul_of_nonneg_left hκZ (inv_nonneg.mpr hκpos.le)
            _ = Z := by field_simp
      _ ≤ _ := by gcongr

end ChartSystem
end Submission.Lib.K4ChartLifting
