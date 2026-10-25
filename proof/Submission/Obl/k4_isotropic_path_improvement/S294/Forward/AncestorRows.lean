-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Forward.AncestorRows, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Forward.SignalJets
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.AncestorFullPrior

/-!
# The ancestor's own test as the signal of the clock model

For the relative row packet below an ancestor packet `a` (block `[t_a, t_a + q_a]`, thickness
`δ_a`), the signal is the test `R_a` of `a`. Its clock model is taken on the clock of `a`
itself, with the polynomial `X_a = (q_a/δ_a) R_a`:

* `ancestorSignal_clock`: `2^T_a X_a = R_a / δ_a`, the physical signal of `a` (clock/physical ratio
  `θ = 1`); the model's signal derivative is `(q_a/δ_a)` times the original rate of `R_a`.
* `ancestor_clock_coefficients`: along every line of the assignment of `a` all non-constant clock
  coefficients of `X_a` are bounded by `max (24 κ) (κ² + ‖v‖)` (Markov on the block of `a` for the
  two signal jets, the plank of `a` for the base intercepts), and the constant one by `κ`.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SignalGraph

open Set MeasureTheory MvPolynomial
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open ParentSource.Native
open Submission.Lib.K4GlobalParentSignal
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
open Submission.Lib.K4ParentSignalPreparation.Census
open Submission.Obl.k4_initial_horizon_bound
open Submission.Obl.k4_scalar_grid_cartesian_field
open scoped ENNReal

noncomputable section

/-- The ancestor's test scaled so that its clock signal is its physical signal. -/
def ancestorSignal {W : ℕ} (N : ℝ) (p : PathData W) (a : Fin p.C) : Po :=
  MvPolynomial.C (((2 : ℝ) ^ p.T (p.lev a))⁻¹ / ParentSource.δ N (p.r (p.lev a))) * p.R a

theorem ancestorSignal_totalDegree {W : ℕ} (N : ℝ) (p : PathData W) (a : Fin p.C)
    (hR : (p.R a).totalDegree ≤ 2) : (ancestorSignal N p a).totalDegree ≤ 2 := by
  unfold ancestorSignal
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa using hR)

theorem eval_ancestorSignal {W : ℕ} (N : ℝ) (p : PathData W) (a : Fin p.C) (x : Fin 4 → ℝ) :
    eval x (ancestorSignal N p a) =
      ((2 : ℝ) ^ p.T (p.lev a))⁻¹ / ParentSource.δ N (p.r (p.lev a)) * eval x (p.R a) := by
  simp [ancestorSignal]

/-- The clock signal of the scaled test is the physical signal `R_a/δ_a` (ratio one). -/
theorem ancestorSignal_clock {W : ℕ} (N : ℝ) (p : PathData W) (a : Fin p.C) (z : Ev) :
    (1 : ℝ) * physicalParentSignal N p a (p.R a) z =
      clockParentSignal p a (ancestorSignal N p a) z := by
  have hδ : ParentSource.δ N (p.r (p.lev a)) ≠ 0 := by unfold ParentSource.δ; positivity
  have hc : (2 : ℝ) ^ p.T (p.lev a) ≠ 0 := by positivity
  unfold physicalParentSignal clockParentSignal
  rw [eval_ancestorSignal]
  field_simp

end

section Bounds

variable {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)

include hp

/-- Along every line of the assignment of `a`, the scaled test is bounded by `κ q_a` on the block
of `a`. -/
theorem ancestorSignal_block_bound (a : Fin p.C) {l : Ln} (hl : l ∈ p.A a) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      |eval (xp l ((p.j a : ℝ) * ((2 : ℝ) ^ p.T (p.lev a))⁻¹ +
        ((2 : ℝ) ^ p.T (p.lev a))⁻¹ * t)) (ancestorSignal (d.N k) p a)| ≤
        p.κ * ((2 : ℝ) ^ p.T (p.lev a))⁻¹ := by
  intro t ht
  rcases hp.2.2.2.2.2.2.2 a with ⟨-, -, -, -, -, -, -, -, -, -, -, hfit, -, -⟩
  set h := ((2 : ℝ) ^ p.T (p.lev a))⁻¹ with hh
  have hh0 : 0 < h := by positivity
  have hδ : 0 < ParentSource.δ (d.N k) (p.r (p.lev a)) := by unfold ParentSource.δ; positivity
  have htb : (p.j a : ℝ) * h + h * t ∈ Icc ((p.j a : ℝ) / (2 : ℝ) ^ p.T (p.lev a))
      (((p.j a : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev a)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, ← hh]
    constructor <;> nlinarith [ht.1, ht.2]
  obtain ⟨-, hR, -, -⟩ := (hfit l hl).2.2 _ htb
  rw [eval_ancestorSignal, abs_mul, abs_of_pos (div_pos hh0 hδ)]
  calc h / ParentSource.δ (d.N k) (p.r (p.lev a)) *
        |eval (xp l ((p.j a : ℝ) * h + h * t)) (p.R a)|
      ≤ h / ParentSource.δ (d.N k) (p.r (p.lev a)) *
          (p.κ * ParentSource.δ (d.N k) (p.r (p.lev a))) := by
        gcongr
        exact hR
    _ = p.κ * h := by field_simp

/-- **Clock coefficients of the scaled test** along a line of the assignment of `a`: the two
signal jets are at most `24 κ`, the base intercepts at most `κ²`, the velocities at most `‖v l‖`,
and the constant at most `κ`. -/
theorem ancestor_clock_coefficients (a : Fin p.C) (hR : (p.R a).totalDegree ≤ 2)
    {l : Ln} (hl : l ∈ p.A a) :
    |ParentSignal.clockPacketCoefficients (ancestorSignal (d.N k) p a) p a l 0| ≤ p.κ ∧
    |ParentSignal.clockPacketCoefficients (ancestorSignal (d.N k) p a) p a l 1| ≤ 24 * p.κ ∧
    |ParentSignal.clockPacketCoefficients (ancestorSignal (d.N k) p a) p a l 2| ≤ 24 * p.κ ∧
    |ParentSignal.clockPacketCoefficients (ancestorSignal (d.N k) p a) p a l 3| ≤ p.κ ^ 2 ∧
    |ParentSignal.clockPacketCoefficients (ancestorSignal (d.N k) p a) p a l 4| ≤ ‖v l‖ ∧
    |ParentSignal.clockPacketCoefficients (ancestorSignal (d.N k) p a) p a l 5| ≤ p.κ ^ 2 ∧
    |ParentSignal.clockPacketCoefficients (ancestorSignal (d.N k) p a) p a l 6| ≤ ‖v l‖ := by
  set X := ancestorSignal (d.N k) p a with hX
  set h := ((2 : ℝ) ^ p.T (p.lev a))⁻¹ with hh
  have hh0 : 0 < h := by positivity
  have hXdeg : X.totalDegree ≤ 2 := ancestorSignal_totalDegree _ p a hR
  have hbound := ancestorSignal_block_bound hp a hl
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  -- the two signal jets: Markov on the block of `a` itself
  obtain ⟨h1, h2⟩ := clockPacket_jets_of_block X hXdeg a l hh0 hbound le_rfl
    (by rw [hh]; ring_nf; exact le_rfl)
  have e1 : 24 * (p.κ * h) / h = 24 * p.κ := by field_simp
  rw [e1] at h1 h2
  -- the constant: `2^T X (x_l(t_a)) = R_a/δ_a`, bounded by `κ`
  have h0 : |ParentSignal.clockPacketCoefficients X p a l 0| ≤ p.κ := by
    have hb0 := hbound 0 (by norm_num)
    rw [mul_zero, add_zero] at hb0
    change |(2 : ℝ) ^ p.T (p.lev a) *
      ParentSignal.oldBlockCoefficients X ((p.j a : ℝ) * h) h (p.c a) (p.u a) l 0| ≤ p.κ
    have hc : (2 : ℝ) ^ p.T (p.lev a) = h⁻¹ := by rw [hh, inv_inv]
    rw [hc]
    change |h⁻¹ * eval (xp l ((p.j a : ℝ) * h)) X| ≤ p.κ
    rw [abs_mul, abs_of_pos (inv_pos.mpr hh0)]
    calc h⁻¹ * |eval (xp l ((p.j a : ℝ) * h)) X| ≤ h⁻¹ * (p.κ * h) :=
          mul_le_mul_of_nonneg_left hb0 (inv_pos.mpr hh0).le
      _ = p.κ := by field_simp
  -- the base intercepts: the plank of `a` at its left endpoint
  have hY := AncestorSource.assigned_left_base_bound hp a hl
  have hc3 : ParentSignal.clockPacketCoefficients X p a l 3 =
      (h⁻¹ • (y l ((p.j a : ℝ) * h) - p.c a - ((p.j a : ℝ) * h) • p.u a)) 0 := by
    simp only [ParentSignal.clockPacketCoefficients, ParentSignal.scaleSignal,
      ParentSignal.oldPacketCoefficients, ParentSignal.oldBlockCoefficients, y, x]
    simp [div_eq_mul_inv]
    rw [hh, inv_inv]
    ring
  have hc5 : ParentSignal.clockPacketCoefficients X p a l 5 =
      (h⁻¹ • (y l ((p.j a : ℝ) * h) - p.c a - ((p.j a : ℝ) * h) • p.u a)) 1 := by
    simp only [ParentSignal.clockPacketCoefficients, ParentSignal.scaleSignal,
      ParentSignal.oldPacketCoefficients, ParentSignal.oldBlockCoefficients, y, x]
    simp [div_eq_mul_inv]
    rw [hh, inv_inv]
    ring
  have h3 : |ParentSignal.clockPacketCoefficients X p a l 3| ≤ p.κ ^ 2 := by
    rw [hc3]; exact (PiLp.norm_apply_le _ 0).trans hY
  have h5 : |ParentSignal.clockPacketCoefficients X p a l 5| ≤ p.κ ^ 2 := by
    rw [hc5]; exact (PiLp.norm_apply_le _ 1).trans hY
  have h4 : |ParentSignal.clockPacketCoefficients X p a l 4| ≤ ‖v l‖ :=
    PiLp.norm_apply_le (v l) 0
  have h6 : |ParentSignal.clockPacketCoefficients X p a l 6| ≤ ‖v l‖ :=
    PiLp.norm_apply_le (v l) 1
  exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

end Bounds

/-- The rate is linear in the signal: `rate (c • P) = c rate P`. -/
theorem rate_C_mul (c : ℝ) (P : Po) (l : Ln) (t : ℝ) :
    rate (MvPolynomial.C c * P) l t = c * rate P l t := by
  unfold rate
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Derivation.leibniz, MvPolynomial.pderiv_C, smul_zero, add_zero, smul_eq_mul, map_mul,
    MvPolynomial.eval_C]
  ring

theorem rate_ancestorSignal {W : ℕ} (N : ℝ) (p : PathData W) (a : Fin p.C) (l : Ln) (t : ℝ) :
    rate (ancestorSignal N p a) l t =
      ((2 : ℝ) ^ p.T (p.lev a))⁻¹ / ParentSource.δ N (p.r (p.lev a)) * rate (p.R a) l t :=
  rate_C_mul _ _ l t

/-- The good lines of the ancestor model: the assignment of `a`, with bounded velocity. -/
def ancestorGood {W : ℕ} (p : PathData W) (a : Fin p.C) (Vmax : ℝ) : Set Ln :=
  p.A a ∩ {l | ‖v l‖ ≤ Vmax}

theorem measurableSet_ancestorGood {W : ℕ} (p : PathData W) (a : Fin p.C) (Vmax : ℝ)
    (hA : MeasurableSet (p.A a)) : MeasurableSet (ancestorGood p a Vmax) := by
  apply hA.inter
  apply measurableSet_le _ measurable_const
  exact (show Continuous v by unfold v; fun_prop).measurable.norm

section Model

variable {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)

include hp

/-- All clock coefficients of the scaled test on the good lines. -/
theorem ancestor_good_coefficients (a : Fin p.C) (hR : (p.R a).totalDegree ≤ 2) {Vmax : ℝ} :
    ∀ l ∈ ancestorGood p a Vmax, l ∈ p.A a → ∀ i,
      |ParentSignal.clockPacketCoefficients (ancestorSignal (d.N k) p a) p a l i| ≤
        p.κ + 24 * p.κ + p.κ ^ 2 + Vmax := by
  intro l hl _ i
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hV : 0 ≤ Vmax := (norm_nonneg _).trans hl.2
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := ancestor_clock_coefficients hp a hR hl.1
  have hv : ‖v l‖ ≤ Vmax := hl.2
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    linarith [sq_nonneg p.κ]

/-- The four jets of the scaled test on the good lines. -/
theorem ancestor_good_jets (a : Fin p.C) (hR : (p.R a).totalDegree ≤ 2) {Vmax : ℝ} :
    ∀ l ∈ ancestorGood p a Vmax,
      |ParentSignal.clockPacketCoefficients (ancestorSignal (d.N k) p a) p a l 1| ≤
          24 * p.κ + Vmax ∧
      |ParentSignal.clockPacketCoefficients (ancestorSignal (d.N k) p a) p a l 2| ≤
          24 * p.κ + Vmax ∧
      |ParentSignal.clockPacketCoefficients (ancestorSignal (d.N k) p a) p a l 4| ≤
          24 * p.κ + Vmax ∧
      |ParentSignal.clockPacketCoefficients (ancestorSignal (d.N k) p a) p a l 6| ≤
          24 * p.κ + Vmax := by
  intro l hl
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hV : 0 ≤ Vmax := (norm_nonneg _).trans hl.2
  obtain ⟨-, h1, h2, -, h4, -, h6⟩ := ancestor_clock_coefficients hp a hR hl.1
  have hv : ‖v l‖ ≤ Vmax := hl.2
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The non-constant clock coefficients of the scaled test on the good lines. -/
theorem ancestor_good_nonconstant (a : Fin p.C) (hR : (p.R a).totalDegree ≤ 2) {Vmax : ℝ} :
    ∀ l ∈ ancestorGood p a Vmax, ∀ e : Fin 7, e ≠ 0 →
      |ParentSignal.clockPacketCoefficients (ancestorSignal (d.N k) p a) p a l e| ≤
        1 + 24 * p.κ + p.κ ^ 2 + Vmax := by
  intro l hl e he
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hV : 0 ≤ Vmax := (norm_nonneg _).trans hl.2
  obtain ⟨-, h1, h2, h3, h4, h5, h6⟩ := ancestor_clock_coefficients hp a hR hl.1
  have hv : ‖v l‖ ≤ Vmax := hl.2
  have hk2 : 0 ≤ p.κ ^ 2 := sq_nonneg _
  fin_cases e
  · exact absurd rfl he
  all_goals simp only [Fin.mk_one, Fin.reduceFinMk]
  all_goals linarith

end Model

section Rows

variable {d : ProblemData} (hd : d.Valid) {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)

/-- On a good incidence of the ancestor, the derivative of the model signal at the time-changed
incidence is `(q_a/δ_a)` times the original rate of `R_a`. -/
theorem ancestor_model_rate (a : Fin p.C) (hR : (p.R a).totalDegree ≤ 2) {Vmax B : ℝ}
    (hgood : MeasurableSet (ancestorGood p a Vmax)) (hB : 0 ≤ B)
    (hcoef : ∀ l ∈ ancestorGood p a Vmax, l ∈ p.A a → ∀ i,
      |ParentSignal.clockPacketCoefficients (ancestorSignal (d.N k) p a) p a l i| ≤ B)
    (J : Set Ev) (hJ : MeasurableSet J) (hJF : J ⊆ p.F a) {x : Ev}
    (hxG : x.1 ∈ ancestorGood p a Vmax) :
    ((signalModel hp a (ancestorSignal (d.N k) p a) (ancestorGood p a Vmax) hgood hB hcoef J hJ
        hJF).signal ((hp.frozenPacket a).timeChange x).1).derivative.eval
        ((hp.frozenPacket a).timeChange x).2 =
      ((2 : ℝ) ^ p.T (p.lev a))⁻¹ / ParentSource.δ (d.N k) (p.r (p.lev a)) *
        rate (p.R a) x.1 x.2 := by
  set pm := signalModel hp a (ancestorSignal (d.N k) p a) (ancestorGood p a Vmax) hgood hB hcoef
    J hJ hJF
  rw [clock_timeChange hp a x]
  rw [← pm.scalar_x_derivative x.1 (packetTime p a x)]
  change safeSignalCoefficients _ _ p a x.1 1 +
    2 * safeSignalCoefficients _ _ p a x.1 2 * packetTime p a x = _
  rw [safeSignalCoefficients_eq _ _ p a hxG,
    ParentSignal.clockPacket_rate (ancestorSignal_totalDegree _ p a hR) p a x,
    rate_ancestorSignal]

include hd

/-- **Velocity rows of the ancestor's test on the clock of the ancestor.** From a census of
`R_a/δ_a` (with the unsheared base of `a`), a breadth renewal on the clock code of `R_a/δ_a`, and the
band cap of `R_a/δ_a` at the coarse width, MK4 gives rows on the clock codes at mesh `n` whose
error against the original rate of `R_a`, in units of `δ_a/q_a`, is `80 Kg⁷ mesh^((1-d)/24)`. -/
theorem ancestor_velocity_rows (a : Fin p.C) (hR : (p.R a).totalDegree ≤ 2)
    (hAmeas : MeasurableSet (p.A a)) {Vmax : ℝ} (hV0 : 0 ≤ Vmax)
    {fineMesh Kcensus dimension cellRate durationRate coarse radius ratio : ℝ} (steps : ℕ)
    (hFine : 0 < fineMesh) (hFine1 : fineMesh ≤ 1) (hKcensus : 1 ≤ Kcensus)
    (hsteps : Kcensus ^ (100 : ℕ) ≤ (2 : ℝ) ^ steps)
    (hresolved : fineMesh * (2 : ℝ) ^ steps ≤ 1)
    (hcellRate : 0 < cellRate) (hdurationRate : 0 < durationRate) (hratio0 : 0 ≤ ratio)
    (source : Set Ev) (hsource : MeasurableSet source) (hsourceF : source ⊆ p.F a)
    (hsourceGood : source ⊆ Prod.fst ⁻¹' ancestorGood p a Vmax)
    (hcensus : ∀ b w : ℝ, fineMesh ≤ b → b ≤ 1 → fineMesh ≤ w → w ≤ 1 →
      Kcensus ^ (100 : ℕ) * b ≤ 1 * w →
      (occupied source (fun z j => unshearedPacketBase p a z j)
        (physicalParentSignal (d.N k) p a (p.R a)) b w).Finite ∧
      ((occupied source (fun z j => unshearedPacketBase p a z j)
        (physicalParentSignal (d.N k) p a (p.R a)) b w).ncard : ℝ) ≤
        Kcensus / (b ^ 3 * w ^ dimension))
    {renewCost : ℝ≥0∞}
    (hrenew : ∀ middle : Set Ev, MeasurableSet middle → middle ⊆ source →
      ∃ current : Set Ev, MeasurableSet current ∧ current ⊆ middle ∧
        ((d.ν k (p.γ a)).prod volume) middle ≤
          ((d.ν k (p.γ a)).prod volume) current + renewCost ∧
        ∀ label (n center : P2), ‖n‖ = 1 →
          (((d.ν k (p.γ a)).prod volume).restrict current)
            {z | clockParentCode p a (ancestorSignal (d.N k) p a) (fineMesh * (2 : ℝ) ^ steps) z =
                label ∧
              |Inner.inner ℝ n ((6 * p.κ)⁻¹ • p.normalizedVelocity a z - center)| ≤ radius} ≤
            ENNReal.ofReal ratio *
              (((d.ν k (p.γ a)).prod volume).restrict current)
                (clockParentCode p a (ancestorSignal (d.N k) p a) (fineMesh * (2 : ℝ) ^ steps) ⁻¹'
                  {label}))
    (n : ℕ) (hmesh : fineMesh * (2 : ℝ) ^ steps = Submission.Lib.K4DyadicRowScales.mesh n)
    (hcoarse : coarse = Submission.Lib.K4DyadicRowScales.coarse n)
    (hdim0 : 0 ≤ dimension) (hdim1 : dimension < 1)
    {Cband : ℝ} (hCband : 0 ≤ Cband)
    (hband : ∀ U : Set P3, MeasurableSet U → ∀ c : P3 → ℝ, Measurable c →
      (((d.ν k (p.γ a)).prod volume).restrict source)
        {x | unshearedPacketBase p a x ∈ U ∧
          |clockParentSignal p a (ancestorSignal (d.N k) p a) x -
            c (unshearedPacketBase p a x)| ≤ coarse} ≤
      ENNReal.ofReal (Cband * 1 ^ (-dimension) * coarse ^ dimension) *
        (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)) * volume U)
    {Kg baseRho w gfraction ε : ℝ}
    (hKgJ : 6 * (1 + 24 * p.κ + p.κ ^ 2 + Vmax) ≤ Kg) (hKgRate : durationRate⁻¹ ≤ Kg)
    (hKgCount : 8 * Cband / cellRate ≤ Kg)
    (hbaseRho : 0 ≤ baseRho) (hcond : 1 ≤ Kg * baseRho ^ 3) (hbaseRho4 : baseRho ≤ 1 / 4)
    (hwRho : 2 * (Vmax + 1) * baseRho ≤ w)
    (hwRadius : w * d.N k ^ (2 * δ₀ * d.L) ≤ 6 * radius)
    (hgfraction : 0 < gfraction) (hgfrac : gfraction < 1 - ratio) (hε : 0 < ε)
    (hsmall : Submission.Lib.K4DyadicRowScales.mesh n ^ ((1 - dimension) / 24) ≤
      min (1 / (64 * Kg)) (min (1 / (36 * Kg ^ 4))
        ((gfraction / 4) ^ 4 * ε ^ 4 / (256 * curvatureRowConstant ^ 3 * Kg ^ 9 + 1)))) :
    ∃ (current : Set Ev) (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (retained : Set Ev),
      MeasurableSet current ∧ current ⊆ source ∧
      ((d.ν k (p.γ a)).prod volume) source ≤ ((d.ν k (p.γ a)).prod volume) current +
        (ENNReal.ofReal ((Kcensus * ((2 : ℝ) ^ steps) ^ 3) * cellRate) +
          ENNReal.ofReal (durationRate * (3 * (1 + 24 * p.κ + p.κ ^ 2 + Vmax) + 3) *
            (7 : ℝ) ^ 4)) *
          (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)) + renewCost ∧
      Measurable row ∧ MeasurableSet retained ∧
      retained ⊆ (hp.frozenPacket a).selectedEvent current ∧
      (∀ q j, |row q j| ≤ 28 * Kg ^ 6) ∧
      (((hp.frozenPacket a).prior (d.ν k (p.γ a))).prod volume).real
          ((hp.frozenPacket a).selectedEvent current) ≤
        (((hp.frozenPacket a).prior (d.ν k (p.γ a))).prod volume).real retained + ε +
          gfraction * (((hp.frozenPacket a).prior (d.ν k (p.γ a))).prod volume).real
            ((hp.frozenPacket a).selectedEvent current) ∧
      ∀ x ∈ current, (hp.frozenPacket a).timeChange x ∈ retained →
        |((2 : ℝ) ^ p.T (p.lev a))⁻¹ / ParentSource.δ (d.N k) (p.r (p.lev a)) *
            rate (p.R a) x.1 x.2 -
          ∑ j, row (clockParentCode p a (ancestorSignal (d.N k) p a)
              (Submission.Lib.K4DyadicRowScales.mesh n) x) j *
            (![1, v x.1 0, v x.1 1] : Fin 3 → ℝ) j| ≤
          80 * Kg ^ 7 * Submission.Lib.K4DyadicRowScales.mesh n ^ ((1 - dimension) / 24) := by
  have : IsProbabilityMeasure (d.ν k (p.γ a)) := (hd.weights k).2.2 _
  set X := ancestorSignal (d.N k) p a with hXdef
  set good := ancestorGood p a Vmax with hgooddef
  have hgoodM : MeasurableSet good := measurableSet_ancestorGood p a Vmax hAmeas
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  set B := p.κ + 24 * p.κ + p.κ ^ 2 + Vmax with hBdef
  have hB : 0 ≤ B := by positivity
  have hcoef := ancestor_good_coefficients hp a hR (Vmax := Vmax)
  have hXdeg : X.totalDegree ≤ 2 := ancestorSignal_totalDegree _ p a hR
  have hKc : (1 : ℝ) ≤ 1 + 24 * p.κ + p.κ ^ 2 + Vmax := by nlinarith [sq_nonneg p.κ]
  obtain ⟨stage, hcost⟩ := exists_signal_clock_stage hd hp a X good
    (physicalParentSignal (d.N k) p a (p.R a))
    (measurable_physicalParentSignal _ _ _ _) (θ := 1) (fineMesh := fineMesh)
    (Kcensus := Kcensus) (dimension := dimension) (cellRate := cellRate)
    (durationRate := durationRate) (coarse := coarse) (radius := radius) (ratio := ratio)
    (Kc := 1 + 24 * p.κ + p.κ ^ 2 + Vmax) steps one_pos
    (fun z => ancestorSignal_clock (d.N k) p a z) hFine hFine1 hKcensus hKcensus hsteps
    hresolved hcellRate.le hdurationRate.le hKc
    (hcoarse ▸ Submission.Lib.K4DyadicRowScales.coarse_pos n)
    (hcoarse ▸ Submission.Lib.K4DyadicRowScales.coarse_le_one n)
    source hsource hsourceF hsourceGood
    (fun q hq e he => ancestor_good_nonconstant hp a hR q.1 (hsourceGood hq) e he)
    hcensus hrenew
  have hF : stage.earlier ⊆ p.F a := stage.earlier_subset.trans hsourceF
  have hbandE : ∀ U : Set P3, MeasurableSet U → ∀ c : P3 → ℝ, Measurable c →
      (((d.ν k (p.γ a)).prod volume).restrict stage.earlier)
        {x | unshearedPacketBase p a x ∈ U ∧
          |clockParentSignal p a X x - c (unshearedPacketBase p a x)| ≤ coarse} ≤
      ENNReal.ofReal (Cband * 1 ^ (-dimension) * coarse ^ dimension) *
        (d.ν k (p.γ a) (p.A a) * ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev a))⁻¹)) * volume U :=
    fun U hU c hc => (Measure.restrict_mono stage.earlier_subset le_rfl _).trans (hband U hU c hc)
  obtain ⟨row, retained, hrow, hret, hsub, hbound, hloss, hfit⟩ :=
    signal_stage_velocity_rows hp a X good hgoodM hB hcoef hd stage hF n hmesh hcoarse hXdeg
      one_pos hcellRate hdurationRate hratio0 hdim0 hdim1 hKc hV0 (fun l hl => hl.2)
      (fun l hl => by
        obtain ⟨h1, h2, h4, h6⟩ := ancestor_good_jets hp a hR l hl
        refine ⟨h1.trans ?_, h2.trans ?_, h4.trans ?_, h6.trans ?_⟩ <;> nlinarith [sq_nonneg p.κ])
      hCband hbandE hKgJ hKgRate hKgCount hbaseRho hcond hbaseRho4 hwRho hwRadius hgfraction
      hgfrac hε hsmall
  refine ⟨stage.current, row, retained, stage.current_measurable,
    stage.current_subset.trans stage.earlier_subset, hcost, hrow, hret, hsub, hbound, ?_, ?_⟩
  · -- the model event mass is at most one
    have hN0 : 0 < d.N k := by linarith [hd.1 k]
    have : IsProbabilityMeasure ((hp.frozenPacket a).prior (d.ν k (p.γ a))) :=
      hp.frozenPacket_prior_probability hN0 a
    have hev : (((hp.frozenPacket a).prior (d.ν k (p.γ a))).prod volume).real
        (signalModel hp a X good hgoodM hB hcoef stage.earlier stage.earlier_measurable hF).event ≤ 1 := by
      have hsub' : (signalModel hp a X good hgoodM hB hcoef stage.earlier stage.earlier_measurable
          hF).event ⊆ univ ×ˢ Icc (0 : ℝ) 1 := fun z hz =>
        ⟨mem_univ _, (signalModel hp a X good hgoodM hB hcoef stage.earlier
          stage.earlier_measurable hF).event_time z hz⟩
      calc _ ≤ (((hp.frozenPacket a).prior (d.ν k (p.γ a))).prod volume).real
            (univ ×ˢ Icc (0 : ℝ) 1) := by
            refine measureReal_mono hsub' ?_
            rw [Measure.prod_prod]
            exact ENNReal.mul_ne_top (measure_ne_top _ _) (by simp [Real.volume_Icc])
        _ = 1 := by
            rw [measureReal_def, Measure.prod_prod, measure_univ, one_mul, Real.volume_Icc]
            simp
    calc _ ≤ _ := hloss
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left hev hε.le
          linarith
  · intro x hx hxr
    have hxG : x.1 ∈ good := stage.good_lines hx
    have hxF : x ∈ p.F a := hF (stage.current_subset hx)
    have h := hfit _ hxr
    rw [ancestor_model_rate hp a hR hgoodM hB hcoef stage.earlier stage.earlier_measurable hF hxG,
      signalModel_code_eq hp a X good hgoodM hB hcoef hXdeg stage.earlier stage.earlier_measurable
        hF hxF hxG] at h
    have hvel : (signalModel hp a X good hgoodM hB hcoef stage.earlier stage.earlier_measurable
        hF).velocity ((hp.frozenPacket a).timeChange x).1 = ![1, v x.1 0, v x.1 1] := by
      rw [clock_timeChange hp a x]
      have hpl := signalModel_planar hp a X good hgoodM hB hcoef stage.earlier
        stage.earlier_measurable hF hxG
      funext j
      fin_cases j
      · rfl
      · exact congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hpl
      · exact congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) hpl
    rw [hvel] at h
    exact h

end Rows

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.SignalGraph
