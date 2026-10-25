import Submission.Obl.k4_balanced_native_packet_transport.Refined
import Submission.Obl.k4_balanced_native_packet_transport.UncappedPacket
import Submission.Obl.k4_balanced_native_packet_transport.PacketPruning
import Submission.Obl.k4_balanced_native_packet_transport.WindowTolerance
import Submission.Obl.k4_balanced_native_packet_transport.FullnessMass

/-!
Assembly of the uncapped intermediate sample from a native sample and a valid
refinement: restricted native laws, their renormalization by full original
subchart budgets, light-law pruning, coverage and transported windows.
-/

namespace Submission.Obl.k4_balanced_native_packet_transport
namespace Refined

open MeasureTheory Filter Set
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section
set_option linter.unusedVariables false

variable {W : ℕ}

namespace SampleAux

/-- Enlarging only the polynomial-size exponent preserves a chart. A variant of
`Submission.Obl.k4_quadratic_atlas_normalization.chart_mono` (this workspace) with
the slack `κ` fixed, so that no sign condition on the scale `Bv` is needed. -/
theorem chart_mono_M {N κ j r Bv : ℝ} {M M' D T : ℕ} {Ev : Set Inc}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set Traj} {F : Set Inc} {ex : Prop}
    (hN : 1 ≤ N) (hM : M ≤ M') (h : chart N M D κ T j r Bv Ev c u Q R A F ex) :
    chart N M' D κ T j r Bv Ev c u Q R A F ex := by
  have hpow : N ^ M ≤ N ^ M' := pow_le_pow_right₀ hN hM
  rcases h with ⟨hdet, hcu, hframe, hsize, hdeg, hcoeff, hA, hF, hformat, hwhole,
    hselected, hext⟩
  refine ⟨hdet, hcu.trans hpow, hframe.trans hpow, hsize, hdeg,
    fun e => (hcoeff e).trans hpow, hA, hF, ?_, ?_, hselected, hext⟩
  · intro i
    obtain ⟨⟨m₁, hm₁, p₁, hp₁, b₁, hb₁⟩, ⟨m₂, hm₂, p₂, hp₂, b₂, hb₂⟩⟩ := hformat i
    exact ⟨⟨m₁, hm₁.trans hpow, p₁, hp₁, b₁, hb₁⟩, ⟨m₂, hm₂.trans hpow, p₂, hp₂, b₂, hb₂⟩⟩
  · intro l hl
    obtain ⟨htag, hcoords, hfits⟩ := hwhole l hl
    exact ⟨htag.trans hpow, fun e => (hcoords e).trans hpow, hfits⟩

/-- The chart clauses used in the assembly. -/
theorem chart_parts {N κ j r Bv : ℝ} {M D T : ℕ} {Ev : Set Inc}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set Traj} {F : Set Inc} {ex : Prop}
    (h : chart N M D κ T j r Bv Ev c u Q R A F ex) :
    Q.det ≠ 0 ∧ ‖c‖ + ‖u‖ ≤ N ^ M ∧ (∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'|) ≤ κ / (2 : ℝ) ^ T ∧
      R.totalDegree ≤ 2 ∧ MeasurableSet A ∧ MeasurableSet F ∧
      (∀ l ∈ A, ∀ t ∈ Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T),
        ‖Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u)‖ ≤ κ ∧
        |MvPolynomial.eval (x l t) R| ≤ κ * δ N r) ∧
      (∀ p ∈ F, p.1 ∈ A ∧ p.2 ∈ Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T)) := by
  rcases h with ⟨hdet, hcu, hframe, hsize, hdeg, hcoeff, hA, hF, hformat, hwhole,
    hselected, hext⟩
  refine ⟨hdet, hcu, hsize, hdeg, hA, hF, ?_, ?_⟩
  · intro l hl t ht
    obtain ⟨_, _, hfits⟩ := hwhole l hl
    exact ⟨(hfits t ht).1, (hfits t ht).2.1⟩
  · intro p hp
    exact ⟨(hselected p hp).2.1, (hselected p hp).2.2.1⟩

/-- A unit vector reads a frame residual with the entrywise size of the frame. -/
theorem abs_inner_le_frame {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q.det ≠ 0)
    {e : EuclideanSpace ℝ (Fin 2)} (he : ‖e‖ = 1) (w : EuclideanSpace ℝ (Fin 2)) :
    |inner ℝ e w| ≤ (∑ i : Fin 2, ∑ j : Fin 2, |Q i j|) * ‖Matrix.toEuclideanLin Q⁻¹ w‖ := by
  have hw := FullnessMass.toEuclideanLin_mul_inv_apply hQ w
  calc
    |inner ℝ e w| = |inner ℝ e (Matrix.toEuclideanLin Q (Matrix.toEuclideanLin Q⁻¹ w))| := by
      rw [hw]
    _ = |inner ℝ (Matrix.toEuclideanLin Q.transpose e) (Matrix.toEuclideanLin Q⁻¹ w)| := by
      rw [FullnessMass.inner_toEuclideanLin]
    _ ≤ ‖Matrix.toEuclideanLin Q.transpose e‖ * ‖Matrix.toEuclideanLin Q⁻¹ w‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa [he] using FullnessMass.norm_toEuclideanLin_transpose_le Q e

/-- The normal of a rotation-scaling frame reads `g` times the second frame coordinate. -/
theorem abs_inner_normal_le_frame {t₁ t₂ g : ℝ} (ht : t₁ ^ 2 + t₂ ^ 2 = 1) (hg : 0 < g)
    {Q : Matrix (Fin 2) (Fin 2) ℝ} (hQ : Q = ![![t₁, -g * t₂], ![t₂, g * t₁]])
    (w : EuclideanSpace ℝ (Fin 2)) :
    |inner ℝ (WithLp.toLp 2 ![-t₂, t₁] : EuclideanSpace ℝ (Fin 2)) w| ≤
      g * ‖Matrix.toEuclideanLin Q⁻¹ w‖ := by
  have hdet : Q.det ≠ 0 := by
    rw [Matrix.det_fin_two, hQ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have : t₁ * (g * t₁) - -g * t₂ * t₂ = g := by linear_combination g * ht
    rw [this]
    exact hg.ne'
  have hinner : ∀ z : EuclideanSpace ℝ (Fin 2),
      inner ℝ (WithLp.toLp 2 ![-t₂, t₁] : EuclideanSpace ℝ (Fin 2))
        (Matrix.toEuclideanLin Q z) = g * z 1 := by
    intro z
    rw [FullnessMass.inner_fin2, FullnessMass.toEuclideanLin_apply_fin2,
      FullnessMass.toEuclideanLin_apply_fin2, hQ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (g * z 1) * ht
  have hw := FullnessMass.toEuclideanLin_mul_inv_apply hdet w
  calc
    |inner ℝ (WithLp.toLp 2 ![-t₂, t₁] : EuclideanSpace ℝ (Fin 2)) w|
        = |inner ℝ (WithLp.toLp 2 ![-t₂, t₁] : EuclideanSpace ℝ (Fin 2))
            (Matrix.toEuclideanLin Q (Matrix.toEuclideanLin Q⁻¹ w))| := by rw [hw]
    _ = g * |(Matrix.toEuclideanLin Q⁻¹ w) 1| := by
          rw [hinner, abs_mul, abs_of_pos hg]
    _ ≤ g * ‖Matrix.toEuclideanLin Q⁻¹ w‖ := by
          apply mul_le_mul_of_nonneg_left _ hg.le
          simpa using PiLp.norm_apply_le (Matrix.toEuclideanLin Q⁻¹ w) 1

/-- The native omission bound charges the selected union of each original law. -/
theorem selected_union_omission {C C' : ℕ} (parent : Fin C' → Fin C)
    (wC Rw : Fin C → ENNReal) (lam μ : Fin C → Measure Inc)
    (F : Fin C → Set Inc) (H : Fin C' → Set Inc) (hH : ∀ i, MeasurableSet (H i))
    (hHF : ∀ i, H i ⊆ F (parent i))
    (hdisj : ∀ i i', i ≠ i' → parent i = parent i' → Disjoint (H i) (H i'))
    (hdom : ∀ a, Rw a • μ a ≤ wC a • (lam a).restrict (F a))
    (hfin : ∀ a, wC a * lam a (F a) ≠ ⊤) (θ : ENNReal)
    (homit : (∑ a, wC a * lam a (F a)) ≤ (∑ a, Rw a * μ a univ) + θ) :
    (∑ i, wC (parent i) * lam (parent i) (H i)) ≤
      (∑ a, Rw a * μ a {p | ∃ i, parent i = a ∧ p ∈ H i}) + θ := by
  classical
  set U : Fin C → Set Inc := fun a => {p | ∃ i, parent i = a ∧ p ∈ H i} with hUdef
  have hUeq (a : Fin C) : U a = ⋃ i, ⋃ (_ : parent i = a), H i := by
    ext p
    simp [U]
  have hU (a : Fin C) : MeasurableSet (U a) := by
    rw [hUeq a]
    exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hH i
  have hUF (a : Fin C) : U a ⊆ F a := by
    rintro p ⟨i, rfl, hp⟩
    exact hHF i hp
  have hsplit : (∑ i, wC (parent i) * lam (parent i) (H i)) = ∑ a, wC a * lam a (U a) := by
    symm
    simpa only [true_and, ite_true] using
      Submission.Obl.k4_quadratic_finite_greedy_cover.weighted_assignment_union
        lam wC (fun _ : Fin C' => True) parent H
        (fun i _ => hH i) (fun i j _ _ hne heq => hdisj i j hne heq)
  have hF (a : Fin C) : wC a * lam a (F a) = wC a * lam a (U a) + wC a * lam a (F a \ U a) := by
    rw [← mul_add, ← measure_inter_add_sdiff (F a) (hU a), inter_eq_right.mpr (hUF a)]
  have hR (a : Fin C) : Rw a * μ a univ = Rw a * μ a (U a) + Rw a * μ a (U a)ᶜ := by
    rw [← mul_add, measure_add_measure_compl (hU a)]
  have hcompl (a : Fin C) : Rw a * μ a (U a)ᶜ ≤ wC a * lam a (F a \ U a) := by
    have h := hdom a (U a)ᶜ
    rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
      Measure.restrict_apply (hU a).compl] at h
    rwa [Set.sdiff_eq, inter_comm]
  have hYfin : (∑ a, wC a * lam a (F a \ U a)) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro a _
    exact ne_top_of_le_ne_top (hfin a) (mul_le_mul' le_rfl (measure_mono sdiff_subset))
  rw [hsplit]
  apply ENNReal.le_of_add_le_add_right hYfin
  calc
    (∑ a, wC a * lam a (U a)) + ∑ a, wC a * lam a (F a \ U a)
        = ∑ a, wC a * lam a (F a) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun a _ => (hF a).symm)
    _ ≤ (∑ a, Rw a * μ a univ) + θ := homit
    _ = (∑ a, Rw a * μ a (U a)) + (∑ a, Rw a * μ a (U a)ᶜ) + θ := by
          rw [← Finset.sum_add_distrib]
          congr 1
          exact Finset.sum_congr rfl (fun a _ => hR a)
    _ ≤ (∑ a, Rw a * μ a (U a)) + (∑ a, wC a * lam a (F a \ U a)) + θ := by
          exact add_le_add (add_le_add le_rfl (Finset.sum_le_sum fun a _ => hcompl a)) le_rfl
    _ = _ := by ring

/-- The clauses of an unbalanced native full-time sample, with its unit block
(`T = 0`, `t₀ = 0`, `q = 1`) substituted. -/
structure NFacts (σ : NativeSample W) (N K : ℝ) (ω : Fin W → ℝ) (ν : Fin W → Measure Traj)
    (E : Fin W → Set Inc) (P : Fin W → MvPolynomial (Fin 4) ℝ) (B : Fin W → ℝ)
    (M₀ D₀ : ℕ) (a₀ w ℓ χ₀ d s m S U : ℝ) : Prop where
  ambient : K ≤ N ^ ℓ
  T0 : σ.T = 0
  charts : ∀ a, chart N M₀ D₀ (N ^ ℓ) σ.T ((σ.j a : ℕ) : ℝ) 0 (B (σ.γ a)) (E (σ.γ a))
    (σ.c a) (σ.u a) (σ.Q a) (P (σ.γ a)) (σ.A a) (σ.F a)
      (∀ p ∈ σ.F a, a ∈ σ.lst (σ.γ a) (obs (B (σ.γ a)) (δ N 1) p))
  coords : ∀ a, |σ.offset a| ≤ N ^ M₀ ∧ ∀ i, |σ.tangent a i| ≤ N ^ M₀
  laws : ∀ a, RegularScalarLaw N χ₀ d s m S U
      (((ν (σ.γ a)) (σ.A a))⁻¹ • (ν (σ.γ a)).restrict (σ.A a)) (σ.law a)
      (nativeCoeff (P (σ.γ a)) 0 1 (σ.offset a) (σ.tangent a) (σ.A a)) ∧
    Measurable (σ.base a) ∧ Measurable (σ.signal a) ∧
    (∀ᵐ z ∂σ.law a, σ.base a (obs (B (σ.γ a)) (δ N 1) z) =
        WithLp.toLp 2 ![z.2, scalarY (nativeCoeff (P (σ.γ a)) 0 1 (σ.offset a)
          (σ.tangent a) (σ.A a) z.1) z.2] ∧
      |scalarX (nativeCoeff (P (σ.γ a)) 0 1 (σ.offset a) (σ.tangent a) (σ.A a) z.1) z.2 -
        σ.signal a (obs (B (σ.γ a)) (δ N 1) z)| ≤ N ^ (-1 + χ₀)) ∧
    (∀ᵐ z ∂σ.law a, z.1 ∈ σ.A a) ∧
    ν (σ.γ a) (σ.A a) • σ.law a ≤ ((ν (σ.γ a)).prod volume).restrict (σ.F a)
  cert : WindowCertificate N χ₀ d s m σ.C
    (fun a => ENNReal.ofReal (ω (σ.γ a)) * ν (σ.γ a) (σ.A a)) σ.law
    (fun a => nativeCoeff (P (σ.γ a)) 0 1 (σ.offset a) (σ.tangent a) (σ.A a))
  tangent : ∀ a, σ.tangent a 0 = 0 ∧ σ.tangent a 1 ^ 2 + σ.tangent a 2 ^ 2 = 1
  frame : ∃ g : ℝ, 0 < g ∧ g ≤ N ^ (-w) ∧ ∀ a,
    σ.Q a = ![![σ.tangent a 1, -g * σ.tangent a 2], ![σ.tangent a 2, g * σ.tangent a 1]]
  omission : (∑ a, ENNReal.ofReal (ω (σ.γ a)) * ((ν (σ.γ a)).prod volume) (σ.F a)) ≤
    (∑ a, ENNReal.ofReal (ω (σ.γ a)) * ν (σ.γ a) (σ.A a) * σ.law a univ) +
      ENNReal.ofReal (N ^ (-a₀))

theorem nfacts_of_holds {N K : ℝ} {ω : Fin W → ℝ} {ν : Fin W → Measure Traj}
    {E : Fin W → Set Inc} {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    {M₀ D₀ : ℕ} {a₀ w ℓ χ₀ d s m S U : ℝ} (σ : NativeSample W)
    (hσ : σ.Holds false N K ω ν E P B M₀ D₀ a₀ w ℓ 1 χ₀ d s m S U) :
    NFacts σ N K ω ν E P B M₀ D₀ a₀ w ℓ χ₀ d s m S U := by
  obtain ⟨hK, hT, hC, hsep, hlst, hlstm, hcharts, hcoords, hR, hlaws, hmass, hcert,
    hextra⟩ := hσ
  simp only [Bool.false_eq_true, ite_false] at hextra
  obtain ⟨hT0, htan, hframe, homit⟩ := hextra
  have hq1 : (1 : ℝ) / 2 ^ σ.T = 1 := by rw [hT0]; norm_num
  have hj0 : ∀ a, ((σ.j a : ℕ) : ℝ) = 0 := by
    intro a
    have h := (σ.j a).isLt
    have h1 : (2 : ℕ) ^ σ.T = 1 := by rw [hT0]; rfl
    have : (σ.j a : ℕ) = 0 := by omega
    simp [this]
  simp only [hq1, hj0, zero_div, ENNReal.ofReal_one, one_mul, zero_add, Prod.mk.eta,
    Measure.map_id'] at hlaws hcert homit
  refine ⟨hK, hT0, hcharts, fun a => ⟨(hcoords a).1, (hcoords a).2.1⟩, ?_, hcert, htan,
    hframe, homit⟩
  intro a
  obtain ⟨hreg, _, hb, hs, hobs, hsupp, hdom⟩ := hlaws a
  exact ⟨hreg, hb, hs, hobs, hsupp, hdom⟩

namespace NFacts

variable {σ : NativeSample W} {N K : ℝ} {ω : Fin W → ℝ} {ν : Fin W → Measure Traj}
    {E : Fin W → Set Inc} {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    {M₀ D₀ : ℕ} {a₀ w ℓ χ₀ d s m S U : ℝ}

theorem j0 (hf : NFacts σ N K ω ν E P B M₀ D₀ a₀ w ℓ χ₀ d s m S U) (a : Fin σ.C) :
    ((σ.j a : ℕ) : ℝ) = 0 := by
  have h := (σ.j a).isLt
  have h1 : (2 : ℕ) ^ σ.T = 1 := by rw [hf.T0]; rfl
  have : (σ.j a : ℕ) = 0 := by omega
  simp [this]

theorem window (hf : NFacts σ N K ω ν E P B M₀ D₀ a₀ w ℓ χ₀ d s m S U) (a : Fin σ.C) :
    Icc (((σ.j a : ℕ) : ℝ) / (2 : ℝ) ^ σ.T) ((((σ.j a : ℕ) : ℝ) + 1) / (2 : ℝ) ^ σ.T) =
      Icc (0 : ℝ) 1 := by
  rw [hf.j0 a, hf.T0]
  norm_num

theorem frame_bound (hf : NFacts σ N K ω ν E P B M₀ D₀ a₀ w ℓ χ₀ d s m S U) (a : Fin σ.C)
    (l : Traj) (hl : l ∈ σ.A a) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖Matrix.toEuclideanLin (σ.Q a)⁻¹ (y l t - σ.c a - t • σ.u a)‖ ≤ N ^ ℓ := by
  have h := (chart_parts (hf.charts a)).2.2.2.2.2.2.1 l hl t (by rw [hf.window a]; exact ht)
  exact h.1

theorem F_time (hf : NFacts σ N K ω ν E P B M₀ D₀ a₀ w ℓ χ₀ d s m S U) (a : Fin σ.C)
    (p : Inc) (hp : p ∈ σ.F a) : p.2 ∈ Icc (0 : ℝ) 1 := by
  have h := ((chart_parts (hf.charts a)).2.2.2.2.2.2.2 p hp).2
  rwa [hf.window a] at h

theorem degree (hf : NFacts σ N K ω ν E P B M₀ D₀ a₀ w ℓ χ₀ d s m S U) (a : Fin σ.C) :
    (P (σ.γ a)).totalDegree ≤ 2 :=
  (chart_parts (hf.charts a)).2.2.2.1

theorem A_meas (hf : NFacts σ N K ω ν E P B M₀ D₀ a₀ w ℓ χ₀ d s m S U) (a : Fin σ.C) :
    MeasurableSet (σ.A a) :=
  (chart_parts (hf.charts a)).2.2.2.2.1

theorem F_meas (hf : NFacts σ N K ω ν E P B M₀ D₀ a₀ w ℓ χ₀ d s m S U) (a : Fin σ.C) :
    MeasurableSet (σ.F a) :=
  (chart_parts (hf.charts a)).2.2.2.2.2.1

/-- The original incidence product of a chart is finite. -/
theorem F_finite (hf : NFacts σ N K ω ν E P B M₀ D₀ a₀ w ℓ χ₀ d s m S U)
    (hν : ∀ γ, IsProbabilityMeasure (ν γ)) (a : Fin σ.C) :
    ENNReal.ofReal (ω (σ.γ a)) * ((ν (σ.γ a)).prod volume) (σ.F a) ≠ ⊤ := by
  have := hν (σ.γ a)
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
  apply ne_top_of_le_ne_top _ (measure_mono (s := σ.F a) (t := univ ×ˢ Icc (0 : ℝ) 1) ?_)
  · rw [Measure.prod_prod]
    simp
  · intro p hp
    exact ⟨mem_univ _, hf.F_time a p hp⟩

end NFacts

/-! ### The refined packet record -/

theorem q_pos {C₀ : ℕ} (ρ : Family W C₀) : 0 < ρ.q := by
  unfold Family.q
  positivity

/-- The fixed physical tangent center of a subchart at its initial time. -/
def center (σ : NativeSample W) (ρ : Family W σ.C) (i : Fin ρ.C) : ℝ :=
  σ.offset (ρ.parent i) + inner ℝ (tangentAxis σ (ρ.parent i)) (ρ.c i + ρ.t₀ i • ρ.u i)

/-- Native laws restricted to the half-open subchart incidences and renormalized
by the full original subchart priors; time is changed to the unit block. -/
def packet (σ : NativeSample W) (ρ : Family W σ.C) (ν : Fin W → Measure Traj) :
    PacketData W where
  T := ρ.T
  C := ρ.C
  γ i := σ.γ (ρ.parent i)
  j := ρ.j
  c := ρ.c
  u := ρ.u
  Q := ρ.Q
  A := ρ.A
  F := ρ.F
  lst := ρ.lst
  offset i := (σ.offset (ρ.parent i) - center σ ρ i) / ρ.q
  tangent i k := σ.tangent (ρ.parent i) k / ρ.q
  law i := selectedBlockLaw (ν (σ.γ (ρ.parent i))) (ρ.A i) (ρ.t₀ i) ρ.q (q_pos ρ)
    (ν (σ.γ (ρ.parent i)) (σ.A (ρ.parent i))) (σ.law (ρ.parent i)) (ρ.H i)
  base i := normalizeScalarBase (ρ.t₀ i) ρ.q (center σ ρ i) ∘ σ.base (ρ.parent i)
  signal i := σ.signal (ρ.parent i)

section Basic

variable {σ : NativeSample W} {ρ : Family W σ.C} {N : ℝ} {ν : Fin W → Measure Traj}
  {E : Fin W → Set Inc} {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
  {M D : ℕ} {loss h f₀ ξ : ℝ}

theorem packet_coeff (i : Fin ρ.C) :
    (packet σ ρ ν).coeff P i = nativeCoeff (P (σ.γ (ρ.parent i))) (ρ.t₀ i) ρ.q
      ((σ.offset (ρ.parent i) - center σ ρ i) / ρ.q)
      (fun k => σ.tangent (ρ.parent i) k / ρ.q) (ρ.A i) := rfl

theorem q_le_one : ρ.q ≤ 1 := by
  unfold Family.q
  rw [div_le_one (by positivity)]
  exact one_le_pow₀ (by norm_num)

theorem t₀_nonneg (i : Fin ρ.C) : 0 ≤ ρ.t₀ i := by
  unfold Family.t₀
  positivity

theorem t₀_add_q (i : Fin ρ.C) :
    ρ.t₀ i + ρ.q = (((ρ.j i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ ρ.T := by
  unfold Family.t₀ Family.q
  rw [add_div]

theorem t₀_add_q_le (i : Fin ρ.C) : ρ.t₀ i + ρ.q ≤ 1 := by
  rw [t₀_add_q, div_le_one (by positivity)]
  have h := (ρ.j i).isLt
  have h' : ((ρ.j i : ℕ) : ℝ) + 1 ≤ ((2 ^ ρ.T : ℕ) : ℝ) := by exact_mod_cast h
  simpa using h'

theorem window_eq (i : Fin ρ.C) :
    Icc (((ρ.j i : ℕ) : ℝ) / (2 : ℝ) ^ ρ.T) ((((ρ.j i : ℕ) : ℝ) + 1) / (2 : ℝ) ^ ρ.T) =
      Icc (ρ.t₀ i) (ρ.t₀ i + ρ.q) := by
  rw [t₀_add_q]
  rfl

theorem block_mem (i : Fin ρ.C) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) 1) :
    ρ.t₀ i + ρ.q * τ ∈ Icc (ρ.t₀ i) (ρ.t₀ i + ρ.q) := by
  have hq := q_pos ρ
  constructor
  · nlinarith [hτ.1]
  · nlinarith [hτ.2]

theorem A_meas (hρ : ρ.Valid σ N ν E P B M D loss h f₀ ξ) (i : Fin ρ.C) :
    MeasurableSet (ρ.A i) :=
  (chart_parts (hρ.charts i)).2.2.2.2.1

theorem H_meas (hρ : ρ.Valid σ N ν E P B M D loss h f₀ ξ) (i : Fin ρ.C) :
    MeasurableSet (ρ.H i) :=
  (chart_parts (hρ.charts i)).2.2.2.2.2.1.inter (MeasurableSet.univ.prod measurableSet_Ico)

theorem H_sub_F (i : Fin ρ.C) : ρ.H i ⊆ ρ.F i := inter_subset_left

theorem H_sub_block (hρ : ρ.Valid σ N ν E P B M D loss h f₀ ξ) (i : Fin ρ.C) :
    ρ.H i ⊆ ρ.A i ×ˢ Icc (ρ.t₀ i) (ρ.t₀ i + ρ.q) := by
  intro p hp
  exact ⟨((chart_parts (hρ.charts i)).2.2.2.2.2.2.2 p hp.1).1, Ico_subset_Icc_self hp.2.2⟩

theorem H_disj (hρ : ρ.Valid σ N ν E P B M D loss h f₀ ξ) (i i' : Fin ρ.C) (hne : i ≠ i')
    (hpar : ρ.parent i = ρ.parent i') : Disjoint (ρ.H i) (ρ.H i') := by
  rw [Set.disjoint_left]
  intro p hp hp'
  by_cases hj : ρ.j i = ρ.j i'
  · have hA := hρ.sep i i' hne (by rw [hpar]) hj
    exact Set.disjoint_left.mp hA ((H_sub_block hρ i hp).1) ((H_sub_block hρ i' hp').1)
  · apply hj
    have h1 := hp.2.2
    have h2 := hp'.2.2
    rw [t₀_add_q] at h1 h2
    unfold Family.t₀ at h1 h2
    have hpos : (0 : ℝ) < (2 : ℝ) ^ ρ.T := by positivity
    rw [mem_Ico, div_le_iff₀ hpos, lt_div_iff₀ hpos] at h1 h2
    have ha : ((ρ.j i : ℕ) : ℝ) < ((ρ.j i' : ℕ) : ℝ) + 1 := by linarith
    have hb : ((ρ.j i' : ℕ) : ℝ) < ((ρ.j i : ℕ) : ℝ) + 1 := by linarith
    have ha' : (ρ.j i : ℕ) < (ρ.j i' : ℕ) + 1 := by exact_mod_cast ha
    have hb' : (ρ.j i' : ℕ) < (ρ.j i : ℕ) + 1 := by exact_mod_cast hb
    exact Fin.ext (by omega)

theorem prior_ne_zero (hρ : ρ.Valid σ N ν E P B M D loss h f₀ ξ) (hN : 0 < N)
    (i : Fin ρ.C) : ν (σ.γ (ρ.parent i)) (ρ.A i) ≠ 0 := by
  have hdet : 0 < |Matrix.det (ρ.Q i)| := abs_pos.mpr (chart_parts (hρ.charts i)).1
  exact ((ENNReal.ofReal_pos.mpr
    (mul_pos (Real.rpow_pos_of_pos hN _) hdet)).trans_le (hρ.prior_lower i)).ne'

theorem prior_ne_top (hν : ∀ γ, IsProbabilityMeasure (ν γ)) (i : Fin ρ.C) :
    ν (σ.γ (ρ.parent i)) (ρ.A i) ≠ ⊤ := by
  have := hν (σ.γ (ρ.parent i))
  exact measure_ne_top _ _

end Basic

/-! ### Uniform coefficient bound -/

theorem norm_tangentAxis {σ : NativeSample W} {N K : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Traj} {E : Fin W → Set Inc} {P : Fin W → MvPolynomial (Fin 4) ℝ}
    {B : Fin W → ℝ} {M₀ D₀ : ℕ} {a₀ w ℓ χ₀ d s m S U : ℝ}
    (hf : NFacts σ N K ω ν E P B M₀ D₀ a₀ w ℓ χ₀ d s m S U) (a : Fin σ.C) :
    ‖tangentAxis σ a‖ = 1 := by
  have h := FullnessMass.norm_sq_fin2 (tangentAxis σ a)
  have he : (tangentAxis σ a) 0 ^ 2 + (tangentAxis σ a) 1 ^ 2 = 1 := by
    simpa [tangentAxis] using (hf.tangent a).2
  rw [he] at h
  have h0 := norm_nonneg (tangentAxis σ a)
  nlinarith

theorem tangent_sum_eq (v : Fin 3 → ℝ) (hv : v 0 = 0) (l : Traj) (t : ℝ) :
    ∑ k : Fin 3, v k * x l t k.castSucc =
      inner ℝ (WithLp.toLp 2 ![v 1, v 2] : EuclideanSpace ℝ (Fin 2)) (y l t) := by
  rw [FullnessMass.inner_fin2]
  simp [Fin.sum_univ_three, x, y, hv]

theorem coeff_bound {σ : NativeSample W} {ρ : Family W σ.C} {N K : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Traj} {E : Fin W → Set Inc} {P : Fin W → MvPolynomial (Fin 4) ℝ}
    {B : Fin W → ℝ} {M₀ D₀ M D : ℕ} {a₀ w ℓ χ₀ d s m S U loss h f₀ ξ χ : ℝ}
    (hf : NFacts σ N K ω ν E P B M₀ D₀ a₀ w ℓ χ₀ d s m S U)
    (hρ : ρ.Valid σ N ν E P B M D loss h f₀ ξ) (hN : 1 ≤ N) (hloss : 0 < loss)
    (hcoeff₀ : 32 * N ^ χ₀ ≤ N ^ χ) (hcoeff₁ : 16 * N ^ (2 * loss) ≤ N ^ χ)
    (i : Fin ρ.C) : ∀ l k, |(packet σ ρ ν).coeff P i l k| ≤ N ^ χ := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hq := q_pos ρ
  set a := ρ.parent i with ha
  obtain ⟨hdet, _, hsize, hdeg, _, _, hwhole, _⟩ := chart_parts (hρ.charts i)
  have hAC : ρ.A i ⊆ σ.A a := hρ.A_sub i
  have hχ₀pos : 0 ≤ N ^ χ₀ := Real.rpow_nonneg hNpos.le _
  have hsq : N ^ (2 * loss) = N ^ loss * N ^ loss := by
    rw [two_mul, Real.rpow_add hNpos]
  have hloss_le : N ^ loss ≤ N ^ (2 * loss) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hbound : N ^ (2 * loss) + N ^ χ₀ ≤ N ^ χ / 8 := by
    have := Real.rpow_nonneg hNpos.le (2 * loss)
    linarith
  rw [packet_coeff]
  have h8 : N ^ χ = 8 * (N ^ χ / 8) := by ring
  intro l k
  rw [h8]
  apply nativeCoeff_bound_of_full_block (P (σ.γ a)) hdeg (ρ.t₀ i) ρ.q _ _ (ρ.A i)
    (by positivity) _ _ l k
  · intro l hl τ hτ
    rw [← nativeCoeff_scalarY (P (σ.γ a)) (ρ.t₀ i) ρ.q _ _ hl τ]
    have hslope : |nativeCoeff (P (σ.γ a)) 0 1 (σ.offset a) (σ.tangent a) (σ.A a) l 1| ≤
        N ^ χ₀ := (hf.laws a).1.2.2.2.2 l 1
    have hcenter : |scalarY (nativeCoeff (P (σ.γ a)) 0 1 (σ.offset a) (σ.tangent a)
        (σ.A a) l) (ρ.t₀ i) - center σ ρ i| ≤ ρ.q * N ^ (2 * loss) := by
      rw [nativeCoeff_scalarY (P (σ.γ a)) 0 1 _ _ (hAC hl), zero_add, one_mul,
        tangent_sum_eq _ (hf.tangent a).1]
      have hres : (σ.offset a + inner ℝ (WithLp.toLp 2 ![σ.tangent a 1, σ.tangent a 2] :
          EuclideanSpace ℝ (Fin 2)) (y l (ρ.t₀ i))) - center σ ρ i =
          inner ℝ (tangentAxis σ a) (y l (ρ.t₀ i) - ρ.c i - ρ.t₀ i • ρ.u i) := by
        unfold center
        rw [← ha, sub_sub, inner_sub_right]
        unfold tangentAxis
        ring
      rw [hres]
      have hfr := (hwhole l hl (ρ.t₀ i) (by
        rw [window_eq]; exact ⟨le_rfl, by linarith⟩)).1
      calc
        _ ≤ (∑ e : Fin 2, ∑ e' : Fin 2, |ρ.Q i e e'|) *
            ‖Matrix.toEuclideanLin (ρ.Q i)⁻¹ (y l (ρ.t₀ i) - ρ.c i - ρ.t₀ i • ρ.u i)‖ :=
          abs_inner_le_frame hdet (norm_tangentAxis hf a) _
        _ ≤ (N ^ loss / (2 : ℝ) ^ ρ.T) * N ^ loss :=
          mul_le_mul hsize hfr (norm_nonneg _) (by positivity)
        _ = ρ.q * N ^ (2 * loss) := by
          rw [hsq]
          unfold Family.q
          ring
    have := native_retime_tangent_bound (P (σ.γ a)) (ρ.t₀ i) ρ.q (σ.offset a)
      (center σ ρ i) hq (σ.tangent a) hAC hχ₀pos hl hslope hcenter hτ
    linarith
  · intro l hl τ hτ
    have hx := (hwhole l hl (ρ.t₀ i + ρ.q * τ) (by
      rw [window_eq]; exact block_mem i hτ)).2
    rw [show δ N 0 = 1 by simp [δ], mul_one] at hx
    have := Real.rpow_nonneg hNpos.le χ₀
    linarith

/-! ### Geometry of the refined packets -/

theorem packet_geometry {σ : NativeSample W} {ρ : Family W σ.C} {N K : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Traj} {E : Fin W → Set Inc} {P : Fin W → MvPolynomial (Fin 4) ℝ}
    {B : Fin W → ℝ} {M₀ D₀ M D M' : ℕ} {a₀ w ℓ χ₀ d s m S U loss h f₀ ξ : ℝ}
    (hf : NFacts σ N K ω ν E P B M₀ D₀ a₀ w ℓ χ₀ d s m S U)
    (hρ : ρ.Valid σ N ν E P B M D loss h f₀ ξ)
    (hω : ∀ γ, 0 ≤ ω γ) (hω₁ : ∑ γ, ω γ = 1) (hν : ∀ γ, IsProbabilityMeasure (ν γ))
    (hN : 1 ≤ N) (hℓ : 2 * N ^ ℓ ≤ N ^ loss) (hM : M ≤ M')
    (hM₀ : 4 * (N ^ M₀ + N ^ M) * N ^ (h + loss) ≤ N ^ M') :
    (packet σ ρ ν).Geometry N K ω ν E P B M' D loss h := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hq := q_pos ρ
  have hNM₀ : 1 ≤ N ^ M₀ := one_le_pow₀ hN
  have hNM : 0 ≤ N ^ M := pow_nonneg hNpos.le _
  have hpow : 0 ≤ N ^ (h + loss) := Real.rpow_nonneg hNpos.le _
  have hT : (2 : ℝ) ^ ρ.T ≤ N ^ (h + loss) := hρ.time
  have hqinv : ρ.q⁻¹ = (2 : ℝ) ^ ρ.T := by unfold Family.q; rw [one_div, inv_inv]
  have hp1 : 0 ≤ N ^ M₀ * N ^ (h + loss) := mul_nonneg (by linarith) hpow
  have hp2 : 0 ≤ N ^ M * N ^ (h + loss) := mul_nonneg hNM hpow
  have hM'1 : N ^ M₀ * N ^ (h + loss) ≤ N ^ M' := by nlinarith
  have hM'2 : N ^ M * N ^ (h + loss) ≤ N ^ M' := by nlinarith
  have hM'3 : N ^ (h + loss) ≤ N ^ M' := by nlinarith
  refine ⟨hf.ambient.trans (by have := Real.rpow_nonneg hNpos.le ℓ; linarith), hρ.time,
    hρ.count.trans (pow_le_pow_right₀ hN hM), fun a a' hne hγ hj => hρ.sep a a' hne hγ hj,
    hρ.lst_card, hρ.lst_meas, fun i => chart_mono_M hN hM (hρ.charts i), ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_, ?_⟩
    · show |(σ.offset (ρ.parent i) - center σ ρ i) / ρ.q| ≤ N ^ M'
      have heq : (σ.offset (ρ.parent i) - center σ ρ i) / ρ.q =
          -(inner ℝ (tangentAxis σ (ρ.parent i)) (ρ.c i + ρ.t₀ i • ρ.u i)) * ρ.q⁻¹ := by
        unfold center
        ring
      rw [heq, abs_mul, abs_neg, hqinv, abs_of_pos (show (0 : ℝ) < 2 ^ ρ.T by positivity)]
      have hcu := (chart_parts (hρ.charts i)).2.1
      have ht1 : ρ.t₀ i ≤ 1 := by linarith [t₀_add_q_le (ρ := ρ) i]
      have hinner : |inner ℝ (tangentAxis σ (ρ.parent i)) (ρ.c i + ρ.t₀ i • ρ.u i)| ≤
          N ^ M := by
        calc
          _ ≤ ‖tangentAxis σ (ρ.parent i)‖ * ‖ρ.c i + ρ.t₀ i • ρ.u i‖ :=
            abs_real_inner_le_norm _ _
          _ = ‖ρ.c i + ρ.t₀ i • ρ.u i‖ := by rw [norm_tangentAxis hf, one_mul]
          _ ≤ ‖ρ.c i‖ + ‖ρ.t₀ i • ρ.u i‖ := norm_add_le _ _
          _ ≤ ‖ρ.c i‖ + ‖ρ.u i‖ := by
            rw [norm_smul, Real.norm_of_nonneg (t₀_nonneg i)]
            nlinarith [norm_nonneg (ρ.u i), t₀_nonneg (ρ := ρ) i]
          _ ≤ N ^ M := hcu
      calc
        _ ≤ N ^ M * (2 : ℝ) ^ ρ.T :=
          mul_le_mul hinner le_rfl (by positivity) hNM
        _ ≤ N ^ M * N ^ (h + loss) := mul_le_mul_of_nonneg_left hT hNM
        _ ≤ N ^ M' := hM'2
    · intro k
      show |σ.tangent (ρ.parent i) k / ρ.q| ≤ N ^ M'
      rw [div_eq_mul_inv, abs_mul, hqinv, abs_of_pos (show (0 : ℝ) < 2 ^ ρ.T by positivity)]
      calc
        _ ≤ N ^ M₀ * (2 : ℝ) ^ ρ.T :=
          mul_le_mul ((hf.coords _).2 k) le_rfl (by positivity) (by linarith)
        _ ≤ N ^ M₀ * N ^ (h + loss) := mul_le_mul_of_nonneg_left hT (by linarith)
        _ ≤ N ^ M' := hM'1
    · show |ρ.q⁻¹| ≤ N ^ M'
      rw [hqinv, abs_of_pos (by positivity)]
      exact hT.trans hM'3
  · exact original_assignment_budget ν ω (fun i => σ.γ (ρ.parent i)) ρ.j ρ.A hν hω hω₁
      (A_meas hρ) hρ.sep

/-! ### Analysis of the refined packets -/

theorem packet_analysis {σ : NativeSample W} {ρ : Family W σ.C} {N K : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Traj} {E : Fin W → Set Inc} {P : Fin W → MvPolynomial (Fin 4) ℝ}
    {B : Fin W → ℝ} {M₀ D₀ M D : ℕ} {a₀ w ℓ χ₀ d s m S U loss h f₀ ξ χ S' U' : ℝ}
    (hf : NFacts σ N K ω ν E P B M₀ D₀ a₀ w ℓ χ₀ d s m S U)
    (hρ : ρ.Valid σ N ν E P B M D loss h f₀ ξ)
    (hν : ∀ γ, IsProbabilityMeasure (ν γ))
    (hN : 1 ≤ N) (hloss : 0 < loss) (hχ₀ : 0 < χ₀) (hχ₀χ : χ₀ ≤ χ)
    (hcoeff₀ : 32 * N ^ χ₀ ≤ N ^ χ) (hcoeff₁ : 16 * N ^ (2 * loss) ≤ N ^ χ) :
    (packet σ ρ ν).ProvisionalAnalysis N χ d s m S' U' ω ν P B := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hq := q_pos ρ
  have hNχ : 1 ≤ N ^ χ := Real.one_le_rpow hN (by linarith)
  have hsource (a : Fin σ.C) :
      ν (σ.γ a) (σ.A a) • σ.law a ≤ (ν (σ.γ a)).prod volume :=
    (hf.laws a).2.2.2.2.2.trans Measure.restrict_le_self
  have hrestore (i : Fin ρ.C) :
      (packet σ ρ ν).budget ν i •
          Measure.map ((packet σ ρ ν).expand i) ((packet σ ρ ν).law i) =
        ν (σ.γ (ρ.parent i)) (σ.A (ρ.parent i)) • (σ.law (ρ.parent i)).restrict (ρ.H i) :=
    selectedBlockLaw_restore _ _ _ _ hq _ _ _ (prior_ne_zero hρ hNpos i) (prior_ne_top hν i)
  have hbudget (i : Fin ρ.C) : (packet σ ρ ν).budget ν i ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr hq).ne' (prior_ne_zero hρ hNpos i)
  have hsupport (i : Fin ρ.C) : ∀ᵐ z ∂(packet σ ρ ν).law i, z.1 ∈ ρ.A i :=
    selectedBlockLaw_ae_assignment _ _ (A_meas hρ i) _ _ hq _ _ _ (H_meas hρ i)
      (fun p hp => ⟨(H_sub_block hρ i hp).1, mem_univ _⟩)
  have hac (i : Fin ρ.C) :
      Measure.map ((packet σ ρ ν).expand i) ((packet σ ρ ν).law i) ≪ σ.law (ρ.parent i) := by
    refine (Measure.absolutelyContinuous_smul (hbudget i)).trans ?_
    rw [hrestore i]
    exact Measure.smul_absolutelyContinuous.trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  have hε : N ^ (-1 + χ₀) ≤ N ^ (-1 + χ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  refine ⟨?_, ?_, ?_, ?_, hsupport, ?_, ?_⟩
  · intro i
    have := hν (σ.γ (ρ.parent i))
    have hb : Measurable ((packet σ ρ ν).coeff P i) :=
      measurable_nativeCoeff _ _ _ _ _ (A_meas hρ i)
    exact selectedBlockLaw_regular hNχ (ν (σ.γ (ρ.parent i))) (ρ.A i) (ρ.t₀ i) ρ.q hq
      (ν (σ.γ (ρ.parent i)) (σ.A (ρ.parent i))) (σ.law (ρ.parent i)) (ρ.H i)
      (prior_ne_zero hρ hNpos i) (prior_ne_top hν i) (hsource _) (H_sub_block hρ i)
      ((packet σ ρ ν).coeff P i) hb (coeff_bound hf hρ hN hloss hcoeff₀ hcoeff₁ i)
  · intro i
    exact (measurable_normalizeScalarBase _ _ _).comp (hf.laws _).2.1
  · intro i
    exact (hf.laws _).2.2.1
  · intro i
    obtain ⟨_, _, hobs⟩ := native_subblock_observation (P (σ.γ (ρ.parent i)))
      (hf.degree _) (σ.offset (ρ.parent i)) (σ.tangent (ρ.parent i)) (hρ.A_sub i)
      (ρ.t₀ i) ρ.q (center σ ρ i) (N ^ (-1 + χ₀)) hq.ne'
      (obs (B (σ.γ (ρ.parent i))) (δ N 1)) (σ.base (ρ.parent i)) (σ.signal (ρ.parent i))
      (hf.laws _).2.1 (hf.laws _).2.2.1 (σ.law (ρ.parent i)) ((packet σ ρ ν).law i)
      (hac i) (hsupport i) (hf.laws _).2.2.2.1
    filter_upwards [hobs] with z hz
    exact ⟨hz.1, hz.2.trans hε⟩
  · intro i
    rw [hrestore i, ← Measure.restrict_smul]
    exact (Measure.restrict_mono subset_rfl (hsource _)).trans
      (Measure.restrict_mono (H_sub_F i) le_rfl)
  · have hdom := selected_family_domination ρ.parent (fun a => ν (σ.γ a)) ρ.A ρ.t₀ ρ.q hq
      (fun a => ENNReal.ofReal (ω (σ.γ a))) (fun a => ν (σ.γ a) (σ.A a)) σ.law ρ.H
      (H_meas hρ) (H_disj hρ) (prior_ne_zero hρ hNpos) (prior_ne_top hν)
    have hpositive (i : Fin ρ.C) : 0 < (packet σ ρ ν).weight ω ν i := by
      have hw := hf.cert.weight_pos (ρ.parent i)
      exact ENNReal.mul_pos (left_ne_zero_of_mul hw.ne') (hbudget i)
    have hsupp (i : Fin ρ.C) :
        (packet σ ρ ν).law i (ρ.A i ×ˢ (univ : Set ℝ))ᶜ = 0 := by
      have h := hsupport i
      rw [ae_iff] at h
      have hset : (ρ.A i ×ˢ (univ : Set ℝ))ᶜ = {z : Inc | ¬ z.1 ∈ ρ.A i} := by
        ext z
        simp
      rw [hset]
      exact h
    have hcert := WindowCertificate.native_subblocks (fun a => P (σ.γ a))
      (fun a => hf.degree a) σ.offset σ.tangent σ.A
      (fun a => ENNReal.ofReal (ω (σ.γ a)) * ν (σ.γ a) (σ.A a)) σ.law hf.cert
      ρ.parent ρ.A (A_meas hρ) hρ.A_sub ρ.t₀ (center σ ρ) ρ.q hq q_le_one
      ((packet σ ρ ν).weight ω ν) ((packet σ ρ ν).law) hpositive hsupp
      (fun B hB => hdom B hB)
    exact hcert.mono_chi hN hχ₀χ

/-! ### Capping geometry of the refined packets -/

theorem normal_strip {σ : NativeSample W} {N K : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Traj} {E : Fin W → Set Inc} {P : Fin W → MvPolynomial (Fin 4) ℝ}
    {B : Fin W → ℝ} {M₀ D₀ : ℕ} {a₀ w ℓ χ₀ d s m S U loss U' : ℝ}
    (hf : NFacts σ N K ω ν E P B M₀ D₀ a₀ w ℓ χ₀ d s m S U)
    (hN : 0 < N) (hℓ : 2 * N ^ ℓ ≤ N ^ loss) (hw : N ^ (-w) ≤ N ^ (-U'))
    (a : Fin σ.C) (l : Traj) (hl : l ∈ σ.A a) :
    |inner ℝ (WithLp.toLp 2 ![-σ.tangent a 2, σ.tangent a 1] : EuclideanSpace ℝ (Fin 2)) (v l) -
      inner ℝ (WithLp.toLp 2 ![-σ.tangent a 2, σ.tangent a 1] : EuclideanSpace ℝ (Fin 2))
        (σ.u a)| ≤ N ^ loss * N ^ (-U') := by
  obtain ⟨g, hg, hgw, hQ⟩ := hf.frame
  set n : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![-σ.tangent a 2, σ.tangent a 1]
    with hn
  have hb : ∀ t ∈ Icc (0 : ℝ) 1,
      |inner ℝ n (y l t - σ.c a - t • σ.u a)| ≤ g * N ^ ℓ := by
    intro t ht
    exact (abs_inner_normal_le_frame (hf.tangent a).2 hg (hQ a) _).trans
      (mul_le_mul_of_nonneg_left (hf.frame_bound a l hl t ht) hg.le)
  have h0 := hb 0 ⟨le_rfl, zero_le_one⟩
  have h1 := hb 1 ⟨zero_le_one, le_rfl⟩
  have hdiff : inner ℝ n (v l) - inner ℝ n (σ.u a) =
      inner ℝ n (y l 1 - σ.c a - (1 : ℝ) • σ.u a) -
        inner ℝ n (y l 0 - σ.c a - (0 : ℝ) • σ.u a) := by
    have hy : y l 1 - y l 0 = v l := by
      ext k
      fin_cases k <;> simp [y, x, v]
    rw [← inner_sub_right, ← inner_sub_right, one_smul, zero_smul, sub_zero, ← hy]
    congr 1
    abel
  rw [hdiff]
  have hpos : 0 ≤ N ^ ℓ := Real.rpow_nonneg hN.le _
  have hsum : |inner ℝ n (y l 1 - σ.c a - (1 : ℝ) • σ.u a) -
      inner ℝ n (y l 0 - σ.c a - (0 : ℝ) • σ.u a)| ≤ g * N ^ ℓ + g * N ^ ℓ := by
    rw [abs_le] at h0 h1 ⊢
    constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]
  calc
    _ ≤ g * N ^ ℓ + g * N ^ ℓ := hsum
    _ = g * (2 * N ^ ℓ) := by ring
    _ ≤ N ^ (-w) * N ^ loss :=
      mul_le_mul hgw hℓ (by positivity) (Real.rpow_nonneg hN.le _)
    _ ≤ N ^ (-U') * N ^ loss :=
      mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg hN.le _)
    _ = N ^ loss * N ^ (-U') := mul_comm _ _

theorem packet_capping {σ : NativeSample W} {ρ : Family W σ.C} {N K : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Traj} {E : Fin W → Set Inc} {P : Fin W → MvPolynomial (Fin 4) ℝ}
    {B : Fin W → ℝ} {M₀ D₀ M D : ℕ} {a₀ w ℓ χ₀ d s m S U loss h f₀ ξ U' : ℝ}
    (hf : NFacts σ N K ω ν E P B M₀ D₀ a₀ w ℓ χ₀ d s m S U)
    (hρ : ρ.Valid σ N ν E P B M D loss h f₀ ξ)
    (hN : 0 < N) (hℓ : 2 * N ^ ℓ ≤ N ^ loss) (hw : N ^ (-w) ≤ N ^ (-U')) :
    (packet σ ρ ν).CappingGeometry N loss U' f₀ ξ ν := by
  refine ⟨hρ.prior_lower, ?_, ?_⟩
  · intro i
    show σ.tangent (ρ.parent i) 0 / ρ.q = 0
    rw [(hf.tangent _).1, zero_div]
  · intro i
    have hq := q_pos ρ
    have he : packetAxis (packet σ ρ ν).q ((packet σ ρ ν).tangent i) =
        tangentAxis σ (ρ.parent i) := by
      show packetAxis ρ.q (fun k => σ.tangent (ρ.parent i) k / ρ.q) = _
      unfold packetAxis tangentAxis
      rw [mul_div_cancel₀ _ hq.ne', mul_div_cancel₀ _ hq.ne']
    have ht := (hf.tangent (ρ.parent i)).2
    refine ⟨_, WithLp.toLp 2 ![-σ.tangent (ρ.parent i) 2, σ.tangent (ρ.parent i) 1],
      inner ℝ (WithLp.toLp 2 ![-σ.tangent (ρ.parent i) 2, σ.tangent (ρ.parent i) 1] :
        EuclideanSpace ℝ (Fin 2)) (σ.u (ρ.parent i)), rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [he]
      exact norm_tangentAxis hf _
    · have h := FullnessMass.norm_sq_fin2
        (WithLp.toLp 2 ![-σ.tangent (ρ.parent i) 2, σ.tangent (ρ.parent i) 1] :
          EuclideanSpace ℝ (Fin 2))
      have hv : (WithLp.toLp 2 ![-σ.tangent (ρ.parent i) 2, σ.tangent (ρ.parent i) 1] :
          EuclideanSpace ℝ (Fin 2)) 0 ^ 2 +
          (WithLp.toLp 2 ![-σ.tangent (ρ.parent i) 2, σ.tangent (ρ.parent i) 1] :
            EuclideanSpace ℝ (Fin 2)) 1 ^ 2 = 1 := by
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        linear_combination ht
      rw [hv] at h
      have h0 := norm_nonneg
        (WithLp.toLp 2 ![-σ.tangent (ρ.parent i) 2, σ.tangent (ρ.parent i) 1] :
          EuclideanSpace ℝ (Fin 2))
      nlinarith
    · rw [he, FullnessMass.inner_fin2]
      simp only [tangentAxis, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    · rw [he]
      exact hρ.full i
    · intro l hl
      exact normal_strip hf hN hℓ hw (ρ.parent i) l (hρ.A_sub i hl)

/-! ### Mass of the refined packets -/

theorem packet_mass {σ : NativeSample W} {ρ : Family W σ.C} {N K : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Traj} {E : Fin W → Set Inc} {P : Fin W → MvPolynomial (Fin 4) ℝ}
    {B : Fin W → ℝ} {M₀ D₀ M D : ℕ} {a₀ w ℓ χ₀ d s m S U loss h f₀ ξ χ : ℝ}
    (hf : NFacts σ N K ω ν E P B M₀ D₀ a₀ w ℓ χ₀ d s m S U)
    (hρ : ρ.Valid σ N ν E P B M D loss h f₀ ξ)
    (hν : ∀ γ, IsProbabilityMeasure (ν γ)) (hN : 0 < N)
    (hcover : ENNReal.ofReal (N ^ (-loss)) + ENNReal.ofReal (N ^ (-χ)) +
        ENNReal.ofReal (N ^ (-a₀)) ≤
      ∑ i, ENNReal.ofReal (ω (σ.γ (ρ.parent i))) *
        ((ν (σ.γ (ρ.parent i))).prod volume) (ρ.H i)) :
    ENNReal.ofReal (N ^ (-loss)) + ENNReal.ofReal (N ^ (-χ)) ≤ (packet σ ρ ν).mass ω ν := by
  have hq := q_pos ρ
  have hsel := selected_family_mass ρ.parent (fun a => ν (σ.γ a)) ρ.A ρ.t₀ ρ.q hq
    (fun a => ENNReal.ofReal (ω (σ.γ a))) (fun a => ν (σ.γ a) (σ.A a)) σ.law ρ.H
    (H_meas hρ) (H_disj hρ) (prior_ne_zero hρ hN) (prior_ne_top hν)
  have hdom (a : Fin σ.C) :
      (ENNReal.ofReal (ω (σ.γ a)) * ν (σ.γ a) (σ.A a)) • σ.law a ≤
        ENNReal.ofReal (ω (σ.γ a)) • ((ν (σ.γ a)).prod volume).restrict (σ.F a) := by
    intro S
    have h := (hf.laws a).2.2.2.2.2 S
    rw [Measure.smul_apply, smul_eq_mul] at h
    rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc]
    exact mul_le_mul' le_rfl h
  have homit := selected_union_omission ρ.parent (fun a => ENNReal.ofReal (ω (σ.γ a)))
    (fun a => ENNReal.ofReal (ω (σ.γ a)) * ν (σ.γ a) (σ.A a))
    (fun a => (ν (σ.γ a)).prod volume) σ.law σ.F ρ.H (H_meas hρ)
    (fun i => (H_sub_F i).trans (hρ.F_sub i)) (H_disj hρ) hdom (hf.F_finite hν)
    (ENNReal.ofReal (N ^ (-a₀))) hf.omission
  apply ENNReal.le_of_add_le_add_right (ENNReal.ofReal_ne_top (r := N ^ (-a₀)))
  calc
    _ ≤ _ := hcover
    _ ≤ _ := homit
    _ = (packet σ ρ ν).mass ω ν + ENNReal.ofReal (N ^ (-a₀)) := by
      congr 1
      exact hsel.symm

/-! ### Pruning and repackaging -/

theorem provisional_reindex {p : PacketData W} {N χ d s m S U : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Traj} {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    (hp : p.ProvisionalAnalysis N χ d s m S U ω ν P B) {C' : ℕ} (e : Fin C' ↪ Fin p.C) :
    (p.reindex e).ProvisionalAnalysis N χ d s m S U ω ν P B :=
  ⟨fun a => hp.regular (e a), fun a => hp.base_measurable (e a),
    fun a => hp.signal_measurable (e a), fun a => hp.observed (e a),
    fun a => hp.assignment_support (e a), fun a => hp.original_domination (e a),
    hp.certificate.reindex e⟩

theorem capping_reindex {p : PacketData W} {N loss U f₀ ξ : ℝ} {ν : Fin W → Measure Traj}
    (hp : p.CappingGeometry N loss U f₀ ξ ν) {C' : ℕ} (e : Fin C' ↪ Fin p.C) :
    (p.reindex e).CappingGeometry N loss U f₀ ξ ν :=
  ⟨fun a => hp.prior_lower (e a), fun a => hp.tangent_time (e a), fun a => hp.physical (e a)⟩

theorem uncapped_of_packet {N K : ℝ} {ω : Fin W → ℝ} {ν : Fin W → Measure Traj}
    {E : Fin W → Set Inc} {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    {M D : ℕ} {loss h χ d s m S U f₀ ξ : ℝ} (p : PacketData W)
    (hg : p.Geometry N K ω ν E P B M D loss h)
    (ha : p.ProvisionalAnalysis N χ d s m S U ω ν P B)
    (hfloor : ∀ a, ENNReal.ofReal (N ^ (-χ)) ≤ p.law a univ)
    (hmass : ENNReal.ofReal (N ^ (-loss)) ≤ p.mass ω ν)
    (hcap : p.CappingGeometry N loss U f₀ ξ ν) :
    UncappedNativeSample N K W ω ν E P B M D loss h χ d s m S U f₀ ξ :=
  ⟨p.T, p.C, p.γ, p.j, p.c, p.u, p.Q, p.A, p.F, p.lst, p.offset, p.tangent, p.law, p.base,
    p.signal, hg.ambient, hg.time, hg.count, hg.separated, hg.list_bound, hg.list_measurable,
    hg.charts, hg.coordinates, hg.budget_sum,
    fun a => ⟨ha.regular a, hfloor a, ha.base_measurable a, ha.signal_measurable a,
      ha.observed a, ha.assignment_support a, ha.original_domination a⟩,
    hmass, ha.certificate, fun a => ⟨hcap.prior_lower a, hcap.tangent_time a, hcap.physical a⟩⟩

end SampleAux

/-- The uncapped intermediate sample of the two-stage seam, assembled from one
native sample and a valid refinement. The laws are the native laws restricted
to the half-open subblock incidences, renormalized by the full original
subchart budgets; light laws are pruned. The coverage hypothesis reserves the
target mass, the light threshold and the native formatted omission. -/
theorem uncapped_of_refined
    {N K : ℝ} {ω : Fin W → ℝ} {ν : Fin W → Measure Traj} {E : Fin W → Set Inc}
    {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    {M₀ D₀ : ℕ} {a₀ w ℓ χ₀ d s m S U : ℝ}
    (σ : NativeSample W)
    (hσ : σ.Holds false N K ω ν E P B M₀ D₀ a₀ w ℓ 1 χ₀ d s m S U)
    (hω : ∀ γ, 0 ≤ ω γ) (hω₁ : ∑ γ, ω γ = 1)
    (hν : ∀ γ, IsProbabilityMeasure (ν γ))
    {M D M' : ℕ} {loss h f₀ ξ χ U' : ℝ}
    (ρ : Family W σ.C) (hρ : ρ.Valid σ N ν E P B M D loss h f₀ ξ)
    (hN : 2 ≤ N) (hloss : 0 < loss) (hloss₁ : loss ≤ 1) (hh : 0 < h)
    (hχ₀ : 0 < χ₀) (hχ₀χ : χ₀ ≤ χ)
    (hℓ : 2 * N ^ ℓ ≤ N ^ loss)
    (hcoeff₀ : 32 * N ^ χ₀ ≤ N ^ χ) (hcoeff₁ : 16 * N ^ (2 * loss) ≤ N ^ χ)
    (hw : N ^ (-w) ≤ N ^ (-U'))
    (hM : M ≤ M') (hM₀ : 4 * (N ^ M₀ + N ^ M) * N ^ (h + loss) ≤ N ^ M')
    (hcover : ENNReal.ofReal (N ^ (-loss)) + ENNReal.ofReal (N ^ (-χ)) +
        ENNReal.ofReal (N ^ (-a₀)) ≤
      ∑ i, ENNReal.ofReal (ω (σ.γ (ρ.parent i))) *
        ((ν (σ.γ (ρ.parent i))).prod volume) (ρ.H i)) :
    UncappedNativeSample N K W ω ν E P B M' D loss h χ d s m S U' f₀ ξ := by
  classical
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hf := SampleAux.nfacts_of_holds σ hσ
  have hg := SampleAux.packet_geometry hf hρ hω hω₁ hν hN1 hℓ hM hM₀
  have ha := SampleAux.packet_analysis (S' := S) (U' := U') hf hρ hν hN1 hloss hχ₀ hχ₀χ
    hcoeff₀ hcoeff₁
  have hcap := SampleAux.packet_capping hf hρ hNpos hℓ hw
  have hmass := SampleAux.packet_mass hf hρ hν hNpos hcover
  set p := SampleAux.packet σ ρ ν with hp
  let keep := Finset.univ.filter (fun i => ENNReal.ofReal (N ^ (-χ)) ≤ p.law i univ)
  let e : Fin keep.card ↪ Fin p.C :=
    ⟨keep.orderEmbOfFin rfl, (keep.orderEmbOfFin rfl).injective⟩
  apply SampleAux.uncapped_of_packet (p.restrictTo keep) (hg.reindex e)
    (SampleAux.provisional_reindex ha e) _ _ (SampleAux.capping_reindex hcap e)
  · intro a
    exact (Finset.mem_filter.mp (keep.orderEmbOfFin_mem rfl a)).2
  · rw [PacketData.mass_restrictTo]
    exact heavy_packet_mass_lower (p.weight ω ν) (fun a => p.law a univ)
      ENNReal.ofReal_ne_top hg.budget_sum hmass

end
end Refined
end Submission.Obl.k4_balanced_native_packet_transport
