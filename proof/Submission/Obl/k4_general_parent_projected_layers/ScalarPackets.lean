import Submission.Obl.k4_fixed_budget_quadratic_recovery.ScalarCandidates
import Submission.Obl.k4_horizontal_supercritical_three_projections.Conditioning

namespace Submission.Obl.k4_general_parent_projected_layers

open MeasureTheory Set
open Submission.Obl.k4_fixed_budget_quadratic_recovery (ScalarMeshProjection scalarY scalarX scalarCell)
open Submission.Obl.k4_horizontal_supercritical_three_projections (chartLaw chartLaw_restore_floor)

noncomputable section

/-- Scalar input without the angular hypothesis, as required by ordinary layers. -/
structure ScalarInput {α : Type} [MeasurableSpace α]
    (N eta d s M C c : ℝ) (ν : Measure α) (μ : Measure (α × ℝ))
    (b : α → Fin 5 → ℝ) : Prop where
  measurable : Measurable b
  prior : IsProbabilityMeasure ν
  domination : μ ≤ ENNReal.ofReal (N ^ eta) • (ν.prod volume)
  time : μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0
  coeff : ∀ l i, |b l i| ≤ N ^ eta
  c_lower : N ^ (-C) ≤ c
  c_upper : c ≤ N ^ C
  cap : ∀ (r : ℝ) (q : Fin 2 → ℤ) (j : ℤ), 0 ≤ r → r ≤ s →
    μ {p | scalarCell (b p.1) p.2 (N ^ (-M)) = q ∧
      ⌊scalarX (b p.1) p.2 / N ^ (-r)⌋ = j} ≤
        ENNReal.ofReal (N ^ eta * (N ^ (-M)) ^ 2 * c * (N ^ (-r)) ^ d)
  support : ∃ F : Finset ((Fin 2 → ℤ) × ℤ),
    (F.card : ℝ) * (N ^ (-M)) ^ 2 ≤ N ^ eta * c⁻¹ * (N ^ (-s)) ^ (-d) ∧
    ∀ᵐ p ∂μ, (scalarCell (b p.1) p.2 (N ^ (-M)), ⌊scalarX (b p.1) p.2 / N ^ (-s)⌋) ∈ F

/-- Retain the scalar theorem's common width, centers, and moving norm. -/
structure ScalarPackets {α : Type} [MeasurableSpace α]
    (N d s M c eps : ℝ) (μ : Measure (α × ℝ)) (b : α → Fin 5 → ℝ) where
  n : ℕ
  beta : ℝ
  A : Fin n → Set α
  u : Fin n → ℝ
  v : Fin n → ℝ
  P : Fin n → MvPolynomial (Fin 2) ℝ
  beta_lower : N ^ (-M) / N ^ eps ≤ beta
  beta_upper : beta ≤ N ^ eps
  measurable : ∀ i, MeasurableSet (A i)
  disjoint : ∀ i j, i ≠ j → Disjoint (A i) (A j)
  centers : ∀ i, |u i| + |v i| ≤ N ^ eps
  degree : ∀ i, (P i).totalDegree ≤ 2
  norm : ∀ i t, t ∈ Icc (0 : ℝ) 1 → ∀ w ∈ Icc (-1 : ℝ) 1,
    |MvPolynomial.eval ![t, u i + t * v i + beta * w] (P i)| ≤ N ^ eps
  fit : ∀ i l, l ∈ A i → ∀ t ∈ Icc (0 : ℝ) 1,
    |scalarY (b l) t - u i - t * v i| ≤ N ^ eps * beta ∧
    |scalarX (b l) t - MvPolynomial.eval ![t, scalarY (b l) t] (P i)| ≤ N ^ eps * N ^ (-s)
  floor : ∀ i, ENNReal.ofReal (c * (N ^ (-s)) ^ d * beta / N ^ eps) ≤
    μ (A i ×ˢ Icc (0 : ℝ) 1)
  mass : ENNReal.ofReal (N ^ (-eps)) ≤ μ {p | ∃ i, p.1 ∈ A i}

theorem scalar_packets_of_mesh (hScalar : ScalarMeshProjection)
    {d s M C eps : ℝ} (hd : 0 ≤ d) (hd1 : d < 1) (hs : 0 < s)
    (hsM : s < M) (hC : 0 < C) (heps : 0 < eps) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α]
      (ν : Measure α) (μ : Measure (α × ℝ)) (b : α → Fin 5 → ℝ) (c : ℝ),
      ScalarInput N eta d s M C c ν μ b → ENNReal.ofReal (N ^ (-eta)) ≤ μ univ →
        Nonempty (ScalarPackets N d s M c eps μ b) := by
  obtain ⟨eta, heta, N₀, hN₀, H⟩ := hScalar d s M C 1 (M / 2) eps hd hd1 hs hsM hC
    (by norm_num) (by linarith) (by linarith) heps
  refine ⟨eta, heta, N₀, hN₀, ?_⟩
  intro N hN α _ ν μ b c hinput hmass
  obtain ⟨n, beta, A, u, v, P, hlo, hup, _, hA, hdisj, hfit, hcovered⟩ :=
    H N hN α ν μ b c false hinput.measurable hinput.prior hinput.domination hinput.time hmass
      hinput.coeff hinput.c_lower hinput.c_upper hinput.cap hinput.support (by simp)
  exact ⟨{
    n := n, beta := beta, A := A, u := u, v := v, P := P
    beta_lower := hlo, beta_upper := hup, measurable := hA, disjoint := hdisj
    centers := fun i => (hfit i).1
    degree := fun i => (hfit i).2.1
    norm := fun i => (hfit i).2.2.1
    fit := fun i => (hfit i).2.2.2.1
    floor := fun i => (hfit i).2.2.2.2
    mass := hcovered }⟩

namespace ScalarPackets

variable {α : Type} [MeasurableSpace α]

/-- The scalar lower mesh bound makes every retained physical width positive. -/
theorem beta_pos {N d s M c eps : ℝ} {μ : Measure (α × ℝ)} {b : α → Fin 5 → ℝ}
    (F : ScalarPackets N d s M c eps μ b) (hN : 0 < N) : 0 < F.beta :=
  lt_of_lt_of_le (by positivity) F.beta_lower

/-- Restrict assignments to the unchanged original group, replacing padded
coefficients by the original ones only where they agree. -/
def trim {N d s M c eps : ℝ} {μ : Measure (α × ℝ)} {b b' : α → Fin 5 → ℝ}
    (F : ScalarPackets N d s M c eps μ b) {G : Set α} (hG : MeasurableSet G)
    (hsupport : ∀ᵐ p ∂μ, p.1 ∈ G) (hb : ∀ l ∈ G, b l = b' l) :
    ScalarPackets N d s M c eps μ b' where
  n := F.n
  beta := F.beta
  A := fun i => F.A i ∩ G
  u := F.u
  v := F.v
  P := F.P
  beta_lower := F.beta_lower
  beta_upper := F.beta_upper
  measurable := fun i => (F.measurable i).inter hG
  disjoint := fun i j hij => (F.disjoint i j hij).mono inter_subset_left inter_subset_left
  centers := F.centers
  degree := F.degree
  norm := F.norm
  fit := by
    intro i l hl t ht
    rw [← hb l hl.2]
    exact F.fit i l hl.1 t ht
  floor := by
    intro i
    apply (F.floor i).trans_eq
    apply measure_congr
    filter_upwards [hsupport] with p hp
    exact propext (by change (p.1 ∈ F.A i ∧ p.2 ∈ Icc (0 : ℝ) 1) ↔
      ((p.1 ∈ F.A i ∧ p.1 ∈ G) ∧ p.2 ∈ Icc (0 : ℝ) 1); tauto)
  mass := by
    apply F.mass.trans_eq
    apply measure_congr
    filter_upwards [hsupport] with p hp
    exact propext ⟨fun ⟨i, hi⟩ => ⟨i, hi, hp⟩, fun ⟨i, hi⟩ => ⟨i, hi.1⟩⟩

/-- Restore every full-width floor before making further restrictions. -/
theorem restore {N d s M W eps : ℝ} (ν : Measure α) [IsFiniteMeasure ν]
    (ζ : Measure (α × ℝ)) (G : Set α) (hG₀ : ν G ≠ 0) (b : α → Fin 5 → ℝ)
    (F : ScalarPackets N d s M (W / (ν G).toReal) eps (chartLaw ν ζ G) b) :
    (∀ i, ENNReal.ofReal (W * (N ^ (-s)) ^ d * F.beta / N ^ eps) ≤
      ζ (F.A i ×ˢ Icc (0 : ℝ) 1)) ∧
    ENNReal.ofReal ((ν G).toReal * N ^ (-eps)) ≤ ζ {p | ∃ i, p.1 ∈ F.A i} := by
  have hmass := chartLaw_restore_floor ν ζ G hG₀ _ F.mass
  refine ⟨?_, hmass⟩
  intro i
  have H := chartLaw_restore_floor ν ζ G hG₀ _ (F.floor i)
  have hGreal : (ν G).toReal ≠ 0 :=
    (ENNReal.toReal_pos hG₀ (measure_ne_top ν G)).ne'
  convert H using 1
  congr 1
  field_simp

end ScalarPackets

end

end Submission.Obl.k4_general_parent_projected_layers
