import Submission.Obl.k4_fixed_budget_quadratic_recovery.QuadraticPolynomial
import Submission.Obl.k4_horizontal_supercritical_three_projections.Conditioning

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open MeasureTheory Set
open Submission.Obl.k4_fixed_budget_quadratic_recovery

/-- The entire finite family is kept; selecting a single heavy packet would
lose the dense ensemble required for the three-layer construction. -/
structure ScalarPackets {α : Type} [MeasurableSpace α]
    (N d s m c ε : ℝ) (μ : Measure (α × ℝ)) (b : α → Fin 5 → ℝ) where
  n : ℕ
  A : Fin n → Set α
  candidate : Fin n → ScalarCandidate N s m ε
  measurable : ∀ i, MeasurableSet (A i)
  disjoint : ∀ i j, i ≠ j → Disjoint (A i) (A j)
  fit : ∀ i l, l ∈ A i → ∀ t ∈ Icc (0 : ℝ) 1,
    |scalarX (b l) t - MvPolynomial.eval ![t, scalarY (b l) t] (candidate i).P| ≤
      N ^ ε * N ^ (-s)
  floor : ∀ i, ENNReal.ofReal (scalarCandidateFloor N c d s ε) ≤
    μ (A i ×ˢ Icc (0 : ℝ) 1)
  mass : ENNReal.ofReal (N ^ (-ε)) ≤ μ {p | ∃ i, p.1 ∈ A i}

/-- Trim the output assignments to their original chart, restoring the
unpadded scalar coefficients there. Its normalized law already has this support. -/
def ScalarPackets.trim {α : Type} [MeasurableSpace α]
    {N d s m c ε : ℝ} {μ : Measure (α × ℝ)} {b b' : α → Fin 5 → ℝ}
    (F : ScalarPackets N d s m c ε μ b) {G : Set α} (hG : MeasurableSet G)
    (hsupport : ∀ᵐ p ∂μ, p.1 ∈ G) (hb : ∀ l ∈ G, b l = b' l) :
    ScalarPackets N d s m c ε μ b' := by
  refine {
    n := F.n
    A := fun i => F.A i ∩ G
    candidate := F.candidate
    measurable := fun i => (F.measurable i).inter hG
    disjoint := fun i j hij => (F.disjoint i j hij).mono inter_subset_left inter_subset_left
    fit := ?_
    floor := ?_
    mass := ?_ }
  · intro i l hl t ht
    rw [← hb l hl.2]
    exact F.fit i l hl.1 t ht
  · intro i
    apply (F.floor i).trans_eq
    apply measure_congr
    filter_upwards [hsupport] with p hp
    apply propext
    change (p.1 ∈ F.A i ∧ p.2 ∈ Icc (0 : ℝ) 1) ↔
      ((p.1 ∈ F.A i ∧ p.1 ∈ G) ∧ p.2 ∈ Icc (0 : ℝ) 1)
    exact ⟨fun h => ⟨⟨h.1, hp⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
  · apply F.mass.trans_eq
    apply measure_congr
    filter_upwards [hsupport] with p hp
    apply propext
    exact ⟨fun ⟨i, hi⟩ => ⟨i, hi, hp⟩, fun ⟨i, hi⟩ => ⟨i, hi.1⟩⟩

/-- Restore every packet floor and the entire scalar success event to the
original chart measure, before any subsequent restriction. -/
theorem ScalarPackets.restore {α : Type} [MeasurableSpace α]
    {N d s m W ε : ℝ} (ν : Measure α) [IsFiniteMeasure ν]
    (ζ : Measure (α × ℝ)) (G : Set α) (hG₀ : ν G ≠ 0)
    (b : α → Fin 5 → ℝ)
    (F : ScalarPackets N d s m (W / (ν G).toReal) ε (chartLaw ν ζ G) b) :
    (∀ i, ENNReal.ofReal (W * (N ^ (-s)) ^ d * N ^ (-ε) / N ^ ε) ≤
      ζ (F.A i ×ˢ Icc (0 : ℝ) 1)) ∧
    ENNReal.ofReal ((ν G).toReal * N ^ (-ε)) ≤ ζ {p | ∃ i, p.1 ∈ F.A i} := by
  have hν₀ : 0 < (ν G).toReal := ENNReal.toReal_pos hG₀ (measure_ne_top ν G)
  refine ⟨?_, chartLaw_restore_floor ν ζ G hG₀ _ F.mass⟩
  intro i
  have h := chartLaw_restore_floor ν ζ G hG₀ _ (F.floor i)
  convert h using 1
  congr 1
  unfold scalarCandidateFloor
  field_simp

/-- Apply the scalar premise uniformly in the input prior and current law,
retaining full-time fits and original whole-assignment floors for every packet. -/
theorem scalar_packets_of_mesh (hmesh : ScalarMeshProjection)
    {d s m C S U ε : ℝ} (hd : 0 ≤ d) (hd₁ : d < 1)
    (hs : 0 < s) (hsm : s < m) (hC : 0 < C) (hS : 0 < S)
    (hU : 0 < U) (hUm : U < m) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α]
        (ν : Measure α) (μ : Measure (α × ℝ)) (b : α → Fin 5 → ℝ) (c : ℝ),
        ScalarAdmissible N η d s m C S U c ν b μ →
        ENNReal.ofReal (N ^ (-η)) ≤ μ univ →
        Nonempty (ScalarPackets N d s m c ε μ b) := by
  obtain ⟨η, hη, N₀, hN₀, H⟩ := hmesh d s m C S U ε hd hd₁ hs hsm hC hS hU hUm hε
  refine ⟨η, hη, N₀, hN₀, ?_⟩
  intro N hN α _ ν μ b c hadm hmass
  obtain ⟨hb, hν, hdom, hsupp, hcoeff, hc₁, hc₂, hcap, hcover, hang⟩ := hadm
  obtain ⟨n, β, A, u, v, P, hβ, hβup, hβlo, hA, hdisj, hpackets, hcovered⟩ :=
    H N hN α ν μ b c true hb hν hdom hsupp hmass hcoeff hc₁ hc₂ hcap hcover
      (fun _ => hang)
  let F : Fin n → ScalarCandidate N s m ε := fun i =>
    ⟨P i, β, u i, v i, hβlo rfl, hβup, (hpackets i).1,
      (hpackets i).2.1, (hpackets i).2.2.1⟩
  refine ⟨{
    n := n
    A := A
    candidate := F
    measurable := hA
    disjoint := hdisj
    fit := fun i l hl t ht => ((hpackets i).2.2.2.1 l hl t ht).2
    floor := ?_
    mass := hcovered }⟩
  intro i
  apply (ENNReal.ofReal_le_ofReal ?_).trans ((hpackets i).2.2.2.2)
  unfold scalarCandidateFloor
  apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (by linarith : 0 ≤ N) _)
  apply mul_le_mul_of_nonneg_left (hβlo rfl)
  exact mul_nonneg ((Real.rpow_nonneg (by linarith : 0 ≤ N) _).trans hc₁)
    (Real.rpow_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ N) _) _)

end Submission.Obl.k4_horizontal_supercritical_three_projections
