import Submission.Obl.k4_horizontal_wide_interval_return.ScalarCell
import Submission.Obl.k4_horizontal_wide_interval_return.CellGraph
import Submission.Obl.k4_horizontal_wide_interval_return.GraphReturn
import Submission.Obl.k4_fixed_budget_quadratic_recovery.QuadraticPolynomial
import Submission.Obl.k4_fixed_budget_quadratic_recovery.ScalarBudget

namespace Submission.Obl.k4_horizontal_wide_interval_return

open MeasureTheory Set MvPolynomial
open Submission.Lib.K4ChartLifting
open Submission.Obl.k4_fixed_budget_quadratic_recovery

noncomputable section

/-- Scalar hypotheses in the coordinates of one true parent block. The mass
normalization uses the full original assignment `ν A`. -/
structure CellInput {α : Type} [MeasurableSpace α]
    (N η d v m S U : ℝ) (ν : Measure α) (lam : Measure (α × ℝ))
    (b : α → Fin 6 → ℝ) (A Bs : Set α) (F : CellFrame) : Prop where
  measurable_coefficients : Measurable b
  measurable_assignment : MeasurableSet A
  measurable_source : MeasurableSet Bs
  source_subset : Bs ⊆ A
  probability_prior : IsProbabilityMeasure ν
  assignment_ne_zero : ν A ≠ 0
  time_pos : 0 < F.q
  transverse_pos : 0 < F.g
  thickness_pos : 0 < F.a
  domination : lam ≤ ENNReal.ofReal (N ^ η) • ν.prod volume
  support : ∀ᵐ p ∂lam, p.1 ∈ Bs ∧ p.2 ∈ Icc F.t₀ (F.t₀ + F.q)
  mass : ENNReal.ofReal (N ^ (-η)) * (ENNReal.ofReal F.q * ν A) ≤ lam univ
  coefficients : ∀ l ∈ Bs, ∀ i, |F.lineCoeffs (b l) i| ≤ N ^ η
  cap : ∀ (r : ℝ) (q₀ : Fin 2 → ℤ) (j : ℤ), 0 ≤ r → r ≤ v →
    lam {p | F.cellCode (N ^ (-m)) (b p.1) p.2 = q₀ ∧
      ⌊F.cellSig (b p.1) p.2 / N ^ (-r)⌋ = j} ≤
      ENNReal.ofReal (N ^ η * (N ^ (-m)) ^ 2 * (N ^ (-r)) ^ d) *
        (ENNReal.ofReal F.q * ν A)
  finite_support : ∃ Fs : Finset ((Fin 2 → ℤ) × ℤ),
    (Fs.card : ℝ) * (N ^ (-m)) ^ 2 ≤ N ^ η * (N ^ (-v)) ^ (-d) ∧
    ∀ᵐ p ∂lam, (F.cellCode (N ^ (-m)) (b p.1) p.2,
      ⌊F.cellSig (b p.1) p.2 / N ^ (-v)⌋) ∈ Fs
  angular_cap : ∀ (r : ℝ) (q₀ : Fin 2 → ℤ) (j k : ℤ), 0 < r → r ≤ U →
    lam {p | F.cellCode (N ^ (-m)) (b p.1) p.2 = q₀ ∧
      ⌊F.cellSig (b p.1) p.2 / N ^ (-v)⌋ = j ∧
      ⌊F.y₁ (b p.1) / N ^ (-r)⌋ = k} ≤
      ENNReal.ofReal (N ^ η * (N ^ (-m)) ^ 2 * (N ^ (-v)) ^ d * N ^ (-S * r)) *
        (ENNReal.ofReal F.q * ν A)

/-- The adapted scalar norm controls the ordinary coefficient norm. This uses
the coefficient reconstruction already proved in o177. -/
theorem scalarCandidate_coeffL1 {N s m δ : ℝ} (G : ScalarCandidate N s m δ)
    (hN : 1 ≤ N) (hδ : 0 ≤ δ) : coeffL1 G.P ≤ 2160 * (N ^ δ) ^ 5 := by
  obtain ⟨c, hc, hcoeff⟩ := G.exists_coefficients hN hδ
  have hpcoeff : ∀ e, |G.P.coeff e| ≤ 240 * (N ^ δ) ^ 5 := by
    intro e
    rw [polynomial_eq_of_quadratic_values hc]
    have hh := quadraticPolynomial_coeff_bound
      (by positivity : 0 ≤ 40 * (N ^ δ) ^ 5) hcoeff e
    convert hh using 1 <;> ring
  have hnorm := coeffL1_le_of_coeff_le G.P G.degree
    (240 * (N ^ δ) ^ 5) hpcoeff
  norm_num at hnorm
  linarith

/-- The scalar theorem on a normalized true block produces a quadratic graph in
the full original base, with its mass still measured by the original law. -/
theorem graph_of_cell_input (hScalar : Scalar) {d v m S U δ : ℝ}
    (hd : 0 ≤ d) (hd1 : d < 1) (hv : 0 < v) (hvm : v < m)
    (hS : 0 < S) (hU : 0 < U) (hUm : U < m) (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
    ∀ (α : Type) [MeasurableSpace α] (ν : Measure α) (lam : Measure (α × ℝ))
      (b : α → Fin 6 → ℝ) (A Bs : Set α) (F : CellFrame) (H : ℝ),
      CellInput N η d v m S U ν lam b A Bs F →
      1 ≤ H → F.q ≤ 1 → F.g ≤ 1 → F.a ≤ 1 → |F.t₀| ≤ H →
      (∀ i, |F.c i| ≤ H) → (∀ i, |F.L i| ≤ H) → (∀ i, |F.C i| ≤ H) →
      2160 * (N ^ δ) ^ 5 ≤ H →
      ∃ G : MvPolynomial (Fin 3) ℝ, G.totalDegree ≤ 2 ∧
        coeffL1 G ≤ 53 * H ^ 3 * ((F.q * F.g)⁻¹) ^ 2 ∧
        ENNReal.ofReal (N ^ (-d * v - 2 * δ)) * (ENNReal.ofReal F.q * ν A) ≤
          lam {p | p.1 ∈ Bs ∧ p.2 ∈ Icc F.t₀ (F.t₀ + F.q) ∧
            ∀ t ∈ Icc F.t₀ (F.t₀ + F.q),
              |lineX (b p.1) t - eval ![t, lineZ (b p.1) t, lineY (b p.1) t] G| ≤
                F.a * (N ^ δ * N ^ (-v))} := by
  obtain ⟨η, hη, N₀, hN₀, hmain⟩ :=
    scalar_cell_candidate hScalar hd hd1 hv hvm hS hU hUm hδ
  refine ⟨η, hη, N₀, hN₀, ?_⟩
  intro N hN α _ ν lam b A Bs F H hinput hH hq1 hg1 ha1 ht₀ hc hL hC hsize
  have hNpos : 0 < N := by linarith
  obtain ⟨G, hG⟩ := hmain N hN α ν lam b A Bs F hinput.measurable_coefficients
    hinput.measurable_assignment hinput.measurable_source hinput.source_subset
    hinput.probability_prior hinput.assignment_ne_zero hinput.time_pos
    hinput.transverse_pos hinput.thickness_pos hinput.domination hinput.support
    hinput.mass hinput.coefficients hinput.cap hinput.finite_support hinput.angular_cap
  refine ⟨F.cellGraph G.P, F.totalDegree_cellGraph G.P G.degree,
    F.coeffL1_cellGraph hH hinput.time_pos hq1 hinput.transverse_pos hg1
      hinput.thickness_pos ha1 ht₀ hc hL hC G.P G.degree
      ((scalarCandidate_coeffL1 G (by linarith) hδ.le).trans hsize), ?_⟩
  have hfloor : scalarCandidateFloor N 1 d v δ = N ^ (-d * v - 2 * δ) := by
    rw [scalarCandidateFloor_eq hNpos]
    congr 1
    ring
  rw [hfloor] at hG
  refine hG.trans (measure_mono ?_)
  intro p hp
  refine ⟨hp.1, hp.2.1, ?_⟩
  intro t ht
  have hz : F.zt t ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1) hinput.time_pos.le
    · exact (div_le_one hinput.time_pos).mpr (by linarith [ht.2])
  have hfit := hp.2.2 (F.zt t) hz
  rw [CellFrame.t₀_add_zt hinput.time_pos.ne'] at hfit
  rw [CellFrame.sub_eval_cellGraph hinput.thickness_pos.ne', abs_mul,
    abs_of_pos hinput.thickness_pos]
  exact mul_le_mul_of_nonneg_left hfit hinput.thickness_pos.le

/-- The polynomial alternative in the original-label candidate assertion. -/
def NativeCandidate {α : Type} [MeasurableSpace α]
    (N d s v ε R : ℝ) (T : ℕ) (ν : Measure α) (ρ : Measure (α × ℝ))
    (b : α → Fin 6 → ℝ) (A B : Set α) (I : Set ℝ)
    (F₀ P₀ : MvPolynomial (Fin 4) ℝ) : Prop :=
  ∃ Q : MvPolynomial (Fin 4) ℝ, Q.totalDegree ≤ 2 ∧
      (∀ e, |Q.coeff e| ≤ N ^ R *
        ((1 + ∑ e ∈ F₀.support, |F₀.coeff e|) +
          ∑ e ∈ P₀.support, |P₀.coeff e|) ^ R) ∧
      ENNReal.ofReal (N ^ (-d * v - ε) / (2 : ℝ) ^ T) * ν A ≤
        ρ {p | p.1 ∈ B ∧ p.2 ∈ I ∧
          (∀ t ∈ I,
            |eval ![t, lineZ (b p.1) t, lineY (b p.1) t, lineX (b p.1) t] Q| ≤
                N ^ ε * N ^ (-s - v) ∧
            |eval ![t, lineZ (b p.1) t, lineY (b p.1) t, lineX (b p.1) t]
              (pderiv (3 : Fin 4) Q)| ≤ N ^ ε ∧
            |eval ![t, lineZ (b p.1) t, lineY (b p.1) t, lineX (b p.1) t]
              (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) Q))| ≤
                N ^ ε / N ^ (-s - v)) ∧
          N ^ (-ε) ≤
            |eval ![p.2, lineZ (b p.1) p.2, lineY (b p.1) p.2, lineX (b p.1) p.2]
              (pderiv (3 : Fin 4) Q)|}

/-- Return a cell graph to the original polynomial candidate. The source law
may be restricted, while its reference weight remains the full `ν A`. -/
theorem candidate_of_cell_graph {α : Type} [MeasurableSpace α]
    (ν : Measure α) (ρ lam : Measure (α × ℝ)) (b : α → Fin 6 → ℝ)
    (A B Bs : Set α) (F : CellFrame) (N d s v ε δ R₀ : ℝ) (T : ℕ)
    (hN : 2 ≤ N) (hε : 0 < ε) (hδε : δ ≤ ε) (hR₀ : 0 ≤ R₀)
    (hlam : lam ≤ ρ) (hBs : Bs ⊆ B) (ha : F.a = N ^ (-s))
    (hq : F.q = ((2 : ℝ) ^ T)⁻¹)
    (F₀ P₀ : MvPolynomial (Fin 4) ℝ) (G : MvPolynomial (Fin 3) ℝ)
    (hdeg : G.totalDegree ≤ 2) (hnorm : coeffL1 G ≤ N ^ R₀)
    (hmass : ENNReal.ofReal (N ^ (-d * v - ε)) * (ENNReal.ofReal F.q * ν A) ≤
      lam {p | p.1 ∈ Bs ∧ p.2 ∈ Icc F.t₀ (F.t₀ + F.q) ∧
        ∀ t ∈ Icc F.t₀ (F.t₀ + F.q),
          |lineX (b p.1) t - eval ![t, lineZ (b p.1) t, lineY (b p.1) t] G| ≤
            F.a * (N ^ δ * N ^ (-v))}) :
    NativeCandidate N d s v ε (R₀ + 2) T ν ρ b A B
      (Icc F.t₀ (F.t₀ + F.q)) F₀ P₀ := by
  have hN1 : 1 ≤ N := by linarith
  have hNpos : 0 < N := by linarith
  let E : Set (α × ℝ) := {p | p.1 ∈ Bs ∧ p.2 ∈ Icc F.t₀ (F.t₀ + F.q) ∧
    ∀ t ∈ Icc F.t₀ (F.t₀ + F.q),
      |lineX (b p.1) t - eval ![t, lineZ (b p.1) t, lineY (b p.1) t] G| ≤
        F.a * (N ^ δ * N ^ (-v))}
  have hmass' : ENNReal.ofReal (N ^ (-d * v - ε) / (2 : ℝ) ^ T) * ν A ≤ ρ E := by
    have heq : ENNReal.ofReal (N ^ (-d * v - ε) / (2 : ℝ) ^ T) * ν A =
        ENNReal.ofReal (N ^ (-d * v - ε)) * (ENNReal.ofReal F.q * ν A) := by
      rw [hq, div_eq_mul_inv, ENNReal.ofReal_mul
        (Real.rpow_nonneg hNpos.le _), mul_assoc]
    rw [heq]
    exact hmass.trans (hlam E)
  apply native_candidate_of_graph_mass
    (fun l t => ![t, lineZ (b l) t, lineY (b l) t, lineX (b l) t])
    ν ρ A B (Icc F.t₀ (F.t₀ + F.q)) E N d s v ε R₀ T hN hε hR₀
    F₀ P₀ G hdeg hnorm _ hmass'
  intro p hp
  refine ⟨hBs hp.1, hp.2.1, ?_⟩
  intro t ht
  have hbase :
      (fun i : Fin 3 =>
        (![t, lineZ (b p.1) t, lineY (b p.1) t, lineX (b p.1) t] : Fin 4 → ℝ)
          i.castSucc) = ![t, lineZ (b p.1) t, lineY (b p.1) t] := by
    funext i
    fin_cases i <;> rfl
  simp only [Matrix.cons_val_three, hbase]
  refine (hp.2.2 t ht).trans ?_
  rw [ha]
  calc N ^ (-s) * (N ^ δ * N ^ (-v))
      ≤ N ^ (-s) * (N ^ ε * N ^ (-v)) := by
        gcongr
    _ = N ^ ε * N ^ (-s - v) := by
      rw [sub_eq_add_neg, Real.rpow_add hNpos]
      ring

/-- A single normalized scalar input suffices for the exact polynomial return.
The chosen scalar accuracy is at most one, so its coefficient budget can be
fixed independently of the requested final accuracy. -/
theorem native_candidate_of_cell_input (hScalar : Scalar) {d v m S U ε : ℝ}
    (hd : 0 ≤ d) (hd1 : d < 1) (hv : 0 < v) (hvm : v < m)
    (hS : 0 < S) (hU : 0 < U) (hUm : U < m) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
    ∀ (α : Type) [MeasurableSpace α] (ν : Measure α) (ρ lam : Measure (α × ℝ))
      (b : α → Fin 6 → ℝ) (A B Bs : Set α) (F : CellFrame) (H s R₀ : ℝ) (T : ℕ)
      (F₀ P₀ : MvPolynomial (Fin 4) ℝ),
      CellInput N η d v m S U ν lam b A Bs F → lam ≤ ρ → Bs ⊆ B →
      1 ≤ H → F.q ≤ 1 → F.g ≤ 1 → F.a ≤ 1 → |F.t₀| ≤ H →
      (∀ i, |F.c i| ≤ H) → (∀ i, |F.L i| ≤ H) → (∀ i, |F.C i| ≤ H) →
      2160 * N ^ (5 : ℕ) ≤ H → 0 ≤ R₀ →
      53 * H ^ 3 * ((F.q * F.g)⁻¹) ^ 2 ≤ N ^ R₀ →
      F.a = N ^ (-s) → F.q = ((2 : ℝ) ^ T)⁻¹ →
      NativeCandidate N d s v ε (R₀ + 2) T ν ρ b A B
        (Icc F.t₀ (F.t₀ + F.q)) F₀ P₀ := by
  let δ : ℝ := min (ε / 2) 1
  have hδ : 0 < δ := lt_min (by positivity) zero_lt_one
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδε : δ ≤ ε := (min_le_left _ _).trans (by linarith)
  have h2δε : 2 * δ ≤ ε := by have := min_le_left (ε / 2) 1; dsimp [δ]; linarith
  obtain ⟨η, hη, N₀, hN₀, hmain⟩ :=
    graph_of_cell_input hScalar hd hd1 hv hvm hS hU hUm hδ
  refine ⟨η, hη, N₀, hN₀, ?_⟩
  intro N hN α _ ν ρ lam b A B Bs F H s R₀ T F₀ P₀ hinput hlam hBs hH
    hq1 hg1 ha1 ht₀ hc hL hC hsize hR₀ hbudget ha hq
  have hN1 : 1 ≤ N := by linarith
  have hNpos : 0 < N := by linarith
  have hsize' : 2160 * (N ^ δ) ^ 5 ≤ H := by
    apply le_trans _ hsize
    gcongr
    exact (Real.rpow_le_rpow_of_exponent_le hN1 hδ1).trans_eq (Real.rpow_one N)
  obtain ⟨G, hdeg, hnorm, hmass⟩ := hmain N hN α ν lam b A Bs F H hinput
    hH hq1 hg1 ha1 ht₀ hc hL hC hsize'
  apply candidate_of_cell_graph ν ρ lam b A B Bs F N d s v ε δ R₀ T
    (hN₀.trans hN) hε hδε hR₀ hlam hBs ha hq F₀ P₀ G hdeg
    (hnorm.trans hbudget)
  exact (mul_le_mul'
    (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hN1
      (show -d * v - ε ≤ -d * v - 2 * δ by linarith))) le_rfl).trans hmass

end

end Submission.Obl.k4_horizontal_wide_interval_return
