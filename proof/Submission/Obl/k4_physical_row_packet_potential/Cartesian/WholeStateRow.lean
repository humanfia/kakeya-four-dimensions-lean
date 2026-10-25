-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/WholeStateRow.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/WholeStateRow.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.OriginalPolynomialRow
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.RoundGrid
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.FiberGeometry
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.FrameSubst
import Submission.Lib.K4ScalarCoreAssembly.PolynomialWitnessTransfer
import Submission.Lib.K4ContactTransfer.ContactCorrection

/-!
# Cartesian interpolation of the physical field on whole states

Paper tex-06 l. 940-1035 (`a05:interpolated-field`), for the old packet in its
normalized coordinates.  Fix a spanning velocity triple `J` with frame
`A = (1, J i)` and inverse `Ainv`.  Every state `D` of a family `Ωst` carries,
for each axis, a qualified witness through `D` of velocity within `η` of
`J axis`; the reference states have short field lists on every base box of
radius `30 K² ξ`; the family has a base density ceiling.  Then one polynomial
row `T` of degree at most `3 M`, in the normalized base coordinates `z`, fits
the state row `Gs` up to `C K^e p` on a union `S` of WHOLE states of the family,
which retains a fraction `(C K^e)⁻¹` of the original mass.

The grid is the symmetric `ξ`-grid in the coordinates `u = Ainv z`; the
combinatorics is x0358's `original_polynomial_row` (o106).  States are kept
whole, so conditional laws inside a state are unchanged on `S`.
-/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open MeasureTheory Set MvPolynomial Matrix
open Submission.Lib.K4CommonLocalChoice (cell)
open Submission.Lib.K4ChartLifting (coeffL1 coeffL1_nonneg abs_coeff_le_coeffL1
  coeffL1_le_of_coeff_le)

noncomputable section

/-- The real key of a grid fiber. -/
theorem realFiberKey_gridPoint {S : Finset ℝ} (axis : Fin 3) (g : S × S × S) :
    realFiberKey axis (gridPoint g) =
      (((gridFiberKey axis g).1 : ℝ), ((gridFiberKey axis g).2 : ℝ)) := by
  fin_cases axis <;> rfl

theorem abs_gridPoint_le {ξ : ℝ} (hξ : 0 ≤ ξ) {R : ℕ} (g : symGrid ξ R × symGrid ξ R × symGrid ξ R)
    (i : Fin 3) : |gridPoint g i| ≤ ξ * R := by
  fin_cases i
  · exact abs_le_of_mem_symGrid hξ g.1.2
  · exact abs_le_of_mem_symGrid hξ g.2.1.2
  · exact abs_le_of_mem_symGrid hξ g.2.2.2

/-- Rounding a vector to the grid. -/
def roundGrid3 (ξ : ℝ) (R : ℕ) (u : Fin 3 → ℝ) : symGrid ξ R × symGrid ξ R × symGrid ξ R :=
  (roundGrid ξ R (u 0), roundGrid ξ R (u 1), roundGrid ξ R (u 2))

theorem abs_sub_gridPoint_roundGrid3_le {ξ : ℝ} (hξ : 0 < ξ) {R : ℕ} {u : Fin 3 → ℝ}
    (hu : ∀ i, |u i| ≤ ξ * R) (i : Fin 3) :
    |u i - gridPoint (roundGrid3 ξ R u) i| ≤ ξ / 2 := by
  fin_cases i
  · exact abs_sub_roundGrid_le hξ (hu 0)
  · exact abs_sub_roundGrid_le hξ (hu 1)
  · exact abs_sub_roundGrid_le hξ (hu 2)

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open MeasureTheory Set MvPolynomial Matrix
open Submission.Lib.K4CommonLocalChoice (cell)
open Submission.Lib.K4ChartLifting (coeffL1 coeffL1_nonneg abs_coeff_le_coeffL1
  coeffL1_le_of_coeff_le)

noncomputable section

/-- The kernel application, with all its numerical parameters explicit.  The
caller supplies the budget and the gap; this lemma only transports the data. -/
theorem whole_state_row_core (M : ℕ) {Bsel Ck : ℝ}
    (hrow : ∀ {X : Type} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
      (S : Finset ℝ) [Nonempty S] (code : X → S × S × S), Measurable code →
      ∀ (G : X → Fin 3 → ℝ), Measurable G →
      ∀ (P : Fin 3 → X → Fin 3 → Polynomial ℝ),
      (∀ axis, Measurable (fun x => polynomialFitCoefficients M (P axis x))) →
      ∀ (Ω : Set X), MeasurableSet Ω →
      ∀ (p K ξ ε a U δ r : ℝ), 0 < p → 1 ≤ K → 0 < ξ → 0 ≤ ε → 0 < a → 0 < U → 0 ≤ δ →
      0 < r →
      (∀ axis x, x ∈ Ω → ∀ j, (P axis x j).natDegree ≤ M) →
      ∀ E : Fin 3 → X → Set ℝ,
      (∀ axis x, x ∈ Ω → MeasurableSet (E axis x)) →
      (∀ axis x, x ∈ Ω → E axis x ⊆ Icc (0 : ℝ) 1) →
      (∀ axis x, x ∈ Ω → ENNReal.ofReal (1 / K) ≤ volume (E axis x)) →
      ∀ H : Fin 3 → X → ℝ → Fin 3 → ℝ,
      (∀ axis x, x ∈ Ω → ∀ t ∈ E axis x, ∀ j, |(P axis x j).eval t - H axis x t j| ≤ p) →
      (∀ g, ∃ F : Finset (Fin 3 → ℤ), (F.card : ℝ) ≤ K ∧
        ∀ x ∈ Ω, code x = g → cell p (G x) ∈ F) →
      (∀ axis key t, ∃ F : Finset (Fin 3 → ℤ), (F.card : ℝ) ≤ K ∧
        ∀ x ∈ Ω, gridFiberKey axis (code x) = key → t ∈ E axis x →
          cell p (H axis x t) ∈ F) →
      ∀ (u : X → Fin 3 → ℝ),
      (∀ s ∈ S, |s| ≤ K) →
      (∀ x ∈ Ω, ∀ i, |u x i| ≤ K) →
      (∀ x ∈ Ω, ∀ i, |u x i - gridPoint (code x) i| ≤ ξ) →
      (∀ x ∈ Ω, ∀ j, |G x j| ≤ K) →
      (∀ axis x, x ∈ Ω → ∀ j k, |(P axis x j).coeff k| ≤ K) →
      (∀ axis x, x ∈ Ω → ∀ j, |G x j - (P axis x j).eval (∑ i, u x i)| ≤ ε) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ξ ≤ dist x y) →
      (∀ i : S × S × S, μ.real {x | code x = i} ≤ U) →
      δ * U * (S.card : ℝ) ^ 3 + (S.card : ℝ) ^ 3 * a ≤
        μ.real Ω / (Bsel * K ^ (1 + 3 * (3 + 3 * M * (3 * (M + 1))))) →
      3 * ((M + 1 : ℕ) : ℝ) ^ 2 * ((2 * r / ξ + 1) / (S.card : ℝ)) < δ ^ ((M + 2) ^ 3) →
      ∃ (Q : Fin 3 → MvPolynomial (Fin 3) ℝ) (T' : Set X),
        MeasurableSet T' ∧ T' ⊆ Ω ∧
        (∀ j, (Q j).totalDegree ≤ 3 * M) ∧
        (∀ j d, |(Q j).coeff d| ≤
          Ck * (((M : ℝ) + 1) ^ 3 * (K + p) * ((1 + K) / r) ^ (3 * M))) ∧
        (δ ^ ((M + 2) ^ 3) - 3 * ((M + 1 : ℕ) : ℝ) ^ 2 * ((2 * r / ξ + 1) / (S.card : ℝ))) / 2 *
          a * (S.card : ℝ) ^ 3 ≤ μ.real T' ∧
        ∀ x ∈ T', ∀ j, |G x j - eval (gridPoint (code x)) (Q j)| ≤
          p + 3 * (1 + ((M : ℝ) + 1) * ((2 * K) / r) ^ M) ^ 3 *
            (p + ε + ((M : ℝ) + 1) * p * (3 * K) ^ M +
              3 * ((M : ℝ) + 1) * M * (K + p) * (3 * K) ^ M * ξ))
    {Λ σ : Type} [MeasurableSpace Λ] [MeasurableSpace σ] [Countable σ]
    [MeasurableSingletonClass σ]
    (μ : Measure (Λ × ℝ)) [IsFiniteMeasure μ]
    (E0 Eref : Set (Λ × ℝ)) (hE0 : MeasurableSet E0) (hE0ref : E0 ⊆ Eref)
    (st : Λ × ℝ → σ) (hst : Measurable st)
    (Gs cz : σ → Fin 3 → ℝ) (z : Λ × ℝ → Fin 3 → ℝ) (v : Λ → Fin 2 → ℝ) (t0 h : ℝ)
    (hh : 0 < h) (hz0 : ∀ l t, z (l, t) 0 = (t - t0) / h)
    (hzline : ∀ l t t', z (l, t') = z (l, t) + ((t' - t) / h) • lift (v l))
    (J : Fin 3 → Fin 2 → ℝ) (Ainv : Matrix (Fin 3) (Fin 3) ℝ) (hA : liftMatrix J * Ainv = 1)
    (K ξ ε η p err : ℝ) (hK : 1 ≤ K) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hε : 0 ≤ ε) (hεξ : ε ≤ ξ)
    (hη : 0 ≤ η) (hηξ : η ≤ ξ) (hp : 0 < p) (herr : 0 ≤ err) (herrp : err ≤ p)
    (hJ : ∀ i k, |J i k| ≤ K) (hAinv : ∀ i k, |Ainv i k| ≤ K)
    (hcz : ∀ x ∈ Eref, ∀ i, |z x i - cz (st x) i| ≤ ε)
    (Ωst : Set σ)
    (hczK : ∀ D ∈ Ωst, ∀ i, |cz D i| ≤ K)
    (hGK : ∀ D ∈ Ωst, ∀ j, |Gs D j| ≤ K)
    (hwit : ∀ D ∈ Ωst, ∀ axis : Fin 3, ∃ w ∈ Eref, st w = D ∧ (∀ k, |v w.1 k - J axis k| ≤ η) ∧
      t0 ≤ w.2 ∧ w.2 ≤ t0 + h ∧ QualWitness Eref st Gs t0 h M K err (1 / K) w)
    (hfield : ∀ c : Fin 3 → ℝ, ∃ F : Finset (Fin 3 → ℤ), (F.card : ℝ) ≤ K ∧
      ∀ x ∈ Eref, (∀ i, |z x i - c i| ≤ 30 * K ^ 2 * ξ) → cell p (Gs (st x)) ∈ F)
    (U a δ r : ℝ) (hU : 0 < U) (ha : 0 < a) (hδ : 0 ≤ δ) (hr : 0 < r)
    (hcap : ∀ c : Fin 3 → ℝ,
      μ.real (E0 ∩ st ⁻¹' Ωst ∩ {x | ∀ i, |z x i - c i| ≤ 3 * K * ξ}) ≤ U)
    (hbudget : δ * U * ((symGrid ξ ⌈3 * K ^ 2 / ξ⌉₊).card : ℝ) ^ 3 +
        ((symGrid ξ ⌈3 * K ^ 2 / ξ⌉₊).card : ℝ) ^ 3 * a ≤
      μ.real (E0 ∩ st ⁻¹' Ωst) / (Bsel * (4 * K ^ 2) ^ (1 + 3 * (3 + 3 * M * (3 * (M + 1))))))
    (hgap : 3 * ((M + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * r / ξ + 1) / ((symGrid ξ ⌈3 * K ^ 2 / ξ⌉₊).card : ℝ)) < δ ^ ((M + 2) ^ 3)) :
    ∃ (Q : Fin 3 → MvPolynomial (Fin 3) ℝ) (S : Set (Λ × ℝ)),
      MeasurableSet S ∧ S ⊆ E0 ∩ st ⁻¹' Ωst ∧
      (∀ x ∈ E0, ∀ y ∈ S, st x = st y → x ∈ S) ∧
      (∀ j, (Q j).totalDegree ≤ 3 * M) ∧
      (∀ j d, |(Q j).coeff d| ≤
        Ck * (((M : ℝ) + 1) ^ 3 * (4 * K ^ 2 + p) * ((1 + 4 * K ^ 2) / r) ^ (3 * M))) ∧
      (δ ^ ((M + 2) ^ 3) - 3 * ((M + 1 : ℕ) : ℝ) ^ 2 *
          ((2 * r / ξ + 1) / ((symGrid ξ ⌈3 * K ^ 2 / ξ⌉₊).card : ℝ))) / 2 *
        a * ((symGrid ξ ⌈3 * K ^ 2 / ξ⌉₊).card : ℝ) ^ 3 ≤ μ.real S ∧
      ∀ x ∈ S, ∀ j,
        |Gs (st x) j - eval (gridPoint (roundGrid3 ξ ⌈3 * K ^ 2 / ξ⌉₊ (Ainv *ᵥ cz (st x))))
            (Q j)| ≤
          p + 3 * (1 + ((M : ℝ) + 1) * ((2 * (4 * K ^ 2)) / r) ^ M) ^ 3 *
            (p + (err + ((M : ℝ) + 1) * M * K * K ^ M * ε) + ((M : ℝ) + 1) * p * (3 * (4 * K ^ 2)) ^ M +
              3 * ((M : ℝ) + 1) * M * (4 * K ^ 2 + p) * (3 * (4 * K ^ 2)) ^ M * ξ) := by
  classical
  set R : ℕ := ⌈3 * K ^ 2 / ξ⌉₊ with hR
  set S := symGrid ξ R with hS
  set Kk : ℝ := 4 * K ^ 2 with hKk
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hKK : K ≤ Kk := by nlinarith
  have hKk1 : 1 ≤ Kk := hK.trans hKK
  have hξR : 3 * K ^ 2 ≤ ξ * R := by
    have := Nat.le_ceil (3 * K ^ 2 / ξ)
    rw [← hR] at this
    rw [div_le_iff₀ hξ] at this
    linarith
  -- the family and its grid coordinates
  set Ω : Set (Λ × ℝ) := E0 ∩ st ⁻¹' Ωst with hΩ
  have hΩmeas : MeasurableSet Ω := hE0.inter (hst (Set.to_countable Ωst).measurableSet)
  have hΩref : ∀ x ∈ Ω, x ∈ Eref := fun x hx => hE0ref hx.1
  set uS : σ → Fin 3 → ℝ := fun D => Ainv *ᵥ cz D with huS
  have huS_bound : ∀ D ∈ Ωst, ∀ i, |uS D i| ≤ 3 * K ^ 2 := by
    intro D hD i
    have := abs_mulVec_le Ainv (cz D) hAinv (hczK D hD) i
    calc |uS D i| ≤ 3 * K * K := this
      _ = 3 * K ^ 2 := by ring
  set codeS : σ → S × S × S := fun D => roundGrid3 ξ R (uS D) with hcodeS
  have hcodeS_close : ∀ D ∈ Ωst, ∀ i, |uS D i - gridPoint (codeS D) i| ≤ ξ / 2 :=
    fun D hD i => abs_sub_gridPoint_roundGrid3_le hξ
      (fun k => (huS_bound D hD k).trans hξR) i
  -- the family is not empty (the budget charges a positive mass)
  have hcard_pos : (0 : ℝ) < (S.card : ℝ) := by
    rw [hS, card_symGrid hξ]; positivity
  have hΩpos : μ.real Ω ≠ 0 := by
    intro h0
    rw [h0, zero_div] at hbudget
    have : 0 < ((S.card : ℝ)) ^ 3 * a := by positivity
    nlinarith [mul_nonneg (mul_nonneg hδ hU.le) (pow_nonneg hcard_pos.le 3)]
  have hΩne : Ω.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    exact hΩpos (by rw [hne, measureReal_empty])
  obtain ⟨x₀, -⟩ := hΩne
  have : Nonempty (Λ × ℝ) := ⟨x₀⟩
  -- witnesses and their qualification data
  have hwit' : ∀ D ∈ Ωst, ∀ axis : Fin 3, ∃ w ∈ Eref, st w = D ∧
      (∀ k, |v w.1 k - J axis k| ≤ η) ∧ t0 ≤ w.2 ∧ w.2 ≤ t0 + h ∧
      ∃ P : Fin 3 → Polynomial ℝ, (∀ j, (P j).natDegree ≤ M) ∧ (∀ j k, |(P j).coeff k| ≤ K) ∧
        (∀ j, |Gs (st w) j - (P j).eval ((w.2 - t0) / h)| ≤ err) ∧
        ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Icc 0 1 ∧ ENNReal.ofReal (1 / K) ≤ volume E ∧
          ∀ s ∈ E, (w.1, t0 + h * s) ∈ Eref ∧
            ∀ j, |Gs (st (w.1, t0 + h * s)) j - (P j).eval s| ≤ err := hwit
  choose! wit hwitref hwitst hwitv hwit0 hwit1 Pw hPwdeg hPwcoef hPwfit Ew hEwm hEwsub hEwvol
    hEwfit using hwit'
  -- the kernel data on incidences, all functions of the state
  set code : Λ × ℝ → S × S × S := fun x => codeS (st x) with hcode
  have hcodem : Measurable code := (measurable_of_countable codeS).comp hst
  set G : Λ × ℝ → Fin 3 → ℝ := fun x => Gs (st x) with hG
  have hGm : Measurable G := (measurable_of_countable Gs).comp hst
  set P : Fin 3 → Λ × ℝ → Fin 3 → Polynomial ℝ := fun axis x => Pw (st x) axis with hP
  have hPm : ∀ axis, Measurable (fun x => polynomialFitCoefficients M (P axis x)) := fun axis =>
    (measurable_of_countable (fun D => polynomialFitCoefficients M (Pw D axis))).comp hst
  set E : Fin 3 → Λ × ℝ → Set ℝ := fun axis x => Ew (st x) axis with hE
  set H : Fin 3 → Λ × ℝ → ℝ → Fin 3 → ℝ :=
    fun axis x t => Gs (st ((wit (st x) axis).1, t0 + h * t)) with hH
  set u : Λ × ℝ → Fin 3 → ℝ := fun x => uS (st x) with hu
  have hRlt : (R : ℝ) < 3 * K ^ 2 / ξ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hξRle : ξ * R ≤ Kk := by
    have h1 : ξ * R ≤ ξ * (3 * K ^ 2 / ξ + 1) := mul_le_mul_of_nonneg_left hRlt.le hξ.le
    have h2 : ξ * (3 * K ^ 2 / ξ + 1) = 3 * K ^ 2 + ξ := by field_simp
    nlinarith
  -- the normalized time of a witness lies in the block
  have hwit_time : ∀ D ∈ Ωst, ∀ axis, z (wit D axis) 0 ∈ Icc (0 : ℝ) 1 := by
    intro D hD axis
    have h0 := hz0 (wit D axis).1 (wit D axis).2
    simp only [Prod.mk.eta] at h0
    rw [h0]
    constructor
    · exact div_nonneg (by linarith [hwit0 D hD axis]) hh.le
    · rw [div_le_one hh]; linarith [hwit1 D hD axis]
  obtain ⟨Q, T', hT'm, hT'Ω, hQdeg, hQcoef, hT'mass, hQerr⟩ :=
    hrow (μ.restrict Ω) S code hcodem G hGm P hPm Ω hΩmeas p Kk ξ
      (err + ((M : ℝ) + 1) * M * K * K ^ M * ε) a U δ r hp hKk1 hξ (by positivity) ha hU hδ hr
      (fun axis x hx j => hPwdeg (st x) hx.2 axis j) E
      (fun axis x hx => hEwm (st x) hx.2 axis) (fun axis x hx => hEwsub (st x) hx.2 axis)
      (fun axis x hx => (ENNReal.ofReal_le_ofReal
        (one_div_le_one_div_of_le (by linarith) hKK)).trans (hEwvol (st x) hx.2 axis)) H
      (fun axis x hx t ht j => by
        rw [abs_sub_comm]
        exact ((hEwfit (st x) hx.2 axis t ht).2 j).trans herrp)
      (fun g => by
        obtain ⟨F, hF, hFm⟩ := hfield (liftMatrix J *ᵥ gridPoint g)
        refine ⟨F, hF.trans hKK, fun x hx hxg => hFm x (hΩref x hx) ?_⟩
        intro i
        have hclose : ∀ k, |(Ainv *ᵥ cz (st x)) k - gridPoint g k| ≤ ξ / 2 := by
          intro k
          have := hcodeS_close (st x) hx.2 k
          simpa [code, hxg] using this
        have := state_near_grid hA hK hξ.le hεξ hJ (cz (st x)) (gridPoint g) (z x) hclose
          (hcz x (hΩref x hx)) i
        nlinarith)
      (fun axis key t => by
        obtain ⟨F, hF, hFm⟩ :=
          hfield (liftMatrix J *ᵥ fiberPoint axis ((key.1 : ℝ), (key.2 : ℝ)) t)
        refine ⟨F, hF.trans hKK, fun x hx hkey ht => ?_⟩
        have hD := hx.2
        have hwref := hwitref (st x) hD axis
        have hwst := hwitst (st x) hD axis
        refine hFm _ (hEwfit (st x) hD axis t ht).1 ?_
        intro i
        set w := wit (st x) axis with hw
        have hpos : z (w.1, t0 + h * t) = z w + (t - z w 0) • lift (v w.1) := by
          have h1 := hzline w.1 w.2 (t0 + h * t)
          have h2 := hz0 w.1 w.2
          simp only [Prod.mk.eta] at h1 h2
          rw [h1, h2]
          congr 2
          field_simp
          ring
        have hzw : ∀ k, |z w k - cz (st x) k| ≤ ε := by
          intro k
          have := hcz w hwref k
          rwa [hwst] at this
        have hclose : ∀ k, |(Ainv *ᵥ cz (st x)) k - gridPoint (code x) k| ≤ ξ / 2 :=
          hcodeS_close (st x) hD
        have hnear := witness_near_fiber hA hK hξ.le hε hεξ hη hηξ hJ hAinv (cz (st x))
          (gridPoint (code x)) (z w) hclose hzw axis (v w.1) (hwitv (st x) hD axis) t
          (hEwsub (st x) hD axis ht) (hwit_time (st x) hD axis) i
        rw [realFiberKey_gridPoint, hkey] at hnear
        rw [hpos]
        nlinarith)
      u
      (fun s hs => (abs_le_of_mem_symGrid hξ.le hs).trans hξRle)
      (fun x hx i => (huS_bound (st x) hx.2 i).trans (by nlinarith))
      (fun x hx i => (hcodeS_close (st x) hx.2 i).trans (by linarith))
      (fun x hx j => (hGK (st x) hx.2 j).trans hKK)
      (fun axis x hx j k => (hPwcoef (st x) hx.2 axis j k).trans hKK)
      (fun axis x hx j => by
        have hD := hx.2
        have hsum : ∑ i, u x i = cz (st x) 0 := by
          have := liftMatrix_mulVec_zero J (uS (st x))
          rw [huS, frame_mulVec_inv hA] at this
          exact this.symm
        rw [hsum]
        set w := wit (st x) axis with hw
        have hwst := hwitst (st x) hD axis
        have hfitw := hPwfit (st x) hD axis j
        rw [hwst] at hfitw
        have hzw0 : z w 0 = (w.2 - t0) / h := by
          have h2 := hz0 w.1 w.2
          simpa only [Prod.mk.eta] using h2
        have hshift : |(w.2 - t0) / h - cz (st x) 0| ≤ ε := by
          have := hcz w (hwitref (st x) hD axis) 0
          rwa [hwst, hzw0] at this
        have htime := hwit_time (st x) hD axis
        rw [hzw0] at htime
        have hs : |(w.2 - t0) / h| ≤ K := by
          rw [abs_le]; constructor <;> linarith [htime.1, htime.2]
        exact Submission.Lib.K4ScalarCoreAssembly.polynomial_fit_at_nearby_time M
          (Pw (st x) axis j) (hPwdeg (st x) hD axis j) K K hK0 hK
          (fun k _ => hPwcoef (st x) hD axis j k) (Gs (st x) j) _ _ err ε hs
          (hczK (st x) hD 0) hfitw hshift)
      (symGrid_sep hξ R)
      (fun g => by
        have hgm : MeasurableSet {x | code x = g} := hcodem (measurableSet_singleton g)
        rw [measureReal_restrict_apply hgm]
        refine (measureReal_mono ?_).trans (hcap (liftMatrix J *ᵥ gridPoint g))
        rintro x ⟨hxg, hx⟩
        refine ⟨hx, ?_⟩
        intro i
        have hxg' : code x = g := hxg
        have hclose : ∀ k, |(Ainv *ᵥ cz (st x)) k - gridPoint g k| ≤ ξ / 2 := by
          intro k
          have := hcodeS_close (st x) hx.2 k
          simpa [code, hxg'] using this
        exact state_near_grid hA hK hξ.le hεξ hJ (cz (st x)) (gridPoint g) (z x) hclose
          (hcz x (hΩref x hx)) i)
      (by
        rw [measureReal_restrict_apply hΩmeas, Set.inter_self]
        exact hbudget)
      hgap
  -- whole states of the selected incidences
  set Ssel : Set (Λ × ℝ) := E0 ∩ st ⁻¹' (st '' T') with hSsel
  have hSselm : MeasurableSet Ssel := hE0.inter (hst (Set.to_countable _).measurableSet)
  have hT'Ssel : T' ⊆ Ssel := fun y hy => ⟨(hT'Ω hy).1, ⟨y, hy, rfl⟩⟩
  refine ⟨Q, Ssel, hSselm, ?_, ?_, hQdeg, hQcoef, ?_, ?_⟩
  · rintro x ⟨hx0, y, hy, hyx⟩
    exact ⟨hx0, by rw [Set.mem_preimage, ← hyx]; exact (hT'Ω hy).2⟩
  · rintro x hx y ⟨-, y', hy', hy'y⟩ hxy
    exact ⟨hx, y', hy', hy'y.trans hxy.symm⟩
  · refine hT'mass.trans ?_
    rw [measureReal_restrict_apply hT'm, Set.inter_eq_left.mpr hT'Ω]
    exact measureReal_mono hT'Ssel
  · rintro x ⟨-, y, hy, hyx⟩ j
    have := hQerr y hy j
    simp only [G, code, codeS, hyx] at this
    exact this

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
