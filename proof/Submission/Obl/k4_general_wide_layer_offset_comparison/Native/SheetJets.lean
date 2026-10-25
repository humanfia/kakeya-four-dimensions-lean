-- Adapted from this LOT tree, obligation o254, branch x0898, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/SheetJets.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0864, commit 14a7e56376763201c24256782261147a69c7bd82,
   Submission/Obl/k4_finite_projected_horizontal_candidates/SheetJets.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Obl.k4_algebraic_real_jet_comparison
import Submission.Obl.k4_algebraic_real_jet_comparison.AffineRelations

/-!
# Algebraic sheets and their center jets

The sheet class of the accepted local matching theorem (o112) and of the accepted real jet
comparison (o149): a function on `ℂ³` that is holomorphic on the ball of radius `4`, satisfies a
nonzero polynomial relation of degree at most `D` there, and is real on the real unit ball.

`exists_sheet_jets` packages o149 as a finite-dimensional jet `J` with a two-sided comparison:
the jet difference at the center controls the difference of two sheets on the real ball of
radius `1/2`, and is controlled by their difference on the real ball of radius `1/4`.
This is the tool for grouping sheets by neighbouring jet bins at a fixed discrepancy scale
(paper, proof of Lemma 8.3, "Matching with separate reference weights").
-/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Metric Set Filter
open scoped Topology

noncomputable section

/-- The real points of `ℂ³`. -/
def emb (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 (fun i => (x i : ℂ))

theorem emb_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    emb (c • x) = (c : ℂ) • emb x := by
  ext i
  simp [emb]

theorem emb_add (x y : EuclideanSpace ℝ (Fin 3)) : emb (x + y) = emb x + emb y := by
  ext i
  simp [emb]

theorem emb_zero : emb 0 = 0 := by
  ext i
  simp [emb]

theorem norm_emb (x : EuclideanSpace ℝ (Fin 3)) : ‖emb x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [emb]

/-- A bounded-degree algebraic sheet, holomorphic on the ball of radius `4` and real on the real
unit ball. -/
def IsSheet (D : ℕ) (f : EuclideanSpace ℂ (Fin 3) → ℂ) : Prop :=
  ∃ P : MvPolynomial (Fin 4) ℂ, P ≠ 0 ∧ P.totalDegree ≤ D ∧
    DifferentiableOn ℂ f (ball 0 4) ∧
    (∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      MvPolynomial.eval (Fin.snoc (fun i : Fin 3 => z i) (f z)) P = 0) ∧
    ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 → (f (emb x)).im = 0

/-- The zero sheet, with relation `w = 0`. -/
theorem isSheet_zero {D : ℕ} (hD : 1 ≤ D) : IsSheet D (fun _ => 0) := by
  refine ⟨MvPolynomial.X 3, MvPolynomial.X_ne_zero _, ?_, differentiableOn_const _, ?_, ?_⟩
  · rw [MvPolynomial.totalDegree_X]
    exact hD
  · intro z _
    simp [Fin.snoc]
  · intro x _
    simp

/-- Rescaling the base of a sheet by `0 < c ≤ 1` gives a sheet. -/
theorem IsSheet.comp_smul {D : ℕ} {f : EuclideanSpace ℂ (Fin 3) → ℂ} (hf : IsSheet D f)
    {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    IsSheet D (fun z => f ((c : ℂ) • z)) := by
  obtain ⟨P, hP0, hPdeg, hhol, hrel, hreal⟩ := hf
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
  have hmaps : ∀ z ∈ ball (0 : EuclideanSpace ℂ (Fin 3)) 4, (c : ℂ) • z ∈ ball 0 4 := by
    intro z hz
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc0.le]
    calc c * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
      _ < 4 := by simpa using hz
  refine ⟨Submission.Obl.k4_algebraic_real_jet_comparison.affineRelation 0 (c : ℂ) 1 P,
    fun h => hP0 ?_,
    (Submission.Obl.k4_algebraic_real_jet_comparison.totalDegree_affineRelation_le _ _ _ _).trans
      hPdeg, ?_, ?_, ?_⟩
  · exact Submission.Obl.k4_algebraic_real_jet_comparison.affineRelation_injective 0 hcne
      one_ne_zero (h.trans (map_zero _).symm)
  · exact hhol.comp ((differentiable_id.const_smul ((c : ℂ))).differentiableOn) hmaps
  · intro z hz
    rw [Submission.Obl.k4_algebraic_real_jet_comparison.eval_affineRelation]
    have := hrel _ (hmaps z hz)
    simpa [Fin.snoc] using this
  · intro x hx
    have : (c : ℂ) • emb x = emb (c • x) := (emb_smul c x).symm
    simp only [this]
    apply hreal
    rw [norm_smul, Real.norm_of_nonneg hc0.le]
    nlinarith [norm_nonneg x]

/-- The real part of a sheet along the line `t ↦ t • v`. -/
def lineRe (f : EuclideanSpace ℂ (Fin 3) → ℂ) (v : EuclideanSpace ℝ (Fin 3)) : ℝ → ℝ :=
  fun t => (f (emb (t • v))).re

/-- Scaling the variable of a function smooth on `(-1, 1)` by `|c| ≤ 1` scales its iterated
derivatives at `0`. -/
theorem iteratedDeriv_comp_mul_zero {h : ℝ → ℝ} (hh : ContDiffOn ℝ ⊤ h (Ioo (-1) 1))
    {c : ℝ} (hc : |c| ≤ 1) (m : ℕ) :
    iteratedDeriv m (fun t => h (c * t)) 0 = c ^ m * iteratedDeriv m h 0 := by
  have hs : IsOpen (Ioo (-1 : ℝ) 1) := isOpen_Ioo
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  have hmaps : MapsTo (c * ·) (Ioo (-1 : ℝ) 1) (Ioo (-1 : ℝ) 1) := by
    intro t ht
    have ht' : |t| < 1 := abs_lt.mpr ⟨ht.1, ht.2⟩
    have : |c * t| < 1 := by
      rw [abs_mul]
      calc |c| * |t| ≤ 1 * |t| := by gcongr
        _ < 1 := by simpa using ht'
    exact ⟨(abs_lt.mp this).1, (abs_lt.mp this).2⟩
  have e1 := iteratedDerivWithin_comp_const_smul (n := m) h0 hs.uniqueDiffOn
    (hh.of_le (by exact_mod_cast le_top)) c hmaps
  rw [iteratedDerivWithin_of_isOpen hs h0, mul_zero, iteratedDerivWithin_of_isOpen hs h0] at e1
  simpa [smul_eq_mul] using e1

/-- **Center jets of sheets.** A finite-dimensional jet with a two-sided comparison, from the
accepted o149. -/
theorem exists_sheet_jets (D : ℕ) (hD : 1 ≤ D) :
    ∃ (m : ℕ) (J : (EuclideanSpace ℂ (Fin 3) → ℂ) → Fin m → ℝ) (c₁ c₂ : ℝ),
      0 < c₁ ∧ 0 < c₂ ∧
      (∀ f g, IsSheet D f → IsSheet D g → ∀ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 →
        ‖f (emb y) - g (emb y)‖ ≤ c₁ * ∑ i, |J f i - J g i|) ∧
      (∀ f g, IsSheet D f → IsSheet D g → ∀ A : ℝ, 0 < A →
        (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 → ‖f (emb x) - g (emb x)‖ ≤ A) →
        ∀ i, |J f i - J g i| ≤ c₂ * A) := by
  classical
  obtain ⟨K, -, V, -, c, hc, B, hB, H⟩ := Submission.k4_algebraic_real_jet_comparison D
  -- the conclusions of o149 for a pair of sheets
  have hA : ∀ f g, IsSheet D f → IsSheet D g → ∀ v ∈ V, ∀ x : EuclideanSpace ℝ (Fin 3),
      ‖x‖ ≤ 3 / 4 → ContDiffOn ℝ ⊤
        (fun t : ℝ => (f (emb (x + t • v)) - g (emb (x + t • v))).re) (Ioo (-1) 1) := by
    intro f g hf hg
    obtain ⟨P, hP0, hPd, hfh, hfr, hfre⟩ := hf
    obtain ⟨Q, hQ0, hQd, hgh, hgr, hgre⟩ := hg
    exact (H f g P Q hP0 hQ0 hPd hQd hfh hgh hfr hgr (fun x hx => ⟨hfre x hx, hgre x hx⟩)).1
  have hC : ∀ f g, IsSheet D f → IsSheet D g → ∀ A : ℝ, 0 < A →
      (∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 → ‖f (emb x) - g (emb x)‖ ≤ A) →
      ∀ v ∈ V, ∀ (m : ℕ) (x : EuclideanSpace ℝ (Fin 3)), ‖x‖ ≤ 3 / 4 →
        |iteratedDeriv m (fun t : ℝ => (f (emb (x + t • v)) - g (emb (x + t • v))).re) 0| ≤
          B m * A := by
    intro f g hf hg
    obtain ⟨P, hP0, hPd, hfh, hfr, hfre⟩ := hf
    obtain ⟨Q, hQ0, hQd, hgh, hgr, hgre⟩ := hg
    exact (H f g P Q hP0 hQ0 hPd hQd hfh hgh hfr hgr (fun x hx => ⟨hfre x hx, hgre x hx⟩)).2.2.1
  have hDd : ∀ f g, IsSheet D f → IsSheet D g → ∀ x y : EuclideanSpace ℝ (Fin 3),
      ‖x‖ ≤ 1 / 2 → ‖y‖ ≤ 1 / 2 → c * ‖f (emb y) - g (emb y)‖ ≤
        ∑ v ∈ V, ∑ j ∈ Finset.range (K + 1),
          |iteratedDeriv j (fun t : ℝ => (f (emb (x + t • v)) - g (emb (x + t • v))).re) 0| := by
    intro f g hf hg
    obtain ⟨P, hP0, hPd, hfh, hfr, hfre⟩ := hf
    obtain ⟨Q, hQ0, hQd, hgh, hgr, hgre⟩ := hg
    exact (H f g P Q hP0 hQ0 hPd hQd hfh hgh hfr hgr (fun x hx => ⟨hfre x hx, hgre x hx⟩)).2.2.2
  -- smoothness of the line restrictions of one sheet
  have hsmooth : ∀ f, IsSheet D f → ∀ v ∈ V, ContDiffOn ℝ ⊤ (lineRe f v) (Ioo (-1) 1) := by
    intro f hf v hv
    have := hA f (fun _ => 0) hf (isSheet_zero hD) v hv 0 (by rw [norm_zero]; norm_num)
    unfold lineRe
    simpa using this
  -- the jet of the difference is the difference of the jets
  have hdiff : ∀ f g, IsSheet D f → IsSheet D g → ∀ v ∈ V, ∀ j : ℕ,
      iteratedDeriv j (fun t : ℝ => (f (emb (0 + t • v)) - g (emb (0 + t • v))).re) 0 =
        iteratedDeriv j (lineRe f v) 0 - iteratedDeriv j (lineRe g v) 0 := by
    intro f g hf hg v hv j
    have h0 : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
    have hfa : ContDiffAt ℝ j (lineRe f v) 0 :=
      ((hsmooth f hf v hv).contDiffAt h0).of_le (by exact_mod_cast le_top)
    have hga : ContDiffAt ℝ j (lineRe g v) 0 :=
      ((hsmooth g hg v hv).contDiffAt h0).of_le (by exact_mod_cast le_top)
    have hfun : (fun t : ℝ => (f (emb (0 + t • v)) - g (emb (0 + t • v))).re) =
        lineRe f v - lineRe g v := by
      funext t
      simp only [lineRe, Pi.sub_apply, zero_add, Complex.sub_re]
    rw [hfun, iteratedDeriv_sub hfa hga]
  -- the jet index
  set ι := {v // v ∈ V} × Fin (K + 1) with hι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let J : (EuclideanSpace ℂ (Fin 3) → ℂ) → Fin (Fintype.card ι) → ℝ := fun f i =>
    iteratedDeriv ((e.symm i).2 : ℕ) (lineRe f (e.symm i).1) 0
  -- a common derivative constant
  set Bmax : ℝ := ∑ j ∈ Finset.range (K + 1), (4 : ℝ) ^ j * B j + 1 with hBmax
  have hBmax_pos : 0 < Bmax := by
    have : 0 ≤ ∑ j ∈ Finset.range (K + 1), (4 : ℝ) ^ j * B j :=
      Finset.sum_nonneg fun j _ => by have := hB j; positivity
    linarith
  have hBj : ∀ j : ℕ, j ≤ K → (4 : ℝ) ^ j * B j ≤ Bmax := by
    intro j hj
    have hmem : j ∈ Finset.range (K + 1) := Finset.mem_range.mpr (by omega)
    have := Finset.single_le_sum (f := fun j => (4 : ℝ) ^ j * B j)
      (fun j _ => by have := hB j; positivity) hmem
    linarith
  refine ⟨Fintype.card ι, J, c⁻¹, Bmax, inv_pos.mpr hc, hBmax_pos, ?_, ?_⟩
  · -- upper comparison on the ball of radius `1/2`
    intro f g hf hg y hy
    have hd := hDd f g hf hg 0 y (by simp) hy
    have hsum : (∑ v ∈ V, ∑ j ∈ Finset.range (K + 1),
        |iteratedDeriv j (fun t : ℝ => (f (emb (0 + t • v)) - g (emb (0 + t • v))).re) 0|) =
        ∑ i, |J f i - J g i| := by
      rw [← e.sum_comp (fun i => |J f i - J g i|)]
      simp only [J, Equiv.symm_apply_apply]
      rw [Fintype.sum_prod_type, ← Finset.sum_coe_sort V]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.sum_range (fun j => |iteratedDeriv j
        (fun t : ℝ => (f (emb (0 + t • (v : EuclideanSpace ℝ (Fin 3)))) -
          g (emb (0 + t • (v : EuclideanSpace ℝ (Fin 3))))).re) 0|)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hdiff f g hf hg v v.2 j]
    have hd' : c * ‖f (emb y) - g (emb y)‖ ≤ ∑ i, |J f i - J g i| := by
      rw [← hsum]
      exact hd
    rw [inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
    exact hd'
  · -- lower comparison on the ball of radius `1/4`
    intro f g hf hg A hA hfgA i
    have hq0 : (0 : ℝ) < 1 / 4 := by norm_num
    have hq1 : (1 / 4 : ℝ) ≤ 1 := by norm_num
    have hf4 := hf.comp_smul hq0 hq1
    have hg4 := hg.comp_smul hq0 hq1
    rcases hi : e.symm i with ⟨⟨v, hv⟩, j⟩
    simp only [J, hi]
    have hbound : ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 →
        ‖f (((1 / 4 : ℝ) : ℂ) • emb x) - g (((1 / 4 : ℝ) : ℂ) • emb x)‖ ≤ A := by
      intro x hx
      rw [← emb_smul]
      apply hfgA
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4)]
      linarith
    have hCj := hC _ _ hf4 hg4 A hA hbound v hv j 0 (by rw [norm_zero]; norm_num)
    -- the scaled line function
    set h : ℝ → ℝ := lineRe f v - lineRe g v with hh
    have hfun : (fun t : ℝ => (f (((1 / 4 : ℝ) : ℂ) • emb (0 + t • v)) -
        g (((1 / 4 : ℝ) : ℂ) • emb (0 + t • v))).re) = fun t => h ((1 / 4 : ℝ) * t) := by
      funext t
      simp only [hh, lineRe, Pi.sub_apply, zero_add, Complex.sub_re, ← emb_smul, smul_smul]
    rw [hfun] at hCj
    have hsm : ContDiffOn ℝ ⊤ h (Ioo (-1) 1) := (hsmooth f hf v hv).sub (hsmooth g hg v hv)
    rw [iteratedDeriv_comp_mul_zero hsm (by rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]; norm_num)
      j] at hCj
    have h0 : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
    have hfa : ContDiffAt ℝ j (lineRe f v) 0 :=
      ((hsmooth f hf v hv).contDiffAt h0).of_le (by exact_mod_cast le_top)
    have hga : ContDiffAt ℝ j (lineRe g v) 0 :=
      ((hsmooth g hg v hv).contDiffAt h0).of_le (by exact_mod_cast le_top)
    rw [hh, iteratedDeriv_sub hfa hga, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (1 / 4) ^ (j : ℕ))]
      at hCj
    have h4 : (0 : ℝ) < 4 ^ (j : ℕ) := by positivity
    have hkey : |iteratedDeriv j (lineRe f v) 0 - iteratedDeriv j (lineRe g v) 0| ≤
        4 ^ (j : ℕ) * B j * A := by
      have : (1 / 4 : ℝ) ^ (j : ℕ) * 4 ^ (j : ℕ) = 1 := by
        rw [← mul_pow]; norm_num
      calc |iteratedDeriv j (lineRe f v) 0 - iteratedDeriv j (lineRe g v) 0|
          = 4 ^ (j : ℕ) * ((1 / 4 : ℝ) ^ (j : ℕ) *
              |iteratedDeriv j (lineRe f v) 0 - iteratedDeriv j (lineRe g v) 0|) := by
            rw [← mul_assoc, mul_comm ((4 : ℝ) ^ (j : ℕ)), this, one_mul]
        _ ≤ 4 ^ (j : ℕ) * (B j * A) := by gcongr
        _ = 4 ^ (j : ℕ) * B j * A := by ring
    calc |iteratedDeriv j (lineRe f v) 0 - iteratedDeriv j (lineRe g v) 0|
        ≤ 4 ^ (j : ℕ) * B j * A := hkey
      _ ≤ Bmax * A := by
        gcongr
        exact hBj j (Nat.lt_succ_iff.mp j.2)

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
