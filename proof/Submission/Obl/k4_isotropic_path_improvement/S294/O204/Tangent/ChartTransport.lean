-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.O204.Tangent.ChartTransport, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Adapted from this LOT tree, o204 (k4_uniform_sampled_isotropic_branches), session x1078,
-- branch x1078, commit c3fccb87c, file Submission/Obl/k4_uniform_sampled_isotropic_branches/Tangent/ChartTransport.lean;
-- namespace renamed to Submission.Obl.k4_isotropic_path_improvement.S294.O204. Attributions in the file are kept.
-- Transport of an original chart to the virtual packet below an ancestor (x1078, o204).
-- Uses x1080's `Tangent.Forward` (isotropic frame coordinates), accepted o280's
-- `PFrame.normTest`, and lib `K4RepresentativeAssembly.fmt_affine_preimage` (imported).
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.Forward
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.Schedule
import Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent.Injective
import Submission.Obl.k4_finite_affine_candidate_return.ParentFrameInv
import Submission.Lib.K4RepresentativeAssembly.FiniteFormat

/-!
# The chart of a packet, seen from an ancestor

`ch_virtual`: the frozen chart `ch` of a packet `b` (clock `Tb`, block `jb`, depth `rb`, unit
`B`, centre `c`, velocity `u`, frame `Q`, test `R`) inside an ancestor block (clock `TA`, block
`jA`, unsheared centre `cA`) is, in the isotropic frame `isoPFrame t₀ q cA (B/δA)`
(`t₀ = jA/2^TA`, `q = 2^-TA`, `δA = δ(N, rA)`), the frozen chart of the virtual packet with
clock `Tb - TA`, block `jb - jA 2^(Tb - TA)`, depth `rb - rA`, unit one, centre
`q⁻¹(c + t₀ u - cA)`, velocity `u`, frame `q⁻¹ Q`, test `normTest δA R`, assignment
`tanLine '' A` and counted set `tanEvent '' F`, with slack `2κ`. The polynomial formats of the
image sets have the same atom count and degree; the coefficient and size budgets are
explicit hypotheses.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent

open MeasureTheory MvPolynomial
open Submission.Obl.k4_finite_affine_candidate_return
open Submission.Obl.k4_remainder_pure_profile_normalization.Normalization
open Submission.Obl.k4_isotropic_path_improvement.S294.O204.Split

noncomputable section

/-- The inverse of the isotropic line map on coefficients. -/
def isoInv (t₀ q : ℝ) (c : P2) (sc : ℝ) (x : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![q * x 0 - t₀ * x 3 + c 0, q * x 1 - t₀ * x 4 + c 1, x 2 / sc - t₀ * (x 5 / (sc * q)),
    x 3, x 4, x 5 / (sc * q)]

/-- The inverse as polynomials of degree at most one. -/
def isoInvPoly (t₀ q : ℝ) (c : P2) (sc : ℝ) : Fin 6 → MvPolynomial (Fin 6) ℝ :=
  ![C q * X 0 - C t₀ * X 3 + C (c 0), C q * X 1 - C t₀ * X 4 + C (c 1),
    C sc⁻¹ * X 2 - C (t₀ * (sc * q)⁻¹) * X 5, X 3, X 4, C (sc * q)⁻¹ * X 5]

lemma eval_isoInvPoly (t₀ q : ℝ) (c : P2) (sc : ℝ) (x : Fin 6 → ℝ) :
    (fun j => eval x (isoInvPoly t₀ q c sc j)) = isoInv t₀ q c sc x := by
  funext j
  fin_cases j <;> simp [isoInvPoly, isoInv] <;> ring

lemma totalDegree_isoInvPoly_le (t₀ q : ℝ) (c : P2) (sc : ℝ) (j : Fin 6) :
    (isoInvPoly t₀ q c sc j).totalDegree ≤ 1 := by
  fin_cases j
  · exact deg1_add (deg1_sub (deg1_C_mul _ (deg1_X _)) (deg1_C_mul _ (deg1_X _))) (deg1_C _)
  · exact deg1_add (deg1_sub (deg1_C_mul _ (deg1_X _)) (deg1_C_mul _ (deg1_X _))) (deg1_C _)
  · exact deg1_sub (deg1_C_mul _ (deg1_X _)) (deg1_C_mul _ (deg1_X _))
  · exact deg1_X _
  · exact deg1_X _
  · exact deg1_C_mul _ (deg1_X _)

lemma tanLine_isoInv (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : q ≠ 0) (hsc : sc ≠ 0) (i : ℕ)
    (x : Fin 6 → ℝ) : tanLine (isoPFrame t₀ q c sc) 0 (i, isoInv t₀ q c sc x) = (i, x) := by
  rw [tanLine_iso t₀ q c sc hq]
  congr 1
  funext j
  fin_cases j <;> simp [isoInv] <;> field_simp <;> ring

lemma isoInv_tanLine (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : q ≠ 0) (hsc : sc ≠ 0) (l : Ln) :
    isoInv t₀ q c sc (tanLine (isoPFrame t₀ q c sc) 0 l).2 = l.2 := by
  rw [tanLine_iso t₀ q c sc hq]
  funext j
  fin_cases j <;> simp [isoInv] <;> field_simp <;> ring

lemma mem_image_tanLine_iff (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : q ≠ 0) (hsc : sc ≠ 0)
    (A : Set Ln) (i : ℕ) (x : Fin 6 → ℝ) :
    (i, x) ∈ tanLine (isoPFrame t₀ q c sc) 0 '' A ↔ (i, isoInv t₀ q c sc x) ∈ A := by
  constructor
  · rintro ⟨l, hl, hlx⟩
    have h1 : l.1 = i := by
      have := congrArg Prod.fst hlx; simpa [tanLine] using this
    have h2 : l.2 = isoInv t₀ q c sc x := by
      rw [← isoInv_tanLine t₀ q c sc hq hsc l, hlx]
    have : l = (i, isoInv t₀ q c sc x) := Prod.ext h1 h2
    rwa [← this]
  · intro h
    exact ⟨_, h, tanLine_isoInv t₀ q c sc hq hsc i x⟩

/-- Assignment sections of the image keep their polynomial format. -/
lemma fmt_tanLine_image (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : q ≠ 0) (hsc : sc ≠ 0)
    (A : Set Ln) (i : ℕ) (H : ℝ) (D : ℕ) (h : Split.fmt 6 H D {x | (i, x) ∈ A}) :
    Split.fmt 6 H D {x | (i, x) ∈ tanLine (isoPFrame t₀ q c sc) 0 '' A} := by
  have hp := Submission.Lib.K4RepresentativeAssembly.fmt_affine_preimage h
    (isoInvPoly t₀ q c sc) (totalDegree_isoInvPoly_le t₀ q c sc)
  have hset : {x | (i, x) ∈ tanLine (isoPFrame t₀ q c sc) 0 '' A} =
      (fun x j => eval x (isoInvPoly t₀ q c sc j)) ⁻¹' {x | (i, x) ∈ A} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [mem_image_tanLine_iff t₀ q c sc hq hsc, eval_isoInvPoly]
  rw [hset]
  exact hp

/-- The inverse of the isotropic event map on the seven event coordinates. -/
def isoInvPoly7 (t₀ q : ℝ) (c : P2) (sc : ℝ) : Fin 7 → MvPolynomial (Fin 7) ℝ :=
  Fin.snoc (fun j : Fin 6 => rename Fin.castSucc (isoInvPoly t₀ q c sc j)) (C t₀ + C q * X 6)

lemma eval_isoInvPoly7_castSucc (t₀ q : ℝ) (c : P2) (sc : ℝ) (x : Fin 7 → ℝ) (j : Fin 6) :
    eval x (isoInvPoly7 t₀ q c sc j.castSucc) =
      isoInv t₀ q c sc (fun k : Fin 6 => x k.castSucc) j := by
  rw [isoInvPoly7, Fin.snoc_castSucc, eval_rename, ← eval_isoInvPoly]
  rfl

lemma eval_isoInvPoly7_last (t₀ q : ℝ) (c : P2) (sc : ℝ) (x : Fin 7 → ℝ) :
    eval x (isoInvPoly7 t₀ q c sc 6) = t₀ + q * x 6 := by
  have : (6 : Fin 7) = Fin.last 6 := rfl
  rw [this, isoInvPoly7, Fin.snoc_last]
  simp

lemma totalDegree_isoInvPoly7_le (t₀ q : ℝ) (c : P2) (sc : ℝ) (k : Fin 7) :
    (isoInvPoly7 t₀ q c sc k).totalDegree ≤ 1 := by
  refine Fin.lastCases ?_ (fun j => ?_) k
  · rw [isoInvPoly7, Fin.snoc_last]
    exact deg1_add (deg1_C _) (deg1_C_mul _ (deg1_X _))
  · rw [isoInvPoly7, Fin.snoc_castSucc]
    exact (totalDegree_rename_le _ _).trans (totalDegree_isoInvPoly_le t₀ q c sc j)

lemma mem_image_tanEvent_iff (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : q ≠ 0) (hsc : sc ≠ 0)
    (F : Set Ev) (i : ℕ) (x : Fin 6 → ℝ) (τ : ℝ) :
    ((i, x), τ) ∈ tanEvent (isoPFrame t₀ q c sc) 0 '' F ↔
      ((i, isoInv t₀ q c sc x), t₀ + q * τ) ∈ F := by
  constructor
  · rintro ⟨p, hp, hpx⟩
    simp only [tanEvent, Prod.mk.injEq] at hpx
    obtain ⟨hl, ht⟩ := hpx
    have h1 : p.1.1 = i := by have := congrArg Prod.fst hl; simpa [tanLine] using this
    have h2 : p.1.2 = isoInv t₀ q c sc x := by rw [← isoInv_tanLine t₀ q c sc hq hsc p.1, hl]
    have h3 : p.2 = t₀ + q * τ := by
      have hh : (isoPFrame t₀ q c sc).F.t₀ = t₀ := rfl
      have hh' : (isoPFrame t₀ q c sc).F.q = q := rfl
      rw [hh, hh'] at ht
      rw [← ht]; field_simp; ring
    have : p = ((i, isoInv t₀ q c sc x), t₀ + q * τ) := Prod.ext (Prod.ext h1 h2) h3
    rwa [← this]
  · intro h
    refine ⟨_, h, ?_⟩
    simp only [tanEvent, tanLine_isoInv t₀ q c sc hq hsc]
    congr 1
    show (t₀ + q * τ - t₀) / q = τ
    field_simp; ring

/-- Counted-set sections of the image keep their polynomial format. -/
lemma fmt_tanEvent_image (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : q ≠ 0) (hsc : sc ≠ 0)
    (F : Set Ev) (i : ℕ) (H : ℝ) (D : ℕ)
    (h : Split.fmt 7 H D {x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ F}) :
    Split.fmt 7 H D {x₁ : Fin 7 → ℝ |
      ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ tanEvent (isoPFrame t₀ q c sc) 0 '' F} := by
  have hp := Submission.Lib.K4RepresentativeAssembly.fmt_affine_preimage h
    (isoInvPoly7 t₀ q c sc) (totalDegree_isoInvPoly7_le t₀ q c sc)
  have hset : {x₁ : Fin 7 → ℝ |
      ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ tanEvent (isoPFrame t₀ q c sc) 0 '' F} =
      (fun x k => eval x (isoInvPoly7 t₀ q c sc k)) ⁻¹'
        {x₁ : Fin 7 → ℝ | ((i, fun j₁ : Fin 6 => x₁ j₁.castSucc), x₁ 6) ∈ F} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [mem_image_tanEvent_iff t₀ q c sc hq hsc]
    have h6 : eval x (isoInvPoly7 t₀ q c sc 6) = t₀ + q * x 6 := eval_isoInvPoly7_last t₀ q c sc x
    have hcs : (fun j₁ : Fin 6 => eval x (isoInvPoly7 t₀ q c sc j₁.castSucc)) =
        isoInv t₀ q c sc (fun k : Fin 6 => x k.castSucc) := by
      funext j₁; exact eval_isoInvPoly7_castSucc t₀ q c sc x j₁
    rw [h6, hcs]
  rw [hset]
  exact hp


/-- Pointwise identities of the virtual test in the isotropic frame. -/
lemma eval_normTest_iso (t₀ q : ℝ) (c : P2) (sc δA : ℝ) (hq : q ≠ 0) (hsc : sc ≠ 0)
    (R : Po) (l : Ln) (τ : ℝ) :
    MvPolynomial.eval (xp (tanLine (isoPFrame t₀ q c sc) 0 l) τ)
        ((isoPFrame t₀ q c sc).normTest δA R) = δA⁻¹ * MvPolynomial.eval (xp l (t₀ + q * τ)) R ∧
    MvPolynomial.eval (xp (tanLine (isoPFrame t₀ q c sc) 0 l) τ)
        (MvPolynomial.pderiv 3 ((isoPFrame t₀ q c sc).normTest δA R)) =
      sc⁻¹ * (δA⁻¹ * MvPolynomial.eval (xp l (t₀ + q * τ)) (MvPolynomial.pderiv 3 R)) ∧
    MvPolynomial.eval (xp (tanLine (isoPFrame t₀ q c sc) 0 l) τ)
        (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 ((isoPFrame t₀ q c sc).normTest δA R))) =
      sc⁻¹ * (sc⁻¹ * (δA⁻¹ * MvPolynomial.eval (xp l (t₀ + q * τ))
        (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 R)))) := by
  set Φ := isoPFrame t₀ q c sc with hΦ
  have hq' : Φ.F.q ≠ 0 := hq
  have hD : IsUnit Φ.F.D.det := by
    refine Ne.isUnit ?_
    simp [hΦ, isoPFrame, isoFrame, hq]
  have hsc' : Φ.sc ≠ 0 := hsc
  have hτ : (t₀ + q * τ - Φ.F.t₀) / Φ.F.q = τ := by
    show (t₀ + q * τ - t₀) / q = τ
    field_simp; ring
  have hx : xp (tanLine Φ 0 l) τ = exS Φ.eb l ((t₀ + q * τ - Φ.F.t₀) / Φ.F.q) := by
    rw [hτ, xp_tanLine]
    congr 1
    funext l'
    exact hiddenShear_zero Φ.eb l'
  have hg : ∀ P : Po, MvPolynomial.eval (Submission.Lib.K4XInterface.gx l (t₀ + q * τ)) P =
      MvPolynomial.eval (xp l (t₀ + q * τ)) P := fun P => rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hx, Φ.eval_normTest hq' hD hsc' δA R l (t₀ + q * τ), hg]
  · rw [hx, Φ.pderiv_normTest, smul_eval, Φ.eval_normTest hq' hD hsc' δA _ l (t₀ + q * τ), hg]
    rfl
  · rw [hx, Φ.pderiv_normTest, Derivation.map_smul, Φ.pderiv_normTest, smul_eval, smul_eval,
      Φ.eval_normTest hq' hD hsc' δA _ l (t₀ + q * τ), hg]
    rfl

/-- The planar position of a tangent line is the rescaled original position. -/
lemma y_tanLine_iso (t₀ q : ℝ) (c : P2) (sc : ℝ) (hq : q ≠ 0) (l : Ln) (τ : ℝ) :
    Split.y (tanLine (isoPFrame t₀ q c sc) 0 l) τ = q⁻¹ • (Split.y l (t₀ + q * τ) - c) := by
  have h := xp_tanLine_iso t₀ q c sc hq l τ
  ext i
  fin_cases i
  · have := congrFun h 1
    simp only [Split.y, Split.x] at this ⊢
    simp [this, div_eq_inv_mul]
  · have := congrFun h 2
    simp only [Split.y, Split.x] at this ⊢
    simp [this, div_eq_inv_mul]

/-- The chart of a packet below an ancestor, in the ancestor's isotropic frame. -/
theorem ch_virtual (N : ℝ) (Mp Dp M' : ℕ) (κ : ℝ) (Tb jb TA jA : ℕ) (rb rA B : ℝ)
    (E : Set Ev) (c u cA : P2) (Q : Matrix (Fin 2) (Fin 2) ℝ) (R : Po) (A : Set Ln)
    (F : Set Ev) (ex : Prop)
    (hN : 1 ≤ N) (hMp : Mp ≤ M') (hB : 0 < B) (hκ : 0 < κ)
    (hTT : TA ≤ Tb) (hj : jA * 2 ^ (Tb - TA) ≤ jb)
    (hch : Split.ch N Mp Dp κ Tb (jb : ℝ) rb B E c u Q R A F ex)
    (hcenter : ‖((2:ℝ)^TA) • (c + ((jA:ℝ)/(2:ℝ)^TA) • u - cA)‖ + ‖u‖ ≤ N ^ M')
    (hframe : (2:ℝ)^TA * N^Mp ≤ N^M')
    (hcoeffR : ∀ e, |((isoPFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ cA
      (B / Split.δ N rA)).normTest (Split.δ N rA) R).coeff e| ≤ N^M')
    (hline : ∀ l ∈ A, ∀ e, |(tanLine (isoPFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ cA
      (B / Split.δ N rA)) 0 l).2 e| ≤ N^M') :
    Split.ch N M' Dp (2*κ) (Tb - TA) ((jb - jA * 2^(Tb - TA) : ℕ) : ℝ) (rb - rA) 1 Set.univ
      (((2:ℝ)^TA) • (c + ((jA:ℝ)/(2:ℝ)^TA) • u - cA)) u (((2:ℝ)^TA) • Q)
      ((isoPFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ cA (B / Split.δ N rA)).normTest
        (Split.δ N rA) R)
      (tanLine (isoPFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ cA (B / Split.δ N rA)) 0 '' A)
      (tanEvent (isoPFrame ((jA:ℝ)/(2:ℝ)^TA) ((2:ℝ)^TA)⁻¹ cA (B / Split.δ N rA)) 0 '' F)
      ex := by
  obtain ⟨hdet, -, hQsum, hQsmall, hRdeg, -, hAm, hFm, hfmt, hlines, hcount, hex⟩ := hch
  set t₀ : ℝ := (jA:ℝ)/(2:ℝ)^TA with ht₀
  set q : ℝ := ((2:ℝ)^TA)⁻¹ with hqdef
  set δA : ℝ := Split.δ N rA with hδA
  set sc : ℝ := B / δA with hscdef
  set Φ := isoPFrame t₀ q cA sc with hΦ
  have hq : q ≠ 0 := by positivity
  have hqpos : 0 < q := by positivity
  have hδApos : 0 < δA := δ_pos _ _
  have hsc : sc ≠ 0 := div_ne_zero hB.ne' hδApos.ne'
  have h2pos : (0:ℝ) < (2:ℝ)^TA := by positivity
  have h2ge : (1:ℝ) ≤ (2:ℝ)^TA := one_le_pow₀ (by norm_num)
  have hDdet : Φ.F.D.det ≠ 0 := by simp [hΦ, isoPFrame, isoFrame, hq]
  have hLe := measurableEmbedding_tanLine Φ 0 hq hDdet hsc
  have hEe := measurableEmbedding_tanEvent Φ 0 hq hDdet hsc
  have hNM : N ^ Mp ≤ N ^ M' := pow_le_pow_right₀ hN hMp
  have hinvQ : (((2:ℝ)^TA) • Q)⁻¹ = q • Q⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.nonsing_inv_mul _ (Ne.isUnit hdet), smul_smul,
      hqdef, inv_mul_cancel₀ (by positivity), one_smul]
  -- block correspondence
  have hblock : ∀ τ : ℝ, τ ∈ Set.Icc (((jb - jA * 2 ^ (Tb - TA) : ℕ) : ℝ)/(2:ℝ)^(Tb - TA))
      ((((jb - jA * 2 ^ (Tb - TA) : ℕ) : ℝ)+1)/(2:ℝ)^(Tb - TA)) →
      t₀ + q * τ ∈ Set.Icc ((jb:ℝ)/(2:ℝ)^Tb) (((jb:ℝ)+1)/(2:ℝ)^Tb) := by
    intro τ hτ
    apply (block_iff_virtual TA Tb jA jb hTT hj (t₀ + q * τ)).mpr
    have : (t₀ + q * τ - (jA:ℝ)/(2:ℝ)^TA) / ((2:ℝ)^TA)⁻¹ = τ := by
      rw [← ht₀, ← hqdef]; field_simp; ring
    rwa [this]
  have hblock' : ∀ t : ℝ, t ∈ Set.Icc ((jb:ℝ)/(2:ℝ)^Tb) (((jb:ℝ)+1)/(2:ℝ)^Tb) →
      (t - t₀) / q ∈ Set.Icc (((jb - jA * 2 ^ (Tb - TA) : ℕ) : ℝ)/(2:ℝ)^(Tb - TA))
        ((((jb - jA * 2 ^ (Tb - TA) : ℕ) : ℝ)+1)/(2:ℝ)^(Tb - TA)) :=
    fun t ht => (block_iff_virtual TA Tb jA jb hTT hj t).mp ht
  -- thickness comparisons
  have hδ1 : Split.δ N rb ≤ δA * Split.δ N (rb - rA) := by
    have := δ_add_le N rA (rb - rA); rwa [add_sub_cancel] at this
  have hδ2 : δA * Split.δ N (rb - rA) ≤ 2 * Split.δ N rb := by
    have := δ_le_two_mul N rA (rb - rA); rwa [add_sub_cancel] at this
  refine ⟨?_, hcenter, ?_, ?_, (Φ.totalDegree_normTest_le δA R).trans hRdeg, hcoeffR,
    hLe.measurableSet_image.mpr hAm, hEe.measurableSet_image.mpr hFm, ?_, ?_, ?_, hex⟩
  · -- determinant
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by positivity)) hdet
  · -- frame sums
    rw [hinvQ]
    calc (∑ e : Fin 2, ∑ e' : Fin 2, (|(((2:ℝ)^TA) • Q) e e'| + |(q • Q⁻¹) e e'|))
        ≤ ∑ e : Fin 2, ∑ e' : Fin 2, ((2:ℝ)^TA * (|Q e e'| + |Q⁻¹ e e'|)) := by
          gcongr with e _ e' _
          simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos h2pos,
            abs_of_pos hqpos]
          have : q * |Q⁻¹ e e'| ≤ (2:ℝ)^TA * |Q⁻¹ e e'| := by
            gcongr
            calc q ≤ 1 := by rw [hqdef]; exact inv_le_one_of_one_le₀ h2ge
              _ ≤ _ := h2ge
          linarith
      _ = (2:ℝ)^TA * ∑ e : Fin 2, ∑ e' : Fin 2, (|Q e e'| + |Q⁻¹ e e'|) := by
          simp only [Finset.mul_sum]
      _ ≤ (2:ℝ)^TA * N^Mp := by gcongr
      _ ≤ N^M' := hframe
  · -- small frame
    have hpow : (2:ℝ)^Tb = (2:ℝ)^TA * (2:ℝ)^(Tb - TA) := by
      rw [← pow_add, Nat.add_sub_cancel' hTT]
    calc (∑ e : Fin 2, ∑ e' : Fin 2, |(((2:ℝ)^TA) • Q) e e'|)
        = (2:ℝ)^TA * ∑ e : Fin 2, ∑ e' : Fin 2, |Q e e'| := by
          simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos h2pos, Finset.mul_sum]
      _ ≤ (2:ℝ)^TA * (κ / (2:ℝ)^Tb) := by gcongr
      _ = κ / (2:ℝ)^(Tb - TA) := by rw [hpow]; field_simp
      _ ≤ 2 * κ / (2:ℝ)^(Tb - TA) := by gcongr; linarith
  · -- formats
    intro i
    obtain ⟨h6, h7⟩ := hfmt i
    refine ⟨fmt_tanLine_image t₀ q cA sc hq hsc A i _ Dp ?_,
      fmt_tanEvent_image t₀ q cA sc hq hsc F i _ Dp ?_⟩
    · exact Submission.Lib.K4RepresentativeAssembly.fmt_mono h6 hNM le_rfl
    · exact Submission.Lib.K4RepresentativeAssembly.fmt_mono h7 hNM le_rfl
  · -- whole-block bounds on assigned lines
    rintro l' ⟨l, hl, rfl⟩
    obtain ⟨hl1, -, hlt⟩ := hlines l hl
    refine ⟨by simpa [tanLine] using hl1.trans hNM, hline l hl, fun τ hτ => ?_⟩
    have ht := hblock τ hτ
    obtain ⟨hQb, hR0, hR1, hR2⟩ := hlt _ ht
    obtain ⟨e0, e1, e2⟩ := eval_normTest_iso t₀ q cA sc δA hq hsc R l τ
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [y_tanLine_iso t₀ q cA sc hq l τ, hinvQ]
      have hw : q⁻¹ • (Split.y l (t₀ + q * τ) - cA) -
          (((2:ℝ)^TA) • (c + t₀ • u - cA)) - τ • u =
          q⁻¹ • (Split.y l (t₀ + q * τ) - c - (t₀ + q * τ) • u) := by
        rw [hqdef, inv_inv]
        ext i
        simp only [PiLp.sub_apply, PiLp.smul_apply, PiLp.add_apply, smul_eq_mul]
        field_simp
        ring
      rw [hw, LinearEquiv.map_smul, LinearMap.smul_apply, map_smul, smul_smul,
        mul_inv_cancel₀ hq, one_smul]
      linarith
    · change |MvPolynomial.eval (xp (tanLine Φ 0 l) τ) (Φ.normTest δA R)| ≤
        2 * κ * Split.δ N (rb - rA)
      rw [e0, abs_mul, abs_of_pos (inv_pos.mpr hδApos)]
      calc δA⁻¹ * |MvPolynomial.eval (xp l (t₀ + q * τ)) R|
          ≤ δA⁻¹ * (κ * Split.δ N rb) := by gcongr; exact hR0
        _ ≤ δA⁻¹ * (κ * (δA * Split.δ N (rb - rA))) := by gcongr
        _ = κ * Split.δ N (rb - rA) := by field_simp
        _ ≤ 2 * κ * Split.δ N (rb - rA) := by
            have := δ_pos N (rb - rA); nlinarith
    · change |MvPolynomial.eval (xp (tanLine Φ 0 l) τ)
        (MvPolynomial.pderiv 3 (Φ.normTest δA R))| ≤ 2 * κ * 1
      rw [e1]
      have hval : sc⁻¹ * δA⁻¹ = B⁻¹ := by rw [hscdef]; field_simp
      rw [← mul_assoc, hval, abs_mul, abs_of_pos (inv_pos.mpr hB)]
      calc B⁻¹ * |MvPolynomial.eval (xp l (t₀ + q * τ)) (MvPolynomial.pderiv 3 R)|
          ≤ B⁻¹ * (κ * B) := by gcongr; exact hR1
        _ = κ := by field_simp
        _ ≤ 2 * κ * 1 := by linarith
    · change |MvPolynomial.eval (xp (tanLine Φ 0 l) τ)
        (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 (Φ.normTest δA R)))| ≤
          2 * κ * 1 ^ 2 / Split.δ N (rb - rA)
      rw [e2]
      have hval : sc⁻¹ * (sc⁻¹ * δA⁻¹) = δA / B^2 := by rw [hscdef]; field_simp
      rw [← mul_assoc, ← mul_assoc, show sc⁻¹ * sc⁻¹ * δA⁻¹ = δA / B^2 by
        rw [← hval]; ring, abs_mul, abs_of_pos (by positivity : 0 < δA / B^2)]
      have hδr := δ_pos N (rb - rA)
      have hδb := δ_pos N rb
      calc δA / B^2 * |MvPolynomial.eval (xp l (t₀ + q * τ))
            (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 R))|
          ≤ δA / B^2 * (κ * B^2 / Split.δ N rb) := by gcongr; exact hR2
        _ = κ * δA / Split.δ N rb := by field_simp
        _ ≤ 2 * κ * 1 ^ 2 / Split.δ N (rb - rA) := by
            rw [div_le_div_iff₀ hδb hδr]
            nlinarith
  · -- counted incidences
    rintro p' ⟨p, hp, rfl⟩
    obtain ⟨-, hpA, hpI, hpL⟩ := hcount p hp
    refine ⟨Set.mem_univ _, ⟨p.1, hpA, rfl⟩, hblock' p.2 hpI, ?_⟩
    obtain ⟨-, e1, -⟩ := eval_normTest_iso t₀ q cA sc δA hq hsc R p.1 ((p.2 - t₀) / q)
    have hp2 : t₀ + q * ((p.2 - t₀) / q) = p.2 := by field_simp; ring
    rw [hp2] at e1
    change 1 / (2 * κ) ≤ |MvPolynomial.eval (xp (tanLine Φ 0 p.1) ((p.2 - t₀) / q))
      (MvPolynomial.pderiv 3 (Φ.normTest δA R))|
    rw [e1]
    have hval : sc⁻¹ * δA⁻¹ = B⁻¹ := by rw [hscdef]; field_simp
    rw [← mul_assoc, hval, abs_mul, abs_of_pos (inv_pos.mpr hB)]
    calc 1 / (2 * κ) ≤ 1 / κ := by gcongr; linarith
      _ = B⁻¹ * (B / κ) := by field_simp
      _ ≤ _ := by gcongr; exact hpL

end

end Submission.Obl.k4_isotropic_path_improvement.S294.O204.Tangent
